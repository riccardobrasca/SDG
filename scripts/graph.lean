import Mathlib

import SDG

open Lean Meta Elab Command

namespace ChoiceDeps

abbrev DepSet := Std.HashSet Name
abbrev ChoiceMemo := NameMap Bool

def addExprDeps (deps : DepSet) (e : Expr) : DepSet :=
  Id.run <| do
    let mut out := deps
    for c in e.getUsedConstants do
      out := out.insert c
    return out

def directDeps (env : Environment) (decl : Name) : DepSet :=
  let deps := match env.checked.get.find? decl with
    | some (.axiomInfo v) =>
      addExprDeps {} v.type
    | some (.defnInfo v) =>
      addExprDeps (addExprDeps {} v.type) v.value
    | some (.thmInfo v) =>
      addExprDeps (addExprDeps {} v.type) v.value
    | some (.opaqueInfo v) =>
      addExprDeps (addExprDeps {} v.type) v.value
    | some (.quotInfo _) =>
      {}
    | some (.ctorInfo v) =>
      addExprDeps {} v.type
    | some (.recInfo v) =>
      addExprDeps {} v.type
    | some (.inductInfo v) =>
      v.ctors.foldl (init := addExprDeps {} v.type) fun acc c => acc.insert c
    | none =>
      {}
  deps.erase decl

partial def transitiveDeps (env : Environment) (root : Name) : DepSet :=
  let rec visit (decl : Name) (visited : DepSet) : DepSet :=
    if visited.contains decl then
      visited
    else
      (directDeps env decl).toArray.foldl (init := visited.insert decl) fun acc dep =>
        visit dep acc
  (visit root {}).erase root

partial def dependsOnChoiceM (env : Environment) (decl : Name) : StateM ChoiceMemo Bool := do
  let memo ← get
  if let some b := memo.find? decl then
    return b
  modify fun s => s.insert decl false
  let deps := directDeps env decl
  if deps.contains ``Classical.choice then
    modify fun s => s.insert decl true
    return true
  let rec go (i : Nat) (arr : Array Name) : StateM ChoiceMemo Bool := do
    if h : i < arr.size then
      let d := arr[i]
      if ← dependsOnChoiceM env d then
        return true
      go (i + 1) arr
    else
      return false
  let res ← go 0 deps.toArray
  modify fun s => s.insert decl res
  return res

def choiceDependencyGraph (env : Environment) (root : Name)
    : Array Name × NameMap (Array Name) :=
  let work : StateM ChoiceMemo (Array Name × NameMap (Array Name)) := do
    let mut bfsOrder : Array Name := #[]
    let mut graph : NameMap (Array Name) := {}
    let mut queue : Array Name := #[root]
    let mut qHead := 0
    let mut visited : DepSet := {}
    while qHead < queue.size do
      let current := queue[qHead]!
      qHead := qHead + 1
      if visited.contains current then continue
      if !(← dependsOnChoiceM env current) then continue
      visited := visited.insert current
      bfsOrder := bfsOrder.push current
      let allDeps := directDeps env current
      let mut choiceDeps : Array Name := #[]
      if allDeps.contains ``Classical.choice then
        choiceDeps := choiceDeps.push ``Classical.choice
      for d in allDeps.toArray.qsort Name.quickLt do
        if d == ``Classical.choice then continue
        if ← dependsOnChoiceM env d then
          choiceDeps := choiceDeps.push d
          if !visited.contains d then
            queue := queue.push d
      graph := graph.insert current choiceDeps
    return (bfsOrder, graph)
  work.run' {}

def formatGraph (bfsOrder : Array Name) (graph : NameMap (Array Name)) : MessageData :=
  let lines := bfsOrder.toList.filterMap fun n =>
    match graph.find? n with
    | none => none
    | some deps =>
      let depsMsg := MessageData.joinSep (deps.toList.map fun d => m!"{.ofConstName d}") ", "
      some m!"{.ofConstName n} → {depsMsg}"
  MessageData.joinSep lines "\n"

private def dotNode (n : Name) : String := "\"" ++ n.toString ++ "\""

/-- Produce a Graphviz DOT string for the choice-dependency graph.
    Paste it at https://dreampuf.github.io/GraphvizOnline -/
def formatDot (root : Name) (bfsOrder : Array Name) (graph : NameMap (Array Name)) : String :=
  let edges : Array String := bfsOrder.foldl (init := #[]) fun acc n =>
    match graph.find? n with
    | none => acc
    | some deps => deps.foldl (init := acc) fun acc2 d =>
        acc2.push s!"  {dotNode n} -> {dotNode d};"
  let allNodes : Array String := bfsOrder.foldl (init := #[dotNode ``Classical.choice ++ " [shape=diamond, style=filled, fillcolor=tomato]"]) fun acc n =>
    if n == ``Classical.choice then acc
    else if n == root then
      acc.push s!"{dotNode n} [style=filled, fillcolor=lightblue]"
    else
      acc.push s!"{dotNode n} [style=filled, fillcolor=lightyellow]"
  let body := ((allNodes.map fun s => "  " ++ s) ++ edges).toList
  "digraph choice_deps {\n  rankdir=TB;\n  node [fontname=\"Helvetica\", fontsize=10];\n" ++
    "\n".intercalate body ++
    "\n}"

syntax (name := printChoiceDepsDot) "#print " &"choice_deps_on_choice_dot" ppSpace ident : command

elab_rules : command
  | `(#print choice_deps_on_choice_dot $id:ident) => do
    let targets ← liftCoreM <| realizeGlobalConstWithInfos id
    let env ← getEnv
    for target in targets do
      let (bfsOrder, graph) := choiceDependencyGraph env target
      if graph.isEmpty then
        logInfo m!"{.ofConstName target}: no dependency on Classical.choice"
      else
        let dot := formatDot target bfsOrder graph
        IO.FS.writeFile "graph.dot" dot
        logInfo m!"DOT graph written to graph.dot\n\n{dot}"

end ChoiceDeps

/-
Example:
  #print choice_deps_on_choice_dot SDG.taylor_multi  -- paste output into GraphvizOnline
-/
