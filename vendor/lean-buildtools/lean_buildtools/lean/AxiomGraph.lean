import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Data.Json.FromToJson

/-! Read complete declaration data without constructing a global import environment.
This is metadata tooling, not an independent proof checker. Lean 4.35 is required.
-/

open Lean Elab Command

namespace BuildTools.AxiomGraph

private def copyString (value : String) : String := String.ofList value.toList

private def copyName : Name → Name
  | .anonymous => .anonymous
  | .str parent text => .str (copyName parent) (copyString text)
  | .num parent number => .num (copyName parent) number.repr.toNat!

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

private def dependencies (info : ConstantInfo) : Array Name := Id.run do
  if info matches .quotInfo _ then return #[]
  let mut names := info.type.getUsedConstantsAsSet
  if let some body := info.value? (allowOpaque := true) then
    names := names ++ body.getUsedConstantsAsSet
  match info with
  | .inductInfo value =>
    for name in value.ctors do names := names.insert name
  | _ => pure ()
  return names.toArray.qsort Name.lt

/-- Lossless, canonical expression DAG. Pointer memoization only avoids repeated
visits; canonical nodes are interned by complete structural text, never a hash
alone. References cannot escape the mapped module regions. -/
unsafe def expressionIdentity (root : Expr) : IO String := do
  let mut memo : PtrMap Expr Nat := mkPtrMap
  let mut intern : Std.HashMap String Nat := {}
  let mut nodes : Array String := #[]
  let mut todo : Array (Expr × Bool) := #[(root, false)]
  while !todo.isEmpty do
    let (expr, ready) := todo.back!
    todo := todo.pop
    if memo.contains expr then continue
    if !ready then
      todo := todo.push (expr, true)
      let children := match expr with
        | .app f a => #[f, a]
        | .lam _ t b _ | .forallE _ t b _ => #[t, b]
        | .letE _ t v b _ => #[t, v, b]
        | .mdata _ b | .proj _ _ b => #[b]
        | _ => #[]
      for child in children.reverse do
        if !memo.contains child then todo := todo.push (child, false)
    else
      let ref (child : Expr) : IO Expr := do
        let some id := memo.find? child | throw <| IO.userError "missing expression DAG child"
        return .bvar id
      let shape : Expr ← match expr with
        | .app f a => pure (.app (← ref f) (← ref a))
        | .lam n t b i => pure (.lam n (← ref t) (← ref b) i)
        | .forallE n t b i => pure (.forallE n (← ref t) (← ref b) i)
        | .letE n t v b d => pure (.letE n (← ref t) (← ref v) (← ref b) d)
        | .mdata d b => pure (.mdata d (← ref b))
        | .proj n i b => pure (.proj n i (← ref b))
        | other => pure other
      let key := reprStr shape
      let id := match intern[key]? with
        | some id => id
        | none => nodes.size
      if id == nodes.size then
        nodes := nodes.push key
        intern := intern.insert key id
      memo := memo.insert expr id
  let some rootId := memo.find? root | throw <| IO.userError "missing expression DAG root"
  return (toJson (rootId, nodes)).compress

private def isEquationName (name : Name) : Bool := Id.run do
  let suffix := (name.toString.splitOn ".").getLast!
  if suffix == "eq_def" || suffix == "eq_unfold" then return true
  let chars := suffix.toList
  let digits := if suffix.startsWith "eq_" then chars.drop 3
    else if suffix.startsWith "eq" then chars.drop 2 else []
  return !digits.isEmpty && digits.all Char.isDigit

private def emit (stream : IO.FS.Handle) (value : Json) : IO Unit :=
  stream.putStrLn value.compress

/-- Identity includes every existing part, so public-file aliases cannot hide
conflicting private bodies. Keep the logical path for sibling-part loading. -/
private def artifactIdentity (path : System.FilePath) : IO (Array (Option System.FilePath)) := do
  let mut identity := #[]
  for part in #[path, OLeanLevel.server.adjustFileName path, OLeanLevel.private.adjustFileName path] do
    let entry ← if ← part.pathExists then do
      pure (some (← realPathNormalized part))
    else pure none
    identity := identity.push entry
  return identity

/-- Resolve complete module paths, even when packages share a namespace prefix.
Distinct existing artifact sets are ambiguous; repeated paths to one set are not. -/
def resolveOLean (module : Name) : IO System.FilePath := do
  let mut candidates : Array (System.FilePath × Array (Option System.FilePath)) := #[]
  for root in ← searchPathRef.get do
    let candidate := modToFilePath root module "olean"
    if ← candidate.pathExists then
      let identity ← artifactIdentity candidate
      unless candidates.any (fun entry => entry.2 == identity) do
        let currentDir ← IO.currentDir
        let logical := if candidate.isAbsolute then candidate else currentDir / candidate
        candidates := candidates.push (logical.normalize, identity)
  if candidates.size == 1 then
    return candidates[0]!.1
  if candidates.isEmpty then
    throw <| IO.userError s!"no existing compiled artifact for module {module}"
  throw <| IO.userError s!"ambiguous compiled artifacts for module {module}: {candidates.map (·.1)}"

/-- The return value contains only copied names and unboxed region handles.
All references into mapped declaration data die before the caller frees regions. -/
private unsafe def dumpModule (module : Name) (stream : IO.FS.Handle) (metadataOnly : Bool)
    (artifacts : NameMap System.FilePath) :
    IO (Array Name × Array CompactedRegion) := do
  let path ← resolveOLean module
  if let some supplied := artifacts.find? module then
    unless (← artifactIdentity supplied) == (← artifactIdentity path) do
      throw <| IO.userError s!"artifact override disagrees with resolved module {module}"
  let currentDir ← IO.currentDir
  let path := if path.isAbsolute then path else currentDir / path
  let (publicData, publicRegion) ← readModuleData path
  let isModule := publicData.isModule
  let paths := if isModule then
      #[path, OLeanLevel.server.adjustFileName path, OLeanLevel.private.adjustFileName path]
    else #[path]
  -- The same ordered dependent-region loading used by readModuleDataParts,
  -- retaining the first part read above to avoid mapping it twice.
  let mut parts := #[(publicData, publicRegion)]
  if isModule then
    let server ← CompactedRegion.read (α := ModuleData) paths[1]! #[publicRegion]
    let priv ← CompactedRegion.read (α := ModuleData) paths[2]! #[publicRegion, server.2]
    parts := parts.push server |>.push priv
  let some (data, _) := parts.back? | throw <| IO.userError "empty module data"
  unless data.constNames.size == data.constants.size do
    throw <| IO.userError s!"malformed constant index: {module}"
  let imports := data.imports.map (fun item => copyName item.module)
  emit stream <| Json.mkObj [
    ("event", toJson "module"), ("module", toJson module.toString),
    ("path", toJson path.toString), ("is_module", toJson isModule),
    ("parts", toJson <| paths.map System.FilePath.toString),
    ("imports", toJson <| imports.map Name.toString),
    ("declaration_count", toJson data.constants.size)]
  unless metadataOnly do
   for name in data.constNames, info in data.constants do
    unless name == info.name do
      throw <| IO.userError s!"constant index/name mismatch: {module}/{name}"
    -- Lean.Environment.subsumesInfo permits different proofs of an on-demand
    -- equation theorem only when its exact type, universes and `all` agree.
    -- Emit structural data, not a short hash or a cached axiom approximation.
    let equationIdentity ← match info with
      | .thmInfo value => do
        if isEquationName info.name then
          let identity ← expressionIdentity info.type
          pure <| toJson ((toJson ("equation-type-dag-v1", reprStr info.levelParams,
            identity, reprStr value.all)).compress)
        else pure Json.null
      | _ => pure Json.null
    emit stream <| Json.mkObj [
      ("event", toJson "declaration"), ("module", toJson module.toString),
      ("name", toJson info.name.toString), ("kind", toJson (kind info)),
      ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial),
      ("equation_identity", equationIdentity),
      ("dependencies", toJson <| (dependencies info).map Name.toString),
      ("cached_axioms", Json.null)]
  stream.flush
  return (imports, parts.map (·.2))

unsafe def run (requestPath : String) : IO Unit := do
  let request ← IO.ofExcept <| Json.parse (← IO.FS.readFile requestPath)
  let modules ← IO.ofExcept <| request.getObjValAs? (Array String) "modules"
  let output ← IO.ofExcept <| request.getObjValAs? String "output"
  let metadataOnly ← IO.ofExcept <| request.getObjValAs? Bool "metadata_only"
  let entries ← IO.ofExcept <| request.getObjValAs? (Array (String × String)) "artifacts"
  let artifacts : NameMap System.FilePath := entries.foldl
    (fun result (name, path) => result.insert name.toName path) {}
  let stream ← IO.FS.Handle.mk output .write
  let mut pending := modules.map String.toName
  let mut seen : NameHashSet := {}
  while !pending.isEmpty do
    let module := pending.back!
    pending := pending.pop
    if seen.contains module then continue
    seen := seen.insert module
    let (imports, regions) ← dumpModule module stream metadataOnly artifacts
    regions.forM CompactedRegion.free
    pending := pending ++ imports
  emit stream <| Json.mkObj [("event", toJson "complete"), ("modules", toJson seen.size)]
  stream.flush

end BuildTools.AxiomGraph
