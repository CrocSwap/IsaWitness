-- CORE: compiler compatibility probe preserving official Hashable bodies and public exposure.
module
public meta import Lean

public meta section
open Lean Elab Command Term Meta

namespace ArmCert.BuildTools.ExposedHashable

private def exposeAttribute (stx : Syntax) : Syntax :=
  stx.rewriteBottomUp fun node =>
    if node.getKind == ``Parser.Term.attrInstance then
      node.rewriteBottomUp fun child =>
        if child.isIdent && child.getId.eraseMacroScopes == `no_expose then
          mkIdentFrom child `expose
        else child
    else node

def derive (names : Array Name) : CommandElabM Bool := do
  if !(← names.allM isInductive) then return false
  for name in names do
    let info ← getConstInfoInduct name
    for related in info.all do
      let relatedInfo ← getConstInfoInduct related
      if isPrivateName related || relatedInfo.ctors.any isPrivateName then
        return false
  for name in names do
    Lean.Elab.Deriving.withoutExposeFromCtors name do
      let commands ← liftTermElabM do
        let ctx ← Lean.Elab.Deriving.mkContext ``Hashable "hash" name
        return #[← Lean.Elab.Deriving.Hashable.mkHashFuncs ctx] ++
          (← Lean.Elab.Deriving.mkInstanceCmds ctx `Hashable #[name])
      for command in commands do
        elabCommand (exposeAttribute command)
  return true

initialize Lean.Elab.registerDerivingHandler ``Hashable derive

end ArmCert.BuildTools.ExposedHashable
