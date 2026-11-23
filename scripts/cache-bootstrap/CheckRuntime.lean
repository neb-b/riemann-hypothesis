/-
Check that C emitted by a fresh source compilation can accompany the preserved
published olean. This reads raw module data only: it imports no target modules
and runs no target initializers or metaprograms.

Usage: check-runtime ARCHIVED.olean FRESH.olean [REPORT.json]
Both files must use the same pinned Lean format and normalized package metadata.
-/
module

import all Lean.Compiler.ModPkgExt
import Lean
import Lean.Compiler.IR.NormIds
import Lean.Compiler.LCNF.PhaseExt

open Lean

namespace CheckRuntime

private unsafe def entriesAs (data : ModuleData) (name : Name) : Array α :=
  match data.entries.find? (fun entry => entry.1 == name) with
  | some (_, entries) => unsafeCast entries
  | none => #[]

private partial def caseTypes (body : IR.FnBody) : Array IR.IRType := Id.run do
  -- Stock IR.FnBody's alpha-equivalence ignores the case scrutinee type.
  -- Compare it separately because native switch emission uses this field.
  let mut pending := #[body]
  let mut types := #[]
  while !pending.isEmpty do
    let current := pending.back!
    pending := pending.pop
    match current with
    | .jdecl _ _ value rest => pending := pending.push rest |>.push value
    | .case _ _ type alternatives =>
        types := types.push type
        for alternative in alternatives do pending := pending.push alternative.body
    | _ => unless current.isTerminal do pending := pending.push current.body
  return types

private def sameIR (old fresh : IR.Decl) : Bool :=
  let params (xs ys : Array IR.Param) := Array.isEqv xs ys fun x y =>
    x.x == y.x && x.ty == y.ty && x.borrow == y.borrow
  match old.normalizeIds, fresh.normalizeIds with
  | .fdecl f xs type body info, .fdecl f' xs' type' body' info' =>
      f == f' && params xs xs' && type == type' && body == body'
        && caseTypes body == caseTypes body' && info.sorryDep? == info'.sorryDep?
  | .extern f xs type attr, .extern f' xs' type' attr' =>
      f == f' && params xs xs' && type == type' && attr == attr'
  | _, _ => false

private def sameSignature
    (old fresh : Compiler.LCNF.Signature .impure) : Bool :=
  old.name == fresh.name && old.levelParams == fresh.levelParams && old.type == fresh.type
    && old.safe == fresh.safe && Array.isEqv old.params fresh.params (fun x y =>
      -- Binder IDs and pretty-printing names do not form part of the native ABI.
      x.type == y.type && x.borrow == y.borrow)

private def sameConstant (old fresh : ConstantInfo) : Bool :=
  match old, fresh with
  | .axiomInfo x, .axiomInfo y => x == y
  | .defnInfo x, .defnInfo y => x == y
  | .thmInfo x, .thmInfo y => x == y
  | .opaqueInfo x, .opaqueInfo y => x == y
  | .ctorInfo x, .ctorInfo y => x == y
  | .recInfo x, .recInfo y => x == y
  | .inductInfo x, .inductInfo y =>
      x.toConstantVal == y.toConstantVal && x.numParams == y.numParams
        && x.numIndices == y.numIndices && x.all == y.all && x.ctors == y.ctors
        && x.numNested == y.numNested && x.isRec == y.isRec
        && x.isUnsafe == y.isUnsafe && x.isReflexive == y.isReflexive
  | .quotInfo x, .quotInfo y =>
      x.toConstantVal == y.toConstantVal && match x.kind, y.kind with
        | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
        | _, _ => false
  | _, _ => false

private unsafe def check (old fresh : ModuleData) : IO Json := do
  if old.isModule || fresh.isModule then
    throw <| IO.userError "runtime compatibility checker supports legacy modules only"
  unless old.imports == fresh.imports do
    throw <| IO.userError "module import declarations differ"
  let oldPackages : Array (Option PkgId) := entriesAs old modPkgExt.name
  let freshPackages : Array (Option PkgId) := entriesAs fresh modPkgExt.name
  unless oldPackages == freshPackages do
    throw <| IO.userError "normalized package metadata differs"

  let freshConstants := fresh.constants.foldl
    (fun map value => map.insert value.name value) ({} : NameMap ConstantInfo)
  for constant in old.constants do
    let some actual := freshConstants.find? constant.name
      | throw <| IO.userError s!"fresh compilation omitted constant {constant.name}"
    unless sameConstant constant actual do
      throw <| IO.userError s!"fresh constant differs: {constant.name}"

  let oldSignatures : Array (Compiler.LCNF.Signature .impure) :=
    entriesAs old `Lean.Compiler.LCNF.impureSigExt
  let freshSignatures : Array (Compiler.LCNF.Signature .impure) :=
    entriesAs fresh `Lean.Compiler.LCNF.impureSigExt
  let signatureMap := freshSignatures.foldl (fun map value => map.insert value.name value)
    ({} : NameMap (Compiler.LCNF.Signature .impure))
  for signature in oldSignatures do
    let some actual := signatureMap.find? signature.name
      | throw <| IO.userError s!"fresh compilation omitted native signature {signature.name}"
    unless sameSignature signature actual do
      throw <| IO.userError s!"fresh native signature differs: {signature.name}"

  let oldIR : Array IR.Decl := entriesAs old `Lean.IR.declMapExt
  let freshIR : Array IR.Decl := entriesAs fresh `Lean.IR.declMapExt
  let oldIRNames := oldIR.foldl (fun names declaration => names.insert declaration.name)
    ({} : NameSet)
  for signature in oldSignatures do
    unless oldIRNames.contains signature.name do
      throw <| IO.userError s!"archived native signature has no runtime IR: {signature.name}"
  let irMap := freshIR.foldl (fun map value => map.insert value.name value)
    ({} : NameMap IR.Decl)
  for declaration in oldIR do
    let some actual := irMap.find? declaration.name
      | throw <| IO.userError s!"fresh compilation omitted runtime helper {declaration.name}"
    unless sameIR declaration actual do
      throw <| IO.userError s!"fresh runtime IR differs: {declaration.name}"

  -- Initialization order and its declaration targets must agree as well.
  for extension in #[`Lean.regularInitAttr, `Lean.builtinInitAttr] do
    let oldEntries : Array (Name × Name) := entriesAs old extension
    let freshEntries : Array (Name × Name) := entriesAs fresh extension
    unless oldEntries == freshEntries do
      throw <| IO.userError s!"module initializer metadata differs: {extension}"

  return Json.mkObj [
    ("constants", toJson old.constants.size),
    ("signatures", toJson oldSignatures.size),
    ("runtimeIR", toJson oldIR.size),
    ("compatible", toJson true)]

end CheckRuntime

public unsafe def main (args : List String) : IO Unit := do
  let (oldFile, freshFile, report) ← match args with
    | [oldFile, freshFile] => pure (oldFile, freshFile, none)
    | [oldFile, freshFile, report] => pure (oldFile, freshFile, some report)
    | _ => throw <| IO.userError "usage: check-runtime ARCHIVED.olean FRESH.olean [REPORT.json]"
  let started ← IO.monoMsNow
  let (old, _) ← readModuleData oldFile
  let (fresh, _) ← readModuleData freshFile
  let result ← CheckRuntime.check old fresh
  let text := result.compress ++ "\n"
  if let some path := report then IO.FS.writeFile path text else IO.print text
  IO.eprintln s!"checked runtime compatibility in {(← IO.monoMsNow) - started}ms"
