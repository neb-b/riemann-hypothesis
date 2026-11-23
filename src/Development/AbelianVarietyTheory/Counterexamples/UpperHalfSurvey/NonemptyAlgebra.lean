module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0028

@[expose] public section

open WittVector Ideal ReciprocityTheory.PGsh

namespace GlobalTheory.AinfChecks


open WittVector Ideal in
theorem _root_.GlobalTheory.AinfChecks.padicComplex (p : ℕ) [Fact p.Prime] :
    ∃ (_ : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p])) (_ : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]),
      (∃ pflat : PreTilt 𝓞_ℂ_[p] p, pflat.untilt = ((p : ℕ) : 𝓞_ℂ_[p])) ∧
      (∃ ε : PreTilt 𝓞_ℂ_[p] p,
        IsPrimitiveRoot (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε).untilt) p) ∧
      _root_.ReciprocityTheory.PGsh.KerThetaStatement p 𝓞_ℂ_[p] ∧ _root_.ReciprocityTheory.PGsh.XiNuStatement p ℂ_[p] Valued.v 𝓞_ℂ_[p] ∧
      _root_.ReciprocityTheory.PGsh.RegularStatement p 𝓞_ℂ_[p] ∧ _root_.ReciprocityTheory.PGsh.FlatW'Statement p 𝓞_ℂ_[p] := by
  obtain ⟨hunit, hcomp, ε, hv, hε⟩ := _root_.GlobalTheory.PadicComplexHost.main p
  have hker : _root_.ReciprocityTheory.PGsh.KerThetaStatement p 𝓞_ℂ_[p] := _root_.ReciprocityTheory.PGsh.kerTheta ℂ_[p] Valued.v hv
  refine ⟨hunit, hcomp, _root_.ReciprocityTheory.PGsh.exists_pflat ℂ_[p] Valued.v 𝓞_ℂ_[p] hv, ⟨ε, hε⟩, hker,
    _root_.ReciprocityTheory.PGsh.xiNu p ℂ_[p] Valued.v 𝓞_ℂ_[p] hker, ?_, _root_.ReciprocityTheory.PGsh.flatW' p 𝓞_ℂ_[p]⟩
  refine _root_.ReciprocityTheory.PGsh.regular p 𝓞_ℂ_[p] fun x hx => ?_
  have h : ((p : ℂ_[p]) * (x : ℂ_[p])) = 0 := by
    simpa using congrArg (fun y : 𝓞_ℂ_[p] => (y : ℂ_[p])) hx
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  · exact Subtype.ext h

section
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]


end

end GlobalTheory.AinfChecks
