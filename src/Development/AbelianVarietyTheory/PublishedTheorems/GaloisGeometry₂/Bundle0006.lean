module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def AlgebraicCharacterWD : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Qbar l ≃+* ℂ)
    (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ),
    IsAlgPos χ n → Continuous μ → IsLAdicOf art ι χ n μ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
      (hj : GlobalTheory.Pst.Induces Bw) (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : GlobalTheory.NPin.IsComp χ w ξ)
      (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a),
      wdAt P ι Bw h hj ((rk1 μ).comp (Dec (F := E) A).subtype) = WD.lpOfChar h (ξ.comp a) (ha.smooth hξ.1)

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HeckeLAdicParameterAbove
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def HeckeLAdicParameterAbove : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Qbar l ≃+* ℂ)
    (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ),
    IsAlgPos χ n → Continuous μ → IsLAdicOf art ι χ n μ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
      (hj : GlobalTheory.Pst.Induces Bw) (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : GlobalTheory.NPin.IsComp χ w ξ),
      ∀ rc, IsRec h rc → wdAt P ι Bw h hj ((rk1 μ).comp (Dec (F := E) A).subtype) =
        rc (cls (GlobalTheory.SplitRead.Irr.ofDet 1 ξ hξ.1).toIrrRep)

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotPairedId
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.ContraPair.Model

namespace GlobalTheory.Published.InvTransposeModel

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem eq_triv (π : CuspSub E 0) : π = CuspSub.triv E (Nat.zero_le 1) := by
  refine CuspSub.ext (((CuspSub.triv E (Nat.zero_le 1)).irred π.V (fun φ _ => ?_) π.stable).resolve_left π.ne_bot)
  refine Submodule.mem_span_singleton.2 ⟨φ.1 1, Subtype.ext (funext fun g => ?_)⟩
  change φ.1 1 * 1 = φ.1 g
  rw [mul_one, show g = 1 from Units.ext (Subsingleton.elim _ _)]

theorem rank_zero (π : CuspSub E 0) : Paired π π invTOp := by
  have h := paired_invTOp (E := E) (Nat.zero_le 1) 1
  rw [line, CuspSub.twist_one] at h
  rw [eq_triv π]
  exact h

theorem twist {π : CuspSub E a} (h : Paired π π invTOp) (χ : HChar E) : Paired (π.twist χ) (π.twist χ) invTOp := by
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := h
  let T := π.toTwist χ
  refine ⟨B.compl₁₂ T.symm.toLinearMap T.symm.toLinearMap, fun φ h => ?_, fun ψ h => ?_, fun k φ ψ => ?_,
    fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · exact T.symm.map_eq_zero_iff.1 (h1 _ fun ψ => by simpa using h (T ψ))
  · exact T.symm.map_eq_zero_iff.1 (h2 _ fun φ => by simpa using h (T φ))
  all_goals
    obtain ⟨φ, rfl⟩ := T.surjective φ
    obtain ⟨ψ, rfl⟩ := T.surjective ψ
    simp only [T, CuspSub.op_toTwist, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  · have e := h3 k φ ψ
    simp only [invTOp] at e ⊢
    simp only [opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, e, smul_smul, opMul, chiDet,
      MonoidHom.comp_apply, det_finGL, det_invT, map_inv]
    simp
  · have e := h4 k φ ψ
    simp only [invTOp] at e ⊢
    simp only [opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, e, smul_smul, opMul, chiDet,
      MonoidHom.comp_apply, det_infGL, toUnits_barK, det_invT, map_inv]
    simp
  · have e := h5 X φ ψ
    have e2 : opAdd χ (invTOp (.lie X)) = -opAdd χ (.lie X) := by
      change dchi χ (-(Matrix.of X)ᵀ).trace = -dchi χ _
      rw [Matrix.trace_neg, Matrix.trace_transpose, map_neg]
    have e3 : opMul χ (invTOp (.lie X)) = 1 := rfl
    have e4 : opMul χ (.lie X) = 1 := rfl
    rw [e2, e3, e4]
    simp only [Units.val_one, one_smul, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination e


end GlobalTheory.Published.InvTransposeModel

end
end

