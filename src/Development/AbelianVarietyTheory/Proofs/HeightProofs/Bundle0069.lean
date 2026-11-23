module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0063
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0002
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.IsTypeAtCentral
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0066

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.AbelianUnramIn
section
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize

namespace GlobalTheory.FieldSize.WeberUnram


set_option autoImplicit false in
open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.FieldSize.WeberUnram.of_algHom {K M R : Type} [Field K] [NumberField K]
    [Field M] [Algebra K M] [Field R] [NumberField R]
    [Algebra K R] [IsAbelianGalois K R] (f : M →ₐ[K] R) :
    ∃ (_ : NumberField M) (_ : IsAbelianGalois K M),
      ∀ 𝔭 : HeightOneSpectrum (𝓞 K), _root_.GlobalTheory.NT.UnramIn R 𝔭 →
        _root_.GlobalTheory.NT.UnramIn M 𝔭 := by
  have hab : IsAbelianGalois K M := IsAbelianGalois.of_algHom f
  letI : Algebra M R := f.toRingHom.toAlgebra
  haveI : IsScalarTower K M R := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  haveI : FiniteDimensional K M := FiniteDimensional.left K M R
  haveI : FiniteDimensional ℚ M := Module.Finite.trans K M
  haveI nf : NumberField M := ⟨⟩
  exact ⟨nf, hab, fun 𝔭 h => _root_.GlobalTheory.RayMaximal.unramIn_of_tower (L := M) (M := R) h⟩

end GlobalTheory.FieldSize.WeberUnram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CurveOverOfRayField
section
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.RayExistCurve

section Quadratic

variable {K : Type} [Field K] [NumberField K] {d : ℕ}

end Quadratic


set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField in
theorem _root_.GlobalTheory.FieldSize.RayExistCurve.finrank_adjoin {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) :
    FiniteDimensional ℚ ℚ⟮r⟯ ∧ Module.finrank ℚ ℚ⟮r⟯ = 2 := by
  open Polynomial in
  have hroot : aeval r (X ^ 2 + C (d : ℚ)) = 0 := by simp [hr]
  have hmon : (X ^ 2 + C (d : ℚ)).Monic := monic_X_pow_add_C _ (by norm_num)
  have hint : IsIntegral ℚ r := ⟨_, hmon, by simpa [aeval_def] using hroot⟩
  have hdeg : (X ^ 2 + C (d : ℚ)).natDegree = 2 := natDegree_X_pow_add_C
  have hirr : Irreducible (X ^ 2 + C (d : ℚ)) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]; decide
    · intro x hx
      have hx' : x ^ 2 + (d : ℚ) = 0 := by simpa using hx
      have hd' : (0 : ℚ) < d := by exact_mod_cast hd
      nlinarith [sq_nonneg x]
  have hmin : minpoly ℚ r = X ^ 2 + C (d : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hmon).symm
  refine ⟨IntermediateField.adjoin.finiteDimensional hint, ?_⟩
  rw [IntermediateField.adjoin.finrank hint, hmin, hdeg]

end GlobalTheory.FieldSize.RayExistCurve
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.TypeAtCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem card_eq_of_congr {n p q : ℕ} {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (hs : Formalism.UG.HasSignature G p q) :
    (Finset.univ.filter fun a => ε a = true).card = p ∧ (Finset.univ.filter fun a => ε a = false).card = q := by
  classical
  obtain ⟨hc, Q, hQ⟩ := Formalism.UG.P.sig_data G p q hs
  set p' := (Finset.univ.filter fun a => ε a = true).card with hp'
  set q' := (Finset.univ.filter fun a => ε a = false).card with hq'
  let e1 : Fin p' ≃ {a // ε a = true} := (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype])).symm
  let e2 : Fin q' ≃ {a // ¬ ε a = true} :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype]; simp [hq'])).symm
  let e : Fin p' ⊕ Fin q' ≃ Fin n := (Equiv.sumCongr e1 e2).trans (Equiv.sumCompl _)
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hJ : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    rw [← h]
    calc (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  have hQ' : (P⁻¹.submatrix id e)ᴴ * G * P⁻¹.submatrix id e = Formalism.UG.Jpq p' q' := by
    have : (P⁻¹.submatrix id e)ᴴ * G * P⁻¹.submatrix id e = ((P⁻¹)ᴴ * G * P⁻¹).submatrix e e := by
      ext i j; simp [Matrix.mul_apply]
    rw [this, hJ]
    have h1 : ∀ a, ε (e (Sum.inl a)) = true := fun a => (e1 a).2
    have h2 : ∀ a, ¬ ε (e (Sum.inr a)) = true := fun a => (e2 a).2
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Formalism.REAL.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, h1, h2]
    split_ifs <;> simp
  have hn : n = p' + q' := by
    have := Fintype.card_congr e
    simpa using this.symm
  have h1 := Formalism.UG.P.sig_dim G Q hQ _ hQ'
  have h2 := Formalism.UG.P.sig_dim G _ hQ' Q hQ
  simp only [Fintype.card_fin] at h1 h2 hc
  omega

theorem conj_mem {n : ℕ} {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G) :
    P * g * P⁻¹ ∈ UJset ε := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hg' : gᴴ * G * g = G := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        rw [h, hg', ← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

section Pred

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {S : SPar}
  {σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)} {lam : Fin V.rank → ℝ} {ε : Fin V.rank → Bool}
  {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}

end Pred

variable {D : D7} {X : ThetaX D}


end GlobalTheory.TypeAtCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsRayIntermediateField
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.SmallField

theorem exists_isRay_intermediateField (hR : GlobalTheory.NT.RayField) (K : IntermediateField ℚ ℂ) [NumberField K]
    (𝔮 : Ideal (𝓞 K)) (h𝔮 : 𝔮 ≠ ⊥) :
    ∃ (R : IntermediateField K ℂ) (_ : NumberField R) (_ : IsAbelianGalois K R), IsRay R 𝔮 := by
  obtain ⟨M, _, _, _, hM⟩ := GlobalTheory.Mem.Fld.rayField_iff.1 hR K 𝔮 h𝔮
  have := hM.1
  let f : M →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e : M ≃ₐ[K] f.fieldRange := AlgEquiv.ofInjectiveField f
  have : FiniteDimensional K f.fieldRange := e.toLinearEquiv.finiteDimensional
  have : NumberField f.fieldRange := NumberField.of_module_finite K f.fieldRange
  have h := hM.of_algEquiv e
  exact ⟨f.fieldRange, inferInstance, h.1, h.2⟩

end GlobalTheory.FieldSize.SmallField

namespace GlobalTheory.FieldSize

open SmallField GlobalTheory.Mem.BaseExt

end GlobalTheory.FieldSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsReadingDensKNrmTieU
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.HeightDefinite.Generic

theorem supPTGe_of_fnPin : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j), ∀ (fn : ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ), GlobalTheory.FrameNorm.FnPin (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (xiR D) fn → ∀ (hG : GenFrEx (T.Q.Xo j) T.Q.c) (yP : ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∀ P : Om Z →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt (sgOf P))), (∀ Z, CBase hG Z (yP Z)) → ∀ ka : WeightFamilies.Wt D j, SupPTGe h j hG fn yP ka := by
  intro D T h j hj fn hfn hG yP hyP ka Z F hF hev
  have hU : ∀ σ, Formalism.L2.PjFree.GoodEmb T.Q.c σ →
      Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) := fun σ hσ => h.unf j hj σ hσ
  have hFc : F.1 ∈ Formalism.L2.PjFree.cusp (T.Q.Xo j) T.Q.c (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
      (wtA ka) ka.n := cutR_le T.C j ka F.2
  obtain ⟨g, hg, h1, h0, hI⟩ := GlobalTheory.Reg.exists_cusp_restrict_comp_int _ _ _ _ (T.Q.Xo j) T.Q.c D.R.r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hU hG Z (wtA ka) ka.n F.1 hFc
  have hg' : g ∈ cutR T.C j ka := by
    rw [cutR_eq T.C hj]; exact hg
  have hx : 0 < xiR D := (GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins).2.2.2.1
  refine ⟨⟨g, hg'⟩, ?_, ?_, fun sg => ?_⟩
  · intro la v hv
    have hFv := hF la v hv
    obtain ⟨⟨q, Tc, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
    change 0 ≤ nval Tc.V e (evI y g)
    change 0 ≤ nval Tc.V e (evI y F.1) at hFv
    rcases hI Tc io y with h2 | h2
    · rw [h2]; exact hFv
    · rw [h2, nval_zero]; exact le_top
  · intro h2
    have h3 : g = 0 := congrArg Subtype.val h2
    apply hev
    change evC hG Z F.1 = 0
    rw [← h1, h3, evC_zero]
  · have h4 := (GlobalTheory.HeightDefinite.Generic.supC_le_iSup_generic _ _ _ _ (T.Q.Xo j) T.Q.c D.R.r
      (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hU (xiR D) fn hx hfn hG yP hyP (wtA ka) ka.n (dom_wtA ka) Z
      F.1 hFc g hg h1 h0 sg).2
    change cutN T.C T.Ns j ka sg ⟨g, hg'⟩ ≤ _
    unfold cutN
    rw [if_pos hj]
    exact h4

theorem exists_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (xR : ℝ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (hx : 0 < xR)
    (hfn : GlobalTheory.FrameNorm.FnPin (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) xR fn)
    (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) :
    ∃ (k : (U (goodOf c σ)).Comp) (x : ((U (goodOf c σ)).X k).dom), ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n,
      Formalism.L2.Pj.ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f y =
        recNrm (U (goodOf c σ)) xR a n f k x.1 := by
  obtain ⟨-, h2, h3⟩ := GlobalTheory.FrameNorm.Comparison₂.ptNorm_eq_pnorm E H Dw l Xo c r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hU xR fn hx hfn
  have hg := goodEmb_goodOf c σ
  by_cases hσ : GoodEmb c σ
  · have e : goodOf c σ = σ := if_pos hσ
    rw [e]
    obtain ⟨k, x, t, ht⟩ := (hU σ hσ).2.2.1 y
    exact ⟨k, x, fun a n hd f hf => h2 σ hσ k x t y ht a n hd f hf⟩
  · have e : goodOf c σ = (starRingEnd ℂ).comp σ := if_neg hσ
    rw [e] at hg ⊢
    obtain ⟨y', hy'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _
      (GlobalTheory.FrameNorm.conjAlg σ) y
    obtain ⟨k, x, t, ht⟩ := (hU _ hg).2.2.1 y'
    exact ⟨k, x, fun a n hd f hf => (h3 σ y y' hy' a n f hf).symm.trans (h2 _ hg k x t y' ht a n hd f hf)⟩

theorem exists_reading_densK_nrmTieU : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j), ∀ (fn : ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ), GlobalTheory.FrameNorm.FnPin (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (xiR D) fn → ∀ (hG : GenFrEx (T.Q.Xo j) T.Q.c) (yP : ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∀ P : Om Z →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt (sgOf P))), (∀ Z, CBase hG Z (yP Z)) → ∃ pt : ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (P : Om Z →+* ℂ), SupPtAt (Tc := T) j (goodOf T.Q.c (sgOf P)), (∀ (Z : Comp (T.Q.Xo j) T.Q.c) (P : Om Z →+* ℂ) a n, Dom a n → ∀ F ∈ sec (T.Q.Xo j) T.Q.c a n, nrmC fn (yP Z) (wtZ a n) (valC hG a n F Z) P = recNrm (T.U j (goodOf T.Q.c (sgOf P))) (xiR D) a n F (pt Z P).1 (pt Z P).2.1) ∧ (∀ ka : WeightFamilies.Wt D j, DensK h j hG ka pt) ∧ ∀ (N : ℕ) (wR : Fin (N + 1) → T.R j) (uL : WtR D.host.E) (etR : T.R j) (uet : WtR D.host.E), Dom uL.1 uL.2 → Dom uet.1 uet.2 → (∀ k, wR k ∈ sec (T.Q.Xo j) T.Q.c uL.1 uL.2) → etR ∈ sec (T.Q.Xo j) T.Q.c uet.1 uet.2 → NrmTieU hG fn yP (T.U j) (xiR D) wR uL etR uet := by
  intro D T h j hj fn hfn hG yP hyP
  have hx : 0 < xiR D := (GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins).2.2.2.1
  have hU := h.unf j hj
  have h3 := (GlobalTheory.FrameNorm.fnConj_valAtCx_nrmC_eq_ptNorm _ _ _ _ (T.Q.Xo j) T.Q.c _
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hU (xiR D) fn hx hfn hG yP hyP).2.2
  choose k x hkx using fun (Z : Comp (T.Q.Xo j) T.Q.c) (P : Om Z →+* ℂ) =>
    exists_frame (T.U j) hU (xiR D) fn hx hfn (sgOf P) (yP Z P)
  have key : ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (P : Om Z →+* ℂ) a n, Dom a n → ∀ F ∈ sec (T.Q.Xo j) T.Q.c a n,
      nrmC fn (yP Z) (wtZ a n) (valC hG a n F Z) P =
        recNrm (T.U j (goodOf T.Q.c (sgOf P))) (xiR D) a n F (k Z P) (x Z P).1 :=
    fun Z P a n hd F hF => (h3 Z P a n F hF).trans (hkx Z P a n hd F hF)
  refine ⟨fun Z P => ⟨k Z P, ⟨(x Z P).1, (x Z P).2⟩⟩, key, fun ka Z F hF hev => ?_,
    fun N wR uL etR uet hL he hw het Z P => ?_⟩
  · obtain ⟨F', hF', hne, hsup⟩ := supPTGe_of_fnPin D T h j hj fn hfn hG yP hyP ka Z F hF hev
    refine ⟨F', hF', hne, fun sg => (hsup sg).trans (le_of_eq ?_)⟩
    exact iSup_congr fun P => key Z P _ _ (dom_wtA ka) _ (cusp_le_sec _ _ _ _ _ (cutR_le T.C j ka F.2))
  · exact ⟨goodOf T.Q.c (sgOf P), goodEmb_goodOf _ _, k Z P, (x Z P).1, (x Z P).2,
      fun i => key Z P _ _ hL _ (hw i), (key Z P _ _ he _ het).le⟩

end GlobalTheory.HeightDefinite.Generic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetRayClassField
section
set_option autoImplicit false

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.InRayAny

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField in
private theorem weberSet_subset_of_isRay_span_natCast :
    ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 →
      discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) →
      ∀ n : ℕ, 3 ≤ n → ∀ (R : IntermediateField K ℂ) [NumberField R] [IsAbelianGalois K R],
      _root_.GlobalTheory.FieldSize.IsRay R (Ideal.span {(n : 𝓞 K)}) → _root_.GlobalTheory.FieldSize.weberSet L n ⊆ R := by
  intro K _ _ h2 hd L hL n hn R _ _ hR
  obtain ⟨hM, S, hS⟩ := _root_.GlobalTheory.WeberSplitAny.splits_completely_of_three_le K h2 hd L hL n hn
  have hn0 : 0 < n := by omega
  have hN : Ideal.absNorm (Ideal.span {(n : 𝓞 K)}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn0.ne'
  have hMR : IntermediateField.adjoin (↥K) (_root_.GlobalTheory.FieldSize.weberSet L n) ≤ R := by
    apply _root_.GlobalTheory.Bauer.le_of_finite_split_not_split (↥K) ℂ R _
    refine ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K)
      (S.sup id + Ideal.absNorm (Ideal.span {(n : 𝓞 K)}))).preimage
      (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro 𝔭 ⟨hp, hsplit, hnot⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    by_cases hpS : Ideal.absNorm 𝔭.asIdeal ∈ S
    · exact le_add_right (Finset.le_sup (f := id) hpS)
    by_cases hn𝔭 : (n : 𝓞 K) ∈ 𝔭.asIdeal
    · refine le_add_left (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) ?_)
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hn𝔭)
    · exfalso
      obtain ⟨π, hπ, hπ1⟩ :=
        (_root_.GlobalTheory.FieldSize.RaySplit.ncard_eq_finrank_iff (↥K) (↥R) n hn0 hR 𝔭 hn𝔭).mp hsplit
      apply hnot
      rw [hπ] at hp hpS ⊢
      exact hS π _ hp hpS rfl hπ1
  exact fun x hx => hMR (IntermediateField.subset_adjoin _ _ hx)


set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField in
theorem _root_.GlobalTheory.FieldSize.InRayAny.weberSet_subset :
    ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 →
      discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) →
      ∀ n : ℕ, 3 ≤ n → ∀ (R : IntermediateField K ℂ) [NumberField R] [IsAbelianGalois K R],
      _root_.GlobalTheory.FieldSize.IsRay R (Ideal.span {(n : 𝓞 K)}) → _root_.GlobalTheory.FieldSize.weberSet L n ⊆ R :=
  weberSet_subset_of_isRay_span_natCast

end GlobalTheory.FieldSize.InRayAny
end

