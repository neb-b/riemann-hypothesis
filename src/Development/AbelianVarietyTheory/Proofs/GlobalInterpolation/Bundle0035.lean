module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassFamilyLogDerivReGtOne
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeierstrassPSuperlatticeHalfPeriodProd
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleProductTwoVariableTheta
section
open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.JacobiTriple

theorem tripleProduct : GlobalTheory.ThetaWeberRoad.TripleProduct := by
  intro τ z
  set s := cexp (π * I * (τ : ℂ)) with hs
  set x := cexp (2 * π * I * z) with hx
  have hτ : 0 < (τ : ℂ).im := τ.2
  have hs1 : ‖s‖ < 1 := norm_exp_pi_I_lt_one (τ : ℂ) hτ
  have hs0 : s ≠ 0 := exp_ne_zero _
  have hx0 : x ≠ 0 := exp_ne_zero _
  have ht1 : ‖s ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg s]
  obtain ⟨hP, hP0, -⟩ := qPoch_tendsto (s ^ 2) ht1
  have hT := _root_.GlobalTheory.JacobiTriple.tendsto_finCoeff_sum_jacobiTheta₂ (τ : ℂ) z hτ
  rw [(multipliable_tpFactor τ z).hasProd_iff_tendsto_nat]
  have key : ∀ n : ℕ, ∏ k ∈ Finset.range n, GlobalTheory.ThetaWeberRoad.tpFactor τ z k =
      qPoch (s ^ 2) n * ∑ j ∈ Finset.Icc (-(n : ℤ)) n,
        finCoeff (cexp (π * I * (τ : ℂ)) ^ 2) n j * jacobiTheta₂_term j z τ := by
    intro n
    rw [Finset.prod_congr rfl (fun k _ => tpFactor_eq τ z k), Finset.prod_mul_distrib]
    have hf := GlobalTheory.T.jacobiTriple_finite_product s x hs0 hs1 hx0 n
    simp only [hs, hx] at hf
    simp only [hf, jacobiTheta₂_term_eq_zpow]
    rfl
  simp_rw [key]
  have := hP.mul hT
  rwa [mul_left_comm, mul_inv_cancel₀ hP0, mul_one] at this

end GlobalTheory.JacobiTriple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassFamilyLogDerivReGtOneStatement
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one : ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (s : ℂ), 1 < s.re → LSeriesSummable (𝓕.lamChi χ) s ∧ ((s.re - 1) / s.re) ^ 2 ≤ ‖LSeries (𝓕.aChi χ) s‖ ∧ 𝓕.F χ s ≠ 0 ∧ -(deriv (𝓕.F χ) s / 𝓕.F χ s) + (if χ = 1 then 1 / (s - 1) else 0) = LSeries (𝓕.lamChi χ) s := by
  first | exact @GlobalTheory.Hk.LogDeriv.logDeriv_F | exact GlobalTheory.Hk.LogDeriv.logDeriv_F | (intros; apply GlobalTheory.Hk.LogDeriv.logDeriv_F <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceInfAlgebraMap
section
namespace GlobalTheory.TraceSumRealEmbeddings

open NumberField NumberField.InfinitePlace

theorem re_embedding_mk {F : Type} [Field F] (φ : F →+* ℂ) (x : F) :
    ((InfinitePlace.mk φ).embedding x).re = (φ x).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h <;> rw [h]
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]

theorem sum_re_embeddings (F : Type) [Field F] [NumberField F] (x : F) :
    ∑ φ : F →+* ℂ, (φ x).re = ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re := by
  classical
  rw [← Finset.univ.sum_fiberwise (fun φ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hw : ∀ φ ∈ ({φ | InfinitePlace.mk φ = w} : Finset (F →+* ℂ)), (φ x).re = (w.embedding x).re :=
    fun φ hφ => by rw [← (Finset.mem_filter.mp hφ).2, re_embedding_mk]
  rw [Finset.sum_congr rfl hw, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]

theorem trace_eq_sum_re (F : Type) [Field F] [NumberField F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ x).re := by
  have h2 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ x := by
    rw [Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ => φ x) (fun σ => σ x) (fun φ => rfl),
      ← trace_eq_sum_embeddings]
    exact (eq_ratCast (algebraMap ℚ ℂ) _).symm
  rw [← Complex.re_sum, ← h2, Complex.ratCast_re]

theorem traceInf_algebraMap (F : Type) [Field F] [NumberField F] (x : F) :
    GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf F (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) x) =
      ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  rw [trace_eq_sum_re, sum_re_embeddings]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 2
  rw [InfiniteAdeleRing.algebraMap_apply]
  simpa using InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)

end GlobalTheory.TraceSumRealEmbeddings
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeierstrassPSuperlatticeHalfPeriodProdStatement
section
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_superlattice_half_period_prod : ∀ (L L' : PeriodPair) (T : Finset ℂ) (w : ℂ), L.lattice ≤ L'.lattice → (∀ t ∈ T, t ∈ L'.lattice ∧ t ∉ L.lattice) → (∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ L.lattice → t = t') → (∀ x ∈ L'.lattice, x ∈ L.lattice ∨ ∃ t ∈ T, x - t ∈ L.lattice) → 2 * w ∈ L.lattice → w ∉ L'.lattice → ∀ z, z ∉ L'.lattice → (L'.weierstrassP z - L'.weierstrassP w) * ∏ t ∈ T, (L.weierstrassP z - L.weierstrassP t) = (L.weierstrassP z - L.weierstrassP w) * ∏ t ∈ T, (L.weierstrassP z - L.weierstrassP (w + t)) := by
  first | exact @GlobalTheory.HalfPeriodProduct.wp_half_period_prod | exact GlobalTheory.HalfPeriodProduct.wp_half_period_prod | (intros; apply GlobalTheory.HalfPeriodProduct.wp_half_period_prod <;> assumption)
end

