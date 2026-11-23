module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.StepRowsInverseNonzeroEntry
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.UnitComb

theorem coe_minorIJ {L : Type} [Field L] (V : ValuationSubring L) {N : ℕ}
    (h : Matrix (Fin N) (Fin N) V) (I J : Finset (Fin N)) :
    ((minorIJ h I J : V) : L) = minorIJ (h.map V.subtype) I J := by
  unfold minorIJ
  split_ifs with e
  · exact RingHom.map_det V.subtype _
  · rfl

theorem minorIJ_one_diag {R : Type} [CommRing R] {N : ℕ} (J : Finset (Fin N)) :
    minorIJ (1 : Matrix (Fin N) (Fin N) R) J J = 1 := by
  unfold minorIJ
  rw [dite_eq_left rfl, Matrix.submatrix_one _ (J.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem exists_isUnit_of_sum {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} (s : Finset ι)
    (f : ι → R) (h : IsUnit (∑ a ∈ s, f a)) : ∃ a ∈ s, IsUnit (f a) := by
  by_contra hc
  push_neg at hc
  have : ∑ a ∈ s, f a ∈ IsLocalRing.maximalIdeal R :=
    Ideal.sum_mem _ fun a ha => (IsLocalRing.mem_maximalIdeal _).2 (hc a ha)
  exact (IsLocalRing.mem_maximalIdeal _).1 this h

theorem stepCols_ne_empty {N j : ℕ} (i : Fin N) (hj : j ≤ N) : stepCols N j i ≠ ∅ := by
  have hi := i.2
  by_cases c : (i : ℕ) + 1 ≤ j
  · refine Finset.Nonempty.ne_empty ⟨⟨N - j, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos c]
    omega
  · refine Finset.Nonempty.ne_empty ⟨⟨0, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg c]
    omega

theorem unit_comb : ∀ (L : Type) [Field L] (V : ValuationSubring L) (N j : ℕ) (i : Fin N) (H : Matrix (Fin N) (Fin N) L) (κ : Type) [Fintype κ] (u : κ → Finset (Fin N) → L) (u' : Finset (Fin N) → κ → L), j ≤ N → IsBlockDiag j H → (∀ a b, H a b ∈ V) → H.det ≠ 0 → (H.det)⁻¹ ∈ V → (∀ I m, u' I m ∈ V) → (∀ m I, u m I ∈ V) → (∀ I I', IsStepRows N j i I → IsStepRows N j i I' → ∑ m, u' I m * u m I' = if I = I' then 1 else 0) → ∃ m, (∑ I, u m I * minorIJ H I (stepCols N j i)) ≠ 0 ∧ (∑ I, u m I * minorIJ H I (stepCols N j i))⁻¹ ∈ V := by
  intro L _ V N j i H κ _ u u' hj hB hH hdet hinv hu' hu horth
  let Hv : Matrix (Fin N) (Fin N) V := Matrix.of fun a b => ⟨H a b, hH a b⟩
  have hHv : Hv.map V.subtype = H := by ext a b; rfl
  let uv : κ → Finset (Fin N) → V := fun m I => ⟨u m I, hu m I⟩
  let uv' : Finset (Fin N) → κ → V := fun I m => ⟨u' I m, hu' I m⟩
  have hdetc : ((Hv.det : V) : L) = H.det := by
    have := RingHom.map_det V.subtype Hv
    rw [RingHom.mapMatrix_apply, hHv] at this
    exact this
  have hunit : IsUnit Hv.det := by
    refine IsUnit.of_mul_eq_one (⟨(H.det)⁻¹, hinv⟩ : V) ?_
    apply Subtype.ext
    change ((Hv.det : V) : L) * (H.det)⁻¹ = 1
    rw [hdetc, mul_inv_cancel₀ hdet]
  have main := _root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main V N j i hj
  have hJ := stepCols_ne_empty (j := j) i hj
  have hBv : IsBlockDiag j Hv := fun a b hab => Subtype.ext (hB a b hab)
  have hstep : ∀ I, ¬ IsStepRows N j i I → minorIJ Hv I (stepCols N j i) = 0 := fun I hI =>
    (main.2.1 Hv I hBv hI).resolve_right hJ
  have hsum1 : IsUnit (∑ I', minorIJ Hv⁻¹ (stepCols N j i) I' * minorIJ Hv I' (stepCols N j i)) := by
    rw [← main.1, Matrix.nonsing_inv_mul _ hunit, minorIJ_one_diag]
    exact isUnit_one
  obtain ⟨I₀, -, hI₀⟩ := exists_isUnit_of_sum _ _ hsum1
  have hI₀' : IsUnit (minorIJ Hv I₀ (stepCols N j i)) := isUnit_of_mul_isUnit_right hI₀
  have hI₀s : IsStepRows N j i I₀ := by
    by_contra hc
    rw [hstep I₀ hc] at hI₀'
    exact not_isUnit_zero hI₀'
  have horthV : ∀ I', IsStepRows N j i I' → ∑ m, uv' I₀ m * uv m I' = if I₀ = I' then 1 else 0 := by
    intro I' hI'
    apply Subtype.ext
    have := horth I₀ I' hI₀s hI'
    split_ifs at this ⊢ with e
    · simpa [uv, uv'] using this
    · simpa [uv, uv'] using this
  let w : κ → V := fun m => ∑ I, uv m I * minorIJ Hv I (stepCols N j i)
  have hw : ∑ m, uv' I₀ m * w m = minorIJ Hv I₀ (stepCols N j i) := by
    have e1 : ∑ m, uv' I₀ m * w m =
        ∑ I, (∑ m, uv' I₀ m * uv m I) * minorIJ Hv I (stepCols N j i) := by
      simp only [w, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc]
    rw [e1, Finset.sum_eq_single I₀]
    · rw [horthV I₀ hI₀s, if_pos rfl, one_mul]
    · intro b _ hb
      by_cases hs : IsStepRows N j i b
      · rw [horthV b hs, if_neg (Ne.symm hb), zero_mul]
      · rw [hstep b hs, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [← hw] at hI₀'
  obtain ⟨m, -, hm⟩ := exists_isUnit_of_sum _ _ hI₀'
  have hwm : IsUnit (w m) := isUnit_of_mul_isUnit_right hm
  have hcoe : ((w m : V) : L) = ∑ I, u m I * minorIJ H I (stepCols N j i) := by
    simp only [w, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, coe_minorIJ, hHv]
    rfl
  refine ⟨m, ?_, ?_⟩
  · rw [← hcoe]
    intro h0
    exact hwm.ne_zero (Subtype.ext h0)
  · obtain ⟨c, hc⟩ := hwm.exists_right_inv
    have hc' : ((w m : V) : L) * (c : L) = 1 := congrArg Subtype.val hc
    rw [← hcoe, inv_eq_of_mul_eq_one_right hc']
    exact c.2

end GlobalTheory.CompanionTheory.Ar.PB.UnitComb
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightDescendsOfSameOrbit
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA

private theorem grading_map_coeff_eq_monomial {K σ : Type} (s : σ → K)
    (φ : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial K (MvPolynomial σ ℤ))
    (hφ : ∀ q, φ (MvPolynomial.X q) = MvPolynomial.C (MvPolynomial.X q) * MvPolynomial.X (s q))
    (g : MvPolynomial σ ℤ) : ∀ a : K →₀ ℕ,
    φ ((φ g).coeff a) = MvPolynomial.monomial a ((φ g).coeff a) := by
  classical
  induction g using MvPolynomial.induction_on
  · rename_i r
    intro a
    have h1 : φ (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
      simpa [MvPolynomial.algebraMap_apply] using φ.commutes r
    rw [h1, MvPolynomial.coeff_C]
    split_ifs with h
    · subst h
      rw [h1, MvPolynomial.C_apply]
    · simp
  · rename_i f1 f2 hf hg
    intro a
    simp only [map_add (f := _), MvPolynomial.coeff_add, hf, hg]
  · rename_i f n hf
    intro a
    rw [map_mul φ f (MvPolynomial.X n), hφ, mul_left_comm, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_mul_X']
    split_ifs with h
    · have he : Finsupp.single (s n) 1 ≤ a := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp h)
      have hX : (MvPolynomial.X (s n) : MvPolynomial K (MvPolynomial σ ℤ)) =
          MvPolynomial.monomial (Finsupp.single (s n) 1) 1 := rfl
      rw [map_mul, hφ, hf, mul_assoc, hX, MvPolynomial.monomial_mul, MvPolynomial.C_mul_monomial,
        one_mul, add_tsub_cancel_of_le he]
    · simp

private theorem smul_mem_lemma_2 {K : Type} {ι : K → Type} {Φ : Type} [Field Φ]
    (y : (Σ k, ι k) → Φ) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ f ∈ mCoordIdeal y, MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0)
    (c : K → ℂ) (f : MRing ι) (hf : f ∈ mCoordIdeal y) :
    MvPolynomial.eval (fun r : (Σ k, ι k) => c r.1 * z r) (MvPolynomial.map (Int.castRingHom ℂ) f) = 0 := by
  classical
  let φ : MvPolynomial ((k : K) × ι k) ℤ →ₐ[ℤ] MvPolynomial K (MvPolynomial ((k : K) × ι k) ℤ) :=
    MvPolynomial.aeval (fun q => MvPolynomial.C (MvPolynomial.X q) * MvPolynomial.X q.1)
  have hφ : ∀ q, φ (MvPolynomial.X q) = MvPolynomial.C (MvPolynomial.X q) * MvPolynomial.X q.1 :=
    fun q => MvPolynomial.aeval_X _ _
  have hA : ∀ g, mConeMap y g =
      MvPolynomial.map (MvPolynomial.aeval (R := ℤ) y).toRingHom (φ g) := by
    intro g
    have key : (mConeMap y : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial K Φ) =
        ((MvPolynomial.map (MvPolynomial.aeval (R := ℤ) y).toRingHom).toIntAlgHom).comp φ := by
      apply MvPolynomial.algHom_ext
      intro q
      show mConeMap y (MvPolynomial.X q) =
        MvPolynomial.map (MvPolynomial.aeval (R := ℤ) y).toRingHom (φ (MvPolynomial.X q))
      rw [hφ]
      simp [mConeMap]
    rw [key]
    rfl
  have hf' : mConeMap y f = 0 := RingHom.mem_ker.mp hf
  have hcomp : ∀ a, (φ f).coeff a ∈ mCoordIdeal y := by
    intro a
    have h1 : (MvPolynomial.aeval (R := ℤ) y).toRingHom ((φ f).coeff a) = 0 := by
      have := congrArg (AddMonoidAlgebra.coeff · a) (hA f)
      rw [hf', MvPolynomial.coeff_zero, MvPolynomial.coeff_map] at this
      exact this.symm
    show (φ f).coeff a ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker, hA, grading_map_coeff_eq_monomial Sigma.fst φ hφ f a, MvPolynomial.map_monomial, h1,
      map_zero]
  have hB : MvPolynomial.eval (fun r : (Σ k, ι k) => c r.1 * z r) (MvPolynomial.map (Int.castRingHom ℂ) f) =
      MvPolynomial.eval c (MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom (φ f)) := by
    rw [MvPolynomial.eval_map, ← algebraMap_int_eq, ← MvPolynomial.aeval_def]
    have key : (MvPolynomial.aeval (R := ℤ) (fun r : (Σ k, ι k) => c r.1 * z r)) =
        ((MvPolynomial.eval c).toIntAlgHom).comp
          (((MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom).toIntAlgHom).comp φ) := by
      apply MvPolynomial.algHom_ext
      intro q
      show MvPolynomial.aeval (R := ℤ) (fun r : (Σ k, ι k) => c r.1 * z r) (MvPolynomial.X q) =
        MvPolynomial.eval c (MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom (φ (MvPolynomial.X q)))
      rw [hφ]
      simp [mul_comm]
    rw [key]
    rfl
  rw [hB]
  have hzero : MvPolynomial.map (MvPolynomial.aeval (R := ℤ) z).toRingHom (φ f) = 0 := by
    ext a
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
    have := hz _ (hcomp a)
    rwa [MvPolynomial.eval_map, ← algebraMap_int_eq, ← MvPolynomial.aeval_def] at this
  rw [hzero, map_zero]

theorem weight_descends_of_sameOrbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (e e' : ℕ)
    (R : AnLogRes (mCoordIdeal y) ⊤ e) (Rp : AnLogRes (mCoordIdeal (y ∘ stepV M p)) ⊤ e') (h : R.X → Rp.X)
    (A B : HermLine ι) (ph : Rp.X → ℝ) (W : Set Rp.X), A.a = B.a →
    (∀ x, SameOrbit (Rp.lift (h x) (h x)) (R.lift x x ∘ stepV M p)) →
    (∀ x ∈ W, ∀ z ∈ mcPts (mCoordIdeal y), z ∘ stepV M p = Rp.lift x x →
      Real.log (A.h z) = Real.log (B.h z) + ph x) →
    ∀ x, h x ∈ W → Real.log (A.h (R.lift x x)) = Real.log (B.h (R.lift x x)) + ph (h x) := by
  intro K _ ι _ Φ _ y Ψ N j M p e e' R Rp h A B ph W hab horb hW x hx
  classical
  obtain ⟨c, hc0, hceq⟩ := horb x
  have hwmem : R.lift x x ∈ mcPts (mCoordIdeal y) := R.mem x x (R.mem_U x)
  let c' : K → ℂ := fun k =>
    if hk : ((∀ p' : Ψ × Fin N, M.blk p' ≠ Option.some k) ∨ M.blk p = Option.some k) then c ⟨k, hk⟩ else 1
  have hc'0 : ∀ k, c' k ≠ 0 := by
    intro k
    by_cases hk : ((∀ p' : Ψ × Fin N, M.blk p' ≠ Option.some k) ∨ M.blk p = Option.some k)
    · simp only [c', dif_pos hk]
      exact hc0 _
    · simp only [c', dif_neg hk]
      exact one_ne_zero
  let z : (Σ k, ι k) → ℂ := fun r => c' r.1 * R.lift x x r
  have hzstep : z ∘ stepV M p = Rp.lift (h x) (h x) := by
    rw [hceq]
    funext q
    have hq : (∀ p' : Ψ × Fin N, M.blk p' ≠ Option.some q.1.1) ∨ M.blk p = Option.some q.1.1 := q.1.2
    show c' q.1.1 * R.lift x x ⟨q.1.1, q.2⟩ = c q.1 * R.lift x x ⟨q.1.1, q.2⟩
    congr 1
    simp only [c', dif_pos hq]
  have hzmem : z ∈ mcPts (mCoordIdeal y) := by
    refine ⟨fun k => ?_, fun f hf => ?_⟩
    · obtain ⟨i, hi⟩ := hwmem.1 k
      exact ⟨i, mul_ne_zero (hc'0 k) hi⟩
    · exact smul_mem_lemma_2 y (R.lift x x) hwmem.2 c' f hf
  have key := hW (h x) hx z hzmem hzstep
  have hAz : A.h z = (∏ k, ‖c' k‖ ^ A.a k) * A.h (R.lift x x) := A.smul c' _ hc'0
  have hBz : B.h z = (∏ k, ‖c' k‖ ^ A.a k) * B.h (R.lift x x) := by
    rw [hab]
    exact B.smul c' _ hc'0
  have hP : (∏ k, ‖c' k‖ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc'0 k)))
  have hApos := A.pos _ hwmem.1
  have hBpos := B.pos _ hwmem.1
  rw [hAz, hBz, Real.log_mul hP hApos.ne', Real.log_mul hP hBpos.ne'] at key
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.FA
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.WordCoefficientSecondDerivative
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN.WordProd

theorem pderiv_comm {σ : Type*} (a b : σ) (P : MvPolynomial σ ℝ) :
    pderiv a (pderiv b P) = pderiv b (pderiv a P) := by
  have h : ⁅(pderiv a : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)),
      (pderiv b : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    classical
    have hc : ∀ c : σ, pderiv (R := ℝ) c (X i) = if i = c then 1 else 0 := fun c => by
      rw [pderiv_X, Pi.single_apply]
    simp only [Derivation.commutator_apply, hc, Derivation.coe_zero, Pi.zero_apply]
    split_ifs <;> simp
  have h2 := congrArg (fun D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ) => D P) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using h2

theorem pderiv_some_rename_mul (j : Fin 2) (P : MvPolynomial (Fin 2) ℝ) (m : ℕ) :
    pderiv (some j) (rename some P * (X none : MvPolynomial (Option (Fin 2)) ℝ) ^ m) =
      rename some (pderiv j P) * X none ^ m := by
  have h0 : pderiv (some j) ((X none : MvPolynomial (Option (Fin 2)) ℝ) ^ m) = 0 := by
    simp [Derivation.leibniz_pow, pderiv_X, Pi.single_apply]
  rw [Derivation.leibniz, h0, pderiv_rename (Option.some_injective _)]
  simp [mul_comm]

theorem evalW_rename (n₀ n₁ : Fin 3 → ℝ) (P : MvPolynomial (Fin 2) ℝ) :
    evalW n₀ n₁ (rename some P) = rename some (aeval ![lin3 n₀, lin3 n₁] P) := by
  have h : ((evalW n₀ n₁).comp (rename some) : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] _) =
      (rename some).comp (aeval ![lin3 n₀, lin3 n₁]) := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;> simp [evalW, lin4]
  exact DFunLike.congr_fun h P

theorem prod_rows_word (d k i : ℕ) (hk : 2 * k ≤ d + 2) :
    (∏ r : Fin (d + 2),
      rowW (if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0)
        (if (r : ℕ) < 2 * k then 0 else 1)) =
    rename some (wwLinProd k (DiagonalFibreFubini.wordCoef i)) * X none ^ (d + 2 - 2 * k) := by
  rw [Fin.prod_univ_eq_prod_range (fun r : ℕ =>
    rowW (if r < 2 * k then DiagonalFibreFubini.wordCoef i r else 0) (if r < 2 * k then 0 else 1)) (d + 2)]
  obtain ⟨m, hm⟩ : ∃ m, d + 2 = 2 * k + m := ⟨d + 2 - 2 * k, by omega⟩
  rw [hm, Finset.prod_range_add, show 2 * k + m - 2 * k = m by omega]
  congr 1
  · rw [wwLinProd, map_prod]
    refine Finset.prod_congr rfl fun n hn => ?_
    have hn' : n < 2 * k := Finset.mem_range.mp hn
    simp [rowW, hn']
  · rw [Finset.prod_congr rfl (g := fun _ => (X none : MvPolynomial (Option (Fin 2)) ℝ))]
    · simp
    · intro x _
      simp [rowW]

theorem evalW_pderiv_prod_rows_word : ∀ (d k i : ℕ), i < k → 2 * k ≤ d + 2 → ∀ n₀ n₁ : Fin 3 → ℝ,
    evalW n₀ n₁ (pderiv (some 1) (pderiv (some 0) (∏ r : Fin (d + 2),
      rowW (if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0)
        (if (r : ℕ) < 2 * k then 0 else 1)))) =
    rename some (aeval ![lin3 n₀, lin3 n₁]
      (pderiv 0 (pderiv 1 (wwLinProd k (DiagonalFibreFubini.wordCoef i))))) * X none ^ (d + 2 - 2 * k) := by
  intro d k i _ hk n₀ n₁
  rw [prod_rows_word d k i hk, pderiv_some_rename_mul, pderiv_some_rename_mul, map_mul, evalW_rename,
    pderiv_comm 1 0, map_pow]
  congr 1
  simp [evalW]

end GlobalTheory.CompanionTheory.Ar.PB.FibN.WordProd
end

