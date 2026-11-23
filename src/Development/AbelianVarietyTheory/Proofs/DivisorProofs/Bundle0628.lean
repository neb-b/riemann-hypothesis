module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0608
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstIsogeny
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0024
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameInvariantEqZeroOfTauDvd
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TauUniq

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} (F : BFrame ε)

theorem p_cancel {b c : F.B} (h : (p : F.B) * b = p * c) : b = c := by
  have h1 := congrArg (algebraMap F.B F.Q) h
  simp only [map_mul, map_natCast] at h1
  exact F.frame.inj (F.frame.unit_p.mul_left_cancel h1)

theorem frob_teich (x : PreTilt O p) :
    WittVector.frobenius (WittVector.teichmuller p x) = WittVector.teichmuller p x ^ p := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem sigma_tau : F.σ F.τ = p * F.τ := by
  apply p_cancel F
  have hS : WittVector.frobenius (Sandwich.mu ε) =
      Sandwich.mu ε * ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i := by
    unfold Sandwich.mu
    rw [map_sub, map_one, frob_teich, mul_comm, geom_sum_mul]
  have hd : Sandwich.mu ε ∣ ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i - (p : Ainf p O) := by
    have : ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i - (p : Ainf p O) =
        ∑ i ∈ Finset.range p, (WittVector.teichmuller p ε ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [this]
    apply Finset.dvd_sum
    intro i _
    simpa [Sandwich.mu, one_pow] using sub_dvd_pow_sub_pow (WittVector.teichmuller p ε) 1 i
  have h0 := (F.τ_mul _).2 hd
  rw [map_sub, map_natCast] at h0
  have h1 : (p : F.B) * F.σ F.τ = F.a (WittVector.frobenius (Sandwich.mu ε)) := by
    rw [← F.σ_a, ← F.p_τ, map_mul, map_natCast]
  rw [h1, hS, map_mul, ← F.p_τ]
  linear_combination (p : F.B) * h0

theorem theta_tau [IsDomain O] : F.θ F.τ = 0 :=
  mul_self_eq_zero.1 (by rw [← map_mul, F.τ_sq, map_zero])

theorem dvd_tau {b : F.B} (h : F.τ ∣ b) : ∃ x, b = F.τ * F.a x := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨x, y, rfl⟩ := F.gen c
  exact ⟨x, by rw [mul_add, ← mul_assoc, F.τ_sq, zero_mul, add_zero]⟩

theorem lift_exists {ι : Type} (M : Matrix ι ι F.B) :
    ∃ m : Matrix ι ι (Ainf p O), ∀ i j, F.τ ∣ M i j - F.a (m i j) := by
  choose x y h using fun i j => F.gen (M i j)
  exact ⟨Matrix.of x, fun i j => ⟨F.a (y i j), by rw [h i j, Matrix.of_apply]; ring⟩⟩

theorem step {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (m : Matrix ι ι (Ainf p O))
    (hm : ∀ i j, F.τ ∣ M i j - F.a (m i j)) (u : ι → F.B) (u' : ι → Ainf p O)
    (hu : ∀ j, F.τ ∣ u j - F.a (u' j)) (i : ι) :
    F.τ ∣ M.mulVec (fun j => F.σ (u j)) i -
      F.a (m.mulVec (fun j => WittVector.frobenius (u' j)) i) := by
  have hI : Ideal.span {F.τ} ≤ (Ideal.span {F.τ}).comap F.σ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, sigma_tau]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  simp only [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq] at hm hu ⊢
  have hs : ∀ j, Ideal.Quotient.mk (Ideal.span {F.τ}) (F.σ (u j)) =
      Ideal.Quotient.mk (Ideal.span {F.τ}) (F.a (WittVector.frobenius (u' j))) := by
    intro j
    rw [← F.σ_a, ← Ideal.quotientMap_mk (H := hI), hu j, Ideal.quotientMap_mk]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [hm i j, hs j]

theorem iter {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (m : Matrix ι ι (Ainf p O))
    (hm : ∀ i j, F.τ ∣ M i j - F.a (m i j)) (w : ι → Ainf p O) (n : ℕ) (i : ι) :
    F.τ ∣ (fun v : ι → F.B => M.mulVec fun j => F.σ (v j))^[n] (fun j => F.a (w j)) i -
      F.a ((fun v : ι → Ainf p O => m.mulVec fun j => WittVector.frobenius (v j))^[n] w i) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact step F M m hm _ _ ih i

theorem nil_lift [IsDomain O] {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (m : Matrix ι ι (Ainf p O))
    (hm : ∀ i j, F.τ ∣ M i j - F.a (m i j)) (hM : IsNil F.θ F.σ M) :
    IsNil (WittVector.fontaineTheta O p) (WittVector.frobenius : Ainf p O →+* Ainf p O) m := by
  obtain ⟨N, hN⟩ := hM
  refine ⟨N, fun w i hu => hN (fun j => F.a (w j)) i ?_⟩
  obtain ⟨c, hc⟩ := iter F M m hm w N i
  rw [sub_eq_iff_eq_add] at hc
  rw [hc, map_add (f := _), map_mul, theta_tau, zero_mul, zero_add, F.θ_a]
  exact hu

theorem core (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    [Algebra O C] [IsDomain O] (hv : v.Integers O) (hε : IsPrimitiveSystem ε) {ι : Type} [Fintype ι]
    (M : Matrix ι ι F.B) (hM : IsNil F.θ F.σ M) (z : ι → Ainf p O)
    (hz : ∀ i, F.τ * F.a (z i) = F.τ * M.mulVec (fun j => F.σ (F.a (z j))) i) (i : ι) :
    F.τ * F.a (z i) = 0 := by
  obtain ⟨m, hm⟩ := lift_exists F M
  have key : ∀ i, Sandwich.mu ε ∣ z i - m.mulVec (fun j => WittVector.frobenius (z j)) i := by
    intro i
    rw [← F.τ_mul, map_sub, mul_sub, hz i]
    obtain ⟨c, hc⟩ := step F M m hm (fun j => F.a (z j)) z (fun j => by simp) i
    rw [sub_eq_iff_eq_add] at hc
    rw [hc, mul_add, ← mul_assoc, F.τ_sq, zero_mul, zero_add, sub_self]
  exact (F.τ_mul _).2 ((GlobalTheory.T.ainf_frobenius_semilinear_equation_existsUnique p C v O hv ε hε ι m (nil_lift F M m hm hM)).2 z key i)

theorem vec_eq {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (g : ι → F.B) (z : ι → Ainf p O)
    (hz : ∀ i, g i = F.τ * F.a (z i))
    (hg : ∀ i, M.mulVec (fun j => F.σ (g j)) i = (p : F.B) * g i) (i : ι) :
    F.τ * F.a (z i) = F.τ * M.mulVec (fun j => F.σ (F.a (z j))) i := by
  apply p_cancel F
  have e := hg i
  simp only [Matrix.mulVec, dotProduct, hz, map_mul, sigma_tau F] at e
  rw [← e]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem blk_mul_blk (d k : ℕ) (R : Type) [CommRing R] (u : R) :
    blk d k 1 u * blk d k u 1 = u • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) R) := by
  rw [blk, blk, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
  congr 1
  funext i
  rcases i with i | i <;> simp

theorem eq_zero_of_tau_dvd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), IsUnit U → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → (∀ Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B, Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y → (∀ i m, F.τ ∣ Y i m) → Y = 0) ∧ ∀ g : Fin d ⊕ Fin k → F.B, Matrix.mulVec (U * blk d k (p : F.B) 1) (fun i => F.σ (g i)) = (p : F.B) • g → (∀ i, F.τ ∣ g i) → g = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h U hU hN1 hN2
  have hdet : IsUnit U.transpose.det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det U).1 hU
  refine ⟨fun Y hY hdiv => ?_, fun g hg hdiv => ?_⟩
  · choose z hz using fun i c => dvd_tau F (hdiv i c)
    have hM : U.transpose⁻¹ * blk d k 1 (p : F.B) * Y.map F.σ = (p : F.B) • Y := by
      rw [hY, Matrix.mul_assoc, ← Matrix.mul_assoc (blk d k 1 (p : F.B)),
        ← Matrix.mul_assoc (blk d k 1 (p : F.B)), blk_mul_blk, Matrix.smul_mul, Matrix.one_mul,
        Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
        Matrix.one_mul]
    ext i c
    rw [hz i c, Matrix.zero_apply]
    refine core F C v hv hε _ hN1 (fun j => z j c)
      (vec_eq F _ (fun j => Y j c) (fun j => z j c) (fun j => hz j c) (fun i => ?_)) i
    have e := congrArg (fun X => X i c) hM
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using e
  · choose z hz using fun i => dvd_tau F (hdiv i)
    funext i
    rw [hz i, Pi.zero_apply]
    exact core F C v hv hε _ hN2 z
      (vec_eq F _ g z hz (fun i => by simpa using congrFun hg i)) i

end GlobalTheory.TauUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicNormalizedWeierstrassValuesCm
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.AlgebraicitySecondEisenstein

theorem main : ∀ (L : PeriodPair) (β Ω : ℂ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L →
    IsAlgebraic ℚ (s2 L / Ω ^ 2) ∧ ∀ (M : ℕ) (P : ℂ), 0 < M → (M : ℂ) * P ∈ L.lattice →
      IsAlgebraic ℚ (L.weierstrassP P / Ω ^ 2) ∧ IsAlgebraic ℚ (L.derivWeierstrassP P / Ω ^ 3) := by
  intro L β Ω hst him hΩ
  have alg : ∀ x : ℂ, IsAlgebraic ℚ x ↔ x ∈ algebraicClosure ℚ ℂ := fun x => mem_algebraicClosure_iff.symm
  have intAlg : ∀ x : ℂ, IsIntegral ℤ x → x ∈ algebraicClosure ℚ ℂ := fun x hx =>
    (alg x).1 (hx.tower_top (A := ℚ)).isAlgebraic
  have natMem : ∀ k : ℕ, (k : ℂ) ∈ algebraicClosure ℚ ℂ := fun k => natCast_mem _ k
  have part2 : ∀ (M : ℕ) (P : ℂ), 0 < M → (M : ℂ) * P ∈ L.lattice →
      IsAlgebraic ℚ (L.weierstrassP P / Ω ^ 2) ∧ IsAlgebraic ℚ (L.derivWeierstrassP P / Ω ^ 3) := by
    intro M P hM hP
    obtain ⟨h1, -⟩ := _root_.GlobalTheory.WpFam.LatTorsVal.main L β Ω M hst him hΩ hM
    obtain ⟨i1, i2⟩ := h1 P hP
    have a1 := intAlg _ i1
    have a2 := intAlg _ i2
    have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [mul_div_assoc] at a1 a2
    have c1 : (12 * (M : ℂ) ^ 2) = ((12 * M ^ 2 : ℕ) : ℂ) := by push_cast; ring
    have c2 : ((M : ℂ) ^ 3) = ((M ^ 3 : ℕ) : ℂ) := by push_cast; ring
    have n1 : (12 * (M : ℂ) ^ 2) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hMc)
    have n2 : ((M : ℂ) ^ 3) ≠ 0 := pow_ne_zero _ hMc
    constructor
    · rw [alg]
      have := div_mem a1 (c1 ▸ natMem (12 * M ^ 2))
      rwa [mul_div_cancel_left₀ _ n1] at this
    · rw [alg]
      have := div_mem a2 (c2 ▸ natMem (M ^ 3))
      rwa [mul_div_cancel_left₀ _ n2] at this
  refine ⟨?_, part2⟩
  have hβ0 : β ≠ 0 := by rintro rfl; simp at him
  obtain ⟨S, hS⟩ := kernel_reps_exist L β hβ0 hst
  have hcard := kernel_reps_card L β S hβ0 hst hS
  obtain ⟨t, n, ht, hn, hq⟩ := mul_stable_integral L β hst
  have hs2 := cm_s2 L β S hst him hS
  have hconj : MulStable L (conj β) := fun ω hω => by
    have e : conj β * ω = t • ω - β * ω := by rw [zsmul_eq_mul, ← ht]; ring
    rw [e]
    exact sub_mem (Submodule.smul_mem _ t hω) (hst ω hω)
  have hM : ((S.card + 1 : ℕ) : ℂ) = conj β * β := by
    rw [← Complex.normSq_eq_conj_mul_self]
    have := congrArg (fun r : ℝ => (r : ℂ)) hcard
    push_cast at this ⊢
    exact this
  have hP : ∀ P ∈ S, L.weierstrassP P / Ω ^ 2 ∈ algebraicClosure ℚ ℂ := fun P hP => by
    have hmem : ((S.card + 1 : ℕ) : ℂ) * P ∈ L.lattice := by
      rw [hM, mul_assoc]; exact hconj _ (hS.1 P hP).1
    exact (alg _).1 (part2 _ P (Nat.succ_pos _) hmem).1
  have hβint : IsIntegral ℤ β := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
    · monicity!
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      simpa using hq
  have hβm := intAlg _ hβint
  have hcm : conj β ∈ algebraicClosure ℚ ℂ := by
    have e : conj β = (t : ℂ) - β := by rw [← ht]; ring
    rw [e]; exact sub_mem (intCast_mem _ t) hβm
  rw [alg, hs2, div_div, mul_comm (β * _), ← div_div, Finset.sum_div]
  exact div_mem (sum_mem hP) (mul_mem hβm (sub_mem hβm hcm))

end GlobalTheory.AlgebraicitySecondEisenstein
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AssocEvalStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEval_comul_assoc_of_isEval : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : A ⊗[O] (A ⊗[O] A))}) (A ⊗[O] (A ⊗[O] A))] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (E₃ : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O →ₐ[O] A ⊗[O] (A ⊗[O] A)) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → (∀ i, constantCoeff (μ i) = 0) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A ⊗[O] A)) (Sum.elim (fun i => (1 : A) ⊗ₜ[O] (x i ⊗ₜ[O] (1 : A))) fun i => (1 : A) ⊗ₜ[O] ((1 : A) ⊗ₜ[O] x i))) E₃ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, E₃ (op μ (op μ x1 x2) x3 i) = E₃ (op μ x1 (op μ x2 x3) i) := by
  first | exact @GlobalTheory.Chart.Assoc.assoc_eval | exact GlobalTheory.Chart.Assoc.assoc_eval | (intros; apply GlobalTheory.Chart.Assoc.assoc_eval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtlasSectionsMulDivNonvanishingIsOpen
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem sections_prod_quot_open : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), (∀ (la mu : La) (a b : ι → Y → ℂ), A.IsSec la a → A.IsSec mu b → A.IsSec (la + mu) (fun i y => a i y * b i y) ∧ ∀ y, A.nsq (la + mu) (fun i y => a i y * b i y) y = A.nsq la a y * A.nsq mu b y) ∧ (∀ (la : La) (a : ι → Y → ℂ), A.IsSec la a → IsOpen (nz A a)) ∧ (∀ (B la : La) (a b : ι → Y → ℂ) (U : Set Y), A.IsSec (B + la) a → A.IsSec B b → (∀ y ∈ U, a (A.pick y) y ≠ 0 ∧ b (A.pick y) y ≠ 0) → A.IsFrameOn la U (fun i y => a i y / b i y)) := by
  intro n Y _ _ _ _ _ ι La _ A
  refine ⟨?_, ?_, ?_⟩
  · intro la mu a b ha hb
    refine ⟨⟨fun i => ?_, fun i j y _ hi hj => ?_⟩, fun y => ?_⟩
    · exact (ha.1 i).mul (hb.1 i)
    · beta_reduce
      rw [A.g_add la mu i j y hi hj, ha.2 i j y trivial hi hj, hb.2 i j y trivial hi hj]
      ring
    · simp only [WeightedAtlas.nsq]
      rw [A.ph_add la mu _ y (A.mem_pick y), norm_mul, mul_pow, neg_add, Real.exp_add]
      ring
  · intro la a ha
    have hc : Continuous (A.nsq la a) := bsA_nsq_cont A ha
    have : nz A a = A.nsq la a ⁻¹' {0}ᶜ := by
      ext y
      simp only [nz, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff, WeightedAtlas.nsq]
      constructor
      · intro h
        exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr h)) (Real.exp_pos _).ne'
      · intro h h0
        apply h
        simp [h0]
    rw [this]
    exact isOpen_compl_singleton.preimage hc
  · intro B la a b U ha hb hU
    have hbne : ∀ i y, y ∈ U → y ∈ (A.chart i).source → b i y ≠ 0 := by
      intro i y hy hi
      rw [hb.2 i (A.pick y) y trivial hi (A.mem_pick y)]
      exact mul_ne_zero (A.g_ne B i (A.pick y) y hi (A.mem_pick y)) (hU y hy).2
    refine ⟨⟨fun i => ?_, fun i j y hy hi hj => ?_⟩, fun y hy => div_ne_zero (hU y hy).1 (hU y hy).2⟩
    · have hS : (A.chart i).target ∩ (A.chart i).symm ⁻¹' U ⊆
          (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ := fun v hv => ⟨hv.1, trivial⟩
      have h1 : DifferentiableOn ℂ (a i ∘ (A.chart i).symm)
          ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (ha.1 i).mono hS
      have h2 : DifferentiableOn ℂ (b i ∘ (A.chart i).symm)
          ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (hb.1 i).mono hS
      have h3 := h1.mul (h2.inv (fun v (hv : v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U) =>
        hbne i _ hv.2 ((A.chart i).map_target hv.1)))
      refine h3.congr (fun v _ => ?_)
      simp [div_eq_mul_inv]
    · have hgB := A.g_ne B i j y hi hj
      have hbj := hbne j y hy hj
      beta_reduce
      rw [ha.2 i j y trivial hi hj, hb.2 i j y trivial hi hj, A.g_add B la i j y hi hj]
      field_simp

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BallExistsEtaleSteinExhaustion
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.BallStein

variable {n : ℕ}

noncomputable def sqd (c : V n) (y : V n) : ℝ := ‖y - c‖ ^ 2

theorem contDiff_sqd (c : V n) : ContDiff ℝ ∞ (sqd c) :=
  (contDiff_norm_sq ℂ).comp (contDiff_id.sub contDiff_const)

theorem sqd_lt {c y : V n} {r : ℝ} (hy : y ∈ ball c r) : sqd c y < r ^ 2 := by
  have h1 : ‖y - c‖ < r := by simpa [dist_eq_norm] using hy
  have h0 : 0 ≤ ‖y - c‖ := norm_nonneg _
  unfold sqd
  nlinarith

theorem hasDerivAt_k (r t : ℝ) (ht : t < r ^ 2) :
    HasDerivAt (fun t : ℝ => (r ^ 2 - t)⁻¹) (((r ^ 2 - t) ^ 2)⁻¹) t := by
  have hne : r ^ 2 - t ≠ 0 := by linarith
  have := ((hasDerivAt_id t).const_sub (r ^ 2)).inv hne
  refine this.congr_deriv ?_
  simp only [id]
  ring

theorem hasDerivAt_k' (r t : ℝ) (ht : t < r ^ 2) :
    HasDerivAt (fun t : ℝ => ((r ^ 2 - t) ^ 2)⁻¹) (2 * (r ^ 2 - t) / ((r ^ 2 - t) ^ 2) ^ 2) t := by
  have hne : (r ^ 2 - t) ^ 2 ≠ 0 := by
    have : r ^ 2 - t ≠ 0 := by linarith
    positivity
  have h1 := (((hasDerivAt_id t).const_sub (r ^ 2)).pow 2).inv hne
  refine h1.congr_deriv ?_
  simp only [id, Pi.pow_apply]
  norm_num

theorem deriv_k (r t : ℝ) (ht : t < r ^ 2) :
    deriv (fun t : ℝ => (r ^ 2 - t)⁻¹) t = ((r ^ 2 - t) ^ 2)⁻¹ :=
  (hasDerivAt_k r t ht).deriv

theorem deriv_deriv_k (r t : ℝ) (ht : t < r ^ 2) :
    deriv (deriv (fun t : ℝ => (r ^ 2 - t)⁻¹)) t = 2 * (r ^ 2 - t) / ((r ^ 2 - t) ^ 2) ^ 2 := by
  have hev : deriv (fun t : ℝ => (r ^ 2 - t)⁻¹) =ᶠ[𝓝 t] fun t : ℝ => ((r ^ 2 - t) ^ 2)⁻¹ := by
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact deriv_k r u hu
  rw [hev.deriv_eq]
  exact (hasDerivAt_k' r t ht).deriv

theorem leviV_sqd_nonneg (c x : V n) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun y => ((sqd c y : ℝ) : ℂ)) x ξ).re := by
  let u : Fin n → V n → ℝ := fun j y => Complex.normSq (EuclideanSpace.proj j (y - c))
  have hfun : (fun y => ((sqd c y : ℝ) : ℂ)) = fun y => ((∑ j, u j y : ℝ) : ℂ) := by
    funext y
    congr 1
    simp only [sqd, u, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]
    rfl
  have hg : ∀ j : Fin n, ContDiffAt ℂ 2 (fun y : V n => EuclideanSpace.proj j (y - c)) x := fun j =>
    ((EuclideanSpace.proj j : V n →L[ℂ] ℂ).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hu : ∀ j, ContDiffAt ℝ 2 (u j) x := fun j => by
    have hu' : u j = fun y => ‖EuclideanSpace.proj j (y - c)‖ ^ 2 := by
      funext y; simp only [u, Complex.normSq_eq_norm_sq]
    rw [hu']
    exact (contDiff_norm_sq ℂ).contDiffAt.comp x ((hg j).restrict_scalars ℝ)
  rw [hfun, leviV_ofReal_sum hu, Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => ((logPshAt_normSq (hg j)).2 ξ).1

end GlobalTheory.BallStein

namespace GlobalTheory.BallStein

variable {n : ℕ}

noncomputable def exh (c : V n) (r : ℝ) (y : V n) : ℝ := (r ^ 2 - sqd c y)⁻¹

theorem contDiffOn_exh (c : V n) (r : ℝ) : ContDiffOn ℝ ∞ (exh c r) (ball c r) :=
  (contDiffOn_const.sub (contDiff_sqd c).contDiffOn).inv fun _ hy => (sub_pos.2 (sqd_lt hy)).ne'

theorem leviV_exh_nonneg {c y : V n} {r : ℝ} (hy : y ∈ ball c r) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun w => ((exh c r w : ℝ) : ℂ)) y ξ).re := by
  have hlt := sqd_lt hy
  have hp : 0 < r ^ 2 - sqd c y := sub_pos.2 hlt
  have hk : ContDiffAt ℝ 2 (fun t : ℝ => (r ^ 2 - t)⁻¹) (sqd c y) :=
    (contDiffAt_const.sub contDiffAt_id).inv hp.ne'
  have hc := leviChain n (fun t : ℝ => (r ^ 2 - t)⁻¹) (sqd c) y ξ
    (((contDiff_norm_sq ℂ).comp (contDiff_id.sub contDiff_const) : ContDiff ℝ 2 (sqd c)).contDiffAt) hk
  have he : (fun w => ((exh c r w : ℝ) : ℂ)) =
      fun w => (((fun t : ℝ => (r ^ 2 - t)⁻¹) (sqd c w) : ℝ) : ℂ) := rfl
  rw [he, hc, deriv_k r _ hlt, deriv_deriv_k r _ hlt]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  have h1 := leviV_sqd_nonneg c y ξ
  have h2 := Complex.normSq_nonneg (∑ j, wd n j (fun w => ((sqd c w : ℝ) : ℂ)) y * ξ j)
  refine add_nonneg (mul_nonneg (by positivity) h1) (mul_nonneg (by positivity) h2)

theorem isCompact_exh (c : V n) (r a : ℝ) : IsCompact {y | y ∈ ball c r ∧ exh c r y ≤ a} := by
  by_cases hr : r ≤ 0
  · have : {y | y ∈ ball c r ∧ exh c r y ≤ a} = ∅ := by
      ext y; simp [Metric.ball_eq_empty.2 hr]
    rw [this]; exact isCompact_empty
  push_neg at hr
  by_cases ha : a ≤ 0
  · have : {y | y ∈ ball c r ∧ exh c r y ≤ a} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
      intro hy
      have hp : 0 < r ^ 2 - sqd c y := sub_pos.2 (sqd_lt hy)
      exact lt_of_le_of_lt ha (inv_pos.2 hp)
    rw [this]; exact isCompact_empty
  push_neg at ha
  have heq : {y | y ∈ ball c r ∧ exh c r y ≤ a} = {y | sqd c y ≤ r ^ 2 - a⁻¹} := by
    ext y
    simp only [Set.mem_setOf_eq, exh]
    constructor
    · rintro ⟨hy, hle⟩
      have hp : 0 < r ^ 2 - sqd c y := sub_pos.2 (sqd_lt hy)
      have := (inv_le_comm₀ hp ha).1 hle
      linarith
    · intro hle
      have hai : 0 < a⁻¹ := inv_pos.2 ha
      have hp : 0 < r ^ 2 - sqd c y := by linarith
      refine ⟨?_, (inv_le_comm₀ hp ha).2 (by linarith)⟩
      rw [mem_ball, dist_eq_norm]
      by_contra hcon
      push_neg at hcon
      have : r ^ 2 ≤ sqd c y := by unfold sqd; nlinarith
      linarith
  rw [heq]
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (contDiff_sqd c).continuous continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := c) (r := r)).subset fun y hy => ?_
  have hai : 0 < a⁻¹ := inv_pos.2 ha
  have h1 : sqd c y ≤ r ^ 2 := by simp only [Set.mem_setOf_eq] at hy; linarith
  rw [mem_closedBall, dist_eq_norm]
  unfold sqd at h1
  nlinarith [norm_nonneg (y - c)]

theorem ball_etaleStein : ∀ (n : ℕ) (c : V n) (r : ℝ), ∃ X : EtaleStein n (ball c r), X.z = Subtype.val := by
  intro n c r
  have hU : IsOpen (ball c r) := isOpen_ball
  refine ⟨{ z := Subtype.val
            isLocalHomeomorph := ReciprocityTheory.ChartRestriction.G.AR.Up.HE.val_lh hU
            e := fun x => exh c r x.1
            smooth_e := ReciprocityTheory.ChartRestriction.G.AR.Up.HE.smoothR_val (contDiffOn_exh c r)
            levi_e := fun x ξ => by
              rw [ReciprocityTheory.ChartRestriction.G.AR.Up.HE.levi_val hU]
              exact leviV_exh_nonneg x.2 ξ
            isCompact_le := fun a => by
              rw [Subtype.isCompact_iff]
              convert isCompact_exh c r a using 1
              ext y
              constructor
              · rintro ⟨x, hx, rfl⟩
                exact ⟨x.2, hx⟩
              · rintro ⟨hy, hy'⟩
                exact ⟨⟨y, hy⟩, hy', rfl⟩ }, rfl⟩

end GlobalTheory.BallStein
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualTangentModEqEvalAdditiveStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierDual_tangent_mod_eq_eval_additive : ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a}), ∃ (b : A) (z : A ⊗[O] A), cobOne O A b = a • z ∧ ∀ φ : CartierDual O A, u (dUnit (R := O) φ) = Ideal.Quotient.mk _ (φ b) := by
  first | exact @GlobalTheory.cartierDual_tangent_mod | exact GlobalTheory.cartierDual_tangent_mod | (intros; apply GlobalTheory.cartierDual_tangent_mod <;> assumption)
end

