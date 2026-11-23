module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0205
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelLengthFiltrationInterKerCofactorLinearFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HerbrandDeterminantIdentityOfRelativeLength
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HerbrandLengthIdentitiesOfRelativeLength
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEigenFiltrationPiecesAddValInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneFixerSumVanishesHarishChandraInduction
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralCompAddEquivRescale
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem hasGauss_comp_equiv (X Y : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (μ : Measure X) (μ' : Measure Y)
    (T : X ≃ₜ+ Y) (r : NNReal) (f : Y → ℂ) (γ : ℂ) (hμ : μ.map T = r • μ') (h : HasGauss μ' f γ) :
    HasGauss μ (fun x => f (T x)) ((r : ℝ) * γ) := by
  intro K hK
  obtain ⟨L, hLc, hLo, hKL, hint⟩ := h (T '' K) (hK.image T.continuous)
  have hme : MeasurableEmbedding (T : X → Y) := T.toHomeomorph.measurableEmbedding
  have hset : ((L.comap (T.toAddEquiv.toAddMonoidHom) : AddSubgroup X) : Set X) = (T : X → Y) ⁻¹' (L : Set Y) := rfl
  refine ⟨L.comap T.toAddEquiv.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [hset]
    exact T.toHomeomorph.isCompact_preimage.2 hLc
  · rw [hset]
    exact hLo.preimage T.continuous
  · rw [hset]
    intro x hx
    exact hKL ⟨x, hx, rfl⟩
  · rw [hset, ← hme.setIntegral_map f (L : Set Y), hμ, Measure.restrict_smul, integral_smul_nnreal_measure, hint]
    simp [NNReal.smul_def]

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralCompactOpenPi
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem hasGauss_pi : ∀ (Y : Type) [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (_ : Good Y) (μ : Measure Y) [μ.IsAddHaarMeasure] (ι : Type) [Fintype ι] (f : ι → Y → ℂ) (γ : ι → ℂ), (∀ i, HasGauss μ (f i) (γ i)) → HasGauss (Measure.pi fun _ : ι => μ) (fun x => ∏ i, f i (x i)) (∏ i, γ i) := by
  intro Y _ _ _ _ hY μ _ ι _ f γ hf K hK
  haveI := hY.sc
  haveI := hY.lc
  haveI := hY.t2
  haveI : SigmaFinite μ := sigmaFinite_of_locallyFinite
  have hL : ∀ i, ∃ L : AddSubgroup Y, IsCompact (L : Set Y) ∧ IsOpen (L : Set Y) ∧
      (Function.eval i '' K) ⊆ L ∧ ∫ x in (L : Set Y), f i x ∂μ = γ i :=
    fun i => hf i _ (hK.image (continuous_apply i))
  choose L hLc hLo hLK hLi using hL
  refine ⟨AddSubgroup.pi Set.univ L, ?_, ?_, ?_, ?_⟩
  · rw [AddSubgroup.coe_pi]; exact isCompact_univ_pi hLc
  · rw [AddSubgroup.coe_pi]; exact isOpen_set_pi Set.finite_univ fun i _ => hLo i
  · intro x hx
    rw [SetLike.mem_coe, AddSubgroup.mem_pi]
    intro i _
    exact hLK i ⟨x, hx, rfl⟩
  · rw [AddSubgroup.coe_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
    exact Finset.prod_congr rfl fun i _ => hLi i

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionNormalizedDerivWeierstrassPTorsion
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.DerivExpansion

theorem tsum_inv_cube : ∑' m : ℤ, 1 / (m : ℂ) ^ 3 = 0 := by
  have h : ∑' m : ℤ, 1 / (m : ℂ) ^ 3 = -∑' m : ℤ, 1 / (m : ℂ) ^ 3 := by
    conv_lhs => rw [← (Equiv.neg ℤ).tsum_eq]
    rw [← tsum_neg]
    congr 1
    funext b
    simp only [Equiv.neg_apply, Int.cast_neg]
    change 1 / ((-(b : ℂ)) ^ 3) = -(1 / (b : ℂ) ^ 3)
    rw [show (-(b : ℂ)) ^ 3 = -((b : ℂ) ^ 3) by ring, div_neg]
  linear_combination h / 2

theorem row_eq (N : ℕ) [NeZero N] (j : ZMod N) :
    ∑' m : ℤ, 1 / (((j.val : ℂ)) / N + m) ^ 3 =
      -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * (ch N j * (1 + ch N j) / (1 - ch N j) ^ 3) := by
  rcases eq_or_ne j 0 with rfl | hj
  · have hc : ch N 0 = 1 := by simp [ch]
    simp only [ZMod.val_zero, Nat.cast_zero, zero_div, zero_add, hc, sub_self]
    rw [tsum_inv_cube]
    simp
  · set w : ℂ := ((j.val : ℂ)) / N with hw
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have him : w.im = 0 := by simp [hw, -ZMod.natCast_val]
    have hnot : ∀ n : ℤ, w ≠ n := by
      intro n hn
      rw [hw, div_eq_iff hN] at hn
      have hz : (j.val : ℤ) = n * N := by exact_mod_cast hn
      have h1 : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj ((ZMod.val_eq_zero j).mp h))
      have h2 : j.val < N := ZMod.val_lt j
      have h1' : (0 : ℤ) < j.val := by exact_mod_cast h1
      have h2' : (j.val : ℤ) < N := by exact_mod_cast h2
      rcases le_or_gt n 0 with h | h
      · nlinarith
      · nlinarith
    have hc : ch N j = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) := by
      rw [hw]
      unfold ch
      congr 1
      ring
    rw [hc]
    exact (_root_.GlobalTheory.WpFam.RowReal.row_real w him hnot).2

theorem main : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), HasQ N (wpd N x) (cD N x) := by
  intro N _ x
  unfold HasQ
  intro τ
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  obtain ⟨T, hT, hS⟩ := _root_.GlobalTheory.WpFam.RowsSummed.main N 2 τ x _ (by norm_num) (_root_.GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP τ (tors N τ x))
  set q := Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) with hq
  set c0 : ℂ := if x 0 = 0 then ch N (x 1) * (1 + ch N (x 1)) / (1 - ch N (x 1)) ^ 3 else 0 with hc0
  have h0 : cSum N 2 (-1) x 0 = 0 := by simp [cSum]
  have hT' : HasSum (fun k : ℕ => cSum N 2 (-1) x k * q ^ k) T := by
    have e1 : ((-1 : ℂ)) ^ (2 + 1) = -1 := by norm_num
    simpa only [e1] using hT
  have hsum : HasSum (fun n : ℕ => cD N x n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N))
      (c0 + T) := by
    have hA : HasSum (fun n : ℕ => if n = 0 then c0 else 0) c0 := hasSum_ite_eq 0 c0
    convert hA.add hT' using 1
    funext n
    have hexp : Complex.exp (2 * Real.pi * Complex.I * n * τ / N) = q ^ n := by
      rw [hq, ← Complex.exp_nat_mul]
      congr 1
      ring
    rw [hexp]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [cD, h0, hc0]
    · simp [cD, hn]
  convert hsum using 1
  have hrow : (if x 0 = 0 then ∑' m : ℤ, 1 / ((((x 1).val : ℂ)) / N + m) ^ (2 + 1) else 0) =
      -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * c0 := by
    rw [hc0]
    split_ifs
    · exact row_eq N (x 1)
    · simp
  have hf : ((Nat.factorial 2 : ℕ) : ℂ) = 2 := by norm_num [Nat.factorial]
  rw [hrow, hf] at hS
  simp only [wpd]
  rw [div_eq_iff (pow_ne_zero 3 hπ)]
  linear_combination (-2) * hS

end GlobalTheory.WpFam.DerivExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeYDerivativeTermIntegralPolynomialDecay
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.TermDecay

theorem intZ_ibp (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) (a : ℤ) (b m : ℕ) (hab : 2 ≤ a + 2 * b) {y : ℝ}
    (hy : y ≠ 0) :
    2 * (Real.pi : ℂ) * I * ν * intZ σ ν a b m y =
      -(a : ℂ) * intZ σ ν (a + 1) b m y
        + 2 * (-σ - (b : ℂ)) * (intZ σ ν (a - 1) (b + 1) m y - I * intZ σ ν a (b + 1) (m + 1) y) := by
  have i0 := _root_.GlobalTheory.HeckeTwo.TermDecay.integrable_qZ σ hσ a b m hab y hy
  have i1 := _root_.GlobalTheory.HeckeTwo.TermDecay.integrable_qZ σ hσ (a + 1) b m (by omega) y hy
  have i2 := _root_.GlobalTheory.HeckeTwo.TermDecay.integrable_qZ σ hσ (a - 1) (b + 1) m (by push_cast; omega) y hy
  have i3 := _root_.GlobalTheory.HeckeTwo.TermDecay.integrable_qZ σ hσ a (b + 1) (m + 1) (by push_cast; omega) y hy
  have hd : deriv (qZ σ a b m y) = fun t => -(a : ℂ) * qZ σ (a + 1) b m y t
      + 2 * (-σ - (b : ℂ)) * (qZ σ (a - 1) (b + 1) m y t - I * qZ σ a (b + 1) (m + 1) y t) := by
    funext t; exact (_root_.GlobalTheory.HeckeTwo.TermDecay.hasDerivAt_qZ σ a b m y hy t).deriv
  have hdiff : Differentiable ℝ (qZ σ a b m y) := fun t => (_root_.GlobalTheory.HeckeTwo.TermDecay.hasDerivAt_qZ σ a b m y hy t).differentiableAt
  have hi : MeasureTheory.Integrable (deriv (qZ σ a b m y)) := by
    rw [hd]; exact (i1.const_mul _).add ((i2.sub (i3.const_mul _)).const_mul _)
  have key := congrFun (Real.fourier_deriv i0 hdiff hi) ν
  rw [← intZ_eq_fourier, smul_eq_mul] at key
  rw [← key, hd, Real.fourier_real_eq_integral_exp_smul]
  unfold intZ
  set E : ℝ → ℂ := fun t => Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))) with hE
  have hEc : Continuous E := by rw [hE]; fun_prop
  have hEn : ∀ t, ‖E t‖ = 1 := by
    intro t; rw [hE, Complex.norm_exp]; simp
  have e : ∀ (f : ℝ → ℂ), MeasureTheory.Integrable f → MeasureTheory.Integrable (fun t : ℝ => f t * E t) := by
    intro f hf
    refine hf.norm.mono' (hf.aestronglyMeasurable.mul hEc.aestronglyMeasurable) (MeasureTheory.ae_of_all _ fun t => ?_)
    rw [norm_mul, hEn, mul_one]
  have hpt : ∀ t : ℝ, Complex.exp (((-2 * Real.pi * t * ν : ℝ) : ℂ) * I) •
      (-(a : ℂ) * qZ σ (a + 1) b m y t + 2 * (-σ - (b : ℂ)) * (qZ σ (a - 1) (b + 1) m y t - I * qZ σ a (b + 1) (m + 1) y t))
      = -(a : ℂ) * (qZ σ (a + 1) b m y t * E t) + 2 * (-σ - (b : ℂ)) *
        (qZ σ (a - 1) (b + 1) m y t * E t - I * (qZ σ a (b + 1) (m + 1) y t * E t)) := by
    intro t
    rw [smul_eq_mul, hE]
    have : (((-2 * Real.pi * t * ν : ℝ) : ℂ) * I) = -(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)) := by push_cast; ring
    rw [this]; ring
  simp_rw [hpt]
  have j1 : MeasureTheory.Integrable (fun v => -(a : ℂ) * (qZ σ (a + 1) b m y v * E v)) := (e _ i1).const_mul _
  have j2 : MeasureTheory.Integrable (fun v => qZ σ (a - 1) (b + 1) m y v * E v) := e _ i2
  have j3 : MeasureTheory.Integrable (fun v => I * (qZ σ a (b + 1) (m + 1) y v * E v)) := (e _ i3).const_mul _
  have j23 : MeasureTheory.Integrable (fun v => 2 * (-σ - (b : ℂ)) *
      (qZ σ (a - 1) (b + 1) m y v * E v - I * (qZ σ a (b + 1) (m + 1) y v * E v))) := (j2.sub j3).const_mul _
  rw [MeasureTheory.integral_add j1 j23, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub j2 j3, MeasureTheory.integral_const_mul]

end GlobalTheory.HeckeTwo.TermDecay

namespace GlobalTheory.HeckeTwo.TermDecay

theorem le_div_one_add_pow_succ_of_mul_le (x : ℝ) (hx : 0 ≤ x) (N : ℕ) (A B Y : ℝ) (hY : 0 ≤ Y) (hA : 0 ≤ A) (hB : 0 ≤ B) (q : ℝ)
    (h0 : q ≤ A * Y) (h1 : x * q ≤ B * Y / (1 + x) ^ N) :
    q ≤ (2 ^ (N + 1) * A + 2 * B) * Y / (1 + x) ^ (N + 1) := by
  have hp : 0 < (1 + x) ^ (N + 1) := by positivity
  rw [le_div_iff₀ hp]
  rcases le_or_gt x 1 with h | h
  · have h2 : (1 + x) ^ (N + 1) ≤ 2 ^ (N + 1) := pow_le_pow_left₀ (by linarith) (by linarith) _
    rcases le_or_gt q 0 with hq | hq
    · have : 0 ≤ (2 ^ (N + 1) * A + 2 * B) * Y := by positivity
      nlinarith [hp]
    · calc q * (1 + x) ^ (N + 1) ≤ A * Y * 2 ^ (N + 1) := mul_le_mul h0 h2 hp.le (by positivity)
        _ ≤ (2 ^ (N + 1) * A + 2 * B) * Y := by nlinarith [mul_nonneg hB hY]
  · have hpN : 0 < (1 + x) ^ N := by positivity
    have h1' : x * q * (1 + x) ^ N ≤ B * Y := by rwa [le_div_iff₀ hpN] at h1
    have hx2 : 1 + x ≤ 2 * x := by linarith
    rcases le_or_gt q 0 with hq | hq
    · have : 0 ≤ (2 ^ (N + 1) * A + 2 * B) * Y := by positivity
      nlinarith [hp]
    · calc q * (1 + x) ^ (N + 1) = q * (1 + x) ^ N * (1 + x) := by ring
        _ ≤ q * (1 + x) ^ N * (2 * x) := by gcongr
        _ = 2 * (x * q * (1 + x) ^ N) := by ring
        _ ≤ 2 * (B * Y) := by linarith
        _ ≤ (2 ^ (N + 1) * A + 2 * B) * Y := by nlinarith [mul_nonneg (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (N + 1)) hA) hY]

theorem intZ_decay (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ halfPlane) (N : ℕ) :
    ∀ (a : ℤ) (b m : ℕ), 2 ≤ a + 2 * b → ∃ C : ℝ, ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖intZ σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  induction N with
  | zero =>
    intro a b m hab
    obtain ⟨C, hC⟩ := _root_.GlobalTheory.HeckeTwo.TermDecay.norm_intZ_le K hK hKH a b m hab
    exact ⟨C, fun σ hσ ν y _ hy => by simpa using hC σ hσ ν y hy⟩
  | succ N ih =>
    intro a b m hab
    obtain ⟨C0, hC0⟩ := _root_.GlobalTheory.HeckeTwo.TermDecay.norm_intZ_le K hK hKH a b m hab
    obtain ⟨C1, hC1⟩ := ih (a + 1) b m (by omega)
    obtain ⟨C2, hC2⟩ := ih (a - 1) (b + 1) m (by push_cast; omega)
    obtain ⟨C3, hC3⟩ := ih a (b + 1) (m + 1) (by push_cast; omega)
    set B : ℝ := (|(a : ℝ)| * |C1| + 2 * (|R| + b) * (|C2| + |C3|)) / (2 * Real.pi) with hB
    refine ⟨2 ^ (N + 1) * |C0| + 2 * B, fun σ hσ ν y hν hy => ?_⟩
    set E : ℝ := (m : ℝ) + 1 - a - 2 * b - 2 * σ.re with hE
    have hyp : 0 < |y| := abs_pos.2 hy
    have hnp : 0 < |ν| := abs_pos.2 hν
    have hx : |ν * y| = |ν| * |y| := abs_mul ν y
    have hpN : 0 < (1 + |ν * y|) ^ N := by positivity
    have hB0 : 0 ≤ B := by rw [hB]; have := Real.pi_pos; positivity
    refine le_trans ?_ (le_of_eq (by ring : (2 ^ (N + 1) * |C0| + 2 * B) * |y| ^ E / (1 + |ν * y|) ^ (N + 1) =
      (2 ^ (N + 1) * |C0| + 2 * B) * |y| ^ E / (1 + |ν * y|) ^ (N + 1)))
    apply le_div_one_add_pow_succ_of_mul_le |ν * y| (abs_nonneg _) N |C0| B (|y| ^ E) (by positivity) (abs_nonneg _) hB0
    · exact (hC0 σ hσ ν y hy).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    ·
      have hibp := intZ_ibp σ (hKH hσ) ν a b m hab hy
      have e1 := hC1 σ hσ ν y hν hy
      have e2 := hC2 σ hσ ν y hν hy
      have e3 := hC3 σ hσ ν y hν hy
      have hE1 : ((m : ℝ) + 1 - ((a + 1 : ℤ) : ℝ) - 2 * b - 2 * σ.re) = E - 1 := by rw [hE]; push_cast; ring
      have hE2 : ((m : ℝ) + 1 - ((a - 1 : ℤ) : ℝ) - 2 * ((b + 1 : ℕ) : ℝ) - 2 * σ.re) = E - 1 := by rw [hE]; push_cast; ring
      have hE3 : (((m + 1 : ℕ) : ℝ) + 1 - (a : ℝ) - 2 * ((b + 1 : ℕ) : ℝ) - 2 * σ.re) = E - 1 := by rw [hE]; push_cast; ring
      rw [hE1] at e1; rw [hE2] at e2; rw [hE3] at e3
      set X : ℝ := |y| ^ (E - 1) / (1 + |ν * y|) ^ N with hX
      have hX0 : 0 ≤ X := by positivity
      have hσb : ‖-σ - (b : ℂ)‖ ≤ |R| + b := by
        calc ‖-σ - (b : ℂ)‖ ≤ ‖σ‖ + ‖(b : ℂ)‖ := by rw [← norm_neg σ]; exact norm_sub_le _ _
          _ ≤ |R| + b := by rw [Complex.norm_natCast]; gcongr; exact (hR σ hσ).trans (le_abs_self R)
      have key : 2 * Real.pi * |ν| * ‖intZ σ ν a b m y‖ ≤ (|(a : ℝ)| * |C1| + 2 * (|R| + b) * (|C2| + |C3|)) * X := by
        have hn : ‖2 * (Real.pi : ℂ) * I * ν * intZ σ ν a b m y‖ = 2 * Real.pi * |ν| * ‖intZ σ ν a b m y‖ := by
          simp [norm_mul, Complex.norm_real, abs_of_pos Real.pi_pos]
        rw [← hn, hibp]
        have f1 : ‖intZ σ ν (a + 1) b m y‖ ≤ |C1| * X := by
          rw [hX, ← mul_div_assoc]; exact e1.trans (by gcongr; exact le_abs_self _)
        have f2 : ‖intZ σ ν (a - 1) (b + 1) m y‖ ≤ |C2| * X := by
          rw [hX, ← mul_div_assoc]; exact e2.trans (by gcongr; exact le_abs_self _)
        have f3 : ‖intZ σ ν a (b + 1) (m + 1) y‖ ≤ |C3| * X := by
          rw [hX, ← mul_div_assoc]; exact e3.trans (by gcongr; exact le_abs_self _)
        calc _ ≤ ‖-(a : ℂ) * intZ σ ν (a + 1) b m y‖ + ‖2 * (-σ - (b : ℂ)) *
              (intZ σ ν (a - 1) (b + 1) m y - I * intZ σ ν a (b + 1) (m + 1) y)‖ := norm_add_le _ _
          _ ≤ |(a : ℝ)| * (|C1| * X) + 2 * (|R| + b) * (|C2| * X + |C3| * X) := by
            rw [norm_mul, norm_mul, norm_neg, norm_mul]
            have ha : ‖(a : ℂ)‖ = |(a : ℝ)| := by rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
            rw [ha]
            have hs : ‖intZ σ ν (a - 1) (b + 1) m y - I * intZ σ ν a (b + 1) (m + 1) y‖ ≤ |C2| * X + |C3| * X := by
              refine (norm_sub_le _ _).trans (add_le_add f2 ?_)
              rw [norm_mul, Complex.norm_I, one_mul]; exact f3
            gcongr
            · simp
          _ = _ := by ring

      have hyE : |y| ^ (E - 1) = |y| ^ E / |y| := by rw [Real.rpow_sub_one hyp.ne']
      have h2p : 0 < 2 * Real.pi * |ν| := by have := Real.pi_pos; positivity
      rw [hx]
      have : |ν| * |y| * ‖intZ σ ν a b m y‖ = |y| / (2 * Real.pi) * (2 * Real.pi * |ν| * ‖intZ σ ν a b m y‖) := by
        field_simp
      rw [this]
      calc |y| / (2 * Real.pi) * (2 * Real.pi * |ν| * ‖intZ σ ν a b m y‖)
          ≤ |y| / (2 * Real.pi) * ((|(a : ℝ)| * |C1| + 2 * (|R| + b) * (|C2| + |C3|)) * X) := by gcongr
        _ = B * |y| ^ E / (1 + |ν| * |y|) ^ N := by
          rw [hB, hX, hyE, ← hx]; field_simp

end GlobalTheory.HeckeTwo.TermDecay


open GlobalTheory.HeckeTwo.TermDecay in
theorem GlobalTheory.HeckeTwo.TermDecay.intT_bound : ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ a b m : ℕ, 2 ≤ a + 2 * b → ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N := by
  intro K hK hKH a b m hab N
  obtain ⟨C, hC⟩ := intZ_decay K hK hKH N (a : ℤ) b m (by exact_mod_cast hab)
  refine ⟨C, fun σ hσ ν y hν hy => ?_⟩
  rw [intT_eq_intZ]
  have := hC σ hσ ν y hν hy
  simpa using this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HerbrandQuotientEigenDet
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory.HerbrandAlg

theorem kerId : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, KernelIdentity v a Fil τ := by
  intro C _ v S _ _ a ha N Fil hF τ
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : lin a τ • x = 0 := hx
    show lin a τ • (Submodule.Quotient.mk x : (Fin N → RS a) ⧸ Fil) = 0
    rw [← Submodule.Quotient.mk_smul, hx', Submodule.Quotient.mk_zero]
  · ext x
    constructor
    · rintro ⟨hx, hk⟩
      have hx' : lin a τ • x = 0 := hx
      have hxF : x ∈ Fil := (Submodule.Quotient.mk_eq_zero Fil).1 hk
      refine ⟨⟨x, hxF⟩, ?_, rfl⟩
      show lin a τ • (⟨x, hxF⟩ : Fil) = 0
      exact Subtype.ext hx'
    · rintro ⟨⟨y, hy⟩, hy', rfl⟩
      have hy'' : lin a τ • (⟨y, hy⟩ : Fil) = 0 := hy'
      refine ⟨?_, ?_⟩
      · show lin a τ • y = 0
        exact congrArg Subtype.val hy''
      · show (Submodule.Quotient.mk y : (Fin N → RS a) ⧸ Fil) = 0
        exact (Submodule.Quotient.mk_eq_zero Fil).2 hy

theorem core : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∃ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ ∧ RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ)) ((preEig a Fil τ).map (comp a N τ)) r := by
  intro C _ v S _ _ a ha N Fil hF τ
  obtain ⟨r, hr, hR⟩ := _root_.GlobalTheory.HerbCore.relLen_lin_filKer C v S a ha N Fil hF τ
  obtain ⟨hd, hcP, hkerc, hsat, hAX, hHc, hcH, hprojX, hHX, hFX, htf, g, hg⟩ :=
    _root_.GlobalTheory.herbrand_lattice_facts C v S a ha N Fil hF τ
  obtain ⟨fF, fX, fK, fH, -, -, -⟩ := _root_.GlobalTheory.HerbFin.finite_main C v S a ha N Fil hF τ
  have tfO : ∀ (c : Int0 v) (x : Fin N → Int0 v), c ≠ 0 → c • x = 0 → x = 0 := by
    intro c x hc h
    funext i
    have := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero] at this
    exact this.resolve_left hc
  have hKF : filKer a Fil τ ≤ Fil.restrictScalars (Int0 v) := inf_le_left
  have fKs : Module.Finite (Int0 v) ↥(eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ) := by
    rw [Module.Finite.iff_fg] at fH fK ⊢
    exact fH.sup fK
  have hle : eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ ≤ preEig a Fil τ :=
    sup_le hHX (hKF.trans hFX)
  have hA : preEig a Fil τ ⊓ LinearMap.ker (mulR a N (lin a τ)) ≤
      eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ := fun x hx =>
    Submodule.mem_sup_left (LinearMap.mem_ker.1 hx.2)
  have hmapH : (eigSub a τ (Fin N → RS a)).map (mulR a N (lin a τ)) = ⊥ :=
    eq_bot_iff.2 (by rintro _ ⟨x, hx, rfl⟩; exact (Submodule.mem_bot _).2 hx)
  have e1 : (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ).map (mulR a N (lin a τ)) =
      (filKer a Fil τ).map (mulR a N (lin a τ)) := by
    rw [Submodule.map_sup, hmapH, bot_sup_eq]
  have s1 : RelLen v (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ) (preEig a Fil τ) r :=
    (_root_.GlobalTheory.LenMap.relLen_map_iff C v _ _ htf htf (mulR a N (lin a τ)) _ _ hle hA fX fKs r).2 (by rw [e1, hAX]; exact hR)
  have hC : preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤
      eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ := fun x hx =>
    Submodule.mem_sup_right ⟨hsat hx, LinearMap.mem_ker.2 ((hcP x).1 (LinearMap.mem_ker.1 hx.2))⟩
  have s2 := (_root_.GlobalTheory.LenMap.relLen_map_iff C v _ _ htf tfO (comp a N τ) _ _ hle hC fX fKs r).1 s1
  have hK0 : (filKer a Fil τ).map (comp a N τ) = ⊥ :=
    eq_bot_iff.2 (by
      rintro _ ⟨x, hx, rfl⟩
      exact (Submodule.mem_bot _).2 ((hcP x).2 (LinearMap.mem_ker.1 hx.2)))
  have e2 : (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ).map (comp a N τ) =
      (eigSub a τ (Fin N → RS a)).map (comp a N τ) := by
    rw [Submodule.map_sup, hK0, sup_bot_eq]
  exact ⟨r, hr, e2 ▸ s2⟩

theorem herbrandDet : HerbrandDet := by
  intro C _ v S _ _ a ha N Fil hF τ
  obtain ⟨r, hr, hR⟩ := core C v S a ha N Fil hF τ
  exact ⟨_root_.GlobalTheory.HerbDet.detIdentity_of_relLen C v S a ha N Fil hF τ r hr hR, kerId C v S a ha N Fil hF τ,
    _root_.GlobalTheory.HerbLen.lengthIdentities_of_relLen C v S a ha N Fil hF τ r hr hR⟩

end GlobalTheory.HerbrandAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertCoordinateMapBijectiveOfLeAffineStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertCoordinateMap_bijective_of_le_affine : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W W' : Z.affineOpens), (W' : Z.Opens) ≤ W → Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y W) → Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y W') := by
  first | (exact @GlobalTheory.HilbAff.coord_bijective_of_le_affine) | (exact GlobalTheory.HilbAff.coord_bijective_of_le_affine) | (intros; apply GlobalTheory.HilbAff.coord_bijective_of_le_affine  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeMetricGramMatrixLocalHolomorphicImPartStatement
section
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeMetricGramMatrix_local_holomorphic_imPart : ∀ (n a g rk : ℕ) (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), IsPeriodChart rk τ₀ B → ∀ z ∈ punctured ha 1, MContDiffAt ∞ (hodgeGram ha τ₀ B) z ∧ (∀ ξ, mdel (hodgeGram ha τ₀ B) z ξ = (1 / (2 * Complex.I)) • ((Matrix.of fun j k => fderiv ℂ (fun x => τ₀ x j k) z ξ) + ∑ i, (ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))) • ((B i).map (Int.cast : ℤ → ℝ)).map Complex.ofReal)) ∧ ∀ ξ η, mddbar (hodgeGram ha τ₀ B) z ξ η = 0 := by
  first | exact @GlobalTheory.HodgeGramLocal.hodgeGram_local | exact GlobalTheory.HodgeGramLocal.hodgeGram_local | (intros; apply GlobalTheory.HodgeGramLocal.hodgeGram_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneFixerSumVanishesHarishChandraInductionStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperplaneFixerSumVanishes_harishChandraInduction : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (A : GL (Fin a) F → ℂ) (B : GL (Fin b) F → ℂ), IsChar ℂ ℂ A → IsChar ℂ ℂ B → HFree A → HFree B → HFree (hc a b A B n) := by
  first | (exact @GlobalTheory.Shin.FreeHc.hfree_hc) | (exact GlobalTheory.Shin.FreeHc.hfree_hc) | (intros; apply GlobalTheory.Shin.FreeHc.hfree_hc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingAtPrimeOfEtaleStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgClosed_fractionRing_atPrime_of_etale' : ∀ (T E : Type) [CommRing T] [IsDomain T] [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime] [IsDomain (Localization.AtPrime P)], IsAlgClosed (FractionRing T) → IsAlgClosed (FractionRing (Localization.AtPrime P)) := by
  first | (exact @GlobalTheory.isAlgClosed_fractionRing_atPrime_of_etale) | (exact GlobalTheory.isAlgClosed_fractionRing_atPrime_of_etale) | (intros; apply GlobalTheory.isAlgClosed_fractionRing_atPrime_of_etale  <;> assumption)
end

