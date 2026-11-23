module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitQExpansionCoeffsIntegral
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowPadicValEqOneOfPrimePow
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem pow_padicVal_eq_one_of_primePow {k : Type} [Field k] {n l : ℕ} (hn : 0 < n) (hl : l.Prime) {y : k}
    (h1 : y ^ n = 1) {a : ℕ} (h2 : y ^ (l ^ a) = 1) : y ^ (l ^ padicValNat l n) = 1 := by
  have := Fact.mk hl
  have d1 : orderOf y ∣ n := orderOf_dvd_of_pow_eq_one h1
  have d2 : orderOf y ∣ l ^ a := orderOf_dvd_of_pow_eq_one h2
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hl).1 d2
  rw [hi] at d1
  have hle : i ≤ padicValNat l n := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hn.ne').1 d1
  apply orderOf_dvd_iff_pow_eq_one.1
  rw [hi]
  exact pow_dvd_pow l hle

theorem primePowRoots_finite_ncard (k : Type) [Field k] (n l : ℕ) (hn : 0 < n) (hl : l.Prime) :
    {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.Finite ∧
      {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.ncard ≤ l ^ padicValNat l n := by
  have hm : 0 < l ^ padicValNat l n := pow_pos hl.pos _
  have hsub : {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1} ⊆
      ((nthRoots (l ^ padicValNat l n) (1 : k)).toFinset : Set k) := by
    rintro y ⟨h1, a, h2⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_nthRoots hm]
    exact pow_padicVal_eq_one_of_primePow hn hl h1 h2
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans (card_nthRoots _ _)

theorem samePart_roots_finite_ncard :
    ∀ (k : Type) [Field k] (n l : ℕ), 0 < n → l.Prime →
      ({y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.Finite ∧
        {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.ncard ≤ l ^ padicValNat l n) ∧
      ∀ z : k, {x : k | x ^ n = 1 ∧ SamePart l x z}.Finite ∧
        {x : k | x ^ n = 1 ∧ SamePart l x z}.ncard ≤ l ^ padicValNat l n := by
  intro k _ n l hn hl
  obtain ⟨hf, hc⟩ := primePowRoots_finite_ncard k n l hn hl
  refine ⟨⟨hf, hc⟩, fun z => ?_⟩
  rcases Set.eq_empty_or_nonempty {x : k | x ^ n = 1 ∧ SamePart l x z} with he | ⟨x₀, hx₀, hb⟩
  · rw [he]; simp
  have hsub : {x : k | x ^ n = 1 ∧ SamePart l x z} ⊆
      (fun y => y * x₀) '' {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1} := by
    rintro x ⟨hx, ha⟩
    have hs : SamePart l x x₀ := Eq.trans ha (Eq.symm hb)
    obtain ⟨a, ha⟩ := (samePart_iff hl (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hx⟩)
      (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hx₀⟩)).1 hs
    have h0 : x₀ ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hx₀
      exact zero_ne_one hx₀
    refine ⟨x / x₀, ⟨?_, a, ?_⟩, div_mul_cancel₀ x h0⟩
    · rw [div_pow, hx, hx₀, div_one]
    · rw [div_pow, ha, div_self (pow_ne_zero _ h0)]
  refine ⟨(hf.image _).subset hsub, ?_⟩
  exact (Set.ncard_le_ncard hsub (hf.image _)).trans ((Set.ncard_image_le hf).trans hc)

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducesToSmallerOddWeightOfLeadingCoeffMatrixDet
section
open UpperHalfPlane Filter GlobalTheory.OddFrame Asymptotics
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

private theorem slash_finset_sum {ι : Type*} (t : Finset ι) (k : ℤ) (f : ι → ℍ → ℂ) (x : SL(2, ℤ)) :
    (∑ i ∈ t, f i) ∣[k] x = ∑ i ∈ t, (f i) ∣[k] x := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

private theorem tendsto_exp_neg_im :
    Tendsto (fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) atImInfty (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  have h : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  exact h.const_mul_atTop_of_neg (by linarith [Real.pi_pos])

theorem reduces_of_det_leadM_eq_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ))
    (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsReps Γ s →
    (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (leadM M s w F).det = 0 → Reduces Γ w F := by
  classical
  intro M Γ r s w F hM hΓ hs hF hdet
  obtain ⟨c, hc, hcv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hT := fun j => GlobalTheory.T.slashQExpansionCoeffWidth_transform M Γ (w j) (F j) hM hΓ (hF j).2
  have hb : ∀ (x : SL(2, ℤ)) (n : ℕ), n < M → ∑ j, c j * co M (w j) (F j) x n = 0 := by
    refine _root_.GlobalTheory.OddFrame.coeff_eq_zero_of_sum_reps_eq_zero M Γ r s (fun x n => ∑ j, c j * co M (w j) (F j) x n) hM hs ?_ ?_ ?_ ?_
    · intro x n
      simp only [fun j => (hT j).1 x n, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · intro γ hγ x n
      simp only [fun j => (hT j).2.1 γ hγ x n]
    · intro x n
      simp only [fun j => (hT j).2.2 (hF j).1 x n, mul_neg, Finset.sum_neg_distrib]
    · intro i
      have := congrFun hcv i
      simp only [Matrix.mulVec, dotProduct, leadM, Matrix.of_apply, Pi.zero_apply, Finset.sum_mul] at this
      rw [Finset.sum_comm, ← this]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ => mul_comm _ _
  have hO : ∀ x : SL(2, ℤ), (fun τ : ℍ => ∑ j, c j * (F j ∣[w j] x) τ) =O[atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
    intro x
    have h1 := IsBigO.sum (s := Finset.univ) fun j _ =>
      (_root_.GlobalTheory.OddFrame.slash_sub_partialSum_isBigO M Γ (w j) (F j) hM hΓ (hF j).2 x).const_mul_left (c j)
    refine h1.congr_left fun τ => ?_
    simp only [Finset.sum_apply, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm, sub_eq_self]
    refine Finset.sum_eq_zero fun n hn => ?_
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, hb x n (Finset.mem_range.mp hn), zero_mul]
  have hne : (Finset.univ.filter fun j => c j ≠ 0).Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
    exact ⟨j, by simpa using hj⟩
  obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_max_image _ w hne
  have hc₀ : c j₀ ≠ 0 := by simpa using hj₀
  have he : ∀ j, ∃ e : ℍ → ℂ, IsMF ⊤ (w j₀ - w j + 4) e ∧
      (fun τ : ℍ => e τ - c j) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
    intro j
    by_cases hj : c j = 0
    · exact ⟨0, IsMF.zero _ _, by simp [hj, isBigO_zero]⟩
    · have hle : w j ≤ w j₀ := hmax j (by simpa using hj)
      obtain ⟨e, h1, h2⟩ := _root_.GlobalTheory.levelOne_form_one_add_expDecay (w j₀ - w j + 4) (by omega)
        (((hF j₀).1.sub_odd (hF j).1).add (by decide))
      refine ⟨c j • e, h1.smul _, (h2.const_mul_left (c j)).congr_left fun τ => ?_⟩
      simp [mul_sub]
  choose e heMF heO using he
  have hH : IsMF Γ (w j₀ + 4) (∑ j, e j * F j) :=
    IsMF.sum _ fun j _ => ((heMF j).mono le_top).mul (hF j).2 (by ring)
  have hHx : ∀ x : SL(2, ℤ), (∑ j, e j * F j) ∣[w j₀ + 4] x = ∑ j, e j * (F j ∣[w j] x) := by
    intro x
    rw [slash_finset_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : w j₀ + 4 = (w j₀ - w j + 4) + w j := by ring
    rw [this, ModularForm.mul_slash_SL2, (heMF j).slash_top]
  have hHO : ∀ x : SL(2, ℤ), ((∑ j, e j * F j) ∣[w j₀ + 4] x) =O[atImInfty]
      fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
    intro x
    have h1 : (fun τ : ℍ => ∑ j, (e j τ - c j) * (F j ∣[w j] x) τ) =O[atImInfty]
        fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
      have h2 : ∀ j, (fun τ : ℍ => (e j τ - c j) * (F j ∣[w j] x) τ) =O[atImInfty]
          fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
        intro j
        have hb' : (F j ∣[w j] x) =O[atImInfty] (fun _ => (1 : ℝ)) := (hF j).2.2.2 x
        simpa only [mul_one] using (heO j).mul hb'
      exact (IsBigO.sum (s := Finset.univ) fun j _ => h2 j).congr_left fun τ => Finset.sum_apply _ _ _
    rw [hHx]
    refine (h1.add (hO x)).congr_left fun τ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by simp; ring
  obtain ⟨G, hG, hHG⟩ := GlobalTheory.T.exists_eq_discriminant_mul_of_expDecay_cusps Γ _ _ hH hHO
  have hΔ : IsMF ⊤ 12 ModularForm.discriminant := (isCF_coe_top CuspForm.discriminant).isMF
  refine ⟨j₀, w j₀ + 4 - 12, G, ModularForm.discriminant, e, by omega, ?_, hG,
    fun j => (heMF j).2.1, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := (hF j₀).1
    exact ⟨m - 4, by omega⟩
  · intro h0
    have h1 := (heO j₀).trans_tendsto tendsto_exp_neg_im
    rw [h0] at h1
    simp only [Pi.zero_apply, zero_sub] at h1
    have := tendsto_nhds_unique h1 tendsto_const_nhds
    exact hc₀ (neg_eq_zero.mp this.symm)
  · intro x τ
    have h1 := hHx x
    have h2 : w j₀ + 4 = 12 + (w j₀ + 4 - 12) := by ring
    rw [hHG, h2, ModularForm.mul_slash_SL2, hΔ.slash_top] at h1
    have h3 := congrFun h1 τ
    simpa [Finset.sum_apply] using h3

end GlobalTheory.OddFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitQExpansionCoeffsIntegralStatement
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedSiegelUnit_qExpansion_coeffs_integral : ∀ (c M a : ℕ), 0 < M → a < M → ∃ k : ℤ, ∀ b : ℕ, admitted c ![(a : ℚ) / M, (b : ℚ) / M] → ∃ A : ℕ → ℂ, HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) A ∧ A 0 ≠ 0 ∧ (∀ n, A n ∈ IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))}) ∧ (Nat.Coprime c M → ∀ n, A n ∈ Subring.closure {ee (1 / (M : ℂ))}) ∧ (b = 0 → ∀ n, ∃ z : ℤ, A n = z) := by
  first | exact @GlobalTheory.SiegQ.sg_expansion_int | exact GlobalTheory.SiegQ.sg_expansion_int | (intros; apply GlobalTheory.SiegQ.sg_expansion_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductDistributionRelation
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

open scoped UpperHalfPlane MatrixGroups Manifold in
theorem _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot {m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) (hm : 0 < m)
    (x y : ℂ) : ∏ j ∈ Finset.range m, (x - ζ ^ j * y) = x ^ m - y ^ m := by
  have hinj : Set.InjOn (fun j : ℕ => ζ ^ j) (Finset.range m) := fun i hi j hj h =>
    hζ.pow_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h
  have himage :
      (Finset.range m).image (fun j : ℕ => ζ ^ j) = Polynomial.nthRootsFinset m (1 : ℂ) := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
      rw [Polynomial.mem_nthRootsFinset hm, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · rw [hζ.card_nthRootsFinset, Finset.card_image_of_injOn hinj, Finset.card_range]
  rw [hζ.pow_sub_pow_eq_prod_sub_mul x y hm, ← himage, Finset.prod_image hinj]

open scoped UpperHalfPlane MatrixGroups Manifold in
theorem _root_.GlobalTheory.Sieg.ee_nat_div_eq_pow (m j : ℕ) :
    _root_.GlobalTheory.Sieg.ee ((j : ℂ) / m) = Complex.exp (2 * Real.pi * Complex.I / m) ^ j := by
  rw [_root_.GlobalTheory.Sieg.ee, ← Complex.exp_nat_mul]
  congr 1
  ring

open scoped UpperHalfPlane MatrixGroups Manifold in
theorem _root_.GlobalTheory.Sieg.prod_cthFac_mul_pow {c m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    (hm : 0 < m) (hc : Nat.Coprime c m) (q t : ℂ) (n : ℕ) :
    ∏ j ∈ Finset.range m, _root_.GlobalTheory.Sieg.cthFac c q (t * ζ ^ j) n =
      _root_.GlobalTheory.Sieg.cthFac c (q ^ m) (t ^ m) n := by
  have key : ∀ {ξ : ℂ}, IsPrimitiveRoot ξ m → ∀ (u : ℂ) (g : ℕ → ℂ), (∀ j, g j = ξ ^ j * u) →
      ∏ j ∈ Finset.range m, (1 - q ^ n * g j) = 1 - (q ^ m) ^ n * u ^ m := by
    intro ξ hξ u g hg
    have h := _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot hξ hm 1 (q ^ n * u)
    rw [one_pow] at h
    calc ∏ j ∈ Finset.range m, (1 - q ^ n * g j)
          = ∏ j ∈ Finset.range m, (1 - ξ ^ j * (q ^ n * u)) :=
          Finset.prod_congr rfl fun j _ => by rw [hg]; ring
      _ = _ := by rw [h]; ring
  unfold _root_.GlobalTheory.Sieg.cthFac
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow,
    Finset.prod_pow, key hζ t _ (fun j => by ring),
    key hζ.inv t⁻¹ _ (fun j => by rw [mul_inv, inv_pow]; ring),
    key (hζ.pow_of_coprime c hc) (t ^ c) _
      (fun j => by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j c]; ring),
    key (hζ.pow_of_coprime c hc).inv (t ^ c)⁻¹ _
      (fun j => by rw [mul_pow, ← pow_mul, inv_pow, ← pow_mul, mul_comm c j, mul_inv]; ring)]
  ring


open scoped UpperHalfPlane MatrixGroups Manifold in
theorem _root_.GlobalTheory.Sieg.prod_cth_mul_ee : ∀ (c m : ℕ) (q t : ℂ), 1 < c →
    Nat.Coprime c 6 → 0 < m → Nat.Coprime c m →
    ‖q‖ < 1 → q ≠ 0 → t ≠ 0 → (∀ n : ℤ, q ^ n * t ^ (c * m) ≠ 1) →
    ∏ j ∈ Finset.range m, _root_.GlobalTheory.Sieg.cth c q (t * _root_.GlobalTheory.Sieg.ee ((j : ℂ) / m)) =
      _root_.GlobalTheory.Sieg.cth c (q ^ m) (t ^ m) := by
  intro c m q t _ _ hm hc hq _ ht _
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / m) with hζdef
  have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m hm.ne'
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  simp only [_root_.GlobalTheory.Sieg.ee_nat_div_eq_pow]
  rw [← hζdef]
  have hA : ∏ j ∈ Finset.range m, (-(t * ζ ^ j)) = -t ^ m := by
    have h := _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot hζ hm 0 t
    simp only [zero_pow hm.ne', zero_sub] at h
    rw [← h]
    exact Finset.prod_congr rfl fun j _ => by ring
  have hB : ∏ j ∈ Finset.range m, (1 - t * ζ ^ j) = 1 - t ^ m := by
    have h := _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot hζ hm 1 t
    rw [one_pow] at h
    rw [← h]
    exact Finset.prod_congr rfl fun j _ => by ring
  have hC : ∏ j ∈ Finset.range m, (1 - (t * ζ ^ j) ^ c) = 1 - (t ^ m) ^ c := by
    have h := _root_.GlobalTheory.Sieg.prod_sub_pow_mul_of_isPrimitiveRoot (hζ.pow_of_coprime c hc) hm 1 (t ^ c)
    rw [one_pow, ← pow_mul, mul_comm c m, pow_mul] at h
    rw [← h]
    exact Finset.prod_congr rfl fun j _ => by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j c]; ring
  have hD : ∏ j ∈ Finset.range m, ∏' n : ℕ, _root_.GlobalTheory.Sieg.cthFac c q (t * ζ ^ j) (n + 1) =
      ∏' n : ℕ, _root_.GlobalTheory.Sieg.cthFac c (q ^ m) (t ^ m) (n + 1) := by
    rw [← Multipliable.tprod_finsetProd fun j _ =>
      _root_.GlobalTheory.Sieg.cthFac_multipliable c q _ hq (mul_ne_zero ht (pow_ne_zero _ hζ0))]
    exact tprod_congr fun n => _root_.GlobalTheory.Sieg.prod_cthFac_mul_pow hζ hm hc q t (n + 1)
  unfold _root_.GlobalTheory.Sieg.cth
  simp only [Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_pow, Finset.prod_zpow,
    Finset.prod_const, Finset.card_range, hB, hC, hD]
  rw [hA]

end GlobalTheory.Sieg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusCardBoundsAndMul
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem degType_pos (g : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : ∀ d ∈ degType g f, 0 < d := by
  intro d hd
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hd
  exact (UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP).natDegree_pos

theorem degType_sum (g : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) (hf : f ≠ 0) :
    (degType g f).sum = f.natDegree := by
  unfold degType
  rw [← natDegree_multiset_prod _ (UniqueFactorizationMonoid.zero_notMem_normalizedFactors f)]
  exact natDegree_eq_of_degree_eq
    (degree_eq_degree_of_associated (UniqueFactorizationMonoid.prod_normalizedFactors hf))

theorem prod_pow_sub_one_le (g : ℕ) (s : Multiset ℕ) :
    (s.map fun d => g ^ d - 1).prod ≤ g ^ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, pow_add]
    exact Nat.mul_le_mul (Nat.sub_le _ _) ih

theorem ne_zero_natDegree_of_mem_sqSet (g : ℕ) [Fact g.Prime] (N : ℕ) (f : (ZMod g)[X])
    (hf : f ∈ sqSet g N) : f ≠ 0 ∧ f.natDegree = N := by
  unfold sqSet at hf
  rw [Finset.mem_filter, Finset.mem_image] at hf
  obtain ⟨⟨c, -, rfl⟩, -⟩ := hf
  have h : (∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).degree < N := degree_sum_fin_lt c
  refine ⟨(monic_X_pow_add h).ne_zero, ?_⟩
  rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]

theorem torusCard_bounds_mul : ∀ (g : ℕ) [Fact g.Prime], (∀ (N : ℕ), ∀ f ∈ sqSet g N, 0 < torusCard g f ∧ torusCard g f ≤ g ^ N ∧ (degType g f).sum = N ∧ ∀ d ∈ degType g f, 0 < d) ∧ (∀ h f : (ZMod g)[X], h ≠ 0 → f ≠ 0 → degType g (h * f) = degType g h + degType g f ∧ torusCard g (h * f) = torusCard g h * torusCard g f) ∧ ∀ P : (ZMod g)[X], Irreducible P → degType g P = {P.natDegree} ∧ torusCard g P = g ^ P.natDegree - 1 := by
  intro g hg
  refine ⟨fun N f hf => ?_, fun h f hh hf => ?_, fun P hP => ?_⟩
  · obtain ⟨h0, hN⟩ := ne_zero_natDegree_of_mem_sqSet g N f hf
    have hs : (degType g f).sum = N := (degType_sum g f h0).trans hN
    refine ⟨?_, ?_, hs, degType_pos g f⟩
    · unfold torusCard
      apply Multiset.prod_pos
      intro a ha
      obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.1 ha
      exact Nat.sub_pos_of_lt (Nat.one_lt_pow (degType_pos g f d hd).ne' hg.out.one_lt)
    · rw [← hs]
      exact prod_pow_sub_one_le g _
  · have hd : degType g (h * f) = degType g h + degType g f := by
      unfold degType
      rw [UniqueFactorizationMonoid.normalizedFactors_mul hh hf, Multiset.map_add (f := _)]
    refine ⟨hd, ?_⟩
    unfold torusCard
    rw [hd, Multiset.map_add (f := _), Multiset.prod_add]
  · have hd : degType g P = {P.natDegree} := by
      unfold degType
      rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hP, Multiset.map_singleton]
      congr 1
      exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (normalize_associated P))
    refine ⟨hd, ?_⟩
    unfold torusCard
    rw [hd, Multiset.map_singleton, Multiset.prod_singleton]

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassUnionBounds
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem mass_eq_sum_ite_union (g : ℕ) [Fact g.Prime] (N : ℕ) (A : (ZMod g)[X] → Prop) :
    mass g N A = ∑ f ∈ sqSet g N, if A f then ((torusCard g f : ℝ))⁻¹ else 0 := by
  unfold mass
  rw [Finset.sum_filter]

theorem mass_union_bounds : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ), (∀ A B : (ZMod g)[X] → Prop, (∀ f ∈ sqSet g N, A f → B f) → mass g N A ≤ mass g N B) ∧ (∀ A, 0 ≤ mass g N A) ∧ (∀ (κ : Type) (s : Finset κ) (A : (ZMod g)[X] → Prop) (B : κ → (ZMod g)[X] → Prop), (∀ f ∈ sqSet g N, A f → ∃ i ∈ s, B i f) → mass g N A ≤ ∑ i ∈ s, mass g N (B i)) ∧ ∀ A : (ZMod g)[X] → Prop, mass g N A + mass g N (fun f => ¬ A f) = mass g N fun _ => True := by
  intro g _ N
  have hw : ∀ f : (ZMod g)[X], (0 : ℝ) ≤ ((torusCard g f : ℝ))⁻¹ := fun f => by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B h
    simp only [mass_eq_sum_ite_union]
    refine Finset.sum_le_sum fun f hf => ?_
    by_cases hA : A f
    · rw [if_pos hA, if_pos (h f hf hA)]
    · rw [if_neg hA]
      split_ifs
      · exact hw f
      · exact le_rfl
  · intro A
    exact Finset.sum_nonneg fun f _ => hw f
  · intro κ s A B h
    simp only [mass_eq_sum_ite_union]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun f hf => ?_
    have hn : ∀ i ∈ s, (0 : ℝ) ≤ if B i f then ((torusCard g f : ℝ))⁻¹ else 0 := by
      intro i _
      split_ifs
      · exact hw f
      · exact le_rfl
    by_cases hA : A f
    · obtain ⟨i, hi, hB⟩ := h f hf hA
      rw [if_pos hA]
      have := Finset.single_le_sum hn hi
      simpa only [if_pos hB] using this
    · rw [if_neg hA]
      exact Finset.sum_nonneg hn
  · intro A
    rw [mass_eq_sum_ite_union, mass_eq_sum_ite_union, mass_eq_sum_ite_union, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases hA : A f <;> simp [hA]

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerExpSlashUpperTriangularEqSubst
section
namespace GlobalTheory.CyclotomicQExpansion
open GlobalTheory.KZ

theorem exp_sl_upper (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (g : GQ) (hg : ent g 1 0 = 0) (f : X.K) :
    X.exp (X.sl g f) = sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp f) := by
  have hdet : 0 < ent g 0 0 * ent g 1 1 := by
    have h := g.2
    have h' : 0 < Matrix.det ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := h
    rw [Matrix.det_fin_two] at h'
    simp only [ent] at hg ⊢
    rw [hg, mul_zero, sub_zero] at h'
    exact h'
  have hd : ent g 1 1 ≠ 0 := by
    rintro h0; rw [h0, mul_zero] at hdet; exact lt_irrefl _ hdet
  have ha : ent g 0 0 ≠ 0 := by
    rintro h0; rw [h0, zero_mul] at hdet; exact lt_irrefl _ hdet
  have hpos : 0 < ent g 0 0 / ent g 1 1 := by
    have : ent g 0 0 / ent g 1 1 = (ent g 0 0 * ent g 1 1) / (ent g 1 1) ^ 2 := by field_simp
    rw [this]; exact div_pos hdet (by positivity)
  ext s
  unfold sub scale
  rw [dite_eq_left hpos]
  set e := (OrderIso.mulLeft₀ (ent g 0 0 / ent g 1 1) hpos).toOrderEmbedding with he
  have hs : s = e (s * ent g 1 1 / ent g 0 0) := by
    simp only [he, RelIso.coe_toRelEmbedding, OrderIso.coe_toOrderEmbedding, OrderIso.mulLeft₀_apply]
    field_simp
  rw [hs, HahnSeries.embDomain_coeff]
  have key := X.exp_upper g hg f (s * ent g 1 1 / ent g 0 0)
  have h2 : s * ent g 1 1 / ent g 0 0 * ent g 0 0 / ent g 1 1 = e (s * ent g 1 1 / ent g 0 0) := by
    rw [← hs]; field_simp
  rw [h2] at key
  rw [key]
  rfl

end GlobalTheory.CyclotomicQExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceTowerAlmostDualBasesAdjoinKummerRootStatement
section
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceTower_almostDualBases_adjoin_kummer_root : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt (p := p) r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∀ (ι : Type) [Fintype ι] (u v : ι → Ω), (∀ k, u k ∈ FixI (Hfix T r)) → (∀ k, v k ∈ FixI (Hfix T r)) →
  ∑ k, u k * v k = (p : Ω) → (∀ h ∈ Hinf T, h r ≠ r → ∑ k, u k * h (v k) = 0) →
  ∃ tr : Ω → Ω, DualData (FixI (Hinf T)) (FixI (Hfix T r)) u v tr := by
  first | exact @GlobalTheory.traceTower_dualData | exact GlobalTheory.traceTower_dualData | (intros; apply GlobalTheory.traceTower_dualData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationTowerZetaSubOneStatement
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_tower_zeta_sub_one : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → ∀ (T : Tower p Ω) (v : Valuation Ω ℝ≥0), v (p : Ω) < 1 → ∀ n : ℕ, 1 ≤ n → v (T.ζ n - 1) < 1 ∧ v (p : Ω) ≤ v (T.ζ 1 - 1) * v (T.ζ n - 1) := by
  first | exact @GlobalTheory.K5.ZetaNonvanishing₂.valuation_zeta_sub_one | exact GlobalTheory.K5.ZetaNonvanishing₂.valuation_zeta_sub_one | (intros; apply GlobalTheory.K5.ZetaNonvanishing₂.valuation_zeta_sub_one <;> assumption)
end

