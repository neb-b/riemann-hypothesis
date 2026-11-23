module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerLevelEqPowMulHeckeV
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem qExpansionFunction_coeffHeckeVOperator_eq_tsum (l : ℕ) (hl : 0 < l) (a : ℕ → ℂ) (τ : ℍ) :
    qs (Vo l a) τ = ∑' m : ℕ, a m * cexp (2 * π * Complex.I * m * ((l : ℂ) * τ)) := by
  unfold qs Vo
  have hinj : Function.Injective (fun m : ℕ => l * m) := fun x y h => by
    simpa [hl.ne'] using h
  rw [← hinj.tsum_eq]
  · congr 1; ext m
    simp only [dvd_mul_right, if_true, Nat.mul_div_cancel_left m hl]
    congr 2; push_cast; ring
  · intro n hn
    by_cases h : l ∣ n
    · obtain ⟨m, rfl⟩ := h; exact ⟨m, rfl⟩
    · simp [Function.mem_support, h] at hn

theorem adjU_sum (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ) (hk : 1 ≤ k) (hl : 0 < l)
    (hf : MF k N (ch ε) h) (τ : ℍ) :
    ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ = (l : ℂ) ^ k * qs (Vo l h) τ := by
  have hlC : (0 : ℝ) < l := by exact_mod_cast hl
  let τ' : ℍ := ⟨(l : ℂ) * τ, by simpa using mul_pos hlC τ.im_pos⟩
  have hτ' : (τ' : ℂ) = (l : ℂ) * τ := rfl
  have key : ∀ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ = (l : ℂ) ^ (k - 1) * qs h τ' := by
    intro j
    let γ : SL(2, ℤ) := ⟨!![1, 0; (N * (j : ℕ) : ℤ), 1], by simp [Matrix.det_fin_two]⟩
    have hγ := hf.2 γ (by simp [γ]) τ'
    have hpt : ((γ • τ' : ℍ) : ℂ) = ((l : ℂ) * τ) / (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) := by
      rw [coe_specialLinearGroup_apply]; simp [γ, hτ']; ring
    have hden : ((((N * (j : ℕ) : ℤ)) : ℂ) * (τ' : ℂ) + 1) = (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) := by
      rw [hτ']; push_cast; ring
    have hne : (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      rcases this with h1 | h1
      · have h2 : N * l * (j : ℕ) = 0 := by rcases h1 with (h1 | h1) | h1 <;> simp [h1]
        simp [h2] at h0
      · exact (τ.im_pos.ne' h1)
    have hγ' : qs h (γ • τ') = (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) ^ k * qs h τ' := by
      rw [← hden, hγ]; simp [γ, ch]
    have harg : ((l : ℂ) * τ / ((N : ℂ) * l * ((j : ℕ) : ℂ) * τ + 1)) = ((γ • τ' : ℍ) : ℂ) := by
      rw [hpt]; push_cast; ring
    unfold slz repL
    simp [Matrix.det_fin_two]
    rw [harg, ofComplex_apply, hγ']
    push_cast at hne ⊢
    field_simp
  simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [qExpansionFunction_coeffHeckeVOperator_eq_tsum l hl h τ]
  have hp : (l : ℂ) * (l : ℂ) ^ (k - 1) = (l : ℂ) ^ k := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  rw [← mul_assoc, hp]
  rfl
end GlobalTheory.EisM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableCardDivisorsSqDivOneAddRpow
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.DivSq

theorem four_factors {n x y : ℕ} (hx : x ∣ n) (hy : y ∣ n) (hn : n ≠ 0) :
    ∃ a b c e : ℕ, a * b * c * e = n ∧ a * b = x ∧ a * c = y := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hn (by simpa using hx)
  obtain ⟨e, he⟩ := Nat.lcm_dvd hx hy
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_left x y
  obtain ⟨c, hc⟩ := Nat.gcd_dvd_right x y
  refine ⟨Nat.gcd x y, b, c, e, ?_, hb.symm, hc.symm⟩
  have hg : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hx0)
  have h1 := Nat.gcd_mul_lcm x y
  have h2 : Nat.gcd x y * b * c = Nat.lcm x y := by
    apply Nat.eq_of_mul_eq_mul_left hg
    rw [h1]
    calc Nat.gcd x y * (Nat.gcd x y * b * c) = (Nat.gcd x y * b) * (Nat.gcd x y * c) := by ring
      _ = x * y := by rw [← hb, ← hc]
  rw [h2, ← he]

theorem inv_rpow_natCast_mul (p : ℝ) (a b : ℕ) :
    ((((a * b : ℕ)) : ℝ) ^ p)⁻¹ = ((a : ℝ) ^ p)⁻¹ * ((b : ℝ) ^ p)⁻¹ := by
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity), mul_inv]

theorem sum_range_le_pow (p : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ p
      ≤ (∑ n ∈ Finset.range N, ((n : ℝ) ^ p)⁻¹) ^ 4 := by
  classical
  set I := Finset.range N with hI
  let φ : ℕ × ℕ × ℕ × ℕ → (Σ _ : ℕ, ℕ × ℕ) :=
    fun q => ⟨q.1 * q.2.1 * q.2.2.1 * q.2.2.2, q.1 * q.2.1, q.1 * q.2.2.1⟩
  let w : (Σ _ : ℕ, ℕ × ℕ) → ℝ := fun s => ((s.1 : ℝ) ^ p)⁻¹
  have hw : ∀ s, 0 ≤ w s := fun s => by simp only [w]; positivity
  have h1 : ∑ n ∈ I, ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ p
      = ∑ s ∈ I.sigma (fun n => n.divisors ×ˢ n.divisors), w s := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [w, Finset.sum_const, Finset.card_product, nsmul_eq_mul]
    push_cast
    ring
  have h2 : I.sigma (fun n => n.divisors ×ˢ n.divisors) ⊆ (I ×ˢ I ×ˢ I ×ˢ I).image φ := by
    rintro ⟨n, x, y⟩ hs
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisors, hI, Finset.mem_range] at hs
    obtain ⟨hnN, ⟨hx, hn⟩, hy, -⟩ := hs
    obtain ⟨a, b, c, e, rfl, rfl, rfl⟩ := four_factors hx hy hn
    have key : ∀ d, d ∣ a * b * c * e → d ∈ I := fun d hd => by
      rw [hI, Finset.mem_range]
      exact lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) hnN
    refine Finset.mem_image.2 ⟨(a, b, c, e), ?_, rfl⟩
    simp only [Finset.mem_product]
    exact ⟨key _ ⟨b * c * e, by ring⟩, key _ ⟨a * c * e, by ring⟩, key _ ⟨a * b * e, by ring⟩,
      key _ ⟨a * b * c, by ring⟩⟩
  have h3 : ∑ s ∈ (I ×ˢ I ×ˢ I ×ˢ I).image φ, w s ≤ ∑ q ∈ I ×ˢ I ×ˢ I ×ˢ I, w (φ q) :=
    Finset.sum_image_le_of_nonneg (fun s _ => hw s)
  have h4 : ∑ q ∈ I ×ˢ I ×ˢ I ×ˢ I, w (φ q) = (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) ^ 4 := by
    have : (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) ^ 4 = (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) *
      ((∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) * ((∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) * (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹))) := by
      ring
    rw [this]
    rw [Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_product, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [w, φ]
    rw [inv_rpow_natCast_mul, inv_rpow_natCast_mul, inv_rpow_natCast_mul]
    ring
  rw [h1, ← h4]
  exact (Finset.sum_le_sum_of_subset_of_nonneg h2 fun s _ _ => hw s).trans h3

theorem summable_card_divisors_sq_div_rpow :
    ∀ s : ℝ, 0 < s → Summable fun n : ℕ => ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ (1 + s) := by
  intro s hs
  have hz : Summable fun n : ℕ => ((n : ℝ) ^ (1 + s))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  refine summable_of_sum_range_le (c := (∑' n : ℕ, ((n : ℝ) ^ (1 + s))⁻¹) ^ 4)
    (fun n => by positivity) fun N => ?_
  refine (sum_range_le_pow (1 + s) N).trans ?_
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => by positivity)
    (hz.sum_le_tsum _ fun n _ => by positivity) 4

end GlobalTheory.DivSq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummablePeriodicMulInvSubInvFloor
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem norm_inv_add_int_sub_inv_add_int_le (z : ℂ) (L : ℝ) (d m : ℤ)
    (hm : |(m : ℝ) - d| ≤ L) (hd : 2 * (‖z‖ + L) + 1 ≤ |(d : ℝ)|) :
    ‖(z + d)⁻¹ - (z + m)⁻¹‖ ≤ 4 * L * (1 / (d : ℝ) ^ 2) := by
  have hL : 0 ≤ L := (abs_nonneg _).trans hm
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  have key : ∀ x : ℤ, |(x : ℝ)| - ‖z‖ ≤ ‖z + x‖ := by
    intro x
    have h1 : ‖(x : ℂ)‖ ≤ ‖z + x‖ + ‖z‖ := by
      have := norm_sub_le (z + x) z
      simpa using this
    have h2 : ‖(x : ℂ)‖ = |(x : ℝ)| := Complex.norm_intCast x
    linarith
  have hdm : |(d : ℝ)| - L ≤ |(m : ℝ)| := by
    have := abs_sub_abs_le_abs_sub (d : ℝ) m
    rw [abs_sub_comm] at this
    linarith
  have hD : 0 < |(d : ℝ)| / 2 := by linarith
  have h1 : |(d : ℝ)| / 2 ≤ ‖z + d‖ := by have := key d; linarith
  have h2 : |(d : ℝ)| / 2 ≤ ‖z + m‖ := by have := key m; linarith
  have n1 : z + d ≠ 0 := norm_pos_iff.1 (hD.trans_le h1)
  have n2 : z + m ≠ 0 := norm_pos_iff.1 (hD.trans_le h2)
  have e : (z + d)⁻¹ - (z + m)⁻¹ = ((m - d : ℤ) : ℂ) / ((z + d) * (z + m)) := by
    push_cast
    field_simp
    ring
  rw [e, norm_div, norm_mul, Complex.norm_intCast]
  push_cast
  calc |(m : ℝ) - d| / (‖z + d‖ * ‖z + m‖)
      ≤ L / (|(d : ℝ)| / 2 * (|(d : ℝ)| / 2)) := by
        gcongr
    _ = 4 * L * (1 / (d : ℝ) ^ 2) := by
        have : |(d : ℝ)| ≠ 0 := (by linarith : 0 < |(d : ℝ)|).ne'
        rw [← sq_abs (d : ℝ)]
        field_simp
        ring

theorem summable_periodic_mul_inv_sub_inv_floor :
    ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im →
      Summable (fun d : ℤ => φ d * ((z + d)⁻¹ - (z + (L * (d / L) : ℤ))⁻¹)) := by
  intro L φ z hL _
  haveI : NeZero L := ⟨hL.ne'⟩
  set M : ℝ := ∑ y, ‖φ y‖ with hM
  have hφ : ∀ y, ‖φ y‖ ≤ M := fun y =>
    Finset.single_le_sum (f := fun y => ‖φ y‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ y)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hφ 0)
  have hs : Summable (fun d : ℤ => M * (4 * (L : ℝ) * (1 / (d : ℝ) ^ 2))) :=
    ((Real.summable_one_div_int_pow.2 one_lt_two).mul_left _).mul_left _
  refine Summable.of_norm_bounded_eventually hs ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * (‖z‖ + L) + 1)
  have hfin : (Set.Icc (-(N : ℤ)) N).Finite := Set.finite_Icc _ _
  refine Filter.mem_of_superset hfin.compl_mem_cofinite ?_
  intro d hd
  have hd' : (N : ℤ) ≤ |d| := by
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hd
    rcases hd with h | h
    · exact le_abs.2 (Or.inr (by omega))
    · exact le_abs.2 (Or.inl h.le)
  have hd'' : (N : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast hd'
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  have hm : |(L : ℤ) * (d / L) - d| ≤ L := by
    have a := Int.emod_nonneg d hL'.ne'
    have b := Int.emod_lt_of_pos d hL'
    have c := Int.emod_def d L
    rw [abs_le]
    constructor <;> linarith
  have hm' : |(((L : ℤ) * (d / L) : ℤ) : ℝ) - d| ≤ (L : ℝ) := by exact_mod_cast hm
  have := norm_inv_add_int_sub_inv_add_int_le z L d _ hm' (hN.trans hd'')
  show ‖_‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul (hφ _) this (norm_nonneg _) hM0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoAtTopOfCofinite
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.RowLim

noncomputable def symS (f : ℤ → ℂ) (R : ℕ) : ℂ := ∑ d ∈ Finset.Icc (-(R : ℤ)) R, f d

lemma symS_succ (f : ℤ → ℂ) (R : ℕ) :
    symS f (R + 1) = f (-((R : ℤ) + 1)) + (f ((R : ℤ) + 1) + symS f R) := by
  unfold symS
  have h : Finset.Icc (-((R + 1 : ℕ) : ℤ)) ((R + 1 : ℕ) : ℤ)
      = insert (-((R : ℤ) + 1)) (insert ((R : ℤ) + 1) (Finset.Icc (-(R : ℤ)) R)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
  rw [h, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
    Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]

lemma symS_shift_one (f : ℤ → ℂ) (R : ℕ) :
    symS (fun d => f (d + 1)) R - symS f R = f ((R : ℤ) + 1) - f (-(R : ℤ)) := by
  induction R with
  | zero => simp [symS]
  | succ R ih =>
    rw [symS_succ, symS_succ]
    push_cast
    have e1 : -((R : ℤ) + 1) + 1 = -(R : ℤ) := by ring
    rw [e1]
    linear_combination ih

lemma tendsto_atTop_of_cofinite {f : ℤ → ℂ} (hf : Tendsto f cofinite (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := hf.mono_left (by rw [Int.cofinite_eq]; exact le_sup_right)

lemma tendsto_atBot_of_cofinite {f : ℤ → ℂ} (hf : Tendsto f cofinite (𝓝 0)) :
    Tendsto f atBot (𝓝 0) := hf.mono_left (by rw [Int.cofinite_eq]; exact le_sup_left)

lemma shift_tendsto {f : ℤ → ℂ} (hf : Tendsto f cofinite (𝓝 0)) (r : ℤ) :
    Tendsto (fun d => f (d + r)) cofinite (𝓝 0) :=
  hf.comp (add_left_injective r).tendsto_cofinite

lemma symS_shift_tendsto (r : ℕ) : ∀ f : ℤ → ℂ, Tendsto f cofinite (𝓝 0) →
    Tendsto (fun R => symS (fun d => f (d + r)) R - symS f R) atTop (𝓝 0) := by
  induction r with
  | zero => intro f _; simp
  | succ r ih =>
    intro f hf
    have h1 := ih (fun e => f (e + 1)) (shift_tendsto hf 1)
    have hR : Tendsto (fun R : ℕ => (R : ℤ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun R : ℕ => f ((R : ℤ) + 1) - f (-(R : ℤ))) atTop (𝓝 0) := by
      have a := (tendsto_atTop_of_cofinite hf).comp (tendsto_atTop_add_const_right _ 1 hR)
      have b := (tendsto_atBot_of_cofinite hf).comp (tendsto_neg_atTop_atBot.comp hR)
      simpa using a.sub b
    have := h1.add ((tendsto_congr (fun R => (symS_shift_one f R).symm)).1 h2)
    rw [add_zero] at this
    refine (tendsto_congr fun R => ?_).1 this
    have e : (fun d : ℤ => f (d + ((r + 1 : ℕ) : ℤ))) = fun d => f (d + (r : ℤ) + 1) := by
      funext d; push_cast; ring_nf
    beta_reduce
    rw [e]; ring

noncomputable def mean (L : ℕ) (k : ℤ → ℂ) (d : ℤ) : ℂ := (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, k (d + r)

lemma mean_tendsto {L : ℕ} {k : ℤ → ℂ} (hk : Tendsto k cofinite (𝓝 0)) :
    Tendsto (mean L k) cofinite (𝓝 0) := by
  have : Tendsto (fun d => ∑ r ∈ Finset.range L, k (d + r)) cofinite (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range L) fun r _ => shift_tendsto hk r
  have h2 := this.const_mul ((L : ℂ)⁻¹)
  rw [mul_zero] at h2
  exact h2

lemma bdd_mul_tendsto {A k : ℤ → ℂ} {C : ℝ} (hA : ∀ d, ‖A d‖ ≤ C)
    (hk : Tendsto k cofinite (𝓝 0)) : Tendsto (fun d => A d * k d) cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at hk ⊢
  refine squeeze_zero (fun _ => norm_nonneg _) (fun d => ?_) (by simpa using hk.const_mul C)
  rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hA d) (norm_nonneg _)

lemma symS_mul_mean_tendsto {L : ℕ} {A k : ℤ → ℂ} {C : ℝ} (hA : ∀ d, ‖A d‖ ≤ C)
    (hsum : ∀ d, ∑ r ∈ Finset.range L, A (d - r) = 0) (hk : Tendsto k cofinite (𝓝 0)) :
    Tendsto (symS fun d => A d * mean L k d) atTop (𝓝 0) := by
  set f : ℕ → ℤ → ℂ := fun r e => A (e - r) * k e with hf
  have eq : ∀ R, symS (fun d => A d * mean L k d) R
      = (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, (symS (fun d => f r (d + r)) R - symS (f r) R) := by
    intro R
    have h0 : ∑ r ∈ Finset.range L, symS (f r) R = 0 := by
      simp only [symS, hf]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [← Finset.sum_mul, hsum, zero_mul]
    rw [Finset.sum_sub_distrib, h0, sub_zero]
    simp only [symS, mean, hf, add_sub_cancel_right]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [show (symS fun d => A d * mean L k d) = _ from funext eq]
  have := tendsto_finsetSum (Finset.range L) fun r _ =>
    symS_shift_tendsto r (f r) (bdd_mul_tendsto (fun d => hA (d - r)) hk)
  simpa using this.const_mul ((L : ℂ)⁻¹)

theorem rowlim : ∀ (L : ℕ) (A g : ℤ → ℂ) (G : ℤ × ℤ → ℂ) (c : ℤ), 0 < L → (∃ C : ℝ, ∀ d, ‖A d‖ ≤ C) → (∀ d, ∑ r ∈ Finset.range L, A (d - r) = 0) → (∀ d, G (c, d) = g d) → Tendsto g cofinite (𝓝 0) → (Summable fun d : ℤ => A d * dif L (0, 1) (dif L (0, 1) G) (c, d)) → Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, A d * g d) atTop (𝓝 (∑' d : ℤ, A d * dif L (0, 1) (dif L (0, 1) G) (c, d))) := by
  intro L A g G c _ ⟨C, hA⟩ hsum hG hg hS
  have hpt : ∀ (F : ℤ × ℤ → ℂ) (d : ℤ), dif L (0, 1) F (c, d) = F (c, d) - mean L (fun e => F (c, e)) d := by
    intro F d
    have e : ∀ r : ℕ, (c, d) + (r : ℤ) • ((0 : ℤ), (1 : ℤ)) = (c, d + r) := by
      intro r; ext <;> simp
    simp only [dif, mean, e]
  set h : ℤ → ℂ := fun d => g d - mean L g d with hh
  have hG1 : ∀ d, dif L (0, 1) G (c, d) = h d := by
    intro d; rw [hpt]; simp only [hh, hG]
  have hG2 : ∀ d, dif L (0, 1) (dif L (0, 1) G) (c, d) = h d - mean L h d := by
    intro d; rw [hpt, hG1]; simp only [hG1]
  simp only [hG2] at hS ⊢
  have hTs := (hS.hasSum.comp Finset.tendsto_Icc_neg)
  have hh0 : Tendsto h cofinite (𝓝 0) := by simpa using hg.sub (mean_tendsto hg)
  have k1 := symS_mul_mean_tendsto hA hsum hg
  have k2 := symS_mul_mean_tendsto hA hsum hh0
  have := (hTs.add k1).add k2
  rw [add_zero, add_zero] at this
  refine (tendsto_congr fun R => ?_).1 this
  simp only [Function.comp, symS, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [hh]; ring

end GlobalTheory.RowLim
end

