module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ContDiffAndFderivTsumFourierOfRapid
section
open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory
namespace RapidFourier

noncomputable def linForm {n : ℕ} (ν : Fin n → ℤ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ k, (ν k : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k

theorem linForm_apply {n : ℕ} (ν : Fin n → ℤ) (x : Fin n → ℝ) :
    linForm ν x = ∑ k, (ν k : ℝ) * x k := by
  simp [linForm]

theorem norm_linForm_le {n : ℕ} (ν : Fin n → ℤ) : ‖linForm ν‖ ≤ ∑ k, |(ν k : ℝ)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun k _ => abs_nonneg _) fun x => ?_
  calc ‖linForm ν x‖ = |∑ k, (ν k : ℝ) * x k| := by rw [linForm_apply, Real.norm_eq_abs]
    _ ≤ ∑ k, |(ν k : ℝ) * x k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |(ν k : ℝ)| * ‖x‖ := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x k)
          (abs_nonneg _)
    _ = (∑ k, |(ν k : ℝ)|) * ‖x‖ := by rw [Finset.sum_mul]

noncomputable def wave (a : ℂ) (t : ℝ) : ℂ := a * cexp (2 * π * I * t)

theorem hasDerivAt_wave (a : ℂ) (t : ℝ) :
    HasDerivAt (wave a) (wave (2 * π * I * a) t) t := by
  have h := (((hasDerivAt_id (t : ℂ)).const_mul (2 * π * I)).cexp.const_mul a).comp_ofReal
  convert (preTransparency := .reducible) h using 1
  · funext y
    simp [wave]
  · simp only [wave, id]
    ring

theorem contDiff_wave (a : ℂ) : ContDiff ℝ ∞ (wave a) := by
  have h : ContDiff ℝ ∞ fun t : ℝ => ((t : ℝ) : ℂ) := Complex.ofRealCLM.contDiff
  exact contDiff_const.mul ((contDiff_const.mul h).cexp)

theorem iteratedDeriv_wave (m : ℕ) (a : ℂ) :
    iteratedDeriv m (wave a) = wave ((2 * π * I) ^ m * a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [(hasDerivAt_wave _ t).deriv, pow_succ]
    ring_nf

theorem norm_wave (a : ℂ) (t : ℝ) : ‖wave a t‖ = ‖a‖ := by
  have h : (2 * π * I * t : ℂ) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [wave, norm_mul, h, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem norm_two_pi_I : ‖(2 * π * I : ℂ)‖ = 2 * π := by
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    mul_one]
  norm_num

theorem term_eq {n : ℕ} (a : ℂ) (ν : Fin n → ℤ) (x : Fin n → ℝ) :
    a * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) = wave a (linForm ν x) := by
  rw [wave, linForm_apply]
  push_cast
  rfl

theorem norm_iteratedFDeriv_term_le {n : ℕ} (a : ℂ) (ν : Fin n → ℤ) (m : ℕ) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ m (wave a ∘ linForm ν) x‖
      ≤ (2 * π) ^ m * (‖a‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m) := by
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ (contDiff_wave a) x
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_wave, norm_wave, norm_mul,
    norm_pow, norm_two_pi_I, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hL : ‖linForm ν‖ ≤ 1 + ∑ k, |(ν k : ℝ)| := (norm_linForm_le ν).trans (le_add_of_nonneg_left zero_le_one)
  have hpow : ‖linForm ν‖ ^ m ≤ (1 + ∑ k, |(ν k : ℝ)|) ^ m := pow_le_pow_left₀ (norm_nonneg _) hL m
  calc (2 * π) ^ m * ‖a‖ * ‖linForm ν‖ ^ m ≤ (2 * π) ^ m * ‖a‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (2 * π) ^ m * (‖a‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m) := by ring

theorem summable_inv_one_add_abs_sq : Summable fun m : ℤ => ((1 + |(m : ℝ)|) ^ 2)⁻¹ := by
  have hN : Summable fun k : ℕ => ((1 + (k : ℝ)) ^ 2)⁻¹ := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr one_lt_two)
    refine h.congr fun k => ?_
    push_cast
    ring_nf
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hN.congr fun k => ?_
    simp
  · refine hN.congr fun k => ?_
    simp

theorem summable_inv_pow (n : ℕ) :
    Summable fun ν : Fin n → ℤ => ((1 + ∑ k, |(ν k : ℝ)|) ^ (2 * n))⁻¹ := by
  have hprod : Summable fun ν : Fin n → ℤ => ∏ k, ((1 + |(ν k : ℝ)|) ^ 2)⁻¹ :=
    GlobalTheory.summable_pi_prod_of_nonneg (f := fun _ (m : ℤ) => ((1 + |(m : ℝ)|) ^ 2)⁻¹)
      (fun _ _ => by positivity) fun _ => summable_inv_one_add_abs_sq
  refine Summable.of_nonneg_of_le (fun ν => by positivity) (fun ν => ?_) hprod
  rw [Finset.prod_inv_distrib]
  apply inv_anti₀ (Finset.prod_pos fun k _ => by positivity)
  calc ∏ k, (1 + |(ν k : ℝ)|) ^ 2 ≤ ∏ _k : Fin n, (1 + ∑ k, |(ν k : ℝ)|) ^ 2 :=
        Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ =>
          pow_le_pow_left₀ (by positivity)
            (add_le_add le_rfl (Finset.single_le_sum (f := fun k => |(ν k : ℝ)|)
              (fun _ _ => abs_nonneg _) (Finset.mem_univ k))) 2
    _ = (1 + ∑ k, |(ν k : ℝ)|) ^ (2 * n) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]

theorem summable_weighted {n : ℕ} {c : (Fin n → ℤ) → ℂ}
    (hc : ∀ N : ℕ, ∃ C : ℝ, ∀ ν, ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N ≤ C) (m : ℕ) :
    Summable fun ν => ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m := by
  obtain ⟨C, hC⟩ := hc (m + 2 * n)
  refine Summable.of_nonneg_of_le (fun ν => by positivity) (fun ν => ?_)
    ((summable_inv_pow n).mul_left C)
  have hpos : 0 < (1 + ∑ k, |(ν k : ℝ)|) ^ (2 * n) := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_assoc, ← pow_add]
  exact hC ν

theorem hasFDerivAt_term {n : ℕ} (a : ℂ) (ν : Fin n → ℤ) (x : Fin n → ℝ) :
    HasFDerivAt (wave a ∘ linForm ν)
      ((linForm ν).smulRight (wave (2 * π * I * a) (linForm ν x))) x := by
  have h := (hasDerivAt_wave a (linForm ν x)).hasFDerivAt.comp x (linForm ν).hasFDerivAt
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp

end RapidFourier


open RapidFourier in
theorem contDiff_and_fderiv_tsum_fourier_of_rapid :
    ∀ (n : ℕ) (c : (Fin n → ℤ) → ℂ), (∀ N : ℕ, ∃ C : ℝ, ∀ ν, ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N ≤ C) → ContDiff ℝ ∞ (fun x : Fin n → ℝ => ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))) ∧ ∀ (x : Fin n → ℝ) (j : Fin n), fderiv ℝ (fun x : Fin n → ℝ => ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))) x (Pi.single j 1) = ∑' ν, 2 * π * I * (ν j : ℂ) * c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) :=
  open RapidFourier in
  by
  intro n c hc
  have hfun : (fun x : Fin n → ℝ => ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))) =
      fun x => ∑' ν, (wave (c ν) ∘ linForm ν) x := by
    funext x
    exact tsum_congr fun ν => term_eq (c ν) ν x
  have hL : ∀ ν : Fin n → ℤ, ‖linForm ν‖ ≤ 1 + ∑ k, |(ν k : ℝ)| := fun ν =>
    (norm_linForm_le ν).trans (le_add_of_nonneg_left zero_le_one)
  have hsum : ∀ m : ℕ, Summable fun ν : Fin n → ℤ =>
      (2 * π) ^ m * (‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m) := fun m =>
    (summable_weighted hc m).mul_left _
  have hD : ∀ (ν : Fin n → ℤ) (y : Fin n → ℝ),
      ‖(linForm ν).smulRight (wave (2 * π * I * c ν) (linForm ν y))‖ ≤
        (2 * π) ^ 1 * (‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ 1) := by
    intro ν y
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_wave, norm_mul, norm_two_pi_I, pow_one,
      pow_one]
    calc ‖linForm ν‖ * (2 * π * ‖c ν‖) ≤ (1 + ∑ k, |(ν k : ℝ)|) * (2 * π * ‖c ν‖) :=
          mul_le_mul_of_nonneg_right (hL ν) (by positivity)
      _ = 2 * π * (‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|)) := by ring
  rw [hfun]
  refine ⟨contDiff_tsum (fun ν => (contDiff_wave (c ν)).comp (linForm ν).contDiff)
    (fun m _ => hsum m) (fun m ν x _ => norm_iteratedFDeriv_term_le (c ν) ν m x), fun x j => ?_⟩
  have h0 : Summable fun ν : Fin n → ℤ => (wave (c ν) ∘ linForm ν) x := by
    refine Summable.of_norm_bounded (hsum 0) fun ν => ?_
    simp [norm_wave]
  have hder := hasFDerivAt_tsum (hsum 1) (fun ν y => hasFDerivAt_term (c ν) ν y) hD h0 x
  have hs : Summable fun ν : Fin n → ℤ =>
      (linForm ν).smulRight (wave (2 * π * I * c ν) (linForm ν x)) :=
    Summable.of_norm_bounded (hsum 1) fun ν => hD ν x
  have hap := (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1 : ℝ))).map_tsum hs
  simp only [ContinuousLinearMap.apply_apply] at hap
  rw [hder.fderiv, hap]
  refine tsum_congr fun ν => ?_
  rw [ContinuousLinearMap.smulRight_apply, ← term_eq, linForm_apply]
  simp [Pi.single_apply, Complex.real_smul]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIntegralOfLocalPresentationPow
section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_pow_mul_one_sub_mem_map_maximalIdeal (O H : Type) [CommRing O] [IsLocalRing O]
    [CommRing H] [Algebra O H] [Module.Finite O H] (u : H) :
    ∃ (N : ℕ) (y : H), u ^ N * (1 - y * u) ∈ (IsLocalRing.maximalIdeal O).map (algebraMap O H) := by
  set m := IsLocalRing.maximalIdeal O
  set J := m.map (algebraMap O H)
  letI : Field (O ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite (O ⧸ m) (H ⧸ J) := Module.Finite.of_restrictScalars_finite O _ _
  haveI : IsArtinianRing (H ⧸ J) := IsArtinianRing.of_finite (O ⧸ m) _
  obtain ⟨N, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (R := H ⧸ J) (M := H ⧸ J)
    (Ideal.Quotient.mk J u) 1
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨N, y, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one, pow_succ] at hy
  simp only [map_mul, map_pow, map_sub, map_one]
  linear_combination -hy

theorem exists_mul_kills_ker_of_localization (O H : Type) [CommRing O] [CommRing H] [Algebra O H]
    [Module.Finite O H] (ε : H →ₐ[O] O) (M : Submonoid H) (T : Type) [CommRing T] [Algebra H T]
    [IsLocalization M T] (u : H) (hu : ∀ h, ε h = 0 → algebraMap H T (h * u) = 0) :
    ∃ s : M, ∀ h, ε h = 0 → h * (s * u) = 0 := by
  classical
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := O) (M := H)
  have h1 : ∀ b : H, ∃ s : M, (s : H) * ((b - algebraMap O H (ε b)) * u) = 0 := fun b =>
    (IsLocalization.map_eq_zero_iff M T _).1 (hu _ (by simp))
  choose s hs using h1
  refine ⟨∏ b ∈ G, s b, fun h hh => ?_⟩
  have key : ∀ h : H, (h - algebraMap O H (ε h)) * (((∏ b ∈ G, s b : M) : H) * u) = 0 := by
    intro h
    have hmem : h ∈ Submodule.span O (G : Set H) := by rw [hG]; trivial
    induction hmem using Submodule.span_induction with
    | mem b hb =>
      rw [← Finset.mul_prod_erase G s hb, Submonoid.coe_mul]
      linear_combination ((∏ x ∈ G.erase b, s x : M) : H) * hs b
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      linear_combination ha + hb
    | smul c a _ ha =>
      rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def]
      linear_combination algebraMap O H c * ha
  simpa [hh] using key h

theorem exists_integral_of_local_presentation :
    ∀ (O H : Type) [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H] [Module.Finite O H] (ε : H →ₐ[O] O) (g n : ℕ) (T : Type) [CommRing T] [Algebra H T] [Algebra O T] [IsScalarTower O H T] [IsLocalization.AtPrime T ((IsLocalRing.maximalIdeal O).comap ε)] (εT : T →ₐ[O] O), (∀ h, εT (algebraMap H T h) = ε h) → ∀ (S : Type) [CommRing S] [Algebra O S] (π : S →ₐ[O] T) (x : Fin g → S) (a : Matrix (Fin g) (Fin g) S) (ρ : S →+* MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)), Function.Surjective π → RingHom.ker π = Ideal.span (Set.range (a.mulVec x)) → RingHom.ker εT = Ideal.span (Set.range fun i => π (x i)) → (∀ i j, εT (π (a i j)) = if i = j then (n : O) else 0) → (∀ i, ρ (x i) = MvPowerSeries.X i) → (∀ c ∈ IsLocalRing.maximalIdeal O, ρ (algebraMap O S c) = 0) → ∃ l : H, (∀ h, ε h = 0 → h * l = 0) ∧ (n : O) ^ g ∣ ε l ∧ l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H) := by
  intro O H _ _ _ _ _ ε g n T _ _ _ _ _ εT hε S _ _ π x a ρ hπ hker hkerT ha hρx hρm
  classical
  set m := IsLocalRing.maximalIdeal O with hm
  set p : Ideal H := m.comap ε with hp
  have hmT : (m.map (algebraMap O H)).map (algebraMap H T) = m.map (algebraMap O T) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hmS : (m.map (algebraMap O S)).map (π : S →+* T) = m.map (algebraMap O T) := by
    rw [Ideal.map_map, AlgHom.comp_algebraMap]
  set A : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)) :=
    ρ.mapMatrix a with hA
  have hred : ∀ z : S, π z ∈ m.map (algebraMap O T) →
      ρ z ∈ Ideal.span (Set.range (A.mulVec MvPowerSeries.X)) := by
    intro z hz
    rw [← hmS] at hz
    have hz' : z ∈ m.map (algebraMap O S) ⊔ RingHom.ker π := by
      have := Ideal.comap_map_of_surjective (π : S →+* T) hπ (m.map (algebraMap O S))
      have h2 : z ∈ ((m.map (algebraMap O S)).map (π : S →+* T)).comap (π : S →+* T) := hz
      rw [this] at h2
      exact h2
    have hle : m.map (algebraMap O S) ⊔ RingHom.ker π ≤
        (Ideal.span (Set.range (A.mulVec MvPowerSeries.X))).comap ρ := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro c hc
        simp only [Ideal.mem_comap, hρm c hc, zero_mem]
      · rw [hker, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        refine Ideal.subset_span ⟨i, ?_⟩
        simp [hA, Matrix.mulVec, dotProduct, hρx]
    exact hle hz'
  have hx0 : ∀ i, εT (π (x i)) = 0 := fun i => by
    have : π (x i) ∈ RingHom.ker εT := by rw [hkerT]; exact Ideal.subset_span ⟨i, rfl⟩
    exact this
  have hnil : ∀ i, ∃ N : ℕ, π (x i) ^ N ∈ m.map (algebraMap O T) := by
    intro i
    obtain ⟨⟨u, t⟩, hut⟩ := IsLocalization.surj p.primeCompl (π (x i))
    have hu : ε u = 0 := by
      have := congrArg εT hut
      rw [map_mul, hx0, zero_mul, hε] at this
      exact this.symm
    obtain ⟨N, y, hy⟩ := exists_pow_mul_one_sub_mem_map_maximalIdeal O H u
    have hy' := Ideal.mem_map_of_mem (algebraMap H T) hy
    rw [hmT, map_mul, map_pow] at hy'
    have hunit : IsUnit (algebraMap H T (1 - y * u)) := by
      refine IsLocalization.map_units T (⟨1 - y * u, ?_⟩ : p.primeCompl)
      intro hc
      have hc' : ε (1 - y * u) ∈ m := hc
      rw [map_sub, map_mul, hu, mul_zero, sub_zero, map_one] at hc'
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 hc')
    rw [Ideal.mul_unit_mem_iff_mem _ hunit] at hy'
    simp only at hut
    rw [← hut, mul_pow,
      Ideal.mul_unit_mem_iff_mem _ ((IsLocalization.map_units T t).pow N)] at hy'
    exact ⟨N, hy'⟩
  choose N hN using hnil
  have hdet : π a.det ∉ m.map (algebraMap O T) := by
    intro hc
    refine det_notMem_span_mulVec_X _ g (Finset.univ.sup N) A (fun i => ?_) ?_
    · rw [← hρx, ← map_pow]
      apply hred
      rw [map_pow]
      exact Ideal.pow_mem_of_pow_mem _ (hN i) (Finset.le_sup (Finset.mem_univ i))
    · rw [hA, ← RingHom.map_det]
      exact hred _ hc
  have hkill : ∀ w : T, εT w = 0 → w * π a.det = 0 := by
    intro w hw
    have hw' : w ∈ RingHom.ker εT := hw
    rw [hkerT] at hw'
    have hle : Ideal.span (Set.range fun i => π (x i)) ≤
        LinearMap.ker (LinearMap.mulRight T (π a.det)) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change π (x i) * π a.det = 0
      rw [← map_mul]
      change x i * a.det ∈ RingHom.ker π
      have h1 : x i * a.det = (a.adjugate.mulVec (a.mulVec x)) i := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
        simp [mul_comm]
      rw [h1, hker]
      change ∑ j, a.adjugate i j * a.mulVec x j ∈ _
      exact Ideal.sum_mem _ fun j _ =>
        Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self j))
    exact hle hw'
  have hval : εT (π a.det) = (n : O) ^ g := by
    have h1 : εT (π a.det) = ((εT.comp π).mapMatrix a).det := by
      rw [← AlgHom.map_det]; rfl
    have h2 : (εT.comp π).mapMatrix a = Matrix.diagonal fun _ => (n : O) := by
      ext i j
      simp [Matrix.diagonal_apply, ha]
    rw [h1, h2, Matrix.det_diagonal]
    simp
  obtain ⟨⟨u, t⟩, hut⟩ := IsLocalization.surj p.primeCompl (π a.det)
  simp only at hut
  obtain ⟨s, hs⟩ := exists_mul_kills_ker_of_localization O H ε p.primeCompl T u (fun h hh => by
    rw [map_mul, ← hut, ← mul_assoc, hkill _ (by rw [hε, hh]), zero_mul])
  refine ⟨s * u, hs, ?_, fun hc => hdet ?_⟩
  · have := congrArg εT hut
    rw [map_mul, hval, hε, hε] at this
    rw [map_mul, ← this]
    exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  · have hc' := Ideal.mem_map_of_mem (algebraMap H T) hc
    rw [hmT, map_mul, Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units T s), ← hut,
      Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units T t)] at hc'
    exact hc'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatMapMaximalIdealIsSeparable
section
open CategoryTheory Limits IsLocalRing

namespace GlobalTheory.IndEtaleLocal

theorem exists_etale_factor {A S Z : Type} [CommRing A] [CommRing S] [Algebra A S]
    [CommRing Z] [Algebra A Z] [Algebra.FinitePresentation A Z]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) (g : Z →ₐ[A] S) :
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra A W) (_ : Algebra.Etale A W)
      (u : Z →ₐ[A] W) (v : W →ₐ[A] S), v.comp u = g := by
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := h
  obtain ⟨i, g', h1, h2⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    (CommRingCat.of A) D t (S := CommRingCat.of Z) (CommRingCat.ofHom (algebraMap A Z))
    (Cocone.mk _ s) hs
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)
    (CommRingCat.ofHom g.toRingHom) (fun i => by
      rw [(hst i).2]
      ext a
      simp)
  let : Algebra A (D.obj i) := (t.app i).hom.toAlgebra
  have het : Algebra.Etale A (D.obj i) := (hst i).1
  refine ⟨D.obj i, inferInstance, inferInstance, het,
    { toRingHom := g'.hom, commutes' := fun a => congr($(h1).hom a) },
    { toRingHom := (s.app i).hom, commutes' := fun a => congr($((hst i).2).hom a) }, ?_⟩
  ext z
  exact (congr($(h2).hom z)).symm

theorem flat_of_isIndEtale {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) : Module.Flat A S := by
  refine Module.Flat.of_forall_isTrivialRelation fun {l f x} hfx => ?_
  let p : MvPolynomial (Fin l) A := ∑ i, f i • MvPolynomial.X i
  let I : Ideal (MvPolynomial (Fin l) A) := Ideal.span {p}
  have : Algebra.FinitePresentation A (MvPolynomial (Fin l) A ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton p)
  let g : (MvPolynomial (Fin l) A ⧸ I) →ₐ[A] S :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval x) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      have : MvPolynomial.aeval x p = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [p, map_sum, map_smul, MvPolynomial.aeval_X, hfx]
      rw [map_mul, this, mul_zero])
  obtain ⟨W, _, _, _, u, v, huv⟩ := exists_etale_factor h g
  let w : Fin l → W := fun i => u (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
  have hw : ∀ i, v (w i) = x i := fun i => by
    have := DFunLike.congr_fun huv (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
    exact this.trans (MvPolynomial.aeval_X x i)
  have hrel : ∑ i, f i • w i = 0 := by
    have h0 : Ideal.Quotient.mkₐ A I p = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self p)
    have : u (Ideal.Quotient.mkₐ A I p) = 0 := by rw [h0, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [p, map_sum, map_smul] using this
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A) (M := W) hrel
  refine ⟨k, a, fun j => v (y j), fun i => ?_, ha⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hw, hy, map_sum]
  simp only [map_smul]

theorem exists_local_unramified {A S : Type} [CommRing A] [IsLocalRing A] [CommRing S]
    [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) (s : S) :
    ∃ (L : Type) (_ : CommRing L) (_ : IsLocalRing L) (_ : Algebra A L)
      (_ : IsLocalHom (algebraMap A L)) (_ : Algebra.FormallyUnramified A L)
      (_ : Algebra.EssFiniteType A L) (φ : L →ₐ[A] S) (_ : IsLocalHom φ) (x : L), φ x = s := by
  first
  | exact @_root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale
  | exact _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale
  | (apply _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale ..)

theorem flat_map_maximalIdeal_isSeparable (A S : Type) [CommRing A] [IsLocalRing A] [CommRing S]
    [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) :
    Module.Flat A S ∧ (maximalIdeal A).map (algebraMap A S) = maximalIdeal S ∧
      Algebra.IsSeparable (ResidueField A) (ResidueField S) := by
  refine ⟨flat_of_isIndEtale h, le_antisymm ?_ fun s hs => ?_, ⟨fun r => ?_⟩⟩
  · exact ((local_hom_tfae (algebraMap A S)).out 1 3 rfl rfl).mp inferInstance
  · obtain ⟨L, _, _, _, _, _, _, φ, hφ, x, rfl⟩ := exists_local_unramified h s
    have hx : x ∈ maximalIdeal L := fun hx => hs (hx.map φ)
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := A)] at hx
    have := Ideal.mem_map_of_mem (φ : L →+* S) hx
    rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this
  · obtain ⟨s, rfl⟩ := residue_surjective r
    obtain ⟨L, _, _, _, _, _, _, φ, hφ, x, rfl⟩ := exists_local_unramified h s
    have : IsLocalHom (φ : L →+* S) := ⟨hφ.1⟩
    let ψ : ResidueField L →ₐ[ResidueField A] ResidueField S :=
      { toRingHom := ResidueField.map (φ : L →+* S)
        commutes' := fun a => by
          obtain ⟨a, rfl⟩ := residue_surjective a
          simp [ResidueField.algebraMap_residue] }
    have := (Algebra.IsSeparable.isSeparable (ResidueField A) (residue L x)).map ψ ψ.injective
    exact this

end GlobalTheory.IndEtaleLocal
end

