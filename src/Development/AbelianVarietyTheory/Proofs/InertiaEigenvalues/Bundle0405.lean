module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFixedEqPadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeLevelPrimePow
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioProportionalTarget
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.Gauss

namespace RatioProp

variable {l : ℕ} [Fact l.Prime]

theorem one_lt_l : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt

theorem inv_l_pos : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (by linarith [(one_lt_l : (1 : ℝ) < l)])

theorem inv_l_lt_one : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ one_lt_l

theorem rho_pos {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) : 0 < ρ := lt_of_lt_of_le inv_l_pos h0

theorem gauss {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) : IsGauss l ρ (gC l ρ) :=
  isGauss_gC_target l ρ h0 h1

theorem phi_zc (c : ℤ_[l]) : φc l (zc l c) = zc l c :=
  (GlobalTheory.MemLoc.PhiFix.phiA_alg l _).trans (congrArg _ (GlobalTheory.MemLoc.PhiFix.φA_zA l c))

theorem iter_lpow (m j : ℕ) (x : Formalism.Per.Acris l) :
    (φc l)^[m] ((l : Formalism.Per.Acris l) ^ j * x) = (l : Formalism.Per.Acris l) ^ j * (φc l)^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast]

theorem gC_zero {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) : gC l ρ 0 = 0 := by
  have hm := (gauss h0 h1).2.2.2.1 0 (l : Formalism.Per.Acris l)
  rw [zero_mul, (_root_.GlobalTheory.PMon.Gauss.gC_basic_values l ρ h0 h1).2.1] at hm
  have e : gC l ρ 0 * (1 - ρ) = 0 := by linear_combination hm
  rcases mul_eq_zero.1 e with h | h
  · exact h
  · exact absurd h (by linarith)

theorem gC_lpow {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) (m : ℕ) (x : Formalism.Per.Acris l) :
    gC l ρ ((l : Formalism.Per.Acris l) ^ m * x) = ρ ^ m * gC l ρ x := by
  induction m with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ m ih =>
    rw [pow_succ', mul_assoc, (gauss h0 h1).2.2.2.1, (_root_.GlobalTheory.PMon.Gauss.gC_basic_values l ρ h0 h1).2.1, ih, pow_succ']
    ring

theorem lpow_ne_zero {x : Formalism.Per.Acris l} (hx : x ≠ 0) (m : ℕ) : (l : Formalism.Per.Acris l) ^ m * x ≠ 0 := by
  intro e
  have h := gC_lpow le_rfl inv_l_lt_one m x
  rw [e, gC_zero le_rfl inv_l_lt_one] at h
  have hp := _root_.GlobalTheory.PMon.Gauss.gC_pos_target l x hx _ le_rfl inv_l_lt_one
  have : (0 : ℝ) < (l : ℝ)⁻¹ ^ m * gC l (l : ℝ)⁻¹ x := mul_pos (pow_pos inv_l_pos m) hp
  linarith

theorem pert {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) (W W' : Formalism.Per.Acris l) (c y : ℤ_[l]) (k : ℕ) :
    gC l ρ (W - zc l (c + (l : ℤ_[l]) ^ k * y) * W') ≤ max (gC l ρ (W - zc l c * W')) (ρ ^ k * gC l ρ W') := by
  have e : W - zc l (c + (l : ℤ_[l]) ^ k * y) * W' =
      (W - zc l c * W') + -((l : Formalism.Per.Acris l) ^ k * (zc l y * W')) := by
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [e]
  refine ((gauss h0 h1).2.1 _ _).trans (max_le_max le_rfl ?_)
  rw [(gauss h0 h1).2.2.1, gC_lpow h0 h1, (gauss h0 h1).2.2.2.1]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left ((gauss h0 h1).1 _).1 ((gauss h0 h1).1 _).2) (pow_nonneg (rho_pos h0).le _)

def digitSet (W W' : Formalism.Per.Acris l) (k : ℕ) : Set ℤ_[l] :=
  {c | ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (W - zc l c * W') ≤ ρ ^ k * gC l ρ W'}

theorem isClosed_digitSet (W W' : Formalism.Per.Acris l) (k : ℕ) : IsClosed (digitSet W W' k) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro c hc
  simp only [digitSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at hc
  obtain ⟨ρ, h0, h1, hlt⟩ := hc
  refine ⟨(l : ℝ) ^ (-(k : ℤ)), zpow_pos (by linarith [(one_lt_l : (1 : ℝ) < l)]) _, fun c' hc' hT => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hc'
  have hmem : c - c' ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow, norm_sub_rev]
    exact hc'.le
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
  have hp := pert h0 h1 W W' c' y k
  have e : c' + (l : ℤ_[l]) ^ k * y = c := by rw [mul_comm, hy]; ring
  rw [e] at hp
  exact absurd (hp.trans (max_le (hT ρ h0 h1) le_rfl)) (not_le.2 hlt)

theorem gC_eq_of_vr {V W' : Formalism.Per.Acris l} (hV : V ≠ 0) (hW' : W' ≠ 0) (n : ℤ)
    (hn : ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r V - vr l r W' = n * r) {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    gC l ρ V = ρ ^ n * gC l ρ W' := by
  have hl : (1 : ℝ) < l := one_lt_l
  have hρ0 : 0 < ρ := rho_pos h0
  have hr : -Real.logb l ρ ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · linarith [Real.logb_neg hl hρ0 h1]
    · have := (Real.logb_le_logb hl inv_l_pos hρ0).2 h0
      rw [Real.logb_inv, Real.logb_self_eq_one hl] at this
      linarith
  have e := hn _ hr
  have hpow : (l : ℝ) ^ (-(-Real.logb l ρ)) = ρ := by
    rw [neg_neg, Real.rpow_logb (by linarith) (ne_of_gt hl) hρ0]
  simp only [vr] at e
  rw [hpow] at e
  have hV0 := _root_.GlobalTheory.PMon.Gauss.gC_pos_target l V hV ρ h0 h1
  have hW0 := _root_.GlobalTheory.PMon.Gauss.gC_pos_target l W' hW' ρ h0 h1
  apply Real.logb_injOn_pos hl hV0 (mul_pos (zpow_pos hρ0 n) hW0)
  have hz : Real.logb l (ρ ^ n) = n * Real.logb l ρ := by
    simp only [Real.logb, Real.log_zpow]
    ring
  rw [Real.logb_mul (ne_of_gt (zpow_pos hρ0 n)) (ne_of_gt hW0), hz]
  linarith

theorem digit_step {h s : ℕ} (hs : s < h) {W W' : Formalism.Per.Acris l}
    (he : (φc l)^[h] W' = (l : Formalism.Per.Acris l) ^ s * W') (hW' : W' ≠ 0)
    (hr : φc l W * W' = W * φc l W') (k : ℕ) (c : ℤ_[l]) (hc : c ∈ digitSet W W' k) :
    (digitSet W W' (k + 1)).Nonempty := by
  have hrV : φc l (W - zc l c * W') * W' = (W - zc l c * W') * φc l W' := by
    rw [map_sub, map_mul, phi_zc]
    linear_combination hr
  by_cases hV0 : W - zc l c * W' = 0
  · refine ⟨c, fun ρ h0 h1 => ?_⟩
    rw [hV0, gC_zero h0 h1]
    exact mul_nonneg (pow_nonneg (rho_pos h0).le _) ((gauss h0 h1).1 _).1
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.PMon.Gauss.vr_sub_eq_int_mul l h s hs _ W' he hV0 hW' hrV
  have hg : ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (W - zc l c * W') = ρ ^ n * gC l ρ W' :=
    fun ρ h0 h1 => gC_eq_of_vr hV0 hW' n hn h0 h1
  have hW0 := _root_.GlobalTheory.PMon.Gauss.gC_pos_target l W' hW' _ le_rfl inv_l_lt_one
  have hk : (k : ℤ) ≤ n := by
    have a := hc _ le_rfl inv_l_lt_one
    rw [hg _ le_rfl inv_l_lt_one] at a
    have b := le_of_mul_le_mul_right a hW0
    rw [← zpow_natCast] at b
    exact (zpow_le_zpow_iff_right_of_lt_one₀ inv_l_pos inv_l_lt_one).1 b
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hkm : k ≤ m := by exact_mod_cast hk
  obtain ⟨u, -, hu⟩ := _root_.GlobalTheory.PMon.Gauss.one_digit l h s hs (W - zc l c * W') ((l : Formalism.Per.Acris l) ^ m * W')
    (by rw [iter_lpow, he]; ring) (lpow_ne_zero hW' m)
    (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hrV)
    (fun ρ h0 h1 => by rw [hg ρ h0 h1, gC_lpow h0 h1, zpow_natCast])
  refine ⟨c + u * (l : ℤ_[l]) ^ m, fun ρ h0 h1 => ?_⟩
  have e : W - zc l (c + u * (l : ℤ_[l]) ^ m) * W' =
      (W - zc l c * W') - zc l u * ((l : Formalism.Per.Acris l) ^ m * W') := by
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [e]
  refine (hu ρ h0 h1).trans ?_
  rw [gC_lpow h0 h1, ← mul_assoc, ← pow_succ']
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (rho_pos h0).le h1.le (by omega))
    ((gauss h0 h1).1 _).1

theorem eq_zc_mul {h s : ℕ} (hs : s < h) {W W' : Formalism.Per.Acris l}
    (he : (φc l)^[h] W' = (l : Formalism.Per.Acris l) ^ s * W') (hW' : W' ≠ 0)
    (hr : φc l W * W' = W * φc l W')
    (hg : ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ W = gC l ρ W') :
    ∃ c : ℤ_[l], W = zc l c * W' := by
  have hmono : ∀ i, digitSet W W' (i + 1) ⊆ digitSet W W' i := fun i c hc ρ h0 h1 =>
    (hc ρ h0 h1).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (rho_pos h0).le h1.le (Nat.le_succ i)) ((gauss h0 h1).1 _).1)
  have hne : ∀ i, (digitSet W W' i).Nonempty := by
    intro i
    induction i with
    | zero => exact ⟨0, fun ρ h0 h1 => by rw [map_zero, zero_mul, sub_zero, pow_zero, one_mul, hg ρ h0 h1]⟩
    | succ i ih =>
      obtain ⟨c, hc⟩ := ih
      exact digit_step hs he hW' hr i c hc
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ hmono hne
    (isCompact_univ.of_isClosed_subset (isClosed_digitSet W W' 0) (Set.subset_univ _))
    (isClosed_digitSet W W')
  rw [Set.mem_iInter] at hc
  refine ⟨c, ?_⟩
  by_contra hne'
  have hpos := _root_.GlobalTheory.PMon.Gauss.gC_pos_target l (W - zc l c * W') (sub_ne_zero.2 hne') _ le_rfl inv_l_lt_one
  have hlim : Filter.Tendsto (fun i : ℕ => (l : ℝ)⁻¹ ^ i * gC l (l : ℝ)⁻¹ W') Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one inv_l_pos.le inv_l_lt_one).mul_const
      (gC l (l : ℝ)⁻¹ W')
  have := ge_of_tendsto' hlim (fun i => hc i _ le_rfl inv_l_lt_one)
  linarith

end RatioProp


open RatioProp in
theorem ratio_proportional_target : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l,
    (φc l)^[h] w = (l : Formalism.Per.Acris l) ^ s * w → (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 →
    φc l w * w' = w * φc l w' → ∃ c d : ℤ_[l], c ≠ 0 ∧ zc l c * w = zc l d * w' := by
  intro l _ h s hs w w' _ he' hw' hr
  by_cases hw : w = 0
  · exact ⟨1, 0, one_ne_zero, by rw [hw, mul_zero, map_zero, zero_mul]⟩
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.PMon.Gauss.vr_sub_eq_int_mul l h s hs w w' he' hw hw' hr
  have hg : ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = ρ ^ n * gC l ρ w' :=
    fun ρ h0 h1 => gC_eq_of_vr hw hw' n hn h0 h1
  rcases le_or_gt 0 n with hn0 | hn0
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn0).symm⟩
    obtain ⟨c, hc⟩ := eq_zc_mul hs (W := w) (W' := (l : Formalism.Per.Acris l) ^ m * w')
      (by rw [iter_lpow, he']; ring) (lpow_ne_zero hw' m)
      (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hr)
      (fun ρ h0 h1 => by rw [hg ρ h0 h1, gC_lpow h0 h1, zpow_natCast])
    refine ⟨1, c * (l : ℤ_[l]) ^ m, one_ne_zero, ?_⟩
    rw [map_one, one_mul, hc, map_mul, map_pow, map_natCast]
    ring
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -n := ⟨(-n).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨c, hc⟩ := eq_zc_mul hs (W := (l : Formalism.Per.Acris l) ^ m * w) (W' := w') he' hw'
      (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hr)
      (fun ρ h0 h1 => by
        rw [gC_lpow h0 h1, hg ρ h0 h1, ← mul_assoc, ← zpow_natCast, hm,
          ← zpow_add₀ (ne_of_gt (rho_pos h0)), neg_add_cancel, zpow_zero, one_mul])
    refine ⟨(l : ℤ_[l]) ^ m, c, pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero), ?_⟩
    rw [map_pow, map_natCast, hc]

end GlobalTheory.PMon.Gauss
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledProductSpanLatticeExistsPadicBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.TraceConjugationCover

theorem latT_basis : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ), (∀ k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t k, zOm l (c' y) • y = 1) → (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → ∃ (d' : ℕ) (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)), LinearIndependent ℚ_[l] bb ∧ (∀ s, bb s ∈ GlobalTheory.TraceConjugationCover.latT ρs t M) ∧ ∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s := by
  intro l _ Γ _ a m ρs t M h1 h2

  set Λ : Fin m → Submodule ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) :=
    fun k => Submodule.span ℤ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l))) with hΛ
  have hsum : ∀ k (c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l]), ∑ y ∈ t k, zOm l (c y) • y ∈ Λ k := by
    intro k c
    refine Submodule.sum_mem _ fun y hy => ?_
    rw [zOm_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hy)
  have hone : ∀ k, (1 : Matrix (Fin a) (Fin a) (Om l)) ∈ Λ k := by
    intro k
    obtain ⟨c, hc⟩ := h1 k
    rw [← hc]; exact hsum k c
  have hstab : ∀ k g, ∀ x ∈ Λ k, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x ∈ Λ k := by
    intro k g x hx
    refine Submodule.span_induction (p := fun x _ => ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x ∈ Λ k) ?_ ?_ ?_ ?_ hx
    · intro y hy
      obtain ⟨c, hc⟩ := h2 k g y hy
      rw [hc]; exact hsum k c
    · simp
    · intro x y _ _ hx hy
      rw [Matrix.mul_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [← zOm_smul, Matrix.mul_smul, zOm_smul]
      exact Submodule.smul_mem _ _ hx

  have hsingle : ∀ k, ∀ x ∈ Λ k, Pi.single k x ∈ latL t 0 := by
    intro k x hx
    have : (LinearMap.single ℤ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k) x ∈ latL t 0 := by
      have hle : (Λ k).map (LinearMap.single ℤ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k) ≤ latL t 0 := by
        rw [hΛ, Submodule.map_span, latL]
        refine Submodule.span_mono ?_
        rintro _ ⟨y, hy, rfl⟩
        refine Set.mem_iUnion.2 ⟨k, y, hy, ?_⟩
        simp
      exact hle (Submodule.mem_map_of_mem hx)
    simpa using this
  have hT : latT ρs t M ≤ latL t 0 := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      rw [show tup ρs g = ∑ k, Pi.single k (tup ρs g k) from (Finset.univ_sum_single _).symm]
      refine Submodule.sum_mem _ fun k _ => hsingle k _ ?_
      have := hstab k g 1 (hone k)
      simpa [tup] using this
    · rw [latL, Submodule.span_le]
      intro z hz
      obtain ⟨k, y, hy, rfl⟩ := Set.mem_iUnion.1 hz
      refine hsingle k _ ?_
      have : ((l : ℤ_[l]) ^ M) • y ∈ Λ k := Submodule.smul_mem _ _ (Submodule.subset_span hy)
      rw [← zOm_smul, map_pow, map_natCast] at this
      exact this
  have hfg0 : (latL t (0 : ℕ)).FG := by
    rw [latL]
    refine Submodule.fg_span ?_
    exact Set.finite_iUnion fun k => (t k).finite_toSet.image _
  have hfg : (latT ρs t M).FG := hfg0.of_le hT
  haveI : Module.Finite ℤ_[l] (latT ρs t M) := Module.Finite.iff_fg.2 hfg
  have hinj : Function.Injective (zOm l) :=
    (algebraMap ℚ_[l] (Om l)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  haveI tf0 : Module.IsTorsionFree ℤ_[l] (Om l) := .of_smul_eq_zero fun c x h => by
    rw [← zOm_smul, smul_eq_mul, mul_eq_zero] at h
    rcases h with h | h
    · left; exact hinj (by simpa using h)
    · right; exact h
  haveI tf1 : Module.IsTorsionFree ℤ_[l] (Matrix (Fin a) (Fin a) (Om l)) :=
    inferInstanceAs (Module.IsTorsionFree ℤ_[l] (Fin a → Fin a → Om l))
  haveI : Module.IsTorsionFree ℤ_[l] (latT ρs t M) := inferInstance
  haveI : Module.Free ℤ_[l] (latT ρs t M) := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ_[l] (latT ρs t M)
  refine ⟨_, fun s => (b s : Fin m → Matrix (Fin a) (Fin a) (Om l)), ?_, fun s => (b s).2, ?_⟩
  · rw [← LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]]
    exact b.linearIndependent.map' (latT ρs t M).subtype (Submodule.ker_subtype _)
  · intro x hx
    refine ⟨b.repr ⟨x, hx⟩, ?_⟩
    have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    simp only [zOm_smul]
    exact this.symm

end GlobalTheory.TraceConjugationCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledProductSpanLatticeStableGaloisRepTuple
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.TraceConjugationCover

theorem tup_mul_tup {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a m : ℕ}
    (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g h : Γ) : tup ρs g * tup ρs h = tup ρs (g * h) := by
  funext k
  simp [tup, map_mul, Units.val_mul]

theorem tup_mul_smul {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a m : ℕ}
    (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g : Γ) (c : ℤ_[l]) (x : Fin m → Matrix (Fin a) (Fin a) (Om l)) :
    tup ρs g * (c • x) = c • (tup ρs g * x) := by
  rw [← zOm_smul, ← zOm_smul]
  funext k
  simp [Pi.mul_apply, Pi.smul_apply, Matrix.mul_smul]

theorem stabE : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ), (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → (∀ g, ∀ x ∈ GlobalTheory.TraceConjugationCover.latL t M, GlobalTheory.TraceConjugationCover.tup ρs g * x ∈ GlobalTheory.TraceConjugationCover.latL t M) ∧ ∀ g, ∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, GlobalTheory.TraceConjugationCover.tup ρs g * x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M := by
  intro l _ Γ _ a m ρs t M hc
  have hL : ∀ g, ∀ x ∈ latL t M, tup ρs g * x ∈ latL t M := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      obtain ⟨y, hy, rfl⟩ := hk
      obtain ⟨c', hc'⟩ := hc k g y hy
      have e : tup ρs g * Pi.single k ((l : Om l) ^ M • y)
          = ∑ z ∈ t k, c' z • (Pi.single k ((l : Om l) ^ M • z) : Fin m → Matrix (Fin a) (Fin a) (Om l)) := by
        have e1 : tup ρs g * Pi.single k ((l : Om l) ^ M • y)
            = Pi.single k ((l : Om l) ^ M • (((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * y)) := by
          funext j
          by_cases hj : j = k
          · subst hj; simp [tup, Matrix.mul_smul]
          · simp [Pi.single_apply, hj]
        rw [e1, hc', Finset.smul_sum]
        funext j
        rw [Finset.sum_apply]
        by_cases hj : j = k
        · subst hj
          simp only [Pi.single_eq_same, Pi.smul_apply]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [smul_comm ((l : Om l) ^ M) (zOm l (c' z)) z, zOm_smul]
        · simp [Pi.single_apply, hj]
      rw [e]
      refine Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact Set.mem_iUnion.mpr ⟨k, z, hz, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [tup_mul_smul]; exact Submodule.smul_mem _ _ hx
  refine ⟨hL, fun g x hx => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  clear hx
  rw [mul_add]
  refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right (hL g z hz))
  refine Submodule.mem_sup_left ?_
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    rw [tup_mul_tup]; exact Submodule.subset_span ⟨_, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [tup_mul_smul]; exact Submodule.smul_mem _ _ hx

end GlobalTheory.TraceConjugationCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetupOfFactor
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime

theorem setup_of_factor : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (M : ℕ) (ι : Type) [Fintype ι] (P : ι → PlE D.host) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ Q : Finset (PlE D.host)), SlopeTestRemainingChoices X i M A₀ P d → IsQ P Q → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ), Kills i A → (∀ g, (∀ q, d q g = 1) → κ g = 1) → Setup bkP i s κ Q ∧ AntiHom X.cc κ ∧ ∀ z, IsTameInertiaElementAtTwistPrime X i z → κ z = 1 := by
  intro D N X bkP i s hG M ι _ P d A₀ Q hA hQ A _ _ _ _ κ _ h1
  have hfin : Module.Finite (X.O0 i) A := Module.Finite.of_finite
  refine ⟨⟨hG, ⟨fun x hx => ?_⟩, hfin, ?_, fun g => ⟨M, ?_⟩, fun v hv B hB σ hσ => h1 σ fun q => ?_, fun v hv hl => ?_,
    fun v hv B hB σ hσ => h1 σ fun q => ?_⟩, fun g g' hg => ?_, ?_⟩
  · by_contra hn
    have h : IsLocalRing.maximalIdeal (X.O0 i) ≤ (IsLocalRing.maximalIdeal A).comap (algebraMap (X.O0 i) A) :=
      (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
        Algebra.IsIntegral.isIntegral (IsLocalRing.maximalIdeal A))).ge
    exact h hn hx
  · refine Subgroup.isOpen_mono (H₁ := ⨅ q, (d q).ker) (fun g hg => h1 g fun q => Subgroup.mem_iInf.1 hg q) ?_
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun q => (hA.2.2 q).1
  · rw [← map_pow]
    refine h1 _ fun q => ?_
    rw [map_pow]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, toAdd_one]
  · exact (hA.2.2 q).2.2.1 v hv B hB σ hσ
  · obtain ⟨q, hq⟩ := (hQ v).1 hv
    exact (hA.1 q v hq).2.2.2.1 (X.twistExcludedPlaces_contains_residueChar i hl)
  · exact (hA.2.2 q).2.2.2.1 v (fun hq => hv ((hQ v).2 ⟨q, hq⟩)) B hB σ hσ
  · rw [eq_inv_iff_mul_eq_one, ← map_mul]
    refine h1 _ fun q => ?_
    rw [map_mul, (hA.2.2 q).2.1 g g' hg, inv_mul_cancel]
  · rintro z ⟨v, hv, B, hB, hz, -⟩
    exact h1 z fun q => (hA.2.2 q).2.2.2.1 v (fun hq => (hA.1 q v hq).2.2.2.1 (X.primes_subset_exceptional i hv)) B hB z hz

end GlobalTheory.NewPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanInfOfSpanTop
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.IntRestBall

open GlobalTheory.TwAll

theorem span_inf_of_span_top {O V : Type} [CommRing O] [IsDomain O] [AddCommGroup V] [Module O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] (B : Submodule O V)
    (hB : Submodule.span (FractionRing O) (B : Set V) = ⊤) (W : Submodule (FractionRing O) V)
    (M : Submodule O V) (hM : ∀ f, f ∈ M ↔ f ∈ B ∧ f ∈ W) :
    Submodule.span (FractionRing O) (M : Set V) = W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    exact fun f hf => ((hM f).1 hf).2
  · intro f hf
    have h1 : f ∈ Submodule.span (FractionRing O) (B : Set V) := hB ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) (FractionRing O) (B : Set V) f h1
    rw [Submodule.span_eq] at ht
    have e : t • f = (algebraMap O (FractionRing O) t) • f := by
      rw [algebraMap_smul]; rfl
    have hne : algebraMap O (FractionRing O) t ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors t.2
    have h2 : t • f ∈ M := (hM _).2 ⟨ht, e ▸ W.smul_mem _ hf⟩
    have h3 := (Submodule.span (FractionRing O) (M : Set V)).smul_mem
      (algebraMap O (FractionRing O) t)⁻¹ (Submodule.subset_span h2)
    rwa [e, smul_smul, inv_mul_cancel₀ hne, one_smul] at h3

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} (T : NTh D.R D.host D.what₂ D.LL0 N X Y)

end GlobalTheory.IntRestBall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeLevelPrimePowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_pairing_lattice_level_primePow : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), ∃ β : QuotientCohomology LA' _ hI' →ₗ[O] QuotientCohomology LA _ hI →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL)), (∀ c, (∀ y, β y c = 0) → c = 0) ∧ ∀ (d : ↥(latticeCocycles LA)) (h : redT LA _ d ∈ quotientCocycles LA _ hI) (c' : ↥(quotientCocycles LA' _ hI')), β (Submodule.Quotient.mk c') (Submodule.Quotient.mk ⟨redT LA _ d, h⟩) = 0 → CobO (P.PD K) L1 (cupLD LA' m (d : ↥(GK K) → A.V) (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T))) := by
  first | exact @GlobalTheory.TateLevel.tate_pairing_level | exact GlobalTheory.TateLevel.tate_pairing_level | (intros; apply GlobalTheory.TateLevel.tate_pairing_level <;> assumption)
end

