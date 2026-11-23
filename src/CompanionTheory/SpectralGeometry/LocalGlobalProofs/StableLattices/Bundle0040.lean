module

public import Mathlib
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.Bundle0001

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NumKG
section
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.ClusterNum

open CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK
open GlobalTheory.CompanionTheory.DSNormLt (sig sig_anti sig_mul pair_eq abs_sig)
open PI.UpqRep

theorem numKG : NumKG := by
  intro n ε γ lev ν B C hG hB hBn hC _ hdom hn
  set X := xv ε γ with hX
  set κ := X - rhoC ε - wt B with hκ
  set μ := X - wt B - wt C with hμ
  obtain ⟨hXa, -, hgap⟩ := hG
  obtain ⟨w, hw, hs⟩ := exists_sort ε κ
  obtain ⟨m, hm, hm2⟩ := hdom w hw
  have i1 : ∑ a, κ (w a) * μ (w a) ≤ ∑ a, κ (w a) * ν a := by
    rw [← sub_nonneg, ← Finset.sum_sub_distrib]
    have e : ∀ a, κ (w a) * ν a - κ (w a) * μ (w a) = ∑ c, ∑ d, (m c d : ℝ) * (κ (w a) * root c d a) := fun a => by
      have := congrFun hm2 a
      simp only [Pi.sub_apply, Function.comp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [← mul_sub, this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_nonneg fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_nonneg fun d _ => ?_
    rw [← Finset.mul_sum]
    by_cases h0 : m c d = 0
    · simp [h0]
    · refine mul_nonneg (Nat.cast_nonneg _) ?_
      simp only [root, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', mem_univ, if_true, sub_nonneg]
      exact hs c d (hm c d h0).1 (hm c d h0).2
  let tC : Fin n → Fin n → ℝ := fun a b => 2 * (ind C a b - ind C b a) - sc ε a b
  have htC : ∀ a b, |tC a b| ≤ if ε a = ε b then 1 else 0 := fun a b => by
    simp only [tC, ind_eq, sc, sig]
    rcases lt_trichotomy a b with h | h | h
    · simp only [dif_pos h, dif_neg h.not_gt, if_pos h]
      by_cases h1 : (⟨(a, b), h⟩ : Pos n) ∈ C
      · have : ε a = ε b := hC _ h1
        simp [h1, this]; norm_num
      · simp only [h1, if_false]; split_ifs <;> simp
    · subst h; simp
    · simp only [dif_pos h, dif_neg h.not_gt, if_pos h, if_neg h.not_gt]
      by_cases h1 : (⟨(b, a), h⟩ : Pos n) ∈ C
      · have : ε a = ε b := (hC _ h1).symm
        simp [h1, this]; norm_num
      · simp only [h1, if_false]; split_ifs <;> simp
  have i2 : ∑ a, κ a * (wt C a - rhoC ε a) ≤ ∑ a, κ (w a) * rhoC ε a := by
    have p1 := pair_eq tC (fun a b => by simp only [tC]; rw [sc_anti ε a b]; ring) κ
    have p2 := pair_eq (sc ε) (sc_anti ε) fun a => κ (w a)
    have e : ∀ a, wt C a - rhoC ε a = (∑ b, tC a b) / 2 := fun a => by
      simp only [tC]
      rw [wt_eq, rhoC_eq, Finset.sum_sub_distrib (f := fun b => 2 * (ind C a b - ind C b a)), ← Finset.mul_sum]
      ring
    simp only [e]
    simp only [rhoC_eq]
    have : ∑ a, ∑ b, tC a b * (κ a - κ b) ≤ ∑ a, ∑ b, sc ε a b * (κ (w a) - κ (w b)) := by
      calc _ ≤ ∑ a, ∑ b, (if ε a = ε b then 1 else 0) * |κ a - κ b| :=
            Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => (le_abs_self _).trans (by
              rw [abs_mul]; exact mul_le_mul_of_nonneg_right (htC a b) (abs_nonneg _))
        _ = ∑ a, ∑ b, (if ε (w a) = ε (w b) then 1 else 0) * |κ (w a) - κ (w b)| := by
            rw [← Equiv.sum_comp w]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Equiv.sum_comp w]
        _ = _ := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            rw [hw, hw, sc, sig]
            by_cases h : ε a = ε b
            · rcases lt_trichotomy a b with h1 | h1 | h1
              · simp [h, h1, abs_of_nonneg (sub_nonneg.2 (hs a b h1 h))]
              · simp [h1]
              · simp [h, h1, h1.not_gt, abs_of_nonpos (sub_nonpos.2 (hs b a h1 h.symm))]
            · simp [h]
    linarith
  have hκw : ∀ a, κ (w a) = ν a + rhoC ε a := by
    have e1 : ∑ a, κ a * κ a = ∑ a, κ (w a) * μ (w a) + ∑ a, κ a * (wt C a - rhoC ε a) := by
      rw [Equiv.sum_comp w fun a => κ a * μ a, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [hκ, hμ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have e2 : ∑ a, κ (w a) * κ (w a) = ∑ a, κ a * κ a := Equiv.sum_comp w fun a => κ a * κ a
    have e3 : ∑ a, (κ (w a) - (ν a + rhoC ε a)) ^ 2 = ∑ a, κ (w a) * κ (w a) - 2 * ∑ a, κ (w a) * ν a -
        2 * ∑ a, κ (w a) * rhoC ε a + ∑ a, (ν a + rhoC ε a) * (ν a + rhoC ε a) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    have hn' : ∑ a, (ν a + rhoC ε a) * (ν a + rhoC ε a) = ∑ a, κ a * κ a := hn
    have h0 : ∑ a, (κ (w a) - (ν a + rhoC ε a)) ^ 2 = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    intro a
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 h0 a (mem_univ _)
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  let t : Fin n → Fin n → ℝ := fun a b =>
    (sig a b - sc ε a b) - 2 * (ind B a b - ind B b a) + sc ε (w.symm a) (w.symm b)
  have hws : ∀ c, ε (w.symm c) = ε c := fun c => by rw [← hw, Equiv.apply_symm_apply]
  have ta : ∀ a b, t b a = -t a b := fun a b => by
    simp only [t]; rw [sig_anti a b, sc_anti ε a b, sc_anti ε (w.symm a)]; ring
  have tb : ∀ a b, a < b → |t a b| ≤ 1 := fun a b h => by
    simp only [t, ind_eq, dif_pos h, dif_neg h.not_gt, sc, hws]
    by_cases h1 : ε a = ε b
    · rw [if_neg fun h2 => (hBn _ h2).1 h1]
      simpa [h1] using abs_sig _ _
    · simp only [if_neg h1, sig, if_pos h]
      split_ifs <;> norm_num
  have tb' : ∀ a b, |t a b| ≤ 1 := fun a b => by
    rcases lt_trichotomy a b with h | h | h
    · exact tb a b h
    · subst h
      have := ta a a
      rw [show t a a = 0 by linarith]; simp
    · rw [ta, abs_neg]; exact tb b a h
  obtain ⟨⟨⟨c, d⟩, hcd⟩, hi⟩ := hB
  have hcd' : c < d := hcd
  have hne : t c d = -1 := by
    have h1 : ¬ε c = ε d := (hBn _ hi).1
    simp only [t, ind_eq, dif_pos hcd', dif_neg hcd'.not_gt, sc, hws, if_neg h1, if_pos hi, sig, if_pos hcd']
    norm_num
  have hgcd : Lc n ≤ X c - X d := hgap c d (hBn _ hi).2

  have p1 := pair_eq t ta X
  have p2 := pair_eq sig sig_anti X
  have hD : ∀ a b, 0 ≤ sig a b * (X a - X b) - t a b * (X a - X b) := fun a b => by
    rw [sig_mul hXa, sub_nonneg]
    exact (le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (tb' a b))
  have hDcd : 2 * Lc n ≤ sig c d * (X c - X d) - t c d * (X c - X d) := by
    rw [hne, show sig c d = 1 by simp [sig, hcd']]
    linarith
  have hsum : ∑ a, ∑ b, t a b * (X a - X b) + 2 * Lc n ≤ ∑ a, ∑ b, sig a b * (X a - X b) := by
    have h1 : sig c d * (X c - X d) - t c d * (X c - X d) ≤
        ∑ a, ∑ b, (sig a b * (X a - X b) - t a b * (X a - X b)) :=
      (Finset.single_le_sum (f := fun b => sig c b * (X c - X b) - t c b * (X c - X b))
        (fun b _ => hD c b) (mem_univ d)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, (sig a b * (X a - X b) - t a b * (X a - X b)))
        (fun a _ => Finset.sum_nonneg fun b _ => hD a b) (mem_univ c))
    simp only [Finset.sum_sub_distrib] at h1
    linarith
  have hy : ∀ a, (ν + (2 : ℝ) • rhoC ε) (w.symm a) = X a + ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) := fun a => by
    have h1 := hκw (w.symm a)
    have h3 := rhoC_eq ε a
    have h4 := rhoC_eq ε (w.symm a)
    rw [← Equiv.sum_comp w.symm] at h4
    have h5 := wt_eq B a
    have ts : ∑ b, t a b = ∑ b, sig a b - ∑ b, sc ε a b - 2 * ∑ b, (ind B a b - ind B b a) +
        ∑ b, sc ε (w.symm a) (w.symm b) := by
      simp only [t]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib (f := fun b => sig a b - sc ε a b),
        Finset.sum_sub_distrib (f := fun b => sig a b), ← Finset.mul_sum]
    simp only [hκ, Equiv.apply_symm_apply, Pi.sub_apply] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ts]
    linarith
  have hY : ∀ a, ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) ^ 2 ≤ (n : ℝ) ^ 2 := fun a => by
    have e : (∑ b, t a b) / 2 - (∑ b, sig a b) / 2 = (∑ b, (t a b - sig a b)) / 2 := by
      rw [Finset.sum_sub_distrib]; ring
    have h2 : |∑ b, (t a b - sig a b)| ≤ 2 * (n : ℝ) := by
      calc _ ≤ ∑ b, |t a b - sig a b| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _b : Fin n, (2 : ℝ) := Finset.sum_le_sum fun b _ => by
            have := abs_sub (t a b) (sig a b)
            linarith [tb' a b, abs_sig a b]
        _ = 2 * (n : ℝ) := by simp [mul_comm]
    rw [e, div_pow]
    have h3 : (∑ b, (t a b - sig a b)) ^ 2 ≤ (2 * (n : ℝ)) ^ 2 := sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2
    nlinarith
  have g1 : vNormSq ε ν = ∑ a, (X a + ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2)) ^ 2 := by
    unfold vNormSq nsq dot
    rw [← Equiv.sum_comp w.symm]
    exact Finset.sum_congr rfl fun a _ => by rw [hy, sq]
  have g2 : vNormSq ε γ = ∑ a, X a ^ 2 := by
    unfold vNormSq nsq dot
    exact Finset.sum_congr rfl fun a _ => (sq _).symm
  have g3 : ∑ a, (X a + ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2)) ^ 2 = ∑ a, X a ^ 2 +
      (2 * ∑ a, X a * ((∑ b, t a b) / 2) - 2 * ∑ a, X a * ((∑ b, sig a b) / 2)) +
      ∑ a, ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have g4 : ∑ a, ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) ^ 2 ≤ (n : ℝ) ^ 3 := by
    calc _ ≤ ∑ _a : Fin n, (n : ℝ) ^ 2 := Finset.sum_le_sum fun a _ => hY a
      _ = (n : ℝ) ^ 3 := by simp; ring
  have g5 : (n : ℝ) ^ 3 < Lc n := by
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    unfold Lc
    nlinarith [pow_le_pow_left₀ h0 (by linarith : (n : ℝ) ≤ n + 1) 3, pow_pos (by linarith : (0 : ℝ) < n + 1) 3]
  rw [g1, g2, g3]
  linarith

end GlobalTheory.CompanionTheory.ClusterNum
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TotalBound
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExhFar

open CompanionTheory.RgExh.U

theorem x_bound {ι : Type*} (s : Finset ι) (x y : ι → ℝ) (a0 : ι) (h0 : a0 ∈ s) (B M K : ℝ) (hK0 : 0 ≤ K)
    (hy : ∀ a ∈ s, |y a| ≤ B) (hM : ∀ a ∈ s, |x a0 - x a| ≤ M) (hK : |∑ a ∈ s, (y a - x a)| ≤ K) :
    |x a0| ≤ B + M + K := by
  have hm : (1 : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨a0, h0⟩
  have e : (s.card : ℝ) * x a0 = ∑ a ∈ s, y a - ∑ a ∈ s, (y a - x a) + ∑ a ∈ s, (x a0 - x a) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have h1 : |∑ a ∈ s, y a| ≤ (s.card : ℝ) * B := by
    calc |∑ a ∈ s, y a| ≤ ∑ a ∈ s, |y a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ s, B := Finset.sum_le_sum hy
      _ = (s.card : ℝ) * B := by simp
  have h2 : |∑ a ∈ s, (x a0 - x a)| ≤ (s.card : ℝ) * M := by
    calc |∑ a ∈ s, (x a0 - x a)| ≤ ∑ a ∈ s, |x a0 - x a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ s, M := Finset.sum_le_sum hM
      _ = (s.card : ℝ) * M := by simp
  have h3 : (s.card : ℝ) * |x a0| ≤ (s.card : ℝ) * B + K + (s.card : ℝ) * M := by
    have : |(s.card : ℝ) * x a0| = (s.card : ℝ) * |x a0| := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (s.card : ℝ))]
    rw [← this, e]
    calc _ ≤ |∑ a ∈ s, y a - ∑ a ∈ s, (y a - x a)| + |∑ a ∈ s, (x a0 - x a)| := abs_add_le _ _
      _ ≤ |∑ a ∈ s, y a| + |∑ a ∈ s, (y a - x a)| + |∑ a ∈ s, (x a0 - x a)| := by
          gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith
  have h4 : (s.card : ℝ) * |x a0| ≤ (s.card : ℝ) * (B + M + K) := by nlinarith
  exact le_of_mul_le_mul_left h4 (by linarith)

theorem fiber_bound {ι : Type*} (s : Finset ι) (x y : ι → ℝ) (a0 : ι) (M X K : ℝ) (hX0 : 0 ≤ X)
    (hX : |x a0| ≤ X) (hM : ∀ a ∈ s, |x a - x a0| ≤ M) (hK : |∑ a ∈ s, (y a - x a)| ≤ K) :
    ∑ a ∈ s, ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) - 2 * X * K ≤ ∑ a ∈ s, (y a ^ 2 - x a ^ 2) := by
  have h1 : ∀ a ∈ s, ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) + 2 * x a0 * (y a - x a) ≤ y a ^ 2 - x a ^ 2 := by
    intro a ha
    have he : (x a - x a0) ^ 2 ≤ M ^ 2 := sq_le_sq' (by linarith [(abs_le.mp (hM a ha)).1])
      (abs_le.mp (hM a ha)).2
    nlinarith [sq_nonneg ((y a - x a) + 2 * (x a - x a0))]
  have h2 := Finset.sum_le_sum h1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h2
  have h3 : -(2 * X * K) ≤ 2 * x a0 * ∑ a ∈ s, (y a - x a) := by
    have : |x a0 * ∑ a ∈ s, (y a - x a)| ≤ X * K := by
      rw [abs_mul]
      exact mul_le_mul hX hK (abs_nonneg _) hX0
    nlinarith [(abs_le.mp this).1]
  linarith

theorem total_bound {n : ℕ} (x y : Fin n → ℝ) (lev : Fin n → ℕ) (M X K : ℝ) (hX0 : 0 ≤ X) (hK0 : 0 ≤ K)
    (hX : ∀ a, |x a| ≤ X) (hM : ∀ a b, lev a = lev b → |x a - x b| ≤ M)
    (hK : ∀ c, |∑ a ∈ univ.filter (fun a => lev a = c), (y a - x a)| ≤ K) :
    ∑ a, ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) - n * (2 * X * K) ≤ ∑ a, (y a ^ 2 - x a ^ 2) := by
  have hmaps : ∀ a ∈ (univ : Finset (Fin n)), lev a ∈ univ.image lev :=
    fun a _ => Finset.mem_image_of_mem _ (Finset.mem_univ a)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun a => y a ^ 2 - x a ^ 2),
    ← Finset.sum_fiberwise_of_maps_to hmaps (fun a => (y a - x a) ^ 2 / 2 - 2 * M ^ 2)]
  have hcard : ((univ.image lev).card : ℝ) ≤ n := by
    have := Finset.card_image_le (s := (univ : Finset (Fin n))) (f := lev)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have h1 : ∑ c ∈ univ.image lev, (∑ a ∈ univ.filter (fun a => lev a = c),
      ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) - 2 * X * K) ≤
      ∑ c ∈ univ.image lev, ∑ a ∈ univ.filter (fun a => lev a = c), (y a ^ 2 - x a ^ 2) := by
    refine Finset.sum_le_sum fun c hc => ?_
    obtain ⟨a0, -, rfl⟩ := Finset.mem_image.mp hc
    refine fiber_bound _ x y a0 M X K hX0 (hX a0) (fun a ha => ?_) (hK _)
    exact hM a a0 (Finset.mem_filter.mp ha).2
  rw [Finset.sum_sub_distrib] at h1
  simp only [Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ((univ.image lev).card : ℝ) * (2 * X * K) ≤ n * (2 * X * K) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  linarith

theorem two_bound {n : ℕ} (d : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) (D : ℝ) (hD : 0 ≤ D)
    (h : D ≤ |d a - d b|) : D ^ 2 / 2 ≤ ∑ c, d c ^ 2 := by
  have h1 : d a ^ 2 + d b ^ 2 ≤ ∑ c, d c ^ 2 := by
    rw [← Finset.sum_pair (f := fun c => d c ^ 2) hab]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have h2 : D ^ 2 ≤ (d a - d b) ^ 2 := by
    rw [← sq_abs (d a - d b)]
    exact pow_le_pow_left₀ hD h 2
  nlinarith [sq_nonneg (d a + d b)]

theorem farNum : FarNum := by
  intro n C δ K hδ
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = |C| := ⟨_, rfl⟩
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ, K' = |K| := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = n * Lc n := ⟨_, rfl⟩
  have hC0 : 0 ≤ C' := hC' ▸ abs_nonneg _
  have hK0 : 0 ≤ K' := hK' ▸ abs_nonneg _
  have hM0 : 0 ≤ M := by rw [hMdef, Lc]; positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 * n * M ^ 2 + 2 * n * K' * (M + K') + 2 * (n : ℝ) ^ 2 * (M + K') + (n : ℝ) ^ 3
      + n * C' ^ 2 + K' := ⟨_, rfl⟩
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = 2 * n * K' * C' + 2 * (n : ℝ) ^ 2 * C' := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ Bc := by rw [hBc]; positivity
  refine ⟨1 + 2 * M / δ + 16 * (A + Bc) / δ ^ 2, ?_⟩
  intro χ x r lev σ N _ _ hr hsp hblk hineq hsep hbd hN a b hab
  by_contra hne
  have hq1 : 0 ≤ 2 * M / δ := by positivity
  have hq2 : 0 ≤ 16 * (A + Bc) / δ ^ 2 := by positivity
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hδN : 2 * M ≤ δ * N := by
    have : 2 * M / δ ≤ N := by linarith
    rw [div_le_iff₀ hδ] at this
    linarith
  have hδ2 : 16 * (A + Bc) + δ ^ 2 ≤ δ ^ 2 * N := by
    have : 16 * (A + Bc) / δ ^ 2 ≤ N - 1 := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    linarith

  obtain ⟨y, hy⟩ : ∃ y : Fin n → ℝ, y = fun a => (χ (σ a)).re := ⟨_, rfl⟩
  have hyb : ∀ a, |y a| ≤ C' * N := by
    intro a
    rw [hy]
    refine (hbd (σ a)).1.trans ?_
    rw [hC']
    exact mul_le_mul_of_nonneg_right (le_abs_self C) hN0
  have hblk' : ∀ c, |∑ a ∈ univ.filter (fun a => lev a = c), (y a - x a)| ≤ K' := by
    intro c
    have h1 := Complex.abs_re_le_norm (∑ a ∈ univ.filter (fun a => lev a = c), χ (σ a)
      - ∑ a ∈ univ.filter (fun a => lev a = c), ((x a : ℝ) : ℂ))
    have h2 : (∑ a ∈ univ.filter (fun a => lev a = c), χ (σ a)
      - ∑ a ∈ univ.filter (fun a => lev a = c), ((x a : ℝ) : ℂ)).re
        = ∑ a ∈ univ.filter (fun a => lev a = c), (y a - x a) := by
      rw [hy, Finset.sum_sub_distrib]
      simp [Complex.re_sum]
    rw [h2] at h1
    exact h1.trans ((hblk c).trans (hK' ▸ le_abs_self K))
  have hspM : ∀ a b, lev a = lev b → |x a - x b| ≤ M := fun a b h => hMdef ▸ hsp a b h

  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = C' * N + M + K' := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hX : ∀ a, |x a| ≤ X := by
    intro a
    rw [hXdef]
    refine x_bound (univ.filter fun c => lev c = lev a) x y a (by simp) _ _ _ hK0
      (fun c _ => hyb c) (fun c hc => hspM a c (Finset.mem_filter.mp hc).2.symm) (hblk' _)

  have hlow := total_bound x y lev M X K' hX0 hK0 hX hspM hblk'
  have hD : (δ * N - M) ^ 2 / 2 ≤ ∑ c, (y c - x c) ^ 2 := by
    refine two_bound (fun c => y c - x c) a b hne _ (by linarith) ?_
    have h1 : δ * N ≤ |y a - y b| := by
      rw [hy]
      exact hsep (σ a) (σ b) (fun h => hne (σ.injective h))
    have h2 := hspM a b hab
    have h3 : |y a - y b| ≤ |(y a - x a) - (y b - x b)| + |x a - x b| := by
      have : y a - y b = ((y a - x a) - (y b - x b)) + (x a - x b) := by ring
      rw [this]
      exact abs_add_le _ _
    show δ * N - M ≤ |(y a - x a) - (y b - x b)|
    linarith

  have hYsum : ∑ a, y a ^ 2 = ∑ a, (χ a).re ^ 2 := by
    rw [hy]
    exact Equiv.sum_comp σ (fun a => (χ a).re ^ 2)
  have hIm : ∑ a, (χ a).im ^ 2 ≤ n * C' ^ 2 := by
    calc ∑ a, (χ a).im ^ 2 ≤ ∑ _a : Fin n, C' ^ 2 := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [← sq_abs (χ a).im]
          exact pow_le_pow_left₀ (abs_nonneg _) ((hbd a).2.trans (hC' ▸ le_abs_self C)) 2
      _ = n * C' ^ 2 := by simp
  have hxr : ∑ a, (x a - r a) ^ 2 ≤ ∑ a, x a ^ 2 + n * (2 * X * n + (n : ℝ) ^ 2) := by
    have : ∀ a ∈ (univ : Finset (Fin n)), (x a - r a) ^ 2 ≤ x a ^ 2 + (2 * X * n + (n : ℝ) ^ 2) := by
      intro a _
      have h1 : |x a * r a| ≤ X * n := by
        rw [abs_mul]
        exact mul_le_mul (hX a) (hr a) (abs_nonneg _) hX0
      have h2 : r a ^ 2 ≤ (n : ℝ) ^ 2 := by
        rw [← sq_abs (r a)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hr a) 2
      nlinarith [(abs_le.mp h1).1]
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_refl _
  have hKK : K ≤ K' := hK' ▸ le_abs_self K
  rw [Finset.sum_sub_distrib] at hineq
  have hup : ∑ a, y a ^ 2 ≤ ∑ a, x a ^ 2 + n * (2 * X * n + (n : ℝ) ^ 2) + n * C' ^ 2 + K' := by
    rw [hYsum]
    linarith
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div] at hlow
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlow
  have hδM : (δ * N / 2) ^ 2 ≤ (δ * N - M) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have e1 : (δ * N / 2) ^ 2 = (δ * N) ^ 2 / 4 := by ring
  have h5 : (δ * N) ^ 2 / 16 ≤ n * (2 * M ^ 2) + n * (2 * X * K') + n * (2 * X * n + (n : ℝ) ^ 2)
      + n * C' ^ 2 + K' := by
    linarith
  have e2 : n * (2 * M ^ 2) + n * (2 * X * K') + n * (2 * X * n + (n : ℝ) ^ 2) + n * C' ^ 2 + K'
      = A + Bc * N := by
    rw [hA, hBc, hXdef]
    ring
  rw [e2] at h5
  have h6 : 16 * (A + Bc) < δ ^ 2 * N := by linarith [pow_pos hδ 2]
  have h7 : 16 * (A + Bc) * N < δ ^ 2 * N * N := mul_lt_mul_of_pos_right h6 (by linarith)
  have e3 : (δ * N) ^ 2 = δ ^ 2 * N * N := by ring
  have h8 : A ≤ A * N := le_mul_of_one_le_right hA0 hN1
  rw [e3] at h5
  linarith

end GlobalTheory.CompanionTheory.RgExhFar
end
end

