module

public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0003
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.LeviForms.RegChartB
section
namespace ReciprocityTheory.AnForm.P.RegularChartScaling

open MeasureTheory Metric Filter Topology Set
open ReciprocityTheory.AnForm.A

noncomputable section

variable {D : ℕ}

lemma log_term_nonneg {x : ℂ} (hx : ‖x‖ ≤ 2) : 0 ≤ Real.log (4 / ‖x‖ ^ 2) := by
  rcases eq_or_lt_of_le (norm_nonneg x) with h | h
  · rw [← h]; simp
  · apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]; nlinarith

lemma rLoc_ge (S : Finset (Fin D)) (m : Fin D → ℕ) {x : Fin D → ℂ} (hx : ∀ i, ‖x i‖ ≤ 2) :
    Real.exp 1 ≤ rLoc S m x := by
  unfold rLoc
  have : 0 ≤ ∑ i ∈ S, (m i : ℝ) * Real.log (4 / ‖x i‖ ^ 2) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (log_term_nonneg (hx i))
  linarith

lemma rLoc_pos (S : Finset (Fin D)) (m : Fin D → ℕ) {x : Fin D → ℂ} (hx : ∀ i, ‖x i‖ ≤ 2) :
    0 < rLoc S m x := (Real.exp_pos 1).trans_le (rLoc_ge S m hx)

lemma norm_coord_le_of_ball {R : ℝ} (hR : R ≤ 2) {x : Fin D → ℂ} (hx : x ∈ ball (0 : Fin D → ℂ) R)
    (i : Fin D) : ‖x i‖ ≤ 2 :=
  (norm_le_pi_norm x i).trans ((mem_ball_zero_iff.1 hx).le.trans hR)

def mTot (S : Finset (Fin D)) (m : Fin D → ℕ) : ℝ := ∑ i ∈ S, (m i : ℝ)

lemma mTot_nonneg (S : Finset (Fin D)) (m : Fin D → ℕ) : 0 ≤ mTot S m :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

lemma rLoc_le_far (S : Finset (Fin D)) (m : Fin D → ℕ) {x : Fin D → ℂ} {s : ℝ} (hs : 0 < s)
    (hx : ∀ i, s ≤ ‖x i‖) : rLoc S m x ≤ Real.exp 1 + mTot S m * Real.log (4 / s ^ 2) := by
  unfold rLoc mTot
  rw [Finset.sum_mul]
  have : ∑ i ∈ S, (m i : ℝ) * Real.log (4 / ‖x i‖ ^ 2) ≤ ∑ i ∈ S, (m i : ℝ) * Real.log (4 / s ^ 2) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (Real.log_le_log (div_pos (by norm_num) (pow_pos (hs.trans_le (hx i)) 2))
        (div_le_div_of_nonneg_left (by norm_num) (pow_pos hs 2) (pow_le_pow_left₀ hs.le (hx i) 2)))
      (Nat.cast_nonneg _)
  linarith

def pmoff (S : Finset (Fin D)) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (t : ℝ) : ℝ :=
  sSup (φ '' (closedBall z t \ coordDiv S))

section Osc

variable {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {R C₅ : ℝ}

lemma pmo_bdd (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅) {z : Fin D → ℂ} {s : ℝ}
    (hs : closedBall z s ⊆ ball 0 R) : BddAbove (u '' (closedBall z s \ coordDiv S)) :=
  ⟨C₅, by rintro _ ⟨x, hx, rfl⟩; exact hub x ⟨hs hx.1, hx.2⟩⟩

lemma pmo_nonempty (z : Fin D → ℂ) {s : ℝ} (hs : 0 < s) :
    (u '' (closedBall z s \ coordDiv S)).Nonempty := by
  obtain ⟨x, hx, hf, -⟩ := exists_far_point z hs
  exact ⟨u x, x, ⟨hx, not_mem_coordDiv_of hs hf⟩, rfl⟩

lemma le_pmo (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅) {z : Fin D → ℂ} {s : ℝ}
    (hs : closedBall z s ⊆ ball 0 R) {x : Fin D → ℂ} (hx : x ∈ closedBall z s \ coordDiv S) :
    u x ≤ pmoff S u z s :=
  le_csSup (pmo_bdd hub hs) (mem_image_of_mem u hx)

lemma pmo_le (z : Fin D → ℂ) {s c : ℝ} (hs : 0 < s) (h : ∀ x ∈ closedBall z s \ coordDiv S, u x ≤ c) :
    pmoff S u z s ≤ c :=
  csSup_le (pmo_nonempty z hs) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

lemma pmo_mono (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅) {z : Fin D → ℂ}
    {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') (hs' : closedBall z s' ⊆ ball 0 R) :
    pmoff S u z s ≤ pmoff S u z s' :=
  csSup_le_csSup (pmo_bdd hub hs') (pmo_nonempty z hs)
    (image_mono (sdiff_subset_sdiff_left (closedBall_subset_closedBall hss)))

lemma pmo_lower (hR : R ≤ 2) (hC₅ : 0 ≤ C₅) (m : Fin D → ℕ)
    (hb : ∀ z ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ u z ∧ u z ≤ C₅)
    {z : Fin D → ℂ} {s : ℝ} (hs : 0 < s) (hsR : closedBall z s ⊆ ball 0 R) :
    -C₅ * Real.log (Real.exp 1 + mTot S m * Real.log (4 / s ^ 2)) ≤ pmoff S u z s := by
  obtain ⟨x, hx, hf, -⟩ := exists_far_point z hs
  have hxA : x ∉ coordDiv S := not_mem_coordDiv_of hs hf
  have hxB : x ∈ ball (0 : Fin D → ℂ) R := hsR hx
  refine le_trans ?_ (le_pmo (fun y hy => (hb y hy).2) hsR ⟨hx, hxA⟩)
  refine le_trans ?_ (hb x ⟨hxB, hxA⟩).1
  have h1 := rLoc_pos S m (norm_coord_le_of_ball hR hxB)
  have h2 := rLoc_le_far S m hs hf
  have : Real.log (rLoc S m x) ≤ Real.log (Real.exp 1 + mTot S m * Real.log (4 / s ^ 2)) :=
    Real.log_le_log h1 h2
  nlinarith

lemma pmo_le_polyMax {w : (Fin D → ℂ) → ℝ} (hw : UpperSemicontinuousOn w (ball 0 R))
    (hwu : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ w x) {z : Fin D → ℂ} {s : ℝ}
    (hs : 0 < s) (hsR : closedBall z s ⊆ ball 0 R) :
    pmoff S u z s ≤ polyMax w z s :=
  pmo_le z hs fun x hx => (hwu x ⟨hsR hx.1, hx.2⟩).trans (le_polyMax hw hsR hx.1)

lemma polyMax_le_pmo (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅)
    {w : (Fin D → ℂ) → ℝ} {κ : ℝ}
    (hW3 : ∀ x ∈ ball (0 : Fin D → ℂ) R, ∀ δ > 0, ∃ y ∈ ball (0 : Fin D → ℂ) R \ coordDiv S,
        dist y x < δ ∧ w x ≤ max (u y) (-κ) + δ)
    {z : Fin D → ℂ} {s s' : ℝ} (hs : 0 ≤ s) (hss : s < s') (hsR : closedBall z s' ⊆ ball 0 R) :
    polyMax w z s ≤ max (pmoff S u z s') (-κ) := by
  refine polyMax_le' hs fun x hx => ?_
  have hxB : x ∈ ball (0 : Fin D → ℂ) R := hsR (closedBall_subset_closedBall hss.le hx)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨y, hy, hyd, hwy⟩ := hW3 x hxB (min δ (s' - s)) (lt_min hδ (by linarith))
  have hyz : y ∈ closedBall z s' := by
    rw [mem_closedBall] at hx ⊢
    have := dist_triangle y x z
    linarith [min_le_right δ (s' - s)]
  have : u y ≤ pmoff S u z s' := le_pmo hub hsR ⟨hyz, hy.2⟩
  have : max (u y) (-κ) ≤ max (pmoff S u z s') (-κ) := max_le_max this le_rfl
  linarith [min_le_left δ (s' - s)]

end Osc

end

end ReciprocityTheory.AnForm.P.RegularChartScaling
end

-- bundled from ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
section
namespace ReciprocityTheory.AnForm.P

open MeasureTheory Metric ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff

noncomputable section

def chartBall {e : ℕ} {X : Type} [TopologicalSpace X] (B : FinHolAtlas e X) (j : Fin B.n) (ρ : ℝ) :
    Set X :=
  (B.chart j).source ∩ B.chart j ⁻¹' ball 0 ρ

def RegMaxDominatedStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι] (η : ℝ) (t : ι → ℝ) (k₀ : ι)
    (I : Finset ι), 0 < η → k₀ ∈ I → (∀ j ∉ I, t j + η ≤ t k₀) →
      ReciprocityTheory.AnForm.A.regMax η t =
        ReciprocityTheory.AnForm.A.regMax η (fun j => if j ∈ I then t j else t k₀ - η)

private theorem kθ_eq_zero_of_half_le_abs {x : ℝ} (hx : 1 / 2 ≤ |x|) : ReciprocityTheory.AnForm.A.kθ x = 0 := by
  unfold ReciprocityTheory.AnForm.A.kθ
  by_contra hne
  have hm : x ∈ Function.support
      ((⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)).normed volume) := hne
  rw [ContDiffBump.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hm
  exact absurd hm (not_lt.mpr hx)

private theorem tmax_eq_of_eqOn_of_le_at_mem {ι : Type} [Fintype ι] [Nonempty ι] (f g : ι → ℝ) (I : Finset ι) (k₀ : ι)
    (hk₀ : k₀ ∈ I) (hI : ∀ j ∈ I, f j = g j) (hf : ∀ j ∉ I, f j ≤ f k₀) (hg : ∀ j ∉ I, g j ≤ g k₀) :
    ReciprocityTheory.AnForm.A.tmax f = ReciprocityTheory.AnForm.A.tmax g := by
  unfold ReciprocityTheory.AnForm.A.tmax
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    by_cases hj : j ∈ I
    · rw [hI j hj]
      exact Finset.le_sup' g (Finset.mem_univ j)
    · calc f j ≤ f k₀ := hf j hj
        _ = g k₀ := hI k₀ hk₀
        _ ≤ _ := Finset.le_sup' g (Finset.mem_univ k₀)
  · apply Finset.sup'_le
    intro j _
    by_cases hj : j ∈ I
    · rw [← hI j hj]
      exact Finset.le_sup' f (Finset.mem_univ j)
    · calc g j ≤ g k₀ := hg j hj
        _ = f k₀ := (hI k₀ hk₀).symm
        _ ≤ _ := Finset.le_sup' f (Finset.mem_univ k₀)

theorem regMax_dominated : RegMaxDominatedStatement := by
  intro ι _ _ _ η t k₀ I hη hk₀ hI
  unfold ReciprocityTheory.AnForm.A.regMax
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  dsimp only
  by_cases hs : ∀ j, |h j| < 1 / 2
  · congr 1
    apply tmax_eq_of_eqOn_of_le_at_mem _ _ I k₀ hk₀
    · intro j hj
      simp [hj]
    · intro j hj
      show t j + η * h j ≤ t k₀ + η * h k₀
      have a := mul_lt_mul_of_pos_left (abs_lt.mp (hs j)).2 hη
      have b := mul_lt_mul_of_pos_left (abs_lt.mp (hs k₀)).1 hη
      have c := hI j hj
      linarith
    · intro j hj
      show (if j ∈ I then t j else t k₀ - η) + η * h j ≤ (if k₀ ∈ I then t k₀ else t k₀ - η) + η * h k₀
      rw [if_neg hj, if_pos hk₀]
      have a := mul_lt_mul_of_pos_left (abs_lt.mp (hs j)).2 hη
      have b := mul_lt_mul_of_pos_left (abs_lt.mp (hs k₀)).1 hη
      linarith
  · push_neg at hs
    obtain ⟨j, hj⟩ := hs
    have h0 : ∏ i, ReciprocityTheory.AnForm.A.kθ (h i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (kθ_eq_zero_of_half_le_abs hj)
    rw [h0, mul_zero, mul_zero]

def GlueCutoffStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] (A B : FinHolAtlas e X), A.Compatible B →
    (∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) →
    ∃ η : Fin B.n → X → ℝ, ∀ j, A.Smooth (η j) ∧ (∀ y, -1 ≤ η j y ∧ η j y ≤ 0) ∧
      (∀ y ∈ chartBall B j 1, η j y = 0) ∧ ∀ y ∉ chartBall B j (9 / 8), η j y = -1

def cutψ (s : ℝ) : ℝ := Real.smoothTransition (64 * (s - 1) / 17)

def cutP {e : ℕ} (z : Fin e → ℂ) : ℝ := ∏ i, (1 - cutψ (‖z i‖ ^ 2))


open Classical in
def glueCut {e : ℕ} {X : Type} [TopologicalSpace X] (B : FinHolAtlas e X) (j : Fin B.n) (y : X) :
    ℝ := by
  classical
  exact if y ∈ (B.chart j).source then cutP (B.chart j y) - 1 else -1

lemma cutψ_nonneg (s : ℝ) : 0 ≤ cutψ s := Real.smoothTransition.nonneg _
lemma cutψ_le_one (s : ℝ) : cutψ s ≤ 1 := Real.smoothTransition.le_one _

lemma cutψ_of_le {s : ℝ} (hs : s ≤ 1) : cutψ s = 0 := by
  unfold cutψ
  apply Real.smoothTransition.zero_of_nonpos
  have h1 : 64 * (s - 1) ≤ 0 := by linarith
  exact div_nonpos_of_nonpos_of_nonneg h1 (by norm_num)

lemma cutψ_of_ge {s : ℝ} (hs : 81 / 64 ≤ s) : cutψ s = 1 := by
  unfold cutψ
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by norm_num)]
  linarith

lemma polydiscCutoff_nonneg {e : ℕ} (z : Fin e → ℂ) : 0 ≤ cutP z := by
  unfold cutP
  exact Finset.prod_nonneg fun i _ => sub_nonneg.mpr (cutψ_le_one _)

lemma cutP_le_one {e : ℕ} (z : Fin e → ℂ) : cutP z ≤ 1 := by
  unfold cutP
  exact Finset.prod_le_one₀ (fun i _ => sub_nonneg.mpr (cutψ_le_one _))
    (fun i _ => by linarith [cutψ_nonneg (‖z i‖ ^ 2)])

lemma polydiscCutoff_eq_one_of_mem_ball {e : ℕ} {z : Fin e → ℂ} (hz : z ∈ ball (0 : Fin e → ℂ) 1) : cutP z = 1 := by
  unfold cutP
  apply Finset.prod_eq_one
  intro i _
  have h1 : ‖z i‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm z i) (mem_ball_zero_iff.mp hz)
  have h2 : ‖z i‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (z i)]
  rw [cutψ_of_le h2, sub_zero]

lemma polydiscCutoff_eq_zero_of_not_mem_ball {e : ℕ} {z : Fin e → ℂ} (hz : z ∉ ball (0 : Fin e → ℂ) (9 / 8)) :
    cutP z = 0 := by
  unfold cutP
  rw [mem_ball_zero_iff, not_lt] at hz
  obtain ⟨i, hi⟩ : ∃ i, 9 / 8 ≤ ‖z i‖ := by
    by_contra hcon
    push_neg at hcon
    have h3 : ‖z‖ < 9 / 8 := (pi_norm_lt_iff (by norm_num)).mpr hcon
    linarith
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have h2 : 81 / 64 ≤ ‖z i‖ ^ 2 := by nlinarith
  rw [cutψ_of_ge h2, sub_self]

lemma cutP_contDiff {e : ℕ} : ContDiff ℝ ∞ (cutP (e := e)) := by
  have hq : ∀ i : Fin e, ContDiff ℝ ∞ (fun z : Fin e → ℂ => 64 * (‖z i‖ ^ 2 - 1) / 17) := fun i =>
    (contDiff_const.mul (((contDiff_apply ℝ (fun _ => ℂ) i).norm_sq ℝ).sub contDiff_const)).div_const 17
  unfold cutP cutψ
  exact contDiff_prod fun i _ => contDiff_const.sub (Real.smoothTransition.contDiff.comp (hq i))

private theorem smooth_glueCut_of_compatible {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X]
    (A B : FinHolAtlas e X) (hAB : A.Compatible B)
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) (j : Fin B.n) :
    A.Smooth (glueCut B j) := by
  have hCt : closedBall (0 : Fin e → ℂ) (9 / 8) ⊆ (B.chart j).target :=
    (closedBall_subset_closedBall (by norm_num)).trans (h2 j)
  have hCc : IsClosed ((B.chart j).symm '' closedBall (0 : Fin e → ℂ) (9 / 8)) :=
    ((isCompact_closedBall _ _).image_of_continuousOn
      ((B.chart j).continuousOn_symm.mono hCt)).isClosed
  have hCsrc : (B.chart j).symm '' closedBall (0 : Fin e → ℂ) (9 / 8) ⊆ (B.chart j).source := by
    rintro _ ⟨z, hz, rfl⟩
    exact (B.chart j).map_target (hCt hz)
  have hout : ∀ y, y ∉ (B.chart j).symm '' closedBall (0 : Fin e → ℂ) (9 / 8) →
      glueCut B j y = -1 := by
    intro y hy
    unfold glueCut
    split_ifs with hys
    · have hn : B.chart j y ∉ ball (0 : Fin e → ℂ) (9 / 8) := fun hb =>
        hy ⟨B.chart j y, ball_subset_closedBall hb, (B.chart j).left_inv hys⟩
      rw [polydiscCutoff_eq_zero_of_not_mem_ball hn]
      ring
    · rfl
  intro k
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  by_cases hxs : (A.chart k).symm x ∈ (B.chart j).source
  · refine ⟨(A.chart k).target ∩ (A.chart k).symm ⁻¹' (B.chart j).source,
      (A.chart k).isOpen_inter_preimage_symm (B.chart j).open_source, ⟨hx.1, hxs⟩, ?_⟩
    have hR : ContDiffOn ℝ ∞ (B.chart j ∘ (A.chart k).symm)
        ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (B.chart j).source) :=
      ((hAB.1 k j).contDiffOn (n := ∞) ((A.chart k).isOpen_inter_preimage_symm
        (B.chart j).open_source).uniqueDiffOn).restrict_scalars ℝ
    have hc := (cutP_contDiff.comp_contDiffOn hR).sub (contDiffOn_const (c := (1 : ℝ)))
    refine (hc.mono Set.inter_subset_right).congr ?_
    intro z hz
    show glueCut B j ((A.chart k).symm z) = cutP (B.chart j ((A.chart k).symm z)) - 1
    unfold glueCut
    exact if_pos hz.2.2
  · refine ⟨(A.chart k).target ∩ (A.chart k).symm ⁻¹' ((B.chart j).symm '' closedBall 0 (9 / 8))ᶜ,
      (A.chart k).isOpen_inter_preimage_symm hCc.isOpen_compl, ⟨hx.1, fun hc => hxs (hCsrc hc)⟩, ?_⟩
    refine (contDiffOn_const (c := (-1 : ℝ))).congr ?_
    intro z hz
    exact hout _ hz.2.2

theorem glue_cutoff : GlueCutoffStatement := by
  intro e X _ _ A B hAB h2
  refine ⟨glueCut B, fun j => ⟨smooth_glueCut_of_compatible A B hAB h2 j, fun y => ?_, fun y hy => ?_,
    fun y hy => ?_⟩⟩
  · unfold glueCut
    split_ifs
    · constructor <;> linarith [polydiscCutoff_nonneg (B.chart j y), cutP_le_one (B.chart j y)]
    · norm_num
  · unfold glueCut
    rw [if_pos hy.1, polydiscCutoff_eq_one_of_mem_ball hy.2, sub_self]
  · unfold glueCut
    split_ifs with hys
    · have hn : B.chart j y ∉ ball (0 : Fin e → ℂ) (9 / 8) := fun hb =>
        hy (show y ∈ (B.chart j).source ∩ B.chart j ⁻¹' ball 0 (9 / 8) from ⟨hys, hb⟩)
      rw [polydiscCutoff_eq_zero_of_not_mem_ball hn]
      norm_num
    · rfl

section Glue

variable {e : ℕ} {X : Type} [TopologicalSpace X]

lemma chartBall_isOpen (B : FinHolAtlas e X) (j : Fin B.n) (ρ : ℝ) : IsOpen (chartBall B j ρ) :=
  (B.chart j).isOpen_inter_preimage isOpen_ball

lemma chartBall_mono (B : FinHolAtlas e X) (j : Fin B.n) {ρ ρ' : ℝ} (h : ρ ≤ ρ') :
    chartBall B j ρ ⊆ chartBall B j ρ' :=
  Set.inter_subset_inter_right _ (Set.preimage_mono (ball_subset_ball h))


open Classical in
def glueArg (B : FinHolAtlas e X) (f η : Fin B.n → X → ℝ) (δ Mb : ℝ) (j : Fin B.n) (y : X) : ℝ := by
  classical
  exact if y ∈ chartBall B j (5 / 4) then f j y + 4 * δ * η j y else -Mb - 10

end Glue

end

end ReciprocityTheory.AnForm.P
end

