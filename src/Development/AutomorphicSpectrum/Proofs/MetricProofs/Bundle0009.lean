module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0007
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicGroupLawGerm
section
open Set

namespace GlobalTheory.CompanionTheory.Ar.Flat

def IsHolMarkingOn {n g : ℕ} {Λ : Type} [AddCommGroup Λ]
    (Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)) (Q : (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℝ)
    (e : Λ → Λ → ℝ) (U : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))) : Prop :=
  (∀ x, DifferentiableOn ℂ (fun b => P b x) U) ∧
    ∀ b ∈ U, Function.Injective (P b) ∧ (P b).range = Γ b ∧ ∀ x y, Q b (P b x) (P b y) = e x y

section
variable {n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Countable Λ]
  {Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)} {Q : (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℝ}
  {e : Λ → Λ → ℝ}

omit [Countable Λ] in
theorem IsHolMarkingOn.mono {U V : Set (Fin n → ℂ)} {P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))}
    (h : IsHolMarkingOn Γ Q e U P) (hVU : V ⊆ U) : IsHolMarkingOn Γ Q e V P :=
  ⟨fun x => (h.1 x).mono hVU, fun b hb => h.2 b (hVU hb)⟩

theorem IsHolMarkingOn.exists_twist {U V : Set (Fin n → ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    (hc : IsPreconnected (U ∩ V)) (hne : (U ∩ V).Nonempty)
    {P P' : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))}
    (h : IsHolMarkingOn Γ Q e U P) (h' : IsHolMarkingOn Γ Q e V P') :
    ∃ R : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), IsHolMarkingOn Γ Q e V R ∧
      ∀ b ∈ U ∩ V, R b = P b := by
  obtain ⟨T, hT⟩ := exists_const_addEquiv_of_range_eq n g Λ Λ (U ∩ V) (hU.inter hV) hc hne P P'
    (fun x => (h.1 x).mono inter_subset_left) (fun x => (h'.1 x).mono inter_subset_right)
    (fun b hb => ⟨(h.2 b hb.1).1, (h'.2 b hb.2).1, by
      rw [(h.2 b hb.1).2.1, (h'.2 b hb.2).2.1]⟩)
  have hR : ∀ b ∈ U ∩ V, ∀ x, P' b (T.symm x) = P b x := fun b hb x => by
    rw [hT b hb, T.apply_symm_apply]
  refine ⟨fun b => (P' b).comp T.symm.toAddMonoidHom, ⟨fun x => h'.1 (T.symm x), ?_⟩, ?_⟩
  · intro b hb
    obtain ⟨hi, hr, hq⟩ := h'.2 b hb
    refine ⟨hi.comp T.symm.injective, ?_, ?_⟩
    · rw [← hr]
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨T.symm x, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨T x, by simp⟩
    · intro x y
      obtain ⟨c, hc'⟩ := hne
      have h1 := (h.2 c hc'.1).2.2 x y
      have h2 := (h'.2 c hc'.2).2.2 (T.symm x) (T.symm y)
      rw [hR c hc' x, hR c hc' y, h1] at h2
      simpa using (hq (T.symm x) (T.symm y)).trans h2.symm
  · intro b hb
    ext1 x
    exact hR b hb x

theorem IsHolMarkingOn.exists_glue {U V : Set (Fin n → ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    (hc : IsPreconnected (U ∩ V)) (hne : (U ∩ V).Nonempty)
    {P P' : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))}
    (h : IsHolMarkingOn Γ Q e U P) (h' : IsHolMarkingOn Γ Q e V P') :
    ∃ R, IsHolMarkingOn Γ Q e (U ∪ V) R := by
  classical
  obtain ⟨R, hR, hRP⟩ := h.exists_twist hU hV hc hne h'
  have eU : ∀ b ∈ U, (if b ∈ U then P b else R b) = P b := fun b hb => if_pos hb
  have eV : ∀ b ∈ V, (if b ∈ U then P b else R b) = R b := fun b hb => by
    by_cases hbU : b ∈ U
    · rw [if_pos hbU, hRP b ⟨hbU, hb⟩]
    · rw [if_neg hbU]
  refine ⟨fun b => if b ∈ U then P b else R b, fun x => ?_, ?_⟩
  · have d1 : DifferentiableOn ℂ (fun b => (if b ∈ U then P b else R b) x) U :=
      (h.1 x).congr fun b hb => by rw [eU b hb]
    have d2 : DifferentiableOn ℂ (fun b => (if b ∈ U then P b else R b) x) V :=
      (hR.1 x).congr fun b hb => by rw [eV b hb]
    rintro b (hb | hb)
    · exact ((d1 b hb).differentiableAt (hU.mem_nhds hb)).differentiableWithinAt
    · exact ((d2 b hb).differentiableAt (hV.mem_nhds hb)).differentiableWithinAt
  · rintro b (hb | hb)
    · simpa only [eU b hb] using h.2 b hb
    · simpa only [eV b hb] using hR.2 b hb

theorem IsHolMarkingOn.eq_of_eq_at {W : Set (Fin n → ℂ)} (hW : IsOpen W) (hc : IsPreconnected W)
    {P P' : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))}
    (h : IsHolMarkingOn Γ Q e W P) (h' : IsHolMarkingOn Γ Q e W P')
    {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ W) (h0 : P b₀ = P' b₀) : ∀ b ∈ W, P b = P' b := by
  obtain ⟨T, hT⟩ := exists_const_addEquiv_of_range_eq n g Λ Λ W hW hc ⟨b₀, hb₀⟩ P P' h.1 h'.1
    (fun b hb => ⟨(h.2 b hb).1, (h'.2 b hb).1, by rw [(h.2 b hb).2.1, (h'.2 b hb).2.1]⟩)
  have hid : ∀ x, T x = x := fun x => (h.2 b₀ hb₀).1 (by rw [← hT b₀ hb₀, h0])
  intro b hb
  ext1 x
  rw [hT b hb, hid]

theorem exists_marking_of_convex_family {B : Set (Fin n → ℂ)} {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ B)
    (H : ∀ b ∈ B, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ Convex ℝ U ∧ U ⊆ B ∧ b₀ ∈ U ∧ b ∈ U ∧
      ∃ P, IsHolMarkingOn Γ Q e U P) :
    ∃ P, IsHolMarkingOn Γ Q e B P := by
  obtain ⟨U₀, hU₀, hC₀, -, hbU₀, -, P₀, hP₀⟩ := H b₀ hb₀
  have H' : ∀ b ∈ B, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ Convex ℝ U ∧ U ⊆ B ∧ b₀ ∈ U ∧ b ∈ U ∧
      ∃ R, IsHolMarkingOn Γ Q e U R ∧ R b₀ = P₀ b₀ := by
    intro b hb
    obtain ⟨U, hU, hC, hUB, h0, h1, P, hP⟩ := H b hb
    obtain ⟨R, hR, hRP⟩ := hP₀.exists_twist hU₀ hU (hC₀.inter hC).isPreconnected ⟨b₀, hbU₀, h0⟩ hP
    exact ⟨U, hU, hC, hUB, h0, h1, R, hR, hRP b₀ ⟨hbU₀, h0⟩⟩
  choose! U hU hC hUB h0 h1 R hR hRb using H'
  have key : ∀ b ∈ B, ∀ c ∈ U b, R c c = R b c := fun b hb c hcb => by
    have hc : c ∈ B := hUB b hb hcb
    exact ((hR c hc).mono inter_subset_left).eq_of_eq_at ((hU c hc).inter (hU b hb))
      ((hC c hc).inter (hC b hb)).isPreconnected ((hR b hb).mono inter_subset_right)
      ⟨h0 c hc, h0 b hb⟩ ((hRb c hc).trans (hRb b hb).symm) c ⟨h1 c hc, hcb⟩
  refine ⟨fun b => R b b, fun x b hb => ?_, fun b hb => (hR b hb).2 b (h1 b hb)⟩
  have hn := (hU b hb).mem_nhds (h1 b hb)
  have hev : (fun c => R c c x) =ᶠ[nhds b] fun c => R b c x := by
    filter_upwards [hn] with c hc
    rw [key b hb c hc]
  exact (((hR b hb).1 x b (h1 b hb)).differentiableAt hn).congr_of_eventuallyEq hev
    |>.differentiableWithinAt

theorem exists_marking_tube {B : Set (Fin n → ℂ)} (hconv : Convex ℝ B)
    (H : ∀ b₀ ∈ B, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ b₀ ∈ N ∧ N ⊆ B ∧
      ∃ P, IsHolMarkingOn Γ Q e N P)
    {a b : Fin n → ℂ} (ha : a ∈ B) (hb : b ∈ B) :
    ∃ U : Set (Fin n → ℂ), IsOpen U ∧ Convex ℝ U ∧ U ⊆ B ∧ a ∈ U ∧ b ∈ U ∧
      ∃ P, IsHolMarkingOn Γ Q e U P := by
  let γ : ℝ →ᵃ[ℝ] (Fin n → ℂ) := AffineMap.lineMap a b
  have hγ : Continuous γ := by
    have : (γ : ℝ → Fin n → ℂ) = fun t => t • (b - a) + a :=
      funext fun t => AffineMap.lineMap_apply_module' a b t
    rw [this]
    fun_prop
  have hγ0 : γ 0 = a := AffineMap.lineMap_apply_zero a b
  have hγ1 : γ 1 = b := AffineMap.lineMap_apply_one a b
  have hmem : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ B := fun r hr =>
    hconv.segment_subset ha hb (by rw [segment_eq_image_lineMap]; exact ⟨r, hr, rfl⟩)
  let ι := {N : Set (Fin n → ℂ) // IsOpen N ∧ N ⊆ B ∧ ∃ P, IsHolMarkingOn Γ Q e N P}
  let c : ι → Set unitInterval := fun N => (fun s : unitInterval => γ s) ⁻¹' N.1
  obtain ⟨t, ht0, hmono, ⟨m, hm⟩, hcov⟩ := exists_monotone_Icc_subset_open_cover_unitInterval
    (c := c) (fun N => N.2.1.preimage (hγ.comp continuous_subtype_val)) (fun s _ => by
      obtain ⟨N, h1, h2, h3, h4⟩ := H _ (hmem s s.2)
      exact mem_iUnion.2 ⟨⟨N, h1, h3, h4⟩, h2⟩)
  have claim : ∀ k, ∃ δ : ℝ, 0 < δ ∧ Metric.thickening δ (γ '' Icc 0 (t k : ℝ)) ⊆ B ∧
      ∃ P, IsHolMarkingOn Γ Q e (Metric.thickening δ (γ '' Icc 0 (t k : ℝ))) P := by
    intro k
    induction k with
    | zero =>
      obtain ⟨N, hN, haN, hNB, P, hP⟩ := H a ha
      have hsub : γ '' Icc 0 (t 0 : ℝ) ⊆ N := by
        rintro _ ⟨r, hr, rfl⟩
        have hr0 : r = 0 := le_antisymm (by simpa [ht0] using hr.2) hr.1
        rw [hr0, hγ0]
        exact haN
      obtain ⟨δ, hδ, hth⟩ := (isCompact_Icc.image hγ).exists_thickening_subset_open hN hsub
      exact ⟨δ, hδ, hth.trans hNB, P, hP.mono hth⟩
    | succ k ih =>
      obtain ⟨δ₁, hδ₁, hB₁, P₁, hP₁⟩ := ih
      obtain ⟨N, hN⟩ := hcov k
      obtain ⟨hNo, hNB, P₂, hP₂⟩ := N.2
      have hle : (t k : ℝ) ≤ t (k + 1) := hmono (Nat.le_succ k)
      have h0 : (0 : ℝ) ≤ t k := (t k).2.1
      have hsub : γ '' Icc (t k : ℝ) (t (k + 1)) ⊆ N.1 := by
        rintro _ ⟨r, hr, rfl⟩
        have hr' : r ∈ Icc (0 : ℝ) 1 := ⟨h0.trans hr.1, hr.2.trans (t (k + 1)).2.2⟩
        exact hN (show (⟨r, hr'⟩ : unitInterval) ∈ Icc (t k) (t (k + 1)) from ⟨hr.1, hr.2⟩)
      obtain ⟨δ₂, hδ₂, hth⟩ := (isCompact_Icc.image hγ).exists_thickening_subset_open hNo hsub
      have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
      have hA : Metric.thickening (min δ₁ δ₂) (γ '' Icc 0 (t k : ℝ)) ⊆
          Metric.thickening δ₁ (γ '' Icc 0 (t k : ℝ)) :=
        Metric.thickening_mono (min_le_left _ _) _
      have hC : Metric.thickening (min δ₁ δ₂) (γ '' Icc (t k : ℝ) (t (k + 1))) ⊆ N.1 :=
        (Metric.thickening_mono (min_le_right _ _) _).trans hth
      have hKs : γ '' Icc 0 (t (k + 1) : ℝ) =
          γ '' Icc 0 (t k : ℝ) ∪ γ '' Icc (t k : ℝ) (t (k + 1)) := by
        rw [← image_union, Icc_union_Icc_eq_Icc h0 hle]
      have hconvA := ((convex_Icc (0 : ℝ) (t k)).affine_image γ).thickening (min δ₁ δ₂)
      have hconvC := ((convex_Icc (t k : ℝ) (t (k + 1))).affine_image γ).thickening (min δ₁ δ₂)
      have hpt : γ (t k) ∈ Metric.thickening (min δ₁ δ₂) (γ '' Icc 0 (t k : ℝ)) ∩
          Metric.thickening (min δ₁ δ₂) (γ '' Icc (t k : ℝ) (t (k + 1))) :=
        ⟨Metric.self_subset_thickening hδ _ ⟨_, ⟨h0, le_rfl⟩, rfl⟩,
          Metric.self_subset_thickening hδ _ ⟨_, ⟨le_rfl, hle⟩, rfl⟩⟩
      obtain ⟨R, hR⟩ := (hP₁.mono hA).exists_glue (P' := P₂) Metric.isOpen_thickening
        Metric.isOpen_thickening (hconvA.inter hconvC).isPreconnected ⟨_, hpt⟩ (hP₂.mono hC)
      refine ⟨min δ₁ δ₂, hδ, ?_, R, ?_⟩
      · rw [hKs, Metric.thickening_union]
        exact union_subset (hA.trans hB₁) (hC.trans hNB)
      · rw [hKs, Metric.thickening_union]
        exact hR
  obtain ⟨δ, hδ, hδB, P, hP⟩ := claim m
  have htm : (t m : ℝ) = 1 := by rw [hm m le_rfl]; rfl
  rw [htm] at hδB hP
  exact ⟨_, Metric.isOpen_thickening, ((convex_Icc (0 : ℝ) 1).affine_image γ).thickening δ, hδB,
    Metric.self_subset_thickening hδ _ ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩,
    Metric.self_subset_thickening hδ _ ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩, P, hP⟩

end

theorem exists_global_marking_of_local : ∀ (n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Countable Λ] (B : Set (Fin n → ℂ)), IsOpen B → Convex ℝ B → ∀ (Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)) (Q : (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℝ) (e : Λ → Λ → ℝ), (∀ b₀ ∈ B, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ b₀ ∈ N ∧ N ⊆ B ∧ ∃ P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun b => P b x) N) ∧ ∀ b ∈ N, Function.Injective (P b) ∧ (P b).range = Γ b ∧ ∀ x y, Q b (P b x) (P b y) = e x y) → ∃ P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun b => P b x) B) ∧ ∀ b ∈ B, Function.Injective (P b) ∧ (P b).range = Γ b ∧ ∀ x y, Q b (P b x) (P b y) = e x y := by
  intro n g Λ _ _ B _ hconv Γ Q e H
  rcases B.eq_empty_or_nonempty with rfl | ⟨b₀, hb₀⟩
  · exact ⟨fun _ => 0, fun x => by simp, by simp⟩
  · have H' : ∀ b₀ ∈ B, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ b₀ ∈ N ∧ N ⊆ B ∧
        ∃ P, IsHolMarkingOn Γ Q e N P := fun b hb => by
      obtain ⟨N, h1, h2, h3, P, h4, h5⟩ := H b hb
      exact ⟨N, h1, h2, h3, P, h4, h5⟩
    obtain ⟨P, hP⟩ := exists_marking_of_convex_family hb₀
      (fun b hb => exists_marking_tube hconv H' hb₀ hb)
    exact ⟨P, hP.1, hP.2⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviFlatSeparatelyHarmonic
section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

theorem harmonicAt_update_of_levi_eq_zero :
    ∀ (n : ℕ) (φ : (Fin n → ℂ) → ℝ) (O : Set (Fin n → ℂ)), IsOpen O → ContDiffOn ℝ ∞ φ O →
      (∀ z ∈ O, ∀ w, levi φ z w = 0) → ∀ z ∈ O, ∀ i,
        InnerProductSpace.HarmonicAt (fun t : ℂ => φ (Function.update z i t)) (z i) := by
  intro n φ O hO hφ hl z hz i
  set e : Fin n → ℂ := Pi.single i 1 with he
  let L : ℂ →L[ℝ] (Fin n → ℂ) := ((ContinuousLinearMap.id ℂ ℂ).smulRight e).restrictScalars ℝ
  have hLw : ∀ w : ℂ, L w = w • e := fun _ => rfl
  set z0 : Fin n → ℂ := Function.update z i 0 with hz0
  have hupd : ∀ t : ℂ, Function.update z i t = z0 + t • e := by
    intro t
    funext j
    by_cases h : j = i
    · subst h
      simp [hz0, he]
    · simp [hz0, he, h]
  have hline : ∀ t : ℂ, HasFDerivAt (fun w : ℂ => z0 + w • e) L t := fun t =>
    L.hasFDerivAt.const_add z0
  have hcont : Continuous (fun t : ℂ => z0 + t • e) := by fun_prop
  have hU : IsOpen ((fun t : ℂ => z0 + t • e) ⁻¹' O) := hO.preimage hcont
  have hzU : z i ∈ (fun t : ℂ => z0 + t • e) ⁻¹' O := by
    show z0 + z i • e ∈ O
    rw [← hupd]
    simpa using hz
  have hφ2 : ∀ y ∈ O, ContDiffAt ℝ 2 φ y := fun y hy =>
    ((hφ y hy).contDiffAt (hO.mem_nhds hy)).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp)
  have hlap : ∀ t ∈ (fun t : ℂ => z0 + t • e) ⁻¹' O,
      Laplacian.laplacian (fun t : ℂ => φ (z0 + t • e)) t = 0 := by
    intro t ht
    have hy : z0 + t • e ∈ O := ht
    have h1 : fderiv ℝ (fun w : ℂ => φ (z0 + w • e)) =ᶠ[𝓝 t]
        fun w : ℂ => (fderiv ℝ φ (z0 + w • e)).comp L := by
      filter_upwards [hU.mem_nhds ht] with w hw
      exact (((hφ2 _ hw).differentiableAt (by simp)).hasFDerivAt.comp w (hline w)).fderiv
    have hD : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (z0 + t • e)) (z0 + t • e) :=
      (((hφ2 _ hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
    have h2 := ((hD.comp t (hline t)).clm_comp (hasFDerivAt_const L t)).fderiv
    simp only [Function.comp_def] at h2
    have hle := hl _ hy e
    unfold levi at hle
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDeriv_two_apply]
    rw [h1.fderiv_eq, h2]
    simp [hLw]
    linarith
  rw [show (fun t : ℂ => φ (Function.update z i t)) = fun t : ℂ => φ (z0 + t • e) from
    funext fun t => by rw [hupd]]
  refine ⟨?_, ?_⟩
  · have hA : ContDiffAt ℝ 2 (fun t : ℂ => z0 + t • e) (z i) := by
      have : ContDiff ℝ 2 (fun t : ℂ => z0 + L t) := contDiff_const.add L.contDiff
      exact this.contDiffAt
    exact (hφ2 _ hzU).comp (z i) hA
  · filter_upwards [hU.mem_nhds hzU] with t ht
    simpa using hlap t ht

end GlobalTheory.CompanionTheory.Metric
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviZeroInCompatibleChart
section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LeviChart

theorem levi_eq_zero_of_compatChart : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ), IsCompatChart A ψ →
    IsOpen U → A.SmoothOn U g →
    (∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, ∀ w,
      levi (g ∘ (A.chart j).symm) y w = 0) →
    ∀ z ∈ ψ.target, ψ.symm z ∈ U → ∀ w, levi (g ∘ ψ.symm) z w = 0 := by
  intro e X _ A ψ U g hψ hU hg hA z hz hzU w
  obtain ⟨j, hj⟩ := A.cover (ψ.symm z)
  have hzs : z ∈ ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source := ⟨hz, hj⟩
  have hopen : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) :=
    ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target (A.chart j).open_source
  have hτ : AnalyticAt ℂ (⇑(A.chart j) ∘ ⇑ψ.symm) z := (hψ j).2 z hzs
  have hEq : g ∘ ⇑ψ.symm =ᶠ[𝓝 z] (g ∘ ⇑(A.chart j).symm) ∘ (⇑(A.chart j) ∘ ⇑ψ.symm) := by
    filter_upwards [hopen.mem_nhds hzs] with y hy
    simp only [Function.comp_apply, (A.chart j).left_inv hy.2]
  have hcz : (⇑(A.chart j) ∘ ⇑ψ.symm) z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Set.mem_preimage, Function.comp_apply, (A.chart j).left_inv hj]
    exact hzU
  have hopen2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target hU
  have hsm : ContDiffAt ℝ 2 (g ∘ ⇑(A.chart j).symm) ((⇑(A.chart j) ∘ ⇑ψ.symm) z) :=
    ((hg j).contDiffAt (hopen2.mem_nhds hcz)).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp | norm_num | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
  rw [levi_congr hEq w, levi_comp w hτ hsm]
  exact hA j _ hcz _

end GlobalTheory.CompanionTheory.LeviChart
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalUnitaryNormalFrame2x2
section
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.exists_frame_normal_near :
    ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) →
      (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) →
      ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y' => g y' p q) ∧
        IsUnit (g y).det ∧ (∀ᶠ y' in 𝓝 y, ((g y')ᴴ * G y' * g y').PosDef) ∧
        (∀ p q, ContDiffAt ℝ 2 (fun y' => ((g y')ᴴ * G y' * g y') p q) y) ∧
        (g y)ᴴ * G y * g y = 1 ∧ ∀ p q, fderiv ℝ (fun y' => ((g y')ᴴ * G y' * g y') p q) y = 0 := by
  intro d G y hpd hC
  let Gh : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ := fun y' => (1 / 2 : ℂ) • (G y' + (G y')ᴴ)
  have hent : ∀ y' p q, Gh y' p q = (1 / 2 : ℂ) * (G y' p q + (starRingEnd ℂ) (G y' q p)) := by
    intro y' p q
    simp [Gh, Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply]
    ring
  have hherm : ∀ y', (Gh y').IsHermitian := by
    intro y'
    ext p q
    rw [Matrix.conjTranspose_apply, hent, hent]
    have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
      apply Complex.ext <;> simp
    simp only [RCLike.star_def, map_mul, map_add (f := _), Complex.conj_conj, hhalf]
    ring
  have hEq : ∀ᶠ y' in 𝓝 y, Gh y' = G y' := by
    filter_upwards [hpd] with y' h
    have e : (G y')ᴴ = G y' := h.isHermitian.eq
    ext p q
    simp only [Gh, e, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hy : Gh y = G y := hEq.self_of_nhds
  have hpdy : (Gh y).PosDef := by
    rw [hy]
    exact hpd.self_of_nhds
  have hCh : ∀ p q, ContDiffAt ℝ 2 (fun y' => Gh y' p q) y := by
    intro p q
    have h1 := hC p q
    have h2 : ContDiffAt ℝ 2 (fun y' => (starRingEnd ℂ) (G y' q p)) y :=
      Complex.conjCLE.contDiff.contDiffAt.comp y (hC q p)
    have e : (fun y' => Gh y' p q) = fun y' => (1 / 2 : ℂ) * (G y' p q + (starRingEnd ℂ) (G y' q p)) :=
      funext fun y' => hent y' p q
    rw [e]
    exact contDiffAt_const.mul (h1.add h2)
  obtain ⟨g, hg, hu, h1, hd⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.normal_holomorphic_frame d Gh y hpdy hherm hCh
  refine ⟨g, hg, hu, ?_, GlobalTheory.CompanionTheory.Ar.PB.FibPt.contDiffAt_frame_entry G g y hC hg, ?_, ?_⟩
  · have hc : ∀ p q, ContinuousAt (fun y' => g y' p q) y := fun p q => (hg p q).continuous.continuousAt
    have hdetc : ContinuousAt (fun y' => (g y').det) y := by
      simp only [Matrix.det_fin_two]
      exact ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))
    have hne : ∀ᶠ y' in 𝓝 y, (g y').det ≠ 0 := hdetc.eventually_ne hu.ne_zero
    filter_upwards [hpd, hne] with y' ha hb
    exact (_root_.GlobalTheory.CompanionTheory.Ar.PB.xiPot_logSin_change_of_frame (G y') (g y') ha (isUnit_iff_ne_zero.mpr hb)).1
  · rw [← hy]
    exact h1
  · intro p q
    have hev : (fun y' => ((g y')ᴴ * G y' * g y') p q) =ᶠ[𝓝 y] fun y' => ((g y')ᴴ * Gh y' * g y') p q := by
      filter_upwards [hEq] with y' h
      rw [h]
    rw [hev.fderiv_eq]
    exact hd p q
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PshExtensionAcrossClosedDense
section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.AnForm

theorem isPsh_of_dense_compl : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (Q Q' : LocPot X), IsClosed B → Dense Bᶜ → (∀ x, Q'.U x = Q.U x) → (∀ x, A.SmoothOn (Q'.U x) (Q'.φ x)) → (∀ x, ∀ y ∈ Q.U x, y ∉ B → Q'.φ x y = Q.φ x y) → IsPshOn A Bᶜ Q → IsPsh A Q' := by
  intro e X _ A B Q Q' hB hD hU hS hE hP x j y hy w
  by_contra hneg
  have hneg' : levi (Q'.φ x ∘ (A.chart j).symm) y w < 0 := not_le.mp hneg
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (Q'.isOpen_U x)
  have hf : ContDiffOn ℝ 2 (Q'.φ x ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) :=
    (hS x j).of_le ENat.LEInfty.out
  have hc := continuousOn_levi hO hf
  have hc' : ContinuousOn (fun y' => levi (Q'.φ x ∘ (A.chart j).symm) y' w)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) :=
    hc.comp (f := fun y' => (y', w)) (by fun_prop) (fun y' hy' => ⟨hy', Set.mem_univ _⟩)
  have hV := hc'.isOpen_inter_preimage hO (isOpen_Iio (a := (0 : ℝ)))
  set V := ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) ∩
    (fun y' => levi (Q'.φ x ∘ (A.chart j).symm) y' w) ⁻¹' Set.Iio 0 with hVdef
  have hVt : V ⊆ (A.chart j).target := fun z hz => hz.1.1
  have hVi : IsOpen ((A.chart j).symm '' V) :=
    (A.chart j).symm.isOpen_image_of_subset_source hV hVt
  have hne : ((A.chart j).symm '' V).Nonempty := ⟨_, y, ⟨hy, hneg'⟩, rfl⟩
  obtain ⟨z, ⟨y', hy'V, rfl⟩, hzB⟩ := hD.inter_open_nonempty _ hVi hne
  have hW : IsOpen (V ∩ (A.chart j).symm ⁻¹' Bᶜ) := by
    have h1 := (A.chart j).isOpen_inter_preimage_symm hB.isOpen_compl
    have : V ∩ (A.chart j).symm ⁻¹' Bᶜ =
        V ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Bᶜ) := by
      ext u
      exact ⟨fun h => ⟨h.1, hVt h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [this]
    exact hV.inter h1
  have hev : (Q'.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 y'] (Q.φ x ∘ (A.chart j).symm) := by
    filter_upwards [hW.mem_nhds ⟨hy'V, hzB⟩] with u hu
    have huU : (A.chart j).symm u ∈ Q.U x := hU x ▸ hu.1.1.2
    exact hE x _ huU hu.2
  have h0 := hP x j y' ⟨hy'V.1.1, (hU x ▸ hy'V.1.2 : (A.chart j).symm y' ∈ Q.U x), hzB⟩ w
  rw [← levi_congr hev w] at h0
  exact absurd h0 (not_le.mpr hy'V.2)

end GlobalTheory.CompanionTheory.AnForm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnOfChartComposition
section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

theorem smoothOn_comp_compatChart (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (G : (Fin e → ℂ) → ℝ)
    (hψ : IsCompatChart A ψ) (hO : IsOpen O) (_hOt : O ⊆ ψ.target)
    (hG : ContDiffOn ℝ ∞ G O) : A.SmoothOn (ψ.source ∩ ψ ⁻¹' O) (G ∘ ψ) := by
  intro j y hy
  obtain ⟨hyt, hys, hyO⟩ := hy
  have han : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y := (hψ j).1 y ⟨hyt, hys⟩
  have hτ : ContDiffAt ℝ ∞ (ψ ∘ (A.chart j).symm) y :=
    (han.restrictScalars (𝕜 := ℝ)).contDiffAt.of_le le_top
  have hGat : ContDiffAt ℝ ∞ G ((ψ ∘ (A.chart j).symm) y) :=
    hG.contDiffAt (hO.mem_nhds hyO)
  exact (hGat.comp y hτ).contDiffWithinAt

theorem smoothOn_comp_compatChart' : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (G : (Fin e → ℂ) → ℝ), IsCompatChart A ψ → IsOpen O → O ⊆ ψ.target → ContDiffOn ℝ ∞ G O → A.SmoothOn (ψ.source ∩ ψ ⁻¹' O) (G ∘ ψ) :=
  fun e X _ A ψ O G h1 h2 h3 h4 => smoothOn_comp_compatChart e X A ψ O G h1 h2 h3 h4

end GlobalTheory.CompanionTheory.Metric
end

