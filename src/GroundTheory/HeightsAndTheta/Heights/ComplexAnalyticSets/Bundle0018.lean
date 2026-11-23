module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperSheetedFibreEsymm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Set Complex

open scoped Real

namespace ProperSheetedFibreEsymm


open Classical in
noncomputable def fibreEsymm {σ : Type} {d : ℕ} (Y : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (l : (σ → ℂ) →L[ℂ] ℂ) (j : ℕ) (t : Fin d → ℂ) : ℂ :=
  if h : {x | x ∈ Y ∧ A x = t}.Finite then (h.toFinset.val.map l).esymm j else 0

theorem fibreEsymm_eq {σ : Type} {d : ℕ} {Y : Set (σ → ℂ)} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {l : (σ → ℂ) →L[ℂ] ℂ} {j : ℕ} {t : Fin d → ℂ} (s : Finset (σ → ℂ))
    (hs : (↑s : Set (σ → ℂ)) = {x | x ∈ Y ∧ A x = t}) : fibreEsymm Y A l j t = (s.val.map l).esymm j := by
  have h : {x | x ∈ Y ∧ A x = t}.Finite := hs ▸ s.finite_toSet
  have hs' : h.toFinset = s := Finset.coe_injective (by rw [Set.Finite.coe_toFinset, hs])
  rw [fibreEsymm, dite_eq_left h, hs']

theorem fibre_sections {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} (hD : IsOpen D)
    (hprop : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K})
    (hchart : ∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O)
    {y : Fin d → ℂ} (hyD : y ∈ D) (hδy : δ y ≠ 0) :
    ∃ (F : Finset (σ → ℂ)) (g : (σ → ℂ) → (Fin d → ℂ) → σ → ℂ), (∀ x ∈ F, AnalyticAt ℂ (g x) y) ∧
      ∀ᶠ y' in 𝓝 y, Set.InjOn (fun x => g x y') ↑F ∧
        {x | x ∈ Y ∧ A x = y'} = (fun x => g x y') '' ↑F := by
  choose! O V g hO hV hxV hg hsec hYV using hchart

  have key : ∀ x ∈ Y, δ (A x) ≠ 0 → ∀ z ∈ Y, z ∈ V x → A z ∈ O x ∧ g x (A z) = z := by
    intro x hx hδ z hz hzV
    obtain ⟨w, hw, rfl⟩ : z ∈ g x '' O x := hYV x hx hδ ▸ ⟨hz, hzV⟩
    rw [hsec x hx hδ w hw]; exact ⟨hw, rfl⟩
  set F := {x | x ∈ Y ∧ A x = y} with hFdef
  have hFδ : ∀ x ∈ F, δ (A x) ≠ 0 := fun x hx => hx.2 ▸ hδy
  have hyO : ∀ x ∈ F, y ∈ O x := fun x hx => hx.2 ▸ (key x hx.1 (hFδ x hx) x hx.1 (hxV x hx.1 (hFδ x hx))).1
  have hgy : ∀ x ∈ F, g x y = x := fun x hx => hx.2 ▸ (key x hx.1 (hFδ x hx) x hx.1 (hxV x hx.1 (hFδ x hx))).2

  have hFc : IsCompact F := by
    simpa [hFdef] using hprop {y} (singleton_subset_iff.2 hyD) isCompact_singleton
  have hFfin : F.Finite := by
    obtain ⟨t, htF, hcov⟩ := hFc.elim_nhds_subcover V
      (fun x hx => (hV x hx.1 (hFδ x hx)).mem_nhds (hxV x hx.1 (hFδ x hx)))
    refine t.finite_toSet.subset fun z hz => ?_
    obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (hcov hz)
    have hx := htF x hxt
    have := (key x hx.1 (hFδ x hx) z hz.1 hzx).2
    rw [hz.2, hgy x hx] at this
    exact this ▸ hxt
  refine ⟨hFfin.toFinset, g, fun x hx => ?_, ?_⟩
  · rw [Set.Finite.mem_toFinset] at hx
    exact hg x hx.1 (hFδ x hx) y (hyO x hx)
  rw [Set.Finite.coe_toFinset]

  have hev1 : ∀ᶠ y' in 𝓝 y, ∀ x ∈ F, y' ∈ O x :=
    (eventually_all_finite hFfin).2 fun x hx => (hO x hx.1 (hFδ x hx)).mem_nhds (hyO x hx)

  have hev2 : ∀ᶠ y' in 𝓝 y, ∀ p ∈ F ×ˢ F, p.1 ≠ p.2 → g p.1 y' ≠ g p.2 y' := by
    refine (eventually_all_finite (hFfin.prod hFfin)).2 fun p hp => ?_
    by_cases hne : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hne h
    have c1 := (hg p.1 hp.1.1 (hFδ _ hp.1) y (hyO _ hp.1)).continuousAt
    have c2 := (hg p.2 hp.2.1 (hFδ _ hp.2) y (hyO _ hp.2)).continuousAt
    have hne' : g p.1 y ≠ g p.2 y := by rwa [hgy _ hp.1, hgy _ hp.2]
    exact ((c1.tendsto.prodMk_nhds c2.tendsto).eventually
      (isClosed_diagonal.isOpen_compl.mem_nhds hne')).mono fun _ h _ => h

  have hev3 : ∀ᶠ y' in 𝓝 y, ∀ z ∈ Y, A z = y' → ∃ x ∈ F, z ∈ V x := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hD y hyD
    set K := Metric.closedBall y (ε / 2)
    have hKD : K ⊆ D := (Metric.closedBall_subset_ball (by linarith)).trans hball
    set W := ⋃ x ∈ F, V x
    have hW : IsOpen W := isOpen_biUnion fun x hx => hV x hx.1 (hFδ x hx)
    have hC : IsCompact ({z | z ∈ Y ∧ A z ∈ K} \ W) :=
      (hprop K hKD (isCompact_closedBall y _)).diff hW
    have hyn : y ∉ A '' ({z | z ∈ Y ∧ A z ∈ K} \ W) := by
      rintro ⟨z, ⟨⟨hzY, -⟩, hzW⟩, hzy⟩
      exact hzW (mem_iUnion₂.2 ⟨z, ⟨hzY, hzy⟩, hxV z hzY (hzy ▸ hδy)⟩)
    filter_upwards [Metric.closedBall_mem_nhds y (half_pos hε),
      (hC.image A.continuous).isClosed.isOpen_compl.mem_nhds hyn] with y' hy'K hy'C z hzY hzy
    by_contra hno
    exact hy'C ⟨z, ⟨⟨hzY, hzy ▸ hy'K⟩, fun h => hno (by simpa [W] using h)⟩, hzy⟩
  filter_upwards [hev1, hev2, hev3] with y' h1 h2 h3
  refine ⟨fun a ha b hb hab => ?_, ?_⟩
  · by_contra hne
    exact h2 (a, b) ⟨ha, hb⟩ hne hab
  ext z
  constructor
  · rintro ⟨hzY, hzy⟩
    obtain ⟨x, hx, hzx⟩ := h3 z hzY hzy
    exact ⟨x, hx, by simpa [hzy] using (key x hx.1 (hFδ x hx) z hzY hzx).2⟩
  · rintro ⟨x, hx, rfl⟩
    have hm : g x y' ∈ Y ∩ V x := hYV x hx.1 (hFδ x hx) ▸ mem_image_of_mem _ (h1 x hx)
    exact ⟨hm.1, hsec x hx.1 (hFδ x hx) y' (h1 x hx)⟩

theorem fibreEsymm_analyticAt {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} (l : (σ → ℂ) →L[ℂ] ℂ) (j : ℕ)
    (hD : IsOpen D) (hprop : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K})
    (hchart : ∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O)
    {y : Fin d → ℂ} (hyD : y ∈ D) (hδy : δ y ≠ 0) : AnalyticAt ℂ (fibreEsymm Y A l j) y := by
  classical
  obtain ⟨F, g, hga, hev⟩ := fibre_sections hD hprop hchart hyD hδy
  have hP : AnalyticAt ℂ (fun t => ∑ u ∈ F.powersetCard j, ∏ x ∈ u, l (g x t)) y :=
    Finset.analyticAt_fun_sum _ fun u hu => Finset.analyticAt_fun_prod _ fun x hx =>
      (l.analyticAt _).comp (hga x ((Finset.mem_powersetCard.1 hu).1 hx))
  refine hP.congr ?_
  filter_upwards [hev] with t ht
  rw [fibreEsymm_eq (F.image fun x => g x t) (by rw [Finset.coe_image, ht.2]),
    Finset.image_val_of_injOn ht.1, Multiset.map_map, Finset.esymm_map_val]
  rfl

theorem norm_esymm_map_le {ι : Type*} (S : Finset ι) (f : ι → ℂ) (j : ℕ) {C : ℝ} (hC : ∀ x ∈ S, ‖f x‖ ≤ C) :
    ‖(S.val.map f).esymm j‖ ≤ (S.card.choose j : ℝ) * C ^ j := by
  rw [Finset.esymm_map_val]
  calc ‖∑ u ∈ S.powersetCard j, ∏ x ∈ u, f x‖ ≤ ∑ u ∈ S.powersetCard j, ‖∏ x ∈ u, f x‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ S.powersetCard j, C ^ j := by
        refine Finset.sum_le_sum fun u hu => ?_
        obtain ⟨hu1, hu2⟩ := Finset.mem_powersetCard.1 hu
        rw [norm_prod, ← hu2, ← Finset.prod_const]
        exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun x hx => hC x (hu1 hx)
    _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

theorem fibreEsymm_locally_bounded (hcount : UnbranchedProperCountConstant.Statement) {σ : Type} [Fintype σ]
    {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ}
    (l : (σ → ℂ) →L[ℂ] ℂ) (j : ℕ) (hD : IsOpen D)
    (hprop : ∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) (hδ : AnalyticOnNhd ℂ δ D)
    (hchart : ∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O)
    {τ : Fin d → ℂ} (hτ : τ ∈ D) :
    ∃ N ∈ 𝓝 τ, Bornology.IsBounded (fibreEsymm Y A l j '' (N ∩ D ∩ {t | δ t ≠ 0})) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hD τ hτ
  set B := Metric.ball τ (ε / 2)
  have hKD : Metric.closedBall τ (ε / 2) ⊆ D := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBD : B ⊆ D := Metric.ball_subset_closedBall.trans hKD

  obtain ⟨n, hn⟩ := hcount σ (Y ∩ A ⁻¹' B) d A B δ Metric.isOpen_ball (convex_ball τ _).isPreconnected
    (fun x hx => hx.2) (fun K hK hKc => by
      convert hprop K (hK.trans hBD) hKc using 1
      ext x; exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hK h.2⟩, h.2⟩⟩) (hδ.mono hBD) (by
      intro x hx hδx
      obtain ⟨O, V, g, hO, hV, hxV, hg, hsec, hYV⟩ := hchart x hx.1 hδx
      refine ⟨O ∩ B, V, g, hO.inter Metric.isOpen_ball, hV, hxV, hg.continuousOn.mono inter_subset_left,
        fun y hy => hsec y hy.1, ?_⟩
      ext z
      constructor
      · rintro ⟨⟨hzY, hzB⟩, hzV⟩
        obtain ⟨w, hw, rfl⟩ : z ∈ g '' O := hYV ▸ ⟨hzY, hzV⟩
        refine ⟨w, ⟨hw, ?_⟩, rfl⟩
        have : A (g w) ∈ B := hzB
        rwa [hsec w hw] at this
      · rintro ⟨w, ⟨hw, hwB⟩, rfl⟩
        have hm : g w ∈ Y ∩ V := hYV ▸ mem_image_of_mem g hw
        refine ⟨⟨hm.1, ?_⟩, hm.2⟩
        show A (g w) ∈ B
        rwa [hsec w hw])

  obtain ⟨C, hC⟩ := (hprop _ hKD (isCompact_closedBall τ _)).exists_bound_of_continuousOn
    l.continuous.continuousOn
  refine ⟨B, Metric.ball_mem_nhds τ (half_pos hε), (Metric.isBounded_iff_subset_closedBall 0).2
    ⟨(n.choose j : ℝ) * C ^ j, ?_⟩⟩
  rintro _ ⟨t, ⟨⟨htB, -⟩, htδ⟩, rfl⟩
  have hfib : {x | x ∈ Y ∩ A ⁻¹' B ∧ A x = t} = {x | x ∈ Y ∧ A x = t} := by
    ext x; exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, show A x ∈ B from h.2 ▸ htB⟩, h.2⟩⟩
  have hcard := hn t htB htδ
  rw [hfib] at hcard
  have hfin : {x | x ∈ Y ∧ A x = t}.Finite := Set.finite_of_encard_eq_coe hcard
  rw [hfin.encard_eq_coe_toFinset_card, Nat.cast_inj] at hcard
  rw [Metric.mem_closedBall, dist_zero_right, fibreEsymm_eq hfin.toFinset hfin.coe_toFinset, ← hcard]
  refine norm_esymm_map_le _ _ _ fun x hx => hC x ?_
  rw [Set.Finite.mem_toFinset] at hx
  exact ⟨hx.1, hx.2 ▸ Metric.ball_subset_closedBall htB⟩

theorem analyticOnNhd_of_differentiableOn (hcirc : ParametricCircleIntegralAnalytic.Statement) {k : ℕ}
    {U : Set (Fin k → ℂ)} {F : (Fin k → ℂ) → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ F U := by
  have h := hcirc (Fin k) (fun p => F p.1 * p.2⁻¹) (U ×ˢ {s | s ≠ 0}) U 0 1 zero_le_one
    (hU.prod isOpen_ne) hU
    ((hF.fun_comp differentiable_fst.differentiableOn mapsTo_fst_prod).mul
      (differentiable_snd.differentiableOn.inv fun _ hp => (mem_prod.1 hp).2))
    (fun x hx s hs => ⟨hx, by rintro rfl; simp at hs⟩)
  have hinv : (∮ z in C(0, 1), z⁻¹) = 2 * π * I := by
    simpa using circleIntegral.integral_sub_inv_of_mem_ball (c := 0) (w := 0) (R := 1) (by simp)
  intro x hx
  refine ((h x hx).mul (analyticAt_const (v := (2 * π * I)⁻¹))).congr (Eventually.of_forall fun y => ?_)
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  simp only [Pi.mul_apply, circleIntegral.integral_const_mul, hinv]
  field_simp

end ProperSheetedFibreEsymm


open ProperSheetedFibreEsymm in
theorem ProperSheetedFibreEsymm.proof (hcount : UnbranchedProperCountConstant.Statement)
    (hriem : RiemannExtensionAnalytic.Statement) (hcirc : ParametricCircleIntegralAnalytic.Statement) :
    ProperSheetedFibreEsymm.Statement := by
  intro σ _ Y d A D δ l j hD _ hprop hδ hW hchart
  obtain ⟨F, hFd, hFeq⟩ := hriem d D δ (fibreEsymm Y A l j) hD hδ.differentiableOn hW
    (fun t ht => (fibreEsymm_analyticAt l j hD hprop hchart ht.1 ht.2).differentiableAt.differentiableWithinAt)
    (fun τ hτ => fibreEsymm_locally_bounded hcount l j hD hprop hδ hchart hτ)
  refine ⟨F, analyticOnNhd_of_differentiableOn hcirc hD hFd, fun t ht hδt s hs => ?_⟩
  rw [hFeq ⟨ht, hδt⟩, fibreEsymm_eq s hs]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularSequenceLengthLeDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence Pointwise

universe u

theorem RegularSequenceLengthLeDim.proof : RegularSequenceLengthLeDim.Statement.{u} := by
  suffices key : ∀ (n : ℕ) (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (rs : List R),
      rs.length = n → (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs →
        (rs.length : WithBot ℕ∞) ≤ ringKrullDim R from
    fun R _ _ _ rs hmem hreg => key _ R rs rfl hmem hreg
  intro n
  induction n with
  | zero =>
    intro R _ _ _ rs hlen _ _
    rw [hlen, Nat.cast_zero]
    exact ringKrullDim_nonneg_of_nontrivial
  | succ n ih =>
    intro R _ _ _ rs hlen hmem hreg
    obtain _ | ⟨r, rs⟩ := rs
    · simp at hlen
    rw [List.length_cons, Nat.succ_inj] at hlen
    rw [isWeaklyRegular_cons_iff] at hreg
    obtain ⟨hr, htail⟩ := hreg
    have hrm : r ∈ maximalIdeal R := hmem r (List.mem_cons_self ..)
    set S := R ⧸ Ideal.span {r}
    have hne : Ideal.span {r} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact (mem_maximalIdeal _).mp hrm
    have : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing S := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {r})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hdim : ringKrullDim S + 1 = ringKrullDim R :=
      ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hr hrm
    have heq : (r • ⊤ : Submodule R R) = Ideal.span {r} := by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
    have hS : IsWeaklyRegular S rs :=
      (Submodule.quotEquivOfEq _ _ heq).isWeaklyRegular_congr rs |>.mp htail
    have hS' : IsWeaklyRegular S (rs.map (algebraMap R S)) :=
      (isWeaklyRegular_map_algebraMap_iff S S rs).mpr hS
    have hmem' : ∀ s ∈ rs.map (algebraMap R S), s ∈ maximalIdeal S := by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      refine (mem_maximalIdeal _).mpr fun hu => (mem_maximalIdeal _).mp (hmem t (List.mem_cons_of_mem _ ht)) ?_
      exact isUnit_of_map_unit (Ideal.Quotient.mk (Ideal.span {r})) t hu
    have h := ih S _ (by rw [List.length_map, hlen]) hmem' hS'
    rw [List.length_map] at h
    rw [← hdim, List.length_cons, Nat.cast_succ]
    exact add_le_add h le_rfl

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSimpleRootBranch
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

theorem eval_map_eval_eq_sum {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (w : Fin d → ℂ) (s : ℂ) :
    (p.map (MvPolynomial.eval w)).eval s =
      ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval w (p.coeff i) * s ^ i := by
  rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (Polynomial.natDegree_map_le) (Nat.lt_succ_self _))]
  simp [Polynomial.coeff_map]

theorem analyticAt_eval_map {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (v : (Fin d → ℂ) × ℂ) :
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval v.1)).eval v.2) v := by
  have h : (fun v : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval v.1)).eval v.2) =
      fun v => ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval v.1 (p.coeff i) * v.2 ^ i := by
    funext v; exact eval_map_eval_eq_sum p v.1 v.2
  rw [h]
  refine Finset.analyticAt_fun_sum (𝕜 := ℂ) _ fun i _ => ?_
  refine AnalyticAt.mul ?_ (analyticAt_snd.pow i)
  exact (AnalyticOnNhd.eval_mvPolynomial (p.coeff i) v.1 trivial).comp analyticAt_fst

theorem SimpleRootBranch.proof : SimpleRootBranch.Statement := by
  intro d p y τ hroot hder
  set F : (Fin d → ℂ) × ℂ → ℂ := fun v => (p.map (MvPolynomial.eval v.1)).eval v.2 with hFdef
  have hcd : ContDiffAt ℂ 1 F (y, τ) := (analyticAt_eval_map p (y, τ)).contDiffAt

  have hpart : fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      (1 : ℂ →L[ℂ] ℂ).smulRight ((p.map (MvPolynomial.eval y)).derivative.eval τ) := by
    have h1 : HasFDerivAt (fun s : ℂ => F (y, s))
        (fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) τ :=
      ((analyticAt_eval_map p (y, τ)).differentiableAt.hasFDerivAt).comp τ
        ((hasFDerivAt_const y τ).prodMk (hasFDerivAt_id τ))
    exact h1.unique ((p.map (MvPolynomial.eval y)).hasDerivAt τ).hasFDerivAt
  have hinv : (fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hpart]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hder), ?_⟩
    ext; simp
  set ψ := hcd.implicitFunction one_ne_zero hinv with hψdef
  have hψy : ψ y = τ := hcd.implicitFunction_apply_self one_ne_zero hinv
  have hFu : F (y, τ) = 0 := hroot
  obtain ⟨U₀, hU₀, B₀, hB₀, hsub⟩ :=
    mem_nhds_prod_iff.mp (hcd.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv)
  obtain ⟨B, hBsub, hBo, hτB⟩ := mem_nhds_iff.mp hB₀
  have hψcd : ContDiffAt ℂ 1 ψ y := hcd.contDiffAt_implicitFunction one_ne_zero hinv
  have hψB : ∀ᶠ w in 𝓝 y, ψ w ∈ B :=
    hψcd.continuousAt.preimage_mem_nhds (by rw [hψy]; exact hBo.mem_nhds hτB)
  obtain ⟨U, hUsub, hUo, hyU⟩ := eventually_nhds_iff.mp
    (((show ∀ᶠ w in 𝓝 y, w ∈ U₀ from hU₀).and (hψcd.eventually (by simp))).and hψB)
  refine ⟨U, B, ψ, hUo, hyU, hBo, hτB, fun w hw => ?_, hψy, fun w hw => ⟨(hUsub w hw).2, ?_⟩⟩
  · exact ((hUsub w hw).1.2.differentiableAt one_ne_zero).differentiableWithinAt
  · intro s hs
    have h := hsub (Set.mk_mem_prod (hUsub w hw).1.1 (hBsub hs))
    simp only [Set.mem_ofPred_eq, hFu] at h
    rw [Polynomial.IsRoot.def]
    exact h.trans eq_comm

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepWeightMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology

noncomputable section

theorem measurable_poincareDeepWeight' : Measurable poincareDeepWeight := by
  have hn : Measurable fun z : ℂ => ‖z‖ ^ 2 := (continuous_norm.pow 2).measurable
  exact Measurable.ite (measurableSet_lt hn.log measurable_const) (hn.mul (hn.log.pow_const 2)).inv
    measurable_const

theorem integrableOn_inv_log_sq_mul :
    IntegrableOn (fun r : ℝ => ((Real.log r) ^ 2 * r)⁻¹) (Set.Ioc 0 (Real.exp (-(Real.exp 1 / 2)))) := by
  have hρ1 : Real.exp (-(Real.exp 1 / 2)) < 1 :=
    Real.exp_lt_one_iff.2 (by have := Real.exp_pos 1; linarith)
  have hcont0 : ContinuousAt (fun r : ℝ => -(Real.log r)⁻¹) 0 := by
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
    simpa using (Real.tendsto_log_nhdsNE_zero.inv_tendsto_atBot).neg
  refine intervalIntegral.integrableOn_deriv_of_nonneg (g := fun r : ℝ => -(Real.log r)⁻¹) ?_ ?_ ?_
  · intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h
      exact hcont0.continuousWithinAt
    · have hl : Real.log x ≠ 0 := (Real.log_neg h (hx.2.trans_lt hρ1)).ne
      exact ((Real.continuousAt_log h.ne').inv₀ hl).neg.continuousWithinAt
  · intro x hx
    have hl : Real.log x ≠ 0 := (Real.log_neg hx.1 (hx.2.trans hρ1)).ne
    have hx0 : x ≠ 0 := hx.1.ne'
    have : HasDerivAt (fun r : ℝ => -(Real.log r)⁻¹) (-(-x⁻¹ / Real.log x ^ 2)) x :=
      ((Real.hasDerivAt_log hx0).inv hl).neg
    refine this.congr_deriv ?_
    rw [neg_div, neg_neg]
    ring
  · intro x hx
    exact inv_nonneg.2 (mul_nonneg (sq_nonneg _) hx.1.le)

theorem ofReal_mul_poincareDeepWeight_le (r : ℝ) :
    ENNReal.ofReal r * ENNReal.ofReal (if Real.log (|r| ^ 2) < -Real.exp 1 then
        (|r| ^ 2 * Real.log (|r| ^ 2) ^ 2)⁻¹ else 0) ≤
      (Set.Ioc 0 (Real.exp (-(Real.exp 1 / 2)))).indicator
        (fun r : ℝ => ENNReal.ofReal (((Real.log r) ^ 2 * r)⁻¹ / 4)) r := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ENNReal.ofReal_of_nonpos hr]
  · rw [abs_of_pos hr]
    split_ifs with hc
    · have hl : Real.log (r ^ 2) = 2 * Real.log r := by rw [Real.log_pow]; norm_num
      rw [hl] at hc
      have hlr : Real.log r < -(Real.exp 1 / 2) := by linarith
      have hl0 : Real.log r ≠ 0 := (hlr.trans (by have := Real.exp_pos 1; linarith)).ne
      rw [Set.indicator_of_mem (show r ∈ Set.Ioc 0 (Real.exp (-(Real.exp 1 / 2))) from ⟨hr, ((Real.log_lt_iff_lt_exp hr).1 hlr).le⟩), ← ENNReal.ofReal_mul hr.le, hl]
      refine le_of_eq (congrArg ENNReal.ofReal ?_)
      field_simp
      ring
    · simp

theorem lintegral_poincareDeepWeight_lt_top :
    ∫⁻ z : ℂ, ENNReal.ofReal (poincareDeepWeight z) < ⊤ := by
  set ρ := Real.exp (-(Real.exp 1 / 2))
  set h : ℝ → ENNReal := (Set.Ioc 0 ρ).indicator
    (fun r : ℝ => ENNReal.ofReal (((Real.log r) ^ 2 * r)⁻¹ / 4)) with hh
  have hm : Measurable h := by
    refine Measurable.indicator ?_ measurableSet_Ioc
    exact ENNReal.measurable_ofReal.comp
      (((Real.measurable_log.pow_const 2).mul measurable_id).inv.div_const 4)
  rw [← Complex.lintegral_comp_polarCoord_symm]
  calc ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • ENNReal.ofReal (poincareDeepWeight (Complex.polarCoord.symm p))
      ≤ ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, h p.1 * (fun _ : ℝ => (1 : ENNReal)) p.2 := by
        rw [polarCoord_target]
        refine lintegral_mono fun p => ?_
        simp only [poincareDeepWeight, Complex.norm_polarCoord_symm, smul_eq_mul, mul_one, hh]
        exact ofReal_mul_poincareDeepWeight_le p.1
    _ = (∫⁻ r in Set.Ioi 0, h r) * ∫⁻ _ in Set.Ioo (-Real.pi) Real.pi, 1 := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact lintegral_prod_mul hm.aemeasurable aemeasurable_const
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ?_ ?_
        · refine (setLIntegral_le_lintegral _ _).trans_lt ?_
          rw [hh, lintegral_indicator measurableSet_Ioc]
          exact ((integrableOn_inv_log_sq_mul).div_const 4).lintegral_lt_top
        · rw [setLIntegral_one, Real.volume_Ioo]
          exact ENNReal.ofReal_lt_top

theorem TubeDeepWeightMass.proof : TubeDeepWeightMass.Statement := by
  intro d R
  set T : Set (Fin d → ℂ) := {w | ∀ i, ‖w i‖ ≤ R} with hTdef
  have hT : volume T < ⊤ := by
    have hsub : T ⊆ Metric.closedBall (0 : Fin d → ℂ) |R| := by
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg (abs_nonneg R)).2 fun i => (hw i).trans (le_abs_self R)
    exact (measure_mono hsub).trans_lt measure_closedBall_lt_top
  have e := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0
  have hpre : {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R} =
      MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0 ⁻¹' (Set.univ ×ˢ T) := by
    ext z
    simp [hTdef, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.tail]
  have key := e.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _)
    (fun p : ℂ × (Fin d → ℂ) => ENNReal.ofReal (poincareDeepWeight p.1) * (fun _ => (1 : ENNReal)) p.2)
    (Set.univ ×ˢ T)
  rw [hpre]
  simp only [mul_one] at key
  have h0 : ∀ z : Fin (d + 1) → ℂ, (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0 z).1 = z 0 := fun z => rfl
  simp only [h0] at key
  rw [key, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have := lintegral_prod_mul (μ := (volume : Measure ℂ).restrict Set.univ)
    (ν := (volume : Measure (Fin d → ℂ)).restrict T)
    (ENNReal.measurable_ofReal.comp measurable_poincareDeepWeight').aemeasurable
    (aemeasurable_const (b := (1 : ENNReal)))
  simp only [mul_one, Function.comp_apply] at this
  rw [this, Measure.restrict_univ, setLIntegral_one]
  exact ENNReal.mul_lt_top lintegral_poincareDeepWeight_lt_top hT

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteFibreCentredEquation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def FiniteFibreCentredEquation.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
      ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        (∀ T : ℂ, T ^ n + ∑ j, b j (A w) * T ^ (j : ℕ) = (T - g w) ^ n) ∧
        ∀ᶠ z in 𝓝 w, z ∈ X → g z ^ n + ∑ j, b j (A z) * g z ^ (j : ℕ) = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

