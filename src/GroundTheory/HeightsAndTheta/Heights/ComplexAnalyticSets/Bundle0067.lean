module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetPieceProductAnalytic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

noncomputable section

namespace SheetPieceProductAnalytic

def tailL (d : ℕ) : (Fin (d + 1) → ℂ) →L[ℂ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

theorem tailL_apply {d : ℕ} (p : Fin (d + 1) → ℂ) (i : Fin d) : tailL d p i = p i.succ := rfl

theorem tailL_cons {d : ℕ} (a : ℂ) (y : Fin d → ℂ) : tailL d (Fin.cons a y) = y := by
  ext i
  simp [tailL_apply]

theorem cons_tailL {d : ℕ} (p : Fin (d + 1) → ℂ) : (Fin.cons (p 0) (tailL d p) : Fin (d + 1) → ℂ) = p := by
  ext i
  cases i using Fin.cases <;> simp [tailL_apply]

def prodFn {σ : Type} [Fintype σ] (X B U : Set (σ → ℂ)) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (ℓ : (σ → ℂ) →L[ℂ] ℂ) (p : Fin (d + 1) → ℂ) : ℂ :=
  ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p}, (p 0 - ℓ x)

theorem exists_ne_zero_of_open {d : ℕ} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ}
    (hδ : AnalyticOnNhd ℂ δ D) (hD : IsPreconnected D) (hne : ∃ y ∈ D, δ y ≠ 0)
    (V : Set (Fin (d + 1) → ℂ)) (hV : IsOpen V) (hVW : V ⊆ tailL d ⁻¹' D) (hVne : V.Nonempty) :
    ∃ p ∈ V, δ (tailL d p) ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨p, hp⟩ := hVne
  have hc : Continuous fun y : Fin d → ℂ => (Fin.cons (p 0) y : Fin (d + 1) → ℂ) := by
    refine continuous_pi fun i => ?_
    cases i using Fin.cases
    · simpa using continuous_const
    · simpa using continuous_apply _
  have hev : δ =ᶠ[𝓝 (tailL d p)] 0 := by
    have hmem : (fun y : Fin d → ℂ => (Fin.cons (p 0) y : Fin (d + 1) → ℂ)) ⁻¹' V ∈ 𝓝 (tailL d p) := by
      refine hc.continuousAt.preimage_mem_nhds ?_
      show V ∈ 𝓝 (Fin.cons (p 0) (tailL d p) : Fin (d + 1) → ℂ)
      rw [cons_tailL]
      exact hV.mem_nhds hp
    filter_upwards [hmem] with y hy
    have := h _ hy
    rwa [tailL_cons] at this
  obtain ⟨y, hy, hy0⟩ := hne
  exact hy0 (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hD (hVW hp) hev hy)

theorem differentiableAt_prodFn (hsec : UnbranchedFibreSections.Statement)
    {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {B : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} {N : ℕ}
    {U V : Set (σ → ℂ)} (ℓ : (σ → ℂ) →L[ℂ] ℂ)
    (hP : IsLocalParametrisation X w B A D δ N) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ U ∪ V)
    (hdisj : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) = ∅)
    {p₀ : Fin (d + 1) → ℂ} (hp₀ : tailL d p₀ ∈ D) (hδp₀ : δ (tailL d p₀) ≠ 0) :
    DifferentiableAt ℂ (prodFn X B U A ℓ) p₀ := by
  classical
  obtain ⟨r, g, hr, -, hrδ, hg, hfib⟩ := hsec σ X w B d A D δ N hP _ hp₀ hδp₀
  set y₀ := tailL d p₀ with hy₀def
  have hy₀ : y₀ ∈ ball y₀ r := mem_ball_self hr
  have hconst : ∀ i, ∀ y ∈ ball y₀ r, (g i y ∈ U ↔ g i y₀ ∈ U) := by
    intro i
    have hgc : ContinuousOn (g i) (ball y₀ r) := (hg i).continuousOn
    have hS : ∀ y ∈ ball y₀ r, g i y ∈ X ∩ B ∧ δ (A (g i y)) ≠ 0 := by
      intro y hy
      have hx : g i y ∈ {x | x ∈ X ∩ B ∧ A x = y} := by
        rw [(hfib y hy).2]
        exact ⟨i, rfl⟩
      exact ⟨hx.1, by rw [hx.2]; exact hrδ y hy⟩
    have hopU := hgc.isOpen_inter_preimage isOpen_ball hU
    have hopV := hgc.isOpen_inter_preimage isOpen_ball hV
    have hdj : Disjoint (ball y₀ r ∩ g i ⁻¹' U) (ball y₀ r ∩ g i ⁻¹' V) := by
      rw [Set.disjoint_left]
      rintro y ⟨hy, hyU⟩ ⟨-, hyV⟩
      have : g i y ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) := ⟨hS y hy, hyU, hyV⟩
      rw [hdisj] at this
      exact this
    have hcv : ball y₀ r ⊆ (ball y₀ r ∩ g i ⁻¹' U) ∪ (ball y₀ r ∩ g i ⁻¹' V) := by
      intro y hy
      rcases hcov (hS y hy) with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    have hc : IsPreconnected (ball y₀ r) := (convex_ball y₀ r).isPreconnected
    intro y hy
    constructor
    · intro hyU
      by_contra hy0U
      have hy0V : y₀ ∈ ball y₀ r ∩ g i ⁻¹' V := (hcv hy₀).resolve_left fun h => hy0U h.2
      have hsub := hc.subset_right_of_subset_union hopU hopV hdj hcv ⟨y₀, hy₀, hy0V⟩
      exact Set.disjoint_left.1 hdj ⟨hy, hyU⟩ (hsub hy)
    · intro hy0U
      exact (hc.subset_left_of_subset_union hopU hopV hdj hcv ⟨y₀, hy₀, hy₀, hy0U⟩ hy).2
  set I : Finset (Fin N) := Finset.univ.filter fun i => g i y₀ ∈ U with hIdef
  have hrep : ∀ p : Fin (d + 1) → ℂ, tailL d p ∈ ball y₀ r →
      prodFn X B U A ℓ p = ∏ i ∈ I, (p 0 - ℓ (g i (tailL d p))) := by
    intro p hp
    have hset : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p} =
        (fun i => g i (tailL d p)) '' (I : Set (Fin N)) := by
      ext x
      constructor
      · rintro ⟨hxB, hxU, hxA⟩
        have hx : x ∈ Set.range (fun i => g i (tailL d p)) := by
          rw [← (hfib _ hp).2]
          exact ⟨hxB, hxA⟩
        obtain ⟨i, rfl⟩ := hx
        exact ⟨i, by simpa [hIdef] using (hconst i _ hp).1 hxU, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        have hx : g i (tailL d p) ∈ {x | x ∈ X ∩ B ∧ A x = tailL d p} := by
          rw [(hfib _ hp).2]
          exact ⟨i, rfl⟩
        exact ⟨hx.1, (hconst i _ hp).2 (by simpa [hIdef] using hi), hx.2⟩
    unfold prodFn
    rw [hset, finprod_mem_image ((hfib _ hp).1.injOn), finprod_mem_coe_finset]
  have hev : prodFn X B U A ℓ =ᶠ[𝓝 p₀] fun p => ∏ i ∈ I, (p 0 - ℓ (g i (tailL d p))) := by
    have hmem : tailL d ⁻¹' ball y₀ r ∈ 𝓝 p₀ :=
      (tailL d).continuous.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hy₀)
    filter_upwards [hmem] with p hp using hrep p hp
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have hfac : ∀ i, DifferentiableAt ℂ (fun p : Fin (d + 1) → ℂ => p 0 - ℓ (g i (tailL d p))) p₀ := by
    intro i
    have h1 : DifferentiableAt ℂ (fun p : Fin (d + 1) → ℂ => p 0) p₀ := differentiableAt_apply 0 p₀
    have h2 : DifferentiableAt ℂ (fun p => ℓ (g i (tailL d p))) p₀ :=
      ℓ.differentiableAt.comp _ (((hg i) _ hy₀).differentiableAt.comp _ (tailL d).differentiableAt)
    exact h1.sub h2
  refine Finset.induction_on I ?_ ?_
  · simp
  · intro j s hj ih
    simp only [Finset.prod_insert hj]
    exact (hfac j).mul ih

theorem isBounded_prodFn {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {B : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} {N : ℕ}
    (U : Set (σ → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ)
    (hP : IsLocalParametrisation X w B A D δ N) {p₀ : Fin (d + 1) → ℂ} (hp₀ : tailL d p₀ ∈ D) :
    ∃ Nb ∈ 𝓝 p₀, Bornology.IsBounded
      (prodFn X B U A ℓ '' (Nb ∩ tailL d ⁻¹' D ∩ {p | δ (tailL d p) ≠ 0})) := by
  obtain ⟨-, -, hD, -, -, hprop, -, -, -, hcard, -, -⟩ := hP
  obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.1 hD _ hp₀
  set y₀ := tailL d p₀ with hy₀def
  have hK : IsCompact {x | x ∈ X ∩ B ∧ A x ∈ closedBall y₀ (ρ / 2)} :=
    hprop _ ((closedBall_subset_ball (half_lt_self hρ)).trans hρD) (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (hK.image ℓ.continuous).isBounded
  set C : ℝ := max 1 (‖p₀ 0‖ + 1 + M) with hCdef
  refine ⟨tailL d ⁻¹' ball y₀ (ρ / 2) ∩ {p | ‖p 0‖ < ‖p₀ 0‖ + 1}, ?_, ?_⟩
  · refine Filter.inter_mem ((tailL d).continuous.continuousAt.preimage_mem_nhds
      (isOpen_ball.mem_nhds (mem_ball_self (half_pos hρ)))) ?_
    exact (isOpen_lt (continuous_norm.comp (continuous_apply 0)) continuous_const).mem_nhds (by simp)
  rw [isBounded_iff_forall_norm_le]
  refine ⟨C ^ N, ?_⟩
  rintro _ ⟨p, ⟨⟨⟨hpb, hpn⟩, hpD⟩, hpδ⟩, rfl⟩
  have hpn' : ‖p 0‖ < ‖p₀ 0‖ + 1 := hpn
  have hsub : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p} ⊆ {x | x ∈ X ∩ B ∧ A x = tailL d p} :=
    fun x hx => ⟨hx.1, hx.2.2⟩
  have hfin : {x | x ∈ X ∩ B ∧ A x = tailL d p}.encard = N := hcard _ hpD hpδ
  have hsfin : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p}.Finite :=
    (Set.finite_of_encard_eq_coe hfin).subset hsub
  have hcardle : hsfin.toFinset.card ≤ N := by
    have h1 := Set.encard_le_encard hsub
    rw [hfin, ← hsfin.coe_toFinset, Set.encard_coe_eq_coe_finsetCard] at h1
    exact_mod_cast h1
  have hbd : ∀ x ∈ hsfin.toFinset, ‖p 0 - ℓ x‖ ≤ C := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    have hxK : x ∈ {x | x ∈ X ∩ B ∧ A x ∈ closedBall y₀ (ρ / 2)} :=
      ⟨hx.1, by rw [hx.2.2]; exact ball_subset_closedBall hpb⟩
    have hMx := hM _ ⟨x, hxK, rfl⟩
    calc ‖p 0 - ℓ x‖ ≤ ‖p 0‖ + ‖ℓ x‖ := norm_sub_le _ _
      _ ≤ ‖p₀ 0‖ + 1 + M := by linarith
      _ ≤ C := le_max_right _ _
  unfold prodFn
  rw [finprod_mem_eq_finite_toFinset_prod _ hsfin]
  calc ‖∏ x ∈ hsfin.toFinset, (p 0 - ℓ x)‖ ≤ ∏ x ∈ hsfin.toFinset, ‖p 0 - ℓ x‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ _x ∈ hsfin.toFinset, C := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hbd
    _ = C ^ hsfin.toFinset.card := Finset.prod_const C
    _ ≤ C ^ N := pow_le_pow_right₀ (le_max_left _ _) hcardle

end SheetPieceProductAnalytic


open SheetPieceProductAnalytic in
theorem SheetPieceProductAnalytic.proof (hsec : UnbranchedFibreSections.Statement) :
    SheetPieceProductAnalytic.Statement := by
  intro σ _ X w B d A D δ N U V ℓ hP hU hV hcov hdisj
  have hP' := hP
  obtain ⟨-, -, hD, hDc, -, -, -, hδ, hne, -, -, -⟩ := hP'
  have hW : IsOpen (tailL d ⁻¹' D) := hD.preimage (tailL d).continuous
  have hgd : DifferentiableOn ℂ (fun p => δ (tailL d p)) (tailL d ⁻¹' D) := fun p hp =>
    ((hδ _ hp).differentiableAt.comp p (tailL d).differentiableAt).differentiableWithinAt
  obtain ⟨F, hF, hFG⟩ := RiemannExtensionAnalytic.proof (d + 1) (tailL d ⁻¹' D) (fun p => δ (tailL d p))
    (prodFn X B U A ℓ) hW hgd (fun V' hV' hsub hne' => exists_ne_zero_of_open hδ hDc hne V' hV' hsub hne')
    (fun p hp => (differentiableAt_prodFn hsec ℓ hP hU hV hcov hdisj hp.1 hp.2).differentiableWithinAt)
    (fun p hp => isBounded_prodFn U ℓ hP hp)
  have hFa : AnalyticOnNhd ℂ F (tailL d ⁻¹' D) := RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hW hF
  have hcons : ∀ z, tailL d (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) = A z := fun z => tailL_cons _ _
  refine ⟨fun z => F (Fin.cons (ℓ z) (A z)), fun z hz => ?_, fun z hz hδz => ?_⟩
  · have hm : (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) ∈ tailL d ⁻¹' D := by
      rw [Set.mem_preimage, hcons]
      exact hz
    have hlin : AnalyticAt ℂ (fun z => (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ)) z := by
      rw [analyticAt_pi_iff]
      intro i
      cases i using Fin.cases
      · simpa using ℓ.analyticAt z
      · rename_i j
        simp only [Fin.cons_succ]
        exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) j).comp A).analyticAt z
    exact AnalyticAt.comp (g := F) (f := fun z => (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ)) (hFa _ hm) hlin
  · have hm : (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) ∈
        tailL d ⁻¹' D ∩ {p | δ (tailL d p) ≠ 0} := by
      refine ⟨?_, ?_⟩
      · rw [Set.mem_preimage, hcons]
        exact hz
      · show δ (tailL d _) ≠ 0
        rw [hcons]
        exact hδz
    show F _ = _
    rw [hFG hm]
    simp only [prodFn, hcons, Fin.cons_zero]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceImmersiveGeneral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology MeasureTheory

noncomputable section

theorem dim_component_linForm {n d : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)} {u : Fin n → ℂ}
    (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ))
    (hu : linForm u ∉ J) (hW : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) := by
  have := hJ
  have hIW : J ≤ W := le_sup_left.trans hW.1.2
  have huW : linForm u ∈ W := (le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self _)
  have hWprime : W.IsPrime := hW.1.1
  set B := MvPolynomial (Fin n) ℂ ⧸ J
  have _ : Algebra.FiniteType ℂ B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ J) (Ideal.Quotient.mkₐ_surjective ℂ J)
  set W' : Ideal B := W.map (Ideal.Quotient.mk J)
  have hW'prime : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hu
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk J (linForm u) ∈ W' := Ideal.mem_map_of_mem _ huW
    rw [h, Ideal.mem_bot] at this
    exact this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient ℂ (A := B) W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot] at hform hdrop
  change ringKrullDim B = _ at hdim
  rw [hdim] at hform hdrop
  obtain ⟨y, hy⟩ : ∃ y : ℕ∞, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = y := by
    cases h : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) with
    | bot =>
      have := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ W)
      rw [h] at this
      exact absurd this (by simp)
    | coe y => exact ⟨y, rfl⟩
  rw [hy] at hform hdrop ⊢
  have h1 : y + 1 ≤ ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast hdrop
  have h2 : W'.height + y = ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast hform
  have hyle : y ≤ d := by
    have : y + 1 ≤ (d : ℕ∞) + 1 := by exact_mod_cast h1
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ℕ∞) = y :=
    ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top d) hyle)
  have h3 : ((d + 1 : ℕ) : ℕ∞) ≤ 1 + k := by rw [← h2]; gcongr
  have h4 : d + 1 ≤ 1 + k := by exact_mod_cast h3
  have h5 : k ≤ d := by exact_mod_cast hyle
  have : k = d := by omega
  subst this
  rfl

def hyperplaneEmb (d : ℕ) : (Fin d → ℂ) →L[ℂ] (Fin (d + 1) → ℂ) :=
  ContinuousLinearMap.pi
    (Fin.cons 0 fun j => ContinuousLinearMap.proj j : Fin (d + 1) → (Fin d → ℂ) →L[ℂ] ℂ)

theorem hyperplaneEmb_apply (d : ℕ) (t : Fin d → ℂ) : hyperplaneEmb d t = Fin.cons 0 t := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [hyperplaneEmb]

theorem hyperplaneEmb_tail {d : ℕ} {s : Fin (d + 1) → ℂ} (hs : s 0 = 0) :
    hyperplaneEmb d (Fin.tail s) = s := by
  rw [hyperplaneEmb_apply, ← hs]
  exact Fin.cons_self_tail s

def sliceMap {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (γ : GroundTheory.Heights₂.Heights.VarBranch J (d + 1) p) : (Fin d → ℂ) → Fin n → ℂ :=
  fun t => γ.toFun (hyperplaneEmb d t)

theorem SliceImmersiveGeneral.proof (hcrit : CriticalImageNull.Statement)
    (hmass : ZeroSetOpenMass.Statement) : SliceImmersiveGeneral.Statement := by
  intro n d J W u p m γ hJ hdim hu hW hp hN
  obtain ⟨N, hN, hsl⟩ := hN
  have hWd := dim_component_linForm hJ hdim hu hW

  have hball : ∀ b, ∀ s ∈ Metric.ball (0 : Fin (d + 1) → ℂ) (γ b).radius,
      Fin.tail s ∈ Metric.ball (0 : Fin d → ℂ) (γ b).radius := by
    intro b s hs
    rw [ball_pi _ (γ b).radius_pos] at hs ⊢
    exact fun j _ => hs j.succ (Set.mem_univ _)
  have hmaps : ∀ b, Set.MapsTo (hyperplaneEmb d) (Metric.ball 0 (γ b).radius)
      (Metric.ball 0 (γ b).radius) := by
    intro b t ht
    rw [ball_pi _ (γ b).radius_pos] at ht ⊢
    intro i _
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hyperplaneEmb_apply, (γ b).radius_pos]
    · simpa [hyperplaneEmb_apply] using ht j (Set.mem_univ _)

  have hnull : ∀ b, μH[((2 * d : ℕ) : ℝ)] (sliceMap (γ b) '' {t | t ∈ Metric.ball 0 (γ b).radius ∧
      ¬ Function.Injective (fderiv ℂ (sliceMap (γ b)) t)}) = 0 := fun b =>
    hcrit d n _ _ Metric.isOpen_ball
      ((γ b).differentiableOn.comp (hyperplaneEmb d).differentiableOn (hmaps b))
  refine ⟨interior N, interior_mem_nhds.2 hN, ?_⟩
  rintro x ⟨hxW, hxN⟩
  rw [mem_closure_iff]
  intro o ho hxo
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne

  have hsub : GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ (o ∩ interior N) ⊆
      ⋃ b, sliceMap (γ b) '' {t | t ∈ Metric.ball 0 (γ b).radius ∧
        ¬ Function.Injective (fderiv ℂ (sliceMap (γ b)) t)} := by
    rintro y ⟨hyW, hyo, hyN⟩
    by_contra hy
    simp only [Set.mem_iUnion, not_exists] at hy
    have hyG : y ∈ o ∩ {x | x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∧
        ∀ b, ∃ s ∈ Metric.ball 0 (γ b).radius, s 0 = 0 ∧ (γ b).toFun s = x ∧
          ∀ v : Fin (d + 1) → ℂ, v 0 = 0 → fderiv ℂ (γ b).toFun s v = 0 → v = 0} := by
      refine ⟨hyo, hyW, fun b => ?_⟩
      obtain ⟨s, ⟨hs, hs0⟩, hsy⟩ := hsl b ⟨hyW, interior_subset hyN⟩
      have hs0' : s 0 = 0 := hs0
      refine ⟨s, hs, hs0', hsy, fun v hv0 hv => ?_⟩
      have hst := hyperplaneEmb_tail hs0'
      have hinj : Function.Injective (fderiv ℂ (sliceMap (γ b)) (Fin.tail s)) := by
        by_contra hni
        exact hy b ⟨Fin.tail s, ⟨hball b s hs, hni⟩, by simp only [sliceMap, hst, hsy]⟩
      have hγd : DifferentiableAt ℂ (γ b).toFun (hyperplaneEmb d (Fin.tail s)) := by
        rw [hst]
        exact (γ b).differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds hs)
      have hchain : fderiv ℂ (sliceMap (γ b)) (Fin.tail s) =
          (fderiv ℂ (γ b).toFun (hyperplaneEmb d (Fin.tail s))).comp (hyperplaneEmb d) := by
        have h := fderiv_comp (Fin.tail s) hγd (hyperplaneEmb d).differentiableAt
        rw [ContinuousLinearMap.fderiv] at h
        exact h
      have hvt := hyperplaneEmb_tail hv0
      have : Fin.tail v = 0 := hinj (by
        rw [hchain, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hvt, hst, hv,
          map_zero, map_zero])
      rw [← hvt, this, map_zero]
    rw [hne] at hyG
    exact hyG
  have hpos := hmass n d W hW.1.1 hWd x (o ∩ interior N) (ho.inter isOpen_interior) ⟨hxo, hxN⟩ hxW
  exact hpos.ne' (measure_mono_null hsub (measure_iUnion_null hnull))

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSmallSetBallCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets Metric

noncomputable section

theorem volume_ball_pi_complex {n : ℕ} (c : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    volume (ball c ρ) = ENNReal.ofReal ((Real.pi * ρ ^ 2) ^ n) := by
  rw [ball_pi c hρ, volume_pi_pi]
  simp only [Complex.volume_ball, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hρ.le,
    mul_comm, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]

theorem exists_cover_le_volume_thickening {n : ℕ} {A : Set (Fin n → ℂ)} (hA : IsCompact A) {r : ℝ}
    (hr : 0 < r) : ∃ T : Finset (Fin n → ℂ), (↑T : Set (Fin n → ℂ)) ⊆ A ∧ A ⊆ ⋃ c ∈ T, ball c r ∧
      (T.card : ℝ) * (Real.pi * (r / 4) ^ 2) ^ n ≤ (volume (thickening r A)).toReal := by
  set δ : NNReal := ⟨r / 4, by positivity⟩
  have hδ : (δ : ℝ) = r / 4 := rfl
  have hpack : packingNumber (2 * δ) A ≠ ⊤ := by
    obtain ⟨N, -, hNfin, hN⟩ := exists_finite_isCover_of_isCompact (ε := δ)
      (by rw [ne_eq, ← NNReal.coe_eq_zero, hδ]; positivity) hA
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.2 hNfin)
      ((packingNumber_two_mul_le_externalCoveringNumber δ A).trans hN.externalCoveringNumber_le_encard)
  set S := maximalSeparatedSet (2 * δ) A
  have hSfin : S.Finite := Set.encard_ne_top_iff.1 (by rw [encard_maximalSeparatedSet hpack]; exact hpack)
  refine ⟨hSfin.toFinset, by simpa using maximalSeparatedSet_subset, ?_, ?_⟩
  · refine ((isCover_maximalSeparatedSet hpack).subset_iUnion_closedBall).trans ?_
    refine Set.iUnion₂_subset fun c hc => ?_
    refine (closedBall_subset_ball ?_).trans (Set.subset_biUnion_of_mem (u := fun c => ball c r) ?_)
    · simp only [NNReal.coe_mul, NNReal.coe_ofNat, hδ]; linarith
    · simpa using hc
  · have hsep := isSeparated_maximalSeparatedSet (ε := 2 * δ) (A := A)
    have hdisj : (↑hSfin.toFinset : Set (Fin n → ℂ)).PairwiseDisjoint (fun c => ball c (r / 4)) := by
      intro x hx y hy hxy
      apply ball_disjoint_ball
      have h1 : ((2 * δ : NNReal) : ENNReal) < edist x y := hsep (by simpa using hx) (by simpa using hy) hxy
      rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at h1
      simp only [NNReal.coe_mul, NNReal.coe_ofNat, hδ] at h1
      linarith
    have hsub : (⋃ c ∈ hSfin.toFinset, ball c (r / 4)) ⊆ thickening r A := by
      refine Set.iUnion₂_subset fun c hc => ?_
      exact (ball_subset_thickening (maximalSeparatedSet_subset (by simpa using hc)) _).trans
        (thickening_mono (by linarith) A)
    have hvol := measure_mono (μ := volume) hsub
    rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)] at hvol
    simp only [volume_ball_pi_complex _ (by positivity : (0 : ℝ) < r / 4), Finset.sum_const,
      nsmul_eq_mul] at hvol
    have hfin : volume (thickening r A) ≠ ⊤ := (hA.isBounded.thickening).measure_lt_top.ne
    have := ENNReal.toReal_mono hfin hvol
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at this

theorem SmallSetBallCover.proof (h : SmallSetTubeVolume.Statement) : SmallSetBallCover.Statement := by
  intro n d I K hdim hK
  obtain ⟨C, hC0, hC⟩ := h n d I K hdim hK
  refine ⟨C * (16 / Real.pi) ^ n, by positivity, fun r hr => ?_⟩
  have hr0 := hr.1
  have hZ : IsClosed (zeroSet I) := by
    have : zeroSet I = ⋂ q ∈ I, {x : Fin n → ℂ | eval x q = 0} := by ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  have hA : IsCompact (zeroSet I ∩ K) := hK.inter_left hZ
  obtain ⟨T, hTA, hcov, hcount⟩ := exists_cover_le_volume_thickening hA hr0
  refine ⟨T, hTA, hcov, ?_⟩
  have hV := ENNReal.toReal_le_of_le_ofReal (by positivity) (hC r hr)
  have hz : r ^ ((2 * n + 2 : ℤ) - 2 * d) * r ^ (2 * d) = r ^ (2 * n) * r ^ 2 := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hr0.ne', ← zpow_add₀ hr0.ne']
    congr 1; push_cast; ring
  have hP : 0 < (Real.pi / 16) ^ n * r ^ (2 * n) := by positivity
  have he : (16 / Real.pi) ^ n * (Real.pi / 16) ^ n = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm 16, div_self (by positivity), one_pow]
  have hball : (Real.pi * (r / 4) ^ 2) ^ n = (Real.pi / 16) ^ n * r ^ (2 * n) := by
    rw [pow_mul, ← mul_pow]; ring_nf
  refine le_of_mul_le_mul_right ?_ hP
  calc (T.card : ℝ) * r ^ (2 * d) * ((Real.pi / 16) ^ n * r ^ (2 * n))
      = ((T.card : ℝ) * (Real.pi * (r / 4) ^ 2) ^ n) * r ^ (2 * d) := by rw [hball]; ring
    _ ≤ (C * r ^ ((2 * n + 2 : ℤ) - 2 * d)) * r ^ (2 * d) := mul_le_mul_of_nonneg_right (hcount.trans hV) (by positivity)
    _ = C * (16 / Real.pi) ^ n * r ^ 2 * ((Real.pi / 16) ^ n * r ^ (2 * n)) := by
      rw [mul_assoc, hz]
      linear_combination (-(C * r ^ (2 * n) * r ^ 2)) * he

end

end GroundTheory.Heights₂.Heights
end

