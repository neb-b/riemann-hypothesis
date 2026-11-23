module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0074

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteProjectionPushforward
section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter

namespace GlobalTheory.CompanionTheory.ComplexSets.DiscCover

open Metric

theorem const_coord (y : Fin 1 → ℂ) : (fun _ : Fin 1 => y 0) = y := by
  funext i
  rw [Subsingleton.elim i 0]

theorem line_ext {y y' : Fin 1 → ℂ} (h : y 0 = y' 0) : y = y' := by
  funext i
  rw [Subsingleton.elim i 0]
  exact h

theorem line_dist (y y' : Fin 1 → ℂ) : dist y y' = dist (y 0) (y' 0) := by
  have h : dist (fun _ : Fin 1 => y 0) (fun _ : Fin 1 => y' 0) = dist (y 0) (y' 0) :=
    dist_pi_const (y 0) (y' 0)
  rw [const_coord y, const_coord y'] at h
  exact h

theorem mem_line_ball {y c : Fin 1 → ℂ} {ρ : ℝ} : y ∈ ball c ρ ↔ y 0 ∈ ball (c 0) ρ := by
  simp only [mem_ball, line_dist]

theorem exists_punctured_ball_ne_zero (δ : (Fin 1 → ℂ) → ℂ) (c : Fin 1 → ℂ) (hδ : AnalyticAt ℂ δ c)
    (hne : ¬ ∀ᶠ y in 𝓝 c, δ y = 0) : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ y ∈ ball c ρ₀, y ≠ c → δ y ≠ 0 := by
  set e := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  have hF : AnalyticAt ℂ (fun t : ℂ => δ (fun _ => t)) (c 0) := by
    have h1 : AnalyticAt ℂ δ (e.symm (c 0)) := by
      have h2 : e.symm (c 0) = c := const_coord c
      rw [h2]
      exact hδ
    exact h1.comp (e.symm.analyticAt _)
  rcases hF.eventually_eq_zero_or_eventually_ne_zero with h0 | h1
  · exfalso
    apply hne
    have ht : Tendsto (fun y : Fin 1 → ℂ => y 0) (𝓝 c) (𝓝 (c 0)) := (continuous_apply 0).tendsto c
    filter_upwards [ht h0] with y hy
    have hy' : δ (fun _ => y 0) = 0 := hy
    rwa [const_coord] at hy'
  · obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h1)
    refine ⟨ε, hε, fun y hy hyc => ?_⟩
    have h2 := h (y := y 0) (by simpa [line_dist] using mem_ball.1 hy)
      (fun h3 => hyc (line_ext h3))
    rwa [const_coord] at h2

theorem isCompact_inter_of_cut {σ : Type} [Fintype σ] {Y C Nn : Set (σ → ℂ)} {k : ℕ}
    {f : Fin k → (σ → ℂ) → ℂ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) Nn)
    (hY : Y ∩ Nn = {z | z ∈ Nn ∧ ∀ i, f i z = 0}) (hC : IsCompact C) (hsub : C ⊆ Nn) :
    IsCompact (Y ∩ C) := by
  have hcont : ContinuousOn (fun z i => f i z) C :=
    continuousOn_pi.2 fun i => (hf i).continuousOn.mono hsub
  have hcl := hcont.preimage_isClosed_of_isClosed hC.isClosed (isClosed_singleton (x := (0 : Fin k → ℂ)))
  have heq : Y ∩ C = C ∩ (fun z i => f i z) ⁻¹' {(0 : Fin k → ℂ)} := by
    ext z
    constructor
    · rintro ⟨hzY, hzC⟩
      have h : z ∈ Y ∩ Nn := ⟨hzY, hsub hzC⟩
      rw [hY] at h
      exact ⟨hzC, funext h.2⟩
    · rintro ⟨hzC, hz⟩
      have h : z ∈ {z | z ∈ Nn ∧ ∀ i, f i z = 0} := ⟨hsub hzC, fun i => congrFun hz i⟩
      rw [← hY] at h
      exact ⟨h.1, hzC⟩
  rw [heq]
  exact hC.of_isClosed_subset hcl Set.inter_subset_left

theorem cover_of_radii (hCount : UnbranchedProperCountConstant.Statement) (σ : Type) [Fintype σ]
    (Y : Set (σ → ℂ)) (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)) (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ)
    (hw : w ∈ Y) (hcomp : IsCompact (Y ∩ closedBall w r))
    (hsph : ∀ x ∈ Y, dist x w = r → A x ∉ ball (A w) ρ)
    (hiso : ∀ x ∈ Y ∩ closedBall w r, A x = A w → x = w)
    (hsheet : ∀ x ∈ Y ∩ closedBall w r, A x ≠ A w → A x ∈ ball (A w) ρ →
      ∃ (O : Set (Fin 1 → ℂ)) (V : Set (σ → ℂ)) (g : (Fin 1 → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ x ∈ V ∧
        AnalyticOnNhd ℂ g O ∧ (∀ t ∈ O, A (g t) = t) ∧ Y ∩ V = g '' O)
    (hsurj : A '' (Y ∩ ball w r) ∈ 𝓝 (A w)) :
    ∃ N : ℕ, IsCentredDiscCover (Y ∩ (ball w r ∩ A ⁻¹' ball (A w) ρ)) w
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).comp A) ρ N := by
  set B := ball w r ∩ A ⁻¹' ball (A w) ρ with hBdef
  have hBopen : IsOpen B := isOpen_ball.inter (isOpen_ball.preimage A.continuous)
  have hclosed : ∀ C : Set (Fin 1 → ℂ), IsClosed C → C ⊆ ball (A w) ρ →
      IsCompact {x | x ∈ Y ∩ B ∧ A x ∈ C} := by
    intro C hC hCD
    have heq : {x | x ∈ Y ∩ B ∧ A x ∈ C} = (Y ∩ closedBall w r) ∩ A ⁻¹' C := by
      ext x
      constructor
      · rintro ⟨⟨hxY, hxb, -⟩, hxC⟩
        exact ⟨⟨hxY, ball_subset_closedBall hxb⟩, hxC⟩
      · rintro ⟨⟨hxY, hxb⟩, hxC⟩
        have hD := hCD hxC
        refine ⟨⟨hxY, ?_, hD⟩, hxC⟩
        rcases (mem_closedBall.1 hxb).lt_or_eq with h | h
        · exact mem_ball.2 h
        · exact absurd hD (hsph x hxY h)
    rw [heq]
    exact hcomp.inter_right (hC.preimage A.continuous)
  have hsec : ∀ x ∈ Y ∩ B, A x ≠ A w →
      ∃ (O : Set (Fin 1 → ℂ)) (V : Set (σ → ℂ)) (g : (Fin 1 → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ x ∈ V ∧
        DifferentiableOn ℂ g O ∧ (∀ t ∈ O, A (g t) = t) ∧ (Y ∩ B) ∩ V = g '' O := by
    intro x hx hne
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hYV⟩ :=
      hsheet x ⟨hx.1, ball_subset_closedBall hx.2.1⟩ hne hx.2.2
    have hgc : ContinuousOn g O := hg.continuousOn
    refine ⟨O ∩ g ⁻¹' B, V ∩ B, g, hgc.isOpen_inter_preimage hO hBopen, hV.inter hBopen, ⟨hxV, hx.2⟩,
      hg.differentiableOn.mono Set.inter_subset_left, fun t ht => hAg t ht.1, ?_⟩
    rw [Set.image_inter_preimage, ← hYV]
    ext z
    simp only [Set.mem_inter_iff]
    tauto
  obtain ⟨N, hN⟩ := hCount σ (Y ∩ B) 1 A (ball (A w) ρ) (fun y => y 0 - A w 0) isOpen_ball
    (convex_ball (A w) ρ).isPreconnected (fun x hx => hx.2.2)
    (fun K hK hKc => hclosed K hKc.isClosed hK)
    (fun y _ => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt y).sub
      analyticAt_const)
    (fun x hx hne => by
      obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hYV⟩ := hsec x hx (fun h => hne (by simp [h]))
      exact ⟨O, V, g, hO, hV, hxV, hg.continuousOn, hAg, hYV⟩)
  refine ⟨N, ?_⟩
  unfold IsCentredDiscCover
  refine ⟨⟨hw, mem_ball_self hr, by exact Set.mem_preimage.mpr (mem_ball_self hρ)⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hnh := Filter.inter_mem hsurj (ball_mem_nhds (A w) hρ)
    have hnb : (𝓝[≠] (A w)).NeBot := Module.punctured_nhds_neBot ℂ (Fin 1 → ℂ) (A w)
    obtain ⟨y, ⟨⟨x, hx, hxy⟩, hyD⟩, hyne⟩ :=
      Filter.nonempty_of_mem
        (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds hnh) self_mem_nhdsWithin : _ ∈ 𝓝[≠] (A w))
    have hc := hN y hyD (sub_ne_zero.2 fun h => hyne (line_ext h))
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · exfalso
      subst h0
      have hempty : {z | z ∈ Y ∩ B ∧ A z = y} = ∅ := Set.encard_eq_zero.1 (by simpa using hc)
      have hmem : x ∈ {z | z ∈ Y ∩ B ∧ A z = y} :=
        ⟨⟨hx.1, hx.2, by simpa [Set.mem_preimage, hxy] using hyD⟩, hxy⟩
      rw [hempty] at hmem
      exact hmem
    · exact h0
  · exact fun x hx => mem_line_ball.1 hx.2.2
  · exact fun x hx hpx => hiso x ⟨hx.1, ball_subset_closedBall hx.2.1⟩ (line_ext hpx)
  · intro t ht hne
    have hc : (fun _ : Fin 1 => t) ∈ ball (A w) ρ := mem_line_ball.2 ht
    have h := hN (fun _ => t) hc (sub_ne_zero.2 hne)
    have heq : {x | x ∈ Y ∩ B ∧
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).comp A) x = t} =
        {x | x ∈ Y ∩ B ∧ A x = fun _ => t} := by
      ext x
      constructor
      · rintro ⟨hx, h1⟩
        exact ⟨hx, line_ext h1⟩
      · rintro ⟨hx, h1⟩
        refine ⟨hx, ?_⟩
        show A x 0 = t
        rw [h1]
    rw [heq]
    exact h
  · intro K hK hKc
    exact hclosed ((fun y : Fin 1 → ℂ => y 0) ⁻¹' K) (hKc.isClosed.preimage (continuous_apply 0))
      (fun y hy => mem_line_ball.2 (hK hy))
  · intro x hx hne
    have hne' : A x ≠ A w := fun h => hne (by
      show A x 0 = A w 0
      rw [h])
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hYV⟩ := hsec x hx hne'
    have hcc : Continuous (fun (t : ℂ) (_ : Fin 1) => t) := continuous_pi fun _ => continuous_id
    have hcd : Differentiable ℂ (fun (t : ℂ) (_ : Fin 1) => t) :=
      differentiable_pi.2 fun _ => differentiable_id
    have hcs : Function.Surjective (fun (t : ℂ) (_ : Fin 1) => t) := fun y => ⟨y 0, const_coord y⟩
    refine ⟨(fun (t : ℂ) (_ : Fin 1) => t) ⁻¹' O, V, g ∘ (fun (t : ℂ) (_ : Fin 1) => t),
      hO.preimage hcc, hV, hxV, hg.comp hcd.differentiableOn (fun t ht => ht), fun t ht => ?_, ?_⟩
    · show A (g (fun _ => t)) 0 = t
      rw [hAg _ ht]
    · rw [Set.image_comp, Set.image_preimage_eq O hcs]
      exact hYV

end GlobalTheory.CompanionTheory.ComplexSets.DiscCover

namespace GlobalTheory.CompanionTheory.ComplexSets

open Metric DiscCover

theorem irreducibleGerm_contains_centredDiscCover :
    FiniteGermProjectionOpenAt.Statement → IrreducibleGermPrimitiveForm.Statement →
    PrimitiveFormSheetedOffDiscriminant.Statement → UnbranchedProperCountConstant.Statement →
    ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)),
      IsAnalyticNear Y w → GermIrreducibleAt Y w → (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) →
      (∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
      ∃ (Y' : Set (σ → ℂ)) (p : (σ → ℂ) →L[ℂ] ℂ) (ρ : ℝ) (N : ℕ), Y' ⊆ Y ∧ IsCentredDiscCover Y' w p ρ N := by
  intro hOpen hPrim hSheet hCount σ _ Y w A hAn hIrr hIso hDom
  obtain ⟨ℓ, N0, a, δ, q, ha, hδ, hq, hδne, hp1, hsep, hcoord⟩ := hPrim σ Y w 1 A hAn hIrr hIso hDom
  obtain ⟨M, hM, hMs⟩ := hSheet σ Y w 1 A hAn hIrr hIso hDom ℓ N0 a δ q ha hδ hq hδne hp1 hsep hcoord
  obtain ⟨ρ₀, hρ₀, hδ0⟩ := exists_punctured_ball_ne_zero δ (A w) hδ hδne
  have hAn2 := hAn
  have hIso2 := hIso
  obtain ⟨Nn, k, f, hNo, hwN, hf, hYN⟩ := hAn2
  obtain ⟨W', hW', hiso⟩ := hIso2
  have hU : M ∩ Nn ∩ W' ∈ 𝓝 w := Filter.inter_mem (Filter.inter_mem hM (hNo.mem_nhds hwN)) hW'
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hU
  have hcomp : IsCompact (Y ∩ closedBall w r) :=
    isCompact_inter_of_cut hf hYN (isCompact_closedBall w r) (fun x hx => (hrU hx).1.2)
  have hS : IsCompact ((Y ∩ closedBall w r) ∩ sphere w r) := hcomp.inter_right isClosed_sphere
  have hAS : A w ∉ A '' ((Y ∩ closedBall w r) ∩ sphere w r) := by
    rintro ⟨x, ⟨⟨hxY, hxb⟩, hxs⟩, hx⟩
    have hxw := hiso x ⟨hxY, (hrU hxb).2⟩ hx
    rw [hxw, mem_sphere, dist_self] at hxs
    exact hr.ne hxs
  have hnh : (A '' ((Y ∩ closedBall w r) ∩ sphere w r))ᶜ ∈ 𝓝 (A w) :=
    (hS.image A.continuous).isClosed.isOpen_compl.mem_nhds hAS
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.mem_nhds_iff.1 hnh
  obtain ⟨N, hN⟩ := cover_of_radii hCount σ Y w A r (min ρ₀ ρ₁) hr (lt_min hρ₀ hρ₁) hIrr.1 hcomp
    (fun x hxY hd hb => hball (ball_subset_ball (min_le_right _ _) hb)
      ⟨x, ⟨⟨hxY, mem_closedBall.2 hd.le⟩, mem_sphere.2 hd⟩, rfl⟩)
    (fun x hx hxe => hiso x ⟨hx.1, (hrU hx.2).2⟩ hxe)
    (fun x hx hne hb => hMs x ⟨hx.1, (hrU hx.2).1.1⟩
      (hδ0 (A x) (ball_subset_ball (min_le_left _ _) hb) hne))
    (hOpen σ Y w 1 A hAn hIso hDom (ball w r) (ball_mem_nhds w hr))
  exact ⟨Y ∩ (ball w r ∩ A ⁻¹' ball (A w) (min ρ₀ ρ₁)), _, _, N, fun x hx => hx.1, hN⟩

end GlobalTheory.CompanionTheory.ComplexSets
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutTranslate
section
noncomputable section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 Pointwise

namespace GlobalTheory.CompanionTheory.HeckeMul

section Generic

variable {G : Type} [Group G]

theorem out_mk_of_right_inv {M : Type} (K : Subgroup G) (φ : G → M)
    (hφ : ∀ x, ∀ k ∈ K, φ (x * k) = φ x) (x : G) :
    φ (QuotientGroup.mk x : G ⧸ K).out = φ x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hh]
  exact hφ x h h.2

theorem finsum_out_translate {M : Type} [AddCommMonoid M] (K : Subgroup G) (φ : G → M)
    (hφ : ∀ x, ∀ k ∈ K, φ (x * k) = φ x) (a : G) :
    ∑ᶠ q : G ⧸ K, φ (a * q.out) = ∑ᶠ q : G ⧸ K, φ q.out := by
  rw [← finsum_comp_equiv (MulAction.toPerm a : Equiv.Perm (G ⧸ K)) (f := fun q : G ⧸ K => φ q.out)]
  refine finsum_congr fun q => ?_
  have h : (MulAction.toPerm a : Equiv.Perm (G ⧸ K)) q = (QuotientGroup.mk (a * q.out) : G ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [h, out_mk_of_right_inv K φ hφ]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_out_mem (K : Subgroup G) (hK : IsOpen (K : Set G)) {C : Set G} (hC : IsCompact C) :
    {q : G ⧸ K | q.out ∈ C}.Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' C) :=
    hC.image QuotientGroup.continuous_mk
  refine hc.finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, hq, QuotientGroup.out_eq' q⟩

end Generic

section Hecke

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isHk_right {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (h : IsHk K e) (x : GL ι F)
    {k : GL ι F} (hk' : k ∈ K) : e (x * k) = e x := by
  simpa using h.2.2.2 1 K.one_mem k hk' x

theorem isHk_left {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (h : IsHk K e) (x : GL ι F)
    {k : GL ι F} (hk' : k ∈ K) : e (k * x) = e x := by
  simpa using h.2.2.2 k hk' 1 K.one_mem x

theorem support_hconv (K : Subgroup (GL ι F)) (e₁ e₂ : GL ι F → ℂ) :
    Function.support (hconv K e₁ e₂) ⊆ tsupport e₁ * tsupport e₂ := by
  intro g hg
  obtain ⟨q, hq⟩ : ∃ q : GL ι F ⧸ K, e₁ q.out * e₂ (q.out⁻¹ * g) ≠ 0 := by
    by_contra h
    push_neg at h
    refine (Function.mem_support.1 hg) ?_
    unfold hconv
    simp only [h]
    exact finsum_zero
  exact Set.mem_mul.2 ⟨q.out, subset_tsupport _ (left_ne_zero_of_mul hq), q.out⁻¹ * g,
    subset_tsupport _ (right_ne_zero_of_mul hq), mul_inv_cancel_left _ _⟩

theorem hconv_biinv {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂)
    {k₁ k₂ : GL ι F} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K) (g : GL ι F) :
    hconv K e₁ e₂ (k₁ * g * k₂) = hconv K e₁ e₂ g := by
  have hφ : ∀ x, ∀ k ∈ K, (fun y => e₁ y * e₂ (y⁻¹ * g)) (x * k) = (fun y => e₁ y * e₂ (y⁻¹ * g)) x := by
    intro x k hk'
    show e₁ (x * k) * e₂ ((x * k)⁻¹ * g) = e₁ x * e₂ (x⁻¹ * g)
    rw [isHk_right h₁ x hk', mul_inv_rev, mul_assoc, isHk_left h₂ _ (K.inv_mem hk')]
  have ht := finsum_out_translate K (fun y => e₁ y * e₂ (y⁻¹ * g)) hφ k₁⁻¹
  unfold hconv
  rw [← ht]
  refine finsum_congr fun q => ?_
  show e₁ q.out * e₂ (q.out⁻¹ * (k₁ * g * k₂)) = e₁ (k₁⁻¹ * q.out) * e₂ ((k₁⁻¹ * q.out)⁻¹ * g)
  rw [isHk_left h₁ _ (K.inv_mem hk₁), ← mul_assoc, isHk_right h₂ _ hk₂]
  simp [mul_assoc]

theorem isHk_hconv {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂) :
    IsHk K (hconv K e₁ e₂) := by
  refine ⟨h₁.1, h₁.2.1, ?_, fun k₁ hk₁ k₂ hk₂ g => hconv_biinv h₁ h₂ hk₁ hk₂ g⟩
  have hc : IsCompact (tsupport e₁ * tsupport e₂) := IsCompact.mul h₁.2.2.1 h₂.2.2.1
  exact HasCompactSupport.of_support_subset_isCompact hc (support_hconv K e₁ e₂)

theorem hk_eq_sum {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V)
    (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (w : V) (A : Finset (GL ι F ⧸ K))
    (hA : ∀ q : GL ι F ⧸ K, e q.out ≠ 0 → q ∈ A) :
    hk ρ K e w = ∑ q ∈ A, e q.out • ρ q.out w := by
  unfold hk
  refine finsum_eq_sum_of_support_subset _ ?_
  intro q hq
  refine Finset.mem_coe.2 (hA q fun h0 => (Function.mem_support.1 hq) ?_)
  show e q.out • ρ q.out w = 0
  rw [h0, zero_smul]

theorem hk_hconv {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V) {v : V}
    (hv : v ∈ fixed ρ K) :
    hk ρ K (hconv K e₁ e₂) v = hk ρ K e₁ (hk ρ K e₂ v) := by
  have hvk : ∀ k ∈ K, ρ k v = v := fun k hk' => by
    have := hv ⟨k, hk'⟩
    simpa using this
  have c1 : IsCompact (tsupport e₁) := h₁.2.2.1
  have c2 : IsCompact (tsupport e₂) := h₂.2.2.1
  have c12 : IsCompact (tsupport e₁ * tsupport e₂) := IsCompact.mul c1 c2
  let A := (finite_out_mem K h₁.1 c1).toFinset
  let A₂ := (finite_out_mem K h₁.1 c2).toFinset
  let B := (finite_out_mem K h₁.1 c12).toFinset
  have memA : ∀ q : GL ι F ⧸ K, q ∈ A ↔ q.out ∈ tsupport e₁ := fun q => by simp [A]
  have memA₂ : ∀ q : GL ι F ⧸ K, q ∈ A₂ ↔ q.out ∈ tsupport e₂ := fun q => by simp [A₂]
  have memB : ∀ q : GL ι F ⧸ K, q ∈ B ↔ q.out ∈ tsupport e₁ * tsupport e₂ := fun q => by simp [B]
  have hc : ∀ g, hconv K e₁ e₂ g = ∑ q ∈ A, e₁ q.out * e₂ (q.out⁻¹ * g) := fun g => by
    unfold hconv
    refine finsum_eq_sum_of_support_subset _ ?_
    intro q hq
    exact Finset.mem_coe.2 ((memA q).2 (subset_tsupport _ (left_ne_zero_of_mul hq)))
  have hL := hk_eq_sum ρ K (hconv K e₁ e₂) v B
    (fun s hs => (memB s).2 (support_hconv K e₁ e₂ hs))
  have hT : ∀ x : GL ι F, ∑ᶠ r : GL ι F ⧸ K, e₂ r.out • ρ (x * r.out) v
      = ∑ᶠ s : GL ι F ⧸ K, e₂ (x⁻¹ * s.out) • ρ s.out v := fun x => by
    have hr : ∀ y, ∀ k ∈ K, (fun y => e₂ (x⁻¹ * y) • ρ y v) (y * k) = (fun y => e₂ (x⁻¹ * y) • ρ y v) y := by
      intro y k hk'
      show e₂ (x⁻¹ * (y * k)) • ρ (y * k) v = e₂ (x⁻¹ * y) • ρ y v
      rw [← mul_assoc, isHk_right h₂ _ hk', map_mul, Module.End.mul_apply, hvk k hk']
    have ht := finsum_out_translate K (fun y => e₂ (x⁻¹ * y) • ρ y v) hr x
    simpa only [inv_mul_cancel_left] using ht
  have hI : ∀ q ∈ A, ρ q.out (hk ρ K e₂ v) = ∑ s ∈ B, e₂ (q.out⁻¹ * s.out) • ρ s.out v := by
    intro q hq
    have hq' := (memA q).1 hq
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hk_eq_sum ρ K e₂ v A₂ (fun r hr => (memA₂ r).2 (subset_tsupport _ hr)), map_sum]
    have h1 : ∑ r ∈ A₂, ρ q.out (e₂ r.out • ρ r.out v) = ∑ᶠ r : GL ι F ⧸ K, e₂ r.out • ρ (q.out * r.out) v := by
      symm
      rw [finsum_eq_sum_of_support_subset (s := A₂)]
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [map_smul, map_mul, Module.End.mul_apply]
      · intro r hr
        refine Finset.mem_coe.2 ((memA₂ r).2 (subset_tsupport _ fun h0 => (Function.mem_support.1 hr) ?_))
        show e₂ r.out • ρ (q.out * r.out) v = 0
        rw [h0, zero_smul]
    rw [h1, hT]
    refine finsum_eq_sum_of_support_subset _ ?_
    intro s hs
    refine Finset.mem_coe.2 ((memB s).2 (Set.mem_mul.2 ⟨q.out, hq', q.out⁻¹ * s.out,
      subset_tsupport _ fun h0 => (Function.mem_support.1 hs) ?_, mul_inv_cancel_left _ _⟩))
    show e₂ (q.out⁻¹ * s.out) • ρ s.out v = 0
    rw [h0, zero_smul]
  have hR : hk ρ K e₁ (hk ρ K e₂ v)
      = ∑ q ∈ A, e₁ q.out • ∑ s ∈ B, e₂ (q.out⁻¹ * s.out) • ρ s.out v := by
    rw [hk_eq_sum ρ K e₁ _ A (fun q hq => (memA q).2 (subset_tsupport _ hq))]
    exact Finset.sum_congr rfl (fun q hq => by rw [hI q hq])
  rw [hL, hR]
  simp only [hc, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

end Hecke

end GlobalTheory.CompanionTheory.HeckeMul
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HkMemFixed
section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeFix

theorem hk_mem_fixed : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V), ∀ v ∈ fixed ρ K, hk ρ K e v ∈ fixed ρ K ∧ ∀ g : GL ι F, (∀ q : GL ι F ⧸ K, e (g * q.out) = e q.out) → True := by
  intro F _ _ _ _ ι _ _ K e hE V _ _ ρ v hv
  refine ⟨?_, fun _ _ => trivial⟩
  have hfix : ∀ c ∈ K, ρ c v = v := by
    intro c hc
    have := hv ⟨c, hc⟩
    simpa using this
  have hbi := hE.2.2.2
  intro h
  have hk' : (h : GL ι F) ∈ K := h.2
  set k : GL ι F := (h : GL ι F) with hkdef
  have hinj : Function.Injective (ρ k : V →ₗ[ℂ] V) := by
    intro x y hxy
    have h1 : ∀ z, ρ k⁻¹ (ρ k z) = z := by
      intro z
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1 x, ← h1 y, hxy]
  have hstep : ∀ q : GL ι F ⧸ K, ρ k (e q.out • ρ q.out v) =
      e (k • q).out • ρ (k • q).out v := by
    intro q
    have hq : k • q = QuotientGroup.mk (k * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K (k * q.out)
    rw [hq, hc, hbi k hk' c c.2 q.out, map_smul, map_mul, Module.End.mul_apply, map_mul,
      Module.End.mul_apply, hfix c c.2]
  have hsum : ρ k (hk ρ K e v) = hk ρ K e v := by
    unfold hk
    have h1 := AddMonoidHom.map_finsum_of_injective (ρ k : V →ₗ[ℂ] V).toAddMonoidHom hinj
      (fun q : GL ι F ⧸ K => e q.out • ρ q.out v)
    simp only [LinearMap.toAddMonoidHom_coe] at h1
    rw [h1]
    simp only [hstep]
    exact finsum_comp_equiv (f := fun q : GL ι F ⧸ K => e q.out • ρ q.out v) (MulAction.toPerm k)
  simpa using hsum

end GlobalTheory.CompanionTheory.HeckeFix
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseTransformLocallyBounded
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem inv_bounded_on_tube : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T]
    (φ : ℝ × ℝ → T → X), ExpDecay φ → (∀ g : T, Continuous fun t => φ t g) → ∀ C : Set (ℝ × ℝ), IsCompact C →
    ∀ g : T, ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ l ∈ tube C, ∀ g' ∈ U, ‖inv (fun t => φ t g') l‖ ≤ M := by
  intro X _ _ T _ φ hφ hc C hC g
  choose ε hε U hU M hM using fun x₀ : ℝ × ℝ => hφ x₀ g
  have hnhds : ∀ x ∈ C, {y : ℝ × ℝ | |y.1 - x.1| < ε x ∧ |y.2 - x.2| < ε x} ∈ 𝓝 x := by
    intro x _
    have h1 : Continuous fun y : ℝ × ℝ => |y.1 - x.1| := by fun_prop
    have h2 : Continuous fun y : ℝ × ℝ => |y.2 - x.2| := by fun_prop
    refine ((isOpen_lt h1 continuous_const).inter (isOpen_lt h2 continuous_const)).mem_nhds ?_
    simpa using hε x
  obtain ⟨s, -, hcov⟩ := hC.elim_nhds_subcover _ hnhds
  refine ⟨⋂ x ∈ s, U x, (Filter.biInter_finset_mem s).2 fun x _ => hU x,
    ‖(((2 * Real.pi) ^ 2 : ℂ)⁻¹)‖ * ∑ x ∈ s, |M x| * (2 / ε x) ^ 2, ?_⟩
  intro l hl g' hg'
  have hlC : ((l.1.re, l.2.re) : ℝ × ℝ) ∈ C := hl
  obtain ⟨x₀, hx₀, h1, h2⟩ := Set.mem_iUnion₂.1 (hcov hlC)
  have hgU : g' ∈ U x₀ := Set.mem_iInter₂.1 hg' x₀ hx₀
  have hb := (GlobalTheory.T.exponential_fourier_integral_bound X (fun t => φ t g') l (ε x₀) (M x₀) (hε x₀) (hc g')
    fun t => hM x₀ (l.1.re, l.2.re) h1.le h2.le g' hgU t).2
  have hterm : M x₀ * (2 / ε x₀) ^ 2 ≤ |M x₀| * (2 / ε x₀) ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  have hsum : |M x₀| * (2 / ε x₀) ^ 2 ≤ ∑ x ∈ s, |M x| * (2 / ε x) ^ 2 :=
    Finset.single_le_sum (f := fun x => |M x| * (2 / ε x) ^ 2)
      (fun x _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)) hx₀
  simp only [inv]
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hb.trans (hterm.trans hsum)) (norm_nonneg _)

end GlobalTheory.CompanionTheory.TubeFourier
end

