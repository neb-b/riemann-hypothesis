module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0034

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaximalCountUnbranched
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

namespace MaximalCountUnbranched

theorem analyticOnNhd_of_differentiableOn_pi {d : ℕ} {σ : Type} [Fintype σ] {U : Set (Fin d → ℂ)}
    {G : (Fin d → ℂ) → σ → ℂ} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) : AnalyticOnNhd ℂ G U := by
  intro y hy
  refine AnalyticAt.pi fun s => ?_
  have hs : DifferentiableOn ℂ (fun x => G x s) U := differentiableOn_pi.1 hG s
  refine analyticOnNhd_of_continuousOn_of_separately hU hs.continuousOn (fun z hz i => ?_) y hy
  have h1 : DifferentiableAt ℂ (fun x => G x s) (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hs.differentiableAt (hU.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update (𝕜 := ℂ) z (z i)).differentiableAt

theorem fibre_unique_near {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {N : ℕ} (hmaps : Set.MapsTo A Y D)
    (hopen : ∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x))
    (hle : ∀ y ∈ D, {x | x ∈ Y ∧ A x = y}.encard ≤ N)
    {z : σ → ℂ} (hz : z ∈ Y) (hzN : {x' | x' ∈ Y ∧ A x' = A z}.encard = N) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ W ∈ 𝓝 (A z), ∀ y ∈ W,
      {x' | x' ∈ Y ∧ A x' = y}.encard = N ∧ (∃ x' ∈ Y, A x' = y ∧ dist x' z < ε) ∧
      ∀ x₁ ∈ Y, ∀ x₂ ∈ Y, A x₁ = y → A x₂ = y → dist x₁ z < ε → dist x₂ z < ε → x₁ = x₂ := by
  have hSfin : {x' | x' ∈ Y ∧ A x' = A z}.Finite := Set.finite_of_encard_eq_coe hzN
  have hzS : z ∈ {x' | x' ∈ Y ∧ A x' = A z} := ⟨hz, rfl⟩
  have hsep : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ {x' | x' ∈ Y ∧ A x' = A z} ×ˢ {x' | x' ∈ Y ∧ A x' = A z},
      p.1 ≠ p.2 → 2 * ε < dist p.1 p.2 := by
    refine (eventually_all_finite (hSfin.prod hSfin)).2 fun p _ => ?_
    by_cases hp : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hp h
    · have hpos : 0 < dist p.1 p.2 / 2 := half_pos (dist_pos.2 hp)
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hpos)] with ε hε _
      linarith
  filter_upwards [hsep, self_mem_nhdsWithin] with ε hε hε0
  have hε0 : (0 : ℝ) < ε := hε0
  refine ⟨⋂ s ∈ {x' | x' ∈ Y ∧ A x' = A z}, A '' (Y ∩ ball s ε), (biInter_mem hSfin).2 fun s hs => ?_,
    fun y hy => ?_⟩
  · have := hopen s hs.1 (ball s ε) (ball_mem_nhds s hε0)
    rwa [hs.2] at this
  have hch : ∀ s ∈ {x' | x' ∈ Y ∧ A x' = A z}, ∃ p, p ∈ Y ∧ dist p s < ε ∧ A p = y := by
    intro s hs
    obtain ⟨p, ⟨hpY, hpb⟩, hpA⟩ := Set.mem_iInter₂.1 hy s hs
    exact ⟨p, hpY, mem_ball.1 hpb, hpA⟩
  choose! f hfY hfd hfA using hch
  have hinj : Set.InjOn f {x' | x' ∈ Y ∧ A x' = A z} := by
    intro s hs s' hs' he
    by_contra hne
    have h1 : 2 * ε < dist s s' := hε (s, s') ⟨hs, hs'⟩ hne
    have h2 : dist s s' ≤ dist (f s) s + dist (f s') s' := by
      calc dist s s' ≤ dist s (f s) + dist (f s) s' := dist_triangle _ _ _
        _ = dist (f s) s + dist (f s') s' := by rw [dist_comm s, he]
    linarith [hfd s hs, hfd s' hs']
  have hyD : y ∈ D := hfA z hzS ▸ hmaps (hfY z hzS)
  have hsub : f '' {x' | x' ∈ Y ∧ A x' = A z} ⊆ {x' | x' ∈ Y ∧ A x' = y} := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hfY s hs, hfA s hs⟩
  have himg : (f '' {x' | x' ∈ Y ∧ A x' = A z}).encard = N := by rw [hinj.encard_image, hzN]
  have hFle := hle y hyD
  have hFeq : {x' | x' ∈ Y ∧ A x' = y}.encard = N :=
    le_antisymm hFle (himg ▸ Set.encard_le_encard hsub)
  have huniq : ∀ x₁ ∈ Y, A x₁ = y → dist x₁ z < ε → x₁ = f z := by
    intro x₁ hx₁ hA₁ hd₁
    by_contra hne
    have hnot : x₁ ∉ f '' {x' | x' ∈ Y ∧ A x' = A z} := by
      rintro ⟨s, hs, rfl⟩
      by_cases hsz : s = z
      · exact hne (hsz ▸ rfl)
      · have h1 : 2 * ε < dist s z := hε (s, z) ⟨hs, hzS⟩ hsz
        have h2 : dist s z ≤ dist (f s) s + dist (f s) z := by
          calc dist s z ≤ dist s (f s) + dist (f s) z := dist_triangle _ _ _
            _ = dist (f s) s + dist (f s) z := by rw [dist_comm s]
        linarith [hfd s hs]
    have hins : insert x₁ (f '' {x' | x' ∈ Y ∧ A x' = A z}) ⊆ {x' | x' ∈ Y ∧ A x' = y} :=
      Set.insert_subset ⟨hx₁, hA₁⟩ hsub
    have hc := Set.encard_le_encard hins
    rw [Set.encard_insert_of_notMem hnot, himg] at hc
    have hc' : ((N + 1 : ℕ) : ℕ∞) ≤ (N : ℕ∞) := by exact_mod_cast hc.trans hFle
    have : N + 1 ≤ N := by exact_mod_cast hc'
    omega
  refine ⟨hFeq, ⟨f z, hfY z hzS, hfA z hzS, hfd z hzS⟩, fun x₁ hx₁ x₂ hx₂ hA₁ hA₂ hd₁ hd₂ => ?_⟩
  rw [huniq x₁ hx₁ hA₁ hd₁, huniq x₂ hx₂ hA₂ hd₂]

theorem proof (hRE : RiemannExtensionAnalytic.Statement) : MaximalCountUnbranched.Statement := by
  intro σ _ Y d A D N _hD hmaps _hprop hopen hgen x hx hxN
  have key := fun (z : σ → ℂ) (hz : z ∈ Y) (hzN : {x' | x' ∈ Y ∧ A x' = A z}.encard = N) =>
    fibre_unique_near hmaps hopen hgen.1 hz hzN
  obtain ⟨ε, ⟨W₀, hW₀, hW₀p⟩, hε0⟩ := ((key x hx hxN).and self_mem_nhdsWithin).exists
  have hε0 : (0 : ℝ) < ε := hε0
  obtain ⟨U, g, hUo, hxU, _hUD, hg, hgnz, hgsec⟩ := hgen.2 (A x) (hmaps hx)
  have hOo : IsOpen (interior W₀ ∩ U) := isOpen_interior.inter hUo
  have hOW : ∀ y ∈ interior W₀ ∩ U, y ∈ W₀ := fun y hy => interior_subset hy.1
  have hex : ∀ y ∈ interior W₀ ∩ U, ∃ x' ∈ Y, A x' = y ∧ dist x' x < ε :=
    fun y hy => (hW₀p y (hOW y hy)).2.1
  choose! h hhY hhA hhd using hex
  have hu : ∀ y ∈ interior W₀ ∩ U, ∀ x' ∈ Y, A x' = y → dist x' x < ε → x' = h y :=
    fun y hy x' hx' hA hd =>
      (hW₀p y (hOW y hy)).2.2 x' hx' (h y) (hhY y hy) hA (hhA y hy) hd (hhd y hy)

  have hcont : ContinuousOn h (interior W₀ ∩ U) := by
    intro y₀ hy₀
    refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro η hη
    have hzN : {x' | x' ∈ Y ∧ A x' = A (h y₀)}.encard = N := by
      rw [hhA y₀ hy₀]; exact (hW₀p y₀ (hOW y₀ hy₀)).1
    have hgap : 0 < ε - dist (h y₀) x := by linarith [hhd y₀ hy₀]
    have hsmall : ∀ᶠ e in 𝓝[>] (0 : ℝ), e < min η (ε - dist (h y₀) x) :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (lt_min hη hgap))
    obtain ⟨e, ⟨W₁, hW₁, hW₁p⟩, he⟩ := ((key (h y₀) (hhY y₀ hy₀) hzN).and hsmall).exists
    rw [hhA y₀ hy₀] at hW₁
    filter_upwards [hW₁, hOo.mem_nhds hy₀] with y hy1 hyO
    obtain ⟨x'', hx''Y, hx''A, hx''d⟩ := (hW₁p y hy1).2.1
    have hm1 := min_le_left η (ε - dist (h y₀) x)
    have hm2 := min_le_right η (ε - dist (h y₀) x)
    have hx''x : dist x'' x < ε := by
      have := dist_triangle x'' (h y₀) x
      linarith
    rw [← hu y hyO x'' hx''Y hx''A hx''x]
    linarith

  have hdiff : ∀ y₀ ∈ interior W₀ ∩ U, g y₀ ≠ 0 → DifferentiableAt ℂ h y₀ := by
    intro y₀ hy₀ hg₀
    obtain ⟨_, hsec⟩ := hgsec y₀ hy₀.2 hg₀
    obtain ⟨O₁, V₁, h₁, hO₁, _hV₁, hzV₁, han₁, hA₁, hYV₁⟩ := hsec (h y₀) (hhY y₀ hy₀) (hhA y₀ hy₀)
    have hz : h y₀ ∈ h₁ '' O₁ := hYV₁ ▸ ⟨hhY y₀ hy₀, hzV₁⟩
    obtain ⟨y₁, hy₁, hy₁e⟩ := hz
    have hy₁₀ : y₁ = y₀ := by rw [← hA₁ y₁ hy₁, hy₁e, hhA y₀ hy₀]
    rw [hy₁₀] at hy₁ hy₁e
    have hc₁ : ContinuousAt h₁ y₀ := (han₁ y₀ hy₁).continuousAt
    have hball : ball x ε ∈ 𝓝 (h₁ y₀) := by
      rw [hy₁e]; exact isOpen_ball.mem_nhds (mem_ball.2 (hhd y₀ hy₀))
    have heq : h₁ =ᶠ[𝓝 y₀] h := by
      filter_upwards [hc₁.preimage_mem_nhds hball, hO₁.mem_nhds hy₁, hOo.mem_nhds hy₀]
        with y hyb hyO₁ hyO
      have hyY : h₁ y ∈ Y := by
        have hmem : h₁ y ∈ h₁ '' O₁ := ⟨y, hyO₁, rfl⟩
        rw [← hYV₁] at hmem
        exact hmem.1
      exact hu y hyO (h₁ y) hyY (hA₁ y hyO₁) (mem_ball.1 hyb)
    exact (han₁ y₀ hy₁).differentiableAt.congr_of_eventuallyEq heq.symm

  have hgd : DifferentiableOn ℂ g (interior W₀ ∩ U) := hg.differentiableOn.mono fun y hy => hy.2
  have hgnz' : ∀ V : Set (Fin d → ℂ), IsOpen V → V ⊆ interior W₀ ∩ U → V.Nonempty → ∃ t ∈ V, g t ≠ 0 :=
    fun V hV hVO hVn => hgnz V hV (hVO.trans Set.inter_subset_right) hVn
  have hdense : interior W₀ ∩ U ⊆ closure ((interior W₀ ∩ U) ∩ {t | g t ≠ 0}) := by
    intro y hy
    rw [_root_.mem_closure_iff]
    intro o ho hyo
    obtain ⟨t, ht, hgt⟩ := hgnz' (o ∩ (interior W₀ ∩ U)) (ho.inter hOo) Set.inter_subset_right ⟨y, hyo, hy⟩
    exact ⟨t, ht.1, ht.2, hgt⟩
  have hcoord : ∀ j : σ, DifferentiableOn ℂ (fun y => h y j) (interior W₀ ∩ U) := by
    intro j
    have hdj : DifferentiableOn ℂ (fun y => h y j) ((interior W₀ ∩ U) ∩ {t | g t ≠ 0}) :=
      fun y hy => (differentiableAt_pi.1 (hdiff y hy.1 hy.2) j).differentiableWithinAt
    have hbj : ∀ τ ∈ interior W₀ ∩ U, ∃ M ∈ 𝓝 τ,
        Bornology.IsBounded ((fun y => h y j) '' (M ∩ (interior W₀ ∩ U) ∩ {t | g t ≠ 0})) := by
      intro τ _
      refine ⟨Set.univ, univ_mem, ?_⟩
      rw [isBounded_iff_forall_norm_le]
      refine ⟨‖x‖ + ε, ?_⟩
      rintro _ ⟨y, ⟨⟨_, hyO⟩, _⟩, rfl⟩
      calc ‖h y j‖ ≤ ‖h y‖ := norm_le_pi_norm (h y) j
        _ ≤ ‖x‖ + ε := norm_le_of_mem_closedBall (mem_closedBall.2 (hhd y hyO).le)
    obtain ⟨F, hF, hFe⟩ := hRE d (interior W₀ ∩ U) g (fun y => h y j) hOo hgd hgnz' hdj hbj
    have hEq : Set.EqOn F (fun y => h y j) (interior W₀ ∩ U) :=
      hFe.of_subset_closure hF.continuousOn (continuousOn_pi.1 hcont j) Set.inter_subset_left hdense
    exact hF.congr fun y hy => (hEq hy).symm
  have han : AnalyticOnNhd ℂ h (interior W₀ ∩ U) :=
    analyticOnNhd_of_differentiableOn_pi hOo (differentiableOn_pi.2 hcoord)
  refine ⟨interior W₀ ∩ U, ball x ε ∩ A ⁻¹' (interior W₀ ∩ U), h, hOo,
    isOpen_ball.inter (hOo.preimage A.continuous),
    ⟨mem_ball_self hε0, mem_interior_iff_mem_nhds.2 hW₀, hxU⟩, han, hhA, ?_⟩
  ext x'
  constructor
  · rintro ⟨hx'Y, hx'b, hx'O⟩
    exact ⟨A x', hx'O, (hu (A x') hx'O x' hx'Y rfl (mem_ball.1 hx'b)).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hhY y hy, mem_ball.2 (hhd y hy), show A (h y) ∈ interior W₀ ∩ U from (hhA y hy).symm ▸ hy⟩

end MaximalCountUnbranched

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNonIsolatedFibreCurve
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

theorem NonIsolatedFibreCurve.analyticOnNhd_of_differentiableOn {k : ℕ} {O : Set (Fin k → ℂ)}
    {g : (Fin k → ℂ) → ℂ} (hO : IsOpen O) (hg : DifferentiableOn ℂ g O) : AnalyticOnNhd ℂ g O := by
  refine analyticOnNhd_of_continuousOn_of_separately hO hg.continuousOn fun z hz i => ?_
  have h1 : DifferentiableAt ℂ g (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hg.differentiableAt (hO.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update z (z i)).differentiableAt

theorem NonIsolatedFibreCurve.proof (hComp : AnalyticGermComponents.Statement)
    (hCurve : IrreducibleGermCurve.Statement) : NonIsolatedFibreCurve.Statement := by
  intro k m U f p hU hf hp hacc
  set Z : Set (Fin k → ℂ) := {v | v ∈ U ∧ f v = f p} with hZ
  have hZan : IsAnalyticNear Z p := by
    refine ⟨U, m, fun i v => f v i - f p i, hU, hp, fun i => ?_, ?_⟩
    · exact analyticOnNhd_of_differentiableOn hU ((differentiableOn_pi.1 hf i).sub_const _)
    · ext v
      simp only [hZ, Set.mem_inter_iff, Set.mem_ofPred_eq, sub_eq_zero, funext_iff]
      tauto
  obtain ⟨n, Y, hY, W, hW, hZW⟩ := hComp (Fin k) Z p hZan ⟨hp, rfl⟩

  have hfreq : ∃ᶠ y in 𝓝 p, y ≠ p ∧ y ∈ ⋃ i, Y i := by
    have h := accPt_iff_frequently.1 hacc
    refine (h.and_eventually hW).mono fun y ⟨⟨hne, hyZ⟩, hyW⟩ => ⟨hne, ?_⟩
    have : y ∈ Z ∩ W := ⟨hyZ, hyW⟩
    rw [hZW] at this
    exact this.1
  obtain ⟨i, hi⟩ : ∃ i, AccPt p (𝓟 (Y i)) := by
    by_contra hno
    push Not at hno
    have hev : ∀ᶠ y in 𝓝 p, ∀ i, ¬ (y ≠ p ∧ y ∈ Y i) := by
      refine eventually_all.2 fun i => ?_
      have := hno i
      rw [accPt_iff_frequently, Filter.not_frequently] at this
      exact this
    obtain ⟨y, ⟨hne, hyU⟩, hy⟩ := (hfreq.and_eventually hev).exists
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hyU
    exact hy j ⟨hne, hj⟩
  obtain ⟨r, hr, γ, hγd, hγi, hγ0, hγm⟩ := hCurve (Fin k) (Y i) p (hY i).1 (hY i).2 hi

  have hcont : ContinuousAt γ 0 := (hγd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).continuousAt
  have hpre : γ ⁻¹' W ∈ 𝓝 (0 : ℂ) := hcont.preimage_mem_nhds (by rwa [hγ0])
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hpre
  have hsub : ball (0 : ℂ) (min r ε) ⊆ ball 0 r := ball_subset_ball (min_le_left _ _)
  refine ⟨min r ε, lt_min hr hε, γ, hγd.mono hsub, hγi.mono hsub, hγ0, fun τ hτ => ?_⟩
  have hτW : γ τ ∈ W := hεW (ball_subset_ball (min_le_right _ _) hτ)
  have : γ τ ∈ (⋃ j, Y j) ∩ W := ⟨Set.mem_iUnion.2 ⟨i, hγm (hsub hτ)⟩, hτW⟩
  rw [← hZW] at this
  exact this.1

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalGermIntegrallyClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

noncomputable section

namespace NormalGermIntegrallyClosed

theorem analyticAt_of_differentiableOn {σ : Type} [Fintype σ] {N : Set (σ → ℂ)} {f : (σ → ℂ) → ℂ}
    (hN : IsOpen N) (hf : DifferentiableOn ℂ f N) {z : σ → ℂ} (hz : z ∈ N) : AnalyticAt ℂ f z := by
  let L : (Fin (Fintype.card σ) → ℂ) ≃L[ℂ] (σ → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ)).toContinuousLinearEquiv
  have hO : IsOpen (L ⁻¹' N) := hN.preimage L.continuous
  have hg : DifferentiableOn ℂ (f ∘ L) (L ⁻¹' N) :=
    hf.comp L.differentiable.differentiableOn fun x hx => hx
  have hA : AnalyticOnNhd ℂ (f ∘ L) (L ⁻¹' N) := by
    refine analyticOnNhd_of_continuousOn_of_separately hO hg.continuousOn fun x hx i => ?_
    have h1 : DifferentiableAt ℂ (f ∘ L) (Function.update x i (x i)) := by
      rw [Function.update_eq_self]
      exact hg.differentiableAt (hO.mem_nhds hx)
    exact h1.comp (x i) (hasFDerivAt_update x (x i)).differentiableAt
  have hz' : L.symm z ∈ L ⁻¹' N := by simpa using hz
  have h2 := (hA _ hz').comp ((L.symm : (σ → ℂ) →L[ℂ] (Fin (Fintype.card σ) → ℂ)).analyticAt z)
  simpa [Function.comp_def] using h2

def anFun {σ : Type} [Fintype σ] (w : σ → ℂ) : Subring ((σ → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f w}
  mul_mem' := fun hf hg => hf.mul hg
  one_mem' := analyticAt_const
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := analyticAt_const
  neg_mem' := fun hf => hf.neg

def toGerm {σ : Type} [Fintype σ] (w : σ → ℂ) : anFun w →+* holGerms w :=
  ((Germ.coeRingHom (𝓝 w)).comp (anFun w).subtype).codRestrict (holGerms w) fun u => ⟨u.1, u.2, rfl⟩

theorem toGerm_surjective {σ : Type} [Fintype σ] (w : σ → ℂ) : Function.Surjective (toGerm w) := by
  rintro ⟨φ, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩

theorem toGerm_eq_iff {σ : Type} [Fintype σ] {w : σ → ℂ} {u v : anFun w} :
    toGerm w u = toGerm w v ↔ (u : (σ → ℂ) → ℂ) =ᶠ[𝓝 w] v := by
  rw [Subtype.ext_iff]
  exact Germ.coe_eq

theorem vanish_of_mem_map {σ : Type} [Fintype σ] {I : Ideal (MvPolynomial σ ℂ)} {w : σ → ℂ} {u : anFun w}
    (hu : toGerm w u ∈ I.map (polyGerm w)) :
    ∀ᶠ z in 𝓝[zeroSetIn I] w, (u : (σ → ℂ) → ℂ) z = 0 := by
  have key : ∀ x, x ∈ Submodule.span (holGerms w) (polyGerm w '' (I : Set (MvPolynomial σ ℂ))) →
      ∃ v : anFun w, toGerm w v = x ∧ ∀ᶠ z in 𝓝[zeroSetIn I] w, (v : (σ → ℂ) → ℂ) z = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      exact ⟨⟨fun z => eval z q, analyticAt_eval_polynomial w q⟩, rfl,
        eventually_nhdsWithin_of_forall fun z hz => hz q hq⟩
    | zero => exact ⟨0, map_zero _, Eventually.of_forall fun z => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, rfl, hu⟩ := hx
      obtain ⟨v, rfl, hv⟩ := hy
      exact ⟨u + v, map_add _ _ _, by filter_upwards [hu, hv] with z h1 h2; simp [h1, h2]⟩
    | smul c x _ hx =>
      obtain ⟨v, rfl, hv⟩ := hx
      obtain ⟨b, rfl⟩ := toGerm_surjective w c
      exact ⟨b * v, by rw [map_mul, smul_eq_mul], by filter_upwards [hv] with z h; simp [h]⟩
  obtain ⟨v, hv, hv0⟩ := key _ hu
  have he : (u : (σ → ℂ) → ℂ) =ᶠ[𝓝 w] v := toGerm_eq_iff.1 hv.symm
  filter_upwards [nhdsWithin_le_nhds he, hv0] with z h1 h2
  rw [h1, h2]

theorem exists_eq_mul_of_integral_relation {S : Type*} [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    {d : ℕ} (f g : S) (a : Fin d → S) (hg : g ≠ 0)
    (hrel : f ^ d + ∑ j, a j * f ^ (j : ℕ) * g ^ (d - (j : ℕ)) = 0) : ∃ y, f = g * y := by
  let K := FractionRing S
  have hinj : Function.Injective (algebraMap S K) := IsFractionRing.injective S K
  have hrelK : algebraMap S K f ^ d + ∑ j, algebraMap S K (a j) * algebraMap S K f ^ (j : ℕ) *
      algebraMap S K g ^ (d - (j : ℕ)) = 0 := by
    have h2 := congrArg (algebraMap S K) hrel
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_mul, map_pow, map_zero] at h2
    exact h2
  have hg0 : algebraMap S K g ≠ 0 := fun h0 => hg (hinj (by rw [h0, map_zero]))
  generalize hfK : algebraMap S K f = fK at hrelK
  generalize hgK : algebraMap S K g = gK at hrelK hg0
  have hint : IsIntegral S (fK / gK) := by
    refine ⟨Polynomial.X ^ d + ∑ j : Fin d, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ),
      Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
    have hterm : ∀ j : Fin d, algebraMap S K (a j) * (fK / gK) ^ (j : ℕ) =
        algebraMap S K (a j) * fK ^ (j : ℕ) * gK ^ (d - (j : ℕ)) / gK ^ d := by
      intro j
      rw [eq_div_iff (pow_ne_zero _ hg0), div_pow,
        show gK ^ d = gK ^ (j : ℕ) * gK ^ (d - (j : ℕ)) by rw [← pow_add, Nat.add_sub_cancel' j.2.le]]
      have hj : gK ^ (j : ℕ) ≠ 0 := pow_ne_zero _ hg0
      rw [show algebraMap S K (a j) * (fK ^ (j : ℕ) / gK ^ (j : ℕ)) * (gK ^ (j : ℕ) * gK ^ (d - (j : ℕ))) =
          algebraMap S K (a j) * fK ^ (j : ℕ) * gK ^ (d - (j : ℕ)) * (gK ^ (j : ℕ) / gK ^ (j : ℕ)) by ring,
        div_self hj, mul_one]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
      Polynomial.eval₂_mul, Polynomial.eval₂_C]
    rw [Finset.sum_congr rfl fun j _ => hterm j, div_pow, ← Finset.sum_div, ← add_div, hrelK, zero_div]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨y, hinj ?_⟩
  rw [map_mul, hy, hfK, hgK, mul_div_assoc', eq_div_iff hg0, mul_comm]

theorem proof (hRueckert : RueckertNullstellensatz.Statement)
    (hZariski : ZariskiAnalyticNormality.Statement) : NormalGermIntegrallyClosed.Statement := by
  intro σ _ I w N F G d a hI hIc hw hN hwN hF hG ha hGnz hrel
  have hFa : AnalyticAt ℂ F w := analyticAt_of_differentiableOn hN hF hwN
  have hGa : AnalyticAt ℂ G w := analyticAt_of_differentiableOn hN hG hwN
  have haa : ∀ j, AnalyticAt ℂ (a j) w := fun j => analyticAt_of_differentiableOn hN (ha j) hwN

  obtain ⟨k, p, hp⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian I)
  have hpI : ∀ i, p i ∈ I := fun i => hp ▸ Submodule.subset_span ⟨i, rfl⟩
  have hZp : ∀ z, (∀ i, eval z (p i) = 0) → z ∈ zeroSetIn I := by
    intro z hz q hq
    have hle : I ≤ RingHom.ker (eval z) := by
      rw [← hp]
      exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hz i)
    exact RingHom.mem_ker.1 (hle hq)

  obtain ⟨hJ, hJc⟩ := hZariski σ I w hI hIc hw
  let J := I.map (polyGerm w)
  have : J.IsPrime := hJ
  let S := holGerms w ⧸ J
  have : IsIntegrallyClosed S := hJc
  let π : anFun w →+* S := (Ideal.Quotient.mk J).comp (toGerm w)
  have hπ0 : ∀ u : anFun w, π u = 0 → ∀ᶠ z in 𝓝[zeroSetIn I] w, (u : (σ → ℂ) → ℂ) z = 0 :=
    fun u hu => vanish_of_mem_map (Ideal.Quotient.eq_zero_iff_mem.1 hu)
  have hπpoly : ∀ q ∈ I, π ⟨fun z => eval z q, analyticAt_eval_polynomial w q⟩ = 0 := fun q hq =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hq)
  have hπeq : ∀ u v : anFun w, (u : (σ → ℂ) → ℂ) =ᶠ[𝓝 w] v → π u = π v := fun u v h => by
    simp only [π, RingHom.comp_apply, toGerm_eq_iff.2 h]

  let FA : anFun w := ⟨F, hFa⟩
  let GA : anFun w := ⟨G, hGa⟩
  let aA : Fin d → anFun w := fun j => ⟨a j, haa j⟩
  let PA : anFun w := FA ^ d + ∑ j, aA j * FA ^ (j : ℕ) * GA ^ (d - (j : ℕ))
  have hPA : ∀ z, (PA : (σ → ℂ) → ℂ) z =
      F z ^ d + ∑ j, a j z * F z ^ (j : ℕ) * G z ^ (d - (j : ℕ)) := by
    intro z
    simp [PA, FA, GA, aA, Finset.sum_apply]

  have hGS : π GA ≠ 0 := by
    intro h
    exact hGnz (eventually_nhdsWithin_iff.1 (hπ0 GA h))

  have hvan : ∀ᶠ z in 𝓝 w, (∀ i, eval z (p i) = 0) → (PA : (σ → ℂ) → ℂ) z * G z = 0 := by
    filter_upwards [hN.mem_nhds hwN] with z hzN hz
    by_cases hG0 : G z = 0
    · rw [hG0, mul_zero]
    · rw [hPA, hrel z ⟨⟨hZp z hz, hzN⟩, hG0⟩, zero_mul]
  obtain ⟨m, h, hm, hh, hgm⟩ := hRueckert σ w k (fun i z => eval z (p i))
    (fun z => (PA : (σ → ℂ) → ℂ) z * G z) (fun i => analyticAt_eval_polynomial w (p i))
    (PA.2.mul hGa) hvan
  let hA : Fin k → anFun w := fun i => ⟨h i, hh i⟩
  let pA : Fin k → anFun w := fun i => ⟨fun z => eval z (p i), analyticAt_eval_polynomial w (p i)⟩
  have hprod : π ((PA * GA) ^ m) = π (∑ i, hA i * pA i) := by
    apply hπeq
    filter_upwards [hgm] with z hz
    simpa [hA, pA, GA, Finset.sum_apply, mul_pow] using hz
  have hPS : π PA = 0 := by
    have h1 : (π PA * π GA) ^ m = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_mul, ← map_pow, hprod, map_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [map_mul, hπpoly _ (hpI i), mul_zero]
    exact (mul_eq_zero.1 ((pow_eq_zero_iff (Nat.pos_iff_ne_zero.1 hm)).1 h1)).resolve_right hGS

  have : IsDomain S := Ideal.Quotient.isDomain J
  obtain ⟨y, hy⟩ := exists_eq_mul_of_integral_relation (π FA) (π GA) (fun j => π (aA j)) hGS (by
    rw [← hPS]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [PA, map_add (f := _), map_sum, map_mul, map_pow])
  obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨HA, rfl⟩ := toGerm_surjective w φ
  have hdiff : π (FA - GA * HA) = 0 := by
    rw [map_sub, map_mul, hy]
    exact sub_self _
  have hv := eventually_nhdsWithin_iff.1 (hπ0 _ hdiff)
  obtain ⟨V, hV, hVo, hwV⟩ := eventually_nhds_iff.1 (hv.and HA.2.eventually_analyticAt)
  refine ⟨V, hVo, hwV, HA, fun z hz => (hV z hz).2.differentiableAt.differentiableWithinAt, ?_⟩
  rintro z ⟨hzZ, hzV⟩
  have h3 := (hV z hzV).1 hzZ
  change F z - G z * (HA : (σ → ℂ) → ℂ) z = 0 at h3
  exact sub_eq_zero.1 h3

end NormalGermIntegrallyClosed

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchProperAtPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

def BranchProperAtPoint.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u p x : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → GroundTheory.Heights₂.Heights.VarBranch J k p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) → linForm u ∉ J →
    (∃ N ∈ 𝓝 x, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {y | GroundTheory.Heights₂.Heights.linEval u y = 0}) →
    ∀ b, ∀ s ∈ Metric.ball 0 (γ b).radius, (γ b).toFun s = x →
      ∀ P ∈ 𝓝 s, ∃ ε > 0, ∀ τ ∈ Metric.ball 0 (γ b).radius,
        (γ b).toFun τ ∈ Metric.ball x ε → τ ∈ P

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

