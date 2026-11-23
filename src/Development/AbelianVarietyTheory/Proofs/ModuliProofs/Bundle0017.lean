module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsLocalHomeomorphAddMonoidHomOfEventuallyEq
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AppellHumbertDataOfIsoCube

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsActionOfIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_action_of_isPullback {Γ : Type} [Group Γ] {X X' Y Y' : Scheme.{0}}
    (ρ : Γ →* Aut X) {π : X ⟶ X'} {φ : Y ⟶ Y'} {p : Y ⟶ X} {p' : Y' ⟶ X'}
    (hπ : ∀ g, (ρ g).asIso.hom ≫ π = π) (H : IsPullback p φ π p') :
    ∃ τ : Γ →* Aut Y, ∀ g,
      (τ g).asIso.hom ≫ φ = φ ∧ (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom := by
  have hc : ∀ g : Γ, (p ≫ (ρ g).asIso.hom) ≫ π = φ ≫ p' := fun g => by
    rw [Category.assoc, hπ g, H.w]
  let e : Γ → (Y ⟶ Y) := fun g => H.lift (p ≫ (ρ g).asIso.hom) φ (hc g)
  have e_p : ∀ g, e g ≫ p = p ≫ (ρ g).asIso.hom := fun g => H.lift_fst _ _ _
  have e_φ : ∀ g, e g ≫ φ = φ := fun g => H.lift_snd _ _ _
  have e_one : e 1 = 𝟙 Y := H.hom_ext
    (by rw [e_p, map_one]; exact (Category.comp_id p).trans (Category.id_comp p).symm)
    (by rw [e_φ, Category.id_comp])
  have e_mul : ∀ g h, e (g * h) = e h ≫ e g := fun g h => H.hom_ext
    (by
      rw [e_p, Category.assoc, e_p, ← Category.assoc, e_p, Category.assoc, map_mul]
      rfl)
    (by rw [e_φ, Category.assoc, e_φ, e_φ])
  let τf : Γ → Aut Y := fun g => Aut.of
    { hom := e g
      inv := e g⁻¹
      hom_inv_id := by rw [← e_mul, inv_mul_cancel, e_one]
      inv_hom_id := by rw [← e_mul, mul_inv_cancel, e_one] }
  refine ⟨{ toFun := τf, map_one' := ?_, map_mul' := ?_ }, fun g => ⟨e_φ g, e_p g⟩⟩
  · exact Aut.ext (Iso.ext e_one)
  · intro g h
    exact Aut.ext (Iso.ext (e_mul g h))

theorem quotient_flat_baseChange :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' Y Y' : Scheme.{0}) (ρ : Γ →* Aut X)
      (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'),
      (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧
        ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V),
          (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)),
            ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) →
      IsPullback φ p p' π → Flat p' →
      (∃ τ : Γ →* Aut Y, ∀ g,
        (τ g).asIso.hom ≫ φ = φ ∧ (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom) ∧
      ∀ τ : Γ →* Aut Y,
        (∀ g, (τ g).asIso.hom ≫ φ = φ ∧ (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom) →
        (IsAffineHom φ ∧ (∀ g, (τ g).asIso.hom ≫ φ = φ) ∧
          ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V),
            (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).asIso.hom ⁻¹ᵁ (φ ⁻¹ᵁ V)),
              ((τ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom) := by
  intro Γ _ _ X X' Y Y' ρ π φ p p' hq H hflat
  obtain ⟨hπa, hπ, hV⟩ := hq
  refine ⟨exists_action_of_isPullback ρ hπ H.flip, fun τ hτ => ?_⟩
  have hQ : IsAffineQuotient ρ π :=
    { comp_eq := hπ
      isAffineHom := hπa
      app_injective := fun W => (hV W).1
      mem_range_app := fun W s hs => (hV W).2 s (by
        unfold IsInvariantSection at hs
        intro g h
        obtain ⟨_, e⟩ := hs g
        exact e) }
  have := hflat
  have hB := hQ.of_isPullback H.flip (fun g => (hτ g).2) (fun g => (hτ g).1)
  exact ⟨hB.isAffineHom, hB.comp_eq, fun V => ⟨hB.app_injective V, fun f hf => hB.mem_range_app V f (by
    unfold IsInvariantSection
    intro g
    have hle : φ ⁻¹ᵁ V ≤ (τ g).asIso.hom ⁻¹ᵁ φ ⁻¹ᵁ V := by
      rw [← Scheme.Hom.comp_preimage, (hτ g).1]
    exact ⟨hle, hf g hle⟩)⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAnalyticParamInverse
section
namespace GlobalTheory

section ParamExp

open Metric Set Filter Asymptotics
open scoped Topology

variable {B V : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem exists_analytic_param_inverse {F : B × V → V} {b₀ : B} {A : V →L[ℂ] V}
    (hF : AnalyticAt ℂ F (b₀, 0)) (h0 : F (b₀, 0) = 0)
    (hA : HasFDerivAt (fun x => F (b₀, x)) A 0) (hinj : Function.Injective A) :
    ∃ G : B × V → V, AnalyticAt ℂ G (b₀, 0) ∧ G (b₀, 0) = 0 ∧
      ∀ᶠ q in 𝓝 ((b₀, 0) : B × V), G (q.1, F q) = q.2 ∧ F (q.1, G q) = q.2 := by
  have hd := hF.differentiableAt.hasFDerivAt
  have hA' : (fderiv ℂ F (b₀, 0)).comp (ContinuousLinearMap.inr ℂ B V) = A :=
    (HasFDerivAt.comp (f := fun x : V => (b₀, x)) (0 : V) hd
      (hasFDerivAt_prodMk_right b₀ (0 : V))).unique hA
  have hΨ : AnalyticAt ℂ (fun q : B × V => (q.1, F q)) (b₀, 0) := analyticAt_fst.prod hF
  have hdΨ : HasFDerivAt (fun q : B × V => (q.1, F q))
      ((ContinuousLinearMap.fst ℂ B V).prod (fderiv ℂ F (b₀, 0))) (b₀, 0) :=
    hasFDerivAt_fst.prodMk hd
  obtain ⟨Φ, hΦ, hs, ha⟩ := AffinePoints.exists_openPartialHomeomorph_analytic rfl hΨ (by
    rw [hdΨ.fderiv, injective_iff_map_eq_zero]
    rintro ⟨u, v⟩ huv
    have hu : u = 0 := congrArg Prod.fst huv
    subst hu
    have hv : A v = A 0 := by
      rw [map_zero, ← hA']
      exact congrArg Prod.snd huv
    rw [hinj hv]
    rfl)
  have hfix : Φ (b₀, 0) = (b₀, 0) := by rw [hΦ]; simp [h0]
  have ht : ((b₀, 0) : B × V) ∈ Φ.target := hfix ▸ Φ.map_source hs
  refine ⟨fun q => (Φ.symm q).2, analyticAt_snd.comp (ha _ ht), ?_, ?_⟩
  · have := Φ.left_inv hs
    rw [hfix] at this
    simp [this]
  · filter_upwards [Φ.eventually_left_inverse hs, Φ.eventually_right_inverse ht] with q h1 h2
    rw [hΦ] at h1 h2
    refine ⟨congrArg Prod.snd h1, ?_⟩
    have h3 : (Φ.symm q).1 = q.1 := by simpa using congrArg Prod.fst h2
    have h4 : F (Φ.symm q) = q.2 := congrArg Prod.snd h2
    rw [← h3]
    exact h4


omit [FiniteDimensional ℂ B] [FiniteDimensional ℂ V] in
theorem eventually_eq_zero_of_slices {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [CompleteSpace V] {F : B × W → V} {b₀ : B} (hF : AnalyticAt ℂ F (b₀, 0))
    (h : ∀ᶠ b in 𝓝 b₀, ∀ᶠ w in 𝓝 (0 : W), F (b, w) = 0) :
    ∀ᶠ q in 𝓝 ((b₀, 0) : B × W), F q = 0 := by
  obtain ⟨s, hs, hsa⟩ := Metric.eventually_nhds_iff_ball.mp hF.eventually_analyticAt
  rw [← ball_prod_same] at hsa
  filter_upwards [prod_mem_nhds (Filter.inter_mem h (ball_mem_nhds b₀ hs)) (ball_mem_nhds 0 hs)]
    with ⟨b, w⟩ ⟨⟨hb, hbs⟩, hw⟩
  have ha : AnalyticOnNhd ℂ (fun w => F (b, w)) (ball 0 s) := fun x hx =>
    AnalyticAt.comp (f := fun x : W => (b, x)) (hsa (b, x) ⟨hbs, hx⟩)
      (analyticAt_const.prod analyticAt_id)
  exact ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 s).isPreconnected
    (mem_ball_self hs) hb hw

theorem analyticAt_param_doublingLog {ε : B × V → V} {b₀ : B} (ha : AnalyticAt ℂ ε (b₀, 0))
    (h : ∀ᶠ b in 𝓝 b₀, (fun x => ε (b, x) - (2 : ℂ)⁻¹ • x) =O[𝓝 0] fun x => ‖x‖ ^ 2) :
    AnalyticAt ℂ (fun q : B × V => doublingLog (fun x => ε (q.1, x)) q.2) (b₀, 0) := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  set K : ℝ := ‖ε (b₀, 0)‖ + 1 with hK
  have hK0 : 0 < K := by positivity
  obtain ⟨s, hs, hsa⟩ := Metric.eventually_nhds_iff_ball.mp
    (ha.eventually_analyticAt.and ((ha.continuousAt.norm.eventually
      (gt_mem_nhds (lt_add_one _))).and ((continuous_fst.tendsto' (b₀, (0 : V)) b₀ rfl).eventually h)))
  rw [← ball_prod_same] at hsa
  set C : ℝ := 4 * K / s ^ 2 with hCdef
  have hC0 : 0 < C := by positivity
  have hCs : ∀ b ∈ ball b₀ s, ∀ x ∈ ball (0 : V) s, ‖ε (b, x) - (2 : ℂ)⁻¹ • x‖ ≤ C * ‖x‖ ^ 2 := by
    intro b hb x hx
    have hO := (hsa (b, 0) ⟨hb, mem_ball_self hs⟩).2.2
    have hd : DifferentiableOn ℂ (fun x => ε (b, x)) (ball 0 s) := fun y hy =>
      (DifferentiableAt.comp (f := fun x : V => (b, x)) y (hsa (b, y) ⟨hb, hy⟩).1.differentiableAt
        (by fun_prop)).differentiableWithinAt
    have h1 := SCV.norm_sub_sub_fderiv_le_of_ball hd
      (fun y hy => (hsa (b, y) ⟨hb, hy⟩).2.1.le) hx
    have h2 : ε (b, 0) = 0 := map_zero_of_isBigO_sq (f := fun x => ε (b, x))
      (L := (2 : ℂ)⁻¹ • ContinuousLinearMap.id ℂ V) hO
    have h3 := (hasFDerivAt_of_isBigO_sq (f := fun x => ε (b, x))
      (L := (2 : ℂ)⁻¹ • ContinuousLinearMap.id ℂ V) hO).fderiv
    rw [h3, h2, sub_zero, sub_zero] at h1
    refine le_of_le_of_eq h1 ?_
    rw [hCdef, div_pow]
    ring
  set r : ℝ := min s (1 / (8 * C)) with hr
  have hr0 : 0 < r := lt_min hs (by positivity)
  have hrs : r ≤ s := min_le_left _ _
  have hC : ∀ b ∈ ball b₀ s, ∀ x ∈ ball (0 : V) r, ‖ε (b, x) - (2 : ℂ)⁻¹ • x‖ ≤ C * ‖x‖ ^ 2 :=
    fun b hb x hx => hCs b hb x (ball_subset_ball hrs hx)
  have hc : ∀ b ∈ ball b₀ s, ∀ x ∈ ball (0 : V) r, ‖ε (b, x)‖ ≤ 5 / 8 * ‖x‖ := by
    intro b hb x hx
    have h1 := hC b hb x hx
    have h2 : ‖x‖ ≤ 1 / (8 * C) := (mem_ball_zero_iff.mp hx).le.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h2
    have h3 : ‖(2 : ℂ)⁻¹ • x‖ = 1 / 2 * ‖x‖ := by simp [norm_smul]
    have h4 := norm_le_norm_sub_add (ε (b, x)) ((2 : ℂ)⁻¹ • x)
    nlinarith [norm_nonneg x]
  have hd : ∀ j : ℕ, DifferentiableOn ℂ (fun q : B × V => (fun x => ε (q.1, x))^[j] q.2)
      (ball b₀ s ×ˢ ball 0 r) := by
    intro j
    induction j with
    | zero => exact differentiableOn_snd
    | succ j ih =>
      simp only [Function.iterate_succ_apply']
      intro q hq
      exact DifferentiableAt.comp_differentiableWithinAt
        (f := fun q : B × V => (q.1, (fun x => ε (q.1, x))^[j] q.2)) q
        (hsa (q.1, (fun x => ε (q.1, x))^[j] q.2) ⟨hq.1, ball_subset_ball hrs
          (iterate_mem_ball_of_contraction (hc q.1 hq.1) hq.2 j)⟩).1.differentiableAt
        (differentiableWithinAt_fst.prodMk (ih q hq))
  have hu : TendstoUniformlyOn
      (fun (j : ℕ) (q : B × V) => (2 : ℂ) ^ j • (fun x => ε (q.1, x))^[j] q.2)
      (fun q : B × V => doublingLog (fun x => ε (q.1, x)) q.2) atTop (ball b₀ s ×ˢ ball 0 r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    have h0 : Tendsto (fun j : ℕ => 64 / 7 * C * r ^ 2 * (25 / 32 : ℝ) ^ j) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (25 / 32 : ℝ)) (by norm_num)
        (by norm_num)).const_mul (64 / 7 * C * r ^ 2)
    filter_upwards [h0.eventually (gt_mem_nhds hη)] with j hj q hq
    rw [dist_comm]
    refine ((dist_doublingLog_le_of_contraction (hc q.1 hq.1) hC0.le (hC q.1 hq.1) hq.2 j).trans
      ?_).trans_lt hj
    have := (mem_ball_zero_iff.mp hq.2).le
    gcongr
  exact SCV.analyticAt_of_differentiableOn
    (SCV.differentiableOn_of_tendstoLocallyUniformlyOn (isOpen_ball.prod isOpen_ball)
      hu.tendstoLocallyUniformlyOn (Eventually.of_forall fun j => (hd j).const_smul _))
    (prod_mem_nhds (ball_mem_nhds b₀ hs) (ball_mem_nhds 0 hr0))

theorem exists_param_exp_log {b₀ : B} {M : B × V × V → V} (hM : AnalyticAt ℂ M (b₀, 0, 0))
    (hu : ∀ᶠ q : B × V in 𝓝 (b₀, 0), M (q.1, q.2, 0) = q.2)
    (hc : ∀ᶠ q : B × V × V in 𝓝 (b₀, 0, 0), M (q.1, q.2.1, q.2.2) = M (q.1, q.2.2, q.2.1))
    (hs : ∀ᶠ q : B × V × V × V in 𝓝 (b₀, 0, 0, 0),
      M (q.1, M (q.1, q.2.1, q.2.2.1), q.2.2.2) = M (q.1, q.2.1, M (q.1, q.2.2.1, q.2.2.2))) :
    ∃ E L : B × V → V, AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧
      (∀ᶠ b in 𝓝 b₀, E (b, 0) = 0 ∧
        HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ V) 0) ∧
      (∀ᶠ q : B × V in 𝓝 (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧
      ∀ᶠ q : B × V × V in 𝓝 (b₀, 0, 0),
        E (q.1, q.2.1 + q.2.2) = M (q.1, E (q.1, q.2.1), E (q.1, q.2.2)) := by
  have : CompleteSpace V := FiniteDimensional.complete ℂ V
  have hlaw : ∀ᶠ b in 𝓝 b₀, IsLocalCommGroupLaw fun p : V × V => M (b, p) := by
    filter_upwards [hM.eventually_analyticAt.curry_nhds, hu.curry_nhds, hc.curry_nhds,
      hs.curry_nhds] with b h1 h2 h3 h4
    exact IsLocalCommGroupLaw.of_unit
      (AnalyticAt.comp (f := fun p : V × V => (b, p)) h1.self_of_nhds
        (analyticAt_const.prod analyticAt_id)) h2 h3 h4
  have h₀ := hlaw.self_of_nhds
  have hM0 : M (b₀, 0, 0) = 0 := h₀.map_zero
  obtain ⟨ε, hεa, -, hε⟩ := exists_analytic_param_inverse
    (F := fun q : B × V => M (q.1, q.2, q.2)) (b₀ := b₀)
    (AnalyticAt.comp (f := fun q : B × V => (q.1, q.2, q.2)) hM
      (analyticAt_fst.prod (analyticAt_snd.prod analyticAt_snd))) hM0
    h₀.hasFDerivAt_doubling (IsLocalCommGroupLaw.twoEquiv V).injective
  have hε' : ∀ᶠ b in 𝓝 b₀, ∀ᶠ x in 𝓝 (0 : V), ε (b, M (b, x, x)) = x :=
    (hε.mono fun q hq => hq.1).curry_nhds
  set L : B × V → V := fun q => doublingLog (fun x => ε (q.1, x)) q.2 with hL
  have hLa : AnalyticAt ℂ L (b₀, 0) := analyticAt_param_doublingLog hεa (by
    filter_upwards [hlaw, hε'] with b h1 h2
    exact h1.isBigO_inverse (ε := fun x => ε (b, x)) h2)
  have hLb : ∀ᶠ b in 𝓝 b₀, L (b, 0) = 0 ∧
      HasFDerivAt (fun x => L (b, x)) (ContinuousLinearMap.id ℂ V) 0 ∧
      ∀ᶠ p in 𝓝 (0 : V × V), L (b, M (b, p)) - (L (b, p.1) + L (b, p.2)) = 0 := by
    filter_upwards [hlaw, hε'] with b h1 h2
    exact ⟨h1.doublingLog_zero (ε := fun x => ε (b, x)) h2,
      h1.hasFDerivAt_doublingLog (ε := fun x => ε (b, x)) h2,
      (h1.doublingLog_law (ε := fun x => ε (b, x)) h2).mono fun p hp => sub_eq_zero.mpr hp⟩
  have hadd : ∀ᶠ q : B × V × V in 𝓝 (b₀, 0),
      L (q.1, M q) - (L (q.1, q.2.1) + L (q.1, q.2.2)) = 0 := by
    refine eventually_eq_zero_of_slices
      (F := fun q : B × V × V => L (q.1, M q) - (L (q.1, q.2.1) + L (q.1, q.2.2))) ?_
      (hLb.mono fun b hb => hb.2.2)
    refine AnalyticAt.sub ?_ (AnalyticAt.add ?_ ?_)
    · exact AnalyticAt.comp_of_eq (f := fun q : B × V × V => (q.1, M q)) hLa
        (analyticAt_fst.prod hM) (Prod.ext rfl hM0)
    · exact AnalyticAt.comp_of_eq (f := fun q : B × V × V => (q.1, q.2.1)) hLa
        (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)) rfl
    · exact AnalyticAt.comp_of_eq (f := fun q : B × V × V => (q.1, q.2.2)) hLa
        (analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)) rfl
  obtain ⟨E, hEa, hE0, hE⟩ := exists_analytic_param_inverse hLa hLb.self_of_nhds.1
    hLb.self_of_nhds.2.1 Function.injective_id
  refine ⟨E, L, hEa, hLa, ?_, hE.mono fun q hq => hq.symm, ?_⟩
  · filter_upwards [hLb, hE.curry_nhds, hEa.eventually_analyticAt.curry_nhds] with b h1 h2 h3
    have h4 : E (b, 0) = 0 := by simpa [h1.1] using h2.self_of_nhds.1
    refine ⟨h4, ?_⟩
    have h5 : HasFDerivAt (fun v => E (b, v)) (fderiv ℂ (fun v => E (b, v)) 0) 0 :=
      (DifferentiableAt.comp (f := fun v : V => (b, v)) 0 h3.self_of_nhds.differentiableAt
        (by fun_prop)).hasFDerivAt
    have h6 := HasFDerivAt.comp (g := fun x => L (b, x)) (f := fun v => E (b, v)) 0
      (by simpa only [h4] using h1.2.1) h5
    have h7 := h6.unique ((hasFDerivAt_id (0 : V)).congr_of_eventuallyEq
      (h2.mono fun v hv => hv.2))
    rw [ContinuousLinearMap.id_comp] at h7
    rwa [h7] at h5
  · have tE : Tendsto E (𝓝 (b₀, 0)) (𝓝 0) := by
      simpa only [hE0] using hEa.continuousAt.tendsto
    have tM : Tendsto M (𝓝 (b₀, 0, 0)) (𝓝 0) := by
      simpa only [hM0] using hM.continuousAt.tendsto
    have t0 : Tendsto (fun q : B × V × V => q.1) (𝓝 (b₀, 0, 0)) (𝓝 b₀) :=
      continuous_fst.tendsto' _ _ rfl
    have t1 : Tendsto (fun q : B × V × V => (q.1, q.2.1)) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
      Continuous.tendsto' (by fun_prop) _ _ rfl
    have t2 : Tendsto (fun q : B × V × V => (q.1, q.2.2)) (𝓝 (b₀, 0, 0)) (𝓝 (b₀, 0)) :=
      Continuous.tendsto' (by fun_prop) _ _ rfl
    have t3 := t0.prodMk_nhds ((tE.comp t1).prodMk_nhds (tE.comp t2))
    filter_upwards [t3.eventually hadd, t1.eventually hE, t2.eventually hE,
      (t3.eventually (((continuous_fst.tendsto' _ _ rfl).prodMk_nhds tM).eventually hE))]
      with q h1 h2 h3 h4
    simp only [Function.comp] at h1 h2 h3 h4
    rw [sub_eq_zero, h2.2, h3.2] at h1
    rw [← h1, h4.1]

end ParamExp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem exists_param_exp_log_pi : ∀ (m g : ℕ) (b₀ : Fin m → ℂ) (M : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) → (Fin g → ℂ)), AnalyticAt ℂ M (b₀, 0, 0) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), M (q.1, q.2, 0) = q.2) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), M (q.1, q.2.1, q.2.2) = M (q.1, q.2.2, q.2.1)) → (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0, 0), M (q.1, M (q.1, q.2.1, q.2.2.1), q.2.2.2) = M (q.1, q.2.1, M (q.1, q.2.2.1, q.2.2.2))) → ∃ E L : (Fin m → ℂ) × (Fin g → ℂ) → (Fin g → ℂ), AnalyticAt ℂ E (b₀, 0) ∧ AnalyticAt ℂ L (b₀, 0) ∧ (∀ᶠ b in nhds b₀, E (b, 0) = 0 ∧ HasFDerivAt (fun v => E (b, v)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) ∧ (∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) in nhds (b₀, 0), L (q.1, E q) = q.2 ∧ E (q.1, L q) = q.2) ∧ ∀ᶠ q : (Fin m → ℂ) × (Fin g → ℂ) × (Fin g → ℂ) in nhds (b₀, 0, 0), E (q.1, q.2.1 + q.2.2) = M (q.1, E (q.1, q.2.1), E (q.1, q.2.2)) :=
  fun _ _ _ _ hM hu hc hs => exists_param_exp_log hM hu hc hs

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAppellHumbertFrameOfPulledBiextension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.PulledBiextFrame

open GlobalTheory.CubeValues GlobalTheory.SelfCube

def combUnif {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {K : Type} [Fintype K] (φ : K → (A.left ⟶ A.left))
    (p : K → (Fin g → ℂ) → (Fin g → ℂ)) (hd : ∀ k, Differentiable ℂ (p k)) (ε : K → ℤ)
    (hp : ∀ k z, (u.ex z).left ≫ φ k = (u.ex (p k z)).left) :
    HolUnif A (LB.LinComb L φ ε) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fun j z => ∏ k, u.fr (j k) (p k z) ^ ε k
  fr_hol := fun j => by
    have hD : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.LinComb L φ ε).U j →
        ∀ k, ⊤ ≤ (u.ex (p k z)).left ⁻¹ᵁ L.U (j k) := fun z hz k => by
      rw [← hp]; exact (le_preimage_wchart (u.ex z).left L φ j).1 hz k
    refine differentiableOn_prod' _ fun k => DifferentiableOn.zpow
      ((u.fr_hol (j k)).comp (hd k).differentiableOn fun z hz => hD z hz k) ?_
    exact Or.inl fun z hz => u.fr_ne _ _ (hD z hz k)
  fr_ne := fun j z hz => by
    refine Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (u.fr_ne _ _ ?_)
    rw [← hp]; exact (le_preimage_wchart (u.ex z).left L φ j).1 hz k
  fr_compat := fun j j' z hz => by
    obtain ⟨h1, h2⟩ := (le_preimage_inf _ _ _).1 hz
    have e := val_linComb (u.ex z).left GlobalTheory.valAt'_rules L φ ε j j' h1 h2
    refine Eq.trans ?_ (congrArg (· * _) e.symm)
    simp only [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have a1 := (le_preimage_wchart (u.ex z).left L φ j).1 h1 k
    have a2 := (le_preimage_wchart (u.ex z).left L φ j').1 h2 k
    rw [hp] at a1 a2 ⊢
    rw [u.fr_compat _ _ _ ((le_preimage_inf _ _ _).2 ⟨a1, a2⟩), mul_zpow]

theorem exists_appellHumbert_frame :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ) (w : P.A ⟶ P.A) (F F' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)), u.IsAH Hm χ → (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) → (∀ z, u.ex (F z) = u.ex z ≫ w) → F + F' = LinearMap.id → (∀ z z', hermForm Hm (F z) z' = hermForm Hm z (F' z')) → ∃ (u₁ : HolUnif P.A (cubeLB P.A ![𝟙 P.A, w] P.L) P.g) (χ₁ : u₁.Λ → ℂ), u₁.ex = u.ex ∧ u₁.Λ = u.Λ ∧ u₁.IsAH Hm χ₁ ∧ ∀ (l : u₁.Λ) (a b : u.Λ), (a : Fin P.g → ℂ) = l → (b : Fin P.g → ℂ) = F l → χ₁ l = (-1) ^ Ef a b := by
  intro _ _ _ _ P u Hm χ Ef w F F' ⟨hH, hpos, hχ, hfr⟩ hE hw hFF hadj
  classical
  have hv : ValueRules := GlobalTheory.valAt'_rules
  have hF : ∀ l ∈ u.Λ, F l ∈ u.Λ := fun l hl => by
    have h0 := hw 0
    rw [map_zero, ex_zero] at h0
    rw [← u.ker, hw, (u.ker l).2 hl, ← h0]
  have hsc := fun l m => semicharacter_rule hv P.isLB u hH χ hfr l m _ (hE l m)
  have hχ0 : ∀ l, χ l ≠ 0 := fun l h => by simpa [h] using hχ l
  let Y : Fin 2 → (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ) := ![LinearMap.id, F]
  have hy : ∀ k z, u.ex z ≫ (![𝟙 P.A, w] : Fin 2 → _) k = u.ex (Y k z) := by
    intro k z
    fin_cases k
    · exact Category.comp_id _
    · exact (hw z).symm
  let p : ULift.{0} (Finset (Fin 2)) → (Fin P.g → ℂ) → (Fin P.g → ℂ) := fun I z => ∑ k ∈ I.down, Y k z
  have hpd : ∀ I, Differentiable ℂ (p I) := fun I =>
    Differentiable.fun_sum fun k _ => (LinearMap.toContinuousLinearMap (Y k)).differentiable
  have hps : ∀ (I : ULift.{0} (Finset (Fin 2))) z,
      (u.ex z).left ≫ (psum P.A ![𝟙 P.A, w] I.down).left = (u.ex (p I z)).left := fun I z => by
    rw [← Over.comp_left, comp_psum u (u.ex z) _ (fun k => Y k z) (fun k => hy k z)]
  refine ⟨combUnif u _ p hpd _ hps, fun l : u.Λ => (-1) ^ Ef l ⟨F l, hF l l.2⟩, rfl, rfl,
    ⟨hH, hpos, fun l => by simp [norm_zpow], ?_⟩, ?_⟩
  · intro (l : u.Λ) j z hz
    have hc : ∀ I, ⊤ ≤ (u.ex (p I z)).left ⁻¹ᵁ P.L.U (j I) := fun I => by
      rw [← hps]; exact (le_preimage_wchart (u.ex z).left P.L _ j).1 hz I
    change ∏ I, u.fr (j I) (p I z) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      (-1) ^ Ef l ⟨F l, hF l l.2⟩ *
        Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) *
        ∏ I, u.fr (j I) (p I (z + l)) ^ ((-1 : ℤ) ^ (2 - I.down.card))
    rw [prod_finset_fin_two fun I => u.fr (j ⟨I⟩) (p ⟨I⟩ z) ^ ((-1 : ℤ) ^ (2 - I.card)),
      prod_finset_fin_two fun I => u.fr (j ⟨I⟩) (p ⟨I⟩ (z + l)) ^ ((-1 : ℤ) ^ (2 - I.card))]
    have p0 : ∀ x, p ⟨∅⟩ x = 0 := fun x => by simp [p]
    have p1 : ∀ x, p ⟨{0}⟩ x = x := fun x => by simp [p, Y]
    have p2 : ∀ x, p ⟨{1}⟩ x = F x := fun x => by simp [p, Y]
    have p3 : ∀ x, p ⟨{0, 1}⟩ x = x + F x := fun x => by simp [p, Y]
    have c1 := hc ⟨{0}⟩
    have c2 := hc ⟨{1}⟩
    have c3 := hc ⟨{0, 1}⟩
    rw [p1] at c1
    rw [p2] at c2
    rw [p3] at c3
    have e1 := hfr l _ _ c1
    have e2 := hfr ⟨F l, hF l l.2⟩ _ _ c2
    have e3 := hfr (l + ⟨F l, hF l l.2⟩) _ _ c3
    rw [hsc] at e3
    have k2 : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
    have s3 : z + F z + ((l + ⟨F l, hF l l.2⟩ : u.Λ) : Fin P.g → ℂ) = z + l + F (z + l) := by
      simp only [Submodule.coe_add, map_add (f := _)]; abel
    rw [s3] at e3
    have hsum : ∀ x y, hermForm Hm x (F y) + hermForm Hm (F x) y = hermForm Hm x y := fun x y => by
      rw [hadj, ← herm_add_right]
      exact congrArg _ (LinearMap.congr_fun hFF y)
    change _ = _ * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * _ at e1
    change _ = _ * Complex.exp (Real.pi * hermForm Hm (F z) (F l) +
      Real.pi / 2 * hermForm Hm (F l) (F l)) * u.fr _ (F z + F l) at e2
    change _ = _ * Complex.exp (Real.pi * hermForm Hm (z + F z) (l + F l) +
      Real.pi / 2 * hermForm Hm (l + F l) (l + F l)) * _ at e3
    rw [← map_add (f := _)] at e2
    have hx : Real.pi * hermForm Hm (z + F z) (l + F l) +
        Real.pi / 2 * hermForm Hm (l + F l) (l + F l) =
        (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) +
        (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) +
        (Real.pi * hermForm Hm (F z) (F l) + Real.pi / 2 * hermForm Hm (F l) (F l)) := by
      simp only [herm_add_left, herm_add_right]
      linear_combination (Real.pi : ℂ) * hsum z l + (Real.pi / 2 : ℂ) * hsum l l
    rw [hx, Complex.exp_add, Complex.exp_add (_ + _) (_ + _)] at e3
    simp only [p0, p1, p2, p3, k2, Finset.card_empty, Finset.card_singleton]
    rw [e1, e2, e3]
    have n1 := hχ0 l
    have n2 := hχ0 ⟨F l, hF l l.2⟩
    norm_num
    field_simp
  · intro (l : u.Λ) a b ha hb
    obtain rfl : a = l := Subtype.ext ha
    obtain rfl : b = ⟨F a, hF a a.2⟩ := Subtype.ext hb
    rfl

end GlobalTheory.PulledBiextFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientExistsUniqueCompEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem quotient_existsUnique_comp_eq :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (T : Scheme.{0}) (f : X ⟶ T), (∀ g, (ρ g).asIso.hom ≫ f = f) → ∃! f' : X' ⟶ T, π ≫ f' = f := by
  intro Γ _ _ X X' ρ π ⟨hπ, hinv, hV⟩ T f hf

  have hq : IsAffineQuotient ρ π :=
    { comp_eq := hinv
      isAffineHom := hπ
      app_injective := fun W => (hV W).1
      mem_range_app := fun W s hs => (hV W).2 s (fun g _ => by obtain ⟨_, e⟩ := hs g; exact e) }
  exact hq.existsUnique_comp_eq f hf

end GlobalTheory
end

