module

public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0636
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellMassIntegrableNearNondegenerateZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicSectionOfRapidCauchyDbar
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem ofReal_sq_sub_mul_le (x y z : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ENNReal.ofReal (‖x - y‖ ^ 2 * ρ) ≤
      2 * ENNReal.ofReal (‖z - x‖ ^ 2 * ρ) + 2 * ENNReal.ofReal (‖z - y‖ ^ 2 * ρ) := by
  have h1 : ‖x - y‖ ≤ ‖z - x‖ + ‖z - y‖ := by
    calc ‖x - y‖ = ‖(z - y) - (z - x)‖ := by congr 1; ring
      _ ≤ ‖z - y‖ + ‖z - x‖ := norm_sub_le _ _
      _ = ‖z - x‖ + ‖z - y‖ := add_comm _ _
  have h2 : ‖x - y‖ ^ 2 ≤ 2 * ‖z - x‖ ^ 2 + 2 * ‖z - y‖ ^ 2 := by
    nlinarith [norm_nonneg (x - y), norm_nonneg (z - x), norm_nonneg (z - y),
      sq_nonneg (‖z - x‖ - ‖z - y‖)]
  have h3 : ‖x - y‖ ^ 2 * ρ ≤ 2 * (‖z - x‖ ^ 2 * ρ) + 2 * (‖z - y‖ ^ 2 * ρ) := by
    have := mul_le_mul_of_nonneg_right h2 hρ
    linarith
  calc ENNReal.ofReal (‖x - y‖ ^ 2 * ρ)
      ≤ ENNReal.ofReal (2 * (‖z - x‖ ^ 2 * ρ) + 2 * (‖z - y‖ ^ 2 * ρ)) := ENNReal.ofReal_le_ofReal h3
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num)]
      simp

theorem exists_isSec_of_rapid_cauchy : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (t K : ℝ) (F : ℕ → ι → Y → ℂ), 0 < t → CurvGe C la t → 0 ≤ K → (∀ m, A.IsSSec (A.kap + la) (F m)) → (∀ m, n0 A la (F m - F (m + 1)) ≤ ENNReal.ofReal (K / 4 ^ m)) → Tendsto (fun m => n1 C la (F m)) atTop (𝓝 0) → ∃ G : ι → Y → ℂ, A.IsSec (A.kap + la) G ∧ n0 A la (F 0 - G) ≤ ENNReal.ofReal (4 * K) := by
  intro n Y _ _ _ _ _ ι La _ A C la t K F ht hcurv hK hF hcau hn1
  obtain ⟨f, hfc, hfm, hfn⟩ := _root_.GlobalTheory.L2Limit.exists_l2_limit n Y ι La A la F K hK hF hcau

  have hWsub : ∀ a, ball (C.c a) (C.r a) ⊆ (A.chart (C.idx a)).target :=
    fun a => ball_subset_closedBall.trans (C.sub a)

  have hH : ∀ m a, ∃ u : V n → ℂ, DifferentiableOn ℂ u (ball (C.c a) (C.r a)) ∧
      ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) ≤ ENNReal.ofReal t⁻¹ * n1 C la (F m) := by
    intro m a
    obtain ⟨u, hu, hle⟩ := _root_.GlobalTheory.HormanderBall.hormander_ball n (C.c a) (C.r a) t
      (fun w => A.ph la (C.idx a) ((A.chart (C.idx a)).symm w)) (F m (C.idx a) ∘ (A.chart (C.idx a)).symm) ht
      ((A.smooth_ph la (C.idx a)).mono (hWsub a)) (((hF m).1 (C.idx a)).mono (hWsub a))
      (by
        intro v hv ξ
        have := hcurv a v hv ξ
        simp only [WeightedAtlas.leviAt] at this
        rwa [(A.chart (C.idx a)).right_inv (hWsub a hv)] at this)
    refine ⟨u, hu, hle.trans ?_⟩
    gcongr
    unfold n1
    exact Finset.single_le_sum (f := fun a => ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
      ((∑ j, ‖wdb n j (F m (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) (fun _ _ => bot_le) (Finset.mem_univ a)
  choose u hu hule using hH

  have hD : ∀ m a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) -
      f (C.idx a) ((A.chart (C.idx a)).symm v)‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))
      ≤ ENNReal.ofReal (4 * K / 4 ^ m) := by
    intro m a
    have e := _root_.GlobalTheory.OTY.lintegral_nsq_chart_part n Y ι La A la (C.idx a) (ball (C.c a) (C.r a)) (F m - f) measurableSet_ball (hWsub a)
      (by
        intro y hy _
        simp only [Pi.sub_apply]
        rw [(hF m).2 _ _ _ (A.mem_pick y) hy, hfc _ _ _ (A.mem_pick y) hy]
        ring)
      (((((hF m).1 (C.idx a)).continuousOn.aemeasurable (A.chart (C.idx a)).open_target.measurableSet).sub
        (hfm (C.idx a))).mono_measure (Measure.restrict_mono (hWsub a) le_rfl))
    refine le_trans (le_of_eq e.symm) ?_
    exact (setLIntegral_le_lintegral _ _).trans (hfn m)
  have hT : Tendsto (fun m : ℕ => 2 * ENNReal.ofReal (4 * K / 4 ^ m) +
      2 * (ENNReal.ofReal t⁻¹ * n1 C la (F m))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => ENNReal.ofReal (4 * K / 4 ^ m)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal
        (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)))
    have h2 : Tendsto (fun m => ENNReal.ofReal t⁻¹ * n1 C la (F m)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hn1 (Or.inr ENNReal.ofReal_ne_top)
    simpa using (ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofNat_ne_top)).add
      (ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofNat_ne_top))

  have hG : ∀ a, ∃ g : V n → ℂ, DifferentiableOn ℂ g (ball (C.c a) (C.r a)) ∧
      g =ᵐ[volume.restrict (ball (C.c a) (C.r a))] f (C.idx a) ∘ (A.chart (C.idx a)).symm := by
    intro a
    have hρ : ContinuousOn (fun v => Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))
        (ball (C.c a) (C.r a)) :=
      Real.continuous_exp.comp_continuousOn
        (((A.smooth_ph la (C.idx a)).continuousOn.mono (hWsub a)).neg)
    refine _root_.GlobalTheory.L2LimitHolomorphic.exists_holo_ae_eq n (ball (C.c a) (C.r a)) _ (fun m => u m a)
      (f (C.idx a) ∘ (A.chart (C.idx a)).symm) isOpen_ball hρ (fun v _ => Real.exp_pos _)
      (fun m => hu m a) ((hfm (C.idx a)).mono_measure (Measure.restrict_mono (hWsub a) le_rfl)) ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => bot_le) ?_
    intro m
    have hY : AEMeasurable (fun v => 2 * ENNReal.ofReal
        (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u m a v‖ ^ 2 *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))))
        (volume.restrict (ball (C.c a) (C.r a))) := by
      refine AEMeasurable.const_mul ?_ _
      refine ContinuousOn.aemeasurable ?_ measurableSet_ball
      refine ENNReal.continuous_ofReal.comp_continuousOn ?_
      refine ContinuousOn.mul ?_ hρ
      refine ContinuousOn.pow ?_ 2
      refine ContinuousOn.norm ?_
      exact ((((hF m).1 (C.idx a)).continuousOn.mono (hWsub a))).sub (hu m a).continuousOn
    calc ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖(f (C.idx a) ∘ (A.chart (C.idx a)).symm) v - u m a v‖ ^ 2 *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))
        ≤ ∫⁻ v in ball (C.c a) (C.r a), (2 * ENNReal.ofReal
            (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - f (C.idx a) ((A.chart (C.idx a)).symm v)‖ ^ 2 *
              Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) +
          2 * ENNReal.ofReal (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u m a v‖ ^ 2 *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) :=
          lintegral_mono (fun v => ofReal_sq_sub_mul_le _ _ _ _ (Real.exp_pos _).le)
      _ = 2 * (∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
            (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - f (C.idx a) ((A.chart (C.idx a)).symm v)‖ ^ 2 *
              Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) +
          2 * (∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
            (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u m a v‖ ^ 2 *
              Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) := by
          rw [lintegral_add_right' _ hY, lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
      _ ≤ 2 * ENNReal.ofReal (4 * K / 4 ^ m) + 2 * (ENNReal.ofReal t⁻¹ * n1 C la (F m)) := by
          gcongr
          · exact hD m a
          · exact hule m a
  choose g hg hgae using hG
  obtain ⟨G, hGs, hGae⟩ := _root_.GlobalTheory.AeHoloGlue.main n Y ι La A C (A.kap + la) f g hfc hg hgae
  refine ⟨G, hGs, ?_⟩
  have e : n0 A la (F 0 - G) = n0 A la (F 0 - f) := by
    unfold n0
    apply lintegral_congr_ae
    filter_upwards [hGae] with y hy
    simp only [WeightedAtlas.nsq, Pi.sub_apply, hy]
  rw [e]
  simpa using hfn 0

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerBoundaryEtaleCohomology
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem hk_pull_ext : ∀ (R : Type) [CommRing R] {K L : Cx R} (f : L ⟶ K) {F G : Shv R} {n : ℤ} (z : Cocycle (res R F) (res R G) n) (m k : ℤ) (h : m + n = k) (x : HK R K F m),
  HK.pull R f G k (HK.ext R K z m k h x) = HK.ext R L z m k h (HK.pull R f F m x) := by
  intro R _ K L f F G n z m k h x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem kummer_boundary : ∀ (q : ℕ) [NeZero q], ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) ∧ ∃ bd : ∀ (E : Spc) (n : ℤ), H ℤ E Gm n →+ Ht q E (n + 1) 1, (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → ∀ (n : ℤ) x, pull _ f _ _ (bd E' n x) = bd E n (pull _ f _ _ x)) ∧ (∀ (E : Spc), Inv q E → ∀ n : ℤ, Function.Exact (HK.post ℤ ((chains ℤ).obj E) ((q : ℤ) • 𝟙 Gm) n) (bd E n) ∧ Function.Exact (bd E n) (fun c => HK.post ℤ ((chains ℤ).obj E) κ (n + 1) (restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) c)) ∧ Function.Exact (fun c => HK.post ℤ ((chains ℤ).obj E) κ (n + 1) (restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) c)) (HK.post ℤ ((chains ℤ).obj E) ((q : ℤ) • 𝟙 Gm) (n + 1))) ∧ (∃ s : ℤˣ, ∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → bd (sch.obj X) 0 (secClass Gm (unitSec u)) = s • kum q u) ∧ ∃ s : ℤˣ, ∀ (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → bd E 1 (picClass L) = s • c1 q L := by
  intro q _
  obtain ⟨κ, hmono, h0, hgen, hker, hloc⟩ := GlobalTheory.T.kummer_sequence_etale_tateTwist q
  refine ⟨κ, hgen, ?_⟩
  let S : ShortComplex (Shv ℤ) := ShortComplex.mk κ (cokernel.π κ) (cokernel.condition κ)
  have hS : S.ShortExact :=
    { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel κ), mono_f := hmono, epi_g := (inferInstance : Epi (cokernel.π κ)) }
  obtain ⟨z, hex, s, hchar⟩ := GlobalTheory.T.exists_connecting_cocycle_hypercohomology_les ℤ S hS
  set qb := cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0 with hqb
  have hπq : cokernel.π κ ≫ qb = (q : ℤ) • 𝟙 Gm := cokernel.π_desc _ _ _
  have hbij := GlobalTheory.T.kummer_cokernel_to_multiplicativeGroup_bijective q κ h0 hker hloc
  have hP : ∀ E, Inv q E → ∀ n, Function.Bijective (HK.post ℤ ((chains ℤ).obj E) qb n) := fun E hE n =>
    GlobalTheory.T.etaleCohomology_bijective_of_support_bijective ℤ E qb (fun U hU => hbij U (hE U hU)) n
  have hR : ∀ E n, Function.Bijective (restrH (Int.castRingHom (ZMod q)) E (tw q 1) n) := fun E n =>
    GlobalTheory.T.etaleCohomology_coefficientRing_invariance ℤ (ZMod q) _ E (tw q 1) n
  have hpostc : ∀ (K : Cx ℤ) n x, HK.post ℤ K ((q : ℤ) • 𝟙 Gm) n x = HK.post ℤ K qb n (HK.post ℤ K (cokernel.π κ) n x) := by
    intro K n x
    rw [← hπq]
    exact (GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ K n).2.1 _ _ x
  let Pe : ∀ E, Inv q E → ∀ n, H ℤ E (cokernel κ) n ≃+ H ℤ E Gm n := fun E hE n =>
    AddEquiv.ofBijective (HK.post ℤ _ qb n) (hP E hE n)
  let Re : ∀ E n, Ht q E n 1 ≃+ H ℤ E ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) n := fun E n =>
    AddEquiv.ofBijective (restrH _ E (tw q 1) n) (hR E n)
  have hPe : ∀ E hE n x, Pe E hE n x = HK.post ℤ _ qb n x := fun _ _ _ _ => rfl
  have hRe : ∀ E n x, Re E n x = restrH _ E (tw q 1) n x := fun _ _ _ => rfl
  classical
  let bd : ∀ (E : Spc) (n : ℤ), H ℤ E Gm n →+ Ht q E (n + 1) 1 := fun E n =>
    if hE : Inv q E then
      (Re E (n + 1)).symm.toAddMonoidHom.comp ((HK.ext ℤ _ z n (n + 1) rfl).comp (Pe E hE n).symm.toAddMonoidHom)
    else 0
  have hbd : ∀ E (hE : Inv q E) n x, bd E n x = (Re E (n + 1)).symm (HK.ext ℤ _ z n (n + 1) rfl ((Pe E hE n).symm x)) := by
    intro E hE n x
    simp only [bd, dif_pos hE]
    rfl
  refine ⟨bd, ?_, ?_, ?_, ?_⟩
  · intro E E' f hE' n x
    have hE : Inv q E := fun U ⟨y⟩ => hE' U ⟨(f.app _).app _ y⟩
    rw [hbd E hE, hbd E' hE']
    apply (Re E (n + 1)).injective
    rw [AddEquiv.apply_symm_apply, hRe]
    have h1 : restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) (pull _ f _ _ ((Re E' (n + 1)).symm
        (HK.ext ℤ _ z n (n + 1) rfl ((Pe E' hE' n).symm x)))) =
        pull _ f _ _ (restrH (Int.castRingHom (ZMod q)) E' (tw q 1) (n + 1) ((Re E' (n + 1)).symm
        (HK.ext ℤ _ z n (n + 1) rfl ((Pe E' hE' n).symm x)))) :=
      ((restrMap (Int.castRingHom (ZMod q)) (tw q 1)).op.nat f (n + 1) _).symm
    rw [h1, ← hRe, AddEquiv.apply_symm_apply]
    have h2 : HK.pull ℤ ((chains ℤ).map f) (cokernel κ) n ((Pe E' hE' n).symm x) = (Pe E hE n).symm (pull _ f _ _ x) := by
      apply (Pe E hE n).injective
      rw [AddEquiv.apply_symm_apply, hPe E hE n]
      change HK.post ℤ _ qb n (HK.pull ℤ ((chains ℤ).map f) _ n _) = HK.pull ℤ ((chains ℤ).map f) _ n x
      rw [← (GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ _ n).2.2.2.2 ((chains ℤ).map f) qb, ← hPe E' hE', AddEquiv.apply_symm_apply]
    change HK.pull ℤ _ _ _ (HK.ext ℤ _ z n (n + 1) rfl _) = _
    rw [hk_pull_ext, h2]
  · intro E hE n
    obtain ⟨e1, e2, e3⟩ := hex ((chains ℤ).obj E) n
    obtain ⟨e1', -, -⟩ := hex ((chains ℤ).obj E) (n + 1)
    refine ⟨fun y => ?_, fun c => ?_, fun y => ?_⟩
    · rw [hbd E hE, AddEquivClass.map_eq_zero_iff, e2]
      constructor
      · rintro ⟨w, hw⟩
        refine ⟨w, ?_⟩
        rw [hpostc, ← hPe E hE, hw]
        exact AddEquiv.apply_symm_apply _ _
      · rintro ⟨w, rfl⟩
        refine ⟨w, ?_⟩
        change _ = (Pe E hE n).symm _
        rw [hpostc, ← hPe E hE, AddEquiv.symm_apply_apply]
    · change HK.post ℤ _ κ (n + 1) (restrH _ E (tw q 1) (n + 1) c) = 0 ↔ _
      rw [show HK.post ℤ _ κ (n + 1) = HK.post ℤ _ S.f (n + 1) from rfl, e3]
      constructor
      · rintro ⟨w, hw⟩
        refine ⟨(Pe E hE n) w, ?_⟩
        rw [hbd E hE, AddEquiv.symm_apply_apply]
        apply (Re E (n + 1)).injective
        rw [AddEquiv.apply_symm_apply, hw, hRe]
      · rintro ⟨w, rfl⟩
        refine ⟨(Pe E hE n).symm w, ?_⟩
        rw [hbd E hE, ← hRe, AddEquiv.apply_symm_apply]
    · rw [hpostc]
      have : HK.post ℤ _ qb (n + 1) (HK.post ℤ _ (cokernel.π κ) (n + 1) y) = 0 ↔ HK.post ℤ _ (cokernel.π κ) (n + 1) y = 0 := by
        rw [← hPe E hE]; exact (Pe E hE (n + 1)).map_eq_zero_iff
      rw [this, show HK.post ℤ _ (cokernel.π κ) (n + 1) = HK.post ℤ _ S.g (n + 1) from rfl, e1']
      constructor
      · rintro ⟨w, rfl⟩
        refine ⟨(Re E (n + 1)).symm w, ?_⟩
        change HK.post ℤ _ κ (n + 1) (Re E (n + 1) _) = _
        rw [AddEquiv.apply_symm_apply]
      · rintro ⟨c, rfl⟩
        exact ⟨_, rfl⟩
  · refine ⟨s, fun X u hu => ?_⟩
    have hE : Inv q (sch.obj X) := by
      rintro U ⟨x⟩
      have := hu.map x.appTop.hom
      rw [map_natCast] at this
      exact this
    obtain ⟨c, hc⟩ := (hbij X hu).2 (unitSec u)
    have hpre : (Pe _ hE 0).symm (secClass Gm (unitSec u)) = secClass (cokernel κ) c := by
      apply (Pe _ hE 0).injective
      rw [AddEquiv.apply_symm_apply, hPe _ hE 0, (GlobalTheory.T.degreeZeroSectionClass_properties ℤ (cokernel κ) X).2.2.2.2 qb c, hc]
    rw [hbd _ hE, hpre, GlobalTheory.T.kummerConnecting_unitClass_eq_kummerClass q κ h0 hmono hgen hker hloc hbij z s hchar X u c hu hc, Units.smul_def, Units.smul_def,
      map_zsmul, ← hRe, AddEquiv.symm_apply_apply]
  · refine ⟨s, fun E L hE => ?_⟩
    have hy : HK.post ℤ _ qb 1 ((Pe E hE 1).symm (picClass L)) = picClass L := by
      rw [← hPe E hE, AddEquiv.apply_symm_apply]
    rw [hbd E hE, GlobalTheory.T.kummerBoundary_lineBundle_firstChernClass q κ h0 hmono hgen hker hloc hbij z s hchar E L hE _ hy, Units.smul_def, Units.smul_def,
      map_zsmul, ← hRe, AddEquiv.symm_apply_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHolomorphicExtensionNearZeros
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma continuous_sqn_of_isSec' {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*}
    [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La) {L : La} {N : ℕ} {s : Fin N → ι → Y → ℂ}
    (hs : ∀ k, A.IsSec L (s k)) : Continuous (A.sqn L s) := by
  have hsum : A.sqn L s = fun y => ∑ k, A.nsq L (s k) y := by
    funext y
    rfl
  rw [hsum]
  refine continuous_finsetSum _ fun k _ => ?_
  have hk : A.IsSecOn L Set.univ (s k) := hs k
  exact continuousOn_univ.mp (_root_.ReciprocityTheory.L2DbarEstimates.Y.api_nsq_contOn A isOpen_univ hk)

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma mem_zeroSet_of_sqn_eq_zero {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*}
    [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La) {L : La} {N : ℕ} (s : Fin N → ι → Y → ℂ) {y : Y}
    (hy : A.sqn L s y = 0) : y ∈ A.zeroSet s := by
  have hy' : ∑ k, A.nsq L (s k) y = 0 := hy
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => A.nsq_nonneg L (s k) y)] at hy'
  simp only [_root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zeroSet, Set.mem_setOf_eq]
  intro k
  have hk : ‖s k (A.pick y) y‖ ^ 2 * Real.exp (-A.ph L (A.pick y) y) = 0 :=
    hy' k (Finset.mem_univ _)
  have h2 := (mul_eq_zero.mp hk).resolve_right (Real.exp_pos _).ne'
  simpa using h2

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma lintegral_le_sum_of_pairwiseDisjoint_pieces {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (Z : Finset Y) (V W : Y → Set Y) (hd : (↑Z : Set Y).PairwiseDisjoint V)
    (hV : ∀ P ∈ Z, MeasurableSet (V P)) (hVW : ∀ P ∈ Z, V P ⊆ W P) (F : Y → ℝ≥0∞)
    (G : Y → Y → ℝ≥0∞) (hF0 : ∀ y, y ∉ ⋃ P ∈ Z, V P → F y = 0)
    (hFG : ∀ P ∈ Z, ∀ y ∈ V P, F y = G P y) :
    ∫⁻ y, F y ∂ν ≤ ∑ P ∈ Z, ∫⁻ y in W P, G P y ∂ν := by
  rw [← setLIntegral_eq_of_support_subset (s := ⋃ P ∈ Z, V P), lintegral_biUnion_finset hd hV]
  · refine Finset.sum_le_sum fun P hP => ?_
    rw [setLIntegral_congr_fun (hV P hP) (fun y hy => hFG P hP y hy)]
    exact lintegral_mono_set (hVW P hP)
  · intro y hy
    by_contra hyn
    exact hy (hF0 y hyn)

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma resSq_nonneg {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*}
    [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La) (E L : La) (s : Fin n → ι → Y → ℂ) (P : Y) (c : ℂ) :
    0 ≤ _root_.GlobalTheory.Published.L2Extension.resSq A E L s P c := by
  unfold _root_.GlobalTheory.Published.L2Extension.resSq
  positivity


open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
theorem _root_.GlobalTheory.OTY.exists_local_extension : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La), 1 ≤ n → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ hS : (A.zeroSet s).Finite, (∀ P ∈ A.zeroSet s, _root_.GlobalTheory.Published.L2Extension.jacAt A s P ≠ 0) → ∀ (f : Y → ℂ) (δ : ℝ), 0 < δ → ∃ (Ω : Set Y) (h : ι → Y → ℂ) (m : ℝ), (IsOpen Ω ∧ A.IsSecOn (A.kap + E) Ω h ∧ (∀ i y, y ∉ Ω → h i y = 0)) ∧ 0 < m ∧ (∀ y, A.sqn L s y < m → y ∈ Ω) ∧ (∀ P ∈ A.zeroSet s, h (A.pick P) P = f P) ∧ (∀ T : ℝ, 2 ≤ T → ∫⁻ y in {y | -T - 1 ≤ δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y ∧ δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)) ∂A.mu ≤ ENNReal.ofReal (62 / 30 * (Real.pi ^ n / ((n - 1).factorial : ℝ)) / δ * ∑ P ∈ hS.toFinset, _root_.GlobalTheory.Published.L2Extension.resSq A E L s P (f P))) ∧ ∫⁻ y, ENNReal.ofReal (1 / (1 + (δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y) ^ 2) * A.nsq (A.kap + E) h y * Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)) ∂A.mu < ⊤ := by
  intro n Y _ _ _ _ _ _ ι La _ A hn E L s hs hS hjac f δ hδ
  choose! N hNo hPN hNsub hNT hNfin using fun P (hP : P ∈ A.zeroSet s) =>
    _root_.GlobalTheory.OTY.ShellZero.shell_near_zero n Y ι La A hn E L s hs P hP (hjac P hP) (f P) δ hδ
  obtain ⟨U, hU, hUd⟩ := hS.t2_separation
  set Z := hS.toFinset with hZ
  have hmemZ : ∀ {P}, P ∈ Z → P ∈ A.zeroSet s := fun hP => hS.mem_toFinset.mp hP
  have hd : (↑Z : Set Y).PairwiseDisjoint (fun P => N P ∩ U P) := by
    intro P hP Q hQ hPQ
    exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right
      (hUd (hmemZ (Finset.mem_coe.mp hP)) (hmemZ (Finset.mem_coe.mp hQ)) hPQ)
  have hVo : ∀ P ∈ Z, IsOpen (N P ∩ U P) := fun P hP => (hNo P (hmemZ hP)).inter (hU P).2
  obtain ⟨h, hh⟩ : ∃ h : ι → Y → ℂ, h = fun i y =>
      ∑ P ∈ Z, (N P ∩ U P).indicator (fun y => A.g (A.kap + E) i (A.pick P) y * f P) y :=
    ⟨_, rfl⟩
  have hloc : ∀ P ∈ Z, ∀ y ∈ N P ∩ U P, ∀ i, h i y = A.g (A.kap + E) i (A.pick P) y * f P := by
    intro P hP y hy i
    rw [hh]
    dsimp only
    rw [Finset.sum_eq_single P]
    · exact Set.indicator_of_mem hy _
    · intro Q hQ hQP
      refine Set.indicator_of_notMem (fun hyQ => ?_) _
      exact Set.disjoint_left.mp (hd (Finset.mem_coe.mpr hQ) (Finset.mem_coe.mpr hP) hQP) hyQ hy
    · intro hPn
      exact absurd hP hPn
  have hout : ∀ y, y ∉ ⋃ P ∈ Z, N P ∩ U P → ∀ i, h i y = 0 := by
    intro y hy i
    rw [hh]
    exact Finset.sum_eq_zero fun P hP =>
      Set.indicator_of_notMem (fun hyP => hy (Set.mem_iUnion₂.mpr ⟨P, hP, hyP⟩)) _
  have hZΩ : ∀ y ∈ A.zeroSet s, y ∈ ⋃ P ∈ Z, N P ∩ U P := fun y hy =>
    Set.mem_iUnion₂.mpr ⟨y, hS.mem_toFinset.mpr hy, hPN y hy, (hU y).1⟩
  have hΩo : IsOpen (⋃ P ∈ Z, N P ∩ U P) :=
    isOpen_iUnion fun P => isOpen_iUnion fun hP => hVo P hP
  have hnsq : ∀ P ∈ Z, ∀ y ∈ N P ∩ U P, A.nsq (A.kap + E) h y =
      A.nsq (A.kap + E) (fun i y => A.g (A.kap + E) i (A.pick P) y * f P) y := by
    intro P hP y hy
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq
    rw [hloc P hP y hy]
  have hnsq0 : ∀ y, y ∉ ⋃ P ∈ Z, N P ∩ U P → A.nsq (A.kap + E) h y = 0 := by
    intro y hy
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq
    rw [hout y hy]
    simp
  obtain ⟨m, hm, hmΩ⟩ : ∃ m : ℝ, 0 < m ∧ ∀ y, A.sqn L s y < m → y ∈ ⋃ P ∈ Z, N P ∩ U P := by
    rcases (⋃ P ∈ Z, N P ∩ U P)ᶜ.eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun y _ => ?_⟩
      by_contra hy
      have hyc : y ∈ (⋃ P ∈ Z, N P ∩ U P)ᶜ := hy
      rw [he] at hyc
      exact hyc
    · obtain ⟨x0, hx0, hmin⟩ := hΩo.isClosed_compl.isCompact.exists_isMinOn hne
        (continuous_sqn_of_isSec' A hs).continuousOn
      refine ⟨A.sqn L s x0, lt_of_le_of_ne (A.sqn_nonneg L s x0)
        (fun h0 => hx0 (hZΩ x0 (mem_zeroSet_of_sqn_eq_zero A s h0.symm))), fun y hy => ?_⟩
      by_contra hyΩ
      exact (not_le.mpr hy) (isMinOn_iff.mp hmin y hyΩ)
  refine ⟨⋃ P ∈ Z, N P ∩ U P, h, m, ⟨hΩo, ⟨?_, ?_⟩, fun i y hy => hout y hy i⟩, hm, hmΩ, ?_, ?_, ?_⟩
  · intro i x hx
    obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.mp hx.2
    have hWo : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (N P ∩ U P)) :=
      (A.chart i).isOpen_inter_preimage_symm (hVo P hP)
    have hW : (A.chart i).target ∩ (A.chart i).symm ⁻¹' (N P ∩ U P) ∈ 𝓝 x :=
      hWo.mem_nhds ⟨hx.1, hxP⟩
    have hg : DifferentiableAt ℂ (A.g (A.kap + E) i (A.pick P) ∘ (A.chart i).symm) x := by
      refine ((A.holo_g (A.kap + E) i (A.pick P)).mono ?_).differentiableAt hW
      intro z hz
      unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.ovl
      exact ⟨hz.1, hNsub P (hmemZ hP) hz.2.1⟩
    refine ((hg.mul_const (f P)).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hW] with z hz
    simp only [Function.comp_apply]
    exact hloc P hP _ hz.2 i
  · intro i j y hy hi hj
    obtain ⟨P, hP, hyP⟩ := Set.mem_iUnion₂.mp hy
    rw [hloc P hP y hyP i, hloc P hP y hyP j, ← mul_assoc,
      ← A.g_cocycle _ i j _ y hi hj (hNsub P (hmemZ hP) hyP.1)]
  · intro P hP
    rw [hloc P (hS.mem_toFinset.mpr hP) P ⟨hPN P hP, (hU P).1⟩, A.g_self _ _ (A.mem_pick P),
      one_mul]
  · intro T hT
    refine (lintegral_le_sum_of_pairwiseDisjoint_pieces _ Z (fun P => N P ∩ U P) N hd
      (fun P hP => (hVo P hP).measurableSet) (fun P _ => Set.inter_subset_left) _
      (fun P y => ENNReal.ofReal (A.nsq (A.kap + E)
        (fun i y => A.g (A.kap + E) i (A.pick P) y * f P) y *
          Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)))
      (fun y hy => by simp only [hnsq0 y hy, zero_mul, ENNReal.ofReal_zero])
      (fun P hP y hy => by simp only [hnsq P hP y hy])).trans ?_
    calc _ ≤ ∑ P ∈ Z, ENNReal.ofReal (62 / 30 * (Real.pi ^ n / ((n - 1).factorial : ℝ)) / δ *
          _root_.GlobalTheory.Published.L2Extension.resSq A E L s P (f P)) := by
          refine Finset.sum_le_sum fun P hP => ?_
          rw [Measure.restrict_restrict (hNo P (hmemZ hP)).measurableSet]
          exact hNT P (hmemZ hP) T hT
      _ = _ := by
          rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
          intro P _
          exact mul_nonneg (by positivity) (resSq_nonneg A E L s P (f P))
  · refine lt_of_le_of_lt (lintegral_le_sum_of_pairwiseDisjoint_pieces A.mu Z (fun P => N P ∩ U P) N hd
      (fun P hP => (hVo P hP).measurableSet) (fun P _ => Set.inter_subset_left) _
      (fun P y => ENNReal.ofReal (1 / (1 + (δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y) ^ 2) *
        A.nsq (A.kap + E) (fun i y => A.g (A.kap + E) i (A.pick P) y * f P) y *
          Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)))
      (fun y hy => by simp only [hnsq0 y hy, mul_zero, zero_mul, ENNReal.ofReal_zero])
      (fun P hP y hy => by simp only [hnsq P hP y hy])) ?_
    exact ENNReal.sum_lt_top.2 fun P hP => hNfin P (hmemZ hP)

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpGLiAddSmul
section
noncomputable section

open NumberField

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E]

def expGLi (a : ℕ) (X : Matrix (Fin a) (Fin a) (Cinf E)) : GL (Fin a) (Cinf E) :=
  (Matrix.isUnit_exp X).unit

@[simp] theorem val_expGLi (a : ℕ) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    (expGLi a X).val = NormedSpace.exp X := rfl

theorem expGLi_add_smul (a : ℕ) (X : Matrix (Fin a) (Fin a) (Cinf E)) (s t : ℝ) :
    expGLi a ((s + t) • X) = expGLi a (s • X) * expGLi a (t • X) :=
  Units.ext (by
    rw [Units.val_mul, val_expGLi, val_expGLi, val_expGLi, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t))

@[simp] theorem expGLi_zero (a : ℕ) : expGLi a (0 : Matrix (Fin a) (Fin a) (Cinf E)) = 1 :=
  Units.ext (by rw [val_expGLi, NormedSpace.exp_zero, Units.val_one])

end GlobalTheory.CuspRep
end
end

