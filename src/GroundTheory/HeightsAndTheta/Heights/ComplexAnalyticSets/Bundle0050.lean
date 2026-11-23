module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalGraphMass
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0045

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicInverse
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

namespace InjectiveHolomorphicInverse

theorem analyticAt_of_differentiableOn {k : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin k → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : Fin k → ℂ} (hx : x ∈ U) : AnalyticAt ℂ f x := by
  refine AnalyticAt.pi fun i => ?_
  refine analyticOnNhd_of_continuousOn_of_separately hU
    ((continuous_apply i).comp_continuousOn hf.continuousOn) (fun z hz j => ?_) x hx
  have hfz : DifferentiableAt ℂ (fun w => f w i) z :=
    differentiableAt_pi.mp (hf.differentiableAt (hU.mem_nhds hz)) i
  have hu : DifferentiableAt ℂ (Function.update z j) (z j) :=
    (hasFDerivAt_update z (z j)).differentiableAt
  have hfz' : DifferentiableAt ℂ (fun w => f w i) (Function.update z j (z j)) := by
    rwa [Function.update_eq_self]
  exact hfz'.comp (z j) hu

theorem exists_equiv (hJ : InjectiveHolomorphicJacobianNeZero.Statement) {k : ℕ} {U : Set (Fin k → ℂ)}
    {f : (Fin k → ℂ) → Fin k → ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U)
    {x : Fin k → ℂ} (hx : x ∈ U) :
    ∃ e : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ), HasStrictFDerivAt f (e : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) x := by
  have hdet := hJ k U f hU hf hinj x hx
  refine ⟨(LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv, ?_⟩
  have he : ((LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv :
      (Fin k → ℂ) →L[ℂ] Fin k → ℂ) = fderiv ℂ f x := by
    ext1 v
    rfl
  rw [he]
  exact (analyticAt_of_differentiableOn hU hf hx).hasStrictFDerivAt

theorem proof (hJ : InjectiveHolomorphicJacobianNeZero.Statement) : InjectiveHolomorphicInverse.Statement := by
  intro k U f hU hf hinj
  have hleft : ∀ z ∈ U, Function.invFunOn f U (f z) = z := fun z hz =>
    hinj (Function.invFunOn_mem ⟨z, hz, rfl⟩) hz (Function.invFunOn_eq ⟨z, hz, rfl⟩)
  refine ⟨?_, Function.invFunOn f U, ?_, hleft⟩
  · rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := exists_equiv hJ hU hf hinj hx
    rw [← he.map_nhds_eq_of_equiv]
    exact Filter.image_mem_map (hU.mem_nhds hx)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := exists_equiv hJ hU hf hinj hx
    refine (he.to_local_left_inverse ?_).differentiableAt.differentiableWithinAt
    filter_upwards [hU.mem_nhds hx] with z hz
    exact hleft z hz

end InjectiveHolomorphicInverse

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreLocalUnbranched
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

private theorem germ_zero_of_mul_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {y : E}
    (hf : AnalyticAt ℂ f y) (hg : AnalyticAt ℂ g y) (hfg : ∀ᶠ z in 𝓝 y, f z * g z = 0) :
    (∀ᶠ z in 𝓝 y, f z = 0) ∨ (∀ᶠ z in 𝓝 y, g z = 0) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    ((hf.eventually_analyticAt.and hg.eventually_analyticAt).and hfg)
  by_cases hf0 : ∀ z ∈ Metric.ball y r, f z = 0
  · exact Or.inl (Filter.mem_of_superset (Metric.ball_mem_nhds y hr) hf0)
  · right
    push Not at hf0
    obtain ⟨p, hp, hfp⟩ := hf0
    have hgp : g =ᶠ[𝓝 p] 0 := by
      filter_upwards [(hball hp).1.1.continuousAt.eventually_ne hfp, Metric.isOpen_ball.mem_nhds hp]
        with z hz1 hz2
      exact (mul_eq_zero.1 (hball hz2).2).resolve_left hz1
    have hgan : AnalyticOnNhd ℂ g (Metric.ball y r) := fun z hz => (hball hz).1.2
    have hzero := hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball y r).isPreconnected hp hgp
    exact Filter.mem_of_superset (Metric.ball_mem_nhds y hr) fun z hz => by simpa using hzero hz

private theorem germ_factor_zero_of_prod_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    (h : ι → E → ℂ) {y : E} (s : Finset ι) (han : ∀ i ∈ s, AnalyticAt ℂ (h i) y)
    (hprod : ∀ᶠ z in 𝓝 y, ∏ i ∈ s, h i z = 0) : ∃ i ∈ s, ∀ᶠ z in 𝓝 y, h i z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨z, hz⟩ := hprod.exists
    simp at hz
  | insert a s ha ih =>
    have hg : AnalyticAt ℂ (fun z => ∏ i ∈ s, h i z) y :=
      Finset.analyticAt_fun_prod s fun i hi => han i (Finset.mem_insert_of_mem hi)
    have hprod' : ∀ᶠ z in 𝓝 y, h a z * ∏ i ∈ s, h i z = 0 := by
      filter_upwards [hprod] with z hz
      rwa [Finset.prod_insert ha] at hz
    rcases germ_zero_of_mul_zero (han a (Finset.mem_insert_self a s)) hg hprod' with h1 | h1
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨i, hi, h2⟩ := ih (fun i hi => han i (Finset.mem_insert_of_mem hi)) h1
      exact ⟨i, Finset.mem_insert_of_mem hi, h2⟩

private theorem isOpen_diff_of_zeroSet {σ : Type} [Fintype σ] {Y N : Set (σ → ℂ)} {k : ℕ}
    {φ : Fin k → (σ → ℂ) → ℂ} (hN : IsOpen N) (hφ : ∀ m, AnalyticOnNhd ℂ (φ m) N)
    (hY : Y ∩ N = {z | z ∈ N ∧ ∀ m, φ m z = 0}) : IsOpen (N \ Y) := by
  have hEq : N \ Y = ⋃ m, N ∩ φ m ⁻¹' {0}ᶜ := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hzN, hzY⟩
      by_contra hcon
      push Not at hcon
      have hz : z ∈ Y ∩ N := by
        rw [hY]
        exact ⟨hzN, fun m => hcon m hzN⟩
      exact hzY hz.1
    · rintro ⟨m, hzN, hzm⟩
      refine ⟨hzN, fun hzY => hzm ?_⟩
      have hz : z ∈ Y ∩ N := ⟨hzY, hzN⟩
      rw [hY] at hz
      exact hz.2 m
  rw [hEq]
  exact isOpen_iUnion fun m => (hφ m).continuousOn.isOpen_inter_preimage hN isOpen_compl_singleton

theorem IsolatedFibreLocalUnbranched.proof (hcomp : OpenProjectionDominantComponents.Statement)
    (hmeet : IrreducibleGermMeetOverHypersurface.Statement)
    (hprim : IrreducibleGermPrimitiveForm.Statement)
    (hsheet : PrimitiveFormSheetedOffDiscriminant.Statement) :
    IsolatedFibreLocalUnbranched.Statement := by
  classical
  intro σ _ X B k f d A hB hf hXB hopen w hw hiso
  obtain ⟨n, Y, hY, hsepY, W0, hW0, hXW0⟩ := hcomp σ X B k f d A hB hf hXB hopen w hw
  obtain ⟨W, hW, hWiso⟩ := hiso

  have hisoY : ∀ i, ∃ W' ∈ 𝓝 w, ∀ x ∈ Y i ∩ W', A x = A w → x = w := fun i =>
    ⟨W ∩ W0, inter_mem hW hW0, fun x hx hAx => by
      have hxX : x ∈ X ∩ B ∩ W0 := by
        rw [hXW0]
        exact ⟨Set.mem_iUnion.2 ⟨i, hx.1⟩, hx.2.2⟩
      exact hWiso x ⟨hxX.1, hx.2.1⟩ hAx⟩

  have hsh : ∀ i, ∃ δ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ δ (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) ∧
      ∃ M ∈ 𝓝 w, ∀ y ∈ Y i ∩ M, δ (A y) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
        (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ y ∈ V ∧ AnalyticOnNhd ℂ g O ∧
          (∀ t ∈ O, A (g t) = t) ∧ Y i ∩ V = g '' O := by
    intro i
    obtain ⟨ℓ, N, a, δ, q, ha, hδ, hq, hδ0, hP, hsep, hQ⟩ :=
      hprim σ (Y i) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY i).2.2
    exact ⟨δ, hδ, hδ0,
      hsheet σ (Y i) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY i).2.2 ℓ N a δ q ha hδ hq hδ0 hP hsep hQ⟩
  choose δ hδa hδ0 M hM hMsh using hsh

  have hsp : ∀ i j, ∃ e : (Fin d → ℂ) → ℂ, AnalyticAt ℂ e (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), e y = 0) ∧
      (i ≠ j → ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j → e (A z) = 0) := by
    intro i j
    by_cases hij : i = j
    · refine ⟨fun _ => 1, analyticAt_const, fun h => ?_, fun h => absurd hij h⟩
      obtain ⟨y, hy⟩ := h.exists
      exact one_ne_zero hy
    · obtain ⟨e, he, he0, hez⟩ :=
        hmeet σ (Y i) (Y j) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY j).1 (hsepY i j hij)
      exact ⟨e, he, he0, fun _ => hez⟩
  choose e hea he0 hez using hsp

  have hYa : ∀ j, ∃ (N : Set (σ → ℂ)) (kk : ℕ) (φ : Fin kk → (σ → ℂ) → ℂ), IsOpen N ∧ w ∈ N ∧
      (∀ m, AnalyticOnNhd ℂ (φ m) N) ∧ Y j ∩ N = {z | z ∈ N ∧ ∀ m, φ m z = 0} := fun j => (hY j).1
  choose N kk φ hNo hwN hφ hYN using hYa
  have hfac : ∀ i, AnalyticAt ℂ (fun y => δ i y * ∏ j, e i j y) (A w) := fun i =>
    (hδa i).mul (Finset.analyticAt_fun_prod _ fun j _ => hea i j)
  refine ⟨interior W0 ∩ (⋂ i, M i) ∩ (⋂ j, N j) ∩
      {z | ∀ i j, i ≠ j → z ∈ Y i → z ∈ Y j → e i j (A z) = 0},
    fun y => ∏ i, (δ i y * ∏ j, e i j y), ?_, Finset.analyticAt_fun_prod _ fun i _ => hfac i, ?_, ?_⟩
  · refine inter_mem (inter_mem (inter_mem (interior_mem_nhds.2 hW0) (iInter_mem.2 hM))
      (iInter_mem.2 fun j => (hNo j).mem_nhds (hwN j))) ?_
    have hev : ∀ i j, ∀ᶠ z in 𝓝 w, i ≠ j → z ∈ Y i → z ∈ Y j → e i j (A z) = 0 := fun i j => by
      by_cases hij : i = j
      · exact Eventually.of_forall fun _ h => absurd hij h
      · filter_upwards [hez i j hij] with z hz _ using hz
    exact eventually_all.2 fun i => eventually_all.2 fun j => hev i j
  · intro hg0
    obtain ⟨i, -, hi⟩ := germ_factor_zero_of_prod_zero (fun i y => δ i y * ∏ j, e i j y) Finset.univ
      (fun i _ => hfac i) hg0
    rcases germ_zero_of_mul_zero (hδa i) (Finset.analyticAt_fun_prod _ fun j _ => hea i j) hi with h1 | h1
    · exact hδ0 i h1
    · obtain ⟨j, -, hj⟩ := germ_factor_zero_of_prod_zero (e i) Finset.univ (fun j _ => hea i j) h1
      exact he0 i j hj
  · intro x hx hgx
    obtain ⟨hxXB, ⟨⟨hxW0, hxM⟩, hxN⟩, hxe⟩ := hx
    simp only [Set.mem_iInter] at hxM hxN
    have hgx' : ∀ i, δ i (A x) ≠ 0 ∧ ∀ j, e i j (A x) ≠ 0 := by
      intro i
      have hi := (Finset.prod_ne_zero_iff.1 hgx) i (Finset.mem_univ i)
      exact ⟨left_ne_zero_of_mul hi,
        fun j => (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hi)) j (Finset.mem_univ j)⟩
    have hxU : x ∈ (⋃ i, Y i) ∩ W0 := by
      rw [← hXW0]
      exact ⟨hxXB, interior_subset hxW0⟩
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxU.1
    have hxnot : ∀ j, j ≠ i → x ∉ Y j := fun j hji hxj =>
      (hgx' i).2 j (hxe i j (Ne.symm hji) hxi hxj)

    let U : Set (σ → ℂ) := interior W0 ∩ ⋂ j, (if j = i then Set.univ else N j \ Y j)
    have hUo : IsOpen U := by
      refine isOpen_interior.inter (isOpen_iInter_of_finite fun j => ?_)
      split_ifs
      · exact isOpen_univ
      · exact isOpen_diff_of_zeroSet (hNo j) (hφ j) (hYN j)
    have hxUm : x ∈ U := by
      refine ⟨hxW0, Set.mem_iInter.2 fun j => ?_⟩
      split_ifs with hji
      · trivial
      · exact ⟨hxN j, hxnot j hji⟩
    have hXU : X ∩ B ∩ U = Y i ∩ U := by
      ext z
      constructor
      · rintro ⟨hzXB, hzU⟩
        have hzW : z ∈ (⋃ i, Y i) ∩ W0 := by
          rw [← hXW0]
          exact ⟨hzXB, interior_subset hzU.1⟩
        obtain ⟨j, hzj⟩ := Set.mem_iUnion.1 hzW.1
        by_cases hji : j = i
        · rw [hji] at hzj
          exact ⟨hzj, hzU⟩
        · have hzj' := Set.mem_iInter.1 hzU.2 j
          rw [if_neg hji] at hzj'
          exact absurd hzj hzj'.2
      · rintro ⟨hzi, hzU⟩
        have hzW : z ∈ X ∩ B ∩ W0 := by
          rw [hXW0]
          exact ⟨Set.mem_iUnion.2 ⟨i, hzi⟩, interior_subset hzU.1⟩
        exact ⟨hzW.1, hzU⟩

    obtain ⟨O, V, h, hO, hV, hxV, hh, hAh, hYV⟩ := hMsh i x ⟨hxi, hxM i⟩ (hgx' i).1
    refine ⟨O ∩ h ⁻¹' U, V ∩ U, h, hh.continuousOn.isOpen_inter_preimage hO hUo, hV.inter hUo,
      ⟨hxV, hxUm⟩, hh.mono Set.inter_subset_left, fun t ht => hAh t ht.1, ?_⟩
    rw [Set.image_inter_preimage, ← hYV]
    ext z
    constructor
    · rintro ⟨hzXB, hzV, hzU⟩
      have hz : z ∈ Y i ∩ U := by
        rw [← hXU]
        exact ⟨hzXB, hzU⟩
      exact ⟨⟨hz.1, hzV⟩, hzU⟩
    · rintro ⟨⟨hzi, hzV⟩, hzU⟩
      have hz : z ∈ X ∩ B ∩ U := by
        rw [hXU]
        exact ⟨hzi, hzU⟩
      exact ⟨hz.1, hzV, hzU⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalGraphProjectionMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Function

open scoped ENNReal

noncomputable section

namespace LocalGraphProjectionMass

variable {n : ℕ}

theorem frameFibreCount_image_repr_map (b c : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (A : Set (EuclideanSpace ℂ (Fin n))) (x : I → ℂ) :
    frameFibreCount (c.map b.repr) I (b.repr '' A) x = frameFibreCount c I A x := by
  have hP : ∀ z, frameProj (c.map b.repr) I (b.repr z) = frameProj c I z := by
    intro z
    funext i
    simp only [frameProj, OrthonormalBasis.map_apply, LinearIsometryEquiv.inner_map_map]
  have h : {y ∈ b.repr '' A | frameProj (c.map b.repr) I y = x} =
      b.repr '' {z ∈ A | frameProj c I z = x} := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      exact ⟨z, ⟨hz, by rwa [hP] at hy⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, by rw [hP]; exact hzx⟩
  simp only [frameFibreCount]
  rw [h, b.repr.injective.injOn.encard_image]

theorem mass_piece_frame (hPF : ProjectionFormula.Statement)
    (b c : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n)) {d : ℕ}
    (hd : I₀.card = d) (Ω : Set (I₀ → ℂ)) (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n))
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (hfix : ∀ w ∈ Ω, frameProj b I₀ (g w) = w)
    (M : Set (EuclideanSpace ℂ (Fin n))) (hM : MeasurableSet M) :
    μH[((2 * d : ℕ) : ℝ)] (g '' Ω ∩ M) =
      ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
        frameFibreCount c I (g '' Ω ∩ M) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) := by
  obtain ⟨m, e, Ω', F, hΩ', hF, himg⟩ := LocalGraphMass.image_repr_eq_graph b I₀ hd Ω g hΩ hg hfix
  have hT : b.repr '' (g '' Ω ∩ M) = graphPt e F '' Ω' ∩ b.repr '' M := by
    rw [Set.image_inter b.repr.injective, himg]
  have hM' : MeasurableSet (b.repr '' M) :=
    b.repr.toHomeomorph.measurableEmbedding.measurableSet_image.2 hM
  have h := hPF d m n e Ω' F hΩ' hF (c.map b.repr) _ hM'
  rw [← hT, b.repr.isometry.hausdorffMeasure_image (Or.inr b.repr.surjective)] at h
  rw [h]
  simp_rw [frameFibreCount_image_repr_map]

theorem lintegral_count_le (U : Matrix (Fin n) (Fin n) ℂ)
    (c : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hc : ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (c i) z = ∑ j, U i j * z j)
    {d : ℕ} (I : Finset (Fin n)) (hI : I.card = d) (A : Set (EuclideanSpace ℂ (Fin n))) :
    ∫⁻ x : EuclideanSpace ℂ I, frameFibreCount c I A (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) ≤
      (⨆ y : EuclideanSpace ℂ (Fin d),
          (({z | z ∈ A ∧ rowsProj U (I.orderEmbOfFin hI) z = y}.encard : ℕ∞) : ℝ≥0∞)) *
        μH[((2 * d : ℕ) : ℝ)] (rowsProj U (I.orderEmbOfFin hI) '' A) := by
  set e := I.orderIsoOfFin hI
  set s : Fin d → Fin n := ⇑(I.orderEmbOfFin hI) with hs
  let φ : EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.toEquiv.symm
  have hφ : ∀ x k, φ x k = x (e k) := fun x k => rfl
  have hrow : ∀ z k, rowsProj U s z k = inner ℂ (c (e k)) z := by
    intro z k
    rw [hc]
    simp [rowsProj, Matrix.mulVec, dotProduct, s, e, Finset.coe_orderIsoOfFin_apply]
  have hiff : ∀ x z, frameProj c I z = WithLp.ofLp x ↔ rowsProj U s z = φ x := by
    intro x z
    constructor
    · intro h
      ext k
      rw [hrow, hφ]
      exact congrFun h (e k)
    · intro h
      funext i
      have := congrArg (fun y : EuclideanSpace ℂ (Fin d) => y (e.symm i)) h
      simp only [hrow, hφ, OrderIso.apply_symm_apply] at this
      exact this
  set T := rowsProj U s '' A
  set N := ⨆ y : EuclideanSpace ℂ (Fin d), (({z | z ∈ A ∧ rowsProj U s z = y}.encard : ℕ∞) : ℝ≥0∞)
  have hle : ∀ x : EuclideanSpace ℂ I, frameFibreCount c I A (WithLp.ofLp x) ≤
      (φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T).indicator (fun _ => N) x := by
    intro x
    have hset : {z ∈ A | frameProj c I z = WithLp.ofLp x} = {z | z ∈ A ∧ rowsProj U s z = φ x} := by
      ext z
      exact and_congr Iff.rfl (hiff x z)
    by_cases hx : φ x ∈ T
    · rw [Set.indicator_of_mem (show x ∈ φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T from
        subset_toMeasurable _ T hx)]
      simp only [frameFibreCount]
      rw [hset]
      exact le_iSup (fun y => (({z | z ∈ A ∧ rowsProj U s z = y}.encard : ℕ∞) : ℝ≥0∞)) (φ x)
    · have h0 : {z ∈ A | frameProj c I z = WithLp.ofLp x} = ∅ := by
        rw [hset]
        exact Set.eq_empty_of_forall_notMem fun z hz => hx ⟨z, hz.1, hz.2⟩
      simp only [frameFibreCount]
      rw [h0]
      simp
  calc _ ≤ ∫⁻ x : EuclideanSpace ℂ I, (φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T).indicator (fun _ => N) x ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        lintegral_mono hle
    _ = N * μH[((2 * d : ℕ) : ℝ)] (φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T) :=
        lintegral_indicator_const ((measurableSet_toMeasurable _ _).preimage φ.continuous.measurable) _
    _ = N * μH[((2 * d : ℕ) : ℝ)] T := by
        rw [φ.isometry.hausdorffMeasure_preimage (Or.inr φ.surjective), φ.surjective.range_eq,
          Set.inter_univ, measure_toMeasurable]

end LocalGraphProjectionMass


open LocalGraphProjectionMass in
theorem LocalGraphProjectionMass.proof (hPF : ProjectionFormula.Statement) :
    LocalGraphProjectionMass.Statement := by
  intro n d b I₀ S hd hS U hU B hB
  classical
  obtain ⟨c, hc⟩ := MassFinite.exists_frame U hU
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hS' : ∀ z : S, ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
      (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ (z : EuclideanSpace ℂ (Fin n)) ∈ V ∧
        DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ S ∩ V = g '' Ω :=
    fun z => hS z z.2
  choose Ω V g hΩ hV hzV hg hfix hSV using hS'
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hV
  have hmemT : ∀ z ∈ S, ∃ i ∈ T, z ∈ V i := by
    intro z hz
    have : z ∈ ⋃ i ∈ T, V i := hTU ▸ Set.mem_iUnion.2 ⟨⟨z, hz⟩, hzV _⟩
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 this
    exact ⟨i, hi, hzi⟩
  have hTne : T.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨i, hi, -⟩ := hmemT z hz
    exact ⟨i, hi⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  let W : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun k => V (f k)
  have hcover : S ⊆ ⋃ k, disjointed W k := by
    intro z hz
    rw [iUnion_disjointed]
    obtain ⟨i, hi, hzi⟩ := hmemT z hz
    rw [hf] at hi
    obtain ⟨k, rfl⟩ := hi
    exact Set.mem_iUnion.2 ⟨k, hzi⟩
  have hDmeas : ∀ k, MeasurableSet (disjointed W k) :=
    MeasurableSet.disjointed fun k => (hV _).measurableSet
  have hpiece : ∀ k, S ∩ B ∩ disjointed W k = g (f k) '' Ω (f k) ∩ (B ∩ disjointed W k) := by
    intro k
    rw [← hSV (f k)]
    ext z
    constructor
    · rintro ⟨⟨hzS, hzB⟩, hzD⟩
      exact ⟨⟨hzS, disjointed_subset W k hzD⟩, hzB, hzD⟩
    · rintro ⟨⟨hzS, -⟩, hzB, hzD⟩
      exact ⟨⟨hzS, hzB⟩, hzD⟩
  have hdisj : Pairwise (Disjoint on fun k => S ∩ B ∩ disjointed W k) :=
    fun i j hij => (disjoint_disjointed W hij).mono Set.inter_subset_right Set.inter_subset_right
  let G : (Fin d → Fin n) → ℝ≥0∞ := fun s =>
    (⨆ x : EuclideanSpace ℂ (Fin d),
        (({z | z ∈ S ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
      μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (S ∩ B))
  calc μH[((2 * d : ℕ) : ℝ)] (S ∩ B)
      ≤ μH[((2 * d : ℕ) : ℝ)] (⋃ k, S ∩ B ∩ disjointed W k) := by
        refine measure_mono fun z hz => ?_
        obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hcover hz.1)
        exact Set.mem_iUnion.2 ⟨k, hz, hk⟩
    _ ≤ ∑' k, μH[((2 * d : ℕ) : ℝ)] (S ∩ B ∩ disjointed W k) := measure_iUnion_le _
    _ = ∑' k, ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount c I (S ∩ B ∩ disjointed W k) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) := by
        congr 1
        funext k
        rw [hpiece k]
        exact mass_piece_frame hPF b c I₀ hd _ _ (hΩ _) (hg _) (hfix _) _ (hB.inter (hDmeas k))
    _ = ∑ I ∈ Finset.univ.powersetCard d, ∑' k, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount c I (S ∩ B ∩ disjointed W k) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ I ∈ Finset.univ.powersetCard d, ⨆ hI : I.card = d, G (I.orderEmbOfFin hI) := by
        refine Finset.sum_le_sum fun I hI => ?_
        have hIc := (Finset.mem_powersetCard.1 hI).2
        refine le_trans ?_ (le_iSup (fun h : I.card = d => G (I.orderEmbOfFin h)) hIc)
        calc _ ≤ ∫⁻ x : EuclideanSpace ℂ I, ∑' k,
              frameFibreCount c I (S ∩ B ∩ disjointed W k) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) :=
              LocalGraphMass.tsum_lintegral_le _ _
          _ ≤ ∫⁻ x : EuclideanSpace ℂ I, frameFibreCount c I (S ∩ B) (WithLp.ofLp x)
                ∂(μH[((2 * d : ℕ) : ℝ)]) :=
              lintegral_mono fun x =>
                LocalGraphMass.tsum_frameFibreCount_le c I _ (fun k => Set.inter_subset_left) hdisj _
          _ ≤ G (I.orderEmbOfFin hIc) := lintegral_count_le U c hc I hIc (S ∩ B)
    _ = ∑ s ∈ Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s), G s := by
        refine Finset.sum_bij (fun I hI => ⇑(I.orderEmbOfFin (Finset.mem_powersetCard.1 hI).2))
          (fun I hI => Finset.mem_filter.2 ⟨Finset.mem_univ _, (I.orderEmbOfFin _).strictMono⟩)
          (fun I₁ hI₁ I₂ hI₂ h => ?_) (fun t ht => ?_) (fun I hI => ?_)
        · have := congrArg Set.range h
          rw [Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin] at this
          exact Finset.coe_inj.1 this
        · have hmono := (Finset.mem_filter.1 ht).2
          have hcard : (Finset.univ.image t).card = d := by
            rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
          refine ⟨Finset.univ.image t, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hcard⟩, ?_⟩
          exact (Finset.orderEmbOfFin_unique hcard
            (fun x => Finset.mem_image_of_mem t (Finset.mem_univ x)) hmono).symm
        · exact iSup_pos (Finset.mem_powersetCard.1 hI).2

end

end GroundTheory.Heights₂.Heights
end

