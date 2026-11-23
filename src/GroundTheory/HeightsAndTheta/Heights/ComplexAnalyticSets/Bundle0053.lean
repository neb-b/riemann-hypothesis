module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeGermNullstellensatz
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

namespace PrimeGermNullstellensatz

variable {σ : Type} [Fintype σ] {w : σ → ℂ}

theorem exists_of_mem_holGermIdeal {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) {φ : holGerms w}
    (hφ : φ ∈ holGermIdeal w p) :
    ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧
      (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨i, hi⟩ := hφ
    refine ⟨fun j _ => if j = i then 1 else 0, fun j => analyticAt_const, ?_⟩
    rw [hi]
    congr 1
    funext z
    simp
  | zero =>
    refine ⟨fun _ _ => 0, fun _ => analyticAt_const, ?_⟩
    rw [show (fun z => ∑ i, (fun (_ : Fin k) (_ : σ → ℂ) => (0 : ℂ)) i z * p i z) = (0 : (σ → ℂ) → ℂ) by
      funext z; simp]
    rfl
  | add x y _ _ hx hy =>
    obtain ⟨h₁, hh₁, e₁⟩ := hx
    obtain ⟨h₂, hh₂, e₂⟩ := hy
    refine ⟨fun i z => h₁ i z + h₂ i z, fun i => (hh₁ i).add (hh₂ i), ?_⟩
    show (x : Germ (𝓝 w) ℂ) + y = _
    rw [e₁, e₂, ← Germ.coe_add]
    congr 1
    funext z
    simp [add_mul, Finset.sum_add_distrib]
  | smul a x _ hx =>
    obtain ⟨h, hh, e⟩ := hx
    obtain ⟨fa, hfa, efa⟩ : ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f w ∧ (f : Germ (𝓝 w) ℂ) = a := a.2
    refine ⟨fun i z => fa z * h i z, fun i => hfa.mul (hh i), ?_⟩
    show (a : Germ (𝓝 w) ℂ) * x = _
    rw [e, ← efa, ← Germ.coe_mul]
    congr 1
    funext z
    simp [Finset.mul_sum, mul_assoc]

theorem mem_holGermIdeal_of_eq {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ} (hp : ∀ i, AnalyticAt ℂ (p i) w)
    {h : Fin k → (σ → ℂ) → ℂ} (hh : ∀ i, AnalyticAt ℂ (h i) w) (φ : holGerms w)
    (hφ : (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)) :
    φ ∈ holGermIdeal w p := by
  have hsum : φ = ∑ i, (⟨(h i : Germ (𝓝 w) ℂ), h i, hh i, rfl⟩ : holGerms w) *
      ⟨(p i : Germ (𝓝 w) ℂ), p i, hp i, rfl⟩ := by
    apply Subtype.ext
    rw [hφ, show (fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) = ∑ i, h i * p i by
      funext z; simp [Finset.sum_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show ((∑ i, h i * p i : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = Germ.coeRingHom (𝓝 w) (∑ i, h i * p i) from rfl,
      map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    rfl
  rw [hsum]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem coeff_eq_zero_of_distinct_roots {N : ℕ} (c t : Fin N → ℂ) (ht : Function.Injective t)
    (hroot : ∀ m, ∑ j, c j * t m ^ (j : ℕ) = 0) : ∀ j, c j = 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact fun j => j.elim0
  set Q : Polynomial ℂ := ∑ j : Fin N, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)
  have hQe : ∀ s, Q.eval s = ∑ j, c j * s ^ (j : ℕ) := by
    intro s
    simp [Q, Polynomial.eval_finsetSum]
  have hdeg : Q.natDegree < Fintype.card (Fin N) := by
    rw [Fintype.card_fin]
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := N - 1) fun j _ => ?_)
      (Nat.sub_lt hN Nat.one_pos)
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_sub_one_of_lt j.isLt)
  have hQ : Q = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q ht
    (fun m => by rw [hQe]; exact hroot m) hdeg
  intro j
  have hj := congrArg (fun q : Polynomial ℂ => q.coeff (j : ℕ)) hQ
  simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero,
    Fin.val_inj] at hj
  simpa using hj

theorem proof (hCover : PrimeGermCanonicalCover.Statement) : PrimeGermNullstellensatz.Statement := by
  intro σ _ w k p g hp hg hP hvan
  obtain ⟨d, A, ℓ, N, δ, hδ, hδP, hdiv, hsheet⟩ := hCover σ w k p hp hP
  obtain ⟨M, a, h, ha, hh, hrel⟩ := hdiv g hg

  have hoff : ∀ᶠ y in 𝓝 (A w), δ y ≠ 0 → ∀ j, a j y = 0 := by
    filter_upwards [hsheet _ (hrel.and hvan)] with y hy hδy
    obtain ⟨x, hx, hinj⟩ := hy hδy
    refine coeff_eq_zero_of_distinct_roots (fun j => a j y) (fun m => ℓ (x m)) hinj fun m => ?_
    obtain ⟨⟨hr, hv⟩, hpx, hAx⟩ := hx m
    have hg0 : g (x m) = 0 := hv hpx
    have h0 : δ (A (x m)) ^ M * g (x m) - ∑ j, a j (A (x m)) * ℓ (x m) ^ (j : ℕ) = 0 := by
      rw [hr]
      simp [hpx]
    rw [hg0, mul_zero, zero_sub, neg_eq_zero, hAx] at h0
    exact h0

  have hδne : ¬ (δ =ᶠ[𝓝 (A w)] 0) := by
    intro h0
    apply hδP
    refine ⟨fun _ _ => 0, fun _ => analyticAt_const, ?_⟩
    filter_upwards [(A.continuous.tendsto w).eventually h0] with z hz
    simpa using hz

  have hzero : ∀ᶠ y in 𝓝 (A w), ∀ j, a j y = 0 := by
    have hall : ∀ᶠ y in 𝓝 (A w), AnalyticAt ℂ δ y ∧ (∀ j, AnalyticAt ℂ (a j) y) ∧
        (δ y ≠ 0 → ∀ j, a j y = 0) :=
      hδ.eventually_analyticAt.and ((eventually_all.2 fun j => (ha j).eventually_analyticAt).and hoff)
    obtain ⟨r, hr0, hrB⟩ := Metric.eventually_nhds_iff_ball.1 hall
    filter_upwards [Metric.ball_mem_nhds (A w) hr0] with y₀ hy₀ j
    by_contra hne
    apply hδne
    have hnear : δ =ᶠ[𝓝 y₀] 0 := by
      have hcont : ContinuousAt (a j) y₀ := ((hrB y₀ hy₀).2.1 j).continuousAt
      filter_upwards [hcont.eventually_ne hne, Metric.isOpen_ball.mem_nhds hy₀] with y hy hyB
      by_contra hδy
      exact hy ((hrB y hyB).2.2 hδy j)
    have hon : AnalyticOnNhd ℂ δ (Metric.ball (A w) r) := fun y hy => (hrB y hy).1
    have hEq := hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hy₀ hnear
    filter_upwards [Metric.ball_mem_nhds (A w) hr0] with y hy using hEq hy

  have hrel' : ∀ᶠ z in 𝓝 w, δ (A z) ^ M * g z = ∑ i, h i z * p i z := by
    filter_upwards [hrel, (A.continuous.tendsto w).eventually hzero] with z hz hz0
    rw [← hz]
    simp [hz0]
  have hδA : AnalyticAt ℂ (fun z => δ (A z)) w := hδ.comp (A.analyticAt w)
  let G : holGerms w := ⟨(g : Germ (𝓝 w) ℂ), g, hg, rfl⟩
  let Dg : holGerms w := ⟨((fun z => δ (A z) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ), _, hδA, rfl⟩
  have hmem : Dg ^ M * G ∈ holGermIdeal w p := by
    refine mem_holGermIdeal_of_eq hp hh _ ?_
    rw [show ((Dg ^ M * G : holGerms w) : Germ (𝓝 w) ℂ) =
        (((fun z => δ (A z)) ^ M * g : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) by
      rw [Germ.coe_mul, Germ.coe_pow]
      rfl]
    exact Germ.coe_eq.2 (hrel'.mono fun z hz => by simpa using hz)
  have hDg : Dg ∉ holGermIdeal w p := by
    intro hD
    obtain ⟨h', hh', e⟩ := exists_of_mem_holGermIdeal p hD
    exact hδP ⟨h', hh', Germ.coe_eq.1 e⟩
  have hG : G ∈ holGermIdeal w p := by
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact absurd (hP.mem_of_pow_mem M h1) hDg
    · exact h1
  obtain ⟨h', hh', e⟩ := exists_of_mem_holGermIdeal p hG
  exact ⟨h', hh', Germ.coe_eq.1 e⟩

end PrimeGermNullstellensatz

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperHolomorphicSurjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric MeasureTheory
open scoped ENNReal NNReal

namespace ProperHolomorphicSurjective

theorem analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

noncomputable def jac {k : ℕ} (g : (Fin k → ℂ) → Fin k → ℂ) (v : Fin k → ℂ) : ℂ :=
  LinearMap.det (fderiv ℂ g v : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)

theorem jac_ne_zero_iff {k : ℕ} (g : (Fin k → ℂ) → Fin k → ℂ) (v : Fin k → ℂ) :
    jac g v ≠ 0 ↔ Function.Injective (fderiv ℂ g v) := by
  rw [jac, ← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, LinearMap.injective_iff_surjective.1 h⟩

theorem differentiableOn_jac {k : ℕ} {Ω : Set (Fin k → ℂ)} {g : (Fin k → ℂ) → Fin k → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) : DifferentiableOn ℂ (jac g) Ω := by
  have hfd : DifferentiableOn ℂ (fderiv ℂ g) Ω :=
    (analyticOnNhd_of_differentiableOn hΩ hg).fderiv.differentiableOn
  have hentry : ∀ i j : Fin k,
      DifferentiableOn ℂ (fun v => fderiv ℂ g v (Pi.single j 1) i) Ω := fun i j =>
    differentiableOn_pi.1 (hfd.clm_apply (differentiableOn_const _)) i
  have hjac : jac g = fun v => ∑ σ : Equiv.Perm (Fin k),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, fderiv ℂ g v (Pi.single i 1) (σ i) := by
    funext v
    rw [jac, ← LinearMap.det_toMatrix', Matrix.det_apply']
    simp [LinearMap.toMatrix'_apply]
  rw [hjac]
  refine DifferentiableOn.fun_sum fun σ _ => (differentiableOn_const _).mul ?_
  intro x hx
  exact (HasFDerivWithinAt.finsetProd (u := Finset.univ)
    (g := fun i v => fderiv ℂ g v (Pi.single i 1) (σ i))
    fun i _ => ((hentry (σ i) i) x hx).hasFDerivWithinAt).differentiableWithinAt

theorem proof (hFin : CompactHolomorphicFibreFinite.Statement) (hInf : RankDeficientFibreInfinite.Statement)
    (hDim : HolomorphicZeroSetDimH.Statement) (hConn : HausdorffNullComplementConnected.Statement) :
    ProperHolomorphicSurjective.Statement := by
  intro k Ω D g hΩ hΩne hD hDc hg hmaps hprop
  refine Set.Subset.antisymm (Set.image_subset_iff.2 hmaps) ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · intro y _
    obtain ⟨v, hv⟩ := hΩne
    exact ⟨v, hv, Subsingleton.elim _ _⟩
  have han := analyticOnNhd_of_differentiableOn hΩ hg
  have hfr : Module.finrank ℝ (Fin k → ℂ) = 2 * k := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]

  have hopen : ∀ v ∈ Ω, jac g v ≠ 0 → g '' Ω ∈ 𝓝 (g v) := by
    intro v hv hdet
    have he : ((LinearMap.equivOfDetNeZero (fderiv ℂ g v : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)
        hdet).toContinuousLinearEquiv : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) = fderiv ℂ g v := by
      ext1 u
      rfl
    have hs : HasStrictFDerivAt g ((LinearMap.equivOfDetNeZero
        (fderiv ℂ g v : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) hdet).toContinuousLinearEquiv :
          (Fin k → ℂ) →L[ℂ] Fin k → ℂ) v := by
      rw [he]
      exact (han v hv).hasStrictFDerivAt
    rw [← hs.map_nhds_eq_of_equiv]
    exact Filter.image_mem_map (hΩ.mem_nhds hv)

  have hreg : ∀ W ⊆ Ω, IsOpen W → W.Nonempty → ∃ w ∈ W, jac g w ≠ 0 := by
    intro W hW hWo hWne
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    obtain ⟨y, hy⟩ := hInf k k W g hWo hWne (hg.mono hW)
      fun v hv hinj => (jac_ne_zero_iff g v).2 hinj (hcon v hv)
    obtain ⟨t, htW, hty⟩ := hy.nonempty
    have hyD : y ∈ D := hty ▸ hmaps (hW htW)
    have hcpt : IsCompact {v | v ∈ Ω ∧ g v = y} :=
      hprop {y} (Set.singleton_subset_iff.2 hyD) isCompact_singleton
    exact hy ((hFin k k Ω g y hΩ hg hcpt).subset fun t ht => ⟨hW ht.1, ht.2⟩)

  set C : Set (Fin k → ℂ) := g '' {v | v ∈ Ω ∧ jac g v = 0} with hC
  have hdimC : dimH C ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := by
    refine le_trans ?_ (hDim k Ω (jac g) hΩ (differentiableOn_jac hΩ hg) hreg)
    refine dimH_image_le_of_locally_lipschitzOn fun x hx => ?_
    obtain ⟨K, t, ht, hL⟩ := ((han x hx.1).contDiffAt (n := 1)).exists_lipschitzOnWith
    exact ⟨K, t, nhdsWithin_le_nhds ht, hL⟩
  have hnull : μH[(Module.finrank ℝ (Fin k → ℂ) : ℝ) - 1] C = 0 := by
    have hlt : dimH C < (((2 * k - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_natCast]
      calc dimH C ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := hdimC
        _ = ((2 * (k - 1) : ℕ) : ℝ≥0∞) := by push_cast; ring
        _ < ((2 * k - 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast (by omega : 2 * (k - 1) < 2 * k - 1)
    have h0 := hausdorffMeasure_of_dimH_lt hlt
    have hexp : ((((2 * k - 1 : ℕ) : ℝ≥0)) : ℝ) = (Module.finrank ℝ (Fin k → ℂ) : ℝ) - 1 := by
      rw [hfr, NNReal.coe_natCast, Nat.cast_sub (by omega)]
      push_cast
      ring
    rwa [hexp] at h0
  have hR : IsPreconnected (D \ C) := hConn (Fin k → ℂ) D C hD hDc hnull

  have hclosed : ∀ y ∈ D, y ∈ closure (g '' Ω) → y ∈ g '' Ω := by
    intro y hyD hycl
    obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.1 hD y hyD
    have hLD : closedBall y (r / 2) ⊆ D := (closedBall_subset_ball (by linarith)).trans hrD
    have hK := hprop (closedBall y (r / 2)) hLD (isCompact_closedBall y (r / 2))
    have hgK : IsCompact (g '' (Ω ∩ g ⁻¹' closedBall y (r / 2))) :=
      hK.image_of_continuousOn (hg.continuousOn.mono Set.inter_subset_left)
    refine Set.image_mono Set.inter_subset_left (hgK.isClosed.closure_subset ?_)
    rw [mem_closure_iff_nhds] at hycl ⊢
    intro U hU
    obtain ⟨z, ⟨hzU, hzB⟩, v, hv, rfl⟩ :=
      hycl (U ∩ ball y (r / 2)) (Filter.inter_mem hU (ball_mem_nhds y (by linarith)))
    exact ⟨g v, hzU, v, ⟨hv, ball_subset_closedBall hzB⟩, rfl⟩

  have hne : ((D \ C) ∩ interior (g '' Ω)).Nonempty := by
    obtain ⟨w, hwΩ, hw⟩ := hreg Ω subset_rfl hΩ hΩne
    have hN : g '' Ω ∈ 𝓝 (g w) := hopen w hwΩ hw
    by_contra hcon
    have hsubC : interior (g '' Ω) ⊆ C := by
      intro z hz
      by_contra hzC
      exact hcon ⟨z, ⟨Set.image_subset_iff.2 hmaps (interior_subset hz), hzC⟩, hz⟩
    have h1 : dimH (interior (g '' Ω)) = Module.finrank ℝ (Fin k → ℂ) :=
      Real.dimH_of_nonempty_interior (by rw [interior_interior]; exact ⟨g w, mem_interior_iff_mem_nhds.2 hN⟩)
    have h2 := (dimH_mono hsubC).trans hdimC
    rw [h1, hfr, show (2 : ℝ≥0∞) * ((k - 1 : ℕ) : ℝ≥0∞) = ((2 * (k - 1) : ℕ) : ℝ≥0∞) by push_cast; ring]
      at h2
    have h3 : 2 * k ≤ 2 * (k - 1) := by exact_mod_cast h2
    omega

  have hRsub : D \ C ⊆ interior (g '' Ω) ∪ (closure (g '' Ω))ᶜ := by
    rintro y ⟨hyD, hyC⟩
    by_cases hyE : y ∈ g '' Ω
    · left
      obtain ⟨v, hv, rfl⟩ := hyE
      have hjv : jac g v ≠ 0 := fun h0 => hyC ⟨v, ⟨hv, h0⟩, rfl⟩
      exact mem_interior_iff_mem_nhds.2 (hopen v hv hjv)
    · right
      exact fun hcl => hyE (hclosed y hyD hcl)
  have hdisj : Disjoint (interior (g '' Ω)) (closure (g '' Ω))ᶜ :=
    Set.disjoint_compl_right_iff_subset.2 (interior_subset.trans subset_closure)
  have hRE := hR.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl hdisj hRsub hne
  intro y hyD
  by_cases hyC : y ∈ C
  · obtain ⟨v, ⟨hv, _⟩, rfl⟩ := hyC
    exact ⟨v, hv, rfl⟩
  · exact interior_subset (hRE ⟨hyD, hyC⟩)

end ProperHolomorphicSurjective

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularOffHypersurface
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem exists_ringKrullDim_quotient_eq_nat {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime) :
    ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
  have : J.IsPrime := hJ
  have hge : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ringKrullDim_nonneg_of_nontrivial
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : WithBot ℕ∞) := by
    refine (ringKrullDim_quotient_le J).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
      Fintype.card_fin, zero_add]
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at hge hle
  induction x using WithBot.recBotCoe with
  | bot => exact absurd hge (by simp)
  | coe m =>
    induction m using ENat.recTopCoe with
    | top => exact absurd hle (by norm_cast)
    | coe d => exact ⟨d, rfl⟩

theorem analyticOnNhd_of_differentiableOn_fin {d : ℕ} {σ : Type} [Fintype σ] {U : Set (Fin d → ℂ)}
    {G : (Fin d → ℂ) → σ → ℂ} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) : AnalyticOnNhd ℂ G U := by
  intro y hy
  refine AnalyticAt.pi fun s => ?_
  have hs : DifferentiableOn ℂ (fun x => G x s) U :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) s).differentiable.comp_differentiableOn hG
  refine analyticOnNhd_of_continuousOn_of_separately hU hs.continuousOn (fun z hz i => ?_) y hy
  have h1 : DifferentiableAt ℂ (fun x => G x s) (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hs.differentiableAt (hU.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update (𝕜 := ℂ) z (z i)).differentiableAt

theorem RegularOffHypersurface.proof (hG : FrameGraphGeneric.Statement) : RegularOffHypersurface.Statement := by
  intro σ _ I hI
  set n := Fintype.card σ
  set e : σ ≃ Fin n := Fintype.equivFin σ
  set φ : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ := renameEquiv ℂ e.symm
  set J : Ideal (MvPolynomial (Fin n) ℂ) := I.comap φ
  have hJ : J.IsPrime := Ideal.IsPrime.comap _
  have hφ : ∀ (x : σ → ℂ) (q : MvPolynomial (Fin n) ℂ), eval x (φ q) = eval (x ∘ e.symm) q := fun x q => by
    simp [φ, eval_rename]
  obtain ⟨d, hd⟩ := exists_ringKrullDim_quotient_eq_nat J hJ
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, q, hcard, hqJ, hreg⟩ := hG n d J hJ hd b

  let T : (σ → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp
      (ContinuousLinearMap.pi fun i : Fin n => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm i))
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] (σ → ℂ) :=
    (ContinuousLinearMap.pi fun s : σ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (e s)).comp
      ((EuclideanSpace.equiv (Fin n) ℂ : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)))
  have hT : ∀ x i, T x i = x (e.symm i) := fun x i => rfl
  have hS : ∀ w s, S w s = w (e s) := fun w s => rfl
  have hST : ∀ x, S (T x) = x := fun x => funext fun s => by simp [hS, hT]
  have hTS : ∀ w, T (S w) = w := fun w => by ext i; simp [hS, hT]
  have hZ : ∀ x : σ → ℂ, x ∈ zeroSetIn I ↔ T x ∈ zeroSetEuc J := by
    intro x
    have hx : (fun i => T x i) = x ∘ e.symm := rfl
    simp only [zeroSetIn, zeroSetEuc, Set.mem_ofPred_eq, hx]
    constructor
    · intro h p hp
      rw [← hφ]
      exact h _ (Ideal.mem_comap.mp hp)
    · intro h p hp
      have := h (φ.symm p) (by simpa [J, Ideal.mem_comap] using hp)
      rwa [← hφ, AlgEquiv.apply_symm_apply] at this
  refine ⟨φ q, fun h => hqJ (Ideal.mem_comap.mpr h), ?_⟩
  intro z hz hzh
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hg, hproj, hgraph⟩ :=
    hreg (T z) ((hZ z).mp hz) (by rwa [hφ] at hzh)
  let eI : I₀ ≃ Fin d := I₀.equivFinOfCardEq hcard
  let Ψ : (Fin d → ℂ) →L[ℂ] (I₀ → ℂ) :=
    ContinuousLinearMap.pi fun i : I₀ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) (eI i)
  let A : (σ → ℂ) →L[ℂ] (Fin d → ℂ) :=
    ContinuousLinearMap.pi fun k : Fin d =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm (eI.symm k))
  have hΨ : ∀ y i, Ψ y i = y (eI i) := fun y i => rfl
  have hA : ∀ x k, A x k = x (e.symm (eI.symm k)) := fun x k => rfl
  have hO : IsOpen (Ψ ⁻¹' Ω) := hΩ.preimage Ψ.continuous
  refine ⟨hz, d, A, Ψ ⁻¹' Ω, T ⁻¹' V, fun y => S (g (Ψ y)), hO, hV.preimage T.continuous, hzV, ?_, ?_, ?_⟩
  · exact analyticOnNhd_of_differentiableOn_fin hO (S.differentiable.comp_differentiableOn
      (hg.comp Ψ.differentiable.differentiableOn fun y hy => hy))
  · intro y hy
    ext k
    have h1 := congrFun (hproj (Ψ y) hy) (eI.symm k)
    simp only [frameProj, b, EuclideanSpace.basisFun_inner] at h1
    show A (S (g (Ψ y))) k = y k
    rw [hA, hS, Equiv.apply_symm_apply, h1, hΨ, Equiv.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨hxZ, hxV⟩
      have hmem : T x ∈ zeroSetEuc J ∩ V := ⟨(hZ x).mp hxZ, hxV⟩
      rw [hgraph] at hmem
      obtain ⟨u, hu, hgu⟩ := hmem
      have hΨu : Ψ (fun k => u (eI.symm k)) = u := funext fun i => by simp [hΨ]
      refine ⟨fun k => u (eI.symm k), ?_, ?_⟩
      · show Ψ _ ∈ Ω
        rwa [hΨu]
      · simp only [hΨu, hgu, hST]
    · rintro ⟨y, hy, rfl⟩
      have hmem : g (Ψ y) ∈ zeroSetEuc J ∩ V := hgraph ▸ Set.mem_image_of_mem g hy
      refine ⟨(hZ _).mpr ?_, ?_⟩
      · rw [hTS]; exact hmem.1
      · show T (S (g (Ψ y))) ∈ V
        rw [hTS]; exact hmem.2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartChangeSheetNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def ChartChangeSheetNull.Statement : Prop :=
  ∀ (n d : ℕ) (J J' : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (u u' : Fin n → ℂ) (U U' : Set (Fin n → ℂ)) (Φ Ψ : (Fin n → ℂ) → Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    J'.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') = d →
    linForm u ∉ J → linForm u' ∉ J' → IsFiniteProjection J A → IsFiniteProjection J' A' →
    IsOpen U → IsOpen U' → zeroSet J \ {x | linEval u x = 0} ⊆ U →
    zeroSet J' \ {x | linEval u' x = 0} ⊆ U' →
    DifferentiableOn ℂ Φ U' → DifferentiableOn ℂ Ψ U →
    Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}) →
    Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}) →
    (∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x) →
    (∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x) →
      volume ((fun x => A *ᵥ x) ''
        {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧
          ¬ (linEval u x ≠ 0 ∧ ∃ s', IsSheetAt J' A' (Ψ x) s')}) = 0

namespace ChartChange

end ChartChange

end

end GroundTheory.Heights₂.Heights
end

