module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsMulEqPolynomialWeierstrassP
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosure

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAnalyticOfTendsto
section
open Filter PeriodPair
open scoped Topology

noncomputable section

namespace GlobalTheory.EllipticPoles

variable (L : PeriodPair)

lemma tendsto_neg_ne (a : ℂ) : Tendsto (fun z : ℂ ↦ -z) (𝓝[≠] a) (𝓝[≠] (-a)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (continuous_neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (by filter_upwards [self_mem_nhdsWithin] with z hz using by simpa using hz)

lemma tendsto_add_ne (a l : ℂ) : Tendsto (fun z : ℂ ↦ z + l) (𝓝[≠] a) (𝓝[≠] (a + l)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((continuous_add_const l).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (by filter_upwards [self_mem_nhdsWithin] with z hz using by simpa using hz)

lemma tendsto_two_ne (a : ℂ) : Tendsto (fun z : ℂ ↦ z + z) (𝓝[≠] a) (𝓝[≠] (a + a)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((by fun_prop : Continuous fun z : ℂ ↦ z + z).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (by
      filter_upwards [self_mem_nhdsWithin] with z hz h
      apply hz
      simp only [Set.mem_singleton_iff] at h ⊢
      linear_combination h / 2)

lemma exists_analytic_of_tendsto {f : ℂ → ℂ} {a c : ℂ} (hf : MeromorphicAt f a)
    (h : Tendsto f (𝓝[≠] a) (𝓝 c)) : ∃ g, AnalyticAt ℂ g a ∧ f =ᶠ[𝓝[≠] a] g :=
  hf.meromorphicOrderAt_nonneg_iff.1 ((tendsto_nhds_iff_meromorphicOrderAt_nonneg hf).1 ⟨c, h⟩)

lemma even_case {g : ℂ → ℂ} (hg : Meromorphic g)
    (hd : ∀ a ∉ L.lattice, ∃ c, Tendsto g (𝓝[≠] a) (𝓝 c))
    (hp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z) (hev : ∀ z, g (-z) = g z) :
    ∃ A : Polynomial ℂ, ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀, g z = A.eval (℘[L] z) := by
  classical
  let G : ℂ → ℂ := fun z ↦ if z ∈ L.lattice then 0 else limUnder (𝓝[≠] z) g
  have hG : ∀ a ∉ L.lattice, ∀ c, Tendsto g (𝓝[≠] a) (𝓝 c) → G a = c := fun a ha c h ↦ by
    simp only [G, if_neg ha]
    exact h.limUnder_eq
  have hGg : ∀ z₀, G =ᶠ[𝓝[≠] z₀] g := fun z₀ ↦ by
    filter_upwards [(hg z₀).eventually_analyticAt, eventually_ne_notMem_periodLattice L z₀]
      with z h1 h2
    exact hG z h2 _ (h1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  obtain ⟨A, hA⟩ := exists_eq_polynomial_weierstrassP L (g := G) ((hg 0).congr (hGg 0).symm)
    (fun a ha ↦ by
      obtain ⟨c, hc⟩ := hd a ha
      obtain ⟨h, hh, hgh⟩ := exists_analytic_of_tendsto (hg a) hc
      refine hh.differentiableAt.congr_of_eventuallyEq ?_
      rw [← nhdsNE_sup_pure, EventuallyEq, eventually_sup]
      refine ⟨(hGg a).trans hgh, ?_⟩
      simp only [eventually_pure]
      exact hG a ha _ ((hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hgh.symm))
    (fun z l hl ↦ by
      by_cases hz : z ∈ L.lattice
      · simp [G, hz, add_mem hz hl]
      · have hz' : z + l ∉ L.lattice := by rwa [L.lattice.add_mem_iff_left hl]
        obtain ⟨c, hc⟩ := hd _ hz'
        rw [hG _ hz' c hc, hG z hz c
          ((hc.comp (tendsto_add_ne z l)).congr fun w ↦ hp w l hl)])
    (fun z ↦ by
      by_cases hz : z ∈ L.lattice
      · simp [G, hz]
      · have hz' : -z ∉ L.lattice := by simpa using hz
        obtain ⟨c, hc⟩ := hd _ hz'
        rw [hG _ hz' c hc, hG z hz c ((hc.comp (tendsto_neg_ne z)).congr fun w ↦ hev w)])
  refine ⟨A, fun z₀ ↦ ?_⟩
  filter_upwards [hGg z₀, eventually_ne_notMem_periodLattice L z₀] with z h1 h2
  rw [← h1, hA z h2]

lemma no_pole_case {g : ℂ → ℂ} (hg : Meromorphic g)
    (hd : ∀ a ∉ L.lattice, ∃ c, Tendsto g (𝓝[≠] a) (𝓝 c))
    (hp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z) :
    ∃ A B : Polynomial ℂ, ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀,
      g z = A.eval (℘[L] z) + B.eval (℘[L] z) * ℘'[L] z := by
  have hgn : Meromorphic fun z ↦ g (-z) := fun a ↦
    MeromorphicAt.comp_analyticAt (f := g) (g := fun z ↦ -z) (hg (-a)) (by fun_prop)
  have hdn : ∀ a ∉ L.lattice, ∃ c, Tendsto (fun z ↦ g (-z)) (𝓝[≠] a) (𝓝 c) := fun a ha ↦ by
    obtain ⟨c, hc⟩ := hd (-a) (by simpa using ha)
    exact ⟨c, hc.comp (tendsto_neg_ne a)⟩
  have hpn : ∀ z, ∀ l ∈ L.lattice, g (-(z + l)) = g (-z) := fun z l hl ↦ by
    rw [neg_add, hp _ _ (neg_mem hl)]
  obtain ⟨A, hA⟩ := even_case L (g := fun z ↦ (g z + g (-z)) / 2)
    (fun a ↦ by have := hg a; have := hgn a; fun_prop)
    (fun a ha ↦ by
      obtain ⟨c, hc⟩ := hd a ha
      obtain ⟨c', hc'⟩ := hdn a ha
      exact ⟨_, (hc.add hc').div_const 2⟩)
    (fun z l hl ↦ by simp only [hp z l hl, hpn z l hl])
    (fun z ↦ by simp only [neg_neg, add_comm])
  let o : ℂ → ℂ := fun z ↦ (g z - g (-z)) / 2
  have ho : Meromorphic o := fun a ↦ by have := hg a; have := hgn a; fun_prop
  have hop : ∀ z, ∀ l ∈ L.lattice, o (z + l) = o z := fun z l hl ↦ by
    simp only [o, hp z l hl, hpn z l hl]
  have hon : ∀ z, o (-z) = -o z := fun z ↦ by simp only [o, neg_neg]; ring
  obtain ⟨B, hB⟩ := even_case L (g := fun z ↦ o z / ℘'[L] z)
    (fun a ↦ (ho a).div (L.meromorphic_derivWeierstrassP a))
    (fun a ha ↦ by
      obtain ⟨c, hc⟩ := hd a ha
      obtain ⟨c', hc'⟩ := hdn a ha
      have h1 : Tendsto o (𝓝[≠] a) (𝓝 ((c - c') / 2)) := (hc.sub hc').div_const 2
      have hP := hasDerivAt_derivWeierstrassP L ha
      by_cases h0 : ℘'[L] a = 0
      · have h2 := (derivWeierstrassP_eq_zero_iff L ha).1 h0
        obtain ⟨h, hh, hoh⟩ := exists_analytic_of_tendsto (ho a) h1
        have h3 : Tendsto o (𝓝[≠] a) (𝓝 (h a)) :=
          (hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hoh.symm
        have h4 : Tendsto (fun z : ℂ ↦ -z + (a + a)) (𝓝[≠] a) (𝓝[≠] a) := by
          have := (tendsto_add_ne (-a) (a + a)).comp (tendsto_neg_ne a)
          simpa [Function.comp_def] using this
        have h5 : Tendsto o (𝓝[≠] a) (𝓝 (-h a)) :=
          (h3.comp h4).neg.congr fun z ↦ by simp [hop _ _ h2, hon]
        have h6 : h a = 0 := CharZero.eq_neg_self_iff.1 (tendsto_nhds_unique h3 h5)
        refine ⟨_, ((hasDerivAt_iff_tendsto_slope.1 hh.differentiableAt.hasDerivAt).div
          (hasDerivAt_iff_tendsto_slope.1 hP) (weierstrassP_second_ne_zero L ha h0)).congr' ?_⟩
        filter_upwards [hoh, self_mem_nhdsWithin] with z hz hza
        have : z - a ≠ 0 := sub_ne_zero.2 hza
        simp only [Pi.div_apply, slope_def_field, h6, h0, sub_zero, hz]
        rw [div_div_div_cancel_right₀ this]
      · exact ⟨_, h1.div (hP.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) h0⟩)
    (fun z l hl ↦ by simp only [hop z l hl, L.derivWeierstrassP_add_coe z ⟨l, hl⟩])
    (fun z ↦ by simp only [hon, derivWeierstrassP_neg, neg_div_neg_eq])
  refine ⟨A, B, fun z₀ ↦ ?_⟩
  filter_upwards [hA z₀, hB z₀,
    (tendsto_two_ne z₀).eventually (eventually_ne_notMem_periodLattice L (z₀ + z₀))]
    with z h1 h2 h3
  have h4 : ℘'[L] z ≠ 0 := fun h ↦
    h3 ((derivWeierstrassP_eq_zero_iff L fun hz ↦ h3 (add_mem hz hz)).1 h)
  rw [← h1, ← h2, div_mul_cancel₀ _ h4]
  simp only [o]
  ring

theorem exists_mul_prod_eq (L : PeriodPair) (φ : ℂ → ℂ) (hφ : GlobalTheory.MomOne.Ell L φ) :
    ∃ (m : ℕ) (P : Fin m → ℂ) (A B : Polynomial ℂ),
      (∀ i, P i ∉ L.lattice ∧ meromorphicOrderAt φ (P i) < 0) ∧
      ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀, φ z * ∏ i, (L.weierstrassP z - L.weierstrassP (P i)) =
        A.eval (L.weierstrassP z) + B.eval (L.weierstrassP z) * L.derivWeierstrassP z := by
  classical
  obtain ⟨hf, hp⟩ := hφ
  have hK := (ZSpan.fundamentalDomain_isBounded L.basis).isCompact_closure
  set K := closure (ZSpan.fundamentalDomain L.basis)
  have hS := hK.finite_sdiff_of_mem_codiscreteWithin
    (hf.meromorphicOn (s := K)).analyticAt_mem_codiscreteWithin
  let S : Finset ℂ := hS.toFinset.filter fun a ↦ a ∉ L.lattice ∧ meromorphicOrderAt φ a < 0
  choose n hn using id hf
  let e := Fintype.equivFin (Σ a : S, Fin (n a))
  let D : ℂ → ℂ := fun z ↦ ∏ a ∈ S, (℘[L] z - ℘[L] a) ^ n a
  have hD : ∀ z, ∏ i, (℘[L] z - ℘[L] (e.symm i).1) = D z := fun z ↦ by
    rw [e.symm.prod_comp (fun x : (Σ a : S, Fin (n a)) ↦ ℘[L] z - ℘[L] x.1), Fintype.prod_sigma]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact Finset.prod_coe_sort S fun a ↦ (℘[L] z - ℘[L] a) ^ n a
  have hK' : ∀ a ∈ K, a ∉ L.lattice → ∃ c, Tendsto (fun z ↦ φ z * D z) (𝓝[≠] a) (𝓝 c) := by
    intro a haK ha
    have hP := L.analyticOnNhd_weierstrassP a ha
    have hP' := hP.continuousAt
    by_cases haS : a ∈ S
    · obtain ⟨u, hu, hu'⟩ := (natCast_le_analyticOrderAt (f := fun z ↦ ℘[L] z - ℘[L] a)
        (z₀ := a) (by fun_prop) (n := 1)).mp
        ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (by fun_prop)).mpr fun i hi ↦ by
          interval_cases i; simp)
      have h1 := (hn a).continuousAt
      have h2 := hu.continuousAt
      have h3 : ContinuousAt (fun z ↦ ((z - a) ^ n a • φ z) * u z ^ n a *
          ∏ b ∈ S.erase a, (℘[L] z - ℘[L] b) ^ n b) a := by fun_prop
      refine ⟨_, (h3.tendsto.congr' ?_).mono_left nhdsWithin_le_nhds⟩
      filter_upwards [hu'] with z hz
      simp only [D]
      rw [← Finset.mul_prod_erase _ _ haS, hz]
      simp only [smul_eq_mul, mul_pow]
      ring
    · have h1 : 0 ≤ meromorphicOrderAt φ a := by
        by_contra h
        refine haS (Finset.mem_filter.2 ⟨?_, ha, not_le.1 h⟩)
        simp only [Set.Finite.mem_toFinset]
        exact ⟨haK, fun h' ↦ h (AnalyticAt.meromorphicOrderAt_nonneg h')⟩
      obtain ⟨c, hc⟩ := (tendsto_nhds_iff_meromorphicOrderAt_nonneg (hf a)).2 h1
      have h2 : ContinuousAt D a := by simp only [D]; fun_prop
      exact ⟨_, hc.mul (h2.tendsto.mono_left nhdsWithin_le_nhds)⟩
  have hper : ∀ z, ∀ l ∈ L.lattice, φ (z + l) * D (z + l) = φ z * D z := fun z l hl ↦ by
    simp only [D, hp l hl z, L.weierstrassP_add_coe z ⟨l, hl⟩]
  obtain ⟨A, B, hAB⟩ := no_pole_case L (g := fun z ↦ φ z * D z)
    (fun a ↦ by
      have h1 := hf a
      have h2 := L.meromorphic_weierstrassP a
      simp only [D]
      fun_prop)
    (fun z hz ↦ by
      have hl : -(ZSpan.floor L.basis z : ℂ) ∈ L.lattice := by
        rw [L.lattice_eq_span_range_basis]; exact neg_mem (ZSpan.floor L.basis z).2
      obtain ⟨c, hc⟩ := hK' (z + -ZSpan.floor L.basis z)
        (by rw [← sub_eq_add_neg]; exact subset_closure (ZSpan.fract_mem_fundamentalDomain L.basis z))
        (by rwa [L.lattice.add_mem_iff_left hl])
      exact ⟨c, (hc.comp (tendsto_add_ne z _)).congr fun w ↦ hper w _ hl⟩)
    hper
  refine ⟨_, fun i ↦ (e.symm i).1, A, B, fun i ↦ (Finset.mem_filter.1 (e.symm i).1.2).2, fun z₀ ↦ ?_⟩
  simpa only [hD] using hAB z₀

end GlobalTheory.EllipticPoles
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEqConstMulOfForallExistsNormEq
section
namespace GlobalTheory

open Metric Set Filter Topology

theorem exists_eventually_eq_mul_of_norm_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {O : Set V} (hO : IsOpen O) {P Q : V → ℂ} (hP : DifferentiableOn ℂ P O) (hQ : DifferentiableOn ℂ Q O)
    {x : V} (hx : x ∈ O) (h : ∀ᶠ y in 𝓝 x, ‖P y‖ = ‖Q y‖) :
    ∃ z ∈ O, ∃ c : ℂ, ∀ᶠ y in 𝓝 z, P y = c * Q y := by
  by_cases h0 : ∀ᶠ y in 𝓝 x, Q y = 0
  · refine ⟨x, hx, 0, ?_⟩
    filter_upwards [h, h0] with y hy hy0
    rw [hy0, norm_zero, norm_eq_zero] at hy
    simp [hy]
  · have hfr : ∃ᶠ y in 𝓝 x, Q y ≠ 0 := not_eventually.mp h0
    obtain ⟨z, hz0, hzO, hz⟩ :=
      (hfr.and_eventually (Filter.Eventually.and (hO.mem_nhds hx) h.eventually_nhds)).exists
    have hzO' : z ∈ O := hzO
    have hne : ∀ᶠ y in 𝓝 z, Q y ≠ 0 :=
      (hQ.continuousOn.continuousAt (hO.mem_nhds hzO')).eventually_ne hz0
    have hall : ∀ᶠ y in 𝓝 z, y ∈ O ∧ Q y ≠ 0 ∧ ‖P y‖ = ‖Q y‖ :=
      Filter.Eventually.and (hO.mem_nhds hzO') (hne.and hz)
    obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.mp hall
    have hsub : ball z ε ⊆ O := fun y hy => (hb y hy).1
    have hd : DifferentiableOn ℂ (fun y => P y / Q y) (ball z ε) := by
      simp only [div_eq_mul_inv]
      exact (hP.mono hsub).mul ((hQ.mono hsub).inv (fun y hy => (hb y hy).2.1))
    have hn : ∀ y ∈ ball z ε, ‖P y / Q y‖ = 1 := by
      intro y hy
      rw [norm_div, (hb y hy).2.2, div_self (norm_ne_zero_iff.mpr (hb y hy).2.1)]
    have hmax : IsMaxOn (norm ∘ fun y => P y / Q y) (ball z ε) z := by
      intro y hy
      show ‖P y / Q y‖ ≤ ‖P z / Q z‖
      rw [hn y hy, hn z (mem_ball_self hε)]
    have hc := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball z ε).isPreconnected
      isOpen_ball hd (mem_ball_self hε) hmax
    refine ⟨z, hzO', P z / Q z, ?_⟩
    filter_upwards [ball_mem_nhds z hε] with y hy
    have e : P y / Q y = P z / Q z := hc hy
    rw [← e, div_mul_cancel₀ _ (hb y hy).2.1]

theorem exists_eq_const_mul_of_forall_exists_norm_eq :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (ι : Type) [Countable ι]
      (O : Set V), IsOpen O → IsPreconnected O → O.Nonempty → ∀ (P : V → ℂ) (Q : ι → V → ℂ),
      DifferentiableOn ℂ P O → (∀ i, DifferentiableOn ℂ (Q i) O) → (∀ x ∈ O, ∃ i, ‖P x‖ = ‖Q i x‖) →
      ∃ (i : ι) (c : ℂ), ∀ x ∈ O, P x = c * Q i x := by
  intro V _ _ _ ι _ O hO hc hne P Q hP hQ h
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  haveI : BaireSpace O := hO.baireSpace
  haveI : Nonempty O := hne.to_subtype
  have hcl : ∀ i, IsClosed {x : O | ‖P x‖ = ‖Q i x‖} := fun i =>
    isClosed_eq (hP.continuousOn.restrict.norm) ((hQ i).continuousOn.restrict.norm)
  have hcov : ⋃ i, {x : O | ‖P x‖ = ‖Q i x‖} = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨i, hi⟩ := h x x.2
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨i, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hcov
  have hx1 : ∀ᶠ y : O in 𝓝 x, ‖P y‖ = ‖Q i y‖ := mem_interior_iff_mem_nhds.mp hx
  have hx2 : ∀ᶠ y in 𝓝 (x : V), ‖P y‖ = ‖Q i y‖ := by
    rw [← hO.isOpenEmbedding_subtypeVal.map_nhds_eq x]
    exact hx1
  obtain ⟨z, hz, c, hzc⟩ := exists_eventually_eq_mul_of_norm_eq hO hP (hQ i) x.2 hx2
  refine ⟨i, c, fun y hy => ?_⟩
  have hd : DifferentiableOn ℂ (fun y => P y - c * Q i y) O := hP.sub ((hQ i).const_mul c)
  have := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_eventually hO hc hd hz
    (by filter_upwards [hzc] with y hy; simp [hy]) y hy
  exact sub_eq_zero.mp this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLimitPowerSeriesAgreeOnAnnulusPoints
section
open GlobalTheory.ConvSer Filter Topology

namespace GlobalTheory.ConvSer

theorem intg_iff_coeff_one_var {K : Type} [NormedField K] (f : PowerSeries K) :
    Intg f ↔ ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1 := by
  constructor
  · intro h n
    exact h (Finsupp.single () n)
  · intro h ν
    have hν : ν = Finsupp.single () (ν ()) := by
      ext; simp
    rw [hν]
    exact h (ν ())

theorem norm_coeff_mul_pow_le_of_intg {K : Type} [NormedField K] {f : PowerSeries K}
    (hf : Intg f) (x : K) (k : ℕ) : ‖PowerSeries.coeff k f * x ^ k‖ ≤ ‖x‖ ^ k := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) ((intg_iff_coeff_one_var f).1 hf k)

theorem summable_coeff_mul_pow_of_intg {K : Type} [NormedField K] [CompleteSpace K]
    {f : PowerSeries K} (hf : Intg f) {x : K} (hx : ‖x‖ < 1) :
    Summable fun k : ℕ => PowerSeries.coeff k f * x ^ k :=
  Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg x) hx)
    (norm_coeff_mul_pow_le_of_intg hf x)

theorem exists_tendsto_of_sub_tendsto_zero_ultra {K : Type} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (a : ℕ → K) (h : Tendsto (fun n => a (n + 1) - a n) atTop (𝓝 0)) :
    ∃ l, Tendsto a atTop (𝓝 l) := by
  have hs : Summable fun n => a (n + 1) - a n :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (by rwa [Nat.cofinite_eq_atTop])
  have h1 := hs.hasSum.tendsto_sum_nat
  simp only [Finset.sum_range_sub] at h1
  refine ⟨_, (h1.add_const (a 0)).congr fun n => ?_⟩
  simp

theorem exists_limit_of_agree_on_points : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (G : ℕ → Finset K) (r : ℝ), 0 < r → r ≤ 1 → Monotone G → (∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1) → Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0) → ∀ g : ℕ → PowerSeries K, (∀ n, Intg (g n)) → (∀ n, ∀ x ∈ G n, ev1 (g (n + 1)) x = ev1 (g n) x) → ∃ f : PowerSeries K, Intg f ∧ (∀ k, Filter.Tendsto (fun n => PowerSeries.coeff k (g n)) Filter.atTop (nhds (PowerSeries.coeff k f))) ∧ ∀ n, ∀ x ∈ G n, ev1 f x = ev1 (g n) x := by
  intro K _ _ _ G r hr hr1 hG hx hprod g hg hagree
  have hcoef : ∀ n k, ‖PowerSeries.coeff k (g (n + 1)) - PowerSeries.coeff k (g n)‖ ≤
      (∏ x ∈ G n, ‖x‖) / r ^ k := by
    intro n k
    have hI : Intg (g (n + 1) - g n) := by
      rw [intg_iff_coeff_one_var]
      intro j
      rw [map_sub, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · exact (intg_iff_coeff_one_var _).1 (hg _) j
      · rw [norm_neg]; exact (intg_iff_coeff_one_var _).1 (hg _) j
    have hz : ∀ x ∈ G n, ‖x‖ < 1 ∧ ev1 (g (n + 1) - g n) x = 0 := by
      intro x hxn
      refine ⟨(hx n x hxn).2, ?_⟩
      have h1 := summable_coeff_mul_pow_of_intg (hg (n + 1)) (hx n x hxn).2
      have h2 := summable_coeff_mul_pow_of_intg (hg n) (hx n x hxn).2
      have h3 := hagree n x hxn
      unfold ev1 at h3 ⊢
      simp only [map_sub, sub_mul]
      rw [h1.tsum_sub h2, h3, sub_self]
    have := (_root_.GlobalTheory.ConvSer.norm_coeff_le_prod_zeros K _ (G n) hI hz).1 r hr hr1 (fun x hxn => (hx n x hxn).1) k
    rw [map_sub] at this
    rwa [le_div_iff₀ (by positivity)]
  have hlim : ∀ k, ∃ l, Tendsto (fun n => PowerSeries.coeff k (g n)) atTop (𝓝 l) := by
    intro k
    apply exists_tendsto_of_sub_tendsto_zero_ultra
    refine squeeze_zero_norm (fun n => hcoef n k) ?_
    simpa using hprod.div_const (r ^ k)
  choose c hc using hlim
  have hfI : Intg (PowerSeries.mk c) := by
    rw [intg_iff_coeff_one_var]
    intro k
    rw [PowerSeries.coeff_mk]
    exact le_of_tendsto' (hc k).norm fun n => (intg_iff_coeff_one_var _).1 (hg n) k
  refine ⟨PowerSeries.mk c, hfI, fun k => by simpa using hc k, ?_⟩
  intro n x hxn
  have hx1 := (hx n x hxn).2
  have hconst : ∀ m, n ≤ m → ev1 (g m) x = ev1 (g n) x := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [hagree m x (hG hm hxn), ih]
  have ht : Tendsto (fun m => ev1 (g m) x) atTop (𝓝 (ev1 (PowerSeries.mk c) x)) := by
    unfold ev1
    refine tendsto_tsum_of_dominated_convergence (bound := fun k => ‖x‖ ^ k)
      (summable_geometric_of_lt_one (norm_nonneg x) hx1) (fun k => ?_)
      (Eventually.of_forall fun m k => norm_coeff_mul_pow_le_of_intg (hg m) x k)
    rw [PowerSeries.coeff_mk]
    exact (hc k).mul_const _
  have ht2 : Tendsto (fun m => ev1 (g m) x) atTop (𝓝 (ev1 (g n) x)) :=
    tendsto_const_nhds.congr' ((eventually_ge_atTop n).mono fun m hm => (hconst m hm).symm)
  exact tendsto_nhds_unique ht ht2

end GlobalTheory.ConvSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRingEquivApplyEqMulOfTranscendental
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem exists_ringEquiv_apply_eq_mul_of_transcendental {K L : Type*} [Field K] [Field L]
    [Algebra K L] [IsAlgClosed L] {x : L} (hx : Transcendental K x) {c : K} (hc : c ≠ 0) :
    ∃ σ : L ≃+* L, (∀ k : K, σ (algebraMap K L k) = algebraMap K L k) ∧
      σ x = algebraMap K L c * x := by
  have h1 : AlgebraicIndepOn K id ({x} : Set L) :=
    algebraicIndependent_unique_type_iff.2 hx
  obtain ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset h1
  let e : MvPolynomial s K ≃ₐ[K] MvPolynomial s K :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval fun i => c • MvPolynomial.X i)
      (MvPolynomial.aeval fun i => c⁻¹ • MvPolynomial.X i)
      (by ext i : 1; simp [smul_smul, hc]) (by ext i : 1; simp [smul_smul, hc])
  obtain ⟨σ, hσ⟩ :=
    GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis hs hs e.toRingEquiv
  refine ⟨σ, fun k => ?_, ?_⟩
  · simpa [e] using hσ (MvPolynomial.C k)
  · have := hσ (MvPolynomial.X ⟨x, hxs rfl⟩)
    rw [← Algebra.smul_def]
    simpa [e] using this

theorem mem_algebraicClosure_of_norm_le :
    ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (x : ℂ) (B : ℝ),
      (∀ ι' : ℂ ≃+* ℂ_[q], (∀ a : algebraicClosure ℚ ℂ, ι' (a : ℂ) = ι (a : ℂ)) → ‖ι' x‖ ≤ B) →
        x ∈ algebraicClosure ℚ ℂ := by
  intro q hq ι x B h
  by_contra hx
  rw [mem_algebraicClosure_iff] at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx isAlgebraic_zero
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hx' : Transcendental (algebraicClosure ℚ ℂ) x := fun ha =>
    hx (ha.restrictScalars ℚ)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
  have hq0 : q ≠ 0 := hq.out.ne_zero
  have hpos : 0 < ‖ι x‖ := by simpa using hx0
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (B / ‖ι x‖) hq1
  have hc : ((q : algebraicClosure ℚ ℂ) ^ j)⁻¹ ≠ 0 := by
    simp [hq0]
  obtain ⟨σ, hσ, hσx⟩ := exists_ringEquiv_apply_eq_mul_of_transcendental hx' hc
  have h2 := h (σ.trans ι) fun a => by
    have := hσ a
    simp only [RingEquiv.trans_apply]
    exact congrArg ι this
  have hn : ‖(q : ℂ_[q])‖ = (q : ℝ)⁻¹ := by
    have h3 : (q : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] (q : ℚ_[q]) := by simp
    rw [h3, norm_algebraMap', Padic.norm_p]
  rw [RingEquiv.trans_apply, hσx] at h2
  simp only [map_mul, map_inv₀, map_pow, map_natCast, norm_mul, norm_inv, norm_pow, hn,
    inv_pow, inv_inv] at h2
  rw [div_lt_iff₀ hpos] at hj
  linarith

end GlobalTheory.MomOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosureStatement
section
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_integral_bounded_closure : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (σ : Type), (∀ S T : MvPowerSeries σ K, Intg S → Intg T → Intg (S + T) ∧ Intg (S - T) ∧ Intg (S * T)) ∧ (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → Bdd (S + T) ∧ Bdd (S - T) ∧ Bdd (S * T)) ∧ (∀ (S : MvPowerSeries σ K) (n : ℕ), (Intg S → Intg (S ^ n)) ∧ (Bdd S → Bdd (S ^ n)) ∧ (Intg S → Bdd S)) ∧ (∀ a : K, Bdd (MvPowerSeries.C a : MvPowerSeries σ K) ∧ (‖a‖ ≤ 1 → Intg (MvPowerSeries.C a : MvPowerSeries σ K)) ∧ (‖a‖ < 1 → Small (MvPowerSeries.C a : MvPowerSeries σ K))) ∧ (∀ i : σ, Small (MvPowerSeries.X i : MvPowerSeries σ K)) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → MvPowerSeries σ K), ((∀ i ∈ t, Intg (f i)) → Intg (∏ i ∈ t, f i) ∧ Intg (∑ i ∈ t, f i)) ∧ ((∀ i ∈ t, Bdd (f i)) → Bdd (∏ i ∈ t, f i) ∧ Bdd (∑ i ∈ t, f i))) ∧ (∀ (ρ : Type) [Fintype ρ] (a : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K), (∀ j, Intg (a j)) → (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → (Intg S → Intg (MvPowerSeries.subst a S)) ∧ (Bdd S → Bdd (MvPowerSeries.subst a S))) ∧ (∀ (a : MvPowerSeries σ K) (f : PowerSeries K), Intg a → MvPowerSeries.constantCoeff a = 0 → (Intg f → Intg (f.subst a)) ∧ (Bdd f → Bdd (f.subst a))) ∧ (∀ (k ι : Type) [CommRing k] (φ : k →+* K) (a : ι → MvPowerSeries σ K) (A : MvPolynomial ι k), (∀ j, Bdd (a j)) → Bdd (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A)) ∧ (∀ f : PowerSeries K, (Intg f ↔ ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1) ∧ (Bdd f ↔ ∃ C : ℝ, ∀ n, ‖PowerSeries.coeff n f‖ ≤ C)) := by
  first | exact @GlobalTheory.BddAlg.bdd_alg | exact GlobalTheory.BddAlg.bdd_alg | (intros; apply GlobalTheory.BddAlg.bdd_alg <;> assumption)
end

