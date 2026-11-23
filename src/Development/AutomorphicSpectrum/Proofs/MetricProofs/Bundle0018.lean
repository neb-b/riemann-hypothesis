module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralParametrizedCover
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

section

variable {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]


omit [CompactSpace X] [T2Space X] in
theorem chartPartition_norm_le_one (A : FinHolAtlas e X) (Q : ChartPartition A) (j : Fin A.n)
    (x : X) : ‖Q.χ j x‖ ≤ 1 := by
  have h : Q.χ j x ≤ ∑ k, Q.χ k x :=
    Finset.single_le_sum (f := fun k => Q.χ k x) (fun k _ => Q.nonneg k x) (Finset.mem_univ j)
  rw [Q.sum_eq_one] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (Q.nonneg j x)]
  exact h

theorem chartTerm_integrableOn (A : FinHolAtlas e X) (Q : ChartPartition A) (P : Fin e → LocPot X)
    (g : X → ℝ) (hg : MIntegrable A P g) (j : Fin A.n) :
    IntegrableOn (fun y => Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y)
      (A.chart j).target := by
  have hK : IsCompact (A.chart j '' tsupport (Q.χ j)) :=
    (isClosed_tsupport _).isCompact.image_of_continuousOn
      ((A.chart j).continuousOn.mono (Q.tsupport_subset j))
  have hKt : A.chart j '' tsupport (Q.χ j) ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (Q.tsupport_subset j hx)
  have h0 := hg j _ hKt hK
  have hcont : ContinuousOn (fun y => Q.χ j ((A.chart j).symm y)) (A.chart j).target := by
    have h := (Q.smooth j j).continuousOn
    simpa [Function.comp_def] using h
  have hm : AEStronglyMeasurable (fun y => Q.χ j ((A.chart j).symm y))
      (volume.restrict (A.chart j '' tsupport (Q.χ j))) :=
    (hcont.mono hKt).aestronglyMeasurable hK.measurableSet
  have h1 : IntegrableOn
      (fun y => Q.χ j ((A.chart j).symm y) * (g ((A.chart j).symm y) * locDens A P j y))
      (A.chart j '' tsupport (Q.χ j)) :=
    Integrable.bdd_mul (c := 1) h0 hm (ae_of_all _ fun y => chartPartition_norm_le_one A Q j _)
  have h2 : IntegrableOn
      (fun y => Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y)
      (A.chart j '' tsupport (Q.χ j)) := by
    simpa only [mul_assoc] using h1
  refine IntegrableOn.of_forall_sdiff_eq_zero h2 (A.chart j).open_target.measurableSet ?_
  rintro y ⟨hy, hyK⟩
  have hn : (A.chart j).symm y ∉ tsupport (Q.χ j) := fun hmem =>
    hyK ⟨_, hmem, (A.chart j).right_inv hy⟩
  rw [image_eq_zero_of_notMem_tsupport hn]
  ring

theorem chartTerm_hasSum (A : FinHolAtlas e X) (V B : ℕ → Set (Fin e → ℂ))
    (Φ : ℕ → (Fin e → ℂ) → X) (P : Fin e → LocPot X) (g : X → ℝ) (Q : ChartPartition A)
    (hc : IsParamCover A V B Φ) (hC2 : ∀ n, ∀ z ∈ B n, ∀ i, IsTwiceDifferentiableAt A (P i) (Φ n z))
    (hg : MIntegrable A P g) (j : Fin A.n) :
    (∀ n, IntegrableOn (fun z => Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z) (B n)) ∧
      HasSum (fun n => ∫ z in B n, Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z)
        (∫ y in (A.chart j).target,
          Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y) := by
  obtain ⟨hpar, hB, hdisj, hnull⟩ := hc
  have hf := chartTerm_integrableOn A Q P g hg j
  have hCm : ∀ n, MeasurableSet (B n ∩ Φ n ⁻¹' (A.chart j).source) := by
    intro n
    have hO : IsOpen (V n ∩ Φ n ⁻¹' (A.chart j).source) :=
      (hpar n).2.1.isOpen_inter_preimage (hpar n).1 (A.chart j).open_source
    have hEq : B n ∩ Φ n ⁻¹' (A.chart j).source = B n ∩ (V n ∩ Φ n ⁻¹' (A.chart j).source) := by
      ext z
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (hB n).2 h1, h2⟩
      · rintro ⟨h1, _, h2⟩
        exact ⟨h1, h2⟩
    rw [hEq]
    exact (hB n).1.inter hO.measurableSet
  have key := fun n => _root_.GlobalTheory.CompanionTheory.Ar.PB.param_chart_changeOfVariables e X A (V n) (B n ∩ Φ n ⁻¹' (A.chart j).source) (Φ n) P
    (fun x => Q.χ j x * g x) j (hpar n) (hCm n) (fun z hz => (hB n).2 hz.1) (fun z hz => hz.2)
    (fun z hz => hC2 n z hz.1)
  have hsub : ∀ n, (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source) ⊆
      (A.chart j).target := by
    rintro n _ ⟨z, hz, rfl⟩
    exact (A.chart j).map_source hz.2
  have hzero : ∀ n, ∀ z ∈ B n \ (B n ∩ Φ n ⁻¹' (A.chart j).source),
      Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z = 0 := by
    rintro n z ⟨hz, hz'⟩
    have hn : Φ n z ∉ tsupport (Q.χ j) := fun hmem =>
      hz' ⟨hz, Q.tsupport_subset j hmem⟩
    rw [image_eq_zero_of_notMem_tsupport hn]
    ring
  have hdis : Pairwise (Function.onFun Disjoint fun n =>
      (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source)) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hzw⟩
    have hEq : Φ n z = Φ m w := by
      refine (A.chart j).injOn hz.2 hw.2 ?_
      exact hzw.symm
    exact Set.disjoint_left.1 (hdisj hnm) ⟨z, hz.1, rfl⟩ ⟨w, hw.1, hEq.symm⟩
  have hUsub : (⋃ n, (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source)) ⊆
      (A.chart j).target := Set.iUnion_subset hsub
  have hsum := hasSum_integral_iUnion (fun n => (key n).1) hdis (hf.mono_set hUsub)
  have hUeq : (⋃ n, (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source)) =ᵐ[volume]
      (A.chart j).target := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [Set.sdiff_eq_empty.2 hUsub]
      exact measure_empty
    · refine measure_mono_null ?_ (hnull j)
      rintro y ⟨hy, hyU⟩
      refine ⟨hy, ?_⟩
      intro hmem
      obtain ⟨_, ⟨n, rfl⟩, z, hz, hzy⟩ := hmem
      refine hyU (Set.mem_iUnion.2 ⟨n, z, ⟨hz, ?_⟩, ?_⟩)
      · show Φ n z ∈ (A.chart j).source
        rw [hzy]
        exact (A.chart j).map_target hy
      · show A.chart j (Φ n z) = y
        rw [hzy]
        exact (A.chart j).right_inv hy
  rw [setIntegral_congr_set hUeq] at hsum
  constructor
  · intro n
    refine IntegrableOn.of_forall_sdiff_eq_zero
      ((key n).2.1.1 (hf.mono_set (hsub n))) (hB n).1 (hzero n)
  · have hEq : (fun n => ∫ z in B n, Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z) =
        fun n => ∫ y in (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source),
          Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y := by
      funext n
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hB n).1 Set.inter_subset_left
        (hzero n)]
      exact ((key n).2.2).symm
    rw [hEq]
    exact hsum

theorem integrableOn_hasSum_paramCover : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (V B : ℕ → Set (Fin e → ℂ)) (Φ : ℕ → (Fin e → ℂ) → X) (P : Fin e → LocPot X) (g : X → ℝ), IsParamCover A V B Φ → (∀ n, ∀ z ∈ B n, ∀ i, IsTwiceDifferentiableAt A (P i) (Φ n z)) → MIntegrable A P g → (∀ n, IntegrableOn (fun z => g (Φ n z) * paramDens P (Φ n) z) (B n)) ∧ HasSum (fun n => ∫ z in B n, g (Φ n z) * paramDens P (Φ n) z) (mInt A P g) := by
  intro e X _ _ _ A V B Φ P g hc hC2 hg
  have hne : Nonempty (ChartPartition A) := existsPartition A
  have hm : mInt A P g = ∑ j, ∫ y in (A.chart j).target,
      hne.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y := by
    rw [mInt, dite_eq_left hne, integralWith]
  have hj := fun j => chartTerm_hasSum A V B Φ P g hne.some hc hC2 hg j
  have hpt : ∀ n z, g (Φ n z) * paramDens P (Φ n) z =
      ∑ j, hne.some.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z := by
    intro n z
    rw [← Finset.sum_mul, ← Finset.sum_mul, hne.some.sum_eq_one, one_mul]
  have hfun : ∀ n, (fun z => g (Φ n z) * paramDens P (Φ n) z) =
      fun z => ∑ j, hne.some.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z :=
    fun n => funext (hpt n)
  constructor
  · intro n
    rw [hfun n]
    exact integrable_finsetSum _ fun j _ => (hj j).1 n
  · rw [hm]
    have hs := hasSum_sum (s := Finset.univ) fun j _ => (hj j).2
    have hEq : (fun n => ∫ z in B n, g (Φ n z) * paramDens P (Φ n) z) =
        fun n => ∑ j, ∫ z in B n, hne.some.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z := by
      funext n
      rw [hfun n]
      exact integral_finsetSum _ fun j _ => (hj j).1 n
    rw [hEq]
    exact hs

end

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistHeightIntegralDecomposition
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw.SheetD

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.Tw

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def joinIdx (i : (k : K) → ι k) (j : Fin 2) : (o : Option K) → Tb ι o
  | none => j
  | some k => i k

theorem segre_split (u : (Σ o, Tb ι o) → ℂ) (J : (o : Option K) → Tb ι o) :
    segre u J = segre (basePart₂ u) (fun k => J (some k)) * u ⟨none, J none⟩ := by
  show ∏ o, u ⟨o, J o⟩ = (∏ k, u ⟨some k, J (some k)⟩) * u ⟨none, J none⟩
  rw [Fintype.prod_option, mul_comm]

theorem embL_apply (v : Fin 2 → ℂ) (w : ((k : K) → ι k) → ℂ) (J : (o : Option K) → Tb ι o) :
    embL v w J = w (fun k => J (some k)) * v (J none) := rfl

theorem embL_injective {v : Fin 2 → ℂ} (hv1 : v 1 = 1) :
    Function.Injective (embL v : (((k : K) → ι k) → ℂ) → _) := by
  intro w w' h
  funext i
  have := congrFun h (joinIdx i 1)
  simpa [embL_apply, joinIdx, hv1] using this

theorem glue_oldPart (u : (Σ o, Tb ι o) → ℂ) :
    glue (basePart₂ u) (fun j => u ⟨none, j⟩) = u := by
  funext q
  obtain ⟨o, i⟩ := q
  cases o <;> rfl

theorem oldPart_mem {p : ℕ} {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) : basePart₂ u ∈ mcPts Q := by
  refine ⟨oldPart_ne hu.1, fun f hf => ?_⟩
  have h1 : inc f ∈ twist p Q := Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)
  have h2 := hu.2 _ h1
  rw [← glue_oldPart u, eval_inc] at h2
  exact h2

theorem quad_eq_zero {p : ℕ} {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) :
    u ⟨none, (0 : Fin 2)⟩ ^ 2 + (p : ℂ) * u ⟨none, (1 : Fin 2)⟩ ^ 2 = 0 := by
  have h1 : (quad p : MRing (Tb ι)) ∈ twist p Q :=
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have h2 := hu.2 _ h1
  rwa [eval_quad] at h2

theorem second_ne_zero {p : ℕ} (hp : p ≠ 0) {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) : u ⟨none, (1 : Fin 2)⟩ ≠ 0 := by
  intro h0
  have h1 := quad_eq_zero hu
  rw [h0] at h1
  have h2 : u ⟨none, (0 : Fin 2)⟩ = 0 := by simpa using h1
  obtain ⟨i, hi⟩ := hu.1 none
  refine hi ?_
  have hi' : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
    have : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    exact this i
  rcases hi' with rfl | rfl
  · exact h2
  · exact h0

theorem glue_isSheet {p e : ℕ} {Q : Ideal (MRing ι)}
    {Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {v : Fin 2 → ℂ}
    (hv : v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0) (hv1 : v 1 ≠ 0) {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSheet Q (pj v Ψ) y w γ) :
    IsSheet (twist p Q) Ψ y (embL v w) (fun y' => glue (γ y') v) := by
  refine ⟨by rw [segre_glue, h.1], ?_⟩
  filter_upwards [h.2] with y' ⟨hd, hm, hΨ⟩
  refine ⟨?_, glue_mem_mcPts hm hv hv1, ?_⟩
  · refine differentiableAt_pi.mpr fun q => ?_
    obtain ⟨o, i⟩ := q
    cases o with
    | none => exact differentiableAt_const _
    | some k => exact differentiableAt_pi.mp hd ⟨k, i⟩
  · rw [segre_glue]; exact hΨ

open Classical in
theorem sheet_of_twist_sheet {p e : ℕ} (hp : p ≠ 0) {Q : Ideal (MRing ι)} (hQ : IsMultiHomogIdeal Q)
    (k0 : K) {Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {v : Fin 2 → ℂ}
    (hv : v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0) (hv1 : v 1 = 1) {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ' : (Fin e → ℂ) → (Σ o, Tb ι o) → ℂ}
    (h : IsSheet (twist p Q) Ψ y (embL v w) γ') :
    ∃ γ, IsSheet Q (pj v Ψ) y w γ := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hd0, hm0, hΨ0⟩ := h2.self_of_nhds
  have hρ : v 0 ^ 2 = -(p : ℂ) := by
    rw [hv1] at hv
    linear_combination hv
  have hρ0 : v 0 ≠ 0 := by
    intro h0
    rw [h0] at hρ
    have : (p : ℂ) = 0 := by simpa using hρ
    exact hp (by exact_mod_cast this)
  have hb0 := second_ne_zero hp hm0

  have hne : embL v w ≠ 0 := by
    intro h0
    rw [h1, h0, map_zero] at hΨ0
    have := congrFun hΨ0 0
    simp at this
  have hw : w ≠ 0 := by
    intro h0
    exact hne (by rw [h0, map_zero])
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  have hi' : w i ≠ 0 := hi
  have hseg : ∀ j : Fin 2, segre (basePart₂ (γ' y)) i * γ' y ⟨none, j⟩ = w i * v j := by
    intro j
    have := congrFun h1 (joinIdx i j)
    rw [segre_split, embL_apply] at this
    exact this
  have hm : segre (basePart₂ (γ' y)) i ≠ 0 := by
    intro h0
    have := hseg 1
    rw [h0, zero_mul, hv1, mul_one] at this
    exact hi' this.symm
  have hay : γ' y ⟨none, (0 : Fin 2)⟩ = v 0 * γ' y ⟨none, (1 : Fin 2)⟩ := by
    apply mul_left_cancel₀ hm
    have e0 := hseg 0
    have e1 := hseg 1
    rw [hv1, mul_one] at e1
    rw [e0]
    linear_combination (-(v 0)) * e1

  have hcont : ContinuousAt (fun y' => γ' y' ⟨none, (0 : Fin 2)⟩ + v 0 * γ' y' ⟨none, (1 : Fin 2)⟩) y :=
    ((differentiableAt_pi.mp hd0 _).continuousAt).add
      (continuousAt_const.mul (differentiableAt_pi.mp hd0 _).continuousAt)
  have hne2 : γ' y ⟨none, (0 : Fin 2)⟩ + v 0 * γ' y ⟨none, (1 : Fin 2)⟩ ≠ 0 := by
    rw [hay]
    have : v 0 * γ' y ⟨none, (1 : Fin 2)⟩ + v 0 * γ' y ⟨none, (1 : Fin 2)⟩ =
        2 * (v 0 * γ' y ⟨none, (1 : Fin 2)⟩) := by ring
    rw [this]
    exact mul_ne_zero two_ne_zero (mul_ne_zero hρ0 hb0)
  have hline : ∀ᶠ y' in 𝓝 y, γ' y' ⟨none, (0 : Fin 2)⟩ = v 0 * γ' y' ⟨none, (1 : Fin 2)⟩ := by
    filter_upwards [h2, hcont.eventually_ne hne2] with y' ⟨_, hm', _⟩ hn
    have hq := quad_eq_zero hm'
    have hz : (γ' y' ⟨none, (0 : Fin 2)⟩ - v 0 * γ' y' ⟨none, (1 : Fin 2)⟩) *
        (γ' y' ⟨none, (0 : Fin 2)⟩ + v 0 * γ' y' ⟨none, (1 : Fin 2)⟩) = 0 := by
      linear_combination hq - γ' y' ⟨none, (1 : Fin 2)⟩ ^ 2 * hρ
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hn)

  let c : K → (Fin e → ℂ) → ℂ := fun k y' => if k = k0 then γ' y' ⟨none, (1 : Fin 2)⟩ else 1
  let γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' q => c q.1 y' * basePart₂ (γ' y') q
  have hprod : ∀ y', ∏ k, c k y' = γ' y' ⟨none, (1 : Fin 2)⟩ := by
    intro y'
    simp [c, Finset.prod_ite_eq']
  have hkey : ∀ y', γ' y' ⟨none, (0 : Fin 2)⟩ = v 0 * γ' y' ⟨none, (1 : Fin 2)⟩ →
      embL v (segre (γ y')) = segre (γ' y') := by
    intro y' hl
    funext J
    have hj : γ' y' ⟨none, J none⟩ = γ' y' ⟨none, (1 : Fin 2)⟩ * v (J none) := by
      have hJ : ∀ j : Fin 2, γ' y' ⟨none, j⟩ = γ' y' ⟨none, (1 : Fin 2)⟩ * v j := by
        intro j
        have : j = 0 ∨ j = 1 := by
          have : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
          exact this j
        rcases this with rfl | rfl
        · rw [hl]; ring
        · rw [hv1, mul_one]
      exact hJ _
    have hsm : segre (γ y') = (∏ k, c k y') • segre (basePart₂ (γ' y')) :=
      segre_smul (fun k => c k y') (basePart₂ (γ' y'))
    have hs : segre (γ y') (fun k => J (some k)) =
        γ' y' ⟨none, (1 : Fin 2)⟩ * segre (basePart₂ (γ' y')) (fun k => J (some k)) := by
      rw [hsm, hprod]
      rfl
    rw [embL_apply, segre_split, hj, hs]
    ring
  refine ⟨γ, embL_injective hv1 ?_, ?_⟩
  · rw [hkey y hay, h1]
  · filter_upwards [h2, hline] with y' ⟨hd, hm', hΨ'⟩ hl
    refine ⟨?_, ?_, ?_⟩
    · refine differentiableAt_pi.mpr fun q => ?_
      have hc : DifferentiableAt ℂ (c q.1) y' := by
        by_cases hk : q.1 = k0
        · simp only [c, hk, if_true]
          exact differentiableAt_pi.mp hd _
        · simp only [c, hk, if_false]
          exact differentiableAt_const _
      exact hc.mul (differentiableAt_pi.mp hd _)
    · refine mcPts_smul hQ (fun k => c k y') (fun k => ?_) (oldPart_mem hm')
      by_cases hk : k = k0
      · simpa [c, hk] using second_ne_zero hp hm'
      · simp [c, hk]
    · show Ψ (embL v (segre (γ y'))) = _
      rw [hkey y' hl]
      exact hΨ'

theorem density_twist : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (Q : Ideal (MRing ι)) (e : ℕ) (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L' : Fin e → HermLine (Tb ι)) (A' : HermLine (Tb ι)) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι) (v : Fin 2 → ℂ), p ≠ 0 → IsArithVar Q (e + 1) → IsArithVar (twist p Q) (e + 1) → IsGoodProj (twist p Q) Ψ → (∀ j, IsSmoothHerm (L' j)) → IsSmoothHerm A' → IsSectionOn (twist p Q) A' (inc s) → (v = vPlus p ∨ v = vMinus p) → (∀ j, ∀ z ∈ mcPts Q, (L' j).h (glue z v) = (L j).h z) → (∀ z ∈ mcPts Q, A'.h (glue z v) = A.h z) → ∀ᵐ y, ∀ w, sheetDensity (twist p Q) Ψ (pot L') (logNorm A' (inc s)) y (embL v w) = sheetDensity Q (pj v Ψ) (pot L) (logNorm A s) y w := by
  intro K _ ι _ p Q e Ψ L' A' L A s v hp hQ hT hΨ hL' hA' hs hv hLh hAh
  have hv1 : v 1 = 1 := by
    rcases hv with rfl | rfl <;> simp [vPlus, vMinus]
  have hvq : v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0 := by
    rcases hv with rfl | rfl
    · exact vPlus_root p
    · exact vMinus_root p
  obtain ⟨k0⟩ := hQ.1
  have hQh : IsMultiHomogIdeal Q := hQ.2.1.2.1
  filter_upwards [sheetIndep (Option K) (Tb ι) (twist p Q) e Ψ L' A' (inc s) hT hΨ hL' hA' hs] with y hind
  intro w
  by_cases hγ : ∃ γ, IsSheet Q (pj v Ψ) y w γ
  · have hg := hγ.choose_spec
    have hg1 := glue_isSheet hvq (by rw [hv1]; exact one_ne_zero) hg
    have hex : ∃ γ', IsSheet (twist p Q) Ψ y (embL v w) γ' := ⟨_, hg1⟩
    unfold sheetDensity
    rw [dite_eq_left hex, dite_eq_left hγ, hind _ _ _ hex.choose_spec hg1]
    have hlog : logNorm A' (inc s) (glue (hγ.choose y) v) = logNorm A s (hγ.choose y) := by
      rw [logNorm, logNorm, eval_inc, hAh _ hg.2.self_of_nhds.2.1]
    have hma : maDensity (fun j y' => pot L' j (glue (hγ.choose y') v)) y =
        maDensity (fun j y' => pot L j (hγ.choose y')) y := by
      refine maDensity_congr_of_eventuallyEq fun j => ?_
      filter_upwards [hg.2] with y' ⟨_, hm, _⟩
      simp only [pot, hLh j _ hm]
    rw [hlog, hma]
  · have hno : ¬ ∃ γ', IsSheet (twist p Q) Ψ y (embL v w) γ' := fun ⟨γ', h⟩ =>
      hγ (sheet_of_twist_sheet hp hQh k0 hvq hv1 h)
    unfold sheetDensity
    rw [dite_eq_right hno, dite_eq_right hγ]

end GlobalTheory.CompanionTheory.Ar.Tw.SheetD
end
end

