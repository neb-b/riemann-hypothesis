module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ContinuousNormMulOneAddAbsLogPow
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0007
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FibreTwistEqUnionEmbeddings
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem oldPart_mem_mcPts {p : ℕ} {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) : basePart₂ u ∈ mcPts Q := by
  refine ⟨fun k => hu.1 (some k), fun f hf => ?_⟩
  have hg : glue (basePart₂ u) (fun j => u ⟨none, j⟩) = u := by
    funext ⟨o, i⟩
    cases o <;> rfl
  have h1 := hu.2 (inc f) (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))
  have h2 := eval_inc (basePart₂ u) (fun j => u ⟨none, j⟩) f
  rw [hg] at h2
  rw [← h2]
  exact h1

theorem exists_segre_eq_embL [Nonempty K] {p : ℕ} {Q : Ideal (MRing ι)} (hQ : IsMultiHomogIdeal Q)
    {u : (Σ o, Tb ι o) → ℂ} (hu : u ∈ mcPts (twist p Q)) {v : Fin 2 → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hv : ∀ j : Fin 2, u ⟨none, j⟩ = c * v j) :
    ∃ z ∈ mcPts Q, segre u = embL v (segre z) := by
  classical
  obtain ⟨k0⟩ := ‹Nonempty K›
  refine ⟨_, mcPts_smul hQ (fun k => if k = k0 then c else 1)
    (fun k => by by_cases h : k = k0 <;> simp [h, hc]) (oldPart_mem_mcPts hu), ?_⟩
  funext J
  show ∏ o, u ⟨o, J o⟩ =
    (∏ k, (if k = k0 then c else 1) * basePart₂ u ⟨k, J (some k)⟩) * v (J none)
  rw [Fintype.prod_option, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k0]
  have h1 : u ⟨none, J none⟩ = c * v (J none) := hv (J none)
  rw [h1]
  simp only [Finset.mem_univ, if_true]
  have h2 : ∀ k, basePart₂ u ⟨k, J (some k)⟩ = u ⟨some k, J (some k)⟩ := fun _ => rfl
  simp only [h2]
  ring

theorem new_coords {p : ℕ} {Q : Ideal (MRing ι)} {u : (Σ o, Tb ι o) → ℂ}
    (hu : u ∈ mcPts (twist p Q)) :
    ∃ c : ℂ, c ≠ 0 ∧ ((∀ j : Fin 2, u ⟨none, j⟩ = c * vPlus p j) ∨
      (∀ j : Fin 2, u ⟨none, j⟩ = c * vMinus p j)) := by
  have hq : u ⟨none, (0 : Fin 2)⟩ ^ 2 + (p : ℂ) * u ⟨none, (1 : Fin 2)⟩ ^ 2 = 0 := by
    rw [← eval_quad]
    exact hu.2 _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hy : u ⟨none, (1 : Fin 2)⟩ ≠ 0 := by
    intro h0
    rw [h0] at hq
    have hx : u ⟨none, (0 : Fin 2)⟩ = 0 := by simpa using hq
    obtain ⟨i, hi⟩ := hu.1 none
    have hall : ∀ j : Fin 2, u ⟨none, j⟩ = 0 := by
      intro j
      fin_cases j
      · exact hx
      · exact h0
    exact hi (hall i)
  refine ⟨u ⟨none, (1 : Fin 2)⟩, hy, ?_⟩
  have hf : (u ⟨none, (0 : Fin 2)⟩ - u ⟨none, (1 : Fin 2)⟩ * cRoot p) *
      (u ⟨none, (0 : Fin 2)⟩ + u ⟨none, (1 : Fin 2)⟩ * cRoot p) = 0 := by
    have : (u ⟨none, (0 : Fin 2)⟩ - u ⟨none, (1 : Fin 2)⟩ * cRoot p) *
      (u ⟨none, (0 : Fin 2)⟩ + u ⟨none, (1 : Fin 2)⟩ * cRoot p) =
        u ⟨none, (0 : Fin 2)⟩ ^ 2 - u ⟨none, (1 : Fin 2)⟩ ^ 2 * cRoot p ^ 2 := by ring
    rw [this, cRoot_sq, ← hq]
    ring
  rcases mul_eq_zero.mp hf with h | h
  · left
    intro j
    fin_cases j
    · simpa [vPlus] using sub_eq_zero.mp h
    · simp [vPlus]
  · right
    intro j
    fin_cases j
    · simpa [vMinus] using eq_neg_of_add_eq_zero_left h
    · simp [vMinus]

theorem embL_image_subset {e : ℕ} {p : ℕ} {Q : Ideal (MRing ι)}
    {Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ} {v : Fin 2 → ℂ}
    (hv : v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0) (hv1 : v 1 ≠ 0) :
    embL v '' fibre Q (pj v Ψ) y ⊆ fibre (twist p Q) Ψ y := by
  rintro _ ⟨w, ⟨z, hz, rfl, hΨ⟩, rfl⟩
  exact ⟨glue z v, glue_mem_mcPts hz hv hv1, segre_glue z v, hΨ⟩

theorem fibre_twist : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (Q : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ),
    p ≠ 0 → Nonempty K → IsMultiHomogIdeal Q →
    fibre (twist p Q) Ψ y =
      embL (vPlus p) '' fibre Q (pj (vPlus p) Ψ) y ∪
        embL (vMinus p) '' fibre Q (pj (vMinus p) Ψ) y := by
  intro K _ ι _ p Q e Ψ y _ hK hQ
  refine Set.Subset.antisymm ?_ (Set.union_subset
    (embL_image_subset (vPlus_root p) (by simp [vPlus]))
    (embL_image_subset (vMinus_root p) (by simp [vMinus])))
  rintro w ⟨u, hu, rfl, hΨ⟩
  obtain ⟨c, hc, h | h⟩ := new_coords hu
  · obtain ⟨z, hz, hs⟩ := exists_segre_eq_embL hQ hu hc h
    refine Or.inl ⟨segre z, ⟨z, hz, rfl, ?_⟩, hs.symm⟩
    show Ψ (embL (vPlus p) (segre z)) = _
    rw [← hs]
    exact hΨ
  · obtain ⟨z, hz, hs⟩ := exists_segre_eq_embL hQ hu hc h
    refine Or.inr ⟨segre z, ⟨z, hz, rfl, ?_⟩, hs.symm⟩
    show Ψ (embL (vMinus p) (segre z)) = _
    rw [← hs]
    exact hΨ

end GlobalTheory.CompanionTheory.Ar.Tw.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDomainUnitaryTriangular
section
open Complex Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_extension_polydisc_of_log_growth :
    ∀ (n : ℕ) (S : Finset (Fin n)) (φ : (Fin n → ℂ) → ℂ) (ρ C : ℝ) (N : ℕ), 0 < ρ →
      DifferentiableOn ℂ φ {z ∈ ball (0 : Fin n → ℂ) ρ | ∀ i ∈ S, z i ≠ 0} →
      (∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) →
        ‖φ z‖ ≤ C * (1 + ∑ i ∈ S, |Real.log ‖z i‖|) ^ N) →
      ∃ ψ : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ ψ (ball 0 ρ) ∧
        ∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) → ψ z = φ z := by
  intro n S φ ρ C N _ hφ hb
  have hg : HasLogGrowth S id (ball (0 : Fin n → ℂ) ρ) φ := fun K hK _ =>
    ⟨C, N, fun z hz hB => hb z (hK hz) (notMem_coordDivisor.1 hB)⟩
  obtain ⟨ψ, hψ, he⟩ := HasLogGrowth.exists_differentiableOn_extension isOpen_ball
    (hφ.mono fun z hz => ⟨hz.1, notMem_coordDivisor.1 hz.2⟩) hg
  exact ⟨ψ, hψ, fun z hz h0 => he ⟨hz, notMem_coordDivisor.2 h0⟩⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HorizontalDivSuppTwistStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontal_divSupp_twist_eq_image : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (P : Ideal (MRing ι)) (s : MRing ι), (∀ W, W ∈ divSupp P s → IsHorizontal W → (twist p W).IsPrime) → {W' | W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'} = twist p '' {W | W ∈ divSupp P s ∧ IsHorizontal W} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.horizontal_divSupp_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.horizontal_divSupp_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.horizontal_divSupp_twist <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralNormSqMobDMulCompMobStatement
section
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_normSq_mobD_mul_comp_mob' : ∀ (g : Matrix (Fin 2) (Fin 2) ℂ), IsUnit g.det → ∀ f : ℂ → ℝ, ∫ a : ℂ, Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g a) * f (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g a) = ∫ b : ℂ, f b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_normSq_mobD_mul_comp_mob | exact GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_normSq_mobD_mul_comp_mob | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_normSq_mobD_mul_comp_mob <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantCofactorExpansion
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem mdisc_split_fibre_direction : ∀ (d : ℕ), (∀ (f : Fin (d + 1) → ℂ) (Bm : Fin (d + 1) → Matrix (Fin d) (Fin d) ℂ), ((d + 1).factorial : ℂ) * mdisc (fun r => Matrix.of fun p q : Fin (d + 1) => Fin.cases (Fin.cases (f r) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => Bm r p' q') q) p) = ∑ r, f r * ((d.factorial : ℂ) * mdisc fun s => Bm (r.succAbove s))) ∧ ∃ Λ : MultilinearMap (RingHom.id ℂ) (fun _ : Fin d => Matrix (Fin d) (Fin d) ℂ) ℂ, (∀ Bm, Λ Bm = mdisc Bm) ∧ ∀ (π : Equiv.Perm (Fin d)) Bm, Λ (Bm ∘ π) = Λ Bm :=
  PositivityTheory.Xgp.t_fib_mdisc

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereChartDensityIntegral
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

private theorem hessC_congr_of_eventuallyEq' {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : f =ᶠ[𝓝 z] g) : ReciprocityTheory.AnForm.hessC f z = ReciprocityTheory.AnForm.hessC g z := by
  have h2 : fderiv ℝ (fderiv ℝ f) z = fderiv ℝ (fderiv ℝ g) z := (h.fderiv (𝕜 := ℝ)).fderiv_eq
  unfold ReciprocityTheory.AnForm.hessC
  rw [h2]

private theorem maDens_congr_of_hessC_eq {D : ℕ} {f g : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ k, f k =ᶠ[𝓝 z] g k) : ReciprocityTheory.AnForm.maDens f z = ReciprocityTheory.AnForm.maDens g z := by
  unfold ReciprocityTheory.AnForm.maDens
  rw [show (fun k => ReciprocityTheory.AnForm.hessC (f k) z) = (fun k => ReciprocityTheory.AnForm.hessC (g k) z) from
    funext fun k => hessC_congr_of_eventuallyEq' (h k)]

theorem paramDens_eq_normSq_mul_locDens {e : ℕ} {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) {V : Set (Fin e → ℂ)} {Φ : (Fin e → ℂ) → X} (P : Fin e → LocPot X)
    (j : Fin A.n) (hΦ : IsParam A V Φ) {z : Fin e → ℂ} (hzV : z ∈ V)
    (hz : Φ z ∈ (A.chart j).source) (hc : ∀ i, IsTwiceDifferentiableAt A (P i) (Φ z)) :
    paramDens P Φ z = Complex.normSq (ReciprocityTheory.AnForm.A.jacC (A.chart j ∘ Φ) z).det *
      locDens A P j ((A.chart j ∘ Φ) z) := by
  have hcont : ContinuousAt Φ z := hΦ.2.1.continuousAt (hΦ.1.mem_nhds hzV)
  have hev : ∀ᶠ z' in 𝓝 z, Φ z' ∈ (A.chart j).source :=
    hcont.preimage_mem_nhds ((A.chart j).open_source.mem_nhds hz)
  have han : AnalyticAt ℂ (A.chart j ∘ Φ) z := hΦ.2.2.2 j z ⟨hzV, hz⟩
  have hinv : (A.chart j).symm ((A.chart j ∘ Φ) z) = Φ z := (A.chart j).left_inv hz
  have key := ReciprocityTheory.AnForm.A.maDens_comp (fun k => (P k).φ (Φ z) ∘ (A.chart j).symm)
    (A.chart j ∘ Φ) z han (fun k => hc k j hz)
  have h1 : paramDens P Φ z = ReciprocityTheory.AnForm.maDens
      (fun k => ((P k).φ (Φ z) ∘ (A.chart j).symm) ∘ (A.chart j ∘ Φ)) z := by
    unfold paramDens
    apply maDens_congr_of_hessC_eq
    intro k
    filter_upwards [hev] with z' hz'
    simp only [Function.comp_apply, (A.chart j).left_inv hz']
  have h2 : locDens A P j ((A.chart j ∘ Φ) z) = ReciprocityTheory.AnForm.maDens
      (fun k => (P k).φ (Φ z) ∘ (A.chart j).symm) ((A.chart j ∘ Φ) z) := by
    unfold ReciprocityTheory.AnForm.M.locDens
    rw [hinv]
    rfl
  rw [h1, key, h2, mul_comm]

theorem param_chart_changeOfVariables : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (V B : Set (Fin e → ℂ)) (Φ : (Fin e → ℂ) → X) (P : Fin e → LocPot X) (g : X → ℝ) (j : Fin A.n), IsParam A V Φ → MeasurableSet B → B ⊆ V → (∀ z ∈ B, Φ z ∈ (A.chart j).source) → (∀ z ∈ B, ∀ i, IsTwiceDifferentiableAt A (P i) (Φ z)) → MeasurableSet ((A.chart j ∘ Φ) '' B) ∧ (IntegrableOn (fun y => g ((A.chart j).symm y) * locDens A P j y) ((A.chart j ∘ Φ) '' B) ↔ IntegrableOn (fun z => g (Φ z) * paramDens P Φ z) B) ∧ ∫ y in (A.chart j ∘ Φ) '' B, g ((A.chart j).symm y) * locDens A P j y = ∫ z in B, g (Φ z) * paramDens P Φ z := by
  intro e X _ _ _ A V B Φ P g j hΦ hB hBV hsrc hc2
  have han : ∀ z ∈ B, AnalyticAt ℂ (A.chart j ∘ Φ) z := fun z hz => hΦ.2.2.2 j z ⟨hBV hz, hsrc z hz⟩
  have hτd : ∀ z ∈ B, HasFDerivWithinAt (A.chart j ∘ Φ)
      ((fderiv ℂ (A.chart j ∘ Φ) z).restrictScalars ℝ) B z := fun z hz =>
    ((han z hz).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hinj : Set.InjOn (A.chart j ∘ Φ) B := by
    intro x hx y hy hxy
    apply hΦ.2.2.1 (hBV hx) (hBV hy)
    have h := congrArg (A.chart j).symm hxy
    simpa only [Function.comp_apply, (A.chart j).left_inv (hsrc x hx),
      (A.chart j).left_inv (hsrc y hy)] using h
  have hdet : ∀ z ∈ B, |((fderiv ℂ (A.chart j ∘ Φ) z).restrictScalars ℝ).det| =
      Complex.normSq (ReciprocityTheory.AnForm.A.jacC (A.chart j ∘ Φ) z).det := by
    intro z hz
    rw [← ((han z hz).differentiableAt.hasFDerivAt.restrictScalars ℝ).fderiv,
      ReciprocityTheory.AnForm.A.det_fderiv_real_eq_normSq _ _ (han z hz).differentiableAt]
    exact abs_of_nonneg (Complex.normSq_nonneg _)
  have hpt : Set.EqOn (fun z => |((fderiv ℂ (A.chart j ∘ Φ) z).restrictScalars ℝ).det| •
      (g ((A.chart j).symm ((A.chart j ∘ Φ) z)) * locDens A P j ((A.chart j ∘ Φ) z)))
      (fun z => g (Φ z) * paramDens P Φ z) B := by
    intro z hz
    simp only
    rw [hdet z hz, smul_eq_mul,
      paramDens_eq_normSq_mul_locDens A P j hΦ (hBV hz) (hsrc z hz) (hc2 z hz)]
    have hl : (A.chart j).symm ((A.chart j ∘ Φ) z) = Φ z := (A.chart j).left_inv (hsrc z hz)
    rw [hl]
    ring
  refine ⟨measurable_image_of_fderivWithin hB hτd hinj, ?_, ?_⟩
  · rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hB hτd hinj]
    exact integrableOn_congr_fun hpt hB
  · rw [integral_image_eq_integral_abs_det_fderiv_smul volume hB hτd hinj]
    exact setIntegral_congr_fun hB hpt

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityDiagonalLevi
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.MaDiag

theorem matrix_eq_of_form {e : ℕ} (A B : Matrix (Fin e) (Fin e) ℂ)
    (h : ∀ w : Fin e → ℂ, w ⬝ᵥ (A *ᵥ star w) = w ⬝ᵥ (B *ᵥ star w)) : A = B := by
  set C := A - B with hC
  have hΦ : ∀ w : Fin e → ℂ, w ⬝ᵥ (C *ᵥ star w) = 0 := by
    intro w
    rw [hC, Matrix.sub_mulVec, dotProduct_sub, h w, sub_self]
  have expand : ∀ (u w : Fin e → ℂ) (c : ℂ), (u + c • w) ⬝ᵥ (C *ᵥ star (u + c • w)) =
      u ⬝ᵥ (C *ᵥ star u) + star c * (u ⬝ᵥ (C *ᵥ star w)) + c * (w ⬝ᵥ (C *ᵥ star u)) +
        c * star c * (w ⬝ᵥ (C *ᵥ star w)) := by
    intro u w c
    simp only [star_add, star_smul, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
      dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have hsI : (star Complex.I : ℂ) = -Complex.I := Complex.conj_I
  have hpair : ∀ u w : Fin e → ℂ, u ⬝ᵥ (C *ᵥ star w) = 0 := by
    intro u w
    have h1 := expand u w 1
    have h2 := expand u w Complex.I
    rw [hΦ (u + (1 : ℂ) • w), hΦ u, hΦ w, star_one] at h1
    rw [hΦ (u + Complex.I • w), hΦ u, hΦ w, hsI] at h2
    linear_combination (-1 / 2 : ℂ) * h1 + (-Complex.I / 2) * h2 +
      ((u ⬝ᵥ (C *ᵥ star w) - w ⬝ᵥ (C *ᵥ star u)) / 2) * Complex.I_sq
  ext i j
  have hs : star (Pi.single j (1 : ℂ) : Fin e → ℂ) = Pi.single j 1 := by
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  have := hpair (Pi.single i 1) (Pi.single j 1)
  rw [hs] at this
  simpa [C, sub_eq_zero] using this

private theorem pair_inv_mul_eq_of_mul_self_eq_one (c d : ℂ) (a b p q : ℝ) :
    c * ((((a + q : ℝ) : ℂ) + Complex.I * ((b - p : ℝ) : ℂ)) / 4 * star d) =
      ((((c.re * d.re * a + c.re * d.im * b + c.im * d.re * p + c.im * d.im * q) +
        ((Complex.I * c).re * (Complex.I * d).re * a + (Complex.I * c).re * (Complex.I * d).im * b +
          (Complex.I * c).im * (Complex.I * d).re * p +
            (Complex.I * c).im * (Complex.I * d).im * q)) / 4 : ℝ) : ℂ) +
      Complex.I * ((((c.re * (Complex.I * d).re * a + c.re * (Complex.I * d).im * b +
          c.im * (Complex.I * d).re * p + c.im * (Complex.I * d).im * q) -
        ((Complex.I * c).re * d.re * a + (Complex.I * c).re * d.im * b +
          (Complex.I * c).im * d.re * p + (Complex.I * c).im * d.im * q)) / 4 : ℝ) : ℂ) := by
  have h4 : ∀ X : ℂ, X / 4 = ((1 / 4 : ℝ) : ℂ) * X := fun X => by push_cast; ring
  rw [h4]
  apply Complex.ext <;> simp <;> ring

theorem dot_hessC_star {e : ℕ} (f : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ)
    (hf : ContDiffAt ℝ 2 f z) (w : Fin e → ℂ) :
    w ⬝ᵥ (hessC f z *ᵥ star w) = (levi f z w : ℂ) := by
  set H := fderiv ℝ (fderiv ℝ f) z with hH
  have hsymm : ∀ x y, H x y = H y x := fun x y =>
    hf.isSymmSndFDerivAt minSmoothness_of_isRCLikeNormedField.le x y
  have hsmul : ∀ (c : ℂ) (u : Fin e → ℂ), c • u = c.re • u + c.im • (Complex.I • u) := by
    intro c u
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  have hHs : ∀ (c d : ℂ) (u v : Fin e → ℂ), H (c • u) (d • v) =
      c.re * d.re * H u v + c.re * d.im * H u (Complex.I • v) +
        c.im * d.re * H (Complex.I • u) v + c.im * d.im * H (Complex.I • u) (Complex.I • v) := by
    intro c d u v
    rw [hsmul c u, hsmul d v]
    simp only [map_add (f := _), map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul]
    ring
  set E := fun i : Fin e => (Pi.single i (1 : ℂ) : Fin e → ℂ) with hE
  have hw : ∀ x : Fin e → ℂ, x = ∑ i, x i • E i := by
    intro x
    ext k
    simp [hE, Finset.sum_apply, Pi.single_apply]
  have hHsum : ∀ x y : Fin e → ℂ, H x y = ∑ i, ∑ j, H (x i • E i) (y j • E j) := by
    intro x y
    conv_lhs => rw [hw x, hw y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, ContinuousLinearMap.sum_apply]
    exact Finset.sum_comm
  have hpair : ∀ i j, w i * (hessC f z i j * star (w j)) =
      (((H (w i • E i) (w j • E j) + H ((Complex.I * w i) • E i) ((Complex.I * w j) • E j)) / 4 : ℝ) : ℂ) +
        Complex.I * (((H (w i • E i) ((Complex.I * w j) • E j) -
          H ((Complex.I * w i) • E i) (w j • E j)) / 4 : ℝ) : ℂ) := by
    intro i j
    have hx : hessC f z i j = (((H (E i) (E j) + H (Complex.I • E i) (Complex.I • E j) : ℝ) : ℂ) +
        Complex.I * ((H (E i) (Complex.I • E j) - H (Complex.I • E i) (E j) : ℝ) : ℂ)) / 4 := rfl
    rw [hx, hHs (w i) (w j), hHs (Complex.I * w i) (Complex.I * w j), hHs (w i) (Complex.I * w j),
      hHs (Complex.I * w i) (w j)]
    exact pair_inv_mul_eq_of_mul_self_eq_one (w i) (w j) _ _ _ _
  have hanti : ∀ F : Fin e → Fin e → ℝ, (∀ i j, F i j = -F j i) → ∑ i, ∑ j, F i j = 0 := by
    intro F hF
    have h1 : ∑ i, ∑ j, F i j = ∑ j, ∑ i, F i j := Finset.sum_comm
    have h2 : ∑ j, ∑ i, F i j = -∑ j, ∑ i, F j i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => hF i j)
    linarith
  have hQ0 : ∑ i, ∑ j, ((H (w i • E i) ((Complex.I * w j) • E j) -
      H ((Complex.I * w i) • E i) (w j • E j)) / 4 : ℝ) = 0 := by
    apply hanti
    intro i j
    rw [hsymm (w i • E i), hsymm ((Complex.I * w i) • E i)]
    ring
  have hLHS : w ⬝ᵥ (hessC f z *ᵥ star w) = ∑ i, ∑ j, w i * (hessC f z i j * star (w j)) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  have hlevi : levi f z w = (H w w + H (Complex.I • w) (Complex.I • w)) / 4 := rfl
  rw [hLHS]
  simp_rw [hpair]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib), Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, ← Complex.ofReal_sum]
  rw [hQ0, Complex.ofReal_zero, mul_zero, add_zero, hlevi, hHsum w w,
    hHsum (Complex.I • w) (Complex.I • w)]
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 1
  simp only [add_div, Finset.sum_add_distrib, Finset.sum_div]

theorem dot_congr_diag {e : ℕ} (dd : Fin e → ℝ) (M : Matrix (Fin e) (Fin e) ℂ) (w : Fin e → ℂ) :
    w ⬝ᵥ ((Mᵀ * Matrix.diagonal (fun q => (dd q : ℂ)) * M.map (starRingEnd ℂ)) *ᵥ star w) =
      ((∑ q, dd q * ‖(M *ᵥ w) q‖ ^ 2 : ℝ) : ℂ) := by
  have hs : M.map (starRingEnd ℂ) *ᵥ star w = star (M *ᵥ w) := by
    ext q
    simp [Matrix.mulVec, dotProduct, star_sum]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro q _
  rw [← Complex.mul_conj']
  simp only [Complex.star_def]
  ring

theorem det_congr_diag {e : ℕ} (dd : Fin e → ℝ) (M : Matrix (Fin e) (Fin e) ℂ) :
    (Mᵀ * Matrix.diagonal (fun q => (dd q : ℂ)) * M.map (starRingEnd ℂ)).det =
      (((∏ q, dd q) * ‖M.det‖ ^ 2 : ℝ) : ℂ) := by
  have hc : (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det := by
    rw [RingHom.map_det]
    rfl
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, hc]
  push_cast
  rw [← Complex.mul_conj']
  ring

theorem maDens_diag_levi (e : ℕ) (φ : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ) (dd : Fin e → ℝ)
    (M : Matrix (Fin e) (Fin e) ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hl : ∀ v, levi φ z v = ∑ q, dd q * ‖(M *ᵥ v) q‖ ^ 2) :
    maDens (fun _ => φ) z =
      (e.factorial : ℝ) * (2 / Real.pi) ^ e * (∏ q, dd q) * ‖M.det‖ ^ 2 := by
  have hH : hessC φ z = Mᵀ * Matrix.diagonal (fun q => (dd q : ℂ)) * M.map (starRingEnd ℂ) := by
    apply matrix_eq_of_form
    intro w
    rw [dot_hessC_star φ z hφ w, dot_congr_diag, hl w]
  simp only [maDens]
  rw [hH, ReciprocityTheory.AnForm.A.mdisc_const, det_congr_diag, Complex.ofReal_re]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.MaDiag
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RingKrullDimTwistSuccStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_twist_succ : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), W.IsPrime → ringKrullDim (MRing (Tb ι) ⧸ twist p W) = ringKrullDim (MRing ι ⧸ W) + 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.ringKrullDim_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.ringKrullDim_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.ringKrullDim_twist <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodenseStatement
section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_boundary_closed_and_codense : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → IsClosed (bdry s) ∧ Dense (bdry s)ᶜ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Bdry.bdry_isClosed_dense_compl | exact GlobalTheory.CompanionTheory.Ar.Bdry.bdry_isClosed_dense_compl | (intros; apply GlobalTheory.CompanionTheory.Ar.Bdry.bdry_isClosed_dense_compl <;> assumption)
end

