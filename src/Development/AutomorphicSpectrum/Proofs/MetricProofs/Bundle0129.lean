module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XSqLimit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0060
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0050
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0118
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0127
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0128
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoC2
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralTendstoOffDivisor
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0104
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0107
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0124
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0106
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0123
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0023

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSquareRegularizedConvergence
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.analytic_square_regularized_convergence : Inputs → ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (w : Fin (d + 2) → Option σ), MIntegrable Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH ∧ Tendsto (fun t => mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (Q.gT t)) (𝓝[>] 0) (𝓝 (mInt Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH)) := by
  intro hI d σ _ SY a₀ ε Q w
  classical
  have hCS : ConvergenceSignedStatement := hI.1.2.1
  have ht0 : 0 < Q.SW.t₀ := (Q.SW.reg none).1
  let mm : σ × Fin 2 → Option σ := fun i => if i.2 = 0 then some i.1 else if i.1 = a₀ then none else some i.1
  let c : σ × Fin 2 → ℝ := fun i => 1 / 2 * (ε i.1 : ℝ)
  have hph : ∀ x, 1 / 2 * ∑ a : σ, (ε a : ℝ) * (SY.ph a (Q.q 0 x) + SY.ph a (Q.q 1 x)) = ∑ i : σ × Fin 2, c i * Q.SW.ph (mm i) x := by
    intro x
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.sum_univ_two]
    have e0 : Q.SW.ph (mm (a, 0)) x = SY.ph a (Q.q 0 x) := by simp [mm, Q.ph0]
    have e1 : Q.SW.ph (mm (a, 1)) x = SY.ph a (Q.q 1 x) := by
      by_cases ha : a = a₀
      · subst ha
        simp [mm, Q.ph1]
      · simp [mm, ha, Q.ph0]
        exact congrFun (Q.base_ph a ha) x
    rw [e0, e1]
    simp only [c]
    ring
  have hphT : ∀ t x, 1 / 2 * ∑ a : σ, (ε a : ℝ) * (SY.phT a t (Q.q 0 x) + SY.phT a t (Q.q 1 x)) = ∑ i : σ × Fin 2, c i * Q.SW.phT (mm i) t x := by
    intro t x
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.sum_univ_two]
    have e0 : Q.SW.phT (mm (a, 0)) t x = SY.phT a t (Q.q 0 x) := by simp [mm, Q.phase_some_eq_comp_first_projection]
    have e1 : Q.SW.phT (mm (a, 1)) t x = SY.phT a t (Q.q 1 x) := by
      by_cases ha : a = a₀
      · subst ha
        simp [mm, Q.phase_none_eq_comp_second_projection]
      · simp [mm, ha, Q.phase_some_eq_comp_first_projection]
        exact congrFun (Q.base_phT a ha t) x
    rw [e0, e1]
    simp only [c]
    ring
  have hgH : Q.gH = fun x => logNormSec Q.L' Q.v x + (Q.cst + ∑ i, c i * Q.SW.ph (mm i) x) := by
    funext x
    simp only [AnSq.gH]
    rw [hph]
    ring
  have hgT : ∀ t, Q.gT t = fun x => logNormSec Q.L' Q.v x + (Q.cst + ∑ i, c i * Q.SW.phT (mm i) t x) := by
    intro t
    funext x
    simp only [AnSq.gT]
    rw [hphT]
    ring
  obtain ⟨hsI, hsE, hsT⟩ := PositivityTheory.Xgp.sq_limit.singular_part hI Q w
  obtain ⟨hrI, hrT⟩ := PositivityTheory.Xgp.sq_limit.regular hCS Q.SW w mm c Q.cst ht0
  refine ⟨?_, ?_⟩
  · rw [hgH]
    exact PositivityTheory.Xgp.sq_limit.mIntegrable_add' _ _ hsI hrI
  · rw [hgH, PositivityTheory.Xgp.sq_limit.mInt_add' _ _ hsI hrI]
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (logNormSec Q.L' Q.v) + mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (fun x => Q.cst + ∑ i, c i * Q.SW.phT (mm i) t x) = mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (Q.gT t) := by
      filter_upwards [hsE, Ioo_mem_nhdsGT ht0] with t ht htt
      rw [hgT t]
      refine (PositivityTheory.Xgp.sq_limit.mInt_add' _ _ ht ?_).symm
      apply PositivityTheory.Xgp.sq_limit.mIntegrable_of_continuous
      · intro i
        exact ReciprocityTheory.AnForm.M.isPotentialAdd _ _ _ (Q.SW.sing (w i)).1 (ReciprocityTheory.AnForm.M.isPotential_ofFun _ _ ((Q.SW.reg (w i)).2.2 t htt.1 htt.2.le).1)
      · exact continuous_const.add (continuous_finsetSum _ fun i _ => continuous_const.mul (ReciprocityTheory.AnForm.M.projLine_continuous_of_smooth _ ((Q.SW.reg (mm i)).2.2 t htt.1 htt.2.le).1))
    exact (hsT.add hrT).congr' hev
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingPiecesOfIntersectionAndResolution
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem embeddingPieces_of_resK (hA : ArithIntersectionSystemStatement)
    (hR : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) :
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.Statement :=
  have hInt : PtsIntegrableStatement := _root_.GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegrable_of_resK hR
  have hRes : ResExistsStatement := _root_.GlobalTheory.CompanionTheory.Ar.Giv.resExists_of_resK hR
  GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.PiecesAdditive.proof hInt)
    (_root_.GlobalTheory.CompanionTheory.Ar.Giv.pieceDegree hA hRes hInt)

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDimensionCount
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem dim_eq_of_holo_inverse {a b : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas a X) (B : FinHolAtlas b Y) (f : X → Y) (g : Y → X)
    (hf : HoloMap A B f) (hg : HoloMap B A g) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) (x : X) :
    a = b := by
  obtain ⟨j, hj⟩ := A.cover x
  obtain ⟨k, hk⟩ := B.cover (f x)
  have hu_t : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hj
  have hw_t : B.chart k (f x) ∈ (B.chart k).target := (B.chart k).map_source hk
  have hsu : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hj
  have hsw : (B.chart k).symm (B.chart k (f x)) = f x := (B.chart k).left_inv hk
  let F : (Fin a → ℂ) → (Fin b → ℂ) := B.chart k ∘ f ∘ (A.chart j).symm
  let G : (Fin b → ℂ) → (Fin a → ℂ) := A.chart j ∘ g ∘ (B.chart k).symm
  have hFu : F (A.chart j x) = B.chart k (f x) := by
    show B.chart k (f ((A.chart j).symm (A.chart j x))) = _
    rw [hsu]
  have hGw : G (B.chart k (f x)) = A.chart j x := by
    show A.chart j (g ((B.chart k).symm (B.chart k (f x)))) = _
    rw [hsw, hgf]
  have dF : DifferentiableAt ℂ F (A.chart j x) :=
    (hf.2 j k _ ⟨hu_t, by
      show f ((A.chart j).symm (A.chart j x)) ∈ (B.chart k).source
      rw [hsu]; exact hk⟩).differentiableAt
  have dG : DifferentiableAt ℂ G (B.chart k (f x)) :=
    (hg.2 k j _ ⟨hw_t, by
      show g ((B.chart k).symm (B.chart k (f x))) ∈ (A.chart j).source
      rw [hsw, hgf]; exact hj⟩).differentiableAt
  have e1 : G ∘ F =ᶠ[𝓝 (A.chart j x)] id := by
    have c : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
      hf.1.continuousAt.comp ((A.chart j).continuousAt_symm hu_t)
    have hs : ∀ᶠ v in 𝓝 (A.chart j x), (f ∘ (A.chart j).symm) v ∈ (B.chart k).source :=
      c.eventually ((B.chart k).open_source.mem_nhds (by
        show f ((A.chart j).symm (A.chart j x)) ∈ (B.chart k).source
        rw [hsu]; exact hk))
    filter_upwards [hs, (A.chart j).open_target.mem_nhds hu_t] with v h1 h2
    have h1' : f ((A.chart j).symm v) ∈ (B.chart k).source := h1
    show A.chart j (g ((B.chart k).symm (B.chart k (f ((A.chart j).symm v))))) = v
    rw [(B.chart k).left_inv h1', hgf, (A.chart j).right_inv h2]
  have e2 : F ∘ G =ᶠ[𝓝 (B.chart k (f x))] id := by
    have c : ContinuousAt (g ∘ (B.chart k).symm) (B.chart k (f x)) :=
      hg.1.continuousAt.comp ((B.chart k).continuousAt_symm hw_t)
    have hs : ∀ᶠ v in 𝓝 (B.chart k (f x)), (g ∘ (B.chart k).symm) v ∈ (A.chart j).source :=
      c.eventually ((A.chart j).open_source.mem_nhds (by
        show g ((B.chart k).symm (B.chart k (f x))) ∈ (A.chart j).source
        rw [hsw, hgf]; exact hj))
    filter_upwards [hs, (B.chart k).open_target.mem_nhds hw_t] with v h1 h2
    have h1' : g ((B.chart k).symm v) ∈ (A.chart j).source := h1
    show B.chart k (f ((A.chart j).symm (A.chart j (g ((B.chart k).symm v))))) = v
    rw [(A.chart j).left_inv h1', hfg, (B.chart k).right_inv h2]
  have d1 : (fderiv ℂ G (B.chart k (f x))).comp (fderiv ℂ F (A.chart j x)) = ContinuousLinearMap.id ℂ _ := by
    have dG' : DifferentiableAt ℂ G (F (A.chart j x)) := by rw [hFu]; exact dG
    have h := fderiv_comp (A.chart j x) dG' dF
    rw [e1.fderiv_eq, fderiv_id, hFu] at h
    exact h.symm
  have d2 : (fderiv ℂ F (A.chart j x)).comp (fderiv ℂ G (B.chart k (f x))) = ContinuousLinearMap.id ℂ _ := by
    have dF' : DifferentiableAt ℂ F (G (B.chart k (f x))) := by rw [hGw]; exact dF
    have h := fderiv_comp (B.chart k (f x)) dF' dG
    rw [e2.fderiv_eq, fderiv_id, hGw] at h
    exact h.symm
  let E : (Fin a → ℂ) ≃ₗ[ℂ] (Fin b → ℂ) := LinearEquiv.ofLinearMap
    (fderiv ℂ F (A.chart j x) : (Fin a → ℂ) →ₗ[ℂ] (Fin b → ℂ))
    (fderiv ℂ G (B.chart k (f x)) : (Fin b → ℂ) →ₗ[ℂ] (Fin a → ℂ))
    (LinearMap.ext fun v => congrArg (fun L : (Fin b → ℂ) →L[ℂ] (Fin b → ℂ) => L v) d2)
    (LinearMap.ext fun v => congrArg (fun L : (Fin a → ℂ) →L[ℂ] (Fin a → ℂ) => L v) d1)
  simpa using E.finrank_eq

theorem dim_eq_of_res {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {a b : ℕ}
    (R : AnLogRes P ⊤ a) (hJ : J = ⊤) (R' : AnLogRes P J b) (x : R'.X) : a = b := by
  subst hJ
  have hP : P ≤ imageZ id P := fun f hf => by
    show rename id f ∈ P
    rwa [rename_id_apply]
  obtain ⟨h, hh, ho⟩ := GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj K ι K ι id id P P ⊤ a b R R' isBlockMap_id hP
  obtain ⟨g, hg, go⟩ := GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj K ι K ι id id P P ⊤ b a R' R isBlockMap_id hP
  have hemp : ∀ z, z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun z hz => by
    have := hz.2 1 trivial
    simp at this
  have hgh : ∀ x, g (h x) = x := fun x => R'.inj _ _ (hemp _) (orbit_trans (go (h x)) (ho x))
  have hhg : ∀ x, h (g x) = x := fun x => R.inj _ _ (hemp _) (orbit_trans (ho (g x)) (go x))
  exact dim_eq_of_holo_inverse R.A R'.A g h hg hh hhg hgh (h x)

theorem flagAn_dim : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA
  have hk : ∀ k, k ∈ Set.range (id : K → K) ↔
      ((∀ p, M.blk p ≠ some k) ∨ ∃ p, (fun _ : Ψ × Fin N => True) p ∧ M.blk p = some k) := fun k =>
    ⟨fun _ => by
      by_cases h : ∀ p, M.blk p ≠ some k
      · exact Or.inl h
      · obtain ⟨p, hp⟩ := not_forall.1 h
        exact Or.inr ⟨p, trivial, not_not.1 hp⟩, fun _ => ⟨k, rfl⟩⟩
  obtain ⟨e, R, he, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.main K ι Φ y Ψ N j M n _ BM.Rb rfl (fun _ => True) K ι id id isBlockMap_id hk
  have R2 : AnLogRes (mCoordIdeal y) ⊤ e := R
  obtain ⟨z, hz, hJ⟩ :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.exists_mcPts_not_mem_mcPts FA.Re.arith FA.Re.R.nondeg
  obtain ⟨x, -⟩ := FA.Re.R.surj z hz hJ
  rw [← he fun _ => trivial]
  exact (dim_eq_of_res R2 FA.J_top FA.Re.R x).symm

end GlobalTheory.CompanionTheory.Ar.PB.WSq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightComparisonBetweenModels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

section Main
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W}

theorem tuo_const {A₁ B₁ C₂ : Type*} [UniformSpace B₁] (l : Filter C₂) (f : A₁ → B₁) (s : Set A₁) :
    TendstoUniformlyOn (fun _ : C₂ => f) f l s :=
  fun _ hu => Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu

theorem mem_Xo_of_proj_mem {Hd : HodgeData D} {M : XModel D} (S : LogLogRegularisationSetting M D.Xo (muLine Hd))
    {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) (hY : M.proj z ∈ S.R.Yo) : z ∈ D.Xo := by
  obtain ⟨z', ⟨hz'X, hz'P⟩, hz'⟩ := S.Yo_sub _ hY
  obtain ⟨c, hc, hzc⟩ := (M.fibre z' hz'P z hz).1 hz'
  refine ⟨hz, fun hB => ?_⟩
  have hinv : ∀ k, (c k)⁻¹ ≠ 0 := fun k => inv_ne_zero (hc k)
  have h1 := D.bd_torus z hB (fun k => (c k)⁻¹) hinv
  have h2 : torusSmul (fun k => (c k)⁻¹) z = z' := by
    funext p
    rw [hzc]
    simp [torusSmul, inv_mul_cancel_left₀ (hc p.1)]
  rw [h2] at h1
  exact hz'X.2 h1

theorem tendsto_arLimFun (hLoc : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement) {Hd : HodgeData D} {M : XModel D}
    (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (hS : S.IsTied) (B : ℕ) (hII : IsFullIntersectionSystem II)
    (Nb : HermLine J) (hNb : IsSmoothHerm Nb) (hNa : Nb.a = muTwDeg Hd B) :
    Tendsto (arLimFun Hd S B) (𝓝[>] 0) (𝓝 (limTop Hd B Nb)) := by
  obtain ⟨Pn, hPn, hPnS⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Giv.exists_potential_of_smoothHerm K J (mCoordIdeal D.y) D.n M Nb hNb
  obtain ⟨Θ, hΘ, hΘp, hΘN⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.exists_posPot_dominating K J II Ψ Ω W D M Pn hPn
  obtain ⟨-, ⟨C₁, hC₁⟩, hpsh⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Giv.tied_regularisation_weak K J (mCoordIdeal D.y) D.n M D.Xo (muLine Hd) S Θ hS hΘ hΘp
  obtain ⟨κ, hκc, hκ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.Descent.logDiff_descends K J II Ψ Ω W D Hd M S B Nb hNb hNa
  obtain ⟨Bκ, hBκ⟩ : ∃ b : ℝ, ∀ x, |κ x| ≤ b := by
    obtain ⟨b, hb⟩ := (isCompact_univ.image hκc).isBounded.exists_norm_le
    exact ⟨b, fun x => hb _ ⟨x, Set.mem_univ _, rfl⟩⟩
  obtain ⟨hYo, hYnull, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Giv.regData_open_part D.n M.Xc M.atlas S.R
  have hph := S.R.ph_smooth

  set Cc : ℝ := |C₁| + |S.R.Clog| + |Bκ| + 1 with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  have hlogr : ∀ x ∈ S.R.Yo, 0 ≤ Real.log (S.R.r x) := fun x hx => Real.log_nonneg (S.R.one_le_r x hx)

  have hbd : ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) ∧
      ∀ x ∈ S.R.Yo, |S.regWeight t x| ≤ |C₁| + |S.R.Clog| * Real.log (S.R.r x) ∧ S.regWeight t x ≤ |C₁| := by
    filter_upwards [hC₁] with t ht
    refine ⟨ht.1, fun x hx => ?_⟩
    obtain ⟨h1, h2⟩ := ht.2 x hx
    have h3 := S.R.ph_ge x hx
    have h4 : -(|S.R.Clog| * Real.log (S.R.r x)) ≤ -S.R.Clog * Real.log (S.R.r x) := by
      have := mul_le_mul_of_nonneg_right (le_abs_self S.R.Clog) (hlogr x hx)
      linarith
    have h5 : C₁ ≤ |C₁| := le_abs_self _
    have h6 : 0 ≤ |S.R.Clog| * Real.log (S.R.r x) := mul_nonneg (abs_nonneg _) (hlogr x hx)
    have h7 : 0 ≤ |C₁| := abs_nonneg _
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, by linarith⟩
  set G : M.Xc → ℝ := S.R.Yo.indicator fun x => κ x - S.R.ph x with hG
  set GT : ℝ → M.Xc → ℝ := fun t x => κ x - S.regWeight t x with hGT
  have hconv : ∀ i : ℕ, MIntegrable M.atlas (positionPot S.R.th Pn S.R.ph i) G ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t)) ∧
      Tendsto (fun t => mInt M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t)) (𝓝[>] 0)
        (𝓝 (mInt M.atlas (positionPot S.R.th Pn S.R.ph i) G)) := by
    intro i
    refine _root_.GlobalTheory.CompanionTheory.Ar.Giv.mixed_integral_tendsto_of_C2_off_divisor D.n M.Xc M.atlas S.R Θ hΘ hΘp
      (fun j : Fin D.n => if (j : ℕ) < i then S.R.th else Pn)
      (fun j : Fin D.n => if (j : ℕ) < i then S.R.ph else fun _ => 0)
      (fun (j : Fin D.n) t => if (j : ℕ) < i then S.regWeight t else fun _ => 0) G GT Cc
      ?_ ?_ ?_ ?_ ?_ ?_
    · intro j
      by_cases h : (j : ℕ) < i
      · simpa [h] using S.R.th_pot
      · simpa [h] using hPn
    · intro j
      by_cases h : (j : ℕ) < i
      · simpa [h] using hph
      · simp only [h, if_false]
        intro j'
        exact contDiffOn_const
    · have h1 := hpsh 1 one_pos
      filter_upwards [hbd, h1] with t ht ht1 j
      by_cases h : (j : ℕ) < i
      · simp only [h, if_true]
        refine ⟨ht.1, ?_, fun x hx => ?_⟩
        · have : Θ.rsmul 1 = Θ := by
            cases Θ
            simp [LocPot.rsmul]
          rwa [this] at ht1
        · obtain ⟨h2, h3⟩ := ht.2 x hx
          have hL := hlogr x hx
          have h4 : |S.R.Clog| * Real.log (S.R.r x) ≤ Cc * Real.log (S.R.r x) :=
            mul_le_mul_of_nonneg_right (by rw [hCc]; linarith [abs_nonneg C₁, abs_nonneg Bκ]) hL
          have h5 : |C₁| ≤ Cc := by rw [hCc]; linarith [abs_nonneg S.R.Clog, abs_nonneg Bκ]
          exact ⟨by linarith, by linarith⟩
      · simp only [h, if_false]
        refine ⟨fun j' => contDiffOn_const, hΘN, fun x hx => ?_⟩
        have hL := hlogr x hx
        have := mul_nonneg hCc0 hL
        simp only [abs_zero]
        exact ⟨by linarith, hCc0⟩
    · intro j k K' hK' hK'c
      by_cases h : (j : ℕ) < i
      · simp only [h, if_true]
        exact _root_.GlobalTheory.CompanionTheory.Ar.Giv.regWeight_tendsto_C2_of_tied K J (mCoordIdeal D.y) D.n M D.Xo (muLine Hd) S hS k K' hK' hK'c
      · simp only [h, if_false]
        exact ⟨tuo_const _ _ _, tuo_const _ _ _, tuo_const _ _ _⟩
    · filter_upwards [hbd] with t ht
      refine ⟨?_, fun x hx => ?_⟩
      · letI : MeasurableSpace M.Xc := borel M.Xc
        haveI : BorelSpace M.Xc := ⟨rfl⟩
        have hc : Continuous (GT t) := hκc.sub (_root_.GlobalTheory.CompanionTheory.Ar.AtlasSmooth.continuous_of_atlas_smooth D.n M.Xc M.atlas _ ht.1)
        exact hc.measurable.indicator hYo.measurableSet
      · obtain ⟨h2, -⟩ := ht.2 x hx
        have hL := hlogr x hx
        have h4 : |S.R.Clog| * Real.log (S.R.r x) ≤ Cc * Real.log (S.R.r x) :=
          mul_le_mul_of_nonneg_right (by rw [hCc]; linarith [abs_nonneg C₁, abs_nonneg Bκ]) hL
        have h5 : |C₁| + |κ x| ≤ Cc := by
          have := hBκ x
          have h6 := le_abs_self Bκ
          rw [hCc]; linarith [abs_nonneg S.R.Clog]
        have h7 : |GT t x| ≤ |κ x| + |S.regWeight t x| := abs_sub _ _
        linarith
    · intro K' hK' hK'c
      have hu := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.tendstoUniformlyOn_regWeight_of_isTied K J (mCoordIdeal D.y) D.n M D.Xo (muLine Hd) S hS K' hK' hK'c
      have hu2 : TendstoUniformlyOn GT (fun x => κ x - S.R.ph x) (𝓝[>] 0) K' := by
        rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
        intro ε hε
        filter_upwards [hu ε hε] with t ht x hx
        have := ht x hx
        simp only [hGT, Real.dist_eq] at this ⊢
        rwa [show κ x - S.R.ph x - (κ x - S.regWeight t x) = -(S.R.ph x - S.regWeight t x) by ring, abs_neg]
      exact hu2.congr_right fun x hx => by simp [hG, Set.indicator_of_mem (hK' hx)]

  have hmeasT : ∀ t, M.atlas.Smooth (S.regWeight t) → ∀ j, AEStronglyMeasurable (GT t ∘ (M.atlas.chart j).symm)
      (volume.restrict (M.atlas.chart j).target) := by
    intro t ht j
    have hc : Continuous (GT t) := hκc.sub (_root_.GlobalTheory.CompanionTheory.Ar.AtlasSmooth.continuous_of_atlas_smooth D.n M.Xc M.atlas _ ht)
    exact (hc.comp_continuousOn (M.atlas.chart j).continuousOn_symm).aestronglyMeasurable
      (M.atlas.chart j).open_target.measurableSet
  have hmeasG : ∀ j, AEStronglyMeasurable (G ∘ (M.atlas.chart j).symm)
      (volume.restrict (M.atlas.chart j).target) := by
    intro j
    set V : Set (Fin D.n → ℂ) := (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo with hV
    have hVo : IsOpen V := (M.atlas.chart j).continuousOn_symm.isOpen_inter_preimage
      (M.atlas.chart j).open_target hYo
    have hF : ContinuousOn (fun y => κ ((M.atlas.chart j).symm y) - S.R.ph ((M.atlas.chart j).symm y)) V := by
      refine ContinuousOn.sub ?_ (hph j).continuousOn
      exact hκc.comp_continuousOn ((M.atlas.chart j).continuousOn_symm.mono Set.inter_subset_left)
    have h1 : AEStronglyMeasurable (V.indicator fun y => κ ((M.atlas.chart j).symm y) -
        S.R.ph ((M.atlas.chart j).symm y)) volume :=
      (aestronglyMeasurable_indicator_iff hVo.measurableSet).2 (hF.aestronglyMeasurable hVo.measurableSet)
    refine (h1.mono_measure Measure.restrict_le_self).congr ?_
    refine (ae_restrict_iff' (M.atlas.chart j).open_target.measurableSet).2 (Filter.Eventually.of_forall fun y hy => ?_)
    by_cases hyY : (M.atlas.chart j).symm y ∈ S.R.Yo
    · have hyV : y ∈ V := ⟨hy, hyY⟩
      simp [hG, Set.indicator_of_mem hyY, Set.indicator_of_mem hyV]
    · have hyV : y ∉ V := fun h => hyY h.2
      simp [hG, Set.indicator_of_notMem hyY, Set.indicator_of_notMem hyV]

  have hwl : ∀ i, ptsIntegral (mCoordIdeal D.y)
      (pot fun j : Fin D.n => if (j : ℕ) < i then muVert Hd B else Nb)
      (fun z => Real.log (Nb.h z) - Real.log ((muVert Hd B).h z)) =
      mInt M.atlas (positionPot S.R.th Pn S.R.ph i) G := by
    intro i
    refine _root_.GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_word_eq_mInt K J II Ψ Ω W D Hd M S B Nb (muVert Hd B) Pn i S.R.ph G _ hPn hPnS hph ?_ ?_ hmeasG (hconv i).1
    · intro z hz hY
      have h1 := S.ph_eq z ⟨mem_Xo_of_proj_mem S hz hY, hz⟩ hY
      rw [_root_.GlobalTheory.CompanionTheory.Ar.Cusp.log_muVert_h_of_mem K J II Ψ Ω W D Hd B z hz, h1]
      ring
    · intro z hz hY
      have h1 := S.ph_eq z ⟨mem_Xo_of_proj_mem S hz hY, hz⟩ hY
      have h2 := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.log_muVert_h_of_mem K J II Ψ Ω W D Hd B z hz
      have h3 := hκ z hz
      simp only [hG, Set.indicator_of_mem hY]
      rw [h1, h2, h3]
      ring
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      II K J (mCoordIdeal D.y) (D.n + 1) (fun _ => Nb) - ∑ i ∈ Finset.range (D.n + 1),
        mInt M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t) = arLimFun Hd S B t := by
    have hint : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i ∈ Finset.range (D.n + 1),
        MIntegrable M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t) :=
      (Filter.eventually_all_finset _).2 fun i _ => (hconv i).2.1
    filter_upwards [_root_.GlobalTheory.CompanionTheory.Ar.Cusp.muReg_smooth_log K J II Ψ Ω W D Hd M S B hS, hbd, hint] with t hsp hb hi
    obtain ⟨hsm, hdeg, hlog⟩ := hsp
    have hT := _root_.GlobalTheory.CompanionTheory.Ar.Tele.telescope hLoc K J II (mCoordIdeal D.y) D.n Nb (muReg Hd S B t) hII D.arith hNb hsm
      (hdeg.trans hNa.symm)
    rw [arLimFun, hT]
    congr 1
    refine Finset.sum_congr rfl fun i hi' => ?_
    refine (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_word_eq_mInt K J II Ψ Ω W D Hd M S B Nb (muReg Hd S B t) Pn i (S.regWeight t) (GT t) _ hPn hPnS
      (fun j => (hb.1 j).mono fun y hy => ⟨hy.1, Set.mem_univ _⟩) ?_ ?_ (hmeasT t hb.1) (hi i hi')).symm
    · intro z hz _
      exact hlog z hz
    · intro z hz _
      simp only [hGT]
      rw [hlog z hz, hκ z hz]
      ring
  have hlim : Tendsto (fun t => II K J (mCoordIdeal D.y) (D.n + 1) (fun _ => Nb) -
      ∑ i ∈ Finset.range (D.n + 1), mInt M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t))
      (𝓝[>] 0) (𝓝 (limTop Hd B Nb)) := by
    rw [limTop]
    simp only [hwl]
    exact tendsto_const_nhds.sub (tendsto_finsetSum _ fun i _ => (hconv i).2.2)
  exact hlim.congr' hev

end Main
end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PtsIntegralLogNormRatEqBase
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem ptsIntegral_logNormRat_eq_base : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P J D) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (π : R.X → X) (hπ : HoloMap R.A A π) (dg : ℕ) (br : Set X), IsArithVar P (D + 1) → IsDegreeOff A R.A π dg br → ∀ (L : Fin D → HermLine ι) (Φ : Fin D → LocPot X), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPotential A (Φ j)) → (∀ j, SamePot R.A Set.univ (potOf R (L j)) ((Φ j).pullback π hπ.1)) → ∀ (Am : HermLine ι) (f g : MRing ι) (u : X → ℝ) (N : Set R.X), IsSmoothHerm Am → IsRatSectionOn P Am f g → IsNull R.A N → (∀ x ∉ N, logNormRat Am f g (R.lift x x) = u (π x)) → MIntegrable A Φ u → ptsIntegral P (pot L) (logNormRat Am f g) = dg * mInt A Φ u :=
  @PositivityTheory.Xgp.t_re_bridge

end GlobalTheory.CompanionTheory.Ar.PB
end

