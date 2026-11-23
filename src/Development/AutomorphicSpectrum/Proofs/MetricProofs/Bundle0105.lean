module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0098
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0111
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeSheet
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.LintegralFibSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFromOrbitCharts
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen

open GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}

theorem analyticAt_eval {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : E → σ → ℂ} {w₀ : E}
    (hg : ∀ q, AnalyticAt ℂ (fun w => g w q) w₀) (f : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun w => eval (g w) f) w₀ := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    refine (hp.add hq).congr (Filter.Eventually.of_forall fun w => ?_)
    simp
  | mul_X p n hp =>
    refine (hp.mul (hg n)).congr (Filter.Eventually.of_forall fun w => ?_)
    simp

section Overlap

variable (hP : IsMultiHomogIdeal P) (C₁ C₂ : OrbitChart P e) (x₁ x₂ : PtsOf P)
include hP

theorem mem_O_of_mem_srcOf {w : Fin e → ℂ} (hw : w ∈ C₁.D) (h : clsT x₁ (C₁.φ w) ∈ srcOf C₂) : C₁.φ w ∈ C₂.O := by
  have h' : rep (cls (C₁.φ w) (C₁.mem w hw)) ∈ C₂.O := by
    rw [← clsT_of_mem x₁ (C₁.mem w hw)]
    exact h
  exact mem_O_of_orbit C₂ hP h' (Proj.orbit_symm (rep_cls_orbit _ _)) (rep_mem_mcPts _)

theorem rho_clsT {w : Fin e → ℂ} (hw : w ∈ C₁.D) (h : clsT x₁ (C₁.φ w) ∈ srcOf C₂) :
    C₂.ρ (rep (clsT x₁ (C₁.φ w))) = C₂.ρ (C₁.φ w) := by
  have hO := mem_O_of_mem_srcOf hP C₁ C₂ x₁ hw h
  refine C₂.ρ_orbit _ hO _ h ?_
  rw [clsT_of_mem x₁ (C₁.mem w hw)]
  exact rep_cls_orbit _ _

theorem isOpen_overlap :
    IsOpen ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' srcOf C₂) :=
  (orbChart hP C₁ x₁).isOpen_inter_preimage_symm (isOpen_srcOf hP C₂)

theorem analytic_transition :
    AnalyticOnNhd ℂ (orbChart hP C₂ x₂ ∘ (orbChart hP C₁ x₁).symm)
      ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' (orbChart hP C₂ x₂).source) := by
  have h1 : AnalyticOnNhd ℂ (fun w => C₂.ρ (C₁.φ w))
      ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' srcOf C₂) :=
    (_root_.GlobalTheory.CompanionTheory.Ar.PB.WMan.OrbitChart.analyticOnNhd_transition K ι P e C₁ C₂).mono fun w hw => ⟨hw.1, mem_O_of_mem_srcOf hP C₁ C₂ x₁ hw.1 hw.2⟩
  exact h1.congr (isOpen_overlap hP C₁ C₂ x₁) fun w hw => (rho_clsT hP C₁ C₂ x₁ hw.1 hw.2).symm

theorem analytic_lift (p : Σ k, ι k) :
    AnalyticOnNhd ℂ ((fun y : PtsOf P => C₂.φ (C₂.ρ (rep y)) p) ∘ (orbChart hP C₁ x₁).symm)
      ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' srcOf C₂) := by
  have h1 : AnalyticOnNhd ℂ (fun w => C₂.φ (C₂.ρ (C₁.φ w)) p)
      ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' srcOf C₂) := fun w hw => by
    have hO := mem_O_of_mem_srcOf hP C₁ C₂ x₁ hw.1 hw.2
    exact AnalyticAt.comp (g := fun v => C₂.φ v p) (f := fun w => C₂.ρ (C₁.φ w))
      (C₂.holo p _ (C₂.ρ_mem _ hO)) (_root_.GlobalTheory.CompanionTheory.Ar.PB.WMan.OrbitChart.analyticOnNhd_transition K ι P e C₁ C₂ w ⟨hw.1, hO⟩)
  refine h1.congr (isOpen_overlap hP C₁ C₂ x₁) fun w hw => ?_
  have e1 : C₂.ρ (rep (clsT x₁ (C₁.φ w))) = C₂.ρ (C₁.φ w) := rho_clsT hP C₁ C₂ x₁ hw.1 hw.2
  show C₂.φ (C₂.ρ (C₁.φ w)) p = C₂.φ (C₂.ρ (rep (clsT x₁ (C₁.φ w)))) p
  rw [e1]

theorem immersion_lift {x : PtsOf P} (hx₂ : x ∈ srcOf C₂) (hx₁ : x ∈ srcOf C₁) (p : (k : K) → ι k)
    (hp : ∀ k, C₂.φ (C₂.ρ (rep x)) ⟨k, p k⟩ ≠ 0) :
    (fderiv ℂ (fun y => affCoord p (C₂.φ (C₂.ρ (rep ((orbChart hP C₁ x₁).symm y)))))
      (orbChart hP C₁ x₁ x)).ker = ⊥ := by
  set ψ := orbChart hP C₁ x₁ with hψ
  have hw₀ : ψ x ∈ ψ.target := ψ.map_source hx₁
  have hsym : ψ.symm (ψ x) = x := ψ.left_inv hx₁
  have hV : ψ.target ∩ ψ.symm ⁻¹' srcOf C₂ ∈ 𝓝 (ψ x) :=
    (isOpen_overlap hP C₁ C₂ x₁).mem_nhds ⟨hw₀, by rw [Set.mem_preimage, hsym]; exact hx₂⟩
  have heq : (fun y => affCoord p (C₂.φ (C₂.ρ (rep (ψ.symm y))))) =ᶠ[𝓝 (ψ x)]
      fun y => affCoord p (C₁.φ y) := by
    filter_upwards [hV] with w hw
    have hm := C₁.mem w hw.1
    have h1 : SameOrbit (rep (ψ.symm w)) (C₁.φ w) := by
      show SameOrbit (rep (clsT x₁ (C₁.φ w))) (C₁.φ w)
      rw [clsT_of_mem x₁ hm]
      exact rep_cls_orbit _ hm
    exact Proj.affCoord_eq (Proj.orbit_trans (C₂.φ_ρ _ hw.2) h1) p
  rw [heq.fderiv_eq]
  have ho : SameOrbit (C₂.φ (C₂.ρ (rep x))) (C₁.φ (ψ x)) :=
    Proj.orbit_trans (C₂.φ_ρ _ hx₂) (Proj.orbit_symm (C₁.φ_ρ _ hx₁))
  exact C₁.immersion _ hw₀ p fun k => Proj.orbit_ne ho (hp k)

end Overlap

def atlasOf (hP : IsMultiHomogIdeal P) (Cx : PtsOf P → OrbitChart P e) (t : Finset (PtsOf P))
    (hcov : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y)) : FinHolAtlas e (PtsOf P) where
  n := t.card
  chart j := orbChart hP (Cx (t.equivFin.symm j)) (t.equivFin.symm j)
  cover x := by
    obtain ⟨y, hy, hx⟩ := hcov x
    refine ⟨t.equivFin ⟨y, hy⟩, ?_⟩
    show x ∈ srcOf (Cx (t.equivFin.symm (t.equivFin ⟨y, hy⟩)))
    rw [Equiv.symm_apply_apply]
    exact hx
  holo j k := analytic_transition hP _ _ _ _

theorem isCompat_orbChart (hP : IsMultiHomogIdeal P) (Cx : PtsOf P → OrbitChart P e) (t : Finset (PtsOf P))
    (hcov : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y)) (C : OrbitChart P e) (x₀ : PtsOf P) :
    IsCompatChart (atlasOf hP Cx t hcov) (orbChart hP C x₀) := fun _ =>
  ⟨analytic_transition hP _ _ _ _, analytic_transition hP _ _ _ _⟩

theorem holoOn_eval (hP : IsMultiHomogIdeal P) (Cx : PtsOf P → OrbitChart P e) (t : Finset (PtsOf P))
    (hcov : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y)) (C : OrbitChart P e) (f : MvPolynomial (Σ k, ι k) ℂ) :
    (atlasOf hP Cx t hcov).HoloOn (srcOf C) (fun y => eval (C.φ (C.ρ (rep y))) f) := fun j w hw =>
  analyticAt_eval (g := fun w => C.φ (C.ρ (rep (((atlasOf hP Cx t hcov).chart j).symm w))))
    (fun q => analytic_lift hP _ C _ q w hw) f

def resOf (hP : IsMultiHomogIdeal P) (hnd : ¬ (⊤ : Ideal (MRing ι)) ≤ P) (Cx : PtsOf P → OrbitChart P e)
    (hCx : ∀ x, x ∈ srcOf (Cx x)) (t : Finset (PtsOf P)) (hcov : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y)) :
    AnLogRes P ⊤ e where
  homog := ⟨{1}, fun f hf => ⟨0, by
    rw [Set.mem_singleton_iff.1 hf]
    intro m hm k
    have hm0 : m = 0 := by
      rw [MvPolynomial.support_one] at hm
      simpa using hm
    simp [hm0]⟩, by simp⟩
  nondeg := hnd
  X := PtsOf P
  top := inferInstance
  compact := Top.compactSpace_pts (isMultiHomogIdeal_pC hP)
  t2 := inferInstance
  A := atlasOf hP Cx t hcov
  U x := srcOf (Cx x)
  isOpen_U x := isOpen_srcOf hP _
  mem_U := hCx
  lift x y := (Cx x).φ ((Cx x).ρ (rep y))
  holo x p j := analytic_lift hP _ _ _ p
  mem x y hy := (Cx x).mem _ ((Cx x).ρ_mem _ hy)
  compat x x' y hy := Proj.orbit_trans ((Cx x).φ_ρ _ hy.1) (Proj.orbit_symm ((Cx x').φ_ρ _ hy.2))
  surj z hz _ := ⟨cls z hz, Proj.orbit_trans ((Cx _).φ_ρ _ (hCx _)) (rep_cls_orbit z hz)⟩
  inj x x' _ h := pts_eq_of_orbit (Proj.orbit_trans (Proj.orbit_symm ((Cx x).φ_ρ _ (hCx x)))
    (Proj.orbit_trans h ((Cx x').φ_ρ _ (hCx x'))))
  immersion x _ p hp j hj := immersion_lift hP _ (Cx x) _ (hCx x) hj p hp
  snc f a _ _ hz := ⟨0, Fin.elim0, Fin.elim0, fun x => ⟨orbChart hP (Cx x) x, isCompat_orbChart hP Cx t hcov _ _,
    hCx x, subset_rfl, Fin.elim0, fun k => k.elim0, fun k => k.elim0,
    fun y => eval ((Cx x).φ ((Cx x).ρ (rep y))) (map (Int.castRingHom ℂ) f),
    holoOn_eval hP Cx t hcov (Cx x) _,
    fun y hy h0 => Proj.not_mem_mcPts_top _ (hz _ ((Cx x).mem _ ((Cx x).ρ_mem _ hy)) h0),
    fun y _ => by simp⟩⟩
  null j := by
    have : {x : PtsOf P | (Cx x).φ ((Cx x).ρ (rep x)) ∈ mcPts (⊤ : Ideal (MRing ι))} = ∅ :=
      Set.eq_empty_of_forall_notMem fun x => Proj.not_mem_mcPts_top _
    rw [this]
    simp

theorem exists_anLogRes_of_orbitCharts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ), Nonempty K → IsMultiHomogIdeal P → ¬ (⊤ : Ideal (MRing ι)) ≤ P → (∀ z ∈ mcPts P, ∃ C : OrbitChart P e, z ∈ C.O) → ∃ R : AnLogRes P ⊤ e, ∀ C : OrbitChart P e, (mcPts P).Nonempty → ∃ ψ : OpenPartialHomeomorph R.X (Fin e → ℂ), IsCompatChart R.A ψ ∧ ψ.target = C.D ∧ (∀ x, x ∈ ψ.source ↔ R.lift x x ∈ C.O) ∧ ∀ x ∈ ψ.source, SameOrbit (C.φ (ψ x)) (R.lift x x) := by
  intro K _ ι _ P e _ hP hnd hcov
  have h' : ∀ x : PtsOf P, ∃ C : OrbitChart P e, x ∈ srcOf C := fun x => hcov _ (rep_mem_mcPts x)
  choose Cx hCx using h'
  haveI : CompactSpace (PtsOf P) := Top.compactSpace_pts (isMultiHomogIdeal_pC hP)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => srcOf (Cx x))
    (fun x _ => (isOpen_srcOf hP _).mem_nhds (hCx x))
  have hc : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y) := fun x => by
    simpa using ht.2 (Set.mem_univ x)
  refine ⟨resOf hP hnd Cx hCx t hc, fun C hne => ?_⟩
  obtain ⟨z, hz⟩ := hne
  have ho : ∀ x : PtsOf P, SameOrbit ((Cx x).φ ((Cx x).ρ (rep x))) (rep x) := fun x => (Cx x).φ_ρ _ (hCx x)
  have hm : ∀ x : PtsOf P, (Cx x).φ ((Cx x).ρ (rep x)) ∈ mcPts P := fun x => (Cx x).mem _ ((Cx x).ρ_mem _ (hCx x))
  refine ⟨orbChart hP C (cls z hz), isCompat_orbChart hP Cx t hc C _, rfl, fun x => ?_, fun x hx => ?_⟩
  · exact ⟨fun h => mem_O_of_orbit C hP h (ho x) (rep_mem_mcPts x),
      fun h => mem_O_of_orbit C hP h (Proj.orbit_symm (ho x)) (hm x)⟩
  · exact Proj.orbit_trans (C.φ_ρ _ hx) (Proj.orbit_symm (ho x))

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFubiniStudyPositive
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace PosFs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fsHerm_one_h (y : (Σ k, ι k) → ℂ) :
    (fsHerm ι fun _ => 1).h y = (GroundTheory.Heights₂.Heights.fsMulti ι).h y := by
  rw [fsHerm_h]
  unfold refNorm
  simp only [GroundTheory.Heights₂.Heights.fsMulti, HermLine.ofMetrics, zpow_one]
  refine Finset.prod_congr rfl fun k _ => ?_
  change _ = ‖WithLp.toLp 2 (fun i => y ⟨k, i⟩)‖
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_rpow]
  norm_num

theorem levi_fs_pos {z w : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hw : ∀ c : K → ℂ, w ≠ torusSmul c z) :
    0 < levi (fun y => Real.log ((fsHerm ι fun _ => 1).h y)) z w := by
  have h := GlobalTheory.CompanionTheory.Ar.FS.levi_fsMulti_pos hz hw
  have e : (fun y => Real.log ((fsHerm ι fun _ => 1).h y)) =
      fun y => Real.log ((GroundTheory.Heights₂.Heights.fsMulti ι).h y) := by
    funext y
    rw [fsHerm_one_h]
  rw [e]
  exact h

theorem contDiffAt_log_h {A : HermLine ι} (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z := by
  have hopen : ∀ᶠ y in 𝓝 z, ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    refine Filter.eventually_all.mpr fun k => ?_
    obtain ⟨i, hi⟩ := hz k
    exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
      fun y hy => ⟨i, hy⟩
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h z := hA.contDiffAt hopen
  exact (h1.of_le (by first | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤) | (rw [show (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) by norm_cast]; exact WithTop.coe_le_coe.2 le_top))).log (A.pos z hz).ne'

theorem fderiv_affCoord_torus {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {γ : E → (Σ k, ι k) → ℂ} {y : E} (p : (k : K) → ι k) (hγ : DifferentiableAt ℂ γ y)
    (hp : ∀ k, γ y ⟨k, p k⟩ ≠ 0) {w : E} {c : K → ℂ} (hc : fderiv ℂ γ y w = torusSmul c (γ y)) :
    fderiv ℂ (fun y' => affCoord p (γ y')) y w = 0 := by
  have hd := hγ.hasFDerivAt
  have hq : ∀ q : Σ k, ι k, HasFDerivAt (fun y' => γ y' q)
      ((ContinuousLinearMap.proj q).comp (fderiv ℂ γ y)) y := fun q => hasFDerivAt_pi'.1 hd q
  have hu : ∀ q : Σ k, ι k, HasFDerivAt (fun y' => affCoord p (γ y') q)
      ((γ y q) • ((-((γ y ⟨q.1, p q.1⟩) ^ 2)⁻¹) •
          ((ContinuousLinearMap.proj ⟨q.1, p q.1⟩).comp (fderiv ℂ γ y))) +
        ((γ y ⟨q.1, p q.1⟩)⁻¹) • ((ContinuousLinearMap.proj q).comp (fderiv ℂ γ y))) y := by
    intro q
    have hinv := (hasDerivAt_inv (hp q.1)).comp_hasFDerivAt y (hq ⟨q.1, p q.1⟩)
    have hm := (hq q).mul hinv
    refine hm.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y' => ?_)
    simp [affCoord, div_eq_mul_inv]
  have hall : fderiv ℂ (fun y' => affCoord p (γ y')) y = ContinuousLinearMap.pi _ :=
    (hasFDerivAt_pi.2 hu).fderiv
  rw [hall]
  funext q
  have h1 : fderiv ℂ γ y w q = c q.1 * γ y q := congrFun hc q
  have h2 : fderiv ℂ γ y w ⟨q.1, p q.1⟩ = c q.1 * γ y ⟨q.1, p q.1⟩ := congrFun hc _
  have hr := hp q.1
  simp only [ContinuousLinearMap.coe_pi', ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    h1, h2, smul_eq_mul, Pi.zero_apply]
  field_simp
  ring

theorem isPosPot_fs (P : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P ⊤ D) :
    IsPosPot R.A (potOf R (fsHerm ι fun _ => 1)) := by
  classical
  intro x j y hy w hw
  obtain ⟨hyt, hyU⟩ := hy
  have hx₀ : (R.A.chart j).symm y ∈ (R.A.chart j).source := (R.A.chart j).map_target hyt
  have hex₀ : R.A.chart j ((R.A.chart j).symm y) = y := (R.A.chart j).right_inv hyt
  have hxU : (R.A.chart j).symm y ∈ R.U x := hyU
  let γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ := fun y' => R.lift x ((R.A.chart j).symm y')
  have hγ : AnalyticAt ℂ γ y := analyticAt_pi_iff.2 fun q => R.holo x q j y ⟨hyt, hyU⟩
  have hz : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := (R.mem x _ hxU).1
  have hc2 := contDiffAt_log_h (GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm K ι fun _ => 1) hz
  have heq : levi ((potOf R (fsHerm ι fun _ => 1)).φ x ∘ (R.A.chart j).symm) y w =
      levi (fun z => Real.log ((fsHerm ι fun _ => 1).h z)) (γ y) (fderiv ℂ γ y w) :=
    levi_comp w hγ hc2
  rw [heq]
  refine levi_fs_pos hz fun c hc => hw ?_
  choose p hp using (R.mem _ _ (R.mem_U ((R.A.chart j).symm y))).1
  have hnot : R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y) ∉ mcPts (⊤ : Ideal (MRing ι)) := by
    intro h
    have := h.2 1 trivial
    simp at this
  have himm := R.immersion _ hnot p hp j hx₀
  rw [hex₀] at himm
  have hev : (fun y' => affCoord p (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y'))) =ᶠ[𝓝 y]
      fun y' => affCoord p (γ y') := by
    have hmem : (R.A.chart j).symm ⁻¹' (R.U x ∩ R.U ((R.A.chart j).symm y)) ∈ 𝓝 y :=
      ((R.A.chart j).continuousAt_symm hyt).preimage_mem_nhds
        (((R.isOpen_U x).inter (R.isOpen_U _)).mem_nhds ⟨hxU, R.mem_U _⟩)
    filter_upwards [hmem] with y' hy'
    obtain ⟨c', hc', h⟩ := R.compat _ x _ ⟨hy'.2, hy'.1⟩
    funext q
    simp only [affCoord, γ]
    rw [h]
    exact mul_div_mul_left _ _ (hc' q.1)
  rw [hev.fderiv_eq] at himm
  have hpγ : ∀ k, γ y ⟨k, p k⟩ ≠ 0 := by
    intro k
    obtain ⟨c', hc', h⟩ := R.compat _ x _ ⟨R.mem_U _, hxU⟩
    have := hp k
    rw [h] at this
    exact right_ne_zero_of_mul this
  have hk := fderiv_affCoord_torus p hγ.differentiableAt hpγ hc
  have hmem : w ∈ (fderiv ℂ (fun y' => affCoord p (γ y')) y).ker := hk
  rw [himm] at hmem
  exact (Submodule.mem_bot _).1 hmem

end PosFs

theorem fs_pos_potential : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P ⊤ D), (∀ A : HermLine ι, IsSmoothHerm A → IsPotential R.A (potOf R A)) ∧ IsSmoothHerm (fsHerm ι fun _ => 1) ∧ IsPosPot R.A (potOf R (fsHerm ι fun _ => 1)) :=
  fun K _ ι _ P D R => ⟨fun _ hA => isPotential_potOf R hA,
    GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm K ι _, PosFs.isPosPot_fs P D R⟩

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasurableFibreCountOfLocalDiffeo
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push

section FibreMeas

variable {e : ℕ}

theorem fibSum_eq_sub_of_finite {O : Set (Fin e → ℂ)} {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (h : (Fin e → ℂ) → ℝ) (y : Fin e → ℂ) (hy : (O ∩ Q ⁻¹' {y}).Finite) :
    fibSum O Q (fun u => max (h u) 0) y - fibSum O Q (fun u => max (-h u) 0) y = fibSum O Q h y := by
  unfold fibSum
  rw [← finsum_mem_sub_distrib _ _ hy]
  refine finsum_mem_congr rfl fun u _ => ?_
  rw [← sub_div, max_zero_sub_max_neg_zero_eq_self]

theorem aemeasurable_fibSum_of_nonneg {O : Set (Fin e → ℂ)} (hO : IsOpen O)
    {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQ : ∀ u ∈ O, AnalyticAt ℂ Q u ∧
      LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    {h : (Fin e → ℂ) → ℝ} (hh : ∀ u, 0 ≤ h u) (hm : Measurable h)
    (hfin : ∀ᵐ y, (O ∩ Q ⁻¹' {y}).Finite) : AEMeasurable (fibSum O Q h) := by
  have h1 := (LintegralFibSum.lintegral_fibSum_open hO hQ hh
    (hm.comp measurable_subtype_coe) hfin).1
  refine h1.ennreal_toReal.congr (Eventually.of_forall fun y => ?_)
  exact ENNReal.toReal_ofReal (LintegralFibSum.fibSum_nonneg _ _ hh y)

theorem aestronglyMeasurable_fibSum {O : Set (Fin e → ℂ)} (hO : IsOpen O)
    {Q : (Fin e → ℂ) → (Fin e → ℂ)}
    (hQ : ∀ u ∈ O, AnalyticAt ℂ Q u ∧
      LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    {h : (Fin e → ℂ) → ℝ} (hm : AEStronglyMeasurable h (volume.restrict O))
    (hfin : ∀ᵐ y, (O ∩ Q ⁻¹' {y}).Finite) : AEStronglyMeasurable (fibSum O Q h) volume := by
  have hmm : Measurable (hm.mk h) := hm.stronglyMeasurable_mk.measurable
  have hae : ∀ᵐ u, u ∈ O → h u = hm.mk h u :=
    (ae_restrict_iff' hO.measurableSet).mp hm.ae_eq_mk
  have hnull : volume (O ∩ {u | h u ≠ hm.mk h u}) = 0 := by
    refine measure_mono_null ?_ (ae_iff.mp hae)
    rintro u ⟨huO, hne⟩ hu
    exact hne (hu huO)
  have himg : volume (Q '' (O ∩ {u | h u ≠ hm.mk h u})) = 0 := by
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ hnull
    intro u hu
    exact ((hQ u hu.1).1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  have hp : AEMeasurable (fibSum O Q fun u => max (hm.mk h u) 0) :=
    aemeasurable_fibSum_of_nonneg hO hQ (fun u => le_max_right _ _) (hmm.max measurable_const) hfin
  have hn : AEMeasurable (fibSum O Q fun u => max (-hm.mk h u) 0) :=
    aemeasurable_fibSum_of_nonneg hO hQ (fun u => le_max_right _ _) (hmm.neg.max measurable_const) hfin
  refine (hp.sub hn).aestronglyMeasurable.congr ?_
  filter_upwards [hfin, measure_eq_zero_iff_ae_notMem.mp himg] with y hy hyn
  show fibSum O Q (fun u => max (hm.mk h u) 0) y - fibSum O Q (fun u => max (-hm.mk h u) 0) y = _
  rw [fibSum_eq_sub_of_finite _ y hy]
  unfold fibSum
  refine finsum_mem_congr rfl fun u hu => ?_
  have : h u = hm.mk h u := by
    by_contra hne
    exact hyn ⟨u, ⟨hu.1, hne⟩, hu.2⟩
  rw [this]

end FibreMeas

theorem aestronglyMeasurable_fibreSum_pushDens : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X) (G : X → ℝ), (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0) → (∀ x ∉ S, ∀ j, x ∈ (A.chart j).source → AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧ LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) → (∀ y, (q ⁻¹' {y} \ S).Finite) → (∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source → ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x)) → (∀ j, AEStronglyMeasurable (fun u => G ((A.chart j).symm u) * locDens A Φ j u) (volume.restrict (A.chart j).target)) → AEStronglyMeasurable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x) volume := by
  intro e X _ _ _ A Φ q S G hS hq hfin hsm hG
  classical
  obtain ⟨Pt⟩ := existsPartition A
  set hj : Fin A.n → (Fin e → ℂ) → ℝ := fun j u =>
    Pt.χ j ((A.chart j).symm u) * (G ((A.chart j).symm u) * locDens A Φ j u) with hhj
  have hN : ∀ j, volume ((q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) = 0 := by
    intro j
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ ?_
    · intro u hu
      exact (hu.1.2.1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
    · exact measure_mono_null
        (Set.inter_subset_inter_left _ fun u (hu : u ∈ goodT A q j) => hu.1) (hS j)
  have hfinj : ∀ j, ∀ᵐ y, (goodT A q j ∩ (q ∘ (A.chart j).symm) ⁻¹' {y}).Finite := by
    intro j
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hN j)] with y hy
    rw [goodT_fibre_eq A q S hq j hy]
    exact ((hfin y).subset Set.inter_subset_right).image _
  have hχc : ∀ j, ContinuousOn (fun u => Pt.χ j ((A.chart j).symm u)) (A.chart j).target := by
    intro j
    have := (Pt.smooth j j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at this
    exact this
  have hjm : ∀ j, AEStronglyMeasurable (hj j) (volume.restrict (goodT A q j)) := fun j =>
    (((hχc j).aestronglyMeasurable (A.chart j).open_target.measurableSet).mul (hG j)).mono_measure
      (Measure.restrict_mono (by exact fun u hu => hu.1) le_rfl)
  have hsum := sum_fibSum_ae A q S hN hq hfin Pt hj (fun x => G x * pushDens A Φ q x) (by
    intro j x hx hxS
    have hd := locDens_div_jacN A Φ q S hq hsm j hx hxS
    simp only [hhj, (A.chart j).left_inv hx]
    rw [← hd]
    ring)
  exact (Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ =>
    aestronglyMeasurable_fibSum (isOpen_goodT A q j) (fun u hu => hu.2) (hjm j) (hfinj j)).congr hsum

end GlobalTheory.CompanionTheory.Ar.Giv.Push
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

def blockG {p q : ℕ} (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) : Matrix (Fin (p + q)) (Fin (p + q)) ℂ :=
  (Matrix.fromBlocks (omBlock Γ)ᵀ⁻¹ 0 0 (wBlock Γ)).submatrix (blockEquiv p q).symm (blockEquiv p q).symm

theorem wBlock_blockG {p q : ℕ} (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) : wBlock (blockG Γ) = wBlock Γ := by
  ext a b
  simp [wBlock, blockG, ← blockEquiv_inr]

theorem omBlock_blockG {p q : ℕ} (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) :
    omBlock (blockG Γ) = (omBlock Γ)ᵀ⁻¹ := by
  ext a b
  simp [omBlock, blockG, ← blockEquiv_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}


open Classical in
def dualFam (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) :
    Fin D.q → 𝔐.Vgen (.inr τ) :=
  if h : ∃ v : Fin D.q → 𝔐.Vgen (.inr τ), ∀ a b, tie.omFrame F τ a (v b) = if a = b then 1 else 0 then h.choose
  else 0

theorem wFrame_mem (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    (a : Fin D.p) : tie.wFrame F τ a ∈ 𝔐.Vgen (.inl τ) := by
  unfold FlagTie.wFrame colFrame
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (tie.eW τ b).2

def gbS (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) :
    Fin (D.p + D.q) → ↥(𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)) := fun i =>
  Sum.elim (fun a => ⟨(dualFam tie F τ a : 𝔐.Li), Submodule.mem_sup_right (dualFam tie F τ a).2⟩)
    (fun a => ⟨tie.wFrame F τ a, Submodule.mem_sup_left (wFrame_mem tie F τ a)⟩) ((blockEquiv D.p D.q).symm i)

def gb (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) :
    Fin (D.p + D.q) → 𝔐.Li := fun i => (gbS tie F τ i : 𝔐.Li)

def baseGram (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) {n : ℕ}
    (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (x : Rb.X) : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ :=
  HodgeMetric.gramFn 𝔐 (gb tie F τ) (Rb.lift x x)

end GlobalTheory.CompanionTheory.Ar.PB.BMx
end
end

