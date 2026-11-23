module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0142
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsTranslatedRiemannLattice
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.RiemannLatticeIsometryTransport
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumAndCuspWeightBounds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0138
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0027
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0120
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFlAn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0050
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0131
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCSqsys
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0090
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGrassmannPushOfInputs

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenProjectionInEigenspace
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F) (R : RiemLat E g Λ)


omit [IsCMField E] in
theorem embOf_coe (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : embOf s (a : E) = s a :=
  IsFractionRing.lift_algebraMap (intEmb_injective s) a

def mulPt (a : 𝓞 E) : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Ψ → Fin (j + j') → ℂ) where
  toFun y := fun τ => F.σ τ a • y τ
  map_add' y y' := by
    ext τ i
    simp [mul_add]
  map_smul' r y := by
    ext τ i
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul, RingHom.id_apply]
    ring

theorem vec_smul (a : 𝓞 E) (x : Λ) : C.vec (a • x) = mulPt (F := F) a (C.vec x) := by
  ext τ i
  simp [LatEmb.vec, mulPt, C.e_smul, embOf_coe]

def vecHom : Λ →+ (Ψ → Fin (j + j') → ℂ) where
  toFun := C.vec
  map_zero' := by
    ext τ i
    simp [LatEmb.vec]
  map_add' x y := by
    ext τ i
    simp [LatEmb.vec]

theorem vec_lam (k : Fin (2 * g)) : C.vec (C.lam k) = C.bas k := by
  ext τ i
  exact (C.bas_eq k τ i).symm

theorem perExt_bas (k : Fin (2 * g)) : C.perExt R (C.bas k) = R.P (C.lam k) := by
  simp [LatEmb.perExt]

theorem perExt_vec (x : Λ) : C.perExt R (C.vec x) = R.P x := by
  have h : ((C.perExt R).toAddMonoidHom.comp (vecHom C)).toIntLinearMap = R.P.toIntLinearMap := by
    refine C.lam.ext fun k => ?_
    change C.perExt R (C.vec (C.lam k)) = R.P (C.lam k)
    rw [vec_lam, perExt_bas]
  exact congrArg (fun f : Λ →ₗ[ℤ] (Fin g → ℂ) => f x) h

theorem perExt_mulPt (a : 𝓞 E) (y : Ψ → Fin (j + j') → ℂ) :
    C.perExt R (mulPt (F := F) a y) = R.B a (C.perExt R y) := by
  have h : (C.perExt R).comp (mulPt (F := F) a) = ((R.B a).restrictScalars ℝ).comp (C.perExt R) := by
    refine C.bas.ext fun k => ?_
    change C.perExt R (mulPt (F := F) a (C.bas k)) = R.B a (C.perExt R (C.bas k))
    rw [← vec_lam, ← vec_smul, perExt_vec, perExt_vec, R.act]
  exact congrArg (fun f : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ) => f y) h

open Classical in
theorem perExt_single_smul (a : 𝓞 E) (τ : Ψ) (y : Fin (j + j') → ℂ) :
    C.perExt R (Pi.single τ (F.σ τ a • y)) = R.B a (C.perExt R (Pi.single τ y)) := by
  rw [← perExt_mulPt]
  congr 1
  ext τ' i
  by_cases h : τ' = τ
  · subst h
    simp [mulPt]
  · simp [mulPt, Pi.single_eq_of_ne h]

theorem B_pPart (a : 𝓞 E) (τ : Ψ) (y : Fin (j + j') → ℂ) :
    R.B a (C.pPart R τ y) = F.σ τ a • C.pPart R τ y := by
  classical
  have h : C.pPart R τ (F.σ τ a • y) = F.σ τ a • C.pPart R τ y := (pPartL C R τ).map_smul _ _
  rw [← h]
  simp only [LatEmb.pPart, map_smul, map_sub, perExt_single_smul]
  rw [smul_comm Complex.I (F.σ τ a) y, perExt_single_smul]

theorem pPart_mem_eigSp (τ : Ψ) (y : Fin (j + j') → ℂ) : C.pPart R τ y ∈ eigSp R.B (F.σ τ) := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker]
  intro a
  simp [B_pPart]

end

theorem pPart_mem_eigSp_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (τ : Ψ) (y : Fin (j + j') → ℂ), C.pPart R τ y ∈ eigSp R.B (F.σ τ) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R τ y
  exact pPart_mem_eigSp C R τ y

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsCutoffFamilySymmetric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_cutoff_family_symmetric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (P : GroundTheory.Heights₂.Heights.Regular.PotentialCharts M.atlas) (κ : Equiv.Perm (Fin P.N)), SymmCharts M P κ → ∃ (cut : Fin P.N → M.Xc → ℝ) (C : ℝ), P.IsCutoffFamily cut C ∧ ∀ j, ∀ z ∈ mcPts (mCoordIdeal D.y), cut (κ j) (M.proj (conjVec z)) = cut j (M.proj z) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D M P κ hS
  obtain ⟨hκ, -, hS3⟩ := hS
  choose g0 hg0s hg0b hg0one hg0c hg0t using fun j => LevelTowerAlt.exists_bumps P j
  have hstarMid : ∀ j t, t ∈ P.chartMid (κ j) → star t ∈ P.chartMid j := by
    intro j t ht
    obtain ⟨ht1, ht2⟩ := ht
    obtain ⟨z, hz, hzx⟩ := M.surj ((P.chart (κ j)).symm t)
    obtain ⟨hsrc, hmid, -, hch⟩ := hS3 (κ j) z hz
    rw [hκ] at hsrc hmid hch
    have hx : M.proj z ∈ P.mid (κ j) := by
      rw [hzx]
      exact ht2
    have hx' : M.proj (conjVec z) ∈ P.mid j := hmid.2 hx
    have hxs : M.proj z ∈ (P.chart (κ j)).source := P.closure_mid _ (subset_closure hx)
    have hx's : M.proj (conjVec z) ∈ (P.chart j).source := P.closure_mid _ (subset_closure hx')
    have heq : P.chart j (M.proj (conjVec z)) = star t := by
      rw [hch hxs, hzx, (P.chart (κ j)).right_inv ht1]
    show star t ∈ (P.chart j).target ∩ (P.chart j).symm ⁻¹' P.mid j
    refine ⟨?_, ?_⟩
    · rw [← heq]
      exact (P.chart j).map_source hx's
    · show (P.chart j).symm (star t) ∈ P.mid j
      rw [← heq, (P.chart j).left_inv hx's]
      exact hx'
  let g : Fin P.N → (Fin D.n → ℂ) → ℝ := fun j t => (g0 j t + g0 (κ j) (star t)) / 2
  have hsm : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g j) := fun j =>
    ((hg0s j).add ((hg0s (κ j)).comp (LevelTowerAlt.contDiff_star _))).div_const 2
  have hbd : ∀ j y, 0 ≤ g j y ∧ g j y ≤ 1 := by
    intro j y
    have h1 := hg0b j y
    have h2 := hg0b (κ j) (star y)
    constructor
    · show 0 ≤ (g0 j y + g0 (κ j) (star y)) / 2
      linarith
    · show (g0 j y + g0 (κ j) (star y)) / 2 ≤ 1
      linarith
  have hone : ∀ j, ∀ x ∈ P.inner j, g j (P.chart j x) = 1 := by
    intro j x hx
    obtain ⟨z, hz, rfl⟩ := M.surj x
    obtain ⟨-, -, hinn, hch⟩ := hS3 j z hz
    have hmid : M.proj z ∈ P.mid j := P.closure_inner _ (subset_closure hx)
    have hsrc : M.proj z ∈ (P.chart j).source := P.closure_mid _ (subset_closure hmid)
    have h1 : g0 j (P.chart j (M.proj z)) = 1 := hg0one j _ ⟨_, subset_closure hx, rfl⟩
    have h2 : g0 (κ j) (star (P.chart j (M.proj z))) = 1 := by
      rw [← hch hsrc]
      exact hg0one (κ j) _ ⟨_, subset_closure (hinn.2 hx), rfl⟩
    show (g0 j (P.chart j (M.proj z)) + g0 (κ j) (star (P.chart j (M.proj z)))) / 2 = 1
    rw [h1, h2]
    norm_num
  have hK : ∀ j, tsupport (g j) ⊆ tsupport (g0 j) ∪ star '' tsupport (g0 (κ j)) := by
    intro j
    apply closure_minimal _ (((hg0c j).union ((hg0c (κ j)).image continuous_star)).isClosed)
    intro t ht
    rw [Function.mem_support] at ht
    by_cases h1 : g0 j t = 0
    · right
      refine ⟨star t, subset_tsupport _ ?_, star_star t⟩
      rw [Function.mem_support]
      intro h2
      apply ht
      show (g0 j t + g0 (κ j) (star t)) / 2 = 0
      rw [h1, h2]
      norm_num
    · left
      exact subset_tsupport _ h1
  have hcpt : ∀ j, IsCompact (tsupport (g j)) := fun j =>
    ((hg0c j).union ((hg0c (κ j)).image continuous_star)).of_isClosed_subset (isClosed_tsupport _) (hK j)
  have hsub : ∀ j, tsupport (g j) ⊆ P.chartMid j := by
    intro j t ht
    rcases hK j ht with h | ⟨u, hu, rfl⟩
    · exact hg0t j h
    · exact hstarMid j u (hg0t (κ j) hu)
  obtain ⟨C, hC⟩ := LevelTowerAlt.cutoff_of_bumps P g hsm hbd hone hcpt hsub
  refine ⟨_, C, hC, ?_⟩
  intro j z hz
  obtain ⟨hsrc, -, -, hch⟩ := hS3 j z hz
  simp only [ReciprocityTheory.AnForm.M.PLAux.chartPush]
  by_cases hx : M.proj z ∈ (P.chart j).source
  · rw [Set.indicator_of_mem (hsrc.2 hx), Set.indicator_of_mem hx]
    simp only [Function.comp]
    rw [hch hx]
    show (g0 (κ j) (star (P.chart j (M.proj z))) + g0 (κ (κ j)) (star (star (P.chart j (M.proj z))))) / 2 - 1
      = (g0 j (P.chart j (M.proj z)) + g0 (κ j) (star (P.chart j (M.proj z)))) / 2 - 1
    rw [hκ, star_star]
    ring
  · rw [Set.indicator_of_notMem (mt hsrc.1 hx), Set.indicator_of_notMem hx]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsTranslatedRiemannLatticeStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translated_riemann_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (a ai : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ), R.form = F.form → (∀ τ, a τ * ai τ = 1) → (∀ τ, (a τ)ᴴ * C.gr τ * a τ = C.gr τ) → ∃ R' : RiemLat E g Λ, R'.form = R.form ∧ R'.B = R.B ∧ (∀ x, R'.P x = C.perExt R fun τ => ai τ *ᵥ C.vec x τ) ∧ ∀ A, C.IsAdapted R A → C.IsAdapted R' fun τ => a τ * A τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Rotate.rotate_exists | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Rotate.rotate_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Rotate.rotate_exists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumContinuousCuspWeightMeasurable
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamilyMeas

theorem first_minimum_cusp_weight_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ), 1 ≤ j' → ContinuousOn (fun t => (F.R t).lam1) (ballDom F.q) ∧ Measurable ((ballDom F.q).indicator fun t => (F.R t).cuspW F.σ) ∧ IsOpen (ballDom F.q) ∧ ∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, F.Eqv (autGrp F.form) t t' → (F.R t).lam1 = (F.R t').lam1 ∧ (F.R t).cuspW F.σ = (F.R t').cuspW F.σ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F hj
  have hO : IsOpen (ballDom F.q) := BallInverse.isOpen_ballDom F.q
  let U := ↥(ballDom F.q)
  let R : U → RiemLat E g Λ := fun t => F.R t.1
  have hP : ∀ v, Continuous fun x : U => (R x).P v := fun v =>
    continuousOn_iff_continuous_restrict.1 (F.hol.2 v).continuousOn
  have hH : Continuous fun x : U => (R x).Hm := GlobalTheory.T.continuous_hermitian_matrix_family E g Λ U R F.form (fun x => F.form_eq _) hP
  have hlam : Continuous fun x : U => (R x).lam1 := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.continuous_first_minimum E g Λ U R hP hH
  have hnz : ∀ I, Continuous fun x : U => (R x).nz F.σ I := fun I => GlobalTheory.T.continuous_cusp_norm_family E g Λ Ψ U R F.σ I hP hH
  have hbdd : ∀ x : U, BddAbove {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz F.σ I)} := by
    intro x
    have hr : (R x).HasRank F.σ j' := fun τ => (F.sig x.1 x.2 τ).1
    obtain ⟨-, -, h3, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.cuspW_le E g Λ Ψ (R x) F.σ j' F.cm hr hj
    refine ⟨(R x).cuspW F.σ, ?_⟩
    rintro y ⟨I, hI, rfl⟩
    exact (h3 I hI).1
  have hcw : Measurable fun x : U => (R x).cuspW F.σ :=
    GlobalTheory.T.measurable_cusp_weight_family E g Λ Ψ U R F.σ F.form (fun x => F.form_eq _) (fun I => (hnz I).measurable) hbdd
  refine ⟨continuousOn_iff_continuous_restrict.2 hlam, ?_, hO, ?_⟩
  · classical
    have e : (ballDom F.q).indicator (fun t => (F.R t).cuspW F.σ) =
        fun t => if h : t ∈ ballDom F.q then (R ⟨t, h⟩).cuspW F.σ else 0 := by
      funext t
      by_cases h : t ∈ ballDom F.q <;> simp [h, R]
    rw [e]
    exact Measurable.dite (s := ballDom F.q) hcw measurable_const hO.measurableSet
  · rintro t ht t' ht' ⟨γ, hγ, φ, hφ⟩
    have hf : ∀ x y, (F.R t').form (γ x) (γ y) = (F.R t).form x y := fun x y => by
      rw [F.form_eq, F.form_eq]
      exact hγ x y
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso.isometry_and_commutes E g Λ (F.R t) (F.R t') γ φ hf hφ
    have himg : φ '' Set.range (F.R t).P = Set.range (F.R t').P := by
      ext z
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨γ x, hφ x⟩
      · rintro ⟨y, rfl⟩
        refine ⟨_, ⟨γ.symm y, rfl⟩, ?_⟩
        rw [← hφ, γ.apply_symm_apply]
    obtain ⟨a, b, -⟩ := _root_.LevelTowerAlt.riemann_lattice_isometry_transport E g Λ Ψ (F.R t) F.σ g Λ (F.R t') φ F.cm himg h1 h2
    exact ⟨b.symm, a.symm⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.FamilyMeas
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyAnalyticSystemExists
section
noncomputable section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem flagVarieties_flagSys : Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N →
    ∃ (d : ℕ) (S : AnSys (d + 1) (Ψ × Fin N)) (Re : Realis S (PFl Ψ N)), d + 1 = antisymDegree Ψ N ∧
      Re.deg = 1 ∧ (∀ p, Re.ref p = yLineFl Ψ N p) ∧ (∀ p t, Re.line p t = yLineFl Ψ N p) ∧
      Nonempty (FlagSys Re N) := by
  intro hIn Ψ _ _ _ N hN
  obtain ⟨M, BM, hhom, hdy, hbd⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.flagModel_over_point Ψ N hN
  have hA := _root_.GlobalTheory.CompanionTheory.Ar.PB.pFl_isArithVar Ψ N hN
  have hpos : 0 < antisymDegree Ψ N := by
    have h1 : 0 < Fintype.card Ψ := Fintype.card_pos
    have h2 : 0 < N.choose 2 := Nat.choose_pos hN
    exact Nat.mul_pos h1 h2
  obtain ⟨d, hd1⟩ : ∃ d, d + 1 = antisymDegree Ψ N := ⟨antisymDegree Ψ N - 1, Nat.sub_add_cancel hpos⟩
  have hAr : IsArithVar (mCoordIdeal (yFl Ψ N)) (d + 2) := by
    have hd2 : d + 2 = antisymDegree Ψ N + 1 := by omega
    rw [hd2]
    exact hA
  have h0 : (N - N).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have hdeg : d + 1 = 0 + Fintype.card Ψ * (N.choose 2 + (N - N).choose 2) := by
    rw [h0, add_zero, zero_add]
    exact hd1
  have hhom' : ∀ p : Ψ × Fin N, BM.hom p = fsHerm (FlIdx Ψ N) (M.dy p) := fun p => (hhom p).trans (hdy p).symm
  obtain ⟨FA, hFAline⟩ := _root_.PositivityTheory.Xgp.t_c_fl_an _ _ _ _ Ψ N N M 0 d BM hAr hdeg hbd hhom'
  obtain ⟨Cv, CR, hCv, hCRref, hCRline⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.identity_cover _ _ _ _ Ψ N N M 0 d BM FA
  have hunif := _root_.GlobalTheory.CompanionTheory.Relay.flag_analytic_data_uniformised _ _ _ _ Ψ N N M 0 d BM FA (by simp) hd1
  refine ⟨d, FA.S.comap some, CR.Re, hd1, ?_, ?_, ?_, ?_⟩
  · rw [CR.deg_eq, hCv]
  · intro p
    rw [hCRref, FA.ref_some, hdy]
  · intro p t
    rw [hCRline, hFAline, hdy]
  · exact ⟨FlagSys.mk le_rfl hd1 hunif (fun τ a b hab hor =>
      (_root_.PositivityTheory.Xgp.t_c_sqsys hIn _ _ _ _ Ψ N N M 0 d BM FA _ _ _ _ M Cv CR hAr τ a b hab hor).some)⟩

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GrassmannHeightZ2OfInputsAndZ2
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem grassmann_height_Z2_of_push : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement →
    SuccessiveMinimaUpperBound → GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement :=
  fun hIn hAI hZ2 =>
    GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.proof hZ2 (_root_.GlobalTheory.CompanionTheory.Ar.Giv.flagGrassPush hIn hAI)
      (GroundTheory.Heights₂.Heights.HilbertSamuel.FSGeomDegPos.proof hIn.degree
        GroundTheory.Heights₂.Heights.HilbertSamuel.MultiDegreePositive.full)

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicCoefficientsInFrame
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem differentiableOn_coeff_of_linearIndependent (n m g : ℕ) (U : Set (Fin n → ℂ))
    (d : Fin m → (Fin n → ℂ) → Fin g → ℂ) (x : (Fin n → ℂ) → Fin g → ℂ)
    (w : (Fin n → ℂ) → Fin m → ℂ) (hU : IsOpen U)
    (hd : ∀ b, DifferentiableOn ℂ (d b) U) (hx : DifferentiableOn ℂ x U)
    (hli : ∀ t ∈ U, LinearIndependent ℂ (fun b => d b t))
    (hw : ∀ t ∈ U, x t = ∑ b, w t b • d b t) : DifferentiableOn ℂ w U := by
  intro t₀ ht₀
  apply DifferentiableAt.differentiableWithinAt
  have hUn : U ∈ 𝓝 t₀ := hU.mem_nhds ht₀

  let φ : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ (fun b => d b t₀)
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have h0 := Fintype.linearIndependent_iff.1 (hli t₀ ht₀) v
      (by simpa [φ, Fintype.linearCombination_apply] using hv)
    exact funext h0
  obtain ⟨L0, hL0⟩ := φ.exists_leftInverse_of_injective hφ
  let L : (Fin g → ℂ) →L[ℂ] (Fin m → ℂ) := LinearMap.toContinuousLinearMap L0
  have hLd : ∀ b, L (d b t₀) = Pi.single b 1 := by
    intro b
    have h1 : φ (Pi.single b 1) = d b t₀ := by
      simp [φ, Fintype.linearCombination_apply, Pi.single_apply]
    have h2 := LinearMap.congr_fun hL0 (Pi.single b 1)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, h1] at h2
    exact h2
  let T : (Fin n → ℂ) → ((Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) := fun t =>
    ∑ b, (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) b).smulRight (L (d b t))
  have hTapply : ∀ t v, T t v = ∑ b, v b • L (d b t) := by
    intro t v
    simp [T, ContinuousLinearMap.sum_apply]
  have hT0 : T t₀ = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    rw [hTapply]
    simp only [hLd]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hTd : DifferentiableAt ℂ T t₀ := by
    have hb : ∀ b ∈ (Finset.univ : Finset (Fin m)), DifferentiableAt ℂ (fun t =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) b).smulRight (L (d b t))) t₀ := by
      intro b _
      exact (ContinuousLinearMap.smulRightL ℂ (Fin m → ℂ) (Fin m → ℂ)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) b)).differentiableAt.comp t₀
        (L.differentiableAt.comp t₀ ((hd b).differentiableAt hUn))
    exact DifferentiableAt.fun_sum hb
  have hTu : ∀ᶠ t in 𝓝 t₀, IsUnit (T t) := by
    have hc : ContinuousAt T t₀ := hTd.continuousAt
    have : {u : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ) | IsUnit u} ∈ 𝓝 (T t₀) := by
      rw [hT0]
      exact Units.isOpen.mem_nhds isUnit_one
    exact hc this
  have heq : w =ᶠ[𝓝 t₀] fun t => Ring.inverse (T t) (L (x t)) := by
    filter_upwards [hTu, hUn] with t hu ht
    obtain ⟨u, hu'⟩ := hu
    have h1 : L (x t) = T t (w t) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hw t ht, hTapply, map_sum]
      simp
    rw [h1, ← hu', Ring.inverse_unit, ← ContinuousLinearMap.mul_apply, u.inv_mul]
    rfl
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  have hinv : DifferentiableAt ℂ (fun t => Ring.inverse (T t)) t₀ := by
    have : DifferentiableAt ℂ Ring.inverse (T t₀) := by
      rw [hT0]
      exact differentiableAt_inverse isUnit_one
    exact this.comp t₀ hTd
  have hLx : DifferentiableAt ℂ (fun t => L (x t)) t₀ :=
    L.differentiableAt.comp t₀ (hx.differentiableAt hUn)
  exact hinv.clm_apply hLx

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end

