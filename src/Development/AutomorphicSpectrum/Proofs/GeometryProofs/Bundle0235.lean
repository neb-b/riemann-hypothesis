module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0033
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0233
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0154
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0136
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0116
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0133

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedAtlasSncSection
section
open GlobalTheory.CompanionTheory.Ar AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open Classical

namespace GlobalTheory.CompanionTheory.Ar.Adapt


open ReciprocityTheory.AnForm.M.PLAux in
theorem exists_adaptedAtlas : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W →
    (∀ y, logNormSec L s y ≤ 0) → ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B L s := by
  intro e X _ _ _ A L s n m W hL hs hsnc _hle
  have hgood : ∀ x : X, ∃ φ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A φ ∧
      x ∈ φ.source ∧ φ x = 0 ∧ Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target ∧
      ∃ (S : Finset (Fin e)) (μ : Fin e → ℕ) (M : ℝ), (∀ i ∈ S, 1 ≤ μ i) ∧
        (∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧
        ∀ y ∈ Metric.closedBall (0 : Fin e → ℂ) 2, φ.symm y ∉ bdry s →
          |rW L s (φ.symm y) - rLoc S μ y| ≤ M := by
    intro x
    obtain ⟨φ, S, μ, v, hφc, hxφ, hball, hφx, hsrcU, hμ, hv, hv0, hsv⟩ :=
      GlobalTheory.CompanionTheory.Ar.PB.LocalForm.exists_local_form e X A L s n m W hsnc x
    refine ⟨φ, hφc, hxφ, hφx, hball, S, μ, ?_⟩

    have hnorm : ∀ y ∈ φ.source,
        ‖s y y‖ * Real.exp (-L.φ y y) = ‖s x y‖ * Real.exp (-L.φ x y) := fun y hy =>
      (hs.2 x y y ⟨hsrcU hy, L.mem_U y⟩).symm
    have hzero : ∀ y ∈ φ.source, (s y y = 0 ↔ s x y = 0) := by
      intro y hy
      have h := hnorm y hy
      constructor
      · intro h0
        rw [h0, norm_zero, zero_mul] at h
        have := (mul_eq_zero.1 h.symm).resolve_right (Real.exp_pos _).ne'
        exact norm_eq_zero.1 this
      · intro h0
        rw [h0, norm_zero, zero_mul] at h
        have := (mul_eq_zero.1 h).resolve_right (Real.exp_pos _).ne'
        exact norm_eq_zero.1 this
    have hmono : ∀ y ∈ φ.source, (s x y = 0 ↔ ∃ i ∈ S, φ y i = 0) := by
      intro y hy
      rw [hsv y hy, mul_eq_zero, Finset.prod_eq_zero_iff]
      constructor
      · rintro (h | ⟨i, hi, h⟩)
        · exact absurd h (hv0 y hy)
        · exact ⟨i, hi, pow_eq_zero_iff (Nat.one_le_iff_ne_zero.1 (hμ i hi)) |>.1 h⟩
      · rintro ⟨i, hi, h⟩
        exact Or.inr ⟨i, hi, by rw [h, zero_pow (Nat.one_le_iff_ne_zero.1 (hμ i hi))]⟩
    have hbd : ∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0) := by
      intro y hy
      have hp := φ.map_target hy
      show s (φ.symm y) (φ.symm y) = 0 ↔ _
      rw [hzero _ hp, hmono _ hp, φ.right_inv hy]

    have hK : IsCompact (Metric.closedBall (0 : Fin e → ℂ) 2) := isCompact_closedBall _ _
    have hF : ContinuousOn (fun z => Real.log ‖v (φ.symm z)‖) (Metric.closedBall (0 : Fin e → ℂ) 2) := by
      intro z hz
      have hzt := hball hz
      have han := analyticAt_compat_fun hφc hv hzt (φ.map_target hzt)
      exact (han.continuousAt.norm.log (by simpa using hv0 _ (φ.map_target hzt))).continuousWithinAt
    have hG : ContinuousOn (fun z => L.φ x (φ.symm z)) (Metric.closedBall (0 : Fin e → ℂ) 2) := by
      have h := contDiffOn_compat hφc (L.isOpen_U x) (hL.1 x)
      refine h.continuousOn.mono ?_
      intro z hz
      exact ⟨hball hz, hsrcU (φ.map_target (hball hz))⟩
    obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn hF
    obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn hG
    refine ⟨2 * C₁ + 2 * C₂ + ∑ i ∈ S, (μ i : ℝ) * Real.log 4, hμ, hbd, ?_⟩
    intro y hy hyb
    have hyt := hball hy
    have hp := φ.map_target hyt
    set p := φ.symm y with hpdef
    have hφp : φ p = y := φ.right_inv hyt
    have hspp : s p p ≠ 0 := hyb
    have hsxp : s x p ≠ 0 := fun h => hspp ((hzero p hp).2 h)
    have hyi : ∀ i ∈ S, y i ≠ 0 := fun i hi h0 =>
      hsxp ((hmono p hp).2 ⟨i, hi, by rw [hφp]; exact h0⟩)
    have hvp : v p ≠ 0 := hv0 p hp

    have hlogN : logNormSec L s p = Real.log ‖v p‖ + ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ - L.φ x p := by
      unfold logNormSec
      rw [hnorm p hp, Real.log_mul (norm_ne_zero_iff.2 hsxp) (Real.exp_pos _).ne', Real.log_exp,
        hsv p hp, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hvp), norm_prod,
        Real.log_prod]
      · rw [hφp]
        congr 2
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [norm_pow, Real.log_pow]
      · intro i hi
        rw [hφp, norm_pow]
        exact pow_ne_zero _ (norm_ne_zero_iff.2 (hyi i hi))
      · rw [norm_ne_zero_iff, Finset.prod_ne_zero_iff]
        intro i hi
        rw [hφp]
        exact pow_ne_zero _ (hyi i hi)
    have hloc : rLoc S μ y = Real.exp 1 + ∑ i ∈ S, (μ i : ℝ) * (Real.log 4 - 2 * Real.log ‖y i‖) := by
      unfold rLoc
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Real.log_div (by norm_num) (pow_ne_zero _ (norm_ne_zero_iff.2 (hyi i hi))), Real.log_pow]
      push_cast
      ring
    have hdiff : rW L s p - rLoc S μ y =
        -2 * Real.log ‖v p‖ + 2 * L.φ x p - ∑ i ∈ S, (μ i : ℝ) * Real.log 4 := by
      unfold rW
      rw [hlogN, hloc]
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [show ∑ i ∈ S, (μ i : ℝ) * (2 * Real.log ‖y i‖) = 2 * ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring]
      ring
    rw [hdiff]
    have h1 : |Real.log ‖v p‖| ≤ C₁ := by simpa [Real.norm_eq_abs] using hC₁ y hy
    have h2 : |L.φ x p| ≤ C₂ := by simpa [Real.norm_eq_abs] using hC₂ y hy
    have h3 : 0 ≤ ∑ i ∈ S, (μ i : ℝ) * Real.log 4 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  choose φ hφc hφx hφ0 hφb hrest using hgood
  choose S μ M hμ hbd hbnd using hrest
  have hU : ∀ x, φ x ⁻¹' Metric.ball 0 1 ∩ (φ x).source ∈ nhds x := by
    intro x
    refine IsOpen.mem_nhds ?_ ⟨by simp [hφ0 x], hφx x⟩
    rw [Set.inter_comm]
    exact (φ x).continuousOn.isOpen_inter_preimage (φ x).open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover _ hU
  have hcov : ∀ x, ∃ y ∈ t, x ∈ φ y ⁻¹' Metric.ball 0 1 ∩ (φ y).source := by
    intro x
    have : x ∈ (⊤ : Set X) := trivial
    rw [← ht] at this
    simp only [Set.mem_iUnion] at this
    obtain ⟨y, hy, hx⟩ := this
    exact ⟨y, hy, hx⟩
  obtain ⟨B, hAB, h1, h2⟩ := ReciprocityTheory.AnForm.M.atlasOfCompat A (fun i => φ (t.equivFin.symm i))
    (fun i => hφc _) (fun x => by
      obtain ⟨y, hy, hx⟩ := hcov x
      exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hx.2⟩)
  refine ⟨B, hAB, fun j => ?_, fun x => ?_, ∑ y ∈ t, |M y|, fun j => ?_⟩
  · obtain ⟨i, hi⟩ := h2 j
    rw [hi]
    exact hφb _
  · obtain ⟨y, hy, hx⟩ := hcov x
    obtain ⟨j, hj⟩ := h1 (t.equivFin ⟨y, hy⟩)
    refine ⟨j, ?_, ?_⟩
    · rw [hj]; simpa using hx.2
    · rw [hj]; simpa using hx.1
  · obtain ⟨i, hi⟩ := h2 j
    set y : X := (t.equivFin.symm i : X) with hydef
    have hyt : y ∈ t := (t.equivFin.symm i).2
    refine ⟨S y, μ y, hμ y, ?_, ?_⟩
    · rw [hi]; exact hbd y
    · intro z hz hzb
      rw [hi] at hzb ⊢
      refine (hbnd y z hz hzb).trans ((le_abs_self _).trans ?_)
      exact Finset.single_le_sum (f := fun y => |M y|) (fun _ _ => abs_nonneg _) hyt

end GlobalTheory.CompanionTheory.Ar.Adapt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorsionQuasiFiniteGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorsQF

variable {X : Scheme.{0}} (G : Over X) [GrpObj G]

theorem pow_eq_one_of_res {A B : Scheme.{0}} (u : A ⟶ B) [Epi u] (ξ : B ⟶ X) (y : Over.mk ξ ⟶ G) (n : ℕ)
    (g : Over.mk (u ≫ ξ) ⟶ G) (hg : g.left = u ≫ y.left) (h : g ^ n = 1) : y ^ n = 1 := by
  let f : Over.mk (u ≫ ξ) ⟶ Over.mk ξ := Over.homMk u rfl
  have e : g = f ≫ y := by ext1; simpa [f] using hg
  have h1 : f ≫ y ^ n = f ≫ 1 := by rw [comp_pow, ← e, h, comp_one]
  ext1
  have h2 := congrArg (fun z => z.left) h1
  simp only [Over.comp_left] at h2
  exact (cancel_epi u).1 h2

theorem epi_spMap {K L : Type} [Field K] [Field L] (a : K →+* L) : Epi (spMap a) := by
  have : Flat (spMap a) := by
    rw [spMap, Flat.SpecMap_iff]
    letI := a.toAlgebra
    exact (RingHom.flat_algebraMap_iff (R := K) (S := L)).2 inferInstance
  have : Surjective (spMap a) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    exact ⟨z, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩
  exact Flat.epi_of_flat_of_surjective _

theorem torsion_qfGroup : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (X : Scheme.{0})
    (G : Over X) [GrpObj G] (x : Sp R ⟶ X) (n : ℕ), IsSemiAbelian G → 0 < n →
    FullTorsion G (spMap (algebraMap R (FractionRing R)) ≫ x) n →
    ∃ (T : Type) (_ : CommGroup T) (_ : Finite T) (Q : BT.QFGroup R T) (i : Q.G.left ⟶ G.left),
      Q.IsTorsionAlong G x n i := by
  intro R _ _ _ _ X G _ x n hG hn hF
  have := hG.comm
  let ξ : Sp (FractionRing R) ⟶ X := spMap (algebraMap R (FractionRing R)) ≫ x
  let T : Subgroup (Over.mk ξ ⟶ G) := (powMonoidHom n).ker
  have hT : ∀ y : T, (y : Over.mk ξ ⟶ G) ^ n = 1 := fun y => MonoidHom.mem_ker.1 y.2
  have hfin : Finite T := by
    let L := AlgebraicClosure (FractionRing R)
    let a : FractionRing R →+* L := algebraMap (FractionRing R) L
    haveI := epi_spMap a
    let t : Sp L ⟶ X := spMap a ≫ ξ
    have h0 := GlobalTheory.finite_torsion_semiAbelian L ((Over.pullback t).obj G) (IsSemiAbelian.pullback t G hG) n hn
    have h1 : Finite {g : Over.mk t ⟶ G // g ^ n = 1} :=
      GlobalTheory.FewZeros.finite_torsion_of_mulEquiv
        (GlobalTheory.TorsionLift.ptsEquiv t G (𝟙_ (Over (Sp L))) t (Category.id_comp t)) n h0
    let f : Over.mk t ⟶ Over.mk ξ := Over.homMk (spMap a) rfl
    let φ : T → {g : Over.mk t ⟶ G // g ^ n = 1} := fun y => ⟨f ≫ y.1, by rw [← comp_pow, hT y, comp_one]⟩
    refine Finite.of_injective φ fun y z e => ?_
    have e1 := congrArg (fun w => (w.1 : Over.mk t ⟶ G).left) e
    simp only [φ, f, Over.comp_left, Over.homMk_left] at e1
    exact Subtype.ext (Over.OverMorphism.ext ((cancel_epi (spMap a)).1 e1))
  obtain ⟨Γ, i, h, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_torsion R T X G hG x n hn T.subtype Subtype.val_injective hT
    (fun Ω _ _ a g hg => by
      obtain ⟨y, hy⟩ := hF Ω a g hg
      haveI := epi_spMap a
      exact ⟨⟨y, MonoidHom.mem_ker.2 (pow_eq_one_of_res G (spMap a) ξ y n g hy hg)⟩, hy⟩)
  exact ⟨T, inferInstance, hfin, Γ, i, h⟩

end GlobalTheory.CompanionTheory.Ar.TorsQF
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantHolds
section
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem finConst_of_all_hosts : FinConst :=
  FinConstAll.finConst _root_.GlobalTheory.CompanionTheory.Ar.Flat.FinAll.finConstAll

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteMapEqOfThickeningsEq
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.EqRed
open GlobalTheory.AdicColimit

variable {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]

theorem eq_zero_of_forall_mem_map (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A] (x : A)
    (h : ∀ e : ℕ, x ∈ (I ^ (e + 1)).map (algebraMap R A)) : x = 0 := by
  have hI : I ≤ (⊥ : Ideal R).jacobson := IsAdicComplete.le_jacobson_bot I
  have key := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := A) I
    (by simpa only [Ideal.jacobson_bot] using hI)
  have hx : x ∈ (⨅ i : ℕ, I ^ i • (⊤ : Submodule R A)) := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    have h1 : x ∈ (I ^ (i + 1) • (⊤ : Submodule R A)) := by
      rw [Ideal.smul_top_eq_map]
      exact h i
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ i)) h1
  rw [key] at hx
  simpa using hx

theorem eq_of_reductions (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom] (f g : X ⟶ Y)
    (h : ∀ e, (Over.pullback (thick R I e)).map f = (Over.pullback (thick R I e)).map g) : f = g := by
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  have : IsAffine Y.left := isAffine_of_isAffineHom Y.hom

  let ψ : CommRingCat.of R ⟶ Γ(X.left, ⊤) := Spec.preimage (X.left.isoSpec.inv ≫ X.hom)
  have hψ : Spec.map ψ = X.left.isoSpec.inv ≫ X.hom := Spec.map_preimage _
  let _ : Algebra R Γ(X.left, ⊤) := ψ.hom.toAlgebra
  have hfin : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
  have hfin' : ψ.hom.Finite := (IsFinite.SpecMap_iff ψ).1 hfin
  have : Module.Finite R Γ(X.left, ⊤) := hfin'

  let u : Spec Γ(X.left, ⊤) ⟶ Spec Γ(Y.left, ⊤) := X.left.isoSpec.inv ≫ f.left ≫ Y.left.isoSpec.hom
  let v : Spec Γ(X.left, ⊤) ⟶ Spec Γ(Y.left, ⊤) := X.left.isoSpec.inv ≫ g.left ≫ Y.left.isoSpec.hom
  have hu : Spec.map (Spec.preimage u) = u := Spec.map_preimage _
  have hv : Spec.map (Spec.preimage v) = v := Spec.map_preimage _

  have hred : ∀ e : ℕ, Spec.preimage u ≫ CommRingCat.ofHom (Ideal.Quotient.mk
      ((I ^ (e + 1)).map (algebraMap R Γ(X.left, ⊤)))) = Spec.preimage v ≫ CommRingCat.ofHom (Ideal.Quotient.mk
      ((I ^ (e + 1)).map (algebraMap R Γ(X.left, ⊤)))) := by
    intro e
    let J := (I ^ (e + 1)).map (algebraMap R Γ(X.left, ⊤))
    let m : Spec (CommRingCat.of (Γ(X.left, ⊤) ⧸ J)) ⟶ Spec Γ(X.left, ⊤) :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
    let q : Spec (CommRingCat.of (Γ(X.left, ⊤) ⧸ J)) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap J (algebraMap R Γ(X.left, ⊤)) Ideal.le_comap_map))
    have hcond : (m ≫ X.left.isoSpec.inv) ≫ X.hom = q ≫ thick R I e := by
      rw [Category.assoc, ← hψ]
      simp only [m, q, thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 1
    let t : Spec (CommRingCat.of (Γ(X.left, ⊤) ⧸ J)) ⟶ (thickObj R I e X).left :=
      pullback.lift (m ≫ X.left.isoSpec.inv) q hcond
    have ht : t ≫ thickι I e X = m ≫ X.left.isoSpec.inv := pullback.lift_fst _ _ _
    have hfg : thickι I e X ≫ f.left = thickι I e X ≫ g.left := by
      have hl : thickHom I e f = thickHom I e g := congrArg (fun φ => φ.left) (h e)
      rw [← thickHom_ι, ← thickHom_ι, hl]
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hu, hv]
    change m ≫ u = m ≫ v
    simp only [u, v]
    rw [← Category.assoc m, ← Category.assoc m, ← ht, Category.assoc t, Category.assoc t,
      reassoc_of% hfg]
  have hpre : Spec.preimage u = Spec.preimage v := by
    ext b
    refine sub_eq_zero.1 (eq_zero_of_forall_mem_map I Γ(X.left, ⊤) _ fun e => ?_)
    exact Ideal.Quotient.eq.1 (congrArg (fun φ => φ.hom b) (hred e))
  have huv : u = v := by rw [← hu, ← hv, hpre]
  apply Over.OverMorphism.ext
  have h1 : f.left ≫ Y.left.isoSpec.hom = g.left ≫ Y.left.isoSpec.hom := (cancel_epi X.left.isoSpec.inv).1 huv
  exact (cancel_mono Y.left.isoSpec.hom).1 h1

end GlobalTheory.CompanionTheory.Ar.BT.EqRed
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsOfClosedSubgroup
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.BT.RatKer

theorem exists_section_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (H : Type) [CommGroup H] (Γf : QFGroup R H) (A E : Over (Spec (CommRingCat.of R))) (a : A ⟶ Γf.G) (b : Γf.G ⟶ E) (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ E), IsClosedImmersion a.left → IsPullback a (toUnit A) b e → ∀ g : A.left, (A.hom g).asIdeal = ⊥ → ∃ (κ : genPt R ⟶ A) (x : Spec (CommRingCat.of (FractionRing R))), κ.left x = g := by
  intro R _ _ H _ Γf A E a b e ha hP g hg
  have hwa : Γf.G.hom (a.left g) = A.hom g := by
    rw [← Scheme.Hom.comp_apply, Over.w]
  obtain ⟨t, x, hx⟩ := Γf.11 (a.left g) (by rw [hwa]; exact hg)
  have hgen : (GlobalTheory.CompanionTheory.Ar.BT.genPt R).hom x = A.hom g := by
    rw [← Over.w (Γf.9 t), Scheme.Hom.comp_apply, hx, hwa]
  have hab := congrArg (fun φ => φ.left g) hP.w
  simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.toUnit_left] at hab
  have hpt : Γf.9 t ≫ b = toUnit (GlobalTheory.CompanionTheory.Ar.BT.genPt R) ≫ e := by
    apply Over.OverMorphism.ext
    apply GlobalTheory.CompanionTheory.Ar.BT.Tors.eq_of_same_point E.hom _ _ (Over.w _) (Over.w _) x x
    simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.toUnit_left]
    rw [hx, hab, hgen]
  refine ⟨hP.lift (Γf.9 t) (toUnit _) hpt, x, ?_⟩
  apply a.left.isClosedEmbedding.injective
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hP.lift_fst, hx]

end GlobalTheory.CompanionTheory.Ar.BT.RatKer
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelActionSubalgebra
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackLie

theorem lieModel_along_generic : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel G ξ Li) (B : Type) [CommRing B] (act : OAct B G) (ρ₀ : B →+* Module.End Ω Li), M₀.IsActOf act.act ρ₀ → ∀ (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) (x : Spec (CommRingCat.of R) ⟶ X), spMap (algebraMap R Ω) ≫ x = ξ → ∃ (L : Type) (_ : AddCommGroup L) (_ : Module R L) (M : LieModel G x L) (ρ : B →+* Module.End R L) (toLi : L →ₗ[R] Li), Module.Finite R L ∧ Module.Projective R L ∧ M.IsActOf act.act ρ ∧ IsBaseChange Ω toLi ∧ (∀ v, (M₀.pt (toLi v)).left = spMap (dualMap (algebraMap R Ω)) ≫ (M.pt v).left) ∧ ∀ a v, toLi (ρ a v) = ρ₀ a (toLi v) := by
  intro X G _ _ _ Ω _ ξ Li _ _ M₀ B _ act ρ₀ h₀ O _ _ R x hx
  subst hx
  obtain ⟨L, iL, mL, ⟨M⟩⟩ := lieModel_exists X G R x
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act X G R x L M B act.act act.hom act.one act.mul act.add
  have hsm : ∀ (a : R) (t : Li), a • t = algebraMap R Ω a • t := fun _ _ => rfl
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ x = spMap (algebraMap R Ω) ≫ x := rfl
  have ex : ∀ e, ∃ t, M₀.pt t = LieTangent.epsBase (algebraMap R Ω) hφ ≫ M.pt e :=
    fun e => M₀.onto _ (LieTangent.isTanAt_base _ hφ (M.tan e))
  choose f hf using ex
  let j : L →ₗ[R] Li :=
    { toFun := f
      map_add' := fun a b => M₀.inj (by rw [M₀.add, hf, hf, hf, M.add, comp_mul])
      map_smul' := fun c e => M₀.inj (by
        rw [RingHom.id_apply, hsm, LieModel.pt_smul, hf, hf, LieModel.pt_smul, ← Category.assoc,
          LieTangent.base_scale, Category.assoc]) }
  have hl : ∀ v, (M₀.pt (j v)).left = spMap (dualMap (algebraMap R Ω)) ≫ (M.pt v).left := fun v => by
    change (M₀.pt (f v)).left = _
    rw [hf]
    rfl
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange X G R x L M
  refine ⟨L, iL, mL, M, ρ, j, h1, h2, hρ, h3 Ω Li M₀ j hl, hl, fun a v => M₀.inj ?_⟩
  change M₀.pt (f (ρ a v)) = M₀.pt (ρ₀ a (f v))
  rw [h₀ a, hf, hf, hρ a, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackLie
end

