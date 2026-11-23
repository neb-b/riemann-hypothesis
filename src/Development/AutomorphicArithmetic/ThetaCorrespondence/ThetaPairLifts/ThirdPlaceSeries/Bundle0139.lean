module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0726
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0328
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2124
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0127
public import Formalism.LocalToGlobal.FiniteTOf
public import Formalism.LocalToGlobal.Bundle0002
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0109
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0091
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0120
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0458
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0111
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VectorAtSplitPlace
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DzVecLoc
theorem vector_at_split_place (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (hC : GlobalTheory.HeightCounting.Up.CenLoc D P.M) (S : Reading P.T)
    (hT : _root_.GlobalTheory.NPin.IsFaithfulReading P S) (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E)
    (hw : IsSplitPl D.host s.w) (hs : s.w = D.naut.plGw k v) (ρ : FDRep ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    (hρ : CategoryTheory.Simple ρ) (hocc : PairedCharacterCondition.RT.Occurs i PI k v (idemOf D k ρ)) :
    ∃ x, IsBlockVec (S i s.w hw).mu ((S i s.w hw).rep PI).π x ∧ NotKilled ((S i s.w hw).rep PI).π (idemOf D k ρ) x := by
  classical
  have hrep := hT.rep i s hw PI
  rcases hrep with ⟨c, T, hc, hcs, -, -, -⟩
  obtain ⟨F, hF, hne⟩ := hocc
  set z := idemOf D k ρ with hz
  have hzc : ∀ b, z * b = b * z := by
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exact (GlobalTheory.SerOSys.zIdem_centralIdempotent ρ hρ).2
  have hcen := GlobalTheory.SeriesSupportTest.atPlace_central D k v z hzc
  obtain ⟨L, hLift, hCL⟩ := hC i
  have e : (P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) F) =
      actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) ((P.M.loc i).real F) := by
    rw [NTypes.onMt, dite_eq_left hcen]; exact hCL ⟨_, hcen⟩ F
  have hne' : actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) ((P.M.loc i).real F) ≠ 0 := by
    rw [← e]; intro h0; apply hne; exact (P.M.loc i).real_inj (h0.trans (map_zero _).symm)
  let g : GL (Fin D.R.r) (ZMod (D.host.g k)) → G0g D.nd := fun h =>
    Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩ h
  have hsum : actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) ((P.M.loc i).real F) =
      ∑ h, z.coeff h • NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) := by
    unfold actSum Formalism.MainNotions.ArithmeticCylinders.atPlace
    rw [MonoidAlgebra.coeff_ofCoeff, Finsupp.sum_mapDomain_index
      (h := fun g c => c • NG.rt D.host.E D.R.nV (L g) ((P.M.loc i).real F))
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
    exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)
  have hg : ∀ h, ∃ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x ∧ IsLiftN h (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) ∧ NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) = NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) := fun h =>
    _root_.GlobalTheory.T.lift_through_completion_iso_alt hL D P i PI k v s hs c hc hcs L hLift F hF h (g h) (by simp [g]) (fun kv hkv => by simp [g, Pi.mulSingle_eq_of_ne hkv])
  choose xs hxs using hg
  have hne'' : ∑ h, z.coeff h • NG.rt D.host.E D.R.nV (xs h) ((P.M.loc i).real F) ≠ 0 := by
    rw [hsum] at hne'
    simpa only [(hxs _).2.2] using hne'
  obtain ⟨U, hU, h1U, hθU⟩ := _root_.GlobalTheory.BlockType.blockChar_eventually_one _ D.R.r D.R.t (S i s.w hw).mu (S i s.w hw).mu_ok.1
  have hFS : (P.M.loc i).real F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i PI) := by
    have := hF; rw [P.H.av.typeV] at this; exact this
  obtain ⟨y, hy, hyz⟩ := _root_.GlobalTheory.EigLocalSum.exists_eigen_local_sum D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i PI) (P.H.av.irr i PI) s
    ((S i s.w hw).rep PI).toIrrRep (hT.rep i s hw PI) c hc hcs (GlobalTheory.BlockType.blockGrp _ D.R.r D.R.t)
    (GlobalTheory.BlockType.blockChar (S i s.w hw).mu) U (fun h hh => hh.1) (GlobalTheory.BlockType.kOne_le_blockGrp _ _) hU h1U
    (fun g hg _ => hθU g hg) _ hFS (_root_.GlobalTheory.T.completion_iso_split_place_alt hL D P S hT i PI k v s hw hs c hc hcs F hF) _ xs (fun h => z.coeff h)
    (fun h => (hxs h).1) hne''
  refine ⟨y, GlobalTheory.BlockType.isBlockVec_of _ _ _ hy, fun h => Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV (xs h)), fun h => (hxs h).2.1, ?_⟩
  rw [Finsupp.sum_fintype _ _ (by simp)]
  exact hyz
end GlobalTheory.DzVecLoc
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPointStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_parameter_strict_antitone_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → 1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 ∧ (∀ u1, Quo p i PP u1 → u1 = (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) ∧ (∀ τ, StrictAnti ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ) ∧ StrictAnti (CompHt.uPrime (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ)) ∧ (∃ w : Psi p.T.Q.H → ℤ, (∀ τ, |w τ| ≤ 3 * ((Fm.D x ι).R.r : ℤ)) ∧ uM p i = (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP) + GlobalTheory.FlatLine.parWt (dat p i) w) ∧ ∀ s : ℕ, s ≤ 3 → ∀ τ, Antitone (uM p i τ + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ) ∧ Antitone (((lenT p i PP + CompHt.dimFlag (dat p i) + (if s = 0 then 3 else 4) : ℕ) : ℤ) • (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ - (uM p i τ + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ)) := by
  first | exact @_root_.GlobalTheory.QuoWt.weights_at_point_alt | exact _root_.GlobalTheory.QuoWt.weights_at_point_alt | (intros; apply _root_.GlobalTheory.QuoWt.weights_at_point_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Wire4F
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S
namespace Formalism.L2.Top4Wire2
variable {𝒜 : FamClass} {sel : _root_.Formalism.L2.TwistSelection 𝒜} {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel}
  {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP} {selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel}
theorem wire4F_alt [∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (i : Fm.Ix x), IsTotallyComplex (Fm.D x i).what₂.LL]
    (selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK) (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel selI)
    (OneMapRow : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop)
    (Cabs : ℝ) (hCabs : 1 ≤ Cabs)
    (hTw : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      TieTwRec (Fm.L x i) (selP Fm hc x hx h i).1.S0.Tw)
    (hD0 : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      (Fm.D x i).what₂.D0 = ((selP Fm hc x hx h i).1.A3.A.fam.R (selP Fm hc x hx h i).1.A3.A.fam.μ0).dZ ((selP Fm hc x hx h i).1.A3.A.fam.lvl (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0)
        ((selP Fm hc x hx h i).1.Zs.Z (selP Fm hc x hx h i).1.A3.A.fam.μ0))
    (hPt : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      RowsHoldDcPt3 (selP Fm hc x hx h i).1)
    (hR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      DivRows3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps (selP Fm hc x hx h i).1.ψs (selP Fm hc x hx h i).1.Zs (selP Fm hc x hx h i).1.S0 (selP Fm hc x hx h i).1.S1 (Fm.ex x hx i).p0 (selP Fm hc x hx h i).1.C (selP Fm hc x hx h i).1.NuC (selP Fm hc x hx h i).1.I)
    :
    _root_.Formalism.L2.Top4.Wire4Alt sel selS selP selDH selC selK selI hPA (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt selI Fm hc x hx h i C CH)
      OneMapRow Cabs := by
  intro eps Fm hc CH hCsz hDG hRows hOne _hBu hN
  obtain ⟨Ce, x3, hCe⟩ := id hN
  obtain ⟨Cd, x4, hFDG⟩ := hDG
  obtain ⟨C, hC, x1, hr⟩ := hRows
  obtain ⟨x2, ho⟩ := hOne
  refine ⟨max 0 (max (50 * c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct + 10)
      (60 * ceF C Ce (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct))),
    max (max x1 x2) (max (max x3 x4)
      (x0F eps Fm.Ct Fm.Cc CH (ceF C Ce (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct)))),
    fun x hx0 hx h i => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0
  have hx2 : x2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0
  have hx3 : x3 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx0
  have hx4 : x4 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx0
  have hx5 : x0F eps Fm.Ct Fm.Cc CH (ceF C Ce (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct)) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx0
  obtain ⟨ra, hd⟩ := hr x hx h hx1 i
  obtain ⟨prows, hsep⟩ := hPA Fm (d3_a hc) x hx h i
  have hok1 := (selC Fm (d3_a hc) x hx h i).ok1
  have hP : CovolumeOntoIsometryConditions (selI Fm (d3_a hc) x hx h i).Rl (selI Fm (d3_a hc) x hx h i).F (selI Fm (d3_a hc) x hx h i).sEE (hkCan (selP Fm (d3_a hc) x hx h i).1.A3) C CH :=
    { toPrimRows3 := prows, w1 := ra.w1, covol := ra.covol, onto := ra.onto hN, lamLow := ra.lamLow (ho x hx h hx2 i),
      seeIso := ra.seeIso, miStar := ra.miStar, fun0 := ra.fun0 hN }
  have hZs : (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).Zs = (selP Fm (d3_a hc) x hx h i).1.Zs := (selI Fm (d3_a hc) x hx h i).zs
  have hS0 : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).core.base.toIndefData (selP Fm (d3_a hc) x hx h i).1.S0 := (selI Fm (d3_a hc) x hx h i).s0
  have hS := Fm.sizes x hx i
  have hFD : FactDGam (Fm.D x i) (max Cd 0) := J.factDGam_mono (hFDG x hx4 i) (le_max_left _ _)
  have hDGp := _root_.Formalism.L2.DIV.Cons.gamma_size_of_sizeData_alt (selP Fm (d3_a hc) x hx h i).2 (_root_.Formalism.L2.Top4Wire2.finite_T_of_squareIntegrableColumns (selC Fm (d3_a hc) x hx h i))
    hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hS.2.2.2.2.2.1 (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2 (Fm.L x i).Nc (cloudConstant_nonneg (Fm.L x i))
    (max Cd 0) (le_max_right _ _) hFD
  have eCc : (Fm.L x i).Cc = Fm.Cc := Fm.Cc_eq x i
  have eCt : (Fm.L x i).Ct = Fm.Ct := Fm.Ct_eq x i
  have eCY : (Fm.params x hx i).CYL = Fm.CYL := Fm.params_CYL x hx i
  have hxL : x0F (Fm.L x i).sc.eps (Fm.L x i).Ct (Fm.L x i).Cc CH
      (ceF C Ce (2 + 9 * max Cd 0) (c0F Fm.Csz (Fm.L x i).Cc (Fm.params x hx i).CYL (Fm.L x i).Ct)) ≤ (Fm.L x i).sc.x := by
    rw [Fm.L_eps x i, eCt, eCc, eCY, Fm.L_x x i hx]
    exact hx5
  obtain ⟨lam0, Sw, C1, H, dg, hdg, hdvd, hA⟩ := arithClause_rec (Fm.L x i) (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2 hS (selDH Fm (d3_a hc) x hx h i).2.1 (selDH Fm (d3_a hc) x hx h i).2.2 (Fm.params x hx i) (Fm.ex x hx i).fdef
    (Fm.ex x hx i).kap_def (selP Fm (d3_a hc) x hx h i).1.A3 (selP Fm (d3_a hc) x hx h i).1.tied.div.grp.card (selP Fm (d3_a hc) x hx h i).1.P0 (selP Fm (d3_a hc) x hx h i).1.ψ0 (selP Fm (d3_a hc) x hx h i).1.Ps (selP Fm (d3_a hc) x hx h i).1.ψs (selC Fm (d3_a hc) x hx h i).c.face (selC Fm (d3_a hc) x hx h i).Sp _ C CH Fm.Csz Ce
    (2 + 9 * max Cd 0) (_root_.Formalism.L2.Top4Wire2.finite_T_of_squareIntegrableColumns (selC Fm (d3_a hc) x hx h i)) hDGp hC hCsz hxL (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass)
  have e0 : c0F Fm.Csz (Fm.L x i).Cc (Fm.params x hx i).CYL (Fm.L x i).Ct = c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct := by
    rw [eCc, eCY, eCt]
  exact _root_.Formalism.L2.RowDataTransport.ptK_of_real_alt ((sel Fm (d3_a hc)).2 x hx h i) ((_root_.Formalism.L2.Top4.RankOfDivisionKernel sel selS selP selDH selC selK selI hPA Fm hc).2 x hx h i) rfl
    (selP Fm (d3_a hc) x hx h i).2 ra.kap (hPt Fm (d3_a hc) x hx h i) (hR Fm (d3_a hc) x hx h i)
    (selS Fm (d3_a hc) x hx h i) (selI Fm (d3_a hc) x hx h i) hsep C CH hP ra.pass _ Cabs (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2
    (selDH Fm (d3_a hc) x hx h i).2.1 (selDH Fm (d3_a hc) x hx h i).2.2 lam0 _ _ Fm.Csz Sw C1 (Equiv.refl _) H
    (_root_.Formalism.L2.RowDataTransport.inpAt_of_alt (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2 lam0 _ _ Fm.Csz Sw C1 (Equiv.refl _) H Ce (hCe x hx3 i)
      (by rw [tw_heq hZs hS0]; exact hTw Fm (d3_a hc) x hx h i) (by rw [hZs]; exact hD0 Fm (d3_a hc) x hx h i)
      (lift_exponent_of_least (selP Fm (d3_a hc) x hx h i).1.A3.A hok1.ok2 (selP Fm (d3_a hc) x hx h i).1.P0 (selP Fm (d3_a hc) x hx h i).1.ψ0 ((selP Fm (d3_a hc) x hx h i).1.A3.fam3.toSub2 (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).Zs)
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).core.base.μ (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).core.base.Tw _ (fun _ _ _ => rfl))
      ⟨dg, hdg, hdvd, hA⟩ (fun NuC I hT hI u => hd hok1 hsep hP ra.pass lam0 _ _ Sw C1 H NuC I hT hI u))
    (Fm.nprimeDef x hx i) (fun u => Fm.h_eq x hx i u)
    (fixedScale_tied (Fm.L x i) (selDH Fm (d3_a hc) x hx h i).1.1 (selDH Fm (d3_a hc) x hx h i).1.2 (Fm.ex x hx i).kap_def (Fm.ex x hx i).fdef (selP Fm (d3_a hc) x hx h i).1.A3 (selP Fm (d3_a hc) x hx h i).1.P0 (selP Fm (d3_a hc) x hx h i).1.ψ0 (Equiv.refl _)
      (Fm.L x i).Nc Fm.Csz (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm (d3_a hc) x hx h i) hok1 hsep C CH hP ra.pass).Zs C CH)
    (le_max_left _ _) (by rw [e0]; exact le_trans (le_max_left _ _) (le_max_right _ _))
    (by rw [e0]; exact le_trans (le_max_right _ _) (le_max_right _ _)) hCabs
    (Formalism.MainNotions.DIV.La_nonneg (Fm.L x i) (Fm.sizes x hx i).2.2.2.2.2.2.1)
end Formalism.L2.Top4Wire2
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiChrEqCols
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 Formalism.IndefR Formalism.IndefR.Links
namespace GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem xi_chrEq_cols_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ t, Formalism.IndefR.Links.ChrEq ((_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).xi t) (q.w.I.xi (b.P.I.tup t)) := by
  intro hL p K q c b hw
  obtain ⟨x, a, ax, y, recPin, s, pt, sx, eF, cW, d3b, side, colPins⟩ := hw
  have key : ∀ t : x.T, Formalism.IndefR.Links.ChrEq (x.R.toRealDat.xi t) (q.w.I.xi (x.Y.tup t)) := by
    have hxi : ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) μ → HEq (x.R.toLevCh.xiH (x.Y.tupT μ)) (q.w.I.xi μ) := by
      have h := eq_of_heq ax
      rw [← h]
      exact fun μ hμ => ((GlobalTheory.Mem.R3.twArgs_lev K q.B q.f q.T q.w q.Z _ _ _ _ _ _ _ _ _ _ a).2.2.1 μ hμ).2
    intro t
    have hu : Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) (x.Y.tup t) := by
      rcases x.pins.char.tup.mu_used t with h | ⟨w, h⟩
      · rw [h]; exact Or.inl x.Y.tup0
      · rw [← h]
        obtain ⟨w', rfl⟩ := (q.w.D q.Z).plEq.surjective w
        exact Or.inr ⟨w', (x.Y.muAt w').symm⟩
    have h1 := hxi _ hu
    rw [x.Y.tupT_tup] at h1
    have h2 := x.pins.char.base.lev.xi t
    rw [eq_of_heq h1] at h2
    exact h2
  show (fun k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => ∀ t : k.P.T, Formalism.IndefR.Links.ChrEq (k.B.Q.Rl.toRealDat.xi t) (q.w.I.xi (k.P.I.tup t))) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b)
  rw [y.eq]
  exact key
end GlobalTheory.Fam
end
end

