module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockSubstitutionPreservesHarmonicLetterPolynomia
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0789
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0441
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointHighestWeightHarmonicOfFockLowestKType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Sl2NonnegWeightOfHighestWeightVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0048

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVecExistsUnique
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatVecExist

open GlobalTheory.PlaceModel

variable {D : D7}

theorem idemSum_split {e : AE D} {P Q : Finset (Pl D.host.E)} (he : IsIdemSum e (P ∪ Q)) (hd : Disjoint P Q) :
    ∃ eP eQ : AE D, IsIdemSum eP P ∧ IsIdemSum eQ Q ∧ eP * eQ = 0 ∧ eP * cA D eQ = 0 ∧ eQ * cA D eP = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, hc⟩ := he
  have h1 : ∀ i ∈ P ∪ Q, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hx := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es (P ∪ Q) h1 hc
  have hcr : ∀ A B : Finset (Pl D.host.E), A ⊆ P ∪ Q → B ⊆ P ∪ Q →
      (∑ i ∈ A, es i) * cA D (∑ j ∈ B, es j) = 0 := fun A B hA hB => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => hx i (hA hi) j (hB hj)
  have hP : P ⊆ P ∪ Q := Finset.subset_union_left
  have hQ : Q ⊆ P ∪ Q := Finset.subset_union_right
  refine ⟨∑ i ∈ P, es i, ∑ i ∈ Q, es i, ⟨⟨es, fun i hi => hes i (hP hi), rfl⟩, hcr P P hP hP⟩,
    ⟨⟨es, fun i hi => hes i (hQ hi), rfl⟩, hcr Q Q hQ hQ⟩, ?_, hcr P Q hP hQ, hcr Q P hQ hP⟩
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  exact GlobalTheory.PlaceDatum.idemAt_mul (hes i (hP hi)) (hes j (hQ hj)) (hx i (hP hi) j (hQ hj)) (hx j (hQ hj) i (hP hi))
    fun h => Finset.disjoint_left.1 hd hi (h ▸ hj)

theorem exists_model_of_fix {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {e : AE D} (he : GlobalTheory.PlaceModelSum.IsOrthSum e)
    (hec : e * cA D e = 0) {g : WO S T → ℂ}
    (hf : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, heisO ψ S T u g = g)
    (hf' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), heisO ψ S T u g = g) :
    ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 g Tm := by
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  refine exists_placeModel ψ hec _ (fun u hu y hy => (hdual u (he.infPart_half hu.2)).1 hu.1 y hy.1)
    (he.mem_of_dual hdual) (fun y hy h => ?_) (fun k hk => ?_) one_ne_zero g hf hf'
  · refine he.conj.mem_of_dual hdual y hy fun u hu => ?_
    rw [GlobalTheory.DualPairCheck.cA_cA] at hu
    rw [symplO_skew, AddChar.map_neg_eq_inv, h u hu, inv_one]
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, GlobalTheory.PlaceModelSum.idem_smul_half he.idem hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]


open Classical in
theorem omegaFlat_congr {a b : ℕ} (Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    {y y' : ∀ PP : Pl D.host.E, Matrix (Fin a) (Fin b) (kP PP)} (h : ∀ PP ∈ Q, y PP = y' PP) :
    GlobalTheory.ConjTwist.omegaFlat Q r ξ y = GlobalTheory.ConjTwist.omegaFlat Q r ξ y' := by
  have hiff : (∀ PP ∈ Q, IsUnit (topL r (y PP)).det) ↔ ∀ PP ∈ Q, IsUnit (topL r (y' PP)).det :=
    forall_congr' fun PP => forall_congr' fun hPP => by rw [h PP hPP]
  unfold GlobalTheory.ConjTwist.omegaFlat
  by_cases h1 : ∀ PP ∈ Q, IsUnit (topL r (y PP)).det
  · rw [dite_eq_left h1, dite_eq_left (hiff.1 h1)]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have e : (h1 PP.1 PP.2).unit = (hiff.1 h1 PP.1 PP.2).unit :=
      Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, h PP.1 PP.2])
    rw [e]
  · rw [dite_eq_right h1, dite_eq_right fun h2 => h1 (hiff.2 h2)]

theorem off_of_half {e c : AE D} (hc : e * c = 0) (hc' : cA D e * c = 0) {S T : HSp D} {u : WO S T} (hu : IsHalf c u) :
    ∀ a b, e * u a b = 0 ∧ cA D e * u a b = 0 := fun a b => by
  rw [← hu a b, ← mul_assoc, ← mul_assoc, hc, hc', zero_mul]
  exact ⟨rfl, rfl⟩

theorem flatVec_existsUnique : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), (∃ f, IsFlatVec R i t f) ∧ ∀ f f', IsFlatVec R i t f → IsFlatVec R i t f' → f = f' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR _ i t
  refine ⟨?_, ?_⟩
  · obtain ⟨hvac, e, he, -⟩ := hR.thP.vP i t
    have hψ := hvac.1
    have sV : IsSelfDualC (Vc D i) (R.ΛV i) :=
      GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βV i))
    have sW : IsSelfDualC (Wc D i) (R.ΛW i) :=
      GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βW i))
    have fullV := GlobalTheory.PlaceVec.selfDual_isFullLattice (Vc D i) (R.ΛV i) sV
    have fullW := GlobalTheory.PlaceVec.selfDual_isFullLattice (Wc D i) (R.ΛW i) sW
    obtain ⟨eg, eQ, hg, hq, h1, h2, h3⟩ := idemSum_split he (Formalism.IndefR.Fin.disjoint_Pg_Q R.toLevCh hR.lev t)
    have hinfg := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)
    obtain ⟨fg, hfg⟩ := GlobalTheory.PlaceVec.exists_isThetaAt hψ sV sW (a := cA D eg)
      (by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self hg]) hinfg
      (GlobalTheory.PlaceModelSum.placeModelExistsSum D R.ψ hψ _ _ _ _ sV sW _ eg hg _ hvac.2.theta hvac.2.lat).2
      (GlobalTheory.PlaceVec.isSBHalf_of_red fullV fullW hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
        (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _) R.Pg
        (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h)
    have hoQ := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hq
    have fix : ∀ u, (∀ a b, cA D eg * u a b = 0 ∧ eg * u a b = 0) →
        heisO R.ψ (Vc D i) (Wc D i) u (R.vacP i) = R.vacP i → heisO R.ψ (Vc D i) (Wc D i) u fg = fg :=
      fun u hu h0 => GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ _ _ (cA D eg) _ 1 _ _ fg hfg u
        (fun a b => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hu a b) h0
    have hPM := exists_model_of_fix hψ sV sW hoQ hq.2
      (fun u hu => fix u (fun a b => (off_of_half h1 (by rw [mul_comm, h3])
          ((isHalf_iff _ _).2 hu.2) a b).symm)
        (hoQ.heisO_eq (by rw [mul_comm, hq.2]) hvac.2.lat u hu))
      (fun u hu => fix u (fun a b => (off_of_half h2
          (by rw [← RingHom.map_mul, h1, map_zero]) ((isHalf_iff _ _).2 hu.2) a b).symm)
        (hoQ.conj.heisO_eq (by rw [GlobalTheory.DualPairCheck.cA_cA, hq.2]) hvac.2.lat u hu))
    have hinfQ := GlobalTheory.PlaceDatum.infPart_idemSum hq
    obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO fullV fullW (R.βV i) (R.βW i)
    obtain ⟨f, hf⟩ := GlobalTheory.PlaceDatum.exists_isThetaAt hψ sV sW (GlobalTheory.PlaceDatum.idemSum_mul_self hq) hinfQ hPM
      (GlobalTheory.PlaceDatum.isSBHalf_of_red eQ _ (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (GlobalTheory.PlaceDatum.frMapO_add _ _)
        (GlobalTheory.PlaceDatum.exists_den_frMapO sV.1.fg sW.1.fg _ _)
        ⟨K, hK, fun x hx => hC x (GlobalTheory.PlaceDatum.infPart_of_half hinfQ hx)⟩ (R.Q t)
        (fun y => GlobalTheory.ConjTwist.omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) y) fun y y' h => omegaFlat_congr _ _ _ h)
    exact ⟨f, eg, eQ, fg, hg, hq, hfg, hf⟩
  · rintro f f' ⟨eg, eQ, fg, hg, hq, hfg, hf⟩ ⟨eg', eQ', fg', hg', hq', hfg', hf'⟩
    obtain rfl := GlobalTheory.BaseKernelUniq.idemSum_unique (Vc D i) hg hg'
    obtain rfl := GlobalTheory.BaseKernelUniq.idemSum_unique (Vc D i) hq hq'
    obtain rfl : fg = fg' := by
      obtain ⟨⟨Tm, hTm⟩, hall⟩ := hfg
      rw [hall Tm hTm, hfg'.2 Tm hTm]
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
    rw [hall Tm hTm, hf'.2 Tm hTm]

end GlobalTheory.FlatVecExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockPolynomialSubstitutionCommuteTargetGlActionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialSubstitution_commute_targetGlAction : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (g : GLR D n) (τ : D.what₂.Tau) (Y : Matrix (Fin m) (Fin m) ℂ) (P : PolF D m n), fockSubst p g (fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y P) = fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) Y (fockSubst p g P) := by
  first | exact @GlobalTheory.FockSubstComm.fockSubst_fockT | exact GlobalTheory.FockSubstComm.fockSubst_fockT | (intros; apply GlobalTheory.FockSubstComm.fockSubst_fockT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockSubstitutionPreservesHarmonicLetterPolynomiaStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSubstitution_preserves_harmonicLetterPolynomials : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (m n : ℕ) (lt : LtN Dw n ≃ FVar D m n),
    m = Dw.p + Dw.q → (∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) → IsLetters Dw lt →
    ∀ (u : GlobalTheory.ExportSeries.GLR D n) (wa : (D.host.E →+* ℂ) × ℕ → ℕ) (Q : MvPolynomial (LtN Dw n) ℂ),
      Q ∈ HHa Dw.mult n ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)) →
      MvPolynomial.rename lt.symm (GlobalTheory.ExportSeries.fockSubst (m := m) (fun _ => Dw.p) u (MvPolynomial.rename lt Q)) ∈
        HHa Dw.mult n ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)) := by
  first | exact @GlobalTheory.FockSubstHarm.rename_fockSubst_mem_HHa | exact GlobalTheory.FockSubstHarm.rename_fockSubst_mem_HHa | (intros; apply GlobalTheory.FockSubstHarm.rename_fockSubst_mem_HHa <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockTargetMatrixUnitCompactTotalDegreeLeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockTargetMatrixUnit_compact_totalDegree_le : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (τ : D.what₂.Tau) (a b : Fin m), GlobalTheory.LowestKType.Cpt w τ a b → ∀ (d : ℕ) (P : PolF D m n), P.totalDegree ≤ d → (GlobalTheory.LowestKType.kop w τ a b P).totalDegree ≤ d := by
  first | exact @GlobalTheory.LowestKType.kop_totalDegree_le | exact GlobalTheory.LowestKType.kop_totalDegree_le | (intros; apply GlobalTheory.LowestKType.kop_totalDegree_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodBaseDataWeightEqLiftCoeffModuleWeight
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseLiftWeight

theorem c_eq {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)}
    (hL : L.Is μ0) (hB : B.Good) (hmu : B.mu0 = L.mu0 ((j : ℕ) + 1)) (τ : D.what₂.Tau) :
    B.w.c τ = GlobalTheory.ConjTwist.liftC D j τ := by
  have h1 := hB.inf τ
  rw [hmu] at h1
  have h2 := GlobalTheory.Mem.HeckeExp.hasInfExp_unique h1 (GlobalTheory.ConjRefChar.reference_lift_character_exponent_neg_base hL j τ)
  have hs := hB.sig τ
  have hp : B.w.p τ = ((Wc D j).sig (tauE D τ)).1 := congrArg Prod.fst hs
  have hq : B.w.q τ = ((Wc D j).sig (tauE D τ)).2 := congrArg Prod.snd hs
  have h3 := GlobalTheory.ConjTwist.liftC_cast D j τ
  rw [hp, hq] at h2
  have h4 : (B.w.c τ : ℚ) = (GlobalTheory.ConjTwist.liftC D j τ : ℚ) := by
    rw [h3]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.pS, GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.qS] at *
    linarith
  exact_mod_cast h4

theorem lam_eq : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), L.Is μ0 → B.Good → B.mu0 = L.mu0 ((j : ℕ) + 1) → (∀ τ, B.w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ) → (∀ τ, B.w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ) → B.w.lam = FWT.lamV D j := by
  intro D T0 L μ0 j B hL hB hmu hap ham
  funext τ
  have hs := hB.sig τ
  have hp : B.w.p τ = ((Wc D j).sig (tauE D τ)).1 := congrArg Prod.fst hs
  have hq : B.w.q τ = ((Wc D j).sig (tauE D τ)).2 := congrArg Prod.snd hs
  have hc := c_eq hL hB hmu τ
  have e1 := hB.wt.lam_eq τ
  have e2 := (GlobalTheory.ConjTwist.liftWeight_good D j).lam_eq τ
  rw [hp, hq, hap τ, ham τ, hc] at e1
  have key : (B.w.lam τ).w = (FWT.lamV D j τ).w := funext fun a => (e1 a).trans (e2 a).symm
  generalize B.w.lam τ = x at key
  generalize FWT.lamV D j τ = y at key
  cases x
  cases y
  cases key
  rfl

end GlobalTheory.BaseLiftWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasDerivAtFockVectorsTargetLieRealPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

namespace GlobalTheory.FockLieW

theorem hasDerivAt_fockVector : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (τ : D.what₂.Tau), ∃ κ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ → ℂ, ∀ Y ∈ lieAt (Wc D i) τ, ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (z : WO (Vc D i) (Wc D i)), HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin (Vc D i).rank => true) ((R.MW i (sg0 D A)).ε τ) ((R.MW i (sg0 D A)).fr τ * Y * ((R.MW i (sg0 D A)).fr τ)⁻¹) P + κ Y • P) z) 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t τ
  have hC := hG.core
  have hB := hC.models.BV i
  set AV := GlobalTheory.FockDerivP.frONB (R.BV i) hB with hAV
  set BW := GlobalTheory.ChainFr.Fr.ofModel (R.MW i (sg0 D A)) with hBW
  have hcA := GlobalTheory.FockDerivP.frONB_cart (R.BV i) hB
  have hoA := GlobalTheory.FockDerivP.frONB_onb (R.BV i) hB
  obtain ⟨hf, hv, -⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  have hvac : GlobalTheory.ChainFr.IsVacF R.ψ R.θ AV BW (R.vP i t) := by
    refine ⟨hf, fun ρ => ?_⟩
    rw [hcA]
    exact hv ρ
  have hI := GlobalTheory.PairInfTypes.infTypesAt D T R.toLevCh A.μ0 hC.lev i t τ
  have hAll := GlobalTheory.LieScalar.lieFockAll D (Vc D i) (Wc D i) AV BW R.θ R.ψ _ _ (R.ωP i t) (R.vP i t) τ _ _
    hC.models.inf (hC.thP.ωP i t) hI.chiV hI.chiW hvac
  have hpt : GlobalTheory.ChainFr.ptF R.ψ R.θ AV BW (R.vP i t) = R.ptP i t := by
    unfold GlobalTheory.ChainFr.ptF RealDat.ptP
    rw [hcA, hoA]
    rfl
  refine ⟨fun Y => ((-eS D i τ : ℚ) : ℂ) * Y.trace, fun Y hY P z => ?_⟩
  have h := hAll.2 Y hY P z
  rw [hpt] at h
  exact h

end GlobalTheory.FockLieW

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharInfinityEqCoeffMulHalfNormPow
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem phase_zpow_eq (z : ℂ) (hz : z ≠ 0) (b : ℤ) (r : ℕ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * b + (r : ℤ)) =
      z ^ (b + (r : ℤ)) * ((starRingEnd ℂ z) ^ b)⁻¹ * (((‖z‖ : ℝ) : ℂ) ^ r)⁻¹ := by
  have hN : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
  have hc : starRingEnd ℂ z ≠ 0 := (map_ne_zero _).2 hz
  have hsq : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * starRingEnd ℂ z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have h2b : ((‖z‖ : ℝ) : ℂ) ^ (2 * b) = z ^ b * (starRingEnd ℂ z) ^ b := by
    rw [_root_.zpow_mul, show ((‖z‖ : ℝ) : ℂ) ^ (2 : ℤ) = ((‖z‖ : ℝ) : ℂ) ^ (2 : ℕ) from zpow_ofNat _ 2, hsq, mul_zpow]
  have hzn : z ^ (2 * b + (r : ℤ)) = z ^ b * z ^ (b + (r : ℤ)) := by
    rw [← zpow_add₀ hz]; congr 1; ring
  rw [div_zpow, zpow_add₀ hN, h2b, hzn, zpow_natCast]
  have h1 : z ^ b ≠ 0 := zpow_ne_zero _ hz
  have h2 : (starRingEnd ℂ z) ^ b ≠ 0 := zpow_ne_zero _ hc
  have h3 : ((‖z‖ : ℝ) : ℂ) ^ r ≠ 0 := pow_ne_zero _ hN
  field_simp

theorem prod_norm_inv_pow {ι : Type} [Fintype ι] (z : ι → ℂ) (r : ℕ) :
    ∏ i, (((‖z i‖ : ℝ) : ℂ) ^ r)⁻¹ = (((∏ i, ‖z i‖ ^ 2) ^ (-(r : ℝ) / 2) : ℝ) : ℂ) := by
  rw [← Real.finsetProd_rpow _ _ (fun i _ => by positivity) _]
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_natCast_mul (norm_nonneg _)]
  rw [show ((2 : ℕ) : ℝ) * (-(r : ℝ) / 2) = -(r : ℝ) by push_cast; ring, Real.rpow_neg (norm_nonneg _),
    Real.rpow_natCast]
  push_cast
  rfl

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem conjugate_tauE_ne_tauE (D : D7) (τ τ' : D.what₂.Tau) :
    NumberField.ComplexEmbedding.conjugate (tauE D τ) ≠ tauE D τ' := by
  intro h
  have e := DFunLike.congr_fun h D.host.sqrtMinusD
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, Formalism.L2.Theta.tauE_sqrtMinusD,
    Formalism.L2.Theta.tauE_sqrtMinusD] at e
  have e2 := congrArg Complex.im e
  simp at e2
  have : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  linarith

theorem mk_tauE_bij (D : D7) : Function.Bijective (fun τ : D.what₂.Tau => InfinitePlace.mk (tauE D τ)) := by
  refine ⟨fun τ τ' h => ?_, fun w => GlobalTheory.CharInfPlace.exists_mk_tauE D w⟩
  rcases InfinitePlace.mk_eq_iff.1 h with e | e
  · exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 e))
  · exact absurd e (conjugate_tauE_ne_tauE D τ τ')

theorem mk_tauE_complex (D : D7) (τ : D.what₂.Tau) : ¬ (InfinitePlace.mk (tauE D τ)).IsReal := by
  rw [InfinitePlace.isReal_mk_iff, NumberField.ComplexEmbedding.isReal_iff]
  exact conjugate_tauE_ne_tauE D τ τ

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem inf_eq_mul_normPow : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (χ : Formalism.L2.Host.HChar D.host.E), ChrEq χW χ → ∀ (k : Type) [Field k] (σ : k →+* ℂ), ConjIn D σ → ∀ a : D.host.Eˣ, ∃ y : k, ((χ.inf a : ℂˣ) : ℂ) = σ y * ((|((Algebra.norm ℚ (a : D.host.E) : ℚ) : ℝ)| ^ (-(W.rank : ℝ) / 2) : ℝ) : ℂ) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hvp χ hc k _ σ hσ a
  choose b hb using hvp.1.expW
  obtain ⟨n, hn, hinf⟩ := GlobalTheory.HeckeInfExp.hasInfQ_of_hasInfExp D χW χ _ hc hb
  have hn' : ∀ τ, n τ = 2 * b τ + (W.rank : ℤ) := fun τ => by
    have : (n τ : ℚ) = ((2 * b τ + (W.rank : ℤ) : ℤ) : ℚ) := by rw [hn]; push_cast; ring
    exact_mod_cast this
  have hnorm : ∏ τ, ‖tauE D τ (a : D.host.E)‖ ^ 2 = |((Algebra.norm ℚ (a : D.host.E) : ℚ) : ℝ)| := by
    rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm]
    refine (Fintype.prod_bijective _ (mk_tauE_bij D) _ _ (fun τ => ?_))
    rw [NumberField.InfinitePlace.mult, if_neg (mk_tauE_complex D τ)]
    rfl
  have hA : ∏ τ, (tauE D τ (a : D.host.E) ^ ((b τ : ℤ) + (W.rank : ℤ)) *
      ((starRingEnd ℂ (tauE D τ (a : D.host.E))) ^ (b τ : ℤ))⁻¹) ∈ σ.fieldRange := by
    refine prod_mem fun τ _ => mul_mem (zpow_mem ?_ _) (inv_mem (zpow_mem ?_ _))
    · obtain ⟨y, hy⟩ := hσ (tauE D τ) a
      exact ⟨y, hy⟩
    · obtain ⟨y, hy⟩ := hσ ((starRingEnd ℂ).comp (tauE D τ)) a
      exact ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hA
  refine ⟨y, ?_⟩
  rw [hinf a, hy, ← hnorm, ← prod_norm_inv_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hn' τ]
  exact phase_zpow_eq _ ((map_ne_zero _).2 a.ne_zero) _ W.rank

end GlobalTheory.LevelSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointHighestWeightHarmonicOfFockLowestKTypeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointHighestWeightHarmonic_of_fock_lowestKType : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (lam : D.what₂.Tau → Fin n → ℂ) (P : PolF D m n), GlobalTheory.LowestKType.IsHarm w P → GlobalTheory.LowestKType.IsNHw w lam P → GlobalTheory.LowestKType.IsKHw w P → ∀ τ : D.what₂.Tau, ∃ (α : Fin (min (w.p τ) m) → ℂ) (β : Fin (m - w.p τ) → ℂ), GlobalTheory.CompactHarm.JointTop (Prod.mk τ ∘ GlobalTheory.HarmLine.zR m n (w.p τ)) (Prod.mk τ ∘ GlobalTheory.HarmLine.yR m n (w.p τ)) (fun a => lam τ a - (m : ℂ) / 2 + ((m - w.p τ : ℕ) : ℂ)) α β P := by
  first | exact @GlobalTheory.JointDict.jointTop_of_lowestKType | exact GlobalTheory.JointDict.jointTop_of_lowestKType | (intros; apply GlobalTheory.JointDict.jointTop_of_lowestKType <;> assumption)
end

