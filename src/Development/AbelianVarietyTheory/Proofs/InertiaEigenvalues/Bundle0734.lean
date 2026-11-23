module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
public import GroundTheory.AutomorphicForms.ReductionMeasure
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0533
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0703
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroOfDiag
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0672
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsStatementHolds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0512
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimensionSaturationUnramified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0726
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0642
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0509
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRefinedFlagChartIntegralPointsInOpen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddHaarMapMulFiniteIdeleOfUniformizerPowers
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
open scoped Pointwise

namespace GlobalTheory.AdeleScale

variable {E : Type} [Field E] [NumberField E]

theorem qV_ne_zero (v : HeightOneSpectrum (𝓞 E)) : (qV E v : ℝ) ≠ 0 := by
  rw [qV, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

theorem finId_adl_snd (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (v : HeightOneSpectrum (𝓞 E)) :
    ((finId E (GlobalTheory.CellDec.adl ϖ m) : AdeleRing (𝓞 E) E)).2 v = ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by
  change ((1 : Af E) - 1 + ((GlobalTheory.CellDec.adl ϖ m : (Af E)ˣ) : Af E)) v = _
  rw [sub_self, zero_add]
  rfl

theorem finId_fst (a : (Af E)ˣ) : ((finId E a : AdeleRing (𝓞 E) E)).1 = 1 := by
  change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
  rw [sub_zero, add_zero]

theorem ideleModule_finId_adl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (s : Finset (HeightOneSpectrum (𝓞 E))) (hs : ∀ v, v ∉ s → m v = 0) :
    (GroundTheory.Global.IdeleGroup.ideleModule E (finId E (GlobalTheory.CellDec.adl ϖ m)) : ℝ) =
      ∏ v ∈ s, ((qV E v : ℝ) ^ m v)⁻¹ := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h1 : ∀ w : InfinitePlace E,
      ‖((finId E (GlobalTheory.CellDec.adl ϖ m) : AdeleRing (𝓞 E) E)).1 w‖ ^ w.mult = 1 := fun w => by
    rw [finId_fst]
    change ‖(1 : w.Completion)‖ ^ w.mult = 1
    rw [norm_one, one_pow]
  have h2 : ∀ v : HeightOneSpectrum (𝓞 E),
      ‖((finId E (GlobalTheory.CellDec.adl ϖ m) : AdeleRing (𝓞 E) E)).2 v‖ = ((qV E v : ℝ) ^ m v)⁻¹ := fun v => by
    have hu : Valued.v ((ϖ v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := hϖ v
    rw [finId_adl_snd, Units.val_zpow_eq_zpow_val, norm_zpow, GroundTheory.Global.norm_uniformizer hu, _root_.inv_zpow]
    rfl
  rw [Finset.prod_eq_one fun w _ => h1 w, one_mul]
  simp_rw [h2]
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
  by_contra hvs
  exact hv (by show ((qV E v : ℝ) ^ m v)⁻¹ = 1; rw [hs v hvs, zpow_zero, inv_one])

end GlobalTheory.AdeleScale


open GlobalTheory.AdeleScale in
theorem GlobalTheory.AdeleScale.map_mul_finId_adl : ∀ (E : Type) [Field E] [NumberField E] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (s : Finset (HeightOneSpectrum (𝓞 E))), (∀ v, v ∉ s → m v = 0) →
    ∀ [MeasurableSpace (AdeleRing (𝓞 E) E)] [BorelSpace (AdeleRing (𝓞 E) E)] (μR : Measure (AdeleRing (𝓞 E) E)) [μR.IsAddHaarMeasure],
    Measure.map (fun x : AdeleRing (𝓞 E) E => ((finId E (GlobalTheory.CellDec.adl ϖ m) : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E) * x) μR =
      ENNReal.ofReal (∏ v ∈ s, (qV E v : ℝ) ^ m v) • μR := by
  intro E _ _ ϖ hϖ m s hs _ _ μR _
  set a : (AdeleRing (𝓞 E) E)ˣ := finId E (GlobalTheory.CellDec.adl ϖ m) with ha
  have hm : Measurable fun x : AdeleRing (𝓞 E) E => (a : AdeleRing (𝓞 E) E) * x :=
    (continuous_const.mul continuous_id).measurable
  have hchar : distribHaarChar (AdeleRing (𝓞 E) E) a • μR.map (fun x => (a : AdeleRing (𝓞 E) E) * x) = μR := by
    ext S hS
    rw [Measure.smul_apply, Measure.map_apply hm hS]
    have h1 := distribHaarChar_mul μR a ((fun x : AdeleRing (𝓞 E) E => (a : AdeleRing (𝓞 E) E) * x) ⁻¹' S)
    have e : a • ((fun x : AdeleRing (𝓞 E) E => (a : AdeleRing (𝓞 E) E) * x) ⁻¹' S) = S := by
      ext y
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp [Units.smul_def]
    rw [e] at h1
    rw [ENNReal.smul_def, smul_eq_mul]
    exact h1
  have hmod : (distribHaarChar (AdeleRing (𝓞 E) E) a : ℝ) = ∏ v ∈ s, ((qV E v : ℝ) ^ m v)⁻¹ := by
    rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing]
    exact ideleModule_finId_adl ϖ hϖ m s hs
  have hone : ENNReal.ofReal (∏ v ∈ s, (qV E v : ℝ) ^ m v) * (distribHaarChar (AdeleRing (𝓞 E) E) a : ℝ≥0∞) = 1 := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ =>
      zpow_nonneg (Nat.cast_nonneg _) _), hmod, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one fun v _ => mul_inv_cancel₀ (zpow_ne_zero _ (qV_ne_zero v)), ENNReal.ofReal_one]
  conv_rhs => rw [← hchar]
  rw [ENNReal.smul_def (distribHaarChar (AdeleRing (𝓞 E) E) a), smul_smul, hone, one_smul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2PairOfAdmissible
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.PointRepAboveL

theorem place_unique {D : D7} {i : D.nd.Loc} {τ : D.host.E →+* Qbar (D.nd.l i)} {w w' : PlE D.host}
    (h : InducesW D.nd i τ w) (h' : InducesW D.nd i τ w') : w' = w := by
  apply HeightOneSpectrum.ext
  ext x
  rw [← h x, h' x]

end GlobalTheory.PointRepAboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoTopOfLocalTateDualityEulerChar
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TopClosing

theorem blochKatoTop_of_localTateDuality_eulerChar_alt : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), tableLineDegreeTwo.aux₃ D HW F := by
  intro _ hdual heul D HW F Cm
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, -, hE⟩ :
      Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm := _root_.GlobalTheory.NL.wach_used_clauses D HW F Cm
  obtain ⟨a23, a24⟩ := tableLineDegreeTwo.ainf_clauses_of_theorem D HW F hE
  have hA : Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F := GlobalTheory.HerrFull.herr_part_a_every_record D HW F
  have hFN : Formalism.MainNotions.HerrComplexNaturality.FN D HW F := GlobalTheory.Decompl.fontaine_and_decompletion D HW F
  have a16 : tableLineDegreeTwo.adm16 D HW F :=
    Formalism.MainNotions.InvariantsGenerators.herr_lattice_of_fon D HW F ⟨hA, _root_.GlobalTheory.invariants_of_field_of_norms D HW F hFN, _root_.GlobalTheory.fontaine_litFont_assembled D HW F⟩
  have a17 : tableLineDegreeTwo.adm17 D HW F :=
    (Formalism.MainNotions.InvariantsGenerators.herr_lattice_rest_iff D HW F).2
      ⟨GlobalTheory.EtaleSub.exists_lattice_of_pow_mem D HW F, GlobalTheory.ExtDict.extension_rule D HW F⟩
  have a21 : tableLineDegreeTwo.adm21 D HW F := GlobalTheory.SenMult.stmtSen D HW F Cm ⟨a2, a4, a5, a9, a11⟩
  exact GlobalTheory.TopBridge.twistedLatticeCohomology_theoremTOP D HW F Cm
    ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, ⟨hdual, heul⟩,
      GlobalTheory.FiltrationJumpMultiplicity.blochKato_dimension_saturation_unramified D, _root_.GlobalTheory.CrysCharJumps.adm20_of_fonOf D HW F, a21, GlobalTheory.CrysFormalism.crysLit_all D, a23, a24⟩

end GlobalTheory.TopClosing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CosetSumTransferAlongSurjectionPreimageStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetSum_transfer_along_surjection_preimage : ∀ {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (U0 : Subgroup G) (K : Subgroup H) (T : Subgroup G) (ψ : T →* H), Function.Surjective ψ → (∀ t : T, ψ t ∈ K ↔ (t : G) ∈ U0) → ∀ (a φ' : H → ℂ) (β : G → V) (lam : V →ₗ[ℂ] ℂ), (∀ x, ∀ k ∈ K, a (x * k) = a x) → (Function.support fun d : H ⧸ K => a d.out).Finite → (∀ x, ∀ u ∈ U0, β (x * u) = β x) → (∀ t : T, φ' (ψ t) = lam (β t)) → ∑ᶠ d : H ⧸ K, a d.out * φ' d.out = lam (∑ᶠ c : G ⧸ U0, if hc : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T then a (ψ ⟨hc.choose, hc.choose_spec.2⟩) • β hc.choose else 0) := by
  first | exact @GlobalTheory.cosetSum_transfer_surj | exact GlobalTheory.cosetSum_transfer_surj | (intros; apply GlobalTheory.cosetSum_transfer_surj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryFundamentalDomainVolumePosFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.DefVol

theorem fdV_measure_pos_lt_top : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F →
    ∀ (i : Fin D.R.m) (t : T), 0 < R.νV i t (R.fdV i t) ∧ R.νV i t (R.fdV i t) < ⊤ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F h i t
  have hm := h.models.νV i t
  have hH : (R.νV i t).IsHaarMeasure := hm.1.1
  have hfd : IsFundamentalDomain (GQ (Vc D i)) (R.fdV i t) (R.νV i t) := hm.2
  obtain ⟨hs, hp⟩ := h.posDef i
  have hc : GlobalTheory.Unf.CoCpt (Vc D i) := GlobalTheory.SeeSaw.Inh.coCpt_of_isDefinite hs (fun τ => Or.inl (hp τ))
  refine ⟨?_, GlobalTheory.Unf.vol_fund_lt_top hc ⟨_, _, hH, hfd⟩⟩
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ (Vc D i))
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ (Vc D i)) (R.νV i t)
  rw [pos_iff_ne_zero]
  intro h0
  have hu := hfd.measure_zero_of_invariant (t := Set.univ) (fun g => Set.smul_set_univ) (by simpa using h0)
  exact (Measure.measure_univ_ne_zero.2 (NeZero.ne (R.νV i t))) hu

end GlobalTheory.DefVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusGoodSplitPlacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_frobenius_goodSplitPlaces : ∀ (D : D7) (l : ℕ) (Q : Finset (PlE D.host)), l.Prime → GlobalTheory.RowTie.ChebSplit D.nd →
    Dense {σ : G D.host.E D.nd.Om | ∃ v : PlE D.host,
      (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E l ∧ v ∉ placesS D l ∧ v ∉ Q) ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ} := by
  first | exact @GlobalTheory.FrobDense.frob_dense_goodSplit | exact GlobalTheory.FrobDense.frob_dense_goodSplit | (intros; apply GlobalTheory.FrobDense.frob_dense_goodSplit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdeleUnitCongrOne
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitRootCong

open Formalism.MainNotions.StandardLattice

section Gen

variable {F : Type} [Field F] [NumberField F]

def mkAf (g : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hg : ∀ v, g v ∈ v.adicCompletionIntegers F) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F :=
  ⟨g, Filter.Eventually.of_forall hg⟩

theorem evalV_mkAf (g : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hg : ∀ v, g v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (mkAf g hg) = g v := rfl

theorem mkAf_mem (g : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hg : ∀ v, g v ∈ v.adicCompletionIntegers F) : mkAf g hg ∈ intAf F := fun v => by
  rw [evalV_mkAf]; exact hg v

theorem val_eq_one_of_mul (v : HeightOneSpectrum (𝓞 F)) {a b : v.adicCompletion F}
    (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1) (hab : Valued.v (a * b) = 1) : Valued.v a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : _) = Valued.v a * Valued.v b := by rw [← map_mul, hab]
    _ ≤ Valued.v a * 1 := mul_le_mul_right hb (Valued.v a)
    _ = Valued.v a := mul_one _

theorem val_le_one {v : HeightOneSpectrum (𝓞 F)} {a : v.adicCompletion F}
    (ha : a ∈ v.adicCompletionIntegers F) : Valued.v a ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 ha

theorem mem_of_val {v : HeightOneSpectrum (𝓞 F)} {a : v.adicCompletion F}
    (ha : Valued.v a ≤ 1) : a ∈ v.adicCompletionIntegers F :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 ha

theorem val_natCast_le (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) : Valued.v (k : v.adicCompletion F) ≤ 1 :=
  val_le_one (natCast_mem (HeightOneSpectrum.adicCompletionIntegers F v) k)

theorem val_unit_of_rel (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) {t q r : v.adicCompletion F}
    (hm : Valued.v (((2 * k + 1 : ℕ) : v.adicCompletion F)) < 1)
    (ht : Valued.v t ≤ 1) (hq : Valued.v q ≤ 1) (hr : Valued.v r ≤ 1)
    (h4 : (4 : v.adicCompletion F) = t * q + ((2 * k + 1 : ℕ) : v.adicCompletion F) * r) :
    Valued.v (-(k : v.adicCompletion F) * t) = 1 := by
  set M : v.adicCompletion F := ((2 * k + 1 : ℕ) : v.adicCompletion F) with hM
  have hk : Valued.v (k : v.adicCompletion F) ≤ 1 := val_natCast_le v k
  have h2k : Valued.v (2 * (k : v.adicCompletion F)) = 1 := by
    have e : 2 * (k : v.adicCompletion F) = -1 + M := by rw [hM]; push_cast; ring
    rw [e, Valuation.map_add_eq_of_lt_left Valued.v (by rw [Valuation.map_neg, map_one]; exact hm),
      Valuation.map_neg, map_one]
  have hsq : (2 * (k : v.adicCompletion F)) ^ 2 = (-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q) +
      M * ((k : v.adicCompletion F) ^ 2 * r) := by
    linear_combination (k : v.adicCompletion F) ^ 2 * h4
  have hsmall : Valued.v (M * ((k : v.adicCompletion F) ^ 2 * r)) < 1 := by
    rw [map_mul]
    calc Valued.v M * Valued.v ((k : v.adicCompletion F) ^ 2 * r) ≤ Valued.v M * 1 := by
          refine mul_le_mul_right ?_ _
          rw [map_mul, map_pow]
          calc Valued.v (k : v.adicCompletion F) ^ 2 * Valued.v r ≤ 1 * 1 := by
                gcongr
                exact pow_le_one₀ zero_le' hk
            _ = 1 := one_mul 1
      _ < 1 := by rw [mul_one]; exact hm
  have hprod : Valued.v ((-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q)) = 1 := by
    have e : (-(k : v.adicCompletion F) * t) * (-(k : v.adicCompletion F) * q) =
        (2 * (k : v.adicCompletion F)) ^ 2 + -(M * ((k : v.adicCompletion F) ^ 2 * r)) := by
      rw [hsq]; ring
    have hv1 : Valued.v ((2 * (k : v.adicCompletion F)) ^ 2) = 1 := by rw [map_pow, h2k, one_pow]
    rw [e, Valuation.map_add_eq_of_lt_left Valued.v (by rw [Valuation.map_neg, hv1]; exact hsmall), hv1]
  refine val_eq_one_of_mul v ?_ ?_ hprod
  · rw [map_mul, Valuation.map_neg]
    calc Valued.v (k : v.adicCompletion F) * Valued.v t ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  · rw [map_mul, Valuation.map_neg]
    calc Valued.v (k : v.adicCompletion F) * Valued.v q ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1

end Gen

end GlobalTheory.UnitRootCong

namespace GlobalTheory.UnitRootCong

open Formalism.MainNotions.StandardLattice


set_option maxHeartbeats 2000000 in
theorem exists_adele_unit_congr_one : ∀ (D : D7) (m : ℕ), Odd m → ∀ (z y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ), (y : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D → ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D → (y : Af D.host.F ⊗[D.host.F] D.host.E) = z * sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) → (∃ w ∈ intAE D, (z : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = m • w) → ∃ (b : (Af D.host.F)ˣ) (y' : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ), (y' : Af D.host.F ⊗[D.host.F] D.host.E) = (y : Af D.host.F ⊗[D.host.F] D.host.E) * ((b : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) ∧ (y' : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧ ((y'⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧ ∃ w ∈ intAE D, (y' : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = m • w := by
  classical
  intro D m hm z y hyI hyiI hyz hzw
  obtain ⟨w, hwI, hw⟩ := hzw
  obtain ⟨k, rfl⟩ := hm
  have hE := GlobalTheory.AdelicU.isCMExt_host D
  set M : ℕ := 2 * k + 1 with hMdef
  set yv : Af D.host.F ⊗[D.host.F] D.host.E := (y : Af D.host.F ⊗[D.host.F] D.host.E) with hyv
  set yi : Af D.host.F ⊗[D.host.F] D.host.E := ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) with hyi
  have hyy : yv * yi = 1 := y.mul_inv
  set s := sigR (Af D.host.F) D.sp.cm.sig yv with hs
  have hsI : s ∈ intAE D := GlobalTheory.PlaceIdem.sig_mem D hyI
  set T := Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) with hT
  set ι := algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) with hι
  have ht : yv + s = ι (T yv) := GlobalTheory.GaussMean.OneVec.add_sigR _ hE yv
  have hw' : (z : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = (M : Af D.host.F ⊗[D.host.F] D.host.E) * w := by
    rw [hw, nsmul_eq_mul]
  have E3 : 2 * yv = ι (T yv) + (M : Af D.host.F ⊗[D.host.F] D.host.E) * (w * s) := by
    linear_combination ht + hyz + s * hw'

  have hιI : ∀ a ∈ intAf D.host.F, ι a ∈ intAE D := fun a ha =>
    AddSubgroup.subset_closure ⟨a, ha, 1, by simp [hι, Algebra.TensorProduct.algebraMap_apply]⟩
  have hmulI : ∀ {a b}, a ∈ intAE D → b ∈ intAE D → a * b ∈ intAE D := fun ha hb =>
    GlobalTheory.HostAdeleIso.intAE_mul_mem D ha hb
  have hoI : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := by
    simpa using hιI 1 GlobalTheory.SplitHeckeLabel.one_mem_intAf
  have hnI : ∀ n : ℕ, (n : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := fun n => by
    rw [← nsmul_one]; exact nsmul_mem hoI n
  have hrI : w * s * yi ∈ intAE D := hmulI (hmulI hwI hsI) hyiI

  have hTl : ∀ (a : Af D.host.F) x, T (ι a * x) = a * T x := fun a x => by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hT2 : T (ι 2) = 4 := by
    have h1 := GlobalTheory.GaussMean.OneVec.half_trace (Af D.host.F) hE (2 : Af D.host.F)
    have h2 := GlobalTheory.GaussMean.OneVec.half_two (F := D.host.F) (Af D.host.F)
    linear_combination 2 * h1 - T (ι 2) * h2
  have R1 : (4 : Af D.host.F) = T yv * T yi + (M : Af D.host.F) * T (w * s * yi) := by
    have e : ι 2 = ι (T yv) * yi + ι (M : Af D.host.F) * (w * s * yi) := by
      rw [map_ofNat, map_natCast]
      linear_combination yi * E3 - 2 * hyy
    rw [← hT2, e, map_add (f := _), hTl, hTl]

  let P : HeightOneSpectrum (𝓞 D.host.F) → Prop := fun v => Valued.v ((M : v.adicCompletion D.host.F)) < 1
  have hunit : ∀ v, P v → Valued.v (-(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv)) = 1 := fun v hv => by
    refine val_unit_of_rel v k hv (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hyI v))
      (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hyiI v))
      (val_le_one (GlobalTheory.SplitHeckeLabel.trace_mem_intAf hrI v)) ?_
    have := congrArg (evalV D.host.F v) R1
    simp only [map_add (f := _), map_mul, map_natCast, map_ofNat] at this
    exact this
  have hMone : ∀ v, ¬ P v → Valued.v ((M : v.adicCompletion D.host.F)) = 1 := fun v hv =>
    le_antisymm (val_natCast_le v M) (not_lt.1 hv)
  have hMne : ∀ v, ¬ P v → (M : v.adicCompletion D.host.F) ≠ 0 := fun v hv h => by
    have := hMone v hv; rw [h, map_zero] at this; exact zero_ne_one this
  let eg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F := fun v => if P v then 1 else 0
  let fg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F :=
    fun v => if P v then 0 else (M : v.adicCompletion D.host.F)⁻¹
  let cg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F :=
    fun v => if P v then -(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv) else 1
  let dg : ∀ v : HeightOneSpectrum (𝓞 D.host.F), v.adicCompletion D.host.F :=
    fun v => if P v then (-(k : v.adicCompletion D.host.F) * evalV D.host.F v (T yv))⁻¹ else 1
  have heg : ∀ v, eg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [eg, hv, if_true, if_false] <;> [exact one_mem _; exact zero_mem _]
  have hfg : ∀ v, fg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [fg, hv, if_true, if_false]
    · exact zero_mem _
    · exact mem_of_val (by rw [map_inv₀, hMone v hv, inv_one])
  have hcg : ∀ v, cg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [cg, hv, if_true, if_false]
    · exact mem_of_val (hunit v hv).le
    · exact one_mem _
  have hdg : ∀ v, dg v ∈ v.adicCompletionIntegers D.host.F := fun v => by
    by_cases hv : P v <;> simp only [dg, hv, if_true, if_false]
    · exact mem_of_val (by rw [map_inv₀, hunit v hv, inv_one])
    · exact one_mem _
  set e := mkAf eg heg
  set f := mkAf fg hfg
  set c := mkAf cg hcg
  set d := mkAf dg hdg
  have hcd : c * d = 1 := GlobalTheory.SplitHeckeLabel.af_ext fun v => by
    rw [map_mul, map_one, evalV_mkAf, evalV_mkAf]
    by_cases hv : P v <;> simp only [cg, dg, hv, if_true, if_false, mul_one]
    refine mul_inv_cancel₀ fun h0 => ?_
    have := hunit v hv; rw [h0, map_zero] at this; exact zero_ne_one this
  have hef : e + (M : Af D.host.F) * f = 1 := GlobalTheory.SplitHeckeLabel.af_ext fun v => by
    rw [map_add (f := _), map_mul, map_one, map_natCast, evalV_mkAf, evalV_mkAf]
    by_cases hv : P v <;> simp only [eg, fg, hv, if_true, if_false, mul_zero, add_zero, zero_add]
    exact mul_inv_cancel₀ (hMne v hv)
  have hce : c = e * (-(k : Af D.host.F) * T yv) + (M : Af D.host.F) * f := GlobalTheory.SplitHeckeLabel.af_ext fun v => by
    rw [map_add (f := _), map_mul, map_mul, map_mul, map_neg, map_natCast, map_natCast, evalV_mkAf, evalV_mkAf, evalV_mkAf]
    by_cases hv : P v <;> simp only [eg, fg, cg, hv, if_true, if_false, mul_zero, add_zero, zero_add, one_mul, zero_mul]
    exact (mul_inv_cancel₀ (hMne v hv)).symm
  have E1 : ι e + (M : Af D.host.F ⊗[D.host.F] D.host.E) * ι f = 1 := by
    have := congrArg ι hef; rwa [map_add, map_mul, map_natCast, map_one] at this
  have E2 : ι c = ι e * (-(k : Af D.host.F ⊗[D.host.F] D.host.E) * ι (T yv)) + (M : Af D.host.F ⊗[D.host.F] D.host.E) * ι f := by
    rw [hce, map_add (f := _), map_mul, map_mul, map_mul, map_neg, map_natCast, map_natCast]
  have E4 : ι c * ι d = 1 := by rw [← map_mul, hcd, map_one]
  set W := ι e * (yv - (k : Af D.host.F ⊗[D.host.F] D.host.E) * (w * s)) + ι f * (yv - 1) with hW
  have hmain : yv - ι c = (M : Af D.host.F ⊗[D.host.F] D.host.E) * W := by
    have hM : (M : Af D.host.F ⊗[D.host.F] D.host.E) = 2 * (k : Af D.host.F ⊗[D.host.F] D.host.E) + 1 := by
      rw [hMdef]; push_cast; ring
    rw [hW]
    linear_combination (-1 : Af D.host.F ⊗[D.host.F] D.host.E) * E2 - yv * E1 - (k : Af D.host.F ⊗[D.host.F] D.host.E) * ι e * E3 - ι e * yv * hM
  have hWI : W ∈ intAE D := by
    rw [hW]
    refine add_mem (hmulI (hιI _ (mkAf_mem eg heg)) (sub_mem hyI (hmulI (hnI k) (hmulI hwI hsI))))
      (hmulI (hιI _ (mkAf_mem fg hfg)) (sub_mem hyI hoI))
  let b : (Af D.host.F)ˣ := ⟨d, c, by rw [mul_comm]; exact hcd, hcd⟩
  refine ⟨b, y * Units.map ι.toMonoidHom b, ?_, ?_, ?_, W * ι d, ?_, ?_⟩
  · rw [Units.val_mul, Units.coe_map]
    rfl
  · exact hmulI hyI (hιI _ (mkAf_mem dg hdg))
  · rw [mul_inv_rev, Units.val_mul, ← map_inv, Units.coe_map]
    exact hmulI (hιI _ (mkAf_mem cg hcg)) hyiI
  · exact hmulI hWI (hιI _ (mkAf_mem dg hdg))
  · rw [Units.val_mul, Units.coe_map, nsmul_eq_mul]
    show yv * ι d - 1 = _
    linear_combination ι d * hmain + E4

end GlobalTheory.UnitRootCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRefinedFlagChartIntegralPointsInOpenStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_refined_flagChart_integral_points_in_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)) (S : Set Y.X) (P : PChart Xo c (algebraMap O c.F)) (T : CDVR) (io : c.F →+* T.Fr), IsOpen S → letI := io.toAlgebra; ∀ (e : P.Ω) (he : e ∈ P.es) (ψ : P.R e →ₐ[c.F] T.Fr) (z : FrPt Xo c T.Fr), (∀ g : P.R e, (g : P.Ω) ∈ P.gens → InV T (ψ g)) → FrMap ψ (P.y e he) z → ExtIn Y S T io z.x → ∃ (P' : PChart Xo c (algebraMap O c.F)) (e' : P'.Ω) (he' : e' ∈ P'.es) (ψ' : P'.R e' →ₐ[c.F] T.Fr), (∀ g : P'.R e', (g : P'.Ω) ∈ P'.gens → InV T (ψ' g)) ∧ FrMap ψ' (P'.y e' he') z ∧ ∀ (T₁ : CDVR) (io₁ : c.F →+* T₁.Fr), (∀ a : O, InV T₁ (io₁ (algebraMap O c.F a))) → letI := io₁.toAlgebra; ∀ (ψ₁ : P'.R e' →ₐ[c.F] T₁.Fr) (z₁ : FrPt Xo c T₁.Fr), (∀ g : P'.R e', (g : P'.Ω) ∈ P'.gens → InV T₁ (ψ₁ g)) → FrMap ψ₁ (P'.y e' he') z₁ → ExtIn Y S T₁ io₁ z₁.x := by
  first | exact @GlobalTheory.GoodRefine.exists_refine_extIn | exact GlobalTheory.GoodRefine.exists_refine_extIn | (intros; apply GlobalTheory.GoodRefine.exists_refine_extIn <;> assumption)
end

