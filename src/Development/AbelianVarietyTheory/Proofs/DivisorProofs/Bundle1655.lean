module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyLatR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1039
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0602
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1169
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvConjTransposeMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModeMatrixDetEqAdjointDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointDetOnCompactTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1642
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogTensorIdeleAbsDetExpScalarCentreEqMul
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.GLOneVol

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume GlobalTheory.OneRep.SplitTwist

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem idl_det_eq (k : ℕ) (g : GL (Fin k) (AF F ⊗[F] E)) :
    GlobalTheory.TateConv.idl F E (Matrix.GeneralLinearGroup.det g) = Matrix.GeneralLinearGroup.det (glTens F E k g) := by
  ext
  change GlobalTheory.TateConv.tens F E (g : Matrix (Fin k) (Fin k) (AF F ⊗[F] E)).det =
    ((GlobalTheory.TateConv.tens F E).toRingEquiv.toRingHom.mapMatrix (g : Matrix (Fin k) (Fin k) (AF F ⊗[F] E))).det
  exact RingHom.map_det (GlobalTheory.TateConv.tens F E).toRingEquiv.toRingHom _

variable [_root_.NumberField.IsTotallyComplex E]

theorem absE_det_cR (k : ℕ) (t : ℝ) :
    ((absE F E (Matrix.GeneralLinearGroup.det (cR F E k t)) : ℝ≥0) : ℝ) =
      ideleNorm (E := E) (Matrix.GeneralLinearGroup.det (GlobalTheory.UnitaryBC.splitCentre E k t)) := by
  rw [GlobalTheory.TateConv.absE_eq, idl_det_eq, glTens_cR]
  rfl

end GlobalTheory.GLOneVol

theorem GlobalTheory.GLOneVol.log_absE_det_cR : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [_root_.NumberField.IsTotallyComplex E] (k : ℕ), 1 ≤ k → ∃ a : ℝ, a ≠ 0 ∧ ∀ t : ℝ,
      Real.log ((absE F E (Matrix.GeneralLinearGroup.det (GlobalTheory.GLOneVol.cR F E k t)) : ℝ≥0) : ℝ) = a * t := by
  intro F E _ _ _ _ _ _ k hk
  let D : ℝ →+ ℝ := AddMonoidHom.mk'
    (fun t => Real.log (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (E := E)
      (Matrix.GeneralLinearGroup.det (GlobalTheory.UnitaryBC.splitCentre E k t)))) fun x y => by
      rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_add, map_mul, map_mul,
        Real.log_mul (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _)]
  have hD : Continuous D :=
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleNorm.comp (Matrix.GeneralLinearGroup.continuous_det.comp
      GlobalTheory.OneRep.SplitTwist.continuous_splitCentre)).log fun _ => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _
  have hDt : ∀ t, D t = t * D 1 := fun t => by simpa using map_real_smul D hD t 1
  have hD1 : 0 < D 1 := by
    change 0 < Real.log (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (E := E)
      (Matrix.GeneralLinearGroup.det (GlobalTheory.UnitaryBC.splitCentre E k 1)))
    rw [GlobalTheory.CuspRep.CuspidalL2GL.det_splitCentre_one, map_pow, Real.log_pow]
    exact mul_pos (by exact_mod_cast hk) (Real.log_pos (GlobalTheory.IdeleCovolume.one_lt_ideleNorm_eIdele E))
  refine ⟨D 1, hD1.ne', fun t => ?_⟩
  rw [GlobalTheory.GLOneVol.absE_det_cR, mul_comm]
  exact hDt t
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactPseudoCoefficientData
section
open GlobalTheory.PsCo.Pc1

namespace GlobalTheory.PsCo.Pc1

theorem maximalCompact_pseudoCoefficientData' : StKData :=
  GlobalTheory.PsCo.PcEF.stKData_of
    GlobalTheory.PsCo.PcEF.maxCompactPolynomial_blockTimesConjDetPower GlobalTheory.PsCo.PcEF.modeMatrixDet_eq_adjointDet GlobalTheory.PsCo.PcEF.coefPoly
    GlobalTheory.PsCo.PcEF.trPoly GlobalTheory.PsCo.PcEF.adjointDetTrace_classFunction GlobalTheory.PsCo.PcEF.harishChandraWeight_integral_dominant
    GlobalTheory.PsCo.PcEF.polyCoefIrrep_hasDerivedAction GlobalTheory.PsCo.PcEF.adjointDet_onCompactTorus GlobalTheory.PsCo.PcEF.torusId_full
    GlobalTheory.PsCo.PcEF.tracePairing_nonzero_intertwiner GlobalTheory.PsCo.PcEF.norm_irreducibleCharacter_unitaryMaxCompact_eq_one GlobalTheory.PsCo.PcEF.rangeFD_closed
    GlobalTheory.PsCo.PcEF.casimirScalar_stableSumSpace GlobalTheory.PsCo.PcEF.supertrace_carriedBy_diracKernel GlobalTheory.PsCo.PcEF.StrIdx_proof2
    GlobalTheory.PsCo.PcEF.intertwiner_preserves_highestWeight GlobalTheory.PsCo.PcEF.fockCoordinates_span_finiteDimensional GlobalTheory.PsCo.PcEF.casimirValue_highestWeightCoordinates
    GlobalTheory.PsCo.PcEF.highestWeightKernel_lowestType GlobalTheory.PsCo.PcEF.eq_discreteSeries_of_lowestKType_casimir GlobalTheory.PsCo.PcEF.compactDiscreteSeries_ownType
    GlobalTheory.PsCo.PcEF.gapConditions_of_largeGaps GlobalTheory.PsCo.PcEF.unitaryRep_upq_matrixFunction GlobalTheory.HcPort.casimirActsByScalar_indefUnitary

end GlobalTheory.PsCo.Pc1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCmCoordinateLatticeOfIntegralGramPairing
section
set_option autoImplicit false

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

namespace GlobalTheory.FlatCM.HomLat

theorem mem_lat_of_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
      ∀ d : Fin p → E, (∀ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) →
        d ∈ GlobalTheory.FlatCM.HomLat.lat X := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X gP gQ hG barE hbar d hd
  classical
  obtain ⟨y, hy0, hyi⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image d)
  have hsq : ((y.natAbs ^ 2 : ℕ) : ℤ) = y * y := by rw [Nat.cast_pow, Int.natCast_natAbs, sq_abs, sq]
  have hint : ∀ a, IsIntegral ℤ (((y.natAbs ^ 2 : ℕ) : E) * d a) := fun a => by
    have h1 := hyi (d a) (Finset.mem_image_of_mem d (Finset.mem_univ a))
    have e : ((y.natAbs ^ 2 : ℕ) : E) * d a = (algebraMap ℤ E y) * (y • d a) := by
      rw [zsmul_eq_mul, algebraMap_int_eq, eq_intCast, ← _root_.mul_assoc]
      congr 1
      rw [← Int.cast_natCast (R := E), hsq]
      try push_cast
      try ring
    rw [e]
    exact isIntegral_algebraMap.mul h1
  set n : ℕ := y.natAbs ^ 2 with hn_def
  have hn : 0 < n := pow_pos (Int.natAbs_pos.2 hy0) 2
  let x : Fin p → 𝓞 E := fun a => ⟨(n : E) * d a, hint a⟩
  have hx : ∀ a, (x a : E) = n * d a := fun a => rfl
  have hψ := GlobalTheory.FlatCM.HomLat.isLinearHom_prod X x
  have hk := _root_.GlobalTheory.FlatCM.TorsKill.kill E H hH K ρ σ₁ p X _ hψ n hn (fun f hf ⟨m, hm, z, hfz⟩ => by
    have hm' : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
    have hc : (fun a => (z a : E) / m) ∈ GlobalTheory.FlatCM.HomLat.lat X := Submodule.subset_span
      ⟨m, hm, z, fun a => by field_simp, f, hf, hfz⟩
    obtain ⟨w, hw⟩ := hd _ hc
    refine ⟨w, _root_.GlobalTheory.FlatCM.HomLat.weilEq_gram E H hH K ρ σ₁ p X gP gQ hG m hm z f hf hfz x _ ?_⟩
    have hb : ∀ b, ((H.bar (x b) : 𝓞 E) : E) = n * barE (d b) := fun b => by
      rw [← hbar, hx, map_mul, map_natCast]
    have key : (m : E) * ((n : E) * (w : E)) =
        ∑ a, ∑ b, (z a : E) * (gP a b : E) * ((H.bar (x b) : 𝓞 E) : E) := by
      simp_rw [hb]
      rw [hw]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      field_simp
    apply RingOfIntegers.coe_injective
    push_cast
    exact key)
  obtain ⟨χ, hχ, hχn⟩ := _root_.GlobalTheory.DivisibleLinear.exists_linear_pow_eq E H K σ₁ (X.A true) X.B _ hψ n hn hk
  exact Submodule.subset_span ⟨n, hn, x, hx, χ, hχ, hχn⟩

end GlobalTheory.FlatCM.HomLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedFiniteDatumEqSumRationalRootTranslates
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.AdTh.MovedDatumCore
open GlobalTheory.AdTh.MovedDatum

theorem moved_datum_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (bad N : ℕ) (h : GA D (Vc D i)) (k : GA D (Wc D i)) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → SplitOffBad (Vc D i) bad h → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι k mk → ∀ (Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E) (γ : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (u : (Fin (Vc D i).rank → LevQ Dw l₂) → WO (Vc D i) (Wc D i)), IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) k)) mk N Y → (∀ q, colsR (rank_Wc i) (γ q) = (δ : ℤ) • Y q ∧ IsFinOf (Vc D i) (Wc D i) (γ q) (u q)) → R.ωP i t (h, k) (R.vP i t) = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (u q) (R.ωP i t (h, k) (R.vacP i)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hiso
  obtain ⟨δ, hδ⟩ := GlobalTheory.DatumFourierCore.thetaVector_eq_sum_heisenberg_core D G Pl0 T0 A Ks R F hR i hV H Dw ι hι hiso
  refine ⟨δ, fun t l φ hφ hP bad N h k Λ mk hbad hh hΛ hT hL hmk Y γ u hY hu => ?_⟩
  obtain ⟨e, he, -⟩ := id hφ
  obtain ⟨hp, -, a1, a2, a3, a4, a5⟩ := GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A Ks R F hR i t hV
  obtain ⟨hψ, hvac⟩ := (hR.thP.vP i t).1
  rw [hδ t l φ hφ hP e he, map_smul]
  by_cases hfin : Finite (Fin (Vc D i).rank → LevQ Dw l)
  swap
  · haveI := not_finite_iff_infinite.1 hfin
    rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero, _root_.inv_zero, zero_smul, zero_smul]
  rw [map_finsum _ (Set.toFinite _)]
  congr 1
  refine finsum_congr fun q => ?_
  rw [map_smul]
  by_cases hq : hatC l φ q = 0
  · rw [hq, zero_smul, zero_smul]
  obtain ⟨c, hc, h1, h2⟩ := step R.ψ hψ (Vc D i) (Wc D i) hp.std (rank_Wc i) (R.ΛV i) (R.ΛW i) a1 a2 a3 a4 a5 l ι hι δ
    _ e he (fun PP hPP => ⟨(hP PP (Finset.mem_union.1 hPP)).1, fun h2 => (hP PP (Finset.mem_union.1 hPP)).2 (by
      obtain ⟨c, hc⟩ : 2 ∣ D.host.QS := (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd
      rw [hc, mul_assoc, mul_assoc, Nat.cast_mul, Nat.cast_ofNat]; exact Ideal.mul_mem_right _ _ h2)⟩)
    bad N h k Λ mk (fun PP hPP => hbad PP (Finset.mem_union.1 hPP)) hh hΛ hT hL hmk Y hY q
    (fun s hs => GlobalTheory.T.levelPoint_smul_integral_of_fourierCoeff_ne_zero D G Pl0 T0 A Ks R i H Dw ι t l φ hφ q hq s fun PP hPP => hs PP (Finset.mem_union.2 hPP))
    (γ q) (u q) (hu q).1 (hu q).2
  have h3 : heisO R.ψ (Vc D i) (Wc D i) (2 • actO (Vc D i) (Wc D i) h k c) (R.ωP i t (h, k) (R.vacP i)) =
      R.ωP i t (h, k) (R.vacP i) := by
    rw [← actO_two, ← hp.weil.om_heis h k _ _ hvac.theta, hvac.lat.1 c hc]
  have h4 := GlobalTheory.PlaceModel.heisL_heisL (Vc D i) (Wc D i) R.ψ _ _ (R.ωP i t (h, k) (R.vacP i)) |>.trans
    (congrArg (· • _) h2)
  rw [one_smul, ← h1] at h4
  rw [hp.weil.om_heis h k _ _ hvac.theta]
  congr 1
  refine Eq.trans ?_ h4
  exact congrArg _ h3.symm

end GlobalTheory.AdTh.MovedDatumCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatWDualWtOfLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SignedHC

namespace GlobalTheory.GridWtBound

theorem natW_dual_wtOf_le (n : ℕ) (E : Finset ℚ) (M : ℝ) (hM : 0 ≤ M) (hE : ∀ x ∈ E, |(x : ℝ)| ≤ M) (a : Fin n) :
    (((wtOf n E).dual.natW a : ℕ) : ℝ) ≤ 2 * M + 1 := by
  have hn : 0 < n := a.pos
  have hrev : Fin.rev (⟨n - 1, by omega⟩ : Fin n) = ⟨0, hn⟩ := by ext; simp; omega
  have key : (wtOf n E).dual.natW a = ((wtOf n E).w ⟨0, hn⟩ - (wtOf n E).w a.rev).toNat := by
    simp only [DomWeight.natW, DomWeight.detShift, DomWeight.dual, dif_pos hn, hrev]
    congr 1; ring
  have hd : (((wtOf n E).w ⟨0, hn⟩ - (wtOf n E).w a.rev : ℤ) : ℝ) ≤ 2 * M + 1 := by
    unfold wtOf
    split_ifs with h
    · have e0 := hE _ (descEnum_mem E h.1 ⟨0, hn⟩)
      have e1 := hE _ (descEnum_mem E h.1 a.rev)
      have f0 : ((⌊highestWeight E h.1 ⟨0, hn⟩⌋ : ℤ) : ℝ) ≤ ((highestWeight E h.1 ⟨0, hn⟩ : ℚ) : ℝ) := by
        exact_mod_cast Int.floor_le _
      have f1 : ((highestWeight E h.1 a.rev : ℚ) : ℝ) - 1 < ((⌊highestWeight E h.1 a.rev⌋ : ℤ) : ℝ) := by
        exact_mod_cast Int.sub_one_lt_floor _
      have hr : (0 : ℝ) ≤ ((a.rev : ℕ) : ℝ) := Nat.cast_nonneg _
      have g0 : ((highestWeight E h.1 ⟨0, hn⟩ : ℚ) : ℝ) ≤ M - ((n : ℝ) - 1) / 2 := by
        simp only [highestWeight]; push_cast; linarith [(abs_le.1 e0).2]
      have g1 : -M - ((n : ℝ) - 1) / 2 ≤ ((highestWeight E h.1 a.rev : ℚ) : ℝ) := by
        simp only [highestWeight]; push_cast; linarith [(abs_le.1 e1).1]
      push_cast
      linarith
    · simp; linarith
  rw [key]
  have c : (((wtOf n E).w ⟨0, hn⟩ - (wtOf n E).w a.rev).toNat : ℝ) =
      (((((wtOf n E).w ⟨0, hn⟩ - (wtOf n E).w a.rev).toNat : ℤ)) : ℝ) := (Int.cast_natCast _).symm
  rw [c, Int.toNat_eq_max]
  push_cast
  exact max_le (by push_cast at hd; exact hd) (by linarith)

end GlobalTheory.GridWtBound

namespace GlobalTheory.GridWtBound

theorem extend_bounds {n : ℕ} (d : ℕ) (f : Fin n → ℚ) (h : ℝ) (hh : 0 ≤ h)
    (hf : ∀ i, 0 ≤ ((f i : ℚ) : ℝ) ∧ ((f i : ℚ) : ℝ) ≤ h) (j : ℕ) :
    0 ≤ ((GridData.extend d f j : ℤ) : ℝ) ∧ ((GridData.extend d f j : ℤ) : ℝ) ≤ h := by
  unfold GridData.extend
  split_ifs with hj
  · obtain ⟨h1, h2⟩ := hf ⟨j - d, hj⟩
    have a1 : (0 : ℚ) ≤ f ⟨j - d, hj⟩ := by exact_mod_cast h1
    refine ⟨by exact_mod_cast Int.floor_nonneg.2 a1, le_trans ?_ h2⟩
    exact_mod_cast Int.floor_le _
  · simp [hh]

variable {D : D7}

end GlobalTheory.GridWtBound

namespace GlobalTheory.GridWtBound

theorem one_le_b {D : D7} (large₂ : SizeData₂ D) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) : (1 : ℝ) ≤ large₂.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, -, -⟩ := hs
  have hSc := large₂.Sc_pos
  have hsg : sLen D < gap D 1 := sLen_lt_gap D 1
  have hg1 : (1 : ℝ) ≤ (gap D 1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ gap D 1)
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  nlinarith

end GlobalTheory.GridWtBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OppositeKernelsRationalRowMapLargeConstants
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

theorem ratRowAt_big : BigC fun _ ch _ _ => RatRowAt ch := by
  refine ⟨0, fun _ _ => ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩⟩
  intro D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ hK
  intro Φ β d hd c i
  obtain ⟨hβ, τ, hτ, hdτ⟩ := hd
  have hr := (hK.isRatAt hβ hτ hdτ c).2 i
  refine GlobalTheory.RatTop.exists_linearMap_of_repr_mem_range D.what₂.embLL (GlobalTheory.CoefModel.mapVV D.what₂.embLL _)
    (GlobalTheory.CoefModel.mapVV D.what₂.embLL _) (bVV D.what₂.LL _) (bVV ℂ _) (bVV ℂ _)
    (fun k => ⟨_, (GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.1⟩)
    (fun k => ⟨_, (GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.1⟩) ?_ ?_ _ ?_
  · intro k
    apply Subtype.ext
    rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
    exact ((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.2).symm
  · intro k
    apply Subtype.ext
    rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
    exact ((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.2).symm
  · intro k l
    have h := hr k l
    rwa [Normal.kkIn, LinearMap.toMatrix_apply] at h

end GlobalTheory.KerConjMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierLeftIsometryL2
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.DoublingEvaluationL2

theorem partL_lintegral_sq : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (A : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
    (∀ Φ ∈ schA F (κ ⊕ κ'), partL (κ' := κ') A Φ ∈ schA F (κ ⊕ κ')) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖A φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partL (κ' := κ') A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ κ' _ _ A hmem hA μ hμ
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  letI mX : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mY : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  letI mZ : MeasurableSpace (κ ⊕ κ' → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ' → AF F) := ⟨rfl⟩
  let μ₁ : Measure (κ → AF F) := Measure.addHaar
  let μ₂ : Measure (κ' → AF F) := Measure.addHaar
  obtain ⟨C₁, hC₁⟩ := hA μ₁ inferInstance
  refine ⟨C₁, fun Φ hΦ => ?_⟩
  let e : (κ ⊕ κ' → AF F) ≃ₜ (κ → AF F) × (κ' → AF F) := Homeomorph.sumArrowHomeomorphProdArrow
  let eA : ((κ → AF F) × (κ' → AF F)) ≃ₜ+ (κ ⊕ κ' → AF F) :=
    { e.symm with map_add' := fun a b => by funext i; cases i <;> rfl }
  let ν : Measure (κ ⊕ κ' → AF F) := (μ₁.prod μ₂).map eA
  haveI : ν.IsAddHaarMeasure := eA.isAddHaarMeasure_map _
  obtain ⟨c, hμν⟩ : ∃ c : NNReal, μ = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul μ ν⟩
  have key : ∀ f : (κ ⊕ κ' → AF F) → ℝ≥0∞, Measurable f →
      ∫⁻ z, f z ∂μ = c * ∫⁻ y, ∫⁻ x, f (Sum.elim x y) ∂μ₁ ∂μ₂ := by
    intro f hf
    have hmeas : Measurable (⇑eA) := eA.continuous.measurable
    rw [hμν, lintegral_smul_measure]
    simp only [ν]
    rw [lintegral_map hf hmeas, lintegral_prod_symm (fun p => f (eA p)) (hf.comp hmeas).aemeasurable]
    rfl
  have hc1 := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F (hmem Φ hΦ)
  have hc2 := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ
  rw [key _ (hc1.measurable.enorm.pow_const 2), key _ (hc2.measurable.enorm.pow_const 2)]
  have inner : ∀ y, ∫⁻ x, ‖partL (κ' := κ') A Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ =
      C₁ * ∫⁻ x, ‖Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ := by
    intro y
    have h := hC₁ _ (GlobalTheory.DoublingEvLaw.sliceL hΦ y)
    simpa only [partL_apply, Sum.elim_comp_inl, Sum.elim_comp_inr] using h
  have hm : Measurable fun y => ∫⁻ x, ‖Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ :=
    Measurable.lintegral_prod_left' (f := fun p : (κ → AF F) × (κ' → AF F) => ‖Φ (eA p)‖ₑ ^ 2)
      ((hc2.comp eA.continuous).measurable.enorm.pow_const 2)
  simp_rw [inner]
  rw [lintegral_const_mul _ hm]
  ring

end GlobalTheory.DoublingEvaluationL2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierRightIsometryL2
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.DoublingEv.L2RightPartial

theorem partR_lintegral_sq_eq_const_mul_of_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (A : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)),
    (∀ Φ ∈ schA F (κ ⊕ κ'), partR (κ := κ) A Φ ∈ schA F (κ ⊕ κ')) →
    (∀ μ : @Measure (κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ', ∫⁻ x, ‖A φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partR (κ := κ) A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ κ' _ _ A hmem hA μ hμ
  exact GlobalTheory.DblEval.L2RightPartial.partR_lintegral_sq_eq_const_mul_of_mem_schA (κ := κ) A hA hmem μ hμ

end GlobalTheory.DoublingEv.L2RightPartial

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdCharFiniteAdeleRationalEqExpTraceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdChar_finiteAdele_rational_eq_exp_trace : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ q : D.host.F, ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q)) = Complex.exp (2 * Real.pi * Complex.I * ∑ τ, tauE D τ (q : D.host.E)) := by
  first | exact @GlobalTheory.PsiFinRat.psi_pairA_zero_algebraMap | exact GlobalTheory.PsiFinRat.psi_pairA_zero_algebraMap | (intros; apply GlobalTheory.PsiFinRat.psi_pairA_zero_algebraMap <;> assumption)
end

