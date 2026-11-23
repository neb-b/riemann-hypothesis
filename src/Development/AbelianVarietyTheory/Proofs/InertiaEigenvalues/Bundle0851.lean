module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0846
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0839
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0815
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0009
public import Formalism.LocalToGlobal.Columns.MtAdWt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0840
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormBoundGoodPointsExtendsAllPoints
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupSetFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonOfScalar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import GroundTheory.AutomorphicForms.ReductionFinite

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseLevelCharacterMemCoefficientRing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
noncomputable section

namespace GlobalTheory.LamVal

theorem exists_of_pow {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] {a : FractionRing A} {n : ℕ}
    (hn : n ≠ 0) (h : a ^ n = 1) : ∃ y : A, algebraMap A (FractionRing A) y = a := by
  have hi : IsIntegral A a := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h]⟩
  exact IsIntegrallyClosed.isIntegral_iff.1 hi

variable {D : D7}

theorem e_mem_of_pow {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (b : Bool) {a : FractionRing (D.ntw.O i)} {n : ℕ}
    (hn : n ≠ 0) (h : a ^ n = 1) : ρ.e i b a ∈ (ρ.eOk i b 0).range := by
  obtain ⟨y, rfl⟩ := exists_of_pow hn h
  exact ⟨algebraMap _ _ y, hρ.ek_e i b 0 y⟩

theorem de_mem {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ) :
    (((ρ.B i j b).de.chi z : Circle) : ℂ) ∈ (ρ.eOk i b 0).range := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O i) (D.ntw.Ok i 0)
    (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)), ?_⟩
  rw [hρ.ek_e, hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm

end GlobalTheory.LamVal

namespace GlobalTheory.LamVal

variable {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D}

theorem typeCharacterExtension_mem_range_coefficientRing (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (g : G0 (Y.Z.ρ.B i j b).G.Pg (Wc D j).rank) :
    ((ext1 (Y.Z.ρ.B i j b).G.P.H (⇑(Y.Z.ρ.B i j b).G.P.chi) g : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  unfold ext1
  split_ifs with h
  · set g' := (Y.Z.ρ.eG i j b).symm g with hg'
    have hg : Y.Z.ρ.eG i j b g' = g := MulEquiv.apply_symm_apply _ _
    have h' : Y.Z.ρ.eG i j b g' ∈ (Y.Z.ρ.B i j b).G.P.H := by rw [hg]; exact h
    have hu : g' ∈ D.nexp.U := ((Y.Z.tie i j b).U_eq g').1 h'
    have e1 := (Y.Z.tie i j b).psiU_eq ⟨g', hu⟩ h'
    have e2 : (Y.Z.ρ.B i j b).G.P.chi ⟨g, h⟩ = (Y.Z.ρ.B i j b).G.P.chi ⟨Y.Z.ρ.eG i j b g', h'⟩ := by
      congr 1
      exact Subtype.ext hg.symm
    rw [e2, e1]
    have hfin : ((Y.Z.ρ.B i j b).G.P.chi ⟨Y.Z.ρ.eG i j b g', h'⟩) ^ Nat.card (Y.Z.ρ.B i j b).G.P.H = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    refine e_mem_of_pow Y.Z.good i b (n := Nat.card (Y.Z.ρ.B i j b).G.P.H) Nat.card_pos.ne' ?_
    apply (Y.Z.ρ.e i b).injective
    rw [map_pow, ← e1, ← Units.val_pow_eq_pow_val, hfin, Units.val_one, map_one]
  · exact one_mem _

theorem loc_mem (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (PP : Pl D.host.E) (w : (kP PP)ˣ) :
    ((((Y.Z.ρ.B i j b).de.locC PP * (Y.Z.ρ.tw i b 0 ∅ 1).locC PP) w : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  have hψ : (Y.Z.ρ.tw i b 0 ∅ 1).locC PP = 1 := by
    simp [Twist.locC, Setup.tw, twistOf, half_empty]
  rw [hψ, mul_one]
  unfold Twist.locC
  split_ifs with hq
  · have hB := Y.Z.good.base i j b
    obtain ⟨P, -, hQ, hsp⟩ := hB.places.split
    obtain ⟨x, hx⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (hsp.isIdemAt (hQ hq)) w
    show (((Y.Z.ρ.B i j b).de.res PP w : Circle) : ℂ) ∈ _
    rw [← hx.eq (hB.de.res PP hq)]
    exact de_mem Y.Z.good i j b x
  · simp

end GlobalTheory.LamVal

namespace GlobalTheory.LamVal

variable {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D}

theorem de_frac {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ) :
    ∃ d, ρ.e i b d = (((ρ.B i j b).de.chi z : Circle) : ℂ) := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O i) _
    (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)), ?_⟩
  rw [hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm

theorem baseCharacter_finiteIdeles_mem_range_fractionRing (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) (hx : infPart D (x : AE D) = 1) :
    ∃ a, Y.Z.ρ.e i b a = (((Y.Z.ρ.B i j b).mu0 x : Circle) : ℂ) := by
  obtain ⟨y, hy⟩ := X.valKs j x hx
  refine ⟨sideEmb D.ntw i b (Y.S.kKs ((Y.YS.fi j).eK.symm y)), ?_⟩
  rw [Y.Z.good.e_LL0, Y.Z.pin.mu0 i j b]
  refine Eq.trans ?_ hy.symm
  change D.what₂.embLL ((Y.S.kKs ((Y.YS.fi j).eK.symm y) : D.LL0) : D.what₂.LL) = _
  rw [Y.S.kKs_spec, ← (Y.YS.fi j).eK_LL, RingEquiv.apply_symm_apply]

theorem muC_mem (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    {PP : Pl D.host.E} (hPP : PP ∈ (Y.Z.ρ.B i j b).G.Pg) (w : (kP PP)ˣ) :
    (((Y.Z.ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  have hB := Y.Z.good.base i j b
  obtain ⟨P, hPg, -, hsp⟩ := hB.places.split
  obtain ⟨x, hx⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (hsp.isIdemAt (hPg hPP)) w
  have e1 : (Y.Z.ρ.B i j b).G.mu PP w = (Y.Z.ρ.B i j b).mu x := (hx.eq (hB.tame PP hPP)).symm
  show (((Y.Z.ρ.B i j b).G.mu PP w : Circle) : ℂ) ∈ _
  obtain ⟨a, ha⟩ := baseCharacter_finiteIdeles_mem_range_fractionRing Y i j b x hx.inf
  obtain ⟨d, hd⟩ := de_frac Y.Z.good i j b x
  have e2 : (((Y.Z.ρ.B i j b).G.mu PP w : Circle) : ℂ) = Y.Z.ρ.e i b (a * d) := by
    rw [e1, Base.mu, MonoidHom.mul_apply, Circle.coe_mul, map_mul, ha, hd]
  haveI : Finite (kP PP)ˣ := inferInstance
  have hfin : ((Y.Z.ρ.B i j b).G.mu PP w) ^ Nat.card (kP PP)ˣ = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  rw [e2]
  refine e_mem_of_pow Y.Z.good i b (n := Nat.card (kP PP)ˣ) Nat.card_pos.ne' ?_
  apply (Y.Z.ρ.e i b).injective
  rw [map_pow, ← e2, ← Circle.coe_pow, hfin, Circle.coe_one, map_one]

theorem levLam_mem_coef : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
    (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := by
  intro D X E Y i j b k
  rw [GlobalTheory.MtLatConj.levelCharacter_apply_eq_levelFunction_swap]
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod]
  exact mul_mem (mul_mem (typeCharacterExtension_mem_range_coefficientRing Y i j b _) (prod_mem fun PP hPP => prod_mem fun _ _ => muC_mem Y i j b hPP _))
    (prod_mem fun PP _ => loc_mem Y i j b PP _)

end GlobalTheory.LamVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellDecompositionLatticeIntegralUnfoldingStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_decomposition_lattice_integral_unfolding : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (F : GA E (m + 1) → ℂ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T) (U : Subgroup (GL (Fin (m + 1)) (Af E))) (Φ : (Fin (m + 1) → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (C : Set (GA E (m + 1))), IsCompact C →
    (∀ w, l₀.1 w (Fin.last m) = 0) → (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * p ∈ C) →
    HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ KGL w (n := (m + 1))) ∧ (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∃ K : Set (GA E (m + 1)), IsCompact K ∧ ∀ (x : ℝ) (g : GA E (m + 1)), g ∈ GlobalTheory.CellDec.C0 E (m + 1) T →
      GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * g ∈ K := by
  first | (exact @GlobalTheory.RSCell.CptMod.exists_isCompact_mod_NA) | (exact GlobalTheory.RSCell.CptMod.exists_isCompact_mod_NA) | (intros; apply GlobalTheory.RSCell.CptMod.exists_isCompact_mod_NA  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharPolyInertiaOfPotSemistableEnlargement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.PstModel

theorem charPol_upRep_of_isPstAt : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) → ∃ (LL' : FinExt (D.nd.l i)) (hL : (D.nbr i w hw).LL.1 ≤ LL'.1), GlobalTheory.Pst.IsPst (D.loc (D.nd.l i)) ((D.nbr i w hw).repE LL' (GlobalTheory.PstLine.upRep hL m (mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w))))) ∧ ∀ (σ : Gw D.nd w) (hσ : (σ : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) (p : (D.nd.O i)[X]), p.map (iotaO D.nd D.naut i) = (GlobalTheory.Pst.wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w)).inePol (σ : GE D.nd) → ((p.map (D.nbr i w hw).toLL).map (IntermediateField.inclusion hL).toRingHom).map ((D.naut.iotaQC i).toRingHom.comp (algebraMap ↥LL'.1 (Om (D.nd.l i)))) = (GlobalTheory.Pst.wdPst (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) ((D.nbr i w hw).repE LL' (GlobalTheory.PstLine.upRep hL m (mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w)))))).charPol (GlobalTheory.WeilDeligne.ineIncl (D.nd.plOm.2 w) ⟨(σ : GE D.nd), hσ⟩) := by
  intro D i w hw m r h
  obtain ⟨LL', r', ⟨hL, hmod⟩, hpst, hwd⟩ := GlobalTheory.Pst.wdAt_of_isPstAt (P := D.loc (D.nd.l i)) (D.naut.iotaQC i)
    (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) h
  have key : r' = GlobalTheory.PstLine.upRep hL m (mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w))) := by
    ext g a b
    have h1 := congrArg (fun f => ((f g : GL (Fin m) (Om (D.nd.l i))) : Matrix (Fin m) (Fin m) (Om (D.nd.l i))) a b) hmod
    have h2 := (D.loc_tie i w hw).1 (((r g : GL (Fin m) (D.nd.O i)) : Matrix (Fin m) (Fin m) (D.nd.O i)) a b)
    simp only [mapRep, GlobalTheory.Pst.resDec, GlobalTheory.PstLine.upRep] at h1 ⊢
    simp at h1 ⊢
    exact h1.trans h2
  refine ⟨LL', hL, key ▸ hpst, ?_⟩
  intro σ hσ p hp
  rw [← key, ← hwd, ← GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine, ← hp, Polynomial.map_map, Polynomial.map_map]
  congr 1
  ext x
  have h2 := (D.loc_tie i w hw).1 x
  simp only [iotaO, iotaOQ] at h2 ⊢
  simp at h2 ⊢
  exact h2.symm

end GlobalTheory.PstModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjGenTransportExists
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Pointwise

namespace GlobalTheory.ConjTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem symm_alg (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (x : E) :
    c.symm (algebraMap E Ω x) = algebraMap E Ω (τ.symm x) := by
  rw [RingEquiv.symm_apply_eq, hτ, RingEquiv.apply_symm_apply]

def conjG (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) :
    G E Ω →* G E Ω where
  toFun g := AlgEquiv.ofRingEquiv (f := c.symm.trans (g.toRingEquiv.trans c)) (fun x => by
    simp only [RingEquiv.trans_apply, symm_alg c τ hτ, AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, hτ, RingEquiv.apply_symm_apply])
  map_one' := by ext y; simp
  map_mul' g h := by ext y; simp

theorem conjG_apply (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x))
    (g : G E Ω) (y : Ω) : conjG c τ hτ g y = c (g (c.symm y)) := rfl

theorem conjG_apply_c (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x))
    (g : G E Ω) (y : Ω) : conjG c τ hτ g (c y) = c (g y) := by
  rw [conjG_apply, RingEquiv.symm_apply_apply]

theorem conjG_conjG_symm (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x))
    (g : G E Ω) : conjG c τ hτ (conjG c.symm τ.symm (symm_alg c τ hτ) g) = g := by
  ext y; simp [conjG_apply]

theorem conjG_continuous [Algebra.IsAlgebraic E Ω] (c : Ω ≃+* Ω) (τ : E ≃+* E)
    (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) : Continuous (conjG c τ hτ) := by
  classical
  apply continuous_of_continuousAt_one (conjG c τ hτ)
  rw [ContinuousAt, map_one]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff] at hU
  obtain ⟨S, hS, hSU⟩ := hU
  let b := Module.finBasis E S
  let s : Finset Ω := Finset.univ.image (fun i => c.symm (b i : Ω))
  have hfin : FiniteDimensional E (IntermediateField.adjoin E (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral)
  show _ ∈ nhds (1 : G E Ω)
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨_, hfin, fun g hg => hSU ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hg ⊢
  intro x hx
  have hb : ∀ i, conjG c τ hτ g (b i : Ω) = b i := by
    intro i
    rw [conjG_apply, hg _ (IntermediateField.subset_adjoin _ _ (by simp [s])), RingEquiv.apply_symm_apply]
  have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Ω) := by
    have := congrArg (fun z : S => (z : Ω)) (b.sum_repr ⟨x, hx⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_smul] at this
    exact this.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx', map_sum]
  simp [map_smul, hb]

theorem mem_Dec_iff' {A : ValuationSubring Ω} {σ : G E Ω} :
    σ ∈ Dec (F := E) A ↔ ∀ y, σ y ∈ A ↔ y ∈ A := by
  constructor
  · exact fun h y => apply_mem_iff_of_mem_Dec h y
  · intro h
    show σ • A = A
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← h, mul_inv_apply]

theorem lt_one_transport {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω) (hc : ∀ y, y ∈ A ↔ c y ∈ A') (y : Ω) :
    A.valuation y < 1 ↔ A'.valuation (c y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hc, ← hc, map_eq_zero_iff _ c.injective]

theorem conjG_mem_Ine {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω) (τ : E ≃+* E)
    (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {g : G E Ω}
    (hg : g ∈ Ine (F := E) A) : conjG c τ hτ g ∈ Ine (F := E) A' := by
  have hsurj : ∀ y', ∃ y, y' = c y := fun y' => ⟨c.symm y', (c.apply_symm_apply y').symm⟩
  refine ⟨?_, ?_⟩
  · have hD : g ∈ Dec (F := E) A := hg.1
    show conjG c τ hτ g ∈ Dec (F := E) A'
    rw [mem_Dec_iff'] at hD ⊢
    intro y'
    obtain ⟨y, rfl⟩ := hsurj y'
    rw [conjG_apply_c, ← hc, ← hc, hD]
  · intro y' hy'
    obtain ⟨y, rfl⟩ := hsurj y'
    rw [conjG_apply_c, ← map_sub, ← lt_one_transport c hc]
    rw [ValuationSubring.valuation_le_one_iff, ← hc, ← ValuationSubring.valuation_le_one_iff] at hy'
    exact hg.2 y hy'

theorem conjG_mem_wild {A A' : ValuationSubring Ω} (c : Ω ≃+* Ω) (τ : E ≃+* E)
    (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (hc : ∀ y, y ∈ A ↔ c y ∈ A') {g : G E Ω}
    (hg : ∀ y : Ω, y ≠ 0 → A.valuation (g y / y - 1) < 1) :
    ∀ y : Ω, y ≠ 0 → A'.valuation (conjG c τ hτ g y / y - 1) < 1 := by
  intro y' hy'
  obtain ⟨y, rfl⟩ : ∃ y, y' = c y := ⟨c.symm y', (c.apply_symm_apply y').symm⟩
  have hy : y ≠ 0 := fun h => hy' (by rw [h, map_zero])
  rw [conjG_apply_c, ← map_div₀, ← map_one c, ← map_sub, ← lt_one_transport c hc]
  exact hg y hy

end GlobalTheory.ConjTransport

namespace GlobalTheory

open GlobalTheory.ConjTransport

theorem conjGen_transport_exists : ∀ (D : D7) (w w' : PlE D.host) (γ : GE D.nd), IsConjPl D.host w w' →
    TameGenAt (D.nd.plOm.1 w) γ → ∃ γ' : GE D.nd, IsConjGen D w w' γ γ' ∧ TameGenAt (D.nd.plOm.1 w') γ' := by
  intro D w w' γ hww hγ
  let τ : D.host.E ≃+* D.host.E := (D.host.conj : D.host.E ≃+* D.host.E)
  let c₀ : D.nd.Om ≃+* D.nd.Om := IsAlgClosure.equivOfEquiv D.nd.Om D.nd.Om τ
  have hc₀ : ∀ x, c₀ (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (τ x) :=
    IsAlgClosure.equivOfEquiv_algebraMap D.nd.Om D.nd.Om τ
  set A := D.nd.plOm.1 w with hAdef
  set A' := D.nd.plOm.1 w' with hA'def
  have hA : IsPlaceOver A w := D.nd.plOm.2 w
  have hA' : IsPlaceOver A' w' := D.nd.plOm.2 w'
  let B : ValuationSubring D.nd.Om := A.comap (c₀.symm : D.nd.Om →+* D.nd.Om)
  have hAB : ∀ y, y ∈ A ↔ c₀ y ∈ B := fun y => by
    show y ∈ A ↔ c₀.symm (c₀ y) ∈ A
    rw [RingEquiv.symm_apply_apply]
  have hB : IsPlaceOver B w' := by
    intro x
    let x'' : 𝓞 D.host.E := ⟨τ.symm x, (x.isIntegral_coe).map (τ.symm : D.host.E →+* D.host.E).toIntAlgHom⟩
    have h1 : algebraMap D.host.E D.nd.Om (x : D.host.E) = c₀ (algebraMap D.host.E D.nd.Om (x'' : D.host.E)) := by
      rw [hc₀]; congr 1
      show (x : D.host.E) = τ (τ.symm (x : D.host.E)); exact (τ.apply_symm_apply _).symm
    rw [h1, ← lt_one_transport c₀ hAB, hA x'']
    exact hww x'' x (by show (x : D.host.E) = τ (τ.symm (x : D.host.E)); exact (τ.apply_symm_apply _).symm)
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hB hA'
  let c : D.nd.Om ≃+* D.nd.Om := c₀.trans σ.toRingEquiv
  have hcE : ∀ x, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (τ x) := by
    intro x
    show σ (c₀ _) = _
    rw [hc₀, AlgEquiv.commutes]
  have hcA : ∀ y, y ∈ A ↔ c y ∈ A' := by
    intro y
    rw [hAB, ← hσ, ← ValuationSubring.smul_mem_pointwise_smul_iff (g := σ), AlgEquiv.smul_def]
    rfl
  have hcA' : ∀ y, y ∈ A' ↔ c.symm y ∈ A := by
    intro y
    rw [hcA, RingEquiv.apply_symm_apply]
  refine ⟨conjG c τ hcE γ, ⟨c, fun x => hcE x, hcA, fun y => conjG_apply_c c τ hcE γ y⟩, ?_⟩
  refine ⟨conjG_mem_Ine c τ hcE hcA hγ.1, ?_⟩
  intro h hh
  have h1 := hγ.2 (conjG_mem_Ine c.symm τ.symm (symm_alg c τ hcE) hcA' hh)
  rw [← conjG_conjG_symm c τ hcE h]
  refine closure_mono ?_ (image_closure_subset_closure_image (conjG_continuous c τ hcE) ⟨_, h1, rfl⟩)
  rw [← Subgroup.coe_map, MonoidHom.map_closure]
  refine SetLike.coe_subset_coe.mpr (Subgroup.closure_mono ?_)
  rintro _ ⟨g, hg, rfl⟩
  rcases hg with rfl | hg
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (conjG_mem_wild c τ hcE hcA hg)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContragredientPolynomialWeightUniqueHighestWeighStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contragredient_polynomialWeight_unique_highestWeight : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', e.comp (emb t) ≠ ComplexEmbedding.conjugate (e.comp (emb t'))) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (lam : ι → DomWeight n), Formalism.L2.Col.TenIrr (fun t => e.comp (emb t)) lam → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W) (T : W ≃ₗ[K] VV K lam), (∀ γ x, T (ρ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat (L := L) (n := n) γ) (T x)) → ∀ (t : ι) (lam0 : Fin n → ℤ), NX.HWAtF c ρ.dual (emb t) lam0 → lam0 = (lam t).w := by
  first | exact @GlobalTheory.mtRatDual_hw | exact GlobalTheory.mtRatDual_hw | (intros; apply GlobalTheory.mtRatDual_hw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralArcSectionEqualCharStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_integral_arc_section_equalChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c (la.valuation c.F).valuationSubring.subtype), PushInvertible Y.t.G Y.t.PP.L → IsOpen (abLocus Y.t.G) → Y.N4 → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a' n → f ∈ cusp Xo c U a' n → (∀ (T₁ : CDVR) (io₁ : c.F →+* T₁.Fr), (∀ k : c.F, io₁ k ∈ (algebraMap T₁.V T₁.Fr).range) → ∀ y₁ : IntFr Xo c T₁ io₁, (letI := io₁.toAlgebra; ExtIn Y (abLocus Y.t.G) T₁ io₁ y₁.1.x) → evI y₁ f ∈ (algebraMap T₁.V T₁.Fr).range) → ∀ (T : CDVR) (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → (∃ κ : T.Fr →+* ℂ, κ.comp io = c.F.val.toRingHom) → ∀ (b : (la.valuation c.F).valuationSubring →+* T.V), (algebraMap T.V T.Fr).comp b = io.comp (la.valuation c.F).valuationSubring.subtype → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (a : ArcIn Dw l (la.valuation c.F).valuationSubring.subtype T.V b) (y' : Sp T.V ⟶ Y.X), y' ≫ Y.s = spMap b → Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id T.V) ϖ y' → ∀ (y : IntFr Xo c T io) (z : Sp T.Fr ⟶ Xo.XF c), (letI := io.toAlgebra; z ≫ pullback.fst _ _ = y.1.x) → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' → evI y f ∈ (algebraMap T.V T.Fr).range := by
  first | exact @GlobalTheory.GoodTransfer.inV_of_arc_of_extIn | exact GlobalTheory.GoodTransfer.inV_of_arc_of_extIn | (intros; apply GlobalTheory.GoodTransfer.inV_of_arc_of_extIn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormSmoothSpanNormLeShortRationalVectorStatement
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormSmoothSpan_norm_le_shortRationalVector : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (π : CuspSub E a), π.IsUnitary → ∀ φ : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → ∀ l : List (Lie E a),
    ∀ L : Set (Fin a → Af E), IsCompact L → ∀ C₀ : Set (GA E a), IsCompact C₀ → ∀ N : ℕ, ∃ C : ℝ,
      ∀ g : GA E a, ∀ c ∈ C₀, ∀ ξ : Fin a → E, ξ ≠ 0 →
        (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)) ∈ L →
          ‖(GlobalTheory.GLFin.word l φ).1 (g * c)‖ ≤
            C * (‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)‖ ^ (a * Module.finrank ℚ E) /
              (ideleModule E (GeneralLinearGroup.det g) : ℝ)) ^ N := by
  first | exact @GlobalTheory.MSpanDecay.norm_le_of_short_vector_mspanR | exact GlobalTheory.MSpanDecay.norm_le_of_short_vector_mspanR | (intros; apply GlobalTheory.MSpanDecay.norm_le_of_short_vector_mspanR <;> assumption)
end

