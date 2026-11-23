module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0849
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedThetaGeneratorEqClassSumIntegralForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0850
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicLevelCharacterEqTwistLevelCharacter
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0806
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0851

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

noncomputable section

namespace GlobalTheory.UnfoldRows

open Matrix

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem single_last_vecMul {m : ℕ} {R : Type} [CommRing R] (M : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    (Pi.single (Fin.last m) 1 : Fin (m + 1) → R) ᵥ* M = M (Fin.last m) := by
  funext j
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

theorem algebraMap_comp_single {m : ℕ} :
    (algebraMap E (Ad E) ∘ (Pi.single (Fin.last m) 1 : Fin (m + 1) → E)) = Pi.single (Fin.last m) 1 := by
  funext j
  by_cases h : j = Fin.last m
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem lastRow_eq {m : ℕ} (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow g = Matrix.vecMul (algebraMap E (Ad E) ∘ (Pi.single (Fin.last m) 1 : Fin (m + 1) → E)) g.val := by
  rw [algebraMap_comp_single, single_last_vecMul]
  rfl

theorem det_posM_eq_one {R : Type} [CommRing R] {a : ℕ} {ι : Type} [Fintype ι] {p : ι → Fin a × Fin a}
    (hp : ∀ t, (p t).1 < (p t).2) (x : ι → R) : (1 + posM p x).det = 1 := by
  have hz : ∀ i j : Fin a, j ≤ i → posM p x i j = 0 := by
    intro i j hij
    simp only [posM, Matrix.sum_apply, Matrix.single_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨rfl, rfl, -⟩
    exact absurd (hp t) (not_lt.2 hij)
  have hT : (1 + posM p x).IsUpperTriangular := by
    intro i j hij
    have hne : i ≠ j := ne_of_gt hij
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, hz i j (le_of_lt hij), add_zero]
  rw [Matrix.det_of_isUpperTriangular hT]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Matrix.add_apply, Matrix.one_apply_eq, hz i i le_rfl, add_zero]

theorem detAbs_of_det_one {a : ℕ} (u : GA E a) (hu : (u : Matrix (Fin a) (Fin a) (Ad E)).det = 1) :
    GlobalTheory.RSnm.detAbs u = 1 := by
  have h : GeneralLinearGroup.det u = 1 := Units.ext (by rw [GeneralLinearGroup.val_det_apply, hu, Units.val_one])
  simp [GlobalTheory.RSnm.detAbs, h]

theorem rows_main : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ),
    (∀ (γ : GL (Fin (m + 1)) E) (g : GA E (m + 1)), GlobalTheory.ZEul.lastRow (ratGL E (m + 1) γ * g) =
      Matrix.vecMul (algebraMap E (Ad E) ∘ Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) γ.val) g.val) ∧
    (∀ g : GA E (m + 1), GlobalTheory.ZEul.lastRow g = Matrix.vecMul (algebraMap E (Ad E) ∘ (Pi.single (Fin.last m) 1 : Fin (m + 1) → E)) g.val) ∧
    (∀ γ : GL (Fin (m + 1)) E, IsMir m γ → Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) γ.val = Pi.single (Fin.last m) 1) ∧
    (∀ (r l : ℕ) (y : UnipotentBlockColumnIndex (m + 1) r l → Ad E) (g : GA E (m + 1)), GlobalTheory.ZEul.lastRow (blkU y * g) = GlobalTheory.ZEul.lastRow g ∧
      GlobalTheory.RSnm.detAbs (blkU y * g) = GlobalTheory.RSnm.detAbs g) ∧
    (∀ (X : GroundTheory.Automorphic.FourierWhittaker.Pos (m + 1) → Ad E) (g : GA E (m + 1)),
      GlobalTheory.RSnm.detAbs (uGL X * g) = GlobalTheory.RSnm.detAbs g) := by
  intro E _ _ _ m
  refine ⟨?_, lastRow_eq, ?_, ?_, ?_⟩
  · intro γ g
    rw [lastRow_eq, GlobalTheory.ThetaUnfold.vecMul_ratGL_mul]
  · intro γ hγ
    rw [single_last_vecMul]
    funext k
    have := hγ (Fin.last m) k (Or.inl (by simp))
    rw [this]
    by_cases h : k = Fin.last m
    · subst h; simp
    · simp [Matrix.one_apply, Pi.single_apply, h, Ne.symm h]
  · intro r l y g
    have hp : ∀ t : UnipotentBlockColumnIndex (m + 1) r l, t.1.1 < t.1.2 := fun t => by
      have := t.2; exact Fin.lt_def.2 (by omega)
    refine ⟨?_, ?_⟩
    · funext j
      change ((blkU y).val * g.val) (Fin.last m) j = g.val (Fin.last m) j
      rw [blkU, posU_val, add_mul, one_mul, Matrix.add_apply, add_eq_left]
      simp only [posM, Finset.sum_mul, Matrix.sum_apply]
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [Matrix.single_mul_apply_of_ne]
      intro h
      have h1 := t.2.1
      have h2 := t.1.2.isLt
      have h3 := t.2.2.1
      rw [← h] at h1
      simp only [Fin.val_last] at h1
      omega
    · rw [GlobalTheory.RSnm.detAbs_mul, detAbs_of_det_one, one_mul]
      rw [blkU, posU_val]
      exact det_posM_eq_one (p := Subtype.val) hp y
  · intro X g
    rw [GlobalTheory.RSnm.detAbs_mul, detAbs_of_det_one, one_mul]
    rw [GroundTheory.Automorphic.FourierWhittaker.coe_uGL, GroundTheory.Automorphic.FourierWhittaker.det_uMat]

end GlobalTheory.UnfoldRows
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRootsInField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.TwInputs

variable {D : D7} {ρ : Setup D.ntw}

theorem de_mem_eO (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (z : (AE D)ˣ) :
    (((ρ.B i j b).de.chi z : Circle) : ℂ) ∈ (ρ.eO i b).range := by
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
  refine ⟨algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i), ?_⟩
  rw [hρ.delta i j b]
  exact (charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm

theorem e_mem_eO (ρ : Setup D.ntw) (i : D.ntw.Tw) (b : Bool) {a : FractionRing (D.ntw.O i)} {n : ℕ}
    (hn : n ≠ 0) (h : ρ.e i b a ^ n = 1) : ρ.e i b a ∈ (ρ.eO i b).range := by
  have h1 : a ^ n = 1 := (ρ.e i b).injective (by rw [map_pow, h, map_one])
  have hi : IsIntegral (D.ntw.O i) a := ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [h1]⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact ⟨y, rfl⟩

theorem typeCharacterExtension_value_mem_coefficientRing {hρ : ρ.Good} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {rd : Rd ρ D.nexp i j b}
    (T : CellTie hρ D.nexp rd) (g : G0 (ρ.B i j b).G.Pg (Wc D j).rank) :
    ((ext1 (ρ.B i j b).G.P.H (⇑(ρ.B i j b).G.P.chi) g : ℂˣ) : ℂ) ∈ (ρ.eO i b).range := by
  unfold ext1
  split_ifs with h
  · obtain ⟨g', rfl⟩ := (ρ.eG i j b).surjective g
    have e1 := T.psiU_eq ⟨g', (T.U_eq g').1 h⟩ h
    have hfin : ((ρ.B i j b).G.P.chi ⟨ρ.eG i j b g', h⟩) ^ Nat.card (ρ.B i j b).G.P.H = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    rw [e1]
    refine e_mem_eO ρ i b (n := Nat.card (ρ.B i j b).G.P.H) Nat.card_pos.ne' ?_
    rw [← e1, ← Units.val_pow_eq_pow_val, hfin, Units.val_one]
  · exact one_mem _

theorem card_residueField_of_type {k : Fin 2} {PP : Pl D.host.E} (h : PP ∈ placesOver D.host.E (D.host.g k)) :
    Nat.card (kP PP) = D.host.g k :=
  GlobalTheory.SplitResidueCard.card_quotient_of_ncard (F := D.host.E) (D.host.g_prime k) (D.nd.g_split k) PP h

theorem muC_mem_eO (hρ : ρ.Good)
    (hr : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange)
    (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {PP : Pl D.host.E} (hPP : PP ∈ (ρ.B i j b).G.Pg) (w : (kP PP)ˣ) :
    (((ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ∈ (ρ.eO i b).range := by
  obtain ⟨k, hk⟩ := hρ.Pg i j b PP hPP
  have hw : w ^ (D.host.g k - 1) = 1 := by
    rw [← card_residueField_of_type hk, ← Nat.card_units]
    exact pow_card_eq_one'
  have hz : (((ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) ^ (D.host.g k * (D.host.g k - 1)) = 1 := by
    rw [mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, hw, map_one, Units.val_one, one_pow]
  obtain ⟨x, hx⟩ := hr k _ hz
  have h2 := (D.host.g_prime k).two_le
  have e : ρ.e i b (sideEmb D.ntw i b x) = (((ρ.B i j b).G.muC PP w : ℂˣ) : ℂ) := (hρ.e_LL0 i b x).trans hx
  rw [← e] at hz ⊢
  exact e_mem_eO ρ i b (Nat.mul_ne_zero (by omega) (by omega)) hz

theorem locC_mem {t : Twist D Circle} (ht : t.Good) {O : Subring ℂ} (h : ∀ x, ((t.chi x : Circle) : ℂ) ∈ O)
    (PP : Pl D.host.E) (w : (kP PP)ˣ) : ((t.locC PP w : ℂˣ) : ℂ) ∈ O := by
  unfold Twist.locC
  split_ifs with hq
  · obtain ⟨x, hx⟩ := GlobalTheory.ConjTwist.exists_isLocUnit (ht.split.isIdemAt hq) w
    show ((t.res PP w : Circle) : ℂ) ∈ _
    rw [← hx.eq (ht.res PP hq)]
    exact h x
  · simp

theorem levLam_mem_eOk {hρ : ρ.Good}
    (hr : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange)
    {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {rd : Rd ρ D.nexp i j b} (T : CellTie hρ D.nexp rd) {k Q ψ} (hψ : TwOK i k Q ψ)
    (x : (ρ.B i j b).levJ (ρ.tw i b k Q ψ)) :
    (((ρ.B i j b).levLam (ρ.tw i b k Q ψ) x : ℂˣ) : ℂ) ∈ (ρ.eOk i b k).range := by
  obtain ⟨hg, -, hv⟩ := GlobalTheory.TwistGood.tw_good D _ _ ρ hρ i j b k Q ψ hψ
  have hle := hρ.range_le i b k
  have e : (ρ.B i j b).levLam (ρ.tw i b k Q ψ) x =
      levFn (ρ.B i j b).F.βS ((ρ.B i j b).levS (ρ.tw i b k Q ψ)) (Formalism.UG.bc (Lev.swapAE D) x.1.1) := by
    unfold Base.levLam Lev.levCharAfE
    rfl
  rw [e]
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod]
  refine mul_mem (mul_mem (hle (typeCharacterExtension_value_mem_coefficientRing T _)) (prod_mem fun PP hPP => prod_mem fun _ _ => hle (muC_mem_eO hρ hr i j b hPP _)))
    (prod_mem fun PP _ => ?_)
  rw [MonoidHom.mul_apply, Units.val_mul]
  exact mul_mem (hle (locC_mem (hρ.base i j b).de (de_mem_eO hρ i j b) PP _))
    (locC_mem (O := (ρ.eOk i b k).range) hg (fun z => (hv z).elim fun u hu => ⟨u, hu.symm⟩) PP _)

theorem admT4_of_full_compatibility : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd →
    (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) →
    ∀ E : IntegralHeckeForms.XD D, IntegralHeckeForms.admT4 D.nexp E := by
  intro D ρ hρ rd hT hr E i _ j hj b k Q ψ hψ Sg _
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨j', rfl⟩ : ∃ j' : Fin D.R.m, j = (j' : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  have T := hT.tie i j' b
  rw [IntegralHeckeForms.ThPsi, Submodule.span_le]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨d, -, hx⟩ := hx
  have hg := (T.thPsi_iff k Q ψ hψ d x).1 hx
  obtain ⟨F, hF, e⟩ := _root_.GlobalTheory.TwTraceCx.trace_cx D ρ hρ i j' b k Q ψ hψ (levLam_mem_eOk hr T hψ) _ _ _ (T.dat d) _ hg
  obtain ⟨f, hf, rfl⟩ := (T.mtLat_iff k Q ψ hψ F).1 hF
  refine ⟨f, hf, T.injective_rdK k ?_⟩
  rw [T.thP_eq k Q ψ hψ f ⟨x, e⟩]
  exact e.symm

end GlobalTheory.TwInputs

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalInertiaEqZeroPotSemistableDieudonneStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_inertia_eq_zero_potSemistableDieudonne : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw) {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V), GlobalTheory.Pst.IsPst P ρ → ∀ (σ : ↥(Ine (F := E) A)) (q : (↥LL.1)[X]), q.map (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) = (GlobalTheory.Pst.wdPst P ι Bw h hj ρ).charPol (GlobalTheory.WeilDeligne.ineIncl h σ) → ∀ x ∈ GlobalTheory.Pst.Dpst P ρ, Polynomial.aeval (GlobalTheory.Pst.stRep P ρ (GlobalTheory.Pst.weilToGK Bw h (GlobalTheory.WeilDeligne.ineIncl h σ))) q x = 0 := by
  first | exact @GlobalTheory.IneKillsDpst.aeval_stRep_eq_zero | exact GlobalTheory.IneKillsDpst.aeval_stRep_eq_zero | (intros; apply GlobalTheory.IneKillsDpst.aeval_stRep_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicLevelCharacterEqTwistLevelCharacterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicLevelCharacter_eq_twistLevelCharacter : ∀ (D : D7) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i (j.1 + 1) b k Q ψ e W₀ ρ₀ τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) (t : Twist D Circle) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi (Vc D j) D.R.nV), IdFrame hF P → B.F.βS = 1 → (∀ PP, PP ∈ B.G.Pg ↔ ∃ kv, PP = NX.pG D kv) → Function.Injective (NX.pG D) → t.Q = M.QP → B.de.Q = M.DP → ∀ (iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv)) (eG : G0g D.nd ≃* G0 B.G.Pg (Wc D j).rank), (∀ (g : G0g D.nd) kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank), (eG g ⟨NX.pG D kv, h⟩).val a c = iso kv ((g kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c))) → (∀ g, eG g ∈ B.G.P.H ↔ g ∈ D.nexp.U) → D.nexp.U = NX.Uup (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r → Disjoint M.QP M.DP → ∀ (e₀ : FractionRing (D.ntw.O i) →+* ℂ) (ek : NX.Kk D i k →+* ℂ), (∀ x, ek (NX.toKk D i k x) = e₀ x) → NX.IsStdGeneric (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r (D.nexp.psiU i b) → (∀ (u : D.nexp.U) hu, ((B.G.P.chi ⟨eG u, hu⟩ : ℂˣ) : ℂ) = e₀ (D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ)) → (∀ kv (x : (ZMod (D.host.g kv.1))ˣ) (z : (kP (NX.pG D kv))ˣ), (z : kP (NX.pG D kv)) = iso kv x → ((B.G.muC (NX.pG D kv) z : ℂˣ) : ℂ) = e₀ (τ kv x : (FractionRing (D.ntw.O i))ˣ)) → (∀ PP ∈ M.QP, ∀ u : 𝓞 D.host.E, u ∉ PP.asIdeal → ∀ z : (kP PP)ˣ, (z : kP PP) = Ideal.Quotient.mk PP.asIdeal u → ((t.resC PP z : ℂˣ) : ℂ) = ek (NX.ofOk D i k (NX.tameVal ψ PP e u).1)) → (∀ PP ∈ M.DP, ∀ u : 𝓞 D.host.E, u ∉ PP.asIdeal → ∀ z : (kP PP)ˣ, (z : kP PP) = Ideal.Quotient.mk PP.asIdeal u → ((B.de.resC PP z : ℂˣ) : ℂ) = ek (NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) PP (if b then e else -e) u).1)) → ∀ g (h : g ∈ M.J) (h' : frameEquiv P g ∈ B.levJ t), ek ((M.χ ⟨g, h⟩ : (NX.Kk D i k)ˣ) : NX.Kk D i k) = ((B.levLam t ⟨frameEquiv P g, h'⟩ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.LevChiRead.levChi_read | exact GlobalTheory.LevChiRead.levChi_read | (intros; apply GlobalTheory.LevChiRead.levChi_read <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AugmentationLengthColengthBound
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

noncomputable section

namespace GlobalTheory.PartialBlock

open GroundTheory.Automorphic.FourierWhittaker (partialCoeff_self coe_blockGL blockMat_apply diagonal_blockGL)

variable {E : Type} [Field E] [NumberField E]

theorem good_top {ψ : AddChar (Ad E) ℂ} {k : ℕ} {φ : GA E (k + 1) → ℂ} (hφ : Continuous φ)
    (hl : ∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g)
    (hv : ∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) :
    Good ψ k φ := by
  refine ⟨hφ, fun γ _ g => hl γ g, ?_, hv⟩
  intro j hj y g
  have he : IsEmpty (UnipotentBlockColumnIndex (k + 1) j j) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
  have hy : y = 0 := Subsingleton.elim _ _
  subst hy
  have hd : dot (eLast (k + 1) j) (0 : UnipotentBlockColumnIndex (k + 1) j j → Ad E) = 0 := by simp [dot]
  rw [hd, AddChar.map_zero_eq_one, one_mul]
  unfold blkU
  rw [posU_zero, one_mul]

theorem good_partialCoeff {k : ℕ} {φ : GA E (k + 1) → ℂ} (hφ : Continuous φ)
    (hl : ∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g)
    (hv : ∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0)
    {m : ℕ} (hm : m ≤ k) : Good (GlobalTheory.StdCharConductor.psi E) m (partialCoeff φ (m + 1)) := by
  induction hm using Nat.decreasingInduction with
  | self => rw [partialCoeff_self]; exact good_top hφ hl hv
  | of_succ m hm ih =>
    rw [← GlobalTheory.WhitCols.colT_partialCoeff hφ (fun γ _ g => hl γ g) (by omega : m + 1 < k + 1)]
    exact GlobalTheory.CuspRep.Generic.good_colT (GlobalTheory.StdCharConductor.stdPsi_psi E) (by omega) ih

theorem blkU_entry {R : Type} [CommRing R] {a r m : ℕ} (y : UnipotentBlockColumnIndex a r m → R) (i k : Fin a) :
    (blkU y : GL (Fin a) R).val i k = (1 : Matrix (Fin a) (Fin a) R) i k +
      if h : (i : ℕ) < r ∧ r ≤ (k : ℕ) ∧ (k : ℕ) ≤ m then y ⟨(i, k), h⟩ else 0 := by
  rw [← posM_block_entry]; rfl

def blkEquiv {n m : ℕ} (h : m + 1 ≤ n) (r : ℕ) : UnipotentBlockColumnIndex n r m ≃ UnipotentBlockColumnIndex (m + 1) r m where
  toFun t := ⟨(⟨t.1.1.1, by have := t.2; omega⟩, ⟨t.1.2.1, by have := t.2; omega⟩), t.2⟩
  invFun t := ⟨(⟨t.1.1.1, by have := t.2; omega⟩, ⟨t.1.2.1, by have := t.2; omega⟩), t.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def blkHom {n m : ℕ} (h : m + 1 ≤ n) (r : ℕ) : (UnipotentBlockColumnIndex (m + 1) r m → Ad E) ≃ₜ+ (UnipotentBlockColumnIndex n r m → Ad E) where
  toFun x := fun t => x (blkEquiv h r t)
  invFun y := fun i => y ((blkEquiv h r).symm i)
  left_inv x := by funext i; simp
  right_inv y := by funext t; simp
  map_add' x y := rfl
  continuous_toFun := continuous_pi fun t => continuous_apply _
  continuous_invFun := continuous_pi fun i => continuous_apply _

theorem blkHom_mem_iff {n m : ℕ} (h : m + 1 ≤ n) (r : ℕ) (x : UnipotentBlockColumnIndex (m + 1) r m → Ad E) :
    blkHom h r x ∈ ratV E (UnipotentBlockColumnIndex n r m) ↔ x ∈ ratV E (UnipotentBlockColumnIndex (m + 1) r m) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun i => c ((blkEquiv h r).symm i), funext fun i => congrFun hc ((blkEquiv h r).symm i)⟩
  · rintro ⟨c, rfl⟩
    exact ⟨fun t => c (blkEquiv h r t), rfl⟩

theorem blockGL_blkU {n m : ℕ} (h : m + 1 ≤ n) (r : ℕ) (x : UnipotentBlockColumnIndex (m + 1) r m → Ad E) :
    (blockGL h (blkU x) : GL (Fin n) (Ad E)) = blkU (blkHom h r x) := by
  refine Units.ext ?_
  ext i j
  rw [coe_blockGL, blockMat_apply, blkU_entry]
  by_cases hi : (i : ℕ) < m + 1
  · by_cases hj : (j : ℕ) < m + 1
    · rw [dite_eq_left hi, dite_eq_left hj, blkU_entry]
      congr 1
      simp only [Matrix.one_apply, Fin.ext_iff]
    · have hne : i ≠ j := fun e => hj (e ▸ hi)
      rw [dite_eq_left hi, dite_eq_right hj, dite_eq_right (by omega), Matrix.one_apply_ne hne, add_zero]
  · rw [dite_eq_right hi, dite_eq_right (by omega), add_zero, Matrix.one_apply]

omit [NumberField E] in
theorem isMir_blockGL {n m : ℕ} (h : m + 1 ≤ n) {γ : GL (Fin (m + 1)) E} (hγ : IsMir m γ) :
    IsMir m (blockGL h γ : GL (Fin n) E) := by
  intro i j hij
  rw [coe_blockGL, blockMat_apply]
  by_cases hi : (i : ℕ) < m + 1
  · by_cases hj : (j : ℕ) < m + 1
    · rw [dite_eq_left hi, dite_eq_left hj, hγ _ _ hij]
      simp only [Matrix.one_apply, Fin.ext_iff]
    · have hne : i ≠ j := fun e => hj (e ▸ hi)
      rw [dite_eq_left hi, dite_eq_right hj, Matrix.one_apply_ne hne]
  · rw [dite_eq_right hi, Matrix.one_apply]

theorem good_restrict {ψ : AddChar (Ad E) ℂ} {n m : ℕ} (h : m + 1 ≤ n) {F : GA E n → ℂ} (hF : Good ψ m F) :
    Good ψ m (fun g : GA E (m + 1) => F (blockGL h g)) := by
  refine ⟨hF.cont.comp (GlobalTheory.RSnm.continuous_blockGL h), ?_, ?_, ?_⟩
  · intro γ hγ g
    have e : (blockGL h (ratGL E (m + 1) γ) : GA E n) = ratGL E n (blockGL h γ) := (diagonal_blockGL h γ).symm
    simp only [map_mul]
    rw [e, hF.left _ (isMir_blockGL h hγ)]
  · intro j hj y g
    have he : IsEmpty (UnipotentBlockColumnIndex (m + 1) j j) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have hd : dot (eLast (m + 1) j) (0 : UnipotentBlockColumnIndex (m + 1) j j → Ad E) = 0 := by simp [dot]
    rw [hd, AddChar.map_zero_eq_one, one_mul]
    unfold blkU
    rw [posU_zero, one_mul]
  · intro r hr hrm g
    have hP := per_blk (r := r) (m := m) hF.cont (fun c g => hF.left _ (isMir_blkU c) g) (blockGL h g)
    rw [← hF.van r hr hrm (blockGL h g), ← avg_equiv _ _ _ _ (isCoLat_ratV E _) (isCoLat_ratV E _) (blkHom h r)
      (blkHom_mem_iff h r) _ hP]
    simp only [map_mul, blockGL_blkU]

theorem good_partialCoeff_blockGL : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ) (hmk : m + 1 ≤ k) (φ : GA E (k + 1) → ℂ),
    Continuous φ → (∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) →
    Good (GlobalTheory.StdCharConductor.psi E) m (fun h => partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ k + 1) h)) := by
  intro E _ _ k m hmk φ hφ hl hv
  exact good_restrict _ (good_partialCoeff hφ hl hv (by omega))

end GlobalTheory.PartialBlock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharPolyInertiaOfPotSemistableEnlargementStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charPoly_inertia_of_potSemistable_enlargement : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) → ∃ (LL' : FinExt (D.nd.l i)) (hL : (D.nbr i w hw).LL.1 ≤ LL'.1), GlobalTheory.Pst.IsPst (D.loc (D.nd.l i)) ((D.nbr i w hw).repE LL' (GlobalTheory.PstLine.upRep hL m (mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w))))) ∧ ∀ (σ : Gw D.nd w) (hσ : (σ : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) (p : (D.nd.O i)[X]), p.map (iotaO D.nd D.naut i) = (GlobalTheory.Pst.wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w)).inePol (σ : GE D.nd) → ((p.map (D.nbr i w hw).toLL).map (IntermediateField.inclusion hL).toRingHom).map ((D.naut.iotaQC i).toRingHom.comp (algebraMap ↥LL'.1 (Om (D.nd.l i)))) = (GlobalTheory.Pst.wdPst (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) ((D.nbr i w hw).repE LL' (GlobalTheory.PstLine.upRep hL m (mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w)))))).charPol (GlobalTheory.WeilDeligne.ineIncl (D.nd.plOm.2 w) ⟨(σ : GE D.nd), hσ⟩) := by
  first | exact @GlobalTheory.PstModel.charPol_upRep_of_isPstAt | exact GlobalTheory.PstModel.charPol_upRep_of_isPstAt | (intros; apply GlobalTheory.PstModel.charPol_upRep_of_isPstAt <;> assumption)
end

