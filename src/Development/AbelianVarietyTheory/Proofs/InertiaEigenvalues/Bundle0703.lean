module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToAmbCoefH1EqCoefAmbToAmb
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VanishOfLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPresTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0691
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeUsedPropertiesOfAdmitted
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0267
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def kerOp {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (F : GA E a → ℂ) :
    GA E a → ℂ := fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν

structure IsBCC (F : GA E a → ℂ) : Prop where
  cont : Continuous F
  bdd : ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C
  cusp : IsCuspidal F
  left : ∀ γ g, F (ratGL E a γ * g) = F g


variable (E a) in
def lieBasis : Module.Basis (Fin (Module.finrank ℝ (Lie E a))) ℝ (Lie E a) := Module.finBasis ℝ (Lie E a)


variable (E a) in
def lieCoord (i : Fin (Module.finrank ℝ (Lie E a))) : Lie E a →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap ((lieBasis E a).coord i))

def adCoef (γ : GL (Fin a) (Cinf E)) (p : Fin (Module.finrank ℝ (Lie E a)) × Fin (Module.finrank ℝ (Lie E a))) : ℂ :=
  lieCoord E a p.1 (toL ((γ⁻¹).val * Matrix.of (lieBasis E a p.2) * γ.val))

theorem sum_lieCoord (X : Lie E a) : ∑ i, ((lieBasis E a).coord i X) • lieBasis E a i = X :=
  (lieBasis E a).sum_repr X

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameRelationCocycleSquareZeroInertiaStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_relation_cocycle_squareZero_inertia : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∀ (k : ℕ), normV v % (2 * l ^ k) = 1 → ∀ (M : ℕ) (d : G F Ω →* Multiplicative (ZMod (l ^ M))) (γ σ : G F Ω), 1 ≤ M → IsOpen (d.ker : Set (G F Ω)) → γ ∈ Ine (F := F) A → d γ = Multiplicative.ofAdd 1 → IsFrob A (normV v) σ → ∀ (R : Type) [CommRing R] (W : Type) [AddCommGroup W] [Module R W] [TopologicalSpace W] [DiscreteTopology W] (ρ : Representation R (G F Ω) W) (a b : R), (∀ m : W, (l ^ k) • m = 0) → b * b = 0 → (∀ τ ∈ Ine (F := F) A, ∀ m, ρ τ m = m + (((Multiplicative.toAdd (d τ)).val : R) * b) • m) → (∀ m, ρ σ m = m + a • m) → ∀ z : Z1 ρ, a • z.1 γ = b • z.1 σ ∧ (b = 0 → z.1 γ = 0 → ∀ τ ∈ Ine (F := F) A, z.1 τ = 0) := by
  first | exact @GlobalTheory.TameRelation.tame_relation | exact GlobalTheory.TameRelation.tame_relation | (intros; apply GlobalTheory.TameRelation.tame_relation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedLatticeCohomologyTheoremTOP
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
open GlobalTheory.PhiGam GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.TopBridge

theorem freeH_of_vanish_euler : Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.Vanish → S.FreeH := by
  intro heul l _ P S hV
  obtain ⟨hs, ht, -, -, -⟩ := S.hyp
  obtain ⟨hDVR, -, -, hA, hF, hFr⟩ := GlobalTheory.CoefInt.integers_laws l S.LL
  haveI := hDVR
  haveI := hFr
  exact GlobalTheory.FreeCoh.free_and_tensIso_gal S.Γ hs.2.2.2.2.2 hA hF
    (GlobalTheory.LocalIntegers.isOpen_integers l S.LL)
    (fun U hU => GlobalTheory.FreeCoh.pow_mul_mem_nhds S.LL S.Γ.lam hs.2.2.2.2.2 U hU)
    ht.2.2.1.1 (GlobalTheory.AdmClasses.not_isUnit_integers l S.LL) hV.1 hV.2 ht.1 hs.2.2.1
    (fun M _ _ _ π hlm hlc h0 h2 => _root_.GlobalTheory.EulerFree.card_H1_eq_pow heul l S.K S.O M π hlm hlc h0 h2)

theorem stmtAt_of_real (hdual : Formalism.GaloisCohomology.LocalTateDualityK) (heul : Formalism.GaloisCohomology.LocalEulerCharK)
    {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (htied : Nonempty (LocTied l P AI))
    (hreal : ∀ S : TopSit P, S.Real)
    (hbk : ∀ K LL : FinExt l, CaseA K LL → tableLineDegreeTwo.BlochKatoJumpDimension (P.PD K) (LL := ↥LL.1) (O := ↥(OL LL)) (IK K)) :
    GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.ErrorExponentStatement P := by
  intro K LL n r _ emb D Γ hs ht h1 h2 h3
  let S : TopSit P := ⟨K, LL, n, r, emb, D, Γ, ⟨hs, ht, h1, h2, h3⟩⟩
  have hCC : S.CrysCalc := GlobalTheory.TopSteps.CrysRules.crysCalc AI htied S
  have hR : S.Real := hreal S
  have hV : S.Vanish := GlobalTheory.TopVanish.vanish_of_real hdual S hR
  have hF : S.FreeH := freeH_of_vanish_euler heul S hV
  have hCl : S.Closed := GlobalTheory.AdmClosure.admissible_closed S
  have hStd : S.StdAdm := GlobalTheory.TopSteps.StdAdm.stdAdm S hCC hCl
  have hL0 : S.Lem0 S.Γ.W₀ := (GlobalTheory.AdmClasses.admissibleLocalSituation_admissible_classes S hCl hStd).1
  have hFS : S.FSummand :=
    GlobalTheory.TopSteps.FinSummandJumps.fSummand S (hbk K LL hs.2.1) hCC hV hF
  have hFA : S.FinAdm :=
    GlobalTheory.FiniteAdm.finAdm S hCC (GlobalTheory.FontaineExtensionCriteria.extCrys_of_tied P AI htied) hCl hStd hL0
  have hPsi : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi := GlobalTheory.PsiShiftProof.lemmaPsi
  have hRB : S.ResBound S.Γ.W₀ S.D.dsum := GlobalTheory.ResidueBound.resBound_dsum hPsi S hR hL0
  refine ⟨hV.1, hV.2, hF.1, hFS, fun X _ _ _ => ⟨hF.2 X, ?_⟩⟩
  exact GlobalTheory.AdmFinite.cls_eq_H1fX S hL0 hF hFS hFA hRB X

theorem twistedLatticeCohomology_theoremTOP : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    tableLineDegreeTwo.Stmt D HW F Cm := by
  intro D HW F Cm hA l _ K LL hK lam hlam
  have htied : Nonempty (LocTied l (D.loc l) (D.locA l)) := ⟨D.locT l⟩
  have h18 := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h19 := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hreal : ∀ S : TopSit (D.loc l), S.Real := fun S =>
    GlobalTheory.BasePairs.real_of_presented (D.locA l) (HW l) (F l) S
      (GlobalTheory.RedFun.realD (D.locA l) (HW l) (F l) S)
      (_root_.GlobalTheory.WachQN.qN_of_admitted D HW F Cm hA l S.K S.LL S.hyp.1.2.1)
      (GlobalTheory.TopSteps.CrysRules.crysCalc (D.locA l) htied S)
  exact _root_.GlobalTheory.TopDict.topCore_of_typings (D.loc l) (D.locA l) htied (HW l)
    (stmtAt_of_real h18.1 h18.2 (D.loc l) (D.locA l) htied hreal (fun K' LL' hc => h19 l K' LL' hc))
    (GlobalTheory.TopSteps.CharVanish.stmt_of_real (D.loc l) (D.locA l) htied hreal)
    (GlobalTheory.TopSteps.admissibleUntwistedCharUnramified_of_residueRealisation (D.loc l) (D.locA l) htied hreal)
    K LL hK lam hlam

end GlobalTheory.TopBridge
end

