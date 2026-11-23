module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0885
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0884
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0874
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0855
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFourierCoefficientsConjugateTuples
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoreConstantsEqVacuumIdentityUpToPhase
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeightOfPointwise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0888
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSecond
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedFiniteDatumFourierExpansionChainless
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0811
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActExtLApply
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

noncomputable section
namespace GlobalTheory.UseLoc.Cases.AdmW

open GlobalTheory.AdmLoc

section Ext
variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
  (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X] (χ₁ : G →* Oˣ) (z : G → ↥L.T ⊗[O] X)

def actExtL (g : G) : ((↥L.T ⊗[O] X) × O) →ₗ[O] ((↥L.T ⊗[O] X) × O) :=
  LinearMap.prod ((actT L g).rTensor X ∘ₗ LinearMap.fst O _ O +
      (LinearMap.id : O →ₗ[O] O).smulRight (((χ₁ g : Oˣ) : O) • z g) ∘ₗ LinearMap.snd O _ O)
    ((((χ₁ g : Oˣ) : O) • (LinearMap.id : O →ₗ[O] O)) ∘ₗ LinearMap.snd O _ O)

theorem actExtL_apply (g : G) (p : (↥L.T ⊗[O] X) × O) : actExtL L X χ₁ z g p = tableLineDegreeTwo.actExt L X χ₁ z g p := by
  simp [actExtL, tableLineDegreeTwo.actExt, mul_comm]

variable {L X χ₁ z}

variable (L X χ₁ z)

theorem actExtL_ker (lam : O) (a : ℕ) (hX : ∀ x : X, lam ^ a • x = 0) (g : G) :
    tableLineDegreeTwo.kerExt L X lam a ≤ (tableLineDegreeTwo.kerExt L X lam a).comap (actExtL L X χ₁ z g) := by
  have hT : ∀ m : ↥L.T ⊗[O] X, lam ^ a • m = 0 := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul t x => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hX, TensorProduct.tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  rintro ⟨m, y⟩ ⟨hm, hy⟩
  simp only [Submodule.mem_bot] at hm
  subst hm
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [Submodule.mem_comap, actExtL_apply]
  refine ⟨?_, ?_⟩
  · show _ ∈ (⊥ : Submodule O (↥L.T ⊗[O] X))
    rw [Submodule.mem_bot]
    simp only [tableLineDegreeTwo.actExt, map_zero, zero_add]
    rw [mul_smul, hT, smul_zero]
  · show _ ∈ Ideal.span {lam ^ a}
    simp only [tableLineDegreeTwo.actExt]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

theorem kerExt_kill (lam : O) (a : ℕ) (hX : ∀ x : X, lam ^ a • x = 0)
    (m : ((↥L.T ⊗[O] X) × O) ⧸ tableLineDegreeTwo.kerExt L X lam a) : lam ^ a • m = 0 := by
  have hT : ∀ m : ↥L.T ⊗[O] X, lam ^ a • m = 0 := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul t x => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hX, TensorProduct.tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine ⟨?_, ?_⟩
  · show _ ∈ (⊥ : Submodule O (↥L.T ⊗[O] X))
    rw [Submodule.mem_bot]
    exact hT p.1
  · show _ ∈ Ideal.span {lam ^ a}
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end Ext
end GlobalTheory.UseLoc.Cases.AdmW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockGLSupportedMemMirabolicSupportedStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockGL_supported_mem_mirabolic_supported : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
      GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)) := by
  first | (exact @GlobalTheory.BlockMirabolic.blockGL_mem_mirS) | (exact GlobalTheory.BlockMirabolic.blockGL_mem_mirS) | (intros; apply GlobalTheory.BlockMirabolic.blockGL_mem_mirS  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumTermsInvariantPrincipalLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

namespace GlobalTheory.PrincClassSum

theorem fin_symm {D : D7} (S : HSp D) (y : Bridge.Gf S) :
    finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) = y :=
  (GlobalTheory.ClassRegroup.finEquiv S).apply_symm_apply y

theorem left_inv {D : D7} {S T : HSp D} (B : Base S T) (hB : B.Good) (hS : S.SigOK) (ψ : Twist D Circle) (hψ : ψ.Good)
    (hQ : B.admitted ψ.Q) (ω : PairRep S T) (hω : B.IsWeil ψ.chi ω) {F : Bridge.Gf S → _} (hF : F ∈ B.formsC ψ)
    (g : GA D T) (γ : GQ S) (y : Bridge.Gf S) :
    series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (Bridge.ratF S γ * y) : GfC S) : GA D S)
        (F (Bridge.ratF S γ * y)) g =
      series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g := by
  have e : finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm (Bridge.ratF S γ * y) : GfC S) : GA D S) =
      Bridge.ratF S γ * finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) *
        ((1 : (GlobalTheory.FlatVecSum.princ B).levJ ψ) : Bridge.Gf S) := by
    rw [fin_symm, fin_symm, OneMemClass.coe_one, mul_one]
  have hm := GlobalTheory.BaseClassSum.series_move (GlobalTheory.FlatVecSum.princ_good hB) hS hψ hQ hω (Subtype.property _) (Subtype.property _)
    γ 1 e (F (Bridge.ratF S γ * y))
  have hl := (B.mem_formsC.1 hF).2 γ y 1
  rw [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at hl
  have hinv : B.act ((γ⁻¹ : GQ S) : GA D S) (B.act (γ : GA D S) (F y)) = F y := by
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [map_one, Units.val_one, inv_one, one_smul] at hm
  rw [hl] at hm ⊢
  rw [show (GlobalTheory.FlatVecSum.princ B).act = B.act from rfl, hinv] at hm
  exact congrFun hm g

set_option maxHeartbeats 8000000 in
theorem right_inv {D : D7} {S T : HSp D} (B : Base S T) (hB : B.Good) (hS : S.SigOK) (ψ : Twist D Circle) (hψ : ψ.Good)
    (hQ : B.admitted ψ.Q) (ω : PairRep S T) (hω : B.IsWeil ψ.chi ω) {F : Bridge.Gf S → _} (hF : F ∈ B.formsC ψ)
    (g : GA D T) (k : Bridge.Gf S) (hk : k ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ) (y : Bridge.Gf S) :
    series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (y * k) : GfC S) : GA D S)
        (F (y * k)) g =
      series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g := by
  obtain ⟨hle, hlam⟩ := _root_.GlobalTheory.FlatVecSum.princ_levJ_le_levLam_eq B hB ψ hQ
  have e : finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm (y * k) : GfC S) : GA D S) =
      Bridge.ratF S 1 * finPt S (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) *
        ((⟨k, hk⟩ : (GlobalTheory.FlatVecSum.princ B).levJ ψ) : Bridge.Gf S) := by
    rw [fin_symm, fin_symm, (Bridge.ratF S).map_one, one_mul]
  have hm := GlobalTheory.BaseClassSum.series_move (GlobalTheory.FlatVecSum.princ_good hB) hS hψ hQ hω (Subtype.property _) (Subtype.property _)
    1 ⟨k, hk⟩ e (F (y * k))
  have hl := (B.mem_formsC.1 hF).2 1 y ⟨k, hle hk⟩
  rw [(Bridge.ratF S).map_one, one_mul, OneMemClass.coe_one, map_one, Module.End.one_apply] at hl
  rw [show (GlobalTheory.FlatVecSum.princ B).act = B.act from rfl, inv_one, OneMemClass.coe_one, map_one,
    Module.End.one_apply, hlam k hk] at hm
  rw [hl] at hm ⊢
  rw [LinearMap.map_smul, LinearMap.map_smul, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at hm
  rw [LinearMap.map_smul]
  exact congrFun hm g

theorem terms_inv : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ F ∈ B.formsC ψ, ∀ g : GA D T,
      (∀ (γ : GQ S) (y : Bridge.Gf S),
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (Bridge.ratF S γ * y) : GfC S) : GA D S)
          (F (Bridge.ratF S γ * y)) g =
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g) ∧
      ∀ k ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ, ∀ y : Bridge.Gf S,
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm (y * k) : GfC S) : GA D S)
          (F (y * k)) g =
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat ψ) (((GlobalTheory.ClassRegroup.finEquiv S).symm y : GfC S) : GA D S) (F y) g :=
  fun B hB hS ψ hψ hQ ω hω _ hF g =>
    ⟨fun γ y => left_inv B hB hS ψ hψ hQ ω hω hF g γ y, fun k hk y => right_inv B hB hS ψ hψ hQ ω hω hF g k hk y⟩

end GlobalTheory.PrincClassSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CondExpEqZeroOfNotMem
section
noncomputable section

open NumberField IsDedekindDomain Formalism.UG

namespace GlobalTheory.RamShift

variable {E : Type} [Field E] [NumberField E]

def CondOne (w : HeightOneSpectrum (𝓞 E)) (c : w.adicCompletion E) : Prop :=
  ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (c * x * y))) : ℂ) = 1) ↔ x ∈ Ov E w


open Classical in
def condExp (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E)) : ℤ :=
  if CondOne w 1 then 0
  else if h : ∃ k : ℤ, CondOne w ((ϖ w ^ k : (w.adicCompletion E)ˣ) : w.adicCompletion E) then h.choose else 0


variable (E) in
def badSet : Finset (HeightOneSpectrum (𝓞 E)) := (GlobalTheory.JSW.psiLoc_conductor_eventually E).choose

theorem condOne_one_of_notMem {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ badSet E) : CondOne w 1 := by
  intro x
  simp only [one_mul]
  exact (GlobalTheory.JSW.psiLoc_conductor_eventually E).choose_spec w hw x

theorem condExp_eq_zero_of_notMem (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ badSet E) : condExp ϖ w = 0 := by
  classical
  rw [condExp, if_pos (condOne_one_of_notMem hw)]


open Classical in
def shiftFn (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (w : HeightOneSpectrum (𝓞 E)) : Fin (m + 1) → ℤ :=
  if w ∈ T then 0 else fun i : Fin (m + 1) => condExp ϖ w * ((m : ℤ) - ((i : ℕ) : ℤ))

theorem shiftFn_mem_badSet (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E))
    (h : shiftFn m T ϖ w ≠ 0) : w ∈ badSet E := by
  classical
  by_contra hw
  apply h
  unfold shiftFn
  split_ifs
  · rfl
  · funext i
    simp [condExp_eq_zero_of_notMem ϖ hw]


open Classical in
def shift (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) :
    GlobalTheory.CellDec.abelian₂ E (m + 1) T :=
  ⟨Finsupp.onFinset (badSet E) (shiftFn m T ϖ) (shiftFn_mem_badSet m T ϖ), fun w hw => by
    rw [Finsupp.onFinset_apply, shiftFn, if_pos hw]⟩

theorem shift_apply (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    (shift m T ϖ).1 w = shiftFn m T ϖ w := by
  classical
  simp only [shift, Finsupp.onFinset_apply]

theorem shift_apply_of_notMem (m : ℕ) {T : Finset (HeightOneSpectrum (𝓞 E))}
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ T) :
    (shift m T ϖ).1 w = fun i : Fin (m + 1) => condExp ϖ w * ((m : ℤ) - ((i : ℕ) : ℤ)) := by
  classical
  rw [shift_apply, shiftFn, if_neg hw]

theorem shift_last (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    (shift m T ϖ).1 w (Fin.last m) = 0 := by
  classical
  rw [shift_apply, shiftFn]
  split_ifs
  · rfl
  · simp

end GlobalTheory.RamShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjThetaClassSumEqRootOfUnityConjTuple
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.GalEqCls

theorem isThClsD_transfer {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ}
    {d d' : Formalism.L2.Pj.DeltaDat Xo c n} (hd : d' = d)
    {Cl Cl' : Type} [Fintype Cl] [Fintype Cl'] (e : Cl ≃ Cl')
    (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (w' : Cl' → (Fin n → LevQ Dw d'.l₂) → c.F)
    (hw : ∀ k, HEq (w k) (w' (e k)))
    (La : Cl → GenLat E n) (La' : Cl' → GenLat E n) (hLa : ∀ k, La' (e k) = La k)
    (Nc : Cl → ℕ) (Nc' : Cl' → ℕ) (hNc : ∀ k, Nc' (e k) = Nc k)
    (gam : Cl → ℕ) (gam' : Cl' → ℕ) (hgam : ∀ k, gam' (e k) = gam k)
    (vol : c.F) (ep : Cl → c.F) (ep' : Cl' → c.F) (hep : ∀ k, ep' (e k) = ep k)
    {Vs : Type} [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (x : Cl → Vs) (x' : Cl' → Vs) (hx : ∀ k, x' (e k) = x k) (f : Rul Xo c)
    (h : IsThClsD Xo c d w La Nc gam vol ep io x f) : IsThClsD Xo c d' w' La' Nc' gam' vol ep' io x' f := by
  subst hd
  intro k _ _ A A₂ hk y y₂ hy
  obtain ⟨vc, hvc, he⟩ := @h k _ _ A A₂ hk y y₂ hy
  refine ⟨fun cl => vc (e.symm cl), fun cl => ?_, ?_⟩
  · obtain ⟨k', rfl⟩ := e.surjective cl
    dsimp only
    rw [e.symm_apply_apply, ← eq_of_heq (hw k'), hLa, hNc, hx]
    exact hvc k'
  · rw [he]
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun k' _ => ?_
    dsimp only
    rw [e.symm_apply_apply, hgam, hep]

theorem galRul_isSum : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∃ (hf : Fixes M.c' ta) (k0 : ℂ), IsRoot1 k0 ∧ ∀ (a b : Tp) (e : M.Cl' a ≃ M.Cl' b), SameCover M a b e → ConjTup R τ (tup a) (tup b) → ∃ (u : M.c'.F) (s : (AE D)ˣ), (u : ℂ) = k0 * ((R.xi (tup b) s : Circle) : ℂ) ∧ ∀ (xs : M.Cl' a → VsV D i M.c'.F) (xs' : M.Cl' b → VsV D i M.c'.F), (∀ k, (xs' (e k) : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (xs k : Pol M.c'.F D.what₂.Tau (Vc D i).rank)) → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M a xs f → u • galRul hf f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧ GlobalTheory.OneMapAll.IsSum M b xs' (u • galRul hf f) := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix hcurve hxi
  have hf : Fixes M.c' ta := ⟨fun φ x => Subtype.ext (by rw [hta]; exact hfix.host φ x),
    fun a => Subtype.ext (by rw [hta]; exact hfix.core ⟨a, T.Q.c.le a.2⟩)⟩
  obtain ⟨k0, hk0, hcxi⟩ := GlobalTheory.T.galoisConj_coverFunction_eq_const_mul_conjTuple D G Pl0 T0 A T R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix hcurve hxi
  have hk0ne : k0 ≠ 0 := by
    rintro rfl
    obtain ⟨n, hn, hkn⟩ := hk0
    rw [zero_pow hn.ne'] at hkn
    exact zero_ne_one hkn
  refine ⟨hf, k0⁻¹, ?_, ?_⟩
  · obtain ⟨n, hn, hkn⟩ := hk0
    exact ⟨n, hn, by rw [inv_pow, hkn, inv_one]⟩
  intro a b e hsame hconj
  obtain ⟨⟨cx, hcx⟩, hU, hdict, -, -, hcl⟩ := id hsame
  obtain ⟨h₂, ka, s1, hka, hev⟩ := hcxi a b cx hcx hU hdict hconj
  obtain ⟨u, s2, w', hu, hw'eq, hw⟩ :=
    _root_.GlobalTheory.ConjDatum.conj_coeff D G Pl0 T0 A T R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix a b e hsame hconj
  obtain ⟨hvol, hep⟩ := _root_.GlobalTheory.ConjScalar.conj_vol_ep D G Pl0 T0 A T R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix a b e hsame hconj
  have hkane : ka ≠ 0 := fun h0 => by
    have h1 : ((ka : ℂ)) = 0 := by rw [h0]; rfl
    rw [hka] at h1
    exact mul_ne_zero hk0ne (Circle.coe_ne_zero _) h1
  have hune : u ≠ 0 := fun h0 => by
    have h1 : ((u : ℂ)) = 0 := by rw [h0]; rfl
    rw [hu] at h1
    exact Circle.coe_ne_zero _ h1
  refine ⟨(ka * u)⁻¹, (s1 * s2)⁻¹, ?_, ?_⟩
  · have e1 : (((ka * u)⁻¹ : M.c'.F) : ℂ) = ((ka : ℂ) * (u : ℂ))⁻¹ := by push_cast; rfl
    rw [e1, hka, hu, map_inv, map_mul, Circle.coe_inv, Circle.coe_mul]
    ring
  intro xs xs' hxs f hfs hsum
  obtain ⟨-, cga, hio⟩ := hP.io
  have hio' := fun v => GlobalTheory.HarmBasis.mem_HHa_of_mem_span subset_rfl (hio.2.2.1 ▸ LinearMap.mem_range_self M.io v)
  obtain ⟨hLev, -, hN⟩ := hP.cov a
  have hδ := hLev.2.2.2.2.2.2.2.1
  have key := GlobalTheory.GalTw.isThClsD_galRul hC _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) M.c' ta hf (Vc D i).rank (M.dδ a) h₂ hN hδ cx
    ka u hkane hune hev (M.Cl' a) (M.w a) w' (M.La a) (M.Nc a) (M.gam a) (M.vol a) (M.ep a) (VsV D i M.c'.F) M.io
    (wtA (κ i)) hio' hw xs (fun k => xs' (e k))
    (fun k => _root_.GlobalTheory.IoConj.io_map_conj D G Pl0 T0 A T R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix (xs k) (xs' (e k)) (hxs k))
    (Vc D i).rank f hfs hsum
  refine ⟨key.1, ?_⟩
  have key2 := key.2
  rw [hvol] at key2
  exact isThClsD_transfer hcx e w' (M.w b) hw'eq (M.La a) (M.La b) (fun k => (hcl k).2.1) (M.Nc a) (M.Nc b)
    (fun k => (hcl k).2.2.1) (M.gam a) (M.gam b) (fun k => (hcl k).2.2.2) (M.vol b) (fun k => ta (M.ep a k)) (M.ep b)
    (fun k => (hep k).symm) M.io (fun k => xs' (e k)) xs' (fun _ => rfl) _ key2

end GlobalTheory.GalEqCls
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoreConstantsEqVacuumIdentityUpToPhaseStatement
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
theorem _root_.GlobalTheory.T.coreConstants_eq_vacuumIdentity_up_to_phase : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → ∃ ph : ℂ, ‖ph‖ = 1 ∧ BaseCc T R i hV ph := by
  first | exact @GlobalTheory.LevelSeries.PinBase.baseCc_of_framePin | exact GlobalTheory.LevelSeries.PinBase.baseCc_of_framePin | (intros; apply GlobalTheory.LevelSeries.PinBase.baseCc_of_framePin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDominantWeightCuspSectionsNoCommonZero
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.BpfUniform

theorem exists_weight_noCommonZero : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (b : (D.host.E →+* ℂ) × ℕ → ℕ) (m : ℕ), Dom b m ∧ LastPos (T.Q.Dw j) b ∧ 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ m ∧ ∀ k, ∀ x ∈ ((T.U j σ).X k).dom, ∃ P ∈ Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) b m), P k x ≠ 0 :=
  exists_weight_of_pointwise GlobalTheory.ScalarPoin.exists_cusp_ne

end GlobalTheory.BpfUniform
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsScalarLevelCoverAnalyticFibreStatement
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
open CategoryTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_levelCover_analyticFibre : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (C : Cover T j σ), C.d.IsLev → C.σ₂.comp C.inc = σ → ∀ (y : FrPt (T.Q.Xo j) T.Q.c (CAt σ)) (y₂ : FrPt C.d.Xo₂ C.d.c₂ (CAt C.σ₂)), (y₂.x : Sp ℂ ⟶ C.d.Xo₂.X) ≫ C.d.r = (y.x : Sp ℂ ⟶ (T.Q.Xo j).X) → (∀ τ i, (y₂.u τ i : Sp (DualNumber ℂ) ⟶ C.d.Xo₂.univ.t.G.left) ≫ C.d.m.φ = (y.u τ i : Sp (DualNumber ℂ) ⟶ (T.Q.Xo j).univ.t.G.left)) → ∃ t : ℂ, t ≠ 0 ∧ (∀ (n : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ f₂ : Rul C.d.Xo₂ C.d.c₂, C.IsPull f f₂ → toC (evR C.d.Xo₂ C.d.c₂ f₂ y₂) = t ^ n * toC (evR (T.Q.Xo j) T.Q.c f y)) ∧ ∀ (r g : ℕ) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 (T.Q.Dw j)) (x : Frame X.Ψ r) (L : Lt D.host.E r) (mk : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ ϑ : (Fin g → ℂ) → ℂ, (letI : Algebra T.Q.c.F ℂ := σ.toAlgebra; ∃ A : AnFib X bas idx e x L y, A.Marked mk ∧ A.Reads 1 y.s ϑ) → (letI : Algebra C.d.c₂.F ℂ := C.σ₂.toAlgebra; ∃ A₂ : AnFib X bas idx e x L y₂, A₂.Reads 1 y₂.s (fun z => t * ϑ z)) := by
  first | exact @GlobalTheory.CoverFibScalar.exists_scalar_fib | exact GlobalTheory.CoverFibScalar.exists_scalar_fib | (intros; apply GlobalTheory.CoverFibScalar.exists_scalar_fib <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCosetRepresentativesLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section
namespace GlobalTheory.LevReps

theorem reps : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ψ : Twist D Circle), B.admitted ψ.Q →
    ∃ F : Finset (Bridge.Gf S), (∀ u ∈ F, u ∈ B.levJ ψ) ∧
      ∀ κ ∈ B.levJ ψ, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ (GlobalTheory.FlatVecSum.princ B).levJ ψ := by
  first
  | exact @_root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ
  | exact _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ
  | (apply _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ <;> assumption)
  | (intros; apply _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FirstBlocksReduction.exists_reps_levJ ..)

end GlobalTheory.LevReps
end
end

