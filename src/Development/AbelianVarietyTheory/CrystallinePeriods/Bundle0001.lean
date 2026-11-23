module

public import Mathlib
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.MemAcris0OfFactorialMul
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.ExistsPowDivFactorial
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.EvalLogAlgebraMap
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.MapEqPadicPowCyclotomicCharacter
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Bundle0002
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps
section
open scoped Formalism.Per

namespace GlobalTheory.AdicMaps

open Formalism

noncomputable section

section Gen
variable {R S : Type} [CommRing R] [CommRing S]

def levMap (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) (n : ℕ) :
    R ⧸ I ^ n →+* S ⧸ J ^ n :=
  Ideal.quotientMap (J ^ n) f (Reformulated.AutPerF.pow_le_comap_pow hf n)

def adicMap (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) :
    AdicCompletion I R →+* AdicCompletion J S :=
  Reformulated.AutPerF.adicMap I J f hf

theorem adicMap_alg (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I ≤ J.comap f) (r : R) :
    adicMap I J f hf (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion J S) (f r) := by
  first | exact @AdicMapAlgebra.Bridge.AdicMaps.adicMap_alg | exact AdicMapAlgebra.Bridge.AdicMaps.adicMap_alg .. | (intros; apply AdicMapAlgebra.Bridge.AdicMaps.adicMap_alg <;> assumption)

abbrev PHat (p : ℕ) (R : Type) [CommRing R] : Type := AdicCompletion (Ideal.span {(p : R)}) R

def padicMap (p : ℕ) (f : R →+* S) : PHat p R →+* PHat p S :=
  Reformulated.AutPerF.adicMap _ _ f (Reformulated.AutPerF.span_natCast_le_comap p f)

theorem padicMap_alg (p : ℕ) (f : R →+* S) (r : R) :
    padicMap p f (algebraMap R (PHat p R) r) = algebraMap S (PHat p S) (f r) := by
  first | exact @PadicMapAlgebra.Bridge.AdicMaps.padicMap_alg | exact PadicMapAlgebra.Bridge.AdicMaps.padicMap_alg .. | (intros; apply PadicMapAlgebra.Bridge.AdicMaps.padicMap_alg <;> assumption)

end Gen

theorem exists_acris_completion (l : ℕ) [Fact l.Prime] :
    ∃ e : Per.Acris l ≃+* AdicCompletion (Ideal.span {(l : Per.Acris0 l)}) (Per.Acris0 l),
      ∀ s : Per.Acris0 l, e (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
        algebraMap (Per.Acris0 l) (AdicCompletion (Ideal.span {(l : Per.Acris0 l)}) (Per.Acris0 l)) s := by
  first | exact @CrisCompletionExists.Bridge.AdicMaps.exists_acris_completion | exact CrisCompletionExists.Bridge.AdicMaps.exists_acris_completion .. | (intros; apply CrisCompletionExists.Bridge.AdicMaps.exists_acris_completion <;> assumption)

theorem coeff_galois (l : ℕ) [Fact l.Prime] (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : Per.Fl l)
    (n : ℕ) (y : Per.OC l)
    (h : PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) y) :
    PreTilt.coeff n (Per.σF g x) =
      Ideal.Quotient.mk (Ideal.span {((l : ℕ) : Per.OC l)}) (Per.σO g y) := by
  first | exact @AdicCoeffGalois.Bridge.AdicMaps.coeff_galois | exact AdicCoeffGalois.Bridge.AdicMaps.coeff_galois .. | (intros; apply AdicCoeffGalois.Bridge.AdicMaps.coeff_galois <;> assumption)

end

end GlobalTheory.AdicMaps
end

-- bundled from Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
section
open Formalism
open scoped Formalism.Per

namespace GlobalTheory.CrisLoc

variable (l : ℕ) [Fact l.Prime]

theorem exists_root_ne_one : ∃ e : Per.Fl l, e.untilt = 1 ∧ e ≠ 1 := by
  first | exact @CrisRootNeOne.Bridge.CrisLoc.exists_root_ne_one | exact CrisRootNeOne.Bridge.CrisLoc.exists_root_ne_one .. | (intros; apply CrisRootNeOne.Bridge.CrisLoc.exists_root_ne_one <;> assumption)

theorem bcris_away (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    IsLocalization.Away (algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1)) (Per.Bcris l) := by
  first | exact @CrisAway.Bridge.CrisLoc.bcris_away | exact CrisAway.Bridge.CrisLoc.bcris_away .. | (intros; apply CrisAway.Bridge.CrisLoc.bcris_away <;> assumption)

theorem bdR_away (b : Per.AinfP l) (hb : Per.kerP l = Ideal.span {b}) :
    IsLocalization.Away (algebraMap (Per.AinfP l) (Per.BdRp l) b) (Per.BdR l) := by
  first | exact @DeRhamAway.Bridge.CrisLoc.bdR_away | exact DeRhamAway.Bridge.CrisLoc.bdR_away .. | (intros; apply DeRhamAway.Bridge.CrisLoc.bdR_away <;> assumption)

theorem mem_fil_neg (b : Per.AinfP l) (hb : Per.kerP l = Ideal.span {b}) (n : ℕ) (x : Per.BdR l) :
    x ∈ Per.FilD l (-(n : ℤ)) ↔ ∃ y : Per.BdRp l,
      x * algebraMap (Per.BdRp l) (Per.BdR l) (algebraMap (Per.AinfP l) (Per.BdRp l) b) ^ n =
        algebraMap (Per.BdRp l) (Per.BdR l) y := by
  first | exact @FiltrationNeg.Bridge.CrisLoc.mem_fil_neg | exact FiltrationNeg.Bridge.CrisLoc.mem_fil_neg .. | (intros; apply FiltrationNeg.Bridge.CrisLoc.mem_fil_neg <;> assumption)

theorem unit_of_root (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    IsUnit (algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1))) := by
  first | exact @UnitOfRootAlt.Bridge.CrisLoc.unit_of_root | exact UnitOfRootAlt.Bridge.CrisLoc.unit_of_root .. | (intros; apply UnitOfRootAlt.Bridge.CrisLoc.unit_of_root <;> assumption)

theorem unit_of_root_aB (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    IsUnit (Per.aB l (Per.tm e - 1)) := by
  first | exact @UnitOfRootLog.Bridge.CrisLoc.unit_of_root_aB | exact UnitOfRootLog.Bridge.CrisLoc.unit_of_root_aB .. | (intros; apply UnitOfRootLog.Bridge.CrisLoc.unit_of_root_aB <;> assumption)

theorem bcris_hom_ext {R : Type*} [CommRing R] {f g : Per.Bcris l →+* R}
    (h : ∀ x : Per.Acris l, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  CrisHomExtUnit.Bridge.CrisLoc.bcris_hom_ext_u l h

theorem exists_mul_pow_eq (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) (b : Per.Bcris l) :
    ∃ (n : ℕ) (x : Per.Acris l), b * algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1)) ^ n = algebraMap (Per.Acris l) (Per.Bcris l) x := by
  first | exact @MulPowEq.Bridge.CrisLoc.exists_mul_pow_eq | exact MulPowEq.Bridge.CrisLoc.exists_mul_pow_eq .. | (intros; apply MulPowEq.Bridge.CrisLoc.exists_mul_pow_eq <;> assumption)

theorem exists_pow_mul_eq_zero (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) {x : Per.Acris l}
    (hx : algebraMap (Per.Acris l) (Per.Bcris l) x = 0) :
    ∃ n : ℕ, algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1) ^ n * x = 0 := by
  first | exact @PowMulEqZero.Bridge.CrisLoc.exists_pow_mul_eq_zero | exact PowMulEqZero.Bridge.CrisLoc.exists_pow_mul_eq_zero .. | (intros; apply PowMulEqZero.Bridge.CrisLoc.exists_pow_mul_eq_zero <;> assumption)

theorem bdR_hom_ext {R : Type*} [CommRing R] {f g : Per.BdR l →+* R}
    (h : ∀ x : Per.BdRp l, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  DeRhamHomExtUnit.Bridge.CrisLoc.bdR_hom_ext_u l h

theorem constantCoeff_root_ne_zero (e : Per.Fl l) (hne : e ≠ 1) :
    WittVector.constantCoeff (Per.tm e - 1 : Per.Ainf l) ≠ 0 := by
  first | exact @RootConstantCoeffNeZero.Bridge.CrisLoc.constantCoeff_root_ne_zero | exact RootConstantCoeffNeZero.Bridge.CrisLoc.constantCoeff_root_ne_zero .. | (intros; apply RootConstantCoeffNeZero.Bridge.CrisLoc.constantCoeff_root_ne_zero <;> assumption)

end GlobalTheory.CrisLoc
end

-- bundled from Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
section
noncomputable section
namespace GlobalTheory.CrisMaps
open Formalism
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

@[irreducible] def frob (l : ℕ) [Fact l.Prime] : Per.Acris l →+* Per.Acris l := Reformulated.AutPerF.Acris.frob l (Per.OC l)

@[irreducible] def gal (g : Per.Gq l) : Per.Acris l →+* Per.Acris l := Reformulated.AutPerF.Acris.map l (Per.σO g)

structure Extends (f : Per.Ainf l →+* Per.Ainf l) (F : Per.Acris l →+* Per.Acris l) : Prop where
  mem : ∀ y ∈ Per.Acris0 l, Per.extP f y ∈ Per.Acris0 l
  env : ∀ s : Per.Acris0 l, F (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
    algebraMap (Per.Acris0 l) (Per.Acris l) ⟨Per.extP f s, mem _ s.2⟩
  alg : ∀ a : Per.Ainf l, F (algebraMap (Per.Ainf l) (Per.Acris l) a) = algebraMap (Per.Ainf l) (Per.Acris l) (f a)

theorem frob_extends (l : ℕ) [Fact l.Prime] : Extends (Per.φA l) (frob l) := by
  unfold frob; first | exact (fun h => ⟨h.mem, h.env, h.alg⟩) (FrobeniusExtendsCris.Bridge.CrisMaps.frob_extends ..)

theorem gal_extends (g : Per.Gq l) : Extends (Per.σA g) (gal g) := by
  unfold gal; first | exact (fun h => ⟨h.mem, h.env, h.alg⟩) (FrobeniusExtendsStructure.Bridge.CrisMaps.gal_extends ..)

theorem frob_gal (g : Per.Gq l) (x : Per.Acris l) : frob l (gal g x) = gal g (frob l x) := by
  unfold frob gal; first | exact @FrobeniusGalois.Bridge.CrisMaps.frob_gal | exact FrobeniusGalois.Bridge.CrisMaps.frob_gal .. | (intros; apply FrobeniusGalois.Bridge.CrisMaps.frob_gal <;> assumption)

theorem φB_algebraMap (l : ℕ) [Fact l.Prime] (x : Per.Acris l) :
    Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (frob l x) := by
  unfold frob; first | exact @FrobeniusPeriodAlgebraMap.Bridge.CrisMaps.φB_algebraMap | exact FrobeniusPeriodAlgebraMap.Bridge.CrisMaps.φB_algebraMap .. | (intros; apply FrobeniusPeriodAlgebraMap.Bridge.CrisMaps.φB_algebraMap <;> assumption)

theorem σB_algebraMap (g : Per.Gq l) (x : Per.Acris l) :
    Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (gal g x) := by
  unfold gal; first | exact @CrisFrobeniusAlgebraMap.Bridge.CrisMaps.σB_algebraMap | exact CrisFrobeniusAlgebraMap.Bridge.CrisMaps.σB_algebraMap .. | (intros; apply CrisFrobeniusAlgebraMap.Bridge.CrisMaps.σB_algebraMap <;> assumption)

end GlobalTheory.CrisMaps
end
end

-- bundled from Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
section
open Formalism
open scoped Formalism.Per

namespace GlobalTheory.RingBasics

section Field
variable {p : ℕ} [Fact p.Prime]

theorem norm_eq_val (x : ℂ_[p]) : ‖x‖ = ((Valued.v x : NNReal) : ℝ) := by
  first | exact @NormEqValuation.Bridge.RingBasics.norm_eq_val | exact NormEqValuation.Bridge.RingBasics.norm_eq_val .. | (intros; apply NormEqValuation.Bridge.RingBasics.norm_eq_val <;> assumption)

theorem mem_OC (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  first | exact @IntegralComplexMem.Bridge.RingBasics.mem_OC | exact IntegralComplexMem.Bridge.RingBasics.mem_OC .. | (intros; apply IntegralComplexMem.Bridge.RingBasics.mem_OC <;> assumption)

theorem p_ne_zero : ((p : ℕ) : ℂ_[p]) ≠ 0 := by
  first | exact @PrimeNeZero.Bridge.RingBasics.p_ne_zero | exact PrimeNeZero.Bridge.RingBasics.p_ne_zero .. | (intros; apply PrimeNeZero.Bridge.RingBasics.p_ne_zero <;> assumption)

theorem norm_p_lt : ‖((p : ℕ) : ℂ_[p])‖ < 1 := by
  first | exact @NormPrimeLtOne.Bridge.RingBasics.norm_p_lt | exact NormPrimeLtOne.Bridge.RingBasics.norm_p_lt .. | (intros; apply NormPrimeLtOne.Bridge.RingBasics.norm_p_lt <;> assumption)

theorem norm_gal (g : Per.Gq p) (x : Per.Qb p) : ‖g x‖ = ‖x‖ := by
  first | exact @GaloisNormAlt.Bridge.RingBasics.norm_gal | exact GaloisNormAlt.Bridge.RingBasics.norm_gal .. | (intros; apply GaloisNormAlt.Bridge.RingBasics.norm_gal <;> assumption)

theorem mem_span_pow_OC (n : ℕ) (x : Per.OC p) :
    x ∈ (Ideal.span {((p : ℕ) : Per.OC p)}) ^ n ↔ ‖(x : ℂ_[p])‖ ≤ ‖((p : ℕ) : ℂ_[p])‖ ^ n := by
  first | exact @SpanPowerIntegral.Bridge.RingBasics.mem_span_pow_OC | exact SpanPowerIntegral.Bridge.RingBasics.mem_span_pow_OC .. | (intros; apply SpanPowerIntegral.Bridge.RingBasics.mem_span_pow_OC <;> assumption)

theorem σC_coe (g : Per.Gq p) (x : Per.Qb p) :
    Per.σC g (x : ℂ_[p]) = ((g x : Per.Qb p) : ℂ_[p]) := by
  first | exact @FrobeniusComplexCoe.Bridge.RingBasics.σC_coe | exact FrobeniusComplexCoe.Bridge.RingBasics.σC_coe .. | (intros; apply FrobeniusComplexCoe.Bridge.RingBasics.σC_coe <;> assumption)

theorem norm_σC (g : Per.Gq p) (x : ℂ_[p]) : ‖Per.σC g x‖ = ‖x‖ := by
  first | exact @NormGaloisComplex.Bridge.RingBasics.norm_σC | exact NormGaloisComplex.Bridge.RingBasics.norm_σC .. | (intros; apply NormGaloisComplex.Bridge.RingBasics.norm_σC <;> assumption)

theorem σC_one (x : ℂ_[p]) : Per.σC (1 : Per.Gq p) x = x := by
  first | exact @FrobeniusComplexOne.Bridge.RingBasics.σC_one | exact FrobeniusComplexOne.Bridge.RingBasics.σC_one .. | (intros; apply FrobeniusComplexOne.Bridge.RingBasics.σC_one <;> assumption)

theorem σC_mul (g h : Per.Gq p) (x : ℂ_[p]) : Per.σC (g * h) x = Per.σC g (Per.σC h x) := by
  first | exact @FrobeniusMulComplex.Bridge.RingBasics.σC_mul | exact FrobeniusMulComplex.Bridge.RingBasics.σC_mul .. | (intros; apply FrobeniusMulComplex.Bridge.RingBasics.σC_mul <;> assumption)

theorem σF_one (x : Per.Fl p) : Per.σF (1 : Per.Gq p) x = x := by
  first | exact @FrobeniusTiltOne.Bridge.RingBasics.σF_one | exact FrobeniusTiltOne.Bridge.RingBasics.σF_one .. | (intros; apply FrobeniusTiltOne.Bridge.RingBasics.σF_one <;> assumption)

theorem σF_mul (g h : Per.Gq p) (x : Per.Fl p) : Per.σF (g * h) x = Per.σF g (Per.σF h x) := by
  first | exact @FrobeniusTiltMul.Bridge.RingBasics.σF_mul | exact FrobeniusTiltMul.Bridge.RingBasics.σF_mul .. | (intros; apply FrobeniusTiltMul.Bridge.RingBasics.σF_mul <;> assumption)

theorem untilt_σF (g : Per.Gq p) (x : Per.Fl p) : (Per.σF g x).untilt = Per.σO g x.untilt := by
  first | exact @UntiltFrobenius.Bridge.RingBasics.untilt_σF | exact UntiltFrobenius.Bridge.RingBasics.untilt_σF .. | (intros; apply UntiltFrobenius.Bridge.RingBasics.untilt_σF <;> assumption)

theorem σA_one (x : Per.Ainf p) : Per.σA (1 : Per.Gq p) x = x := by
  first | exact @FrobeniusOneA.Bridge.RingBasics.σA_one | exact FrobeniusOneA.Bridge.RingBasics.σA_one .. | (intros; apply FrobeniusOneA.Bridge.RingBasics.σA_one <;> assumption)

theorem σA_mul (g h : Per.Gq p) (x : Per.Ainf p) : Per.σA (g * h) x = Per.σA g (Per.σA h x) := by
  first | exact @FrobeniusMulA.Bridge.RingBasics.σA_mul | exact FrobeniusMulA.Bridge.RingBasics.σA_mul .. | (intros; apply FrobeniusMulA.Bridge.RingBasics.σA_mul <;> assumption)

theorem θ_σA (g : Per.Gq p) (x : Per.Ainf p) : Per.θ p (Per.σA g x) = Per.σO g (Per.θ p x) := by
  first | exact @ThetaFrobeniusA.Bridge.RingBasics.θ_σA | exact ThetaFrobeniusA.Bridge.RingBasics.θ_σA .. | (intros; apply ThetaFrobeniusA.Bridge.RingBasics.θ_σA <;> assumption)

theorem awayMap_algebraMap₂ (f : Per.Ainf p →+* Per.Ainf p) (x : Per.Ainf p) :
    Per.extP f (algebraMap (Per.Ainf p) (Per.AinfP p) x) = algebraMap (Per.Ainf p) (Per.AinfP p) (f x) := by
  first | exact @ExtensionAlgebra.Bridge.RingBasics.awayMap_algebraMap₂ | exact ExtensionAlgebra.Bridge.RingBasics.awayMap_algebraMap₂ .. | (intros; apply ExtensionAlgebra.Bridge.RingBasics.awayMap_algebraMap₂ <;> assumption)

theorem extP_inv (g : Per.Gq p) (x : Per.AinfP p) :
    Per.extP (Per.σA g) (Per.extP (Per.σA g⁻¹) x) = x := by
  first | exact @ExtendedInverse.Bridge.RingBasics.extP_inv | exact ExtendedInverse.Bridge.RingBasics.extP_inv .. | (intros; apply ExtendedInverse.Bridge.RingBasics.extP_inv <;> assumption)

theorem ker_σ (g : Per.Gq p) : Per.kerP p ≤ Ideal.comap (Per.extP (Per.σA g)) (Per.kerP p) := by
  first | exact @FrobeniusKernel.Bridge.RingBasics.ker_σ | exact FrobeniusKernel.Bridge.RingBasics.ker_σ .. | (intros; apply FrobeniusKernel.Bridge.RingBasics.ker_σ <;> assumption)

end Field

section Explicit
variable (l : ℕ) [Fact l.Prime]

theorem exists_pow_div_factorial (n : ℕ) :
    ∃ c : ℤ_[l], ((n.factorial : ℕ) : ℤ_[l]) * c = ((l : ℕ) : ℤ_[l]) ^ n := by
  first | exact @PowDivFactorialAlt.Bridge.RingBasics.exists_pow_div_factorial | exact PowDivFactorialAlt.Bridge.RingBasics.exists_pow_div_factorial .. | (intros; apply PowDivFactorialAlt.Bridge.RingBasics.exists_pow_div_factorial <;> assumption)

theorem φA_apply (x : Per.Ainf l) : Per.φA l x = WittVector.frobenius x := by
  first | exact @FrobeniusApplyA.Bridge.RingBasics.φA_apply | exact FrobeniusApplyA.Bridge.RingBasics.φA_apply .. | (intros; apply FrobeniusApplyA.Bridge.RingBasics.φA_apply <;> assumption)

theorem frob_lift (x : Per.Ainf l) : ∃ z : Per.Ainf l, Per.φA l x = x ^ l + (l : Per.Ainf l) * z := by
  first | exact @WittFrobeniusLift.Bridge.RingBasics.frob_lift | exact WittFrobeniusLift.Bridge.RingBasics.frob_lift .. | (intros; apply WittFrobeniusLift.Bridge.RingBasics.frob_lift <;> assumption)

theorem isUnit_l : IsUnit ((l : ℕ) : Per.AinfP l) := by
  first | exact @PrimeIsUnit.Bridge.RingBasics.isUnit_l | exact PrimeIsUnit.Bridge.RingBasics.isUnit_l .. | (intros; apply PrimeIsUnit.Bridge.RingBasics.isUnit_l <;> assumption)

theorem isUnit_nat (n : ℕ) (hn : n ≠ 0) : IsUnit ((n : ℕ) : Per.AinfP l) := by
  first | exact @NatIsUnit.Bridge.RingBasics.isUnit_nat | exact NatIsUnit.Bridge.RingBasics.isUnit_nat .. | (intros; apply NatIsUnit.Bridge.RingBasics.isUnit_nat <;> assumption)

theorem fontaineTheta_eq_zero_of_mem_ker (x : Per.AinfP l) (hx : x ∈ Per.kerP l ^ 1) : Per.θP l x = 0 := by
  first | exact @ThetaKernel.Bridge.RingBasics.fontaineTheta_eq_zero_of_mem_ker | exact ThetaKernel.Bridge.RingBasics.fontaineTheta_eq_zero_of_mem_ker .. | (intros; apply ThetaKernel.Bridge.RingBasics.fontaineTheta_eq_zero_of_mem_ker <;> assumption)

end Explicit

end GlobalTheory.RingBasics
end

