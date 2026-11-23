module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0002
public import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0047
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassTorsionQCoefficients
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma one_sub_mul_sum_range_natCast_mul_pow_add (x : ℂ) (n : ℕ) :
    (1 - x) * ∑ i ∈ Finset.range n, (i : ℂ) * x ^ i + n * x ^ n =
      ∑ i ∈ Finset.range n, x ^ (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    push_cast
    ring

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma isIntegral_natCast_div_one_sub_of_isIntegral_of_ne_one (ζ : ℂ) (M : ℕ) (hζ : IsIntegral ℤ ζ)
    (hM : ζ ^ M = 1) (h1 : ζ ≠ 1) : IsIntegral ℤ ((M : ℂ) / (1 - ζ)) := by
  have hsub : (1 - ζ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hgeom : ∑ i ∈ Finset.range M, ζ ^ (i + 1) = 0 := by
    simp_rw [pow_succ]
    rw [← Finset.sum_mul, geom_sum_eq h1, hM, sub_self, zero_div, zero_mul]
  have key := one_sub_mul_sum_range_natCast_mul_pow_add ζ M
  rw [hgeom, hM, mul_one] at key
  have hq : (M : ℂ) / (1 - ζ) = -∑ i ∈ Finset.range M, (i : ℂ) * ζ ^ i := by
    rw [div_eq_iff hsub]
    linear_combination key
  rw [hq]
  exact (IsIntegral.sum _ fun i _ => (isIntegral_natCast i).mul (hζ.pow i)).neg


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.isIntegral_coefficients : ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N) (k : ℕ),
    0 < M → M • x = 0 → IsIntegral ℤ ((M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cB N x k) ∧
      IsIntegral ℤ ((M : ℂ) ^ 3 * _root_.GlobalTheory.WpFam.cD N x k) ∧ IsIntegral ℤ (12 * (M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cP N x k) ∧
      IsIntegral ℤ (12 * _root_.GlobalTheory.WpFam.cG N k) := by
  intro N _ M x k _ hx
  obtain ⟨-, -, hzero, -, hpow, -, -, hint⟩ :=
    _root_.GlobalTheory.WpFam.AddCharZMod.main N
  have h12 : IsIntegral ℤ (12 : ℂ) := by simpa using isIntegral_natCast (R := ℤ) (B := ℂ) 12
  have htw : ∀ (a : ℕ) (s : ℂ), IsIntegral ℤ s →
      IsIntegral ℤ (_root_.GlobalTheory.WpFam.cSum N a s x k) := by
    intro a s hs
    unfold _root_.GlobalTheory.WpFam.cSum
    refine IsIntegral.sum _ fun m _ => ((isIntegral_natCast m).pow a).mul ?_
    refine IsIntegral.add ?_ (hs.mul ?_)
    · split_ifs
      · exact hint _
      · exact isIntegral_zero
    · split_ifs
      · exact hint _
      · exact isIntegral_zero
  have hG : IsIntegral ℤ (12 * _root_.GlobalTheory.WpFam.cG N k) := by
    unfold _root_.GlobalTheory.WpFam.cG
    split_ifs
    · rw [show (12 : ℂ) * (-1 / 12) = -1 by norm_num]
      exact isIntegral_one.neg
    · exact h12.mul ((isIntegral_natCast 2).mul (isIntegral_natCast _))
    · simp [isIntegral_zero]
  have hB : IsIntegral ℤ ((M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cB N x k) ∧
      IsIntegral ℤ ((M : ℂ) ^ 3 * _root_.GlobalTheory.WpFam.cD N x k) := by
    unfold _root_.GlobalTheory.WpFam.cB _root_.GlobalTheory.WpFam.cD
    split_ifs with hk h0
    · by_cases h1 : _root_.GlobalTheory.WpFam.ch N (x 1) = 1
      · simp [h1, isIntegral_zero]
      · have hζM : _root_.GlobalTheory.WpFam.ch N (x 1) ^ M = 1 := by
          have hx1 := congr_fun hx 1
          simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] at hx1
          rw [← hpow, hx1, hzero]
        have hq := isIntegral_natCast_div_one_sub_of_isIntegral_of_ne_one _ M (hint (x 1)) hζM h1
        constructor
        · rw [show (M : ℂ) ^ 2 * (_root_.GlobalTheory.WpFam.ch N (x 1) / (1 - _root_.GlobalTheory.WpFam.ch N (x 1)) ^ 2)
              = _root_.GlobalTheory.WpFam.ch N (x 1) * ((M : ℂ) / (1 - _root_.GlobalTheory.WpFam.ch N (x 1))) ^ 2 by
              rw [div_pow]; ring]
          exact (hint _).mul (hq.pow 2)
        · rw [show (M : ℂ) ^ 3 * (_root_.GlobalTheory.WpFam.ch N (x 1) * (1 + _root_.GlobalTheory.WpFam.ch N (x 1)) /
              (1 - _root_.GlobalTheory.WpFam.ch N (x 1)) ^ 3) = _root_.GlobalTheory.WpFam.ch N (x 1) *
              (1 + _root_.GlobalTheory.WpFam.ch N (x 1)) *
              ((M : ℂ) / (1 - _root_.GlobalTheory.WpFam.ch N (x 1))) ^ 3 by rw [div_pow]; ring]
          exact ((hint _).mul (isIntegral_one.add (hint _))).mul (hq.pow 3)
    · simp [isIntegral_zero]
    · exact ⟨((isIntegral_natCast M).pow 2).mul (htw 1 1 isIntegral_one),
        ((isIntegral_natCast M).pow 3).mul (htw 2 (-1) isIntegral_one.neg)⟩
  refine ⟨hB.1, hB.2, ?_, hG⟩
  unfold _root_.GlobalTheory.WpFam.cP
  split_ifs
  · simp [isIntegral_zero]
  · rw [show 12 * (M : ℂ) ^ 2 * (_root_.GlobalTheory.WpFam.cB N x k - _root_.GlobalTheory.WpFam.cG N k)
        = 12 * ((M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cB N x k) -
          (M : ℂ) ^ 2 * (12 * _root_.GlobalTheory.WpFam.cG N k) by ring]
    exact (h12.mul hB.1).sub (((isIntegral_natCast M).pow 2).mul hG)

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfRepresentsHilbertFunctorOfLocalStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_represents_hilbertFunctor_of_local : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (H : Scheme.{0}) (u : GlobalTheory.HilbGlue.HPt z r H), (∀ (T : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r T), ∃! c : T ⟶ H, GlobalTheory.HilbGlue.HPt.map c u = x) → (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme), IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme), x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x) → IsProper u.1 := by
  first | (exact @GlobalTheory.HilbGlue.isProper_of_represents_of_local_proper) | (exact GlobalTheory.HilbGlue.isProper_of_represents_of_local_proper) | (intros; apply GlobalTheory.HilbGlue.isProper_of_represents_of_local_proper  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedOfFormallyEtale
section
open IsLocalRing TensorProduct

namespace GlobalTheory.RootFibre

section
variable (R K L : Type) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
include K

end

variable (R L Q : Type) [CommRing R] [CommRing L] [Algebra R L] [CommRing Q] [Algebra R Q] [IsDomain Q]

noncomputable def toFrac : Q ⊗[R] L →ₐ[Q] FractionRing Q ⊗[R] L :=
  Algebra.TensorProduct.map (Algebra.ofId Q (FractionRing Q)) (AlgHom.id R L)

theorem toFrac_injective [Module.Flat R L] : Function.Injective (toFrac R L Q) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := L)
    ((IsScalarTower.toAlgHom R Q (FractionRing Q)).toLinearMap)
    (IsFractionRing.injective Q (FractionRing Q))
  have e : ⇑(toFrac R L Q) =
      ⇑(LinearMap.rTensor L (IsScalarTower.toAlgHom R Q (FractionRing Q)).toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [toFrac]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [e]; exact h

theorem finite_integralClosure [Module.Flat R L] [Algebra.FormallyEtale R L] [Algebra.EssFiniteType R L]
    [IsIntegrallyClosed Q] [IsNoetherianRing Q] :
    Module.Finite Q (integralClosure Q (Q ⊗[R] L)) := by
  classical
  have : Algebra.EssFiniteType (FractionRing Q) (FractionRing Q ⊗[R] L) :=
    Algebra.EssFiniteType.baseChange R L (FractionRing Q)
  have hfin : Module.Finite (FractionRing Q) (FractionRing Q ⊗[R] L) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  obtain ⟨I, _, A, _, _, e, hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod (FractionRing Q) (FractionRing Q ⊗[R] L)).1
      inferInstance
  letI : ∀ i, Algebra Q (A i) := fun i =>
    ((algebraMap (FractionRing Q) (A i)).comp (algebraMap Q (FractionRing Q))).toAlgebra
  haveI : ∀ i, IsScalarTower Q (FractionRing Q) (A i) := fun i =>
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : ∀ i, FiniteDimensional (FractionRing Q) (A i) := fun i =>
    Module.Finite.of_surjective ((Pi.evalAlgHom (FractionRing Q) A i).comp e.toAlgHom).toLinearMap
      (fun a => ⟨e.symm (Pi.single i a), by simp⟩)
  haveI : ∀ i, IsNoetherian Q (integralClosure Q (A i)) := fun i =>
    IsIntegralClosure.isNoetherian Q (FractionRing Q) (A i) (integralClosure Q (A i))
  let g : Q ⊗[R] L →ₐ[Q] (∀ i, A i) :=
    ((e.toAlgHom).restrictScalars Q).comp (toFrac R L Q)
  have hg : Function.Injective g := e.injective.comp (toFrac_injective R L Q)
  let ψ : integralClosure Q (Q ⊗[R] L) →ₗ[Q] (∀ i, integralClosure Q (A i)) :=
    { toFun := fun y i => ⟨g y i, ((y.2.map g).map (Pi.evalAlgHom Q A i))⟩
      map_add' := fun a b => by ext i; simp
      map_smul' := fun c a => by ext i; simp }
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    apply hg
    funext i
    have := congrArg (fun f => ((f i : A i))) hab
    simpa [ψ] using this
  have : IsNoetherian Q (integralClosure Q (Q ⊗[R] L)) := isNoetherian_of_injective ψ hψ
  exact Module.IsNoetherian.finite Q _

end GlobalTheory.RootFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSMulRegularOfEtalePuncturedOfDepthPos
section
open IsLocalRing

namespace GlobalTheory

theorem isSMulRegular_of_etale_punctured_of_depth_pos :
    ∀ (R A : Type) [CommRing R] [IsRegularLocalRing R] [CommRing A] [Algebra R A]
      [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 1 →
      (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
      ∀ f : R, f ≠ 0 → IsSMulRegular A f := by
  intro R A _ _ _ _ _ hdepth het f hf

  obtain ⟨rs, hlen, hmem, hreg⟩ := hdepth
  obtain ⟨w, hw⟩ : ∃ w, rs = [w] := List.length_eq_one_iff.mp hlen
  subst hw
  have hwm : w ∈ maximalIdeal R := hmem w (by simp)
  have hwr : IsSMulRegular A w := ((RingTheory.Sequence.isRegular_cons_iff A w []).mp hreg).1
  have hmax : maximalIdeal R ∉ associatedPrimes R A := ReciprocityTheory.CA.max_not_mem_ass_of_reg hwm hwr

  refine IsSMulRegular.of_right_eq_zero_of_smul fun a ha => ?_
  by_contra ha0
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R a ha0
  have hfP : f ∈ P := hle (Submodule.mem_colon_singleton.mpr (by simpa using ha))
  obtain ⟨hPprime, b, hb⟩ := Submodule.isAssociatedPrime_iff.mp hP
  haveI := hPprime
  have hPm : P ≠ maximalIdeal R := fun h => hmax (h ▸ hP)
  haveI := het P hPm
  set L := Localization.AtPrime P
  haveI : Module.Free L (TensorProduct R L A) := Module.free_of_flat_of_isLocalRing
  have hfb : f • b = 0 := by
    have : f ∈ (⊥ : Submodule R A).colon {b} := hb ▸ hfP
    simpa using Submodule.mem_colon_singleton.mp this
  have hloc : IsLocalizedModule P.primeCompl (TensorProduct.mk R L A 1) :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl L _).mpr (TensorProduct.isBaseChange R A L)
  have hfL : algebraMap R L f ≠ 0 := by
    intro h0
    apply hf
    exact (IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors P)) (by simpa using h0)
  have h1 : (1 : L) ⊗ₜ[R] b = 0 := by
    have : algebraMap R L f • ((1 : L) ⊗ₜ[R] b) = 0 := by
      rw [algebraMap_smul, ← TensorProduct.tmul_smul, hfb, TensorProduct.tmul_zero]
    exact (smul_eq_zero.mp this).resolve_left hfL
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff P.primeCompl (TensorProduct.mk R L A 1)).mp h1
  have htP : (t : R) ∈ P := by
    have : (t : R) ∈ (⊥ : Submodule R A).colon {b} :=
      Submodule.mem_colon_singleton.mpr (by simpa [Submonoid.smul_def] using ht)
    exact hb ▸ this
  exact t.2 htP

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSMulRegularOfEtalePuncturedOfDepthPosDomain
section
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem isSMulRegular_of_etale_punctured_of_depth_pos_domain :
    ∀ (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsDomain S] (A : Type)
      [CommRing A] [Algebra S A], ReciprocityTheory.CA.ModDepthGE S A 1 →
      (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) →
      ∀ s : S, s ≠ 0 → IsSMulRegular A s := by
  intro S _ _ _ _ A _ _ hdepth het f hf
  obtain ⟨rs, hlen, hmem, hreg⟩ := hdepth
  obtain ⟨w, hw⟩ : ∃ w, rs = [w] := List.length_eq_one_iff.mp hlen
  subst hw
  have hwm : w ∈ maximalIdeal S := hmem w (by simp)
  have hwr : IsSMulRegular A w := ((RingTheory.Sequence.isRegular_cons_iff A w []).mp hreg).1
  have hmax : maximalIdeal S ∉ associatedPrimes S A := ReciprocityTheory.CA.max_not_mem_ass_of_reg hwm hwr
  refine IsSMulRegular.of_right_eq_zero_of_smul fun a ha => ?_
  by_contra ha0
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing S a ha0
  have hfP : f ∈ P := hle (Submodule.mem_colon_singleton.mpr (by simpa using ha))
  obtain ⟨hPprime, b, hb⟩ := Submodule.isAssociatedPrime_iff.mp hP
  haveI := hPprime
  have hPm : P ≠ maximalIdeal S := fun h => hmax (h ▸ hP)
  haveI := het P hPm
  set L := Localization.AtPrime P
  haveI : Module.Flat L (TensorProduct S L A) := inferInstance
  have hfb : f • b = 0 := by
    have : f ∈ (⊥ : Submodule S A).colon {b} := hb ▸ hfP
    simpa using Submodule.mem_colon_singleton.mp this
  have hloc : IsLocalizedModule P.primeCompl (TensorProduct.mk S L A 1) :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl L _).mpr (TensorProduct.isBaseChange S A L)
  have hfL : algebraMap S L f ≠ 0 := by
    intro h0
    apply hf
    exact (IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors P)) (by simpa using h0)
  have h1 : (1 : L) ⊗ₜ[S] b = 0 := by
    have : algebraMap S L f • ((1 : L) ⊗ₜ[S] b) = 0 := by
      rw [algebraMap_smul, ← TensorProduct.tmul_smul, hfb, TensorProduct.tmul_zero]
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := TensorProduct S L A)
      (mem_nonZeroDivisors_of_ne_zero hfL)
    exact hreg (show algebraMap S L f • ((1 : L) ⊗ₜ[S] b) = algebraMap S L f • 0 by rw [this, smul_zero])
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff P.primeCompl (TensorProduct.mk S L A 1)).mp h1
  have htP : (t : S) ∈ P := by
    have : (t : S) ∈ (⊥ : Submodule S A).colon {b} :=
      Submodule.mem_colon_singleton.mpr (by simpa [Submonoid.smul_def] using ht)
    exact hb ▸ this
  exact t.2 htP

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSepClosedResidueFieldOfModuleFinite
section
noncomputable section

namespace GlobalTheory

open IsLocalRing

theorem isLocalHom_algebraMap_of_moduleFinite (R T : Type) [CommRing R] [IsLocalRing R]
    [CommRing T] [IsLocalRing T] [Algebra R T] [Module.Finite R T] :
    IsLocalHom (algebraMap R T) := by
  constructor
  intro a ha
  by_contra hna
  haveI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  haveI hmax : (Ideal.comap (algebraMap R T) (maximalIdeal T)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal T)
  have heq := IsLocalRing.eq_maximalIdeal hmax
  have hm : a ∈ Ideal.comap (algebraMap R T) (maximalIdeal T) := by
    rw [heq]; exact (mem_maximalIdeal a).2 hna
  exact (mem_maximalIdeal _).1 hm ha

theorem isSepClosed_residueField_of_moduleFinite (R T : Type) [CommRing R] [IsLocalRing R]
    [IsSepClosed (ResidueField R)] [CommRing T] [IsLocalRing T] [Algebra R T]
    [Module.Finite R T] : IsSepClosed (ResidueField T) := by
  haveI := isLocalHom_algebraMap_of_moduleFinite R T
  haveI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  haveI : Algebra.IsIntegral (ResidueField R) (ResidueField T) := inferInstance
  haveI : Algebra.IsAlgebraic (ResidueField R) (ResidueField T) := inferInstance
  exact Algebra.IsAlgebraic.isSepClosed (F := ResidueField R)

theorem finite_algebra_strictly_henselian_pi : ∀ (R S : Type) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (ResidueField R)] [CommRing S] [Algebra R S] [Module.Finite R S],
    ∃ (ι : Type) (_ : Finite ι) (T : ι → Type) (_ : ∀ i, CommRing (T i))
      (_ : ∀ i, Algebra R (T i)) (_ : S ≃ₐ[R] Π i, T i) (_ : ∀ i, HenselianLocalRing (T i)),
      ∀ i, IsSepClosed (ResidueField (T i)) ∧ Module.Finite R (T i) := by
  intro R S _ _ _ _ _ _
  obtain ⟨ι, hι, T, hT, hA, e, h⟩ := ((finite_algebras_over_henselian R).1 S).1
  refine ⟨ι, hι, T, hT, hA, e, fun i ↦ (h i).1, fun i ↦ ⟨?_, (h i).2⟩⟩
  haveI := (h i).1
  haveI := (h i).2
  exact isSepClosed_residueField_of_moduleFinite R (T i)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSiegelUpperHalfSpaceNegMulInvSymplectic
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

open scoped ComplexOrder

namespace GlobalTheory

theorem IsSiegel.neg_mul_inv_of_symplectic (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (P Q : Matrix l l ℂ)
    (hP : ∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ))
    (hQ : ∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ))
    (hs : s ∈ Matrix.symplecticGroup l ℝ) (hdet : P.det ≠ 0) (hsym : (-(Q * P⁻¹)).IsSymm) :
    GlobalTheory.IsSiegel (-(Q * P⁻¹)) := by
  refine ⟨hsym, ?_⟩
  set A : Matrix l l ℂ := fun a b => (s (.inl a) (.inl b) : ℂ) with hA
  set B : Matrix l l ℂ := fun a b => (s (.inl a) (.inr b) : ℂ) with hB
  set C : Matrix l l ℂ := fun a b => (s (.inr a) (.inl b) : ℂ) with hC
  set D : Matrix l l ℂ := fun a b => (s (.inr a) (.inr b) : ℂ) with hD
  have hPe : P = A - I • B := by ext a b; simp only [hP]; rfl
  have hQe : Q = C - I • D := by ext a b; simp only [hQ]; rfl
  have hsc : s.map (Complex.ofRealHom : ℝ →+* ℂ) = fromBlocks A B C D := by
    ext (a|a) (b|b) <;> rfl
  have hJ : (J l ℝ).map (Complex.ofRealHom : ℝ →+* ℂ) = J l ℂ := by
    ext (a|a) (b|b) <;> simp [J, Matrix.one_apply] <;> split_ifs <;> simp
  have hc : (fromBlocks A B C D)ᵀ * J l ℂ * fromBlocks A B C D = J l ℂ := by
    have h1 := congrArg (fun M => M.map (Complex.ofRealHom : ℝ →+* ℂ)) (SymplecticGroup.mem_iff'.mp hs)
    simp only [Matrix.map_mul, transpose_map, hJ, hsc] at h1
    exact h1
  rw [J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at hc
  obtain ⟨h11, h12, h21, h22⟩ := hc
  simp at h11 h12 h21 h22
  have star_real : ∀ X : Matrix l l ℂ, (∀ a b, star (X a b) = X a b) → Xᴴ = Xᵀ := by
    intro X hX; ext a b; simp [conjTranspose_apply, hX]
  have hAs : Aᴴ = Aᵀ := star_real A (fun a b => by simp [A])
  have hBs : Bᴴ = Bᵀ := star_real B (fun a b => by simp [B])
  have hCs : Cᴴ = Cᵀ := star_real C (fun a b => by simp [C])
  have hDs : Dᴴ = Dᵀ := star_real D (fun a b => by simp [D])
  have key : Pᴴ * Q - Qᴴ * P = -(2 * I) • (1 : Matrix l l ℂ) := by
    rw [hPe, hQe]
    simp only [conjTranspose_sub, conjTranspose_smul, hAs, hBs, hCs, hDs, Complex.star_def, conj_I,
      sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
    linear_combination (norm := (match_scalars <;> ring_nf <;> (try simp only [I_sq]) <;> ring_nf)) -h11 - h22 + I • h12 - I • h21
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
  set τ := -(Q * P⁻¹) with hτ
  have hτP : τ * P = -Q := by rw [hτ, neg_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  have hsymm : ∀ a b, τ b a = τ a b := fun a b => by
    have := congrFun (congrFun hsym a) b
    simpa [transpose_apply] using this
  set M : Matrix l l ℝ := τ.map im with hM
  set Mc : Matrix l l ℂ := M.map (Complex.ofRealHom : ℝ →+* ℂ) with hMc
  have hdiff : τ - τᴴ = (2 * I) • Mc := by
    ext a b
    simp only [Matrix.sub_apply, conjTranspose_apply, hsymm a b, Matrix.smul_apply, smul_eq_mul, Mc, M, map_apply,
      Complex.ofRealHom_eq_coe, Complex.star_def, Complex.sub_conj]
    push_cast
    ring
  have hQP : Pᴴ * τᴴ = -Qᴴ := by rw [← conjTranspose_mul, hτP, conjTranspose_neg]
  have h2 : Pᴴ * Mc * P = 1 := by
    have e : Pᴴ * (τ - τᴴ) * P = (2 * I) • (1 : Matrix l l ℂ) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hτP, hQP]
      rw [Matrix.mul_neg, Matrix.neg_mul]
      linear_combination (norm := (match_scalars <;> ring_nf <;> (try simp only [I_sq]) <;> ring_nf)) -key
    rw [hdiff, Matrix.mul_smul, Matrix.smul_mul] at e
    exact smul_right_injective _ (by simp [I_ne_zero] : (2 * I) ≠ 0) e
  have e1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hu, conjTranspose_one]
  have e2 : P * P⁻¹ = 1 := mul_nonsing_inv _ hu
  have hMcf : Mc = (P⁻¹)ᴴ * P⁻¹ := by
    calc Mc = ((P⁻¹)ᴴ * Pᴴ) * Mc * (P * P⁻¹) := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = (P⁻¹)ᴴ * (Pᴴ * Mc * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * P⁻¹ := by rw [h2, Matrix.mul_one]
  have hinj : Function.Injective (P⁻¹).mulVec := by
    intro u v h
    have := congrArg P.mulVec h
    simpa [mulVec_mulVec, e2] using this
  have hpd : Mc.PosDef := hMcf ▸ PosDef.conjTranspose_mul_self _ hinj
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext a b
    simp [conjTranspose_apply, M, hsymm a b]
  · intro x hx
    set xc : l → ℂ := fun i => (x i : ℂ) with hxc
    have hxc0 : xc ≠ 0 := by
      intro h; apply hx; ext i
      have := congrFun h i
      simpa [xc] using this
    have e : star xc ⬝ᵥ Mc *ᵥ xc = ((star x ⬝ᵥ M *ᵥ x : ℝ) : ℂ) := by
      simp [dotProduct, mulVec, Mc, xc, Complex.ofReal_sum, Complex.ofReal_mul]
    have := hpd.dotProduct_mulVec_pos hxc0
    rw [e] at this
    exact zero_lt_real.mp this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothHolomorphicInSigmaFamilyMulLeftStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_mul_left : ∀ (F : Type) [Field F] [NumberField F] (k : ℂ → ℂ) (P : ℂ → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) → ℂ), DifferentiableOn ℂ k GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane → GlobalTheory.HeckeTwo.IsGood P → GlobalTheory.HeckeTwo.IsGood (fun σ z => k σ * P σ z) := by
  first | exact @GlobalTheory.HeckeTwoMul.isGood_mul | exact GlobalTheory.HeckeTwoMul.isGood_mul | (intros; apply GlobalTheory.HeckeTwoMul.isGood_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDualFourierExpansionSchwartzStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_dual_fourier_expansion_schwartz : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V), P.Nondegenerate →
    ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : SchwartzMap V ℂ),
    ∃ c : V → ℂ, (∀ N : ℕ, Summable (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        ‖c μ‖ * (1 + ‖(μ : V)‖) ^ N)) ∧
      ∀ x : V, HasSum (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        c μ * Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) (∑' l : Λ, f (x + l)) := by
  first | exact @GlobalTheory.periodisation_hasSum_fourier_bilinForm | exact GlobalTheory.periodisation_hasSum_fourier_bilinForm | (intros; apply GlobalTheory.periodisation_hasSum_fourier_bilinForm <;> assumption)
end

