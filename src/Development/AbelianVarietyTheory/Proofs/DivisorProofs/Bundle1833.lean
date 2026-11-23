module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1828
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLevelGroupDataSameCovolume
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1819
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorDefiniteUnitaryConjugate
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.StabDenom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


omit [IsCMField E] in
theorem exists_nat_denom {ι : Type} [Fintype ι] (a : ι → Af E) :
    ∃ d : ℕ, 0 < d ∧ ∀ (k : ι) (w : Pl E),
      (d : w.adicCompletion E) * pLoc E w (a k) ∈ w.adicCompletionIntegers E := by
  choose N hN h using fun k => GlobalTheory.AdeleDenom.exists_nat_mul_integral E (a k)
  refine ⟨∏ k, N k, Finset.prod_pos fun k _ => hN k, fun k w => ?_⟩
  have h' : (N k : w.adicCompletion E) * pLoc E w (a k) ∈ w.adicCompletionIntegers E := by
    have := h k w
    rwa [show ((N k : Af E) * a k) w = pLoc E w ((N k : Af E) * a k) from rfl, map_mul, map_natCast] at this
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) h'

theorem cLoc_val (k : finU (E := E) (n := n)) (w : Pl E) (i j : Fin n) :
    (cLoc w (k : UA E n)).val i j = pLoc E w ((FinPart.pU k).val i j) := rfl

theorem exists_denom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ x : finU (E := E) (n := n), ∃ d : ℕ, 0 < d ∧ ∀ g : finU (E := E) (n := n), (∀ w ∈ S, cLoc w ((x⁻¹ * g * x : finU (E := E) (n := n)) : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n)) → ∀ (w : Pl E) (i j : Fin n), (d : w.adicCompletion E) * (cLoc w (g : UA E n)).val i j ∈ w.adicCompletionIntegers E := by
  intro E _ _ _ n S hS x
  obtain ⟨D₁, hD₁, h₁⟩ := exists_nat_denom (E := E) (ι := Fin n × Fin n) fun k => (FinPart.pU x).val k.1 k.2
  obtain ⟨D₂, hD₂, h₂⟩ := exists_nat_denom (E := E) (ι := Fin n × Fin n) fun k => (FinPart.pU x⁻¹).val k.1 k.2
  have key : ∀ (h : finU (E := E) (n := n)) (w : Pl E), cLoc w ((x⁻¹ * h * x : finU (E := E) (n := n)) : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) →
      ∀ i j, ((D₁ * D₂ : ℕ) : w.adicCompletion E) * (cLoc w (h : UA E n)).val i j ∈ w.adicCompletionIntegers E := by
    intro h w hk i j
    have e : (h : UA E n) = (x : UA E n) * ((x⁻¹ * h * x : finU (E := E) (n := n)) : UA E n) * ((x⁻¹ : finU (E := E) (n := n)) : UA E n) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.mul_sum]
    refine sum_mem fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine sum_mem fun a _ => ?_
    have e1 : (D₁ : w.adicCompletion E) * (cLoc w (x : UA E n)).val i a ∈ w.adicCompletionIntegers E := by
      rw [cLoc_val]; exact h₁ (i, a) w
    have e2 : (D₂ : w.adicCompletion E) * (cLoc w ((x⁻¹ : finU (E := E) (n := n)) : UA E n)).val b j ∈ w.adicCompletionIntegers E := by
      rw [cLoc_val]; exact h₂ (b, j) w
    have e3 := GlobalTheory.BCT.LocCpt.entry_mem_of_mem_KGL hk a b
    have e4 : ((D₁ * D₂ : ℕ) : w.adicCompletion E) * ((cLoc w (x : UA E n)).val i a *
        (cLoc w ((x⁻¹ * h * x : finU (E := E) (n := n)) : UA E n)).val a b * (cLoc w ((x⁻¹ : finU (E := E) (n := n)) : UA E n)).val b j) =
        ((D₁ : w.adicCompletion E) * (cLoc w (x : UA E n)).val i a) * (cLoc w ((x⁻¹ * h * x : finU (E := E) (n := n)) : UA E n)).val a b *
        ((D₂ : w.adicCompletion E) * (cLoc w ((x⁻¹ : finU (E := E) (n := n)) : UA E n)).val b j) := by
      push_cast; ring
    rw [e4]
    exact mul_mem (mul_mem e1 e3) e2
  refine ⟨D₁ * D₂, Nat.mul_pos hD₁ hD₂, fun g hg w i j => ?_⟩
  rcases GlobalTheory.BCT.LocCpt.mem_or_conj_mem hS w with hw | hw
  · exact key g w (hg w hw) i j
  · have hinv : cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) ((x⁻¹ * g⁻¹ * x : finU (E := E) (n := n)) : UA E n) ∈
        GlobalTheory.LFun.KGL (conjSrc (GlobalTheory.SplitPts.conjE E) w) (n := n) := by
      have : (x⁻¹ * g⁻¹ * x : finU (E := E) (n := n)) = (x⁻¹ * g * x)⁻¹ := by group
      rw [this, Subgroup.coe_inv, map_inv]
      exact (GlobalTheory.LFun.KGL _ (n := n)).inv_mem (hg _ hw)
    have h1 := key g⁻¹ _ hinv j i
    have e2 : (cLoc w (g : UA E n)).val i j = conjLoc (GlobalTheory.SplitPts.conjE E) w
        ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) ((g⁻¹ : finU (E := E) (n := n)) : UA E n)).val j i) := by
      rw [GlobalTheory.BCT.LocCpt.cLoc_eq_invT]
      show ((GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w)
        (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) (g : UA E n)))⁻¹).val j i = _
      rw [← map_inv, ← map_inv, Subgroup.coe_inv]
      rfl
    rw [e2, ← map_natCast (conjLoc (GlobalTheory.SplitPts.conjE E) w) (D₁ * D₂), ← map_mul,
      HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec _ w).2.2]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1

end GlobalTheory.BCT.StabDenom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteValuationCentredCompleteNormalStatement
section
open IsLocalRing GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_discreteValuation_centred_completeNormal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∃ ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ)), (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) ∧ ∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1 := by
  first | exact @GlobalTheory.DivVal.exists_valuation_centre | exact GlobalTheory.DivVal.exists_valuation_centre | (intros; apply GlobalTheory.DivVal.exists_valuation_centre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualWeylTensorLiftCoefficientSpace
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRead.ExPhi

theorem res_eq {ι : Type} {n : ℕ} {lam : ι → DomWeight n} {lamW : ι → ℕ → ℕ} {c : ι → ℤ} (h : Shift lam lamW c) (τ : ι) :
    res n (lamW τ) = fun a => (lam τ).natW a + lamW τ (n - 1) := by
  funext a
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) a.2
  have h1 := h τ a
  have h2 := h τ ⟨n - 1, by omega⟩
  have h3 : (lam τ).w ⟨n - 1, by omega⟩ ≤ (lam τ).w a := (lam τ).anti (by
    rw [Fin.le_def]; have := a.2; simp only; omega)
  simp only [res, DomWeight.natW, DomWeight.detShift, dif_pos hn] at h2 ⊢
  omega

theorem liftPol_mem {K C : Type} [Field K] [Field C] (e0 : K →+* C) {ι : Type} {n : ℕ} {lam : ι → DomWeight n}
    {lamW : ι → ℕ → ℕ} {c : ι → ℤ} (h : Shift lam lamW c) (τ : ι) (x : MvPolynomial (Fin n × Fin n) K)
    (hx : x ∈ nablaSq K n (lam τ)) : liftPol e0 (lamW τ (n - 1)) x ∈ dualWeyl C n n (res n (lamW τ)) := by
  rw [res_eq h τ]
  exact _root_.GlobalTheory.FrameRead.detPol_pow_mul_mem_dualWeyl C n _ _ _ (dualWeylMap K C e0 n n _ x hx)

theorem ssB_span (K : Type) [Field K] {n : ℕ} (ν : Fin n → ℕ) :
    Submodule.span K (Set.range (ssB K ν)) = dualWeyl K n n ν :=
  (Formalism.GradedWeylDivisibility.sSBasis K n n ν).choose_spec.1.2.1

theorem ssB_mem (K : Type) [Field K] {n : ℕ} (l : DomWeight n) (j : ssIdx n n l.natW) : ssB K l.natW j ∈ nablaSq K n l := by
  unfold nablaSq
  rw [← ssB_span]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem detPol_ne_zero (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) : detPol R n ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2) h
  rw [detPol, RingHom.map_det, map_zero] at h1
  have h2 : (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2).mapMatrix
      (Matrix.of fun a s => X (a, s)) = (1 : Matrix (Fin n) (Fin n) R) := by
    ext a s; simp
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem linInd_map {F K σ ι : Type} [Field F] [Field K] (e : F →+* K) {v : ι → MvPolynomial σ F}
    (hv : LinearIndependent F v) : LinearIndependent K (fun i => MvPolynomial.map e (v i)) := by
  classical
  letI : Algebra F K := e.toAlgebra
  rw [linearIndependent_iff'] at hv ⊢
  intro s c hsum i hi
  let B := Module.Free.chooseBasis F K
  apply B.ext_elem
  intro j
  have key : ∑ i ∈ s, (B.repr (c i) j) • v i = 0 := by
    ext m
    have h1 := congrArg (AddMonoidAlgebra.coeff · m) hsum
    simp only [coeff_sum, coeff_smul, coeff_map, smul_eq_mul] at h1 ⊢
    change ∑ x ∈ s, c x * e ((v x).coeff m) = 0 at h1
    change ∑ x ∈ s, (B.repr (c x)) j * (v x).coeff m = 0
    have h2 := congrArg (fun x => B.repr x j) h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zero, Finsupp.finsetSum_apply, Finsupp.coe_zero, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h3 : c i * e (AddMonoidAlgebra.coeff (v i) m) = AddMonoidAlgebra.coeff (v i) m • c i := by
      rw [Algebra.smul_def, mul_comm]; rfl
    rw [h3, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have := hv s (fun i => B.repr (c i) j) key i hi
  simpa using this

def semiConstr {K C V M I : Type} [Field K] [Field C] [AddCommGroup V] [Module K V] [AddCommGroup M] [Module C M] [Fintype I]
    (e : K →+* C) (b : Module.Basis I K V) (t : I → M) : V →ₛₗ[e] M where
  toFun v := ∑ i, e (b.repr v i) • t i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.smul_sum, mul_smul]

theorem semiConstr_basis {K C V M I : Type} [Field K] [Field C] [AddCommGroup V] [Module K V] [AddCommGroup M] [Module C M]
    [Fintype I] (e : K →+* C) (b : Module.Basis I K V) (t : I → M) (i : I) : semiConstr e b t (b i) = t i := by
  classical
  change ∑ j, e (b.repr (b i) j) • t j = t i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Finsupp.single_apply, hj.symm]
  · simp

def mulMap (C : Type) [Field C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) :
    NablaT C n lamW →ₗ[C] Pol C ι n :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra C ι (Pol C ι n)).compLinearMap fun τ =>
    (blockEmb C τ).toLinearMap ∘ₗ (dualWeyl C n n (res n (lamW τ))).subtype)

theorem mulMap_tprod (C : Type) [Field C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ)
    (y : ∀ τ, dualWeyl C n n (res n (lamW τ))) :
    mulMap C n lamW (PiTensorProduct.tprod C y) = ten fun τ => (y τ : MvPolynomial (Fin n × Fin n) C) := by
  simp [mulMap, ten]

theorem ten_liftPol {K C : Type} [Field K] [Field C] (e0 : K →+* C) {ι : Type} [Fintype ι] {n : ℕ} (k : ι → ℕ)
    (x : ι → MvPolynomial (Fin n × Fin n) K) :
    (ten fun τ => liftPol e0 (k τ) (x τ)) = (ten fun τ => detPol C n ^ k τ) * MvPolynomial.map e0 (ten x) := by
  simp only [ten, liftPol, map_mul, map_prod, Finset.prod_mul_distrib, blockEmb, map_rename]

theorem ten_det_ne_zero (C : Type) [Field C] {ι : Type} [Fintype ι] {n : ℕ} (k : ι → ℕ) :
    (ten fun τ => detPol C n ^ k τ) ≠ 0 := by
  unfold ten
  refine Finset.prod_ne_zero_iff.2 fun τ _ => ?_
  intro h
  have hinj : Function.Injective (blockEmb C (k := n) (n := n) τ) :=
    rename_injective _ fun a b hab => (Prod.mk.inj hab).2
  exact pow_ne_zero _ (detPol_ne_zero C n) (hinj (h.trans (map_zero _).symm))

theorem exists_phi (K C : Type) [Field K] [Field C] (e0 : K →+* C) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ)
    (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (h : Shift lam lamW c) :
    ∃ Φ : VV K lam →ₛₗ[e0] NablaT C n lamW, IsPhi e0 lam lamW Φ ∧ LinearIndependent C fun i => Φ (bVV K lam i) := by
  classical
  let u : ∀ τ, ssIdx n n (lam τ).natW → dualWeyl C n n (res n (lamW τ)) := fun τ j =>
    ⟨liftPol e0 (lamW τ (n - 1)) (ssB K (lam τ).natW j), liftPol_mem e0 h τ _ (ssB_mem K _ j)⟩
  let t : VVIdx lam → NablaT C n lamW := fun i => PiTensorProduct.tprod C fun τ => u τ (i τ)
  refine ⟨semiConstr e0 (bVV K lam) t, ?_, ?_⟩
  · intro x v hx hv
    haveI : ∀ τ, Fintype (ssIdx n n (lam τ).natW) := fun τ => (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).fintype
    have hex : ∀ τ, ∃ a : ssIdx n n (lam τ).natW → K, ∑ j, a j • ssB K (lam τ).natW j = x τ := fun τ => by
      have h1 := hx τ
      unfold nablaSq at h1
      rw [← ssB_span] at h1
      exact (Submodule.mem_span_range_iff_exists_fun K).1 h1
    choose a ha using hex
    have hv' : v = ∑ i : VVIdx lam, (∏ τ, a τ (i τ)) • bVV K lam i := by
      apply Subtype.ext
      rw [hv]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe, bVVfun, ten, ← ha, map_sum, map_smul]
      rw [Finset.prod_univ_sum]
      simp only [Finset.prod_smul]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext i; simp
    refine ⟨fun τ => ∑ j, e0 (a τ j) • u τ j, fun τ => ?_, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [Submodule.coe_sum, Submodule.coe_smul, u, liftPol, ← ha, map_sum, Finset.mul_sum, smul_eq_C_mul, map_mul, map_C]
        refine Finset.sum_congr rfl fun j _ => by ring
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [MultilinearMap.map_sum, hv', map_sum]
        simp only [LinearMap.map_smulₛₗ, semiConstr_basis, MultilinearMap.map_smul_univ, map_prod]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext i; simp
  · simp only [semiConstr_basis]
    refine LinearIndependent.of_comp (mulMap C n lamW) ?_
    have h1 := linInd_map e0 (bVVfun_spec K lam).1
    have h2 := h1.map' (LinearMap.mulLeft C (ten fun τ => detPol C n ^ lamW τ (n - 1)))
      (LinearMap.ker_eq_bot.2 (mul_right_injective₀ (ten_det_ne_zero C _)))
    have h3 : (mulMap C n lamW ∘ t) = (LinearMap.mulLeft C (ten fun τ => detPol C n ^ lamW τ (n - 1))) ∘
        fun i => MvPolynomial.map e0 (bVVfun K lam i) := by
      funext i
      simp only [Function.comp, t, mulMap_tprod, u, ten_liftPol, LinearMap.mulLeft_apply, bVVfun]
    exact h3 ▸ h2

end GlobalTheory.FrameRead.ExPhi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLevelGroupDataSameCovolumeStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullLevelGroup_data_same_covolume : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k : U.Comp, ∃ Y : ReciprocityTheory.ChartRestriction.G.FD.Data E r, Y.Ψ = (U.X k).Ψ ∧ Y.p0 = (U.X k).p0 ∧ Y.Gm = (U.X k).Gm ∧ Y.Λ = (U.X k).Λ ∧ Y.ξ0 = (U.X k).ξ0 ∧ GlobalTheory.EqCovol.IsLevGrp l Y ∧ GlobalTheory.EqCovol.IsSelfDualTr Y ∧ GlobalTheory.TrueCx.covol (U.X k) = GlobalTheory.TrueCx.covol Y := by
  first | exact @GlobalTheory.EqCovol.exists_levGrp_covol | exact GlobalTheory.EqCovol.exists_levGrp_covol | (intros; apply GlobalTheory.EqCovol.exists_levGrp_covol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelBlock
section
namespace GlobalTheory.GammaLevel

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem eq_one_of_block (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (m : Frame X.Ψ r) (hm : ∀ τ (a c : Fin r), (c : ℕ) < X.p0 → X.p0 ≤ (a : ℕ) → m τ a c = 0)
    (h : lact γ x = rmul x m) : γ = 1 := by
  have hp0 := X.p0_le
  have hj : r - X.p0 ≤ r := Nat.sub_le _ _
  have hp : r - (r - X.p0) = X.p0 := by omega
  have hx' : lact γ x ∈ X.dom := FrameFibre.lact_mem_GG (X.Γ_stab γ hγ).1 hx
  have key : ∀ τ : X.Ψ, ∃ b t : Matrix (Fin r) (Fin r) ℂ, b.det ≠ 0 ∧
      (∀ a c : Fin r, (c : ℕ) < r - (r - X.p0) → ¬ (a : ℕ) < r - (r - X.p0) → b a c = 0) ∧
      (∀ a c, c < a → t a c = 0) ∧ mat m τ * b = b * t := by
    intro τ
    refine FreeOnDomain.exists_conj_block hj _ ?_
    ext a c
    refine hm τ _ _ ?_ ?_
    · rw [idx_symm_inr]; have := c.2; omega
    · rw [idx_symm_inl]; omega
  choose b t hb hb0 ht e using key
  have e' : ∀ τ, mat (lact γ x) τ * b τ = mat x τ * b τ * t τ := fun τ => by
    rw [Matrix.mul_assoc, ← e, h, ← Matrix.mul_assoc]
    rfl
  refine X.Γ_free γ hγ (rmul x fun τ => b τ)
    (GlobalTheory.PointOfFrames.rmul_mem_dom X hx _ hb (by rw [hp] at hb0; exact hb0)) (fun τ => t τ)
    (fun τ => ⟨?_, ht τ⟩) ?_
  · intro h0
    have h1 := congrArg det (e' τ)
    have h0' : (t τ).det = 0 := h0
    rw [det_mul, det_mul, h0', mul_zero] at h1
    exact mul_ne_zero (hx' τ).1 (hb τ) h1
  · exact (ReciprocityTheory.ChartRestriction.G.AR.Up.KU.lact_rmul' X γ x _).trans (funext e')


omit [NumberField E] [IsCMField E] in
theorem lact_inv_mul {Ψ : Finset (E →+* ℂ)} {δ γ : GL (Fin r) E} {x m : Frame Ψ r}
    (h : lact γ x = rmul (lact δ x) m) : lact (δ⁻¹ * γ) x = rmul x m := by
  funext τ
  have h1 : (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
    (δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat m τ := congrFun h τ
  change ((δ⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ * mat m τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc, h1, Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.Dict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_level_block {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (h1 : 1 ≤ r) (k : U.Comp) (x x' : (U.X k).dom)
    (hxx : (U.un k x').x = (U.un k x).x) :
    ∃ (δ : GL (Fin r) E) (m : Frame (U.X k).Ψ r), IsUStab (U.X k).Gm (U.X k).Λ δ ∧
      (∀ u ∈ (U.X k).Λ, ∃ u' ∈ (U.X k).Λ, (δ : Matrix (Fin r) (Fin r) E) *ᵥ u = u + l.M • u') ∧
      x'.1 = rmul (lact δ x.1) m ∧
      ∀ τ (a c : Fin r), (c : ℕ) < (U.X k).p0 → (U.X k).p0 ≤ (a : ℕ) → m τ a c = 0 := by
  obtain ⟨W⟩ := nonempty_uw hU
  obtain ⟨hκ, -, -, hrk, hinj, hspan, -⟩ := uw_lattice E H Dw l Xo c σ r U hσ hU h1 W k
  obtain ⟨hr, hX, -⟩ := hU
  obtain ⟨hp0, hty⟩ := hX k
  obtain ⟨idx, hi, hper⟩ := CompInj.exists_idx hσ hr W.e (U.X k) hp0 hty
  have hq : (W.F.Di (W.ik k)).q = Dw.q := (W.F.sig _).2
  have hξ : cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    have h := (U.X k).ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  have hpos : ∀ τ ∈ (U.X k).Ψ, 0 < (τ (-(U.X k).ξ0)).im := by
    intro τ hτ
    have := (U.X k).κ0_sign ⟨τ, hτ⟩
    rw [hκ, map_mul, map_ofNat] at this
    rw [map_neg, Complex.neg_im]
    simp at this
    linarith
  let Pf : Frame (U.X k).Ψ r → ((W.F.Di (W.ik k)).La →+ (Fin W.g → ℂ)) := fun y =>
    AddMonoidHom.mk' (fun v j => Formalism.L2.PjFree.perFr (U.X k) y (W.emb k v)
      (Formalism.L2.PjFree.relab c σ (W.e j).1) (W.e j).2) (by
      intro a b
      funext j
      have he : ∀ τ : E →+* ℂ, Data.emb τ (W.emb k (a + b)) = Data.emb τ (W.emb k a) + Data.emb τ (W.emb k b) := by
        intro τ
        funext i
        simp [Data.emb]
      simp only [Pi.add_apply, hper, he]
      split_ifs
      · simp [hermC, mul_add, Finset.sum_add_distrib]
      · simp [Matrix.mulVec_add])
  have hpt : ∀ y : (U.X k).dom, (U.un k y).x = W.F.u (W.ik k) (Pf y.1) := by
    intro y
    obtain ⟨P, hP, -, hu, -⟩ := W.pt k y
    rw [hu]
    congr 1
    ext a j
    exact hP a j
  have hrange : LinearMap.range (W.emb k) = (U.X k).Λ := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (W.φ k a).2
    · intro hv
      exact ⟨(W.φ k).symm ⟨v, hv⟩, by simp [UW.emb]⟩
  obtain ⟨δ, m, hδ, hM, -, hm, hm0⟩ := FrameFibre.exists_level_block_of_eq E H Dw l Xo _ W.g _ W.F (W.ik k) r
    (-(U.X k).ξ0) (U.X k).Gm (W.emb k) (U.X k).Ψ idx Pf hty (by rw [hq]; exact hi) hξ hpos
    ⟨hinj, hspan, (U.X k).Gm_herm, (U.X k).Gm_det, W.isom k⟩ hrk
    (by rw [hq]; exact fun y v j => hper y _ j) x.1 (by rw [hq, ← hp0]; exact x.2) x'.1
    (by rw [hq, ← hp0]; exact x'.2) (by rw [← hpt, ← hpt, hxx])
  rw [hrange] at hδ
  rw [hq, ← hp0] at hm0
  refine ⟨δ, m, hδ, fun u hu => ?_, hm, hm0⟩
  obtain ⟨a, rfl⟩ : u ∈ LinearMap.range (W.emb k) := hrange ▸ hu
  obtain ⟨w, hw⟩ := hM a
  exact ⟨_, (W.φ k w).2, hw⟩

end

end GlobalTheory.GammaLevel

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.GammaLevel.trivial_mod_of_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (k : U.Comp), (∀ δ : GL (Fin r) E, IsUStab (U.X k).Gm (U.X k).Λ δ → (∀ u ∈ (U.X k).Λ, ∃ u' ∈ (U.X k).Λ, (δ : Matrix (Fin r) (Fin r) E).mulVec u = u + (l.M : ℕ) • u') → δ ∈ (U.X k).Γ) → ∀ γ ∈ (U.X k).Γ, (∀ u ∈ (U.X k).Λ, ∃ u' ∈ (U.X k).Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec u = u + (l.M : ℕ) • u') := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU h1 _ k hP γ hγ
  obtain ⟨x, hx⟩ := GlobalTheory.CompInj.dom_nonempty (U.X k)
  have hx' : lact γ x ∈ (U.X k).dom := GlobalTheory.FrameFibre.lact_mem_GG ((U.X k).Γ_stab γ hγ).1 hx
  obtain ⟨t, ht⟩ := (hU.2.2.2.1 k k ⟨x, hx⟩ ⟨_, hx'⟩).2 ⟨γ, hγ, fun _ => (1 : Matrix (Fin r) (Fin r) ℂ),
    fun τ => ⟨by
      change (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
      simp, fun a c h => Matrix.one_apply_ne h.ne'⟩, by
      congr 1
      funext τ
      exact (Matrix.mul_one (mat (lact γ x) τ)).symm⟩
  obtain ⟨δ, m, hδ, hM, hm, hm0⟩ := GlobalTheory.GammaLevel.exists_level_block (U := Formalism.L2.PjFree.Unf.ofPj U) hσ
    ((Formalism.L2.PjFree.isUnf_ofPj U).2 hU) h1 k ⟨x, hx⟩ ⟨_, hx'⟩ ht.1
  have h := GlobalTheory.GammaLevel.eq_one_of_block (U.X k) (mul_mem (inv_mem (hP δ hδ hM)) hγ) hx m hm0
    (GlobalTheory.GammaLevel.lact_inv_mul hm)
  rw [inv_mul_eq_one] at h
  exact h ▸ hM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftFiniteEtaleSurjectionTestRingStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_finiteEtaleSurjection_testRing : ∀ (Y Z : Scheme.{0}) (π : Z ⟶ Y), IsFinite π → Etale π → Surjective π →
    ∀ (K : Type) [Field K] (p : TRing K) (x : Sp p.R ⟶ Y), ∃ (q : TRing K) (ι : p.R →ₐ[K] q.R),
      (letI := ι.toRingHom.toAlgebra; Module.FaithfullyFlat p.R q.R ∧ Algebra.Etale p.R q.R) ∧
      ∃ z : Sp q.R ⟶ Z, z ≫ π = spMap ι.toRingHom ≫ x := by
  first | exact @GlobalTheory.exists_lift_finiteEtale_testRing | exact GlobalTheory.exists_lift_finiteEtale_testRing | (intros; apply GlobalTheory.exists_lift_finiteEtale_testRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStepCharactersOfColengthStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagStep_characters_of_colength : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), ∀ (f : Lt1 Dw) (xs : NNReal) (r : ℝ), ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HasAF X.v (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (fun (i : Fin (Dw.mult f.1)) j => X.ι (Ch.uvecT ⟨f.1, i⟩ j)) xs → (X.v (p : X.C) : ℝ) ^ r ≤ xs → HasChars (fgl Ch X) (frame Ch X f) (r : EReal) ∧ ∀ k : ℕ, nuFac p y f k ≤ ((k * r : ℝ) : EReal) := by
  first | exact @GlobalTheory.RefSum.hasChars_frame_of_hasAF | exact GlobalTheory.RefSum.hasChars_frame_of_hasAF | (intros; apply GlobalTheory.RefSum.hasChars_frame_of_hasAF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyTransvectionEqSumStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixRowSubstitutionPoly_transvection_eq_sum : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (a b : Fin N) (r : R) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → rowSubst O N R (Matrix.transvection a b r) f = ∑ k ∈ Finset.range (D + 1), r ^ k • MvPolynomial.map (algebraMap O R) (rowDiv O b a k f) := by
  first | exact @GlobalTheory.RowSubstTransvection.rowSubst_transvection | exact GlobalTheory.RowSubstTransvection.rowSubst_transvection | (intros; apply GlobalTheory.RowSubstTransvection.rowSubst_transvection <;> assumption)
end

