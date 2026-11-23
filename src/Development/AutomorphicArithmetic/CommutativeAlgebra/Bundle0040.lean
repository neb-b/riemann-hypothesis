module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomologyFunctorialityAxiomsHold
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0012
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0030
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0039

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.AcyclicSpecFiniteAlgebraStrictHenselian
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Cb.AcycFin

private theorem sepClosed_of_isAlgebraic (K L : Type) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [IsSepClosed K] : IsSepClosed L := by
  exact Algebra.IsAlgebraic.isSepClosed (F := K)

private theorem sh_of_finite (O T : Type) [CommRing O] [CommRing T] [Algebra O T]
    [Module.Finite O T] (hO : SH O) (hT : HenselianLocalRing T) : SH T := by
  obtain ⟨_, hk⟩ := hO
  haveI : IsLocalHom (algebraMap O T) :=
    ((IsLocalRing.local_hom_tfae (algebraMap O T)).out 1 5).mpr
      (GlobalTheory.comap_eq_maximalIdeal_of_finite (IsLocalRing.maximalIdeal T))
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T) := inferInstance
  exact ⟨hT, sepClosed_of_isAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T)⟩

private theorem acyc_of_equiv {q : ℕ} {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (h : Acyc q (sp A)) : Acyc q (sp B) := by
  intro n i hn
  haveI := h n i hn
  have hid : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 (sp B) := by
    have h0 : CommRingCat.ofHom (e.symm : B →+* A) ≫ CommRingCat.ofHom (e : A →+* B) = 𝟙 _ := by
      ext x
      simp
    simp only [spMap, ← Functor.map_comp, ← Spec.map_comp, h0, Spec.map_id]
    exact sch.map_id _
  have key : Function.LeftInverse (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n)
      (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n) := fun x => by
    rw [← pull_comp, hid, pull_id]
  exact key.injective.subsingleton

private theorem acyc_prod {q : ℕ} {A B : Type} [CommRing A] [CommRing B]
    (hA : Acyc q (sp A)) (hB : Acyc q (sp B)) : Acyc q (sp (A × B)) := by
  intro n i hn
  haveI := hA n i hn
  haveI := hB n i hn
  exact ⟨fun x y => (UpperTheory.twistedCohomology_specProd_bijective_prod q A B n i).1
    (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))⟩

private theorem acyc_of_subsingleton {q : ℕ} {A : Type} [CommRing A] [Subsingleton A] :
    Acyc q (sp A) := by
  intro n i hn
  have hfs : RingHom.fst A A = RingHom.snd A A := by
    ext x
    exact Subsingleton.elim _ _
  obtain ⟨_, hsurj⟩ := UpperTheory.twistedCohomology_specProd_bijective_prod q A A n i
  refine ⟨fun u v => ?_⟩
  obtain ⟨x, hx⟩ := hsurj (u, v)
  rw [hfs] at hx
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [← h1, ← h2]

private theorem acyc_pi (q : ℕ) (ι : Type) [Finite ι] :
    ∀ (T : ι → Type) [∀ i, CommRing (T i)], (∀ i, Acyc q (sp (T i))) →
      Acyc q (sp (Π i, T i)) := by
  refine Finite.induction_empty_option (P := fun α => ∀ (T : α → Type) [∀ i, CommRing (T i)],
      (∀ i, Acyc q (sp (T i))) → Acyc q (sp (Π i, T i))) ?_ ?_ ?_ ι
  · intro α β e ih T _ hT
    exact acyc_of_equiv (RingEquiv.piCongrLeft T e) (ih (fun a => T (e a)) (fun a => hT (e a)))
  · intro T _ _
    exact acyc_of_subsingleton
  · intro α _ ih T _ hT
    exact acyc_of_equiv RingEquiv.piOptionEquivProd.symm
      (acyc_prod (hT none) (ih (fun a => T (some a)) (fun a => hT (some a))))

end UpperTheory.Cb.AcycFin


open UpperTheory.Cb.AcycFin in
theorem UpperTheory.acyclic_spec_finite_algebra_strictHenselian :
    ∀ (q : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A], SH O → IsUnit (q : O) → Acyc q (sp A) := by
  intro q O A _ _ _ _ hO _
  obtain ⟨hH, hk⟩ := hO
  obtain ⟨ι, _, T, _, _, e, hT⟩ := GlobalTheory.exists_algEquiv_pi_henselianLocalRing O A
  refine acyc_of_equiv e.symm.toRingEquiv (acyc_pi q ι T fun j => ?_)
  obtain ⟨h1, h2⟩ := hT j
  haveI := h2
  have hs : SH (T j) := sh_of_finite O (T j) ⟨hH, hk⟩ h1
  intro n i hn
  exact UpperTheory.etaleCohomology_functorialityAxioms_hold (ZMod q) (T j) hs (tw q i) n hn
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsFunctionFieldAndChartsOfIsCurveOfIsUnit
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private lemma UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.inc_injective {k K L : Type} [Field k] [Field K] [Algebra k K] [Field L] [Algebra k L]
    (B : Subalgebra k K) : Function.Injective (inc L B) := by
  exact Module.Flat.lTensor_preserves_injective_linearMap (R := k) (M := L) B.val.toLinearMap Subtype.val_injective

private lemma UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.solve {E : Type*} [Field E] {f S T A D : E} {q : ℕ} (hS : S ≠ 0) (hD : D ≠ 0)
    (h : f * (S * D ^ q) = T * A ^ q) : f = T * S⁻¹ * (A * D⁻¹) ^ q := by
  have hDq : D ^ q ≠ 0 := pow_ne_zero _ hD
  rw [mul_pow, inv_pow]
  field_simp
  linear_combination h

theorem UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit :
    Hyps → ∀ (q : ℕ) [NeZero q], ∀ (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → IsFunctionField k C.functionField ∧ Charts k C.functionField q := by
  intro hH q _ k _ _ hq C _ c hc _ hgen
  obtain ⟨hff, n, B, hB, hX⟩ := UpperTheory.isFunctionField_and_chart_cover_of_isCurve k c hc hgen
  refine ⟨hff, n, B, hB, ?_⟩
  intro L _ _ _ F hF hloc
  obtain ⟨X, hXi, u, x, θ, hpb, hic, hcomm, hθ, hfrac, hloc'⟩ := hX L
  have hθF : θ F ≠ 0 := (map_ne_zero_iff θ hθ).mpr hF
  have key := UpperTheory.baseChange_curve_functionField_comp_of_normal hH q k L hq c hc u x hpb hic
    (θ.comp Algebra.TensorProduct.includeRight.toRingHom) hcomm (Units.mk0 (θ F) hθF) (by
      intro y
      obtain ⟨i, m, hm, hw⟩ := hloc' y
      obtain ⟨M, hM, hmM⟩ := Ideal.exists_le_maximal m hm.ne_top
      obtain ⟨s, t, a, b, hs, ht, ha, hb, he⟩ := hloc i M hM
      obtain ⟨ws, hws⟩ := hw s (fun h => hs (hmM h))
      obtain ⟨wt, hwt⟩ := hw t (fun h => ht (hmM h))
      have hinc := UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.inc_injective (L := L) (B i)
      have hne : ∀ z : L ⊗[k] ↥(B i), z ≠ 0 → θ (inc L (B i) z) ≠ 0 := fun z hz =>
        (map_ne_zero_iff θ hθ).mpr ((map_ne_zero_iff _ hinc).mpr hz)
      have hs0 : s ≠ 0 := fun h => hs (h ▸ M.zero_mem)
      have hA := hne a ha
      have hD := hne b hb
      have hS := hne s hs0
      refine ⟨wt * ws⁻¹, Units.mk0 (θ (inc L (B i) a) * (θ (inc L (B i) b))⁻¹) (mul_ne_zero hA (inv_ne_zero hD)), ?_⟩
      have h1 := congrArg θ he
      simp only [map_mul, map_pow] at h1
      rw [Units.val_mk0, Units.val_mk0, Units.val_mul, map_mul, map_units_inv, hws, hwt]
      exact UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.solve hS hD h1)
  obtain ⟨f, h, hfh⟩ := key
  rw [Units.val_mk0] at hfh
  obtain ⟨a, b, hb, hab⟩ := hfrac ↑h
  have hθb : θ b ≠ 0 := (map_ne_zero_iff θ hθ).mpr hb
  refine ⟨f, a, b, ?_, hb, ?_⟩
  · intro ha
    rw [ha, map_zero] at hab
    exact mul_ne_zero h.ne_zero hθb hab
  · apply hθ
    rw [map_mul, map_mul, map_pow, map_pow, ← hab, hfh]
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Algebra.TensorProduct.includeRight_apply]
    ring
end

