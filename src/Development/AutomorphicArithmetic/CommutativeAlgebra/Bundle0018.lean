module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0335
public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Development.AutomorphicArithmetic.BlowupCategories.AffC
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0014
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0015

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.InjectiveProductPushforwardOfInjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

namespace UpperTheory.PwInj

universe u

variable {C : Type u} [Category.{0} C] {S : Type 1} [Ring S]

private noncomputable def lamMap (W : C) (P : Cᵒᵖ ⥤ ModuleCat.{1} S) {T T' : Cᵒᵖ} (h : T ⟶ T') :
    ((T.unop ⟶ W) →₀ P.obj T) →ₗ[S] ((T'.unop ⟶ W) →₀ P.obj T') :=
  Finsupp.lsum ℕ fun g => (Finsupp.lsingle (h.unop ≫ g)).comp (P.map h).hom

private lemma lamMap_single (W : C) (P : Cᵒᵖ ⥤ ModuleCat.{1} S) {T T' : Cᵒᵖ} (h : T ⟶ T')
    (g : T.unop ⟶ W) (m : P.obj T) :
    lamMap W P h (Finsupp.single g m) = Finsupp.single (h.unop ≫ g) ((P.map h).hom m) := by
  simp [lamMap]

private noncomputable def lam (W : C) (P : Cᵒᵖ ⥤ ModuleCat.{1} S) : Cᵒᵖ ⥤ ModuleCat.{1} S where
  obj T := ModuleCat.of S ((T.unop ⟶ W) →₀ P.obj T)
  map h := ModuleCat.ofHom (lamMap W P h)
  map_id T := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro g m
    simp [lamMap_single]
  map_comp f h := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro g m
    simp [lamMap_single]

private lemma mr_single {A : Type} {M N : Type 1} [AddCommGroup M] [AddCommGroup N] [Module S M]
    [Module S N] (f : M →ₗ[S] N) (a : A) (m : M) :
    Finsupp.mapRange.linearMap f (Finsupp.single a m) = Finsupp.single a (f m) := by
  simp

private lemma pmap_op (P : Cᵒᵖ ⥤ ModuleCat.{1} S) {X Y Y' Z : C}
    (a : Y ⟶ X) (b : Z ⟶ Y) (c : Y' ⟶ X) (d : Z ⟶ Y') (h : b ≫ a = d ≫ c) (m : P.obj (op X)) :
    (P.map b.op).hom ((P.map a.op).hom m) = (P.map d.op).hom ((P.map c.op).hom m) := by
  have e := congrArg (fun f : Z ⟶ X => (P.map f.op).hom m) h
  simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  exact e

private lemma pmap_id (P : Cᵒᵖ ⥤ ModuleCat.{1} S) {X Y : C}
    (a : Y ⟶ X) (b : X ⟶ Y) (h : b ≫ a = 𝟙 X) (m : P.obj (op X)) :
    (P.map b.op).hom ((P.map a.op).hom m) = m := by
  have e := congrArg (fun f : X ⟶ X => (P.map f.op).hom m) h
  simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  simpa using e

private noncomputable def lamF (W : C) : (Cᵒᵖ ⥤ ModuleCat.{1} S) ⥤ (Cᵒᵖ ⥤ ModuleCat.{1} S) where
  obj P := lam W P
  map {P Q} φ :=
    { app := fun T => ModuleCat.ofHom (Finsupp.mapRange.linearMap (φ.app T).hom)
      naturality := fun T T' h => by
        apply ModuleCat.hom_ext
        apply Finsupp.lhom_ext
        intro g m
        change Finsupp.mapRange.linearMap (φ.app T').hom (lamMap W P h (Finsupp.single g m)) =
          lamMap W Q h (Finsupp.mapRange.linearMap (φ.app T).hom (Finsupp.single g m))
        rw [lamMap_single, mr_single, mr_single, lamMap_single]
        exact congrArg _ (NatTrans.naturality_apply φ h m) }
  map_id P := by
    ext T : 2
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro g m
    exact mr_single _ g m
  map_comp {P Q Q'} φ ψ := by
    ext T : 2
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro g m
    change Finsupp.mapRange.linearMap ((φ ≫ ψ).app T).hom (Finsupp.single g m) =
      Finsupp.mapRange.linearMap (ψ.app T).hom
        (Finsupp.mapRange.linearMap (φ.app T).hom (Finsupp.single g m))
    rw [mr_single, mr_single, mr_single]
    rfl

private lemma lamF_map_single (W : C) {P Q : Cᵒᵖ ⥤ ModuleCat.{1} S} (φ : P ⟶ Q) (T : Cᵒᵖ)
    (g : T.unop ⟶ W) (m : P.obj T) :
    (((lamF W).map φ).app T).hom (Finsupp.single g m) = Finsupp.single g ((φ.app T).hom m) :=
  mr_single _ g m

private instance (W : C) : (lamF (S := S) W).PreservesMonomorphisms where
  preserves {P Q} φ _ := by
    rw [NatTrans.mono_iff_mono_app]
    intro T
    have h := (NatTrans.mono_iff_mono_app φ).1 inferInstance T
    rw [ModuleCat.mono_iff_injective] at h ⊢
    exact Finsupp.mapRange_injective _ (map_zero _) h

variable [HasBinaryProducts C]


set_option backward.isDefEq.respectTransparency false in
private noncomputable def adjTo (W : C) {P Q : Cᵒᵖ ⥤ ModuleCat.{1} S} (α : lam W P ⟶ Q) :
    P ⟶ (prod.functor.obj W).op ⋙ Q where
  app T := ModuleCat.ofHom
    ((α.app (op (W ⨯ T.unop))).hom ∘ₗ (Finsupp.lsingle (prod.fst : W ⨯ T.unop ⟶ W)) ∘ₗ
      (P.map (prod.snd : W ⨯ T.unop ⟶ T.unop).op).hom)
  naturality T T' h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (α.app (op (W ⨯ T'.unop))).hom (Finsupp.single (prod.fst : W ⨯ T'.unop ⟶ W)
        ((P.map (prod.snd : W ⨯ T'.unop ⟶ T'.unop).op).hom ((P.map h).hom m))) =
      (Q.map ((prod.functor.obj W).map h.unop).op).hom
        ((α.app (op (W ⨯ T.unop))).hom (Finsupp.single (prod.fst : W ⨯ T.unop ⟶ W)
          ((P.map (prod.snd : W ⨯ T.unop ⟶ T.unop).op).hom m)))
    have e := NatTrans.naturality_apply α ((prod.functor.obj W).map h.unop).op
      (Finsupp.single (prod.fst : W ⨯ T.unop ⟶ W) ((P.map (prod.snd : W ⨯ T.unop ⟶ T.unop).op).hom m))
    refine Eq.trans ?_ e
    refine congrArg _ ?_
    change _ = lamMap W P ((prod.functor.obj W).map h.unop).op (Finsupp.single _ _)
    rw [lamMap_single]
    have e1 : ((prod.functor.obj W).map h.unop).op.unop ≫ (prod.fst : W ⨯ T.unop ⟶ W) = prod.fst := by
      simp
    rw [e1]
    refine congrArg _ ?_
    exact pmap_op P h.unop prod.snd prod.snd ((prod.functor.obj W).map h.unop) (by simp) m

private lemma adjTo_app (W : C) {P Q : Cᵒᵖ ⥤ ModuleCat.{1} S} (α : lam W P ⟶ Q) (T : Cᵒᵖ) (m : P.obj T) :
    ((adjTo W α).app T).hom m = (α.app (op (W ⨯ T.unop))).hom (Finsupp.single (prod.fst : W ⨯ T.unop ⟶ W)
      ((P.map (prod.snd : W ⨯ T.unop ⟶ T.unop).op).hom m)) := rfl

private noncomputable def invApp (W : C) {P Q : Cᵒᵖ ⥤ ModuleCat.{1} S}
    (u : P ⟶ (prod.functor.obj W).op ⋙ Q) (T : Cᵒᵖ) :
    ((T.unop ⟶ W) →₀ P.obj T) →ₗ[S] Q.obj T :=
  Finsupp.lsum ℕ fun g => (Q.map (prod.lift g (𝟙 T.unop)).op).hom ∘ₗ (u.app T).hom

set_option backward.isDefEq.respectTransparency false in
private lemma invApp_single (W : C) {P Q : Cᵒᵖ ⥤ ModuleCat.{1} S}
    (u : P ⟶ (prod.functor.obj W).op ⋙ Q) (T : Cᵒᵖ) (g : T.unop ⟶ W) (m : P.obj T) :
    invApp W u T (Finsupp.single g m) = (Q.map (prod.lift g (𝟙 T.unop)).op).hom ((u.app T).hom m) := by
  simp only [invApp, Finsupp.lsum_single, LinearMap.comp_apply]
  try rfl


set_option backward.isDefEq.respectTransparency false in
private noncomputable def adjInv (W : C) {P Q : Cᵒᵖ ⥤ ModuleCat.{1} S}
    (u : P ⟶ (prod.functor.obj W).op ⋙ Q) : lam W P ⟶ Q where
  app T := ModuleCat.ofHom (invApp W u T)
  naturality T T' h := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro g m
    change invApp W u T' (lamMap W P h (Finsupp.single g m)) =
      (Q.map h).hom (invApp W u T (Finsupp.single g m))
    rw [lamMap_single, invApp_single, invApp_single]
    have e : (u.app T').hom ((P.map h).hom m) =
        (Q.map ((prod.functor.obj W).map h.unop).op).hom ((u.app T).hom m) :=
      NatTrans.naturality_apply u h m
    rw [e]
    exact pmap_op Q ((prod.functor.obj W).map h.unop) (prod.lift (h.unop ≫ g) (𝟙 T'.unop))
      (prod.lift g (𝟙 T.unop)) h.unop (by apply Limits.prod.hom_ext <;> simp) _


set_option backward.isDefEq.respectTransparency false in
private noncomputable def lamAdj (W : C) :
    lamF (S := S) W ⊣ (Functor.whiskeringLeft _ _ (ModuleCat.{1} S)).obj (prod.functor.obj W).op :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q =>
        { toFun := adjTo W
          invFun := adjInv W
          left_inv := fun α => by
            ext T : 2
            apply ModuleCat.hom_ext
            apply Finsupp.lhom_ext
            intro g m
            change invApp W (adjTo W α) T (Finsupp.single g m) = (α.app T).hom (Finsupp.single g m)
            rw [invApp_single, adjTo_app]
            have e := NatTrans.naturality_apply α (prod.lift g (𝟙 T.unop)).op
              (Finsupp.single (prod.fst : W ⨯ T.unop ⟶ W) ((P.map (prod.snd : W ⨯ T.unop ⟶ T.unop).op).hom m))
            refine e.symm.trans (congrArg _ ?_)
            change lamMap W P (prod.lift g (𝟙 T.unop)).op _ = _
            rw [lamMap_single]
            have e1 : (prod.lift g (𝟙 T.unop)).op.unop ≫ (prod.fst : W ⨯ T.unop ⟶ W) = g := by simp
            rw [e1]
            refine congrArg _ ?_
            exact (pmap_id P (prod.snd : W ⨯ T.unop ⟶ T.unop) (prod.lift g (𝟙 T.unop)) (by simp) m)
          right_inv := fun u => by
            ext T : 2
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro m
            rw [adjTo_app]
            change invApp W u (op (W ⨯ T.unop)) (Finsupp.single _ _) = _
            rw [invApp_single]
            have e : (u.app (op (W ⨯ T.unop))).hom ((P.map (prod.snd : W ⨯ T.unop ⟶ T.unop).op).hom m) =
                (Q.map ((prod.functor.obj W).map (prod.snd : W ⨯ T.unop ⟶ T.unop)).op).hom ((u.app T).hom m) :=
              NatTrans.naturality_apply u (prod.snd : W ⨯ T.unop ⟶ T.unop).op m
            refine (congrArg (Q.map (prod.lift (prod.fst : W ⨯ T.unop ⟶ W) (𝟙 (W ⨯ T.unop))).op).hom e).trans ?_
            exact pmap_id Q ((prod.functor.obj W).map (prod.snd : W ⨯ T.unop ⟶ T.unop))
              (prod.lift (prod.fst : W ⨯ T.unop ⟶ W) (𝟙 (W ⨯ T.unop)))
              (by apply Limits.prod.hom_ext <;> simp <;> exact Category.id_comp _) _ }
      homEquiv_naturality_left_symm := fun {P P' Q} f g => by
        ext T : 2
        apply ModuleCat.hom_ext
        apply Finsupp.lhom_ext
        intro a m
        change invApp W (f ≫ g) T (Finsupp.single a m) =
          invApp W g T ((((lamF W).map f).app T).hom (Finsupp.single a m))
        rw [lamF_map_single, invApp_single, invApp_single]
        rfl
      homEquiv_naturality_right := fun {P Q Q'} f g => rfl }

end UpperTheory.PwInj


open UpperTheory.PwInj in
private noncomputable def UpperTheory.PwInj.sheafAdj (R : Type) [CommRing R] (W : Scheme.{0}) :
    (sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙ lamF W ⋙
      presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))) ⊣ pw R W :=
  ((lamAdj W).comp (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)))).restrictFullyFaithful
    (iC := sheafToPresheaf _ _) (iD := 𝟭 _)
    (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    (Functor.leftUnitor _ ≪≫ ((prodW W).sheafPushforwardContinuousCompSheafToPresheafIso
      (ModuleCat.{1} (ULift.{1} R)) Scheme.etaleTopology.{0} Scheme.etaleTopology.{0}).symm)

theorem UpperTheory.injective_productPushforward_of_injective :
    ∀ (R : Type) [CommRing R] (W : Scheme.{0}) (J : Shv R) [Injective J], Injective ((pw R W).obj J) := by
  intro R _ W J _
  exact Injective.injective_of_adjoint (UpperTheory.PwInj.sheafAdj R W) J
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsCurvePullbackOfIsCurveBaseChange
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private theorem exists_point {k R : Type} [Field k] [IsAlgClosed k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (m : Ideal R) [m.IsMaximal] :
    ∃ φ : R →ₐ[k] k, ∀ r, φ r = 0 → r ∈ m := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (R ⧸ m) := inferInstance
  haveI : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  haveI : Algebra.IsIntegral k (R ⧸ m) := inferInstance
  let e : k ≃ₐ[k] (R ⧸ m) :=
    AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), fun r hr => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h0 : e.symm (Ideal.Quotient.mk m r) = 0 := hr
  exact (map_eq_zero_iff e.symm e.symm.injective).mp h0

private theorem dom_fg {k R A ι : Type} [Field k] [IsAlgClosed k] [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [CommRing A] [IsDomain A] [Algebra k A] (e : Module.Basis ι k A)
    (s t : Finset ι) (a b : ι → R)
    (h : (∑ i ∈ s, a i ⊗ₜ[k] e i) * (∑ j ∈ t, b j ⊗ₜ[k] e j) = 0) :
    (∀ i ∈ s, a i = 0) ∨ (∀ j ∈ t, b j = 0) := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨i0, hi0, ha⟩, ⟨j0, hj0, hb⟩⟩ := hcon
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
  have hab : a i0 * b j0 ≠ 0 := mul_ne_zero ha hb
  have hjac : (⊥ : Ideal R).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance Ideal.isRadical_bot_of_noZeroDivisors
  have hnot : a i0 * b j0 ∉ (⊥ : Ideal R).jacobson := by
    rw [hjac]
    simpa using hab
  obtain ⟨m, hm, hnm⟩ : ∃ m : Ideal R, m.IsMaximal ∧ a i0 * b j0 ∉ m := by
    by_contra hne
    push_neg at hne
    apply hnot
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro J ⟨-, hJ⟩
    exact hne J hJ
  haveI := hm
  obtain ⟨φ, hφ⟩ := exists_point (k := k) m
  have hφa : φ (a i0) ≠ 0 := fun h0 => hnm (m.mul_mem_right _ (hφ _ h0))
  have hφb : φ (b j0) ≠ 0 := fun h0 => hnm (m.mul_mem_left _ (hφ _ h0))
  let ψ : R ⊗[k] A →ₐ[k] A :=
    Algebra.TensorProduct.lift ((Algebra.ofId k A).comp φ) (AlgHom.id k A) (fun _ _ => Commute.all _ _)
  have hψ : ∀ (c : ι → R) (u : Finset ι),
      ψ (∑ i ∈ u, c i ⊗ₜ[k] e i) = ∑ i ∈ u, φ (c i) • e i := by
    intro c u
    set_option synthInstance.maxHeartbeats 100000 in
      simp [ψ, map_sum, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
  have h2 := congrArg ψ h
  rw [map_mul, hψ, hψ, map_zero] at h2
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hφa ((linearIndependent_iff'.mp e.linearIndependent) s (fun i => φ (a i)) h3 i0 hi0)
  · exact hφb ((linearIndependent_iff'.mp e.linearIndependent) t (fun j => φ (b j)) h3 j0 hj0)

private theorem dom_tensor (k K L : Type) [Field k] [IsAlgClosed k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] : IsDomain (L ⊗[k] K) := by
  classical
  let e := Module.Basis.ofVectorSpace k K
  haveI : Nontrivial (L ⊗[k] K) := inferInstance
  suffices hnz : NoZeroDivisors (L ⊗[k] K) from NoZeroDivisors.to_isDomain _
  refine ⟨fun {x y} hxy => ?_⟩
  let E := TensorProduct.equivFinsuppOfBasisRight (M := L) e
  have hrep : ∀ z : L ⊗[k] K, z = ∑ i ∈ (E z).support, (E z) i ⊗ₜ[k] e i := by
    intro z
    conv_lhs => rw [← E.symm_apply_apply z]
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum]
  let S : Finset L := (E x).support.image (E x) ∪ (E y).support.image (E y)
  let R := Algebra.adjoin k (S : Set L)
  haveI : Algebra.FiniteType k R := Subalgebra.fg_iff_finiteType R |>.mp (Subalgebra.fg_adjoin_finset S)
  have hmem : ∀ (z : L ⊗[k] K), (z = x ∨ z = y) → ∀ i, (E z) i ∈ R := by
    rintro z hz i
    by_cases hi : i ∈ (E z).support
    · apply Algebra.subset_adjoin
      rcases hz with rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)
    · rw [Finsupp.notMem_support_iff.mp hi]
      exact R.zero_mem
  let a : Module.Basis.ofVectorSpaceIndex k K → R := fun i => ⟨(E x) i, hmem x (Or.inl rfl) i⟩
  let b : Module.Basis.ofVectorSpaceIndex k K → R := fun i => ⟨(E y) i, hmem y (Or.inr rfl) i⟩
  let j : R ⊗[k] K →ₐ[k] L ⊗[k] K := Algebra.TensorProduct.map R.val (AlgHom.id k K)
  have hj : Function.Injective j := by
    have := Module.Flat.rTensor_preserves_injective_linearMap (M := K) R.val.toLinearMap Subtype.val_injective
    exact this
  have hja : j (∑ i ∈ (E x).support, a i ⊗ₜ[k] e i) = x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    conv_rhs => rw [hrep x]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [j, a]
  have hjb : j (∑ i ∈ (E y).support, b i ⊗ₜ[k] e i) = y := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    conv_rhs => rw [hrep y]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [j, b]
  have hprod : (∑ i ∈ (E x).support, a i ⊗ₜ[k] e i) * (∑ i ∈ (E y).support, b i ⊗ₜ[k] e i) = 0 := by
    apply hj
    rw [map_mul, hja, hjb, hxy, map_zero]
  rcases dom_fg (k := k) e _ _ a b hprod with h0 | h0
  · left
    rw [hrep x]
    refine Finset.sum_eq_zero fun i hi => ?_
    have := congrArg Subtype.val (h0 i hi)
    simp only [a, ZeroMemClass.coe_zero] at this
    rw [this, TensorProduct.zero_tmul]
  · right
    rw [hrep y]
    refine Finset.sum_eq_zero fun i hi => ?_
    have := congrArg Subtype.val (h0 i hi)
    simp only [b, ZeroMemClass.coe_zero] at this
    rw [this, TensorProduct.zero_tmul]

private theorem gi (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L] :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  constructor
  rw [geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  haveI := dom_tensor k K L
  let e : Y ≅ Spec (CommRingCat.of (L ⊗[k] K)) := h.isoPullback ≪≫ pullbackSpecIso k L K
  haveI : Nonempty Y := ⟨e.inv (Nonempty.some inferInstance)⟩
  exact isIntegral_of_isOpenImmersion e.hom

theorem UpperTheory.isCurve_pullback_of_isCurve_baseChange :
    ∀ (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L] {C : Scheme.{0}} (c : C ⟶ Sp k), IsCurve c → IsCurve (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
  intro k L _ _ _ _ C c hc
  obtain ⟨h1, h2, h3⟩ := hc
  haveI := gi k L
  set g := Spec.map (CommRingCat.ofHom (algebraMap k L)) with hg
  set p := pullback.fst c g with hp
  haveI : GeometricallyIrreducible p := inferInstance
  haveI : GeometricallyReduced p := inferInstance
  haveI : Flat p := inferInstance
  haveI : Finite (irreducibleComponents C) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  haveI hred : IsReduced (pullback c g) :=
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents p
  have hgen : GeneralizingMap p := Flat.generalizingMap p
  set η := genericPoint C
  let ξ : ↥(pullback c g) := p.fiberι η (genericPoint (p.fiber η))
  have hall : ∀ q : ↥(pullback c g), ξ ⤳ q := by
    intro q
    have h0 : η ⤳ p q := genericPoint_specializes _
    obtain ⟨q', hq', hpq'⟩ := hgen h0
    have hmem : q' ∈ Set.range (p.fiberι η) := by
      rw [p.range_fiberι]
      exact hpq'
    obtain ⟨r, rfl⟩ := hmem
    exact ((genericPoint_specializes r).map (p.fiberι η).continuous).trans hq'
  haveI hirr : IrreducibleSpace ↥(pullback c g) := by
    rw [irreducibleSpace_def]
    have hcl : closure ({ξ} : Set ↥(pullback c g)) = Set.univ :=
      Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.mp (hall q)
    rw [Set.top_eq_univ, ← hcl]
    exact isIrreducible_singleton.closure
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, inferInstance, ?_⟩
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) (IsPullback.of_hasPullback c g) h3
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyExistsIsUnitOfSpanRangeEqTop
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem unit_on (T : Scheme.{0}) (f : Γ(T, ⊤)) (W : T.Opens) (h : W ≤ T.basicOpen f) :
    IsUnit ((T.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom f) := by
  apply T.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  rw [TopCat.Presheaf.germ_res_apply]
  exact (T.mem_basicOpen f x trivial).1 (h hx)

private theorem unit_cover (T : Scheme.{0}) {M : ℕ} (v : Fin M → Γ(T, ⊤))
    (hv : Ideal.span (Set.range v) = ⊤) (x : T) : ∃ i, x ∈ T.basicOpen (v i) := by
  have hx : x ∈ (⨆ g ∈ Set.range v, T.basicOpen g) := by
    rw [iSup_basicOpen_of_span_eq_top (X := T) ⊤ _ hv]
    trivial
  simpa [TopologicalSpace.Opens.mem_iSup] using hx

theorem UpperTheory.locally_exists_isUnit_of_span_range_eq_top :
    ∀ (T : Scheme.{0}) {M : ℕ} (v : Fin M → Γ(T, ⊤)), Ideal.span (Set.range v) = ⊤ →
        Loc T fun V g => ∃ i, IsUnit (g.appTop.hom (v i)) := by
  intro T M v hv
  let S : Sieve T :=
    { arrows := fun V g => ∃ i, IsUnit (g.appTop.hom (v i))
      downward_closed := by
        rintro Y Z g ⟨i, hi⟩ k
        refine ⟨i, ?_⟩
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        exact hi.map _ }
  refine ⟨S, ?_, fun V g hg => hg⟩
  have hcov : TopologicalSpace.IsOpenCover (fun i : Fin M => T.basicOpen (v i)) :=
    eq_top_iff.2 (fun x _ => TopologicalSpace.Opens.mem_iSup.2 (unit_cover T v hv x))
  apply Scheme.zariskiTopology_le_etaleTopology
  refine GrothendieckTopology.superset_covering _ ?_
    (Scheme.Cover.mem_grothendieckTopology (T.openCoverOfIsOpenCover _ hcov))
  rintro Z g ⟨W, a, b, ⟨i⟩, rfl⟩
  apply S.downward_closed
  have hu := unit_on T (v i) ((T.basicOpen (v i)).ι ''ᵁ ⊤) (by rw [Scheme.Opens.ι_image_top])
  exact ⟨i, hu⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SurjectiveOfIsPullbackSpecFieldExt
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.surjective_of_isPullback_spec_field_ext :
    ∀ (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → Surjective u := by
  intro k L _ _ _ C X c u x hpb
  have hs : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
    rw [surjective_iff]
    intro p
    obtain ⟨q⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstanceAs (Nonempty (PrimeSpectrum L))
    refine ⟨q, ?_⟩
    exact Subsingleton.elim (α := PrimeSpectrum k) _ _
  exact MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hs
end

