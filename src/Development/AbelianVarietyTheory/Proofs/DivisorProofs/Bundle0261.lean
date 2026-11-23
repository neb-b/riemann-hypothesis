module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0181
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0195
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvalEqOfMultiplicativeOnPoints
section
open scoped TensorProduct

namespace GlobalTheory

open scoped TensorProduct in
private lemma eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced {C V : Type} [Field C] [IsAlgClosed C] [CommRing V]
    [Algebra C V] [Module.Finite C V] [IsReduced V] (v : V) (hv : ∀ z : V →ₐ[C] C, z v = 0) :
    v = 0 := by
  haveI : IsArtinianRing V := IsArtinianRing.of_finite C V
  have hmem : v ∈ (⊥ : Ideal V).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro m ⟨-, hm⟩
    letI : Field (V ⧸ m) := Ideal.Quotient.field m
    have hsurj : Function.Surjective (algebraMap C (V ⧸ m)) := IsSepClosed.algebraMap_surjective C _
    let eqv : C ≃ₐ[C] V ⧸ m := AlgEquiv.ofBijective (Algebra.ofId C (V ⧸ m))
      ⟨(algebraMap C (V ⧸ m)).injective, hsurj⟩
    have h := hv (eqv.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C m))
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.coe_toAlgHom,
      AlgHom.coe_coe] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((map_eq_zero_iff _ eqv.symm.injective).mp h)
  rw [IsArtinianRing.jacobson_eq_radical] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact IsReduced.eq_zero v ⟨n, by simpa using hn⟩

open scoped TensorProduct in
private lemma exists_eq_one_and_eq_zero_of_ne_algHom {C V : Type} [Field C] [CommRing V] [Algebra C V]
    [Fintype (V →ₐ[C] C)] (z : V →ₐ[C] C) :
    ∃ w : V, z w = 1 ∧ ∀ z' : V →ₐ[C] C, z' ≠ z → z' w = 0 := by
  have hsep : ∀ z' : V →ₐ[C] C, z' ≠ z → ∃ a : V, z a ≠ z' a := by
    intro z' hz'
    by_contra h
    push_neg at h
    exact hz' (AlgHom.ext fun a => (h a).symm)
  classical
  let u : (V →ₐ[C] C) → V := fun z' =>
    if h : z' ≠ z then
      (z (hsep z' h).choose - z' (hsep z' h).choose)⁻¹ •
        ((hsep z' h).choose - algebraMap C V (z' (hsep z' h).choose))
    else 1
  have hu : ∀ z', z (u z') = 1 := by
    intro z'
    by_cases h : z' ≠ z
    · simp only [u, dif_pos h, map_smul, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, smul_eq_mul]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr (hsep z' h).choose_spec)
    · simp only [u]
      rw [dite_eq_right h, map_one]
  have hu' : ∀ z', z' ≠ z → z' (u z') = 0 := by
    intro z' h
    simp only [u]
    rw [dif_pos h]
    simp
  refine ⟨∏ z' ∈ Finset.univ.erase z, u z', ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_eq_one fun z' _ => hu z'
  · intro z' hz'
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hz', Finset.mem_univ _⟩) (hu' z' hz')

open scoped TensorProduct in
private lemma sum_sum_mul_sub_mul_mul_eq_zero_of_sum_mul_eq {C ι : Type} [Field C] [Fintype ι] (c X Y : ι → C)
    (M : ι → ι → ι → C)
    (h : ∑ k, c k * ∑ i, ∑ j, M k i j * (X i * Y j) = (∑ i, c i * X i) * ∑ j, c j * Y j) :
    ∑ j, (∑ i, (∑ k, c k * M k i j - c i * c j) * X i) * Y j = 0 := by
  have e1 : ∑ j, (∑ i, (∑ k, c k * M k i j - c i * c j) * X i) * Y j =
      ∑ k, c k * ∑ i, ∑ j, M k i j * (X i * Y j) - (∑ i, c i * X i) * ∑ j, c j * Y j := by
    simp only [Finset.sum_mul, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    congr 1
    · conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e1, h, sub_self]


open scoped TensorProduct in
theorem _root_.GlobalTheory.exists_eval_eq_of_multiplicative_on_points : ∀ (O C A : Type) [CommRing O] [IsDomain O] [Field C] [IsAlgClosed C] [Algebra O C] [IsFractionRing O C] [IsIntegrallyClosed O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Free O A], IsReduced (C ⊗[O] A) → ∀ (Δ : A →ₐ[O] A ⊗[O] A) (ε : A →ₐ[O] O) (κ : (A →ₐ[O] C) → C), (∀ x y : A →ₐ[O] C, κ ((Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)).comp Δ) = κ x * κ y) → κ ((Algebra.ofId O C).comp ε) = 1 → ∃ b : A, ∀ x : A →ₐ[O] C, x b = κ x := by
  intro O C A _ _ _ _ _ _ _ _ _ _ _ hred Δ ε κ hmul _
  classical
  let e := Module.Free.chooseBasis O A
  let eC : Module.Basis (Module.Free.ChooseBasisIndex O A) C (C ⊗[O] A) :=
    Algebra.TensorProduct.basis C e
  let ext : (A →ₐ[O] C) → (C ⊗[O] A →ₐ[C] C) := fun x =>
    Algebra.TensorProduct.lift (Algebra.ofId C C) x (fun _ _ => Commute.all _ _)
  let res : (C ⊗[O] A →ₐ[C] C) → (A →ₐ[O] C) := fun z =>
    (z.restrictScalars O).comp Algebra.TensorProduct.includeRight
  have hres : ∀ x, res (ext x) = x := by
    intro x
    ext a
    simp [res, ext]
  have hevC : ∀ (z : C ⊗[O] A →ₐ[C] C) (a : Module.Free.ChooseBasisIndex O A → C),
      z (∑ i, a i • eC i) = ∑ i, a i * res z (e i) := by
    intro z a
    set_option synthInstance.maxHeartbeats 100000 in
      simp [eC, res, map_sum, Algebra.TensorProduct.basis_apply]
  have hcoord : ∀ a : Module.Free.ChooseBasisIndex O A → C,
      (∀ x : A →ₐ[O] C, ∑ i, a i * x (e i) = 0) → a = 0 := by
    intro a ha
    have hv : ∑ i, a i • eC i = 0 := by
      refine eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced (C := C) _ fun z => ?_
      rw [hevC]
      exact ha (res z)
    funext i
    have hi := congrArg (fun v => eC.repr v i) hv
    simpa [Finsupp.single_apply] using hi
  haveI : Finite (C ⊗[O] A →ₐ[C] C) := (linearIndependent_toLinearMap C (C ⊗[O] A) C).finite
  letI : Fintype (C ⊗[O] A →ₐ[C] C) := Fintype.ofFinite _
  choose w hw1 hw0 using fun z : C ⊗[O] A →ₐ[C] C => exists_eq_one_and_eq_zero_of_ne_algHom z
  let b' : C ⊗[O] A := ∑ z, κ (res z) • w z
  let c := eC.repr b'
  have hval : ∀ x, κ x = ∑ i, c i * x (e i) := by
    intro x
    have h1 : ext x b' = κ x := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [b', map_sum, map_smul, smul_eq_mul]
      rw [Finset.sum_eq_single (ext x)]
      · rw [hw1, mul_one, hres]
      · intro z _ hz
        rw [hw0 z (ext x) (Ne.symm hz), mul_zero]
      · simp
    rw [← h1]
    conv_lhs => rw [← eC.sum_repr b']
    rw [hevC, hres]
  let m : Module.Free.ChooseBasisIndex O A → Module.Free.ChooseBasisIndex O A →
      Module.Free.ChooseBasisIndex O A → O := fun k i j => (e.tensorProduct e).repr (Δ (e k)) (i, j)
  have hprod : ∀ (x y : A →ₐ[O] C) k,
      (Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)) (Δ (e k)) =
        ∑ i, ∑ j, algebraMap O C (m k i j) * (x (e i) * y (e j)) := by
    intro x y k
    conv_lhs => rw [← (e.tensorProduct e).sum_repr (Δ (e k))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Module.Basis.tensorProduct_apply,
      Algebra.smul_def, Fintype.sum_prod_type, map_mul, AlgHom.commutes,
      Algebra.TensorProduct.lift_tmul, m]
  have key : ∀ x y : A →ₐ[O] C, ∑ j, (∑ i, (∑ k, c k * algebraMap O C (m k i j) - c i * c j) *
      x (e i)) * y (e j) = 0 := by
    intro x y
    have h := hmul x y
    simp only [hval, AlgHom.comp_apply, hprod] at h
    exact sum_sum_mul_sub_mul_mul_eq_zero_of_sum_mul_eq c (fun i => x (e i)) (fun j => y (e j))
      (fun k i j => algebraMap O C (m k i j)) h
  have hrel : ∀ i j, c i * c j = ∑ k, c k * algebraMap O C (m k i j) := by
    have h1 : ∀ j, ∀ x : A →ₐ[O] C,
        ∑ i, (∑ k, c k * algebraMap O C (m k i j) - c i * c j) * x (e i) = 0 := by
      intro j x
      exact congrFun (hcoord (fun j => ∑ i, (∑ k, c k * algebraMap O C (m k i j) - c i * c j) *
        x (e i)) (key x)) j
    intro i j
    have h2 := congrFun (hcoord (fun i => ∑ k, c k * algebraMap O C (m k i j) - c i * c j) (h1 j)) i
    exact (sub_eq_zero.mp h2).symm
  let M : Submodule O C := Submodule.span O (insert 1 (Set.range c))
  have hcM : ∀ i, c i ∈ M := fun i => Submodule.subset_span (Set.mem_insert_of_mem 1 ⟨i, rfl⟩)
  have hoM : (1 : C) ∈ M := Submodule.subset_span (Set.mem_insert 1 _)
  have hMM : M * M ≤ M := by
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨s, hs, t, ht, rfl⟩
    rcases hs with rfl | ⟨i, rfl⟩ <;> rcases ht with rfl | ⟨j, rfl⟩ <;> dsimp only
    · rw [one_mul]
      exact hoM
    · rw [one_mul]
      exact hcM j
    · rw [mul_one]
      exact hcM i
    · rw [hrel]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (hcM k)
  let S : Subalgebra O C :=
    M.toSubalgebra hoM fun u v hu hv => hMM (Submodule.mul_mem_mul hu hv)
  have hfg : (Subalgebra.toSubmodule S).FG := Submodule.fg_span ((Set.finite_range c).insert 1)
  have hint : ∀ i, ∃ o : O, algebraMap O C o = c i := fun i =>
    IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.of_mem_of_fg S hfg _ (hcM i))
  choose o ho using hint
  refine ⟨∑ i, o i • e i, fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hval, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.smul_def, ho]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitFiniteTypeIntRings
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.FiniteTypeColimit

noncomputable def diagram (A : CommRingCat.{0}) : Finset A ⥤ CommRingCat.{0} where
  obj t := CommRingCat.of (Algebra.adjoin ℤ (t : Set A))
  map {s t} h := CommRingCat.ofHom
    (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.2 (leOfHom h)))).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def inclusions (A : CommRingCat.{0}) : diagram A ⟶ (Functor.const (Finset A)).obj A where
  app t := CommRingCat.ofHom (Algebra.adjoin ℤ (t : Set A)).val.toRingHom
  naturality _ _ _ := rfl

noncomputable def isColimit (A : CommRingCat.{0}) : IsColimit (Cocone.mk A (inclusions A)) := by
  classical
  haveI : ReflectsColimit (diagram A) (forget CommRingCat.{0}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{0}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun i x y hxy => ?_)
  · exact ⟨{x}, ⟨x, Algebra.subset_adjoin (by simp)⟩, rfl⟩
  · have : x = y := Subtype.ext hxy
    exact ⟨i, 𝟙 i, by rw [this]⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.FiniteTypeColimit.finiteType (A : CommRingCat.{0}) (t : Finset A) :
    Algebra.FiniteType ℤ ((_root_.GlobalTheory.FiniteTypeColimit.diagram A).obj t) := by
  have h : (Algebra.adjoin ℤ (t : Set A)).FG := Subalgebra.fg_adjoin_finset t
  have := (Subalgebra.fg_iff_finiteType _).1 h
  change Algebra.FiniteType ℤ (CommRingCat.of (Algebra.adjoin ℤ (t : Set A)))
  convert this


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType : ∀ A : CommRingCat.{0},
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
      (ι : D ⟶ (Functor.const J).obj A),
      Nonempty (IsColimit (Cocone.mk A ι)) ∧ ∀ j, Algebra.FiniteType ℤ (D.obj j) :=
  fun A => ⟨Finset A, inferInstance, inferInstance, _root_.GlobalTheory.FiniteTypeColimit.diagram A,
    _root_.GlobalTheory.FiniteTypeColimit.inclusions A, ⟨_root_.GlobalTheory.FiniteTypeColimit.isColimit A⟩,
    _root_.GlobalTheory.FiniteTypeColimit.finiteType A⟩

end GlobalTheory.FiniteTypeColimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCoequifiberedSubalgebra
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub

theorem exists_finite_coequifibered_subalgebra : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → (∀ U : X.Opens, IsAffineOpen U → (α.app (Opposite.op U)).hom.IsIntegral) → ∀ (n : ℕ) (U : Fin n → X.AffineZariskiSite) (S : ∀ k, Finset (F.obj (Opposite.op (U k).1))), ∃ (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α' : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (ι : F' ⟶ (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ F), α'.Coequifibered ∧ α' ≫ ι = (Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α ∧ (∀ V, Function.Injective (ι.app V).hom) ∧ (∀ V, (α'.app V).hom.Finite) ∧ ∀ k, ∀ x ∈ S k, ∃ y, (ι.app (Opposite.op (U k))).hom y = x := by
  intro X hX F α hα hint n U S
  obtain ⟨t, ht⟩ := (isCompact_univ (X := X)).elim_finite_subcover
    (fun A : X.AffineZariskiSite => (A.1 : Set X)) (fun A => A.1.isOpen) (by
      intro x _
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩)
  let V : Fin n ⊕ t → X.Opens := Sum.elim (fun k => (U k).1) (fun A => A.1.1)
  have hV : ∀ j, IsAffineOpen (V j) := by
    rintro (k | A)
    exacts [(U k).2, A.1.2]
  have hcov : ∀ x : X, ∃ j, x ∈ V j := by
    intro x
    obtain ⟨A, hA, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨.inr ⟨A, hA⟩, hx⟩
  let S' : ∀ j, Set (F.obj (op (V j))) := fun j =>
    Sum.rec (motive := fun j => Set (F.obj (op (V j)))) (fun k => ((S k : Set (F.obj (op (U k).1))))) (fun _ => ∅) j
  have hS' : ∀ j, (S' j).Finite := by
    rintro (k | A)
    exacts [(S k).finite_toSet, Set.finite_empty]
  obtain ⟨T, hTfin, hST⟩ := _root_.GlobalTheory.sub_choose_finite X hX F α hα V hV S' hS'
  refine ⟨subFunctor F α V T, subNat F α V T, subIncl F α V T,
    GlobalTheory.T.coequifibered_generated_subalgebra_quasiCoherent X F α hα V T (_root_.GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen X hX F α hα V hV T), subNat_comp_subIncl F α V T,
    subIncl_injective F α V T,
    fun W => GlobalTheory.T.finite_cut_out_subalgebra_quasiCoherent X hX F α hα hint V hV hcov T hTfin W.unop.1 W.unop.2,
    fun k x hx => ⟨⟨x, hST (.inl k) (Finset.mem_coe.mpr hx)⟩, rfl⟩⟩

end GlobalTheory.QcSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDepthTwoHullOfEtalePuncturedSpectrum
section
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem exists_finite_depth_two_hull_of_etale_off_closed_point : ∀ (S : Type) [CommRing S] [IsRegularLocalRing S], 2 ≤ ringKrullDim S → ∀ (A : Type) [CommRing A] [Algebra S A] [Module.Finite S A], ReciprocityTheory.CA.ModDepthGE S A 1 → (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) → ∃ (A' : Type) (_ : CommRing A') (_ : Algebra S A'), Module.Finite S A' ∧ ∃ ι : A →ₐ[S] A', Function.Injective ι ∧ ReciprocityTheory.CA.ModDepthGE S A' 2 ∧ (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A')) ∧ ∃ k : ℕ, ∀ x ∈ maximalIdeal S ^ k, ∀ y : A', x • y ∈ ι.range := by
  intro S _ _ hdim A _ _ _ hdep het
  obtain ⟨hSd, hSic⟩ := isDomain_and_isIntegrallyClosed_of_isRegularLocalRing S
  have htf : ∀ s : S, s ≠ 0 → IsSMulRegular A s := _root_.GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos_domain S A hdep het
  let K := FractionRing S
  let j : A →ₐ[S] K ⊗[S] A := Algebra.TensorProduct.includeRight
  have hj : ∀ a, j a = TensorProduct.mk S K A 1 a := fun a => rfl
  haveI : IsLocalizedModule (nonZeroDivisors S) (TensorProduct.mk S K A 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors S) K _).mpr (TensorProduct.isBaseChange S A K)
  have hjinj : Function.Injective j := by
    intro a b hab
    rw [hj, hj] at hab
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors S) hab
    exact htf c (nonZeroDivisors.coe_ne_zero c) hc

  have hVtf : ∀ s : S, s ≠ 0 → ∀ v w : K ⊗[S] A, s • v = s • w → v = w := by
    intro s hs v w h
    rw [← algebraMap_smul K s v, ← algebraMap_smul K s w] at h
    have hs' : algebraMap S K s ≠ 0 := by
      rw [ne_eq, ← map_zero (algebraMap S K)]
      exact fun e => hs (IsFractionRing.injective S K e)
    exact smul_right_injective _ hs' h
  let B := idealTransform S (maximalIdeal S) A
  have hjB : ∀ a, j a ∈ B := fun a => ⟨0, fun b _ => ⟨b • a, by simp [j]⟩⟩
  let ι : A →ₐ[S] B := j.codRestrict B hjB
  have hιinj : Function.Injective ι := fun a b h => hjinj (congrArg Subtype.val h)
  have hrange : ∀ y : B, y ∈ ι.range ↔ (y : K ⊗[S] A) ∈ j.range := by
    intro y
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
    · rintro ⟨a, ha⟩; exact ⟨a, Subtype.ext ha⟩

  have hfg : (Subalgebra.toSubmodule B).FG := by
    refine _root_.GlobalTheory.fg_of_saturated_ideal_power_into_image S (maximalIdeal S) (_root_.GlobalTheory.isInteger_of_maximalIdeal_pow_smul_isInteger S hdim) A _ fun z hz => ?_
    obtain ⟨k, hk⟩ := hz
    exact ⟨k, fun a ha => by obtain ⟨b, hb⟩ := hk a ha; exact ⟨b, hb⟩⟩
  haveI hfin : Module.Finite S B := Module.Finite.iff_fg.mpr hfg

  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ a ∈ maximalIdeal S ^ k, ∀ y : B, a • y ∈ ι.range.toSubmodule := by
    refine _root_.GlobalTheory.Submodule.exists_pow_smul_mem_of_forall_exists S (maximalIdeal S) B _ fun y => ?_
    obtain ⟨k, hk⟩ := y.2
    exact ⟨k, fun a ha => (hrange _).2 (hk a ha)⟩
  refine ⟨B, inferInstance, inferInstance, hfin, ι, hιinj, ?_, ?_, k, hk⟩
  ·
    obtain ⟨q, -, hq0, hqm⟩ := exists_isPrime_ne_bot_lt_maximalIdeal_of_two_le_ringKrullDim S hdim
    have hm0 : maximalIdeal S ≠ ⊥ := (bot_le.trans_lt hqm).ne'
    obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm0
    haveI : Nontrivial A := by
      obtain ⟨rs, -, -, hreg⟩ := hdep
      by_contra hA
      rw [not_nontrivial_iff_subsingleton] at hA
      exact hreg.2 (Subsingleton.elim _ _)
    haveI : Nontrivial B := nontrivial_of_ne (ι 0) (ι 1) (hιinj.ne zero_ne_one)
    have hxreg : IsSMulRegular B x := fun u v h =>
      Subtype.ext (hVtf x hx0 _ _ (congrArg Subtype.val h))
    refine _root_.GlobalTheory.modDepthGE_two_of_isSMulRegular_of_quotSMulTop S B x hxm hxreg fun u hu => ?_
    let w : K ⊗[S] A := (algebraMap S K x)⁻¹ • (u : K ⊗[S] A)
    have hxw : x • w = u := by
      simp only [w, ← algebraMap_smul K x, smul_smul]
      rw [mul_inv_cancel₀, one_smul]
      rw [ne_eq, ← map_zero (algebraMap S K)]
      exact fun e => hx0 (IsFractionRing.injective S K e)
    have hwB : w ∈ B := by
      refine mem_idealTransform_of_forall_smul_mem w fun a ha => ?_
      obtain ⟨v, -, hv⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp (hu a ha)
      have : a • w = v := by
        apply hVtf x hx0
        rw [smul_comm, hxw]
        exact (congrArg Subtype.val hv).symm
      rw [this]; exact v.2
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨⟨w, hwB⟩, Submodule.mem_top, Subtype.ext hxw⟩
  · intro p _ hp
    have hnot : ¬ maximalIdeal S ^ k ≤ p := fun h =>
      hp ((maximalIdeal.isMaximal S).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
        (Ideal.IsPrime.le_of_pow_le h)).symm
    obtain ⟨s, hs, hsp⟩ := Set.not_subset.mp hnot
    exact GlobalTheory.T.etale_localization_of_injective_cokernel_killed S A B ι hιinj p s hsp (hk s hs) (het p hp)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtPointLiftOfSurjectiveLocFinType
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem exists_finite_ext_point_lift_of_surjective_lft :
    ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), LocallyOfFiniteType π → Function.Surjective π →
      ∀ (K : Type) [Field K] (x : Sp K ⟶ X),
        ∃ (K' : Type) (_ : Field K') (σ : K →+* K') (y : Sp K' ⟶ Y),
          σ.Finite ∧ y ≫ π = spMap σ ≫ x := by
  intro X Y π hft hs K _ x
  haveI : Surjective π := ⟨hs⟩
  let P := Limits.pullback π x
  let s : P ⟶ Sp K := Limits.pullback.snd π x
  haveI : LocallyOfFiniteType s := inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd π x))
  haveI : Surjective s := inferInstanceAs (Surjective (Limits.pullback.snd π x))
  haveI : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace s
  obtain ⟨p₀, -⟩ := s.surjective (default : Sp K)
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set P)) ⟨p₀, trivial⟩
    isClosed_univ.isLocallyClosed
  haveI : IsClosedImmersion (P.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.mp hz
  haveI : IsFinite (P.fromSpecResidueField z ≫ s) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  let φ := Spec.preimage (P.fromSpecResidueField z ≫ s)
  have hφ : Spec.map φ = P.fromSpecResidueField z ≫ s := Spec.map_preimage _
  refine ⟨P.residueField z, inferInstance, φ.hom,
    P.fromSpecResidueField z ≫ Limits.pullback.fst π x, ?_, ?_⟩
  · rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  · have h2 : spMap φ.hom = P.fromSpecResidueField z ≫ s := hφ
    rw [h2]
    exact (Category.assoc _ _ _).trans ((congrArg (P.fromSpecResidueField z ≫ ·)
      Limits.pullback.condition).trans (Category.assoc _ _ _).symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFixedUnitsModFixedSquares
section
open NumberField IsDedekindDomain GlobalTheory.FixNormCls
open scoped Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.UnitSq

def fixedUnits (E : Type) [Field E] [NumberField E] (τ : E ≃+* E) : Subgroup (𝓞 E)ˣ where
  carrier := {u | τ ((u : 𝓞 E) : E) = ((u : 𝓞 E) : E)}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at *
    rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h1 : ((a⁻¹ : (𝓞 E)ˣ) : 𝓞 E) * (a : 𝓞 E) = 1 := by simp
    have h1' : (((a⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) * (((a : 𝓞 E) : E)) = 1 := by
      exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) h1
    have h2 : (((a⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) = (((a : 𝓞 E) : E))⁻¹ :=
      eq_inv_of_mul_eq_one_left h1'
    rw [h2, map_inv₀, ha]

end GlobalTheory.UnitSq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueSpecLocalizationAwayMorphismsStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_spec_localizationAway_morphisms : ∀ (S : Type) [CommRing S] (ι : Type) (s : ι → S), Ideal.span (Set.range s) = ⊤ →
    ∀ (Y : Scheme.{0}) (e : ∀ i, Sp (Localization.Away (s i)) ⟶ Y),
    (∀ i j, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (s i * s j)) (s i) (s j)) ≫ e i =
      spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (s i * s j)) (s j) (s i)) ≫ e j) →
    ∃ a : Sp S ⟶ Y, ∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a = e i := by
  first | exact @GlobalTheory.SecGlue.glue_away | exact GlobalTheory.SecGlue.glue_away | (intros; apply GlobalTheory.SecGlue.glue_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitDetKrylovMatrixOfSeparableStatement
section
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnit_det_krylovMatrix_of_separable : ∀ {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F), y.charpoly.Separable → ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det := by
  first | exact @GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable | exact GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable | (intros; apply GlobalTheory.LeviDesc.Krylov.exists_isUnit_det_krylov_of_separable <;> assumption)
end

