module

public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.MonoOfInjectiveOnSimplices
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

theorem UpperTheory.mono_of_injective_on_simplices :
    ∀ {S S' : Spc} (f : S ⟶ S'), (∀ (k : ℕ) (T : Scheme.{0}), Function.Injective (fun x : Sx S k T => x.map f)) → Mono f := by
  intro S S' f hf
  have hm : ∀ n : SimplexCategoryᵒᵖ, Mono (f.app n) := by
    intro n
    have hm' : ∀ T : Schemeᵒᵖ, Mono ((f.app n).app T) := by
      intro T
      rw [mono_iff_injective]
      exact hf n.unop.len T.unop
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app f
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.NerveFirstProjection
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

private theorem unit_unique {A : Type} [CommRing A] {N : ℕ} (v : Fin N → A)
    (h : Ideal.span (Set.range v) = ⊤) (a b : A) (hab : ∀ j, a * v j = b * v j) : a = b := by
  have h1 : (1 : A) ∈ Ideal.span (Set.range v) := by rw [h]; trivial
  have key : ∀ c ∈ Ideal.span (Set.range v), (a - b) * c = 0 := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [sub_mul, hab, sub_self]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  have h2 := key 1 h1
  rw [mul_one] at h2
  exact sub_eq_zero.1 h2

private theorem fam_inj (D : Type) [CommRing D] (d m : ℕ) {A : Type} [CommRing A]
    (x y : Fin (m + 1) → (L2 D d).obj A)
    (hx : ∀ i j, (L2 D d).rel (x i) (x j)) (hy : ∀ i j, (L2 D d).rel (y i) (y j))
    (h1 : ∀ i, (fstV D d).app A (x i) = (fstV D d).app A (y i))
    (h2 : (x 0).1.1.2 (Fin.last d) = (y 0).1.1.2 (Fin.last d)) : x = y := by
  have hv : ∀ i (j : Fin d), (x i).1.1.2 j.castSucc = (y i).1.1.2 j.castSucc :=
    fun i j => congrFun (congrArg (fun z => z.1.2) (h1 i)) j
  have hr : ∀ i, (x i).1.1.1 = (y i).1.1.1 := fun i => congrArg (fun z => z.1.1) (h1 i)
  refine funext fun i => Subtype.ext (Subtype.ext (Prod.ext (hr i) (funext fun j => ?_)))
  obtain ⟨-, u, hu⟩ := hx i 0
  obtain ⟨-, u', hu'⟩ := hy i 0
  have huu : (u : A) = u' := by
    refine unit_unique (fun j : Fin d => (x 0).1.1.2 j.castSucc) (x 0).2 _ _ fun j => ?_
    have e1 : (x i).1.1.2 j.castSucc = (u : A) * (x 0).1.1.2 j.castSucc := congrFun hu _
    have e2 : (y i).1.1.2 j.castSucc = (u' : A) * (y 0).1.1.2 j.castSucc := congrFun hu' _
    change (u : A) * (x 0).1.1.2 j.castSucc = (u' : A) * (x 0).1.1.2 j.castSucc
    rw [← e1, hv i j, e2, hv 0 j]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have e1 : (x i).1.1.2 (Fin.last d) = (u : A) * (x 0).1.1.2 (Fin.last d) := congrFun hu _
    have e2 : (y i).1.1.2 (Fin.last d) = (u' : A) * (y 0).1.1.2 (Fin.last d) := congrFun hu' _
    change (x i).1.1.2 (Fin.last d) = (y i).1.1.2 (Fin.last d)
    rw [e1, e2, huu, h2]
  · exact hv i j
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SimplicesPullbackExistsUniqueOfMapEq
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

theorem UpperTheory.simplices_pullback_existsUnique_of_map_eq :
    ∀ {A B C : Spc} (r : A ⟶ C) (u : B ⟶ C) (k : ℕ) (T : Scheme.{0}) (x : Sx A k T) (y : Sx B k T), x.map r = y.map u →
        ∃! z : Sx (pullback r u) k T, z.map (pullback.fst r u) = x ∧ z.map (pullback.snd r u) = y := by
  intro A B C r u k T x y h
  let F : Spc ⥤ Type := (evaluation _ _).obj (op (SimplexCategory.mk k)) ⋙ (evaluation _ _).obj (op T)
  have hc := isLimitOfHasPullbackOfPreservesLimit F r u
  let e : Sx (pullback r u) k T ≃ Types.PullbackObj (F.map r) (F.map u) :=
    PullbackCone.IsLimit.equivPullbackObj hc
  have e1 : ∀ z : Sx (pullback r u) k T, (e z).1.1 = z.map (pullback.fst r u) := fun z =>
    PullbackCone.IsLimit.equivPullbackObj_apply_fst hc z
  have e2 : ∀ z : Sx (pullback r u) k T, (e z).1.2 = z.map (pullback.snd r u) := fun z =>
    PullbackCone.IsLimit.equivPullbackObj_apply_snd hc z
  have key : ∀ z : Sx (pullback r u) k T,
      z.map (pullback.fst r u) = x ∧ z.map (pullback.snd r u) = y ↔ e z = ⟨(x, y), h⟩ := by
    intro z
    constructor
    · rintro ⟨h1, h2⟩
      apply Subtype.ext
      apply Prod.ext
      · exact (e1 z).trans h1
      · exact (e2 z).trans h2
    · intro hz
      refine ⟨(e1 z).symm.trans ?_, (e2 z).symm.trans ?_⟩
      · rw [hz]
      · rw [hz]
  refine ⟨e.symm ⟨(x, y), h⟩, (key _).2 (e.apply_symm_apply _), ?_⟩
  intro z hz
  rw [← (key z).1 hz, e.symm_apply_apply]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TopologicalKrullDimLeOfIsOpenImmersionIntegral
section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

private theorem UpperTheory.affine_opens_same_krullDim (k : Type) [Field k] {Y : Scheme.{0}} [IsIntegral Y]
    (t : Y ⟶ Sp k) [LocallyOfFiniteType t] :
    ∃ c : WithBot ℕ∞, ∀ U : Y.Opens, IsAffineOpen U → Nonempty U → ringKrullDim Γ(Y, U) = c := by
  classical
  let iso : k →+* Γ(Sp k, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hiso : Function.Surjective iso := by
    intro y
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom y, ?_⟩
    change ((Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom y = y
    simp
  have eT : (⊤ : Y.Opens) ≤ t ⁻¹ᵁ ⊤ := le_top
  haveI : Nonempty (⊤ : Y.Opens) := ⟨⟨Nonempty.some (inferInstance : Nonempty Y), trivial⟩⟩
  let φ : k →+* Y.functionField := (Y.germToFunctionField ⊤).hom.comp ((t.appLE ⊤ ⊤ eT).hom.comp iso)
  letI : Algebra k Y.functionField := φ.toAlgebra
  refine ⟨((Algebra.trdeg k Y.functionField).toENat : WithBot ℕ∞), ?_⟩
  intro U hU hne
  have eU : U ≤ t ⁻¹ᵁ ⊤ := le_top
  letI : Algebra k Γ(Y, U) := ((t.appLE ⊤ U eU).hom.comp iso).toAlgebra
  haveI : Algebra.FiniteType k Γ(Y, U) := by
    have h1 : (t.appLE ⊤ U eU).hom.FiniteType :=
      t.finiteType_appLE (isAffineOpen_top _) hU eU
    exact h1.comp (RingHom.FiniteType.of_surjective _ hiso)
  haveI : IsFractionRing Γ(Y, U) Y.functionField := functionField_isFractionRing_of_isAffineOpen Y U hU
  haveI : IsScalarTower k Γ(Y, U) Y.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change φ x = (Y.germToFunctionField U).hom ((t.appLE ⊤ U eU).hom (iso x))
    simp only [φ, RingHom.comp_apply]
    rw [← Scheme.Hom.appLE_map t eT (homOfLE (le_top : U ≤ ⊤)).op]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, Scheme.germToFunctionField]
    exact (TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (le_top : U ≤ ⊤)) _ _ _).symm
  exact GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg_fractionRing k Y.functionField

theorem UpperTheory.topologicalKrullDim_le_of_isOpenImmersion_integral :
    ∀ (k : Type) [Field k] {Y D : Scheme.{0}} [IsIntegral Y] (t : Y ⟶ Sp k) [LocallyOfFiniteType t] (j : D ⟶ Y) [IsOpenImmersion j] [Nonempty D], topologicalKrullDim Y ≤ topologicalKrullDim D := by
  intro k _ Y D _ t _ j _ _
  obtain ⟨c, hc⟩ := UpperTheory.affine_opens_same_krullDim k t
  have hdim : ∀ U : Y.Opens, IsAffineOpen U → Nonempty U → topologicalKrullDim U = c := by
    intro U hU hne
    rw [← hc U hU hne, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph
  have hup : topologicalKrullDim Y ≤ c := by
    apply GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen
    intro x
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨A, A.isOpen, hxA, (hdim A hA ⟨⟨x, hxA⟩⟩).le⟩
  have hemb := j.isOpenEmbedding
  obtain ⟨d⟩ := ‹Nonempty D›
  obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAsub⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_range_self d) hemb.isOpen_range
  have hZ := GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hemb.isEmbedding rfl
  have hAZ := GlobalTheory.topologicalKrullDim_eq_of_isEmbedding (Topology.IsEmbedding.inclusion hAsub) rfl
  have hle := topologicalKrullDim_subspace_le (Set.range _) (Set.range (Set.inclusion hAsub))
  rw [hAZ, hZ] at hle
  exact hup.trans ((hdim A hA ⟨⟨_, hyA⟩⟩).symm.le.trans hle)
end

