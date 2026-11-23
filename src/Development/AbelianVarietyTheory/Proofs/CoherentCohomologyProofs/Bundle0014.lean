module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsPowMulPowEqOfIsZeroCechH
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexAcyclicIffQuasiIsoCechAug

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexPolyGradingFiniteExact
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem finite_neg_sum_eq (ι : Type) [Fintype ι] (n : ℤ) :
    {a : {a : ι → ℤ // ∑ i, a i = n} |
      Finset.univ.filter (fun i => a.1 i < 0) = Finset.univ}.Finite := by
  classical
  refine Set.Finite.subset ((Set.finite_Icc (fun _ : ι => n) (fun _ => 0)).preimage
    Subtype.val_injective.injOn) ?_
  rintro ⟨a, ha⟩ h
  have h' : ∀ i, a i < 0 := fun i => Finset.filter_eq_self.1 h i (Finset.mem_univ i)
  refine ⟨fun i => ?_, fun i => (h' i).le⟩
  have := Finset.add_sum_erase Finset.univ a (Finset.mem_univ i)
  have h2 : ∑ j ∈ Finset.univ.erase i, a j ≤ 0 := Finset.sum_nonpos fun j _ => (h' j).le
  change n ≤ a i
  omega

theorem cubeComplex_polyGrading_finite_exact : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (n : ℤ), (∀ p, Module.Finite R ((cubeComplex (grCube ι (polyGrading ι R) n)).homology p)) ∧ (1 ≤ n → ∀ p, (cubeComplex (grCube ι (polyGrading ι R) n)).ExactAt p) := by
  intro ι _ _ R _ n
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.exists_basis_grCube_polyGrading ι R n
  have h1 := GlobalTheory.cubeComplex_exactAt_of_monomialBasis ι R _ _ _ b hb
  have h2 := GlobalTheory.CubeTop.main ι R _ _ _ b hb
  refine ⟨fun p => ?_, fun hn p => ?_⟩
  · by_cases hp : p = Fintype.card ι
    · subst hp
      exact h2.2 (finite_neg_sum_eq ι n)
    · have := ModuleCat.subsingleton_of_isZero
        ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h1 p hp))
      infer_instance
  · by_cases hp : p = Fintype.card ι
    · subst hp
      refine h2.1 ?_
      rintro ⟨a, ha⟩ h
      have h' : ∀ i, a i < 0 := fun i => Finset.filter_eq_self.1 h i (Finset.mem_univ i)
      have : ∑ i, a i ≤ 0 := Finset.sum_nonpos fun j _ => (h' j).le
      omega
    · exact h1 p hp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGradedPresentationSaturating
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_graded_presentation_saturating : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G] [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢] [Decomposition 𝒢], (∀ i : ι, Module.FinitePresentation (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) G)) → ∃ (a b : ℕ) (d : Fin a → ℤ) (e : Fin b → ℤ) (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)) (ψ : ((Fin a → MvPolynomial ι R) ⧸ LinearMap.range Φ.mulVecLin) →ₗ[MvPolynomial ι R] G), (∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) ∧ IsGradedMap (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) 𝒢 ψ ∧ ∀ i : ι, (∀ y, ψ y = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0) ∧ (∀ z : G, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range ψ) := by
  intro ι _ _ R _ G _ _ _ _ 𝒢 _ _ hG
  obtain ⟨a, d, g, hg, hsat⟩ := exists_homogeneous_family_saturating ι R G 𝒢 fun i =>
    _root_.GlobalTheory.exists_X_pow_smul_mem_span_of_finite_quot ι R G 𝒢 i (haveI := hG i; inferInstance)
  set φ := Fintype.linearCombination (MvPolynomial ι R) g with hφdef
  have hφ : IsGradedMap (grFree ι R d) 𝒢 φ := isGradedMap_linearCombination 𝒢 hg
  have hsat' : ∀ (i : ι) (z : G), ∃ k : ℕ,
      (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range φ := by
    intro i z
    rw [hφdef, Fintype.range_linearCombination]
    exact hsat i z
  let _ : Decomposition (grSub (grFree ι R d) (LinearMap.ker φ)) :=
    grSubDecomposition _ hφ.isHomogeneous_ker
  obtain ⟨b, e, κ, hκ, hksat⟩ := exists_homogeneous_family_saturating ι R (LinearMap.ker φ)
    (grSub (grFree ι R d) (LinearMap.ker φ)) fun i =>
      _root_.GlobalTheory.exists_X_pow_smul_mem_span_of_finite_quot ι R _ (grSub (grFree ι R d) (LinearMap.ker φ)) i
        (GlobalTheory.finite_quotSMulTop_ker_of_graded ι R _ (grFree ι R d) G 𝒢 φ i hφ inferInstance (hsat' i) (hG i))
  let Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R) := Matrix.of fun l j => (κ j).1 l
  have hrange : LinearMap.range Φ.mulVecLin =
      (Submodule.span (MvPolynomial ι R) (Set.range κ)).map (LinearMap.ker φ).subtype := by
    rw [Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp]
    rfl
  have hle : LinearMap.range Φ.mulVecLin ≤ LinearMap.ker φ := by
    rw [hrange]
    exact Submodule.map_subtype_le _ _
  refine ⟨a, b, d, e, Φ, Submodule.liftQ _ φ hle, fun l j => ?_, hφ.liftQ _ hle,
    fun i => ⟨fun y hy => ?_, fun z => ?_⟩⟩
  · have := mem_grPi.1 (mem_grSub.1 (hκ j)) l
    rw [sub_eq_add_neg]
    exact this
  · obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨k, hk⟩ := hksat i ⟨x, hy⟩
    refine ⟨k, ?_⟩
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hrange]
    exact ⟨_, hk, rfl⟩
  · rw [Submodule.range_liftQ]
    exact hsat' i z

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PresheafCubeExactAtSuccOfSurjective
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

universe w v u

noncomputable section

namespace GlobalTheory

section Presheaf

variable {T : TopCat.{w}} {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
  {P : (Opens T)ᵒᵖ ⥤ ModuleCat.{w} R} (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
  (hs : ∀ ⦃W W' : Opens T⦄ (h : W' ≤ W), Function.Surjective (presheafRes P h))

include hP hs

end Presheaf

section Ab

variable {T : TopCat.{w}} {ι : Type}

variable [LinearOrder ι] [Finite ι] (F : TopCat.Sheaf AddCommGrpCat.{w} T) [F.IsFlasque]

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] in
private theorem cubeComplex_exactAt_one_of_hom_surj_empty_inj_nonempty {A B : _root_.GlobalTheory.Cube ι R} (φ : A ⟶ B)
    (hsurj : ∀ s : Finset ι, s = ∅ → Function.Surjective (φ.app s))
    (hinj : ∀ s : Finset ι, s.Nonempty → Function.Injective (φ.app s))
    (hB : (_root_.GlobalTheory.cubeComplex B).ExactAt 1) : (_root_.GlobalTheory.cubeComplex A).ExactAt 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, _root_.GlobalTheory.cubeComplex_exactAt_succ_iff] at hB ⊢
  have comm : ∀ p (x : A.Term p), (_root_.GlobalTheory.cubeComplexMap φ).f (p + 1) (A.d p x) =
      B.d p ((_root_.GlobalTheory.cubeComplexMap φ).f p x) := by
    intro p x
    have := congrArg (fun f => f.hom x) ((_root_.GlobalTheory.cubeComplexMap φ).comm p (p + 1))
    simp only [_root_.GlobalTheory.cubeComplex, CochainComplex.of_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.coe_comp, Function.comp_apply] at this
    exact this.symm
  have dd : ∀ y : A.Term 0, A.d 1 (A.d 0 y) = 0 := by
    intro y
    have := congrArg (fun f => f.hom y) ((_root_.GlobalTheory.cubeComplex A).d_comp_d 0 1 2)
    simpa [_root_.GlobalTheory.cubeComplex, LinearMap.comp_apply] using this
  have inj1 : Function.Injective ((_root_.GlobalTheory.cubeComplexMap φ).f 1) := by
    intro x y hxy
    funext s
    apply hinj s.1 (Finset.card_pos.mp (by rw [s.2]; norm_num))
    exact congrFun hxy s
  have surj0 : Function.Surjective ((_root_.GlobalTheory.cubeComplexMap φ).f 0) := by
    intro y
    refine ⟨fun s => (hsurj s.1 (Finset.card_eq_zero.mp s.2) (y s)).choose, ?_⟩
    funext s
    exact (hsurj s.1 (Finset.card_eq_zero.mp s.2) (y s)).choose_spec
  intro x
  constructor
  · intro hx
    have h1 : B.d 1 ((_root_.GlobalTheory.cubeComplexMap φ).f 1 x) = 0 := by
      rw [← comm 1 x]
      change (_root_.GlobalTheory.cubeComplexMap φ).f 2 (A.d 1 x) = 0
      rw [show A.d 1 x = 0 from hx]
      exact map_zero _
    obtain ⟨y, hy⟩ := (hB ((_root_.GlobalTheory.cubeComplexMap φ).f 1 x)).1 h1
    obtain ⟨z, rfl⟩ := surj0 y
    exact ⟨z, inj1 ((comm 0 z).trans hy)⟩
  · rintro ⟨y, rfl⟩
    exact dd y

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite in
variable {T : TopCat.{w}} {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
  {P : (Opens T)ᵒᵖ ⥤ ModuleCat.{w} R} (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
  (hs : ∀ ⦃W W' : Opens T⦄ (h : W' ≤ W), Function.Surjective (_root_.GlobalTheory.presheafRes P h)) in
include hP hs in
private theorem cubeComplex_presheafCube_exactAt_one (V : Opens T) (U : ι → Opens T) :
    (_root_.GlobalTheory.cubeComplex (_root_.GlobalTheory.presheafCube P V U)).ExactAt 1 := by
  have h : ∀ s, _root_.GlobalTheory.cechOpen (V ⊓ ⨆ i, U i) U s ≤ _root_.GlobalTheory.cechOpen V U s :=
    fun s => _root_.GlobalTheory.cechOpen_mono (V := V) (U := U) (hV := inf_le_left)
      (hU := fun _ => le_rfl) s
  refine cubeComplex_exactAt_one_of_hom_surj_empty_inj_nonempty (_root_.GlobalTheory.presheafCubeRes P h) ?_ ?_
    (_root_.GlobalTheory.presheafCube_exactAt_zero_one hP (V := V ⊓ ⨆ i, U i) (U := U) inf_le_right).2
  · rintro s rfl
    exact hs (h ∅)
  · intro s hs' x y hxy
    have h' : _root_.GlobalTheory.cechOpen V U s ≤ _root_.GlobalTheory.cechOpen (V ⊓ ⨆ i, U i) U s := by
      intro z hz
      rw [_root_.GlobalTheory.mem_cechOpen] at hz ⊢
      obtain ⟨j, hj⟩ := hs'
      exact ⟨⟨hz.1, Opens.mem_iSup.mpr ⟨j, hz.2 j hj⟩⟩, hz.2⟩
    have back : ∀ (O O' : Opens T) (h₁ : O' ≤ O) (h₂ : O ≤ O') (w : P.obj (op O)),
        P.map (homOfLE h₂).op (P.map (homOfLE h₁).op w) = w := by
      intro O O' h₁ h₂ w
      rw [← ConcreteCategory.comp_apply, ← P.map_comp,
        show (homOfLE h₁).op ≫ (homOfLE h₂).op = 𝟙 _ from Subsingleton.elim _ _]
      simp
    have key : ∀ w, P.map (homOfLE h').op ((_root_.GlobalTheory.presheafCubeRes P h).app s w) = w :=
      fun w => back _ _ (h s) h' w
    rw [← key x, ← key y, hxy]

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite in
variable {T : TopCat.{w}} {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
  {P : (Opens T)ᵒᵖ ⥤ ModuleCat.{w} R} (hP : Presheaf.IsSheaf (Opens.grothendieckTopology T) P)
  (hs : ∀ ⦃W W' : Opens T⦄ (h : W' ≤ W), Function.Surjective (_root_.GlobalTheory.presheafRes P h)) in
include hP hs in
private theorem cubeComplex_presheafCube_exactAt_add_one_of_card (n : ℕ) :
    ∀ {α : Type} [LinearOrder α] [Fintype α], Fintype.card α = n →
      ∀ (V : Opens T) (U : α → Opens T) (p : ℕ),
        (_root_.GlobalTheory.cubeComplex (_root_.GlobalTheory.presheafCube P V U)).ExactAt (p + 1) := by
  induction n with
  | zero =>
    intro α _ _ hcard V U p
    rw [_root_.GlobalTheory.cubeComplex_exactAt_succ_iff]
    have : Subsingleton ((_root_.GlobalTheory.presheafCube P V U).Term (p + 1)) :=
      _root_.GlobalTheory.Cube.subsingleton_term _ (by omega)
    have : Subsingleton ((_root_.GlobalTheory.presheafCube P V U).Term (p + 1 + 1)) :=
      _root_.GlobalTheory.Cube.subsingleton_term _ (by omega)
    intro x
    exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  | succ n ih =>
    intro α _ _ hcard V U p
    cases p with
    | zero => exact cubeComplex_presheafCube_exactAt_one hP hs V U
    | succ p =>
      obtain ⟨i⟩ : Nonempty α := Fintype.card_pos_iff.mp (by omega)
      let e : {j : α // j ≠ i} ↪o α := OrderEmbedding.subtype _
      have he : Set.range e = {i}ᶜ := by
        ext j
        simp [e]
      have hcard' : Fintype.card {j : α // j ≠ i} = n := by
        simp [Fintype.card_subtype_compl, hcard]
      apply _root_.GlobalTheory.cubeComplex_exactAt_succ_of_faces he
      · exact (ih hcard' V (fun k => U (e k)) (p + 1)).of_iso
          ((_root_.GlobalTheory.cubeFunctor _ R).mapIso (_root_.GlobalTheory.presheafCubeLowerFaceIso P V U e)).symm
      · exact (ih hcard' (V ⊓ U i) (fun k => U (e k)) p).of_iso
          ((_root_.GlobalTheory.cubeFunctor _ R).mapIso (_root_.GlobalTheory.presheafCubeUpperFaceIso P V U e i)).symm


open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite in
variable {T : TopCat.{w}} {ι : Type} in
variable [LinearOrder ι] [Finite ι] (F : TopCat.Sheaf AddCommGrpCat.{w} T) [F.IsFlasque] in
theorem _root_.GlobalTheory.subsingleton_cechAbH_succ_of_isFlasque (V : Opens T) (U : ι → Opens T) (p : ℕ) :
    Subsingleton (_root_.GlobalTheory.cechAbH F.obj V U (p + 1)) := by
  have := Fintype.ofFinite ι
  have hP := _root_.GlobalTheory.isSheaf_comp_abToIntModule F.property
  have hs : ∀ ⦃W W' : Opens T⦄ (h : W' ≤ W),
      Function.Surjective (_root_.GlobalTheory.presheafRes (F.obj ⋙ _root_.GlobalTheory.abToIntModule) h) := by
    intro W W' h
    have : Epi (F.obj.map (homOfLE h).op) := TopCat.Presheaf.IsFlasque.epi _
    exact (AddCommGrpCat.epi_iff_surjective _).mp this
  have hex := cubeComplex_presheafCube_exactAt_add_one_of_card hP hs _ rfl V U (p + 1)
  have hcech := (_root_.GlobalTheory.cechComplex_exactAt_succ_iff_cube _ p).mpr hex
  exact ModuleCat.subsingleton_of_isZero hcech.isZero_homology

end Ab

section Modules

variable {X : Scheme.{u}} {ι : Type} (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
  (F : X.Modules) [hF : TopCat.Presheaf.IsFlasque (X := X.toPresheafedSpace.carrier) F.presheaf]

include hF

variable [LinearOrder ι] [Finite ι]

end Modules

end GlobalTheory
end
end

