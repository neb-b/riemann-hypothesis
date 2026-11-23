module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentation
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeEighthPowerOfMatrixAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.MatrixPower

section General

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

@[reducible] def retractGrpObj {G A : C} [GrpObj G] (i : A ⟶ G) (r : G ⟶ A) (hir : i ≫ r = 𝟙 A)
    [he : IsMonHom (r ≫ i)] : GrpObj A :=
  haveI : Mono i := (SplitMono.mk r hir).mono
  have h1 : ∀ {T : C}, ((1 : T ⟶ G) ≫ r) ≫ i = 1 := fun {T} => by
    rw [Category.assoc, MonObj.one_comp]
  have h2 : ∀ {T : C} (a b : T ⟶ A), ((a ≫ i * b ≫ i) ≫ r) ≫ i = a ≫ i * b ≫ i := fun a b => by
    rw [Category.assoc, MonObj.mul_comp]; simp [reassoc_of% hir]
  have h3 : (i⁻¹ ≫ r) ≫ i = i⁻¹ := by
    rw [Category.assoc, GrpObj.inv_comp]; simp [reassoc_of% hir]
  { one := (1 : 𝟙_ C ⟶ G) ≫ r
    mul := (fst A A ≫ i * snd A A ≫ i) ≫ r
    inv := i⁻¹ ≫ r
    one_mul := by
      rw [← cancel_mono i, Category.assoc, h2, MonObj.comp_mul, whiskerRight_fst_assoc,
        whiskerRight_snd_assoc, h1]
      simp [leftUnitor_hom]
    mul_one := by
      rw [← cancel_mono i, Category.assoc, h2, MonObj.comp_mul, whiskerLeft_fst_assoc,
        whiskerLeft_snd_assoc, h1]
      simp [rightUnitor_hom]
    mul_assoc := by
      rw [← cancel_mono i, Category.assoc, h2, Category.assoc, Category.assoc, h2,
        MonObj.comp_mul, whiskerRight_fst_assoc, whiskerRight_snd_assoc, h2,
        MonObj.comp_mul (A ◁ _), whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, h2]
      simp [MonObj.comp_mul, _root_.mul_assoc]
    left_inv := by
      rw [← cancel_mono i, Category.assoc, h2, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
        h3, Category.assoc, h1]
      simp
    right_inv := by
      rw [← cancel_mono i, Category.assoc, h2, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
        h3, Category.assoc, h1]
      simp }

private theorem isMonHom_of_one_comp_of_mul_comp {M N : C} [MonObj M] [MonObj N] (f : M ⟶ N)
    (h1 : (1 : 𝟙_ C ⟶ M) ≫ f = 1)
    (h2 : (fst M M * snd M M) ≫ f = fst M M ≫ f * snd M M ≫ f) : IsMonHom f :=
  { one_hom := by rw [MonObj.one_eq_one M, MonObj.one_eq_one N, h1]
    mul_hom := by
      rw [MonObj.mul_eq_mul M, MonObj.mul_eq_mul N, h2, MonObj.comp_mul, tensorHom_fst,
        tensorHom_snd] }

theorem exists_grpObj_retract {G A : C} [GrpObj G] (i : A ⟶ G) (r : G ⟶ A) (hir : i ≫ r = 𝟙 A)
    [he : IsMonHom (r ≫ i)] : ∃ _ : GrpObj A, IsMonHom i ∧ IsMonHom r := by
  let gA : GrpObj A := retractGrpObj i r hir
  have hm : ∀ {T : C} (a b : T ⟶ A), a * b = (a ≫ i * b ≫ i) ≫ r := by
    intro T a b
    rw [Hom.mul_def]
    change lift a b ≫ (fst A A ≫ i * snd A A ≫ i) ≫ r = _
    rw [← Category.assoc, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  have ho : ∀ {T : C}, (1 : T ⟶ A) = (1 : T ⟶ G) ≫ r := by
    intro T
    rw [Hom.one_def]
    change toUnit T ≫ (1 : 𝟙_ C ⟶ G) ≫ r = _
    rw [← Category.assoc, MonObj.comp_one]
  refine ⟨gA, ?_, ?_⟩
  · refine isMonHom_of_one_comp_of_mul_comp i ?_ ?_
    · rw [ho, Category.assoc, MonObj.one_comp]
    · rw [hm, Category.assoc, MonObj.mul_comp]
      simp only [Category.assoc, reassoc_of% hir]
  · refine isMonHom_of_one_comp_of_mul_comp r ho.symm ?_
    rw [hm]
    calc (fst G G * snd G G) ≫ r = ((fst G G * snd G G) ≫ (r ≫ i)) ≫ r := by
          simp only [Category.assoc, hir, Category.comp_id]
      _ = _ := by rw [MonObj.mul_comp]; simp only [Category.assoc]

variable [BraidedCategory C]

theorem comp_prod {n : Type*} (s : Finset n) {T X G : C} [GrpObj G] [IsCommMonObj G]
    (f : T ⟶ X) (g : n → (X ⟶ G)) : f ≫ ∏ u ∈ s, g u = ∏ u ∈ s, f ≫ g u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, MonObj.comp_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

theorem prod_comp {n : Type*} (s : Finset n) {T G H : C} [GrpObj G] [IsCommMonObj G]
    [GrpObj H] [IsCommMonObj H] (g : n → (T ⟶ G)) (f : G ⟶ H) [IsMonHom f] :
    (∏ u ∈ s, g u) ≫ f = ∏ u ∈ s, g u ≫ f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, MonObj.one_comp]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.mul_comp, ih]

theorem exists_power [HasEqualizers C] {n : Type*} [Fintype n] [DecidableEq n] (o : n)
    (G : C) [GrpObj G] [IsCommMonObj G] (ρ : Matrix n n ℤ → (G ⟶ G))
    (hρ : ∀ m, IsMonHom (ρ m)) (hmul : ∀ m m', ρ (m * m') = ρ m' ≫ ρ m)
    (hadd : ∀ m m', ρ (m + m') = ρ m * ρ m') (hone : ρ 1 = 𝟙 G) :
    ∃ (A : C) (_ : GrpObj A) (_ : IsCommMonObj A) (_ : Retract A G) (pr : n → (G ⟶ A)),
      (∀ u, IsMonHom (pr u)) ∧
      (∀ (T : C) (y : n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) ∧
      ∀ m u, ρ m ≫ pr u = ∏ v, pr v ^ m u v := by
  have : ∀ m, IsMonHom (ρ m) := hρ
  have hc : ∀ a b : Matrix n n ℤ, ρ a ≫ ρ b = ρ (b * a) := fun a b => (hmul b a).symm
  have h0 : ρ 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hneg : ∀ a, ρ (-a) = (ρ a)⁻¹ := fun a =>
    eq_inv_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
  have hsum : ∀ (s : Finset n) (f : n → Matrix n n ℤ), ρ (∑ v ∈ s, f v) = ∏ v ∈ s, ρ (f v) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty, h0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]
  have hzs : ∀ (k : ℤ) (a : Matrix n n ℤ), ρ (k • a) = ρ a ^ k := by
    intro k a
    refine Int.induction_on k ?_ ?_ ?_
    · rw [zero_smul, h0, zpow_zero]
    · intro j ih
      rw [add_smul, one_smul, hadd, ih, zpow_add_one]
    · intro j ih
      rw [sub_smul, one_smul, sub_eq_add_neg, hadd, ih, hneg, zpow_sub_one]
  have hidem : ρ (Matrix.single o o 1) ≫ ρ (Matrix.single o o 1) =
      ρ (Matrix.single o o 1) ≫ 𝟙 G := by
    rw [Category.comp_id, hc, Matrix.single_mul_single_same, _root_.mul_one]
  obtain ⟨A, i, r, hir, hri⟩ : ∃ (A : C) (i : A ⟶ G) (r : G ⟶ A),
      i ≫ r = 𝟙 A ∧ r ≫ i = ρ (Matrix.single o o 1) := by
    refine ⟨equalizer (ρ (Matrix.single o o 1)) (𝟙 G), equalizer.ι _ _, equalizer.lift _ hidem,
      ?_, equalizer.lift_ι _ _⟩
    apply equalizer.hom_ext
    rw [Category.assoc, equalizer.lift_ι, Category.id_comp]
    exact (equalizer.condition _ _).trans (Category.comp_id _)
  have hmono : Mono i := (SplitMono.mk r hir).mono
  have : IsMonHom (r ≫ i) := by rw [hri]; infer_instance
  obtain ⟨gA, hi, hr⟩ := exists_grpObj_retract i r hir
  have hcA : IsCommMonObj A :=
    (isCommMonObj_iff_isMulCommutative _).2 fun X => ⟨⟨fun a b => by
      show a * b = b * a
      rw [← cancel_mono i, MonObj.mul_comp, MonObj.mul_comp, mul_comm]⟩⟩
  refine ⟨A, gA, hcA, ⟨i, r, hir⟩,
    fun u => ρ (Matrix.single o u 1) ≫ r, fun u => inferInstance, ?_, ?_⟩
  · intro T y
    refine ⟨∏ v, y v ≫ i ≫ ρ (Matrix.single v o 1), fun u => ?_, fun x hx => ?_⟩
    · dsimp only
      rw [prod_comp, Finset.prod_eq_single u]
      · have h3 : ρ (Matrix.single u o 1) ≫ ρ (Matrix.single o u 1) ≫ r = r ≫ i ≫ r := by
          rw [← Category.assoc, hc, Matrix.single_mul_single_same, _root_.mul_one, ← hri,
            Category.assoc]
        simp only [Category.assoc]
        rw [h3, reassoc_of% hir, hir, Category.comp_id]
      · intro v _ hv
        have h3 : ρ (Matrix.single v o 1) ≫ ρ (Matrix.single o u 1) ≫ r = 1 := by
          have h5 : Matrix.single o u (1 : ℤ) * Matrix.single v o 1 = 0 := by
            simp [Ne.symm hv]
          rw [← Category.assoc, hc, h5, h0, MonObj.one_comp]
        simp only [Category.assoc]
        rw [h3, MonObj.comp_one, MonObj.comp_one]
      · intro h
        exact absurd (Finset.mem_univ u) h
    · dsimp only at hx
      have h1 : (1 : Matrix n n ℤ) = ∑ v, Matrix.single v v 1 := by
        ext a b
        by_cases hab : a = b
        · subst hab
          simp [Matrix.sum_apply, Matrix.single_apply]
        · rw [Matrix.sum_apply, Finset.sum_eq_zero]
          · exact Matrix.one_apply_ne hab
          · intro v _
            rw [Matrix.single_apply]
            split_ifs with h
            · exact absurd (h.1.symm.trans h.2) hab
            · rfl
      calc x = x ≫ ρ 1 := by rw [hone, Category.comp_id]
        _ = ∏ v, x ≫ ρ (Matrix.single v v 1) := by rw [h1, hsum, comp_prod]
        _ = _ := by
          refine Finset.prod_congr rfl fun v _ => ?_
          rw [← hx v]
          have h4 : ρ (Matrix.single o v 1) ≫ r ≫ i ≫ ρ (Matrix.single v o 1) =
              ρ (Matrix.single v v 1) := by
            rw [reassoc_of% hri, hc, Matrix.single_mul_single_same, hc,
              Matrix.single_mul_single_same]
            simp only [_root_.mul_one]
          simp only [Category.assoc, h4]
  · intro m u
    dsimp only
    have hrow : Matrix.single o u (1 : ℤ) * m = ∑ v, m u v • Matrix.single o v 1 := by
      ext a b
      by_cases ha : a = o
      · subst ha
        simp [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply]
      · simp [Matrix.mul_apply, Matrix.sum_apply, Ne.symm ha]
    have := hcA
    rw [← Category.assoc, hc, hrow, hsum, prod_comp]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hzs, GrpObj.zpow_comp]

end General

theorem abelianScheme_matrix_power : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (ρ : Matrix (Fin 8) (Fin 8) ℤ → (G ⟶ G)), IsAbelianScheme G → (∀ m, IsMonHom (ρ m)) → (∀ m m', ρ (m * m') = ρ m' ≫ ρ m) → (∀ m m', ρ (m + m') = ρ m * ρ m') → ρ 1 = 𝟙 G → ∃ (A : Over S) (_ : GrpObj A) (pr : Fin 8 → (G ⟶ A)), IsAbelianScheme A ∧ (∀ u, IsMonHom (pr u)) ∧ (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) ∧ ∀ m u, ρ m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod := by
  intro S G _ ρ hab hρ hmul hadd hone
  obtain ⟨hcomm, hsmooth, hproper, hgeo⟩ := hab
  obtain ⟨A, gA, hcA, R, pr, hpr, huniv, hact⟩ := exists_power (0 : Fin 8) G ρ hρ hmul hadd hone
  obtain ⟨-, -, -, hsm, -, -, -, -, hpro, -, hgc, -, -⟩ := GlobalTheory.Retract.over_properties R
  refine ⟨A, gA, pr, ⟨hcA, hsm hsmooth, hpro hproper, hgc hgeo⟩, hpr, huniv, fun m u => ?_⟩
  rw [hact, List.prod_ofFn]

end GlobalTheory.MatrixPower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AlgebraMapSurjectiveOfUnramifiedOfUniquePoint
section
open scoped TensorProduct

namespace GlobalTheory

theorem algebraMap_surjective_of_unramified_of_unique_point (K A : Type) [Field K] [IsAlgClosed K]
    [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.FormallyUnramified K A]
    (φ : A →ₐ[K] K) (hφ : ∀ ψ : A →ₐ[K] K, ψ = φ) : Function.Surjective (algebraMap K A) := by
  haveI : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field K A
  have hker : ∀ a : A, φ a = 0 → a = 0 := by
    intro a ha
    apply IsNilpotent.eq_zero
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    have hb : Function.Bijective (algebraMap K (A ⧸ J)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : K ≃ₐ[K] (A ⧸ J) := AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ J)) hb
    have h := hφ ((e.symm : (A ⧸ J) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K J))
    rw [← h] at ha
    have h2 : e.symm (Ideal.Quotient.mk J a) = 0 := ha
    rw [map_eq_zero_iff _ e.symm.injective] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  intro a
  refine ⟨φ a, ?_⟩
  rw [← sub_eq_zero]
  apply hker
  simp

theorem nontrivial_tensor_of_mem_support (R C K : Type) [CommRing R] [AddCommGroup C] [Module R C]
    [Module.Finite R C] [Field K] [Algebra R K] (p : PrimeSpectrum R)
    (hp : RingHom.ker (algebraMap R K) = p.asIdeal) (h : p ∈ Module.support R C) :
    Nontrivial (K ⊗[R] C) := by
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at h
  let g : p.asIdeal.ResidueField →+* K := Ideal.ResidueField.lift p.asIdeal (algebraMap R K)
    hp.ge (by
      intro r hr
      have : algebraMap R K r ≠ 0 := fun h0 => hr (hp.le h0)
      exact (isUnit_iff_ne_zero.mpr this))
  letI : Algebra p.asIdeal.ResidueField K := g.toAlgebra
  haveI : IsScalarTower R p.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq (by
    intro r
    exact (Ideal.ResidueField.lift_algebraMap ..).symm)
  haveI : Nontrivial (K ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[R] C)) :=
    inferInstance
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField K K
    C).symm.toEquiv.nontrivial

open scoped TensorProduct in
private lemma algebraMap_injective_of_denseP_unique_lift {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    (P : Set (Ideal R)) (hP : _root_.GlobalTheory.ZM.DenseP P)
    (hpt : ∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K),
      RingHom.ker x = q ∧ ∃! y : B →+* K, y.comp (algebraMap R B) = x) :
    Function.Injective (algebraMap R B) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  apply hP a
  intro p hp _
  obtain ⟨K, _, _, x, hx, y, hy, -⟩ := hpt p hp
  rw [← hx, RingHom.mem_ker, ← hy, RingHom.comp_apply, ha, map_zero]

open scoped TensorProduct in
private lemma algebraMap_surjective_of_unique_algHom (K A : Type) [Field K] [IsAlgClosed K] [CommRing A]
    [Algebra K A] [Module.Finite K A] [Algebra.FormallyUnramified K A]
    (φ₀ : A →ₐ[K] K) (hφ₀ : ∀ φ : A →ₐ[K] K, φ = φ₀) : Function.Surjective (algebraMap K A) := by
  haveI := Algebra.FormallyUnramified.isReduced_of_field K A
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  have hφ₀s : Function.Surjective φ₀ := fun c => ⟨algebraMap K A c, by simp⟩
  have hmax : ∀ m : Ideal A, m.IsMaximal → m = RingHom.ker φ₀ := by
    intro m hm
    letI := Ideal.Quotient.field m
    have hs : Function.Surjective (algebraMap K (A ⧸ m)) := IsSepClosed.algebraMap_surjective K (A ⧸ m)
    let e : K ≃ₐ[K] A ⧸ m := AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ m))
      ⟨(algebraMap K (A ⧸ m)).injective, hs⟩
    have h := hφ₀ ((e.symm : (A ⧸ m) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K m))
    rw [← h]
    ext a
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  haveI : IsLocalRing A := IsLocalRing.of_unique_max_ideal
    ⟨RingHom.ker φ₀, RingHom.ker_isMaximal_of_surjective _ hφ₀s, fun m hm => hmax m hm⟩
  have hfield := IsArtinianRing.isField_of_isReduced_of_isLocalRing A
  have hinj : Function.Injective φ₀ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hne
    have := congrArg φ₀ hb
    simp [ha] at this
  intro a
  exact ⟨φ₀ a, hinj (by simp)⟩

open scoped TensorProduct in
private lemma exists_smul_mem_range_algebraMap_of_unique_lift {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra.FormallyUnramified R B] {K : Type} [Field K] [IsAlgClosed K]
    (x : R →+* K) (hy : ∃! y : B →+* K, y.comp (algebraMap R B) = x) :
    ∃ f : R, f ∉ RingHom.ker x ∧ ∀ b : B, ∃ a : R, f • b = algebraMap R B a := by
  letI : Algebra R K := x.toAlgebra
  obtain ⟨y, hyx, hyu⟩ := hy
  let y' : B →ₐ[R] K := { y with commutes' := fun r => congrArg (fun g : R →+* K => g r) hyx }
  let φ₀ : K ⊗[R] B →ₐ[K] K := Algebra.TensorProduct.productLeftAlgHom (AlgHom.id K K) y'
  have hΦ : ∀ φ : K ⊗[R] B →ₐ[K] K, φ = φ₀ := by
    intro φ
    have h1 : ((φ.restrictScalars R).comp Algebra.TensorProduct.includeRight).toRingHom = y := by
      apply hyu
      ext r
      exact ((φ.restrictScalars R).comp Algebra.TensorProduct.includeRight).commutes r
    have h2 : ((φ₀.restrictScalars R).comp Algebra.TensorProduct.includeRight).toRingHom = y := by
      apply hyu
      ext r
      exact ((φ₀.restrictScalars R).comp Algebra.TensorProduct.includeRight).commutes r
    apply Algebra.TensorProduct.ext (Subsingleton.elim _ _)
    apply AlgHom.coe_ringHom_injective
    exact h1.trans h2.symm
  have hsurj := algebraMap_surjective_of_unique_algHom K (K ⊗[R] B) φ₀ hΦ
  let N : Submodule R B := LinearMap.range (Algebra.linearMap R B)
  have hsub : Subsingleton (K ⊗[R] (B ⧸ N)) := by
    refine ⟨fun u v => ?_⟩
    have key : ∀ w : K ⊗[R] (B ⧸ N), w = 0 := by
      intro w
      obtain ⟨t, rfl⟩ := LinearMap.lTensor_surjective K (Submodule.mkQ_surjective N) w
      obtain ⟨c, rfl⟩ := hsurj t
      have h1 : (N.mkQ (1 : B)) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact ⟨1, by simp⟩
      simp [Algebra.TensorProduct.algebraMap_apply, h1]
    rw [key u, key v]
  have hq : (RingHom.ker x).IsPrime := RingHom.ker_isPrime x
  let xb : (RingHom.ker x).ResidueField →+* K := Ideal.ResidueField.lift (RingHom.ker x) x le_rfl
    (fun a ha => by
      simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
      exact ha)
  letI : Algebra (RingHom.ker x).ResidueField K := xb.toAlgebra
  haveI : IsScalarTower R (RingHom.ker x).ResidueField K := IsScalarTower.of_algebraMap_eq (fun r => by
    simp [xb, RingHom.algebraMap_toAlgebra])
  have hsub2 : Subsingleton ((RingHom.ker x).ResidueField ⊗[R] (B ⧸ N)) := by
    have e := TensorProduct.AlgebraTensorModule.cancelBaseChange R (RingHom.ker x).ResidueField K K (B ⧸ N)
    haveI : Subsingleton (K ⊗[(RingHom.ker x).ResidueField] ((RingHom.ker x).ResidueField ⊗[R] (B ⧸ N))) :=
      e.toEquiv.subsingleton
    exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right _ _).mp this
  have hns : (⟨RingHom.ker x, hq⟩ : PrimeSpectrum R) ∉ Module.support R (B ⧸ N) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial_iff_subsingleton.mpr hsub2
  rw [Module.mem_support_iff_of_finite] at hns
  obtain ⟨f, hfann, hfq⟩ := SetLike.not_le_iff_exists.mp hns
  refine ⟨f, hfq, fun b => ?_⟩
  have h0 := Module.mem_annihilator.mp hfann (N.mkQ b)
  rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨a, ha⟩ := h0
  exact ⟨a, by simpa using ha.symm⟩


open scoped TensorProduct in
theorem _root_.GlobalTheory.algebraMap_bijective_of_unramified_of_unique_geometric_point :
    ∀ (R B : Type) [CommRing R] [IsReduced R] [CommRing B] [Algebra R B] [Module.Finite R B]
      [Algebra.FormallyUnramified R B] (P : Set (Ideal R)),
      (∀ (q : Ideal R) (f : R), q.IsPrime → f ∉ q → ∃ p ∈ P, p.IsPrime ∧ q ≤ p ∧ f ∉ p) →
      (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K),
        RingHom.ker x = q ∧ ∃! y : B →+* K, y.comp (algebraMap R B) = x) →
      Function.Bijective (algebraMap R B) := by
  intro R B _ _ _ _ _ _ P hP hpt
  have hdense : _root_.GlobalTheory.ZM.DenseP P := by
    intro a ha
    apply IsReduced.eq_zero
    rw [nilpotent_iff_mem_prime]
    intro q hq
    by_contra haq
    obtain ⟨p, hpP, hp, -, hap⟩ := hP q a hq haq
    exact hap (ha p hpP hp)
  refine ⟨algebraMap_injective_of_denseP_unique_lift P hdense hpt, fun b => ?_⟩
  let M : Submodule R B := LinearMap.range (Algebra.linearMap R B)
  let s : Set R := {f | ∃ a : R, f • b = algebraMap R B a}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, hpP, -, hmp, h1p⟩ := hP m 1 hm.isPrime
      (fun h => hm.ne_top ((Ideal.eq_top_iff_one m).mpr h))
    have hpm : p = m := (hm.eq_of_le ((Ideal.ne_top_iff_one p).mpr h1p) hmp).symm
    obtain ⟨K, _, _, x, hx, hy⟩ := hpt p hpP
    obtain ⟨f, hf, hfb⟩ := exists_smul_mem_range_algebraMap_of_unique_lift x hy
    apply hf
    rw [hx, hpm]
    exact hsm (Ideal.subset_span (hfb b))
  have hb := Submodule.mem_of_span_eq_top_of_smul_pow_mem M s hs b (fun r => ⟨1, by
    obtain ⟨a, ha⟩ := r.2
    rw [pow_one, ha]
    exact ⟨a, rfl⟩⟩)
  obtain ⟨a, ha⟩ := hb
  exact ⟨a, ha⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBinaryOpGluedAlongCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem exists_binary_op : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) (ψ : ∀ i, (G i).left ⟶ A.left) (o : ∀ i, G i ⊗ G i ⟶ G i), iSup U = ⊤ → (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i j (T : Scheme.{0}) (r : T ⟶ (U i).toScheme) (r' : T ⟶ (U j).toScheme) (x y : Over.mk r ⟶ G i) (x' y' : Over.mk r' ⟶ G j), x.left ≫ ψ i = x'.left ≫ ψ j → y.left ≫ ψ i = y'.left ≫ ψ j → (lift x y ≫ o i).left ≫ ψ i = (lift x' y' ≫ o j).left ≫ ψ j) → ∃ m : A ⊗ A ⟶ A, ∀ i (T : Over (U i).toScheme) (x y : T ⟶ G i) (x₀ y₀ : Over.mk (T.hom ≫ (U i).ι) ⟶ A), x₀.left = x.left ≫ ψ i → y₀.left = y.left ≫ ψ i → (lift x₀ y₀ ≫ m).left = (lift x y ≫ o i).left ≫ ψ i := by
  intro S I U A G ψ o hU hpb hcomp

  let p : (A ⊗ A).left ⟶ S := (A ⊗ A).hom
  let V : I → (A ⊗ A).left.Opens := fun i => p ⁻¹ᵁ U i
  let q : ∀ i, (V i).toScheme ⟶ (U i).toScheme := fun i => p ∣_ U i
  have hP : ∀ i, IsPullback (V i).ι (q i) p (U i).ι := fun i => (isPullback_morphismRestrict p (U i)).flip

  let T₀ : ∀ i, Over (U i).toScheme := fun i => Over.mk (q i)
  let r : ∀ i, Over.mk ((T₀ i).hom ≫ (U i).ι) ⟶ A ⊗ A := fun i =>
    Over.homMk (V i).ι (hP i).w

  have hx : ∀ i, ∃ x : T₀ i ⟶ G i, (r i ≫ fst A A).left = x.left ≫ ψ i := fun i =>
    exists_lift (hpb i) _
  have hy : ∀ i, ∃ y : T₀ i ⟶ G i, (r i ≫ snd A A).left = y.left ≫ ψ i := fun i =>
    exists_lift (hpb i) _
  choose x hx using hx
  choose y hy using hy

  let f : ∀ i, (V i).toScheme ⟶ A.left := fun i => (lift (x i) (y i) ≫ o i).left ≫ ψ i
  have hf : ∀ i j (T : Scheme.{0}) (a : T ⟶ (V i).toScheme) (b : T ⟶ (V j).toScheme),
      a ≫ (V i).ι = b ≫ (V j).ι → a ≫ f i = b ≫ f j := by
    intro i j T a b hab
    let ea : Over.mk (a ≫ q i) ⟶ T₀ i := Over.homMk a rfl
    let eb : Over.mk (b ≫ q j) ⟶ T₀ j := Over.homMk b rfl
    have key := hcomp i j T (a ≫ q i) (b ≫ q j) (ea ≫ x i) (ea ≫ y i) (eb ≫ x j) (eb ≫ y j)
      (by
        simp only [Over.comp_left, Category.assoc, ← hx, ea, eb, Over.homMk_left, r]
        rw [← Category.assoc, hab, Category.assoc])
      (by
        simp only [Over.comp_left, Category.assoc, ← hy, ea, eb, Over.homMk_left, r]
        rw [← Category.assoc, hab, Category.assoc])
    rw [← comp_lift, ← comp_lift] at key
    simpa only [f, ea, eb, Over.homMk_left, Over.comp_left, Category.assoc] using key
  obtain ⟨F, hF, -⟩ := existsUnique_hom (fun i => (V i).ι) (fun i => inferInstance)
    (covers hU hP) f hf

  have hFw : F ≫ A.hom = (A ⊗ A).hom := by
    refine hom_ext (fun i => (V i).ι) (fun i => inferInstance) (covers hU hP) (fun i => ?_)
    rw [reassoc_of% (hF i)]
    simp only [f, Category.assoc, (hpb i).w]
    rw [← Category.assoc (lift (x i) (y i) ≫ o i).left, Over.w]
    exact (hP i).w.symm
  refine ⟨Over.homMk F hFw, ?_⟩
  intro i T x' y' x₀ y₀ hx₀ hy₀
  have hg : (lift x₀ y₀).left ≫ p = T.hom ≫ (U i).ι := Over.w (lift x₀ y₀)
  let k : T.left ⟶ (V i).toScheme := (hP i).lift (lift x₀ y₀).left T.hom hg
  have hk₁ : k ≫ (V i).ι = (lift x₀ y₀).left := (hP i).lift_fst _ _ _
  have hk₂ : k ≫ q i = T.hom := (hP i).lift_snd _ _ _
  let e : T ⟶ T₀ i := Over.homMk k hk₂
  have ex : e ≫ x i = x' := by
    apply lift_ext (hpb i)
    rw [Over.comp_left, Category.assoc, ← hx i, ← hx₀, Over.comp_left]
    change k ≫ (V i).ι ≫ (fst A A).left = _
    rw [reassoc_of% hk₁, ← Over.comp_left, lift_fst]
  have ey : e ≫ y i = y' := by
    apply lift_ext (hpb i)
    rw [Over.comp_left, Category.assoc, ← hy i, ← hy₀, Over.comp_left]
    change k ≫ (V i).ι ≫ (snd A A).left = _
    rw [reassoc_of% hk₁, ← Over.comp_left, lift_snd]
  rw [← ex, ← ey, ← comp_lift, Category.assoc]
  change (lift x₀ y₀).left ≫ F = (k ≫ (lift (x i) (y i) ≫ o i).left) ≫ ψ i
  rw [← hk₁, Category.assoc, hF i, Category.assoc]

end GlobalTheory.CoverGlue
end

