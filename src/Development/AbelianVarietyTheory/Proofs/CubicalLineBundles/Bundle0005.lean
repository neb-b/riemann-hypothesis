module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsoLineBundleOfRegularPullbacksSameZeroScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SameZeroScheme

theorem resG_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (h' : W ≤ V) (a : Γ(X, U)) :
    resG Y h' ((f.appLE U V h).hom a) = (f.appLE U W (h'.trans h)).hom a := by
  change (f.appLE U V h ≫ Y.presheaf.map (homOfLE h').op).hom a = _
  rw [Scheme.Hom.appLE_map]

theorem appLE_resG {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (h' : U ≤ U') (h'' : V ≤ f ⁻¹ᵁ U') (a : Γ(X, U')) :
    (f.appLE U V h).hom (resG X h' a) = (f.appLE U' V h'').hom a := by
  change (X.presheaf.map (homOfLE h').op ≫ f.appLE U V h).hom a = _
  rw [Scheme.Hom.map_appLE]

theorem appLE_appLE {X Y T : Scheme.{0}} (t : T ⟶ Y) (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (h' : ⊤ ≤ t ⁻¹ᵁ V) (h'' : ⊤ ≤ (t ≫ f) ⁻¹ᵁ U) (a : Γ(X, U)) :
    (t.appLE V ⊤ h').hom ((f.appLE U V h).hom a) = ((t ≫ f).appLE U ⊤ h'').hom a := by
  change (f.appLE U V h ≫ t.appLE V ⊤ h').hom a = _
  rw [Scheme.Hom.appLE_comp_appLE]

theorem appLE_compat {X Y : Scheme.{0}} {L : LB X} (θ : L.Sec) (f : Y ⟶ X) (i j : L.ι) {W : Y.Opens}
    (hi : W ≤ f ⁻¹ᵁ L.U i) (hj : W ≤ f ⁻¹ᵁ L.U j) (hij : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U j)) :
    (f.appLE (L.U i) W hi).hom (θ.f i) =
      (res hij (pullU f (L.U i ⊓ L.U j) (L.g i j)) : Γ(Y, W)ˣ) * (f.appLE (L.U j) W hj).hom (θ.f j) := by
  have e := congrArg (f.appLE (L.U i ⊓ L.U j) W hij).hom (θ.compat i j)
  rw [map_mul] at e
  exact (appLE_resG f hij inf_le_left hi _).symm.trans
    (e.trans (congrArg₂ (· * ·) rfl (appLE_resG f hij inf_le_right hj _)))

theorem unit_eq_of_mul {R : Type*} [CommRing R] {a a' b b' : R} {c c' g₀ g₁ : Rˣ}
    (ha : a ∈ nonZeroDivisors R) (h : b = c * a) (h' : b' = c' * a') (hb : b = g₀ * b')
    (haa : a = g₁ * a') : c = g₀ ^ (1 : ℤ) * g₁ ^ (-1 : ℤ) * c' := by
  apply Units.ext
  apply (mul_cancel_right_mem_nonZeroDivisors ha).1
  rw [← h, hb, h', zpow_one, zpow_neg_one, haa]
  have := g₁.inv_mul
  push_cast
  linear_combination (-(g₀ * c' * a' : R)) * this

theorem exists_isGen_linComb : ∀ (X Y : Scheme.{0}) (L : LB X) (θ : L.Sec) (φ ψ : Y ⟶ X), L.IsLB → (∀ (i : L.ι) (V : Y.Opens) (h : V ≤ φ ⁻¹ᵁ L.U i), (φ.appLE (L.U i) V h).hom (θ.f i) ∈ nonZeroDivisors Γ(Y, V)) → (∀ (i : L.ι) (V : Y.Opens) (h : V ≤ ψ ⁻¹ᵁ L.U i), (ψ.appLE (L.U i) V h).hom (θ.f i) ∈ nonZeroDivisors Γ(Y, V)) → (∀ (T : Scheme.{0}) (t : T ⟶ Y) (i j : L.ι) (h : ⊤ ≤ (t ≫ φ) ⁻¹ᵁ L.U i) (h' : ⊤ ≤ (t ≫ ψ) ⁻¹ᵁ L.U j), ((t ≫ φ).appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ ((t ≫ ψ).appLE (L.U j) ⊤ h').hom (θ.f j) = 0) → ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![φ, ψ] ![1, -1]), t.IsGen := by
  intro X Y L θ φ ψ _ _ hψ H
  have h0 : ∀ j : Fin 2 → L.ι, L.wchart ![φ, ψ] j ≤ φ ⁻¹ᵁ L.U (j 0) :=
    fun j => LB.wchart_le L ![φ, ψ] j 0
  have h1 : ∀ j : Fin 2 → L.ι, L.wchart ![φ, ψ] j ≤ ψ ⁻¹ᵁ L.U (j 1) :=
    fun j => LB.wchart_le L ![φ, ψ] j 1
  have hc : ∀ j : Fin 2 → L.ι, ∃ c : Γ(Y, L.wchart ![φ, ψ] j)ˣ,
      (φ.appLE _ _ (h0 j)).hom (θ.f (j 0)) = c * (ψ.appLE _ _ (h1 j)).hom (θ.f (j 1)) := by
    intro j
    apply exists_unit_mul
    · intro V' h
      rw [resG_appLE]
      exact hψ _ _ _
    · intro T t h
      have k0 : ⊤ ≤ (t ≫ φ) ⁻¹ᵁ L.U (j 0) := fun x hx => h0 j (h hx)
      have k1 : ⊤ ≤ (t ≫ ψ) ⁻¹ᵁ L.U (j 1) := fun x hx => h1 j (h hx)
      rw [appLE_appLE t φ _ h k0, appLE_appLE t ψ _ h k1]
      exact (H T t _ _ k0 k1).symm
  choose c hc using hc
  refine ⟨⟨c⟩, fun i j => ?_⟩
  let W : Y.Opens := L.wchart ![φ, ψ] i ⊓ L.wchart ![φ, ψ] j
  have wi : W ≤ L.wchart ![φ, ψ] i := inf_le_left
  have wj : W ≤ L.wchart ![φ, ψ] j := inf_le_right
  have ei := congrArg (resG Y wi) (hc i)
  have ej := congrArg (resG Y wj) (hc j)
  rw [map_mul, resG_appLE, resG_appLE] at ei ej
  have p0 : W ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0)) := le_inf (wi.trans (h0 i)) (wj.trans (h0 j))
  have p1 : W ≤ ψ ⁻¹ᵁ (L.U (i 1) ⊓ L.U (j 1)) := le_inf (wi.trans (h1 i)) (wj.trans (h1 j))
  have key := unit_eq_of_mul (c := res wi (c i)) (c' := res wj (c j)) (hψ _ _ _) ei ej
    (appLE_compat θ φ (i 0) (j 0) _ _ p0) (appLE_compat θ ψ (i 1) (j 1) _ _ p1)
  refine key.trans ?_
  congr 1
  exact (Fin.prod_univ_two (fun k : Fin 2 => (res (le_inf (wi.trans (LB.wchart_le L ![φ, ψ] i k))
    (wj.trans (LB.wchart_le L ![φ, ψ] j k)) : W ≤ (![φ, ψ] k) ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
    (pullU (![φ, ψ] k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)))) ^ ((![1, -1] : Fin 2 → ℤ) k))).symm

end GlobalTheory.SameZeroScheme
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SpecialisationNumberFieldAndCountableValues
section
namespace GlobalTheory

theorem _root_.GlobalTheory.exists_ringHom_extend_of_finiteType (F A L : Type*) [Field F] [CommRing A]
    [Nontrivial A] [Algebra F A] [Algebra.FiniteType F A] [Field L] [IsAlgClosed L]
    (σ : F →+* L) : ∃ φ : A →+* L, ∀ x, φ (algebraMap F A x) = σ x := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)
  letI : Algebra F L := σ.toAlgebra
  let ψ : (A ⧸ m) →ₐ[F] L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ψ.toRingHom.comp (Ideal.Quotient.mk m), fun x => ?_⟩
  have h1 : Ideal.Quotient.mk m (algebraMap F A x) = algebraMap F (A ⧸ m) x := rfl
  simp only [RingHom.comp_apply, h1, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rfl

private lemma exists_algHom_extend_of_fg_ne_zero {k L M : Type*} [Field k] [Field L] [Algebra k L]
    [Field M] [IsAlgClosed M] [Algebra k M] (F : IntermediateField k L) (σ : F →ₐ[k] M)
    (R : Subalgebra k L) (hR : R.FG) (r : R) (hr : r ≠ 0) :
    ∃ ρ : R →ₐ[k] M, (∀ (x : R) (hx : (x : L) ∈ F), ρ x = σ ⟨x, hx⟩) ∧ ρ r ≠ 0 := by
  classical
  obtain ⟨s, hs⟩ := hR
  have hrL : (r : L) ≠ 0 := fun h => hr (Subtype.ext h)
  obtain ⟨A, hA⟩ : ∃ A : Subalgebra F L, A = Algebra.adjoin F ↑(insert ((r : L)⁻¹) s) := ⟨_, rfl⟩
  haveI : Algebra.FiniteType F A :=
    (Subalgebra.fg_iff_finiteType A).1 ⟨insert ((r : L)⁻¹) s, hA.symm⟩
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.exists_ringHom_extend_of_finiteType F A M σ.toRingHom
  have hgen : ∀ y ∈ insert ((r : L)⁻¹) s, y ∈ A := fun y hy => by
    rw [hA]; exact Algebra.subset_adjoin (Finset.mem_coe.2 hy)
  have hle : ∀ x ∈ R, x ∈ A := by
    intro x hx
    rw [← hs] at hx
    have hsub : Algebra.adjoin k (s : Set L) ≤ A.restrictScalars k :=
      Algebra.adjoin_le fun y hy => (Subalgebra.mem_restrictScalars k).2
        (hgen y (Finset.mem_insert_of_mem (Finset.mem_coe.1 hy)))
    exact (Subalgebra.mem_restrictScalars k).1 (hsub hx)
  let ι : R →+* A :=
    { toFun := fun x => ⟨x, hle x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ => Subtype.ext (by simp) }
  have hι : ∀ (x : R) (hx : (x : L) ∈ F), ι x = algebraMap F A ⟨x, hx⟩ :=
    fun _ _ => Subtype.ext rfl
  have hcomm : ∀ a : k, φ (ι (algebraMap k R a)) = algebraMap k M a := by
    intro a
    have h1 : ι (algebraMap k R a) = algebraMap F A (algebraMap k F a) := Subtype.ext (by
      change algebraMap k L a = algebraMap F L (algebraMap k F a)
      exact IsScalarTower.algebraMap_apply k F L a)
    rw [h1, hφ]
    exact σ.commutes a
  refine ⟨{ toRingHom := φ.comp ι, commutes' := hcomm }, fun x hx => ?_, ?_⟩
  · show φ (ι x) = σ ⟨x, hx⟩
    rw [hι x hx, hφ]
    rfl
  · have hinv : ι r * ⟨(r : L)⁻¹, hgen _ (Finset.mem_insert_self _ _)⟩ = 1 :=
      Subtype.ext (by simp [ι, hrL])
    have := congrArg φ hinv
    rw [map_mul, map_one] at this
    exact left_ne_zero_of_mul_eq_one this

theorem _root_.GlobalTheory.exists_specialisation_finite {k L : Type*} [Field k] [Field L]
    [Algebra k L] [IsAlgClosed L] (R : Subalgebra k L) (hR : R.FG) (r : R) (hr : r ≠ 0) :
    ∃ (K₁ : IntermediateField k L) (ρ : R →ₐ[k] K₁), FiniteDimensional k K₁ ∧ ρ r ≠ 0 ∧
      ∀ c : R, IsAlgebraic k c → (ρ c : L) = c := by
  classical
  haveI : IsAlgClosed (algebraicClosure k L) := IsAlgClosure.isAlgClosed k
  obtain ⟨ρ₁, hfix, hr₁⟩ :=
    exists_algHom_extend_of_fg_ne_zero (algebraicClosure k L) (AlgHom.id k _) R hR r hr
  let ρ₀ : R →ₐ[k] L := (algebraicClosure k L).val.comp ρ₁
  have halg : ∀ x : R, IsAlgebraic k (ρ₀ x) := fun x => mem_algebraicClosure_iff.1 (ρ₁ x).2
  haveI : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).1 hR
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := k) (A := R)
  haveI : Finite (ρ₀ '' (t : Set R)) := (t.finite_toSet.image _).to_subtype
  have hfin : FiniteDimensional k (IntermediateField.adjoin k (ρ₀ '' (t : Set R))) :=
    IntermediateField.finiteDimensional_adjoin fun y hy => by
      obtain ⟨x, -, rfl⟩ := hy
      exact (halg x).isIntegral
  have hmem : ∀ x : R, ρ₀ x ∈ IntermediateField.adjoin k (ρ₀ '' (t : Set R)) := by
    intro x
    have hx : x ∈ Algebra.adjoin k (t : Set R) := by rw [ht]; exact Algebra.mem_top
    have h1 : ρ₀ x ∈ Algebra.adjoin k (ρ₀ '' (t : Set R)) := by
      rw [← AlgHom.map_adjoin]; exact ⟨x, hx, rfl⟩
    exact IntermediateField.algebra_adjoin_le_adjoin k _ h1
  refine ⟨IntermediateField.adjoin k (ρ₀ '' (t : Set R)),
    { toFun := fun x => ⟨ρ₀ x, hmem x⟩
      map_one' := Subtype.ext (map_one ρ₀)
      map_mul' := fun x y => Subtype.ext (map_mul ρ₀ x y)
      map_zero' := Subtype.ext (map_zero ρ₀)
      map_add' := fun x y => Subtype.ext (map_add ρ₀ x y)
      commutes' := fun a => Subtype.ext (ρ₀.commutes a) }, hfin, fun h => hr₁ ?_, fun c hc => ?_⟩
  · have h' : ρ₀ r = 0 := congrArg Subtype.val h
    exact Subtype.ext h'
  · have hcL : (c : L) ∈ algebraicClosure k L := mem_algebraicClosure_iff.2 (hc.algHom R.val)
    show ((ρ₁ c : algebraicClosure k L) : L) = c
    rw [hfix c hcL]
    rfl

theorem _root_.GlobalTheory.specialisation_numberField_and_countable_values :
    ∀ (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (R : Subalgebra k ℂ), R.FG →
    ∀ (c r : R), r ≠ 0 →
    (∃ (K₁ : IntermediateField k ℂ) (ρ : R →ₐ[k] K₁), FiniteDimensional k K₁ ∧ ρ r ≠ 0 ∧
      (IsAlgebraic k c → (ρ c : ℂ) = c)) ∧
    (∀ S : Set ℂ, S.Countable → (∀ ρ : R →ₐ[k] ℂ, ρ c ∈ S) → IsAlgebraic k c) := by
  intro k _ R hR c r hr
  refine ⟨?_, fun S hS hρ => ?_⟩
  · obtain ⟨K₁, ρ, hfin, hr₁, hfix⟩ := _root_.GlobalTheory.exists_specialisation_finite R hR r hr
    exact ⟨K₁, ρ, hfin, hr₁, hfix c⟩
  by_contra hc
  have hct : Transcendental k (c : ℂ) := fun h =>
    hc ((isAlgebraic_algHom_iff R.val Subtype.val_injective).1 h)
  have key : ∀ z : ℂ, Transcendental ℚ z → z ∈ S := by
    intro z hz
    have hzk : Transcendental k z := fun h => hz (h.restrictScalars ℚ)
    let e₁ := RatFunc.algEquivOfTranscendental (c : ℂ) hct
    let e₂ := RatFunc.algEquivOfTranscendental z hzk
    let σ : IntermediateField.adjoin k {(c : ℂ)} →ₐ[k] ℂ :=
      (IntermediateField.adjoin k {z}).val.comp (e₂.toAlgHom.comp e₁.symm.toAlgHom)
    have hcmem : (c : ℂ) ∈ IntermediateField.adjoin k {(c : ℂ)} :=
      IntermediateField.mem_adjoin_simple_self k (c : ℂ)
    have hσ : σ ⟨c, hcmem⟩ = z := by
      have h1 : e₁.symm ⟨c, hcmem⟩ = RatFunc.X := by
        rw [AlgEquiv.symm_apply_eq]
        exact Subtype.ext (RatFunc.algEquivOfTranscendental_X (c : ℂ) hct).symm
      show ((e₂ (e₁.symm ⟨c, hcmem⟩) : IntermediateField.adjoin k {z}) : ℂ) = z
      rw [h1]
      exact RatFunc.algEquivOfTranscendental_X z hzk
    obtain ⟨ρ, hfix, -⟩ :=
      exists_algHom_extend_of_fg_ne_zero (IntermediateField.adjoin k {(c : ℂ)}) σ R hR 1 one_ne_zero
    have h := hρ ρ
    rwa [hfix c hcmem, hσ] at h
  have hcover : (Set.univ : Set ℂ) ⊆ S ∪ {z | IsAlgebraic ℚ z} := fun z _ => by
    by_cases h : IsAlgebraic ℚ z
    · exact Or.inr h
    · exact Or.inl (key z h)
  exact not_countable_complex ((hS.union (Algebraic.countable ℚ ℂ)).mono hcover)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

universe u

namespace GlobalTheory.ComplexPoints

section General

variable {K : Type u} [Field K] [IsAlgClosed K]


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {K : Type u} [Field K] [IsAlgClosed K] in
theorem _root_.GlobalTheory.ComplexPoints.exists_point_mem {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    {Z : Set X} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : Spec (.of K) ⟶ X, x ≫ p = 𝟙 _ ∧ ∀ a, x a ∈ Z := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨y, hyZ, hy⟩ := nonempty_inter_closedPoints hne hZ
  have hy : IsClosed {y} := hy
  exact ⟨pointOfClosedPoint p y hy, pointOfClosedPoint_comp p y hy,
    fun a => by rw [pointOfClosedPoint_apply]; exact hyZ⟩

theorem exists_geomPoint_mem {X S : Scheme.{u}} (p : X ⟶ S) [LocallyOfFiniteType p]
    (t : Spec (.of K) ⟶ S) [Surjective t]
    {Z : Set X} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : Spec (.of K) ⟶ X, x ≫ p = t ∧ ∀ a, x a ∈ Z := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨w, hw⟩ := (pullback.fst p t).surjective z
  obtain ⟨y, hy, hyZ⟩ := exists_point_mem (pullback.snd p t)
    (hZ.preimage (pullback.fst p t).continuous) ⟨w, show pullback.fst p t w ∈ Z from hw ▸ hz⟩
  refine ⟨y ≫ pullback.fst p t, ?_, fun a => hyZ a⟩
  rw [Category.assoc, pullback.condition, reassoc_of% hy]

theorem surjective_specMap_field {k L : Type u} [Field k] [Field L] (σ : k →+* L) :
    Surjective (Spec.map (CommRingCat.ofHom σ)) :=
  ⟨fun x => ⟨IsLocalRing.closedPoint L, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {K : Type u} [Field K] [IsAlgClosed K] in
theorem _root_.GlobalTheory.ComplexPoints.top_le_preimage_iff {L : Type u} [Field L] {X : Scheme.{u}}
    (x : Spec (.of L) ⟶ X) (U : X.Opens) (a : ↥(Spec (.of L))) : ⊤ ≤ x ⁻¹ᵁ U ↔ x a ∈ U := by
  constructor
  · intro h
    exact h (show a ∈ (⊤ : (Spec (.of L)).Opens) from trivial)
  · intro h b _
    rw [Subsingleton.elim b a]
    exact h


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {K : Type u} [Field K] [IsAlgClosed K] in
theorem _root_.GlobalTheory.ComplexPoints.surjective_of_geomPoints_lift {A B S : Scheme.{u}} (p : A ⟶ S)
    [LocallyOfFiniteType p]
    (t : Spec (.of K) ⟶ S) [Surjective t] (ψ : B ⟶ A) (hψ : IsClosed (Set.range ψ))
    (h : ∀ x : Spec (.of K) ⟶ A, x ≫ p = t → ∃ y : Spec (.of K) ⟶ B, y ≫ ψ = x) :
    Surjective ψ := by
  constructor
  by_contra hns
  have hne : (Set.range ψ)ᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    intro hr
    exact hns (Set.range_eq_univ.mp hr)
  have hP : (pullback.fst p t ⁻¹' (Set.range ψ)ᶜ).Nonempty := by
    obtain ⟨a, ha⟩ := hne
    obtain ⟨z, hz⟩ := (pullback.fst p t).surjective a
    exact ⟨z, by simpa [hz] using ha⟩
  obtain ⟨y, hy1, hy2⟩ := _root_.GlobalTheory.ComplexPoints.exists_point_mem (pullback.snd p t)
    (hψ.isOpen_compl.preimage (pullback.fst p t).continuous).isLocallyClosed hP
  obtain ⟨w, hw⟩ := h (y ≫ pullback.fst p t) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hy1, Category.id_comp])
  obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of K)))
  apply hy2 a
  exact ⟨w a, by rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]⟩


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {K : Type u} [Field K] [IsAlgClosed K] in
theorem _root_.GlobalTheory.ComplexPoints.hom_ext_of_points {X Y S : Scheme.{u}} (p : X ⟶ Spec (.of K))
    [LocallyOfFiniteType p]
    [IsReduced X] (q : Y ⟶ S) [IsSeparated q] {f g : X ⟶ Y} (hfg : f ≫ q = g ≫ q)
    (h : ∀ x : Spec (.of K) ⟶ X, x ≫ p = 𝟙 _ → x ≫ f = x ≫ g) : f = g := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  refine ext_of_fromSpecResidueField_eq f g q (closedPoints X)
    (dense_iff_closure_eq.mpr closure_closedPoints) ?_ hfg
  intro y hy
  have e := h (pointOfClosedPoint p y hy) (pointOfClosedPoint_comp p y hy)
  unfold pointOfClosedPoint at e
  simp only [Category.assoc] at e
  exact (cancel_epi _).mp e

end General

variable {X Y : Scheme.{0}}


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in
theorem _root_.GlobalTheory.ComplexPoints.top_le_preimage_basicOpen_iff (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt x U h f ≠ 0 := by
  have e : x ⁻¹ᵁ X.basicOpen f = (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).basicOpen (x.appLE U ⊤ h f) := by
    rw [Scheme.basicOpen_appLE, top_inf_eq]
  rw [e]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
  constructor
  · intro hs h0
    have hz : x.appLE U ⊤ h f = 0 := by
      have := congrArg (Scheme.ΓSpecIso (.of ℂ)).inv.hom h0
      simpa using this
    rw [hz, Scheme.basicOpen_zero] at hs
    obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of ℂ)))
    exact (hs (show a ∈ (⊤ : (Spec (.of ℂ)).Opens) from trivial)).elim
  · intro hne
    have hu : IsUnit (x.appLE U ⊤ h f) := by
      have := (isUnit_iff_ne_zero.mpr hne).map (Scheme.ΓSpecIso (.of ℂ)).inv.hom
      simpa using this
    rw [Scheme.basicOpen_of_isUnit _ hu]

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in
private theorem opens_le_of_forall_complex_section (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    (U V : X.Opens)
    (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) : U ≤ V := by
  intro y hyU
  by_contra hyV
  obtain ⟨x, hx1, hx2⟩ := _root_.GlobalTheory.ComplexPoints.exists_point_mem (K := ℂ) p
    (Z := (U : Set X) ∩ (V : Set X)ᶜ)
    (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed) ⟨y, hyU, hyV⟩
  obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of ℂ)))
  have hU : ⊤ ≤ x ⁻¹ᵁ U := (_root_.GlobalTheory.ComplexPoints.top_le_preimage_iff x U a).mpr (hx2 a).1
  exact (hx2 a).2 ((_root_.GlobalTheory.ComplexPoints.top_le_preimage_iff x V a).mp (h x hx1 hU))


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in
theorem _root_.GlobalTheory.ComplexPoints.eq_of_valAt'_eq (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    [IsReduced X] (U : X.Opens)
    (f g : Γ(X, U))
    (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U f = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U g) :
    f = g := by
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  refine eq_bot_iff.mpr (opens_le_of_forall_complex_section p _ ⊥ fun x hx hb => ?_)
  have hU : ⊤ ≤ x ⁻¹ᵁ U := hb.trans fun b hb' => X.basicOpen_le (f - g) hb'
  have hne := (_root_.GlobalTheory.ComplexPoints.top_le_preimage_basicOpen_iff x U hU (f - g)).mp hb
  have he := h x hx hU
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' at he
  rw [dite_eq_left hU, dite_eq_left hU] at he
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt at hne he
  rw [map_sub, map_sub, he, sub_self] at hne
  exact (hne rfl).elim


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in
theorem _root_.GlobalTheory.ComplexPoints.isUnit_of_valAt'_ne_zero (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U f ≠ 0) : IsUnit f := by
  have hle : U ≤ X.basicOpen f := opens_le_of_forall_complex_section p U _ fun x hx hU => by
    have := h x hx hU
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' at this
    rw [dite_eq_left hU] at this
    exact (_root_.GlobalTheory.ComplexPoints.top_le_preimage_basicOpen_iff x U hU f).mpr this
  have hu := (X.toRingedSpace.isUnit_res_basicOpen f).map
    (X.presheaf.map (homOfLE hle).op).hom
  have hid : (homOfLE (X.basicOpen_le f)).op ≫ (homOfLE hle).op = 𝟙 (Opposite.op U) :=
    Subsingleton.elim _ _
  convert hu using 1
  erw [← CommRingCat.comp_apply, ← Functor.map_comp, hid, CategoryTheory.Functor.map_id,
    CommRingCat.id_apply]


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in
theorem _root_.GlobalTheory.ComplexPoints.over_hom_ext_of_complexPoints {A B : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)} [LocallyOfFiniteType A.hom]
    [IsReduced A.left] [IsSeparated B.hom] {f g : A ⟶ B}
    (h : ∀ x : 𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) ⟶ A, x ≫ f = x ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  refine _root_.GlobalTheory.ComplexPoints.hom_ext_of_points (K := ℂ) A.hom B.hom
    (by rw [Over.w f, Over.w g]) fun x hx => ?_
  have := h (Over.homMk x (by simpa using hx))
  simpa using congrArg (fun k => k.left) this


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in
theorem _root_.GlobalTheory.ComplexPoints.opens_le_of_complexPoints (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p] (U V : X.Opens)
    (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) : U ≤ V :=
  opens_le_of_forall_complex_section p U V h


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in
theorem _root_.GlobalTheory.ComplexPoints.iSup_eq_top_of_complexPoints (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    {I : Type*} (U : I → X.Opens) (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ i, ⊤ ≤ x ⁻¹ᵁ U i) :
    ⨆ i, U i = ⊤ := by
  refine eq_top_iff.mpr (opens_le_of_forall_complex_section p ⊤ _ fun x hx _ => ?_)
  obtain ⟨i, hi⟩ := h x hx
  obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of ℂ)))
  rw [_root_.GlobalTheory.ComplexPoints.top_le_preimage_iff x _ a] at hi ⊢
  exact (le_iSup U i) hi

end GlobalTheory.ComplexPoints

namespace GlobalTheory

end GlobalTheory
end

