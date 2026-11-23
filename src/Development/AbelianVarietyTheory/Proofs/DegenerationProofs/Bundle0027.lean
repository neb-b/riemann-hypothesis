module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineUnitChartSmoothGroupScheme
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
namespace GlobalTheory.SS.ArcInf

theorem exists_isChart : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f := by
  intro k _ G _ hG
  have hs : Smooth G.hom := hG.2.1
  let e : algOver k k ⟶ G := 1
  let x0 : (Sp k) := IsLocalRing.closedPoint k
  obtain ⟨R, i, hi, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := G.left) (x := e.left x0) (U := ⊤) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ G.hom : Spec R ⟶ Spec (CommRingCat.of k))
  letI : Algebra k R := φ.hom.toAlgebra
  have hft : Algebra.FiniteType k R := by
    have h1 : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h1
  let j : algOver k R ⟶ G := Over.homMk i hφ.symm
  have hr : Set.range e.left ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    have : y = x0 := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [this]; exact hx
  let l : algOver k k ⟶ algOver k R := Over.homMk (IsOpenImmersion.lift i e.left hr) (by
    have := Over.w e
    rw [← this]
    show _ ≫ Spec.map φ = _
    rw [hφ, IsOpenImmersion.lift_fac_assoc])
  obtain ⟨ε, hε⟩ := algOverHom_surjective l
  obtain ⟨s, hsg⟩ := hft.out
  refine ⟨R, inferInstance, inferInstance, j, ε, s.card,
    fun n => (s.equivFin.symm n : R) - algebraMap k R (ε (s.equivFin.symm n)), hi, ?_, ?_, ?_⟩
  · rw [hε]
    ext1
    exact IsOpenImmersion.lift_fac i e.left hr
  · rw [eq_top_iff, ← hsg, Algebra.adjoin_le_iff]
    intro a ha
    have h1 : a - algebraMap k R (ε a) ∈ Algebra.adjoin k (Set.range fun n =>
        (s.equivFin.symm n : R) - algebraMap k R (ε (s.equivFin.symm n))) :=
      Algebra.subset_adjoin ⟨s.equivFin ⟨a, ha⟩, by simp⟩
    have h2 := add_mem h1 (Subalgebra.algebraMap_mem _ (ε a))
    simpa using h2
  · intro n
    simp

end GlobalTheory.SS.ArcInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasicOpenFactorFieldPointAffineOpen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
noncomputable section
namespace GlobalTheory.SS.ArcInf

theorem exists_basicOpen_factor : ∀ (k : Type) [CommRing k] (G : Over (Sp k)) (A B F : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Field F] [Algebra k F] (j : algOver k A ⟶ G) (φ : algOver k B ⟶ G) (δ : B →ₐ[k] F) (χ₀ : A →ₐ[k] F), IsOpenImmersion j.left → algOverHom δ ≫ φ = algOverHom χ₀ ≫ j → ∃ e : B, δ e ≠ 0 ∧ ∀ (B' : Type) [CommRing B'] [Algebra k B'] (ρ : B →ₐ[k] B'), IsUnit (ρ e) → ∃ χ : A →ₐ[k] B', algOverHom χ ≫ j = algOverHom ρ ≫ φ := by
  intro k _ G A B F _ _ _ _ _ _ j φ δ χ₀ hj h
  let U : (Spec (CommRingCat.of B)).Opens := φ.left ⁻¹ᵁ j.left.opensRange
  let p₀ : PrimeSpectrum F := ⟨⊥, Ideal.isPrime_bot⟩
  let p : PrimeSpectrum B := PrimeSpectrum.comap (δ : B →+* F) p₀
  have hl : (algOverHom δ).left ≫ φ.left = (algOverHom χ₀).left ≫ j.left := by
    have := congrArg (fun x => x.left) h
    simpa only [Over.comp_left] using this
  have hp : p ∈ (U : Set (Spec (CommRingCat.of B))) := by
    refine ⟨(algOverHom χ₀).left p₀, ?_⟩
    have := congrArg (fun x => x p₀) hl
    simp only [Scheme.Hom.comp_apply] at this
    exact this.symm
  obtain ⟨_, ⟨e, rfl⟩, he, heU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp U.isOpen
  refine ⟨e, fun h0 => he (show δ e ∈ (⊥ : Ideal F) from h0), ?_⟩
  intro B' _ _ ρ hρ
  have hr : Set.range ((algOverHom ρ).left ≫ φ.left) ⊆ Set.range j.left := by
    rintro _ ⟨q, rfl⟩
    have hq : PrimeSpectrum.comap (ρ : B →+* B') q ∈ PrimeSpectrum.basicOpen e := by
      intro hm
      exact q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ (show ρ e ∈ q.asIdeal from hm) hρ)
    rw [Scheme.Hom.comp_apply]
    exact heU hq
  have hf := IsOpenImmersion.lift_fac j.left ((algOverHom ρ).left ≫ φ.left) hr
  let ψ : algOver k B' ⟶ algOver k A :=
    Over.homMk (IsOpenImmersion.lift j.left ((algOverHom ρ).left ≫ φ.left) hr) (by
      rw [← Over.w j, ← Category.assoc, hf, Category.assoc, Over.w φ, Over.w (algOverHom ρ)])
  obtain ⟨χ, hχ⟩ := algOverHom_surjective ψ
  refine ⟨χ, ?_⟩
  rw [hχ]
  ext1
  exact hf

end GlobalTheory.SS.ArcInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorOfRangeSubset
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
namespace GlobalTheory.SS.ArcInf

theorem exists_factor_of_range_subset {k : Type} [CommRing k] {G : Over (Sp k)} {A B : Type} [CommRing A]
    [Algebra k A] [CommRing B] [Algebra k B] (j : algOver k A ⟶ G) (hj : IsOpenImmersion j.left)
    (a : algOver k B ⟶ G) (hr : Set.range a.left ⊆ Set.range j.left) :
    ∃ χ : A →ₐ[k] B, algOverHom χ ≫ j = a := by
  have hf := IsOpenImmersion.lift_fac j.left a.left hr
  let l : algOver k B ⟶ algOver k A := Over.homMk (IsOpenImmersion.lift j.left a.left hr) (by
    rw [← Over.w j, ← Category.assoc, hf, Over.w a])
  obtain ⟨χ, hχ⟩ := algOverHom_surjective l
  refine ⟨χ, ?_⟩
  rw [hχ]
  ext1
  exact hf

theorem exists_extend_of_localSubring : ∀ (k : Type) [CommRing k] (G : Over (Sp k)) (O K F : Type) [CommRing O] [Algebra k O] [Field K] [Algebra k K] [Field F] [Algebra k F] (em : O →ₐ[k] K) (σ : K →ₐ[k] F) (L : Subalgebra k F), IsLocalRing L → Function.Injective em → (∀ x, σ x ∈ L → x ∈ Set.range em) → ∀ (a : algOver k K ⟶ G) (b' : algOver k L ⟶ G), algOverHom σ ≫ a = algOverHom L.val ≫ b' → ∃ b : algOver k O ⟶ G, algOverHom em ≫ b = a := by
  intro k _ G O K F _ _ _ _ _ _ em σ L hL hem hsub a b' hab
  let x0 : (Sp L) := IsLocalRing.closedPoint L
  obtain ⟨R, i, hi, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := G.left)
    (x := b'.left x0) (U := ⊤) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ G.hom : Spec R ⟶ Spec (CommRingCat.of k))
  letI : Algebra k R := φ.hom.toAlgebra
  let j : algOver k R ⟶ G := Over.homMk i hφ.symm
  have hj : IsOpenImmersion j.left := hi
  have hrb : Set.range b'.left ⊆ Set.range j.left := by
    rintro _ ⟨y, rfl⟩
    have hs : y ⤳ x0 := IsLocalRing.specializes_closedPoint (R := L) y
    have hs' := hs.map b'.left.continuous
    exact hs'.mem_open j.left.isOpenEmbedding.isOpen_range hx
  have hra : Set.range a.left ⊆ Set.range j.left := by
    rintro _ ⟨y, rfl⟩
    let p : (Sp F) := IsLocalRing.closedPoint F
    have hy : y = (algOverHom σ).left p := Subsingleton.elim (α := PrimeSpectrum K) _ _
    have hl : (algOverHom σ).left ≫ a.left = (algOverHom L.val).left ≫ b'.left := by
      rw [← Over.comp_left, ← Over.comp_left, hab]
    apply hrb
    refine ⟨(algOverHom L.val).left p, ?_⟩
    rw [hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hl]
  obtain ⟨χL, hχL⟩ := exists_factor_of_range_subset j hj b' hrb
  obtain ⟨χK, hχK⟩ := exists_factor_of_range_subset j hj a hra
  have hc : σ.comp χK = L.val.comp χL := by
    apply eq_of_comp_eq hj
    rw [algOverHom_comp, algOverHom_comp, Category.assoc, Category.assoc, hχK, hχL, hab]
  have hmem : ∀ x, χK x ∈ em.range := fun x => by
    apply hsub
    have : σ (χK x) = (χL x : F) := DFunLike.congr_fun hc x
    rw [this]
    exact (χL x).2
  let χO : R →ₐ[k] O :=
    ((AlgEquiv.ofInjective em hem).symm : em.range →ₐ[k] O).comp (χK.codRestrict em.range hmem)
  have hO : em.comp χO = χK := by
    ext x
    have := AlgEquiv.ofInjective_apply em hem ((AlgEquiv.ofInjective em hem).symm ⟨χK x, hmem x⟩)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨algOverHom χO ≫ j, ?_⟩
  rw [← Category.assoc, ← algOverHom_comp, hO, hχK]

end GlobalTheory.SS.ArcInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFinsetModelOfIsAffine
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_finset_isPushout_model (K A : Type) [Field K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] :
    ∃ s : Finset K, ∀ (k : Type) [Field k] (β : k →+* K), (s : Set K) ⊆ Set.range β →
      ∃ (A₀ : CommRingCat.{0}) (f : CommRingCat.of k ⟶ A₀) (g : A₀ ⟶ CommRingCat.of A),
        IsPushout f (CommRingCat.ofHom β) g (CommRingCat.ofHom (algebraMap K A)) := by
  haveI : Algebra.FinitePresentation K A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let P := Algebra.Presentation.ofFinitePresentation K A
  refine ⟨P.finite_coeffs.toFinset, fun k _ β hs => ?_⟩
  letI : Algebra k K := β.toAlgebra
  letI : Algebra k A := ((algebraMap K A).comp β).toAlgebra
  haveI : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  haveI : P.HasCoeffs k := ⟨fun x hx => hs (by simpa using hx)⟩
  let e := P.tensorModelOfHasCoeffsEquiv k
  have h := (CommRingCat.isPushout_tensorProduct k K (P.ModelOfHasCoeffs k)).flip
  refine ⟨CommRingCat.of (P.ModelOfHasCoeffs k), CommRingCat.ofHom (algebraMap k _),
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom) ≫
      e.toRingEquiv.toCommRingCatIso.hom, ?_⟩
  refine h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso
    ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · ext x
    exact e.commutes x

theorem exists_finset_model_of_isAffine :
    ∀ (K : Type) [Field K] (X : Over (Sp K)), IsAffine X.left → LocallyOfFiniteType X.hom →
      ∃ s : Finset K, ∀ (k : Type) [Field k] (β : k →+* K), (s : Set K) ⊆ Set.range β →
        ∃ (X₀ : Over (Sp k)) (φ : X.left ⟶ X₀.left), IsPullback φ X.hom X₀.hom (spMap β) := by
  intro K _ X hX hft
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := CommRingCat.of K) (S := Γ(X.left, ⊤))
    (X.left.isoSpec.inv ≫ X.hom)
  have h1 : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h1
  letI : Algebra K Γ(X.left, ⊤) := ψ.hom.toAlgebra
  haveI : Algebra.FiniteType K Γ(X.left, ⊤) := h1
  obtain ⟨s, hs⟩ := exists_finset_isPushout_model K Γ(X.left, ⊤)
  refine ⟨s, fun k _ β hβ => ?_⟩
  obtain ⟨A₀, f, g, h⟩ := hs k β hβ
  have h2 : IsPullback (Spec.map g) (Spec.map ψ) (Spec.map f) (spMap β) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ h
  refine ⟨Over.mk (Spec.map f), X.left.isoSpec.hom ≫ Spec.map g, ?_⟩
  refine h2.of_iso X.left.isoSpec.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp [hψ]
  · simp
  · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLeadingQuotientWeightedArcs
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

namespace GlobalTheory.SS

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma weight_fin_two (m n : ℕ) (e : Fin 2 →₀ ℕ) :
    Finsupp.weight (![m, n] : Fin 2 → ℕ) e = m * e 0 + n * e 1 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two, mul_comm]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma leading_polynomial_eq_zero_iff_lt_weightedOrder {k : Type} [Field k] {m n : ℕ} (hm : 1 ≤ m)
    (f : MvPowerSeries (Fin 2) k) {D : ℕ}
    (hD : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f)
    (S : Finset (Fin 2 →₀ ℕ)) (hS : ∀ e, e ∈ S ↔ Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D) :
    (∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e f) * Polynomial.X ^ (e 1)) = 0 ↔
      (D : ℕ∞) < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f := by
  have hcoeff : ∀ e ∈ S,
      (∑ e' ∈ S, Polynomial.C (MvPowerSeries.coeff e' f) * Polynomial.X ^ (e' 1)).coeff (e 1) =
        MvPowerSeries.coeff e f := by
    intro e he
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single e]
    · simp [Polynomial.coeff_C_mul_X_pow]
    · intro e' he' hne
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      intro h1
      apply hne
      have w1 := (hS e').1 he'
      have w2 := (hS e).1 he
      rw [weight_fin_two] at w1 w2
      rw [h1] at w2
      have h0 : e' 0 = e 0 :=
        Nat.eq_of_mul_eq_mul_left hm (Nat.add_right_cancel (w1.trans w2.symm))
      ext i
      fin_cases i
      · exact h0
      · exact h1.symm
    · intro h; exact absurd he h
  constructor
  · intro h0
    by_contra hlt
    push_neg at hlt
    have heq : MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f = D := le_antisymm hlt hD
    obtain ⟨e, hne, hwe⟩ := MvPowerSeries.exists_coeff_ne_zero_and_weightedOrder
      (![m, n] : Fin 2 → ℕ) (f := f) (by rw [heq]; rfl)
    rw [heq, Nat.cast_inj] at hwe
    have := hcoeff e ((hS e).2 hwe)
    rw [h0, Polynomial.coeff_zero] at this
    exact hne this.symm
  · intro hlt
    refine Finset.sum_eq_zero fun e he => ?_
    rw [MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _ (by rw [(hS e).1 he]; exact hlt),
      map_zero, zero_mul]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma prod_pow_fin_two {k : Type} [Field k] (z w : PowerSeries k) (e : Fin 2 →₀ ℕ) :
    (e.prod fun s j => (![z, w] : Fin 2 → PowerSeries k) s ^ j) = z ^ e 0 * w ^ e 1 := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  rfl

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open PowerSeries in
private lemma coeff_pow_mul_pow_of_le_order {k : Type} [Field k] {m n : ℕ} {z w : PowerSeries k}
    (hz : (m : ℕ∞) ≤ z.order) (hw : (n : ℕ∞) ≤ w.order) (a b : ℕ) :
    (∀ j < m * a + n * b, coeff j (z ^ a * w ^ b) = 0) ∧
      coeff (m * a + n * b) (z ^ a * w ^ b) = coeff m z ^ a * coeff n w ^ b := by
  obtain ⟨z', rfl⟩ : X ^ m ∣ z := X_pow_dvd_iff.2 fun j hj =>
    coeff_of_lt_order j (lt_of_lt_of_le (by exact_mod_cast hj) hz)
  obtain ⟨w', rfl⟩ : X ^ n ∣ w := X_pow_dvd_iff.2 fun j hj =>
    coeff_of_lt_order j (lt_of_lt_of_le (by exact_mod_cast hj) hw)
  have hprod : (X ^ m * z') ^ a * (X ^ n * w') ^ b = X ^ (m * a + n * b) * (z' ^ a * w' ^ b) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]; ring
  rw [hprod]
  refine ⟨fun j hj => by rw [coeff_X_pow_mul', if_neg (by omega)], ?_⟩
  rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff, map_mul, map_pow,
    map_pow]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma coeff_subst_eq_zero_of_lt {k : Type} [Field k] {m n : ℕ} {z w : PowerSeries k}
    (hz : (m : ℕ∞) ≤ z.order) (hw : (n : ℕ∞) ≤ w.order)
    (hs : MvPowerSeries.HasSubst (![z, w] : Fin 2 → PowerSeries k)) {f : MvPowerSeries (Fin 2) k}
    {D : ℕ} (hD : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f) {j : ℕ}
    (hj : j < D) : PowerSeries.coeff j (MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) f) = 0 := by
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst hs]
  refine finsum_eq_zero_of_forall_eq_zero fun e => ?_
  by_cases hlt : Finsupp.weight (![m, n] : Fin 2 → ℕ) e < D
  · rw [MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _
      (lt_of_lt_of_le (by exact_mod_cast hlt) hD), zero_smul]
  · rw [weight_fin_two] at hlt
    rw [prod_pow_fin_two, ← PowerSeries.coeff,
      (coeff_pow_mul_pow_of_le_order hz hw (e 0) (e 1)).1 j (by omega), smul_zero]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma coeff_subst_eq_pow_mul_eval_leading {k : Type} [Field k] {m n : ℕ} {z w : PowerSeries k}
    (hz : (m : ℕ∞) ≤ z.order) (hw : (n : ℕ∞) ≤ w.order)
    (hs : MvPowerSeries.HasSubst (![z, w] : Fin 2 → PowerSeries k)) {s t : k}
    (hzs : PowerSeries.coeff m z = s ^ m) (hwt : PowerSeries.coeff n w = s ^ n * t)
    {f : MvPowerSeries (Fin 2) k} {D : ℕ}
    (hD : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f)
    (S : Finset (Fin 2 →₀ ℕ)) (hS : ∀ e, e ∈ S ↔ Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D) :
    PowerSeries.coeff D (MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) f) =
      s ^ D * (∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e f) * Polynomial.X ^ (e 1)).eval t := by
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst hs, finsum_eq_sum_of_support_subset (s := S)]
  · rw [Polynomial.eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have hwe := (hS e).1 he
    rw [weight_fin_two] at hwe
    rw [prod_pow_fin_two, ← PowerSeries.coeff, ← hwe,
      (coeff_pow_mul_pow_of_le_order hz hw (e 0) (e 1)).2, hzs, hwt]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      smul_eq_mul]
    rw [pow_add, pow_mul, pow_mul]
    ring
  · intro e he
    rw [Function.mem_support] at he
    rw [Finset.mem_coe, hS]
    by_contra hne
    apply he
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder _
        (lt_of_lt_of_le (by exact_mod_cast hlt) hD), zero_smul]
    · rw [weight_fin_two] at hgt
      rw [prod_pow_fin_two, ← PowerSeries.coeff,
        (coeff_pow_mul_pow_of_le_order hz hw (e 0) (e 1)).1 D (by omega), smul_zero]


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.SS.exists_polynomial_leading_quotient_subst :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ (r : ℕ) (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), d ≠ 0 → (∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) → ∃ (Pd : Polynomial k) (P : Fin r → Polynomial k), Pd ≠ 0 ∧ (∀ i, P i = 0 ↔ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ ∀ (s t : k) (z w : PowerSeries k), s ≠ 0 → (m : ℕ∞) ≤ z.order → (n : ℕ∞) ≤ w.order → PowerSeries.coeff m z = s ^ m → PowerSeries.coeff n w = s ^ n * t → Pd.eval t ≠ 0 → MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d ≠ 0 ∧ ∃ y : Fin r → PowerSeries k, ∀ i, y i * MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) d = MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) (h i) ∧ PowerSeries.constantCoeff (y i) * Pd.eval t = (P i).eval t := by
  intro k _ _ m n hm hn r h d hd hdh
  have hfin : ((MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d).toNat : ℕ∞) =
      MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d :=
    ENat.coe_toNat ((MvPowerSeries.weightedOrder_eq_top_iff _).not.2 hd)
  set D := (MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d).toNat with hD_def
  have hWpos : ∀ x, (![m, n] : Fin 2 → ℕ) x ≠ 0 := by
    intro x; fin_cases x <;> simp <;> omega
  set S := (Finsupp.finite_of_nat_weight_le _ hWpos D).toFinset.filter
    fun e => Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D with hS_def
  have hS : ∀ e, e ∈ S ↔ Finsupp.weight (![m, n] : Fin 2 → ℕ) e = D := by
    intro e
    simp only [hS_def, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
  have hDd : (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d := hfin.le
  have hDh : ∀ i, (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i) :=
    fun i => hfin.le.trans (hdh i)
  refine ⟨∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e d) * Polynomial.X ^ (e 1),
    fun i => ∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e (h i)) * Polynomial.X ^ (e 1), ?_, ?_, ?_⟩
  · intro h0
    have := (leading_polynomial_eq_zero_iff_lt_weightedOrder hm d hDd S hS).1 h0
    rw [hfin] at this
    exact lt_irrefl _ this
  · intro i
    rw [leading_polynomial_eq_zero_iff_lt_weightedOrder hm (h i) (hDh i) S hS, hfin]
  · intro s t z w hs0 hz hw hzs hwt hPd
    have hz0 : PowerSeries.coeff 0 z = 0 :=
      PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by exact_mod_cast hm) hz)
    have hw0 : PowerSeries.coeff 0 w = 0 :=
      PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by exact_mod_cast hn) hw)
    rw [PowerSeries.coeff_zero_eq_constantCoeff] at hz0 hw0
    have hsub : MvPowerSeries.HasSubst (![z, w] : Fin 2 → PowerSeries k) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
        fin_cases i
        · exact hz0
        · exact hw0
    have factor : ∀ f : MvPowerSeries (Fin 2) k,
        (D : ℕ∞) ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) f →
        ∃ g : PowerSeries k, MvPowerSeries.subst (![z, w] : Fin 2 → PowerSeries k) f =
          PowerSeries.X ^ D * g ∧ PowerSeries.constantCoeff g =
            s ^ D * (∑ e ∈ S, Polynomial.C (MvPowerSeries.coeff e f) * Polynomial.X ^ (e 1)).eval t := by
      intro f hf
      obtain ⟨g, hg⟩ := PowerSeries.X_pow_dvd_iff.2 fun j hj =>
        coeff_subst_eq_zero_of_lt hz hw hsub hf hj
      refine ⟨g, hg, ?_⟩
      have := coeff_subst_eq_pow_mul_eval_leading hz hw hsub hzs hwt hf S hS
      rw [hg, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff] at this
      exact this
    obtain ⟨gd, hgd, hgd0⟩ := factor d hDd
    have hgd0' : PowerSeries.constantCoeff gd ≠ 0 := by
      rw [hgd0]; exact mul_ne_zero (pow_ne_zero _ hs0) hPd
    refine ⟨?_, fun i => (factor (h i) (hDh i)).choose * gd⁻¹, fun i => ?_⟩
    · rw [hgd]
      exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero)
        fun h0 => hgd0' (by rw [h0, map_zero])
    · obtain ⟨hgi, hgi0⟩ := (factor (h i) (hDh i)).choose_spec
      constructor
      · rw [hgd, hgi, show (factor (h i) (hDh i)).choose * gd⁻¹ * (PowerSeries.X ^ D * gd) =
          PowerSeries.X ^ D * (factor (h i) (hDh i)).choose * (gd * gd⁻¹) by ring,
          PowerSeries.mul_inv_cancel _ hgd0', _root_.mul_one]
      · rw [map_mul, PowerSeries.constantCoeff_inv, hgi0, hgd0]
        field_simp

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelExtensionOfDefinedAtPointsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_model_extension_of_definedAtPoints : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A A' : Over (Sp K)) (M : Model R A) (N : Model R A') (f : A ⟶ A'), (∀ y, DefAt M N f y) → ∃! g : M.Y ⟶ N.Y, M.j ≫ g.left = f.left ≫ N.j := by
  first | exact @GlobalTheory.SS.existsUnique_extension_of_forall_defAt | exact GlobalTheory.SS.existsUnique_extension_of_forall_defAt | (intros; apply GlobalTheory.SS.existsUnique_extension_of_forall_defAt <;> assumption)
end

