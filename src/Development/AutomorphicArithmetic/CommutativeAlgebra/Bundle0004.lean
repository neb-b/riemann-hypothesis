module

public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0001
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsTwoChartQuotientOfFiniteCoord
section
noncomputable section
open IsLocalRing UpperTheory.Et

private theorem coord_mem_of_mem {A D ι : Type} [CommRing A] [CommRing D] [Algebra A D]
    (β : Module.Basis ι A D) (I : Ideal A) {x : D} (hx : x ∈ I.map (algebraMap A D)) (i : ι) :
    β.repr x i ∈ I := by
  have hx' : x ∈ I • (⊤ : Submodule A D) := by
    rw [Ideal.smul_top_eq_map]
    exact hx
  refine Submodule.smul_induction_on (p := fun y => β.repr y i ∈ I) hx' ?_ ?_
  · intro a ha n _
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact I.mul_mem_right _ ha
  · intro y z hy hz
    rw [map_add (f := _), Finsupp.add_apply]
    exact I.add_mem hy hz

private theorem mem_smul_span_of_coord {A D ι : Type} [CommRing A] [CommRing D] [Algebra A D]
    (β : Module.Basis ι A D) (I : Ideal A) (W : Set ι) {x : D}
    (hW : x ∈ Submodule.span A (β '' W)) (hc : ∀ i, β.repr x i ∈ I) :
    x ∈ I • Submodule.span A (β '' W) := by
  have hs : ↑(β.repr x).support ⊆ W := (β.mem_span_image).1 hW
  rw [← β.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ (fun i hi => ?_)
  exact Submodule.smul_mem_smul (hc i) (Submodule.subset_span ⟨i, hs hi, rfl⟩)

private theorem mem_map_of_coord {A D ι : Type} [CommRing A] [CommRing D] [Algebra A D]
    (β : Module.Basis ι A D) (I : Ideal A) {x : D} (hc : ∀ i, β.repr x i ∈ I) :
    x ∈ I.map (algebraMap A D) := by
  rw [← β.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Ideal.sum_mem _ (fun i _ => ?_)
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hc i))

theorem UpperTheory.exists_twoChart_quotient_of_finite_coord :
    ∀ (A D : Type) [CommRing A] [CommRing D] [Algebra A D] (T : TC A D), T.Fin → T.Coord → ∀ I : Ideal A, ∃ T' : TC A (D ⧸ I.map (algebraMap A D)), T'.Fin ∧ T'.t = Ideal.Quotient.mk _ T.t ∧ T'.s = Ideal.Quotient.mk _ T.s ∧
      (∀ j, ∀ y ∈ T'.S j, ∃ x ∈ T.S j, Ideal.Quotient.mk _ x = y) ∧ (∀ j, ∀ x ∈ T.S j, Ideal.Quotient.mk _ x ∈ T'.S j) ∧
      (∀ x ∈ T.B, x ∈ I.map (algebraMap A D) → x ∈ I • Subalgebra.toSubmodule T.B) ∧ ∀ x ∈ T.C, x ∈ I.map (algebraMap A D) → x ∈ I • Subalgebra.toSubmodule T.C := by
  classical
  intro A D _ _ _ T hF hC I
  obtain ⟨ι, β, U, V, hU, hV⟩ := hC
  set J := I.map (algebraMap A D) with hJ
  let q := Ideal.Quotient.mkₐ A J
  have hq : ∀ z, q z = Ideal.Quotient.mk J z := fun z => rfl
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have h1 : Ideal.Quotient.mk J T.t * Ideal.Quotient.mk J T.s = 1 := by
    rw [← map_mul, T.ts, map_one]
  let T' : TC A (D ⧸ J) :=
    { B := T.B.map q
      C := T.C.map q
      t := Ideal.Quotient.mk J T.t
      s := Ideal.Quotient.mk J T.s
      ts := h1
      tB := Subalgebra.mem_map.2 ⟨T.t, T.tB, rfl⟩
      sC := Subalgebra.mem_map.2 ⟨T.s, T.sC, rfl⟩
      locB := by
        intro y
        obtain ⟨x, rfl⟩ := hsurj y
        obtain ⟨k, hk⟩ := T.locB x
        exact ⟨k, Subalgebra.mem_map.2 ⟨_, hk, by rw [hq, map_mul, map_pow]⟩⟩
      locC := by
        intro y
        obtain ⟨x, rfl⟩ := hsurj y
        obtain ⟨k, hk⟩ := T.locC x
        exact ⟨k, Subalgebra.mem_map.2 ⟨_, hk, by rw [hq, map_mul, map_pow]⟩⟩ }
  refine ⟨T', ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · obtain ⟨X, hX1, hX2⟩ := hF
    refine ⟨X.image q, ?_, ?_⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact Subalgebra.mem_map.2 ⟨x, hX1 x hx, rfl⟩
    · intro b hb
      obtain ⟨b0, hb0, rfl⟩ := Subalgebra.mem_map.1 hb
      have hm := Submodule.mem_map_of_mem (f := q.toLinearMap) (hX2 b0 hb0)
      rw [Submodule.map_span] at hm
      refine Submodule.span_mono ?_ hm
      rintro _ ⟨y, ⟨x, hx, i, rfl⟩, rfl⟩
      refine ⟨q x, Finset.mem_image.2 ⟨x, hx, rfl⟩, i, ?_⟩
      show q (T.t ^ i * x) = Ideal.Quotient.mk J T.t ^ i * q x
      rw [map_mul, map_pow]
      rfl
  · intro j y hy
    obtain ⟨hyB, hyC⟩ := Submodule.mem_inf.1 hy
    obtain ⟨b, hb, rfl⟩ := Subalgebra.mem_map.1 hyB
    obtain ⟨c, hc, hce⟩ := Subalgebra.mem_map.1 (Submodule.mem_comap.1 hyC)
    have hw : T.t ^ j * c ∈ Submodule.span A (β '' V j) := by
      rw [← (hV j).1, Submodule.mem_comap, LinearMap.mulLeft_apply, ← mul_assoc, ← mul_pow,
        mul_comm T.s, T.ts, one_pow, one_mul]
      exact hc
    have hbw : b - T.t ^ j * c ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, ← hq c, hce]
      change Ideal.Quotient.mk J b - Ideal.Quotient.mk J T.t ^ j *
        (Ideal.Quotient.mk J T.s ^ j * Ideal.Quotient.mk J b) = 0
      rw [← mul_assoc, ← mul_pow, h1, one_pow, one_mul, sub_self]
    have hcoord := coord_mem_of_mem β I hbw
    have hbU : ↑(β.repr b).support ⊆ U := β.mem_span_image.1 (by rw [← hU]; exact hb)
    have hwV : ↑(β.repr (T.t ^ j * c)).support ⊆ V j := β.mem_span_image.1 hw
    set f := Finsupp.filter (· ∈ V j) (β.repr b) with hf
    have hrx : β.repr (β.repr.symm f) = f := β.repr.apply_symm_apply f
    refine ⟨β.repr.symm f, Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · show β.repr.symm f ∈ Subalgebra.toSubmodule T.B
      rw [hU, β.mem_span_image, hrx]
      intro i hi
      rw [Finset.mem_coe, hf, Finsupp.support_filter, Finset.mem_filter] at hi
      exact hbU hi.1
    · show β.repr.symm f ∈ Submodule.comap (LinearMap.mulLeft A (T.s ^ j)) (Subalgebra.toSubmodule T.C)
      rw [(hV j).1, β.mem_span_image, hrx]
      intro i hi
      rw [Finset.mem_coe, hf, Finsupp.support_filter, Finset.mem_filter] at hi
      exact hi.2
    · refine Ideal.Quotient.eq.2 (mem_map_of_coord β I (fun i => ?_))
      rw [map_sub, Finsupp.sub_apply, hrx, hf, Finsupp.filter_apply]
      by_cases hi : i ∈ V j
      · rw [if_pos hi, sub_self]
        exact I.zero_mem
      · rw [if_neg hi, zero_sub]
        have hw0 : β.repr (T.t ^ j * c) i = 0 := Finsupp.notMem_support_iff.1 (fun h => hi (hwV h))
        have hci := hcoord i
        rw [map_sub, Finsupp.sub_apply, hw0, sub_zero] at hci
        exact I.neg_mem hci
  · intro j x hx
    obtain ⟨hxB, hxC⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨Subalgebra.mem_map.2 ⟨x, hxB, rfl⟩, ?_⟩
    show Ideal.Quotient.mk J T.s ^ j * Ideal.Quotient.mk J x ∈ T.C.map q
    exact Subalgebra.mem_map.2 ⟨T.s ^ j * x, hxC, by rw [hq, map_mul, map_pow]⟩
  · intro x hx hxJ
    have hxs : x ∈ Submodule.span A (β '' U) := by rw [← hU]; exact hx
    rw [hU]
    exact mem_smul_span_of_coord β I U hxs (coord_mem_of_mem β I hxJ)
  · intro x hx hxJ
    have hC0 : Subalgebra.toSubmodule T.C = Submodule.span A (β '' V 0) := by
      rw [← (hV 0).1, pow_zero, LinearMap.mulLeft_one, Submodule.comap_id]
    have hxs : x ∈ Submodule.span A (β '' V 0) := by rw [← hC0]; exact hx
    rw [hC0]
    exact mem_smul_span_of_coord β I (V 0) hxs (coord_mem_of_mem β I hxJ)

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsIntegralOfLocalizationCoverUnitProduct
section
open UpperTheory.Et

namespace UpperTheory.IntegralSubring

variable {A D B : Type} [CommRing A] [CommRing D] [Algebra A D] [CommRing B]

private def sub (φ : B →+* D) (α : A →+* B) (h : φ.comp α = algebraMap A D) : Subalgebra A D :=
  { φ.range with
    algebraMap_mem' := fun r => ⟨α r, by rw [← h]; rfl⟩ }

private theorem mem_sub (φ : B →+* D) (α : A →+* B) (h : φ.comp α = algebraMap A D) (x : D) :
    x ∈ sub φ α h ↔ ∃ y, φ y = x := Iff.rfl

private theorem coe_sub (φ : B →+* D) (α : A →+* B) (h : φ.comp α = algebraMap A D) :
    ((sub φ α h : Subalgebra A D) : Set D) = Set.range φ := rfl

private theorem int_sub (φ : B →+* D) (α : A →+* B) (h : φ.comp α = algebraMap A D) (t : B)
    (hint : ∀ x : B, IsIntegral (Subring.closure (Set.range α ∪ {t})) x) :
    ∀ x ∈ sub φ α h, IsIntegral (Algebra.adjoin A {φ t}) x := by
  rintro x ⟨y, rfl⟩
  have hle : Subring.closure (Set.range α ∪ {t}) ≤
      (Algebra.adjoin A {φ t}).toSubring.comap φ := by
    rw [Subring.closure_le]
    rintro z (⟨r, rfl⟩ | hz)
    · have : φ (α r) = algebraMap A D r := by rw [← h]; rfl
      change φ (α r) ∈ Algebra.adjoin A {φ t}
      rw [this]
      exact Subalgebra.algebraMap_mem _ r
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact Algebra.subset_adjoin (Set.mem_singleton _)
  let f : Subring.closure (Set.range α ∪ {t}) →+* Algebra.adjoin A {φ t} :=
    (φ.comp (Subring.closure (Set.range α ∪ {t})).subtype).codRestrict
      (Algebra.adjoin A {φ t}) (fun r => hle r.2)
  exact IsIntegral.map_of_comp_eq f φ (by ext r; rfl) (hint y)

private theorem roots_sub (φ : B →+* D) (α : A →+* B) (h : φ.comp α = algebraMap A D)
    (hφ : Function.Injective φ)
    (hr : ∀ p : Polynomial B, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0) :
    Roots (sub φ α h) := by
  intro p hp hd
  let g : B →+* sub φ α h := φ.codRestrict (sub φ α h) (fun y => (mem_sub φ α h _).2 ⟨y, rfl⟩)
  have hg : Function.Bijective g := by
    refine ⟨fun a b hab => hφ (congrArg Subtype.val hab), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := (mem_sub φ α h x).1 hx
    exact ⟨y, rfl⟩
  let e := RingEquiv.ofBijective g hg
  obtain ⟨a, ha⟩ := hr (p.map (e.symm : sub φ α h →+* B)) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have hpm : (p.map (e.symm : sub φ α h →+* B)).map (e : B →+* sub φ α h) = p := by
    rw [Polynomial.map_map]
    convert Polynomial.map_id
    ext x
    simp
  rw [← hpm, Polynomial.eval_map]
  have := Polynomial.eval₂_hom (e : B →+* sub φ α h) a (p := p.map (e.symm : sub φ α h →+* B))
  rw [ha, map_zero] at this
  exact this

end UpperTheory.IntegralSubring

open UpperTheory.IntegralSubring in
theorem UpperTheory.isIntegral_of_localization_cover_unit_product :
    ∀ {A D B C : Type} [CommRing A] [CommRing D] [Algebra A D] [CommRing B] [CommRing C]
        (φ : B →+* D) (ψ : C →+* D) (α : A →+* B) (β : A →+* C),
        φ.comp α = algebraMap A D → ψ.comp β = algebraMap A D → Function.Injective φ → Function.Injective ψ →
        ∀ (t : B) (s : C), φ t * ψ s = 1 → (∀ x : D, ∃ (k : ℕ) (y : B), φ t ^ k * x = φ y) →
        (∀ x : D, ∃ (k : ℕ) (y : C), ψ s ^ k * x = ψ y) →
        (∀ x : B, IsIntegral (Subring.closure (Set.range α ∪ {t})) x) →
        (∀ x : C, IsIntegral (Subring.closure (Set.range β ∪ {s})) x) →
        (∀ p : Polynomial B, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0) →
        (∀ p : Polynomial C, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0) →
        ∃ T : TC A D, T.Int ∧ Roots T.B ∧ Roots T.C ∧ (T.B : Set D) = Set.range φ ∧ (T.C : Set D) = Set.range ψ := by
  intro A D B C _ _ _ _ _ φ ψ α β hα hβ hφ hψ t s hts hlB hlC hiB hiC hrB hrC
  refine ⟨⟨sub φ α hα, sub ψ β hβ, φ t, ψ s, hts, (mem_sub φ α hα _).2 ⟨t, rfl⟩,
    (mem_sub ψ β hβ _).2 ⟨s, rfl⟩, ?_, ?_⟩, ⟨int_sub φ α hα t hiB, int_sub ψ β hβ s hiC⟩,
    roots_sub φ α hα hφ hrB, roots_sub ψ β hβ hψ hrC, coe_sub φ α hα, coe_sub ψ β hβ⟩
  · intro x
    obtain ⟨k, y, hy⟩ := hlB x
    exact ⟨k, (mem_sub φ α hα _).2 ⟨y, hy.symm⟩⟩
  · intro x
    obtain ⟨k, y, hy⟩ := hlC x
    exact ⟨k, (mem_sub ψ β hβ _).2 ⟨y, hy.symm⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsIntegralSectionsOfIntegralHomOverAffineChart
section
open CategoryTheory Limits AlgebraicGeometry

theorem UpperTheory.isIntegral_sections_of_integralHom_over_affine_chart :
    ∀ (A : Type) [CommRing A] {P Z U L : Scheme.{0}} (u : Z ⟶ L) (l : L ⟶ Spec (CommRingCat.of A)) (f : L ⟶ P),
        IsIntegralHom u → IsPullback f l (terminal.from P) (terminal.from _) →
        ∀ (O : P.Opens), IsAffineOpen O → ∀ (τ : Γ(P, O)), Subring.closure {τ} = ⊤ →
        ∀ (ι : U ⟶ Z) [IsOpenImmersion ι], Set.range ι = ((u ≫ f) ⁻¹ᵁ O : Set Z) →
        ∀ (h : (⊤ : U.Opens) ≤ (ι ≫ u ≫ f) ⁻¹ᵁ O) (x : Γ(U, ⊤)),
          IsIntegral (Subring.closure (Set.range ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ι ≫ u ≫ l).appTop).hom ∪
            {((ι ≫ u ≫ f).appLE O ⊤ h).hom τ})) x := by
  intro A _ P Z U L u l f hu hpb O hO τ hτ ι _ hι h x
  haveI := hu
  haveI : IsAffineHom f := MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  have hV : IsAffineOpen (f ⁻¹ᵁ O) := hO.preimage f
  have hW : u ⁻¹ᵁ (f ⁻¹ᵁ O) = ι ''ᵁ ⊤ := by
    apply SetLike.coe_injective
    change ((u ≫ f) ⁻¹ᵁ O : Set Z) = _
    rw [← hι]
    simp
  have hb : Function.Surjective (ι.appLE (u ⁻¹ᵁ (f ⁻¹ᵁ O)) ⊤ h).hom := by
    have key : ∀ (W : Z.Opens) (_ : W = ι ''ᵁ ⊤) (e : ⊤ ≤ ι ⁻¹ᵁ W),
        Function.Surjective (ι.appLE W ⊤ e).hom := by
      rintro W rfl e
      have e2 : ι.appLE (ι ''ᵁ ⊤) ⊤ e = (ι.appIso ⊤).hom := (Scheme.Hom.appIso_hom' ι ⊤).symm
      rw [e2]
      exact (ι.appIso ⊤).commRingCatIsoToRingEquiv.surjective
    exact key _ hW h
  have ha : (u.appLE (f ⁻¹ᵁ O) (u ⁻¹ᵁ (f ⁻¹ᵁ O)) le_rfl).hom.IsIntegral := by
    rw [← Scheme.Hom.app_eq_appLE]
    exact IsIntegralHom.isIntegral_app u _ hV
  set φ := u.appLE (f ⁻¹ᵁ O) (u ⁻¹ᵁ (f ⁻¹ᵁ O)) le_rfl ≫ ι.appLE (u ⁻¹ᵁ (f ⁻¹ᵁ O)) ⊤ h with hφ
  have hφi : φ.hom.IsIntegral := by
    rw [hφ, CommRingCat.hom_comp]
    exact RingHom.IsIntegral.trans _ _ ha (RingHom.isIntegral_of_surjective _ hb)
  set S := Subring.closure (Set.range ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
    (ι ≫ u ≫ l).appTop).hom ∪ {((ι ≫ u ≫ f).appLE O ⊤ h).hom τ}) with hS
  have hpo := GroundTheory.Arith.SchemeCoh.isPushout_app_of_isPullback hpb hO
  have e1 : f.app O ≫ φ = (ι ≫ u ≫ f).appLE O ⊤ h := by
    rw [hφ, Scheme.Hom.app_eq_appLE, ← Category.assoc, Scheme.Hom.appLE_comp_appLE]
    exact Scheme.Hom.appLE_comp_appLE ι (u ≫ f) O _ ⊤ _ _
  have c1 : ∀ y, φ.hom ((f.app O).hom y) ∈ S := by
    intro y
    have hy : y ∈ Subring.closure {τ} := hτ ▸ Subring.mem_top y
    have hle : Subring.closure {τ} ≤ (S.comap φ.hom).comap (f.app O).hom := by
      rw [Subring.closure_le, Set.singleton_subset_iff]
      show φ.hom ((f.app O).hom τ) ∈ S
      rw [← CommRingCat.comp_apply, e1]
      exact Subring.subset_closure (Or.inr rfl)
    exact hle hy
  have e2 : l.appLE ⊤ (f ⁻¹ᵁ O) (by simp) ≫ φ = (ι ≫ u ≫ l).appTop := by
    rw [hφ]
    refine ((Scheme.Hom.appLE_comp_appLE_assoc u l ⊤ (f ⁻¹ᵁ O) (u ⁻¹ᵁ (f ⁻¹ᵁ O)) _ _ _).trans
      (Scheme.Hom.appLE_comp_appLE ι (u ≫ l) ⊤ _ ⊤ _ _)).trans ?_
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    first
      | rfl
      | (congr 1; simp)
      | simp [Scheme.Hom.appLE]
  have c2 : ∀ y, φ.hom ((l.appLE ⊤ (f ⁻¹ᵁ O) (by simp)).hom y) ∈ S := by
    intro y
    have hy : φ.hom ((l.appLE ⊤ (f ⁻¹ᵁ O) (by simp)).hom y) =
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (ι ≫ u ≫ l).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom y) := by
      rw [← CommRingCat.comp_apply, e2]
      simp
    rw [hy]
    exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
  set T := S.comap φ.hom with hT
  let g1 := CommRingCat.ofHom ((f.app O).hom.codRestrict T c1)
  let g2 := CommRingCat.ofHom ((l.appLE ⊤ (f ⁻¹ᵁ O) (by simp)).hom.codRestrict T c2)
  have hw : Scheme.Hom.appLE (terminal.from P) ⊤ O (by simp) ≫ g1 =
      Scheme.Hom.appTop (terminal.from (Spec (CommRingCat.of A))) ≫ g2 := by
    ext z
    exact congrArg (fun k => k.hom z) hpo.w
  have hid : hpo.desc g1 g2 hw ≫ CommRingCat.ofHom T.subtype = 𝟙 _ := by
    apply hpo.hom_ext
    · rw [hpo.inl_desc_assoc, Category.comp_id]
      ext z
      rfl
    · rw [hpo.inr_desc_assoc, Category.comp_id]
      ext z
      rfl
  have hall : ∀ y, φ.hom y ∈ S := by
    intro y
    have := congrArg (fun k => k.hom y) hid
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this
    rw [← this]
    exact ((hpo.desc g1 g2 hw).hom y).2
  obtain ⟨p, hm, hp⟩ := hφi x
  refine ⟨p.map (φ.hom.codRestrict S hall), hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hp
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyHoldsOfForallAndMonoAndInterAndPullback
section
open CategoryTheory Limits AlgebraicGeometry Opposite UpperTheory.Et

private theorem typeSheaf {τ : GrothendieckTopology Scheme.{0}} {R : Type} [CommRing R] {M : PMod R}
    (h : Presheaf.IsSheaf τ M) : Presieve.IsSheaf τ (M ⋙ forget _) := by
  have h1 := (Presheaf.isSheaf_iff_isSheaf_comp τ M (forget _)).mp h
  exact (isSheaf_iff_isSheaf_of_type τ _).mp h1

private theorem ap_rs {R : Type} [CommRing R] {M N : PMod R} (α : M ⟶ N) {V U : Scheme.{0}} (g : V ⟶ U)
    (y : sec M U) : ap α (rs M g y) = rs N g (ap α y) :=
  ConcreteCategory.congr_hom (α.naturality g.op) y

private theorem rs_comp {R : Type} [CommRing R] (M : PMod R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U)
    (z : sec M U) : rs M (f ≫ g) z = rs M f (rs M g z) := by
  simp [rs]

private theorem loc_mono {τ : GrothendieckTopology Scheme.{0}} {U : Scheme.{0}}
    {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : LocT τ U P) (hPQ : ∀ V g, P V g → Q V g) : LocT τ U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

private theorem loc_and {τ : GrothendieckTopology Scheme.{0}} {U : Scheme.{0}}
    {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : LocT τ U P) (h' : LocT τ U Q) :
    LocT τ U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨T, hT, hQ⟩ := h'
  exact ⟨S ⊓ T, τ.intersection_covering hS hT, fun V g hg => ⟨hP V g hg.1, hQ V g hg.2⟩⟩

private theorem loc_top {τ : GrothendieckTopology Scheme.{0}} {U : Scheme.{0}}
    {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : LocT τ U P :=
  ⟨⊤, τ.top_mem U, fun V g _ => h V g⟩

theorem UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback :
    ∀ (τ : GrothendieckTopology Scheme.{0}),
    (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ V g, P V g) → LocT τ U P) ∧
    (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), LocT τ U P → (∀ V g, P V g → Q V g) → LocT τ U Q) ∧
    (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), LocT τ U P → LocT τ U Q → LocT τ U fun V g => P V g ∧ Q V g) ∧
    (∀ (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), LocT τ U P → LocT τ W fun V g => P V (g ≫ k)) ∧
    (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), LocT τ U (fun V g => LocT τ V fun W k => P W (k ≫ g)) → LocT τ U P) ∧
    (∀ (U : Scheme.{0}) (ι : Type 1) (s : Finset ι) (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ i ∈ s, LocT τ U (P i)) → LocT τ U fun V g => ∀ i ∈ s, P i V g) ∧
    (∀ (R : Type) [CommRing R] (M : PMod R), Presheaf.IsSheaf τ M → ∀ (U : Scheme.{0}) (z : sec M U), (LocT τ U fun _ g => rs M g z = 0) → z = 0) ∧
    (∀ (R : Type) [CommRing R] (M N : PMod R) (α : M ⟶ N), Presheaf.IsSheaf τ M → Presheaf.IsSheaf τ N → ∀ (U : Scheme.{0}), (∀ (V : Scheme.{0}) (_ : V ⟶ U), Function.Injective (ap α (U := V))) → ∀ z : sec N U, (LocT τ U fun V g => ∃ y : sec M V, ap α y = rs N g z) → ∃ y : sec M U, ap α y = z) := by
  intro τ
  refine ⟨fun U P h => loc_top h, fun U P Q h hPQ => loc_mono h hPQ,
    fun U P Q h h' => loc_and h h', ?_, ?_, ?_, ?_, ?_⟩
  · intro U W k P h
    obtain ⟨S, hS, hP⟩ := h
    exact ⟨S.pullback k, τ.pullback_stable k hS, fun V g hg => hP V (g ≫ k) hg⟩
  · intro U P h
    obtain ⟨S, hS, hP⟩ := h
    choose T hT hTP using hP
    refine ⟨Sieve.bind S.arrows (fun V g hg => T V g hg), τ.bind_covering hS (fun V g hg => hT V g hg), ?_⟩
    rintro V f ⟨W, f', g, hg, hf', rfl⟩
    exact hTP W g hg V f' hf'
  · intro U ι s P h
    classical
    induction s using Finset.induction_on with
    | empty => exact loc_top fun V g i hi => absurd hi (Finset.notMem_empty i)
    | insert a s ha ih =>
      have h1 := h a (Finset.mem_insert_self a s)
      have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      refine loc_mono (loc_and h1 h2) ?_
      rintro V g ⟨hA, hB⟩ i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hA
      · exact hB i hi
  · intro R _ M hM U z hz
    obtain ⟨S, hS, hP⟩ := hz
    have hM' := typeSheaf hM
    refine (hM' S hS).isSeparatedFor.ext ?_
    intro V g hg
    change rs M g z = (ModuleCat.Hom.hom (M.map g.op)) 0
    rw [hP V g hg, map_zero]
  · intro R _ M N α hM hN U hinj z hz
    obtain ⟨S, hS, hP⟩ := hz
    choose y hy using hP
    have hM' := typeSheaf hM
    have hN' := typeSheaf hN
    let x : Presieve.FamilyOfElements (M ⋙ forget _) S.arrows := fun V g hg => y V g hg
    have hx : x.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ he
      apply hinj Z (g₁ ≫ f₁)
      change ap α (rs M g₁ (y Y₁ f₁ h₁)) = ap α (rs M g₂ (y Y₂ f₂ h₂))
      rw [ap_rs, ap_rs, hy, hy, ← rs_comp, ← rs_comp, he]
    obtain ⟨t, ht, -⟩ := hM' S hS x hx
    refine ⟨t, (hN' S hS).isSeparatedFor.ext ?_⟩
    intro V g hg
    change rs N g (ap α t) = rs N g z
    rw [← ap_rs]
    change ap α ((M ⋙ forget _).map g.op t) = rs N g z
    rw [ht g hg]
    exact hy V g hg
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.RootsOfUnityLiftModNilpotentUnique
section
noncomputable section
open IsLocalRing UpperTheory.Et

private theorem isUnit_aeval_derivative {S : Type} [CommRing S] {q : ℕ} (hq : IsUnit (q : S)) (hq0 : q ≠ 0)
    {x : S} (hx : IsNilpotent (x ^ q - 1)) :
    IsUnit (Polynomial.aeval x (Polynomial.derivative (Polynomial.X ^ q - 1 : Polynomial ℤ))) := by
  have hxq : IsUnit (x ^ q) := by
    have h := IsNilpotent.isUnit_add_one hx
    simpa using h
  have hxu : IsUnit x := (isUnit_pow_iff hq0).1 hxq
  have h2 : Polynomial.aeval x (Polynomial.derivative (Polynomial.X ^ q - 1 : Polynomial ℤ))
      = (q : S) * x ^ (q - 1) := by
    simp [Polynomial.derivative_X_pow]
  rw [h2]
  exact hq.mul (hxu.pow _)

theorem UpperTheory.roots_of_unity_lift_mod_nilpotent_unique :
    ∀ (S : Type) [CommRing S] (q : ℕ), IsUnit (q : S) → (∀ x : S, IsNilpotent (x ^ q - 1) → ∃ y : S, y ^ q = 1 ∧ IsNilpotent (x - y)) ∧
      ∀ x y : S, x ^ q = 1 → y ^ q = 1 → IsNilpotent (x - y) → x = y := by
  intro S _ q hq
  by_cases hq0 : q = 0
  · subst hq0
    have h01 : (0 : S) = 1 := by simpa using hq
    have : Subsingleton S := subsingleton_of_zero_eq_one h01
    exact ⟨fun x _ => ⟨x, Subsingleton.elim _ _, by simp⟩, fun x y _ _ _ => Subsingleton.elim _ _⟩
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_⟩
  · obtain ⟨y, ⟨hy1, hy2⟩, -⟩ := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero
      (P := (Polynomial.X ^ q - 1 : Polynomial ℤ)) (x := x) (by simpa using hx)
      (isUnit_aeval_derivative hq hq0 hx)
    refine ⟨y, ?_, hy1⟩
    simpa [sub_eq_zero] using hy2
  · have hx' : IsNilpotent (x ^ q - 1) := by simp [hx]
    have h := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero
      (P := (Polynomial.X ^ q - 1 : Polynomial ℤ)) (x := x) (by simpa using hx')
      (isUnit_aeval_derivative hq hq0 hx')
    exact h.unique ⟨by simp, by simp [hx]⟩ ⟨hxy, by simp [hy]⟩

end
end

