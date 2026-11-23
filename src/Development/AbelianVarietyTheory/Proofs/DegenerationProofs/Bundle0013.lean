module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalLiftOfSmooth
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory

theorem henselianLocalRing_valuationSubring_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K]
    (V : ValuationSubring K) : HenselianLocalRing V where
  is_henselian f hf a₀ h₁ _ := by
    classical
    have hg : (f.map (algebraMap V K)).Monic := hf.map _
    have hsplit : (f.map (algebraMap V K)).Splits := IsAlgClosed.splits _

    have hev : ((f.eval a₀ : V) : K) =
        ((f.map (algebraMap V K)).roots.map fun r => (a₀ : K) - r).prod := by
      have h1 : ((f.eval a₀ : V) : K) = (f.map (algebraMap V K)).eval (a₀ : K) := by
        rw [Polynomial.eval_map]
        exact (Polynomial.eval₂_at_apply (algebraMap V K) a₀).symm
      rw [h1]
      exact hsplit.eval_eq_prod_roots_of_monic hg _
    have hlt : V.valuation (((f.map (algebraMap V K)).roots.map fun r => (a₀ : K) - r).prod) < 1 := by
      rw [← hev]
      exact (ValuationSubring.valuation_lt_one_iff V _).mp h₁
    rw [map_multiset_prod, Multiset.map_map] at hlt

    obtain ⟨r, hr, hrlt⟩ : ∃ r ∈ (f.map (algebraMap V K)).roots, V.valuation ((a₀ : K) - r) < 1 := by
      by_contra hcon
      push Not at hcon
      refine absurd hlt (not_lt.mpr (Multiset.one_le_prod_of_one_le ?_))
      simp only [Multiset.mem_map, Function.comp_apply]
      rintro _ ⟨s, hs, rfl⟩
      exact hcon s hs
    have hrV : r ∈ V := by
      rw [← V.valuation_le_one_iff]
      have h2 : r = (a₀ : K) - ((a₀ : K) - r) := by ring
      rw [h2]
      exact (Valuation.map_sub _ _ _).trans (max_le (V.valuation_le_one a₀) hrlt.le)
    refine ⟨⟨r, hrV⟩, ?_, ?_⟩
    · have hroot := (Polynomial.mem_roots hg.ne_zero).mp hr
      show Polynomial.eval _ f = 0
      apply Subtype.ext
      have h3 := Polynomial.eval₂_at_apply (p := f) (algebraMap V K) (⟨r, hrV⟩ : V)
      rw [← Polynomial.eval_map] at h3
      simpa using h3.symm.trans hroot
    · rw [ValuationSubring.valuation_lt_one_iff]
      have h4 : ((((⟨r, hrV⟩ : V) - a₀ : V)) : K) = r - a₀ := rfl
      rw [h4, Valuation.map_sub_swap]
      exact hrlt

theorem ZJ.exists_classical_lift_of_smooth :
    ∀ (p : ℕ) [Fact p.Prime] (X S : Scheme.{0}) (f : X ⟶ S) [Smooth f] (y : Sp (OO p) ⟶ S) (x : Sp (kb p) ⟶ X), x ≫ f = rPt p ≫ y → ∃ b : Sp (OO p) ⟶ X, b ≫ f = y ∧ rPt p ≫ b = x := by
  intro p _ X S f _ y x hx
  have : HenselianLocalRing (OO p) := henselianLocalRing_valuationSubring_of_isAlgClosed _
  obtain ⟨⟨b, hb⟩, hb'⟩ := reducePoint_residue_surjective f (OO p) y ⟨x, hx⟩
  exact ⟨b, hb, congrArg Subtype.val hb'⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsScalMulEqZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TensorProduct

namespace GlobalTheory

namespace GenericEq

open GenericIso

theorem map_eq_generic (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X : Over (Sp R))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (Sg : Set (Sp R)) (hD : Dense Sg)
    (Y : Over (Sp R)) [IsSeparated Y.hom] (f g : X ⟶ Y)
    (H : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
      (Over.pullback t).map f = (Over.pullback t).map g) :
    (Over.pullback (Out.jK R)).map f = (Over.pullback (Out.jK R)).map g := by
  have : IsClosedImmersion (equalizer.ι f g).left := inferInstance
  have : LocallyOfFiniteType (equalizer f g).hom := by
    rw [← Over.w (equalizer.ι f g)]; infer_instance
  have h := isIso_generic_of_dense_fibres R (equalizer f g) X (equalizer.ι f g) Sg hD
    fun x hx => by
      obtain ⟨K, _, t, ht, e⟩ := H x hx
      refine ⟨K, inferInstance, t, ht, ?_⟩
      rw [← equalizerComparison_comp_π]
      have := equalizer.ι_of_eq e
      infer_instance
  rw [← cancel_epi ((Over.pullback (Out.jK R)).map (equalizer.ι f g)), ← Functor.map_comp,
    ← Functor.map_comp, equalizer.condition]

theorem exists_smul_eq_zero {R A : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A] {D : Set (PrimeSpectrum R)} (hD : Dense D)
    (y : A) (H : ∀ x ∈ D, ∃ (K : Type) (_ : Field K) (_ : Algebra R K),
      x.asIdeal = RingHom.ker (algebraMap R K) ∧ (1 : K) ⊗ₜ[R] y = 0) :
    ∃ a : R, a ≠ 0 ∧ algebraMap R A a * y = 0 := by
  let F := Ideal.Quotient.mkₐ R (Ideal.span {y})
  have hF : Function.Surjective F := Ideal.Quotient.mkₐ_surjective _ _
  obtain ⟨a, ha0, ha⟩ := exists_pow_smul_ker_eq_zero_of_dense F hD fun x hx => by
    obtain ⟨K, _, _, hK, hy⟩ := H x hx
    refine (bijective_residueField F K x hK ⟨?_,
      Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hF⟩).1
    rw [RingHom.injective_iff_ker_eq_bot, Algebra.TensorProduct.lTensor_ker F hF,
      show RingHom.ker F = Ideal.span {y} from Ideal.mk_ker,
      Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_bot]
    exact hy
  obtain ⟨n, hn⟩ := ha y (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self y))
  exact ⟨a ^ n, pow_ne_zero _ ha0, by rw [← Algebra.smul_def]; exact hn⟩

theorem appTop_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (q : Z ⟶ Y) (p : Y ⟶ Sp R)
    (a : R) : q.appTop.hom (Out.scal p a) = Out.scal (q ≫ p) a := by
  rfl

theorem exists_scal_mul_chart {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (X : Over (Sp R)) [LocallyOfFiniteType X.hom] {Sg : Set (Sp R)} (hD : Dense Sg)
    (u : Γ(X.left, ⊤))
    (H : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
      (pullback.fst X.hom t).appTop.hom u = 0)
    (A : CommRingCat.{0}) (j : Spec A ⟶ X.left) [IsOpenImmersion j] :
    ∃ a : R, a ≠ 0 ∧ j.appTop.hom (Out.scal X.hom a * u) = 0 := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ X.hom)
  let : Algebra R A := φ.hom.toAlgebra
  have : Algebra.FiniteType R A := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hφ' : Spec.map (CommRingCat.ofHom (algebraMap R A)) = j ≫ X.hom := hφ
  obtain ⟨a, ha0, ha⟩ := exists_smul_eq_zero (R := R) hD
    ((Scheme.ΓSpecIso A).hom.hom (j.appTop.hom u)) fun x hx => by
      obtain ⟨K, _, t, ht, hu⟩ := H x hx
      obtain ⟨ψ, rfl⟩ := Spec.map_surjective t
      let : Algebra R K := ψ.hom.toAlgebra
      refine ⟨K, inferInstance, inferInstance, ?_, ?_⟩
      · have : Spec.map ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) = x :=
          ht.le (Set.mem_range_self _)
        rw [← this]
        rfl
      · have w := (isPullback_tensor (R := R) K A).w
        rw [hφ', ← Category.assoc] at w
        have e := congrArg (fun k => k.appTop.hom u) (pullback.lift_fst _ _ w)
        simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at e
        erw [hu, map_zero] at e
        have n := congrArg (fun k => k.hom (j.appTop.hom u)) (Scheme.ΓSpecIso_naturality
          (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := R) (A := K) (B := A)).toRingHom))
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at n
        erw [← e, map_zero] at n
        exact n.symm
  refine ⟨a, ha0, ?_⟩
  apply (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.injective
  rw [map_zero, ← ha, map_mul, map_mul, appTop_scal, ← hφ]
  congr 1
  have n := congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.ΓSpecIso_naturality φ)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at n
  refine n.trans ?_
  rw [Iso.inv_hom_id_apply]
  rfl

theorem exists_scal_mul_eq_zero (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (X : Over (Sp R)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (Sg : Set (Sp R))
    (hD : Dense Sg) (u : Γ(X.left, ⊤))
    (H : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
      (pullback.fst X.hom t).appTop.hom u = 0) :
    ∃ a : R, a ≠ 0 ∧ Out.scal X.hom a * u = 0 := by
  classical
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let 𝒰 : X.left.OpenCover := X.left.affineCover.finiteSubcover
  have hc : ∀ i : 𝒰.I₀, ∃ a : R, a ≠ 0 ∧ (𝒰.f i).appTop.hom (Out.scal X.hom a * u) = 0 := by
    intro i
    obtain ⟨a, ha0, ha⟩ :=
      exists_scal_mul_chart X hD u H _ ((𝒰.X i).isoSpec.inv ≫ 𝒰.f i)
    refine ⟨a, ha0, ?_⟩
    rw [← (𝒰.X i).isoSpec.hom_inv_id_assoc (𝒰.f i), Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero]
  choose a ha0 ha using hc
  refine ⟨∏ i, a i, Finset.prod_ne_zero_iff.2 fun i _ => ha0 i,
    Scheme.zero_of_zero_cover _ 𝒰 fun i => ?_⟩
  obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
  have e : Out.scal X.hom (∏ i, a i) * u = Out.scal X.hom b * (Out.scal X.hom (a i) * u) := by
    rw [hb]
    simp only [Out.scal, map_mul]
    ring
  rw [e, map_mul]
  exact mul_eq_zero_of_right _ (ha i)

theorem exists_mem_of_not_mem (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (X : Over (Sp R)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (Sg : Set (Sp R))
    (hD : Dense Sg) (V : X.left.Opens) (H : ∀ x : X.left, X.hom x ∈ Sg → x ∈ V) :
    ∃ a : R, a ≠ 0 ∧ ∀ x : X.left, a ∉ (X.hom x).asIdeal → x ∈ V := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  have hC : Topology.IsConstructible ((V : Set X.left)ᶜ) :=
    (IsCompact.isConstructible (TopologicalSpace.NoetherianSpace.isCompact _) V.isOpen).compl
  obtain ⟨W, ⟨y, hy⟩, -, hW⟩ :=
    exists_isAffineOpen_disjoint_image_of_isConstructible_of_disjoint_dense X.left (Sp R) X.hom
      _ Sg hC hD (Set.disjoint_left.2 (by rintro _ ⟨x, hx, rfl⟩ h; exact hx (H x h)))
  obtain ⟨_, ⟨a, rfl⟩, hya, haW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hy W.isOpen
  refine ⟨a, ?_, fun x hx => ?_⟩
  · rintro rfl
    exact hya (Ideal.zero_mem _)
  · by_contra hxV
    exact Set.disjoint_left.1 hW ⟨x, hxV, rfl⟩ (haW hx)

end GenericEq

open GenericEq

theorem generic_of_dense_fibres :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X : Over (Sp R)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (Sg : Set (Sp R)), Dense Sg → (∀ (Y : Over (Sp R)) [IsSeparated Y.hom] (f g : X ⟶ Y), (∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧ (Over.pullback t).map f = (Over.pullback t).map g) → (Over.pullback (Out.jK R)).map f = (Over.pullback (Out.jK R)).map g) ∧ (∀ u : Γ(X.left, ⊤), (∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧ (pullback.fst X.hom t).appTop.hom u = 0) → ∃ a : R, a ≠ 0 ∧ Out.scal X.hom a * u = 0) ∧ (∀ V : X.left.Opens, (∀ x : X.left, X.hom x ∈ Sg → x ∈ V) → ∃ a : R, a ≠ 0 ∧ ∀ x : X.left, a ∉ (X.hom x).asIdeal → x ∈ V) := by
  intro R _ _ _ X _ _ Sg hD
  exact ⟨fun Y _ f g => map_eq_generic R X Sg hD Y f g, exists_scal_mul_eq_zero R X Sg hD,
    exists_mem_of_not_mem R X Sg hD⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem finite_field_of_finiteType_int (K : Type*) [Field K] [Algebra.FiniteType ℤ K] :
    Finite K := by
  have := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  have : Module.Finite ℤ K := finite_of_finite_type_of_isJacobsonRing ℤ _
  obtain ⟨p, hp⟩ := CharP.exists K
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := CharP.charP_to_charZero K
    exact Int.not_isField (isField_of_isIntegral_of_isField
      (algebraMap ℤ K).injective_int (Field.toIsField _))
  have : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero K p).resolve_right hp0⟩
  let := ZMod.algebra K p
  have : Module.Finite (ZMod p) K := Module.Finite.of_restrictScalars_finite ℤ _ _
  exact Module.finite_of_finite (ZMod p)

theorem jacobsonSpace_of_locallyOfFiniteType_int {X : Scheme.{0}} (π : X ⟶ Sp ℤ)
    [LocallyOfFiniteType π] : JacobsonSpace X := by
  have := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  exact LocallyOfFiniteType.jacobsonSpace π

theorem finite_residueField_of_isClosed_of_locallyOfFiniteType_int {X : Scheme.{0}}
    (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (x : X) (hx : IsClosed ({x} : Set X)) :
    Finite (X.residueField x) := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have h : LocallyOfFiniteType (X.fromSpecResidueField x ≫ π) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ π)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  have e : φ.hom = algebraMap ℤ (X.residueField x) := RingHom.ext_int _ _
  have h' : (algebraMap ℤ (X.residueField x)).FiniteType := e ▸ h
  have : Algebra.FiniteType ℤ (X.residueField x) := RingHom.finiteType_algebraMap.mp h'
  exact finite_field_of_finiteType_int _

section Top

variable {T : Type*} [TopologicalSpace T] [JacobsonSpace T]

theorem subset_of_isOpen_of_closedPoints {U V : Set T} (hU : IsOpen U) (hV : IsOpen V)
    (h : ∀ x, IsClosed ({x} : Set T) → x ∈ U → x ∈ V) : U ⊆ V := by
  intro y hy
  by_contra hyV
  obtain ⟨x, ⟨hxU, hxV⟩, hx⟩ := nonempty_inter_closedPoints (Z := U ∩ Vᶜ) ⟨y, hy, hyV⟩
    (hU.isLocallyClosed.inter hV.isClosed_compl.isLocallyClosed)
  exact hxV (h x hx hxU)

theorem exists_isClosed_specializes_mem_iff (ξ : T) {ι : Type*} [Finite ι] (U : ι → Set T)
    (hU : ∀ i, IsOpen (U i)) {W : Set T} (hW : IsOpen W) (hξ : ξ ∈ W) :
    ∃ x : T, IsClosed ({x} : Set T) ∧ ξ ⤳ x ∧ x ∈ W ∧ ∀ i, x ∈ U i ↔ ξ ∈ U i := by
  have hO : IsOpen (W ∩ ⋂ i : {i // ξ ∈ U i}, U i.1) :=
    hW.inter (isOpen_iInter_of_finite fun i => hU i.1)
  obtain ⟨x, ⟨hxc, hxW, hxU⟩, hx⟩ := nonempty_inter_closedPoints
    (Z := closure {ξ} ∩ (W ∩ ⋂ i : {i // ξ ∈ U i}, U i.1))
    ⟨ξ, subset_closure rfl, hξ, Set.mem_iInter.mpr fun i => i.2⟩
    (isClosed_closure.isLocallyClosed.inter hO.isLocallyClosed)
  have hs : ξ ⤳ x := specializes_iff_mem_closure.mpr hxc
  exact ⟨x, hx, hs, hxW, fun i =>
    ⟨fun h => hs.mem_open (hU i) h, fun h => Set.mem_iInter.mp hxU ⟨i, h⟩⟩⟩

theorem exists_dense_of_closedPoints_cover [IrreducibleSpace T] {ι : Type*} [Finite ι]
    (S : ι → Set T) (h : ∀ x, IsClosed ({x} : Set T) → ∃ i, x ∈ S i) : ∃ i, Dense (S i) := by
  have hc : (⋃ i, closure (S i)) = Set.univ := by
    rw [← Set.univ_subset_iff, ← closure_closedPoints (X := T),
      (isClosed_iUnion_of_finite fun i => isClosed_closure).closure_subset_iff]
    intro x hx
    obtain ⟨i, hi⟩ := h x hx
    exact Set.mem_iUnion.mpr ⟨i, subset_closure hi⟩
  classical
  have := Fintype.ofFinite ι
  obtain ⟨Z, hZ, hZ'⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (IrreducibleSpace.isIrreducible_univ T) (Finset.univ.image fun i => closure (S i))
    (by
      intro z hz
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      exact isClosed_closure)
    (by
      intro x _
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc ▸ Set.mem_univ x : x ∈ ⋃ i, closure (S i))
      exact ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i)), hi⟩)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hZ
  exact ⟨i, fun x => hZ' (Set.mem_univ x)⟩

end Top

theorem jacobson_tools_of_locallyOfFiniteType_int :
    ∀ (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π], JacobsonSpace X ∧
      (∀ x : X, IsClosed ({x} : Set X) → Finite (X.residueField x)) ∧
      (∀ U V : X.Opens, (∀ x : X, IsClosed ({x} : Set X) → (x ∈ U ↔ x ∈ V)) → U = V) ∧
      (∀ (ξ : X) (ι : Type) [Finite ι] (U : ι → X.Opens) (W : X.Opens), ξ ∈ W →
        ∃ x : X, IsClosed ({x} : Set X) ∧ ξ ⤳ x ∧ x ∈ W ∧ ∀ i, x ∈ U i ↔ ξ ∈ U i) ∧
      (∀ (ι : Type) [Finite ι] (Sg : ι → Set X), IrreducibleSpace X →
        (∀ x : X, IsClosed ({x} : Set X) → ∃ i, x ∈ Sg i) → ∃ i, Dense (Sg i)) := by
  intro X π _
  have hJ := jacobsonSpace_of_locallyOfFiniteType_int π
  refine ⟨hJ, finite_residueField_of_isClosed_of_locallyOfFiniteType_int π, ?_, ?_, ?_⟩
  · intro U V h
    exact TopologicalSpace.Opens.ext (subset_antisymm
      (subset_of_isOpen_of_closedPoints U.isOpen V.isOpen fun x hx => (h x hx).1)
      (subset_of_isOpen_of_closedPoints V.isOpen U.isOpen fun x hx => (h x hx).2))
  · intro ξ ι _ U W hξ
    exact exists_isClosed_specializes_mem_iff ξ (fun i => (U i : Set X)) (fun i => (U i).isOpen)
      W.isOpen hξ
  · intro ι _ Sg _ h
    exact exists_dense_of_closedPoints_cover Sg h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsUnitEv
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.WtRat

variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}}

def ev (g : Sp R ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V) : Γ(Y, V) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (g.appLE V ⊤ h).hom


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}} in
theorem _root_.GlobalTheory.SS.WtRat.ev_congr {g g' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y} (e : g = g') (V : Y.Opens)
    (h : ⊤ ≤ g ⁻¹ᵁ V) (h' : ⊤ ≤ g' ⁻¹ᵁ V) (u : Γ(Y, V)) :
    _root_.GlobalTheory.SS.WtRat.ev g V h u = _root_.GlobalTheory.SS.WtRat.ev g' V h' u := by
  subst e
  rfl


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}} in
theorem _root_.GlobalTheory.SS.WtRat.ev_appLE (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (φ : Y ⟶ Y') (V : Y'.Opens)
    (W : Y.Opens) (e : W ≤ φ ⁻¹ᵁ V)
    (h : ⊤ ≤ g ⁻¹ᵁ W) (h' : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ V) (u : Γ(Y', V)) :
    _root_.GlobalTheory.SS.WtRat.ev g W h ((φ.appLE V W e).hom u) =
      _root_.GlobalTheory.SS.WtRat.ev (g ≫ φ) V h' u := by
  simp only [_root_.GlobalTheory.SS.WtRat.ev, RingHom.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE]


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}} in
theorem _root_.GlobalTheory.SS.WtRat.ev_res (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) {V W : Y.Opens} (e : W ≤ V)
    (h : ⊤ ≤ g ⁻¹ᵁ W) (h' : ⊤ ≤ g ⁻¹ᵁ V) (u : Γ(Y, V)) :
    _root_.GlobalTheory.SS.WtRat.ev g W h ((Y.presheaf.map (homOfLE e).op).hom u) =
      _root_.GlobalTheory.SS.WtRat.ev g V h' u := by
  simp only [_root_.GlobalTheory.SS.WtRat.ev, RingHom.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.map_appLE]


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}} in
theorem _root_.GlobalTheory.SS.WtRat.ev_top (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (h : ⊤ ≤ g ⁻¹ᵁ ⊤) (u : Γ(Y, ⊤)) :
    _root_.GlobalTheory.SS.WtRat.ev g ⊤ h u =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (g.appTop.hom u) := by
  simp only [_root_.GlobalTheory.SS.WtRat.ev, RingHom.comp_apply, Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]
  rfl


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}} in
theorem _root_.GlobalTheory.SS.WtRat.ev_spMap (σ : R →+* R') (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (V : Y.Opens)
    (h : ⊤ ≤ g ⁻¹ᵁ V) (h' : ⊤ ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ ≫ g) ⁻¹ᵁ V) (u : Γ(Y, V)) :
    _root_.GlobalTheory.SS.WtRat.ev (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ ≫ g) V h' u =
      σ (_root_.GlobalTheory.SS.WtRat.ev g V h u) := by
  rw [← _root_.GlobalTheory.SS.WtRat.ev_appLE (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) g V ⊤ h le_top h' u]
  erw [_root_.GlobalTheory.SS.WtRat.ev_top]
  exact congrArg (fun f => CommRingCat.Hom.hom f ((g.appLE V ⊤ h).hom u))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}} in
private theorem isUnit_of_basicOpen_covers_scheme (X : Scheme) (s : Γ(X, ⊤))
    (hb : ⊤ ≤ X.basicOpen s) : IsUnit s := by
  have := (RingedSpace.isUnit_res_basicOpen _ s).map
    (ConcreteCategory.hom (X.presheaf.map (homOfLE hb).op))
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at this
  erw [Subsingleton.elim (_ ≫ _) (𝟙 (Opposite.op (⊤ : X.Opens))),
    CategoryTheory.Functor.map_id] at this
  simpa using this


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}} in
theorem _root_.GlobalTheory.SS.WtRat.isUnit_ev (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (V : Y.Opens)
    (h : ⊤ ≤ g ⁻¹ᵁ V) (u : Γ(Y, V)) (hu : ⊤ ≤ g ⁻¹ᵁ Y.basicOpen u) :
    IsUnit (_root_.GlobalTheory.SS.WtRat.ev g V h u) := by
  have hb : ⊤ ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R).basicOpen ((g.appLE V ⊤ h).hom u) := by
    have := Scheme.basicOpen_appLE g ⊤ V h u
    erw [this]
    exact le_inf le_rfl hu
  exact (isUnit_of_basicOpen_covers_scheme _ _ hb).map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom

end GlobalTheory.SS.WtRat
end
end

