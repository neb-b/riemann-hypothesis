module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'}

theorem hom_ext_of_isOpenImmersion {W : Scheme.{0}} (q : W ⟶ M'.Z) [IsOpenImmersion q] {p : Sp Ω' ⟶ W}
    (hp : p ≫ q = M'.pt) {g h : W ⟶ M.Z} (hg : p ≫ g = spMap φ.toRingHom ≫ M.pt)
    (hh : p ≫ h = spMap φ.toRingHom ≫ M.pt) : g = h := by
  have := M.sep
  have : IsReduced W := isReduced_of_isOpenImmersion q
  have : IsDominant p := by
    refine ⟨q.isOpenEmbedding.isInducing.dense_iff.2 fun w => ?_⟩
    have e : q '' Set.range p = Set.range M'.pt := by
      rw [← hp, ← Set.range_comp]
      rfl
    rw [e]
    exact M'.pt.denseRange _
  refine ext_of_isDominant_of_isSeparated M.s (ext_of_isDominant p ?_) p (hg.trans hh.symm)
  rw [← Category.assoc, hg, ← Category.assoc, hh]

theorem exists_hom_of_map_ringOn {U : M.Z.Opens} (hU : IsAffineOpen U) (hUne : (U : Set M.Z).Nonempty)
    {V : M'.Z.Opens} (hVne : (V : Set M'.Z).Nonempty) (h : ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V) :
    ∃ g : Spec Γ(M'.Z, V) ⟶ M.Z,
      Spec.map (valMap M'.pt V (M'.top_le_preimage_pt hVne)) ≫ g = spMap φ.toRingHom ≫ M.pt := by
  let χ : M.ringOn U →+* M'.ringOn V :=
    (φ.toRingHom.comp (M.ringOn U).val.toRingHom).codRestrict (M'.ringOn V) fun x => h x x.2
  let ψ : Γ(M.Z, U) →+* Γ(M'.Z, V) :=
    (M'.sectionsEquiv V hVne).symm.toRingHom.comp (χ.comp (M.sectionsEquiv U hUne).toRingHom)
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_⟩
  conv_rhs => rw [← specMap_valMap_fromSpec hU M.pt (M.top_le_preimage_pt hUne)]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext a
  have e : (M'.sectionsEquiv V hVne (ψ a) : Ω') = φ (M.sectionsEquiv U hUne a) :=
    congrArg Subtype.val ((M'.sectionsEquiv V hVne).apply_symm_apply _)
  exact e

theorem exists_isHom_of_local (h : ∀ z : M'.Z, ∃ (V : M'.Z.Opens) (U : M.Z.Opens), z ∈ V ∧ IsAffineOpen U ∧
    (U : Set M.Z).Nonempty ∧ ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V) : ∃ f, M.IsHom M' φ f := by
  have h' : ∀ z : M'.Z, ∃ (V : M'.Z.Opens) (_ : IsAffineOpen V) (hz : z ∈ V) (g : Spec Γ(M'.Z, V) ⟶ M.Z),
      Spec.map (valMap M'.pt V (M'.top_le_preimage_pt ⟨z, hz⟩)) ≫ g = spMap φ.toRingHom ≫ M.pt := fun z => by
    obtain ⟨V, U, hz, hU, hne, H⟩ := h z
    obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset hz
    exact ⟨W, hW, hzW, exists_hom_of_map_ringOn hU hne ⟨z, hzW⟩ fun x hx => ringOn_anti hle (H x hx)⟩
  choose V hV hz g hg using h'
  have hp := fun z => specMap_valMap_fromSpec (hV z) M'.pt (M'.top_le_preimage_pt ⟨z, hz z⟩)
  let 𝒰 : M'.Z.OpenCover := Scheme.Cover.mkOfCovers M'.Z (fun z => Spec Γ(M'.Z, V z)) (fun z => (hV z).fromSpec)
    fun z => by
      have : z ∈ Set.range (hV z).fromSpec := (hV z).range_fromSpec ▸ hz z
      exact ⟨z, this⟩
  have hc : ∀ z w, pullback.fst (hV z).fromSpec (hV w).fromSpec ≫ g z =
      pullback.snd (hV z).fromSpec (hV w).fromSpec ≫ g w := fun z w =>
    hom_ext_of_isOpenImmersion (φ := φ) (pullback.fst _ _ ≫ (hV z).fromSpec)
      (p := pullback.lift _ _ ((hp z).trans (hp w).symm))
      (by rw [pullback.lift_fst_assoc, hp]) (by rw [pullback.lift_fst_assoc, hg])
      (by rw [pullback.lift_snd_assoc, hg])
  refine ⟨𝒰.glueMorphisms g hc, ?_⟩
  have e : (hV (genericPoint M'.Z)).fromSpec ≫ 𝒰.glueMorphisms g hc = g _ := 𝒰.ι_glueMorphisms g hc _
  unfold IsHom
  rw [← hg (genericPoint M'.Z), ← e, ← Category.assoc, hp]

theorem Div.map_mem_O_of_mem_adjoin {J : Type} {t : J → Ω} {i : J} {z : M'.Z}
    (h : M'.Div (fun j => φ (t j)) i z) {x : Ω} (hx : x ∈ Algebra.adjoin o (Set.range fun j => t j / t i)) :
    φ x ∈ M'.O z := by
  refine (Algebra.adjoin_le ?_ : _ ≤ (M'.O z).comap φ) hx
  rintro _ ⟨j, rfl⟩
  simpa using h.2 j

theorem Div.map_mem_O_of_isIntegral {J : Type} {t : J → Ω} {i : J} {z : M'.Z}
    (h : M'.Div (fun j => φ (t j)) i z) [IsIntegrallyClosed (M'.O z)] {x : Ω}
    (hx : IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) x) : φ x ∈ M'.O z := by
  let χ : Algebra.adjoin o (Set.range fun j => t j / t i) →+* M'.O z :=
    (φ.toRingHom.comp (Subalgebra.val _).toRingHom).codRestrict (M'.O z) fun y => h.map_mem_O_of_mem_adjoin y.2
  have hi : IsIntegral (M'.O z) (φ x) := hx.map_of_comp_eq χ φ.toRingHom (RingHom.ext fun _ => rfl)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact hy ▸ y.2

theorem IsCl.exists_isHom {J : Type} [Finite J] {t : J → Ω} (h : M.IsCl t) (hd : M'.HasDiv fun j => φ (t j)) :
    ∃ f, M.IsHom M' φ f := by
  refine exists_isHom_of_local fun z => ?_
  obtain ⟨i, hi⟩ := hd z
  have hi0 : t i ≠ 0 := (map_ne_zero φ).1 hi.1
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi0
  exact ⟨⟨_, M'.isOpen_setOf_div (fun j => φ (t j)) i⟩, U, hi, hU,
    ⟨genericPoint M.Z, hD ▸ div_genericPoint hi0⟩,
    fun x hx => mem_ringOn.2 fun w hw => Div.map_mem_O_of_mem_adjoin hw (hR ▸ hx)⟩

theorem IsNm.exists_isHom {J : Type} [Finite J] {t : J → Ω} (h : M.IsNm t) (hd : M'.HasDiv fun j => φ (t j))
    (hn : ∀ z, IsIntegrallyClosed (M'.O z)) : ∃ f, M.IsHom M' φ f := by
  refine exists_isHom_of_local fun z => ?_
  obtain ⟨i, hi⟩ := hd z
  have hi0 : t i ≠ 0 := (map_ne_zero φ).1 hi.1
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi0
  exact ⟨⟨_, M'.isOpen_setOf_div (fun j => φ (t j)) i⟩, U, hi, hU,
    ⟨genericPoint M.Z, hD ▸ div_genericPoint hi0⟩,
    fun x hx => mem_ringOn.2 fun w hw => Div.map_mem_O_of_isIntegral hw ((hR x).1 hx)⟩

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIntegrallyClosedStalkOfRingOn
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH
namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem isIntegrallyClosed_stalk_of_ringOn {U : M.Z.Opens} (hU : IsAffineOpen U) {z : M.Z} (hz : z ∈ U)
    (h : ∀ x : Ω, IsIntegral (M.ringOn U) x → x ∈ M.ringOn U) :
    IsIntegrallyClosed (M.Z.presheaf.stalk z) := by
  have hne : (U : Set M.Z).Nonempty := ⟨z, hz⟩
  have : Nonempty U := ⟨⟨z, hz⟩⟩
  have : IsFractionRing (M.ringOn U) Ω := isFractionRing_ringOn hU hne
  have : IsIntegrallyClosed (M.ringOn U) := by
    rw [isIntegrallyClosed_iff Ω]
    intro x hx
    exact ⟨⟨x, h x hx⟩, rfl⟩
  have : IsIntegrallyClosed Γ(M.Z, U) := IsIntegrallyClosed.of_equiv (M.sectionsEquiv U hne).symm
  let _ := TopCat.Presheaf.algebra_section_stalk M.Z.presheaf (⟨z, hz⟩ : U)
  have := hU.isLocalization_stalk ⟨z, hz⟩
  exact isIntegrallyClosed_of_isLocalization (M.Z.presheaf.stalk z) _
    (Ideal.primeCompl_le_nonZeroDivisors (hU.primeIdealOf ⟨z, hz⟩).asIdeal)

theorem IsNm.isNormalScheme {J : Type} {t : J → Ω} (h : M.IsNm t) : IsNormalScheme M.Z := by
  obtain ⟨hd, hU⟩ := h
  have key : ∀ z : M.Z, IsIntegrallyClosed (M.Z.presheaf.stalk z) := by
    intro z
    obtain ⟨i, hi⟩ := hd z
    obtain ⟨U, hUa, hUeq, hmem⟩ := hU i hi.1
    have hz : z ∈ (U : Set M.Z) := hUeq ▸ hi
    refine isIntegrallyClosed_stalk_of_ringOn hUa hz fun x hx => ?_
    set A := Algebra.adjoin o (Set.range fun j => t j / t i)
    have hle : A ≤ M.ringOn U := fun y hy => (hmem y).2 (isIntegral_algebraMap (x := (⟨y, hy⟩ : A)))
    let : Algebra A (M.ringOn U) := (Subalgebra.inclusion hle).toRingHom.toAlgebra
    have : IsScalarTower A (M.ringOn U) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : Algebra.IsIntegral A (M.ringOn U) := ⟨fun y =>
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom A (M.ringOn U) Ω) Subtype.val_injective).1
        ((hmem y).1 y.2)⟩
    exact (hmem x).2 (isIntegral_trans x hx)
  exact fun z => ⟨(M.stalkHom_injective z).isDomain _, key z⟩

theorem div_prod_iff {J J' : Type} {t : J → Ω} {t' : J' → Ω} {i : J} {i' : J'} {z : M.Z} :
    M.Div (fun q : J × J' => t q.1 * t' q.2) (i, i') z ↔ M.Div t i z ∧ M.Div t' i' z := by
  simp only [RatModel.Div]
  constructor
  · rintro ⟨h0, h⟩
    have hi : t i ≠ 0 := left_ne_zero_of_mul h0
    have hi' : t' i' ≠ 0 := right_ne_zero_of_mul h0
    refine ⟨⟨hi, fun j => ?_⟩, ⟨hi', fun j' => ?_⟩⟩
    · simpa [mul_div_mul_right _ _ hi'] using h (j, i')
    · simpa [mul_div_mul_left _ _ hi] using h (i, j')
  · rintro ⟨⟨hi, h⟩, ⟨hi', h'⟩⟩
    refine ⟨mul_ne_zero hi hi', fun q => ?_⟩
    rw [mul_div_mul_comm]
    exact mul_mem (h q.1) (h' q.2)

theorem div_finprod_iff {A : Type} [Fintype A] {JJ : A → Type} {tt : ∀ a, JJ a → Ω} {q : ∀ a, JJ a} {z : M.Z} :
    M.Div (fun q : ∀ a, JJ a => ∏ a, tt a (q a)) q z ↔ ∀ a, M.Div (tt a) (q a) z := by
  simp only [RatModel.Div]
  constructor
  · rintro ⟨h0, h⟩
    have hne : ∀ a, tt a (q a) ≠ 0 := fun a => Finset.prod_ne_zero_iff.1 h0 a (Finset.mem_univ a)
    intro a
    refine ⟨hne a, fun j => ?_⟩
    have hj := h (Function.update q a j)
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single a] at hj
    · simpa using hj
    · intro b _ hb
      simp [Function.update_of_ne hb, div_self (hne b)]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · intro h
    refine ⟨Finset.prod_ne_zero_iff.2 fun a _ => (h a).1, fun q' => ?_⟩
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun a _ => (h a).2 (q' a)

theorem hasDiv_finprod_iff {A : Type} [Fintype A] {JJ : A → Type} {tt : ∀ a, JJ a → Ω} :
    M.HasDiv (fun q : ∀ a, JJ a => ∏ a, tt a (q a)) ↔ ∀ a, M.HasDiv (tt a) := by
  simp only [RatModel.HasDiv]
  constructor
  · intro h a z
    obtain ⟨q, hq⟩ := h z
    exact ⟨q a, div_finprod_iff.1 hq a⟩
  · intro h z
    choose q hq using fun a => h a z
    exact ⟨q, div_finprod_iff.2 hq⟩

end RatModel

theorem isNm_normal_and_div_prod : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (J : Type) (t : J → Ω), (M.IsNm t → IsNormalScheme M.Z) ∧ (∀ (J' : Type) (t' : J' → Ω) (i : J) (i' : J') (z : M.Z), M.Div (fun q : J × J' => t q.1 * t' q.2) (i, i') z ↔ M.Div t i z ∧ M.Div t' i' z) ∧ (∀ (A : Type) [Fintype A] (JJ : A → Type) (tt : ∀ a, JJ a → Ω), M.HasDiv (fun q : ∀ a, JJ a => ∏ a, tt a (q a)) ↔ ∀ a, M.HasDiv (tt a)) := by
  intro o Ω _ _ _ M J t
  exact ⟨fun h => h.isNormalScheme, fun J' t' i i' z => RatModel.div_prod_iff,
    fun A _ JJ tt => RatModel.hasDiv_finprod_iff⟩

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMaximalComapMaximalIdealOO
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

open GlobalTheory.Points IsLocalRing

variable {p : ℕ} [Fact p.Prime]

noncomputable def padicIntToOO (p : ℕ) [Fact p.Prime] : ℤ_[p] →+* OO p :=
  (algebraMap ℤ_[p] (PadicAlgCl p)).codRestrict (OO p) fun _ =>
    (mem_OO_iff _).2 ((GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1 isIntegral_algebraMap)

theorem isIntegral_padicIntToOO : (padicIntToOO p).IsIntegral := by
  intro x
  obtain ⟨q, hq, h⟩ := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one (x : PadicAlgCl p)).2 ((mem_OO_iff _).1 x.2)
  refine ⟨q, hq, Subtype.ext ?_⟩
  exact (Polynomial.hom_eval₂ q (padicIntToOO p) (OO p).subtype x).trans h

theorem natCast_residueField_OO : ((p : ℕ) : ResidueField (OO p)) = 0 := by
  rw [← map_natCast (residue (OO p)), residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    not_isUnit_OO_iff]
  have h : (((p : ℕ) : OO p) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) p := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem isIntegral_int_residueField_OO : (Int.castRingHom (ResidueField (OO p))).IsIntegral := by
  intro x
  set ψ : ℤ_[p] →+* ResidueField (OO p) := (residue (OO p)).comp (padicIntToOO p)
  have hψ : ψ.IsIntegral :=
    RingHom.IsIntegral.trans _ _ isIntegral_padicIntToOO
      (RingHom.isIntegral_of_surjective _ residue_surjective)
  obtain ⟨q, hq, h⟩ := hψ x
  have hl : q.map ψ ∈ Polynomial.lifts (Int.castRingHom (ResidueField (OO p))) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    have h1 := PadicInt.sub_zmodRepr_mem (q.coeff n)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    have h2 := congrArg ψ hc
    rw [map_sub, map_mul, map_natCast, map_natCast, natCast_residueField_OO, zero_mul, sub_eq_zero] at h2
    exact ⟨((q.coeff n).zmodRepr : ℤ), by rw [h2]; simp⟩
  obtain ⟨r, hr, -, hrm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (hq.map ψ)
  refine ⟨r, hrm, ?_⟩
  rw [← Polynomial.eval_map, hr, Polynomial.eval_map, h]

theorem isMaximal_comap_maximalIdeal_OO {A : Type*} [CommRing A] (φ : A →+* OO p) :
    ((maximalIdeal (OO p)).comap φ).IsMaximal := by
  have h : ((residue (OO p)).comp φ).IsIntegral := by
    refine RingHom.IsIntegral.tower_top (Int.castRingHom A) _ ?_
    rw [RingHom.ext_int (RingHom.comp _ _) (Int.castRingHom _)]
    exact isIntegral_int_residueField_OO
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ h ⊥
  rwa [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, ker_residue] at this

theorem isClosed_singleton_cPt {X : Scheme.{0}} (y : Sp (OO p) ⟶ X) : IsClosed ({y (cPt p)} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro w hw
  have hs : y (cPt p) ⤳ w := specializes_iff_mem_closure.2 hw
  obtain ⟨U, hU, hwU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := w) trivial
  have hzU : y (cPt p) ∈ U := hs.mem_open U.isOpen hwU
  have hle : ⊤ ≤ y ⁻¹ᵁ U := (le_preimage_iff y U).2 hzU
  have key : ∀ f : Γ(X, U), y (cPt p) ∈ X.basicOpen f ↔
      f ∉ (maximalIdeal (OO p)).comap (valMap y U hle).hom := fun f => by
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, not_not, ← le_preimage_iff,
      le_preimage_basicOpen_iff y hle, valR_eq y U hle]
  have hm := isMaximal_comap_maximalIdeal_OO (valMap y U hle).hom
  refine (Specializes.antisymm ?_ hs).eq
  rw [specializes_iff_forall_open]
  intro V hV hzV
  obtain ⟨f, hfV, hzf⟩ := hU.exists_basicOpen_le (V := ⟨V, hV⟩) ⟨_, hzV⟩ hzU
  refine hfV ?_
  obtain ⟨g, c, hc, e⟩ := hm.exists_inv ((key f).1 hzf)
  have hwc : w ∉ X.basicOpen c := fun h => (key c).1 (hs.mem_open (X.basicOpen c).isOpen h) hc
  rw [X.mem_basicOpen _ _ hwU] at hwc
  show w ∈ X.basicOpen f
  rw [X.mem_basicOpen _ _ hwU]
  have e' := congrArg (X.presheaf.germ U w hwU).hom e
  rw [map_add (f := _), map_mul, map_one] at e'
  rcases isUnit_or_isUnit_of_add_one e' with h | h
  · exact isUnit_of_mul_isUnit_right h
  · exact absurd h hwc

theorem isClosed_centre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [Algebra.FiniteType ℤ o]
    (M : RatModel o Ω) (U : Set M.Z) (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z),
    M.Cen U z y → IsClosed ({z} : Set M.Z) :=
  fun _ _ _ _ _ _ _ _ _ _ _ y h => h.1 ▸ isClosed_singleton_cPt y

end GlobalTheory.ZH
end

