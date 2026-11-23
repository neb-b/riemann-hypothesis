module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoMorphismRestrictOfLocalDominantSections
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH

open GlobalTheory.Points

theorem isIso_pullback_snd_of_dominant_section {X Y V : Scheme.{0}} (f : X ⟶ Y) [IsSeparated f] [IsReduced X]
    (q : V ⟶ Y) [IsOpenImmersion q] (g : V ⟶ X) [IsDominant g] (h : g ≫ f = q) : IsIso (pullback.snd f q) := by
  let σ : V ⟶ pullback f q := pullback.lift g (𝟙 V) (by rw [h, Category.id_comp])
  have e1 : σ ≫ pullback.fst f q = g := pullback.lift_fst _ _ _
  have e2 : σ ≫ pullback.snd f q = 𝟙 V := pullback.lift_snd _ _ _
  have : IsReduced (pullback f q) := isReduced_of_isOpenImmersion (pullback.fst f q)
  have : IsDominant (σ ≫ pullback.fst f q) := e1 ▸ inferInstance
  have : IsDominant σ := IsDominant.of_comp_of_isOpenImmersion σ (pullback.fst f q)
  refine ⟨σ, ?_, e2⟩
  refine ext_of_isDominant_of_isSeparated (pullback.snd f q) ?_ σ ?_
  · rw [Category.assoc, e2, Category.comp_id, Category.id_comp]
  · rw [← Category.assoc, e2, Category.id_comp, Category.comp_id]

theorem isIso_of_local_dominant_sections {X Y : Scheme.{0}} (f : X ⟶ Y) [IsSeparated f] [IsReduced X]
    (h : ∀ y : Y, ∃ (V : Scheme.{0}) (q : V ⟶ Y) (_ : IsOpenImmersion q) (g : V ⟶ X),
      y ∈ Set.range q ∧ IsDominant g ∧ g ≫ f = q) : IsIso f := by
  choose V q hq g hy hg e using h
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y V q fun y => ⟨y, hy y⟩
  exact IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms _) 𝒰 fun y =>
    haveI := hq y
    haveI := hg y
    isIso_pullback_snd_of_dominant_section f (q y) (g y) (e y)

theorem isIso_morphismRestrict_of_local_dominant_sections {X Y : Scheme.{0}} (f : X ⟶ Y) [IsSeparated f] [IsReduced X]
    (W : Y.Opens) (h : ∀ y ∈ W, ∃ (V : Scheme.{0}) (q : V ⟶ Y) (_ : IsOpenImmersion q) (g : V ⟶ X),
      y ∈ Set.range q ∧ Set.range q ⊆ W ∧ IsDominant g ∧ g ≫ f = q) : IsIso (f ∣_ W) := by
  have : IsSeparated (f ∣_ W) := IsZariskiLocalAtTarget.restrict (P := @IsSeparated) ‹_› W
  refine isIso_of_local_dominant_sections _ fun y => ?_
  obtain ⟨V, q, hq, g, ⟨v, hv⟩, hW, hg, e⟩ := h y.1 y.2
  have h1 : Set.range q ⊆ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
  have h2 : Set.range g ⊆ Set.range (f ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact hW ⟨w, by rw [← e]; rfl⟩
  have e1 := IsOpenImmersion.lift_fac W.ι q h1
  have e2 := IsOpenImmersion.lift_fac (f ⁻¹ᵁ W).ι g h2
  have : IsOpenImmersion (IsOpenImmersion.lift W.ι q h1 ≫ W.ι) := e1.symm ▸ hq
  have : IsDominant (IsOpenImmersion.lift (f ⁻¹ᵁ W).ι g h2 ≫ (f ⁻¹ᵁ W).ι) := e2.symm ▸ hg
  refine ⟨V, IsOpenImmersion.lift W.ι q h1, IsOpenImmersion.of_comp _ W.ι, IsOpenImmersion.lift (f ⁻¹ᵁ W).ι g h2,
    ⟨v, ?_⟩, IsDominant.of_comp_of_isOpenImmersion _ (f ⁻¹ᵁ W).ι, ?_⟩
  · refine Subtype.ext ?_
    rw [← hv]
    conv_rhs => rw [← e1]
    rfl
  · rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, e2, e, e1]

namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M M' : RatModel o Ω}

theorem IsNm.isIso_morphismRestrict {J : Type} [Finite J] {u : J → Ω} (h' : M'.IsNm u)
    (hn : ∀ z, IsIntegrallyClosed (M.O z)) {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' (AlgHom.id o Ω) f) (W : M.Z.Opens)
    (hW : ∀ z ∈ W, ∃ i, M.Div u i z) : IsIso (f ∣_ W) := by
  have := M.sep
  have : IsSeparated (f ≫ M.s) := hf.inducedModelMorphism_comp_structureMap.symm ▸ M'.sep
  have : IsSeparated f := IsSeparated.of_comp f M.s
  refine isIso_morphismRestrict_of_local_dominant_sections f W fun z hz => ?_
  obtain ⟨i, hi⟩ := hW z hz
  obtain ⟨U, hU, hD, hR⟩ := h'.2 i hi.1
  obtain ⟨V, hV, hzV, hle⟩ :=
    exists_isAffineOpen_mem_and_subset (U := W ⊓ ⟨_, M.isOpen_setOf_div u i⟩) (x := z) ⟨hz, hi⟩
  obtain ⟨g, hg⟩ := exists_hom_of_map_ringOn (φ := AlgHom.id o Ω) hU
    ⟨genericPoint M'.Z, hD ▸ div_genericPoint hi.1⟩ (V := V) ⟨z, hzV⟩
    fun x hx => mem_ringOn.2 fun w hw =>
      Div.map_mem_O_of_isIntegral (M' := M) (φ := AlgHom.id o Ω) (t := u) (i := i) (z := w) (hle hw).2 ((hR x).1 hx)
  have hp := specMap_valMap_fromSpec hV M.pt (M.top_le_preimage_pt ⟨z, hzV⟩)
  have hid : ∀ {Y : Scheme.{0}} (a : Sp Ω ⟶ Y), spMap (AlgHom.id o Ω).toRingHom ≫ a = a := fun a =>
    (congrArg (· ≫ a) (Spec.map_id _)).trans (Category.id_comp _)
  have hdom : IsDominant (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hzV⟩)) ≫ g) := by
    rw [hg, hid]
    infer_instance
  refine ⟨_, hV.fromSpec, inferInstance, g, hV.range_fromSpec ▸ hzV, hV.range_fromSpec ▸ fun w hw => (hle hw).1,
    IsDominant.of_comp (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hzV⟩))) g, ?_⟩
  refine hom_ext_of_isOpenImmersion (φ := AlgHom.id o Ω) hV.fromSpec hp ?_ (hp.trans (hid _).symm)
  rw [← Category.assoc, hg, hid]
  exact hf

end RatModel

theorem isIso_morphismRestrict_of_isNm_prod : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (M' : RatModel o Ω) (J J' : Type) [Finite J] [Finite J'] (t : J → Ω) (t' : J' → Ω) (f : M'.Z ⟶ M.Z), M.IsNm t → M'.IsNm (fun q : J × J' => t q.1 * t' q.2) → IsProper M'.s → M.IsHom M' (AlgHom.id o Ω) f → ∀ W : M.Z.Opens, (∀ z ∈ W, ∃ i', M.Div t' i' z) → IsIso (f ∣_ W) := by
  intro o Ω _ _ _ M M' J J' _ _ t t' f h h' _ hf W hW
  refine h'.isIso_morphismRestrict (RatModel.isIntegrallyClosed_O h.isNormalScheme) hf W fun z hz => ?_
  obtain ⟨i, hi⟩ := h.1 z
  obtain ⟨i', hi'⟩ := hW z hz
  exact ⟨(i, i'), RatModel.div_prod_iff.2 ⟨hi, hi'⟩⟩

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

open IsLocalRing Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem splits_of_monic_OO {q : (OO p)[X]} (hq : q.Monic) : q.Splits := by
  refine Splits.of_splits_map_of_injective (i := (OO p).subtype) Subtype.val_injective
    (IsAlgClosed.splits _) fun a ha => ?_
  have h : IsIntegral (OO p) a := ⟨q, hq, by
    have := isRoot_of_mem_roots ha
    rwa [IsRoot, Polynomial.eval_map] at this⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact ⟨y, hy⟩

theorem exists_root_residue_OO {q : (OO p)[X]} (hq : q.Monic) {b : kb p}
    (hb : q.eval₂ (residue (OO p)) b = 0) : ∃ a : OO p, q.eval a = 0 ∧ residue (OO p) a = b := by
  have h0 : q.map (residue (OO p)) ≠ 0 := (hq.map _).ne_zero
  have h : b ∈ (q.map (residue (OO p))).roots := by
    rw [mem_roots h0, IsRoot, Polynomial.eval_map, hb]
  rw [(splits_of_monic_OO hq).roots_map_of_ne_zero h0, Multiset.mem_map] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, isRoot_of_mem_roots ha, rfl⟩

theorem isAlgClosed_kb : IsAlgClosed (kb p) := by
  refine IsAlgClosed.of_exists_root _ fun f hf hirr => ?_
  obtain ⟨q, hq, -, hmon⟩ := lifts_and_degree_eq_and_monic
    (mem_lifts_of_surjective (residue_surjective (R := OO p)) f) hf
  have hs : f.Splits := hq ▸ (splits_of_monic_OO hmon).map _
  exact hs.exists_eval_eq_zero (degree_pos_of_irreducible hirr).ne'

theorem charP_kb : CharP (kb p) p :=
  (CharP.charP_iff_prime_eq_zero Fact.out).2 GlobalTheory.ZH.natCast_residueField_OO

theorem exists_pow_eq_one_kb (x : kb p) (hx : x ≠ 0) : ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1 := by
  haveI := charP_kb (p := p)
  letI := ZMod.algebra (kb p) p
  have h : (algebraMap (ZMod p) (kb p)).IsIntegral := by
    refine RingHom.IsIntegral.tower_top (Int.castRingHom (ZMod p)) _ ?_
    rw [RingHom.ext_int (RingHom.comp _ _) (Int.castRingHom _)]
    exact GlobalTheory.ZH.isIntegral_int_residueField_OO
  have h' : IsIntegral (ZMod p) x := h x
  let K := IntermediateField.adjoin (ZMod p) {x}
  haveI : FiniteDimensional (ZMod p) K := IntermediateField.adjoin.finiteDimensional h'
  haveI : Finite K := Module.finite_of_finite (ZMod p)
  let y : K := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h0 => hx (congrArg Subtype.val h0)
  obtain ⟨n, hn, e⟩ := (isOfFinOrder_of_finite (Units.mk0 y hy)).exists_pow_eq_one
  exact ⟨n, hn, by simpa [y] using congrArg (fun u : Kˣ => ((u : K) : kb p)) e⟩

theorem algEquiv_mem_OO (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {x : PadicAlgCl p} (hx : x ∈ OO p) :
    σ x ∈ OO p := by
  rw [GlobalTheory.ZH.mem_OO_iff, ← GlobalTheory.isIntegral_padicInt_iff_norm_le_one] at hx ⊢
  exact hx.map (σ.toAlgHom.restrictScalars ℤ_[p])

noncomputable def restrictOO (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : OO p ≃+* OO p where
  toFun x := ⟨σ x, algEquiv_mem_OO σ x.2⟩
  invFun x := ⟨σ.symm x, algEquiv_mem_OO σ.symm x.2⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv x := Subtype.ext (σ.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul σ (x : PadicAlgCl p) y)
  map_add' x y := Subtype.ext (map_add σ (x : PadicAlgCl p) y)

theorem exists_int_map_eq_kb (q : ℤ_[p][X]) : ∃ g : ℤ[X], g.map (Int.castRingHom (kb p)) =
    q.map ((residue (OO p)).comp (GlobalTheory.ZH.padicIntToOO p)) := by
  rw [← mem_lifts, lifts_iff_coeff_lifts]
  intro n
  rw [coeff_map]
  have h1 := PadicInt.sub_zmodRepr_mem (q.coeff n)
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 := congrArg ((residue (OO p)).comp (GlobalTheory.ZH.padicIntToOO p)) hc
  rw [map_sub, map_mul, map_natCast, map_natCast, GlobalTheory.ZH.natCast_residueField_OO, zero_mul, sub_eq_zero] at h2
  exact ⟨((q.coeff n).zmodRepr : ℤ), by rw [h2]; simp⟩

theorem exists_residue_restrictOO_eq (a : OO p) (b' : kb p)
    (h : ∀ g : ℤ[X], aeval (residue (OO p) a) g = 0 → aeval b' g = 0) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, residue (OO p) (restrictOO σ a) = b' := by
  have ha : IsIntegral ℤ_[p] (a : PadicAlgCl p) :=
    (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 ((GlobalTheory.ZH.mem_OO_iff _).1 a.2)
  set f := minpoly ℤ_[p] (a : PadicAlgCl p) with hf
  have key : ∀ c : OO p, (((f.map (GlobalTheory.ZH.padicIntToOO p)).eval c : OO p) : PadicAlgCl p) =
      aeval (c : PadicAlgCl p) f := fun c => by
    rw [Polynomial.eval_map]
    exact hom_eval₂ f (GlobalTheory.ZH.padicIntToOO p) (OO p).subtype c
  obtain ⟨g, hg⟩ := exists_int_map_eq_kb f
  have e : ∀ b : kb p, aeval b g = (f.map (GlobalTheory.ZH.padicIntToOO p)).eval₂ (residue (OO p)) b := fun b => by
    rw [eval₂_map, ← Polynomial.eval_map, ← hg, Polynomial.eval_map]
    rfl
  have h1 : aeval (residue (OO p) a) g = 0 := by
    have : (f.map (GlobalTheory.ZH.padicIntToOO p)).eval a = 0 := Subtype.ext ((key a).trans (minpoly.aeval _ _))
    rw [e, eval₂_hom, this, map_zero]
  obtain ⟨a', ha', rfl⟩ := exists_root_residue_OO ((minpoly.monic ha).map (GlobalTheory.ZH.padicIntToOO p))
    ((e b').symm.trans (h g h1))
  have h2 : aeval (a' : PadicAlgCl p) (minpoly ℚ_[p] (a : PadicAlgCl p)) = 0 := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] ha, aeval_map_algebraMap, ← hf, ← key, ha']
    rfl
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic _) h2
  exact ⟨σ, congrArg _ (Subtype.ext hσ)⟩

theorem exists_ringEquiv_residue_eq (F : Type) [Field F] [Finite F] (r r' : F →+* kb p) :
    ∃ σ : OO p ≃+* OO p, ∀ (x : F) (a : OO p), residue (OO p) a = r x → residue (OO p) (σ a) = r' x := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_monoid_generator (α := Fˣ)
  obtain ⟨a₀, ha₀⟩ := residue_surjective (r u)
  obtain ⟨σ, hσ⟩ := exists_residue_restrictOO_eq a₀ (r' u) fun g hg => by
    rw [ha₀] at hg
    have h1 := aeval_algHom_apply r.toIntAlgHom (u : F) g
    have h2 := aeval_algHom_apply r'.toIntAlgHom (u : F) g
    have h3 : aeval (u : F) g = 0 := r.injective ((h1.symm.trans hg).trans (map_zero r).symm)
    exact h2.trans (by rw [h3, map_zero])
  refine ⟨restrictOO σ, fun x a ha => ?_⟩
  let τ := ResidueField.mapEquiv (restrictOO σ)
  have hτ : ∀ c : OO p, τ (residue (OO p) c) = residue (OO p) (restrictOO σ c) := fun c => rfl
  rw [← hτ, ha]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨n, hn⟩ := hu (Units.mk0 x hx)
  have hx' : x = (u : F) ^ n := by simpa using (congrArg Units.val hn).symm
  rw [hx', map_pow, map_pow, map_pow, ← ha₀, hτ, hσ]

theorem kb_isAlgClosed_and_conj : ∀ (p : ℕ) [Fact p.Prime], IsAlgClosed (kb p) ∧ (∀ x : kb p, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) ∧ ∀ (F : Type) [Field F] [Finite F] (r r' : F →+* kb p), ∃ σ : OO p ≃+* OO p, ∀ (x : F) (a : OO p), IsLocalRing.residue (OO p) a = r x → IsLocalRing.residue (OO p) (σ a) = r' x :=
  fun _ _ => ⟨isAlgClosed_kb, exists_pow_eq_one_kb, exists_ringEquiv_residue_eq⟩

end GlobalTheory.ZJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSpanRowsIffCoordsMem
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem mem_span_rows_iff_coords_mem {o Ω J : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Fintype J]
    [DecidableEq J] (A : Subalgebra o Ω) {b : Matrix J J Ω} (hb : b.det ≠ 0) (u : J → Ω) :
    u ∈ Submodule.span A (Set.range b) ↔ ∀ i, Matrix.vecMul u b⁻¹ i ∈ A := by
  have hu : IsUnit b.det := isUnit_iff_ne_zero.2 hb
  have key : ∀ c : J → A, ∑ i, c i • b i = Matrix.vecMul (fun i => (c i : Ω)) b := by
    intro c
    ext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply, Subalgebra.smul_def]
  refine (Submodule.mem_span_range_iff_exists_fun (v := fun i => b i) A).trans ?_
  constructor
  · rintro ⟨c, rfl⟩ i
    rw [key, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
    exact (c i).2
  · intro h
    refine ⟨fun i => ⟨_, h i⟩, ?_⟩
    rw [key]
    show Matrix.vecMul (Matrix.vecMul u b⁻¹) b = u
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]

theorem RatModel.val_vecMul_eq_sum {o Ω J K : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Fintype J] [Field K]
    {M : RatModel o Ω} {y : Sp K ⟶ M.Z} {z : M.Z} (h : ∀ w, y w ⤳ z) {u : J → Ω} {c : Matrix J J Ω}
    (hu : ∀ j, u j ∈ M.O z) (hc : ∀ j i, c j i ∈ M.O z) (i : J) :
    M.val y (Matrix.vecMul u c i) = ∑ j, M.val y (u j) * M.val y (c j i) := by
  have e := map_sum (RatModel.valHomOf y z h) (fun j => (⟨u j, hu j⟩ * ⟨c j i, hc j i⟩ : M.O z)) Finset.univ
  simp only [map_mul, RatModel.valHomOf_apply] at e
  rw [← e]
  congr 1
  simp [Matrix.vecMul, dotProduct]

theorem sum_mul_mem_of_mem_span {J K : Type} [Fintype J] [Field K] (V : ValuationSubring K) (c : J → K)
    {s : Set (J → K)} (hs : ∀ w ∈ s, ∑ j, w j * c j ∈ V) {w : J → K} (hw : w ∈ Submodule.span V s) :
    ∑ j, w j * c j ∈ V := by
  induction hw using Submodule.span_induction with
  | mem w hw => exact hs w hw
  | zero => simp
  | add w w' _ _ hw hw' =>
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact add_mem hw hw'
  | smul a w _ hw =>
    have : ∑ j, (a • w) j * c j = (a : K) * ∑ j, w j * c j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
    rw [this]
    exact mul_mem a.2 hw

theorem mem_EE_iff_forall_test :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → S.IsEE M U₀ EE → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ v : S.J → Ω, (∀ j, v j ∈ M.ringOn U₀) → (v ∈ EE.E z ↔ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (fun j => M.val (gPt p ≫ y) (v j)) ∈ τ.E) := by
  intro o Ω _ _ _ _ S M U₀ EE hO hloc htest hEE z hz v hv
  refine ⟨fun h p _ y y₀ τ hc hat => ?_, fun h => ?_⟩
  · rw [← hEE.2 z p y y₀ τ hc hat]
    exact Submodule.subset_span ⟨v, h, rfl⟩
  obtain ⟨W, b, hzW, hb, hE⟩ := EE.loc z
  have hstd : ∀ z' ∈ U₀, ∀ u, u ∈ EE.E z' ↔ ∀ j, u j ∈ M.O z' := fun z' hz' u => by
    rw [hEE.1 z' hz']
    exact RatModel.Lat.mem_const_iff M
  have hrow : ∀ z' ∈ W, ∀ u, u ∈ EE.E z' ↔ ∀ i, Matrix.vecMul u b⁻¹ i ∈ M.O z' := fun z' hz' u => by
    rw [hE z' hz']
    exact mem_span_rows_iff_coords_mem _ hb u
  have hinv : ∀ z' ∈ U₀ ⊓ W, ∀ j i, b⁻¹ j i ∈ M.O z' := fun z' hz' j i => by
    have h1 := (hrow z' hz'.2 (Pi.single j 1)).1 ((hstd z' hz'.1 _).2 fun k => by
      rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]) i
    simpa using h1
  rw [hrow z hzW]
  intro i
  refine (hloc.1 (U₀ ⊓ W) inf_le_left (M.nonempty_inf hO.ne ⟨z, hzW⟩) z hz).2 _ ?_ ?_
  · exact RatModel.mem_ringOn.2 fun z' hz' =>
      (hrow z' hz'.2 v).1 ((hstd z' hz'.1 v).2 fun j => RatModel.mem_ringOn.1 (hv j) z' hz'.1) i
  intro p _ y hc
  have hc₀ : M.Cen U₀ z y := ⟨hc.1, fun w hw => (hc.2 hw).1⟩
  obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := htest z p y hc₀
  have hm := h p y y₀ τ hc₀ hat
  rw [← hEE.2 z p y y₀ τ hc₀ hat] at hm
  obtain ⟨ξ, hξU, hsp, hle⟩ : ∃ ξ ∈ U₀ ⊓ W, (∀ w, (gPt p ≫ y) w ⤳ ξ) ∧ M.O z ≤ M.O ξ :=
    ⟨(gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)), hc.2 ⟨_, rfl⟩,
      RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _),
      RatModel.O_le_of_specializes (RatModel.gPt_specializes hc.1 _)⟩
  rw [RatModel.val_vecMul_eq_sum hsp (fun j => RatModel.mem_ringOn.1 (hv j) ξ hξU.1) (hinv ξ hξU), ← mem_OO_iff]
  refine sum_mul_mem_of_mem_span (OO p) _ ?_ hm
  rintro _ ⟨u, huE, rfl⟩
  have h1 := (hrow z hzW u).1 huE
  have h2 : ∀ j, u j ∈ M.O ξ :=
    (hstd ξ hξU.1 u).1 ((hrow ξ hξU.2 u).2 fun k => hle (h1 k))
  have h3 := hc.norm_val_le_one (h1 i)
  rw [RatModel.val_vecMul_eq_sum hsp h2 (hinv ξ hξU)] at h3
  exact (mem_OO_iff _).2 h3

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSupIIffAndHHEqKer
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem ThetaSys.mem_supI_iff_and_HH_eq_ker :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) := by
  intro o Ω _ _ _ _ S M U₀ hO z p _ y y₀ τ hC hA
  have hw : Set.range (gPt p ≫ y) = {(gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))} :=
    RatModel.range_eq_singleton (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))
  have hξ : (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ (U₀ : Set M.Z) := hC.2 ⟨_, rfl⟩
  have hsp := RatModel.specializes_of_range_eq hw
  have hthO : ∀ j, S.th j ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) :=
    fun j => RatModel.ringOn_le_O hξ (hO.le (S.th_mem j))
  have hinvO : ∀ j, S.th j ≠ 0 →
      (S.th j)⁻¹ ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) :=
    fun j hj => RatModel.ringOn_le_O hξ (hO.th_unit j hj)
  have hmul : ∀ i j, S.th i ≠ 0 → M.val (gPt p ≫ y) (S.th j) =
      M.val (gPt p ≫ y) (S.th j / S.th i) * M.val (gPt p ≫ y) (S.th i) := by
    intro i j hi
    have hq : S.th j / S.th i ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) := by
      rw [div_eq_mul_inv]; exact mul_mem (hthO j) (hinvO i hi)
    rw [← RatModel.val_mul hsp hq (hthO i), div_mul_cancel₀ _ hi]
  have hval : ∀ x, ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = ‖M.val (gPt p ≫ y) (S.th x)‖ := fun x => by rw [hA]
  have hmax : IsGreatest (Set.range fun x => ‖M.val (gPt p ≫ y) (S.th x)‖) τ.δ := by
    simpa only [hval] using τ.δ_max
  have fwd : ∀ x, M.Div S.th x z → ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ := by
    intro x hx
    apply le_antisymm (hmax.2 ⟨x, rfl⟩)
    obtain ⟨j, hj⟩ := hmax.1
    rw [← hj]
    dsimp only
    rw [hmul x j hx.1, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.Cen.norm_val_le_one hC (hx.2 j))
  have key : ∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ := by
    intro x
    refine ⟨fun h => fwd x h, fun hx => ?_⟩
    obtain ⟨i, hi⟩ := hO.div z
    have h1 : ‖M.val (gPt p ≫ y) (S.th x / S.th i)‖ = 1 := by
      rw [hmul i x hi.1, norm_mul, fwd i hi] at hx
      have h2 : ‖M.val (gPt p ≫ y) (S.th x / S.th i)‖ * τ.δ = 1 * τ.δ := by rw [_root_.one_mul]; exact hx
      exact (mul_left_inj' τ.δ_pos.ne').mp h2
    show M.Div S.th x z
    exact (RatModel.Div.div_iff_isUnit hi x).mpr ((RatModel.norm_val_eq_one_iff hC.1 (hi.2 x)).mp h1)
  refine ⟨key, ?_⟩
  rw [← τ.supp]
  show AddSubgroup.closure (S.supI M z) = _
  congr 1
  ext x
  rw [key x, Set.mem_ofPred_eq, hval]

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyBiTrivOfIsIntegrallyClosed
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.BiextTriv

theorem nonempty_biTriv_of_isIntegrallyClosed (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (L : RigLB G) (c : CubicalStr G L)
    (i : splitTorus _ X ⟶ G) [IsMonHom i] : Nonempty (BiTriv c i) := by
  have : IsIntegral G.left := isIntegral_of_smooth_of_geometricallyConnected G.hom
  have : IsIntegral (G ⊗ G).left := by
    have : Smooth (fst G G).left := inferInstanceAs (Smooth (pullback.fst G.hom G.hom))
    have : GeometricallyConnected (fst G G).left :=
      inferInstanceAs (GeometricallyConnected (pullback.fst G.hom G.hom))
    exact isIntegral_of_smooth_of_geometricallyConnected (fst G G).left
  have : IsIntegral (splitTorus (Spec (CommRingCat.of A)) X ⊗ G).left := by
    have : Smooth (snd (splitTorus (Spec (CommRingCat.of A)) X) G).left :=
      inferInstanceAs (Smooth (pullback.snd (splitTorus (Spec (CommRingCat.of A)) X).hom G.hom))
    have : GeometricallyIntegral (snd (splitTorus (Spec (CommRingCat.of A)) X) G).left :=
      inferInstanceAs (GeometricallyIntegral (pullback.snd (splitTorus (Spec (CommRingCat.of A)) X).hom G.hom))
    exact isIntegral_of_geometricallyIntegral (snd (splitTorus (Spec (CommRingCat.of A)) X) G).left
  obtain ⟨s, hs, hn⟩ := exists_normalised_gen (φ := lamφ i) (ε := Oε) (fun U hU => by
      have : IsAffine U.1.toScheme := U.2
      have : IsIntegral U.1.toScheme := isIntegral_of_isOpenImmersion U.1.ι
      have h := (HasRingHomProperty.appTop (P := @Smooth) (U.1.ι ≫ G.hom) inferInstance)
      algebraize [(U.1.ι ≫ G.hom).appTop.hom]
      have : IsIntegrallyClosed Γ(Spec (CommRingCat.of A), ⊤) :=
        IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
      exact isIntegrallyClosed_of_smooth Γ(Spec (CommRingCat.of A), ⊤) _) L.isLB fun V _ h => by
    refine (prod_lam i 1 (𝟙 G) V h).trans ?_
    simp [lamForm]
  have R := (rep_val hs).mul (rep_lam i hs (fst (splitTorus _ X) G) 1).inv
  obtain ⟨s', hs', hv⟩ := exists_gen_of_rep L.isLB (lamφ i) Oε R fun V _ h => by simp [lamForm]
  have hv' : ∀ (Z : Over (Spec (CommRingCat.of A))) (t : Z ⟶ splitTorus _ X) (x : Z ⟶ G) z J, Good L.L z J →
      val s' (lift t x).left z J = val s (lift t x).left z J * (val s (lift t (1 : Z ⟶ G)).left z J)⁻¹ :=
    fun Z t x z J hJ => by rw [hv _ _ z J hJ, ← Over.comp_left, comp_lift, lift_fst, MonObj.comp_one]
  refine nonempty_biTriv c i hs' (fun Z y z J hJ => (hv' Z 1 y z J hJ).trans ?_) fun Z t z J hJ => ?_
  · exact mul_inv_eq_one.2 ((hn Z y z J hJ).trans (hn Z 1 z J hJ).symm)
  · rw [hv' Z t 1 z J hJ, mul_inv_cancel]

theorem nonempty_biTriv_normal : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (L : RigLB G) (c : CubicalStr G L) (i : splitTorus _ X ⟶ G), IsMonHom i → Nonempty (BiTriv c i) :=
  fun _ _ A _ _ _ _ X _ _ _ G _ _ _ _ L c i _ => nonempty_biTriv_of_isIntegrallyClosed A X G L c i

end GlobalTheory.BiextTriv
end

