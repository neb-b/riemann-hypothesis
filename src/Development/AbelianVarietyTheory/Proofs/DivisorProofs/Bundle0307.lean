module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0289
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteClassesModuloInvolutionNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBiproductChainMapOfInjectiveFamily
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.BiprodPush

variable {R : Type} [CommRing R]

theorem cpush_comp (K : Cx R) {I J M : Cx R} (f : I ⟶ J) (g : J ⟶ M) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (f ≫ g) n x = cpush K g n (cpush K f n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [cpush, cpost_mk]
  congr 1

theorem cpush_add (K : Cx R) {I J : Cx R} (f g : I ⟶ J) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (f + g) n x = cpush K f n x + cpush K g n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [cpush, cpost_mk]
  rw [← CohomologyClass.mk_add]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_add, Cochain.comp_add]

theorem cpush_zero (K : Cx R) {I J : Cx R} (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (0 : I ⟶ J) n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [cpush, cpost_mk]
  rw [← CohomologyClass.mk_zero]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_zero]

theorem cpush_id (K : Cx R) {I : Cx R} (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (𝟙 I) n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [cpush, cpost_mk]
  congr 1
  ext1
  simp [zcomp]

def cpushHom (K : Cx R) (I J : Cx R) (n : ℤ) (x : CohomologyClass K I n) : (I ⟶ J) →+ CohomologyClass K J n where
  toFun f := cpush K f n x
  map_zero' := cpush_zero K n x
  map_add' f g := cpush_add K f g n x

theorem cpush_sum (K : Cx R) {I J : Cx R} {ι : Type} (s : Finset ι) (f : ι → (I ⟶ J)) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (∑ j ∈ s, f j) n x = ∑ j ∈ s, cpush K (f j) n x :=
  map_sum (cpushHom K I J n x) f s

end GlobalTheory.BiprodPush

end

noncomputable section

namespace GlobalTheory.BiprodPush

theorem injective_of_retracts {C : Type*} [Category C] [Preadditive C] {ι : Type} [Fintype ι] {X : C} (Y : ι → C)
    [∀ j, Injective (Y j)] (p : ∀ j, X ⟶ Y j) (i : ∀ j, Y j ⟶ X) (h : ∑ j, p j ≫ i j = 𝟙 X) : Injective X := by
  refine ⟨fun {A B} g m _ => ⟨∑ j, Injective.factorThru (g ≫ p j) m ≫ i j, ?_⟩⟩
  rw [Preadditive.comp_sum]
  simp_rw [← Category.assoc, Injective.comp_factorThru, Category.assoc, ← Preadditive.comp_sum, h, Category.comp_id]

theorem biproduct_push : ∀ (R : Type) [CommRing R] {ι : Type} [Fintype ι] (L : ι → Cx R) (C : Cx R) (g : ∀ j, L j ⟶ C) (m : ℤ), (∀ j, (L j).IsStrictlyGE m) → (∀ j n, CategoryTheory.Injective ((L j).X n)) → ∃ (D : Cx R) (f : D ⟶ C), D.IsStrictlyGE m ∧ (∀ n, CategoryTheory.Injective (D.X n)) ∧ ∀ (K : Cx R) (n : ℤ), ∃ e : (∀ j, CohomologyClass K (L j) n) ≃ CohomologyClass K D n, ∀ a, cpush K f n (e a) = ∑ j, cpush K (g j) n (a j) := by
  intro R _ ι _ L C g m hL hI
  classical
  haveI : HasFiniteBiproducts (Cx R) := HasFiniteBiproducts.of_hasFiniteProducts
  have htot : ∀ n, ∑ j, (biproduct.π L j).f n ≫ (biproduct.ι L j).f n = 𝟙 ((⨁ L).X n) := by
    intro n
    have := (HomologicalComplex.eval _ (ComplexShape.up ℤ) n).map_sum (fun j => biproduct.π L j ≫ biproduct.ι L j) Finset.univ
    rw [biproduct.total] at this
    simp only [Functor.map_id, Functor.map_comp, HomologicalComplex.eval_map] at this
    exact this.symm
  refine ⟨⨁ L, biproduct.desc g, ?_, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero, ← htot i]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : IsZero ((L j).X i) := (L j).isZero_of_isStrictlyGE m i hi
    rw [show (biproduct.π L j).f i = 0 from this.eq_of_tgt _ _, zero_comp]
  · intro n
    exact injective_of_retracts (fun j => (L j).X n) (fun j => (biproduct.π L j).f n) (fun j => (biproduct.ι L j).f n) (htot n)
  · intro K n
    refine ⟨{ toFun := fun a => ∑ j, cpush K (biproduct.ι L j) n (a j)
              invFun := fun b j => cpush K (biproduct.π L j) n b
              left_inv := ?_
              right_inv := ?_ }, ?_⟩
    · intro a
      funext k
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, ← cpush_comp]
      rw [Finset.sum_eq_single k]
      · rw [biproduct.ι_π_self, cpush_id]
      · intro j _ hj
        rw [biproduct.ι_π_ne _ hj, cpush_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    · intro b
      simp only [← cpush_comp]
      rw [← cpush_sum, biproduct.total, cpush_id]
    · intro a
      change cpush K (biproduct.desc g) n (∑ j, cpush K (biproduct.ι L j) n (a j)) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [← cpush_comp, biproduct.ι_desc]

end GlobalTheory.BiprodPush

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConductorNeZeroFiniteTypeCharZero
section
namespace GlobalTheory

theorem exists_common_denominator_of_fg {R L : Type*} [CommRing R] [IsDomain R] [Field L]
    [Algebra R L] [IsFractionRing R L] (N : Submodule R L) (hN : N.FG) :
    ∃ c : R, c ≠ 0 ∧ ∀ y ∈ N, ∃ s : R, algebraMap R L s = c • y := by
  obtain ⟨c, hc, h⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors R) hN
  exact ⟨c, nonZeroDivisors.ne_zero hc, fun y hy => h y hy⟩

theorem exists_ne_zero_mul_mem_of_isIntegral_of_fraction (K R B : Type) [Field K] [CharZero K]
    [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] [CommRing B] [IsDomain B]
    [Algebra R B] (hinj : Function.Injective (algebraMap R B)) :
    ∃ c : R, c ≠ 0 ∧ ∀ x : B, IsIntegral R x →
      (∃ r s : R, r ≠ 0 ∧ algebraMap R B r * x = algebraMap R B s) →
      ∃ s : R, algebraMap R B c * x = algebraMap R B s := by
  let L := FractionRing R
  let M := FractionRing B
  haveI : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI hfin : Module.Finite R (integralClosure R L) := finite_integralClosure_dedekind K R L L
  have hfg : (Subalgebra.toSubmodule (integralClosure R L)).FG :=
    Module.Finite.iff_fg.mp hfin
  obtain ⟨c, hc, h⟩ := exists_common_denominator_of_fg _ hfg
  refine ⟨c, hc, fun x hx ⟨r, s, hr, hrs⟩ => ?_⟩
  letI : Algebra L M := FractionRing.liftAlgebra R M
  let φ : L →ₐ[R] M := IsScalarTower.toAlgHom R L M
  have hφ : Function.Injective φ := φ.toRingHom.injective
  have hB : Function.Injective (algebraMap B M) := IsFractionRing.injective B M
  have hrM : algebraMap R M r ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R B M]
    exact (map_ne_zero_iff _ hB).mpr ((map_ne_zero_iff _ hinj).mpr hr)
  have hy : φ (algebraMap R L s / algebraMap R L r) = algebraMap B M x := by
    rw [map_div₀, AlgHom.commutes, AlgHom.commutes, div_eq_iff hrM,
      IsScalarTower.algebraMap_apply R B M, IsScalarTower.algebraMap_apply R B M, ← hrs, map_mul,
      mul_comm]
  have hint : IsIntegral R (algebraMap R L s / algebraMap R L r) := by
    rw [← isIntegral_algHom_iff φ hφ, hy]
    exact hx.map (IsScalarTower.toAlgHom R B M)
  obtain ⟨t, ht⟩ := h _ hint
  refine ⟨t, hB ?_⟩
  have := congrArg φ ht
  rw [map_smul, hy, AlgHom.commutes, Algebra.smul_def, IsScalarTower.algebraMap_apply R B M,
    IsScalarTower.algebraMap_apply R B M] at this
  rw [map_mul, this]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqDiscriminantPowMulEvalJInvariant
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in
theorem _root_.GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT : ∀ (R : Subring ℂ) (N w : ℕ)
    (f : ℍ → ℂ), 0 < N →
    (∀ γ : SL(2, ℤ), f ∣[(12 * w : ℤ)] γ = f) → _root_.GlobalTheory.QFam.QAll (· ∈ R) N f →
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ ∀ τ, f τ = _root_.ReciprocityTheory.ChartRestriction.L1.DD τ ^ w * P.eval (_root_.ReciprocityTheory.ChartRestriction.L1.jT τ) := by
  intro R N w f hN hinv hq
  obtain ⟨a, ha, haR⟩ := hq
  have hmf : _root_.ReciprocityTheory.ChartRestriction.L1.IsMF (12 * w) f := _root_.GlobalTheory.QFam.isMF_of_invariant_of_hasQ N _ f a hN hinv ha
  have h1 : _root_.GlobalTheory.QFam.HasQ 1 f fun n => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f) := by
    rw [_root_.GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion]
    obtain ⟨g, hg⟩ := hmf
    have hgf : (⇑g : ℍ → ℂ) = f := funext hg
    have h := _root_.GlobalTheory.hasQExpansion_modularForm g
    rw [hgf] at h
    simpa using h
  have hN' := _root_.GlobalTheory.QFam.hasQ_mul_spread 1 N f _ one_pos hN h1
  rw [one_mul] at hN'
  have heq := _root_.GlobalTheory.QFam.HasQ.coeff_unique hN ha hN'
  have hcoeff : _root_.ReciprocityTheory.ChartRestriction.L1.CoeffIn R (UpperHalfPlane.qExpansion 1 f) := by
    intro m
    have h := haR (N * m)
    rw [heq] at h
    simpa [_root_.GlobalTheory.QFam.spread, Nat.mul_div_cancel_left _ hN] using h
  obtain ⟨P, hPR, -, hP⟩ := _root_.ReciprocityTheory.ChartRestriction.L1.qPrin R w f hmf hcoeff
  exact ⟨P, hPR, hP⟩

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoverModelOfIsColimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtaleCoverDescent


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout {R S T P : CommRingCat.{0}} {f : R ⟶ S} {g : R ⟶ T}
    {inl : S ⟶ P} {inr : T ⟶ P} (H : IsPushout f g inl inr) (x : Spec S) (y : Spec T)
    (hxy : Spec.map f x = Spec.map g y) : ∃ z : Spec P, Spec.map inl z = x := by
  have hP := isPullback_SpecMap_of_isPushout f g inl inr H
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  refine ⟨hP.isoPullback.inv w, ?_⟩
  rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_fst]
  exact hw

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
private lemma exists_etale_pushout_of_filtered_colimit (J : Type) [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (hc : IsColimit c) {B : CommRingCat.{0}}
    (g : c.pt ⟶ B) (hg : g.hom.Etale) :
    ∃ (j : J) (B' : CommRingCat.{0}) (a : D.obj j ⟶ B') (h : B' ⟶ B),
      a.hom.Etale ∧ IsPushout a (c.ι.app j) h g := by
  letI := g.hom.toAlgebra
  haveI : Algebra.Etale c.pt B := hg
  obtain ⟨j, A, _, _, hA, ⟨e⟩⟩ := _root_.GlobalTheory.EtaleDescent.exists_etale_model_of_isColimit J D c hc B
  letI : Algebra (D.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  refine ⟨j, CommRingCat.of A, CommRingCat.ofHom (algebraMap (D.obj j) A),
    CommRingCat.ofHom ((e : TensorProduct (D.obj j) c.pt A →+* B).comp
      Algebra.TensorProduct.includeRight.toRingHom), ?_, ?_⟩
  · exact RingHom.etale_algebraMap.mpr hA
  · refine (CommRingCat.isPushout_tensorProduct (D.obj j) c.pt A).flip.of_iso (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (RingEquiv.toCommRingCatIso e.toRingEquiv) ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · ext x
      rfl
    · ext x
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      exact e.commutes x

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
private lemma exists_etale_pushout_at_later_index_of_range {J : Type} [SmallCategory J]
    {D : J ⥤ CommRingCat.{0}} (c : Cocone D) {k k' : J} (f : k ⟶ k') {B B' : CommRingCat.{0}}
    {g : c.pt ⟶ B} {a : D.obj k ⟶ B'} {h : B' ⟶ B} (ha : a.hom.Etale)
    (H : IsPushout a (c.ι.app k) h g) :
    ∃ (B'' : CommRingCat.{0}) (a' : D.obj k' ⟶ B'') (h' : B'' ⟶ B),
      a'.hom.Etale ∧ IsPushout a' (c.ι.app k') h' g ∧
      ∀ p : Spec (D.obj k'), Spec.map (D.map f) p ∈ Set.range (Spec.map a) →
        p ∈ Set.range (Spec.map a') := by
  have hw : D.map f ≫ c.ι.app k' ≫ g = a ≫ h := by
    rw [H.w, ← c.w f, Category.assoc]
  refine ⟨pushout (D.map f) a, pushout.inl (D.map f) a,
    pushout.desc (c.ι.app k' ≫ g) h hw, ?_, ?_, ?_⟩
  · exact RingHom.Etale.isStableUnderBaseChange.pushout_inl RingHom.Etale.respectsIso _ _ ha
  · have top : IsPushout a (D.map f) (pushout.inr (D.map f) a) (pushout.inl (D.map f) a) :=
      (IsPushout.of_hasPushout (D.map f) a).flip
    have big : IsPushout a (D.map f ≫ c.ι.app k')
        (pushout.inr (D.map f) a ≫ pushout.desc (c.ι.app k' ≫ g) h hw) g := by
      rw [c.w f, pushout.inr_desc]
      exact H
    exact big.of_top (pushout.inl_desc _ _ _) top
  · rintro p ⟨v, hv⟩
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout (IsPushout.of_hasPushout (D.map f) a) p v hv.symm
    exact ⟨z, hz⟩


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtaleCoverDescent.exists_etale_cover_model_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (ι : Type) [Finite ι] (B : ι → CommRingCat.{0}) (g : ∀ i, c.pt ⟶ B i), (∀ i, (g i).hom.Etale) → (∀ p : Spec c.pt, ∃ i v, Spec.map (g i) v = p) → ∀ j₀ : J, ∃ (j : J) (_ : j₀ ⟶ j) (B' : ι → CommRingCat.{0}) (g' : ∀ i, D.obj j ⟶ B' i) (h : ∀ i, B' i ⟶ B i), (∀ i, (g' i).hom.Etale ∧ IsPushout (g' i) (c.ι.app j) (h i) (g i)) ∧ ∀ p : Spec (D.obj j), ∃ i v, Spec.map (g' i) v = p := by
  intro J _ _ D c hc ι _ B g hg hsurj j₀
  classical
  have := Fintype.ofFinite ι
  choose jm Bm am hm ham hHm using fun i => exists_etale_pushout_of_filtered_colimit J D c hc (g i) (hg i)
  let O : Finset J := insert j₀ (Finset.univ.image jm)
  let j1 := IsFiltered.sup O ∅
  have f0 : j₀ ⟶ j1 := IsFiltered.toSup O ∅ (Finset.mem_insert_self _ _)
  have fm : ∀ i, jm i ⟶ j1 := fun i =>
    IsFiltered.toSup O ∅ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  choose B1 a1 h1 ha1 hH1 _ using fun i => exists_etale_pushout_at_later_index_of_range c (fm i) (ham i) (hHm i)
  let W : Set (Spec (D.obj j1)) := {q | ∀ i, q ∉ Set.range (Spec.map (a1 i))}
  have hW : IsClosed W := by
    have hWe : W = (⋃ i, Set.range (Spec.map (a1 i)))ᶜ := by
      ext q
      simp [W]
    rw [hWe, isClosed_compl_iff]
    refine isOpen_iUnion fun i => ?_
    have : Etale (Spec.map (a1 i)) := by
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      exact ha1 i
    exact (Spec.map (a1 i)).isOpenMap.isOpen_range
  have claim : ∃ (k : J) (f : j1 ⟶ k), ∀ p : Spec (D.obj k), Spec.map (D.map f) p ∉ W := by
    by_contra hcon
    push_neg at hcon
    haveI : ∀ {i i' : Jᵒᵖ} (f : i ⟶ i'), IsAffineHom ((D.op ⋙ Scheme.Spec).map f) :=
      fun f => inferInstanceAs (IsAffineHom (Spec.map (D.map f.unop)))
    obtain ⟨s, hs⟩ := exists_mem_of_isClosed_of_nonempty' (D.op ⋙ Scheme.Spec)
      (Scheme.Spec.mapCone c.op) (isLimitOfPreserves Scheme.Spec hc.op) (j := op j1)
      (fun i hij => (Spec.map (D.map hij.unop)) ⁻¹' W)
      (fun i hij => hW.preimage (Spec.map _).continuous)
      (fun i hij => hcon _ hij.unop)
      (fun i hij => (hW.preimage (Spec.map _).continuous).isCompact)
      (fun i i' hi'i hij x hx => by
        change Spec.map (D.map hij.unop) (Spec.map (D.map hi'i.unop) x) ∈ W
        rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, ← D.map_comp]
        exact hx)
    have hs1 : Spec.map (c.ι.app j1) s ∈ W := by
      have := hs (op j1) (𝟙 _)
      change Spec.map (D.map (𝟙 j1)) (Spec.map (c.ι.app j1) s) ∈ W at this
      simpa [D.map_id, Spec.map_id] using this
    obtain ⟨i, v, rfl⟩ := hsurj s
    refine hs1 i ⟨Spec.map (h1 i) v, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, (hH1 i).w, Spec.map_comp, Scheme.Hom.comp_apply]
  obtain ⟨k, f, hk⟩ := claim
  choose B2 a2 h2 ha2 hH2 hpt using fun i => exists_etale_pushout_at_later_index_of_range c f (ha1 i) (hH1 i)
  refine ⟨k, f0 ≫ f, B2, a2, h2, fun i => ⟨ha2 i, hH2 i⟩, fun p => ?_⟩
  have hp := hk p
  simp only [W, Set.mem_setOf_eq, not_forall, not_not] at hp
  obtain ⟨i, hi⟩ := hp
  obtain ⟨v, hv⟩ := hpt i p hi
  exact ⟨i, v, hv⟩

end GlobalTheory.EtaleCoverDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFactorOfIndEt
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_etale_factor_of_indEt : ∀ (A O : Type) [CommRing A] [CommRing O] [Algebra A O], IndEt A O → ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B] (φ : B →ₐ[A] O), ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.Etale A C) (ψ : B →ₐ[A] C) (χ : C →ₐ[A] O), χ.comp ψ = φ := by
  intro A O _ _ _ hO B _ _ _ φ
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := hO
  have hp : MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0}
      (CommRingCat.ofHom (algebraMap A B)) :=
    CommRingCat.isFinitelyPresentable_hom _ (RingHom.finitePresentation_algebraMap.2 inferInstance)
  obtain ⟨j, q, hq1, hq2⟩ := MorphismProperty.exists_hom_of_isFinitelyPresentable hs hp t
    (CommRingCat.ofHom φ.toRingHom) (fun j => by
      rw [(hst j).2]; ext a; simp)
  letI : Algebra A (D.obj j) := (t.app j).hom.toAlgebra
  haveI : Algebra.Etale A (D.obj j) := (hst j).1
  have h1 : ∀ a : A, q.hom (algebraMap A B a) = algebraMap A (D.obj j) a := fun a =>
    congrArg (fun f => f.hom a) hq1
  have h2 : ∀ a : A, (s.app j).hom (algebraMap A (D.obj j) a) = algebraMap A O a := fun a =>
    congrArg (fun f => f.hom a) (hst j).2
  have h3 : ∀ b : B, (s.app j).hom (q.hom b) = φ b := fun b =>
    congrArg (fun f => f.hom b) hq2
  refine ⟨D.obj j, inferInstance, inferInstance, inferInstance, ⟨q.hom, h1⟩, ⟨(s.app j).hom, h2⟩, ?_⟩
  ext b
  exact h3 b

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFaithfullyFlatPicMapAlgebraEqOne
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.PicLoc

theorem exists_away_mapAlgebra_eq_one : ∀ (A : Type) [CommRing A] (c : CommRing.Pic A) (p : Ideal A) [p.IsPrime], ∃ f ∉ p, CommRing.Pic.mapAlgebra A (Localization.Away f) c = 1 := by
  intro A _ c p _
  letI := @Module.addCommMonoidToAddCommGroup A
  haveI : Module.FinitePresentation A c := Module.finitePresentation_of_projective A c
  haveI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl c) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl c) (Localization.AtPrime p)
  refine ⟨f, hf, ?_⟩
  rw [CommRing.Pic.mapAlgebra_apply, CommRing.Pic.mk_eq_one_iff_free]
  exact Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers f) c)

theorem exists_etale_faithfullyFlat_mapAlgebra_eq_one : ∀ (A : Type) [CommRing A] (c : CommRing.Pic A), ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.Etale A B) (_ : Module.FaithfullyFlat A B), CommRing.Pic.mapAlgebra A B c = 1 := by
  intro A _ c
  classical
  let T : Set A := {f | CommRing.Pic.mapAlgebra A (Localization.Away f) c = 1}
  have hT : Ideal.span T = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hf1⟩ := exists_away_mapAlgebra_eq_one A c m
    exact hf (hle (Ideal.subset_span hf1))
  obtain ⟨s, hsT, hs⟩ := (Ideal.span_eq_top_iff_finite T).mp hT
  let R : s → Type := fun i => Localization.Away (i : A)
  haveI : ∀ i, Algebra.Etale A (R i) := fun i => Algebra.Etale.of_isLocalizationAway (i : A)
  have halg : ∀ i, (Pi.evalRingHom R i).comp (algebraMap A ((i : s) → R i)) = algebraMap A (R i) :=
    fun i => RingHom.ext fun _ => rfl
  refine ⟨(i : s) → R i, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_
    obtain ⟨i, hi⟩ : ∃ i : s, (i : A) ∉ p.asIdeal := by
      by_contra h
      push Not at h
      apply p.isPrime.ne_top
      rw [eq_top_iff, ← hs, Ideal.span_le]
      intro x hx
      exact h ⟨x, hx⟩
    have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (R i))) := by
      rw [PrimeSpectrum.localization_away_comap_range (R i) (i : A)]
      exact hi
    obtain ⟨q, rfl⟩ := hp
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom R i) q, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply, halg]
  · apply GlobalTheory.PicPi.eq_one_of_forall
    intro i
    rw [← CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapRingHom_mapRingHom, halg,
      CommRing.Pic.mapRingHom_algebraMap]
    exact hsT i.2

end GlobalTheory.PicLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitEtaleOfIndEt
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem exists_filtered_colimit_etale_of_indEt : ∀ (A O : Type) [CommRing A] [CommRing O] [Algebra A O], IndEt A O → ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ Under (CommRingCat.of A)) (ι : D ⟶ (Functor.const J).obj (Under.mk (CommRingCat.ofHom (algebraMap A O)))), Nonempty (IsColimit (Cocone.mk _ ι)) ∧ ∀ j, (D.obj j).hom.hom.Etale := by
  intro A O _ _ _ h
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := h
  have : Nonempty J := IsFiltered.nonempty
  refine ⟨J, inferInstance, inferInstance, Under.lift D t,
    { app j := Under.homMk (s.app j) (by simp [hst]) },
    ⟨Under.isColimitLiftCocone _ _ _ _ (by simp [hst]) hs⟩, fun j => (hst j).1⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteClassesModuloInvolutionNormsStatement
section
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_classes_modulo_involutionNorms : ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃+* K), (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ,
    ∃ M : Finset K, ∀ a : K, a ≠ 0 → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : K), b ≠ 0 ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : K) * x) ∧ IsIntegral ℤ ((d : K) * y)) →
    ∃ m ∈ M, ∃ e : K, e ≠ 0 ∧ a = e * m * τ e := by
  first | (exact @GlobalTheory.FixNormField.fixed_classes_mod_norms) | (exact GlobalTheory.FixNormField.fixed_classes_mod_norms) | (intros; apply GlobalTheory.FixNormField.fixed_classes_mod_norms  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreMemInducedSpaceStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_mem_induced_space : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ), GlobalTheory.RankFibre.fibre ν β a b Φ ∈ GlobalTheory.PRep.indSpace (GlobalTheory.SmGL.parab k (GlobalTheory.RankFibre.blocks a b)) (GlobalTheory.SmGL.ofChar (GlobalTheory.RankFibre.parChar ν β a b)) := by
  first | exact @GlobalTheory.RankFibre.fibre_mem_indSpace | exact GlobalTheory.RankFibre.fibre_mem_indSpace | (intros; apply GlobalTheory.RankFibre.fibre_mem_indSpace <;> assumption)
end

