module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0252
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsColimitPushoutUnder
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.BaseChangeColim

variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) (j : J) {B' : CommRingCat.{0}}
  (g' : D.obj j ⟶ B')

noncomputable def mapPush {k k' : Under j} (f : k ⟶ k') :
    pushout g' (D.map k.hom) ⟶ pushout g' (D.map k'.hom) :=
  pushout.desc (pushout.inl g' (D.map k'.hom)) (D.map f.right ≫ pushout.inr g' (D.map k'.hom))
    (by rw [pushout.condition, ← Category.assoc, ← D.map_comp, Under.w f])

@[reassoc]
lemma inl_mapPush {k k' : Under j} (f : k ⟶ k') :
    pushout.inl g' (D.map k.hom) ≫ mapPush D j g' f = pushout.inl g' (D.map k'.hom) :=
  pushout.inl_desc _ _ _

@[reassoc]
lemma inr_mapPush {k k' : Under j} (f : k ⟶ k') :
    pushout.inr g' (D.map k.hom) ≫ mapPush D j g' f = D.map f.right ≫ pushout.inr g' (D.map k'.hom) :=
  pushout.inr_desc _ _ _

noncomputable def diag : Under j ⥤ CommRingCat.{0} where
  obj k := pushout g' (D.map k.hom)
  map f := mapPush D j g' f
  map_id k := by
    apply pushout.hom_ext
    · rw [inl_mapPush, Category.comp_id]
    · rw [inr_mapPush, Category.comp_id, Under.id_right, D.map_id, Category.id_comp]
  map_comp f f' := by
    apply pushout.hom_ext
    · rw [inl_mapPush, inl_mapPush_assoc, inl_mapPush]
    · rw [inr_mapPush, inr_mapPush_assoc, inr_mapPush, Under.comp_right, D.map_comp,
        Category.assoc]

noncomputable def inrNat : Under.forget j ⋙ D ⟶ diag D j g' where
  app k := pushout.inr g' (D.map k.hom)
  naturality k k' f := by
    show D.map f.right ≫ pushout.inr g' (D.map k'.hom) = pushout.inr g' (D.map k.hom) ≫ mapPush D j g' f
    rw [inr_mapPush]

noncomputable def inlNat : (Functor.const _).obj B' ⟶ diag D j g' where
  app k := pushout.inl g' (D.map k.hom)
  naturality k k' f := by
    show 𝟙 B' ≫ pushout.inl g' (D.map k'.hom) = pushout.inl g' (D.map k.hom) ≫ mapPush D j g' f
    rw [inl_mapPush, Category.id_comp]

noncomputable def toB (c : Cocone D) {B : CommRingCat.{0}} (h : B' ⟶ B) (g : c.pt ⟶ B)
    (sq : g' ≫ h = c.ι.app j ≫ g) : diag D j g' ⟶ (Functor.const _).obj B where
  app k := pushout.desc h (c.ι.app k.right ≫ g) (by rw [sq, ← c.w k.hom, Category.assoc])
  naturality k k' f := by
    show mapPush D j g' f ≫ pushout.desc h (c.ι.app k'.right ≫ g) _ =
      pushout.desc h (c.ι.app k.right ≫ g) _ ≫ 𝟙 B
    apply pushout.hom_ext
    · rw [inl_mapPush_assoc, pushout.inl_desc, pushout.inl_desc_assoc, Category.comp_id]
    · rw [inr_mapPush_assoc, pushout.inr_desc, pushout.inr_desc_assoc, Category.comp_id,
        ← Category.assoc, c.w]

theorem exists_isColimit_pushout_under : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (j : J) (B' B : CommRingCat.{0}) (g' : D.obj j ⟶ B') (h : B' ⟶ B) (g : c.pt ⟶ B), IsPushout g' (c.ι.app j) h g → ∃ (D' : Under j ⥤ CommRingCat.{0}) (ι : D' ⟶ (Functor.const _).obj B) (u : Under.forget j ⋙ D ⟶ D') (v : (Functor.const _).obj B' ⟶ D'), Nonempty (IsColimit (Cocone.mk B ι)) ∧ ∀ k : Under j, IsPushout g' (D.map k.hom) (v.app k) (u.app k) ∧ v.app k ≫ ι.app k = h ∧ u.app k ≫ ι.app k = c.ι.app k.right ≫ g := by
  intro J _ _ D c hc j B' B g' h g hsq
  refine ⟨diag D j g', toB D j g' c h g hsq.w, inrNat D j g', inlNat D j g', ⟨?_⟩,
    fun k => ⟨IsPushout.of_hasPushout _ _, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩⟩
  have hc' : IsColimit (c.whisker (Under.forget j)) :=
    (Functor.Final.isColimitWhiskerEquiv _ _).symm hc
  let k0 : Under j := Under.mk (𝟙 j)

  let e : ∀ (s : Cocone (diag D j g')) (k : Under j), pushout g' (D.map k.hom) ⟶ s.pt :=
    fun s k => s.ι.app k
  have he : ∀ (s : Cocone (diag D j g')) {k k' : Under j} (f : k ⟶ k'),
      mapPush D j g' f ≫ e s k' = e s k := fun s _ _ f => s.w f
  let r : Cocone (diag D j g') → Cocone (Under.forget j ⋙ D) := fun s =>
    { pt := s.pt, ι := inrNat D j g' ≫ s.ι }
  have hl : ∀ (s : Cocone (diag D j g')) (k : Under j),
      pushout.inl g' (D.map k.hom) ≫ e s k = pushout.inl g' (D.map k0.hom) ≫ e s k0 := by
    intro s k
    rw [← he s (Under.homMk k.hom (Category.id_comp k.hom) : k0 ⟶ k), inl_mapPush_assoc]
  have hfr : ∀ (s : Cocone (diag D j g')) (k : Under j),
      c.ι.app k.right ≫ hc'.desc (r s) = pushout.inr g' (D.map k.hom) ≫ e s k :=
    fun s k => hc'.fac (r s) k
  have hw : ∀ s : Cocone (diag D j g'),
      g' ≫ (pushout.inl g' (D.map k0.hom) ≫ e s k0) = c.ι.app j ≫ hc'.desc (r s) := by
    intro s
    rw [show c.ι.app j = c.ι.app k0.right from rfl, hfr, ← Category.assoc, pushout.condition,
      Category.assoc]
    exact (congrArg (· ≫ (pushout.inr g' (D.map k0.hom) ≫ e s k0)) (D.map_id j)).trans
      (Category.id_comp _)
  exact
    { desc := fun s => hsq.desc _ _ (hw s)
      fac := fun s k => by
        change pushout.desc _ _ _ ≫ _ = e s k
        apply pushout.hom_ext
        · rw [pushout.inl_desc_assoc, hsq.inl_desc, hl s k]
        · rw [pushout.inr_desc_assoc, Category.assoc, hsq.inr_desc, hfr]
      uniq := fun s m hm => by
        have hm' : ∀ k : Under j, pushout.desc h (c.ι.app k.right ≫ g)
            (by rw [hsq.w, ← c.w k.hom, Category.assoc]) ≫ m = e s k := hm
        apply hsq.hom_ext
        · rw [hsq.inl_desc, ← hm' k0, pushout.inl_desc_assoc]
        · rw [hsq.inr_desc]
          apply hc'.hom_ext
          intro k
          change c.ι.app k.right ≫ g ≫ m = c.ι.app k.right ≫ hc'.desc (r s)
          rw [hfr, ← hm' k, pushout.inr_desc_assoc, Category.assoc] }

end GlobalTheory.BaseChangeColim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFlipSheafComplexPairing
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

noncomputable section
namespace GlobalTheory.EtC.SwapTransfer

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.SwapTransfer.negOnePow_sq' (n m : ℤ) :
    (n.negOnePow : ℤ) * ((m.negOnePow : ℤ) * (n.negOnePow : ℤ)) = m.negOnePow := by
  rw [mul_left_comm, ← Units.val_mul, Int.units_mul_self, Units.val_one, mul_one]

def flipPair {I J K : Cx R} (μ : Pair I J K) : Pair J I K where
  mul U t s w h := (((s * t).negOnePow : ℤ) • μ.mul U s t w (by omega)).flip
  nat g t s w h b a := by
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, Sec.res, map_zsmul]
    rw [← Sec.res, μ.nat]
  leibniz U t s w h b a := by
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, Sec.map, map_zsmul]
    rw [← Sec.map, μ.leibniz]
    have h1 : (s * (t + 1)).negOnePow = (s * t).negOnePow * s.negOnePow := by
      rw [mul_add, mul_one, Int.negOnePow_add]
    have h2 : ((s + 1) * t).negOnePow = (s * t).negOnePow * t.negOnePow := by
      rw [add_mul, one_mul, Int.negOnePow_add]
    rw [h1, h2]
    simp only [Units.smul_def, smul_add, smul_smul, Units.val_mul]
    rw [negOnePow_sq']
    exact add_comm _ _

def swIdx {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w}) : {p : ℤ × ℤ // p.1 + p.2 = w} :=
  ⟨(p.1.2, p.1.1), by have := p.2; simp only at this ⊢; omega⟩

def swapT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens J I U w := by
  classical
  exact DirectSum.toModule _ _ _ fun p =>
    ((p.1.1 * p.1.2).negOnePow : ℤ) • ((DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (J.X q.1.1) U ⊗[ULift.{1} R] Sec (I.X q.1.2) U) (swIdx p)) ∘ₗ
      (TensorProduct.comm (ULift.{1} R) (Sec (I.X p.1.1) U) (Sec (J.X p.1.2) U)).toLinearMap)

end GlobalTheory.EtC.SwapTransfer

namespace GlobalTheory.EtC

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem flipPair_mul_eq_negOnePow_smul_mul {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    (_root_.GlobalTheory.EtC.SwapTransfer.flipPair μ).mul U t s w (by omega) b a = (s * t).negOnePow • μ.mul U s t w h a b := by
  rw [Units.smul_def]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem koszulSwap_lof_tmul_lemma_5 (I J : _root_.GlobalTheory.EtC.Cx R) (U : Scheme.{0}) {w s t : ℤ} (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    _root_.GlobalTheory.EtC.SwapTransfer.swapT I J U w
        (DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
          ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      (s * t).negOnePow • DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (J.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (I.X q.1.2) U)
          ⟨(t, s), by omega⟩ (b ⊗ₜ a) := by
  unfold _root_.GlobalTheory.EtC.SwapTransfer.swapT
  erw [DirectSum.toModule_lof]
  rw [Units.smul_def]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem lift_lof_tmul {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) (U : Scheme.{0}) {w s t : ℤ} (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    μ.lift U w
        (DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
          ⟨(s, t), h⟩ (a ⊗ₜ b)) = μ.mul U s t w h a b := by
  unfold _root_.GlobalTheory.EtC.Pair.lift
  erw [DirectSum.toModule_lof]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem lift_comp_swapT_eq_flipPair_lift {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) (U : Scheme.{0}) (w : ℤ) :
    μ.lift U w ∘ₗ _root_.GlobalTheory.EtC.SwapTransfer.swapT J I U w =
      (_root_.GlobalTheory.EtC.SwapTransfer.flipPair μ).lift U w := by
  unfold _root_.GlobalTheory.EtC.Tens
  apply DirectSum.linearMap_ext
  rintro ⟨⟨t, s⟩, h⟩
  apply TensorProduct.ext'
  intro b a
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, koszulSwap_lof_tmul_lemma_5, map_zsmul_unit, lift_lof_tmul, lift_lof_tmul, Units.smul_def, mul_comm t s]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem swapT_comp_swapT (I J : _root_.GlobalTheory.EtC.Cx R) (U : Scheme.{0}) (w : ℤ) :
    _root_.GlobalTheory.EtC.SwapTransfer.swapT J I U w ∘ₗ _root_.GlobalTheory.EtC.SwapTransfer.swapT I J U w = LinearMap.id := by
  unfold _root_.GlobalTheory.EtC.Tens
  apply DirectSum.linearMap_ext
  rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.comp_apply, LinearMap.comp_apply, koszulSwap_lof_tmul_lemma_5, map_zsmul_unit, koszulSwap_lof_tmul_lemma_5, smul_smul, mul_comm t s, Int.units_mul_self, one_smul]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem tensorRestrict_lof_tmul_lemma_7 (I J : _root_.GlobalTheory.EtC.Cx R) {V U : Scheme.{0}} (g : V ⟶ U) {w s t : ℤ} (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    _root_.GlobalTheory.EtC.Tens.res g w
        (DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
          ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) V ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) V)
          ⟨(s, t), h⟩ (_root_.GlobalTheory.EtC.Sec.res g a ⊗ₜ _root_.GlobalTheory.EtC.Sec.res g b) := by
  unfold _root_.GlobalTheory.EtC.Tens.res
  erw [DirectSum.lmap_lof]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem res_comp_swapT (I J : _root_.GlobalTheory.EtC.Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    _root_.GlobalTheory.EtC.Tens.res g w ∘ₗ _root_.GlobalTheory.EtC.SwapTransfer.swapT I J U w =
      _root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w ∘ₗ _root_.GlobalTheory.EtC.Tens.res g w := by
  unfold _root_.GlobalTheory.EtC.Tens
  apply DirectSum.linearMap_ext
  rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, koszulSwap_lof_tmul_lemma_5, map_zsmul_unit, tensorRestrict_lof_tmul_lemma_7, tensorRestrict_lof_tmul_lemma_7, koszulSwap_lof_tmul_lemma_5]


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
theorem _root_.GlobalTheory.EtC.Pair.exists_isFlip (R : Type) [CommRing R]
    {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) :
    ∃ ν : _root_.GlobalTheory.EtC.Pair J I K, μ.IsFlip ν ∧ ν.IsFlip μ ∧
      (μ.IsTensor → ν.IsTensor) := by
  refine ⟨_root_.GlobalTheory.EtC.SwapTransfer.flipPair μ, ?_, ?_, ?_⟩
  · intro U s t w h a b
    exact flipPair_mul_eq_negOnePow_smul_mul μ U s t w h a b
  · intro U t s w h b a
    rw [flipPair_mul_eq_negOnePow_smul_mul μ U s t w (by omega) a b, smul_smul, mul_comm t s, Int.units_mul_self, one_smul]
  · rintro ⟨hsurj, hinj⟩
    refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
    · obtain ⟨S, hS, hP⟩ := hsurj U w y
      refine ⟨S, hS, fun V g hg => ?_⟩
      obtain ⟨x, hx⟩ := hP V g hg
      refine ⟨_root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w x, ?_⟩
      rw [← lift_comp_swapT_eq_flipPair_lift, LinearMap.comp_apply, ← LinearMap.comp_apply (_root_.GlobalTheory.EtC.SwapTransfer.swapT J I V w), swapT_comp_swapT, LinearMap.id_apply]
      exact hx
    · have hx' : μ.lift U w (_root_.GlobalTheory.EtC.SwapTransfer.swapT J I U w x) = 0 := by
        rw [← LinearMap.comp_apply, lift_comp_swapT_eq_flipPair_lift]
        exact hx
      obtain ⟨S, hS, hP⟩ := hinj U w _ hx'
      refine ⟨S, hS, fun V g hg => ?_⟩
      have hV := congrArg (_root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w) (hP V g hg)
      rw [← LinearMap.comp_apply (_root_.GlobalTheory.EtC.Tens.res g w), res_comp_swapT, LinearMap.comp_apply,
        ← LinearMap.comp_apply (_root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w), swapT_comp_swapT, LinearMap.id_apply, map_zero] at hV
      exact hV

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsAgreeOfCocycle
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue.Cocycle

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (a : A →+* B) (b : B →+* C) : spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [← Spec.map_comp]; rfl

theorem awayMap_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (r : R) : Function.Surjective (Localization.awayMap π r) := by
  intro y
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (π r)) y
  obtain ⟨b, rfl⟩ := hπ a
  refine ⟨IsLocalization.mk' _ b (⟨r ^ m, m, rfl⟩ : Submonoid.powers r), ?_⟩
  simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk']
  congr 1
  ext
  simp

theorem ker_awayMap_le {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (r : R) :
    RingHom.ker (Localization.awayMap π r) ≤
      (RingHom.ker π).map (algebraMap R (Localization.Away r)) := by
  intro x hx
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers r) x
  rw [RingHom.mem_ker] at hx
  simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk'] at hx
  rw [IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨⟨_, p, rfl⟩, hp⟩ := hx
  rw [IsLocalization.mk'_mem_map_algebraMap_iff]
  refine ⟨r ^ p, ⟨p, rfl⟩, ?_⟩
  rw [RingHom.mem_ker, map_mul, map_pow]
  exact hp

theorem ker_awayMap_sq {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (h2 : RingHom.ker π ^ 2 = ⊥) (r : R) :
    RingHom.ker (Localization.awayMap π r) ^ 2 = ⊥ := by
  refine le_bot_iff.1 ((Ideal.pow_right_mono (ker_awayMap_le π r) 2).trans ?_)
  rw [← Ideal.map_pow, h2, Ideal.map_bot]

theorem isCombIn_restrict_chart {Y : Scheme.{0}} {V V' : Y.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') {S T S' : Type} [CommRing S] [CommRing T] [CommRing S']
    (q : S →+* T) (hq : Function.Surjective q) (h2 : RingHom.ker q ^ 2 = ⊥) (g : S →+* S')
    {ι : Type} [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S)
    (hw : ∀ i, spMap q ≫ w i = spMap q ≫ u) (hC : IsCombIn V u c w a)
    (hu : (spMap g ≫ u) ⁻¹ᵁ V' = ⊤) :
    IsCombIn V' (spMap g ≫ u) (spMap g ≫ c) (fun i => spMap g ≫ w i) (fun i => g (a i)) := by
  let J : Ideal S' := (RingHom.ker q).map g
  have hle : RingHom.ker q ≤ RingHom.ker ((Ideal.Quotient.mk J).comp g) := by
    intro x hx
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem g hx
  let g' : T →+* S' ⧸ J := RingHom.liftOfSurjective q hq ⟨(Ideal.Quotient.mk J).comp g, hle⟩
  have hg' : g'.comp q = (Ideal.Quotient.mk J).comp g := RingHom.liftOfSurjective_comp q hq _
  refine _root_.GlobalTheory.SecGlue.isCombIn_of_chart Y V V' hV hV' S' (S' ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    ?_ ι _ _ _ _ (fun i => ?_) (isCombIn_spMap_comp Y V S S' g ι u c w a hC) hu
  · rw [Ideal.mk_ker, ← Ideal.map_pow, h2, Ideal.map_bot]
  · rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, ← hg', ← spMap_comp_spMap,
      Category.assoc, Category.assoc, hw i]

theorem eq_of_cocycle {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) {S : Type} [CommRing S]
    {κ : Type} [Fintype κ] (u u' c c' : Sp S ⟶ Y) (w w' : κ → (Sp S ⟶ Y)) (a b : κ → S)
    (hab : ∑ k, a k * b k = 1) (h : IsCombIn W u c w a) (h' : IsCombIn W u' c' w' a)
    (hco : ∀ k, IsCombIn W u' (w k) ![w' k, u] ![1, 1 - b k]) : c = c' := by
  obtain ⟨hu, hc, hw, e⟩ := h
  obtain ⟨hu', hc', hw', e'⟩ := h'
  refine eq_of_chartHom_eq hW c c' hc hc' fun x => ?_
  have key : ∀ k, chartHom W (w k) (hw k) x - chartHom W u hu x =
      (chartHom W (w' k) (hw' k) x - chartHom W u' hu' x) -
        b k * (chartHom W u hu x - chartHom W u' hu' x) := by
    intro k
    obtain ⟨_, _, _, e''⟩ := hco k
    have := e'' x
    rw [Fin.sum_univ_two] at this
    have this' : chartHom W (w k) (hw k) x = chartHom W u' hu' x +
        (1 * (chartHom W (w' k) (hw' k) x - chartHom W u' hu' x) +
          (1 - b k) * (chartHom W u hu x - chartHom W u' hu' x)) := this
    rw [this']; ring
  rw [e x, e' x]
  simp only [key, mul_sub (a _) (_ - _), Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, hab]
  ring

theorem exists_lifts_agree_of_cocycle : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Fintype κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ (V : κ → X.left.Opens), (∀ k, IsAffineOpen (V k)) →
    ∀ (e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left),
    (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) →
    (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) →
    (∀ k, e k ⁻¹ᵁ V k = ⊤) →
    ∀ (N : ℕ) (t : κ → ∀ j, Sp (Localization.Away (f j)) ⟶ X.left),
    (∀ k j, t k j ≫ X.hom = spMap (algebraMap R (Localization.Away (f j)))) →
    (∀ k j, spMap (Localization.awayMap π (f j)) ≫ t k j = spMap (algebraMap R₀ (Localization.Away (π (f j)))) ≫ g₀) →
    (∀ k j, t k j ⁻¹ᵁ V j = ⊤) →
    ∀ (n : κ → κ → ℕ) (s : ∀ j l, Fin (n j l) → Localization.Away (f j * f l)) (W : ∀ j l, Fin (n j l) → X.left.Opens),
    (∀ j l, Ideal.span (Set.range (s j l)) = ⊤) → (∀ j l i, IsAffineOpen (W j l i)) →
    (∀ j l i, (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j) ⁻¹ᵁ W j l i = ⊤) →
    (∀ j l k i, GlobalTheory.SecGlue.IsCombIn (W j l i) (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ e l)
        (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ t k j)
        ![spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ t k l, spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j]
        ![1, 1 - algebraMap R (Localization.Away (s j l i)) (f k) ^ (N)]) →
    ∃ e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left,
      (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) ∧
      (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) ∧
      ∀ j k, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j =
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k := by
  intro R R₀ _ _ π hπ h2 X g₀ hg₀ κ _ f hf V hV e he he₀ heV N t ht ht₀ htV n s W hs hW heW hco
  have hpow : Ideal.span (Set.range fun k => f k ^ N) = ⊤ := by
    have := Ideal.span_pow_eq_top _ hf N
    rwa [← Set.range_comp] at this
  obtain ⟨a, ha⟩ : ∃ a : κ → R, ∑ k, a k * f k ^ N = 1 :=
    Ideal.mem_span_range_iff_exists_fun.1 (hpow ▸ Submodule.mem_top)
  have hte : ∀ j k, spMap (Localization.awayMap π (f j)) ≫ t k j =
      spMap (Localization.awayMap π (f j)) ≫ e j := fun j k => (ht₀ k j).trans (he₀ j).symm
  choose c hc hc₀ hcp using fun j => _root_.GlobalTheory.SecGlue.CombEx.exists_comb X.left (V j) (hV j) _ _
    (Localization.awayMap π (f j)) (awayMap_surjective π hπ _) (ker_awayMap_sq π h2 _) κ (e j)
    (fun k => t k j) (fun k => algebraMap R _ (a k)) (heV j) (hte j)
  refine ⟨c, fun j => (hcp j R X.hom fun k => (ht k j).trans (he j).symm).trans (he j),
    fun j => (hc₀ j).trans (he₀ j), fun j l => ?_⟩
  refine hom_ext_of_span_eq_top _ _ (s j l) (hs j l) _ _ _ fun i => ?_
  obtain ⟨hlW, -⟩ := hco j l j i
  have hjW := heW j l i
  rw [← Category.assoc, spMap_comp_spMap] at hlW hjW
  have h₁ := isCombIn_restrict_chart (hV j) (hW j l i) _ (awayMap_surjective π hπ _)
    (ker_awayMap_sq π h2 _) _ _ _ _ _ (hte j) (hc j) hjW
  have h₂ := isCombIn_restrict_chart (hV l) (hW j l i) _ (awayMap_surjective π hπ _)
    (ker_awayMap_sq π h2 _) _ _ _ _ _ (hte l) (hc l) hlW
  simp only [RingHom.comp_apply, IsLocalization.Away.awayToAwayRight_eq,
    IsLocalization.Away.awayToAwayLeft_eq, ← IsScalarTower.algebraMap_apply,
    ← spMap_comp_spMap, Category.assoc] at h₁ h₂
  refine eq_of_cocycle (hW j l i) _ _ _ _ _ _ _
    (fun k => algebraMap R (Localization.Away (s j l i)) (f k) ^ N) ?_ h₁ h₂ fun k => hco j l k i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_pow, ← map_mul, ← map_sum, ha, map_one]

end GlobalTheory.SecGlue.Cocycle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPowFibreRankEqPDivGroup
section
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PDivGroup

theorem exists_mulPow_fibreRank_eq (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    (G : _root_.GlobalTheory.PDivGroup p O) (k m : ℕ) :
    ∃ (r : G.A (k + m) →ₐc[O] G.A k) (μ : G.A k →ₐc[O] G.A (k + m)), Function.Surjective r ∧
      RingHom.ker r = torsionIdeal (R := O) (A := G.A (k + m)) (p ^ k) ∧
      (∀ a, μ (r a) = mulBy (R := O) (A := G.A (k + m)) (p ^ m) a) ∧
      ∀ q, fibreRank (μ : G.A k →ₐ[O] G.A (k + m)).toLinearMap q = fibreDim (G.A k) q := by
  obtain ⟨r, hr, hk⟩ := G.exists_res_le (m := k) (n := k + m) (by omega)
  have hle : RingHom.ker r ≤ RingHom.ker (mulBy (R := O) (A := G.A (k + m)) (p ^ m)) := by
    rw [hk]
    refine (kerIdeal_le_ker_iff _
      (mulBy (R := O) (A := G.A (k + m)) (p ^ m) : G.A (k + m) →ₐ[O] G.A (k + m))).2 fun c => ?_
    change mulBy (R := O) (A := G.A (k + m)) (p ^ m)
      (mulBy (R := O) (A := G.A (k + m)) (p ^ k) c) = _
    rw [mulBy_mulBy, ← pow_add, add_comm m k, mulBy_pow_self]
  let μ := liftSurj r hr (mulBy (R := O) (A := G.A (k + m)) (p ^ m)) hle
  have hμ : ∀ a, μ (r a) = mulBy (R := O) (A := G.A (k + m)) (p ^ m) a :=
    liftSurj_apply r hr _ hle
  refine ⟨r, μ, hr, hk, hμ, fun q => ?_⟩
  obtain ⟨f, hf, hfk⟩ := G.exists_res_le (m := m) (n := k + m) (by omega)
  have hker : kerIdeal μ = RingHom.ker (f : G.A (k + m) →ₐ[O] G.A m) := by
    rw [← kerIdeal_comp_of_surjective μ hr, show μ.comp r =
      mulBy (R := O) (A := G.A (k + m)) (p ^ m) from BialgHom.ext hμ]
    exact hfk.symm
  have h1 := fibreDim_eq_ker_mul_range μ q
  rw [hker, fibreDim_congr (Ideal.quotientKerAlgEquivOfSurjective
    (f := (f : G.A (k + m) →ₐ[O] G.A m)) hf).toLinearEquiv, fibreDim_eq, fibreDim_eq,
    add_mul, pow_add, mul_comm (p ^ (k * G.height))] at h1
  rw [fibreDim_eq]
  have hp : 0 < p ^ (m * G.height) := pow_pos (Fact.out : p.Prime).pos _
  exact (Nat.eq_of_mul_eq_mul_left hp h1).symm

end GlobalTheory.PDivGroup
end
end

