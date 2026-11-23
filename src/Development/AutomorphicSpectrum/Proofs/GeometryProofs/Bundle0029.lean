module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharacterSectionMultiplicative
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingIsoFinite
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.FiniteIso

open GlobalTheory.CompanionTheory.Ar.BT.SubOrder

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem isFinOpenSub_top (Γ : QFGroup R T) (hfin : IsFinite Γ.G.hom) : Γ.IsFinOpenSub ⊤ := by
  constructor
  · have := hfin
    have hi : IsIso (⊤ : Γ.G.left.Opens).ι := (Scheme.topIso Γ.G.left).isIso_hom
    infer_instance
  all_goals simp

noncomputable def secMap {X : Scheme.{0}} {A : Type} [CommRing A] (j : X ⟶ Spec (CommRingCat.of A)) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop).hom

theorem val_secMap (Γ : QFGroup R T) {A : Subalgebra R (T → R)} {j : Γ.G.left ⟶ Spec (CommRingCat.of A)}
    (hj : Γ.IsEmb A j) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ (⊤ : Γ.G.left.Opens)) (a : A) :
    valAt (Γ.pt t).left ⊤ h (secMap j a) = algebraMap R (FractionRing R) ((a : T → R) t) := by
  have e0 : j.appLE ⊤ ⊤ (by simp) = j.appTop := Scheme.Hom.appLE_eq_app _
  have h2 : ⊤ ≤ ((Γ.pt t).left ≫ j) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens) := by simp
  have h3 : ⊤ ≤ (Spec.map (CommRingCat.ofHom
    ((algebraMap R (FractionRing R)).comp ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom)))) ⁻¹ᵁ
      (⊤ : (Spec (CommRingCat.of A)).Opens) := by simp
  have e1 := valHom_appLE (Γ.pt t).left j (V := ⊤) (W := ⊤) (by simp) h h2
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
  rw [e0, valHom_congr (hj.pt t) _ h2 h3, valHom_spec_top] at e1
  exact e1

theorem isIso_of_secMap_bijective {X : Scheme.{0}} [IsAffine X] {A : Type} [CommRing A]
    (j : X ⟶ Spec (CommRingCat.of A)) (hb : Function.Bijective (secMap j)) : IsIso j := by
  have h1 : IsIso ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  have h2 : IsIso j.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of A)).inv j.appTop
  have e := Scheme.isoSpec_hom_naturality j
  have h3 : IsIso (j ≫ (Spec (CommRingCat.of A)).isoSpec.hom) := by
    rw [← e]; infer_instance
  exact IsIso.of_isIso_comp_right j (Spec (CommRingCat.of A)).isoSpec.hom

end GlobalTheory.CompanionTheory.Ar.BT.FiniteIso

namespace GlobalTheory.CompanionTheory.Ar.BT.FiniteIso

open GlobalTheory.CompanionTheory.Ar.BT.SubOrder

theorem isIso_of_finite : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsFinite Γ.G.hom → IsIso j := by
  intro R _ _ _ T _ _ Γ j hj hfin
  have hF := isFinOpenSub_top Γ hfin
  have hU := isAffineOpen_of_fin Γ hF
  have : IsAffine Γ.G.left := by
    have := hfin
    exact isAffine_of_isAffineHom Γ.G.hom
  obtain ⟨H, A', hH, hopf, hA'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.SubOrder.hopfOrder_of_finOpenSub R T Γ ⊤ hF
  have htop : ∀ t, ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ (⊤ : Γ.G.left.Opens) := fun t => by simp
  have hHt : ∀ t, t ∈ H := fun t => (hH t).2 (htop t)
  have inj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  letI : Algebra R Γ(Γ.G.left, ⊤) := (secRho Γ hU).toAlgebra
  have hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, ⊤))) :=
    fromSpec_hom Γ hU
  have hfinite := sec_finite hρ hF
  have hval : ∀ (s : Γ(Γ.G.left, ⊤)) (t : T),
      ∃ r : R, algebraMap R (FractionRing R) r = valAt (Γ.pt t).left ⊤ (htop t) s := by
    intro s t
    have h1 : IsIntegral R s := Algebra.IsIntegral.isIntegral s
    exact IsIntegrallyClosed.isIntegral_iff.1 (h1.map (valAlg hρ t (htop t)))
  apply isIso_of_secMap_bijective
  constructor
  · intro a b hab
    apply Subtype.ext
    funext t
    apply inj
    rw [← val_secMap Γ hj t (htop t) a, ← val_secMap Γ hj t (htop t) b, hab]
  · intro s
    choose f hf using hval s
    let f' : H → R := fun h => f h
    have hf' : f' ∈ A' := (hA' f').2 ⟨s, fun t h => (hf t).symm⟩
    have hind : f' ∈ indOrder (MonoidHom.id H) A' := by
      rw [_root_.GlobalTheory.CompanionTheory.Ar.BT.indOrder_id_eq_of_isHopfOrder R H A' hopf]
      exact hf'
    have hmem : f ∈ Γ.btOrder ⊤ := by
      apply Algebra.subset_adjoin
      intro t g _
      obtain ⟨s', hs'⟩ := (hA' _).1 (hind ⟨t, hHt t⟩)
      exact ⟨⊤, trivial, s', fun u h => hs' ⟨u, hHt u⟩ h⟩
    refine ⟨⟨f, hmem⟩, ?_⟩
    rw [← sub_eq_zero]
    apply _root_.GlobalTheory.CompanionTheory.Ar.BT.section_eq_zero_of_val_generic R T Γ ⊤
    intro t h
    rw [← valHom_apply, map_sub, valHom_apply, valHom_apply, val_secMap Γ hj, hf, sub_self]

end GlobalTheory.CompanionTheory.Ar.BT.FiniteIso
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqOfLe
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem QFGroup.btSet_eq_of_le (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens)
    (hU : Γ.IsFinOpenSub U) (hU' : Γ.IsFinOpenSub U') (hle : U' ≤ U) :
    Γ.btSet U = Γ.btSet U' := by
  apply Set.Subset.antisymm
  · intro f hf t g hg
    exact hf t g (hle hg)
  · intro f hf s g hg
    have hcover := Transl.translates_cover R T Γ U U' hU hU' hle g hg
    obtain ⟨σ, t, hσ, hmem⟩ := hcover
    have hreg := hf (s * t⁻¹) _ hmem
    have key := QFGroup.regularAt_translate R T Γ σ t hσ
      (fun h => algebraMap R (FractionRing R) (f (s * t⁻¹ * h))) g hreg
    have heq : (fun h => algebraMap R (FractionRing R) (f (s * t⁻¹ * (t * h)))) =
        fun h => algebraMap R (FractionRing R) (f (s * h)) := by
      funext h
      congr 2
      rw [_root_.mul_assoc, inv_mul_cancel_left]
    simpa only [heq] using key

theorem QFGroup.btOrder_eq_of_le : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.IsFinOpenSub U' → U' ≤ U → Γ.btOrder U = Γ.btOrder U' := by
  intro R _ _ _ T _ _ Γ U U' hU hU' hle
  unfold QFGroup.btOrder
  rw [QFGroup.btSet_eq_of_le R T Γ U U' hU hU' hle]

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharacterSectionTangentFunctional
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.HTLinear

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem valAt_top {B : Type} [CommRing B] {X : Scheme.{0}} (v : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt v ⊤ le_top s = (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (v.appTop.hom s) := by
  rfl

theorem valAt_spec_comp {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (φ : B →+* C)
    (v : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom φ) ≫ v) ⊤ le_top s = φ (valAt v ⊤ le_top s) := by
  rw [valAt_top, valAt_top, Scheme.Hom.comp_appTop]
  exact congrArg (fun f => f.hom (v.appTop.hom s)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

theorem valAt_mul [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {B : Type} [CommRing B]
    (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (y z : Over.mk q ⟶ Γ.G) :
    valAt (B := B) (y * z).left ⊤ le_top s =
      valAt (B := B) y.left ⊤ le_top s * valAt (B := B) z.left ⊤ le_top s := by
  have h := (_root_.GlobalTheory.CompanionTheory.Ar.BT.charValues_mul R T Γ χ s hs (Over.mk q)).1 y z
  rw [valAt_top, valAt_top, valAt_top, ← map_mul]
  exact congrArg _ h

theorem valAt_one [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {B : Type} [CommRing B]
    (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) :
    valAt (B := B) (1 : Over.mk q ⟶ Γ.G).left ⊤ le_top s = 1 := by
  have h := (_root_.GlobalTheory.CompanionTheory.Ar.BT.charValues_mul R T Γ χ s hs (Over.mk q)).2
  rw [valAt_top]
  refine (congrArg _ h).trans ?_
  exact map_one _

theorem tors_one {Γ : QFGroup R T} {S : Scheme.{0}} {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left} (h : Γ.IsTorsionAlong G x N i)
    (Y : Over (Spec (CommRingCat.of R))) :
    (1 : Y ⟶ Γ.G).left ≫ i = (1 : Over.mk (Y.hom ≫ x) ⟶ G).left := by
  let y₀ : Over.mk (Y.hom ≫ x) ⟶ G := Over.homMk ((1 : Y ⟶ Γ.G).left ≫ i) (by
    show ((1 : Y ⟶ Γ.G).left ≫ i) ≫ G.hom = Y.hom ≫ x
    rw [Category.assoc, h.isOver, ← Category.assoc, Over.w])
  have h1 := h.mul Y 1 1 y₀ y₀ rfl rfl
  rw [_root_.mul_one] at h1
  have h2 : y₀ * y₀ = y₀ * 1 := by
    rw [_root_.mul_one]
    exact Over.OverMorphism.ext h1
  have h3 : y₀ = 1 := mul_left_cancel h2
  exact congrArg (fun f => f.left) h3

section Tangent

variable {A : Type} [CommRing A] (π : R →+* A)

abbrev qMap : Spec (CommRingCat.of (DualNumber A)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom ((algebraMap A (DualNumber A)).comp π))

abbrev dMap : Spec (CommRingCat.of (DualNumber A)) ⟶ Spec (CommRingCat.of (DualNumber R)) :=
  Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap π))

theorem dMap_over : dMap π ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = qMap π := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_epsMul (c : R) :
    (epsMul (π c)).comp (GlobalTheory.CompanionTheory.Ar.dualMap π) = (GlobalTheory.CompanionTheory.Ar.dualMap π).comp (epsMul c) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, epsMul, mul_comm]

theorem epsMul_algebraMap (c : A) : (epsMul c).comp (algebraMap A (DualNumber A)) = algebraMap A (DualNumber A) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_dualMap : ((TrivSqZeroExt.fstHom A A A).toRingHom).comp (GlobalTheory.CompanionTheory.Ar.dualMap π) =
    π.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [GlobalTheory.CompanionTheory.Ar.dualMap]

theorem fst_q : ((TrivSqZeroExt.fstHom A A A).toRingHom).comp ((algebraMap A (DualNumber A)).comp π) = π := by
  refine RingHom.ext fun a => ?_
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
  {L : Type} [AddCommGroup L] [Module R L]

def IsTan (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left) (M : LieModel G x L) (e : L)
    (v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left) : Prop :=
  v ≫ Γ.G.hom = qMap π ∧ v ≫ i = dMap π ≫ (M.pt e).left

variable {π} {N : ℕ} {Γ : QFGroup R T} {i : Γ.G.left ⟶ G.left} {M : LieModel G x L}

theorem fst_valAt [Finite T] (h : Γ.IsTorsionAlong G x N i) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {e : L}
    {v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left} (hv : IsTan π Γ i M e v) :
    (valAt v ⊤ le_top s).fst = 1 := by
  let r : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom π)
  let p : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (DualNumber A)) :=
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom)
  have hpq : p ≫ qMap π = r := by
    simp only [p, r, qMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fst_q]
  let y : Over.mk r ⟶ Γ.G := Over.homMk (p ≫ v) (by
    show (p ≫ v) ≫ Γ.G.hom = r
    rw [Category.assoc, hv.1, hpq])
  have hy : y = 1 := by
    apply h.inj (Over.mk r)
    rw [tors_one h]
    have hp : p ≫ dMap π = r ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
      simp only [p, r, dMap]
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, fst_dualMap]
    let w : Over.mk (r ≫ x) ⟶ Over.mk x := Over.homMk r rfl
    have h1 : (w ≫ (1 : Over.mk x ⟶ G)).left = r ≫ (1 : Over.mk x ⟶ G).left := rfl
    rw [comp_one] at h1
    show (p ≫ v) ≫ i = (1 : Over.mk (r ≫ x) ⟶ G).left
    rw [h1, Category.assoc, hv.2, ← Category.assoc, hp, Category.assoc]
    exact congrArg (r ≫ ·) (M.tan e)
  have h2 : valAt (p ≫ v) ⊤ le_top s = 1 := by
    have h3 := valAt_one Γ χ s hs r
    rw [← hy] at h3
    exact h3
  have h4 := valAt_spec_comp (TrivSqZeroExt.fstHom A A A).toRingHom v s
  exact h4.symm.trans h2

theorem isTan_add [Finite T] (h : Γ.IsTorsionAlong G x N i) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {e e' : L}
    {v v' : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left} (hv : IsTan π Γ i M e v)
    (hv' : IsTan π Γ i M e' v') :
    ∃ w, IsTan π Γ i M (e + e') w ∧ valAt w ⊤ le_top s = valAt v ⊤ le_top s * valAt v' ⊤ le_top s := by
  let y : Over.mk (qMap π) ⟶ Γ.G := Over.homMk v hv.1
  let z : Over.mk (qMap π) ⟶ Γ.G := Over.homMk v' hv'.1
  let ρ : Over.mk (qMap π ≫ x) ⟶ epsAt x := Over.homMk (dMap π) (by
    show dMap π ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x = qMap π ≫ x
    rw [← Category.assoc, dMap_over])
  have hm := h.mul (Over.mk (qMap π)) y z (ρ ≫ M.pt e) (ρ ≫ M.pt e') hv.2.symm hv'.2.symm
  rw [← comp_mul, ← M.add] at hm
  exact ⟨(y * z).left, ⟨Over.w (y * z), hm.symm⟩, valAt_mul Γ χ s hs (qMap π) y z⟩

theorem isTan_smul (c : R) {e : L} {v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left}
    (hv : IsTan π Γ i M e v) :
    IsTan π Γ i M (c • e) (Spec.map (CommRingCat.ofHom (epsMul (π c))) ≫ v) := by
  constructor
  · rw [Category.assoc, hv.1, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, epsMul_algebraMap]
  · rw [Category.assoc, hv.2, M.smul, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, dualMap_epsMul]

end Tangent

theorem snd_epsMul {A : Type} [CommRing A] (c : A) (a : DualNumber A) :
    (epsMul c a).snd = c * a.snd := by
  simp [epsMul]

theorem char_on_tangent_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) → ∃ l : L →ₗ[R] (R ⧸ Ideal.span {(N : R)}), ∀ (e : L) (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧ v ≫ i = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left → valAt v ⊤ le_top s = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (l e) := by
  intro R _ _ T _ _ Γ S G _ _ x N i h L _ _ M χ s hs
  have hex : ∀ e : L, ∃ v, IsTan (Ideal.Quotient.mk (Ideal.span {(N : R)})) Γ i M e v ∧
      ∀ w, IsTan (Ideal.Quotient.mk (Ideal.span {(N : R)})) Γ i M e w → w = v :=
    fun e => _root_.GlobalTheory.CompanionTheory.Ar.BT.TanLift.tangent_mod_torsion R T Γ S G x N i h L M e
  choose v hv hu using hex
  have hfst : ∀ e, (valAt (v e) ⊤ le_top s).fst = 1 := fun e => fst_valAt h χ s hs (hv e)
  refine ⟨{ toFun := fun e => (valAt (v e) ⊤ le_top s).snd, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro e e'
    obtain ⟨w, hw, hval⟩ := isTan_add h χ s hs (hv e) (hv e')
    rw [← hu _ w hw, hval, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [add_comm]
  · intro c e
    have h1 := hu _ _ (isTan_smul c (hv e))
    rw [← h1, valAt_spec_comp, snd_epsMul]
    simp [Algebra.smul_def]
  · intro e w hw
    rw [hu e w hw]
    ext
    · simp [hfst]
    · simp

end GlobalTheory.CompanionTheory.Ar.BT.HTLinear
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointConjugate
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

theorem evC_conj {K : Type} {ι : K → Type} (z : (Σ k, ι k) → ℂ) (g : MRing ι) :
    evC (fun p => (starRingEnd ℂ) (z p)) g = (starRingEnd ℂ) (evC z g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [evC]
  | add p q hp hq =>
    simp only [evC, Polynomial.map_add (f := _), map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [evC, map_mul, map_X, eval_X] at hp ⊢
    rw [hp]

theorem ptOver_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type)
    [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) (z : (Σ k, ι k) → ℂ),
    PtOver y φ σ z → PtOver y φ (ComplexEmbedding.conjugate σ) (fun p => (starRingEnd ℂ) (z p)) := by
  intro K _ ι _ Ω _ F _ _ y φ σ z h
  obtain ⟨⟨hne, hvan⟩, hrel⟩ := h
  refine ⟨⟨fun k => ?_, fun f hf => ?_⟩, fun a d g h' hg hh e => ?_⟩
  · obtain ⟨i, hi⟩ := hne k
    exact ⟨i, by simpa using hi⟩
  · have := evC_conj z f
    have h0 : evC z f = 0 := hvan f hf
    rw [h0, map_zero] at this
    exact this
  · rw [evC_conj, evC_conj, hrel a d g h' hg hh e, map_mul, ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCechNerveDiagonalIsoZeroOverBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FlagDet

theorem alt_triangular {Ω E W : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [AddCommGroup W] [Module Ω W] {s : ℕ}
    (f : E [⋀^Fin s]→ₗ[Ω] W) (v w : Fin s → E) (c : Fin s → Ω)
    (h : ∀ i, v i - c i • w i ∈ Submodule.span Ω (w '' {k | k < i})) :
    f v = (∏ i, c i) • f w := by
  classical
  have key : ∀ j : ℕ, f v = f (fun i => if (i : ℕ) < j then c i • w i else v i) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [ih]
      by_cases hj : j < s
      · obtain ⟨i, rfl⟩ : ∃ i : Fin s, (i : ℕ) = j := ⟨⟨j, hj⟩, rfl⟩
        have hnew : (fun k : Fin s => if (k : ℕ) < i + 1 then c k • w k else v k) =
            Function.update (fun k : Fin s => if (k : ℕ) < i then c k • w k else v k) i (c i • w i) := by
          funext k
          by_cases hk : k = i
          · rw [hk, Function.update_self, if_pos (Nat.lt_succ_self _)]
          · rw [Function.update_of_ne hk]
            have hk' : (k : ℕ) ≠ i := fun h => hk (Fin.ext h)
            by_cases hki : (k : ℕ) < i
            · rw [if_pos hki, if_pos (show (k : ℕ) < i + 1 by omega)]
            · rw [if_neg hki, if_neg (show ¬ ((k : ℕ) < i + 1) by omega)]
        rw [hnew]
        generalize hm : (fun k : Fin s => if (k : ℕ) < i then c k • w k else v k) = m
        have hmi : m i = v i := by
          rw [← hm]
          simp
        have hmk : ∀ k : Fin s, k < i → m k = c k • w k := by
          intro k hk
          rw [← hm]
          simp [Fin.lt_def.1 hk]
        have hzero : ∀ u ∈ Submodule.span Ω (w '' {k | k < i}), f (Function.update m i u) = 0 := by
          intro u hu
          induction hu using Submodule.span_induction with
          | mem x hx =>
            obtain ⟨k, hk, rfl⟩ := hx
            have hki : k ≠ i := ne_of_lt hk
            have hmk' : Function.update m i (w k) k = c k • w k := by
              rw [Function.update_of_ne hki]
              exact hmk k hk
            rw [← Function.update_eq_self k (Function.update m i (w k)), hmk', f.map_update_smul]
            rw [f.map_eq_zero_of_eq _ (i := k) (j := i)
              (by rw [Function.update_self, Function.update_of_ne hki.symm, Function.update_self]) hki,
              smul_zero]
          | zero => exact f.map_coord_zero i (by simp)
          | add x y _ _ hx hy => rw [f.map_update_add, hx, hy, add_zero]
          | smul a x _ hx => rw [f.map_update_smul, hx, smul_zero]
        have hv : v i = c i • w i + (v i - c i • w i) := by abel
        conv_lhs => rw [← Function.update_eq_self i m, hmi, hv, f.map_update_add]
        rw [hzero _ (h i), add_zero]
      · congr 1
        funext k
        have := k.2
        simp [show (k : ℕ) < j by omega, show (k : ℕ) < j + 1 by omega]
  rw [key s]
  have hfun : (fun i : Fin s => if (i : ℕ) < s then c i • w i else v i) = fun i => c i • w i := by
    funext i
    rw [if_pos i.2]
  rw [hfun]
  exact f.toMultilinearMap.map_smul_univ c w

theorem exists_diag {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ} {b b₀ : Fin r → E}
    (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) :
    ∃ c : Ω, b i - c • b₀ i ∈ flagStep Ω b₀ i := by
  have hb : b i ∈ flagStep Ω b₀ ((i : ℕ) + 1) := by
    rw [← hF]
    exact Submodule.subset_span ⟨i, show (i : ℕ) < (i : ℕ) + 1 by omega, rfl⟩
  have hset : b₀ '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1} = b₀ '' {k | (k : ℕ) < i} ∪ {b₀ i} := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      by_cases h : (k : ℕ) < i
      · exact Or.inl ⟨k, h, rfl⟩
      · right
        have hk' : (k : ℕ) < (i : ℕ) + 1 := hk
        have : k = i := Fin.ext (by omega)
        rw [this, Set.mem_singleton_iff]
    · rintro (⟨k, hk, rfl⟩ | hx)
      · exact ⟨k, show (k : ℕ) < (i : ℕ) + 1 by have : (k : ℕ) < i := hk; omega, rfl⟩
      · rw [Set.mem_singleton_iff] at hx
        exact ⟨i, show (i : ℕ) < (i : ℕ) + 1 by omega, hx.symm⟩
  unfold flagStep at hb ⊢
  rw [hset, Submodule.span_union, Submodule.mem_sup] at hb
  obtain ⟨y, hy, z, hz, hyz⟩ := hb
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
  exact ⟨c, by rw [← hyz, add_sub_cancel_right]; exact hy⟩

end GlobalTheory.CompanionTheory.Ar.FlagDet
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagCoefficientRatioIntegralStatement
section
open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_coefficient_ratio_integral : ∀ (Ω : Type) [Field Ω] (Li : Type) [AddCommGroup Li] [Module Ω Li] (W : Subring Ω) (r : ℕ) (b₀ b b' : Fin r → Li) (N : Ω) (k : Fin r) (t t' : Ω), LinearIndependent Ω b → (∀ j, flagStep Ω b j = flagStep Ω b₀ j) → (∀ j, flagStep Ω b' j = flagStep Ω b₀ j) → (∀ j, N • b' j ∈ Submodule.span W (Set.range b)) → b k - t • b₀ k ∈ flagStep Ω b₀ k → b' k - t' • b₀ k ∈ flagStep Ω b₀ k → N * (t' / t) ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.leadCoef_ratio_mem | exact GlobalTheory.CompanionTheory.Ar.leadCoef_ratio_mem | (intros; apply GlobalTheory.CompanionTheory.Ar.leadCoef_ratio_mem <;> assumption)
end

