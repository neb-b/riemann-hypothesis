module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExtOfForallQuotient
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiRigid

open SplitTorus

section Affine

variable {S : Scheme.{0}}

variable {R : CommRingCat.{0}} (X : Type) [AddCommGroup X] (t : Spec R ⟶ S)

variable [Module.Free ℤ X] [Module.Finite ℤ X] [IsDomain R]

end Affine

section Field

variable {K : Type} [Field K]

end Field

section Descent

variable {S : Scheme.{0}}

theorem exists_desc {G B Y : Over S} (p : G ⟶ B) [Flat p.left] [Surjective p.left]
    [QuasiCompact p.left] (f : G ⟶ Y)
    (H : ∀ (Z : Over S) (a b : Z ⟶ G), a ≫ p = b ≫ p → a ≫ f = b ≫ f) : ∃ g, p ≫ g = f := by
  have H' : ∀ {Z : Scheme.{0}} (a b : Z ⟶ G.left), a ≫ p.left = b ≫ p.left →
      a ≫ f.left = b ≫ f.left := fun {Z} a b h ↦
    congrArg (·.left) (H (Over.mk (a ≫ G.hom)) (Over.homMk a rfl) (Over.homMk b (by
      change b ≫ G.hom = a ≫ G.hom
      rw [← Over.w p, reassoc_of% h])) (Over.OverMorphism.ext h))
  have e := EffectiveEpi.fac p.left f.left H'
  refine ⟨Over.homMk (EffectiveEpi.desc p.left f.left H') ?_, Over.OverMorphism.ext e⟩
  rw [← cancel_epi p.left, reassoc_of% e, Over.w, Over.w]

theorem epi_of_fpqc {G B : Over S} (p : G ⟶ B) [Flat p.left] [Surjective p.left]
    [QuasiCompact p.left] : Epi p := Over.epi_of_epi_left p

theorem isPullback_whiskerRight {G B : Over S} (p : G ⟶ B) (W : Over S) :
    IsPullback (fst G W).left (p ▷ W).left p.left (fst B W).left := by
  refine IsPullback.of_bot ?_ (congrArg (·.left) (whiskerRight_fst p W).symm)
    (IsPullback.of_hasPullback B.hom W.hom)
  rw [show (p ▷ W).left ≫ pullback.snd B.hom W.hom = (snd G W).left from
    congrArg (·.left) (whiskerRight_snd p W), Over.w]
  exact IsPullback.of_hasPullback G.hom W.hom

instance {G B : Over S} (p : G ⟶ B) (W : Over S) [Flat p.left] : Flat (p ▷ W).left :=
  MorphismProperty.of_isPullback (isPullback_whiskerRight p W) ‹_›

instance {G B : Over S} (p : G ⟶ B) (W : Over S) [Surjective p.left] : Surjective (p ▷ W).left :=
  MorphismProperty.of_isPullback (isPullback_whiskerRight p W) ‹_›

instance {G B : Over S} (p : G ⟶ B) (W : Over S) [QuasiCompact p.left] :
    QuasiCompact (p ▷ W).left :=
  MorphismProperty.of_isPullback (isPullback_whiskerRight p W) ‹_›

theorem exists_eq_mul {T G B Z : Over S} [GrpObj G] [GrpObj B] {i : T ⟶ G} {q : G ⟶ B}
    [IsMonHom q] (hk : IsPullback i (toUnit _) q η[B]) {a b : Z ⟶ G} (h : a ≫ q = b ≫ q) :
    ∃ τ : Z ⟶ T, a = (τ ≫ i) * b :=
  ⟨hk.lift (a * b⁻¹) (toUnit _) (by
    rw [MonObj.mul_comp, GrpObj.inv_comp, h, mul_inv_cancel]; rfl),
    by rw [hk.lift_fst, inv_mul_cancel_right]⟩

theorem globalFns : Out.GlobalFnsSt :=
  GlobalFunctions.globalFns_of (fun _ _ f _ _ ↦ geometricallyIntegral_of_smooth f)
    FlatFibreInjective.injective_baseChange exists_noetherian_model_of_smooth

end Descent

section Main

variable {K : Type} [Field K]

theorem torus_const (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (B : Over (Spec (.of K))) [GrpObj B] [IsProper B.hom] (f : splitTorus (Spec (.of K)) X ⟶ B) :
    f = toUnit _ ≫ η ≫ f := by
  obtain ⟨k, e⟩ := groupRing_hom_const_of_laurent B.hom (laurent_point_const B) K X (𝟙 _)
    ((torusIso K X).hom ≫ f.left) (by rw [Category.assoc, Over.w, torusIso_hom_hom, Category.comp_id])
  rw [← torusIso_hom_hom, Category.assoc, cancel_epi] at e
  have hη : (η : 𝟙_ _ ⟶ splitTorus (Spec (.of K)) X).left ≫ (splitTorus (Spec (.of K)) X).hom =
    𝟙 _ := Over.w _
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, e, reassoc_of% hη]
  rfl

theorem torus_hom_eq_one (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (B : Over (Spec (.of K))) [GrpObj B] [IsProper B.hom] (f : splitTorus (Spec (.of K)) X ⟶ B)
    [IsMonHom f] : f = 1 := by
  rw [torus_const X B f, IsMonHom.one_hom, Hom.one_def]

theorem exists_torus_and_quotient_hom {G H : Over (Spec (.of K))} [GrpObj G] [GrpObj H]
    (D : TorusExtension G) (E : TorusExtension H) (φ : G ⟶ H) [IsMonHom φ] :
    letI := D.addCommGroup; letI := E.addCommGroup; letI := D.grpB; letI := E.grpB
    (∃! α : splitTorus (Spec (.of K)) D.X ⟶ splitTorus (Spec (.of K)) E.X,
      IsMonHom α ∧ α ≫ E.i = D.i ≫ φ) ∧
    (∃! β : D.B ⟶ E.B, IsMonHom β ∧ D.q ≫ β = φ ≫ E.q) := by
  letI := D.addCommGroup; letI := E.addCommGroup; letI := D.grpB; letI := E.grpB
  have := D.free
  have := D.finite
  have := D.i_hom
  have := D.q_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_quasiCompact
  have := E.i_hom
  have := E.q_hom
  have := E.isAbelian.proper
  have h0 : D.i ≫ φ ≫ E.q = 1 := torus_hom_eq_one D.X E.B _
  have : Mono E.i := E.isKernel.flip.mono_snd_of_mono
  have := epi_of_fpqc D.q
  constructor
  · obtain ⟨α, hα⟩ : ∃ α, α ≫ E.i = D.i ≫ φ :=
      ⟨E.isKernel.lift (D.i ≫ φ) (toUnit _) (by rw [Category.assoc, h0]; rfl),
        E.isKernel.lift_fst _ _ _⟩
    refine ⟨α, ⟨⟨?_, ?_⟩, hα⟩, fun α' h ↦ by rw [← cancel_mono E.i, h.2, hα]⟩
    · rw [← cancel_mono E.i, Category.assoc, hα, IsMonHom.one_hom, IsMonHom.one_hom]
    · rw [← cancel_mono E.i, Category.assoc, hα, IsMonHom.mul_hom, Category.assoc,
        IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hα]
  · obtain ⟨β, hβ⟩ := exists_desc D.q (φ ≫ E.q) fun Z a b h ↦ by
      obtain ⟨τ, rfl⟩ := exists_eq_mul D.isKernel h
      rw [MonObj.mul_comp, Category.assoc, h0, MonObj.comp_one, _root_.one_mul]
    refine ⟨β, ⟨⟨?_, ?_⟩, hβ⟩, fun β' h ↦ by rw [← cancel_epi D.q, h.2, hβ]⟩
    · rw [← IsMonHom.one_hom D.q, Category.assoc, hβ, IsMonHom.one_hom]
    · have : Epi (D.B ◁ D.q) := by
        have := epi_of_fpqc (D.q ▷ D.B)
        rw [show D.B ◁ D.q = (β_ _ _).hom ≫ D.q ▷ D.B ≫ (β_ _ _).hom by simp]
        infer_instance
      have := epi_of_fpqc (D.q ▷ G)
      have : Epi (D.q ⊗ₘ D.q) := by rw [MonoidalCategory.tensorHom_def]; infer_instance
      rw [← cancel_epi (D.q ⊗ₘ D.q), ← IsMonHom.mul_hom_assoc, hβ, tensorHom_comp_tensorHom_assoc,
        hβ, IsMonHom.mul_hom]

end Main

section Family

variable {S : Scheme.{0}}

end Family

end GlobalTheory.SemiRigid

namespace GlobalTheory

open SemiRigid

end GlobalTheory
