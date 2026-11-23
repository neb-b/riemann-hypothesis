module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedPartialLineBundleIsoCocycle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.PartialCocycle

private theorem gm_res_eq_gm {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) {U V : X.Opens} (hle : V ≤ U)
    (hz : f z ∈ V) (u : Γ(X, U)ˣ) : gm f z V (res hle u) = gm f z U u := by
  have key : X.presheaf.map (homOfLE hle).op ≫ f.app V ≫ Z.presheaf.germ (f ⁻¹ᵁ V) z hz =
      f.app U ≫ Z.presheaf.germ (f ⁻¹ᵁ U) z (hle hz) := by
    rw [← Scheme.Hom.germ_stalkMap, ← Scheme.Hom.germ_stalkMap, ← Category.assoc, TopCat.Presheaf.germ_res]
  unfold gm
  rw [dite_eq_left hz, dite_eq_left (hle hz)]
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map]
  unfold res pullU
  have h2 := congrArg (fun g => g.hom (u : Γ(X, U))) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  exact h2

theorem gm_iso {X Z : Scheme.{0}} {L M : LB X} {w : LB.Iso L M} (hw : w.IsGen) (f : Z ⟶ X) (z : Z)
    (a a' : M.ι) (b b' : L.ι) (ha : f z ∈ M.U a) (ha' : f z ∈ M.U a') (hb : f z ∈ L.U b) (hb' : f z ∈ L.U b') :
    gm f z (M.U a ⊓ L.U b) (w.s (a, b)) =
      gm f z (M.U a ⊓ M.U a') (M.g a a') * (gm f z (L.U b ⊓ L.U b') (L.g b b'))⁻¹ *
        gm f z (M.U a' ⊓ L.U b') (w.s (a', b')) := by
  have hz : f z ∈ (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') := ⟨⟨ha, hb⟩, ⟨ha', hb'⟩⟩
  have h₁ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a ⊓ L.U b := inf_le_left
  have h₂ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a ⊓ M.U a' :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have h₃ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ L.U b ⊓ L.U b' :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have h₄ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a' ⊓ L.U b' := inf_le_right
  have h1 := hw (a, b) (a', b')
  calc gm f z (M.U a ⊓ L.U b) (w.s (a, b))
      = gm f z _ (res h₁ (w.s (a, b))) := (gm_res_eq_gm f z h₁ hz _).symm
    _ = gm f z _ (res h₂ (M.g a a') * (res h₃ (L.g b b'))⁻¹ * res h₄ (w.s (a', b'))) := congrArg _ h1
    _ = _ := by
      rw [map_mul, map_mul, map_inv, gm_res_eq_gm f z h₂ hz, gm_res_eq_gm f z h₃ hz]
      exact congrArg _ (gm_res_eq_gm f z h₄ hz _)

private theorem algebraMap_OmS_eq_algebraMap_comp {G : Type*} [CommGroup G] (A B C s t u : G) :
    A * B⁻¹ * s * (B * C⁻¹ * t) * (A * C⁻¹ * u)⁻¹ = s * t * u⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem gm_val_eq_germ_app' {X Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) (U : X.Opens) (hz : g z ∈ U)
    (u : Γ(X, U)ˣ) : ((gm g z U u : Z.presheaf.stalk z)) = Z.presheaf.germ (g ⁻¹ᵁ U) z hz (g.app U u.val) := by
  unfold gm
  rw [dite_eq_left hz]
  rfl

private theorem gm_id_val_eq_germ' {X : Scheme.{0}} (z : X) (U : X.Opens) (hz : z ∈ U)
    (u : Γ(X, U)ˣ) : ((gm (𝟙 X) z U u : X.presheaf.stalk z)) = X.presheaf.germ U z hz u.val := by
  exact gm_val_eq_germ_app' (𝟙 X) z U hz u

theorem cocycle_of_rigid : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (V₁ V₂ V₃ : S.Opens) (M₁ M₂ M₃ : LB X) (w₁₂ : LB.Iso M₂ M₁) (w₂₃ : LB.Iso M₃ M₂) (w₁₃ : LB.Iso M₃ M₁), e ≫ p = 𝟙 S → (∀ (V : S.Opens) (u : Γ(X, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → ⨆ a, M₁.U a = p ⁻¹ᵁ V₁ → ⨆ a, M₂.U a = p ⁻¹ᵁ V₂ → ⨆ a, M₃.U a = p ⁻¹ᵁ V₃ → w₁₂.IsGen → w₂₃.IsGen → w₁₃.IsGen → (∀ (x : S) a b c, e x ∈ M₁.U a → e x ∈ M₂.U b → e x ∈ M₃.U c → gm e x (M₁.U a ⊓ M₂.U b) (w₁₂.s (a, b)) * gm e x (M₂.U b ⊓ M₃.U c) (w₂₃.s (b, c)) = gm e x (M₁.U a ⊓ M₃.U c) (w₁₃.s (a, c))) → ∀ (y : X) a b c, y ∈ M₁.U a → y ∈ M₂.U b → y ∈ M₃.U c → gm (𝟙 X) y (M₁.U a ⊓ M₂.U b) (w₁₂.s (a, b)) * gm (𝟙 X) y (M₂.U b ⊓ M₃.U c) (w₂₃.s (b, c)) = gm (𝟙 X) y (M₁.U a ⊓ M₃.U c) (w₁₃.s (a, c)) := by
  intro X S p e V₁ V₂ V₃ M₁ M₂ M₃ w₁₂ w₂₃ w₁₃ hep hrig hU₁ hU₂ hU₃ hg₁₂ hg₂₃ hg₁₃ hcoc y a b c hya hyb hyc
  let T : M₁.ι × M₂.ι × M₃.ι → X.Opens := fun i => M₁.U i.1 ⊓ M₂.U i.2.1 ⊓ M₃.U i.2.2
  have l₁ : ∀ i, T i ≤ M₁.U i.1 ⊓ M₂.U i.2.1 := fun i => inf_le_left
  have l₂ : ∀ i, T i ≤ M₂.U i.2.1 ⊓ M₃.U i.2.2 := fun i => le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l₃ : ∀ i, T i ≤ M₁.U i.1 ⊓ M₃.U i.2.2 := fun i => le_inf (inf_le_left.trans inf_le_left) inf_le_right
  let t : ∀ i, Γ(X, T i)ˣ := fun i => res (l₁ i) (w₁₂.s (i.1, i.2.1)) * res (l₂ i) (w₂₃.s (i.2.1, i.2.2)) *
    (res (l₃ i) (w₁₃.s (i.1, i.2.2)))⁻¹
  have hprod : ∀ {Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) i (hz : g z ∈ T i), gm g z (T i) (t i) =
      gm g z (M₁.U i.1 ⊓ M₂.U i.2.1) (w₁₂.s (i.1, i.2.1)) * gm g z (M₂.U i.2.1 ⊓ M₃.U i.2.2) (w₂₃.s (i.2.1, i.2.2)) *
        (gm g z (M₁.U i.1 ⊓ M₃.U i.2.2) (w₁₃.s (i.1, i.2.2)))⁻¹ := by
    intro Z g z i hz
    simp only [t, map_mul, map_inv]
    exact congrArg₂ _ (congrArg₂ _ (gm_res_eq_gm g z (l₁ i) hz _) (gm_res_eq_gm g z (l₂ i) hz _))
      (congrArg _ (gm_res_eq_gm g z (l₃ i) hz _))
  have hindep : ∀ {Z : Scheme.{0}} (g : Z ⟶ X) (z : Z) i j (hi : g z ∈ T i) (hj : g z ∈ T j),
      gm g z (T i) (t i) = gm g z (T j) (t j) := by
    intro Z g z i j hi hj
    rw [hprod g z i hi, hprod g z j hj]
    obtain ⟨⟨hi1, hi2⟩, hi3⟩ := hi
    obtain ⟨⟨hj1, hj2⟩, hj3⟩ := hj
    rw [gm_iso hg₁₂ g z i.1 j.1 i.2.1 j.2.1 hi1 hj1 hi2 hj2, gm_iso hg₂₃ g z i.2.1 j.2.1 i.2.2 j.2.2 hi2 hj2 hi3 hj3,
      gm_iso hg₁₃ g z i.1 j.1 i.2.2 j.2.2 hi1 hj1 hi3 hj3]
    exact algebraMap_OmS_eq_algebraMap_comp _ _ _ _ _ _
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 T (fun i => (t i).val) := by
    intro i j
    apply TopCat.Presheaf.section_ext X.sheaf
    intro z hz
    show X.presheaf.germ (T i ⊓ T j) z hz (X.presheaf.map (TopologicalSpace.Opens.infLELeft (T i) (T j)).op (t i).val) =
      X.presheaf.germ (T i ⊓ T j) z hz (X.presheaf.map (TopologicalSpace.Opens.infLERight (T i) (T j)).op (t j).val)
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    rw [← gm_id_val_eq_germ' z (T i) _ (t i), ← gm_id_val_eq_germ' z (T j) _ (t j)]
    exact congrArg Units.val (hindep (𝟙 X) z i j hz.1 hz.2)
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing T (fun i => (t i).val) hcompat
  have hcov : p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃) ≤ iSup T := by
    intro x hx
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    have m1 : x ∈ ⨆ a, M₁.U a := by rw [hU₁]; exact h1
    have m2 : x ∈ ⨆ a, M₂.U a := by rw [hU₂]; exact h2
    have m3 : x ∈ ⨆ a, M₃.U a := by rw [hU₃]; exact h3
    obtain ⟨a₁, ha₁⟩ := TopologicalSpace.Opens.mem_iSup.1 m1
    obtain ⟨a₂, ha₂⟩ := TopologicalSpace.Opens.mem_iSup.1 m2
    obtain ⟨a₃, ha₃⟩ := TopologicalSpace.Opens.mem_iSup.1 m3
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a₁, a₂, a₃), ⟨⟨ha₁, ha₂⟩, ha₃⟩⟩
  have hV : V₁ ⊓ V₂ ⊓ V₃ ≤ e ⁻¹ᵁ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) := by
    intro x hx
    show (e ≫ p) x ∈ V₁ ⊓ V₂ ⊓ V₃
    rw [hep]
    exact hx
  let u : Γ(X, p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) := X.presheaf.map (homOfLE hcov).op s
  have hsT : ∀ i (z : X) (hz : z ∈ T i) (hz' : z ∈ iSup T),
      X.presheaf.germ (iSup T) z hz' s = X.presheaf.germ (T i) z hz (t i).val := by
    intro i z hz hz'
    have h := hs i
    dsimp only at h
    rw [← h]
    exact (TopCat.Presheaf.germ_res_apply X.presheaf (TopologicalSpace.Opens.leSupr T i) z hz s).symm
  have hu1 : (e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV).hom u = 1 := by
    apply TopCat.Presheaf.section_ext S.sheaf
    intro x hx
    have hex : e x ∈ p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃) := hV hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov hex)
    show S.presheaf.germ _ x hx ((e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV).hom u) = S.presheaf.germ _ x hx 1
    rw [map_one]
    have k1 : e.appLE (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (V₁ ⊓ V₂ ⊓ V₃) hV ≫ S.presheaf.germ _ x hx =
        X.presheaf.germ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) (e x) hex ≫ e.stalkMap x := by
      rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    have k2 := congrArg (fun g => g.hom u) k1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at k2
    rw [k2]
    have hg1 : gm e x (T i) (t i) = 1 := by
      rw [hprod e x i hi]
      obtain ⟨⟨hi1, hi2⟩, hi3⟩ := hi
      rw [hcoc x i.1 i.2.1 i.2.2 hi1 hi2 hi3, mul_inv_cancel]
    rw [← Units.val_one, ← hg1, gm_val_eq_germ_app' e x (T i) hi]
    simp only [u]
    erw [TopCat.Presheaf.germ_res_apply, hsT i (e x) hi, Scheme.Hom.germ_stalkMap_apply]
  have hu : u = 1 := hrig _ u hV hu1
  have hyT : y ∈ T (a, b, c) := ⟨⟨hya, hyb⟩, hyc⟩
  have hyS : y ∈ iSup T := TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b, c), hyT⟩
  have fin : gm (𝟙 X) y (T (a, b, c)) (t (a, b, c)) = 1 := by
    apply Units.ext
    rw [gm_id_val_eq_germ' y _ hyT, Units.val_one, ← hsT (a, b, c) y hyT hyS]
    have hyV : y ∈ p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃) := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have := (le_iSup M₁.U a) hya
        rw [hU₁] at this
        exact this
      · have := (le_iSup M₂.U b) hyb
        rw [hU₂] at this
        exact this
      · have := (le_iSup M₃.U c) hyc
        rw [hU₃] at this
        exact this
    have k3 := congrArg (X.presheaf.germ (p ⁻¹ᵁ (V₁ ⊓ V₂ ⊓ V₃)) y hyV) hu
    simp only [u, map_one] at k3
    erw [TopCat.Presheaf.germ_res_apply] at k3
    exact k3
  rw [hprod (𝟙 X) y (a, b, c) hyT] at fin
  exact mul_inv_eq_one.1 fin

end GlobalTheory.PartialCocycle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCover
section
namespace GlobalTheory.SmoothDescent

section Rings

open TensorProduct KaehlerDifferential

theorem flat_of_formallySmooth_of_essFiniteType (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    [IsNoetherianRing R] [Algebra.EssFiniteType R B] [Algebra.FormallySmooth R B] :
    Module.Flat R B := by
  let P := Algebra.EssFiniteType.subalgebra R B
  let M : Submonoid P := Algebra.EssFiniteType.submonoid R B
  obtain ⟨n, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R P)
  let M' := M.comap f₀
  let P' := Localization M'
  let fP : P' →ₐ[R] B := IsLocalization.liftAlgHom (M := M')
      (f := (IsScalarTower.toAlgHom R P B).comp f₀) fun x ↦
    IsLocalization.map_units (M := M) B ⟨f₀ x.1, x.2⟩
  have hf₁ : Function.Surjective fP := by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq M x
    obtain ⟨x, rfl⟩ := hf₀ x
    obtain ⟨s, rfl⟩ := hf₀ s
    refine ⟨IsLocalization.mk' (M := M') _ x ⟨s, hs⟩, ?_⟩
    exact (IsLocalization.lift_mk'_spec (M := M') (S := P')
      (g := ((IsScalarTower.toAlgHom R P B).comp f₀).toRingHom)
      (fun x ↦ IsLocalization.map_units (M := M) B ⟨f₀ x.1, x.2⟩) x _ ⟨s, hs⟩).mpr
      (IsLocalization.mk'_spec' B (f₀ x) (⟨f₀ s, hs⟩ : M)).symm
  have : Module.Flat R P' := .trans R (MvPolynomial (Fin n) R) P'
  exact Algebra.FormallySmooth.flat_of_algHom_of_isNoetherianRing fP hf₁

theorem formallySmooth_of_flat_of_formallyUnramified (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]
    [Algebra.EssFiniteType R A] [Module.Flat R A] [Algebra.FormallyUnramified R A] :
    Algebra.FormallySmooth R A := by
  have : Algebra.FormallyEtale (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] A) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field _ _
  have : Algebra.FinitePresentation R (Algebra.EssFiniteType.subalgebra R A) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
    (Algebra.EssFiniteType.submonoid R A)

theorem formallyEtale_of_bijective_mapBaseChange (R P B : Type*) [CommRing R] [CommRing P] [CommRing B]
    [Algebra R P] [Algebra R B] [Algebra P B] [IsScalarTower R P B] [Algebra.FormallySmooth R B]
    (h : Function.Bijective (mapBaseChange R P B)) : Algebra.FormallyEtale P B := by
  have h1 : Subsingleton Ω[B⁄P] := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨y, rfl⟩ := map_surjective R P B x
    exact (exact_mapBaseChange_map R P B y).mpr (h.2 y)
  have h2 : Subsingleton (Algebra.H1Cotangent P B) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    have h3 : Algebra.H1Cotangent.δ R P B x = 0 := by
      apply h.1
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R P B _).mpr ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R P B x).mp h3
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨h1, h2⟩

theorem formallySmooth_of_faithfullyFlat (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsNoetherianRing R] [IsLocalRing A]
    [Algebra.EssFiniteType R A] [Algebra.EssFiniteType A B] [Module.FaithfullyFlat A B]
    [Algebra.FormallyEtale A B] [Algebra.FormallySmooth R B] : Algebra.FormallySmooth R A := by
  classical
  have : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing R A
  have : Algebra.EssFiniteType R B := .comp R A B
  have : Module.FinitePresentation A Ω[A⁄R] := Module.finitePresentation_of_finite _ _
  have : Module.Flat B (B ⊗[A] Ω[A⁄R]) := .of_linearEquiv (tensorKaehlerEquivOfFormallyEtale R A B)
  have : Module.Flat A Ω[A⁄R] := Module.Flat.of_flat_tensorProduct _ _ B
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _ (span_range_derivation R A)
  have : Finite κ := Module.Finite.finite_basis b
  let P := MvPolynomial κ R
  let φ : P →ₐ[R] A := MvPolynomial.aeval a
  algebraize [φ.toRingHom, (algebraMap A B).comp φ.toRingHom]
  have : IsScalarTower R P B := .to₁₂₄ R P A B
  have hX (i : κ) : algebraMap P A (MvPolynomial.X i) = a i := MvPolynomial.aeval_X _ _
  let bB : Module.Basis κ B Ω[B⁄R] := (b.baseChange B).map (tensorKaehlerEquivOfFormallyEtale R A B)
  let bP : Module.Basis κ B (B ⊗[P] Ω[P⁄R]) := (mvPolynomialBasis R κ).baseChange B
  have hbij : Function.Bijective (mapBaseChange R P B) := by
    have : mapBaseChange R P B = (bP.equiv bB (Equiv.refl κ)).toLinearMap := by
      refine bP.ext fun i => ?_
      rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
      simp [bP, bB, hb, ← hX, ← IsScalarTower.algebraMap_apply, P]
    rw [this]
    exact (bP.equiv bB (Equiv.refl κ)).bijective
  have : Algebra.FormallyEtale P B := formallyEtale_of_bijective_mapBaseChange R P B hbij
  let p : Ideal P := (IsLocalRing.maximalIdeal A).comap (algebraMap P A)
  let Q := Localization.AtPrime p
  let ψ : Q →ₐ[P] A := IsLocalization.liftAlgHom (M := p.primeCompl) (f := Algebra.ofId P A) fun x => by
    by_contra h
    exact x.2 h
  algebraize [ψ.toRingHom, (algebraMap A B).comp ψ.toRingHom]
  have : IsScalarTower P Q B := .to₁₂₄ P Q A B
  have : IsScalarTower R Q A := .to₁₃₄ R P Q A
  have : IsScalarTower R Q B := .to₁₂₄ R Q A B
  have : IsLocalHom (algebraMap Q A) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff Q p]
    intro hxp
    have e : algebraMap P A x = algebraMap P A s * algebraMap Q A (IsLocalization.mk' Q x s) := by
      rw [IsScalarTower.algebraMap_apply P Q A s, ← map_mul, IsLocalization.mk'_spec',
        ← IsScalarTower.algebraMap_apply]
    have hs : IsUnit (algebraMap P A s) := by
      by_contra h
      exact s.2 h
    exact hxp (e ▸ hs.mul hx)
  have : Algebra.FormallyEtale Q B := Algebra.FormallyEtale.localization_base p.primeCompl
  have : Algebra.EssFiniteType Q A := .of_comp R Q A
  have : Algebra.EssFiniteType Q B := .of_comp R Q B
  have : Module.Flat Q B := flat_of_formallySmooth_of_essFiniteType Q B
  have : Module.Flat Q A := by
    rw [← RingHom.flat_algebraMap_iff]
    refine ringHom_flat_of_comp_faithfullyFlat (β := algebraMap A B)
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance) ?_
    rw [← IsScalarTower.algebraMap_eq, RingHom.flat_algebraMap_iff]
    infer_instance
  have : Algebra.FormallyUnramified Q A := by
    have h1 : Subsingleton (B ⊗[A] Ω[A⁄Q]) := (tensorKaehlerEquivOfFormallyEtale Q A B).subsingleton
    exact ⟨(Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right A B).mp h1⟩
  have : Algebra.FormallySmooth Q A := formallySmooth_of_flat_of_formallyUnramified Q A
  have : Algebra.FormallySmooth P A := .comp P Q A
  exact .comp R P A

end Rings

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem smooth_of_comp_of_etale_of_surjective {X Y S : Scheme.{0}} (π : X ⟶ Y) (s : Y ⟶ S)
    [IsLocallyNoetherian S] [Etale π] [Surjective π] [LocallyOfFiniteType s] [Smooth (π ≫ s)] :
    Smooth s := by
  have : LocallyOfFinitePresentation s := LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr ‹_›
  have : Flat π := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale π›).1
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  rintro y -
  obtain ⟨x, rfl⟩ := π.surjective y
  rw [Scheme.Hom.mem_smoothLocus]
  have h : ((π ≫ s).stalkMap x).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp ((π ≫ s).smoothLocus_eq_top.ge (Set.mem_univ x))
  rw [Scheme.Hom.stalkMap_comp] at h
  replace h : ((π.stalkMap x).hom.comp (s.stalkMap (π x)).hom).FormallySmooth := h
  have hs : (π.stalkMap x).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp (π.smoothLocus_eq_top.ge (Set.mem_univ x))
  have hu := FormallyUnramified.stalkMap π x
  have hf := faithfullyFlat_stalkMap_of_flat π x
  have e₁ := LocallyOfFiniteType.stalkMap π x
  have e₂ := LocallyOfFiniteType.stalkMap s (π x)
  algebraize [(π.stalkMap x).hom, (s.stalkMap (π x)).hom, (π.stalkMap x).hom.comp (s.stalkMap (π x)).hom]
  have : Algebra.FormallyEtale (Y.presheaf.stalk (π x)) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  exact formallySmooth_of_faithfullyFlat (S.presheaf.stalk (s (π x))) (Y.presheaf.stalk (π x))
    (X.presheaf.stalk x)

theorem smoothOfRelativeDimension_of_etale_cover :
    ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp K) (d : ℕ), Etale π → Surjective π → LocallyOfFiniteType s → SmoothOfRelativeDimension d (π ≫ s) → SmoothOfRelativeDimension d s := by
  intro K _ X Y π s d _ _ _ hd
  have : Smooth (π ≫ s) := SmoothOfRelativeDimension.smooth d _
  have : Smooth s := smooth_of_comp_of_etale_of_surjective π s
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  choose n W hW hn using H1.exists_dim s
  have key (y : Y) : n y = d := by
    obtain ⟨x, rfl⟩ := π.surjective y
    have := hn (π x)
    have h₁ : SmoothOfRelativeDimension (0 + n (π x)) ((π ∣_ W (π x)) ≫ (W (π x)).ι ≫ s) := inferInstance
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc] at h₁
    have h₂ : SmoothOfRelativeDimension (0 + d) ((π ⁻¹ᵁ W (π x)).ι ≫ π ≫ s) := inferInstance
    simpa using H1.dim_unique _ h₁ h₂ ⟨x, hW (π x)⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W ?_ fun y => key y ▸ hn y
  rw [← top_le_iff]
  rintro y -
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩

end GlobalTheory.SmoothDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaObjectComparisonMapsCocycle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaCocycle

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {β : TBase o k} {S S' S'' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}

def PullsBack (t' : TObj g k J β s') (t : TObj g k J β s) (f : S' ⟶ S) (φ : t'.A.left ⟶ t.A.left) : Prop :=
  IsGrpPullback t'.A t.A f φ ∧ LBIso t'.L (t.L.pull φ) ∧ ∀ l, (t'.pt l).left ≫ φ = f ≫ (t.pt l).left

private theorem lbIso_pull_comp_of_lbIso_pull {X Y Z : Scheme.{0}} {L : LB X} {L' : LB Y} {f : Y ⟶ X}
    (H : LBIso L' (L.pull f)) (c : Z ⟶ Y) : LBIso (L'.pull c) (L.pull (c ≫ f)) := by
  have a : ChartPull (L'.pull c) L' c :=
    ⟨fun J => J PUnit.unit, fun J y hy => Set.mem_iInter.1 hy PUnit.unit, fun y J J' hJ hJ' => by
      refine (gm_linComb L' (fun _ => c) (fun _ => 1) (𝟙 _) y J J' hJ hJ').trans ?_
      simp⟩
  exact LBIso.chartPull a (chartPullSame L (fun _ => c ≫ f) (fun _ => f) (fun _ => 1) c (fun _ => rfl)) H

theorem PullsBack.comp {t'' : TObj g k J β s''} {t' : TObj g k J β s'} {t : TObj g k J β s} {f' : S'' ⟶ S'} {f : S' ⟶ S}
    {h : S'' ⟶ S} {φ' : t''.A.left ⟶ t'.A.left} {φ : t'.A.left ⟶ t.A.left} (H' : PullsBack t'' t' f' φ')
    (H : PullsBack t' t f φ) (e : f' ≫ f = h) : PullsBack t'' t h (φ' ≫ φ) := by
  obtain ⟨g', l', p'⟩ := H'
  obtain ⟨g₀, l₀, p₀⟩ := H
  subst e
  refine ⟨g'.comp g₀, ?_, fun i => ?_⟩
  · exact LBIso.trans t''.isLB (pull_isLB t'.isLB φ') (pull_isLB t.isLB (φ' ≫ φ)) l'
      (lbIso_pull_comp_of_lbIso_pull l₀ φ')
  · rw [reassoc_of% (p' i), p₀ i, Category.assoc]

theorem PullsBack.cancel {t'' : TObj g k J β s''} {t' : TObj g k J β s'} {t : TObj g k J β s} (f' : S'' ⟶ S') {f : S' ⟶ S}
    {h : S'' ⟶ S} {ψ : t''.A.left ⟶ t.A.left} {φ : t'.A.left ⟶ t.A.left} (H'' : PullsBack t'' t h ψ)
    (H : PullsBack t' t f φ) (e : f' ≫ f = h) : ∃ c, PullsBack t'' t' f' c ∧ c ≫ φ = ψ := by
  obtain ⟨g'', l'', p''⟩ := H''
  obtain ⟨g₀, l₀, p₀⟩ := H
  subst e
  have sq : ψ ≫ t.A.hom = (t''.A.hom ≫ f') ≫ f := by rw [g''.1.w, Category.assoc]
  set c := g₀.1.lift ψ (t''.A.hom ≫ f') sq with hcdef
  have hc₁ : c ≫ φ = ψ := g₀.1.lift_fst _ _ _
  have hc₂ : c ≫ t'.A.hom = t''.A.hom ≫ f' := g₀.1.lift_snd _ _ _
  refine ⟨c, ⟨g₀.cancel (by rw [hc₁]; exact g'') hc₂, ?_, fun i => ?_⟩, hc₁⟩
  · have l₁ := lbIso_pull_comp_of_lbIso_pull l₀ c
    rw [hc₁] at l₁
    exact LBIso.trans t''.isLB (pull_isLB t.isLB ψ) (pull_isLB t'.isLB c) l'' (LBIso.symm l₁)
  · apply g₀.1.hom_ext
    · rw [Category.assoc, hc₁, p'' i, Category.assoc, Category.assoc, p₀ i]
    · rw [Category.assoc, hc₂, ← Category.assoc, Over.w (t''.pt i), Category.assoc, Over.w (t'.pt i)]
      simp [Out.baseOver]

theorem cocycle : (∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s), f ≫ s = s' → ∃ t' : TObj g k J b s', TMap t' t f) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (β : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (I : Type) (U : I → S.Opens) (t : ∀ i, TObj g k J β ((U i).ι ≫ s)) (u : ∀ i j, TObj g k J β ((U i ⊓ U j).ι ≫ s)) (a : ∀ i j, (u i j).A.left ⟶ (t i).A.left) (b : ∀ i j, (u i j).A.left ⟶ (t j).A.left), (∀ i j, IsGrpPullback (u i j).A (t i).A (S.homOfLE inf_le_left) (a i j) ∧ LBIso (u i j).L ((t i).L.pull (a i j)) ∧ ∀ l, ((u i j).pt l).left ≫ a i j = S.homOfLE inf_le_left ≫ ((t i).pt l).left) → (∀ i j, IsGrpPullback (u i j).A (t j).A (S.homOfLE inf_le_right) (b i j) ∧ LBIso (u i j).L ((t j).L.pull (b i j)) ∧ ∀ l, ((u i j).pt l).left ≫ b i j = S.homOfLE inf_le_right ≫ ((t j).pt l).left) → (∀ (T : Scheme.{0}) (i : I) (f : T ⟶ (U i).toScheme) (u : TObj g k J β (f ≫ (U i).ι ≫ s)) (φ φ' : u.A.left ⟶ (t i).A.left), IsOpenImmersion f → IsGrpPullback u.A (t i).A f φ → IsGrpPullback u.A (t i).A f φ' → LBIso u.L ((t i).L.pull φ) → LBIso u.L ((t i).L.pull φ') → (∀ a, (u.pt a).left ≫ φ = (u.pt a).left ≫ φ') → φ = φ') → ∀ i j k (T : Scheme.{0}) (x : T ⟶ (u i j).A.left) (y : T ⟶ (u j k).A.left) (z : T ⟶ (u i k).A.left), x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k := by
  intro hex o _ g n J β S s I U t u a b ha hb hrig i j m T x y z hxy hxz
  have HA : ∀ i j, PullsBack (u i j) (t i) (S.homOfLE inf_le_left) (a i j) := ha
  have HB : ∀ i j, PullsBack (u i j) (t j) (S.homOfLE inf_le_right) (b i j) := hb
  let V : S.Opens := (U i ⊓ U j) ⊓ (U j ⊓ U m)
  have hVm : V ≤ U m := inf_le_right.trans inf_le_right
  have hVim : V ≤ U i ⊓ U m := le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
  obtain ⟨t', φk, gk, lk, pk, -⟩ := hex o g n J β (U m).toScheme V.toScheme ((U m).ι ≫ s)
    (S.homOfLE hVm ≫ (U m).ι ≫ s) (S.homOfLE hVm) (t m) rfl
  have hk : PullsBack t' (t m) (S.homOfLE hVm) φk := ⟨gk, lk, pk⟩
  obtain ⟨c₁, h₁, e₁⟩ := PullsBack.cancel (S.homOfLE (inf_le_right : V ≤ U j ⊓ U m)) hk (HB j m) (by simp)
  have h₁' : PullsBack t' (t j) (S.homOfLE (inf_le_right.trans inf_le_left : V ≤ U j)) (c₁ ≫ a j m) :=
    h₁.comp (HA j m) (by simp)
  obtain ⟨c₂, h₂, e₂⟩ := PullsBack.cancel (S.homOfLE (inf_le_left : V ≤ U i ⊓ U j)) h₁' (HB i j) (by simp)
  have h₂' : PullsBack t' (t i) (S.homOfLE (inf_le_left.trans inf_le_left : V ≤ U i)) (c₂ ≫ a i j) :=
    h₂.comp (HA i j) (by simp)
  obtain ⟨c₃, h₃, e₃⟩ := PullsBack.cancel (S.homOfLE hVim) h₂' (HA i m) (by simp)
  have h₃' : PullsBack t' (t m) (S.homOfLE hVm) (c₃ ≫ b i m) := h₃.comp (HB i m) (by simp)
  have hφ : φk = c₃ ≫ b i m := hrig V.toScheme m (S.homOfLE hVm) t' φk (c₃ ≫ b i m) inferInstance hk.1 h₃'.1
    hk.2.1 h₃'.2.1 (fun l => by rw [hk.2.2 l, h₃'.2.2 l])
  have hq : (x ≫ (u i j).A.hom) ≫ S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) =
      (y ≫ (u j m).A.hom) ≫ S.homOfLE (inf_le_left : U j ⊓ U m ≤ U j) := by
    rw [Category.assoc, Category.assoc, ← (HB i j).1.1.w, ← (HA j m).1.1.w, ← Category.assoc, hxy, Category.assoc]
  have sq := isPullback_opens_inf_le (X := S) (inf_le_right : U i ⊓ U j ≤ U j) (inf_le_left : U j ⊓ U m ≤ U j)
  obtain ⟨q, hq₁, hq₂⟩ : ∃ q : T ⟶ V.toScheme, q ≫ S.homOfLE (inf_le_left : V ≤ U i ⊓ U j) = x ≫ (u i j).A.hom ∧
      q ≫ S.homOfLE (inf_le_right : V ≤ U j ⊓ U m) = y ≫ (u j m).A.hom :=
    ⟨sq.lift _ _ hq, sq.lift_fst _ _ _, sq.lift_snd _ _ _⟩
  obtain ⟨w, hw₁, hw₂⟩ : ∃ w : T ⟶ t'.A.left, w ≫ c₁ = y ∧ w ≫ t'.A.hom = q :=
    ⟨h₁.1.1.lift y q hq₂.symm, h₁.1.1.lift_fst _ _ _, h₁.1.1.lift_snd _ _ _⟩
  have hwx : w ≫ c₂ = x := by
    apply (HB i j).1.1.hom_ext
    · rw [Category.assoc, e₂, ← Category.assoc, hw₁, hxy]
    · rw [Category.assoc, h₂.1.1.w, ← Category.assoc, hw₂, hq₁]
  have hbase : q ≫ S.homOfLE hVim = z ≫ (u i m).A.hom := by
    have e₅ : ∀ {W : Scheme.{0}} (h : W ⟶ (U i ⊓ U m).toScheme),
        h ≫ (U i ⊓ U m).ι = (h ≫ S.homOfLE (inf_le_left : U i ⊓ U m ≤ U i)) ≫ (U i).ι := fun h => by simp
    rw [← cancel_mono (U i ⊓ U m).ι, Category.assoc, Scheme.homOfLE_ι, e₅ (z ≫ (u i m).A.hom)]
    simp only [Category.assoc]
    rw [← reassoc_of% (HA i m).1.1.w, ← reassoc_of% hxz, reassoc_of% (HA i j).1.1.w, ← reassoc_of% hq₁]
    simp
  have hwz : w ≫ c₃ = z := by
    apply (HA i m).1.1.hom_ext
    · rw [Category.assoc, e₃, ← Category.assoc, hwx, hxz]
    · rw [Category.assoc, h₃.1.1.w, ← Category.assoc, hw₂, hbase]
  calc y ≫ b j m = w ≫ c₁ ≫ b j m := by rw [← Category.assoc, hw₁]
    _ = w ≫ c₃ ≫ b i m := by rw [e₁, hφ]
    _ = z ≫ b i m := by rw [← Category.assoc, hwz]

end GlobalTheory.ThetaCocycle
end

