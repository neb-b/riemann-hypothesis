module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyOfFinitePresentationOfCancel
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.LfpDescent

lemma affine_case {X Y S : Scheme.{0}} [IsAffine X] [IsAffine Y] [IsAffine S] (q : X ⟶ Y)
    (f : Y ⟶ S) [IsFinite q] [Flat q] [LocallyOfFinitePresentation q] [Surjective q]
    [LocallyOfFinitePresentation (q ≫ f)] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  have h1 : q.appTop.hom.Finite :=
    Scheme.Hom.finite_appTop q
  have h2 : q.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q).1 ⟨inferInstance, inferInstance⟩
  have h3 : q.appTop.hom.FinitePresentation :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).1 inferInstance
  have h4 : (q.appTop.hom.comp f.appTop.hom).FinitePresentation := by
    have := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).1
      (inferInstance : LocallyOfFinitePresentation (q ≫ f))
    rwa [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at this
  letI : Algebra Γ(S, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
  letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
  letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := (q.appTop.hom.comp f.appTop.hom).toAlgebra
  haveI : IsScalarTower Γ(S, ⊤) Γ(Y, ⊤) Γ(X, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := h1
  haveI : Algebra.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) := h3
  haveI : Module.FaithfullyFlat Γ(Y, ⊤) Γ(X, ⊤) := h2
  haveI : Module.FinitePresentation Γ(Y, ⊤) Γ(X, ⊤) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  have hp : Module.Projective Γ(Y, ⊤) Γ(X, ⊤) := Module.Flat.projective_of_finitePresentation
  exact _root_.GlobalTheory.CompanionTheory.FinPresDescent.finitePresentation_of_finite_projective_faithfullyFlat _ _ _ inferInstance hp inferInstance h4

theorem descends : ∀ {X Y S : Scheme.{0}} (q : X ⟶ Y) (f : Y ⟶ S), IsFinite q → Flat q →
    LocallyOfFinitePresentation q → Surjective q → LocallyOfFinitePresentation (q ≫ f) →
    LocallyOfFinitePresentation f := by
  intro X Y S q f _ _ _ _ _
  let I := {p : S.affineOpens × Y.affineOpens // (p.2 : Y.Opens) ≤ f ⁻¹ᵁ (p.1 : S.Opens)}
  haveI := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{0})
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFinitePresentation.{0}) (fun i : I ↦ (i.1.2 : Y.Opens)) ?_ ?_
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := f y) (U := ⊤) trivial
    obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := f ⁻¹ᵁ U) hyU
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hVU⟩, hyV⟩
  · rintro ⟨⟨⟨U, hU⟩, ⟨V, hV⟩⟩, e⟩
    dsimp only at e ⊢
    haveI : IsAffine U.toScheme := hU
    haveI : IsAffine V.toScheme := hV
    haveI : IsAffine (q ⁻¹ᵁ V).toScheme := (hV.preimage q)
    have hc : (q ∣_ V) ≫ f.resLE U V e =
        (q ≫ f).resLE U (q ⁻¹ᵁ V) (by simpa using (Scheme.Hom.preimage_mono q e)) := by
      rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE]
    haveI : LocallyOfFinitePresentation ((q ∣_ V) ≫ f.resLE U V e) := by
      rw [hc]; delta Scheme.Hom.resLE; infer_instance
    haveI : Surjective (q ∣_ V) := IsZariskiLocalAtTarget.restrict ‹Surjective q› V
    haveI : LocallyOfFinitePresentation (f.resLE U V e) := affine_case (q ∣_ V) _
    rw [← Scheme.Hom.resLE_comp_ι f e]
    infer_instance

end GlobalTheory.CompanionTheory.LfpDescent
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistApply
section
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Crv.SplitProj

def act (k : Type) {K V O : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] [Field k]
    [Algebra k K] (ρ : O →+* Module.End K V) : TensorProduct ℤ k O →+* Module.End K V :=
  (actMap (k := k) ρ).toRingHom

theorem act_tmul (k : Type) {K V O : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O]
    [Field k] [Algebra k K] (ρ : O →+* Module.End K V) (c : k) (a : O) :
    act k ρ (c ⊗ₜ[ℤ] a) = algebraMap k K c • ρ a :=
  actMap_tmul ρ c a

def toEnd {K O : Type} [Field K] [CommRing O] {d : ℕ} (ρ : O →+* Matrix (Fin d) (Fin d) K) :
    O →+* Module.End K (Fin d → K) :=
  (Matrix.toLinAlgEquiv' (R := K) (n := Fin d)).toAlgHom.toRingHom.comp ρ

theorem toEnd_apply {K O : Type} [Field K] [CommRing O] {d : ℕ}
    (ρ : O →+* Matrix (Fin d) (Fin d) K) (a : O) (v : Fin d → K) :
    toEnd ρ a v = (ρ a).mulVec v := rfl

def twist {K O : Type} [Field K] [CommRing O] {d : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]
    (ρ : O →+* Matrix (Fin d) (Fin d) K) : O →+* Matrix (Fin d) (Fin d) K :=
  (frobenius K p).mapMatrix.comp ρ

theorem twist_apply {K O : Type} [Field K] [CommRing O] {d : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]
    (ρ : O →+* Matrix (Fin d) (Fin d) K) (a : O) : twist p ρ a = (ρ a).map (· ^ p) := rfl

def conjT {K O : Type} [Field K] [CommRing O] [StarRing O] {d : ℕ}
    (ρ : O →+* Matrix (Fin d) (Fin d) K) : O →+* Matrix (Fin d) (Fin d) K where
  toFun a := (ρ (star a)).transpose
  map_one' := by simp
  map_mul' a b := by
    rw [star_mul, map_mul, Matrix.transpose_mul]
  map_zero' := by simp
  map_add' a b := by simp [star_add]

theorem conjT_apply {K O : Type} [Field K] [CommRing O] [StarRing O] {d : ℕ}
    (ρ : O →+* Matrix (Fin d) (Fin d) K) (a : O) : conjT ρ a = (ρ (star a)).transpose := rfl

def frobT (k O : Type) [Field k] [CommRing O] (p : ℕ) [Fact p.Prime] [CharP k p] :
    TensorProduct ℤ k O →+* TensorProduct ℤ k O :=
  (Algebra.TensorProduct.map (frobenius k p).toIntAlgHom (AlgHom.id ℤ O)).toRingHom

theorem frobT_tmul (k O : Type) [Field k] [CommRing O] (p : ℕ) [Fact p.Prime] [CharP k p] (c : k)
    (a : O) : frobT k O p (c ⊗ₜ[ℤ] a) = (c ^ p) ⊗ₜ[ℤ] a := by
  simp [frobT, frobenius_def]

def chiT {k O : Type} [Field k] [CommRing O] (χ : O →+* k) : TensorProduct ℤ k O →ₐ[k] k :=
  Algebra.TensorProduct.lift (AlgHom.id k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _)

theorem chiT_tmul {k O : Type} [Field k] [CommRing O] (χ : O →+* k) (c : k) (a : O) :
    chiT χ (c ⊗ₜ[ℤ] a) = c * χ a := by
  simp [chiT]

def idealV {K A V : Type} [Field K] [CommRing A] [AddCommGroup V] [Module K V]
    (τ : A →+* Module.End K V) (J : Ideal A) : Submodule K V :=
  ⨆ a : J, LinearMap.range (τ a)

def FreeAt {K : Type} [Field K] (C : ACurve K) (k : Type) {A V : Type} [Field k] [Algebra k K]
    [CommRing A] [Algebra k A] [AddCommGroup V] [Module K V] (τ : A →+* Module.End K V)
    (L : C.I → AddSubgroup V) (r : ℕ) (i : C.I) : Prop :=
  ∃ (x : Fin r → V) (Θ : (A →ₗ[k] k) → Fin r → (V →ₗ[K] K)),
    (∀ s, x s ∈ L i) ∧
    (∀ l s s' a, Θ l s (τ a (x s')) = if s = s' then algebraMap k K (l a) else 0) ∧
    (∀ l s y, y ∈ L i → C.v i (Θ l s y) ≤ 1) ∧
    ∀ y : V, y ∈ Submodule.span K (Set.range fun q : A × Fin r => τ q.1 (x q.2))

end GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
end
end

