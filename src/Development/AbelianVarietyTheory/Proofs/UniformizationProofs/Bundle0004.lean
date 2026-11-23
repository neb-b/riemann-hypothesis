module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatCokerOfInjectiveModMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatCokerOfComplexExactModMaximalIdeal
section
open CategoryTheory CategoryTheory.Limits TensorProduct

namespace GlobalTheory

theorem flat_coker_of_complex_exact_mod_maximalIdeal : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] (D : ℕ → Type) [∀ i, AddCommGroup (D i)] [∀ i, Module A (D i)] [∀ i, Module.Finite A (D i)] [∀ i, Module V (D i)] [∀ i, IsScalarTower V A (D i)] [∀ i, Module.Flat V (D i)] (d : ∀ i, D (i + 1) →ₗ[A] D i), (∀ i x, d i (d (i + 1) x) = 0) → (∃ n, ∀ i, n < i → Subsingleton (D i)) → (∀ i (x : D (i + 1)), d i x ∈ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A (D i)) → x ∈ LinearMap.range (d (i + 1)) ⊔ (((IsLocalRing.maximalIdeal V).map (algebraMap V A)) • ⊤ : Submodule A (D (i + 1)))) → Module.Flat V (D 0 ⧸ LinearMap.range (d 0)) := by
  intro V A _ _ _ _ _ _ _ _ D _ _ _ _ _ _ d hdd _ hex
  set J : Ideal A := (IsLocalRing.maximalIdeal V).map (algebraMap V A) with hJ
  have hle : LinearMap.range (d 1) ≤ LinearMap.ker (d 0) := by
    rintro _ ⟨x, rfl⟩
    exact hdd 0 x
  let u : (D 1 ⧸ LinearMap.range (d 1)) →ₗ[A] D 0 := (LinearMap.range (d 1)).liftQ (d 0) hle
  have hr : LinearMap.range u = LinearMap.range (d 0) := Submodule.range_liftQ _ _ _
  have h := _root_.GlobalTheory.flat_coker_of_injective_mod_maximalIdeal V A (D 1 ⧸ LinearMap.range (d 1)) (D 0) u (by
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hy : y ∈ LinearMap.range (d 1) ⊔ (J • ⊤ : Submodule A (D 1)) := hex 0 y hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    have ha0 : (Submodule.Quotient.mk a : D 1 ⧸ LinearMap.range (d 1)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ha
    rw [Submodule.Quotient.mk_add, ha0, zero_add]
    have : (LinearMap.range (d 1)).mkQ b ∈ (J • ⊤ : Submodule A (D 1)).map (LinearMap.range (d 1)).mkQ :=
      Submodule.mem_map_of_mem hb
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this)
  rwa [hr] at h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OverPointsExtOfInjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.over_points_ext_of_injective (S : Scheme.{0}) (G : Over S) [IsSeparated G.hom]
    (W F : Type) [CommRing W] [CommRing F] (φ : W →+* F) (hφ : Function.Injective φ)
    (p : Spec (CommRingCat.of W) ⟶ S) (y y' : Over.mk p ⟶ G)
    (h : (Spec.map (CommRingCat.ofHom φ)) ≫ y.left = (Spec.map (CommRingCat.ofHom φ)) ≫ y'.left) :
    y = y' := by
  let d : Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ p) ⟶ Over.mk p :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl
  have hd : d ≫ y = d ≫ y' := by
    ext1
    simpa [d] using h
  let l := equalizer.lift d hd
  have hl : l ≫ equalizer.ι y y' = d := equalizer.lift_ι d hd
  have hfac : l.left ≫ (equalizer.ι y y').left = Spec.map (CommRingCat.ofHom φ) := by
    rw [← Over.comp_left, hl]
    rfl
  have hdom : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) :=
    (_root_.GlobalTheory.schemeDominant_specMap_iff _).2 (by simpa using hφ)
  have hdomι : IsSchemeTheoreticallyDominant (equalizer.ι y y').left :=
    ⟨eq_bot_iff.2 ((Scheme.Hom.le_ker_comp l.left _).trans (by rw [hfac, hdom.ker_eq_bot]))⟩
  have hiso : IsIso (equalizer.ι y y').left :=
    _root_.GlobalTheory.isIso_of_isClosedImmersion_of_schemeDominant _
  ext1
  rw [← cancel_epi (equalizer.ι y y').left, ← Over.comp_left, ← Over.comp_left,
    equalizer.condition]

end GlobalTheory
end

