module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjFrac

noncomputable section
namespace GlobalTheory.ZM.ProjCoord
variable {R : Type} [CommRing R] {N : ℕ} {A : Type} [CommRing A] {Y : Scheme.{0}}


theorem pt_str (c : R →+* A) (v : Fin (N + 1) → A)
    (hv : Ideal.span (Set.range v) = ⊤) : pt c v hv ≫ PSpace.str R N = spMap c := by
  rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
  congr 1
  ext1
  exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C c v r

set_option backward.isDefEq.respectTransparency false in
theorem secCoord_iff {σ : Type} (e : σ ≃ Fin (N + 1)) (φ : Y ⟶ PSpace R N) (c : R →+* A) (x : Sp A ⟶ Y)
    (hx : (x ≫ φ) ≫ PSpace.str R N = spMap c) (v : σ → A) :
    SecCoord ((O1 R N).pull φ) (fun a => Cartier.secPull (coord R N (e a)) φ) x v ↔
      ∃ hv : Ideal.span (Set.range (v ∘ e.symm)) = ⊤, x ≫ φ = pt c (v ∘ e.symm) hv := by
  have hU : ∀ j : PUnit → PUnit → Fin (N + 1), (((O1 R N).pull φ).pull x).U j = (x ≫ φ) ⁻¹ᵁ chart R N (j ⟨⟩ ⟨⟩) := fun j => by
    rw [pull_U, pull_U]; rfl
  have hval : ∀ (l : Fin (N + 1)) (j : PUnit → PUnit → Fin (N + 1)) (h : (((O1 R N).pull φ).pull x).U j ≤ x ⁻¹ᵁ ((O1 R N).pull φ).U (j PUnit.unit)),
      (x.appLE _ _ h).hom ((Cartier.secPull (coord R N l) φ).f (j PUnit.unit)) = pullRatio (x ≫ φ) _ (j ⟨⟩ ⟨⟩) (hU j).le l := fun l j h => by
    have := resG_secPull_coord φ l (j ⟨⟩) le_rfl
    rw [resG_self] at this
    rw [this, appLE_pullRatio]
  constructor
  · rintro ⟨τ, -, H⟩
    have H' : ∀ (l i : Fin (N + 1)), pullRatio (x ≫ φ) _ i (hU fun _ _ => i).le l =
        fnOn _ (v (e.symm l)) * (show Γ(Sp A, (((O1 R N).pull φ).pull x).U fun _ _ => i) from (τ.s fun _ _ => i).val) := fun l i => by
      have := (hval _ (fun _ _ => i) _).symm.trans (H (e.symm l) (fun _ _ => i) (pull_U _ _ _).le)
      rw [Equiv.apply_symm_apply] at this
      exact this
    have hle : ∀ i, (((O1 R N).pull φ).pull x).U (fun _ _ => i) ≤ spOpen (v (e.symm i)) := fun i => by
      have h1 := H' i i
      rw [pullRatio_self] at h1
      have hu : IsUnit (fnOn ((((O1 R N).pull φ).pull x).U (fun _ _ => i)) (v (e.symm i))) := IsUnit.of_mul_eq_one _ h1.symm
      have := (Sp A).basicOpen_of_isUnit hu
      rw [basicOpen_fnOn] at this
      exact inf_eq_left.1 this
    have hcov : ∀ y : Sp A, ∃ i, y ∈ (((O1 R N).pull φ).pull x).U (fun _ _ => i) := fun y => by
      obtain ⟨i, hi⟩ := exists_mem_chart R N ((x ≫ φ) y)
      exact ⟨i, (hU _).ge hi⟩
    have hv : Ideal.span (Set.range (v ∘ e.symm)) = ⊤ := by
      refine iSup_spOpen_eq_top_iff.1 (top_le_iff.1 fun y _ => ?_)
      obtain ⟨i, hi⟩ := hcov y
      exact Opens.mem_iSup.2 ⟨i, hle i hi⟩
    refine ⟨hv, hom_ext (hx.trans (pt_str c _ hv).symm) fun y => ?_⟩
    obtain ⟨i, hi⟩ := hcov y
    have h2 := (hle i).trans (pt_preimage_chart c _ hv i).ge
    refine ⟨_, hi, i, (hU _).le, h2, fun l => ?_⟩
    have h1 := H' i i
    rw [pullRatio_self] at h1
    have h3 := pullRatio_pt_mul c _ hv i l h2
    rw [H' l i]
    simp only [Function.comp] at h3
    rw [← h3, mul_assoc, ← h1, mul_one]
  · rintro ⟨hv, hp⟩
    have hle : ∀ j : PUnit → PUnit → Fin (N + 1), (((O1 R N).pull φ).pull x).U j ≤ pt c _ hv ⁻¹ᵁ chart R N (j ⟨⟩ ⟨⟩) :=
      fun j => hp ▸ (hU j).le
    have hu : ∀ j : PUnit → PUnit → Fin (N + 1), IsUnit (fnOn ((((O1 R N).pull φ).pull x).U j) (v (e.symm (j ⟨⟩ ⟨⟩)))) := fun j =>
      isUnit_of_basicOpen_eq _ (by
        rw [basicOpen_fnOn]
        exact inf_eq_left.2 ((hle j).trans (pt_preimage_chart c _ hv _).le))
    refine ⟨⟨fun j => (hu j).unit⁻¹⟩, fun i j => ?_, fun a j h => ?_⟩
    · dsimp only
      rw [map_inv, map_inv, ← div_eq_mul_inv, eq_div_iff_mul_eq', inv_mul_eq_iff_eq_mul]
      refine Units.ext ?_
      have hW : (((O1 R N).pull φ).pull x).U i ⊓ (((O1 R N).pull φ).pull x).U j ≤ (x ≫ φ) ⁻¹ᵁ chart R N (i ⟨⟩ ⟨⟩) :=
        inf_le_left.trans (hU i).le
      have hg : ((((O1 R N).pull φ).pull x).g i j).val = pullRatio (x ≫ φ) _ (i ⟨⟩ ⟨⟩) hW (j ⟨⟩ ⟨⟩) := by
        have h1 := restrict_pullback_O1_transition φ (i ⟨⟩) (j ⟨⟩) inf_le_left inf_le_right
        rw [resG_self] at h1
        rw [pull_g]
        have hW' : (((O1 R N).pull φ).pull x).U i ⊓ (((O1 R N).pull φ).pull x).U j ≤
            x ⁻¹ᵁ (((O1 R N).pull φ).U (i ⟨⟩) ⊓ ((O1 R N).pull φ).U (j ⟨⟩)) :=
          le_inf (inf_le_left.trans (pull_U _ _ _).le) (inf_le_right.trans (pull_U _ _ _).le)
        exact (congrArg (x.appLE _ _ hW').hom h1).trans (appLE_pullRatio x hW')
      rw [Units.val_mul, hg, pullRatio_of_eq hp hW (hp ▸ hW)]
      have h3 := pullRatio_pt_mul c _ hv (i ⟨⟩ ⟨⟩) (j ⟨⟩ ⟨⟩) (hp ▸ hW)
      refine Eq.trans (resG_fnOn inf_le_right _) (h3.symm.trans ((mul_comm _ _).trans ?_))
      exact congrArg (· * _) (resG_fnOn inf_le_left _).symm
    · rw [hval, pullRatio_of_eq hp _ (hle j)]
      have h3 := pullRatio_pt_mul c _ hv (j ⟨⟩ ⟨⟩) (e a) (hle j)
      simp only [Function.comp, Equiv.symm_apply_apply] at h3
      change _ = fnOn _ (v a) * ((hu j).unit⁻¹).val
      rw [← h3, mul_assoc, IsUnit.mul_val_inv, mul_one]


omit [CommRing A] in
theorem range_comp_symm {σ τ : Type} (e : σ ≃ τ) (v : σ → A) : Set.range (v ∘ e.symm) = Set.range v :=
  e.symm.surjective.range_comp v

section
variable (K : Type) [Field K] (g n N' : ℕ) {M : ℕ} (e : Ix g (N' ^ 2) ≃ Fin (M + 1))

end

end GlobalTheory.ZM.ProjCoord
