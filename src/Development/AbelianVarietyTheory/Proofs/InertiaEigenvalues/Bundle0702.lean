module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionCompactSupportModuloUnipotent
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExtCpt

open Matrix

section Mat

variable {R : Type} [CommRing R] {m r : ℕ}

theorem eqv_symm_inl_val (a : Fin (m + 1)) : (((eqv m r).symm (Sum.inl a)) : ℕ) = a := by simp [eqv]

theorem eqv_symm_inr_val (b : Fin (r + 1)) : (((eqv m r).symm (Sum.inr b)) : ℕ) = m + 1 + b := by simp [eqv]

theorem unblk_mul (P Q : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) :
    unblk P * unblk Q = unblk (P * Q) := by
  unfold unblk; exact Matrix.submatrix_mul_equiv P Q _ _ _

theorem unblk_one : (unblk (1 : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R)) = 1 := by
  unfold unblk; exact Matrix.submatrix_one_equiv _

theorem fromBlocks_decomp {a b : ℕ} (A : Matrix (Fin a) (Fin a) R) (B : Matrix (Fin a) (Fin b) R)
    (C : Matrix (Fin b) (Fin a) R) (D : Matrix (Fin b) (Fin b) R) (uA cA : Matrix (Fin a) (Fin a) R)
    (uD cD : Matrix (Fin b) (Fin b) R) (hD : IsUnit D.det) (hA : uA * cA = A - B * D⁻¹ * C) (hD' : uD * cD = D) :
    fromBlocks uA (B * D⁻¹ * uD) 0 uD * fromBlocks cA 0 (cD * (D⁻¹ * C)) cD = fromBlocks A B C D := by
  rw [fromBlocks_multiply]
  have h1 : B * D⁻¹ * uD * (cD * (D⁻¹ * C)) = B * D⁻¹ * C := by
    rw [Matrix.mul_assoc (B * D⁻¹) uD, ← Matrix.mul_assoc uD, hD', Matrix.mul_nonsing_inv_cancel_left _ _ hD]
  have h2 : B * D⁻¹ * uD * cD = B := by
    rw [Matrix.mul_assoc (B * D⁻¹) uD, hD', Matrix.nonsing_inv_mul_cancel_right _ _ hD]
  have h3 : uD * (cD * (D⁻¹ * C)) = C := by
    rw [← Matrix.mul_assoc, hD', Matrix.mul_nonsing_inv_cancel_left _ _ hD]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, h1, h2, h3, hD', hA, sub_add_cancel]

end Mat

variable {E : Type} [Field E] [NumberField E] {m r : ℕ}

def gEl (a : GA E (m + 1)) (d : GA E (r + 1)) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) : GA E (m + r + 1 + 1) where
  val := unblk (fromBlocks (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) 0 ((d : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) * Y) d)
  inv := unblk (fromBlocks ((a⁻¹ : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) 0
    (-(Y * ((a⁻¹ : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)))) ((d⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)))
  val_inv := by
    rw [unblk_mul, fromBlocks_multiply, ← unblk_one, ← fromBlocks_one]
    congr 1
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Units.mul_inv, Matrix.mul_neg, Matrix.mul_assoc,
      add_neg_cancel, neg_zero]
  inv_val := by
    rw [unblk_mul, fromBlocks_multiply, ← unblk_one, ← fromBlocks_one]
    congr 1
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Units.inv_mul, Matrix.neg_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc ((d⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) (d : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)),
      Matrix.mul_one, Matrix.one_mul, neg_add_cancel]

theorem coe_gEl (a : GA E (m + 1)) (d : GA E (r + 1)) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) :
    ((gEl a d Y : GA E (m + r + 1 + 1)) : Matrix _ _ (Ad E)) =
      unblk (fromBlocks (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) 0 ((d : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) * Y) d) := rfl

theorem continuous_gEl :
    Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) => gEl z.1 z.2.1 z.2.2 := by
  rw [Units.continuous_iff]
  have ha : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      ((z.1 : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) := Units.continuous_val.comp continuous_fst
  have ha' : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      ((z.1⁻¹ : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) := Units.continuous_coe_inv.comp continuous_fst
  have hd : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      ((z.2.1 : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_snd)
  have hd' : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      ((z.2.1⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) :=
    Units.continuous_coe_inv.comp (continuous_fst.comp continuous_snd)
  have hY : Continuous fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) => z.2.2 :=
    continuous_snd.comp continuous_snd
  have h0 : Continuous fun _ : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) =>
      (0 : Matrix (Fin (m + 1)) (Fin (r + 1)) (Ad E)) := continuous_const
  constructor
  · exact (Continuous.matrix_fromBlocks ha h0 (hd.matrix_mul hY) hd).matrix_submatrix _ _
  · exact (Continuous.matrix_fromBlocks ha' h0 (hY.matrix_mul ha').neg hd').matrix_submatrix _ _

theorem mem_NA_of_blocks (uA : GA E (m + 1)) (uD : GA E (r + 1)) (huA : uA ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)))
    (huD : uD ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1))) (X : Matrix (Fin (m + 1)) (Fin (r + 1)) (Ad E)) (u : GA E (m + r + 1 + 1))
    (hu : (u : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) =
      unblk (fromBlocks (uA : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) X 0 (uD : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)))) :
    u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩ <;> rw [hu]
  · obtain ⟨x, rfl⟩ := (eqv m r).symm.surjective i
    obtain ⟨y, rfl⟩ := (eqv m r).symm.surjective j
    simp only [unblk, submatrix_apply, Equiv.apply_symm_apply]
    rw [Fin.lt_iff_val_lt_val] at hij
    rcases x with a | a <;> rcases y with b | b
    · simp only [eqv_symm_inl_val] at hij
      rw [fromBlocks_apply₁₁]; exact huA.1 a b (Fin.lt_iff_val_lt_val.2 hij)
    · simp only [eqv_symm_inl_val, eqv_symm_inr_val] at hij
      exact absurd hij (by have := a.isLt; omega)
    · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    · simp only [eqv_symm_inr_val] at hij
      rw [fromBlocks_apply₂₂]; exact huD.1 a b (Fin.lt_iff_val_lt_val.2 (by omega))
  · obtain ⟨x, rfl⟩ := (eqv m r).symm.surjective i
    simp only [unblk, submatrix_apply, Equiv.apply_symm_apply]
    rcases x with a | a
    · rw [fromBlocks_apply₁₁]; exact huA.2 a
    · rw [fromBlocks_apply₂₂]; exact huD.2 a

variable [_root_.NumberField.IsTotallyComplex E]

def adOf (z : (Fin (r + 1) → Fin (m + 1) → Cinf E) × (Fin (r + 1) → Fin (m + 1) → Af E)) :
    Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) :=
  fun i j => ((infEq E (z.1 i j), z.2 i j) : InfiniteAdeleRing E × Af E)

theorem continuous_adOf : Continuous (adOf (E := E) (m := m) (r := r)) := by
  refine continuous_matrix fun i j => ?_
  exact ((continuous_infEq E).comp ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))).prodMk
    ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))

end GlobalTheory.SchurExtCpt


open Matrix GlobalTheory.SchurExtCpt in
theorem GlobalTheory.SchurExtCpt.exists_compact_support : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → HasCompactSupport χ → ∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)), schurF β b₁ χ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), u⁻¹ * p ∈ C := by
  intro E _ _ _ m r S β b₁ χ ⟨Cβ, hCβ, hβ⟩ ⟨C₁, hC₁, hb⟩ hχ
  let K : Set (Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) := adOf ''
    (tsupport χ ×ˢ Set.univ.pi fun _ => Set.univ.pi fun _ =>
      (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)))
  have hK : IsCompact K := (hχ.isCompact.prod (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    GroundTheory.Global.isCompact_integralFiniteAdeles E)).image continuous_adOf
  refine ⟨(fun z : GA E (m + 1) × GA E (r + 1) × Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E) => gEl z.1 z.2.1 z.2.2) ''
    (Cβ ×ˢ C₁ ×ˢ K), (hCβ.prod (hC₁.prod hK)).image continuous_gEl, ?_⟩
  intro p hp hF
  by_cases hD : IsUnit (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det
  swap
  · exact absurd (by unfold schurF; rw [if_neg hD]) hF
  unfold schurF at hF
  rw [if_pos hD] at hF
  obtain ⟨⟨⟨-, h2⟩, h3⟩, h4⟩ := (mul_ne_zero_iff.1 hF) |>.imp (mul_ne_zero_iff.1) id |>.imp (fun h => h.imp mul_ne_zero_iff.1 id) id

  have hdet : IsUnit (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det := by
    haveI : Invertible (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).toBlocks₂₂ :=
      Matrix.invertibleOfIsUnitDet _ hD
    have he : (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det =
        (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det *
          (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det := by
      rw [← Matrix.det_submatrix_equiv_self (eqv m r).symm (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))]
      change (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det = _
      rw [← Matrix.fromBlocks_toBlocks (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))),
        Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
      rfl
    have hu := Matrix.isUnits_det_units p
    rw [he] at hu
    exact isUnit_of_mul_isUnit_right hu

  have hsup : mkGL (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := by
    intro w hw
    have hpw := congrArg Units.val (hp.1 w hw)
    apply Units.ext
    change (mkGL (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)).map ((pLoc E w).comp (pFin E)) = 1
    change (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map ((pLoc E w).comp (pFin E)) = 1 at hpw
    rw [coe_mkGL hdet]
    have hbl : (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) = 1 := by
      rw [show (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) =
        blk ((p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map ((pLoc E w).comp (pFin E))) from rfl, hpw]
      exact Matrix.submatrix_one_equiv _
    have hA : (Aof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) = 1 := by
      rw [show (Aof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) =
        ((blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E))).toBlocks₁₁ from rfl,
        hbl, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]
    have hB : (Bof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) = 0 := by
      rw [show (Bof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E)) =
        ((blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map ((pLoc E w).comp (pFin E))).toBlocks₁₂ from rfl,
        hbl, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₂]
    unfold Scof
    rw [Matrix.map_sub _ (map_sub ((pLoc E w).comp (pFin E))), Matrix.map_mul, Matrix.map_mul, hA, hB]
    simp
  obtain ⟨uA, huA, hcA⟩ := hβ _ hsup h2
  obtain ⟨uD, huD, hcD⟩ := hb _ h3

  have hY : Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) ∈ K := by
    unfold chiF at h4
    obtain ⟨h41, h42⟩ := mul_ne_zero_iff.1 h4
    have hint : ∀ i j, pFin E (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
      by_contra hc
      rw [if_neg hc] at h42
      exact h42 rfl
    refine ⟨(fun i j => pInf E (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j),
      fun i j => pFin E (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)), ⟨subset_tsupport _ ?_, ?_⟩, ?_⟩
    · intro h
      apply h41
      rw [h]
      simp
    · simp only [Set.mem_univ_pi]
      exact fun i j => hint i j
    · funext i j
      refine ad_ext ?_ rfl
      show (infEq E).symm (infEq E _) = _
      exact RingEquiv.symm_apply_apply _ _
  refine ⟨p * (gEl (uA⁻¹ * mkGL (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))
    (uD⁻¹ * mkGL (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))
    (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))⁻¹, ?_, ⟨(_, _, _), ⟨hcA, hcD, hY⟩, ?_⟩⟩
  · refine mem_NA_of_blocks uA uD huA huD (Bof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) *
      (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ * (uD : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E))) _ ?_
    have hpU : (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) =
        unblk (fromBlocks (uA : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Bof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) *
          (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ * (uD : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E))) 0
          (uD : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E))) *
        ((gEl (uA⁻¹ * mkGL (Scof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))
          (uD⁻¹ * mkGL (Dof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))))
          (Yof (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) : GA E (m + r + 1 + 1)) :
            Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) := by
      rw [coe_gEl, unblk_mul]
      conv_lhs => rw [← unblk_blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))]
      congr 1
      rw [← Matrix.fromBlocks_toBlocks (blk (p : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))]
      refine (fromBlocks_decomp _ _ _ _ _ _ _ _ hD ?_ ?_).symm
      · rw [← Units.val_mul, mul_inv_cancel_left, coe_mkGL hdet]; try rfl
      · rw [← Units.val_mul, mul_inv_cancel_left, coe_mkGL hD]; try rfl
    rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul]
    exact hpU
  · rw [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]
    rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFunctionWhittakerEquivariant
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurEquiv

open Matrix

section Alg

variable {R : Type} [CommRing R]

def IsUT {n : ℕ} (U : Matrix (Fin n) (Fin n) R) : Prop := (∀ i j : Fin n, j < i → U i j = 0) ∧ ∀ i, U i i = 1

def sd {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : R := ∑ i : Fin n, ∑ j : Fin n, if j.val = i.val + 1 then M i j else 0

theorem superDiag_eq_sd {n : ℕ} (g : GL (Fin n) R) : GlobalTheory.Whittaker.superDiag g = sd (g : Matrix (Fin n) (Fin n) R) := by
  simp [GlobalTheory.Whittaker.superDiag, sd, Finset.sum_filter]

theorem det_of_isUT {n : ℕ} {U : Matrix (Fin n) (Fin n) R} (hU : IsUT U) : U.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j h => hU.1 i j h)]
  simp [hU.2]

variable {m r : ℕ}

theorem eqv_symm_inl (i : Fin (m + 1)) : ((eqv m r).symm (Sum.inl i)).val = i.val := by simp [eqv]
theorem eqv_symm_inr (j : Fin (r + 1)) : ((eqv m r).symm (Sum.inr j)).val = m + 1 + j.val := by simp [eqv]

theorem blk_mul (M N : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : blk (M * N) = blk M * blk N :=
  (Matrix.submatrix_mul_equiv M N _ (eqv m r).symm _).symm

theorem blk_eq (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    blk M = fromBlocks (Aof M) (Bof M) (Cof M) (Dof M) := (fromBlocks_toBlocks _).symm

variable {U : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R}

theorem Cof_of_isUT (hU : IsUT U) : Cof U = 0 := by
  ext i j
  apply hU.1
  rw [Fin.lt_def, eqv_symm_inl, eqv_symm_inr]
  omega

theorem Aof_isUT (hU : IsUT U) : IsUT (Aof U) :=
  ⟨fun i j h => hU.1 _ _ (by rw [Fin.lt_def, eqv_symm_inl, eqv_symm_inl]; exact h), fun i => hU.2 _⟩

theorem Dof_isUT (hU : IsUT U) : IsUT (Dof U) :=
  ⟨fun i j h => hU.1 _ _ (by rw [Fin.lt_def, eqv_symm_inr, eqv_symm_inr]; rw [Fin.lt_def] at h; omega), fun i => hU.2 _⟩

variable (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R)

theorem blk_UM (hU : IsUT U) : blk (U * M) = fromBlocks (Aof U * Aof M + Bof U * Cof M) (Aof U * Bof M + Bof U * Dof M)
    (Dof U * Cof M) (Dof U * Dof M) := by
  rw [blk_mul, blk_eq U, blk_eq M, Cof_of_isUT hU, fromBlocks_multiply]
  simp

theorem Aof_mul (hU : IsUT U) : Aof (U * M) = Aof U * Aof M + Bof U * Cof M := by
  rw [Aof, blk_UM M hU, toBlocks_fromBlocks₁₁]
theorem Bof_mul (hU : IsUT U) : Bof (U * M) = Aof U * Bof M + Bof U * Dof M := by
  rw [Bof, blk_UM M hU, toBlocks_fromBlocks₁₂]
theorem Cof_mul (hU : IsUT U) : Cof (U * M) = Dof U * Cof M := by
  rw [Cof, blk_UM M hU, toBlocks_fromBlocks₂₁]
theorem Dof_mul (hU : IsUT U) : Dof (U * M) = Dof U * Dof M := by
  rw [Dof, blk_UM M hU, toBlocks_fromBlocks₂₂]

theorem isUnit_Dof_mul_iff (hU : IsUT U) : IsUnit (Dof (U * M)).det ↔ IsUnit (Dof M).det := by
  rw [Dof_mul M hU, det_mul, det_of_isUT (Dof_isUT hU), one_mul]

theorem Yof_mul (hU : IsUT U) : Yof (U * M) = Yof M := by
  have hu : IsUnit (Dof U).det := by rw [det_of_isUT (Dof_isUT hU)]; exact isUnit_one
  rw [Yof, Yof, Dof_mul M hU, Cof_mul M hU, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (Dof U)⁻¹,
    nonsing_inv_mul _ hu, Matrix.one_mul]

theorem Scof_mul (hU : IsUT U) (hD : IsUnit (Dof M).det) : Scof (U * M) = Aof U * Scof M := by
  have hu : IsUnit (Dof U).det := by rw [det_of_isUT (Dof_isUT hU)]; exact isUnit_one
  have h1 : (Dof M)⁻¹ * (Dof U)⁻¹ * (Dof U * Cof M) = (Dof M)⁻¹ * Cof M := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Dof U)⁻¹, nonsing_inv_mul _ hu, Matrix.one_mul]
  rw [Scof, Scof, Aof_mul M hU, Bof_mul M hU, Dof_mul M hU, Cof_mul M hU, Matrix.mul_inv_rev, Matrix.mul_assoc _ _ (Dof U * Cof M), h1]
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Dof M) (Dof M)⁻¹ (Cof M), mul_nonsing_inv _ hD, Matrix.one_mul]
  abel

theorem Xof_mul (hU : IsUT U) (hD : IsUnit (Dof M).det) :
    Xof (U * M) = Aof U * Xof M * (Dof U)⁻¹ + Bof U * (Dof U)⁻¹ := by
  rw [Xof, Xof, Bof_mul M hU, Dof_mul M hU, Matrix.mul_inv_rev]
  simp only [Matrix.add_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Dof M) (Dof M)⁻¹ (Dof U)⁻¹, mul_nonsing_inv _ hD, Matrix.one_mul]

theorem inv_first_column_of_upper_triangular {n : ℕ} {V : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hV : IsUT V) (l : Fin (n + 1)) :
    V⁻¹ l 0 = if l = 0 then 1 else 0 := by
  have hu : IsUnit V.det := by rw [det_of_isUT hV]; exact isUnit_one
  have h := congrFun (congrFun (nonsing_inv_mul V hu) l) 0
  rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (n + 1)), hV.2, mul_one, Matrix.one_apply] at h
  · exact h
  · intro k _ hk; rw [hV.1 k 0 (Fin.pos_iff_ne_zero.2 hk), mul_zero]
  · simp

theorem mul_first_column_of_unit_column {n k : ℕ} (N : Matrix (Fin k) (Fin (n + 1)) R) {P : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hP : ∀ l, P l 0 = if l = 0 then 1 else 0) (i : Fin k) : (N * P) i 0 = N i 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp [hP]
  · intro l _ hl; simp [hP, hl]
  · simp

theorem lastRow_mul {n k : ℕ} {Q : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hQ : IsUT Q) (N : Matrix (Fin (n + 1)) (Fin k) R)
    (j : Fin k) : (Q * N) (Fin.last n) j = N (Fin.last n) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n), hQ.2, one_mul]
  · intro l _ hl; rw [hQ.1 _ _ (Fin.lt_last_iff_ne_last.2 hl), zero_mul]
  · simp

theorem Xof_mul_entry (hU : IsUT U) (hD : IsUnit (Dof M).det) :
    Xof (U * M) (Fin.last m) 0 = Xof M (Fin.last m) 0 + Bof U (Fin.last m) 0 := by
  rw [Xof_mul M hU hD, Matrix.add_apply, mul_first_column_of_unit_column _ (inv_first_column_of_upper_triangular (Dof_isUT hU)), mul_first_column_of_unit_column _ (inv_first_column_of_upper_triangular (Dof_isUT hU)),
    lastRow_mul (Aof_isUT hU)]

theorem sd_blocks (U : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    sd U = sd (Aof U) + Bof U (Fin.last m) 0 + sd (Dof U) := by
  have e : ∀ f : Fin (m + r + 1 + 1) → R, ∑ i, f i = ∑ a, f ((eqv m r).symm a) := fun f =>
    (Equiv.sum_comp (eqv m r).symm f).symm
  rw [sd, e]
  simp only [Fintype.sum_sum_type]
  simp_rw [e, Fintype.sum_sum_type, eqv_symm_inl, eqv_symm_inr]
  have h2 : ∑ i : Fin (m + 1), ∑ j : Fin (r + 1),
      (if m + 1 + j.val = i.val + 1 then U ((eqv m r).symm (Sum.inl i)) ((eqv m r).symm (Sum.inr j)) else 0) =
      Bof U (Fin.last m) 0 := by
    rw [Finset.sum_eq_single (Fin.last m), Finset.sum_eq_single (0 : Fin (r + 1))]
    · rw [if_pos (by simp)]; rfl
    · intro j _ hj; rw [if_neg]; intro h; apply hj; ext; simp at h ⊢; omega
    · simp
    · intro i _ hi; refine Finset.sum_eq_zero fun j _ => ?_; rw [if_neg]; intro h; apply hi; ext; simp; omega
    · simp
  have h3 : ∑ i : Fin (r + 1), ∑ j : Fin (m + 1),
      (if j.val = m + 1 + i.val + 1 then U ((eqv m r).symm (Sum.inr i)) ((eqv m r).symm (Sum.inl j)) else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]; omega
  have h4 : ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
      (if m + 1 + j.val = m + 1 + i.val + 1 then U ((eqv m r).symm (Sum.inr i)) ((eqv m r).symm (Sum.inr j)) else 0) =
      sd (Dof U) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j.val = i.val + 1
    · rw [if_pos (by omega), if_pos h]; rfl
    · rw [if_neg (by omega), if_neg h]
  simp only [Finset.sum_add_distrib]
  rw [h2, h3, h4, zero_add]
  rfl

end Alg

end GlobalTheory.SchurEquiv

namespace GlobalTheory.SchurEquiv

open Matrix

section Adelic

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem mkGL_mem_NA {V : Matrix (Fin k) (Fin k) (Ad E)} (hV : IsUT V) : mkGL V ∈ GlobalTheory.JSW.NA (E := E) (a := k) := by
  have hu : IsUnit V.det := by rw [det_of_isUT hV]; exact isUnit_one
  refine ⟨fun i j h => ?_, fun i => ?_⟩ <;> rw [coe_mkGL hu]
  · exact hV.1 i j h
  · exact hV.2 i

theorem mkGL_mul {V S : Matrix (Fin k) (Fin k) (Ad E)} (hV : IsUT V) (hS : IsUnit S.det) :
    mkGL (V * S) = mkGL V * mkGL S := by
  have hu : IsUnit V.det := by rw [det_of_isUT hV]; exact isUnit_one
  have hVS : IsUnit (V * S).det := by rw [det_mul]; exact hu.mul hS
  apply Units.ext
  rw [Units.val_mul, coe_mkGL hVS, coe_mkGL hu, coe_mkGL hS]

theorem psi_add (a b : Ad E) : psi (a + b) = psi a * psi b := by
  simp [psi, AddChar.map_add_eq_mul]

theorem psiN_mkGL {V : Matrix (Fin k) (Fin k) (Ad E)} (hV : IsUT V) : GlobalTheory.JSW.psiN (mkGL V) = psi (sd V) := by
  have hu : IsUnit V.det := by rw [det_of_isUT hV]; exact isUnit_one
  rw [GlobalTheory.JSW.psiN, superDiag_eq_sd, coe_mkGL hu]; rfl

theorem isUnit_Scof {m r : ℕ} (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (hM : IsUnit M.det)
    (hD : IsUnit (Dof M).det) : IsUnit (Scof M).det := by
  letI := (Dof M).invertibleOfIsUnitDet hD
  have h1 : M.det = (Dof M).det * (Scof M).det := by
    have e : (blk M).det = M.det := Matrix.det_submatrix_equiv_self _ _
    rw [← e, blk_eq, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]; rfl
  rw [h1] at hM
  exact isUnit_of_mul_isUnit_right hM

end Adelic

theorem schurF_equivariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), ∀ g, b₁ (u * g) = GlobalTheory.JSW.psiN u * b₁ g) → ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, schurF β b₁ χ (u * g) = GlobalTheory.JSW.psiN u * schurF β b₁ χ g := by
  intro E _ _ _ m r β b₁ χ hβ hb u hu g
  have hU : IsUT (u : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) := hu
  have hM : IsUnit (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  set M := (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) with hMdef
  set U := (u : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) with hUdef
  unfold schurF
  rw [Units.val_mul]
  by_cases hD : IsUnit (Dof M).det
  · rw [if_pos ((isUnit_Dof_mul_iff M hU).2 hD), if_pos hD, Xof_mul_entry M hU hD, Scof_mul M hU hD, Dof_mul M hU,
      Yof_mul M hU, mkGL_mul (Aof_isUT hU) (isUnit_Scof M hM hD), mkGL_mul (Dof_isUT hU) hD,
      hβ _ (mkGL_mem_NA (Aof_isUT hU)), hb _ (mkGL_mem_NA (Dof_isUT hU)), psiN_mkGL (Aof_isUT hU),
      psiN_mkGL (Dof_isUT hU)]
    have h : GlobalTheory.JSW.psiN u = psi (sd (Aof U)) * psi (Bof U (Fin.last m) 0) * psi (sd (Dof U)) := by
      rw [GlobalTheory.JSW.psiN, superDiag_eq_sd, sd_blocks, ← psi_add, ← psi_add]; rfl
    rw [h, psi_add]; ring
  · rw [if_neg (mt (isUnit_Dof_mul_iff M hU).1 hD), if_neg hD, mul_zero]

end GlobalTheory.SchurEquiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitRowPrimeOf
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX.SplitDecl

theorem splitRowPrime_of {D : D7} {L : SizeData₂ D} {X : KillingConditions.HubData D} (i : D.nd.Loc)
    (hg : D.nd.l i ∉ TwistedPlaces.gset D) (hr : KillingConditions.RangeAD L X.exc (D.nd.l i)) (hs : TwistedPlaces.SplitK D (D.nd.l i)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) := by
  have hp := (D.nd.lPrime i).out
  have h5 : 5 ≤ D.nd.l i := by
    have h2 := hp.two_le
    have h3 : D.nd.l i ≠ 3 := fun e => hr.1 (Or.inr e)
    have h2' : D.nd.l i ≠ 2 := fun e => hr.1 (Or.inl (e ▸ D.host.toHostRaw.two_mem_small))
    have h4 : D.nd.l i ≠ 4 := fun e => by rw [e] at hp; norm_num at hp
    omega
  refine ⟨hp, h5, fun e => hr.2.1 (Or.inl e), fun e => hr.2.1 (Or.inr e), fun k e => hg ?_, hs⟩
  rw [e]
  fin_cases k <;> simp [TwistedPlaces.gset]

theorem main : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D),
    GlobalTheory.HubX.Canon L HW R X → ∀ (hJ : AdmissibleParameterJ.ConclusionJa D) (i : D.nd.Loc), TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D →
    KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) →
    EmbeddingTypes.hypDecl i (X.dc i) (Exists.choose hJ) ∧
      ∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1 := by
  intro D L HW R X h hJ i _ hg hr hs
  have hsp := splitRowPrime_of (L := L) (X := X) i hg hr hs
  refine ⟨GlobalTheory.HubX.Check.decl h hJ i hg hr hs ((_root_.GlobalTheory.SplitDecl.main D i hJ.choose hsp).1), ?_⟩
  intro v hv
  exact (GlobalTheory.SplitPlaces.placesSplit D.host (D.nd.l i) hsp v hv).1

end GlobalTheory.HubX.SplitDecl
end

