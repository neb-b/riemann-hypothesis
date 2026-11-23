module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedStandardChainStabilizerRadical
section
open scoped Matrix

namespace GlobalTheory.StdChainStab

open Matrix

variable {K : Type} [Field K] {n m : ℕ}

def lowVec (b : Fin n → Fin m) (j : ℕ) (w : Fin n → K) : Prop :=
  ∀ i : Fin n, j ≤ ((b i : Fin m) : ℕ) → w i = 0

theorem lowVec_single (b : Fin n → Fin m) (c : Fin n) :
    lowVec b ((b c : ℕ) + 1) (Pi.single c (1 : K)) := by
  intro i hi
  have : i ≠ c := by rintro rfl; omega
  simp [Pi.single_apply, this]

theorem mulVec_single_apply (z : Matrix (Fin n) (Fin n) K) (i c : Fin n) :
    (z *ᵥ Pi.single c (1 : K)) i = z i c := by
  simp [Matrix.mulVec_single_one]

theorem stab_iff (b : Fin n → Fin m) (z : Matrix (Fin n) (Fin n) K) :
    (∀ j : Fin (m + 1), ∀ w, lowVec b j w → lowVec b j (z *ᵥ w)) ↔
      ∀ i c, b c < b i → z i c = 0 := by
  constructor
  · intro H i c hic
    have h1 := H ⟨(b c : ℕ) + 1, by omega⟩ _ (lowVec_single b c) i (by simp; exact hic)
    rwa [mulVec_single_apply] at h1
  · intro H j w hw i hi
    simp only [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : (j : ℕ) ≤ (b c : ℕ)
    · rw [hw c hc, mul_zero]
    · rw [H i c (by rw [Fin.lt_iff_val_lt_val]; omega), zero_mul]

theorem rad_iff (b : Fin n → Fin m) (z : Matrix (Fin n) (Fin n) K) :
    (∀ j : Fin m, ∀ w, lowVec b (j.succ : ℕ) w → lowVec b (j.castSucc : ℕ) (z *ᵥ w - w)) ↔
      ∀ i c, ¬ b i < b c → z i c = (1 : Matrix (Fin n) (Fin n) K) i c := by
  constructor
  · intro H i c hic
    have h1 := H (b c) _ (by simpa using lowVec_single (K := K) b c) i
      (by simp; exact (not_lt.1 hic))
    rw [Pi.sub_apply, mulVec_single_apply, sub_eq_zero] at h1
    simpa [Pi.single_apply, Matrix.one_apply, eq_comm] using h1
  · intro H j w hw i hi
    have e : z *ᵥ w - w = (z - 1) *ᵥ w := by rw [sub_mulVec, one_mulVec]
    rw [e]
    simp only [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : (j : ℕ) + 1 ≤ (b c : ℕ)
    · rw [hw c (by simpa using hc), mul_zero]
    · simp only [Fin.coe_castSucc] at hi
      rw [Matrix.sub_apply, H i c (by rw [Fin.lt_iff_val_lt_val]; omega), sub_self, zero_mul]

theorem transport (Gm Gi X : Matrix (Fin n) (Fin n) K) (h1 : Gi * Gm = 1) (h2 : Gm * Gi = 1)
    (P : (Fin n → K) → Prop) (Q : (Fin n → K) → (Fin n → K) → Prop) :
    (∀ y, P (Gi *ᵥ y) → Q (Gi *ᵥ y) (Gi *ᵥ (X *ᵥ y))) ↔ ∀ w, P w → Q w ((Gi * X * Gm) *ᵥ w) := by
  constructor
  · intro H w hw
    have hw' : Gi *ᵥ (Gm *ᵥ w) = w := by rw [mulVec_mulVec, h1, one_mulVec]
    have := H (Gm *ᵥ w) (by rw [hw']; exact hw)
    rw [hw'] at this
    simpa [mulVec_mulVec, Matrix.mul_assoc] using this
  · intro H y hy
    have := H _ hy
    simpa [mulVec_mulVec, Matrix.mul_assoc, h2] using this

theorem stdChain_stab_rad : ∀ {K : Type} [Field K] {n m : ℕ} (Y : Fin (m + 1) → Submodule K (Fin n → K)) (d : Fin m → ℕ) (h : ∑ j, d j = n)
    (g : GL (Fin n) K), (∀ (j : Fin (m + 1)) (y : Fin n → K),
      y ∈ Y j ↔ ∀ i : Fin n, (j : ℕ) ≤ ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d h) i : Fin m) : ℕ) →
        (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) i = 0) →
    (∀ x : GL (Fin n) K, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy g (GlobalTheory.SmGL.parab K (GlobalTheory.SmGL.stdBlocks d h)) ↔
        ∀ j, ∀ y ∈ Y j, (x : Matrix (Fin n) (Fin n) K) *ᵥ y ∈ Y j) ∧
    (∀ x : GL (Fin n) K, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy g (GlobalTheory.SmGL.unipRad K (GlobalTheory.SmGL.stdBlocks d h)) ↔
        ∀ j : Fin m, ∀ y ∈ Y j.succ, (x : Matrix (Fin n) (Fin n) K) *ᵥ y - y ∈ Y j.castSucc) := by
  intro K _ n m Y d h g hY
  set b := GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d h) with hb
  have hGi : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGm : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hz : ∀ x : GL (Fin n) K, (((g⁻¹ * x * g : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) *
        (g : Matrix (Fin n) (Fin n) K) := fun x => by simp only [Units.val_mul]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_conjBy, GlobalTheory.SmGL.mem_parab, hz, ← stab_iff]
    refine forall_congr' fun j => ?_
    have := transport (g : Matrix (Fin n) (Fin n) K) ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      (x : Matrix (Fin n) (Fin n) K) hGi hGm (lowVec b j) (fun _ v => lowVec b j v)
    rw [← this]
    refine forall_congr' fun y => ?_
    rw [hY j y, hY j]
    rfl
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_conjBy, GlobalTheory.RadRev.mem_unipRad_entries, hz, ← rad_iff]
    refine forall_congr' fun j => ?_
    have := transport (g : Matrix (Fin n) (Fin n) K) ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      (x : Matrix (Fin n) (Fin n) K) hGi hGm (lowVec b (j.succ : ℕ)) (fun w v => lowVec b (j.castSucc : ℕ) (v - w))
    rw [← this]
    refine forall_congr' fun y => ?_
    rw [hY j.succ y, hY j.castSucc, mulVec_sub]
    rfl

end GlobalTheory.StdChainStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistPlaceDatumParabolicMove
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParabolicDatum

section Ring

variable {κ : Type} [CommRing κ] {a b r : ℕ}

theorem tri_zero {n : ℕ} {g : GL (Fin n) κ} (hg : g ∈ blockTri (blk2 r)) (i j : Fin n) (hi : r ≤ i.val) (hj : j.val < r) :
    g.val i j = 0 := by
  rw [Formalism.L2.DIV.mem_blockTri] at hg
  apply hg
  simp only [Formalism.L2.DIV.blk2, if_pos hj, if_neg (not_lt.mpr hi)]
  exact Nat.zero_lt_one

theorem lowZero_mul {c : ℕ} {x : Matrix (Fin c) (Fin b) κ} {y : Matrix (Fin b) (Fin a) κ}
    (hx : LowZero r x) (hy : LowZero r y) : LowZero r (x * y) := by
  intro i j hi hj
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l.val < r
  · rw [hx i l hi hl, zero_mul]
  · rw [hy l j (not_lt.mp hl) hj, mul_zero]

theorem lowZero_of_tri {n : ℕ} {g : GL (Fin n) κ} (hg : g ∈ blockTri (blk2 r)) : LowZero r g.val := fun i j hi hj => tri_zero hg i j hi hj

theorem topL_eq (ha : r ≤ a) (hb : r ≤ b) (y : Matrix (Fin b) (Fin a) κ) :
    topL r y = y.submatrix (Fin.castLE hb) (Fin.castLE ha) := by
  ext i j
  have hij : i.val < b ∧ j.val < a := ⟨lt_of_lt_of_le i.isLt hb, lt_of_lt_of_le j.isLt ha⟩
  simp only [topL, dif_pos hij, Matrix.submatrix_apply]
  rfl

theorem topL_mul {c : ℕ} (ha : r ≤ a) (hb : r ≤ b) (hc : r ≤ c) (x : Matrix (Fin c) (Fin b) κ)
    {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero r y) : topL r (x * y) = topL r x * topL r y := by
  rw [topL_eq ha hc, topL_eq hb hc, topL_eq ha hb]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hb) (Fin.castLE_injective hb) _ _ ?_ fun l => rfl
  intro l hl
  have hrl : r ≤ l.val := by
    by_contra hlt
    exact hl ⟨⟨l.val, not_le.mp hlt⟩, rfl⟩
  rw [hy l _ hrl (by simp), mul_zero]

theorem topL_tri {n : ℕ} (hn : r ≤ n) {g : GL (Fin n) κ} (hg : g ∈ blockTri (blk2 r)) :
    topL r g.val = (upperLeftBlock hn g).val := by
  rw [topL_eq hn hn, Formalism.L2.DIV.upper_block_val_submatrix hn hg]

theorem det_blockTriangular_eq_mul_diagBlocks {n : ℕ} (hn : r ≤ n) {g : GL (Fin n) κ} (hg : g ∈ blockTri (blk2 r)) :
    Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hn g) * dBlk (blk2 r) 1 g := by
  apply Units.ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    Formalism.L2.DIV.upper_block_val_submatrix hn hg, Formalism.L2.DIV.diag_block_det_val 1 hg,
    Matrix.twoBlockTriangular_det (g : Matrix (Fin n) (Fin n) κ) (fun i : Fin n => i.val < r)
      (fun i hi j hj => tri_zero hg i j (not_lt.mp hi) hj)]
  congr 1
  · let e : Fin r ≃ {i : Fin n // i.val < r} :=
      ⟨fun i => ⟨Fin.castLE hn i, i.isLt⟩, fun i => ⟨i.1.val, i.2⟩, fun _ => rfl, fun _ => rfl⟩
    rw [← Matrix.det_submatrix_equiv_self e]
    rfl
  · let e : {i : Fin n // Formalism.L2.DIV.blk2 r i = 1} ≃ {i : Fin n // ¬ i.val < r} :=
      Equiv.subtypeEquivRight fun i => by
        unfold Formalism.L2.DIV.blk2
        split_ifs with h <;> simp [h]
    rw [← Matrix.det_submatrix_equiv_self e]
    rfl

theorem lowZero_move {G : GL (Fin a) κ} {H : GL (Fin b) κ} (hG : G ∈ blockTri (blk2 r)) (hH : H ∈ blockTri (blk2 r))
    (y : Matrix (Fin b) (Fin a) κ) : LowZero r ((H⁻¹).val * y * G.val) ↔ LowZero r y := by
  constructor
  · intro h
    have hy : y = H.val * ((H⁻¹).val * y * G.val) * (G⁻¹).val := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
        Units.mul_inv, Matrix.mul_one]
    rw [hy]
    exact lowZero_mul (lowZero_mul (lowZero_of_tri hH) h) (lowZero_of_tri (Subgroup.inv_mem _ hG))
  · intro h
    exact lowZero_mul (lowZero_mul (lowZero_of_tri (Subgroup.inv_mem _ hH)) h) (lowZero_of_tri hG)

theorem det_topL_move (ha : r ≤ a) (hb : r ≤ b) {G : GL (Fin a) κ} {H : GL (Fin b) κ} (hG : G ∈ blockTri (blk2 r))
    (hH : H ∈ blockTri (blk2 r)) {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero r y) :
    (topL r ((H⁻¹).val * y * G.val)).det =
      ((Matrix.GeneralLinearGroup.det G * (dBlk (blk2 r) 1 G)⁻¹ *
        ((Matrix.GeneralLinearGroup.det H)⁻¹ * dBlk (blk2 r) 1 H) : κˣ) : κ) * (topL r y).det := by
  have hHi : H⁻¹ ∈ blockTri (blk2 r) := Subgroup.inv_mem _ hH
  have e1 : topL r ((H⁻¹).val * y * G.val) = (upperLeftBlock hb H⁻¹).val * topL r y * (upperLeftBlock ha G).val := by
    rw [topL_mul ha ha hb _ (lowZero_of_tri hG), topL_mul ha hb hb _ hy, topL_tri hb hHi, topL_tri ha hG]
  have key : (Matrix.GeneralLinearGroup.det G * (dBlk (blk2 r) 1 G)⁻¹ *
      ((Matrix.GeneralLinearGroup.det H)⁻¹ * dBlk (blk2 r) 1 H) : κˣ) =
      Matrix.GeneralLinearGroup.det (upperLeftBlock hb H⁻¹) * Matrix.GeneralLinearGroup.det (upperLeftBlock ha G) := by
    have dG := det_blockTriangular_eq_mul_diagBlocks ha hG
    have dH := det_blockTriangular_eq_mul_diagBlocks hb hHi
    have dinv : dBlk (blk2 r) 1 H⁻¹ = (dBlk (blk2 r) 1 H)⁻¹ :=
      Formalism.L2.DIV.extendOne_inv (Formalism.L2.DIV.blkDet (blk2 r) 1) hH
    rw [map_inv, dinv] at dH
    rw [dG, dH, mul_inv_cancel_right, inv_mul_cancel_right, mul_comm]
  rw [e1, Matrix.det_mul, Matrix.det_mul, key, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_det_apply]
  ring

end Ring

theorem omegaQ_parabolic : ∀ (D : D7) (a b r : ℕ), r ≤ a → r ≤ b → ∀ (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (n : ℤ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Q, G PP ∈ blockTri (blk2 r) ∧ H PP ∈ blockTri (blk2 r)) → ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaQ Q r ξ n (fun PP => ((H PP)⁻¹).val * y PP * (G PP).val) = ((∏ PP ∈ Q, (ξ PP (Matrix.GeneralLinearGroup.det (G PP)) * (ξ PP (dBlk (blk2 r) 1 (G PP)))⁻¹ * ((ξ PP (Matrix.GeneralLinearGroup.det (H PP)))⁻¹ * ξ PP (dBlk (blk2 r) 1 (H PP)))) ^ n : ℂˣ) : ℂ) * omegaQ Q r ξ n y := by
  intro D a b r ha hb Q ξ n G H hGH y
  have hdet : ∀ PP ∈ Q, LowZero r (y PP) →
      (topL r (((H PP)⁻¹).val * y PP * (G PP).val)).det =
        ((Matrix.GeneralLinearGroup.det (G PP) * (dBlk (blk2 r) 1 (G PP))⁻¹ *
          ((Matrix.GeneralLinearGroup.det (H PP))⁻¹ * dBlk (blk2 r) 1 (H PP)) : (kP PP)ˣ) : kP PP) *
          (topL r (y PP)).det :=
    fun PP hP hy => det_topL_move ha hb (hGH PP hP).1 (hGH PP hP).2 hy
  have hcond : (∀ PP ∈ Q, LowZero r (((H PP)⁻¹).val * y PP * (G PP).val) ∧
      IsUnit (topL r (((H PP)⁻¹).val * y PP * (G PP).val)).det) ↔
      ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det := by
    refine forall₂_congr fun PP hP => ?_
    rw [lowZero_move (hGH PP hP).1 (hGH PP hP).2 (y PP)]
    refine and_congr_right fun hy => ?_
    rw [hdet PP hP hy]
    exact Units.isUnit_units_mul _ _
  unfold omegaQ
  split_ifs with h1 h2 h2
  · simp only [← Units.val_zpow_eq_zpow_val, ← Units.coe_prod, ← Units.val_mul]
    congr 1
    rw [← Finset.prod_attach Q, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [← mul_zpow]
    congr 1
    have hu : (h1 PP.1 PP.2).2.unit =
        (Matrix.GeneralLinearGroup.det (G PP.1) * (dBlk (blk2 r) 1 (G PP.1))⁻¹ *
          ((Matrix.GeneralLinearGroup.det (H PP.1))⁻¹ * dBlk (blk2 r) 1 (H PP.1))) * (h2 PP.1 PP.2).2.unit := by
      ext
      rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec]
      exact hdet PP.1 PP.2 (h2 PP.1 PP.2).1
    rw [hu]
    simp only [map_mul, map_inv]
  · exact absurd (hcond.mp h1) h2
  · exact absurd (hcond.mpr h2) h1
  · rw [mul_zero]

end GlobalTheory.ParabolicDatum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePrimeLargeAndOneModSixteenQD
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypePrimeSize

theorem k_pow_le_g {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (i : Fin 2) : D.R.k ^ 8 ≤ D.host.g i := by
  obtain ⟨Y, h1, -, -, h4⟩ := P.g_Y
  have hL : 0 ≤ L.sc.L := by
    unfold Scale.L; exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
  have hb : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp hL
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h2 : (D.R.k : ℝ) ≤ D.R.k * L.sc.b := le_mul_of_one_le_right hk hb
  have h3 : (D.R.k : ℝ) ^ 8 ≤ (D.R.k * L.sc.b) ^ 8 := pow_le_pow_left₀ hk h2 8
  have : (D.R.k : ℝ) ^ 8 ≤ D.host.g i := h3.trans (h1.trans (h4 i).1)
  exact_mod_cast this

theorem typePrime_large_and_ok : ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → ∀ k : Fin 2,
    Module.finrank ℚ D.host.E * D.R.r + 1 < D.host.g k ∧
      GlobalTheory.BadShare.PrimeOK (D.host.g k) D.host.q D.host.d := by
  intro D L P i
  have hg := k_pow_le_g P i
  have hE : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have he := D.host.two_le_e
  have h4 : 2 ^ 2 ≤ 2 ^ D.R.e := Nat.pow_le_pow_right (by norm_num) he
  have hf := D.R.f_le_k
  have hfo : D.R.f = 2 * D.R.ord := rfl
  have ho : 2 ^ D.R.e ≤ D.R.ord := Nat.le_of_dvd D.R.ord_pos D.R.toFrame.two_pow_dvd_ord
  have hm := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have ht := D.R.rank_add_five_le
  have hk8 : 8 ≤ D.R.k := by omega
  have hr : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; omega
  have hE' : Module.finrank ℚ D.host.E ≤ 2 * D.R.k := by
    have h2f : D.R.f = 2 * D.R.ord := rfl
    have hfk : D.R.f ≤ D.R.k := hf
    omega
  have hk6 : 8 ^ 6 ≤ D.R.k ^ 6 := Nat.pow_le_pow_left hk8 6
  have hk2 : 8 ^ 2 ≤ D.R.k ^ 2 := Nat.pow_le_pow_left hk8 2
  have hpow : 8 ^ 6 * D.R.k ^ 2 ≤ D.R.k ^ 8 := by
    calc 8 ^ 6 * D.R.k ^ 2 ≤ D.R.k ^ 6 * D.R.k ^ 2 := Nat.mul_le_mul_right _ hk6
      _ = D.R.k ^ 8 := by ring
  have hprod : Module.finrank ℚ D.host.E * D.R.r ≤ 4 * D.R.k ^ 2 := by
    calc Module.finrank ℚ D.host.E * D.R.r ≤ (2 * D.R.k) * (2 * D.R.k) := Nat.mul_le_mul hE' hr
      _ = 4 * D.R.k ^ 2 := by ring
  obtain ⟨hq, hd, hq8, hd16, -⟩ := D.host.hyp
  have hb := D.host.qd_big.1
  refine ⟨by omega, hq, hd, by omega, by omega, by omega, ?_, ?_, by omega⟩
  · have h1 : 5 * 1 ≤ D.R.t * D.R.r := Nat.mul_le_mul (by omega) hr1
    have h2 : 4 * D.R.t * D.R.r = 4 * (D.R.t * D.R.r) := by ring
    exact le_max_of_le_left (by omega)
  · have hc := D.ntypes.g_cond i
    have hdvd : 16 * D.host.q * D.host.d ∣ D.host.QS * D.host.q * D.host.d := by
      have h16 : 16 ∣ D.host.QS := (pow_dvd_pow 2 (by omega : 4 ≤ D.R.e + 2)).trans D.host.tower_dvd
      exact Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right h16 _) _
    refine hdvd.trans ⟨D.host.g i / (D.host.QS * D.host.q * D.host.d), ?_⟩
    have := Nat.div_add_mod (D.host.g i) (D.host.QS * D.host.q * D.host.d)
    omega

end GlobalTheory.TypePrimeSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefFree.AdelCls

open GlobalTheory.Mass

theorem dc_iff {G H : Type} [Group G] [Group H] (f : G →* H) (Γ A L N : Subgroup G) (Q K : Subgroup H)
    (hQ : Γ.map f = Q) (hA : ∀ x, ∃ h ∈ A, f h = x) (hL : ∀ κ, κ ∈ L ↔ κ ∈ A ∧ f κ ∈ K)
    (hN : ∀ h, f h = 1 ↔ h ∈ N) (h h' : G) :
    (∃ x ∈ Q, ∃ k ∈ K, f h' = x * f h * k) ↔ ∃ γ ∈ Γ, ∃ κ ∈ L, ∃ k ∈ N, h' = γ * h * κ * k := by
  constructor
  · rintro ⟨x, hx, k, hk, e⟩
    rw [← hQ] at hx
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨κ, hκA, rfl⟩ := hA k
    refine ⟨γ, hγ, κ, (hL κ).2 ⟨hκA, hk⟩, (γ * h * κ)⁻¹ * h', (hN _).1 ?_,
      (mul_inv_cancel_left (γ * h * κ) h').symm⟩
    simp only [map_mul, map_inv, e, inv_mul_cancel]
  · rintro ⟨γ, hγ, κ, hκ, k, hk, rfl⟩
    refine ⟨f γ, ?_, f κ, ((hL κ).1 hκ).2, ?_⟩
    · rw [← hQ]
      exact Subgroup.mem_map_of_mem f hγ
    · rw [map_mul, map_mul, map_mul, (hN k).2 hk, mul_one]

variable {D : D7}

theorem finU_eq (V : HSp D) {π : GA D V →* HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram}
    (hπ : IsFinProj D.sp.cm.sig V.gram π) (h : GA D V) :
    finU V h = swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π h) := by
  apply Subtype.ext
  rw [coe_finU, coe_swapPts, hπ h]
  rfl

theorem finU_eq_one_iff (V : HSp D) (h : GA D V) : finU V h = 1 ↔ h ∈ GinfC V := by
  have hs : Function.Injective (swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective
  have hb : Function.Injective
      (Formalism.UG.bc (swapAE D) : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →* GL (Fin V.rank) (EAf D)) :=
    Units.map_injective (Matrix.map_injective hs)
  rw [← OneMemClass.coe_eq_one, coe_finU, GinfC, MonoidHom.mem_ker]
  change Formalism.UG.bc (swapAE D) (finHom V h) = 1 ↔ finHom V h = 1
  exact map_eq_one_iff _ hb

theorem exists_fin (V : HSp D) (x : UA D.sp.cm V.gram) : ∃ h ∈ GfC V, finU V h = x := by
  obtain ⟨hsp, hex⟩ := parts_spec (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram
  obtain ⟨y, rfl⟩ := (swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).surjective x
  obtain ⟨g, g1, g2⟩ := hex 1 (HA.mat _ _ _ y)
  have hg : g ∈ HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig V.gram := by
    refine (hsp g).2 ⟨?_, ?_⟩
    · rw [g1]
      exact one_mem _
    · rw [g2]
      exact (y : HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).2
  refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.2 g1, ?_⟩
  apply Subtype.ext
  rw [coe_swapPts, ← g2]
  rfl

theorem mem_levA (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) (κ : GA D V) :
    κ ∈ levA V K ↔ κ ∈ GfC V ∧ finU V κ ∈ K.subgroupOf (UA D.sp.cm V.gram) := by
  simp only [levA, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_finU]

theorem map_rat (V : HSp D) : (GQ V).map (finU V) = UQ D.sp.cm V.gram := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj (F := D.host.F) D.sp.cm.sig V.gram
  have e : finU V = (swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram :
      HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram →* UA D.sp.cm V.gram).comp π :=
    MonoidHom.ext fun h => finU_eq V hπ h
  have h1 : (GQ V).map π = ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram := hπ.map_ratIn
  rw [e, ← Subgroup.map_map, h1]
  exact map_swapPts_rat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram

theorem rat_mem (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) : finU V γ ∈ UQ D.sp.cm V.gram := by
  rw [← map_rat V]
  exact Subgroup.mem_map_of_mem _ hγ

theorem rat_inj (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) (e : finU V γ = 1) : γ = 1 := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj (F := D.host.F) D.sp.cm.sig V.gram
  rw [finU_eq V hπ, MulEquiv.map_eq_one_iff] at e
  exact hπ.injOn (SetLike.mem_coe.2 hγ) (SetLike.mem_coe.2 (Subgroup.one_mem _)) (by rw [e, map_one])

theorem adelic_classes : ∀ (D : D7) (V : HSp D), (∀ x : UA D.sp.cm V.gram, ∃ h ∈ GfC V, finU V h = x) ∧ (∀ γ ∈ GQ V, finU V γ ∈ UQ D.sp.cm V.gram) ∧ (∀ x ∈ UQ D.sp.cm V.gram, ∃ γ ∈ GQ V, finU V γ = x) ∧ (∀ γ ∈ GQ V, finU V γ = 1 → γ = 1) ∧ ∀ (K : Subgroup (GL (Fin V.rank) (EAf D))) (h h' : GA D V), clsA V K h = clsA V K h' ↔ ∃ γ ∈ GQ V, ∃ κ ∈ levA V K, ∃ k ∈ GinfC V, h' = γ * h * κ * k := by
  intro D V
  refine ⟨exists_fin V, rat_mem V, fun x hx => ?_, rat_inj V, fun K h h' => ?_⟩
  · rw [← map_rat V] at hx
    obtain ⟨γ, hγ, e⟩ := Subgroup.mem_map.1 hx
    exact ⟨γ, hγ, e⟩
  · first
      | rw [clsA, clsA, Quotient.eq'', DoubleCoset.rel_iff]
      | (show DoubleCoset.mk _ _ (finU V h) = DoubleCoset.mk _ _ (finU V h') ↔ _
         rw [DoubleCoset.eq])
    exact dc_iff (finU V) (GQ V) (GfC V) (levA V K) (GinfC V) (UQ D.sp.cm V.gram)
      (K.subgroupOf (UA D.sp.cm V.gram)) (map_rat V) (exists_fin V) (mem_levA V K) (finU_eq_one_iff V) h h'

end GlobalTheory.DefFree.AdelCls
end

