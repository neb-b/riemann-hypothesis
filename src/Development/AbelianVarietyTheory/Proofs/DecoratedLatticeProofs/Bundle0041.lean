module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0040

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb
section
noncomputable section

open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition

namespace GlobalTheory.LowerHecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

def lowU (ν : Matrix D A k) : GL (A ⊕ D) k where
  val := fromBlocks 1 0 ν 1
  inv := fromBlocks 1 0 (-ν) 1
  val_inv := by rw [fromBlocks_multiply]; simp
  inv_val := by rw [fromBlocks_multiply]; simp

theorem val_lowU (ν : Matrix D A k) : (lowU ν).1 = fromBlocks 1 0 ν 1 := rfl


open Classical in
def blockDet (j : GL (A ⊕ D) k) : kˣ :=
  if h : j.1.toBlocks₂₂.det ≠ 0 then Units.mk0 _ h else 1

theorem val_emb_one (m : GL D k) :
    (emb₂ k (Equiv.refl (A ⊕ D)) (1, m)).1 = fromBlocks 1 0 0 m.1 := by
  classical
  ext (i | i) (j | j) <;> simp [emb₂, leviEmb, leviTwo, two, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.blockDiagonal'_apply]

theorem blockDet_lowU_emb (ν : Matrix D A k) (m : GL D k) :
    blockDet (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, m)) = GeneralLinearGroup.det m := by
  have h : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, m)).1.toBlocks₂₂ = m.1 := by
    rw [Units.val_mul, val_emb_one, val_lowU, fromBlocks_multiply]; simp
  have h0 : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, m)).1.toBlocks₂₂.det ≠ 0 := by
    rw [h]; exact (GeneralLinearGroup.det m).ne_zero
  rw [blockDet, dite_eq_left h0]; ext; rw [Units.val_mk0, h, GeneralLinearGroup.val_det_apply]

theorem emb_mul_lowU (m : GL D k) (ν : Matrix D A k) :
    emb₂ k (Equiv.refl (A ⊕ D)) (1, m) * lowU ν = lowU (m.1 * ν) * emb₂ k (Equiv.refl (A ⊕ D)) (1, m) := by
  ext1
  rw [Units.val_mul, Units.val_mul, val_emb_one, val_lowU, val_lowU, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem emb_mul_emb (m m' : GL D k) :
    emb₂ k (Equiv.refl (A ⊕ D)) (1, m) * emb₂ k (Equiv.refl (A ⊕ D)) (1, m') =
      emb₂ k (Equiv.refl (A ⊕ D)) (1, m * m') := by
  rw [← map_mul]; simp

theorem mtor_eq (ϖ : kˣ) (e : D → ℤ) :
    (mtor ϖ e : GL (A ⊕ D) k) = emb₂ k (Equiv.refl (A ⊕ D)) (1, torusElt k D ϖ e) := by
  ext1
  rw [val_emb_one, mtor, val_torusElt, val_torusElt]
  ext (i | i) (j | j) <;> simp [diagonal_apply, Matrix.one_apply]

theorem inv_lowU (ν : Matrix D A k) : (lowU ν)⁻¹ = lowU (-ν) := Units.ext rfl

theorem lowU_mem {ν : Matrix D A k} (h : ∀ i a, valuation k (ν i a) < 1) : lowU ν ∈ parahoric k A D := by
  rw [mem_parahoric, GlobalTheory.StepData.mem_KO]
  refine ⟨⟨?_, ?_⟩, fun i j => by simpa [val_lowU] using h i j⟩
  · rintro (i | i) (j | j) <;> simp only [val_lowU, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply]
    · split_ifs <;> simp
    · exact zero_mem _
    · exact (h i j).le
    · split_ifs <;> simp
  · rw [inv_lowU]
    rintro (i | i) (j | j) <;> simp only [val_lowU, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply, Matrix.neg_apply]
    · split_ifs <;> simp
    · exact zero_mem _
    · exact neg_mem (h i j).le
    · split_ifs <;> simp

theorem emb_mem {κ : GL D k} (h : κ ∈ KO k D) : emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) ∈ parahoric k A D := by
  rw [mem_parahoric, GlobalTheory.StepData.mem_KO]
  obtain ⟨h1, h2⟩ := GlobalTheory.StepData.mem_KO.1 h
  have hinv : (emb₂ k (Equiv.refl (A ⊕ D)) (1, κ))⁻¹ = emb₂ k (Equiv.refl (A ⊕ D)) (1, κ⁻¹) := by
    rw [← map_inv]; simp
  refine ⟨⟨?_, ?_⟩, fun i j => by simp [val_emb_one]⟩
  · rintro (i | i) (j | j) <;> simp only [val_emb_one, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply]
    · split_ifs <;> simp
    · exact zero_mem _
    · exact zero_mem _
    · exact h1 i j
  · rw [hinv]
    rintro (i | i) (j | j) <;> simp only [val_emb_one, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply]
    · split_ifs <;> simp
    · exact zero_mem _
    · exact zero_mem _
    · exact h2 i j


variable (k D) in
def mLat : AddSubgroup (D → k) where
  carrier := {v | ∀ i, valuation k (v i) < 1}
  add_mem' ha hb i := by simpa using Valuation.map_add_lt _ (ha i) (hb i)
  zero_mem' i := by simp
  neg_mem' ha i := by simpa using ha i

def preLat (m : Matrix D D k) : AddSubgroup (D → k) := (mLat k D).comap (Matrix.mulVecLin m).toAddMonoidHom

theorem mem_mLat {v : D → k} : v ∈ mLat k D ↔ ∀ i, valuation k (v i) < 1 := Iff.rfl

theorem mem_preLat {m : Matrix D D k} {v : D → k} : v ∈ preLat m ↔ m.mulVec v ∈ mLat k D := Iff.rfl

end GlobalTheory.LowerHecke

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParahoricAndIntegralGLDoubleCosetReps
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ParHeckeReps

theorem exists_reps_both : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D],
    (∀ g : GL (A ⊕ D) k, ∃ R d, IsReps g R d) ∧ ∀ g : GL D k, ∃ R, IsRepsK g R :=
  fun _ _ _ _ _ _ _ _ _ _ _ => ⟨fun g => Model.exists_isReps g, fun g => Model.exists_isRepsK g⟩

end GlobalTheory.ParHeckeReps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FdegHCRowsMulSuperfactorialLeVandermonde
section
open Formalism.BasicNotions

namespace GlobalTheory.FdegRowsBound

open Finset

theorem pairs_append {p q : ℕ} (g : Fin (p + q) → Fin (p + q) → ℝ) :
    ∏ a : Fin (p + q), ∏ b ∈ univ.filter (fun b => a < b), g a b =
      (∏ i : Fin p, ∏ j ∈ univ.filter (fun j => i < j), g (Fin.castAdd q i) (Fin.castAdd q j)) *
      (∏ i : Fin p, ∏ j : Fin q, g (Fin.castAdd q i) (Fin.natAdd p j)) *
      (∏ i : Fin q, ∏ j ∈ univ.filter (fun j => i < j), g (Fin.natAdd p i) (Fin.natAdd p j)) := by
  simp only [Finset.prod_filter, Fin.prod_univ_add, Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd]
  have h1 : ∀ (i : Fin p) (j : Fin q), (i : ℕ) < p + (j : ℕ) := fun i j => by omega
  have h2 : ∀ (i : Fin q) (j : Fin p), ¬ p + (i : ℕ) < (j : ℕ) := fun i j => by omega
  have h3 : ∀ (i j : Fin q), (p + (i : ℕ) < p + (j : ℕ)) ↔ ((i : ℕ) < (j : ℕ)) := fun i j => by omega
  simp only [h1, h2, h3, if_true, if_false, Finset.prod_const_one, mul_one, one_mul, Finset.prod_mul_distrib]

theorem pairs_cast {n n' : ℕ} (h : n = n') (f : Fin n' → Fin n' → ℝ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b => a < b), f (Fin.cast h a) (Fin.cast h b) =
      ∏ a : Fin n', ∏ b ∈ univ.filter (fun b => a < b), f a b := by
  subst h; rfl

theorem den_eq (n : ℕ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      Formalism.MainNotions.StandardLattice.facProd n := by
  unfold Formalism.MainNotions.StandardLattice.facProd
  rcases n with _ | m
  · simp
  have h := Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) m
  rw [Matrix.det_vandermonde, ← Nat.prod_range_succ_factorial, Nat.cast_prod] at h
  simp only [Finset.filter_lt_eq_Ioi]
  rw [← h]

theorem facProd_pos (n : ℕ) : 0 < Formalism.MainNotions.StandardLattice.facProd n := by
  unfold Formalism.MainNotions.StandardLattice.facProd
  exact Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i

theorem anti_of {K n : ℕ} (hn : K + 1 = n) (u : Fin n → ℚ) (v : Fin K → ℚ)
    (h1 : ∀ i : Fin K, v i < u ⟨i.1, by omega⟩) (h2 : ∀ i : Fin K, u ⟨i.1 + 1, by omega⟩ < v i) :
    StrictAnti u := by
  subst hn
  exact Fin.strictAnti_iff_succ_lt.2 fun i => (h2 i).trans (h1 i)

theorem mono_of {m : ℕ} (f : Fin m → ℚ) (h : ∀ j : Fin m, ∀ hj : j.1 + 1 < m, f j < f ⟨j.1 + 1, hj⟩) :
    StrictMono f := by
  rcases m with _ | m
  · exact fun a => a.elim0
  · exact Fin.strictMono_iff_lt_succ.2 fun i => h (Fin.castSucc i) (by simp)

theorem vand_cast {K : ℕ} (u : Fin (K + 1) → ℝ) :
    Formalism.MainNotions.StandardLattice.vand u = ∏ i : Fin K, ∏ j : Fin K,
      (if i ≤ j then u (Fin.castSucc i) - u (Fin.succ j) else 1) := by
  unfold Formalism.MainNotions.StandardLattice.vand
  rw [Fin.prod_univ_castSucc]
  have hlast : ∏ b ∈ univ.filter (fun b => Fin.last K < b), (u (Fin.last K) - u b) = 1 := by
    apply Finset.prod_eq_one
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact absurd hb (not_lt.2 (Fin.le_last b))
  rw [hlast, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_filter, Fin.prod_univ_succ]
  simp [Fin.castSucc_lt_succ_iff]

theorem interlace_bound {K n : ℕ} (hn : K + 1 = n) (u : Fin n → ℝ) (v : Fin K → ℝ)
    (h1 : ∀ i : Fin K, v i < u ⟨i.1, by omega⟩) (h2 : ∀ i : Fin K, u ⟨i.1 + 1, by omega⟩ < v i)
    (h3 : ∀ i : Fin K, 1 ≤ u ⟨i.1, by omega⟩ - u ⟨i.1 + 1, by omega⟩) :
    ∏ a : Fin K, ∏ b ∈ univ.filter (fun b => a < b), |v a - v b| ≤ Formalism.MainNotions.StandardLattice.vand u := by
  subst hn
  have hu : StrictAnti u := Fin.strictAnti_iff_succ_lt.2 fun i => (h2 i).trans (h1 i)
  rw [vand_cast]
  simp only [Finset.prod_filter]
  apply Finset.prod_le_prod₀
  · intro i _
    exact Finset.prod_nonneg fun j _ => by split_ifs <;> positivity
  intro i _
  apply Finset.prod_le_prod₀
  · intro j _; split_ifs <;> positivity
  intro j _
  by_cases hij : i < j
  · have hle : i ≤ j := hij.le
    simp only [hij, hle, if_true]
    have hsj : Fin.succ i ≤ Fin.castSucc j := by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.coe_castSucc]; exact hij
    have a1 := h1 i
    have a2 := h2 j
    have a3 := h1 j
    have a4 := h2 i
    have a5 := hu.antitone hsj
    have e1 : u ⟨i.1, by omega⟩ = u (Fin.castSucc i) := rfl
    have e2 : u ⟨j.1 + 1, by omega⟩ = u (Fin.succ j) := rfl
    have e3 : u ⟨j.1, by omega⟩ = u (Fin.castSucc j) := rfl
    have e4 : u ⟨i.1 + 1, by omega⟩ = u (Fin.succ i) := rfl
    rw [abs_of_pos (by linarith)]
    linarith
  · simp only [hij, if_false]
    by_cases hle : i ≤ j
    · have : i = j := le_antisymm hle (not_lt.1 hij)
      subst this
      simp only [hle, if_true]
      exact h3 i
    · simp [hle]

theorem lamSH_congr (R : Ranks) (P Q : HCParam R) (hv : Q.v = P.v) (hb : Q.b = P.b) :
    Formalism.MainNotions.S.lamSH R P = Formalism.MainNotions.S.lamSH R Q := by
  unfold Formalism.MainNotions.S.lamSH Formalism.MainNotions.S.lamS; rw [hv, hb]

theorem lamS_left (R : Ranks) (P : HCParam R) (h : (R.k - 1) + R.m = R.r) (i : Fin (R.k - 1)) :
    Formalism.MainNotions.S.lamS R P (Fin.cast h (Fin.castAdd R.m i)) = (P.v i : ℝ) := by
  simp [Formalism.MainNotions.S.lamS]

theorem lamS_right (R : Ranks) (P : HCParam R) (h : (R.k - 1) + R.m = R.r) (j : Fin R.m) :
    Formalism.MainNotions.S.lamS R P (Fin.cast h (Fin.natAdd (R.k - 1) j)) = -(P.b j : ℝ) := by
  simp [Formalism.MainNotions.S.lamS]

theorem count_pairs (m : ℕ) :
    ∑ j : Fin m, (univ.filter (fun j' : Fin m => j < j')).card = m * (m - 1) / 2 := by
  simp only [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => m - 1 - i) m, Finset.sum_range_reflect (fun i => i) m]
  exact Finset.sum_range_id m

theorem fdeg_rows_le : ∀ (R : Ranks) (P Q : HCParam R), Q.v = P.v → Q.b = P.b → ∀ B : ℝ, 1 ≤ B →
    (∀ i j, ((P.v i : ℚ) : ℝ) + ((P.b j : ℚ) : ℝ) ≤ B) →
    (∀ j j', ((P.b j' : ℚ) : ℝ) - ((P.b j : ℚ) : ℝ) ≤ B) →
    Formalism.QuantumDeterminants.fdegHC (Formalism.MainNotions.S.lamSH R P) * Formalism.MainNotions.StandardLattice.facProd R.r ≤
      B ^ ((R.k - 1) * R.m + R.m * (R.m - 1) / 2) * Formalism.MainNotions.StandardLattice.vand (fun i => ((Q.u i : ℚ) : ℝ)) := by
  intro R P Q hv hb B hB1 hvb hbb
  rw [lamSH_congr R P Q hv hb]
  rw [← hv, ← hb] at hvb
  rw [← hb] at hbb
  have hk := R.m_add_three_le_k
  have hm2 := R.two_le_m
  have hr : (R.k - 1) + R.m = R.r := by simp only [Ranks.r]; omega
  have huanti : StrictAnti Q.u := anti_of (by omega : R.k - 1 + 1 = R.k) Q.u Q.v Q.u_gt_v Q.v_gt_u
  have hbmono : StrictMono Q.b := mono_of Q.b fun j hj => by
    have a1 := Q.gap_be j
    have a2 := Q.gap_eb j hj
    have : (0:ℚ) ≤ R.t := by positivity
    linarith
  have hpos : ∀ i j, 0 < ((Q.v i : ℚ) : ℝ) + ((Q.b j : ℚ) : ℝ) := by
    intro i j
    have a1 := Q.v_gt_u i
    have a2 : Q.u ⟨R.k - 1, by omega⟩ ≤ Q.u ⟨i.1 + 1, by omega⟩ :=
      huanti.antitone (by rw [Fin.le_def]; simp only; omega)
    have a3 := Q.u_last_gt (by omega) (by omega)
    have a4 : Q.b ⟨0, by omega⟩ ≤ Q.b j := hbmono.monotone (by rw [Fin.le_def]; simp)
    have : (0:ℚ) < Q.v i + Q.b j := by linarith
    exact_mod_cast this
  have h3 : ∀ i : Fin (R.k - 1), (1:ℝ) ≤ ((Q.u ⟨i.1, by omega⟩ : ℚ) : ℝ) - ((Q.u ⟨i.1 + 1, by omega⟩ : ℚ) : ℝ) := by
    intro i
    obtain ⟨z, hz⟩ := Q.u_half ⟨i.1, by omega⟩
    obtain ⟨z', hz'⟩ := Q.u_half ⟨i.1 + 1, by omega⟩
    have a := (Q.v_gt_u i).trans (Q.u_gt_v i)
    rw [hz, hz'] at a
    have b1 : z' < z := by exact_mod_cast (by linarith : (z':ℚ) < z)
    have b2 : (z':ℚ) + 1 ≤ z := by exact_mod_cast b1
    have : (1:ℚ) ≤ Q.u ⟨i.1, by omega⟩ - Q.u ⟨i.1 + 1, by omega⟩ := by rw [hz, hz']; linarith
    exact_mod_cast this
  have hden := den_eq (2 * R.rS + R.k + 1)
  have hfp : Formalism.MainNotions.StandardLattice.facProd (2 * R.rS + R.k + 1) = Formalism.MainNotions.StandardLattice.facProd R.r := by rw [Formalism.MainNotions.S.dimS_eq]
  unfold Formalism.QuantumDeterminants.fdegHC
  rw [hden, hfp, div_mul_cancel₀ _ (facProd_pos _).ne']
  unfold Formalism.MainNotions.S.lamSH
  have e1 := pairs_cast (Formalism.MainNotions.S.dimS_eq R) (fun a b => |Formalism.MainNotions.S.lamS R Q a - Formalism.MainNotions.S.lamS R Q b|)
  have e2 := pairs_cast hr (fun a b => |Formalism.MainNotions.S.lamS R Q a - Formalism.MainNotions.S.lamS R Q b|)
  beta_reduce at e1 e2
  rw [e1, ← e2, pairs_append]
  simp only [lamS_left, lamS_right]
  have hA : ∏ i : Fin (R.k - 1), ∏ j ∈ univ.filter (fun j => i < j),
      |((Q.v i : ℚ) : ℝ) - ((Q.v j : ℚ) : ℝ)| ≤ Formalism.MainNotions.StandardLattice.vand (fun i => ((Q.u i : ℚ) : ℝ)) :=
    interlace_bound (by omega : R.k - 1 + 1 = R.k) (fun i => ((Q.u i : ℚ) : ℝ)) (fun i => ((Q.v i : ℚ) : ℝ))
      (fun i => by exact_mod_cast Q.u_gt_v i) (fun i => by exact_mod_cast Q.v_gt_u i) h3
  have hC : ∏ i : Fin (R.k - 1), ∏ j : Fin R.m, |((Q.v i : ℚ) : ℝ) - -((Q.b j : ℚ) : ℝ)| ≤
      B ^ ((R.k - 1) * R.m) := by
    calc _ ≤ ∏ i : Fin (R.k - 1), ∏ j : Fin R.m, B :=
          Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _)
            (fun i _ => Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => by
              rw [sub_neg_eq_add, abs_of_pos (hpos i j)]; exact hvb i j))
      _ = B ^ ((R.k - 1) * R.m) := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
  have hD : ∏ i : Fin R.m, ∏ j ∈ univ.filter (fun j => i < j),
      |-((Q.b i : ℚ) : ℝ) - -((Q.b j : ℚ) : ℝ)| ≤ B ^ (R.m * (R.m - 1) / 2) := by
    calc _ ≤ ∏ i : Fin R.m, ∏ j ∈ univ.filter (fun j => i < j), B :=
          Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _)
            (fun i _ => Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j hj => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              have c1 : ((Q.b i : ℚ) : ℝ) < ((Q.b j : ℚ) : ℝ) := by exact_mod_cast hbmono hj
              have c2 := hbb i j
              rw [abs_le]; constructor <;> linarith))
      _ = ∏ i : Fin R.m, B ^ (univ.filter (fun j => i < j)).card := by
          simp only [Finset.prod_const]
      _ = B ^ (∑ i : Fin R.m, (univ.filter (fun j => i < j)).card) := Finset.prod_pow_eq_pow_sum _ _ _
      _ = B ^ (R.m * (R.m - 1) / 2) := by rw [count_pairs]
  have nA : 0 ≤ ∏ i : Fin (R.k - 1), ∏ j ∈ univ.filter (fun j => i < j),
      |((Q.v i : ℚ) : ℝ) - ((Q.v j : ℚ) : ℝ)| :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _
  have nC : 0 ≤ ∏ i : Fin (R.k - 1), ∏ j : Fin R.m, |((Q.v i : ℚ) : ℝ) - -((Q.b j : ℚ) : ℝ)| :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _
  have nD : 0 ≤ ∏ i : Fin R.m, ∏ j ∈ univ.filter (fun j => i < j),
      |-((Q.b i : ℚ) : ℝ) - -((Q.b j : ℚ) : ℝ)| :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _
  have hB0 : (0:ℝ) ≤ B := by linarith
  calc _ ≤ Formalism.MainNotions.StandardLattice.vand (fun i => ((Q.u i : ℚ) : ℝ)) * B ^ ((R.k - 1) * R.m) * B ^ (R.m * (R.m - 1) / 2) :=
        mul_le_mul (mul_le_mul hA hC nC (nA.trans hA)) hD nD
          (mul_nonneg (nA.trans hA) (pow_nonneg hB0 _))
    _ = _ := by rw [pow_add]; ring

end GlobalTheory.FdegRowsBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaTypeReductionToOneTerm
section
open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda.OneTerm

variable {K : Type} [NormedField K]

theorem coeff_frobOp (τ : K →+* K) {q : ℕ} (hq : q ≠ 0) (i : ℕ) (f : K⟦X⟧) (n : ℕ) :
    coeff n (frobOp τ q i f) = if q ^ i ∣ n then (τ ^ i) (coeff (n / q ^ i) f) else 0 := by
  unfold frobOp
  rw [coeff_subst_X_pow (pow_ne_zero _ hq)]
  simp [coeff_map]

theorem pow_apply_pow (τ : K →+* K) (i k : ℕ) (x : K) : (τ ^ i) ((τ ^ k) x) = (τ ^ (i + k)) x := by
  rw [pow_add]; rfl

theorem norm_pow_apply (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (i : ℕ) (x : K) : ‖(τ ^ i) x‖ = ‖x‖ := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih => rw [← pow_apply_pow, ih, pow_one, hτ]

theorem coeff_frobOp_eq_zero (τ : K →+* K) {q : ℕ} (hq : 2 ≤ q) {f : K⟦X⟧} (hf : constantCoeff f = 0)
    {k n : ℕ} (h : n ≤ k) : coeff n (frobOp τ q k f) = 0 := by
  rw [coeff_frobOp τ (by omega)]
  split_ifs with hd
  · have hlt : n < q ^ k := lt_of_le_of_lt h (Nat.lt_pow_self (by omega))
    have h0 : n = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt
    subst h0
    simp [hf]
  · rfl

theorem pow_apply_coeff_frobOp (τ : K →+* K) {q : ℕ} (hq : q ≠ 0) (f : K⟦X⟧) (i k : ℕ) {n : ℕ} (hd : q ^ i ∣ n) :
    (τ ^ i) (coeff (n / q ^ i) (frobOp τ q k f)) = coeff n (frobOp τ q (i + k) f) := by
  rw [coeff_frobOp τ hq, coeff_frobOp τ hq, pow_add q i k]
  by_cases h : q ^ i * q ^ k ∣ n
  · rw [if_pos h, if_pos ((Nat.dvd_div_iff_mul_dvd hd).2 h), pow_apply_pow, Nat.div_div_eq_div_mul]
  · rw [if_neg h, if_neg (fun h' => h ((Nat.dvd_div_iff_mul_dvd hd).1 h')), map_zero]

theorem coeff_frobOp_sub_hondaSum (τ : K →+* K) (l : ℕ) {q : ℕ} (hq : 2 ≤ q) {f : K⟦X⟧} (hf : constantCoeff f = 0)
    (c : ℕ → K) (i n N : ℕ) (hN : n ≤ N) :
    coeff n (frobOp τ q i (C (l : K) * f - hondaSum τ q c f)) =
      (l : K) * coeff n (frobOp τ q i f) -
        ∑ j ∈ Finset.range N, (τ ^ i) (c j) * coeff n (frobOp τ q (i + (j + 1)) f) := by
  have hq0 : q ≠ 0 := by omega
  rw [coeff_frobOp τ hq0]
  set_option synthInstance.maxHeartbeats 100000 in
   by_cases hd : q ^ i ∣ n
   · rw [if_pos hd, coeff_frobOp τ hq0 i f, if_pos hd, map_sub, coeff_C_mul, hondaSum, coeff_mk,
      ← Finset.eventually_constant_sum (N := n / q ^ i) (n := N)
        (fun j hj => by rw [coeff_frobOp_eq_zero τ hq hf (by omega), mul_zero])
        (le_trans (Nat.div_le_self _ _) hN),
      map_sub, map_mul, map_natCast, map_sum]
     congr 1
     refine Finset.sum_congr rfl fun j _ => ?_
     rw [map_mul, pow_apply_coeff_frobOp τ hq0 f i (j + 1) hd]
   · rw [if_neg hd, coeff_frobOp τ hq0 i f, if_neg hd, mul_zero, Finset.sum_eq_zero, sub_zero]
     intro j _
     rw [coeff_frobOp τ hq0, if_neg, mul_zero]
     exact fun h => hd (dvd_trans (pow_dvd_pow q (Nat.le_add_right _ _)) h)

theorem sum_square_eq_sum_diag (N : ℕ) (F : ℕ → ℕ → K) (hF : ∀ i j, N ≤ i + j → F i j = 0) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, F i j =
      ∑ m ∈ Finset.range N, ∑ i ∈ Finset.range (m + 1), F i (m - i) := by
  rw [Finset.sum_range_diag_flip]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.eventually_constant_sum (fun j hj => hF i j (by omega)) (Nat.sub_le _ _)

theorem coeff_identity (τ : K →+* K) (l : ℕ) {q : ℕ} (hq : 2 ≤ q) {f : K⟦X⟧} (hf : constantCoeff f = 0)
    (c t : ℕ → K) (ht0 : t 0 = 1)
    (ht : ∀ n, 2 ≤ n → (l : K) * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i))) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), t i * coeff n (frobOp τ q i (C (l : K) * f - hondaSum τ q c f)) =
      (l : K) * coeff n f - (c 0 - l * t 1) * coeff n (frobOp τ q 1 f) := by
  have hq0 : q ≠ 0 := by omega
  have h1 : ∀ i ∈ Finset.range (n + 1), t i * coeff n (frobOp τ q i (C (l : K) * f - hondaSum τ q c f)) =
      (l : K) * t i * coeff n (frobOp τ q i f) -
        ∑ j ∈ Finset.range (n + 1), t i * (τ ^ i) (c j) * coeff n (frobOp τ q (i + (j + 1)) f) := by
    intro i _
    rw [coeff_frobOp_sub_hondaSum τ l hq hf c i n (n + 1) (Nat.le_succ n), mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib,
    sum_square_eq_sum_diag (n + 1) (fun i j => t i * (τ ^ i) (c j) * coeff n (frobOp τ q (i + (j + 1)) f))
      (fun i j hij => by simp only [coeff_frobOp_eq_zero τ hq hf (show n ≤ i + (j + 1) by omega), mul_zero])]
  have h2 : ∀ m ∈ Finset.range (n + 1),
      ∑ i ∈ Finset.range (m + 1), t i * (τ ^ i) (c (m - i)) * coeff n (frobOp τ q (i + (m - i + 1)) f) =
      (∑ i ∈ Finset.range (m + 1), t i * (τ ^ i) (c (m - i))) * coeff n (frobOp τ q (m + 1) f) := by
    intro m _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i + (m - i + 1) = m + 1 := by have := Finset.mem_range.1 hi; omega
    rw [this]
  rw [Finset.sum_congr rfl h2, Finset.sum_range_succ', Finset.sum_range_succ _ n,
    coeff_frobOp_eq_zero τ hq hf (Nat.le_succ n), mul_zero, add_zero, add_sub_right_comm,
    ← Finset.sum_sub_distrib, Finset.sum_eq_single 0]
  · have h0 : coeff n (frobOp τ q 0 f) = coeff n f := by
      rw [coeff_frobOp τ hq0]; simp
    rw [h0, ht0]
    simp only [zero_add, Finset.sum_range_one, pow_zero, Nat.sub_zero, ht0, RingHom.one_def, RingHom.id_apply]
    ring
  · intro m _ hm
    rw [ht (m + 1) (by omega), Nat.add_sub_cancel, sub_self]
  · intro h
    have hn : n = 0 := by simpa using h
    rw [coeff_frobOp_eq_zero τ hq hf (show n ≤ 0 + 1 by omega), mul_zero, mul_zero, sub_self]

theorem exists_one_term : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K]
    (l q : ℕ) (τ : K →+* K), 2 ≤ q → ‖(l : K)‖ < 1 → (∀ x, ‖τ x‖ = ‖x‖) → ∀ (f : K⟦X⟧), constantCoeff f = 0 →
    ∀ c : ℕ → K, (∀ j, ‖c j‖ ≤ 1) → ‖c 0‖ = 1 → CoefLe ‖(l : K)‖ (C (l : K) * f - hondaSum τ q c f) →
    ∃ c' : K, ‖c'‖ = 1 ∧ CoefLe ‖(l : K)‖ (C (l : K) * f - C c' * frobOp τ q 1 f) := by
  intro K _ _ _ _ l q τ hq hl hτ f hf c hc hc0 hg
  obtain ⟨t, ht0, ht1, ht⟩ := GlobalTheory.Honda.exists_twisted_division K τ hτ (l : K) hl c hc0 hc
  refine ⟨c 0 - l * t 1, ?_, fun n => ?_⟩
  · have hlt : ‖-((l : K) * t 1)‖ < ‖c 0‖ := by
      rw [norm_neg, norm_mul, hc0]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (ht1 1)) hl
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, hc0]
  · rw [map_sub, coeff_C_mul, coeff_C_mul, ← coeff_identity τ l hq hf c t ht0 ht n]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [norm_mul]
    refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (ht1 i)) ?_
    rw [coeff_frobOp τ (by omega)]
    split_ifs
    · rw [norm_pow_apply τ hτ]; exact hg _
    · simp

end GlobalTheory.Honda.OneTerm
end

