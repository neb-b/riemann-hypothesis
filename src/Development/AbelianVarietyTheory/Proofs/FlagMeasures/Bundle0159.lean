module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0543
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesTor
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnipotentMulVecMiddleVec
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueShuffle
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm Formalism.L2.DIV GlobalTheory.FinGL.Bruhat
open scoped Classical

namespace GlobalTheory.GLm.Shuffle

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

theorem pm_eq_mono (σ : Equiv.Perm (Fin n)) : (pm g σ : Mt g n) = mono (σ, fun _ => 1) := by
  have hm : (fun r j : Fin n => if r = σ j then (1 : ZMod g) else 0) = mono (σ, fun _ => (1 : (ZMod g)ˣ)) := by
    ext r j; simp [mono]
  have hu : IsUnit (mono (F := ZMod g) (σ, fun _ => (1 : (ZMod g)ˣ))) := by
    refine IsUnit.of_mul_eq_one (mono (σ.symm, fun _ => (1 : (ZMod g)ˣ))) ?_
    ext r j
    rw [mul_mono]
    simp [mono, Matrix.one_apply]
  unfold pm toG
  rw [hm, dite_eq_left hu]
  rfl

theorem isUniUp_iff (u : Gn g n) : IsUniUp (u : Mt g n) ↔ u ∈ unip (ZMod g) n :=
  ⟨fun h => ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2 rfl⟩,
    fun h a b => ⟨fun hab => unip_lower h hab, fun e => e ▸ unip_diag h a⟩⟩

theorem inPar_iff (a : ℕ) (p : Gn g n) :
    InPar a (p : Mt g n) ↔ p ∈ blockTri (κ := ZMod g) (fun i : Fin n => if (i : ℕ) < a then 0 else 1 : Fin n → ℕ) := by
  rw [mem_blockTri]
  constructor
  · intro h i j hij
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj] at hij
    exact h i j hj (not_lt.1 hi)
  · intro h i j hj hi
    exact h i j (by simp [hj, not_lt.2 hi])

theorem block_of_eq {a : ℕ} {σ σ' : Equiv.Perm (Fin n)} {u u' p p' : Gn g n} (hu : IsUniUp (u : Mt g n))
    (hu' : IsUniUp (u' : Mt g n)) (hp : InPar a (p : Mt g n)) (hp' : InPar a (p' : Mt g n))
    (h : u * pm g σ * p = u' * pm g σ' * p') (r : Fin n) (hr : (σ.symm r : ℕ) < a) : (σ'.symm r : ℕ) < a := by
  have hv : u'⁻¹ * u ∈ unip (ZMod g) n :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ ((isUniUp_iff _).1 hu')) ((isUniUp_iff _).1 hu)
  have hq : InPar a ((p' * p⁻¹ : Gn g n) : Mt g n) :=
    (inPar_iff _ _).2 (Subgroup.mul_mem _ ((inPar_iff _ _).1 hp') (Subgroup.inv_mem _ ((inPar_iff _ _).1 hp)))
  have h1 : (u'⁻¹ * u) * pm g σ = pm g σ' * (p' * p⁻¹) := by
    calc (u'⁻¹ * u) * pm g σ = u'⁻¹ * (u * pm g σ * p) * p⁻¹ := by group
      _ = _ := by rw [h]; group
  have h2 := congrFun (congrFun (congrArg (fun z : Gn g n => (z : Mt g n)) h1) r) (σ.symm r)
  rw [Units.val_mul _ (pm g σ), Units.val_mul (pm g σ'), pm_eq_mono, pm_eq_mono, mul_mono, mono_mul] at h2
  simp only [Equiv.apply_symm_apply, Units.val_one, mul_one, one_mul] at h2
  rw [unip_diag hv] at h2
  by_contra hc
  rw [hq _ _ hr (not_lt.1 hc)] at h2
  exact one_ne_zero h2

noncomputable def key (S : Fin n → Prop) (r : Fin n) : ℕ := if S r then (r : ℕ) else n + r

theorem key_injective (S : Fin n → Prop) : Function.Injective (key S) := by
  intro r s h
  have := r.2; have := s.2
  unfold key at h
  apply Fin.ext
  split_ifs at h <;> omega

theorem key_mono {a : ℕ} {σ : Equiv.Perm (Fin n)} {S : Fin n → Prop} (hS : ∀ r, S r ↔ (σ.symm r : ℕ) < a)
    (hσ : ∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) : Monotone (key S ∘ σ) := by
  refine StrictMono.monotone fun i j hij => ?_
  have h1 := hσ i j hij
  have h2 : (i : ℕ) < j := hij
  have := (σ i).2
  simp only [Function.comp, key, hS, Equiv.symm_apply_apply, Fin.lt_def] at h1 ⊢
  split_ifs <;> omega

theorem exists_shuffle {a : ℕ} (ha : a ≤ n) (s : Equiv.Perm (Fin n)) : ∃ σ : Equiv.Perm (Fin n),
    (∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) ∧
      ∀ j : Fin n, (s.symm (σ j) : ℕ) < a ↔ (j : ℕ) < a := by
  set S : Fin n → Prop := fun r => (s.symm r : ℕ) < a with hS
  set σ := Tuple.sort (key S) with hσ
  have hm : Monotone (key S ∘ σ) := Tuple.monotone_sort _
  have hlt : ∀ r, key S r < n ↔ S r := by
    intro r
    have := r.2
    unfold key
    split_ifs with h <;> simp [h]
  have hcard : (Finset.univ.filter fun i => (key S ∘ σ) i < n).card = a := by
    have : (Finset.univ.filter fun i : Fin n => (i : ℕ) < a).card = a := by
      rw [Fin.card_filter_val_lt]; omega
    rw [← this]
    refine Finset.card_equiv (σ.trans s.symm) fun i => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
    exact hlt _
  have hiff : ∀ j : Fin n, S (σ j) ↔ (j : ℕ) < a := by
    intro j
    rw [← hlt, ← hcard]
    exact (Tuple.lt_card_lt_iff_apply_lt_of_monotone hm).symm
  refine ⟨σ, fun i j hij hb => ?_, hiff⟩
  have h1 : (key S ∘ σ) i < (key S ∘ σ) j :=
    (hm.strictMono_of_injective ((key_injective S).comp σ.injective)) hij
  have h2 : (i : ℕ) < j := hij
  simp only [Function.comp, key, hiff] at h1
  rw [Fin.lt_def]
  split_ifs at h1 <;> omega

theorem existsUnique_shuffle : ∀ (g : ℕ) [Fact g.Prime] (a n : ℕ), a ≤ n → ∀ x : Gn g n, ∃! σ : Equiv.Perm (Fin n), (∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) ∧ ∃ u p : Gn g n, IsUniUp (u : Mt g n) ∧ InPar a (p : Mt g n) ∧ x = u * pm g σ * p := by
  intro g _ a n ha x
  obtain ⟨m, u, hu, u', hu', hx⟩ := exists_decomp x
  obtain ⟨σ, hσ, hb⟩ := exists_shuffle ha m.1
  have hp : InPar a (((pm g σ)⁻¹ * u⁻¹ * x : Gn g n) : Mt g n) := by
    intro i j hj hi
    have h1 : (pm g σ : Mt g n) * (((pm g σ)⁻¹ * u⁻¹ * x : Gn g n) : Mt g n) = mono m * (u' : Mt g n) := by
      rw [← Units.val_mul, ← mul_assoc, mul_inv_cancel_left, Units.val_mul, hx, Matrix.mul_assoc,
        Units.inv_mul_cancel_left]
    have h2 := congrFun (congrFun h1 (σ i)) j
    rw [pm_eq_mono, mono_mul, mono_mul] at h2
    simp only [Equiv.symm_apply_apply, Units.val_one, one_mul] at h2
    have h3 : j < m.1.symm (σ i) := by
      have := (hb i).not.2 (not_lt.2 hi)
      rw [Fin.lt_def]; omega
    rw [h2, unip_lower hu' h3, mul_zero]
  have hu1 := (isUniUp_iff u).2 hu
  have hx1 : x = u * pm g σ * ((pm g σ)⁻¹ * u⁻¹ * x) := by group
  refine ⟨σ, ⟨hσ, u, _, hu1, hp, hx1⟩, ?_⟩
  rintro τ ⟨hτ, v, q, hv, hq, hx2⟩
  have h1 : Monotone (key (fun r => (σ.symm r : ℕ) < a) ∘ σ) := key_mono (fun _ => Iff.rfl) hσ
  have h2 : Monotone (key (fun r => (σ.symm r : ℕ) < a) ∘ τ) := key_mono (fun r =>
    ⟨block_of_eq hu1 hv hp hq (hx1.symm.trans hx2) r, block_of_eq hv hu1 hq hp (hx2.symm.trans hx1) r⟩) hτ
  exact Equiv.ext fun i => key_injective _ (congrFun (Tuple.unique_monotone h2 h1) i)

end GlobalTheory.GLm.Shuffle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryTorusScaleBesselCharacter
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TorusScale

variable {k r : ℕ}

def dS (k r : ℕ) (l : ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then l ^ (r - i.val)
  else if r + k < i.val then (star (l ^ (r - (2 * r + k - i.val))))⁻¹ else 1

theorem dS_ne {l : ℂ} (hl : l ≠ 0) (i : Fin (2 * r + k + 1)) : dS k r l i ≠ 0 := by
  unfold dS
  split_ifs
  · exact pow_ne_zero _ hl
  · exact inv_ne_zero (star_ne_zero.2 (pow_ne_zero _ hl))
  · exact one_ne_zero

theorem dS_eI (l : ℂ) (a : Fin r) : dS k r l (eI k r a) = l ^ (r - a.val) := by
  unfold dS eI; simp [a.isLt]

theorem dS_mid (l : ℂ) (i : Fin (2 * r + k + 1)) (h : ¬ (i.val < r ∨ r + k < i.val)) : dS k r l i = 1 := by
  unfold dS
  rw [if_neg (by omega), if_neg (by omega)]

theorem dS_pair {l : ℂ} (hl : l ≠ 0) (i j : Fin (2 * r + k + 1)) (hi : i.val < r) (hij : i.val + j.val = 2 * r + k) :
    star (dS k r l i) * dS k r l j = 1 := by
  unfold dS
  rw [if_pos hi, if_neg (by omega), if_pos (by omega)]
  have : 2 * r + k - j.val = i.val := by omega
  rw [this]
  exact mul_inv_cancel₀ (star_ne_zero.2 (pow_ne_zero _ hl))

theorem diag_inv {n : Type} [Fintype n] [DecidableEq n] (d : n → ℂ) (hd : ∀ i, d i ≠ 0) :
    (diagonal d)⁻¹ = diagonal fun i => (d i)⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (hd i)

theorem conj_diag {n : Type} [Fintype n] [DecidableEq n] (d : n → ℂ) (hd : ∀ i, d i ≠ 0) (M : Matrix n n ℂ) (i j : n) :
    (diagonal d * M * (diagonal d)⁻¹) i j = d i * M i j * (d j)⁻¹ := by
  rw [diag_inv d hd]
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem diag_mem_UH (d : Fin (2 * r + k + 1) → ℂ) (h : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1) :
    diagonal d ∈ UH (Hpk k r) := by
  show (diagonal d)ᴴ * Hpk k r * diagonal d = Hpk k r
  ext i j
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hM : Hpk k r i j = 0
  · rw [hM]; ring
  · have := h i j hM
    rw [Pi.star_apply, mul_right_comm, this, one_mul]

theorem dS_Hpk {l : ℂ} (hl : l ≠ 0) (i j : Fin (2 * r + k + 1)) (h : Hpk k r i j ≠ 0) :
    star (dS k r l i) * dS k r l j = 1 := by
  by_cases h1 : i.val < r ∧ i.val + j.val = 2 * r + k
  · exact dS_pair hl i j h1.1 h1.2
  by_cases h2 : j.val < r ∧ i.val + j.val = 2 * r + k
  · have := congrArg star (dS_pair hl j i h2.1 (by omega))
    rw [star_mul, star_star, star_one] at this
    exact this
  by_cases h3 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
  · rw [← h3.2.2, dS_mid l i (by omega)]; simp
  exfalso
  unfold Hpk at h
  rw [if_neg h1, if_neg h2, if_neg h3] at h
  exact h rfl

theorem conj_mem_N (d : Fin (2 * r + k + 1) → ℂ) (hd : ∀ i, d i ≠ 0)
    (h : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1) {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hn : n ∈ Nset k r) : diagonal d * n * (diagonal d)⁻¹ ∈ Nset k r := by
  obtain ⟨h1, h2, h3⟩ := hn
  refine ⟨?_, fun a i hi => ?_, fun i j a b c => ?_⟩
  · refine Pv.Frames.UH_mul (Pv.Frames.UH_mul (diag_mem_UH d h) h1) ?_
    rw [diag_inv d hd]
    refine diag_mem_UH _ fun i j hij => ?_
    rw [star_inv₀, ← mul_inv, h i j hij, inv_one]
  · rw [conj_diag d hd, h2 a i hi]
    split_ifs with e
    · rw [e, mul_one, mul_inv_cancel₀ (hd _)]
    · ring
  · rw [conj_diag d hd, h3 i j a b c]
    split_ifs with e
    · rw [e, mul_one, mul_inv_cancel₀ (hd _)]
    · ring

theorem conj_mem_N_iff (d : Fin (2 * r + k + 1) → ℂ) (hd : ∀ i, d i ≠ 0)
    (h : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1) (n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    n ∈ Nset k r ↔ diagonal d * n * (diagonal d)⁻¹ ∈ Nset k r := by
  refine ⟨conj_mem_N d hd h, fun hn => ?_⟩
  have hd' : ∀ i, (d i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hd i)
  have := conj_mem_N (fun i => (d i)⁻¹) hd'
    (fun i j hij => by rw [star_inv₀, ← mul_inv, h i j hij, inv_one]) hn
  convert this using 1
  ext i j
  rw [conj_diag _ hd', conj_diag _ hd]
  have := hd i
  have := hd j
  field_simp

theorem UW_col {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (i j : Fin (2 * r + k + 1)) (hj : j.val < r ∨ r + k < j.val) :
    h i j = if i = j then 1 else 0 := by
  have key : h *ᵥ bvec j = bvec j := by
    rcases hj with hj | hj
    · exact (hh.2.1 ⟨j.val, hj⟩).1
    · have := (hh.2.1 ⟨2 * r + k - j.val, by omega⟩).2
      have e : esI k r ⟨2 * r + k - j.val, by omega⟩ = j := by
        apply Fin.ext
        have := j.isLt
        show 2 * r + k - (2 * r + k - j.val) = j.val
        omega
      rwa [e] at this
  have := congrFun key i
  simpa [bvec, Pi.single_apply] using this

theorem Hpk_outer (i j p : Fin (2 * r + k + 1)) (hj : j.val < r ∨ r + k < j.val) (hij : i.val + j.val = 2 * r + k) :
    Hpk k r j p = if p = i then 1 else 0 := by
  unfold Hpk
  by_cases e : p = i
  · subst e
    rw [if_pos rfl]
    by_cases h1 : j.val < r
    · rw [if_pos ⟨h1, by omega⟩]
    · rw [if_neg (by omega), if_pos (by omega)]
  · have e' : p.val ≠ i.val := fun x => e (Fin.ext x)
    rw [if_neg e, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem UW_row {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (i j : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    h i j = if j = i then 1 else 0 := by
  have hi0 := i.isLt
  let q : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
  have hq : q.val < r ∨ r + k < q.val := by show 2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val; omega
  have hiq : i.val + q.val = 2 * r + k := by show i.val + (2 * r + k - i.val) = _; omega
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have := congrFun (congrFun hU q) j
  rw [Hpk_outer i q j hq hiq, Matrix.mul_assoc, Matrix.mul_apply] at this
  simp only [Matrix.conjTranspose_apply, UW_col hh _ q hq] at this
  rw [Finset.sum_eq_single q (fun b _ hb => by simp [hb]) (by simp), Matrix.mul_apply] at this
  simp only [Hpk_outer i q _ hq hiq] at this
  simpa using this

theorem dS_comm (l : ℂ) {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : diagonal (dS k r l) * h = h * diagonal (dS k r l) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hj : j.val < r ∨ r + k < j.val
  · rw [UW_col hh i j hj]
    split_ifs with e
    · rw [e]; ring
    · ring
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [UW_row hh i j hi]
    split_ifs with e
    · rw [e]; ring
    · ring
  rw [dS_mid l i hi, dS_mid l j hj]; ring

theorem diag_fix (d : Fin (2 * r + k + 1) → ℂ) (hd : ∀ i : Fin (2 * r + k + 1), ¬ (i.val < r ∨ r + k < i.val) → d i = 1)
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : diagonal d *ᵥ z = z := by
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h]; ring
  · rw [hd i h, one_mul]

theorem inv_fix {l : ℂ} (hl : l ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    (diagonal (dS k r l))⁻¹ *ᵥ z = z := by
  rw [diag_inv _ (dS_ne hl)]
  exact diag_fix _ (fun i hi => by rw [dS_mid l i hi, inv_one]) hz

theorem ell_conj {l : ℂ} (hl : l ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ell k r z (diagonal (dS k r l) * M * (diagonal (dS k r l))⁻¹) = l * ell k r z M := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [conj_diag _ (dS_ne hl), dS_eI, dS_eI]
    have e : r - a.val = (r - (a.val + 1)) + 1 := by omega
    rw [e, pow_succ]
    have := pow_ne_zero (r - (a.val + 1)) hl
    field_simp
  · have hra : r - a.val = 1 := by have := a.isLt; omega
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_fix hl hz, Matrix.mulVec_diagonal, dS_eI, hra, pow_one]

theorem pow_bound {x : ℝ} (hx : 0 < x) {m : ℕ} (hm : m ≤ r) :
    (x / 2) ^ m ≤ max (x / 2) (2 / x) ^ r ∧ (2 / x) ^ m ≤ max (x / 2) (2 / x) ^ r := by
  have h1 : 1 ≤ max (x / 2) (2 / x) := by
    rcases le_total x 2 with h | h
    · exact le_max_of_le_right ((one_le_div hx).2 h)
    · exact le_max_of_le_left ((one_le_div two_pos).2 h)
  exact ⟨(pow_le_pow_left₀ (by positivity) (le_max_left _ _) m).trans (pow_le_pow_right₀ h1 hm),
    (pow_le_pow_left₀ (by positivity) (le_max_right _ _) m).trans (pow_le_pow_right₀ h1 hm)⟩

theorem exists_torus_scale : ∀ (k r : ℕ) (c : ℂ), c ≠ 0 → ∃ t ∈ GG k r, (∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r) ∧ (∀ z, inWb k r z → t *ᵥ z = z ∧ (∀ h ∈ UWset k r z, t * h = h * t) ∧ ∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) ∧ ∀ a : Fin (r + 1), ∃ s : ℂ, s ≠ 0 ∧ ‖s‖ ≤ max (‖c‖ / 2) (2 / ‖c‖) ^ r ∧ ‖s‖⁻¹ ≤ max (‖c‖ / 2) (2 / ‖c‖) ^ r ∧ ∀ z, inWb k r z → t⁻¹ *ᵥ fvec k r z a = s • fvec k r z a := by
  intro k r c hc
  have hS : cStd ≠ 0 := by unfold cStd; simp
  have hl : cStd / c ≠ 0 := div_ne_zero hS hc
  have hn : ‖cStd / c‖ = 2 / ‖c‖ := by unfold cStd; simp
  have hx : 0 < ‖c‖ := norm_pos_iff.2 hc
  refine ⟨diagonal (dS k r (cStd / c)), diag_mem_UH _ (dS_Hpk hl), conj_mem_N_iff _ (dS_ne hl) (dS_Hpk hl),
    fun z hz => ⟨diag_fix _ (dS_mid _) hz, fun h hh => dS_comm _ hh, fun n _ => ?_⟩, fun a => ?_⟩
  · unfold psi
    rw [ell_conj hl hz, ← mul_assoc, mul_div_cancel₀ _ hc]
  · have hb := pow_bound (r := r) hx (Nat.sub_le r a.val)
    refine ⟨((cStd / c) ^ (r - a.val))⁻¹, inv_ne_zero (pow_ne_zero _ hl), ?_, ?_, fun z hz => ?_⟩
    · rw [norm_inv, norm_pow, hn, ← inv_pow, inv_div]; exact hb.1
    · rw [norm_inv, inv_inv, norm_pow, hn]; exact hb.2
    · unfold fvec
      split_ifs with h
      · rw [diag_inv _ (dS_ne hl)]
        funext i
        rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
        by_cases e : i = eI k r ⟨a.val, h⟩
        · rw [e, dS_eI]
        · simp [bvec, e]
      · have : r - a.val = 0 := by omega
        rw [inv_fix hl hz, this]; simp

end GlobalTheory.TorusScale

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGramNumberNormalizedInvariance
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.YInv
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YjInv

variable {k r j : ℕ}

theorem N_ej (hj : j ≤ r) {n : Mat k r} (hn : n ∈ Nset k r) (a : Fin j) :
    n *ᵥ bvec (eI k r (Fin.castLE hj a)) =
      ∑ b : Fin j, n (eI k r (Fin.castLE hj b)) (eI k r (Fin.castLE hj a)) • bvec (eI k r (Fin.castLE hj b)) := by
  rw [N_e hn]
  symm
  refine Finset.sum_of_injOn (Fin.castLE hj) ((Fin.castLE_injective hj).injOn) (by simp) ?_ (by simp)
  intro b _ hb
  have hb' : j ≤ b.val := by
    by_contra h
    exact hb ⟨⟨b.val, by omega⟩, by simp, rfl⟩
  have ha := a.isLt
  rw [hn.2.1 (Fin.castLE hj a) _ (by simp [eI]; omega), if_neg, zero_smul]
  intro h
  have := congrArg Fin.val h
  simp [eI] at this
  omega

theorem N_detj (hj : j ≤ r) {n : Mat k r} (hn : n ∈ Nset k r) :
    (Matrix.of fun b a : Fin j => n (eI k r (Fin.castLE hj b)) (eI k r (Fin.castLE hj a))).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp only [Matrix.of_apply]
    rw [hn.2.1 (Fin.castLE hj a) _ le_rfl, if_pos rfl]
  · intro b a hab
    have hab' : a.val < b.val := hab
    simp only [Matrix.of_apply]
    rw [hn.2.1 (Fin.castLE hj a) (eI k r (Fin.castLE hj b)) hab'.le, if_neg]
    intro h
    have := congrArg Fin.val h
    simp [eI] at this
    omega

theorem Yj_N (hj : j ≤ r) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (γ : Mat k r)
    {n₁ n₂ : Mat k r} (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (x : Mat k r) :
    Yj k r hj z z' (n₁ * γ * n₂) x = Yj k r hj z z' γ (n₂ * x) := by
  have h₁' := (nSubgroup k r).2.2 _ h₁
  unfold Yj Dj
  rw [dInv k r z z' hz hz' n₁ (N_sub_S z h₁) n₂ (N_sub_S z' h₂), Ppos_N hz hz' h₁ h₂,
    ← gramProj_comb _ (fun a : Fin j => (n₂ * x)⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)))) _ (N_detj hj h₁')]
  congr 2
  funext a
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    N_ej hj h₁']
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.of_apply, ← Matrix.mulVec_mulVec]

theorem Yj_K (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ x : Mat k r) {κ : Mat k r} (hG : κ ∈ GG k r)
    (hκ : κ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) :
    Yj k r hj z z' γ (x * κ) = Yj k r hj z z' γ x := by
  have h1 : star κ * κ = 1 := Matrix.mem_unitaryGroup_iff'.1 hκ
  have h2 : κ * star κ = 1 := Matrix.mem_unitaryGroup_iff.1 hκ
  have hG' : star κ * Hpk k r * κ = Hpk k r := hG
  have hc : (Hpk k r - 1) * κ = κ * (Hpk k r - 1) := by
    have : κ * Hpk k r = Hpk k r * κ := by
      conv_lhs => rw [← hG', ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [Matrix.sub_mul, Matrix.mul_sub, this, Matrix.one_mul, Matrix.mul_one]
  unfold Yj
  rw [gramProj_unitary (Ppos k r z z' γ x) (Ppos k r z z' γ (x * κ)) _ κ hκ]
  · congr 2
    funext a
    rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ κ,
      Matrix.mul_nonsing_inv _ (det_unit hG), Matrix.one_mulVec]
  · intro p
    rw [mem_Ppos, mem_Ppos]
    simp only [Matrix.mulVec_mulVec, hc]
    refine and_congr ⟨fun h => ?_, fun h => ?_⟩ Iff.rfl
    · rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
    · have := congrArg (star κ *ᵥ ·) h
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      rwa [← Matrix.mul_assoc, h1, Matrix.one_mul] at this

theorem yj_invariant : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → γ ∈ GG k r → ∀ x ∈ GG k r, (∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), Yj k r hj z z' γ (x * κ) = Yj k r hj z z' γ x) ∧ (∀ n₁ ∈ Nset k r, ∀ n₂ ∈ Nset k r, Yj k r hj z z' (n₁ * γ * n₂) x = Yj k r hj z z' γ (n₂ * x)) ∧ ∀ ρ ∈ Rset k r γ, Yj k r hj z z' γ (ρ * x) = Yj k r hj z z' γ x := by
  intro k r j hj z z' γ hz hz' hγ x _
  refine ⟨fun κ hκ => Yj_K hj z z' γ x hκ.1 hκ.2, fun n₁ h₁ n₂ h₂ => Yj_N hj hz hz' γ h₁ h₂ x, fun ρ hρ => ?_⟩
  rw [← Yj_N hj hz hz' γ ((nSubgroup k r).2.2 _ hρ.2) hρ.1 x]
  congr 1
  have hm : IsUnit (γ * ρ * γ⁻¹).det := det_unit hρ.2.1
  have e : γ * ρ = γ * ρ * γ⁻¹ * γ := by
    rw [Matrix.mul_assoc (γ * ρ), Matrix.nonsing_inv_mul _ (det_unit hγ), Matrix.mul_one]
  rw [Matrix.mul_assoc]
  conv_lhs => rw [show (γ * ρ * γ⁻¹)⁻¹ * (γ * ρ) = (γ * ρ * γ⁻¹)⁻¹ * (γ * ρ * γ⁻¹ * γ) from by rw [← e]]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hm, Matrix.one_mul]

end GlobalTheory.Amp.YjInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularBesselModelUnitaryGroup
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem isUnimod_GG : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → IsUnimod (GG k r) μ := by
  intro k r μ hμ
  obtain ⟨hG, h⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  obtain ⟨hM, hR⟩ := h μ hμ
  refine ⟨fun s hs => hR s hs, ?_⟩
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf measurable_invM]
  exact GlobalTheory.HaarInversion.lintegral_inv_eq _ (GG k r) μ hG hM hR f hf

end GlobalTheory.SgInf
end

