module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Formalism.FormalDegreeBessel.StatementG
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainCupProductCongruenceStatement
section
open GlobalTheory.K5

private theorem cup_identity {R : Type*} [CommRing R]
    (N P A B A' B' i m ag bg bh bgh qg qh qgh zg zh zgh x gx gy ghy e₁ e₂ tb tq tz : R)
    (h₁ : P * ag - A * qg - B * zg - (gx - x) = N * e₁)
    (h₂ : P * bh - A' * qh - B' * zh - (ghy - gy) = N * e₂)
    (hb : bgh = bg + bh - N * tb) (hq : qgh = qg + qh - N * tq) (hz : zgh = zg + zh - N * tz)
    (hi : 2 * i = 1 + N * m) :
    (P * ag) * (P * bh) + (A * B' - B * A') * (zg * qh) -
      ((gx * (P * bh) - (A * qh + B * zh) * ghy - i * (A * A') * qh ^ 2 - A * B' * (qh * zh)
          - i * (B * B') * zh ^ 2)
        - (x * (P * bgh) - (A * qgh + B * zgh) * ghy - i * (A * A') * qgh ^ 2
          - A * B' * (qgh * zgh) - i * (B * B') * zgh ^ 2)
        + (x * (P * bg) - (A * qg + B * zg) * gy - i * (A * A') * qg ^ 2 - A * B' * (qg * zg)
          - i * (B * B') * zg ^ 2)) =
    N * (e₁ * (P * bh) + (A * qg + B * zg) * e₂ - P * x * tb + (A * tq + B * tz) * ghy
      - m * (A * A') * (qg * qh) - m * (B * B') * (zg * zh)
      + i * (A * A') * (2 * tq * (qg + qh) - N * tq ^ 2)
      + A * B' * (tq * (zg + zh) + tz * (qg + qh) - N * (tq * tz))
      + i * (B * B') * (2 * tz * (zg + zh) - N * tz ^ 2)) := by
  subst hb hq hz
  linear_combination (P * bh) * h₁ + (A * qg + B * zg) * h₂
    - (A * A' * (qg * qh) + B * B' * (zg * zh)) * hi

private theorem exists_val_add {R : Type*} [CommRing R] (p n : ℕ) (hp : p ≠ 0) (u v : ZMod (p ^ n)) :
    ∃ t : ℕ, (((u + v).val : ℕ) : R) = (u.val : R) + (v.val : R) - (p : R) ^ n * (t : R) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp⟩
  refine ⟨(u.val + v.val) / p ^ n, ?_⟩
  have h := Nat.mod_add_div (u.val + v.val) (p ^ n)
  rw [← ZMod.val_add] at h
  have h' := congrArg (Nat.cast : ℕ → R) h
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_add] at h'
  linear_combination h'

private theorem exists_half (p n : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    ∃ i m : ℤ, 2 * i = 1 + (p : ℤ) ^ n * m := by
  obtain ⟨k, hk⟩ := (hp.odd_of_ne_two h2).pow (n := n)
  refine ⟨k + 1, 1, ?_⟩
  have := congrArg (Nat.cast : ℕ → ℤ) hk
  push_cast at this
  rw [this]; ring

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_cochain_cup_product_congruence : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (H : Subgroup (Gal p Ω)) (n c : ℕ)
  (a b lz lq : Gal p Ω → ZMod (p ^ n)) (A B A' B' : Ω),
  (∀ g ∈ H, ∀ h ∈ H, a (g * h) = a g + a h) → (∀ g ∈ H, ∀ h ∈ H, b (g * h) = b g + b h) →
  (∀ g ∈ H, ∀ h ∈ H, lz (g * h) = lz g + lz h) → (∀ g ∈ H, ∀ h ∈ H, lq (g * h) = lq g + lq h) →
  (∀ g ∈ H, g A = A ∧ g B = B ∧ g A' = A' ∧ g B' = B') →
  IsInt (p := p) ((p : Ω) ^ c * A) → IsInt (p := p) ((p : Ω) ^ c * B) →
  IsInt (p := p) ((p : Ω) ^ c * A') → IsInt (p := p) ((p : Ω) ^ c * B') →
  (∀ g, ∃ S : Finset Ω, ∀ h : Gal p Ω, (∀ x ∈ S, h x = g x) → a h = a g ∧ b h = b g ∧ lz h = lz g ∧ lq h = lq g) →
  Cob1 n H (fun g => (p : Ω) ^ c * ((a g).val : Ω) - (p : Ω) ^ c * A * ((lq g).val : Ω) - (p : Ω) ^ c * B * ((lz g).val : Ω)) →
  Cob1 n H (fun g => (p : Ω) ^ c * ((b g).val : Ω) - (p : Ω) ^ c * A' * ((lq g).val : Ω) - (p : Ω) ^ c * B' * ((lz g).val : Ω)) →
  Cob2 n H (fun g h => (p : Ω) ^ (4 * c) * (((a g).val : Ω) * ((b h).val : Ω)) +
      (p : Ω) ^ (4 * c) * (A * B' - B * A') * (((lz g).val : Ω) * ((lq h).val : Ω))) := by
  intro p hp h2 Ω _ _ H n c a b lz lq A B A' B' _ hb hz hq hfix iA iB iA' iB' hlc ⟨x, ix, hx⟩
    ⟨y, iy, hy⟩
  classical
  obtain ⟨i, m, him⟩ := exists_half p n hp.out h2
  have him' : 2 * (i : Ω) = 1 + (p : Ω) ^ n * (m : Ω) := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) him
  let R := integralClosure (O0 p) Ω
  have key : ∀ v : Ω, IsInt (p := p) v ↔ v ∈ R := fun v => Iff.rfl
  have hmap : ∀ (g : Gal p Ω) (v : Ω), v ∈ R → g v ∈ R := fun g v hv =>
    IsIntegral.map g.toAlgHom hv
  rw [key] at iA iB iA' iB' ix iy
  have iP : (p : Ω) ^ c ∈ R := pow_mem (natCast_mem R p) c
  have iN : (p : Ω) ^ n ∈ R := pow_mem (natCast_mem R p) n
  refine ⟨fun k => ((p : Ω) ^ c) ^ 2 * (x * ((p : Ω) ^ c * ((b k).val : Ω))
    - ((p : Ω) ^ c * A * ((lq k).val : Ω) + (p : Ω) ^ c * B * ((lz k).val : Ω)) * k y
    - (i : Ω) * (((p : Ω) ^ c * A) * ((p : Ω) ^ c * A')) * ((lq k).val : Ω) ^ 2
    - ((p : Ω) ^ c * A) * ((p : Ω) ^ c * B') * (((lq k).val : Ω) * ((lz k).val : Ω))
    - (i : Ω) * (((p : Ω) ^ c * B) * ((p : Ω) ^ c * B')) * ((lz k).val : Ω) ^ 2), ⟨?_, ?_⟩, ?_⟩
  · intro k
    rw [key]
    have h1 := hmap k y iy
    generalize (p : Ω) ^ c * A = A₁ at *
    generalize (p : Ω) ^ c * B = B₁ at *
    generalize (p : Ω) ^ c * A' = A₂ at *
    generalize (p : Ω) ^ c * B' = B₂ at *
    generalize (p : Ω) ^ c = P at *
    repeat' first
      | assumption
      | exact natCast_mem R _
      | exact intCast_mem R _
      | apply mul_mem
      | apply sub_mem
      | apply add_mem
      | apply pow_mem
  · intro k
    obtain ⟨S, hS⟩ := hlc k
    refine ⟨insert y S, fun h hh => ⟨0, (key _).2 (zero_mem R), ?_⟩⟩
    obtain ⟨-, e1, e2, e3⟩ := hS h (fun x hx => hh x (Finset.mem_insert_of_mem hx))
    have e4 := hh y (Finset.mem_insert_self _ _)
    simp only [e1, e2, e3, e4, sub_self, mul_zero]
  · intro g hg h hh
    obtain ⟨e₁, ie₁, h₁⟩ := hx g hg
    obtain ⟨e₂, ie₂, h₂⟩ := hy h hh
    obtain ⟨fA, fB, fA', fB'⟩ := hfix g hg
    have h₂' := congrArg g h₂
    simp only [map_sub, map_mul, map_pow, map_natCast, fA', fB'] at h₂'
    obtain ⟨tb, htb⟩ := exists_val_add (R := Ω) p n hp.out.ne_zero (b g) (b h)
    obtain ⟨tq, htq⟩ := exists_val_add (R := Ω) p n hp.out.ne_zero (lq g) (lq h)
    obtain ⟨tz, htz⟩ := exists_val_add (R := Ω) p n hp.out.ne_zero (lz g) (lz h)
    rw [← hb g hg h hh] at htb
    rw [← hq g hg h hh] at htq
    rw [← hz g hg h hh] at htz
    have main := cup_identity _ _ _ _ _ _ _ _ _ ((b g).val : Ω) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      h₁ h₂' htb htq htz him'
    refine ⟨_, ?_, Eq.trans ?_
      ((congrArg (fun t => ((p : Ω) ^ c) ^ 2 * t) main).trans (mul_left_comm _ _ _))⟩
    swap
    · simp only [map_sub, map_add (f := _), map_mul, map_pow, map_natCast, map_intCast, fA, fB, fA', fB',
        AlgEquiv.mul_apply]
      ring
    · rw [key] at ie₁ ie₂ ⊢
      have h1 := hmap g _ (hmap h y iy)
      have h3 := hmap g _ ie₂
      clear main h₁ h₂ h₂' hx hy htb htq htz him'
      generalize (p : Ω) ^ c * A = A₁ at *
      generalize (p : Ω) ^ c * B = B₁ at *
      generalize (p : Ω) ^ c * A' = A₂ at *
      generalize (p : Ω) ^ c * B' = B₂ at *
      generalize (p : Ω) ^ c = P at *
      generalize (p : Ω) ^ n = N at *
      repeat' first
        | assumption
        | exact natCast_mem R _
        | exact intCast_mem R _
        | apply mul_mem
        | apply sub_mem
        | apply add_mem
        | apply pow_mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingMinorInvariant
section
open Matrix

noncomputable section

namespace GlobalTheory.LeadingMinorInv

open Formalism.QuantumDeterminants

def UpUni {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i j, j < i → U i j = 0) ∧ ∀ i, U i i = 1

lemma minor_mul {n l : ℕ} (hl : l ≤ n) (A U : Matrix (Fin n) (Fin n) ℂ) (hU : UpUni U) :
    ((A * U).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have hsub : (A * U).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * U.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    apply Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl)
    · intro b hb
      have hjb : Fin.castLE hl j < b := by
        rw [Fin.lt_def]
        show j.val < b.val
        by_contra hc
        have := j.isLt
        exact hb ⟨⟨b.val, by omega⟩, Fin.ext rfl⟩
      rw [hU.1 b _ hjb, mul_zero]
    · intro a
      rfl
  have hdet : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · simp [Matrix.submatrix_apply, hU.2]
    · intro i j hij
      simp only [Matrix.submatrix_apply]
      apply hU.1
      rw [Fin.lt_def] at hij ⊢
      exact hij
  rw [hsub, Matrix.det_mul, hdet, mul_one]

lemma minor_mul_left {n l : ℕ} (hl : l ≤ n) (A U : Matrix (Fin n) (Fin n) ℂ) (hU : UpUni U) :
    ((Uᴴ * A).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have e : Uᴴ * A = (Aᴴ * U)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [e, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, minor_mul hl _ _ hU,
    ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, star_star]

def flagMat (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ := Matrix.of fun i a => fvec k r z a i

lemma mul_flagMat (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i) (b) :
    (g * flagMat k r z) i b = (g *ᵥ fvec k r z b) i := rfl

lemma zhat_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Zhat k r z z' g = (flagMat k r z)ᴴ * (Hpk k r * (g * flagMat k r z')) := by
  ext a b
  simp only [Zhat, herm, Matrix.mul_apply, Matrix.conjTranspose_apply, flagMat, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply]

lemma exists_N (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hm : m ∈ Nset k r) :
    ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, UpUni U ∧ m * flagMat k r z = flagMat k r z * U := by
  simp only [Nset, Set.mem_setOf_eq] at hm
  obtain ⟨-, hm2, hm3⟩ := hm
  have key : ∀ (a : Fin (r + 1)) (i : Fin (2 * r + k + 1)),
      (m *ᵥ fvec k r z a) i =
        fvec k r z a i + if i.val < a.val then (m *ᵥ fvec k r z a) i else 0 := by
    intro a i
    have ha := a.isLt
    by_cases hia : i.val < a.val
    · rw [if_pos hia]
      suffices h0 : fvec k r z a i = 0 by rw [h0, zero_add]
      by_cases har : a.val < r
      · simp only [fvec, dif_pos har, bvec]
        rw [Pi.single_apply, if_neg]
        intro he
        have h1 := congrArg Fin.val he
        simp [eI] at h1
        omega
      · simp only [fvec, dif_neg har]
        exact hz i (Or.inl (by omega))
    · rw [if_neg hia, add_zero]
      by_cases har : a.val < r
      · simp only [fvec, dif_pos har, bvec]
        simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        exact hm2 ⟨a.val, har⟩ i (by show a.val ≤ i.val; omega)
      · simp only [fvec, dif_neg har]
        have hterm : ∀ j, m i j * z j = if i = j then z j else 0 := by
          intro j
          by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
          · rw [hm3 i j hj.1 hj.2 (by omega)]
            split_ifs <;> simp
          · rw [hz j (by omega)]
            simp
        simp only [Matrix.mulVec, dotProduct, hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨Matrix.of fun b a => (if b = a then 1 else 0) +
      (if hba : b.val < a.val then
        (m *ᵥ fvec k r z a) (eI k r ⟨b.val, by have := a.isLt; omega⟩) else 0), ⟨?_, ?_⟩, ?_⟩
  · intro i j hij
    have h1 : i ≠ j := hij.ne'
    have h2 : ¬ i < j := by rw [Fin.lt_def] at hij ⊢; omega
    simp [h1, h2]
  · intro i
    simp
  · ext i a
    rw [mul_flagMat, Matrix.mul_apply]
    simp only [flagMat, Matrix.of_apply, mul_add, Finset.sum_add_distrib, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [key a i]
    congr 1
    have ha := a.isLt
    by_cases hia : i.val < a.val
    · have hir : i.val < r := by omega
      rw [if_pos hia, Finset.sum_eq_single (⟨i.val, by omega⟩ : Fin (r + 1))]
      · have he : eI k r ⟨i.val, hir⟩ = i := Fin.ext rfl
        simp [fvec, hir, hia, he, bvec]
      · intro b _ hb
        split_ifs with hba
        · have hbr : b.val < r := by omega
          have hne : i ≠ eI k r ⟨b.val, hbr⟩ := by
            intro he
            apply hb
            ext
            exact (congrArg Fin.val he).symm
          simp [fvec, hbr, bvec, Pi.single_apply, hne]
        · simp
      · simp
    · rw [if_neg hia]
      symm
      apply Finset.sum_eq_zero
      intro b _
      split_ifs with hba
      · have hbr : b.val < r := by omega
        have hne : i ≠ eI k r ⟨b.val, hbr⟩ := by
          intro he
          apply hia
          rw [he]
          exact hba
        simp [fvec, hbr, bvec, Pi.single_apply, hne]
      · simp

lemma exists_S (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hs : s ∈ Sset k r z) :
    sᴴ * Hpk k r * s = Hpk k r ∧ ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, UpUni U ∧ s * flagMat k r z = flagMat k r z * U := by
  simp only [Sset, Set.mem_setOf_eq] at hs
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  obtain ⟨U, hU, hmF⟩ := exists_N k r z hz m hm
  simp only [UWset, Set.mem_setOf_eq] at hh
  obtain ⟨hhU, hfix, hhz⟩ := hh
  have hmU : mᴴ * Hpk k r * m = Hpk k r := by
    simp only [Nset, Set.mem_setOf_eq] at hm
    exact hm.1
  have hhU' : hᴴ * Hpk k r * h = Hpk k r := hhU
  refine ⟨?_, U, hU, ?_⟩
  · calc (h * m)ᴴ * Hpk k r * (h * m) = mᴴ * (hᴴ * Hpk k r * h) * m := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [hhU', hmU]
  · have hF : h * flagMat k r z = flagMat k r z := by
      ext i b
      rw [mul_flagMat]
      simp only [flagMat, Matrix.of_apply]
      by_cases hb : b.val < r
      · simp only [fvec, dif_pos hb]
        rw [(hfix ⟨b.val, hb⟩).1]
      · simp only [fvec, dif_neg hb]
        rw [hhz]
    rw [Matrix.mul_assoc, hmF, ← Matrix.mul_assoc, hF]

end GlobalTheory.LeadingMinorInv

namespace GlobalTheory

open Formalism.QuantumDeterminants LeadingMinorInv

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LimitPolyOfPeriodicSlashFamilyConst
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.QConst

open Filter Topology

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private theorem natDegree_lt_of_mem_degreeLT {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) :
    p.natDegree < w + 1 := by
  rcases eq_or_ne p 0 with rfl | h
  · simp
  · exact (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in
private theorem norm_eval_le_sum_of_mem_degreeLT {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1))
    (x : ℂ) : ‖p.eval x‖ ≤ ∑ j ∈ Finset.range (w + 1), ‖p.coeff j‖ * ‖x‖ ^ j := by
  rw [eval_eq_sum_range' (natDegree_lt_of_mem_degreeLT hp)]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp [norm_mul, norm_pow]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in
private theorem eq_C_of_eval_add_natCast_eq {Q : ℂ[X]} {n : ℕ} (hn : 0 < n)
    (hQ : ∀ x : ℂ, Q.eval (x + n) = Q.eval x) : Q = C (Q.coeff 0) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hroot : ∀ k : ℕ, IsRoot (Q - C (Q.eval 0)) ((k : ℂ) * n) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : ((k + 1 : ℕ) : ℂ) * n = (k : ℂ) * n + n := by push_cast; ring
      simp only [IsRoot.def, eval_sub, eval_C] at ih ⊢
      rw [hk, hQ]
      exact ih
  have hinf : Set.Infinite {x | IsRoot (Q - C (Q.eval 0)) x} :=
    Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k : ℂ) * n)
      (fun a b hab => by exact_mod_cast mul_right_cancel₀ hn' hab) hroot
  rw [coeff_zero_eq_eval_zero]
  exact sub_eq_zero.1 (eq_zero_of_infinite_isRoot _ hinf)

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in
private theorem tendsto_exp_neg_mul_mul_add_pow_zero {c : ℝ} (hc : 0 < c) (b : ℝ) (m : ℕ) :
    Tendsto (fun y : ℝ => Real.exp (-c * y) * (b + y) ^ m) atTop (𝓝 0) := by
  have h1 := ((isLittleO_pow_exp_pos_mul_atTop m hc).comp_tendsto
    (tendsto_atTop_add_const_left atTop b tendsto_id)).tendsto_div_nhds_zero
  have h2 := h1.const_mul (Real.exp (c * b))
  rw [mul_zero] at h2
  refine h2.congr fun y => ?_
  simp only [Function.comp_apply, id]
  rw [mul_add, Real.exp_add, neg_mul, Real.exp_neg]
  field_simp


open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in
theorem _root_.GlobalTheory.HeckeFamilyMatrices.QConst.qconst : ∀ (w n : ℕ) (V : ℍ → ℂ[X]) (Q : ℂ[X]) (C' c : ℝ), 0 < n → 0 < c → Q ∈ degreeLT ℂ (w + 1) →
    (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) →
    (∀ τ : ℍ, _root_.GlobalTheory.HeckeFamilyMatrices.slP w (_root_.GlobalTheory.HeckeFamilyMatrices.mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) →
    (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) →
    Q = C (Q.coeff 0) := by
  intro w n V Q C' c hn hc hQ hV hper h
  have hT : _root_.GlobalTheory.HeckeFamilyMatrices.mat (ModularGroup.T ^ (n : ℤ)) = !![1, (n : ℤ); 0, 1] := by
    unfold _root_.GlobalTheory.HeckeFamilyMatrices.mat
    exact ModularGroup.coe_T_zpow _
  have htrans : ∀ (τ : ℍ) (x : ℂ),
      (V τ).eval x = (V (ModularGroup.T ^ (n : ℤ) • τ)).eval (x + n) := by
    intro τ x
    rw [← hper τ, _root_.GlobalTheory.HeckeFamilyMatrices.eval_polySlash w _ _ x (hV _) (by rw [hT]; simp), hT]
    simp
  have hbound : ∀ τ : ℍ, 1 ≤ τ.im → ∀ b : ℝ, 1 + ‖(τ : ℂ)‖ ≤ b → ∀ x : ℂ,
      ‖(V τ - Q).eval x‖ ≤ C' * Real.exp (-c * τ.im) * b ^ w *
        ∑ j ∈ Finset.range (w + 1), ‖x‖ ^ j := by
    intro τ hτ b hb x
    have hC' : 0 ≤ C' := by
      have h0 := h τ hτ 0 (Nat.zero_le _)
      have : 0 < Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by positivity
      nlinarith [norm_nonneg ((V τ - Q).coeff 0)]
    rw [Finset.mul_sum]
    refine (norm_eval_le_sum_of_mem_degreeLT (Submodule.sub_mem _ (hV τ) hQ) x).trans
      (Finset.sum_le_sum fun j hj => ?_)
    have hj' : j ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    exact mul_le_mul_of_nonneg_right ((h τ hτ j hj').trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb w)
        (mul_nonneg hC' (Real.exp_pos _).le))) (by positivity)
  refine eq_C_of_eval_add_natCast_eq hn fun x => ?_
  set M : ℝ := ∑ j ∈ Finset.range (w + 1), ‖x + n‖ ^ j + ∑ j ∈ Finset.range (w + 1), ‖x‖ ^ j
  have hest : ∀ y : ℝ, 1 ≤ y → ‖Q.eval (x + n) - Q.eval x‖ ≤
      C' * M * (Real.exp (-c * y) * ((1 + n) + y) ^ w) := by
    intro y hy
    let τ : ℍ := ⟨(y : ℂ) * Complex.I, by simp; linarith⟩
    have hτim : τ.im = y := by simp [τ, UpperHalfPlane.im]
    have hτn : ‖(τ : ℂ)‖ = y := by
      simp [τ, abs_of_pos (show (0 : ℝ) < y by linarith)]
    have hτ'c : ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = τ + n := by
      rw [ModularGroup.coe_T_zpow_smul_eq]
      simp
    have hτ'im : (ModularGroup.T ^ (n : ℤ) • τ).im = y := by
      rw [← hτim, ← UpperHalfPlane.coe_im, hτ'c, ← UpperHalfPlane.coe_im]
      simp
    have hτ'n : 1 + ‖((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ)‖ ≤ (1 + n) + y := by
      rw [hτ'c]
      have := norm_add_le (τ : ℂ) (n : ℂ)
      rw [hτn, Complex.norm_natCast] at this
      linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have e1 := hbound τ (by rw [hτim]; exact hy) ((1 + n) + y) (by rw [hτn]; linarith) x
    have e2 := hbound _ (by rw [hτ'im]; exact hy) ((1 + n) + y) hτ'n (x + n)
    rw [hτim] at e1
    rw [hτ'im] at e2
    have hsplit : Q.eval (x + n) - Q.eval x =
        (V τ - Q).eval x - (V (ModularGroup.T ^ (n : ℤ) • τ) - Q).eval (x + n) := by
      simp only [eval_sub, htrans τ x]
      ring
    rw [hsplit]
    refine (norm_sub_le _ _).trans ((add_le_add e1 e2).trans (le_of_eq ?_))
    simp only [M]
    ring
  have hlim := (tendsto_exp_neg_mul_mul_add_pow_zero hc (1 + n) w).const_mul (C' * M)
  rw [mul_zero] at hlim
  have hle : ‖Q.eval (x + n) - Q.eval x‖ ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨1, hest⟩)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

end GlobalTheory.HeckeFamilyMatrices.QConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGamma1InterGamma0ExtQExpansionCoeff
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem eq_of_coef_eq : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ f g : ModularForm (GlobalTheory.Hk.lev N l) k,
    (∀ n, GlobalTheory.Hk.coef ⇑f n = GlobalTheory.Hk.coef ⇑g n) → f = g := by
  intro N l k hN f g h
  ext τ
  have hf := _root_.GlobalTheory.Hk.lev_hasSum_coef N l k hN f τ
  have hg := _root_.GlobalTheory.Hk.lev_hasSum_coef N l k hN g τ
  simp_rw [h] at hf
  exact hf.unique hg

end GlobalTheory.Hk
end

