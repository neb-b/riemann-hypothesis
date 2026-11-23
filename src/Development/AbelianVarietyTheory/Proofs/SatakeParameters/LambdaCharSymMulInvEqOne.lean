module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.SymLevelInv

open Loc LocE

section Red

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem intAt_zero : IntAt P (0 : E) := by simpa using IntAt.coe P 0
theorem intAt_one : IntAt P (1 : E) := by simpa using IntAt.coe P 1
theorem redP_zero' : redP P (0 : E) = 0 := by simpa using reduction_coe P 0
theorem reduction_one' : redP P (1 : E) = 1 := by simpa using reduction_coe P 1

def intRing : Subring E where
  carrier := {a | IntAt P a}
  mul_mem' := IntAt.mul
  one_mem' := intAt_one P
  add_mem' := IntAt.add
  zero_mem' := intAt_zero P
  neg_mem' := fun {a} ha => by
    have h := IntAt.mul (IntAt.coe P (-1)) ha
    simpa using h

def redHom : intRing P →+* 𝓞 E ⧸ P.asIdeal where
  toFun a := redP P a.1
  map_one' := reduction_one' P
  map_mul' a b := reduction_mul a.2 b.2
  map_zero' := redP_zero' P
  map_add' a b := reduction_add a.2 b.2

theorem intAt_sum {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    IntAt P (∑ i ∈ s, f i) := (intRing P).sum_mem h

theorem reduction_sum₂ {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using redP_zero' P
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      reduction_add (h a (Finset.mem_insert_self _ _))
        (intAt_sum P s f fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem reduction_det {t : ℕ} (A : Matrix (Fin t) (Fin t) E) (h : ∀ i j, IntAt P (A i j)) :
    redP P A.det = (Matrix.of fun i j => redP P (A i j)).det := by
  let B : Matrix (Fin t) (Fin t) (intRing P) := Matrix.of fun i j => ⟨A i j, h i j⟩
  have h1 : A.det = (intRing P).subtype B.det := by
    rw [RingHom.map_det]; rfl
  have h2 : (Matrix.of fun i j => redP P (A i j)).det = redHom P B.det := by
    rw [RingHom.map_det]; rfl
  rw [h1, h2]; rfl

theorem of_inv_mul {q : ℕ} (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {a : E}
    (h : IntAt P ((q : E)⁻¹ * a)) : IntAt P a ∧ redP P a = 0 := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  have e : a = algebraMap (𝓞 E) E (q : 𝓞 E) * ((q : E)⁻¹ * a) := by
    rw [map_natCast, mul_inv_cancel_left₀ hq']
  constructor
  · rw [e]; exact (IntAt.coe P _).mul h
  · rw [e, reduction_mul (IntAt.coe P _) h, reduction_coe, Ideal.Quotient.eq_zero_iff_mem.2 hP, zero_mul]

end Red

section Comb

variable {κ : Type} [CommRing κ]

theorem symIdx_cases (k rS i : ℕ) : (i < k ∧ symIdx k rS i = i + rS) ∨
    (k ≤ i ∧ i < k + rS ∧ symIdx k rS i = i - k) ∨ (k + rS ≤ i ∧ symIdx k rS i = i) := by
  unfold symIdx; split_ifs <;> omega

theorem symmetricBlockBoundary_cases (k rS s : ℕ) : (s = rS + k ∧ bd5 k rS s = rS) ∨ (s ≠ rS + k ∧ bd5 k rS s = s) := by
  unfold bd5; split_ifs <;> omega

theorem superdiag {n k₀ rS r : ℕ} (hr : k₀ + rS < r) (hn : r ≤ n) (A B : ℕ → ℕ → κ)
    (hA : ∀ l p', l < n → p' < r → bd5 k₀ rS (symIdx k₀ rS p') ≤ symIdx k₀ rS l →
      A l p' = if l = p' then 1 else 0)
    (hB : ∀ l p', l < n → p' < r → bd5 k₀ rS (symIdx k₀ rS p') ≤ symIdx k₀ rS l →
      B l p' = if l = p' then 1 else 0)
    (p : ℕ) (hp : p + 1 < r) (hp' : p + 1 ≠ k₀)
    (hAB : ∑ l ∈ Finset.range n, A p l * B l (p + 1) = 0) :
    A p (p + 1) + B p (p + 1) = 0 := by
  have hle : ∀ s, bd5 k₀ rS (symIdx k₀ rS s) ≤ symIdx k₀ rS s := by
    intro s; unfold bd5; split_ifs <;> omega
  rw [Finset.sum_eq_add_of_mem p (p + 1) (by simp; omega) (by simp; omega) (by omega)] at hAB
  · rw [hA p p (by omega) (by omega) (hle p), hB (p + 1) (p + 1) (by omega) hp (hle _)] at hAB
    simpa [add_comm] using hAB
  · rintro l hl ⟨h1, h2⟩
    rw [Finset.mem_range] at hl
    by_cases h : bd5 k₀ rS (symIdx k₀ rS (p + 1)) ≤ symIdx k₀ rS l
    · rw [hB l (p + 1) hl hp h, if_neg h2, mul_zero]
    · have h3 : l < r ∧ bd5 k₀ rS (symIdx k₀ rS l) ≤ symIdx k₀ rS p := by
        have e1 := symIdx_cases k₀ rS l
        have e2 := symIdx_cases k₀ rS p
        have e3 := symIdx_cases k₀ rS (p + 1)
        have e4 := symmetricBlockBoundary_cases k₀ rS (symIdx k₀ rS l)
        have e5 := symmetricBlockBoundary_cases k₀ rS (symIdx k₀ rS (p + 1))
        constructor <;> omega
      rw [hA p l (by omega) h3.1 h3.2, if_neg (Ne.symm h1), zero_mul]

theorem block {n a t : ℕ} (hn : a + t ≤ n) (A B : ℕ → ℕ → κ)
    (hA : ∀ l l', l < n → l' < a → a ≤ l → A l l' = 0)
    (hB : ∀ l l', l < n → l' < a + t → a + t ≤ l → B l l' = 0)
    (hAB : ∀ p p', p < n → p' < n →
      ∑ l ∈ Finset.range n, A p l * B l p' = if p = p' then 1 else 0) :
    (Matrix.of fun s s' : Fin t => A (a + s.1) (a + s'.1)).det *
      (Matrix.of fun s s' : Fin t => B (a + s.1) (a + s'.1)).det = 1 := by
  rw [← Matrix.det_mul]
  convert Matrix.det_one (n := Fin t) (R := κ)
  ext s s'
  have hs := s.2
  have hs' := s'.2
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun l => A (a + s.1) (a + l) * B (a + l) (a + s'.1)) t]
  have h := hAB (a + s.1) (a + s'.1) (by omega) (by omega)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range a),
    Finset.sum_eq_zero (s := Finset.range m), zero_add, add_zero] at h
  · rw [h, Matrix.one_apply]
    simp [Fin.ext_iff]
  · intro l hl
    rw [Finset.mem_range] at hl
    rw [hB _ _ (by omega) (by omega) (by omega), mul_zero]
  · intro l hl
    rw [Finset.mem_range] at hl
    rw [hA _ _ (by omega) (by omega) (by omega), zero_mul]

end Comb

section Main

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

def mat {N : ℕ} (g : Sp E N → Sp E N) (p p' : ℕ) : E := atN (g (eN E N p')) p

theorem mem_sclLat {N : ℕ} (e : ℕ → ℤ) (v : Sp E N) :
    v ∈ sclLat P q N e ↔ ∀ l : Fin N, IntAt P (((q : E) ^ e l.1)⁻¹ * v l) := by
  unfold sclLat stdAt
  rw [Submodule.mem_comap, mem_localization_standardLattice]
  rfl

omit [NumberField E] [StarRing E] in
theorem fIdx_zero (k₀ n s : ℕ) : fIdx k₀ 0 n s = s := by
  unfold fIdx; split_ifs <;> omega

theorem fPos_zero {k₀ n l : ℕ} (h : l < n) : fPos k₀ 0 n l = l := by
  unfold fPos; split_ifs <;> omega

theorem scE_lt {n l : ℕ} (ex : ℕ → ℕ) (h : l < n) : scE n ex l = 0 := if_pos h

omit [NumberField E] [StarRing E] in
theorem entB_zero (k₀ n : ℕ) (ex : ℕ → ℕ) (g : HomE E (n + 0) (n + 0)) {p p' : ℕ} (hp : p < n) (hp' : p' < n) :
    entB q k₀ 0 n 0 n ex ex g p p' = mat g p p' := by
  unfold entB mat
  rw [fIdx_zero, fIdx_zero, scE_lt _ hp, scE_lt _ hp']
  simp


variable {P q}

theorem intAt_ite (c : Prop) [Decidable c] : IntAt P (if c then (1 : E) else 0) := by
  split_ifs
  · exact intAt_one P
  · exact intAt_zero P

theorem mat_intAt {k₀ rS r t n : ℕ} {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)} (hg : g ∈ JGsym P q k₀ rS r t n 0)
    (p p' : ℕ) (hp : p < n) : IntAt P (mat g p p') := by
  have h : eN E (n + 0) p' ∈ lamY P q n 0 fun i => i + 1 := by
    unfold lamY
    rw [mem_sclLat]
    intro l
    rw [scE_lt _ (show l.1 < n from l.2), zpow_zero, inv_one, one_mul]
    exact intAt_ite _
  have h2 := (hg.1 _).2 h
  unfold lamY at h2
  rw [mem_sclLat] at h2
  have h3 := h2 ⟨p, hp⟩
  rw [scE_lt _ hp, zpow_zero, inv_one, one_mul] at h3
  unfold mat atN
  rw [dif_pos (show p < n + 0 from hp)]
  exact h3

theorem mat_col (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {k₀ rS r t n : ℕ} (hr : k₀ + rS < r) (hn : r ≤ n)
    {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)} (hg : g ∈ JGsym P q k₀ rS r t n 0)
    (l p' : ℕ) (hl : l < n) (hp' : p' < r) (h : bd5 k₀ rS (symIdx k₀ rS p') ≤ symIdx k₀ rS l) :
    redP P (mat g l p') = if l = p' then 1 else 0 := by
  have h1 := (hg.2.2 (symIdx k₀ rS p') (symIdx_lt hr.le hp')).2
  have e : bvecS E q k₀ rS n 0 (symIdx k₀ rS p') = eN E (n + 0) p' := by
    unfold bvecS bvecG
    rw [symIdxInv_symIdx, fIdx_zero, scE_lt _ (show p' < n by omega), zpow_zero, one_smul]
  rw [e] at h1
  unfold flagS at h1
  rw [mem_sclLat] at h1
  have h2 := h1 ⟨l, hl⟩
  simp only [] at h2
  rw [scE_lt _ hl, fPos_zero hl, if_pos h, zero_add, zpow_one] at h2
  obtain ⟨h3, h4⟩ := of_inv_mul P hq hP h2
  have e2 : mat g l p' = (g (eN E (n + 0) p') - eN E (n + 0) p') ⟨l, hl⟩ + if l = p' then 1 else 0 := by
    unfold mat atN
    rw [dif_pos (show l < n + 0 from hl), Pi.sub_apply]
    exact (sub_add_cancel _ _).symm
  rw [e2, reduction_add h3 (intAt_ite _), h4, zero_add]
  split_ifs
  · exact reduction_one' P
  · exact redP_zero' P

theorem mat_blk (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {k₀ rS r t n : ℕ} (hr : k₀ + rS < r)
    {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)} (hg : g ∈ JGsym P q k₀ rS r t n 0) (i : ℕ)
    (l l' : ℕ) (hl : l < n) (hl' : l' < r + i * t) (h : r + i * t ≤ l) :
    redP P (mat g l l') = 0 := by
  have key : ∀ x, bd5 k₀ rS (r + i * t) ≤ symIdx k₀ rS x ↔ r + i * t ≤ x := by
    intro x
    have e1 := symIdx_cases k₀ rS x
    have e2 := symmetricBlockBoundary_cases k₀ rS (r + i * t)
    generalize i * t = m at *
    omega
  have h0 : eN E (n + 0) l' ∈ flagS P q k₀ rS n 0 (r + i * t) := by
    unfold flagS
    rw [mem_sclLat]
    intro x
    have hx : x.1 < n := x.2
    by_cases hxl : x.1 = l'
    · rw [scE_lt _ hx, fPos_zero hx, if_neg (by rw [key]; omega), zero_add, zpow_zero, inv_one, one_mul]
      exact intAt_ite _
    · unfold eN
      rw [if_neg hxl, mul_zero]
      exact intAt_zero P
  have h1 := (hg.2.1 (r + i * t) ⟨i, rfl⟩ _).2 h0
  unfold flagS at h1
  rw [mem_sclLat] at h1
  have h2 := h1 ⟨l, hl⟩
  simp only [] at h2
  rw [scE_lt _ hl, fPos_zero hl, if_pos ((key l).2 h), zero_add, zpow_one] at h2
  unfold mat atN
  rw [dif_pos (show l < n + 0 from hl)]
  exact (of_inv_mul P hq hP h2).2

theorem redP_superdiag {k₀ rS r t n : ℕ} (hr : k₀ + rS < r) (hn : r ≤ n)
    {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)} (hg : g ∈ JGsym P q k₀ rS r t n 0) (ex : ℕ → ℕ) :
    redP P (∑ i ∈ Finset.range (k₀ - 1), entB q k₀ 0 n 0 n ex ex g.toLinearMap i (i + 1) +
      ∑ i ∈ Finset.range (r - k₀ - 1), entB q k₀ 0 n 0 n ex ex g.toLinearMap (k₀ + i) (k₀ + i + 1)) =
    ∑ i ∈ Finset.range (k₀ - 1), redP P (mat g i (i + 1)) +
      ∑ i ∈ Finset.range (r - k₀ - 1), redP P (mat g (k₀ + i) (k₀ + i + 1)) := by
  have e1 : ∑ i ∈ Finset.range (k₀ - 1), entB q k₀ 0 n 0 n ex ex g.toLinearMap i (i + 1) =
      ∑ i ∈ Finset.range (k₀ - 1), mat g i (i + 1) :=
    Finset.sum_congr rfl fun i hi => by
      rw [Finset.mem_range] at hi
      exact entB_zero q k₀ n ex _ (by omega) (by omega)
  have e2 : ∑ i ∈ Finset.range (r - k₀ - 1), entB q k₀ 0 n 0 n ex ex g.toLinearMap (k₀ + i) (k₀ + i + 1) =
      ∑ i ∈ Finset.range (r - k₀ - 1), mat g (k₀ + i) (k₀ + i + 1) :=
    Finset.sum_congr rfl fun i hi => by
      rw [Finset.mem_range] at hi
      exact entB_zero q k₀ n ex _ (by omega) (by omega)
  have i1 : ∀ i ∈ Finset.range (k₀ - 1), IntAt P (mat g i (i + 1)) := fun i hi => by
    rw [Finset.mem_range] at hi
    exact mat_intAt hg _ _ (by omega)
  have i2 : ∀ i ∈ Finset.range (r - k₀ - 1), IntAt P (mat g (k₀ + i) (k₀ + i + 1)) := fun i hi => by
    rw [Finset.mem_range] at hi
    exact mat_intAt hg _ _ (by omega)
  rw [e1, e2, reduction_add (intAt_sum P _ _ i1) (intAt_sum P _ _ i2), reduction_sum₂ P _ _ i1, reduction_sum₂ P _ _ i2]

theorem redP_det_blk {k₀ rS r t n a : ℕ} (hn : a + t ≤ n)
    {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)} (hg : g ∈ JGsym P q k₀ rS r t n 0) (ex : ℕ → ℕ) :
    redP P (Matrix.det (Matrix.of fun s s' : Fin t =>
      entB q k₀ 0 n 0 n ex ex g.toLinearMap (a + s.1) (a + s'.1))) =
    Matrix.det (Matrix.of fun s s' : Fin t => redP P (mat g (a + s.1) (a + s'.1))) := by
  have e : (Matrix.of fun s s' : Fin t => entB q k₀ 0 n 0 n ex ex g.toLinearMap (a + s.1) (a + s'.1)) =
      Matrix.of fun s s' : Fin t => mat g (a + s.1) (a + s'.1) := by
    ext s s'
    have := s.2
    have := s'.2
    exact entB_zero q k₀ n ex _ (by omega) (by omega)
  rw [e]
  exact reduction_det P (Matrix.of fun s s' : Fin t => mat g (a + s.1) (a + s'.1))
    fun s s' => mat_intAt hg (a + s.1) (a + s'.1) (by have := s.2; omega)

end Main

end GlobalTheory.SymLevelInv
