module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0014
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0006
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamDeg

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinPosEqCast
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Finset Formalism.GM Formalism.GM.M
open scoped Nat

section Block

variable (p : ℕ) [hp : Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

def dTot (a : Fin (N + 1)) : ℕ :=
  (∑ i, G.T.z i • (if M.finPos N (G.T.pos i) = a then 1 else 0)) +
    G.zPlus • (if Fin.castSucc G.uPos = a then 1 else 0) + chDeg G.LL a + (if Fin.last N = a then G.B else 0)

theorem chDeg_cast (LL : M.Letters N) (a0 : Fin N) : chDeg LL (Fin.castSucc a0) = LL.deg a0 := by
  unfold chDeg
  rw [Finset.sum_eq_single a0]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.castSucc_injective _ h)
  · intro h
    exact absurd (Finset.mem_univ a0) h

theorem chDeg_last (LL : M.Letters N) : chDeg LL (Fin.last N) = 0 := by
  unfold chDeg
  apply Finset.sum_eq_zero
  intro b _
  rw [if_neg]
  exact Fin.castSucc_ne_last b

theorem finPos_eq_cast (k : ℕ) (hk : k < N) (a0 : Fin N) : M.finPos N k = Fin.castSucc a0 ↔ (a0 : ℕ) = k := by
  unfold M.finPos
  rw [Fin.ext_iff]
  simp only [Fin.coe_castSucc]
  rw [min_eq_left hk.le]
  exact eq_comm

theorem finPos_ne_last (k : ℕ) (hk : k < N) : M.finPos N k ≠ Fin.last N := by
  unfold M.finPos
  rw [Ne, Fin.ext_iff]
  simp only [Fin.val_last]
  rw [min_eq_left hk.le]
  exact hk.ne

theorem level_room (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (hl : G.LevelOK j jp) (a0 : Fin N) :
    (∑ i, if (a0 : ℕ) = G.T.pos i ∨ (a0 : ℕ) = G.T.pos i + 1 then j i else 0) + (if a0 = G.uPos then jp else 0) ≤
      G.LL.deg a0 := by
  obtain ⟨⟨hmono, hvec, _⟩, hlt, _, _⟩ := hB
  obtain ⟨hj, hjp⟩ := hl
  have hdisj : ∀ b c : Fin G.T.t, G.T.pos b + 1 ≠ G.T.pos c := by
    intro b c h
    obtain ⟨hb1, _, hbf⟩ := hvec b
    obtain ⟨hc1, hct, _⟩ := hvec c
    have e : (⟨G.T.pos b + 1, hb1⟩ : Fin N) = ⟨G.T.pos c, by omega⟩ := Fin.ext h
    rw [e] at hbf
    rw [hbf] at hct
    exact Bool.false_ne_true hct
  by_cases hu : a0 = G.uPos
  · rw [if_pos hu, Finset.sum_eq_zero]
    · rw [hu]
      omega
    intro i _
    rw [if_neg]
    have h1 := hlt i
    have h2 : (a0 : ℕ) = G.uPos := by rw [hu]
    omega
  · rw [if_neg hu, add_zero]
    by_cases hex : ∃ i, (a0 : ℕ) = G.T.pos i ∨ (a0 : ℕ) = G.T.pos i + 1
    · obtain ⟨i0, hi0⟩ := hex
      rw [Finset.sum_eq_single i0]
      · rw [if_pos hi0]
        obtain ⟨hN0, _, _⟩ := hvec i0
        rcases hi0 with h | h
        · exact (hj i0).1.trans_eq (congrArg G.LL.deg (Fin.ext (by simp; omega)))
        · exact (hj i0).2.trans_eq (congrArg G.LL.deg (Fin.ext (by simp; omega)))
      · intro b _ hb
        rw [if_neg]
        intro hb'
        rcases hb' with h1 | h1 <;> rcases hi0 with h2 | h2
        · exact hb (hmono.injective (by omega))
        · exact hdisj i0 b (by omega)
        · exact hdisj b i0 (by omega)
        · exact hb (hmono.injective (by omega))
      · intro h'
        exact absurd (Finset.mem_univ i0) h'
    · push_neg at hex
      rw [Finset.sum_eq_zero]
      · exact Nat.zero_le _
      intro i _
      rw [if_neg]
      intro h
      rcases h with h | h
      · exact (hex i).1 h
      · exact (hex i).2 h

theorem dLvl_eq (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (hl : G.LevelOK j jp) (a : Fin (N + 1)) :
    dLvl G j jp a = dTot G a := by
  have hvec := hB.1.2.1
  have hjp := hl.2
  have hposN : ∀ i, G.T.pos i + 1 < N := fun i => (hvec i).1
  induction a using Fin.lastCases with
  | last =>
    have hA : (∑ i, j i • ((if M.finPos N (G.T.pos i) = Fin.last N then 1 else 0) +
        (if M.finPos N (G.T.pos i + 1) = Fin.last N then 1 else 0))) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg (finPos_ne_last _ (by have := hposN i; omega)), if_neg (finPos_ne_last _ (hposN i))]
      simp
    have hu : ¬ Fin.castSucc G.uPos = Fin.last N := Fin.castSucc_ne_last _
    unfold dLvl dTot
    rw [hA, chDeg_last, chDeg_last, if_neg hu, if_pos rfl, if_pos rfl, if_pos rfl]
    simp only [smul_eq_mul]
    omega
  | cast a0 =>
    have hA : (∑ i, j i • ((if M.finPos N (G.T.pos i) = Fin.castSucc a0 then 1 else 0) +
        (if M.finPos N (G.T.pos i + 1) = Fin.castSucc a0 then 1 else 0))) =
        ∑ i, if (a0 : ℕ) = G.T.pos i ∨ (a0 : ℕ) = G.T.pos i + 1 then j i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      have e1 := finPos_eq_cast (G.T.pos i) (by have := hposN i; omega) a0
      have e2 := finPos_eq_cast (G.T.pos i + 1) (hposN i) a0
      by_cases h1 : (a0 : ℕ) = G.T.pos i
      · have h2 : ¬ (a0 : ℕ) = G.T.pos i + 1 := by omega
        simp only [e1, e2, h1, h2, if_true, if_false, or_false]
        simp
      · by_cases h2 : (a0 : ℕ) = G.T.pos i + 1
        · simp only [e1, e2, h1, h2, if_true, if_false, or_true]
          simp
        · simp only [e1, e2, h1, h2, if_false, or_false]
          simp
    have hB' : jp • ((if Fin.castSucc G.uPos = Fin.castSucc a0 then 1 else 0) +
        (if Fin.last N = Fin.castSucc a0 then 1 else 0)) = if a0 = G.uPos then jp else 0 := by
      have hL : ¬ Fin.last N = Fin.castSucc a0 := fun h => Fin.castSucc_ne_last a0 h.symm
      rw [if_neg hL]
      by_cases h : a0 = G.uPos
      · rw [if_pos (by rw [h]), if_pos h]
        simp
      · rw [if_neg (fun e => h (Fin.castSucc_injective _ e).symm), if_neg h]
        simp
    have hC : chDeg (G.lettersAt j jp) (Fin.castSucc a0) =
        (G.LL.deg a0 - ∑ i, if (a0 : ℕ) = G.T.pos i ∨ (a0 : ℕ) = G.T.pos i + 1 then j i else 0) -
          (if a0 = G.uPos then jp else 0) := by
      rw [chDeg_cast]
      rfl
    have hD := level_room G hB j jp hl a0
    have hL : ¬ Fin.last N = Fin.castSucc a0 := fun h => Fin.castSucc_ne_last a0 h.symm
    unfold dLvl dTot
    rw [hA, hB', hC, chDeg_cast, if_neg hL, if_neg hL]
    omega

theorem sum_ite_inj_le {ι α : Type} [Fintype ι] [DecidableEq α] (x : ι → α) (hx : Function.Injective x) (n : ι → ℕ)
    (a : α) (Mx : ℕ) (h : ∀ i, n i ≤ Mx) : ∑ i, n i • (if x i = a then 1 else 0) ≤ Mx := by
  by_cases hex : ∃ i, x i = a
  · obtain ⟨i0, hi0⟩ := hex
    rw [Finset.sum_eq_single i0]
    · simp [hi0, h i0]
    · intro b _ hb
      rw [if_neg]
      · simp
      intro hba
      exact hb (hx (hba.trans hi0.symm))
    · intro h'
      exact absurd (Finset.mem_univ i0) h'
  · push_neg at hex
    rw [Finset.sum_eq_zero]
    · exact Nat.zero_le _
    intro i _
    simp [hex i]

theorem dTot_le (hB : G.BlockOK) (A : ℕ) (hdeg : ∀ x, G.LL.deg x ≤ 2 * A) (hBa : G.B ≤ 2 * A)
    (hz : ∀ i, G.T.z i ≤ 2 * A) (hzp : G.zPlus ≤ 2 * A) (a : Fin (N + 1)) : dTot G a ≤ 8 * A := by
  classical
  have hpN : ∀ i, G.T.pos i + 1 < N := fun i => (hB.2.1 i).trans G.uPos.2
  have hinj : Function.Injective (fun i => M.finPos N (G.T.pos i)) := by
    intro i i' h
    have h' : min (G.T.pos i) N = min (G.T.pos i') N := congrArg Fin.val h
    have h1 := hpN i
    have h2 := hpN i'
    exact hB.1.1.injective (by omega)
  have e1 := sum_ite_inj_le (fun i => M.finPos N (G.T.pos i)) hinj G.T.z a (2 * A) hz
  have e2 : G.zPlus • (if Fin.castSucc G.uPos = a then 1 else 0) ≤ 2 * A := by
    split_ifs <;> simp [hzp]
  have e3 : chDeg G.LL a ≤ 2 * A := by
    induction a using Fin.lastCases with
    | last => rw [chDeg_last]; exact Nat.zero_le _
    | cast a0 => rw [chDeg_cast]; exact hdeg a0
  have e4 : (if Fin.last N = a then G.B else 0) ≤ 2 * A := by
    split_ifs
    · exact hBa
    · exact Nat.zero_le _
  unfold dTot
  omega

theorem val_gen (hB : G.BlockOK) (A : ℕ) (hdeg : ∀ x, G.LL.deg x ≤ 2 * A) (hBa : G.B ≤ 2 * A)
    (hz : ∀ i, G.T.z i ≤ 2 * A) (hzp : G.zPlus ≤ 2 * A)
    (j : Fin G.T.t → ℕ) (jp : ℕ) (hl : G.LevelOK j jp) (j' : Fin G.T.t → ℕ) (jp' : ℕ) (hl' : G.LevelOK j' jp')
    (μ : M.BVar N r G.T.t →₀ ℕ) (hw : ∀ a, Finsupp.weight (wL (r := r) G a) μ = dLvl G j' jp' a) :
    padicValNat p (lvC (r := r) G j jp * degFact G j jp) ≤ padicValNat p (μ.prod fun _ k => k !) +
      (((N + 1) * r + (G.T.t + 1) * 2) + (G.T.t + 1)) * Nat.log p (8 * A + r) := by
  have hL : ∀ n, n ≤ 8 * A + r → Nat.log p n ≤ Nat.log p (8 * A + r) :=
    fun n hn => Nat.log_mono_right hn
  have hld : ∀ x, (G.lettersAt j jp).deg x ≤ 2 * A := by
    intro x
    have := hdeg x
    simp only [M.BlockData.lettersAt]
    omega
  have hj : ∀ i, j i ≤ 2 * A := fun i => (hl.1 i).1.trans (hdeg _)
  have h1 := val_lvC_le (r := r) p G j jp (Nat.log p (8 * A + r))
    (fun i => hL _ (by
      have := hld (G.letterAt (G.T.pos i))
      have := hld (G.letterAt (G.T.pos i + 1))
      have := hz i
      have := hj i
      omega))
    (hL _ (by
      have := hdeg G.uPos
      have := hl.2
      have := hzp
      have := hBa
      omega))
  have h2 := val_letters_le p G μ (dLvl G j' jp') hw (Nat.log p (8 * A + r))
    (fun a => hL _ (by
      rw [dLvl_eq G hB j' jp' hl' a]
      have := dTot_le G hB A hdeg hBa hz hzp a
      omega))
  have hprod : ∏ a, (dLvl G j jp a)! = ∏ a, (dLvl G j' jp' a)! := by
    apply Finset.prod_congr rfl
    intro a _
    rw [dLvl_eq G hB j jp hl a, dLvl_eq G hB j' jp' hl' a]
  rw [hprod] at h1
  rw [Nat.add_mul ((N + 1) * r + (G.T.t + 1) * 2) (G.T.t + 1)]
  omega

end Block

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.OrthCountOf
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

def OrthBasisLat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])),
    p ≠ 2 → FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) → L.FG →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) →
    ∃ (m : ℕ) (f : Fin m → MvPolynomial σ ℚ_[p]), (∀ a, f a ∈ L) ∧ LinearIndependent ℤ_[p] f ∧
      Submodule.span ℤ_[p] (Set.range f) = L ∧ ∀ a b, a ≠ b → B (f a) (f b) = 0

def OrthCount : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (D : ℤ),
    FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) →
    ∀ (m : ℕ) (f : Fin m → MvPolynomial σ ℚ_[p]), (∀ a, f a ∈ L) → LinearIndependent ℤ_[p] f →
      Submodule.span ℤ_[p] (Set.range f) = L → (∀ a b, a ≠ b → B (f a) (f b) = 0) →
      ∃ (n₁ : ℕ) (e : Fin n₁ → MvPolynomial σ ℚ_[p]), (∀ a, e a ∈ L) ∧ LinearIndependent ℤ_[p] e ∧
        (∀ a b, a ≠ b → B (e a) (e b) = 0) ∧ (∀ a, B (e a) (e a) ≠ 0 ∧ (B (e a) (e a)).valuation ≤ D) ∧
        n₁ ≤ Module.finrank ℤ_[p] L ∧ Module.finrank ℤ_[p] L ≤ n₁ + Formalism.GM.M.bad p B L D


open Classical in
def GoodLeSmall : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (D : ℤ),
    FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) →
    ∀ (m : ℕ) (f : Fin m → MvPolynomial σ ℚ_[p]), (∀ a, f a ∈ L) → LinearIndependent ℤ_[p] f →
      Submodule.span ℤ_[p] (Set.range f) = L → (∀ a b, a ≠ b → B (f a) (f b) = 0) →
      Formalism.GM.M.goodCount p B L D ≤
        (Finset.univ.filter (fun a : Fin m => B (f a) (f a) ≠ 0 ∧ (B (f a) (f a)).valuation ≤ D)).card

open Classical in
theorem orthCount_of (h : GoodLeSmall) : OrthCount := by
  intro p _ σ B L W D hW hLW hsm hadd hsym m f hfL hli hspan horth
  have hgood := h p σ B L W D hW hLW hsm hadd hsym m f hfL hli hspan horth
  have hrank : Module.finrank ℤ_[p] L = m := by
    rw [← hspan, finrank_span_eq_card hli, Fintype.card_fin]
  set S := Finset.univ.filter
    (fun a : Fin m => B (f a) (f a) ≠ 0 ∧ (B (f a) (f a)).valuation ≤ D) with hS
  refine ⟨S.card, fun a => f (S.orderEmbOfFin rfl a), fun a => hfL _,
    hli.comp _ (S.orderEmbOfFin rfl).injective, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact horth _ _ (fun h' => hab ((S.orderEmbOfFin rfl).injective h'))
  · intro a
    have hmem := S.orderEmbOfFin_mem rfl a
    exact (Finset.mem_filter.mp hmem).2
  · rw [hrank]
    exact (Finset.card_le_univ S).trans (le_of_eq (Fintype.card_fin m))
  · unfold Formalism.GM.M.bad
    rw [hrank]
    omega

theorem orthLat_of (h1 : OrthBasisLat) (h2 : OrthCount) : OrthLat := by
  intro p _ σ B L W D hp2 hW hLW hfg hsm hadd hsym
  obtain ⟨m, f, hfL, hli, hspan, horth⟩ := h1 p σ B L W hp2 hW hLW hfg hsm hadd hsym
  exact h2 p σ B L W D hW hLW hsm hadd hsym m f hfL hli hspan horth

end Formalism.MainNotions.G.SymmetricFormBlocks

end

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem orthLat_of' (h1 : OrthBasisLat) (h2 : GoodLeSmall) : OrthLat := orthLat_of h1 (orthCount_of h2)

end Formalism.MainNotions.G.SymmetricFormBlocks
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PhisBSelfAdj
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Gen

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem foldr_comm_of (φ : ι → V →ₗ[K] V) (ψ : V →ₗ[K] V) (l : List ι) (h : ∀ j ∈ l, ∀ x, ψ (φ j x) = φ j (ψ x))
    (x : V) : ψ ((l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) x) = (l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) (ψ x) := by
  induction l generalizing x with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply]
    rw [h j (by simp), ih (fun k hk => h k (by simp [hk]))]

theorem foldr_selfAdj (B : V → V → K) (hB : ∀ a b, B a b = B b a) (φ : ι → V →ₗ[K] V) (l : List ι)
    (hs : ∀ i ∈ l, ∀ a b, B (φ i a) b = B (φ i b) a)
    (hc : l.Pairwise (fun i j => ∀ x, φ i (φ j x) = φ j (φ i x))) (a b : V) :
    B ((l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) a) b = B ((l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) b) a := by
  induction l generalizing a b with
  | nil => simpa using hB a b
  | cons j l ih =>
    rw [List.pairwise_cons] at hc
    have hsl : ∀ i ∈ l, ∀ a b, B (φ i a) b = B (φ i b) a := fun i hi => hs i (by simp [hi])
    have hcomm := foldr_comm_of φ (φ j) l (fun i hi x => (hc.1 i hi x)) b
    simp only [List.foldr_cons, LinearMap.comp_apply]
    rw [hs j (by simp), hB, ih hsl hc.2, hcomm]

end Gen

def RestTieComm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (G : Formalism.GM.M.BlockData N), G.BlockOK →
    ∀ (j : Fin G.T.t → ℕ) (jp : ℕ) (i i' : Fin G.T.t), i ≠ i' → ∀ x : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p],
      Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i), c))
                (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i + 1), c))
                ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)))
                (G.T.z i)
        (Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i'), c))
          (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i' + 1), c))
          ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i'))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i' + 1)))
          (G.T.z i') x) =
      Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i'), c))
                (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i' + 1), c))
                ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i'))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i' + 1)))
                (G.T.z i')
        (Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i), c))
          (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i + 1), c))
          ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)))
          (G.T.z i) x)

theorem phisB_selfAdj (hT : RestTieComm) (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)
    (hG : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    Formalism.GM.M.fockK (phisB p (r := r) G j jp u) v = Formalism.GM.M.fockK (phisB p (r := r) G j jp v) u := by
  have hfk : ∀ F G : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p],
      Formalism.GM.M.fockK F G = Formalism.GM.M.fock p F G := fun F G => rfl
  unfold phisB
  rw [hfk, hfk]
  refine foldr_selfAdj (fun a b => Formalism.GM.M.fock p a b) (fun a b => by apply Formalism.GM.GammaExpansion.fock_comm) _ _
    (fun i _ a b => by apply Formalism.GM.GammaExpansion.fock_phi_symm) ?_ u v
  refine (List.nodup_finRange G.T.t).pairwise_of_forall_ne fun i _ i' _ hii' x => ?_
  exact hT p N r G hG j jp i i' hii' x

theorem restSymm_of (hT : RestTieComm) (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) : RestSymm C0 CE1 CE2 X := by
  intro dl _ aTop _ x _ u _ v _
  unfold bePhi
  congr 1
  exact phisB_selfAdj hT X.p _ (gB_blockOK C0 CE1 CE2 X aTop 0 x.1) _ _ u v

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

