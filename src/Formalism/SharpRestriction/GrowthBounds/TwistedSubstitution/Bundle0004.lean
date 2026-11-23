module

public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Bundle0003

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Lemma5aGeneratorProducts
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting

def pairSet (O : Type) [CommRing O] (r K : ℕ) [NeZero r] [NeZero K] {n' : ℕ} [NeZero n'] (F : Frames n' r)
    (j : ℤ) (m : ℤ → ℤ) (th : ℤ → ℝ) : Set (SegRing O r K) :=
  {P | ∃ (A : MvPolynomial (ℤ × Fin r) O) (G : MvPolynomial (ℤ × Fin K) O) (M : ℤ → ℤ),
      A ∈ supported O {v : ℤ × Fin r | v.1 ∈ F.letters j} ∧
      G ∈ supported O {v : ℤ × Fin K | v.1 ∈ F.letters j ∧ ¬ F.IsW j v.1} ∧
      (∀ x ∈ F.letters j, ¬ F.IsW j x →
        (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
            ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
        (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
            ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
        geR (valS LZ {y | y < x} A) (th x)) ∧
      P = plEmb O r K A * nmEmb O r K G}

section Multi

variable (p : ℕ) {n' m r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) (F : Frames n' r)

def symG (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) (x : ℤ → SegRing O r K) :
    MvPolynomial (TV n' (m + 1)) (KK O) :=
  MvPolynomial.map (algebraMap O (KK O))
    (rename (castV hk) ((∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (x j)) * monomial l 1) * monomial ga 1)

theorem symG_update (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) (x : ℤ → SegRing O r K) (k : ℕ)
    (hk' : k ∈ Finset.range F.J) (y : SegRing O r K) :
    symG p O hk F l ga (Function.update x (k : ℤ) y) =
      MvPolynomial.map (algebraMap O (KK O))
        (rename (castV hk) (phSeg O K p F (k : ℤ) y *
          ((∏ j ∈ (Finset.range F.J).erase k, phSeg O K p F (j : ℤ) (x j)) * monomial l 1)) * monomial ga 1) := by
  unfold symG
  have he : ∏ j ∈ (Finset.range F.J).erase k, phSeg O K p F (j : ℤ) (Function.update x (k : ℤ) y j) =
      ∏ j ∈ (Finset.range F.J).erase k, phSeg O K p F (j : ℤ) (x j) :=
    Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (by exact_mod_cast Finset.ne_of_mem_erase hj)]
  rw [← Finset.mul_prod_erase _ _ hk', he, Function.update_self, mul_assoc]

theorem symG_zero (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) (x : ℤ → SegRing O r K) (k : ℕ)
    (hk' : k ∈ Finset.range F.J) : symG p O hk F l ga (Function.update x (k : ℤ) 0) = 0 := by
  rw [symG_update p O hk F l ga x k hk' 0]
  simp

theorem symG_add (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) (x : ℤ → SegRing O r K) (k : ℕ)
    (hk' : k ∈ Finset.range F.J) (a b : SegRing O r K) :
    symG p O hk F l ga (Function.update x (k : ℤ) (a + b)) =
      symG p O hk F l ga (Function.update x (k : ℤ) a) + symG p O hk F l ga (Function.update x (k : ℤ) b) := by
  rw [symG_update p O hk F l ga x k hk', symG_update p O hk F l ga x k hk',
    symG_update p O hk F l ga x k hk', map_add, add_mul, map_add, add_mul, map_add]

theorem symG_smul (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ) (x : ℤ → SegRing O r K) (k : ℕ)
    (hk' : k ∈ Finset.range F.J) (c : O) (a : SegRing O r K) :
    symG p O hk F l ga (Function.update x (k : ℤ) (c • a)) =
      algebraMap O (KK O) c • symG p O hk F l ga (Function.update x (k : ℤ) a) := by
  rw [symG_update p O hk F l ga x k hk', symG_update p O hk F l ga x k hk', map_smul, smul_mul_assoc,
    map_smul, smul_mul_assoc, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C,
    ← MvPolynomial.smul_eq_C_mul]

theorem symG_span (Q : Submodule (KK O) (MvPolynomial (TV n' (m + 1)) (KK O))) (Sj : ℤ → Set (SegRing O r K))
    (l : Fin n' × Fin (r + K) →₀ ℕ) (ga : TV n' (m + 1) →₀ ℕ)
    (h : ∀ x : ℤ → SegRing O r K, (∀ j : ℕ, j < F.J → x j ∈ Sj j) → symG p O hk F l ga x ∈ Q) :
    ∀ x : ℤ → SegRing O r K, (∀ j : ℕ, j < F.J → x j ∈ Submodule.span O (Sj j)) → symG p O hk F l ga x ∈ Q := by
  have key : ∀ k : ℕ, ∀ x : ℤ → SegRing O r K,
      (∀ j : ℕ, j < F.J → (j < k → x j ∈ Submodule.span O (Sj j)) ∧ (k ≤ j → x j ∈ Sj j)) →
        symG p O hk F l ga x ∈ Q := by
    intro k
    induction k with
    | zero =>
      intro x hx
      exact h x (fun j hj => (hx j hj).2 (Nat.zero_le j))
    | succ k ih =>
      intro x hx
      by_cases hkJ : k < F.J
      · have hk' : k ∈ Finset.range F.J := Finset.mem_range.2 hkJ
        have hspan : ∀ y ∈ Submodule.span O (Sj k),
            symG p O hk F l ga (Function.update x (k : ℤ) y) ∈ Q := by
          intro y hy
          induction hy using Submodule.span_induction with
          | mem y hyS =>
            apply ih
            intro j hj
            by_cases hjk : j = k
            · rw [hjk, Function.update_self]
              exact ⟨fun h' => absurd h' (lt_irrefl _), fun _ => hyS⟩
            · have hne : (j : ℤ) ≠ (k : ℤ) := by exact_mod_cast hjk
              rw [Function.update_of_ne hne]
              exact ⟨fun h' => (hx j hj).1 (by omega), fun h' => (hx j hj).2 (by omega)⟩
          | zero =>
            rw [symG_zero p O hk F l ga x k hk']
            exact Q.zero_mem
          | add a b _ _ ha hb =>
            rw [symG_add p O hk F l ga x k hk']
            exact Q.add_mem ha hb
          | smul c a _ ha =>
            rw [symG_smul p O hk F l ga x k hk']
            exact Q.smul_mem _ ha
        have h1 := hspan (x k) ((hx k hkJ).1 (Nat.lt_succ_self k))
        rwa [Function.update_eq_self] at h1
      · apply ih
        intro j hj
        exact ⟨fun h' => (hx j hj).1 (by omega), fun h' => absurd h' (by omega)⟩
  intro x hx
  exact key F.J x (fun j hj => ⟨fun _ => hx j hj, fun h' => absurd h' (by omega)⟩)

end Multi

def g2mg (p n' : ℕ) [NeZero n'] (r K : ℕ) (F : Frames n' r) (deg : Fin n' → ℕ) (mS : ℕ) (Y : ℝ) (j x : ℤ) : ℤ :=
  (mS : ℤ) + (⌊(deg (posOf n' (F.oldest j x)) : ℝ) / (p : ℝ) ^ F.dist j (F.oldest j x) /
    (((r + K : ℕ) : ℝ) ^ 2 * Y)⌋₊ : ℤ)

def g2th (p n' : ℕ) [NeZero n'] {r : ℕ} (F : Frames n' r) (deg : Fin n' → ℕ) (j x : ℤ) : ℝ :=
  (deg (posOf n' (F.oldest j x)) : ℝ) / (p : ℝ) ^ F.dist j (F.oldest j x) / 2

theorem symbol_spaces_le_pair_span (CLa : ℝ) (p n' : ℕ) [NeZero n'] (O : Type) [CommRing O] (r K : ℕ) [NeZero r] [NeZero K]
    (F : Frames n' r) (deg : Fin n' → ℕ) (L₁ Ns mS : ℕ) (a Y : ℝ) (j : ℤ) {x : SegRing O r K}
    (hx : x ∈ symbolSpaces CLa p n' O r K F deg L₁ Ns mS a Y j) :
    x ∈ Submodule.span O (pairSet O r K F j (g2mg p n' r K F deg mS Y j) (g2th p n' F deg j)) :=
  (Submodule.mem_inf.1 hx).1

end Formalism.MainNotions.TestSideWords
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.WordLossNonneg
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting

section TotallyRealRoots

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r)

def touchT (jz : ℤ) (u : ℕ) (s : Fin n') : Prop :=
  ∃ x ∈ Fr.letters jz, posOf n' x = s ∧ x ≤ posU Fr (Fr.LLset jz).card jz u

def opCost (s : Fin n') (jz : ℤ) (u : ℕ) : ℝ := if touchT Fr jz u s then 2 else 0

def wordLoss {k : ℕ} (l : List (Fin n' × (Fin k × Fin k))) (jz : ℤ) (u : ℕ) : ℝ :=
  (l.map fun z => opCost Fr z.1 jz u).sum

end TotallyRealRoots

def RestLeOfG : Prop :=
  ∀ (sc sL : ℝ) (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
    (F : MvPolynomial (TV n' (m + 1)) (KK O)),
    MemAtG sc sL p O hk Fr deg Y N₁ G' cP F → MemAtLe sc sL (fun _ _ => 0) p O hk Fr deg Y N₁ G' cP F

def OneOpStep (C CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∀ (loss : ℤ → ℕ → ℝ) (Fp : MvPolynomial (TV n' (m + 1)) (KK O)),
      MemAtLe 0 (1 / 8) loss p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x)
        (cPrime n' r TT.card c0 cpp cStar) Fp →
      ∀ s ∈ TT, ∀ a b : Fin (m + 1),
        MemAtLe 0 (1 / 8) (fun jz u => loss jz u + opCost F s jz u) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x)
          (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) (X (s, a) * pderiv (s, b) Fp)

def WordBoundStep (C CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∀ l : List (Fin n' × (Fin (m + 1) × Fin (m + 1))), (∀ z ∈ l, z.1 ∈ TT) →
      (∀ s, (l.filter fun z => z.1 = s).length ≤ c0) →
      ∀ (jz : ℤ) (u : ℕ), u < (F.LLset jz).card + r →
        wordLoss F l jz u ≤ 1 / 8 * (sl p F (flatDeg lam0) Y (r + K) jz (posU F (F.LLset jz).card jz u) : ℝ)

theorem wordLoss_nonneg {n' r k : ℕ} [NeZero n'] (Fr : Frames n' r) (l : List (Fin n' × (Fin k × Fin k))) (jz : ℤ)
    (u : ℕ) : 0 ≤ wordLoss Fr l jz u := by
  unfold wordLoss
  apply List.sum_nonneg
  intro c hc
  obtain ⟨z, -, rfl⟩ := List.mem_map.1 hc
  unfold opCost
  split_ifs <;> norm_num

theorem restWordStep_of (C CLa : ℝ) (hLe : RestLeOfG) (h1 : OneOpStep C CLa) (hB : WordBoundStep C CLa) :
    WordConditionAt C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h' x lam0 aT bT a Y cpp c0 Dp cStar K _ _ hk hrk
    F nb B hD Fp hFp l hl hc

  have hind : ∀ l' : List (Fin n' × (Fin (m + 1) × Fin (m + 1))), (∀ z ∈ l', z.1 ∈ TT) →
      MemAtLe 0 (1 / 8) (fun jz u => wordLoss F l' jz u) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h' x)
        (goodG' r de h' x) (cPrime n' r TT.card c0 cpp cStar) (opWord l' Fp) := by
    intro l' hl'
    induction l' with
    | nil =>
      have h0 := hLe 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h' x) (goodG' r de h' x)
        (cPrime n' r TT.card c0 cpp cStar) Fp hFp
      have e0 : (fun jz u => wordLoss F ([] : List (Fin n' × (Fin (m + 1) × Fin (m + 1)))) jz u) = fun _ _ => 0 := by
        funext jz u; simp [wordLoss]
      rw [e0]
      simpa [opWord] using h0
    | cons y l' ih =>
      have ih' := ih fun z hz => hl' z (List.mem_cons_of_mem _ hz)
      have hy := h1 p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h' x lam0 aT bT a Y cpp c0 Dp cStar K hk hrk F nb B hD
        (fun jz u => wordLoss F l' jz u) (opWord l' Fp) ih' y.1 (hl' y List.mem_cons_self) y.2.1 y.2.2
      have e1 : (fun jz u => wordLoss F (y :: l') jz u) = fun jz u => wordLoss F l' jz u + opCost F y.1 jz u := by
        funext jz u
        simp only [wordLoss, List.map_cons, List.sum_cons]
        ring
      rw [e1]
      simpa [opWord] using hy
  have hW := hind l hl
  apply memAtG_of_le
  refine memAtLe_mono p O hk F (flatDeg lam0) Y (orbitWindowCount r de h' x) (goodG' r de h' x) (cPrime n' r TT.card c0 cpp cStar)
    0 (1 / 8) (1 / 8) (3 / 8) (fun jz u => wordLoss F l jz u) (fun _ _ => 0) ?_ ?_ _ hW
  · intro jz u hu
    have hb := hB p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h' x lam0 aT bT a Y cpp c0 Dp cStar K hk hrk F nb B hD l hl hc jz u
      (by have := NeZero.pos r; omega)
    linarith
  · intro jz u _ hu
    have hb := hB p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h' x lam0 aT bT a Y cpp c0 Dp cStar K hk hrk F nb B hD l hl hc jz u hu
    have h0 := wordLoss_nonneg F l jz u
    linarith

def RestOneOp (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → OneOpStep C CLa

def RestWordBound (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → WordBoundStep C CLa

theorem restWord_of (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hLe : RestLeOfG) (h1 : RestOneOp D CLa Ck Crk Cdeg)
    (hB : RestWordBound D CLa Ck Crk Cdeg) : RestWord D CLa Ck Crk Cdeg := by
  intro hA
  obtain ⟨C₁, p1, h1'⟩ := h1 hA
  obtain ⟨C₂, _, hB'⟩ := hB hA
  refine ⟨max C₁ C₂, lt_max_of_lt_left p1, fun C hC => ?_⟩
  exact restWordStep_of C CLa hLe (h1' C (le_trans (le_max_left _ _) hC)) (hB' C (le_trans (le_max_right _ _) hC))

end Formalism.MainNotions.TestSideWords
end
end

