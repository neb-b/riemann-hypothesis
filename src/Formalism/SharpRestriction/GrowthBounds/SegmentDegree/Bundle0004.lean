module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0003

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.AtypicalPathSmallWeight
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

def beA (n0 : ℕ) (B : Fin N → ℕ) : ℕ := ∑ i : Fin N, if i.val < n0 then B i else 0

structure IsPATHa (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ)
    (dd : Fin N → ℕ) : Prop where
  path : ∃ P : PPath (r + K) N LL dd, P.mu = μ
  degs : ∀ i : Fin N, i.val < n0 → dd i = B i
  head : ∀ (i : Fin N) (m : Fin (r + K)), n0 ≤ i.val → m.val ≤ i.val - n0 → μ i.succ m = (beA n0 B : ℤ)

def posS {n : ℕ} (la : Fin n → ℤ) : ℤ := ∑ m, max (la m) 0

def negS {n : ℕ} (la : Fin n → ℤ) : ℤ := ∑ m, max (-la m) 0

def Xi (r K : ℕ) (bb : Fin N → ℝ) (La : ℝ) (p : ℕ) (i : Fin N) : ℝ := La * bb i / ((p : ℝ) * ((r + K : ℕ) : ℝ))

def Typ [NeZero r] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ) (La : ℝ) (p : ℕ)
    (μ : Fin (N + 1) → Fin (r + K) → ℤ) : Prop :=
  ∀ i : Fin N,
    (LL.vec i = false → ((posS (μ i.castSucc) - posS (μ i.succ) : ℤ) : ℝ) ≤ Xi r K bb La p i) ∧
    (LL.vec i = true → r ≤ i.val → ((negS (μ i.castSucc) - negS (μ i.succ) : ℤ) : ℝ) ≤ Xi r K bb La p i) ∧
    (r ≤ i.val → (2 / 3 : ℝ) * (B (od i) : ℝ) ≤ ((plPart μ i.castSucc (lastIdx r) : ℤ) : ℝ))

def GoodA [NeZero r] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ) (La : ℝ) (p : ℕ)
    (μ : Fin (N + 1) → Fin (r + K) → ℤ) : Prop :=
  ∀ i : Fin N, r ≤ i.val →
    (2 / 3 : ℝ) * (B (od i) : ℝ) ≤ ((plPart μ i.castSucc (lastIdx r) : ℤ) : ℝ) ∧
    (LL.vec i = true → ((∑ c, (tanPart μ i.succ c - tanPart μ i.castSucc c) : ℤ) : ℝ) ≤
      Xi r K bb La p i + 2 * (B (od i) : ℝ)) ∧
    (LL.vec i = false → ((∑ c, (plPart μ i.castSucc c - plPart μ i.succ c) : ℤ) : ℝ) ≤ Xi r K bb La p i)

def rkA (r K n0 : ℕ) (B : Fin N → ℕ) : ℕ :=
  ∏ i : Fin N, if i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1

structure HypT (N n0 r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ) : Prop where
  hN : N = n0 + r
  r1 : 1 ≤ r
  a3 : 3 ≤ a
  p13 : 13 ≤ p
  H1 : ∀ i : Fin N, i.val < n0 → ((r + K : ℕ) : ℝ) ≤ (B i : ℝ) ∧ (B i : ℝ) ≤ 2 * a
  H2 : ∀ i i' : Fin N, i < i' → i'.val < n0 → LL.vec i = LL.vec i' → (p : ℝ) ^ 2 / 5 * (B i : ℝ) ≤ (B i' : ℝ)
  vec_true_of_early : ∀ i : Fin N, i.val < r → LL.vec i = true
  vec_true_of_late : ∀ i : Fin N, n0 ≤ i.val + r → LL.vec i = true
  two_r_le_n0 : 2 * r ≤ n0
  N_add_r_le_K : N + r ≤ K
  H4 : ((r + K : ℕ) : ℝ) / 2 ≤ (K : ℝ) - 2 * (N : ℝ)
  N_le_a : (N : ℝ) ≤ a
  od_lt : ∀ i : Fin N, r ≤ i.val → od i < i
  od_vec : ∀ i : Fin N, r ≤ i.val → LL.vec (od i) = true
  od_card : ∀ i : Fin N, r ≤ i.val →
    (Finset.univ.filter fun l : Fin N => od i ≤ l ∧ l < i ∧ LL.vec l = true).card = r
  bb_pos : ∀ i : Fin N, r ≤ i.val → 0 < bb i
  bb_le : ∀ i l : Fin N, r ≤ i.val → l < i → l.val < n0 → (B l : ℝ) ≤ 4 * bb i / (p : ℝ)
  La_pos : 0 < La

def ell0 (N : ℕ) (a : ℝ) : ℝ := Real.log (1 + 2 * a * (N : ℝ))

abbrev QT (N r K : ℕ) := (Fin (N + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K))

def SP (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) : Set (Fin (N + 1) → Fin (r + K) → ℤ) :=
  {μ | ∃ dd, IsPATHa LL n0 B μ dd}

def SAll (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) : Set (QT N r K) :=
  {q | q.1 ∈ SP LL n0 B ∧ IsSt (tanPart q.1) q.2}

def SGood [NeZero r] (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ) (La : ℝ)
    (p : ℕ) : Set (QT N r K) :=
  {q | q.1 ∈ SP LL n0 B ∧ GoodA LL B od bb La p q.1 ∧ IsSt (tanPart q.1) q.2}

def PathWeightEqRank : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    (SAll (r := r) (K := K) LL n0 B).Finite ∧ (SAll (r := r) (K := K) LL n0 B).ncard = rkA r K n0 B

def PathCountFinite : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    (SP (r := r) (K := K) LL n0 B).Finite ∧
      ((SP (r := r) (K := K) LL n0 B).ncard : ℝ) ≤ Real.exp (2 * (N : ℝ) ^ 2 * ell0 N a)

def AtypicalPathSmallWeight : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    ∀ μ ∈ SP (r := r) (K := K) LL n0 B, ¬ Typ LL B od bb La p μ →
      (({I | IsSt (tanPart μ) I} : Set (ℤ → Finset (Fin K))).ncard : ℝ) ≤
        Real.exp (9 * (N : ℝ) ^ 2 * ell0 N a -
          min (La * ((K : ℝ) - 2 * N) / (16 * ((r + K : ℕ) : ℝ))) (((K : ℝ) - 2 * N) / 12)) * (rkA r K n0 B : ℝ)

def TypicalPathOrdersSmall : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    ∀ μ ∈ SP (r := r) (K := K) LL n0 B, Typ LL B od bb La p μ → GoodA LL B od bb La p μ

def LemT : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    (SGood (r := r) (K := K) LL n0 B od bb La p).Finite ∧
      (1 - Real.exp (11 * (N : ℝ) ^ 2 * ell0 N a - min La ((r + K : ℕ) : ℝ) / 32)) * (rkA r K n0 B : ℝ) ≤
        ((SGood (r := r) (K := K) LL n0 B od bb La p).ncard : ℝ)

theorem lemT_of (ha : PathWeightEqRank) (hb : PathCountFinite) (hc : AtypicalPathSmallWeight) (hd : TypicalPathOrdersSmall) : LemT := by
  classical
  intro N n0 r K _ _ LL B od bb a La p H
  obtain ⟨hfin, hcard⟩ := ha N n0 r K LL B od bb a La p H
  obtain ⟨hPfin, hPcard⟩ := hb N n0 r K LL B od bb a La p H
  have hc' := hc N n0 r K LL B od bb a La p H
  have hd' := hd N n0 r K LL B od bb a La p H
  set SA := SAll (r := r) (K := K) LL n0 B with hSA
  set SG := SGood (r := r) (K := K) LL n0 B od bb La p with hSG
  have hGA : SG ⊆ SA := fun q hq => ⟨hq.1, hq.2.2⟩
  have hGfin : SG.Finite := hfin.subset hGA
  refine ⟨hGfin, ?_⟩
  let SB : Set (QT N r K) := {q | q ∈ SA ∧ ¬ Typ LL B od bb La p q.1}
  have hBfin : SB.Finite := hfin.subset fun q hq => hq.1
  have hcov : SA ⊆ SG ∪ SB := by
    intro q hq
    by_cases ht : Typ LL B od bb La p q.1
    · exact Or.inl ⟨hq.1, hd' q.1 hq.1 ht, hq.2⟩
    · exact Or.inr ⟨hq, ht⟩
  have h1 : SA.ncard ≤ SG.ncard + SB.ncard :=
    le_trans (Set.ncard_le_ncard hcov (hGfin.union hBfin)) (Set.ncard_union_le _ _)
  set cR : ℝ := Real.exp (9 * (N : ℝ) ^ 2 * ell0 N a -
          min (La * ((K : ℝ) - 2 * N) / (16 * ((r + K : ℕ) : ℝ))) (((K : ℝ) - 2 * N) / 12)) * (rkA r K n0 B : ℝ) with hcR
  have hcR0 : 0 ≤ cR := by positivity

  have h2 : (SB.ncard : ℝ) ≤ ((SP (r := r) (K := K) LL n0 B).ncard : ℝ) * cR := by
    rw [Set.ncard_eq_toFinset_card _ hBfin, Set.ncard_eq_toFinset_card _ hPfin]
    have hmaps : ∀ q ∈ hBfin.toFinset, q.1 ∈ hPfin.toFinset := by
      intro q hq
      rw [Set.Finite.mem_toFinset] at hq ⊢
      exact hq.1.1
    have hfib : ∀ μ ∈ hPfin.toFinset, ((hBfin.toFinset.filter fun q => q.1 = μ).card : ℝ) ≤ cR := by
      intro μ hμ
      rw [Set.Finite.mem_toFinset] at hμ
      by_cases ht : Typ LL B od bb La p μ
      · have : hBfin.toFinset.filter (fun q => q.1 = μ) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro q hq hqμ
          rw [Set.Finite.mem_toFinset] at hq
          exact hq.2 (hqμ ▸ ht)
        rw [this]; simpa using hcR0
      · refine le_trans ?_ (hc' μ hμ ht)
        have hIfin : ({I | IsSt (tanPart μ) I} : Set (ℤ → Finset (Fin K))).Finite := by
          refine (hfin.image Prod.snd).subset ?_
          intro I hI
          exact ⟨(μ, I), ⟨hμ, hI⟩, rfl⟩
        rw [Set.ncard_eq_toFinset_card _ hIfin]
        have : (hBfin.toFinset.filter fun q => q.1 = μ).card ≤ hIfin.toFinset.card := by
          refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
          · intro q hq
            simp only [Finset.coe_filter, Set.mem_setOf_eq, Set.Finite.mem_toFinset] at hq
            simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
            have := hq.1.1.2
            rwa [hq.2] at this
          · intro q hq q' hq' hqq
            simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq hq'
            exact Prod.ext (hq.2.trans hq'.2.symm) hqq
        exact_mod_cast this
    have hsum : (hBfin.toFinset.card : ℝ) =
        ∑ μ ∈ hPfin.toFinset, ((hBfin.toFinset.filter fun q => q.1 = μ).card : ℝ) := by
      have := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := hBfin.toFinset) (t := hPfin.toFinset)
        (fun q hq => hmaps q hq)
      rw [this]; push_cast; rfl
    rw [hsum]
    calc ∑ μ ∈ hPfin.toFinset, ((hBfin.toFinset.filter fun q => q.1 = μ).card : ℝ)
        ≤ ∑ _μ ∈ hPfin.toFinset, cR := Finset.sum_le_sum hfib
      _ = (hPfin.toFinset.card : ℝ) * cR := by rw [Finset.sum_const, nsmul_eq_mul]

  have hk0 : (0 : ℝ) < ((r + K : ℕ) : ℝ) := by
    have : 0 < r + K := by have := H.r1; omega
    exact_mod_cast this
  have hmin : min La ((r + K : ℕ) : ℝ) / 32 ≤
      min (La * ((K : ℝ) - 2 * N) / (16 * ((r + K : ℕ) : ℝ))) (((K : ℝ) - 2 * N) / 12) := by
    have hH4 := H.H4
    refine le_min ?_ ?_
    · have h3 : La / 32 ≤ La * ((K : ℝ) - 2 * N) / (16 * ((r + K : ℕ) : ℝ)) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        have := mul_le_mul_of_nonneg_left hH4 H.La_pos.le
        nlinarith
      exact le_trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)) h3
    · have h3 : ((r + K : ℕ) : ℝ) / 32 ≤ ((K : ℝ) - 2 * N) / 12 := by linarith
      exact le_trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)) h3
  have hrk0 : (0 : ℝ) ≤ (rkA r K n0 B : ℝ) := Nat.cast_nonneg _
  have h3 : (SB.ncard : ℝ) ≤
      Real.exp (11 * (N : ℝ) ^ 2 * ell0 N a - min La ((r + K : ℕ) : ℝ) / 32) * (rkA r K n0 B : ℝ) := by
    refine le_trans h2 (le_trans (mul_le_mul_of_nonneg_right hPcard hcR0) ?_)
    rw [hcR, ← mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hrk0
    linarith
  have h1' : (rkA r K n0 B : ℝ) ≤ (SG.ncard : ℝ) + (SB.ncard : ℝ) := by
    rw [← hcard]; exact_mod_cast h1
  linarith

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ColumnWordReductionOfFour
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def ellP (R : Type) [CommRing R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : MvPolynomial (ℤ × Fin r) R :=
  ∏ x ∈ X.toLate j, ∏ c : Fin r, MvPolynomial.X (x, c) ^ e (x, Fin.castAdd K c)

def ellN (R : Type) [CommRing R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : MvPolynomial (ℤ × Fin K) R :=
  ∏ x ∈ X.toLate j, ∏ c : Fin K, MvPolynomial.X (x, c) ^ e (x, Fin.natAdd r c)

def dS (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : ℕ :=
  ∑ x ∈ X.toLate j, if Even x then 0 else ∑ c : Fin r, e (x, Fin.castAdd K c)

def dV (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : ℕ :=
  ∑ x ∈ X.toLate j, if Even x then ∑ c : Fin K, e (x, Fin.natAdd r c) else 0

def Aw (R : Type) [CommRing R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) (nu : Fin (segN X.F j + 1) → Fin r → ℤ)
    (I' : ℤ → Finset (Fin r)) : MvPolynomial (ℤ × Fin r) R :=
  (segRen X.F j R r (Psi R nu I')) ^ (p ^ X.Rj p K j) * X.ellP K R j e * X.DlSeg p K R j

def Gw (R : Type) [CommRing R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) (ka : Fin (segN X.F j + 1) → Fin K → ℤ)
    (I'' : ℤ → Finset (Fin K)) : MvPolynomial (ℤ × Fin K) R :=
  (segRen X.F j R K (Psi R ka I'')) ^ (p ^ X.Rj p K j) * X.ellN K R j e

def Mw [NeZero K] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) (ka : Fin (segN X.F j + 1) → Fin K → ℤ) : ℤ → ℤ :=
  Function.extend (segE X.F j)
    (fun i => ((p ^ X.Rj p K j : ℕ) : ℤ) * (if Even (segE X.F j i) then ka i.succ 0 else ka i.castSucc 0) +
      (X.dV K j e : ℤ)) 0

end Dat

structure WCtx (C₀ : ℝ) (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r)
    (j : ℤ) (b : ℤ → ℕ) (e : ℤ × Fin (r + K) →₀ ℕ)
    (q : (Fin (segN X.F j + 1) → Fin r → ℤ) × (Fin (segN X.F j + 1) → Fin K → ℤ))
    (I' : ℤ → Finset (Fin r)) (I'' : ℤ → Finset (Fin K)) : Prop where
  hX : X.Hyp p K
  hLa : C₀ ≤ X.CLa
  hk : C₀ ≤ X.Ck
  he : X.IsEll p K j e
  h2 : X.Step2 p K j b
  hq : q ∈ segPairs X.F j K (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j)
  hI' : IsSt q.1 I'
  hI'' : IsSt q.2 I''

def FrobeniusReductionProduct (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → ∀ j b e q I' I'', WCtx C₀ p n' r K X j b e q I' I'' →
    MvPolynomial.map (IsLocalRing.residue O)
        (X.zSeg p K O j (segRen X.F j O (r + K) (PsiPl O q.1 I' * PsiTan O q.2 I'')) e) =
      plEmb (FF O) r K (X.Aw p K (FF O) j e q.1 I') * nmEmb (FF O) r K (X.Gw p K (FF O) j e q.2 I'')

def ProductAllowedLetters (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → ∀ j b e q I' I'', WCtx C₀ p n' r K X j b e q I' I'' →
    X.Aw p K (FF O) j e q.1 I' ∈ supported (FF O) {v : ℤ × Fin r | v.1 ∈ X.F.letters j} ∧
    X.Gw p K (FF O) j e q.2 I'' ∈ supported (FF O) {v : ℤ × Fin K | v.1 ∈ X.F.letters j ∧ ¬ X.F.IsW j v.1}

def ColumnConditionsWithMargin (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → ∀ j b e q I' I'', WCtx C₀ p n' r K X j b e q I' I'' →
    ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x →
      (Even x → lam1S LZ {y | y ≤ x} (X.Gw p K (FF O) j e q.2 I'') ≤ ((X.Mw p K j e q.2 x : ℤ) : WithBot ℤ) ∧
          ((X.Mw p K j e q.2 x + X.mg p K j x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} (X.Aw p K (FF O) j e q.1 I')) ∧
      (¬ Even x → lam1S LZ {y | y < x} (X.Gw p K (FF O) j e q.2 I'') ≤ ((X.Mw p K j e q.2 x : ℤ) : WithBot ℤ) ∧
          ((X.Mw p K j e q.2 x + X.mg p K j x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} (X.Aw p K (FF O) j e q.1 I')) ∧
      geR (valS LZ {y | y < x} (X.Aw p K (FF O) j e q.1 I')) (X.th p j x)

def ProductOrdersBounded (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → ∀ j b e q I' I'', WCtx C₀ p n' r K X j b e q I' I'' →
    ∀ mm ∈ (plEmb (FF O) r K (X.Aw p K (FF O) j e q.1 I') * nmEmb (FF O) r K (X.Gw p K (FF O) j e q.2 I'')).support,
      ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x → (ordDeg mm x : ℝ) ≤ X.o p K j x

theorem column_word_reduction_of_four (D : Formalism.BasicNotions.D7) (hB12 : NestedTypeBound D) (C₀ : ℝ) (h1 : FrobeniusReductionProduct C₀) (h2 : ProductAllowedLetters C₀)
    (h3 : ColumnConditionsWithMargin C₀) (h4 : ProductOrdersBounded C₀) : ColumnWordReductionLifts C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b e he hs2 q hq I' I'' hI' hI''
  have : Fact p.Prime := ⟨hX.prime⟩
  have hc : WCtx C₀ p n' r K X j b e q I' I'' := ⟨hX, hLa, hk, he, hs2, hq, hI', hI''⟩
  have hseg : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have h6 := (hB12 p O S n' r K X.F X.L₁ X.N₁ j (X.mg p K j) (X.th p j) (X.o p K j) hX.valid hseg
    (fun x => by unfold Dat.mg; positivity)).2.2.2.2.2
  obtain ⟨P, hP, hPe⟩ := h6 (X.Aw p K (FF O) j e q.1 I') (X.Gw p K (FF O) j e q.2 I'') (X.Mw p K j e q.2)
    (h2 p n' r K X O S j b e q I' I'' hc).1 (h2 p n' r K X O S j b e q I' I'' hc).2
    (h3 p n' r K X O S j b e q I' I'' hc) (h4 p n' r K X O S j b e q I' I'' hc)
  exact ⟨P, hP, hPe.trans (h1 p n' r K X O S j b e q I' I'' hc).symm⟩

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FamilyDegreesAdmissible
section
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

def sumBin (r K n : ℕ) : ℝ := ((Nat.choose (n + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)

theorem sum_one_le_bin (r K n : ℕ) : 1 ≤ sumBin r K n := by
  unfold sumBin
  exact_mod_cast Nat.succ_le_of_lt (Nat.choose_pos (by omega))

theorem sum_one_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h1 : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  calc (1 : ℝ) = ∏ _i ∈ s, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) h1

theorem sum_single_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h1 : ∀ i ∈ s, 1 ≤ f i) {a : ι} (ha : a ∈ s) :
    f a ≤ ∏ i ∈ s, f i := by
  classical
  rw [← Finset.mul_prod_erase s f ha]
  have h2 : (1 : ℝ) ≤ ∏ i ∈ s.erase a, f i := sum_one_le_prod _ _ fun i hi => h1 i (Finset.mem_of_mem_erase hi)
  have h3 : 0 ≤ f a := le_trans zero_le_one (h1 a ha)
  nlinarith

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def sumTset (la : Fin n' → Fin (r + K) → ℕ) (j : ℤ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset fun i : Fin r =>
    (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = X.nz p K la j (X.F.fr j i.val) % X.Qc p K j

def sumhT (t : Fin n') (v : Fin (r + K) → ℕ) : ℝ :=
  ∏ j : Fin X.F.J, ∏ x ∈ X.F.LLset (j.val : ℤ),
    if posOf n' x = t then sumBin r K ((X.a' p K t - ∑ c, v c) / X.Pz p K (j.val : ℤ) x) else 1

def sumSt (t : Fin n') : ℝ := ∑ v ∈ X.laSet p K t, X.sumhT p K t v


omit [NeZero n'] in
def firstSumFactor : ℝ := 1 - 1 / X.a ^ (X.Ns ^ 2)

def sumWf (j : ℤ) : ℝ := ∏ i : Fin r, sumBin r K ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat)

def sumTf (j : ℤ) : ℝ := (((X.Qc p K j : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) ^ r

theorem sum_segBound_eq (j : ℤ) (b : ℤ → ℕ) :
    X.segBound p K j b = (X.firstSumFactor * X.sumWf p K j * X.sumTf p K j) * ∏ x ∈ X.F.LLset j, sumBin r K (b x) := by
  unfold segBound firstSumFactor sumWf sumTf sumBin
  ring

end Dat

structure SumFacts {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) : Prop where
  tiling : ∀ φ : Fin n' → ℝ,
    ∏ t ∈ X.F.TT, φ t = ∏ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), φ (posOf n' x)
  split : ∀ (j : ℤ) (ψ : ℤ → ℝ),
    ∏ x ∈ X.toLate j, ψ x = (∏ x ∈ X.F.LLset j, ψ x) * ∏ i : Fin r, ψ (X.F.fr j i.val)
  LLsub : ∀ j x, x ∈ X.F.LLset j → x ∈ X.toLate j ∧ x < X.F.fr j 0
  frlate : ∀ j (i : Fin r), X.F.fr j i.val ∈ X.toLate j
  uniqP : ∀ j j' x x', x ∈ X.toLate j → x' ∈ X.toLate j' → posOf n' x = posOf n' x' →
    X.Pz p K j x = X.Pz p K j' x'
  kP : ∀ j x, x ∈ X.toLate j → (r + K) * X.Pz p K j x ≤ X.a' p K (posOf n' x)
  compA : ∀ t ∈ X.F.TT, sumBin r K (X.deg t) * (1 - 5 / X.Y) ≤ sumBin r K (X.a' p K t)
  compW : ∀ j (i : Fin r), sumBin r K (X.a' p K (posOf n' (X.F.fr j i.val))) * (1 - 1 / X.Y) ≤
    (((X.Pz p K j (X.F.fr j i.val) * X.Qc p K j : ℕ) : ℝ)) ^ (r + K - 1) *
      sumBin r K ((X.Bw p K (j + 1) (X.F.fr j i.val) - (X.m0 K : ℤ)).toNat)
  prodQ : ∏ j ∈ Finset.range X.F.J, X.Qc p K (j : ℤ) = p ^ n'
  perW : ∀ j (i : Fin r),
    X.Bw p K (j + X.F.J) (X.F.fr (j + X.F.J - 1) i.val) = X.Bw p K j (X.F.fr (j - 1) i.val)
  JN : X.F.J ≤ X.F.TT.card
  a32 : 32 * X.Y ≤ X.a

section Steps

variable {n' r : ℕ} [NeZero n'] {X : Dat n' r} {p K : ℕ}

omit [NeZero n'] in
theorem sum_eZ_val (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) : X.eZ e (j.val : ℤ) = e j := by
  have hJ : 0 < X.F.J := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  unfold Dat.eZ
  rw [dite_eq_left hJ]
  congr 1
  apply Fin.ext
  have h1 : ((j.val : ℤ) % (X.F.J : ℤ)) = j.val := Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)
  simp only [h1, Int.toNat_natCast]
  exact Nat.mod_eq_of_lt j.isLt

theorem sum_late_mem {j x : ℤ} (hx : x ∈ X.toLate j) :
    x ∈ X.F.letters j ∧ ¬ X.F.IsW j x ∧ x ≤ X.F.fr j (r - 1) ∧ posOf n' x ∈ X.F.TT := by
  classical
  have hx' := Finset.mem_filter.mp hx
  have h2 := Finset.mem_filter.mp hx'.1
  exact ⟨hx'.1, hx'.2, (Finset.mem_Icc.mp h2.1).2, h2.2⟩

theorem sum_bfam_late (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) (x : ℤ)
    (hx : x ∈ X.toLate (j.val : ℤ)) :
    X.bfam p K la e (j.val : ℤ) x = X.setTau (j.val : ℤ) (X.nz p K la (j.val : ℤ)) (e j) x := by
  obtain ⟨h1, h2, h3, -⟩ := sum_late_mem hx
  unfold Dat.bfam Dat.setTau
  rw [if_pos h1, if_neg h2, sum_eZ_val]
  by_cases h : X.F.fr (j.val : ℤ) 0 ≤ x
  · rw [if_pos h, if_pos ⟨h, h3⟩]
  · rw [if_neg h, if_neg (fun hh => h hh.1)]

theorem family_degrees_admissible (hr : 0 < r) (hp : 0 < p) (hLL : ∀ j x, x ∈ X.F.LLset j → x ∈ X.toLate j)
    (la : Fin n' → Fin (r + K) → ℕ) (hla : la ∈ X.LA p K) (j : ℤ) :
    X.AdmLL p K j (X.nz p K la j) := by
  classical
  intro x hx
  have hv : la (posOf n' x) ∈ X.laSet p K (posOf n' x) := (Fintype.mem_piFinset.mp hla) _
  obtain ⟨-, hle, hall⟩ := Finset.mem_filter.mp hv
  obtain ⟨hlt, hmod⟩ := hall j x (hLL j x hx) rfl
  set P := X.Pz p K j x with hPdef
  set n := X.a' p K (posOf n' x) with hn
  set s := ∑ c, la (posOf n' x) c with hs
  have hP : 0 < P := by rw [hPdef]; unfold Dat.Pz; exact pow_pos hp _
  have hdvd : P ∣ n - s := (Nat.modEq_iff_dvd' hle).mp hmod
  have hnz : X.nz p K la j x = (n - s) / P := rfl
  have hPr : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hcast : ((X.nz p K la j x : ℕ) : ℝ) = ((n : ℝ) - s) / P := by
    rw [hnz, Nat.cast_div hdvd hPr.ne', Nat.cast_sub hle]
  have hslt : s < (r + K) * P := by
    calc s < ∑ _c : Fin (r + K), P := by
            rw [hs]
            exact Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ fun c _ => hlt c
      _ = (r + K) * P := by simp
  have hslt' : (s : ℝ) < Dat.k (r := r) K * P := by
    unfold Dat.k
    exact_mod_cast hslt
  rw [hcast]
  constructor
  · rw [sub_div, sub_lt_sub_iff_left, div_lt_iff₀ hPr]
    exact hslt'
  · exact div_le_div_of_nonneg_right (by have : (0 : ℝ) ≤ s := Nat.cast_nonneg _; linarith) hPr.le

theorem first_sum_factor_bounds (hY : 1 ≤ X.Y) (ha : 32 * X.Y ≤ X.a) (hNs : 1 ≤ X.Ns) :
    1 - 1 / (32 * X.Y) ≤ X.firstSumFactor ∧ 0 ≤ X.firstSumFactor := by
  have ha1 : 1 ≤ X.a := by linarith
  have h1 : X.a ≤ X.a ^ (X.Ns ^ 2) := by
    calc X.a = X.a ^ 1 := (pow_one _).symm
      _ ≤ X.a ^ (X.Ns ^ 2) := pow_le_pow_right₀ ha1 (Nat.one_le_pow _ _ hNs)
  have h2 : 1 / X.a ^ (X.Ns ^ 2) ≤ 1 / (32 * X.Y) :=
    one_div_le_one_div_of_le (by linarith) (ha.trans h1)
  have h3 : 1 / (32 * X.Y) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  unfold Dat.firstSumFactor
  constructor <;> linarith

end Steps

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

