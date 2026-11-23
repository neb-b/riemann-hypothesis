module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountUp
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0004
public import Formalism.SharpRestriction.GrowthBounds.JointsLit

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KLettersDegEven
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Function

theorem strip_cons {r : ℕ} {nu mu : Fin r → ℤ} {g e : ℕ} (h : Strip nu mu g) {f f' : ℤ} (h1 : f ≤ f')
    (h2 : ∀ c : Fin r, c.val = 0 → nu c ≤ f) (he : f' - f + g = e) :
    Strip (Fin.cons f' nu : Fin (r + 1) → ℤ) (Fin.cons f mu) e := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun c => ?_) i
    · simpa using h1
    · simpa using h.1 c
  · intro i j
    refine Fin.cases ?_ (fun j' => ?_) j
    · intro hij; simp at hij
    · refine Fin.cases ?_ (fun c => ?_) i
      · intro hij
        simp only [Fin.cons_succ, Fin.cons_zero]
        exact h2 j' (by simpa using hij.symm)
      · intro hij
        simp only [Fin.cons_succ]
        exact h.2.1 c j' (by simpa using hij)
  · rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have := h.2.2
    linarith

def fstOf {s : ℕ} (A : Fin s → ℕ) (cp : ℕ → ℤ) (LLv : ChainLetters (2 * s + 1)) (n : ℕ) : ℤ :=
  if n % 2 = 1 then cp ((n - 1) / 2) else
    if h : (n - 2) / 2 < s then cp ((n - 2) / 2) + A ⟨(n - 2) / 2, h⟩ - LLv.deg ⟨2 * ((n - 2) / 2), by omega⟩ else 0

theorem fstOf_odd {s : ℕ} (A : Fin s → ℕ) (cp : ℕ → ℤ) (LLv : ChainLetters (2 * s + 1)) (i : ℕ) :
    fstOf A cp LLv (2 * i + 1) = cp i := by
  unfold fstOf
  rw [if_pos (by omega)]
  congr 1
  omega

theorem fstOf_even {s : ℕ} (A : Fin s → ℕ) (cp : ℕ → ℤ) (LLv : ChainLetters (2 * s + 1)) (i : Fin s) :
    fstOf A cp LLv (2 * i.val + 2) = cp i + A i - LLv.deg ⟨2 * i.val, by omega⟩ := by
  have hi := i.isLt
  unfold fstOf
  rw [if_neg (by omega)]
  have hk : (2 * i.val + 2 - 2) / 2 = i.val := by omega
  rw [dite_eq_left (by omega)]
  simp only [hk]

def muOf {s r : ℕ} (fst : ℕ → ℤ) (ka : Fin (2 * s + 1 + 1) → Fin r → ℤ) : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ :=
  fun l => if l.val = 0 then 0 else Fin.cons (fst l.val) (ka ⟨l.val - 1, by omega⟩)

theorem muOf_succ {s r : ℕ} (fst : ℕ → ℤ) (ka : Fin (2 * s + 1 + 1) → Fin r → ℤ) (n : ℕ) (h : n + 1 < 2 * s + 1 + 1) :
    muOf fst ka ⟨n + 1, h⟩ = Fin.cons (fst (n + 1)) (ka ⟨n, by omega⟩) := by
  simp [muOf]

structure LevFacts {s r : ℕ} (A0 : ℤ) (A C : Fin s → ℕ) (cp : ℕ → ℤ) (LLv : ChainLetters (2 * s + 1))
    (ka : Fin (2 * s + 1 + 1) → Fin r → ℤ) : Prop where
  c0 : cp 0 = A0
  A0nn : 0 ≤ A0
  vecv : ∀ a, LLv.vec a = decide (a.val % 2 = 0)
  hw : ∀ i : Fin s, (LLv.deg ⟨2 * i.val, by omega⟩ : ℤ) ≤ A i
  hc : ∀ i : Fin s, cp (i.val + 1) ≤ cp i.val + A i - LLv.deg ⟨2 * i.val, by omega⟩
  he : ∀ i : Fin s, cp i.val + A i - LLv.deg ⟨2 * i.val, by omega⟩ - cp (i.val + 1) +
    LLv.deg ⟨2 * i.val + 1, by omega⟩ = C i
  hb : ∀ (i : Fin s) (c : Fin r), c.val = 0 → ka ⟨2 * i.val + 1, by omega⟩ c ≤ cp i.val
  hd : ∀ (i : Fin s) (c : Fin r), c.val = 0 → ka ⟨2 * i.val + 1, by omega⟩ c ≤ cp (i.val + 1)
  hf : ∀ c : Fin r, c.val = 0 → ka (Fin.last _) c ≤ cp s

theorem kLetters_deg_odd {s : ℕ} (A0 : ℕ) (A C : Fin s → ℕ) (i : Fin s) :
    (kLetters A0 A C).deg ⟨2 * i.val + 1, by omega⟩ = A i := by
  have hi := i.isLt
  have h0 : ¬ (2 * i.val + 1 = 0) := by omega
  have h1 : (2 * i.val + 1 - 1) / 2 < s := by omega
  have h2 : (2 * i.val + 1) % 2 = 1 := by omega
  simp only [kLetters, Fin.val_mk]
  rw [if_neg h0, dite_eq_left h1, if_pos h2]
  congr 1
  ext
  simp only
  omega

theorem kLetters_deg_even {s : ℕ} (A0 : ℕ) (A C : Fin s → ℕ) (i : Fin s) :
    (kLetters A0 A C).deg ⟨2 * i.val + 2, by omega⟩ = C i := by
  have hi := i.isLt
  have h0 : ¬ (2 * i.val + 2 = 0) := by omega
  have h1 : (2 * i.val + 2 - 1) / 2 < s := by omega
  have h2 : ¬ ((2 * i.val + 2) % 2 = 1) := by omega
  simp only [kLetters, Fin.val_mk]
  rw [if_neg h0, dite_eq_left h1, if_neg h2]
  congr 1
  ext
  simp only
  omega

theorem chain_of_facts {s r : ℕ} {A0 : ℤ} {A C : Fin s → ℕ} {cp : ℕ → ℤ} {LLv : ChainLetters (2 * s + 1)}
    {ka : Fin (2 * s + 1 + 1) → Fin r → ℤ} (hF : LevFacts A0 A C cp LLv ka) (hch : IsChain LLv ka) :
    IsChain (kLetters A0.toNat A C) (muOf (fstOf A cp LLv) ka) ∧
      Inter (muOf (fstOf A cp LLv) ka (Fin.last _)) (ka (Fin.last _)) := by
  constructor
  · refine ⟨by unfold muOf; simp, ?_⟩
    rintro ⟨a, ha⟩
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    ·
      have hv : (kLetters A0.toNat A C).vec ⟨0, ha⟩ = true := by simp [kLetters]
      rw [if_pos hv]
      have e0 : muOf (fstOf A cp LLv) ka (Fin.castSucc ⟨0, ha⟩) = 0 := by unfold muOf; simp
      have e1 : muOf (fstOf A cp LLv) ka (Fin.succ ⟨0, ha⟩) = Fin.cons A0 0 := by
        unfold muOf
        simp only [Fin.succ_mk, Nat.zero_add]
        rw [if_neg (by omega)]
        have := fstOf_odd A cp LLv 0
        simp only [Nat.mul_zero, Nat.zero_add] at this
        rw [this, hF.c0]
        congr 1
        exact hch.1
      have hdeg : (kLetters A0.toNat A C).deg ⟨0, ha⟩ = A0.toNat := by simp [kLetters]
      rw [e0, e1, hdeg]
      refine ⟨?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun c => ?_) i
        · simpa using hF.A0nn
        · simp
      · intro i j
        refine Fin.cases ?_ (fun j' => ?_) j
        · intro hij; simp at hij
        · intro _; simp
      · rw [Fin.sum_univ_succ]
        simp [Int.toNat_of_nonneg hF.A0nn]
    · rcases Nat.even_or_odd' a with ⟨i, rfl | rfl⟩
      ·
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        have hi : i' < s := by omega
        have hv : (kLetters A0.toNat A C).vec ⟨2 * (i' + 1), ha⟩ = false := by
          simp [kLetters]
        rw [if_neg (by rw [hv]; simp)]
        have hst := hch.2 ⟨2 * i' + 1, by omega⟩
        rw [if_neg (by rw [hF.vecv]; simp)] at hst
        have e0 : muOf (fstOf A cp LLv) ka (Fin.castSucc ⟨2 * (i' + 1), ha⟩) =
            Fin.cons (cp i' + A ⟨i', hi⟩ - LLv.deg ⟨2 * i', by omega⟩) (ka (Fin.castSucc ⟨2 * i' + 1, by omega⟩)) := by
          have h := muOf_succ (fstOf A cp LLv) ka (2 * i' + 1) (by omega)
          rw [show fstOf A cp LLv (2 * i' + 1 + 1) = _ from fstOf_even A cp LLv ⟨i', hi⟩] at h
          exact h
        have e1 : muOf (fstOf A cp LLv) ka (Fin.succ ⟨2 * (i' + 1), ha⟩) =
            Fin.cons (cp (i' + 1)) (ka (Fin.succ ⟨2 * i' + 1, by omega⟩)) := by
          have h := muOf_succ (fstOf A cp LLv) ka (2 * (i' + 1)) (by omega)
          rw [fstOf_odd A cp LLv (i' + 1)] at h
          exact h
        have hdeg : (kLetters A0.toNat A C).deg ⟨2 * (i' + 1), ha⟩ = C ⟨i', hi⟩ :=
          kLetters_deg_even A0.toNat A C ⟨i', hi⟩
        rw [e0, e1, hdeg]
        exact strip_cons hst (hF.hc ⟨i', hi⟩) (fun c hc => hF.hd ⟨i', hi⟩ c hc) (hF.he ⟨i', hi⟩)
      ·
        have hi : i < s := by omega
        have hv : (kLetters A0.toNat A C).vec ⟨2 * i + 1, ha⟩ = true := by
          simp [kLetters]
        rw [if_pos hv]
        have hst := hch.2 ⟨2 * i, by omega⟩
        rw [if_pos (by rw [hF.vecv]; simp)] at hst
        have e0 : muOf (fstOf A cp LLv) ka (Fin.castSucc ⟨2 * i + 1, ha⟩) =
            Fin.cons (cp i) (ka (Fin.castSucc ⟨2 * i, by omega⟩)) := by
          have h := muOf_succ (fstOf A cp LLv) ka (2 * i) (by omega)
          rw [fstOf_odd A cp LLv i] at h
          exact h
        have e1 : muOf (fstOf A cp LLv) ka (Fin.succ ⟨2 * i + 1, ha⟩) =
            Fin.cons (cp i + A ⟨i, hi⟩ - LLv.deg ⟨2 * i, by omega⟩) (ka (Fin.succ ⟨2 * i, by omega⟩)) := by
          have h := muOf_succ (fstOf A cp LLv) ka (2 * i + 1) (by omega)
          rw [show fstOf A cp LLv (2 * i + 1 + 1) = _ from fstOf_even A cp LLv ⟨i, hi⟩] at h
          exact h
        have hdeg : (kLetters A0.toNat A C).deg ⟨2 * i + 1, ha⟩ = A ⟨i, hi⟩ :=
          kLetters_deg_odd A0.toNat A C ⟨i, hi⟩
        rw [e0, e1, hdeg]
        refine strip_cons hst (by have := hF.hw ⟨i, hi⟩; linarith) (fun c hc => hF.hb ⟨i, hi⟩ c hc) (by ring)
  ·
    have hst := hch.2 (Fin.last (2 * s))
    rw [if_pos (by rw [hF.vecv]; simp)] at hst
    have e1 : muOf (fstOf A cp LLv) ka (Fin.last (2 * s + 1)) =
        Fin.cons (cp s) (ka (Fin.castSucc (Fin.last (2 * s)))) := by
      have h := muOf_succ (fstOf A cp LLv) ka (2 * s) (by omega)
      rw [fstOf_odd A cp LLv s] at h
      exact h
    rw [Fin.succ_last] at hst
    rw [e1]
    intro i
    constructor
    · simp only [Fin.cons_succ]
      exact hst.1 i
    · rcases Nat.eq_zero_or_pos i.val with h0 | hp
      · have : i.castSucc = 0 := Fin.ext (by simp [h0])
        rw [this, Fin.cons_zero]
        exact hF.hf i h0
      · have : i.castSucc = Fin.succ ⟨i.val - 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [this, Fin.cons_succ]
        exact hst.2.1 ⟨i.val - 1, by omega⟩ i (by simp; omega)

def LevFactsAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ z, SrcOK C0 CE1 CE2 X j m rz ry z →
        LevFacts ((X.seg C0 CE1 CE2 j).A0 X.p)
          (fun i => coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i)
          (fun i => coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) i)
          (fun l => cap X.p (X.seg C0 CE1 CE2 j) z.1 l)
          ((BD C0 CE1 CE2 X j m z.1).lettersAt z.2.1.1 z.2.1.2) z.2.2

def SrcInjAt : Prop :=
  ∀ (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (m : ℝ)
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) (z z' : FinalTheorems (segS X.TT j) X.m (X.seg C0 CE1 CE2 j).t),
    SrcOK C0 CE1 CE2 X j m rz ry z → SrcOK C0 CE1 CE2 X j m rz ry z' → z.2.2 = z'.2.2 → z.2.1.2 = z'.2.1.2 → z = z'

theorem muOf_inj {s r : ℕ} {fst fst' : ℕ → ℤ} {ka ka' : Fin (2 * s + 1 + 1) → Fin r → ℤ}
    (h : muOf fst ka = muOf fst' ka') (hl : ka (Fin.last _) = ka' (Fin.last _)) : ka = ka' := by
  funext l
  by_cases hlt : l.val + 1 < 2 * s + 1 + 1
  · have e := congrFun h ⟨l.val + 1, hlt⟩
    rw [muOf_succ, muOf_succ] at e
    funext c
    have e2 := congrFun e c.succ
    simpa only [Fin.cons_succ] using e2
  · have hl' : l = Fin.last _ := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [hl']
    exact hl

theorem matchUp_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hF : LevFactsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hI : SrcInjAt) : MatchUpAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hH hc j m hm rz ry hd
  refine ⟨fun z => (muOf (fstOf (fun i => coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i)
      (fun l => cap X.p (X.seg C0 CE1 CE2 j) z.1 l) ((BD C0 CE1 CE2 X j m z.1).lettersAt z.2.1.1 z.2.1.2)) z.2.2,
      z.2.2 (Fin.last _), z.2.1.2), ?_, ?_⟩
  · intro z hz z' hz' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun t => t.2.1) h
    have h3 := congrArg (fun t => t.2.2) h
    exact hI C0 CE1 CE2 X j m rz ry z z' hz hz' (muOf_inj h1 h2) h3
  · intro z hz
    have h := chain_of_facts (hF X hD hH hc j m hm rz ry hd z hz) hz.2.2.1
    exact ⟨h.1, h.2, rfl, rfl⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.StWeyl
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem wdim_shift {r : ℕ} (lam : Fin r → ℤ) (c : ℤ) : wdim (fun i => lam i + c) = wdim lam := by
  unfold wdim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  split_ifs
  · congr 1
    push_cast
    ring
  · rfl

theorem wdim_nat {r : ℕ} (nu : Fin r → ℕ) :
    wdim (fun i => (nu i : ℤ)) = ∏ i : Fin r, ∏ j : Fin r,
      if i < j then ((nu i : ℚ) - (nu j : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) else 1 := by
  unfold wdim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp only [Int.cast_natCast]

theorem antitone_of_interlace {r : ℕ} {lamN : Fin (r + 1) → ℕ} (hl : Antitone lamN) (nu : Fin r → ℕ)
    (h : ∀ i : Fin r, lamN i.succ ≤ nu i ∧ nu i ≤ lamN i.castSucc) : Antitone nu := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · have h1 : i.succ ≤ j.castSucc := by
      rw [Fin.le_def]
      have : (i : ℕ) < (j : ℕ) := hlt
      simpa using this
    exact ((h j).2.trans (hl h1)).trans (h i).1

theorem numBranch_of {D : Formalism.BasicNotions.D7} (h2 : adm2 D) (h3 : adm3 D) : NumBranchAt := by
  intro r mu hmu
  classical
  set c : ℤ := mu (Fin.last r) with hc
  let lamN : Fin (r + 1) → ℕ := fun i => (mu i - c).toNat
  have hge : ∀ i, c ≤ mu i := fun i => hmu (Fin.le_last i)
  have hcast : ∀ i, (lamN i : ℤ) = mu i - c := fun i => Int.toNat_of_nonneg (by linarith [hge i])
  have hanti : Antitone lamN := by
    intro i j hij
    have h1 := hmu hij
    have : (lamN j : ℤ) ≤ (lamN i : ℤ) := by rw [hcast, hcast]; linarith
    exact_mod_cast this
  have e1 : wdim mu = (Module.finrank ℚ (Formalism.GradedWeylDivisibility.dualWeyl ℚ (r + 1) (r + 1) lamN) : ℚ) := by
    have hmu' : mu = fun i => (lamN i : ℤ) + c := funext fun i => by rw [hcast]; ring
    calc wdim mu = wdim (fun i => (lamN i : ℤ) + c) := congrArg wdim hmu'
      _ = wdim (fun i => (lamN i : ℤ)) := wdim_shift _ c
      _ = _ := by rw [wdim_nat, h3 ℚ (r + 1) lamN hanti]
  rw [e1, h2 ℚ r lamN hanti]
  push_cast
  set F := (Fintype.piFinset (fun _ : Fin r => Finset.range (lamN 0 + 1))).filter
    (fun nu => ∀ i : Fin r, lamN i.succ ≤ nu i ∧ nu i ≤ lamN i.castSucc) with hF
  have hinj : Set.InjOn (fun (nu : Fin r → ℕ) (i : Fin r) => (nu i : ℤ) + c) F := by
    intro a _ b _ hab
    funext i
    have := congrFun hab i
    simp only at this
    omega
  rw [finsum_eq_sum_of_support_subset (s := F.image (fun (nu : Fin r → ℕ) (i : Fin r) => (nu i : ℤ) + c))]
  · rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [hF, Finset.mem_filter] at hnu
    have hnu2 := hnu.2
    have hA : Antitone nu := antitone_of_interlace hanti nu hnu2
    rw [if_pos, wdim_shift, wdim_nat, h3 ℚ r nu hA]
    intro i
    show mu i.succ ≤ (nu i : ℤ) + c ∧ (nu i : ℤ) + c ≤ mu i.castSucc
    have h1 := hnu2 i
    have a1 := hcast i.succ
    have a2 := hcast i.castSucc
    constructor <;> omega
  · intro lam hlam
    rw [Function.mem_support] at hlam
    have hcond : ∀ i : Fin r, mu i.succ ≤ lam i ∧ lam i ≤ mu i.castSucc := by
      by_contra hn
      exact hlam (if_neg hn)
    rw [Finset.coe_image]
    refine ⟨fun i => (lam i - c).toNat, ?_, ?_⟩
    · rw [Finset.mem_coe, hF, Finset.mem_filter, Fintype.mem_piFinset]
      have hl : ∀ i, ((lam i - c).toNat : ℤ) = lam i - c := fun i =>
        Int.toNat_of_nonneg (by linarith [hge i.succ, (hcond i).1])
      refine ⟨fun i => ?_, fun i => ?_⟩
      · rw [Finset.mem_range]
        show (lam i - c).toNat < lamN 0 + 1
        have a0 := hcast 0
        have h0 : mu i.castSucc ≤ mu 0 := hmu (Fin.zero_le _)
        have := hl i
        have := (hcond i).2
        omega
      · show lamN i.succ ≤ (lam i - c).toNat ∧ (lam i - c).toNat ≤ lamN i.castSucc
        have a1 := hcast i.succ
        have a2 := hcast i.castSucc
        have b1 := hl i
        have b2 := hcond i
        constructor <;> omega
    · funext i
      have : ((lam i - c).toNat : ℤ) = lam i - c :=
        Int.toNat_of_nonneg (by linarith [hge i.succ, (hcond i).1])
      simp only [this]
      ring

theorem stWeylAt (D : Formalism.BasicNotions.D7) : StWeylAt := by
  intro n N LL B P
  have h := Formalism.MainNotions.G.Joints.Lit.weyl_dimension_formula_index_sets D n N P.mu (P.dom (Fin.last N))
  rw [h]
  rfl

end Formalism.MainNotions.ColumnSystems.Pf
end
end

