module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.MemColRangeOfLeEntry
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0041
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0008

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.CardIcutFilter
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Abs3

variable {N r : ℕ}

theorem Icut_eq [NeZero r] {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ) :
    Icut n0 ν c = if 1 ≤ c ∧ c ≤ be then Finset.univ \ riseA n0 ν c r else ∅ := by
  classical
  unfold Icut
  rw [Ican_eq H]
  split_ifs
  · rfl
  · exact Finset.empty_sdiff _

theorem pEnd_cut {n0 : ℕ} (hn : n0 ≤ N) (ν : Fin (N + 1) → Fin r → ℤ) : pEnd (cutPath n0 ν) = stg ν n0 := by
  rw [pEnd_eq, stg_cut n0 ν N le_rfl, min_eq_right hn]

theorem riseA_filter (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : Fin r) :
    (riseA n0 ν c r).filter (· ≤ t) = riseA n0 ν c r \ riseA n0 ν c (r - 1 - t.val) := by
  classical
  ext m
  have hm := m.isLt
  have ht := t.isLt
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, fun h4 => ?_⟩
    have : m.val ≤ t.val := h3
    omega
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    by_contra h4
    have h5 : t.val < m.val := not_le.mp h4
    exact h3 (by omega) h2

theorem riseA_mono (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) {s t : ℕ} (h : s ≤ t) :
    riseA n0 ν c s ⊆ riseA n0 ν c t := by
  classical
  intro m
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨h1, h2⟩
  exact ⟨by omega, h2⟩

theorem card_Icut_filter [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ}
    (H : PlHyp n0 be ν) (c : ℤ) (hc : 1 ≤ c ∧ c ≤ be) (t : Fin r) :
    ((Finset.univ \ riseA n0 ν c r).filter (· ≤ t)).card + r =
      t.val + 1 + colH (stg ν (n0 + (r - 1 - t.val))) c := by
  classical
  have ht := t.isLt
  have h1 : ((Finset.univ \ riseA n0 ν c r).filter (· ≤ t)).card + ((riseA n0 ν c r).filter (· ≤ t)).card =
      t.val + 1 := by
    rw [← Finset.card_union_of_disjoint]
    · have : (Finset.univ \ riseA n0 ν c r).filter (· ≤ t) ∪ (riseA n0 ν c r).filter (· ≤ t) = Finset.Iic t := by
        ext m
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_Iic]
        tauto
      rw [this, Fin.card_Iic]
    · rw [Finset.disjoint_left]
      intro m hm hm'
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hm hm'
      exact hm.1 hm'.1
  have h2 : ((riseA n0 ν c r).filter (· ≤ t)).card + (riseA n0 ν c (r - 1 - t.val)).card = (riseA n0 ν c r).card := by
    rw [riseA_filter, Finset.card_sdiff_add_card_eq_card (riseA_mono n0 ν c (by omega))]
  have h3 := card_riseA H c r le_rfl
  have h4 := card_riseA H c (r - 1 - t.val) (by omega)
  have hNr : colH (stg ν N) c = r := colH_all fun m => by rw [H.fin]; exact hc.2
  rw [hN, hNr] at h3
  omega

theorem isSt_cut [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    IsSt (cutPath n0 ν) (Icut n0 ν) := by
  classical
  have hcard : ∀ c, (Icut n0 ν c).card =
      if 1 ≤ c then colH (pEnd (cutPath n0 ν)) c else r - colH (pEnd (cutPath n0 ν)) c := by
    intro c
    rw [pEnd_cut (by omega), Icut_eq H]
    by_cases h1 : 1 ≤ c
    · rw [if_pos h1]
      by_cases h2 : c ≤ be
      · rw [if_pos ⟨h1, h2⟩, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        have h3 := card_riseA H c r le_rfl
        have hNr : colH (stg ν N) c = r := colH_all fun m => by rw [H.fin]; exact h2
        rw [hN, hNr] at h3
        omega
      · rw [if_neg fun h => h2 h.2, Finset.card_empty,
          colH_none fun m => lt_of_le_of_lt (H.rng n0 (by omega) m).2 (by omega)]
    · rw [if_neg h1, if_neg fun h => h1 h.1, Finset.card_empty,
        colH_all fun m => le_trans (by omega) (H.rng n0 (by omega) m).1]
      omega
  refine ⟨?_, hcard, ?_⟩
  · intro c hc
    by_cases h : 1 ≤ c ∧ c ≤ be
    · rw [← Finset.card_eq_zero, hcard c, if_pos h.1, pEnd_cut (by omega)]
      apply colH_none
      intro m
      by_contra hge
      apply hc
      refine mem_colRange_of_le_entry (cutPath n0 ν) ⟨n0, by omega⟩ m (by omega) ?_
      have : cutPath n0 ν ⟨n0, by omega⟩ m = stg ν n0 m := by simp [cutPath]
      rw [this]; omega
    · rw [Icut_eq H, if_neg h]
  · intro c t
    unfold tabCol
    by_cases h1 : 1 ≤ c
    · rw [if_pos h1, if_pos (by omega : (1 : ℤ) ≤ c + 1), Icut_eq H, Icut_eq H]
      by_cases h2 : c + 1 ≤ be
      · rw [if_pos ⟨by omega, h2⟩, if_pos ⟨h1, by omega⟩]
        have e1 := card_Icut_filter hN H (c + 1) ⟨by omega, h2⟩ t
        have e2 := card_Icut_filter hN H c ⟨h1, by omega⟩ t
        have e3 := colH_anti (stg ν (n0 + (r - 1 - t.val))) (by omega : c ≤ c + 1)
        omega
      · rw [if_neg fun h => h2 h.2]
        simp
    · rw [if_neg h1]
      have hc0 : Icut n0 ν c = ∅ := by rw [Icut_eq H, if_neg fun h => h1 h.1]
      rw [hc0, Finset.sdiff_empty]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

theorem le_iff_lt_colH {μ : Fin r → ℤ} (hμ : Antitone μ) (c : ℤ) (m : Fin r) : c ≤ μ m ↔ m.val < colH μ c := by
  first | exact UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH .. | (apply UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ hμ c m | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ hμ c | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ hμ | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r

theorem eq_of_colH {μ μ' : Fin r → ℤ} (hμ : Antitone μ) (hμ' : Antitone μ') (h : ∀ c, colH μ c = colH μ' c) :
    μ = μ' := by
  funext m
  apply le_antisymm
  · rw [le_iff_lt_colH hμ', ← h, ← le_iff_lt_colH hμ]
  · rw [le_iff_lt_colH hμ, h, ← le_iff_lt_colH hμ']

theorem riseA_eq_filter (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) {t : ℕ} (ht : t ≤ r) :
    riseA n0 ν c t = (riseA n0 ν c r).filter fun m => r - 1 - m.val < t := by
  classical
  ext m
  have := m.isLt
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, h1⟩
  · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩

theorem path_eq_of_cut [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν ν' : Fin (N + 1) → Fin r → ℤ}
    (H : PlHyp n0 be ν) (H' : PlHyp n0 be ν') (hd : ∀ i, Antitone (ν i)) (hd' : ∀ i, Antitone (ν' i))
    (hcut : cutPath n0 ν = cutPath n0 ν') (hI : Icut n0 ν = Icut n0 ν') : ν = ν' := by
  classical
  have hlow : ∀ i ≤ n0, stg ν i = stg ν' i := by
    intro i hi
    have h1 := stg_cut n0 ν i (by omega)
    have h2 := stg_cut n0 ν' i (by omega)
    rw [min_eq_left hi] at h1 h2
    rw [← h1, ← h2, hcut]
  have hrise : ∀ c, 1 ≤ c ∧ c ≤ be → riseA n0 ν c r = riseA n0 ν' c r := by
    intro c hc
    have h1 := congrFun hI c
    rw [Icut_eq H, Icut_eq H', if_pos hc, if_pos hc] at h1
    have := congrArg (fun s => Finset.univ \ s) h1
    simpa [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] using this
  funext i
  rw [stg_eq ν i.val i.isLt, stg_eq ν' i.val i.isLt]
  by_cases hi : i.val ≤ n0
  · exact hlow i.val hi
  · obtain ⟨t, ht⟩ : ∃ t, i.val = n0 + t := ⟨i.val - n0, by omega⟩
    have hi' := i.isLt
    have htr : t ≤ r := by omega
    apply eq_of_colH
    · rw [← stg_eq ν i.val i.isLt]; exact hd i
    · rw [← stg_eq ν' i.val i.isLt]; exact hd' i
    intro c
    rw [ht]
    by_cases hc : 1 ≤ c ∧ c ≤ be
    · rw [← card_riseA H c t htr, ← card_riseA H' c t htr, hlow n0 le_rfl, riseA_eq_filter n0 ν c htr,
        riseA_eq_filter n0 ν' c htr, hrise c hc]
    · by_cases h1 : 1 ≤ c
      · have h2 : be < c := by
          by_contra h; exact hc ⟨h1, by omega⟩
        rw [colH_none fun m => lt_of_le_of_lt (H.rng _ (by omega) m).2 h2,
          colH_none fun m => lt_of_le_of_lt (H'.rng _ (by omega) m).2 h2]
      · rw [colH_all fun m => le_trans (by omega) (H.rng _ (by omega) m).1,
          colH_all fun m => le_trans (by omega) (H'.rng _ (by omega) m).1]

end Abs3

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DplusLeBeA
section
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem finite_St {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : ({I | IsSt mu I} : Set (ℤ → Finset (Fin n))).Finite := by
  classical
  refine Set.Finite.of_injOn (f := fun I (c : colRange mu) => I c.1) (t := Set.univ) (fun _ _ => Set.mem_univ _) ?_
    Set.finite_univ
  intro I hI I' hI' h
  funext c
  by_cases hc : c ∈ colRange mu
  · exact congrFun h ⟨c, hc⟩
  · rw [hI.1 c hc, hI'.1 c hc]

theorem wt_eq (D : Formalism.BasicNotions.D7) (h3 : admB3 D) {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (hd : Dominant (pEnd mu)) :
    ({I | IsSt mu I} : Set (ℤ → Finset (Fin n))).ncard = stCount n (pEnd mu) := by
  have h1 := h3 n N mu hd
  have h2 := h3 n 0 (fun _ => pEnd mu) hd
  have h4 : ((Nat.card {I : ℤ → Finset (Fin n) // IsSt mu I} : ℕ) : ℚ) = ((stCount n (pEnd mu) : ℕ) : ℚ) := by
    rw [h1]; unfold stCount; rw [h2]; rfl
  rw [← Nat.card_coe_set_eq]
  exact_mod_cast h4

theorem stCount_zero (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (n : ℕ) : stCount n (0 : Fin n → ℤ) = 1 := by
  have h2 := h3 n 0 (fun _ => (0 : Fin n → ℤ)) (fun _ _ _ => le_rfl)
  have h4 : ((stCount n (0 : Fin n → ℤ) : ℕ) : ℚ) = 1 := by
    unfold stCount
    rw [h2]
    refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
    split_ifs with hij
    · have : ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) ≠ 0 := by
        have h5 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hij
        linarith
      simp only [pEnd, Pi.zero_apply, Int.cast_zero, sub_zero, zero_add]
      exact div_self this
    · rfl
  exact_mod_cast h4

theorem stCount_cast {n n' : ℕ} (h : n = n') (la : Fin n' → ℤ) :
    stCount n (fun l => la (Fin.cast h l)) = stCount n' la := by
  subst h; rfl

open Classical in
theorem pieri_vec (D : Formalism.BasicNotions.D7) (h5 : GenericProjectionCriterion D) (n : ℕ) (hn : 0 < n) (ν : Fin n → ℤ) (b : ℕ) (hd : Dominant ν) :
    stCount n ν * Nat.choose (b + n - 1) (n - 1) =
      ∑ μ ∈ (Fintype.piFinset fun i : Fin n => Finset.Icc (ν i) (ν i + b)).filter (fun μ => HStrip ν μ b),
        stCount n μ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (h5 m ν b hd).1

open Classical in
theorem pieri_cov (D : Formalism.BasicNotions.D7) (h5 : GenericProjectionCriterion D) (n : ℕ) (hn : 0 < n) (ν : Fin n → ℤ) (b : ℕ) (hd : Dominant ν) :
    stCount n ν * Nat.choose (b + n - 1) (n - 1) =
      ∑ μ ∈ (Fintype.piFinset fun i : Fin n => Finset.Icc (ν i - b) (ν i)).filter (fun μ => HStrip μ ν b),
        stCount n μ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (h5 m ν b hd).2

variable {N r K : ℕ}

def StepOK (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) (i : Fin N) (la la' : Fin (r + K) → ℤ) : Prop :=
  (i.val < n0 → if LL.vec i then HStrip la la' (B i) else HStrip la' la (B i)) ∧
  (n0 ≤ i.val → (∃ d : ℕ, HStrip la la' d) ∧ ∀ m : Fin (r + K), m.val ≤ i.val - n0 → la' m = (beA n0 B : ℤ))

def VP (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) (s : ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) : Prop :=
  μ 0 = 0 ∧ (∀ t : Fin (N + 1), t.val ≤ s → Dominant (μ t)) ∧
    ∀ i : Fin N, i.val < s → StepOK LL n0 B i (μ i.castSucc) (μ i.succ)

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem sp_iff (H : HypT N n0 r K LL B od bb a La p) (μ : Fin (N + 1) → Fin (r + K) → ℤ) :
    μ ∈ SP (r := r) (K := K) LL n0 B ↔ VP LL n0 B N μ := by
  classical
  constructor
  · rintro ⟨dd, hP⟩
    obtain ⟨P, rfl⟩ := hP.path
    refine ⟨P.zero, fun t _ => P.dom t, fun i _ => ⟨fun hi => ?_, fun hi => ⟨⟨dd i, ?_⟩, fun m hm => hP.head i m hi hm⟩⟩⟩
    · have := P.step i
      rwa [hP.degs i hi] at this
    · exact step_vec P i (H.vec_true_of_late i (by omega))
  · rintro ⟨h0, hd, hs⟩
    have hex : ∀ i : Fin N, ∃ d : ℕ, (i.val < n0 → d = B i) ∧
        if LL.vec i then HStrip (μ i.castSucc) (μ i.succ) d else HStrip (μ i.succ) (μ i.castSucc) d := by
      intro i
      by_cases hi : i.val < n0
      · exact ⟨B i, fun _ => rfl, (hs i i.2).1 hi⟩
      · obtain ⟨d, hd'⟩ := ((hs i i.2).2 (by omega)).1
        refine ⟨d, fun h => absurd h hi, ?_⟩
        rw [if_pos (H.vec_true_of_late i (by omega))]
        exact hd'
    choose dd hdd using hex
    exact ⟨dd, ⟨⟨μ, h0, fun t => hd t (by have := t.2; omega), fun i => (hdd i).2⟩, rfl⟩, fun i hi => (hdd i).1 hi,
      fun i m hi hm => ((hs i i.2).2 hi).2 m hm⟩

theorem vp_le_dplus {s : ℕ} {μ : Fin (N + 1) → Fin (r + K) → ℤ} (h : VP LL n0 B s μ) :
    ∀ (t : ℕ) (ht : t < N + 1), t ≤ s → t ≤ n0 → ∀ m, μ ⟨t, ht⟩ m ≤ (dplus LL B t : ℤ) := by
  intro t
  induction t with
  | zero =>
    intro ht _ _ m
    have h0 : (⟨0, ht⟩ : Fin (N + 1)) = 0 := rfl
    rw [h0, h.1]; simp
  | succ t ih =>
    intro ht hts htn m
    have htN : t < N := by omega
    have ih' := ih (by omega) (by omega) (by omega) m
    have hst := (h.2.2 ⟨t, htN⟩ (by simp only; omega)).1 (by simp only; omega)
    have hd : dplus LL B (t + 1) = dplus LL B t + if LL.vec ⟨t, htN⟩ = true then B ⟨t, htN⟩ else 0 :=
      dsum_succ (fun l => LL.vec l = true) B t htN
    rw [hd]
    cases hv : LL.vec ⟨t, htN⟩ with
    | true =>
      rw [if_pos hv] at hst
      have h' : μ ⟨t + 1, ht⟩ m ≤ μ ⟨t, by omega⟩ m + (B ⟨t, htN⟩ : ℤ) := strip_le_add hst m
      simp only [if_true]
      push_cast
      linarith
    | false =>
      rw [if_neg (by simp [hv])] at hst
      have h' : μ ⟨t + 1, ht⟩ m ≤ μ ⟨t, by omega⟩ m := hst.1 m
      simp
      linarith

theorem dplus_le_beA' (t : ℕ) (ht : t ≤ n0) : dplus LL B t ≤ beA n0 B := by
  unfold dplus beA
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hl : l.val < t ∧ LL.vec l = true
  · rw [if_pos hl, if_pos (by omega)]
  · rw [if_neg hl]; exact Nat.zero_le _

theorem vp_le {s : ℕ} {μ : Fin (N + 1) → Fin (r + K) → ℤ} (h : VP LL n0 B s μ) :
    ∀ (t : ℕ) (ht : t < N + 1), t ≤ s → ∀ m, μ ⟨t, ht⟩ m ≤ (beA n0 B : ℤ) := by
  intro t
  induction t with
  | zero =>
    intro ht _ m
    have h0 : (⟨0, ht⟩ : Fin (N + 1)) = 0 := rfl
    rw [h0, h.1]; simp
  | succ t ih =>
    intro ht hts m
    by_cases htn : t + 1 ≤ n0
    · refine le_trans (vp_le_dplus h (t + 1) ht hts htn m) ?_
      exact_mod_cast dplus_le_beA' (t + 1) htn
    · have htN : t < N := by omega
      obtain ⟨⟨d, hst⟩, hhead⟩ := (h.2.2 ⟨t, htN⟩ (by simp only; omega)).2 (by simp only; omega)
      by_cases hm : m.val = 0
      · exact le_of_eq (hhead m (by omega))
      · have hm1 : (m.val - 1) + 1 < r + K := by have := m.2; omega
        have h2 := hst.2.1 ⟨m.val - 1, by have := m.2; omega⟩ hm1
        have hme : (⟨(m.val - 1) + 1, hm1⟩ : Fin (r + K)) = m := Fin.ext (by simp only; omega)
        rw [hme] at h2
        exact le_trans h2 (ih (by omega) (by omega) _)


open Classical in
theorem vp_update {s : ℕ} (hs : s < N) {μ : Fin (N + 1) → Fin (r + K) → ℤ} (h : VP LL n0 B s μ)
    (la' : Fin (r + K) → ℤ) (hd : Dominant la')
    (hst : StepOK LL n0 B ⟨s, hs⟩ (μ (⟨s, hs⟩ : Fin N).castSucc) la') :
    VP LL n0 B (s + 1) (Function.update μ (⟨s, hs⟩ : Fin N).succ la') := by
  have hne : ∀ t : Fin (N + 1), t.val ≤ s → t ≠ (⟨s, hs⟩ : Fin N).succ := by
    intro t ht he
    rw [he] at ht
    simp at ht
  refine ⟨?_, ?_, ?_⟩
  · rw [Function.update_of_ne (hne 0 (by simp))]; exact h.1
  · intro t ht
    by_cases he : t = (⟨s, hs⟩ : Fin N).succ
    · rw [he, Function.update_self]; exact hd
    · rw [Function.update_of_ne he]
      refine h.2.1 t ?_
      have : t.val ≠ s + 1 := fun hv => he (Fin.ext (by simpa using hv))
      omega
  · intro i hi
    by_cases he : i.val = s
    · have hi' : i = ⟨s, hs⟩ := Fin.ext he
      subst hi'
      rw [Function.update_self, Function.update_of_ne (hne _ (by simp))]
      exact hst
    · rw [Function.update_of_ne (hne _ (by simp; omega)), Function.update_of_ne (hne _ (by simp; omega))]
      exact h.2.2 i (by omega)

end

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

