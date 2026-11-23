module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0014
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0012

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DplusLeBeS
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Gen6

variable {N r : ℕ}

theorem stg_castSucc (ν : Fin (N + 1) → Fin r → ℤ) (l : Fin N) : ν l.castSucc = stg ν l.val := by
  unfold stg
  rw [dite_eq_left (by have := l.isLt; omega)]
  rfl

theorem stg_succ (ν : Fin (N + 1) → Fin r → ℤ) (l : Fin N) : ν l.succ = stg ν (l.val + 1) := by
  unfold stg
  rw [dite_eq_left (by have := l.isLt; omega)]
  rfl

theorem stg_plPart {K : ℕ} (μ : Fin (N + 1) → Fin (r + K) → ℤ) (i : ℕ) (m : Fin r) :
    stg (plPart μ) i m = stg μ i (Fin.castAdd K m) := by
  unfold stg
  split_ifs <;> rfl

theorem colH_step {ν ν' : Fin r → ℤ} (hν : Antitone ν) (hν' : Antitone ν') (ha : ∀ a, ν a ≤ ν' a)
    (hb : ∀ (a : Fin r) (h : a.val + 1 < r), ν' ⟨a.val + 1, h⟩ ≤ ν a) (c : ℤ) :
    colH ν c ≤ colH ν' c ∧ colH ν' c ≤ colH ν c + 1 := by
  constructor
  · unfold colH
    apply Finset.card_le_card
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    exact le_trans hm (ha m)
  · unfold colH
    set S := Finset.univ.filter fun m => c ≤ ν m with hS
    set S' := Finset.univ.filter fun m => c ≤ ν' m with hS'
    have hsub : S'.image Fin.val ⊆ insert 0 (S.image fun a => a.val + 1) := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, S', S, Finset.mem_insert] at hx ⊢
      obtain ⟨m, hm, rfl⟩ := hx
      rcases Nat.eq_zero_or_pos m.val with h0 | hpos
      · left
        exact h0
      · right
        have hlt : m.val - 1 < r := by omega
        have h1 : (m.val - 1) + 1 < r := by omega
        have hm' : (⟨(m.val - 1) + 1, h1⟩ : Fin r) = m := Fin.ext (by simp; omega)
        refine ⟨⟨m.val - 1, hlt⟩, ?_, by simp; omega⟩
        have h2 := hb ⟨m.val - 1, hlt⟩ h1
        rw [hm'] at h2
        exact le_trans hm h2
    calc S'.card = (S'.image Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ (insert 0 (S.image fun a => a.val + 1)).card := Finset.card_le_card hsub
      _ ≤ (S.image fun a => a.val + 1).card + 1 := Finset.card_insert_le _ _
      _ ≤ S.card + 1 := by
        have := Finset.card_image_le (s := S) (f := fun a : Fin r => a.val + 1)
        omega

theorem cut_ppath {LL : Letters (Fin N)} {b' : Fin N → ℕ} (P1 : PPath r N LL b') (n0 : ℕ) :
    ∃ bc, ∃ Pc : PPath r N LL bc, Pc.mu = cutPath n0 P1.mu := by
  classical
  have hdom : ∀ k, k < N + 1 → Antitone (stg P1.mu k) := by
    intro k hk
    rw [← stg_eq P1.mu k hk]; exact P1.dom _
  refine ⟨fun i => if i.val < n0 then b' i else 0, ⟨cutPath n0 P1.mu, ?_, ?_, ?_⟩, rfl⟩
  · show stg P1.mu (min (0 : Fin (N + 1)).val n0) = 0
    simp only [Fin.val_zero, Nat.zero_min]
    rw [← stg_eq P1.mu 0 (by omega)]
    exact P1.zero
  · intro i
    exact hdom _ (lt_of_le_of_lt (min_le_left _ _) i.isLt)
  · intro i
    have hi := i.isLt
    by_cases h : i.val < n0
    · have e1 : cutPath n0 P1.mu i.castSucc = P1.mu i.castSucc := by
        show stg P1.mu (min i.val n0) = _
        rw [min_eq_left (by omega), stg_castSucc P1.mu]
      have e2 : cutPath n0 P1.mu i.succ = P1.mu i.succ := by
        show stg P1.mu (min (i.val + 1) n0) = _
        rw [min_eq_left (by omega), stg_succ P1.mu]
      rw [e1, e2]
      simp only [h, if_true]
      exact P1.step i
    · have e1 : cutPath n0 P1.mu i.castSucc = stg P1.mu n0 := by
        show stg P1.mu (min i.val n0) = _
        rw [min_eq_right (by omega)]
      have e2 : cutPath n0 P1.mu i.succ = stg P1.mu n0 := by
        show stg P1.mu (min (i.val + 1) n0) = _
        rw [min_eq_right (by omega)]
      rw [e1, e2]
      simp only [h, if_false]
      have hs : HStrip (stg P1.mu n0) (stg P1.mu n0) 0 :=
        ⟨fun _ => le_rfl, fun a h' => hdom n0 (by omega) (by rw [Fin.le_def]; simp), by simp⟩
      split_ifs <;> exact hs

theorem joinPT_parts {K : ℕ} (μ : Fin (N + 1) → Fin (r + K) → ℤ) : joinPT (plPart μ) (tanPart μ) = μ := by
  funext i
  exact Fin.append_castAdd_natAdd

end Gen6

section Dat6

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

theorem dplus_le_beS (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) (s : ℕ) (hs : s ≤ segN X.F j - r) :
    T.dplus (segLL X.F j) dd s ≤ X.beS p K j b := by
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  unfold T.dplus Dat.beS
  have himg : (X.F.letters j).filter (· < X.F.fr j 0) =
      (Finset.univ.filter fun l : Fin (segN X.F j) => l.val < segN X.F j - r).image (segE X.F j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨i, rfl⟩ := segE_surj X.F j hx
      exact ⟨i, (segE_lt_fr_iff X.F hV hr j i).mp hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨segE_mem X.F j i, (segE_lt_fr_iff X.F hV hr j i).mpr hi⟩
  rw [himg, Finset.sum_image (fun a _ b _ h => (segE_strictMono X.F j).injective h), Finset.sum_filter]
  refine Finset.sum_le_sum fun l _ => ?_
  split_ifs with h1 h2 h2
  · rw [hP.degs l ((segE_lt_fr_iff X.F hV hr j l).mpr h2)]
  · omega
  · exact Nat.zero_le _
  · exact le_rfl

theorem plHyp_of (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) :
    PlHyp (segN X.F j - r) (X.beS p K j b : ℤ) (plPart μ) := by
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  obtain ⟨P, hPμ⟩ := hP.path
  have hrN : r ≤ segN X.F j := k_r_le_segN X.F hV hr j
  have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK

  have htau : ∀ t (ht : t < r), ∃ l : Fin (segN X.F j), l.val = segN X.F j - r + t ∧
      segE X.F j l = X.F.fr j t ∧ HStrip (stg μ (segN X.F j - r + t)) (stg μ (segN X.F j - r + t + 1)) (dd l) := by
    intro t ht
    let l : Fin (segN X.F j) := ⟨segN X.F j - r + t, by omega⟩
    have hl : segE X.F j l = X.F.fr j t := (segE_eq_fr_iff X.F hV j l ht).mpr rfl
    have hvec : (segLL X.F j).vec l = true := by
      rw [comb_vec, hl]; exact (hV.2.2.2.2.1 j t ht).2
    have hs := T.step_vec P l hvec
    rw [hPμ, stg_castSucc μ, stg_succ μ] at hs
    exact ⟨l, rfl, hl, hs⟩
  have hlow : ∀ i ≤ segN X.F j - r, ∀ m, stg μ i m ≤ (X.beS p K j b : ℤ) := by
    intro i hi m
    have h1 := T.mu_le_dplus P i (by omega) m
    rw [hPμ, stg_eq μ i (by omega)] at h1
    have h2 := dplus_le_beS X p K hX j b μ dd hP i hi
    exact le_trans h1 (by exact_mod_cast h2)
  have hup : ∀ t ≤ r, ∀ m, stg μ (segN X.F j - r + t) m ≤ (X.beS p K j b : ℤ) := by
    intro t
    induction t with
    | zero => intro _ m; exact hlow _ le_rfl m
    | succ t ih =>
      intro ht m
      obtain ⟨l, hlv, hl, hs⟩ := htau t (by omega)
      rw [show segN X.F j - r + (t + 1) = segN X.F j - r + t + 1 by ring]
      by_cases hm : m.val = 0
      · have := hP.head l ⟨t, by omega⟩ hl m (by omega)
        rw [stg_succ μ, hlv] at this
        rw [this]
      · have hm' := m.isLt
        have h2 := hs.2.1 ⟨m.val - 1, by omega⟩ (by simp only []; omega)
        have e : (⟨(⟨m.val - 1, by omega⟩ : Fin (r + K)).val + 1, by simp only []; omega⟩ : Fin (r + K)) = m :=
          Fin.ext (by simp only []; omega)
        rw [e] at h2
        exact le_trans h2 (ih (by omega) _)
  have hdom : ∀ k, k < segN X.F j + 1 → Antitone (stg (plPart μ) k) := by
    intro k hk a a' haa
    rw [stg_plPart, stg_plPart, ← stg_eq μ k hk, ← hPμ]
    exact P.dom _ (by rw [Fin.le_def]; simpa using haa)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi m
    rw [stg_plPart]
    constructor
    · have h1 := T.mu_nonneg P i (by omega) (Fin.castAdd K m) (by
        have := m.isLt
        simp only [Fin.val_castAdd]; omega)
      rwa [hPμ, stg_eq μ i (by omega)] at h1
    · by_cases h : i ≤ segN X.F j - r
      · exact hlow i h _
      · have := hup (i - (segN X.F j - r)) (by omega) (Fin.castAdd K m)
        rwa [show segN X.F j - r + (i - (segN X.F j - r)) = i by omega] at this
  · intro m
    rw [stg_plPart]
    obtain ⟨l, hlv, hl, -⟩ := htau (r - 1) (by omega)
    have := hP.head l ⟨r - 1, by omega⟩ hl (Fin.castAdd K m) (by
      have := m.isLt
      simp only [Fin.val_castAdd]; omega)
    rw [stg_succ μ, hlv, show segN X.F j - r + (r - 1) + 1 = segN X.F j by omega] at this
    exact this
  · intro t ht c
    obtain ⟨l, hlv, hl, hs⟩ := htau t ht
    refine colH_step (hdom _ (by omega)) (hdom _ (by omega)) ?_ ?_ c
    · intro a
      rw [stg_plPart, stg_plPart]
      exact hs.1 _
    · intro a h
      rw [stg_plPart, stg_plPart]
      have := hs.2.1 (Fin.castAdd K a) (by simp only [Fin.val_castAdd]; omega)
      exact this

end Dat6

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ProdFromSelfEqOne
section
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

def prodFrom (r K n0 : ℕ) (B : Fin N → ℕ) (s : ℕ) : ℕ :=
  ∏ i : Fin N, if s ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1

theorem prodFrom_succ (n0 : ℕ) (B : Fin N → ℕ) (s : ℕ) (hs : s < N) (hsn : s < n0) :
    prodFrom r K n0 B s = Nat.choose (B ⟨s, hs⟩ + (r + K) - 1) (r + K - 1) * prodFrom r K n0 B (s + 1) := by
  classical
  unfold prodFrom
  have hpt : ∀ i : Fin N, (if s ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1) =
      (if i = ⟨s, hs⟩ then Nat.choose (B ⟨s, hs⟩ + (r + K) - 1) (r + K - 1) else 1) *
      (if s + 1 ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1) := by
    intro i
    by_cases he : i = ⟨s, hs⟩
    · subst he
      rw [if_pos ⟨le_rfl, hsn⟩, if_pos rfl, if_neg (by simp), mul_one]
    · have hne : i.val ≠ s := fun h => he (Fin.ext h)
      rw [if_neg he, one_mul]
      by_cases h1 : s ≤ i.val ∧ i.val < n0
      · rw [if_pos h1, if_pos ⟨by omega, h1.2⟩]
      · rw [if_neg h1, if_neg (by omega)]
  rw [Finset.prod_congr rfl fun i _ => hpt i, Finset.prod_mul_distrib, Finset.prod_ite_eq' ]
  simp

theorem prodFrom_self_eq_one (n0 : ℕ) (B : Fin N → ℕ) : prodFrom r K n0 B n0 = 1 := by
  unfold prodFrom
  refine Finset.prod_eq_one fun i _ => ?_
  rw [if_neg (by omega)]

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

open Classical in
theorem pre_count (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (h4 : ColumnFamilyLowerSet D) (h5 : GenericProjectionCriterion D)
    (H : HypT N n0 r K LL B od bb a La p) (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) :
    ∀ (u s : ℕ) (hsu : s + u = n0) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ), VP LL n0 B s μ0 →
      (Af hfin s μ0).card = stCount (r + K) (μ0 ⟨s, by have := H.hN; omega⟩) * prodFrom r K n0 B s := by
  have hN := H.hN
  have hn : 0 < r + K := by have := H.r1; omega
  intro u
  induction u with
  | zero =>
    intro s hsu μ0 hv
    have hs : s = n0 := by omega
    subst hs
    rw [tau_count D h3 h4 H hfin r s (by omega) le_rfl μ0 hv, prodFrom_self_eq_one, mul_one,
      ← stCount_cast (Nat.add_comm K r) (μ0 ⟨s, by omega⟩)]
    congr 1
    funext l
    rw [tailT_apply r le_rfl]
    congr 1
    exact Fin.ext (by simp)
  | succ u ih =>
    intro s hsu μ0 hv
    have hsn : s < n0 := by omega
    have hs : s < N := by omega
    have hlad : Dominant (μ0 (⟨s, hs⟩ : Fin N).castSucc) := hv.2.1 _ (by simp)
    rw [prodFrom_succ n0 B s hs hsn, ← mul_assoc]
    show _ = stCount (r + K) (μ0 (⟨s, hs⟩ : Fin N).castSucc) * _ * _
    cases hvec : LL.vec ⟨s, hs⟩ with
    | true =>
      rw [pieri_vec D h5 (r + K) hn _ (B ⟨s, hs⟩) hlad, Finset.sum_mul]
      rw [Af_card_sum hfin s hs μ0 _ ?_]
      · refine Finset.sum_congr rfl fun la' hla' => ?_
        rw [Finset.mem_filter] at hla'
        have hst : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) la' :=
          ⟨fun _ => by rw [if_pos hvec]; exact hla'.2, fun h => absurd h (by simp only; omega)⟩
        have hv' := vp_update hs hv la' (dom_of_strip_up hla'.2 hlad) hst
        rw [ih (s + 1) (by omega) _ hv']
        congr 2
        show Function.update μ0 (⟨s, hs⟩ : Fin N).succ la' (⟨s, hs⟩ : Fin N).succ = la'
        rw [Function.update_self]
      · intro q hq
        obtain ⟨_, hstq⟩ := Af_step H hfin s hs μ0 q hq
        have hS := hstq.1 hsn
        rw [if_pos hvec] at hS
        rw [Finset.mem_filter, Fintype.mem_piFinset]
        exact ⟨fun x => Finset.mem_Icc.mpr ⟨hS.1 x, strip_le_add hS x⟩, hS⟩
    | false =>
      rw [pieri_cov D h5 (r + K) hn _ (B ⟨s, hs⟩) hlad, Finset.sum_mul]
      rw [Af_card_sum hfin s hs μ0 _ ?_]
      · refine Finset.sum_congr rfl fun la' hla' => ?_
        rw [Finset.mem_filter] at hla'
        have hst : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) la' :=
          ⟨fun _ => by rw [if_neg (by simp [hvec])]; exact hla'.2, fun h => absurd h (by simp only; omega)⟩
        have hv' := vp_update hs hv la' (dom_of_strip_down hla'.2 hlad) hst
        rw [ih (s + 1) (by omega) _ hv']
        congr 2
        show Function.update μ0 (⟨s, hs⟩ : Fin N).succ la' (⟨s, hs⟩ : Fin N).succ = la'
        rw [Function.update_self]
      · intro q hq
        obtain ⟨_, hstq⟩ := Af_step H hfin s hs μ0 q hq
        have hS := hstq.1 hsn
        rw [if_neg (by simp [hvec])] at hS
        rw [Finset.mem_filter, Fintype.mem_piFinset]
        refine ⟨fun x => Finset.mem_Icc.mpr ⟨?_, hS.1 x⟩, hS⟩
        have := strip_le_add hS x
        linarith

end

theorem path_weight_eq_rank (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (h4 : ColumnFamilyLowerSet D) (h5 : GenericProjectionCriterion D) : PathWeightEqRank := by
  classical
  intro N n0 r K _ _ LL B od bb a La p H
  have hfin := finite_SAll H
  refine ⟨hfin, ?_⟩
  have hv : VP (r := r) (K := K) LL n0 B 0 (fun _ => 0) :=
    ⟨rfl, fun _ _ _ _ _ => le_rfl, fun i hi => absurd hi (by omega)⟩
  have h := pre_count D h3 h4 h5 H hfin n0 0 (by omega) (fun _ => 0) hv
  have hA : Af hfin 0 (fun _ => 0) = hfin.toFinset := by
    unfold Af
    rw [Finset.filter_eq_self]
    intro q hq t ht
    rw [Set.Finite.mem_toFinset] at hq
    have ht0 : t = 0 := Fin.ext (by simpa using ht)
    rw [ht0]
    exact ((sp_iff H q.1).1 hq.1).1
  rw [Set.ncard_eq_toFinset_card _ hfin, ← hA, h]
  have h0 : stCount (r + K) ((fun _ => 0 : Fin (N + 1) → Fin (r + K) → ℤ) ⟨0, by omega⟩) = 1 := stCount_zero D h3 (r + K)
  rw [h0, one_mul]
  unfold prodFrom rkA
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.WordOrderBoundOfNumericBound
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem ell_degree_le_power_bound : EllDegreeLePowerBound := by
  intro p n' r K _ _ _ X hX j e he
  classical
  unfold Dat.dS Dat.dV
  rw [← Finset.sum_add_distrib]
  have h1 : ∀ x ∈ X.toLate j, ((if Even x then 0 else ∑ c : Fin r, e (x, Fin.castAdd K c)) +
      (if Even x then ∑ c : Fin K, e (x, Fin.natAdd r c) else 0)) ≤ (r + K) * p ^ X.Rj p K j := by
    intro x _
    have a1 : ∑ c : Fin r, e (x, Fin.castAdd K c) ≤ r * p ^ X.Rj p K j := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin r => e (x, Fin.castAdd K c)) (p ^ X.Rj p K j)
        (fun c _ => (he.2 _).le)
      simpa using this
    have a2 : ∑ c : Fin K, e (x, Fin.natAdd r c) ≤ K * p ^ X.Rj p K j := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin K => e (x, Fin.natAdd r c)) (p ^ X.Rj p K j)
        (fun c _ => (he.2 _).le)
      simpa using this
    rw [add_mul]
    split_ifs <;> omega
  have h2 := Finset.sum_le_card_nsmul (X.toLate j) _ _ h1
  have h3 : (X.toLate j).card ≤ X.Ns := le_trans (by unfold Dat.toLate; exact Finset.card_filter_le _ _) (hX.card j)
  calc _ ≤ (X.toLate j).card • ((r + K) * p ^ X.Rj p K j) := h2
    _ = (X.toLate j).card * ((r + K) * p ^ X.Rj p K j) := smul_eq_mul _ _
    _ ≤ X.Ns * ((r + K) * p ^ X.Rj p K j) := Nat.mul_le_mul_right _ h3
    _ = (r + K) * X.Ns * p ^ X.Rj p K j := by ring

theorem degAt_ellP {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ) (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (x : ℤ) (hx : x ∈ X.toLate j) :
    DegAt x (∑ c : Fin r, e (x, Fin.castAdd K c)) (X.ellP K R j e) := by
  classical
  have h := degAt_prod (R := R) (x := x) (X.toLate j)
    (fun x' => ∏ c : Fin r, (MvPolynomial.X (x', c) : MvPolynomial (ℤ × Fin r) R) ^ e (x', Fin.castAdd K c))
    (fun x' => ∑ c : Fin r, e (x', Fin.castAdd K c) * (if x' = x then 1 else 0))
    (fun x' _ => degAt_prod Finset.univ _ _ (fun c _ => degAt_pow (degAt_X (x := x) (x', c)) _))
  have hD : (∑ x' ∈ X.toLate j, ∑ c : Fin r, e (x', Fin.castAdd K c) * (if x' = x then 1 else 0)) =
      ∑ c : Fin r, e (x, Fin.castAdd K c) := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [hy]
    · intro h; exact absurd hx h
  rw [hD] at h
  exact h

theorem degAt_ellN {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ) (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (x : ℤ) (hx : x ∈ X.toLate j) :
    DegAt x (∑ c : Fin K, e (x, Fin.natAdd r c)) (X.ellN K R j e) := by
  classical
  have h := degAt_prod (R := R) (x := x) (X.toLate j)
    (fun x' => ∏ c : Fin K, (MvPolynomial.X (x', c) : MvPolynomial (ℤ × Fin K) R) ^ e (x', Fin.natAdd r c))
    (fun x' => ∑ c : Fin K, e (x', Fin.natAdd r c) * (if x' = x then 1 else 0))
    (fun x' _ => degAt_prod Finset.univ _ _ (fun c _ => degAt_pow (degAt_X (x := x) (x', c)) _))
  have hD : (∑ x' ∈ X.toLate j, ∑ c : Fin K, e (x', Fin.natAdd r c) * (if x' = x then 1 else 0)) =
      ∑ c : Fin K, e (x, Fin.natAdd r c) := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [hy]
    · intro h; exact absurd hx h
  rw [hD] at h
  exact h

theorem word_order_bound_of_numeric_bound (D : Formalism.BasicNotions.D7) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) (C₀ : ℝ) (hRow : LateIndexInjective) (hN3 : OrderNumericBound C₀) :
    ProductOrdersBounded C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S j b e q I' I'' hc mm hmm x hx hW
  have : Fact p.Prime := ⟨hc.hX.prime⟩
  obtain ⟨i, rfl⟩ := segE_surj X.F j hx
  obtain ⟨nu, ka⟩ := q
  obtain ⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩, hcond⟩ := hc.hq
  have hI' := hc.hI'
  have hI'' := hc.hI''
  simp only at h1 h2 hcond hI' hI'' hmm
  rw [← h1] at hI' hcond hmm
  rw [← h2] at hI'' hcond hmm
  have u1 := standard_polynomial_mem_bounds (segLL X.F j) b' (fun th M => (hA3 p O S _ r (segLL X.F j) b' th M).2) P1 I' hI'
  have u2 := standard_polynomial_mem_bounds (segLL X.F j) b'' (fun th M => (hA3 p O S _ K (segLL X.F j) b'' th M).2) P2 I'' hI''
  obtain ⟨cE, cO, -⟩ := (hcond i).2 hW
  have hxl : segE X.F j i ∈ X.toLate j := (mem_late X j _).mpr ⟨hx, hW⟩
  have hrows := hRow p n' r K X hc.hX j
  have n3 := hN3 p n' r K X hc.hX hc.hLa hc.hk j _ hxl
  have hQ0 : (0 : ℝ) ≤ ((p ^ X.Rj p K j : ℕ) : ℝ) := Nat.cast_nonneg _
  have dG : DegAt (segE X.F j i) (p ^ X.Rj p K j * b'' i + ∑ c : Fin K, e (segE X.F j i, Fin.natAdd r c))
      (X.Gw p K (FF O) j e P2.mu I'') := by
    unfold Dat.Gw
    exact degAt_mul (degAt_pow (degAt_segRen X.F j u2.1 i) _) (degAt_ellN X K j e _ hxl)
  have dA : ¬ Even (segE X.F j i) →
      DegAt (segE X.F j i) (p ^ X.Rj p K j * b' i + ∑ c : Fin r, e (segE X.F j i, Fin.castAdd K c) + 0)
      (X.Aw p K (FF O) j e P1.mu I') := by
    intro he
    unfold Dat.Aw
    refine degAt_mul (degAt_mul (degAt_pow (degAt_segRen X.F j u1.1 i) _) (degAt_ellP X K j e _ hxl)) ?_
    refine degAt_of_supported {v : ℤ × Fin r | Even v.1} (DlSeg_supported _ X p K j _
      fun x' hx' a _ => ((hrows x' hx').2 a).2.1) ?_
    intro v hv hvx
    exact he (hvx ▸ hv)
  have a1 : ∑ c : Fin r, e (segE X.F j i, Fin.castAdd K c) ≤ r * p ^ X.Rj p K j := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin r => e (segE X.F j i, Fin.castAdd K c))
      (p ^ X.Rj p K j) (fun c _ => (hc.he.2 _).le)
    simpa using this
  have a2 : ∑ c : Fin K, e (segE X.F j i, Fin.natAdd r c) ≤ K * p ^ X.Rj p K j := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin K => e (segE X.F j i, Fin.natAdd r c))
      (p ^ X.Rj p K j) (fun c _ => (hc.he.2 _).le)
    simpa using this
  have a1r : ((∑ c : Fin r, e (segE X.F j i, Fin.castAdd K c) : ℕ) : ℝ) ≤ (r : ℝ) * ((p ^ X.Rj p K j : ℕ) : ℝ) := by
    exact_mod_cast a1
  have a2r : ((∑ c : Fin K, e (segE X.F j i, Fin.natAdd r c) : ℕ) : ℝ) ≤ (K : ℝ) * ((p ^ X.Rj p K j : ℕ) : ℝ) := by
    exact_mod_cast a2
  have hkd : Dat.k (r := r) K = (r : ℝ) + K := by unfold Dat.k; push_cast; ring
  rw [hkd] at n3
  have hr0 : (0 : ℝ) ≤ (r : ℝ) * ((p ^ X.Rj p K j : ℕ) : ℝ) := by positivity
  have hK0 : (0 : ℝ) ≤ (K : ℝ) * ((p ^ X.Rj p K j : ℕ) : ℝ) := by positivity
  rw [ordDeg_prod dA (fun _ => dG) mm hmm]
  refine le_trans ?_ n3
  split_ifs with he
  · have hb := mul_le_mul_of_nonneg_left (cE he).2 hQ0
    rw [Nat.cast_add, Nat.cast_mul]
    linarith
  · have hb := mul_le_mul_of_nonneg_left (cO he).2 hQ0
    rw [add_zero, Nat.cast_add, Nat.cast_mul]
    linarith

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

