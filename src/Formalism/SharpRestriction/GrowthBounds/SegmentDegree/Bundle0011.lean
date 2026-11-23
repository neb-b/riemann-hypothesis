module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0009
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TypicalPathOrdersSmall
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.FinalT

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.CountFromEqFilterLength
section
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas
open Formalism.InvariantFactorPaths

theorem filter_ge_get_eq_take : ∀ (L : List ℕ), L.Pairwise (· > ·) → ∀ (e : ℕ) (he : e < L.length),
    L.filter (fun y => decide (L[e] ≤ y)) = L.take (e + 1) := by
  intro L
  induction L with
  | nil => intro _ e he; simp at he
  | cons x xs ih =>
    intro hp e he
    rw [List.pairwise_cons] at hp
    cases e with
    | zero =>
      simp only [List.getElem_cons_zero, List.take_succ_cons, List.take_zero]
      rw [List.filter_cons_of_pos (by simp)]
      congr 1
      rw [List.filter_eq_nil_iff]
      intro y hy
      have h1 := hp.1 y hy
      simp only [decide_eq_true_eq, not_le]
      omega
    | succ e =>
      simp only [List.getElem_cons_succ, List.take_succ_cons]
      have hlt : xs[e]'(by simp at he; omega) < x := hp.1 _ (List.getElem_mem _)
      rw [List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; omega),
        ih hp.2 e (by simp at he; omega)]

def latestList (P : ℕ → Bool) (M : ℕ) : List ℕ := ((List.range' 1 M).filter P).reverse

theorem mem_latest_list (P : ℕ → Bool) (M y : ℕ) : y ∈ latestList P M ↔ (1 ≤ y ∧ y ≤ M) ∧ P y = true := by
  simp only [latestList, List.mem_reverse, List.mem_filter, List.mem_range'_1]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.1, by omega⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.1, by omega⟩, h2⟩

theorem latest_list_pairwise_gt (P : ℕ → Bool) (M : ℕ) : (latestList P M).Pairwise (· > ·) := by
  rw [latestList, List.pairwise_reverse]
  exact (List.pairwise_lt_range' (s := 1) (n := M)).filter _

theorem latest_list_nodup (P : ℕ → Bool) (M : ℕ) : (latestList P M).Nodup :=
  (latest_list_pairwise_gt P M).imp ne_of_gt

def countFrom (P : ℕ → Bool) (M x : ℕ) : ℕ := ((Finset.Icc 1 M).filter fun y => P y = true ∧ x ≤ y).card

theorem count_from_eq_filter_length (P : ℕ → Bool) (M x : ℕ) :
    countFrom P M x = ((latestList P M).filter fun y => decide (x ≤ y)).length := by
  unfold countFrom
  have hnd : ((latestList P M).filter fun y => decide (x ≤ y)).Nodup := (latest_list_nodup P M).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_Icc, List.mem_toFinset, List.mem_filter, mem_latest_list,
    decide_eq_true_eq]
  tauto

theorem latest_list_get_spec (P : ℕ → Bool) (M e : ℕ) (he : e < (latestList P M).length) :
    ((1 ≤ (latestList P M)[e] ∧ (latestList P M)[e] ≤ M) ∧ P (latestList P M)[e] = true) ∧
      countFrom P M (latestList P M)[e] = e + 1 := by
  refine ⟨(mem_latest_list P M _).1 (List.getElem_mem _), ?_⟩
  rw [count_from_eq_filter_length, filter_ge_get_eq_take _ (latest_list_pairwise_gt P M) e he, List.length_take]
  omega

theorem latest_list_get_of_count (P : ℕ → Bool) (M e x : ℕ) (hx : (1 ≤ x ∧ x ≤ M) ∧ P x = true) (hc : countFrom P M x = e + 1) :
    ∃ he : e < (latestList P M).length, (latestList P M)[e] = x := by
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 ((mem_latest_list P M x).2 hx)
  have h1 := (latest_list_get_spec P M i hi).2
  rw [hix, hc] at h1
  have hie : i = e := by omega
  subst hie
  exact ⟨hi, hix⟩

theorem latest_list_succ_lt (P : ℕ → Bool) (M e : ℕ) (he : e + 1 < (latestList P M).length) :
    (latestList P M)[e + 1] < (latestList P M)[e]'(by omega) := by
  exact List.pairwise_iff_getElem.1 (latest_list_pairwise_gt P M) e (e + 1) (by omega) he (by omega)

variable {N r K : ℕ}

def toL (r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) : BranchingDimensions.Letters where
  r := r
  K := K
  Ns := N
  vec := fun i => if h : 1 ≤ i ∧ i ≤ N then LL.vec ⟨i - 1, by omega⟩ else true
  B := fun i => if h : 1 ≤ i ∧ i ≤ N then B ⟨i - 1, by omega⟩ else 0

theorem toL_vec (LL : Letters (Fin N)) (B : Fin N → ℕ) (i : ℕ) (h : 1 ≤ i ∧ i ≤ N) :
    (toL r K LL B).vec i = LL.vec ⟨i - 1, by omega⟩ := by
  simp only [toL]
  rw [dite_eq_left h]

theorem toL_B (LL : Letters (Fin N)) (B : Fin N → ℕ) (i : ℕ) (h : 1 ≤ i ∧ i ≤ N) :
    (toL r K LL B).B i = B ⟨i - 1, by omega⟩ := by
  simp only [toL]
  rw [dite_eq_left h]

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem letters_n0_eq (H : HypT N n0 r K LL B od bb a La p) : (toL r K LL B).n0 = n0 := by
  show N - r = n0
  have := H.hN
  omega

theorem toL_Wf [NeZero K] (H : HypT N n0 r K LL B od bb a La p) : (toL r K LL B).Wf := by
  have hn0 := letters_n0_eq (r := r) (K := K) H
  have hN := H.hN
  have h3 := H.two_r_le_n0
  refine ⟨H.r1, Nat.one_le_iff_ne_zero.2 (NeZero.ne K), ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩
  · show 3 * r ≤ N
    omega
  · simp only [toL] at h2
    rw [toL_vec LL B i ⟨h1, by omega⟩]
    exact H.vec_true_of_early _ (by simp only; omega)
  · rw [hn0] at h1
    simp only [toL] at h2
    rw [toL_vec LL B i ⟨by omega, h2⟩]
    exact H.vec_true_of_late _ (by simp only; omega)

theorem latest_thresholds_decay (H : HypT N n0 r K LL B od bb a La p) (P : ℕ → Bool) (v : Bool)
    (hP : ∀ i (h : 1 ≤ i ∧ i ≤ N), P i = true → LL.vec ⟨i - 1, by omega⟩ = v) (l : ℕ)
    (hl : l + 1 < ((latestList P n0).map (toL r K LL B).B).length) :
    13 ^ 2 * ((latestList P n0).map (toL r K LL B).B).getD (l + 1) 0 ≤
      5 * ((latestList P n0).map (toL r K LL B).B).getD l 0 := by
  have hlen : l + 1 < (latestList P n0).length := by simpa using hl
  have e1 : ((latestList P n0).map (toL r K LL B).B).getD (l + 1) 0 =
      (toL r K LL B).B ((latestList P n0)[l + 1]) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hlen]
  have e2 : ((latestList P n0).map (toL r K LL B).B).getD l 0 =
      (toL r K LL B).B ((latestList P n0)[l]'(by omega)) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, show l < (latestList P n0).length by omega]
  rw [e1, e2]
  have hxy := latest_list_succ_lt P n0 l hlen
  have hxs := (latest_list_get_spec P n0 (l + 1) hlen).1
  have hys := (latest_list_get_spec P n0 l (by omega)).1
  generalize (latestList P n0)[l + 1] = x at hxy hxs ⊢
  generalize (latestList P n0)[l]'(by omega) = y at hxy hys ⊢
  have hN := H.hN
  rw [toL_B LL B x ⟨hxs.1.1, by omega⟩, toL_B LL B y ⟨hys.1.1, by omega⟩]
  have hv : LL.vec ⟨x - 1, by omega⟩ = LL.vec ⟨y - 1, by omega⟩ := by
    rw [hP x ⟨hxs.1.1, by omega⟩ hxs.2, hP y ⟨hys.1.1, by omega⟩ hys.2]
  have h2 := H.H2 ⟨x - 1, by omega⟩ ⟨y - 1, by omega⟩
    (by rw [Fin.lt_iff_val_lt_val]; simp only; omega) (by simp only; omega) hv
  have hp13 : (13 : ℝ) ≤ p := by exact_mod_cast H.p13
  have hB0 : (0 : ℝ) ≤ (B ⟨x - 1, by omega⟩ : ℝ) := Nat.cast_nonneg _
  have h3 : ((13 ^ 2 * B ⟨x - 1, by omega⟩ : ℕ) : ℝ) ≤ ((5 * B ⟨y - 1, by omega⟩ : ℕ) : ℝ) := by
    push_cast
    have hp2 : (169 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have h8 := mul_le_mul_of_nonneg_right hp2 hB0
    linarith
  exact_mod_cast h3

theorem toL_Hyp [NeZero K] (H : HypT N n0 r K LL B od bb a La p) : (toL r K LL B).Hyp a 13 := by
  have hn0 := letters_n0_eq (r := r) (K := K) H
  have hN := H.hN
  have h3n := H.two_r_le_n0
  have h3K := H.N_add_r_le_K
  have h4 := H.H4
  have h4a := H.N_le_a
  have eV : (toL r K LL B).latestV (toL r K LL B).n0 =
      (latestList (fun l => (toL r K LL B).vec l) n0).map (toL r K LL B).B := by
    simp only [BranchingDimensions.Letters.latestV, latestList, hn0, min_self]
  have eC : (toL r K LL B).latestC (toL r K LL B).n0 =
      (latestList (fun l => !(toL r K LL B).vec l) n0).map (toL r K LL B).B := by
    simp only [BranchingDimensions.Letters.latestC, latestList, hn0, min_self]
  refine ⟨H.a3, by norm_num, le_rfl, fun i h1 h2 => ?_, fun l hl => ?_, fun l hl => ?_,
    fun i h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hn0] at h2
    rw [toL_B LL B i ⟨h1, by omega⟩]
    have h5 := H.H1 ⟨i - 1, by omega⟩ (by simp only; omega)
    refine ⟨?_, h5.2⟩
    show r + K ≤ B ⟨i - 1, by omega⟩
    exact_mod_cast h5.1
  · rw [eV] at hl ⊢
    exact latest_thresholds_decay H _ true (fun i hi hPi => by rw [← toL_vec LL B i hi]; exact hPi) l hl
  · rw [eC] at hl ⊢
    exact latest_thresholds_decay H _ false (fun i hi hPi => by
      rw [← toL_vec LL B i hi]
      simpa using hPi) l hl
  · rw [hn0] at h1 h2
    simp only [toL] at h1
    rw [toL_vec LL B i ⟨by omega, by omega⟩]
    exact H.vec_true_of_late _ (by simp only; omega)
  · show N + r ≤ K
    omega
  · show 2 * r ≤ N
    omega
  · show r + K ≤ 2 * (K - 2 * N)
    have hK : 2 * N ≤ K := by
      have h6 : (2 * N : ℝ) ≤ K := by
        have : (0 : ℝ) ≤ ((r + K : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      exact_mod_cast h6
    have h7 : ((r + K : ℕ) : ℝ) ≤ ((2 * (K - 2 * N) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_sub hK]
      push_cast at h4 ⊢
      linarith
    exact_mod_cast h7
  · show (N : ℝ) ≤ a
    exact h4a

def toB (bb : Fin N → ℝ) (p : ℕ) : ℕ → ℝ := fun i =>
  if h : 1 ≤ i ∧ i ≤ N then 13 * bb ⟨i - 1, by omega⟩ / (p : ℝ) else 1

theorem toL_TData (H : HypT N n0 r K LL B od bb a La p) : (toL r K LL B).TData 13 La (toB bb p) := by
  have hN := H.hN
  have hp : (0 : ℝ) < p := by
    have := H.p13
    exact_mod_cast (by omega : 0 < p)
  refine ⟨H.La_pos, fun i h1 h2 => ?_⟩
  simp only [toL] at h1 h2
  have hi : 1 ≤ i ∧ i ≤ N := ⟨by omega, h2⟩
  have hb : toB bb p i = 13 * bb ⟨i - 1, by omega⟩ / (p : ℝ) := by
    simp only [toB]
    rw [dite_eq_left hi]
  refine ⟨?_, fun l hl1 hl2 hl3 => ?_⟩
  · rw [hb]
    have := H.bb_pos ⟨i - 1, by omega⟩ (by simp only; omega)
    positivity
  · rw [letters_n0_eq H] at hl3
    rw [toL_B LL B l ⟨hl1, by omega⟩, hb]
    have h5 := H.bb_le ⟨i - 1, by omega⟩ ⟨l - 1, by omega⟩ (by simp only; omega)
      (by rw [Fin.lt_iff_val_lt_val]; simp only; omega) (by simp only; omega)
    refine le_trans h5 (le_of_eq ?_)
    push_cast
    ring

end

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.KillOfEmpty
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem kill_rename {R σ τ : Type} [CommRing R] (f : σ → τ) (S : Set τ) (P : MvPolynomial σ R) :
    kill S (rename f P) = rename f (kill (f ⁻¹' S) P) := by
  have h : (kill S).comp (rename f) = (rename f).comp (kill (f ⁻¹' S) : MvPolynomial σ R →ₐ[R] _) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, rename_X, kill, aeval_X]
    by_cases h1 : f i ∈ S
    · have h2 : i ∈ f ⁻¹' S := h1
      rw [if_pos h1, if_pos h2, map_zero]
    · have h2 : i ∉ f ⁻¹' S := h1
      rw [if_neg h1, if_neg h2, rename_X]
  exact AlgHom.congr_fun h P

theorem kill_of_empty {R σ : Type} [CommRing R] (S : Set σ) (hS : S = ∅) (P : MvPolynomial σ R) : kill S P = P := by
  subst hS
  have h : (kill (∅ : Set σ) : MvPolynomial σ R →ₐ[R] _) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [kill]
  rw [h]
  rfl

theorem li_mono_words {R σ ι α : Type} [CommRing R] [IsDomain R] (Tset : Set σ) (w : α → MvPolynomial σ R)
    (hw : LinearIndependent R w) (M : ι → σ →₀ ℕ) (x : ι → α) (hM : ∀ q, ∀ v, M q v ≠ 0 → v ∈ Tset)
    (hsup : ∀ q, w (x q) ∈ supported R Tsetᶜ) (hinj : ∀ q q', M q = M q' → x q = x q' → q = q') :
    LinearIndependent R fun q => monomial (M q) (1 : R) * w (x q) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum q₀ hq₀
  obtain ⟨Φ, hΦmono⟩ : ∃ Φ : MvPolynomial σ R →ₗ[R] MvPolynomial σ R, ∀ (n : σ →₀ ℕ) (a : R),
      Φ (monomial n a) = if n.filter (· ∈ Tset) = M q₀ then monomial (n.filter (· ∉ Tset)) a else 0 := by
    refine ⟨(MvPolynomial.basisMonomials σ R).constr R (fun n : σ →₀ ℕ =>
      if n.filter (· ∈ Tset) = M q₀ then monomial (n.filter (· ∉ Tset)) (1 : R) else 0), fun n a => ?_⟩
    have e : monomial n a = a • (MvPolynomial.basisMonomials σ R) n := by
      simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, Module.Basis.constr_basis]
    split_ifs
    · rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    · rw [smul_zero]
  have hkey : ∀ q, Φ (monomial (M q) (1 : R) * w (x q)) = if M q = M q₀ then w (x q) else 0 := by
    intro q
    have hwsup := hsup q
    rw [mem_supported] at hwsup
    have hT : ∀ n ∈ (w (x q)).support, (M q + n).filter (· ∈ Tset) = M q ∧
        (M q + n).filter (· ∉ Tset) = n := by
      intro n hn
      have hnv : ∀ v, n v ≠ 0 → v ∉ Tset := fun v hv =>
        hwsup ((mem_vars_iff_mem_support v).2 ⟨n, hn, Finsupp.mem_support_iff.2 hv⟩)
      constructor
      · ext v
        rw [Finsupp.filter_apply, Finsupp.add_apply]
        by_cases hv : v ∈ Tset
        · rw [if_pos hv]
          have : n v = 0 := by
            by_contra h
            exact hnv v h hv
          rw [this, add_zero]
        · rw [if_neg hv]
          by_contra h
          exact hv (hM q v (Ne.symm h))
      · ext v
        rw [Finsupp.filter_apply, Finsupp.add_apply]
        by_cases hv : v ∈ Tset
        · rw [if_neg (not_not.2 hv)]
          by_contra h
          exact hnv v (Ne.symm h) hv
        · rw [if_pos hv]
          have : M q v = 0 := by
            by_contra h
            exact hv (hM q v h)
          rw [this, zero_add]
    conv_lhs => rw [(w (x q)).as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    simp only [monomial_mul, one_mul, hΦmono]
    split_ifs with hMq
    · conv_rhs => rw [(w (x q)).as_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [(hT n hn).1, (hT n hn).2, if_pos hMq]
    · refine Finset.sum_eq_zero fun n hn => ?_
      rw [(hT n hn).1, if_neg hMq]
  have hxinj : Function.Injective (fun q : {q // M q = M q₀} => x q.1) := by
    intro a b h
    exact Subtype.ext (hinj a.1 b.1 (a.2.trans b.2.symm) h)
  have hfib : LinearIndependent R (w ∘ fun q : {q // M q = M q₀} => x q.1) := hw.comp _ hxinj
  have h2 : ∑ q ∈ s, g q • (if M q = M q₀ then w (x q) else 0) = 0 := by
    have h := congrArg Φ hsum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h
    calc ∑ q ∈ s, g q • (if M q = M q₀ then w (x q) else 0)
        = ∑ q ∈ s, Φ (g q • (monomial (M q) (1 : R) * w (x q))) :=
          Finset.sum_congr rfl fun q _ => by rw [map_smul, hkey]
      _ = 0 := h
  have h3 : ∑ q ∈ s.subtype (fun q => M q = M q₀), g q.1 • (w ∘ fun q : {q // M q = M q₀} => x q.1) q = 0 := by
    simp only [Function.comp_apply]
    rw [Finset.sum_subtype_eq_sum_filter (f := fun q => g q • w (x q)), Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) h2
    split_ifs <;> simp
  exact linearIndependent_iff'.1 hfib (s.subtype (fun q => M q = M q₀)) (fun q => g q.1) h3 ⟨q₀, rfl⟩
    (Finset.mem_subtype.2 hq₀)

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TailTGlueT
section
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

def tailT (t : ℕ) (la : Fin (r + K) → ℤ) : Fin (K + t) → ℤ := fun l =>
  if h : (r - t) + l.val < r + K then la ⟨(r - t) + l.val, h⟩ else 0

def glueT (t : ℕ) (be : ℤ) (τ : Fin (K + t) → ℤ) : Fin (r + K) → ℤ := fun m =>
  if h : m.val < r - t then be else if h' : m.val - (r - t) < K + t then τ ⟨m.val - (r - t), h'⟩ else 0

theorem tailT_glueT (t : ℕ) (ht : t ≤ r) (be : ℤ) (τ : Fin (K + t) → ℤ) : tailT (r := r) t (glueT t be τ) = τ := by
  funext l
  have hl := l.2
  have h1 : (r - t) + l.val < r + K := by omega
  simp only [tailT, glueT, dif_pos h1]
  simp

theorem tailT_apply (t : ℕ) (ht : t ≤ r) (la : Fin (r + K) → ℤ) (l : Fin (K + t)) :
    tailT t la l = la ⟨(r - t) + l.val, by have := l.2; omega⟩ := by
  unfold tailT; rw [dif_pos]

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem finite_SAll [NeZero r] [NeZero K] (H : HypT N n0 r K LL B od bb a La p) :
    (SAll (r := r) (K := K) LL n0 B).Finite := by
  have hS : (SP (r := r) (K := K) LL n0 B).Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin (N + 1) => Set.pi Set.univ fun _ : Fin (r + K) => Set.Icc (-(beA n0 B : ℤ)) (beA n0 B)) fun _ => Set.Finite.pi fun _ => Set.finite_Icc _ _).subset ?_
    rintro μ ⟨dd, hpa⟩
    obtain ⟨P, rfl⟩ := hpa.path
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const, true_implies]
    intro s m
    exact ⟨le_trans (neg_le_neg (by exact_mod_cast dminus_le_beA H hpa.degs s.val)) (neg_dminus_le_mu P s.val s.2 m), path_le_beA H P hpa s.val s.2 m⟩
  refine (hS.biUnion fun μ _ => (Set.finite_singleton μ).prod (finite_St (tanPart μ))).subset ?_
  rintro ⟨μ, I⟩ ⟨h1, h2⟩
  exact Set.mem_biUnion h1 ⟨rfl, h2⟩


open Classical in
def Af (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) (s : ℕ) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ) :
    Finset (QT N r K) :=
  hfin.toFinset.filter fun q => ∀ t : Fin (N + 1), t.val ≤ s → q.1 t = μ0 t

open Classical in
theorem Af_fiber (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) (s : ℕ) (hs : s < N)
    (μ0 : Fin (N + 1) → Fin (r + K) → ℤ) (la' : Fin (r + K) → ℤ) :
    (Af hfin s μ0).filter (fun q => q.1 (⟨s, hs⟩ : Fin N).succ = la') =
      Af hfin (s + 1) (Function.update μ0 (⟨s, hs⟩ : Fin N).succ la') := by
  ext q
  simp only [Af, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hq, h⟩, h'⟩
    refine ⟨hq, fun t ht => ?_⟩
    by_cases e : t = (⟨s, hs⟩ : Fin N).succ
    · subst e
      rw [Function.update_apply, if_pos rfl]
      exact h'
    · rw [Function.update_of_ne e]
      apply h
      have : t.val ≠ s + 1 := fun h2 => e (Fin.ext (by simp [h2]))
      omega
  · rintro ⟨hq, h⟩
    refine ⟨⟨hq, fun t ht => ?_⟩, ?_⟩
    · have e : t ≠ (⟨s, hs⟩ : Fin N).succ := by
        rintro rfl
        simp at ht
      rw [h t (by omega), Function.update_of_ne e]
    · rw [h _ (by simp)]
      simp

theorem Af_step (H : HypT N n0 r K LL B od bb a La p) (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) (s : ℕ)
    (hs : s < N) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ) (q : QT N r K) (hq : q ∈ Af hfin s μ0) :
    Dominant (q.1 (⟨s, hs⟩ : Fin N).succ) ∧
      StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) (q.1 (⟨s, hs⟩ : Fin N).succ) := by
  classical
  simp only [Af, Finset.mem_filter, Set.Finite.mem_toFinset] at hq
  obtain ⟨⟨hsp, -⟩, hμ⟩ := hq
  obtain ⟨dd, hpa⟩ := hsp
  obtain ⟨P, hP⟩ := hpa.path
  have hc : q.1 (⟨s, hs⟩ : Fin N).castSucc = μ0 (⟨s, hs⟩ : Fin N).castSucc := hμ _ (by simp)
  rw [← hc]
  have hstep := P.step ⟨s, hs⟩
  rw [hP] at hstep
  refine ⟨by rw [← hP]; exact P.dom _, fun hlt => ?_, fun hge => ⟨⟨dd ⟨s, hs⟩, ?_⟩, fun m hm => hpa.head _ m hge hm⟩⟩
  · rwa [← hpa.degs _ hlt]
  · have hv : LL.vec ⟨s, hs⟩ = true := H.vec_true_of_late _ (Nat.le_add_right_of_le hge)
    rwa [if_pos hv] at hstep


open Classical in
theorem Af_card_sum (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) (s : ℕ) (hs : s < N)
    (μ0 : Fin (N + 1) → Fin (r + K) → ℤ) (E : Finset (Fin (r + K) → ℤ))
    (hE : ∀ q ∈ Af hfin s μ0, q.1 (⟨s, hs⟩ : Fin N).succ ∈ E) :
    (Af hfin s μ0).card = ∑ la' ∈ E, (Af hfin (s + 1) (Function.update μ0 (⟨s, hs⟩ : Fin N).succ la')).card := by
  rw [Finset.card_eq_sum_card_fiberwise hE]
  refine Finset.sum_congr rfl fun la' _ => ?_
  rw [Af_fiber hfin s hs]

end

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

