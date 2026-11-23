module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqZeroOfPartialSumsNonneg
section
namespace GlobalTheory.Harm

open Finset


open Finset in
theorem _root_.GlobalTheory.Harm.sum_filter_lt_eq_sum_range {m : ℕ} (f : Fin m → ℤ) (i : ℕ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < i), f k =
      ∑ j ∈ range i, if h : j < m then f ⟨j, h⟩ else 0 := by
  rw [Finset.sum_filter]
  have hfin := Fin.sum_univ_eq_sum_range
    (fun j => if j < i then (if h : j < m then f ⟨j, h⟩ else 0) else 0) m
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta] at hfin
  rw [hfin, ← Finset.sum_filter]
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact hj.2
  · intro j hj hj'
    simp only [Finset.mem_filter, Finset.mem_range, not_and] at hj hj'
    have hjm : ¬ j < m := fun hjm => hj' hjm hj
    simp [hjm]

open Finset in
private theorem sum_range_sub_mul_eq_abel_summation (D e : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ range n, (D (i + 1) - D i) * e i =
      D n * e n + ∑ i ∈ range n, D (i + 1) * (e i - e (i + 1)) - D 0 * e 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, sum_range_succ, ih]; ring


open Finset in
theorem _root_.GlobalTheory.Harm.casimir_value_strict {m : ℕ} (κ κ₀ : Fin m → ℤ) (h : Antitone κ)
    (h₀ : Antitone κ₀)
    (hle : ∀ i : ℕ, ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < i), κ k ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < i), κ₀ k)
    (hsum : ∑ k, κ k = ∑ k, κ₀ k)
    (hC : ∑ i, κ₀ i * (κ₀ i + m - 1 - 2 * (i : ℕ)) ≤ ∑ i, κ i * (κ i + m - 1 - 2 * (i : ℕ))) : κ = κ₀ := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℤ, d = fun j =>
      (if h : j < m then κ₀ ⟨j, h⟩ else 0) - (if h : j < m then κ ⟨j, h⟩ else 0) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℤ, e = fun j =>
      if h : j < m then κ₀ ⟨j, h⟩ + κ ⟨j, h⟩ + (m : ℤ) - 1 - 2 * (j : ℤ) else 0 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℤ, D = fun j => ∑ i ∈ range j, d i := ⟨_, rfl⟩
  have hDj : ∀ j, D j = ∑ k ∈ univ.filter (fun k : Fin m => (k : ℕ) < j), κ₀ k -
      ∑ k ∈ univ.filter (fun k : Fin m => (k : ℕ) < j), κ k := by
    intro j
    simp only [hD, hd, sum_sub_distrib, _root_.GlobalTheory.Harm.sum_filter_lt_eq_sum_range]
  have hD0 : ∀ j, 0 ≤ D j := fun j => by rw [hDj]; linarith [hle j]
  have hDm : D m = 0 := by rw [hDj]; simp [hsum]
  have hDzero : D 0 = 0 := by simp [hD]
  have hdD : ∀ j, d j = D (j + 1) - D j := by intro j; simp [hD, sum_range_succ]
  have hC' : ∑ i ∈ range m, (D (i + 1) - D i) * e i ≤ 0 := by
    have h1 : ∑ i ∈ range m, d i * e i =
        ∑ i : Fin m, (κ₀ i - κ i) * (κ₀ i + κ i + m - 1 - 2 * (i : ℕ)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => d i * e i) m]
      refine sum_congr rfl (fun i _ => ?_)
      simp [hd, he, i.isLt]
    have h2 : ∑ i : Fin m, (κ₀ i - κ i) * (κ₀ i + κ i + m - 1 - 2 * (i : ℕ)) =
        ∑ i, κ₀ i * (κ₀ i + m - 1 - 2 * (i : ℕ)) - ∑ i, κ i * (κ i + m - 1 - 2 * (i : ℕ)) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl (fun i _ => ?_)
      ring
    simp_rw [← hdD]
    rw [h1, h2]
    linarith
  have key := sum_range_sub_mul_eq_abel_summation D e m
  rw [hDm, hDzero, zero_mul, zero_mul, zero_add, sub_zero] at key
  have he_gap : ∀ i, i + 1 < m → 2 ≤ e i - e (i + 1) := by
    intro i hi
    have h1 := h₀ (Fin.mk_le_mk.mpr (Nat.le_succ i) : (⟨i, by omega⟩ : Fin m) ≤ ⟨i + 1, hi⟩)
    have h2 := h (Fin.mk_le_mk.mpr (Nat.le_succ i) : (⟨i, by omega⟩ : Fin m) ≤ ⟨i + 1, hi⟩)
    simp only [he, hi, show i < m by omega, ↓reduceDIte]
    push_cast
    linarith
  have hterm : ∀ i ∈ range m, 0 ≤ D (i + 1) * (e i - e (i + 1)) := by
    intro i hi
    rw [mem_range] at hi
    rcases Nat.lt_or_ge (i + 1) m with h' | h'
    · exact mul_nonneg (hD0 _) (by linarith [he_gap i h'])
    · rw [show i + 1 = m by omega, hDm, zero_mul]
  have hsum0 : ∑ i ∈ range m, D (i + 1) * (e i - e (i + 1)) = 0 :=
    le_antisymm (by linarith) (sum_nonneg hterm)
  have hall := (sum_eq_zero_iff_of_nonneg hterm).mp hsum0
  have hDall : ∀ j, j ≤ m → D j = 0 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hDzero
    rcases Nat.lt_or_ge j m with hjm | hjm
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rcases mul_eq_zero.mp (hall i (mem_range.mpr (by omega))) with h0 | h0
      · exact h0
      · linarith [he_gap i hjm]
    · rw [show j = m by omega]
      exact hDm
  funext k
  have hk' := k.isLt
  have hk := hdD k
  rw [hDall ((k : ℕ) + 1) (by omega), hDall (k : ℕ) (by omega)] at hk
  simp [hd, k.isLt] at hk
  linarith

def mixedWeight (m : ℕ) {p q : ℕ} (a : Fin p → ℕ) (b : Fin q → ℕ) : Fin m → ℤ := fun k =>
  (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) -
    (if h : m - 1 - (k : ℕ) < q then (b ⟨m - 1 - k, h⟩ : ℤ) else 0)

theorem mixedWeight_apply (m : ℕ) {p q : ℕ} (a : Fin p → ℕ) (b : Fin q → ℕ) (k : Fin m) :
    mixedWeight m a b k =
      (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) -
        (if h : m - 1 - (k : ℕ) < q then (b ⟨m - 1 - k, h⟩ : ℤ) else 0) := rfl


open Finset in
theorem _root_.GlobalTheory.Harm.antitone_mixedWeight (m : ℕ) {p q : ℕ} {a : Fin p → ℕ} {b : Fin q → ℕ}
    (ha : Antitone a) (hb : Antitone b) : Antitone (_root_.GlobalTheory.Harm.mixedWeight m a b) := by
  intro k l hkl
  have hkl' : (k : ℕ) ≤ l := hkl
  simp only [_root_.GlobalTheory.Harm.mixedWeight_apply]
  have hA : (if h : (l : ℕ) < p then (a ⟨l, h⟩ : ℤ) else 0) ≤
      (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) := by
    split_ifs <;> first
      | omega | positivity | exact le_rfl | exact_mod_cast ha (Fin.mk_le_mk.mpr hkl')
  have hB : (if h : m - 1 - (k : ℕ) < q then (b ⟨m - 1 - k, h⟩ : ℤ) else 0) ≤
      (if h : m - 1 - (l : ℕ) < q then (b ⟨m - 1 - l, h⟩ : ℤ) else 0) := by
    split_ifs <;> first
      | omega | positivity | exact le_rfl | exact_mod_cast hb (Fin.mk_le_mk.mpr (by omega))
  linarith


open Finset in
theorem _root_.GlobalTheory.Harm.sum_dite_lt {m p : ℕ} (hp : p ≤ m) (f : Fin p → ℤ) :
    ∑ k : Fin m, (if h : (k : ℕ) < p then f ⟨k, h⟩ else 0) = ∑ k, f k := by
  have hfin := Fin.sum_univ_eq_sum_range (fun j => if h : j < p then f ⟨j, h⟩ else 0) m
  have hfin' := Fin.sum_univ_eq_sum_range (fun j => if h : j < p then f ⟨j, h⟩ else 0) p
  beta_reduce at hfin
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta] at hfin'
  rw [hfin, hfin']
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro j _ hj
    simp only [Finset.mem_range] at hj
    simp [hj]


open Finset in
theorem _root_.GlobalTheory.Harm.sum_dite_rev_lt {m q : ℕ} (hq : q ≤ m) (f : Fin q → ℤ) :
    ∑ k : Fin m, (if h : m - 1 - (k : ℕ) < q then f ⟨m - 1 - k, h⟩ else 0) = ∑ k, f k := by
  rw [← _root_.GlobalTheory.Harm.sum_dite_lt hq f]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun k => ?_)
  have hk : ((Fin.revPerm k : Fin m) : ℕ) = m - 1 - k := by
    simp only [Fin.revPerm_apply, Fin.val_rev]
    omega
  simp only [hk]


open Finset in
theorem _root_.GlobalTheory.Harm.sum_mixedWeight {m p q : ℕ} (h : p + q ≤ m) (a : Fin p → ℕ) (b : Fin q → ℕ) :
    ∑ k, _root_.GlobalTheory.Harm.mixedWeight m a b k = ∑ i, (a i : ℤ) - ∑ i, (b i : ℤ) := by
  have h1 := _root_.GlobalTheory.Harm.sum_dite_lt (m := m) (by omega : p ≤ m)
    (fun i => (a i : ℤ))
  have h2 := _root_.GlobalTheory.Harm.sum_dite_rev_lt (m := m) (by omega : q ≤ m)
    (fun i => (b i : ℤ))
  beta_reduce at h1 h2
  simp only [_root_.GlobalTheory.Harm.mixedWeight_apply, Finset.sum_sub_distrib]
  rw [h1, h2]


open Finset in
theorem _root_.GlobalTheory.Harm.casimir_value_mixedWeight {m p q : ℕ} (h : p + q ≤ m) (a : Fin p → ℕ) (b : Fin q → ℕ) :
    ∑ k : Fin m, _root_.GlobalTheory.Harm.mixedWeight m a b k * (_root_.GlobalTheory.Harm.mixedWeight m a b k + m - 1 - 2 * (k : ℕ)) =
      (∑ i : Fin p, (a i : ℤ) * (a i + p - 1 - 2 * (i : ℕ)) + ((m : ℤ) - p) * ∑ i, (a i : ℤ)) +
      (∑ i : Fin q, (b i : ℤ) * (b i + q - 1 - 2 * (i : ℕ)) + ((m : ℤ) - q) * ∑ i, (b i : ℤ)) := by
  have hp : p ≤ m := by omega
  have hq : q ≤ m := by omega
  have h1 := _root_.GlobalTheory.Harm.sum_dite_lt hp
    (fun i : Fin p => (a i : ℤ) * (a i + m - 1 - 2 * (i : ℕ)))
  have h2 := _root_.GlobalTheory.Harm.sum_dite_rev_lt hq
    (fun j : Fin q => (b j : ℤ) * (b j + m - 1 - 2 * (j : ℕ)))
  beta_reduce at h1 h2
  simp only [Fin.val_mk] at h1 h2
  have hpt : ∀ k : Fin m, _root_.GlobalTheory.Harm.mixedWeight m a b k *
        (_root_.GlobalTheory.Harm.mixedWeight m a b k + m - 1 - 2 * (k : ℕ)) =
      (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) * (a ⟨k, h⟩ + m - 1 - 2 * (k : ℕ)) else 0) +
      (if h : m - 1 - (k : ℕ) < q then
        (b ⟨m - 1 - k, h⟩ : ℤ) * (b ⟨m - 1 - k, h⟩ + m - 1 - 2 * (m - 1 - (k : ℕ) : ℕ))
        else 0) := by
    intro k
    have hk := k.isLt
    have hc : ((m - 1 - (k : ℕ) : ℕ) : ℤ) = (m : ℤ) - 1 - (k : ℕ) := by omega
    rw [_root_.GlobalTheory.Harm.mixedWeight_apply]
    split_ifs <;> first | omega | (rw [hc]; ring) | ring
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, h1, h2,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1 <;> refine Finset.sum_congr rfl (fun i _ => ?_) <;> ring

end GlobalTheory.Harm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsJointIntEigenvectorOfStable
section
namespace GlobalTheory

theorem exists_int_eigenvector_of_stable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) (hf : ⨆ n : ℤ, f.eigenspace (n : K) = ⊤)
    (U : Submodule K V) (hU : ∀ x ∈ U, f x ∈ U) (hU0 : U ≠ ⊥) :
    ∃ n : ℤ, ∃ u ∈ U, u ≠ 0 ∧ f u = (n : K) • u := by
  classical
  have key : ∀ s : Finset ℤ, ∀ x ∈ U, x ≠ 0 → x ∈ (⨆ n ∈ s, f.eigenspace (n : K)) →
      ∃ n : ℤ, ∃ u ∈ U, u ≠ 0 ∧ f u = (n : K) • u := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x _ hx0 hx; simp at hx; exact absurd hx hx0
    | insert a s _ ih =>
      intro x hxU hx0 hx
      by_cases hw : f x - (a : K) • x = 0
      · exact ⟨a, x, hxU, hx0, sub_eq_zero.mp hw⟩
      · refine ih _ (U.sub_mem (hU x hxU) (U.smul_mem _ hxU)) hw ?_
        rw [Finset.iSup_insert, Submodule.mem_sup] at hx
        obtain ⟨y, hy, z, hz, rfl⟩ := hx
        rw [Module.End.mem_eigenspace_iff] at hy
        have h1 : f (y + z) - (a : K) • (y + z) = f z - (a : K) • z := by
          rw [map_add (f := _), hy, smul_add]; abel
        rw [h1]
        refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ hz)
        have : (⨆ n ∈ s, f.eigenspace (n : K)) ≤ (⨆ n ∈ s, f.eigenspace (n : K)).comap f := by
          refine iSup₂_le fun n hn => ?_
          intro w hw
          rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff.mp hw]
          exact Submodule.smul_mem _ _
            (le_iSup₂ (f := fun n (_ : n ∈ s) => f.eigenspace (n : K)) n hn hw)
        exact this hz
  obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  have hx : x ∈ ⨆ n : ℤ, f.eigenspace (n : K) := by rw [hf]; trivial
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hx
  exact key s x hxU hx0 hs

theorem exists_joint_int_eigenvector_of_stable {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype ι] (f : ι → Module.End K V) (hc : ∀ a b, f a * f b = f b * f a)
    (hf : ∀ a, ⨆ n : ℤ, (f a).eigenspace (n : K) = ⊤)
    (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, f a x ∈ W) (hW0 : W ≠ ⊥) :
    ∃ κ : ι → ℤ, ∃ u ∈ W, u ≠ 0 ∧ ∀ a, f a u = (κ a : K) • u := by
  classical
  have key : ∀ s : Finset ι, ∃ U : Submodule K V, U ≤ W ∧ U ≠ ⊥ ∧ (∀ a, ∀ x ∈ U, f a x ∈ U) ∧
      ∃ κ : ι → ℤ, ∀ a ∈ s, ∀ x ∈ U, f a x = (κ a : K) • x := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨W, le_rfl, hW0, hW, 0, by simp⟩
    | insert a s ha ih =>
      obtain ⟨U, hUW, hU0, hU, κ, hκ⟩ := ih
      obtain ⟨n, u, huU, hu0, hu⟩ := exists_int_eigenvector_of_stable (f a) (hf a) U (hU a) hU0
      refine ⟨U ⊓ (f a).eigenspace (n : K), inf_le_left.trans hUW, ?_, ?_,
        Function.update κ a n, ?_⟩
      · rw [Submodule.ne_bot_iff]
        exact ⟨u, ⟨huU, Module.End.mem_eigenspace_iff.mpr hu⟩, hu0⟩
      · intro b x hx
        refine ⟨hU b x hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        have h1 := Module.End.mem_eigenspace_iff.mp hx.2
        have h2 := LinearMap.congr_fun (hc a b) x
        simp only [Module.End.mul_apply] at h2
        rw [h2, h1, map_smul]
      · intro b hb x hx
        rcases Finset.mem_insert.mp hb with rfl | hb
        · rw [Function.update_self]; exact Module.End.mem_eigenspace_iff.mp hx.2
        · have : b ≠ a := fun h => ha (h ▸ hb)
          rw [Function.update_of_ne this]; exact hκ b hb x hx.1
  obtain ⟨U, hUW, hU0, -, κ, hκ⟩ := key Finset.univ
  obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  exact ⟨κ, x, hUW hxU, hx0, fun a => hκ a (Finset.mem_univ a) x hxU⟩

theorem exists_highest_vector {K V T : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [Fintype T] [DecidableEq T] {m : ℕ}
    (e : T → Fin m → Fin m → Module.End K V)
    (he : ∀ t t' i k l, e t i i * e t' k l - e t' k l * e t i i = (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : K) else 0) • e t' k l)
    (hdiag : ⨆ κ : T → Fin m → ℤ, (⨅ t, ⨅ i, Module.End.eigenspace (e t i i) (κ t i : K)) = ⊤)
    (W : Submodule K V) [FiniteDimensional K W] (hW : ∀ t i j, ∀ w ∈ W, e t i j w ∈ W) (hW0 : W ≠ ⊥) :
    ∃ v ∈ W, v ≠ 0 ∧ (∀ t i j, i < j → e t i j v = 0) ∧ ∃ κ : T → Fin m → ℤ, ∀ t i, e t i i v = (κ t i : K) • v := by
  classical

  obtain ⟨κ₀, u₀, hu₀W, hu₀, hκ₀⟩ := exists_joint_int_eigenvector_of_stable
    (fun a : T × Fin m => e a.1 a.2 a.2)
    (by
      intro a b
      have := he a.1 b.1 a.2 b.2 b.2
      rw [sub_self, ite_self, zero_smul] at this
      exact sub_eq_zero.mp this)
    (by
      intro a
      rw [eq_top_iff, ← hdiag]
      refine iSup_le fun κ => ?_
      exact le_trans ((iInf_le _ a.1).trans (iInf_le _ a.2))
        (le_iSup (fun n : ℤ => (e a.1 a.2 a.2).eigenspace (n : K)) (κ a.1 a.2)))
    W (fun a => hW a.1 a.2 a.2) hW0

  let ht : (T → Fin m → ℤ) → ℤ := fun κ => ∑ t, ∑ i : Fin m, (i : ℤ) * κ t i
  let h : Module.End K V := ∑ t, ∑ i : Fin m, ((i : ℕ) : K) • e t i i
  have hhW : ∀ w ∈ W, h w ∈ W := by
    intro w hw
    simp only [h, LinearMap.sum_apply, LinearMap.smul_apply]
    exact W.sum_mem fun t _ => W.sum_mem fun i _ => W.smul_mem _ (hW t i i w hw)
  have hh : ∀ (κ : T → Fin m → ℤ) (v : V), (∀ t i, e t i i v = (κ t i : K) • v) →
      h v = (ht κ : K) • v := by
    intro κ v hv
    simp only [h, ht, LinearMap.sum_apply, LinearMap.smul_apply, hv, smul_smul]
    push_cast
    simp only [Finset.sum_smul]
  let S : Set ℤ := {n | ∃ κ : T → Fin m → ℤ, ht κ = n ∧
    ∃ v ∈ W, v ≠ 0 ∧ ∀ t i, e t i i v = (κ t i : K) • v}
  have hS : S.Finite := by
    have hfin := Module.End.finite_hasEigenvalue (h.restrict hhW)
    refine (hfin.preimage (f := fun n : ℤ => (n : K)) Int.cast_injective.injOn).subset ?_
    rintro n ⟨κ, rfl, v, hvW, hv0, hv⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvW⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (hh κ v hv)
    · exact fun h0 => hv0 (congrArg Subtype.val h0)
  have hSne : S.Nonempty :=
    ⟨_, fun t i => κ₀ (t, i), rfl, u₀, hu₀W, hu₀, fun t i => hκ₀ (t, i)⟩
  obtain ⟨n, ⟨κ, rfl, v, hvW, hv0, hv⟩, hmin⟩ := Set.exists_min_image S id hS hSne
  refine ⟨v, hvW, hv0, ?_, κ, hv⟩
  intro t' k l hkl
  by_contra hne
  let δ : T → Fin m → ℤ := fun t i =>
    if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0)) else 0
  have hmem : ht (κ + δ) ∈ S := by
    refine ⟨κ + δ, rfl, e t' k l v, hW _ _ _ v hvW, hne, fun t i => ?_⟩
    have h1 := LinearMap.congr_fun (he t t' i k l) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hv,
      map_smul] at h1
    rw [sub_eq_iff_eq_add] at h1
    rw [h1, ← add_smul, add_comm]
    congr 1
    simp only [δ, Pi.add_apply]
    push_cast
    rfl
  have hδ : ht δ = (k : ℤ) - (l : ℤ) := by
    simp only [ht, δ]
    rw [Finset.sum_eq_single t']
    · simp [mul_sub, Finset.sum_sub_distrib]
    · intro b _ hb; simp [hb]
    · simp
  have hadd : ht (κ + δ) = ht κ + ht δ := by
    simp only [ht, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have h2 := hmin _ hmem
  have h3 : (k : ℕ) < l := hkl
  simp only [id] at h2
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatSmulCoeffIsIntegral
section
namespace GlobalTheory.NatMultipleIntegralCoefficients

theorem exists_nat_smul_coeff_isIntegral {σ K : Type} [Field K] [CharZero K]
    [FiniteDimensional ℚ K] (P : MvPolynomial σ K) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : σ →₀ ℕ, IsIntegral ℤ (AddMonoidAlgebra.coeff ((N : K) • P) m) := by
  classical
  have halg : ∀ x : K, IsAlgebraic ℤ x := fun x =>
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic x)
  have hx : ∀ x : K, ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : K) * x) := by
    intro x
    obtain ⟨y, hy, h⟩ := (halg x).exists_integral_multiple
    refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq y with e | e
    · rw [e] at h
      simpa using h
    · rw [e] at h
      have h2 := h.neg
      simpa using h2
  choose n hn hi using hx
  refine ⟨∏ m ∈ P.support, n (P.coeff m), Finset.prod_pos fun m _ => hn _, fun m => ?_⟩
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases hm : m ∈ P.support
  · rw [← Finset.prod_erase_mul _ _ hm, Nat.cast_mul, mul_assoc]
    refine IsIntegral.mul ?_ (hi _)
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K)
      (x := ((∏ k ∈ P.support.erase m, n (P.coeff k) : ℕ) : ℤ)))
  · rw [MvPolynomial.notMem_support_iff.1 hm, mul_zero]
    exact isIntegral_zero

end GlobalTheory.NatMultipleIntegralCoefficients
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Imports
section
namespace GlobalTheory.CuspFormEvaluationSupplement

universe u_1

theorem main : ∀ {R : Type u_1} [inst : CommRing R] {P : Ideal R}, Ideal.IsPrime P → ∀ (N : ℕ), N ≠ (0 : ℕ) → (↑N : R) ∈ P → ∃ (p : ℕ), Nat.Prime p ∧ p ∣ N ∧ (↑p : R) ∈ P := by
  intro R _ P hP N
  induction N using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h1
    exact absurd ((Ideal.eq_top_iff_one P).mpr (by simpa using h1)) hP.ne_top
  | prime_mul p a hp ih =>
    intro hN hmem
    have ha : a ≠ 0 := by rintro rfl; simp at hN
    push_cast at hmem
    rcases hP.mem_or_mem hmem with h | h
    · exact ⟨p, hp, dvd_mul_right p a, h⟩
    · obtain ⟨q, hq, hqa, hqP⟩ := ih ha h
      exact ⟨q, hq, dvd_mul_of_dvd_right hqa p, hqP⟩

end GlobalTheory.CuspFormEvaluationSupplement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ImportsAlt
section
namespace GlobalTheory.CuspFormEvaluationComplement

theorem main : ∀ (s : Multiset ℂ) {t : ℝ}, (0 : ℝ) ≤ t → (∀ μ ∈ s, ‖μ - (1 : ℂ)‖ ≤ t) →
    ‖Multiset.prod s - (1 : ℂ)‖ ≤ Real.exp ((↑(Multiset.card s) : ℝ) * t) - (1 : ℝ) := by
  intro s t ht hs
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : ‖a - 1‖ ≤ t := hs a (Multiset.mem_cons_self a s)
    have ih' := ih (fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ))
    rw [Multiset.prod_cons, Multiset.card_cons]
    have hna : ‖a‖ ≤ 1 + t := by
      have h0 : a = (a - 1) + 1 := by ring
      calc ‖a‖ = ‖(a - 1) + 1‖ := by rw [← h0]
        _ ≤ ‖a - 1‖ + ‖(1:ℂ)‖ := norm_add_le _ _
        _ ≤ 1 + t := by rw [norm_one]; linarith
    have key : a * s.prod - 1 = a * (s.prod - 1) + (a - 1) := by ring
    have h1 : ‖a * s.prod - 1‖ ≤ (1 + t) * (Real.exp ((Multiset.card s : ℝ) * t) - 1) + t := by
      rw [key]
      calc ‖a * (s.prod - 1) + (a - 1)‖ ≤ ‖a * (s.prod - 1)‖ + ‖a - 1‖ := norm_add_le _ _
        _ = ‖a‖ * ‖s.prod - 1‖ + ‖a - 1‖ := by rw [norm_mul]
        _ ≤ (1 + t) * (Real.exp ((Multiset.card s : ℝ) * t) - 1) + t :=
          add_le_add (mul_le_mul hna ih' (norm_nonneg _) (by linarith)) ha
    have h2 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have hE := Real.exp_pos ((Multiset.card s : ℝ) * t)
    have h3 := mul_le_mul_of_nonneg_right h2 hE.le
    have hexp : Real.exp (((Multiset.card s + 1 : ℕ) : ℝ) * t)
        = Real.exp t * Real.exp ((Multiset.card s : ℝ) * t) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    rw [hexp]
    nlinarith [h1, h3]

end GlobalTheory.CuspFormEvaluationComplement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogNormMapPowMulPowOfMulConj
section
open scoped BigOperators

namespace GlobalTheory

theorem norm_map_eq_sqrt_of_mul_conj {K : Type*} [Semiring K] (σ : K →+* ℂ) (x y : K) (g : ℕ)
    (hxy : x * y = g) (hy : σ y = starRingEnd ℂ (σ x)) : ‖σ x‖ = (g : ℝ) ^ (1 / 2 : ℝ) := by
  have h : σ x * starRingEnd ℂ (σ x) = (g : ℂ) := by
    rw [← hy, ← map_mul, hxy, map_natCast]
  have h2 : ((‖σ x‖ : ℝ) : ℂ) ^ 2 = (g : ℂ) := by
    rw [← Complex.mul_conj', h]
  have h3 : ‖σ x‖ ^ 2 = (g : ℝ) := by exact_mod_cast h2
  rw [← Real.sqrt_eq_rpow, ← h3, Real.sqrt_sq (norm_nonneg _)]

theorem norm_map_pow_mul_pow_of_mul_conj {K : Type*} [Semiring K] (σ : K →+* ℂ) (x y : K) (g : ℕ)
    (hxy : x * y = g) (hy : σ y = starRingEnd ℂ (σ x)) (a b : ℕ) :
    ‖σ (x ^ a * y ^ b)‖ = (g : ℝ) ^ (((a : ℝ) + b) / 2) := by
  have h1 := norm_map_eq_sqrt_of_mul_conj σ x y g hxy hy
  have hyn : ‖σ y‖ = ‖σ x‖ := by rw [hy]; simp
  rw [map_mul, map_pow, map_pow, norm_mul, norm_pow, norm_pow, hyn, ← pow_add, h1,
    ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg g)]
  congr 1
  push_cast
  ring

end GlobalTheory
end

