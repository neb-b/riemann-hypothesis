module

public import Formalism.LocalToGlobal.CharacterGerms.RowTiePIndAr
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0027
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0028

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePPTSelf
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

def PTExSelfSt : Prop :=
  AllSelf fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) →
    (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) →
    ∃ x ∈ X.TySet V g, ∀ c, x 0 (Sum.inl c) = w c

def PTAvgSelfSt : Prop :=
  AllSelf fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (x : ℕ → I g ⊕ JJ I g → C), x ∈ X.TySet V g →
    (∀ n, X.tyC g n ≠ a → x 0 n = 0) →
    ∃ x' ∈ X.TySet V g, x' 0 = x 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x' i n = 0

def OActSelfSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0)
    (g : Fin 2) (α : O) (x : ℕ → I0 ⊕ I0 → C), x ∈ (Y.rawSelf p).TySet V g →
    (fun s n => p.em ((Y.rawSelf p).tyC g n) α * x s n) ∈ (Y.rawSelf p).TySet V g

def LimSelfSt : Prop :=
  AllSelf fun C _ V _ I _ _ X => ∀ (g : Fin 2) (x : ℕ → ℕ → I g ⊕ JJ I g → C) (x' : ℕ → I g ⊕ JJ I g → C),
    (∀ k, x k ∈ X.TySet V g) → VLim V x x' → x' ∈ X.TySet V g

private theorem ge_zero_mul_field {C : Type} [Field C] (V : VF C) {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) :
    V.Ge 0 (a * b) := by
  unfold VF.Ge at *
  rw [V.v.map_mul]
  simp only [WithTop.coe_zero] at *
  exact add_nonneg ha hb

private theorem ge_zero_finset_sum_field {C : Type} [Field C] (V : VF C) {ι : Type} (s : Finset ι) (f : ι → C)
    (h : ∀ i ∈ s, V.Ge 0 (f i)) : V.Ge 0 (∑ i ∈ s, f i) := by
  refine Finset.sum_induction f (fun z => V.Ge 0 z) (fun a b ha hb => ?_) ?_ h
  · exact le_trans (le_min ha hb) (V.v.map_add a b)
  · show ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
    rw [AddValuation.map_zero]
    exact le_top

private theorem tyS_sub_ite_zero_eq_sub_C_mul_X {C : Type} [Field C] (l : ℕ) (a : ℕ → C) (c : C) :
    tyS l (fun s => a s - if s = 0 then c else 0) = tyS l a - PowerSeries.C c * PowerSeries.X := by
  ext m
  rw [map_sub, ← pow_one (PowerSeries.X : PowerSeries C), PowerSeries.coeff_C_mul_X_pow]
  simp only [tyS, PowerSeries.coeff_mk]
  have h1 : ∀ s, (if l ^ s = m then a s - (if s = 0 then c else 0) else 0) =
      (if l ^ s = m then a s else 0) - (if s = 0 then (if m = 1 then c else 0) else 0) := by
    intro s
    by_cases hs : s = 0
    · subst hs
      by_cases hm : m = 1
      · subst hm
        simp
      · have hm' : (1 : ℕ) ≠ m := fun h => hm h.symm
        simp [hm, hm']
    · simp [hs]
  rw [Finset.sum_congr rfl (fun s _ => h1 s), Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp

theorem ptSelf_of (hEx : PTExSelfSt) (hAvg : PTAvgSelfSt) (hStab : HStabSelfSt) : PTSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g a w hw hty
  obtain ⟨x, hx, hx0⟩ := hEx C V O dd Y d I0 p g a w hw hty
  obtain ⟨γ, lam, hγ, hlam, hlg, hq⟩ := hx
  have hl1 : V.l ≠ 1 := V.l_prime.one_lt.ne'
  have hγ0 : ∀ i, ∀ m < 1, PowerSeries.coeff m (γ i) = 0 := by
    intro i m hm
    rw [Nat.lt_one_iff.mp hm, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hγ i).1
  have c1 : ∀ f : ℕ → C, PowerSeries.coeff 1 (tyS V.l f) = f 0 := by
    intro f
    simp [tyS, PowerSeries.coeff_mk, Finset.sum_range_succ, hl1]
  have hdeg : ∀ j : Fin 2 × Fin dd, (Finsupp.single j 1).degree ≤ 1 := by
    intro j
    first
    | simp [Finsupp.degree_single]
    | (unfold Finsupp.degree; simp)
  have hγ1 : ∀ i, PowerSeries.coeff 1 (γ i) = ∑ c, (Y.rawSelf p).u g c i * w c := by
    intro i
    have h1 := congrArg (PowerSeries.coeff 1) (hlg i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [coeff_alongCv_low le_rfl hγ0 (FBChart.self_chart_log_constantCoeff (Y := Y) (p := p) i), map_sum] at h1
    simp only [PowerSeries.coeff_smul, c1, hx0, smul_eq_mul] at h1
    rw [← h1, Finset.sum_eq_single i]
    · rw [FBChart.rawSelf_lin (Y := Y) (p := p) i _ (hdeg i), MvPowerSeries.coeff_X, if_pos rfl, one_mul]
    · intro j _ hji
      rw [FBChart.rawSelf_lin (Y := Y) (p := p) i _ (hdeg j), MvPowerSeries.coeff_X, if_neg, zero_mul]
      intro h
      exact hji (Finsupp.single_left_injective one_ne_zero h)
    · intro h
      exact absurd (Finset.mem_univ i) h
  have key : ∀ q : I0, V.Ge 0 (PowerSeries.coeff 1 (lam q) - x 0 (Sum.inr q)) := by
    intro q
    have h2 := congrArg (PowerSeries.coeff 1) (hq q)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [c1, map_add (f := _), map_sub, map_sum,
      coeff_alongCv_low le_rfl hγ0 (RawChart.constantCoeff_sg (Y.rawSelf p) (fun e he => FBChart.rawSelf_axis0 (Y := Y) (p := p) e he) _)] at h2
    simp only [hγ1] at h2
    have hA : ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) ((Y.rawSelf p).sg ((Y.rawSelf p).u (1 - g) q)) *
        ∑ c, (Y.rawSelf p).u g c i * w c =
        ∑ c, w c * (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) := by
      simp only [RawChart.sg1, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun i _ => by ring))
    rw [hA] at h2
    have hS : ∀ c, PowerSeries.coeff 1 (if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then
        (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c))
        else 0) = if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then
        (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) * w c else 0 := by
      intro c
      split_ifs
      · simp only [PowerSeries.coeff_smul, c1, hx0, smul_eq_mul]
      · exact map_zero _
    simp only [hS] at h2
    have h3 : PowerSeries.coeff 1 (lam q) - x 0 (Sum.inr q) =
        ∑ c, if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then 0 else
          w c * (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) := by
      rw [h2, show ∀ L A S : C, L - (L - A + S) = A - S from fun L A S => by ring, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      split_ifs <;> ring
    rw [h3]
    refine ge_zero_finset_sum_field V _ _ (fun c _ => ?_)
    split_ifs with hne
    · show ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
      rw [AddValuation.map_zero]
      exact le_top
    · exact ge_zero_mul_field V (hw c) (hStab C V O dd Y d I0 p g c q hne)
  have hyT : (fun s n => Sum.elim (fun c => x s (Sum.inl c))
      (fun q => x s (Sum.inr q) - if s = 0 then x 0 (Sum.inr q) else 0) n : ℕ → I0 ⊕ I0 → C) ∈
      (Y.rawSelf p).TySet V g := by
    refine ⟨γ, fun q => lam q - PowerSeries.C (x 0 (Sum.inr q)) * PowerSeries.X, hγ, ?_, ?_, ?_⟩
    · intro q
      refine ⟨?_, ?_⟩
      · simp [(hlam q).1]
      · intro m
        rcases eq_or_ne m 1 with rfl | hm
        · have h4 : PowerSeries.coeff 1 (lam q - PowerSeries.C (x 0 (Sum.inr q)) * PowerSeries.X) =
              PowerSeries.coeff 1 (lam q) - x 0 (Sum.inr q) := by
            simp
          rw [h4]
          exact key q
        · have h4 : PowerSeries.coeff m (lam q - PowerSeries.C (x 0 (Sum.inr q)) * PowerSeries.X) =
              PowerSeries.coeff m (lam q) := by
            rw [map_sub, ← pow_one (PowerSeries.X : PowerSeries C), PowerSeries.coeff_C_mul_X_pow, if_neg hm,
              sub_zero]
          rw [h4]
          exact (hlam q).2 m
    · intro i
      exact hlg i
    · intro q
      show tyS V.l (fun s => x s (Sum.inr q) - if s = 0 then x 0 (Sum.inr q) else 0) =
        (lam q - PowerSeries.C (x 0 (Sum.inr q)) * PowerSeries.X) -
          alongCv γ ((Y.rawSelf p).sg ((Y.rawSelf p).u (1 - g) q)) +
          ∑ c, if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then
            (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c))
            else 0
      rw [tyS_sub_ite_zero_eq_sub_C_mul_X, hq q]
      ring
  obtain ⟨x', hx', h0, hvan⟩ := hAvg C V O dd Y d I0 p g a _ hyT (by
    intro n hn
    rcases n with c | q
    · show x 0 (Sum.inl c) = 0
      rw [hx0]
      exact hty c hn
    · show x 0 (Sum.inr q) - (if (0 : ℕ) = 0 then x 0 (Sum.inr q) else 0) = 0
      simp)
  refine ⟨x', hx', ?_, hvan⟩
  rw [h0]
  funext n
  rcases n with c | q
  · exact hx0 c
  · show x 0 (Sum.inr q) - (if (0 : ℕ) = 0 then x 0 (Sum.inr q) else 0) = 0
    simp

theorem ptAvgSelf_of (hAct : OActSelfSt) (hLim : LimSelfSt) : PTAvgSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g a x hx hx0
  set X := Y.rawSelf p with hX
  let M : Set (ℕ → I0 ⊕ I0 → C) := {m | ∀ y ∈ X.TySet V g, m * y ∈ X.TySet V g}
  have hAdd := addCvSelf_holds C V O dd Y d I0 p
  have h1 : (1 : ℕ → I0 ⊕ I0 → C) ∈ M := fun y hy => by rwa [one_mul]
  have hadd : ∀ m m', m ∈ M → m' ∈ M → m + m' ∈ M := fun m m' hm hm' y hy => by
    rw [add_mul]; exact X.add_mem V g hAdd (fun g c x => Y.rawSelf_u_integral p g c x) _ _ (hm y hy) (hm' y hy)
  have hneg : ∀ m, m ∈ M → -m ∈ M := fun m hm y hy => by
    rw [neg_mul]; exact X.neg_mem V g Y.l_odd _ (hm y hy)
  have hmul : ∀ m m', m ∈ M → m' ∈ M → m * m' ∈ M := fun m m' hm hm' y hy => by
    rw [mul_assoc]; exact hm _ (hm' y hy)
  have hteich : ∀ c : C, V.Ge 0 c → (fun s (_ : I0 ⊕ I0) => c ^ (V.l ^ s)) ∈ M := fun c hc y hy =>
    X.teich_mem V g c hc y hy
  have hact : ∀ α : O, (fun (_ : ℕ) n => p.em (X.tyC g n) α) ∈ M := fun α y hy =>
    hAct C V O dd Y d I0 p g α y hy
  have hlim : ∀ (m : ℕ → ℕ → I0 ⊕ I0 → C) (m' : ℕ → I0 ⊕ I0 → C), (∀ k, m k ∈ M) → VLim V m m' → m' ∈ M :=
    fun m m' hm hmm' y hy => hLim C V O dd Y d I0 p g (fun k => m k * y) (m' * y) (fun k => hm k y hy) (hmm'.mul_right y)
  have hI := IndAr.ind_gen p.em p.em_int p.em_frob p.em_sep (I0 ⊕ I0) (X.tyC g) M h1 hadd hneg hmul hteich hact hlim a
  refine ⟨_, hI x hx, ?_, ?_⟩
  · funext n
    simp only [Pi.mul_apply, Nat.cast_zero, add_zero]
    by_cases hn : X.tyC g n = a
    · rw [if_pos hn, one_mul]
    · rw [if_neg hn, zero_mul, hx0 n hn]
  · intro i n hn
    simp only [Pi.mul_apply]
    rw [if_neg hn, zero_mul]

theorem ptSelf_of_act (hEx : PTExSelfSt) (hAct : OActSelfSt) (hLim : LimSelfSt) (hStab : HStabSelfSt) : PTSelfSt :=
  ptSelf_of hEx (ptAvgSelf_of hAct hLim) hStab

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePTyp
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace TypAr

variable {C : Type} [Field C] {V : VF C}

theorem ge_lpow (k : ℕ) : V.Ge (k : ℝ) ((V.l : C) ^ k) := by
  induction k with
  | zero => simpa using VF.Ge.one (V := V)
  | succ k ih =>
    rw [pow_succ]
    have := ih.mul VF.ge_l
    convert this using 1
    push_cast; ring

theorem ge_of_lpow_dvd {k m : ℕ} (h : V.l ^ k ∣ m) : V.Ge (k : ℝ) (m : C) := by
  obtain ⟨t, rfl⟩ := h
  rw [Nat.cast_mul, Nat.cast_pow]
  simpa using (ge_lpow (V := V) k).mul (VF.ge_natCast t)

theorem vlim_const {N : Type} {a : ℕ → C} {b : C} (h : ∀ K : ℝ, ∃ k0 : ℕ, ∀ k ≥ k0, V.Ge K (b - a k)) :
    VLim V (fun k (_ : ℕ) (_ : N) => a k) (fun _ _ => b) := fun K _ _ => h K

theorem eventually_ge_nat (K : ℝ) (c : ℕ) : ∃ k0 : ℕ, ∀ k ≥ k0, K ≤ ((k + c : ℕ) : ℝ) := by
  obtain ⟨k0, hk0⟩ := exists_nat_ge K
  refine ⟨k0, fun k hk => ?_⟩
  have : (k0 : ℝ) ≤ k := by exact_mod_cast hk
  push_cast
  have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  linarith

theorem typ_gen {N : Type} (M : Set (ℕ → N → C))
    (hroot : ∀ p : ℕ, p.Prime → p ≠ V.l → ∃ ζ : C, IsPrimitiveRoot ζ p)
    (h1 : 1 ∈ M) (hadd : ∀ m m', m ∈ M → m' ∈ M → m + m' ∈ M) (hmul : ∀ m m', m ∈ M → m' ∈ M → m * m' ∈ M)
    (hteich : ∀ c : C, V.Ge 0 c → (fun n (_ : N) => c ^ n) ∈ M)
    (hlim : ∀ (m : ℕ → ℕ → N → C) (m' : ℕ → N → C), (∀ k, m k ∈ M) → VLim V m m' → m' ∈ M) :
    (fun n (_ : N) => if ∃ s, V.l ^ s = n then (1 : C) else 0) ∈ M := by
  have hl2 := V.l_prime.two_le

  have hconst : ∀ k : ℕ, (fun (_ : ℕ) (_ : N) => ((k + 1 : ℕ) : C)) ∈ M := by
    intro k
    induction k with
    | zero => convert h1 using 1; funext n x; simp
    | succ k ih =>
      have := hadd _ _ ih h1
      convert this using 1
      funext n x; simp only [Pi.add_apply, Pi.one_apply]; push_cast; ring

  have h0 : (0 : ℕ → N → C) ∈ M := by
    have hm : ∀ k, (fun (_ : ℕ) (_ : N) => ((V.l ^ k - 1 + 1 : ℕ) : C)) ∈ M := fun k => hconst _
    have e : ∀ k, ((V.l ^ k - 1 + 1 : ℕ) : C) = (V.l : C) ^ k := fun k => by
      rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ V.l_prime.pos)]; push_cast; rfl
    refine hlim (fun k (_ : ℕ) (_ : N) => ((V.l ^ k - 1 + 1 : ℕ) : C)) 0 hm ?_
    intro K s x
    obtain ⟨k0, hk0⟩ := eventually_ge_nat K 0
    refine ⟨k0, fun k hk => ?_⟩
    simp only [Pi.zero_apply, zero_sub, e]
    exact ((ge_lpow k).neg).mono (by simpa using hk0 k hk)

  have hneg : ∀ m, m ∈ M → -m ∈ M := by
    intro m hm
    have hc : ∀ k, (fun (_ : ℕ) (_ : N) => ((V.l ^ (k + 1) - 2 + 1 : ℕ) : C)) * m ∈ M :=
      fun k => hmul _ _ (hconst _) hm
    have e : ∀ k, ((V.l ^ (k + 1) - 2 + 1 : ℕ) : C) = (V.l : C) ^ (k + 1) - 1 := fun k => by
      have h2 : 2 ≤ V.l ^ (k + 1) := le_trans hl2 (Nat.le_self_pow (Nat.succ_ne_zero k) _)
      have : V.l ^ (k + 1) - 2 + 1 = V.l ^ (k + 1) - 1 := by omega
      rw [this, Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one]
    have hv : VLim V (fun k (_ : ℕ) (_ : N) => ((V.l ^ (k + 1) - 2 + 1 : ℕ) : C)) (fun _ _ => (-1 : C)) := by
      apply vlim_const
      intro K
      obtain ⟨k0, hk0⟩ := eventually_ge_nat K 1
      refine ⟨k0, fun k hk => ?_⟩
      rw [e]
      have : (-1 : C) - ((V.l : C) ^ (k + 1) - 1) = -((V.l : C) ^ (k + 1)) := by ring
      rw [this]
      exact ((ge_lpow (k + 1)).neg).mono (by simpa using hk0 k hk)
    have := hlim _ _ hc (hv.mul_right m)
    convert this using 1
    funext n x; simp
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → ℕ → N → C), (∀ i ∈ s, f i ∈ M) → (∑ i ∈ s, f i) ∈ M := by
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact hadd _ _ (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  have hprod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℕ → N → C), (∀ i ∈ s, f i ∈ M) → (∏ i ∈ s, f i) ∈ M := by
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty => simpa using h1
    | insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact hmul _ _ (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  have hpow : ∀ m, m ∈ M → ∀ e : ℕ, m ^ e ∈ M := by
    intro m hm e
    induction e with
    | zero => simpa using h1
    | succ e ih => rw [pow_succ]; exact hmul _ _ ih hm

  have hD : ∀ p : ℕ, p.Prime → p ≠ V.l → (fun n (_ : N) => if p ∣ n then (1 : C) else 0) ∈ M := by
    intro p hp hpl
    obtain ⟨ζ, hζ⟩ := hroot p hp hpl
    have hζi : ∀ j : ℕ, V.Ge 0 (ζ ^ j) := fun j =>
      VF.ge_of_pow_eq_one V hp.ne_zero (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
    set G : ℕ → N → C := ∑ j ∈ Finset.range p, fun n (_ : N) => (ζ ^ j) ^ n with hG
    have hGM : G ∈ M := hsum _ _ fun j _ => hteich _ (hζi j)
    have hGv : ∀ n x, G n x = if p ∣ n then (p : C) else 0 := by
      intro n x
      rw [hG, Finset.sum_apply, Finset.sum_apply]
      have e : ∀ j ∈ Finset.range p, (ζ ^ j) ^ n = (ζ ^ n) ^ j := fun j _ => by
        rw [← pow_mul, ← pow_mul, mul_comm]
      rw [Finset.sum_congr rfl e]
      by_cases hn : p ∣ n
      · rw [if_pos hn]
        obtain ⟨t, rfl⟩ := hn
        rw [pow_mul, hζ.pow_eq_one, one_pow]
        simp
      · rw [if_neg hn]
        have hcop : n.Coprime p := (Nat.coprime_comm.trans (Nat.Prime.coprime_iff_not_dvd hp)).mpr hn
        exact (hζ.pow_of_coprime n hcop).geom_sum_eq_zero hp.one_lt
    refine hlim (fun k => G ^ Nat.totient (V.l ^ (k + 1))) _ (fun k => hpow _ hGM _) ?_
    intro K n x
    obtain ⟨k0, hk0⟩ := eventually_ge_nat K 1
    refine ⟨k0, fun k hk => ?_⟩
    have hφ : 0 < Nat.totient (V.l ^ (k + 1)) := Nat.totient_pos.mpr (pow_pos V.l_prime.pos _)
    show V.Ge K ((if p ∣ n then (1 : C) else 0) - (G ^ Nat.totient (V.l ^ (k + 1))) n x)
    rw [Pi.pow_apply, Pi.pow_apply, hGv]
    by_cases hn : p ∣ n
    · rw [if_pos hn, if_pos hn]
      have hcop : p.Coprime (V.l ^ (k + 1)) :=
        Nat.Coprime.pow_right _ ((Nat.coprime_primes hp V.l_prime).mpr hpl)
      have hmod := Nat.ModEq.pow_totient hcop
      have hdvd : V.l ^ (k + 1) ∣ p ^ Nat.totient (V.l ^ (k + 1)) - 1 :=
        (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp hmod.symm
      have hge := ge_of_lpow_dvd (V := V) hdvd
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hp.pos), Nat.cast_pow, Nat.cast_one] at hge
      have : (1 : C) - (p : C) ^ Nat.totient (V.l ^ (k + 1)) = -((p : C) ^ Nat.totient (V.l ^ (k + 1)) - 1) := by ring
      rw [this]
      exact hge.neg.mono (by simpa using hk0 k hk)
    · rw [if_neg hn, if_neg hn, zero_pow hφ.ne', sub_zero]
      exact VF.Ge.zero K

  set S : ℕ → Finset ℕ := fun P => (Finset.range (P + 1)).filter fun p => p.Prime ∧ p ≠ V.l with hS
  set T : ℕ → ℕ → N → C := fun P => ∏ p ∈ S P, (1 + -(fun n (_ : N) => if p ∣ n then (1 : C) else 0)) with hT
  have hTM : ∀ P, T P ∈ M := fun P => hprod _ _ fun p hp => by
    have hp' := (Finset.mem_filter.mp hp).2
    exact hadd _ _ h1 (hneg _ (hD p hp'.1 hp'.2))
  refine hlim T _ hTM ?_
  intro K n x
  refine ⟨n + 3, fun P hP => ?_⟩
  show V.Ge K ((if ∃ s, V.l ^ s = n then (1 : C) else 0) - T P n x)
  have hTv : T P n x = ∏ p ∈ S P, (1 - if p ∣ n then (1 : C) else 0) := by
    show (∏ p ∈ S P, (1 + -(fun n (_ : N) => if p ∣ n then (1 : C) else 0))) n x = _
    rw [Finset.prod_apply, Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro p _
    simp [sub_eq_add_neg]
  rw [hTv]
  by_cases hpow' : ∃ s, V.l ^ s = n
  · rw [if_pos hpow']
    obtain ⟨s, rfl⟩ := hpow'
    have : ∏ p ∈ S P, (1 - if p ∣ V.l ^ s then (1 : C) else 0) = 1 := by
      apply Finset.prod_eq_one
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      have hnd : ¬ p ∣ V.l ^ s := fun h => hp'.2 ((Nat.prime_dvd_prime_iff_eq hp'.1 V.l_prime).mp (hp'.1.dvd_of_dvd_pow h))
      rw [if_neg hnd, sub_zero]
    rw [this, sub_self]
    exact VF.Ge.zero K
  · rw [if_neg hpow']
    have hex : ∃ p ∈ S P, p ∣ n := by
      by_cases hn0 : n = 0
      · subst hn0
        by_cases hl2' : V.l = 2
        · refine ⟨3, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_three, by omega⟩, dvd_zero 3⟩
        · refine ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two, fun h => hl2' h.symm⟩, dvd_zero 2⟩
      · by_contra hne
        push_neg at hne
        apply hpow'
        refine ⟨n.primeFactorsList.length, (Nat.eq_prime_pow_of_unique_prime_dvd hn0 ?_).symm⟩
        intro q hq hqn
        by_contra hql
        have hqle : q ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hqn
        exact hne q (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq, hql⟩) hqn
    obtain ⟨p, hpS, hpn⟩ := hex
    rw [Finset.prod_eq_zero hpS (by rw [if_pos hpn, sub_self]), sub_zero]
    exact VF.Ge.zero K

end TypAr

end Formalism.L2.FormalSeriesBounds
end
end

