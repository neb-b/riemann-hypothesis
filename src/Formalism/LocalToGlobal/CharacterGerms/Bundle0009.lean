module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.IndependenceBoundRaw
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace ValuationNonnegativity

variable {C : Type} [Field C] {V : VF C}

theorem valuation_nonneg_iff {a : C} : V.Ge 0 a ↔ 0 ≤ V.v a := by
  unfold VF.Ge
  rw [WithTop.coe_zero]

theorem mm_zero : V.MM (0 : C) := by
  unfold VF.MM
  simp

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mm_sum {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  Finset.sum_induction f (fun x => V.MM x) (fun _ _ => mm_add) mm_zero h

theorem mm_mul_int {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  have h0 := valuation_nonneg_iff.mp ha
  unfold VF.MM at *
  rw [V.v.map_mul]
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left h0)

theorem mm_of_pow {a : C} {n : ℕ} (h : V.MM (a ^ n)) : V.MM a := by
  unfold VF.MM at *
  rw [V.v.map_pow] at h
  by_contra hle
  push_neg at hle
  exact absurd h (not_lt.mpr (nsmul_nonpos hle n))

theorem mm_pow {a : C} (ha : V.MM a) {n : ℕ} (hn : n ≠ 0) : V.MM (a ^ n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold VF.MM at *
  rw [V.v.map_pow, succ_nsmul]
  exact lt_of_lt_of_le ha (le_add_of_nonneg_left (nsmul_nonneg ha.le m))

theorem valuation_nonneg_of_pow {a : C} {n : ℕ} (h : V.Ge 0 (a ^ n)) (hn : n ≠ 0) : V.Ge 0 a := by
  rw [valuation_nonneg_iff] at *
  rw [V.v.map_pow] at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_contra hlt
  push_neg at hlt
  rw [succ_nsmul] at h
  have h1 : m • V.v a ≤ 0 := nsmul_nonpos hlt.le m
  exact absurd h (not_le.mpr (lt_of_le_of_lt (le_of_le_of_eq (add_le_add h1 le_rfl) (zero_add _)) hlt))

theorem valuation_nonneg_div {x y : C} (hy : y ≠ 0) (h : V.v y ≤ V.v x) : V.Ge 0 (x / y) := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (fun h' => hy ((V.v.top_iff).mp h'))
  have hx : x = (x / y) * y := by field_simp
  rw [valuation_nonneg_iff]
  by_contra hlt
  push_neg at hlt
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  have h2 : V.v x = ((s + r : ℝ) : WithTop ℝ) := by
    rw [hx, V.v.map_mul, ← hs, ← hr, WithTop.coe_add]
  rw [← hs] at hlt
  rw [h2, ← hr] at h
  have h3 : s < 0 := by exact_mod_cast hlt
  have h4 : r ≤ s + r := by exact_mod_cast h
  linarith

private theorem v_natCast_nonneg' (n : ℕ) : 0 ≤ V.v (n : C) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    refine le_trans (le_min ih ?_) (V.v.map_add _ _)
    rw [V.v.map_one]

theorem frob2 {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) :
    V.MM ((a + b) ^ V.l - a ^ V.l - b ^ V.l) := by
  have hl := V.l_prime
  obtain ⟨k, hk⟩ : ∃ k, V.l = k + 2 := ⟨V.l - 2, by have := hl.two_le; omega⟩
  have hl' : (k + 2).Prime := hk ▸ hl
  have hint : ∀ m n : ℕ, V.Ge 0 (a ^ m * b ^ n) := by
    intro m n
    rw [valuation_nonneg_iff, V.v.map_mul, V.v.map_pow, V.v.map_pow]
    exact add_nonneg (nsmul_nonneg (valuation_nonneg_iff.mp ha) m) (nsmul_nonneg (valuation_nonneg_iff.mp hb) n)
  have hch : ∀ m ∈ Finset.range (k + 1),
      V.MM (a ^ (m + 1) * b ^ (k + 2 - (m + 1)) * ((k + 2).choose (m + 1) : C)) := by
    intro m hm
    rw [Finset.mem_range] at hm
    apply mm_mul_int (hint _ _)
    obtain ⟨t, ht⟩ : (k + 2) ∣ (k + 2).choose (m + 1) := hl'.dvd_choose_self (by omega) (by omega)
    rw [ht, Nat.cast_mul, ← hk]
    unfold VF.MM
    rw [V.v.map_mul, V.v_l]
    exact lt_of_lt_of_le (by exact_mod_cast one_pos) (le_add_of_nonneg_right (v_natCast_nonneg' t))
  have hexp : (a + b) ^ V.l - a ^ V.l - b ^ V.l =
      ∑ m ∈ Finset.range (k + 1), a ^ (m + 1) * b ^ (k + 2 - (m + 1)) * ((k + 2).choose (m + 1) : C) := by
    rw [hk, add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [pow_zero, one_mul, mul_one, Nat.sub_zero, Nat.choose_zero_right, Nat.choose_self,
      Nat.cast_one, Nat.sub_self]
    ring
  rw [hexp]
  exact mm_sum hch

theorem frob_sum {ι : Type*} (s : Finset ι) (f : ι → C) (hf : ∀ i ∈ s, V.Ge 0 (f i)) :
    V.MM ((∑ i ∈ s, f i) ^ V.l - ∑ i ∈ s, f i ^ V.l) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zero_pow V.l_prime.ne_zero, sub_zero]; exact mm_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hs : V.Ge 0 (∑ j ∈ s, f j) := VF.Ge.sum fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have h1 := frob2 (hf i (Finset.mem_insert_self i s)) hs
    have h2 := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have e : (f i + ∑ j ∈ s, f j) ^ V.l - (f i ^ V.l + ∑ j ∈ s, f j ^ V.l) =
        ((f i + ∑ j ∈ s, f j) ^ V.l - f i ^ V.l - (∑ j ∈ s, f j) ^ V.l) +
          ((∑ j ∈ s, f j) ^ V.l - ∑ j ∈ s, f j ^ V.l) := by ring
    rw [e]; exact mm_add h1 h2

theorem exists_rel {N m : ℕ} (hm : m < N) (B : Fin N → Fin m → C) :
    ∃ β : Fin N → C, (∀ ν, V.Ge 0 (β ν)) ∧ (∃ ν, ¬ V.MM (β ν)) ∧ ∀ r, ∑ ν, β ν * B ν r = 0 := by
  let f : (Fin N → C) →ₗ[C] (Fin m → C) := Matrix.vecMulLinear (Matrix.of B)
  have hk : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hm)
  obtain ⟨β, hβ, hne⟩ := (Submodule.ne_bot_iff _).mp hk
  have hrel : ∀ r, ∑ ν, β ν * B ν r = 0 := fun r => by
    have := congrFun (LinearMap.mem_ker.mp hβ) r
    simpa [f, Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct] using this
  obtain ⟨ν1, hν1⟩ : ∃ ν, β ν ≠ 0 := by
    by_contra hc; push Not at hc; exact hne (funext hc)
  obtain ⟨ν0, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun ν => V.v (β ν))
    ⟨ν1, Finset.mem_univ _⟩
  have h0 : β ν0 ≠ 0 := by
    intro h
    have := hmin ν1 (Finset.mem_univ _)
    rw [h, V.v.map_zero, top_le_iff, AddValuation.top_iff] at this
    exact hν1 this
  refine ⟨fun ν => β ν / β ν0, fun ν => valuation_nonneg_div h0 (hmin ν (Finset.mem_univ _)), ⟨ν0, ?_⟩, fun r => ?_⟩
  · show ¬ V.MM (β ν0 / β ν0)
    rw [div_self h0]; unfold VF.MM; rw [V.v.map_one]; exact lt_irrefl 0
  · simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, hrel r, zero_div]

variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]

theorem independence_bound_of_span_raw [IsAlgClosed C] (X : Cart V d I J) (a : ZMod d) (m : ℕ)
    (hR2 : ∀ (w : I → C) (x : ℕ → I ⊕ J → C), X.Good a w x → (∀ q, V.MM (X.c0' x q)) → ∀ c, V.MM (w c))
    (e : Fin m → J → C)
    (hspan : ∀ (w : I → C) (x : ℕ → I ⊕ J → C), X.Good a w x → (∀ c, V.MM (X.V2 x c)) →
      ∃ b : Fin m → C, ∀ q, V.MM (X.c0' x q ^ V.l - ∑ r, b r * e r q))
    (N : ℕ) (w : Fin N → I → C) (x : Fin N → ℕ → I ⊕ J → C) (hg : ∀ ν, X.Good a (w ν) (x ν))
    (hV : ∀ ν c, V.MM (X.V2 (x ν) c)) (hind : IndepMod V w) : N ≤ m := by
  by_contra hN; push Not at hN
  choose b hb using fun ν => hspan (w ν) (x ν) (hg ν) (hV ν)
  obtain ⟨β, hβi, ⟨ν0, hν0⟩, hrel⟩ := exists_rel (V := V) hN b
  have hl2 : 0 < V.l ^ 2 := pow_pos V.l_prime.pos 2
  choose c hc using fun ν => IsAlgClosed.exists_pow_nat_eq (β ν) hl2
  have hci : ∀ ν, V.Ge 0 (c ν) := fun ν => valuation_nonneg_of_pow (by rw [hc ν]; exact hβi ν) hl2.ne'
  have hG := Cart.Good.comb (X := X) Finset.univ (co := c) (fun ν _ => hci ν) (fun ν _ => hg ν)
  have hz : ∀ ν q, V.Ge 0 (X.c0' (x ν) q) := fun ν q => (hg ν).c0'_int q
  have hc0 : ∀ q, V.MM (X.c0' (∑ ν, teich V.l (c ν) (x ν)) q) := by
    intro q
    rw [Cart.c0'_comb]
    apply mm_of_pow (n := V.l)
    have h1 := frob_sum Finset.univ (fun ν => c ν ^ V.l * X.c0' (x ν) q)
      (fun ν _ => VF.Ge.mul_int ((hci ν).pow _) (hz ν q))
    have e1 : ∀ ν, (c ν ^ V.l * X.c0' (x ν) q) ^ V.l = β ν * X.c0' (x ν) q ^ V.l := by
      intro ν; rw [mul_pow, ← pow_mul, ← hc ν, sq]
    simp only [e1] at h1
    have h2 : V.MM (∑ ν, β ν * (X.c0' (x ν) q ^ V.l - ∑ r, b ν r * e r q)) :=
      mm_sum fun ν _ => mm_mul_int (hβi ν) (hb ν q)
    have h3 : ∑ ν, β ν * (∑ r, b ν r * e r q) = 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun r _ => ?_
      calc ∑ ν, β ν * (b ν r * e r q) = (∑ ν, β ν * b ν r) * e r q := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
        _ = 0 := by rw [hrel r, zero_mul]
    have e2 : (∑ ν, c ν ^ V.l * X.c0' (x ν) q) ^ V.l =
        ((∑ ν, c ν ^ V.l * X.c0' (x ν) q) ^ V.l - ∑ ν, β ν * X.c0' (x ν) q ^ V.l) +
          ∑ ν, β ν * (X.c0' (x ν) q ^ V.l - ∑ r, b ν r * e r q) + ∑ ν, β ν * (∑ r, b ν r * e r q) := by
      simp only [mul_sub, Finset.sum_sub_distrib]; ring
    rw [e2, h3, add_zero]
    exact mm_add h1 h2
  have hw := hR2 _ _ hG hc0
  have hcm := hind c hci (fun y => by
    have := hw y
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this)
  apply hν0
  rw [← hc ν0]
  exact mm_pow (hcm ν0) hl2.ne'

theorem even_val_add_two {d : ℕ} [NeZero d] (hd : Even d) (a : ZMod d) :
    Even (a + 2).val ↔ Even a.val := by
  have h2d : 2 ∣ d := even_iff_two_dvd.mp hd
  rw [ZMod.val_add, Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ h2d]
  have h2 : (2 : ZMod d).val % 2 = 0 := by
    rw [show (2 : ZMod d) = ((2 : ℕ) : ZMod d) by norm_num, ZMod.val_natCast, Nat.mod_mod_of_dvd _ h2d]
  omega

end ValuationNonnegativity

section Closed

variable {C : Type} [Field C]

end Closed

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieAxes
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

section VanS

variable {τ : Type}

def Van (T : Set τ) (f : MvPowerSeries τ C) : Prop :=
  ∀ ν : τ →₀ ℕ, (∀ w ∈ ν.support, w ∉ T) → coeff ν f = 0

theorem Van.mul_right {T : Set τ} {f : MvPowerSeries τ C} (hf : Van T f) (g : MvPowerSeries τ C) :
    Van T (f * g) := by
  intro ν hν
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨a, b⟩ hab
  have hab' : a + b = ν := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
  have h0 : coeff a f = 0 := hf a fun w hw => hν w (by
    rw [← hab', Finsupp.mem_support_iff, Finsupp.add_apply]
    have := Finsupp.mem_support_iff.1 hw
    omega)
  simp [h0]

theorem Van.const {T : Set τ} {f : MvPowerSeries τ C} (hf : Van T f) : constantCoeff f = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact hf 0 (by simp)

theorem Van.smul {T : Set τ} {f : MvPowerSeries τ C} (hf : Van T f) (c : C) : Van T (c • f) := by
  intro ν hν
  rw [coeff_smul, hf ν hν, mul_zero]

theorem Van.subst {σ : Type} [Finite σ] {T : Set τ} (S : Set σ) {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (haS : ∀ s ∈ S, Van T (a s)) {f : MvPowerSeries σ C}
    (hf : ∀ e : σ →₀ ℕ, (∀ s ∈ e.support, s ∉ S) → coeff e f = 0) : Van T (MvPowerSeries.subst a f) := by
  intro ν hν
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha0)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases h : ∀ s ∈ e.support, s ∉ S
  · rw [hf e h, zero_smul]
  · push Not at h
    obtain ⟨s, hs, hsS⟩ := h
    have hv : Van T (e.prod fun s m => a s ^ m) := by
      unfold Finsupp.prod
      rw [← Finset.mul_prod_erase _ _ hs]
      apply Van.mul_right
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.1 hs)
      show Van T (a s ^ e s)
      rw [hm, pow_succ']
      exact (haS s hsS).mul_right _
    rw [hv ν hν, smul_zero]

end VanS

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem van_lin (g : Fin 2) (b : I g → C) :
    Van {w : WV I | w.1 = g} (∑ c : I g, b c • (MvPowerSeries.X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C)) := by
  intro ν hν
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  apply Finset.sum_eq_zero
  intro c _
  rw [coeff_smul, coeff_X, if_neg, mul_zero]
  intro h
  exact hν ⟨g, c⟩ (by rw [h]; simp) rfl

theorem van_expPt (hex : ∀ x, constantCoeff (X.ex x) = 0) (g : Fin 2) (x : κ) :
    Van {w : WV I | w.1 = g} (X.expPt g x) := by
  unfold expPt
  refine Van.subst Set.univ (fun i => (van_lin g _).const) (fun i _ => van_lin g _) ?_
  intro e he
  have he0 : e = 0 := by
    rw [← Finsupp.support_eq_empty]
    exact Finset.eq_empty_of_forall_notMem fun s hs => he s hs (Set.mem_univ s)
  rw [he0, coeff_zero_eq_constantCoeff_apply]
  exact hex x

theorem van_hRow (hex : ∀ x, constantCoeff (X.ex x) = 0) (g : Fin 2)
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e X.h = 0) :
    Van {w : WV I | w.1 = g} X.hRow := by
  unfold hRow
  apply Van.smul
  refine Van.subst {s : Fin 2 × κ | s.1 = g} (fun s => (X.van_expPt hex s.1 s.2).const) ?_ hh
  rintro ⟨g', x⟩ hs
  have hg : g' = g := hs
  subst hg
  exact X.van_expPt hex g' x

theorem axes_of (hex : ∀ x, constantCoeff (X.ex x) = 0)
    (hh : ∀ (g : Fin 2) (e : Fin 2 × κ →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e X.h = 0) : X.AxesSt := by
  intro μ h
  rcases h with h | h
  · exact X.van_hRow hex 1 (hh 1) μ fun w hw hw1 => by
      have h0 := h w hw
      have h1 : w.1 = 1 := hw1
      rw [h0] at h1
      exact absurd h1 (by decide)
  · exact X.van_hRow hex 0 (hh 0) μ fun w hw hw0 => by
      have h1 := h w hw
      have h0 : w.1 = 0 := hw0
      rw [h1] at h0
      exact absurd h0 (by decide)

end RawChart

section FBpart

variable {dd : ℕ}

theorem fin_two_eq_one_sub_of_ne' : ∀ g g' : Fin 2, g' ≠ g → g' = 1 - g := by decide

theorem coeff_of_ev_zero (h : PS C 2 dd) (g : Fin 2) (a : Fin 2 → Pt C 1 dd) (hag : a g = 0)
    (hao : ∀ g', g' ≠ g → a g' = pt C dd 0) (hz : ev a h = 0) :
    ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0 := by
  intro e he
  set b : Fin 1 × Fin dd → PS C 2 dd := fun q => X (1 - g, q.2) with hb
  have hbS : HasSubst b := hasSubst_of_constantCoeff_zero fun q => constantCoeff_X _
  have haS : HasSubst (fun p : Fin 2 × Fin dd => a p.1 p.2) := by
    apply hasSubst_of_constantCoeff_zero
    intro s
    by_cases hs : s.1 = g
    · rw [hs, hag]; simp
    · rw [hao _ hs]; exact constantCoeff_X _
  have key : MvPowerSeries.subst b (ev a h) =
      rescale (fun s : Fin 2 × Fin dd => if s.1 = g then (0 : C) else 1) h := by
    unfold ev
    rw [subst_comp_subst_apply haS hbS, rescale_eq_subst]
    congr 1
    funext s
    by_cases hs : s.1 = g
    · have h1 : a s.1 s.2 = 0 := by rw [hs, hag]; rfl
      rw [h1, ← coe_substAlgHom hbS, map_zero]
      simp [hs]
    · have h1 : a s.1 s.2 = X ((0 : Fin 1), s.2) := by rw [hao _ hs]; rfl
      rw [h1, subst_X hbS]
      have h2 : s = (1 - g, s.2) := Prod.ext (fin_two_eq_one_sub_of_ne' g s.1 hs) rfl
      simp only [Pi.smul_apply', if_neg hs, one_smul, hb]
      rw [← h2]
  have h3 := congrArg (coeff e) key
  rw [hz, ← coe_substAlgHom hbS, map_zero, map_zero, coeff_rescale] at h3
  have h4 : (e.prod fun s m => (if s.1 = g then (0 : C) else 1) ^ m) = 1 := by
    unfold Finsupp.prod
    apply Finset.prod_eq_one
    intro s hs
    show (if s.1 = g then (0 : C) else 1) ^ e s = 1
    rw [if_neg (he s hs), one_pow]
  rw [h4, one_mul] at h3
  exact h3.symm

theorem constantCoeff_uncurry (f : PS C 1 dd) : constantCoeff (un1 f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]
  show coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) f = coeff 0 f
  rw [Finsupp.mapDomain_zero]

theorem axesFB : AxesFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p
  apply RawChart.axes_of
  · intro x
    show constantCoeff (un1 (Y.ex x)) = 0
    rw [constantCoeff_uncurry]
    exact Y.ex_const x
  · intro g
    show ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e Y.h = 0
    fin_cases g
    · refine coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl ?_ Y.gauge.ax0
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' 0 g' hg']
      rfl
    · refine coeff_of_ev_zero Y.h 1 ![pt C dd 0, 0] rfl ?_ Y.gauge.ax1
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
      rfl

end FBpart

end Formalism.L2.FormalSeriesBounds
end
end

