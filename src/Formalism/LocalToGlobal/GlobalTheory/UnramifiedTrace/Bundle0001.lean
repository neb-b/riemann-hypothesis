module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.CardFilterSubtype
section
namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

private theorem eq_pow_sub_of_mul_pow_eq_pow {c q k n : ℕ} (hq : 1 < q) (hc : 1 ≤ c) (h : c * q ^ k = q ^ n) :
    c = q ^ (n - k) := by
  have hkn : k ≤ n := by
    by_contra hlt
    push_neg at hlt
    have h1 : q ^ n < q ^ k := Nat.pow_lt_pow_right hq hlt
    have h2 : q ^ k ≤ c * q ^ k := Nat.le_mul_of_pos_left _ hc
    omega
  have hpos : 0 < q ^ k := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h, ← pow_add, Nat.sub_add_cancel hkn]

theorem card_fib_mul {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Fintype V] [Fintype W] [DecidableEq W] (f : V →+ W)
    (hf : Function.Surjective f) (w : W) :
    (Finset.univ.filter (fun v => f v = w)).card * Fintype.card W = Fintype.card V := by
  have hall : ∀ w', (Finset.univ.filter (fun v => f v = w')).card =
      (Finset.univ.filter (fun v => f v = w)).card := by
    intro w'
    obtain ⟨a, ha⟩ := hf w'
    obtain ⟨b, hb⟩ := hf w
    refine Finset.card_bij' (fun x _ => x + (b - a)) (fun x _ => x - (b - a)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [map_add (f := _), map_sub, hx, ha, hb]
      abel
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [map_sub, map_sub, hx, ha, hb]
      abel
    · intro x _
      abel
    · intro x _
      abel
  calc (Finset.univ.filter (fun v => f v = w)).card * Fintype.card W
      = ∑ w' : W, (Finset.univ.filter (fun v => f v = w')).card := by
        rw [Finset.sum_congr rfl (fun w' _ => hall w'), Finset.sum_const, Finset.card_univ,
          smul_eq_mul, mul_comm]
    _ = Finset.univ.card := (Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)).symm
    _ = Fintype.card V := Finset.card_univ

variable {K X : Type*} [Field K] [Fintype K] [DecidableEq K] [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [Fintype (Module.Dual K X)]

theorem exists_dual_one {Y : Type*} [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y] (y : Y) (hy : y ≠ 0) :
    ∃ g : Module.Dual K Y, g y = 1 := by
  have h1 : ∃ g : Module.Dual K Y, g y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy ((Module.forall_dual_apply_eq_zero_iff K y).1 h)
  obtain ⟨g, hg⟩ := h1
  exact ⟨(g y)⁻¹ • g, by simp [hg]⟩

theorem card_dual : Fintype.card (Module.Dual K X) = Fintype.card K ^ Module.finrank K X := by
  rw [Module.card_eq_pow_finrank (K := K), Subspace.dual_finrank_eq]

theorem card_dual_one (x : X) (hx : x ≠ 0) :
    (Finset.univ.filter (fun g : Module.Dual K X => g x = 1)).card = Fintype.card K ^ (Module.finrank K X - 1) := by
  obtain ⟨g1, hg1⟩ := exists_dual_one (K := K) x hx
  let f : Module.Dual K X →+ K :=
    { toFun := fun g => g x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hsurj : Function.Surjective f := fun c => ⟨c • g1, by simp [f, hg1]⟩
  have h : (Finset.univ.filter (fun g : Module.Dual K X => g x = 1)).card * Fintype.card K ^ 1 =
      Fintype.card K ^ Module.finrank K X := by
    rw [pow_one, ← card_dual]
    exact card_fib_mul f hsurj 1
  have hc : 1 ≤ (Finset.univ.filter (fun g : Module.Dual K X => g x = 1)).card :=
    Finset.card_pos.2 ⟨g1, by simp [hg1]⟩
  exact eq_pow_sub_of_mul_pow_eq_pow Fintype.one_lt_card hc h

theorem card_dual_two (te x : X) (hte : te ≠ 0) (hx : x ∉ Submodule.span K {te}) :
    (Finset.univ.filter (fun g : Module.Dual K X => g te = 1 ∧ g x = 1)).card =
      Fintype.card K ^ (Module.finrank K X - 2) := by
  have hte' : te ∉ Submodule.span K {x} := by
    intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hte (by rw [← hc, zero_smul])
    apply hx
    rw [← hc]
    exact Submodule.mem_span_singleton.2 ⟨c⁻¹, by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩
  have hq1 : Submodule.Quotient.mk (p := Submodule.span K {te}) x ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have hq2 : Submodule.Quotient.mk (p := Submodule.span K {x}) te ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  obtain ⟨h2, hh2⟩ := exists_dual_one (K := K) _ hq1
  obtain ⟨h1, hh1⟩ := exists_dual_one (K := K) _ hq2
  let g2 : Module.Dual K X := h2.comp (Submodule.span K {te}).mkQ
  let g1 : Module.Dual K X := h1.comp (Submodule.span K {x}).mkQ
  have g2te : g2 te = 0 := by
    simp only [g2, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self te), map_zero]
  have g2x : g2 x = 1 := hh2
  have g1x : g1 x = 0 := by
    simp only [g1, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self x), map_zero]
  have g1te : g1 te = 1 := hh1
  let f : Module.Dual K X →+ K × K :=
    { toFun := fun g => (g te, g x), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hsurj : Function.Surjective f := by
    rintro ⟨a, b⟩
    refine ⟨a • g1 + b • g2, ?_⟩
    simp [f, g1te, g1x, g2te, g2x]
  have h : (Finset.univ.filter (fun g : Module.Dual K X => g te = 1 ∧ g x = 1)).card *
      Fintype.card K ^ 2 = Fintype.card K ^ Module.finrank K X := by
    rw [← card_dual, sq, ← Fintype.card_prod]
    have h3 := card_fib_mul f hsurj (1, 1)
    have h4 : (Finset.univ.filter (fun g : Module.Dual K X => f g = (1, 1))) =
        Finset.univ.filter (fun g : Module.Dual K X => g te = 1 ∧ g x = 1) := by
      ext g
      simp [f, Prod.ext_iff]
    rw [h4] at h3
    exact h3
  have hc : 1 ≤ (Finset.univ.filter (fun g : Module.Dual K X => g te = 1 ∧ g x = 1)).card :=
    Finset.card_pos.2 ⟨g1 + g2, by simp [g1te, g1x, g2te, g2x]⟩
  exact eq_pow_sub_of_mul_pow_eq_pow Fintype.one_lt_card hc h

theorem card_dual_line (te x : X) (hx : x ∈ Submodule.span K {te}) (hne : x ≠ te) :
    (Finset.univ.filter (fun g : Module.Dual K X => g te = 1 ∧ g x = 1)).card = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro g - ⟨h1, h2⟩
  apply hne
  rw [map_smul, h1, smul_eq_mul, mul_one] at h2
  rw [h2, one_smul]

theorem card_sig_fib {A : Type*} {B : A → Type*} [Fintype A] [∀ a, Fintype (B a)] {Y : Type*} [DecidableEq Y]
    (ι : ∀ a, B a → Y) (P : A → Y → Prop) [∀ a y, Decidable (P a y)] (hι : ∀ a b, P a (ι a b)) (hu : ∀ a y, P a y → ∃! b, ι a b = y) (y : Y) :
    (Finset.univ.filter (fun p : (Σ a, B a) => ι p.1 p.2 = y)).card = (Finset.univ.filter (fun a => P a y)).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [← hp]
    exact hι a b
  · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' h
    simp only at h
    subst h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    have hP : P a y := by rw [← hp]; exact hι a b
    have hbb := (hu a y hP).unique hp hp'
    rw [hbb]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨b, hb, -⟩ := hu a y ha
    exact ⟨⟨a, b⟩, by simp [hb], rfl⟩

theorem card_filter_subtype {α : Type*} [Fintype α] (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    [Fintype {a // p a}] :
    (Finset.univ.filter (fun a : {a // p a} => q a.1)).card = (Finset.univ.filter (fun a => p a ∧ q a)).card := by
  refine Finset.card_bij (fun a _ => a.1) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ⟨a.2, ha⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact ⟨⟨b, hb.1⟩, by simp [hb.2], rfl⟩

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.SumFib
section
open scoped Classical

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

theorem sum_fib {X P : Type*} [Fintype X] [DecidableEq X] [Fintype P] (π : P → X) (V : P → ℂ) (w : X → ℂ)
    (hV : ∀ p, V p = w (π p)) :
    ∑ p, V p = ∑ x, ((Finset.univ.filter (fun p => π p = x)).card : ℂ) * w x := by
  have key : ∀ x, ∑ p ∈ Finset.univ.filter (fun p => π p = x), w (π p) =
      ((Finset.univ.filter (fun p => π p = x)).card : ℂ) * w x := by
    intro x
    rw [Finset.sum_congr rfl (g := fun _ => w x) (fun p hp => by rw [(Finset.mem_filter.1 hp).2]),
      Finset.sum_const, nsmul_eq_mul]
  simp_rw [hV]
  rw [← Finset.sum_fiberwise Finset.univ π (fun p => w (π p))]
  exact Finset.sum_congr rfl (fun x _ => key x)

theorem comb_du {K X PD PE : Type*} [Field K] [Fintype K] [DecidableEq K] [AddCommGroup X] [Module K X] [Fintype X]
    [DecidableEq X] {iPD : Fintype PD} {iPE : Fintype PE} (te : X) (hte0 : te ≠ 0) (Tn n1 n2 : ℕ) (hTn : Tn ≠ 0)
    (πD : PD → X) (πE : PE → X) (VD : PD → ℂ) (VE : PE → ℂ) (Φ : ℂ) (Dl : Kˣ → ℂ) (τ : Kˣ ≃ Kˣ)
    (hcE : ∀ x, (Finset.univ.filter (fun q => πE q = x)).card = if x = 0 then 0 else Tn ^ n1)
    (hcD : ∀ x, (Finset.univ.filter (fun p => πD p = x)).card =
      if x = te then Tn ^ n1 else if x ∈ Submodule.span K {te} then 0 else Tn ^ n2)
    (hself : ∀ p, πD p = te → VD p = Φ)
    (hDE : ∀ p q, πD p = πE q → VD p = VE q)
    (hEE : ∀ p q, πE p = πE q → VE p = VE q)
    (hline : ∀ (a : Kˣ) q, πE q = (a : K) • te → VE q = Dl (τ a)) :
    ∑ p, VD p = (Tn : ℂ) ^ n1 * Φ - (Tn : ℂ) ^ n2 * ∑ a, Dl a + (Tn : ℂ) ^ n2 * (((Tn : ℂ) ^ n1)⁻¹ * ∑ p, VE p) := by
  have hTn' : (0 : ℕ) < Tn ^ n1 := pow_pos (Nat.pos_of_ne_zero hTn) _
  have hA : ((Tn : ℂ) ^ n1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hTn)
  have hfibE : ∀ x : X, x ≠ 0 → ∃ q, πE q = x := by
    intro x hx
    have hc : 0 < (Finset.univ.filter (fun q => πE q = x)).card := by rw [hcE x, if_neg hx]; exact hTn'
    obtain ⟨q, hq⟩ := Finset.card_pos.1 hc
    exact ⟨q, (Finset.mem_filter.1 hq).2⟩
  obtain ⟨wE, hwE⟩ : ∃ wE : X → ℂ, ∀ q, VE q = wE (πE q) :=
    ⟨fun x => if h : ∃ q, πE q = x then VE h.choose else 0, fun q => by
      have h : ∃ q', πE q' = πE q := ⟨q, rfl⟩
      simp only [dif_pos h]
      exact hEE _ _ h.choose_spec.symm⟩
  have hVD : ∀ p, VD p = (if πD p = te then Φ else wE (πD p)) := by
    intro p
    split_ifs with h
    · exact hself p h
    · have h0 : πD p ≠ 0 := by
        intro h0
        have hc := hcD 0
        rw [if_neg (Ne.symm hte0), if_pos (Submodule.zero_mem _)] at hc
        have hm : p ∈ Finset.univ.filter (fun p => πD p = 0) := Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩
        rw [Finset.card_eq_zero.1 hc] at hm
        simp at hm
      obtain ⟨q, hq⟩ := hfibE _ h0
      rw [hDE p q hq.symm, hwE q, hq]
  have hD0 : ∑ p, VD p = ∑ x, ((Finset.univ.filter (fun p => πD p = x)).card : ℂ) *
      (if x = te then Φ else wE x) := sum_fib πD VD _ hVD
  have hE0 : ∑ q, VE q = ∑ x, ((Finset.univ.filter (fun q => πE q = x)).card : ℂ) * wE x :=
    sum_fib πE VE wE hwE
  have e1 : ∀ x : X, ((Finset.univ.filter (fun p => πD p = x)).card : ℂ) * (if x = te then Φ else wE x) =
      (if x = te then (Tn : ℂ) ^ n1 * Φ else 0) +
        (Tn : ℂ) ^ n2 * (if x ∈ Submodule.span K {te} then 0 else wE x) := by
    intro x
    rw [hcD x]
    by_cases h1 : x = te
    · subst h1; simp [Submodule.mem_span_singleton_self]
    · by_cases h2 : x ∈ Submodule.span K {te} <;> simp [h1, h2]
  have e2 : ∀ x : X, ((Finset.univ.filter (fun q => πE q = x)).card : ℂ) * wE x =
      (Tn : ℂ) ^ n1 * ((if x ∈ Submodule.span K {te} then 0 else wE x) +
        (if x ∈ Submodule.span K {te} ∧ x ≠ 0 then wE x else 0)) := by
    intro x
    rw [hcE x]
    by_cases h1 : x = 0
    · subst h1; simp
    · by_cases h2 : x ∈ Submodule.span K {te} <;> simp [h1, h2]
  have hD1 : ∑ x, ((Finset.univ.filter (fun p => πD p = x)).card : ℂ) * (if x = te then Φ else wE x) =
      (Tn : ℂ) ^ n1 * Φ + (Tn : ℂ) ^ n2 * ∑ x : X, (if x ∈ Submodule.span K {te} then 0 else wE x) := by
    rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hE1 : ∑ x, ((Finset.univ.filter (fun q => πE q = x)).card : ℂ) * wE x =
      (Tn : ℂ) ^ n1 * (∑ x : X, (if x ∈ Submodule.span K {te} then 0 else wE x) +
        ∑ x : X, (if x ∈ Submodule.span K {te} ∧ x ≠ 0 then wE x else 0)) := by
    rw [Finset.sum_congr rfl (fun x _ => e2 x), ← Finset.mul_sum, Finset.sum_add_distrib]
  have hS2 : ∑ x : X, (if x ∈ Submodule.span K {te} ∧ x ≠ 0 then wE x else 0) = ∑ a, Dl a := by
    rw [← Finset.sum_filter, ← Equiv.sum_comp τ Dl]
    symm
    refine Finset.sum_bij (fun a _ => (a : K) • te) ?_ ?_ ?_ ?_
    · intro a _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self te), smul_ne_zero a.ne_zero hte0⟩
    · intro a _ b _ h
      exact Units.ext (smul_left_injective K hte0 h)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx.1
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hx.2 (by rw [← hc, zero_smul])
      exact ⟨Units.mk0 c hc0, Finset.mem_univ _, by simp [hc]⟩
    · intro a _
      obtain ⟨q, hq⟩ := hfibE _ (smul_ne_zero a.ne_zero hte0)
      rw [← hq, ← hwE q, hline a q hq]
  rw [hD0, hD1, hE0, hE1, hS2, inv_mul_cancel_left₀ hA]
  ring

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
end

