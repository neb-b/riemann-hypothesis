module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0038
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CayleyHamilton
section
open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.PsChar

open Polynomial

private theorem pseudo_character_sum_cons_expand {M A : Type*} [Monoid M] [CommRing A] (T : M → A) (n : ℕ) (a : M)
    (r : Fin n → M) :
    _root_.GlobalTheory.PsChar.alt T (n + 1) (Fin.cons a r) =
      T a * _root_.GlobalTheory.PsChar.alt T n r -
        ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (a * r i)) := rfl

private theorem pseudo_character_sum_cons_comp_perm {M A : Type*} [Monoid M] [CommRing A] (T : M → A) (n : ℕ)
    (ih : ∀ (w : Fin n → M) (τ : Equiv.Perm (Fin n)),
      _root_.GlobalTheory.PsChar.alt T n (w ∘ τ) = _root_.GlobalTheory.PsChar.alt T n w)
    (a : M) (w : Fin n → M) (τ : Equiv.Perm (Fin n)) :
    _root_.GlobalTheory.PsChar.alt T (n + 1) (Fin.cons a (w ∘ τ)) =
      _root_.GlobalTheory.PsChar.alt T (n + 1) (Fin.cons a w) := by
  rw [pseudo_character_sum_cons_expand, pseudo_character_sum_cons_expand, ih]
  congr 1
  have : ∀ i, Function.update (w ∘ τ) i (a * (w ∘ τ) i) =
      Function.update w (τ i) (a * w (τ i)) ∘ τ := fun i => by
    rw [Function.update_comp_equiv, Equiv.symm_apply_apply]; rfl
  simp only [this, ih]
  exact Equiv.sum_comp τ (fun j => _root_.GlobalTheory.PsChar.alt T n (Function.update w j (a * w j)))

private theorem alt_cons_cons_lemma_5 {M A : Type*} [Monoid M] [CommRing A] (T : M → A) (n : ℕ)
    (a b : M) (r : Fin n → M) :
    _root_.GlobalTheory.PsChar.alt T (n + 2) (Fin.cons a (Fin.cons b r)) =
      T a * T b * _root_.GlobalTheory.PsChar.alt T n r
      - T a * ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * r i))
      - T b * ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (a * r i))
      - T (a * b) * _root_.GlobalTheory.PsChar.alt T n r
      + ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (a * b * r i))
      + ∑ i, _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i))
      + ∑ i, ∑ l, if l = i then 0 else _root_.GlobalTheory.PsChar.alt T n
          (Function.update (Function.update r i (a * r i)) l (b * r l)) := by
  rw [pseudo_character_sum_cons_expand, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, Fin.cons_update, pseudo_character_sum_cons_expand]
  have hin : ∀ i : Fin n, ∑ l, _root_.GlobalTheory.PsChar.alt T n
      (Function.update (Function.update r i (a * r i)) l
        (b * Function.update r i (a * r i) l)) =
      _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i)) +
      ∑ l, if l = i then 0 else _root_.GlobalTheory.PsChar.alt T n
          (Function.update (Function.update r i (a * r i)) l (b * r l)) := by
    intro i
    have hX : (∑ l : Fin n, if l = i then
        _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i)) else 0) =
        _root_.GlobalTheory.PsChar.alt T n (Function.update r i (b * a * r i)) := by simp
    rw [← hX, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = i
    · subst hl; simp [mul_assoc]
    · rw [if_neg hl, if_neg hl, zero_add, Function.update_of_ne hl]
  simp only [← Fin.cons_update, pseudo_character_sum_cons_expand, Finset.sum_sub_distrib, Function.update_self]
  simp only [hin, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private theorem pseudo_character_sum_swap_head_pair {M A : Type*} [Monoid M] [CommRing A] (T : M → A)
    (hc : ∀ a b, T (a * b) = T (b * a)) (n : ℕ) (a b : M) (r : Fin n → M) :
    _root_.GlobalTheory.PsChar.alt T (n + 2) (Fin.cons a (Fin.cons b r)) =
      _root_.GlobalTheory.PsChar.alt T (n + 2) (Fin.cons b (Fin.cons a r)) := by
  rw [alt_cons_cons_lemma_5, alt_cons_cons_lemma_5, hc a b]
  have hoff : (∑ i, ∑ l, if l = i then (0 : A) else _root_.GlobalTheory.PsChar.alt T n
          (Function.update (Function.update r i (a * r i)) l (b * r l))) =
      ∑ i, ∑ l, if l = i then (0 : A) else _root_.GlobalTheory.PsChar.alt T n
          (Function.update (Function.update r i (b * r i)) l (a * r l)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = i
    · simp [hl]
    · rw [if_neg (Ne.symm hl), if_neg hl, Function.update_comm (Ne.symm hl)]
  rw [hoff]
  ring

private theorem pseudo_character_sum_comp_perm {M A : Type*} [Monoid M] [CommRing A] (T : M → A)
    (hc : ∀ a b, T (a * b) = T (b * a)) :
    ∀ (n : ℕ) (v : Fin n → M) (σ : Equiv.Perm (Fin n)),
      _root_.GlobalTheory.PsChar.alt T n (v ∘ σ) = _root_.GlobalTheory.PsChar.alt T n v := by
  intro n
  induction n with
  | zero => intro v σ; rfl
  | succ n ih =>
    have htail : ∀ (v : Fin (n + 1) → M) (i j : Fin n),
        _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ Equiv.swap i.succ j.succ) =
          _root_.GlobalTheory.PsChar.alt T (n + 1) v := by
      intro v i j
      have hv : v ∘ Equiv.swap i.succ j.succ = Fin.cons (v 0) (Fin.tail v ∘ Equiv.swap i j) := by
        funext k
        induction k using Fin.cases with
        | zero =>
          simp [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm
            (Fin.succ_ne_zero j).symm]
        | succ k =>
          simp only [Function.comp_apply, Fin.cons_succ, Fin.tail]
          rw [(Fin.succ_injective n).swap_apply]
      rw [hv, pseudo_character_sum_cons_comp_perm T n ih, Fin.cons_self_tail]
    have h0 : ∀ (v : Fin (n + 1) → M) (j : Fin n),
        _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ Equiv.swap 0 j.succ) =
          _root_.GlobalTheory.PsChar.alt T (n + 1) v := by
      intro v j
      cases n with
      | zero => exact j.elim0
      | succ m =>
        have h01 : ∀ v : Fin (m + 2) → M,
            _root_.GlobalTheory.PsChar.alt T (m + 2) (v ∘ Equiv.swap 0 (Fin.succ 0)) =
              _root_.GlobalTheory.PsChar.alt T (m + 2) v := by
          intro v
          obtain ⟨a, b, r, rfl⟩ : ∃ a b r, v = Fin.cons a (Fin.cons b r) :=
            ⟨_, _, _, (Fin.cons_self_tail v).symm.trans (congrArg _ (Fin.cons_self_tail _).symm)⟩
          have hv : (Fin.cons a (Fin.cons b r) : Fin (m + 2) → M) ∘ Equiv.swap 0 (Fin.succ 0) =
              Fin.cons b (Fin.cons a r) := by
            funext k
            refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
            · simp
            · simp
            · simp only [Function.comp_apply]
              rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
                (fun h => Fin.succ_ne_zero k (Fin.succ_injective _ h))]
              simp
          rw [hv, pseudo_character_sum_swap_head_pair T hc]
        induction j using Fin.cases with
        | zero => exact h01 v
        | succ k =>
          have hp : Equiv.swap (0 : Fin (m + 2)) k.succ.succ =
              Equiv.swap (Fin.succ 0) k.succ.succ * Equiv.swap 0 (Fin.succ 0) *
                Equiv.swap (Fin.succ 0) k.succ.succ := by
            have h1 : Equiv.swap (Fin.succ 0) k.succ.succ (0 : Fin (m + 2)) = 0 :=
              Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero 0).symm (Fin.succ_ne_zero _).symm
            have h2 : Equiv.swap (Fin.succ 0) k.succ.succ (Fin.succ 0 : Fin (m + 2)) = k.succ.succ :=
              Equiv.swap_apply_left _ _
            have := Equiv.swap_apply_apply (Equiv.swap (Fin.succ 0) k.succ.succ) 0 (Fin.succ 0)
            rw [h1, h2, Equiv.swap_inv] at this
            exact this
          rw [hp, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, ← Function.comp_assoc,
            ← Function.comp_assoc, htail, h01, htail]
    have hswap : ∀ (v : Fin (n + 1) → M) (x y : Fin (n + 1)),
        _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ Equiv.swap x y) =
          _root_.GlobalTheory.PsChar.alt T (n + 1) v := by
      intro v x y
      induction x using Fin.cases with
      | zero =>
        induction y using Fin.cases with
        | zero => simp
        | succ j => exact h0 v j
      | succ i =>
        induction y using Fin.cases with
        | zero => rw [Equiv.swap_comm]; exact h0 v i
        | succ j => exact htail v i j
    intro v σ
    revert v
    refine Equiv.Perm.swap_induction_on (motive := fun σ => ∀ v : Fin (n + 1) → M,
      _root_.GlobalTheory.PsChar.alt T (n + 1) (v ∘ σ) = _root_.GlobalTheory.PsChar.alt T (n + 1) v)
      σ (fun v => rfl) ?_
    intro f x y _ hf v
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hf, hswap]


open Polynomial in
theorem _root_.GlobalTheory.PsChar.cayleyHamilton (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R]
    (d : ℕ) (T : R →ₗ[k] k) (h : _root_.GlobalTheory.PsChar.IsPsChar d (fun x => T x)) (x : R) :
    ∃ p : Polynomial k, p.Monic ∧ p.natDegree = d ∧ ∀ y : R, T (Polynomial.aeval x p * y) = 0 := by
  have hc : ∀ a b : R, T (a * b) = T (b * a) := h.comm
  have hupd : ∀ (m : ℕ) (i : Fin (m + 1)) (w : R),
      _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (Function.update (fun _ => x) i w) =
        _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (Fin.cons w fun _ => x) := by
    intro m i w
    rw [← pseudo_character_sum_comp_perm _ hc (m + 1) _ (Equiv.swap 0 i)]
    congr 1
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [Function.comp_apply, Equiv.swap_apply_left, Function.update_self, Fin.cons_zero]
    · rw [Function.comp_apply, Fin.cons_succ, Function.update_of_ne]
      intro hj
      exact Fin.succ_ne_zero _
        ((Equiv.swap 0 i).injective (hj.trans (Equiv.swap_apply_left 0 i).symm))
  have hrec : ∀ (m : ℕ) (y : R),
      _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 2) (Fin.cons y fun _ => x) =
        T y * _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (fun _ => x) -
          (m + 1) * _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1)
            (Fin.cons (y * x) fun _ => x) := by
    intro m y
    rw [pseudo_character_sum_cons_expand]
    simp only [hupd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hcoef : ∀ m : ℕ, ∃ c : ℕ → k,
      (∀ y, _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1) (Fin.cons y fun _ => x) =
        ∑ j ∈ Finset.range (m + 1), c j * T (y * x ^ j)) ∧
      c m = (-1) ^ m * (m.factorial : k) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun _ => 1, fun y => ?_, by simp⟩
      rw [pseudo_character_sum_cons_expand]
      simp
      exact mul_one (T y)
    | succ m ih =>
      obtain ⟨c, hc1, hc2⟩ := ih
      refine ⟨fun j => if j = 0 then _root_.GlobalTheory.PsChar.alt (fun r : R => T r) (m + 1)
        (fun _ => x) else -((m : k) + 1) * c (j - 1), fun y => ?_, ?_⟩
      · rw [hrec, hc1, Finset.sum_range_succ' _ (m + 1)]
        simp only [Nat.add_one_ne_zero, if_false, if_true, Nat.add_sub_cancel, pow_zero, mul_one,
          pow_succ', ← mul_assoc, Finset.mul_sum]
        rw [sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
        congr 1
        · exact Finset.sum_congr rfl fun j _ => by ring
        · ring
      · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, hc2, Nat.factorial_succ]
        push_cast
        ring
  obtain ⟨c, hc1, hc2⟩ := hcoef d
  have hzero : ∀ y, ∑ j ∈ Finset.range (d + 1), c j * T (y * x ^ j) = 0 := fun y =>
    (hc1 y).symm.trans (h.alt_eq_zero _)
  have hcd : c d ≠ 0 := by
    rw [hc2]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero d)
  have hdeg : (∑ i : Fin d, C (c i / c d) * X ^ (i : ℕ)).degree < (d : WithBot ℕ) :=
    Polynomial.degree_sum_fin_lt _
  refine ⟨X ^ d + ∑ i : Fin d, C (c i / c d) * X ^ (i : ℕ), Polynomial.monic_X_pow_add hdeg, ?_,
    fun y => ?_⟩
  · rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.natDegree_X_pow]
  · have e := hzero y
    rw [Finset.sum_range_succ] at e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C,
      add_mul, Finset.sum_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      map_smul, smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i => c i / c d * T (x ^ i * y)) d, hc]
    have hs : ∑ i ∈ Finset.range d, c i / c d * T (x ^ i * y) =
        (∑ i ∈ Finset.range d, c i * T (y * x ^ i)) / c d := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [hc]; ring
    rw [hs]
    field_simp
    linear_combination e

end GlobalTheory.PsChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceLengthFinsetSupEqSum
section
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

namespace GlobalTheory.CongruenceLengthSum

variable {O V : Type} [CommRing O] [AddCommGroup V] [Module O V]

private theorem sep_lemma' {P₁ P₂ : Submodule O V} (hd : Disjoint P₁ P₂) {x₁ y₁ x₂ y₂ : V}
    (h₁ : x₁ ∈ P₁) (h₁' : y₁ ∈ P₁) (h₂ : x₂ ∈ P₂) (h₂' : y₂ ∈ P₂) (h : x₁ + x₂ = y₁ + y₂) :
    x₁ = y₁ ∧ x₂ = y₂ := by
  have e : x₁ - y₁ = y₂ - x₂ := by
    rw [sub_eq_sub_iff_add_eq_add, h, add_comm y₁ y₂]
  have hz : x₁ - y₁ = 0 :=
    Submodule.disjoint_def.mp hd _ (sub_mem h₁ h₁') (e ▸ sub_mem h₂' h₂)
  have e1 : x₁ = y₁ := sub_eq_zero.mp hz
  refine ⟨e1, ?_⟩
  rw [e1] at h
  exact add_left_cancel h

theorem length_quot_sup (T₁ T₂ S₁ S₂ : Submodule O V) (h₁ : S₁ ≤ T₁) (h₂ : S₂ ≤ T₂)
    (hd : Disjoint T₁ T₂) :
    Module.length O (↥(T₁ ⊔ T₂) ⧸ (S₁ ⊔ S₂).comap (T₁ ⊔ T₂).subtype) =
      Module.length O (↥T₁ ⧸ S₁.comap T₁.subtype) + Module.length O (↥T₂ ⧸ S₂.comap T₂.subtype) := by
  have key : ∀ a ∈ T₁, ∀ b ∈ T₂, a + b ∈ S₁ ⊔ S₂ ↔ a ∈ S₁ ∧ b ∈ S₂ := by
    intro a ha b hb
    constructor
    · intro h
      obtain ⟨s₁, hs₁, s₂, hs₂, hs⟩ := Submodule.mem_sup.mp h
      obtain ⟨e1, e2⟩ := sep_lemma' hd ha (h₁ hs₁) hb (h₂ hs₂) hs.symm
      rw [e1, e2]
      exact ⟨hs₁, hs₂⟩
    · rintro ⟨h1, h2⟩
      exact add_mem (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
  let f : (↥T₁ × ↥T₂) →ₗ[O] ↥(T₁ ⊔ T₂) :=
    LinearMap.codRestrict (T₁ ⊔ T₂) (T₁.subtype.coprod T₂.subtype)
      (fun p => add_mem (Submodule.mem_sup_left p.1.2) (Submodule.mem_sup_right p.2.2))
  let Φ := ((S₁ ⊔ S₂).comap (T₁ ⊔ T₂).subtype).mkQ ∘ₗ f
  let Ψ : (↥T₁ × ↥T₂) →ₗ[O] (↥T₁ ⧸ S₁.comap T₁.subtype) × (↥T₂ ⧸ S₂.comap T₂.subtype) :=
    LinearMap.prodMap (S₁.comap T₁.subtype).mkQ (S₂.comap T₂.subtype).mkQ
  have hΦ : Function.Surjective Φ := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hΨ : Function.Surjective Ψ := by
    rintro ⟨y₁, y₂⟩
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y₁
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y₂
    exact ⟨(a, b), rfl⟩
  have hker : LinearMap.ker Φ = LinearMap.ker Ψ := by
    ext ⟨a, b⟩
    simp only [LinearMap.mem_ker, Φ, Ψ, f, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.prodMap_apply, Prod.mk_eq_zero]
    exact key a a.2 b b.2
  calc Module.length O (↥(T₁ ⊔ T₂) ⧸ (S₁ ⊔ S₂).comap (T₁ ⊔ T₂).subtype)
      = Module.length O ((↥T₁ × ↥T₂) ⧸ LinearMap.ker Φ) :=
        (Φ.quotKerEquivOfSurjective hΦ).length_eq.symm
    _ = Module.length O ((↥T₁ × ↥T₂) ⧸ LinearMap.ker Ψ) := (Submodule.quotEquivOfEq _ _ hker).length_eq
    _ = Module.length O ((↥T₁ ⧸ S₁.comap T₁.subtype) × (↥T₂ ⧸ S₂.comap T₂.subtype)) :=
        (Ψ.quotKerEquivOfSurjective hΨ).length_eq
    _ = _ := Module.length_prod _ _ _

theorem sup_inf_split (G₁ B₁ L₁ G₂ B₂ L₂ : Submodule O V) (hd : Disjoint (G₁ ⊔ B₁) (G₂ ⊔ B₂))
    (hL₁ : L₁ ≤ G₁ ⊔ B₁) (hL₂ : L₂ ≤ G₂ ⊔ B₂) :
    (G₁ ⊔ G₂) ⊓ ((L₁ ⊔ L₂) ⊔ (B₁ ⊔ B₂)) = G₁ ⊓ (L₁ ⊔ B₁) ⊔ G₂ ⊓ (L₂ ⊔ B₂) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := Submodule.mem_sup.mp hx1
    obtain ⟨y, hy, c, hc, hyc⟩ := Submodule.mem_sup.mp hx2
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp hc
    have e : g₁ + g₂ = (l₁ + b₁) + (l₂ + b₂) := by rw [← hyc]; abel
    obtain ⟨e1, e2⟩ := sep_lemma' hd (Submodule.mem_sup_left hg₁)
      (add_mem (hL₁ hl₁) (Submodule.mem_sup_right hb₁)) (Submodule.mem_sup_left hg₂)
      (add_mem (hL₂ hl₂) (Submodule.mem_sup_right hb₂)) e
    refine add_mem (Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hg₁, ?_⟩))
      (Submodule.mem_sup_right (Submodule.mem_inf.mpr ⟨hg₂, ?_⟩))
    · rw [e1]
      exact add_mem (Submodule.mem_sup_left hl₁) (Submodule.mem_sup_right hb₁)
    · rw [e2]
      exact add_mem (Submodule.mem_sup_left hl₂) (Submodule.mem_sup_right hb₂)
  · refine sup_le (le_inf (inf_le_left.trans le_sup_left) (inf_le_right.trans ?_))
      (le_inf (inf_le_left.trans le_sup_right) (inf_le_right.trans ?_))
    · exact sup_le_sup le_sup_left le_sup_left
    · exact sup_le_sup le_sup_right le_sup_right

theorem inf_split (G₁ B₁ L₁ G₂ B₂ L₂ : Submodule O V) (hd : Disjoint (G₁ ⊔ B₁) (G₂ ⊔ B₂))
    (hL₁ : L₁ ≤ G₁ ⊔ B₁) (hL₂ : L₂ ≤ G₂ ⊔ B₂) :
    (L₁ ⊔ L₂) ⊓ (G₁ ⊔ G₂) = L₁ ⊓ G₁ ⊔ L₂ ⊓ G₂ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := Submodule.mem_sup.mp hx1
    obtain ⟨g₁, hg₁, g₂, hg₂, hg⟩ := Submodule.mem_sup.mp hx2
    obtain ⟨e1, e2⟩ := sep_lemma' hd (hL₁ hl₁) (Submodule.mem_sup_left hg₁) (hL₂ hl₂)
      (Submodule.mem_sup_left hg₂) hg.symm
    refine add_mem (Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hl₁, ?_⟩))
      (Submodule.mem_sup_right (Submodule.mem_inf.mpr ⟨hl₂, ?_⟩))
    · rw [e1]
      exact hg₁
    · rw [e2]
      exact hg₂
  · exact sup_le (inf_le_inf le_sup_left le_sup_left) (inf_le_inf le_sup_right le_sup_right)

end GlobalTheory.CongruenceLengthSum


open GlobalTheory.CongruenceLengthSum in
theorem GlobalTheory.congruence_length_finset_sup : ∀ (O V ι : Type) [CommRing O] [AddCommGroup V] [Module O V] (F : Finset ι) (L G B : ι → Submodule O V), F.SupIndep (fun i => G i ⊔ B i) → (∀ i ∈ F, Disjoint (G i) (B i)) → (∀ i ∈ F, L i ≤ G i ⊔ B i) → Module.length O (↥(F.sup G ⊓ (F.sup L ⊔ F.sup B)) ⧸ (F.sup L ⊓ F.sup G).comap (F.sup G ⊓ (F.sup L ⊔ F.sup B)).subtype) = ∑ i ∈ F, Module.length O (↥(G i ⊓ (L i ⊔ B i)) ⧸ (L i ⊓ G i).comap (G i ⊓ (L i ⊔ B i)).subtype) := by
  classical
  intro O V ι _ _ _ F L G B
  induction F using Finset.induction_on with
  | empty =>
    intro _ _ _
    rw [Finset.sum_empty, Module.length_eq_zero_iff]
    have : Subsingleton ↥((∅ : Finset ι).sup G ⊓ ((∅ : Finset ι).sup L ⊔ (∅ : Finset ι).sup B)) :=
      ⟨fun a b => Subtype.ext (by
        have ha := a.2
        have hb := b.2
        simp only [Finset.sup_empty, bot_sup_eq, inf_bot_eq, Submodule.mem_bot] at ha hb
        rw [ha, hb])⟩
    exact (Submodule.mkQ_surjective _).subsingleton
  | insert j F hj ih =>
    intro hSI hdis hL
    have hdj : Disjoint (G j ⊔ B j) (F.sup (fun i => G i ⊔ B i)) :=
      hSI (Finset.subset_insert j F) (Finset.mem_insert_self j F) hj
    replace hSI : F.SupIndep (fun i => G i ⊔ B i) := fun t ht i hi hit =>
      hSI (ht.trans (Finset.subset_insert j F)) (Finset.mem_insert_of_mem hi) hit
    have hGB : F.sup (fun i => G i ⊔ B i) = F.sup G ⊔ F.sup B := Finset.sup_sup (s := F) (f := G) (g := B)
    rw [hGB] at hdj
    have hLF : F.sup L ≤ F.sup G ⊔ F.sup B := Finset.sup_le fun i hi =>
      (hL i (Finset.mem_insert_of_mem hi)).trans (sup_le_sup (Finset.le_sup hi) (Finset.le_sup hi))
    have hLj : L j ≤ G j ⊔ B j := hL j (Finset.mem_insert_self j F)
    rw [Finset.sum_insert hj, Finset.sup_insert, Finset.sup_insert, Finset.sup_insert]
    rw [sup_inf_split _ _ _ _ _ _ hdj hLj hLF, inf_split _ _ _ _ _ _ hdj hLj hLF]
    have hS₁ : L j ⊓ G j ≤ G j ⊓ (L j ⊔ B j) := le_inf inf_le_right (inf_le_left.trans le_sup_left)
    have hS₂ : F.sup L ⊓ F.sup G ≤ F.sup G ⊓ (F.sup L ⊔ F.sup B) :=
      le_inf inf_le_right (inf_le_left.trans le_sup_left)
    have hT : Disjoint (G j ⊓ (L j ⊔ B j)) (F.sup G ⊓ (F.sup L ⊔ F.sup B)) :=
      hdj.mono (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_left)
    rw [length_quot_sup _ _ _ _ hS₁ hS₂ hT, ih hSI (fun i hi => hdis i (Finset.mem_insert_of_mem hi))
      (fun i hi => hL i (Finset.mem_insert_of_mem hi))]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfContinuousTrace
section
open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.SSCont

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

theorem mem_imAlg_iff (r : Γ →* GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) :
    x ∈ PI.SSAscent.UnitaryGroupMassFormula.imAlg r ↔
      x ∈ Submodule.span k (Set.range fun g => (r g : Matrix (Fin n) (Fin n) k)) := by
  have h : (Submonoid.closure (Set.range fun g => (r g : Matrix (Fin n) (Fin n) k)) :
      Set (Matrix (Fin n) (Fin n) k)) = Set.range fun g => (r g : Matrix (Fin n) (Fin n) k) := by
    have e : (Set.range fun g => (r g : Matrix (Fin n) (Fin n) k)) =
        (MonoidHom.mrange ((Units.coeHom _).comp r) : Set (Matrix (Fin n) (Fin n) k)) := by
      ext y
      simp
    rw [e, Submonoid.closure_eq]
  rw [PI.SSAscent.UnitaryGroupMassFormula.imAlg, ← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span, h]

theorem exists_linear_of_trace [CharZero k] (r : Γ →* GL (Fin n) k) (hr : IsSSRep r) :
    ∃ (m : ℕ) (c : Fin m → Γ) (ψ : (Fin m → k) →ₗ[k] Matrix (Fin n) (Fin n) k),
      ∀ g, (r g : Matrix (Fin n) (Fin n) k) =
        ψ fun i => ((r (g * c i) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace := by
  have hnd : PI.SSAscent.UnitaryGroupMassFormula.TrNondeg (PI.SSAscent.UnitaryGroupMassFormula.imAlg r) :=
    PI.SSAscent.UnitaryGroupMassFormula.downStep_of PI.SSAscent.UnitaryGroupMassFormula.trace_nilpotent_ascent k Γ n r hr
  set S : Set (Matrix (Fin n) (Fin n) k) := Set.range fun g => (r g : Matrix (Fin n) (Fin n) k) with hS
  obtain ⟨f, hf, hspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq k S
  choose c hc using hf
  let φ : Submodule.span k S →ₗ[k] (Fin (Module.finrank k (Submodule.span k S)) → k) :=
    LinearMap.pi fun i => (Matrix.traceLinearMap (Fin n) k k) ∘ₗ (LinearMap.mulRight k (f i)) ∘ₗ
      (Submodule.span k S).subtype
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    refine hnd x.1 ((mem_imAlg_iff r _).2 x.2) fun y hy => ?_
    have hy' := (mem_imAlg_iff r _).1 hy
    rw [← hS, ← hspan] at hy'
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      simpa [φ] using congrFun hx i
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, Matrix.trace_add, hy, hz, add_zero]
    | smul a y _ hy => rw [Matrix.mul_smul, Matrix.trace_smul, hy, smul_zero]
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective φ hφ
  refine ⟨_, c, (Submodule.span k S).subtype ∘ₗ ψ, fun g => ?_⟩
  let x : Submodule.span k S := ⟨r g, Submodule.subset_span ⟨g, rfl⟩⟩
  have h1 : (fun i => ((r (g * c i) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) = φ x := by
    funext i
    simp [φ, x, ← hc i]
  have h2 : ψ (φ x) = x := LinearMap.congr_fun hψ x
  rw [h1, LinearMap.comp_apply, h2]
  rfl

theorem continuous_of_continuous_trace : ∀ (Γ k : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k] (n : ℕ) (r : Γ →* GL (Fin n) k), IsSSRep r → Continuous (fun g => ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → Continuous r := by
  intro Γ k _ _ _ _ _ _ _ n r hr ht
  obtain ⟨m, c, ψ, h⟩ := exists_linear_of_trace r hr
  have hc : Continuous fun g => ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [funext h]
    exact ψ.continuous_on_pi.comp (continuous_pi fun i => ht.comp (continuous_mul_const (c i)))
  rw [Units.continuous_iff]
  refine ⟨hc, ?_⟩
  simp only [← map_inv]
  exact hc.comp continuous_inv

end GlobalTheory.SSCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesEqCOfSubstFixedNotRootOfUnityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeries_eq_C_of_subst_fixed_not_root_of_unity : ∀ (L : Type) [Field L] (y : PowerSeries L), PowerSeries.constantCoeff y = 0 → (∀ k : ℕ, 0 < k → (PowerSeries.coeff 1 y) ^ k ≠ 1) → ∀ a : PowerSeries L, (PowerSeries.subst y a : PowerSeries L) = a → a = PowerSeries.C (PowerSeries.constantCoeff a) := by
  first | exact @GlobalTheory.powerSeries_eq_C_of_subst_eq_self | exact GlobalTheory.powerSeries_eq_C_of_subst_eq_self | (intros; apply GlobalTheory.powerSeries_eq_C_of_subst_eq_self <;> assumption)
end

