module

public import Mathlib

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

def Supernatural : Type := Nat.Primes → ℕ∞

namespace Supernatural

def mk (f : Nat.Primes → ℕ∞) : Supernatural := f

def exp (a : Supernatural) (p : Nat.Primes) : ℕ∞ := a p

private theorem exp_ext {a b : Supernatural} (h : ∀ p, a.exp p = b.exp p) : a = b :=
  funext h

noncomputable instance : CompleteLattice Supernatural := inferInstanceAs (CompleteLattice (Nat.Primes → ℕ∞))

theorem le_def {a b : Supernatural} : a ≤ b ↔ ∀ p, a.exp p ≤ b.exp p := Iff.rfl

@[simp] theorem exp_iSup {ι : Sort*} (f : ι → Supernatural) (p : Nat.Primes) :
    (⨆ i, f i).exp p = ⨆ i, (f i).exp p :=
  iSup_apply (f := fun i => (f i : Nat.Primes → ℕ∞)) (a := p)

instance : One Supernatural := ⟨mk fun _ => 0⟩

instance : Mul Supernatural := ⟨fun a b => mk fun p => a.exp p + b.exp p⟩

@[simp] theorem exp_mul (a b : Supernatural) (p : Nat.Primes) :
    (a * b).exp p = a.exp p + b.exp p := rfl

instance : CommMonoid Supernatural where
  mul_assoc a b c := by exact exp_ext fun p => add_assoc (a.exp p) (b.exp p) (c.exp p)
  one_mul a := by exact exp_ext fun p => zero_add (a.exp p)
  mul_one a := by exact exp_ext fun p => add_zero (a.exp p)
  mul_comm a b := by exact exp_ext fun p => add_comm (a.exp p) (b.exp p)

theorem dvd_iff_le {a b : Supernatural} : a ∣ b ↔ a ≤ b := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [le_def]
    intro p
    simp
  · intro h
    refine ⟨mk fun p => b.exp p - a.exp p, ?_⟩
    exact exp_ext fun p => (add_tsub_cancel_of_le (le_def.mp h p)).symm

def ofNat (n : ℕ) : Supernatural := mk fun p => (n.factorization p : ℕ∞)

@[simp] theorem exp_ofNat (n : ℕ) (p : Nat.Primes) : (ofNat n).exp p = n.factorization p := rfl

theorem ofNat_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : ofNat (m * n) = ofNat m * ofNat n := by
  refine exp_ext fun p => ?_
  simp [Nat.factorization_mul hm hn]

theorem ofNat_dvd_ofNat {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : ofNat m ∣ ofNat n ↔ m ∣ n := by
  rw [dvd_iff_le, le_def, ← Nat.factorization_le_iff_dvd hm hn, Finsupp.le_def]
  constructor
  · intro h q
    by_cases hq : q.Prime
    · have h' : ((m.factorization q : ℕ) : ℕ∞) ≤ n.factorization q := h ⟨q, hq⟩
      exact_mod_cast h'
    · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  · intro h p
    show ((m.factorization p : ℕ) : ℕ∞) ≤ n.factorization p
    exact_mod_cast h p

theorem ofNat_prime_dvd_iff (p : Nat.Primes) (a : Supernatural) :
    ofNat p ∣ a ↔ 1 ≤ a.exp p := by
  have h1 : (ofNat p).exp p = 1 := by
    rw [exp_ofNat]
    simp [p.prop.factorization_self]
  rw [dvd_iff_le, le_def]
  constructor
  · intro h
    exact h1 ▸ h p
  · intro h q
    by_cases hq : q = p
    · subst hq
      exact h1 ▸ h
    · have hq' : (p : ℕ) ≠ q := fun e => hq (Subtype.ext e.symm)
      simp [p.prop.factorization, hq']

theorem ofNat_prime_dvd_iSup_iff (p : Nat.Primes) {ι : Sort*} (f : ι → Supernatural) :
    ofNat p ∣ ⨆ i, f i ↔ ∃ i, ofNat p ∣ f i := by
  simp only [ofNat_prime_dvd_iff p, Order.one_le_iff_ne_zero]
  rw [exp_iSup]
  constructor
  · intro h
    by_contra h'
    simp only [not_exists, ne_eq, not_not] at h'
    exact h (le_antisymm (iSup_le fun i => (h' i).le) zero_le)
  · rintro ⟨i, hi⟩ h
    exact hi (le_antisymm (h ▸ le_iSup (fun i => (f i).exp p) i) zero_le)

theorem iSup_mul_iSup {ι : Sort*} {f g : ι → Supernatural}
    (h : ∀ i j, ∃ k, f i ≤ f k ∧ g j ≤ g k) :
    (⨆ i, f i) * (⨆ i, g i) = ⨆ i, f i * g i := by
  refine exp_ext fun p => ?_
  simp only [exp_mul, exp_iSup]
  exact ENat.iSup_add_iSup fun i j => (h i j).imp fun k hk =>
    add_le_add (le_def.mp hk.1 p) (le_def.mp hk.2 p)

end Supernatural

end GroundTheory.ProfCoh
