module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.EquivLift
section
noncomputable section

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

def EquivLift : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ (R : Finset (Fin m → ℕ)) (t : Module.End ℂ (PX m n)),
    (∀ f ∈ box ε (R : Set _), t f ∈ box ε (R : Set _)) →
    (∀ i j, ∀ f ∈ box ε (R : Set _), t (KopL ε i j f) = KopL ε i j (t f)) →
    ∃ w ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => firstFamilyOperatorEnd (n := n) ε c ab.1 ab.2), ∀ f ∈ box ε (R : Set _), t f = w f

end PositivityTheory.Rg.Sw.LC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.GaussianMomentRecurrence
section
noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem gaussian_moment_symm (c : ℝ) (p q : ℕ) : g1 c p q = g1 c q p := by
  unfold g1; by_cases h : p = q
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem gaussian_moment_recurrence (c : ℝ) (hc : 0 < c) (p q : ℕ) : (p : ℂ) * g1 c (p - 1) q = (c : ℂ) * g1 c p (q + 1) := by
  rcases p with _ | p
  · simp [g1]
  · simp only [Nat.add_sub_cancel, g1, Nat.add_right_cancel_iff]
    split_ifs with h
    · subst h
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      push_cast
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · simp

theorem phi_split (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n) :
    phi c s = g1 c (s (a, i, false)) (s (a, i, true)) *
      ∏ x ∈ Finset.univ.erase (a, i), g1 c (s (x.1, x.2, false)) (s (x.1, x.2, true)) := by
  unfold phi
  rw [← Fintype.prod_prod_type' (f := fun a i => g1 c (s (a, i, false)) (s (a, i, true)))]
  exact (Finset.mul_prod_erase _ (fun x : Fin m × Fin n => g1 c (s (x.1, x.2, false)) (s (x.1, x.2, true)))
    (Finset.mem_univ (a, i))).symm

theorem rest_congr (c : ℝ) (s s' : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (i : Fin n)
    (h : ∀ x : Fin m × Fin n, x ≠ (a, i) → ∀ b, s (x.1, x.2, b) = s' (x.1, x.2, b)) :
    ∏ x ∈ Finset.univ.erase (a, i), g1 c (s (x.1, x.2, false)) (s (x.1, x.2, true)) =
      ∏ x ∈ Finset.univ.erase (a, i), g1 c (s' (x.1, x.2, false)) (s' (x.1, x.2, true)) := by
  refine Finset.prod_congr rfl fun x hx => ?_
  have hx' := (Finset.mem_erase.1 hx).1
  rw [h x hx' false, h x hx' true]

theorem phi_rel (c : ℝ) (hc : 0 < c) (u : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    (u k : ℂ) * phi c (u - Finsupp.single k 1) = (c : ℂ) * phi c (Finsupp.single (flip k) 1 + u) := by
  obtain ⟨a, i, b⟩ := k
  rw [phi_split c _ a i, phi_split c _ a i,
    rest_congr c (u - Finsupp.single (a, i, b) 1) (Finsupp.single (flip (a, i, b)) 1 + u) a i (fun x hx b' => by
      have h1 : (x.1, x.2, b') ≠ (a, i, b) := fun h => hx (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simpa using this)
      have h2 : (x.1, x.2, b') ≠ flip (a, i, b) := fun h => hx (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simpa [flip] using this)
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
        if_neg (Ne.symm h1), if_neg (Ne.symm h2), tsub_zero, zero_add])]
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  cases b
  · have e1 : (a, i, true) ≠ (a, i, false) := by simp
    simp only [flip, Bool.not_false, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [add_comm]
    exact gaussian_moment_recurrence c hc _ _
  · have e1 : (a, i, true) ≠ (a, i, false) := by simp
    simp only [flip, Bool.not_true, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [gaussian_moment_symm c _ (u (a, i, true) - 1), gaussian_moment_symm c (1 + u (a, i, false)), add_comm]
    exact gaussian_moment_recurrence c hc _ _

variable (hM : OneMom)


include hM in
theorem mom_pderiv (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (Q : PX m n) :
    mom c (pderiv k Q) = (c : ℂ) * mom c (X (flip k) * Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u r =>
    have hX : (X (flip k) : PX m n) * monomial u r = monomial (Finsupp.single (flip k) 1 + u) r := by
      rw [X, monomial_mul, one_mul]
    rw [pderiv_monomial, hX, mom_monomial hM c hc, mom_monomial hM c hc, mul_assoc, phi_rel c hc u k]
    ring
  | add P Q hP hQ => rw [map_add (f := _), mom_add hM c hc, hP, hQ, mul_add, mom_add hM c hc, mul_add]

theorem pderiv_comm (k j : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv k (pderiv j Q) = pderiv j (pderiv k Q) := by
  have : ⁅(pderiv k : Derivation ℂ (PX m n) (PX m n)), (pderiv j : Derivation ℂ (PX m n) (PX m n))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro l
    rw [Derivation.commutator_apply, Derivation.zero_apply]
    classical
    rw [pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have h := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D Q) this
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h
  exact sub_eq_zero.1 h

theorem cr_apply (c : ℝ) (k : Fin m × Fin n × Bool) (Q : PX m n) :
    cr c k Q = -pderiv k Q + (2 * c : ℂ) • (X (flip k) * Q) := by
  obtain ⟨a, i, b⟩ := k
  cases b <;> simp [cr, flip]

theorem pderiv_cr (c : ℝ) (k j : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv k (cr c j Q) = cr c j (pderiv k Q) + (if k = flip j then (2 * c : ℂ) else 0) • Q := by
  classical
  rw [cr_apply, cr_apply, map_add (f := _), map_neg, Derivation.map_smul, pderiv_mul, pderiv_X, pderiv_comm k j]
  by_cases h : k = flip j
  · subst h; simp [Pi.single_apply]; ring
  · simp [Pi.single_apply, h, Ne.symm h]

end PositivityTheory.Rg.Sw.LC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PairSym
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def EtaLt (r : Sym m n) (N : ℕ) : Prop := ∀ t ∈ r.support, (∑ k, t (Sum.inr k)) < N

def EtaLe (r : Sym m n) (N : ℕ) : Prop := ∀ t ∈ r.support, (∑ k, t (Sum.inr k)) ≤ N

def vecVar (ε : Fin m → Bool) (a : Fin m) (i : Fin n) : Sym m n :=
  if ε a then X (Sum.inl (a, i, false)) else X (Sum.inr (a, i, true))

def covVar (ε : Fin m → Bool) (b : Fin m) (i : Fin n) : Sym m n :=
  if ε b then X (Sum.inr (b, i, false)) else X (Sum.inl (b, i, true))

def pairSym (ε : Fin m → Bool) (a b : Fin m) : Sym m n := ∑ i, vecVar ε a i * covVar ε b i

def CompSt : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (u v : Sym m n) (d₁ d₂ : ℕ), SymbolInFirstFamily ε u → SymbolInFirstFamily ε v → EtaLe u d₁ → EtaLe v d₂ →
    ∃ r : Sym m n, SymbolInFirstFamily ε r ∧ EtaLt r (d₁ + d₂) ∧ ∀ f, op u (op v f) = op (u * v) f + op r f

def FFTSym : Prop :=
  PositivityTheory.Rg.Sw.FFT → ∀ (m n : ℕ) (ε : Fin m → Bool) (s : Sym m n), SymbolInFirstFamily ε s → (∀ i j, symK ε i j s = 0) →
    s ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => (pairSym (n := n) ε ab.1 ab.2))

end PositivityTheory.Rg.Sw.LC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.ZeroRight
section
noncomputable section

namespace PositivityTheory.Rg.Sw.LC

namespace CoreA

variable {V : Type} [AddCommGroup V] [Module ℂ V]

structure PosH (φ : V → V → ℂ) : Prop where
  add : ∀ v, ∀ w₁ w₂, φ v (w₁ + w₂) = φ v w₁ + φ v w₂
  smul : ∀ v w (r : ℂ), φ v (r • w) = r * φ v w
  herm : ∀ v w, φ w v = star (φ v w)
  pos : ∀ v, v ≠ 0 → 0 < (φ v v).re

variable {φ : V → V → ℂ}

namespace PosH

variable (h : PosH φ)
include h

theorem zero_right (v : V) : φ v 0 = 0 := by
  have := h.smul v 0 0
  simpa using this

theorem zero_left (v : V) : φ 0 v = 0 := by
  rw [h.herm v 0, h.zero_right, star_zero]

theorem add_left (v₁ v₂ w : V) : φ (v₁ + v₂) w = φ v₁ w + φ v₂ w := by
  rw [h.herm w (v₁ + v₂), h.add, star_add, ← h.herm w v₁, ← h.herm w v₂]

theorem smul_left (v w : V) (r : ℂ) : φ (r • v) w = star r * φ v w := by
  rw [h.herm w (r • v), h.smul, star_mul', ← h.herm w v]

theorem sum_left {ι : Type*} (s : Finset ι) (c : ι → ℂ) (b : ι → V) (w : V) :
    φ (∑ k ∈ s, c k • b k) w = ∑ k ∈ s, star (c k) * φ (b k) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_left, h.smul_left, ih]

theorem definite (v : V) (hv : φ v v = 0) : v = 0 := by
  by_contra hne
  have := h.pos v hne
  rw [hv] at this
  simp at this

theorem re_nonneg (v : V) : 0 ≤ (φ v v).re := by
  by_cases hv : v = 0
  · subst hv; simp [h.zero_right]
  · exact (h.pos v hv).le

def perp (W : Submodule ℂ V) : Submodule ℂ V where
  carrier := {v | ∀ w ∈ W, φ w v = 0}
  add_mem' := by
    intro a b ha hb w hw
    rw [h.add, ha w hw, hb w hw, add_zero]
  zero_mem' := fun w _ => h.zero_right w
  smul_mem' := by
    intro r v hv w hw
    rw [h.smul, hv w hw, mul_zero]

theorem inf_perp (W : Submodule ℂ V) : W ⊓ h.perp W = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rcases Submodule.mem_inf.1 hv with ⟨h1, h2⟩
  exact (Submodule.mem_bot ℂ).2 (h.definite v (h2 v h1))

end PosH

end CoreA

end PositivityTheory.Rg.Sw.LC
end
end

