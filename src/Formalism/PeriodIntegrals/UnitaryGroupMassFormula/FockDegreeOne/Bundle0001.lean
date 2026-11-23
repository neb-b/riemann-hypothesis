module

public import Formalism.PeriodIntegrals.Bundle0013

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.OmEDiagMonomial
section
noncomputable section

open FockH1Action

namespace PI.FockOneDegW.Diag

def lw {p q r s : ℕ} (l : Ln p q r s) (α : Ln p q r s →₀ ℕ) : ℚ :=
  if linePos l then (α l : ℚ) + 1 / 2 else -(α l : ℚ) - 1 / 2

theorem X_mul_monomial' {σ : Type*} (l : σ) (β : σ →₀ ℕ) (c : ℂ) :
    MvPolynomial.X l * MvPolynomial.monomial β c =
      MvPolynomial.monomial (Finsupp.single l 1 + β) c := by
  rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

theorem omE_diag_monomial {p q r s : ℕ} (l : Ln p q r s) (α : Ln p q r s →₀ ℕ) :
    omE l l (MvPolynomial.monomial α (1 : ℂ)) =
      ((lw l α : ℚ) : ℂ) • MvPolynomial.monomial α (1 : ℂ) := by
  unfold FockH1Action.omE
  rw [if_pos rfl]
  unfold FockH1Action.raiB FockH1Action.lowB lw
  cases hl : FockH1Action.linePos l
  · simp only [Bool.false_eq_true, ↓reduceIte, LinearMap.add_apply, Module.End.mul_apply, LinearMap.neg_apply,
      LinearMap.smul_apply, Module.End.one_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
    rw [X_mul_monomial', MvPolynomial.pderiv_monomial, add_tsub_cancel_left]
    refine MvPolynomial.ext _ _ fun β => ?_
    simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_neg, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial,
      Finsupp.add_apply, Finsupp.single_eq_same]
    by_cases hb : α = β <;> simp [hb] <;> ring
  · simp only [↓reduceIte, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.smul_apply, Module.End.one_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
    rw [MvPolynomial.pderiv_monomial, X_mul_monomial']
    by_cases h0 : α l = 0
    · refine MvPolynomial.ext _ _ fun β => ?_
      simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, h0]
      by_cases hb : α = β <;> simp [hb]
    · have hs : Finsupp.single l 1 + (α - Finsupp.single l 1) = α := by
        ext i
        by_cases hi : i = l
        · subst hi
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
          omega
        · have hli : l ≠ i := fun h => hi h.symm
          simp [hli]
      rw [hs]
      refine MvPolynomial.ext _ _ fun β => ?_
      simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
      by_cases hb : α = β <;> simp [hb]

theorem omAct_apply' (p q r s : ℕ) (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s M = ∑ l, ∑ l', M l l' • omE l l' := by
  unfold FockH1Action.omAct
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, Matrix.entryLinearMap_apply]

theorem sum_diag_of {p q r s : ℕ} (M : Matrix (Ln p q r s) (Ln p q r s) ℂ)
    (g : Ln p q r s → Prop) [DecidablePred g]
    (hM : ∀ l l', M l l' = if l = l' ∧ g l then 1 else 0) :
    ∑ l, ∑ l', M l l' • omE l l' = ∑ l, if g l then omE l l else 0 := by
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l]
  · rw [hM]
    by_cases h : g l <;> simp [h]
  · intro l' _ hne
    rw [hM, if_neg (fun h => hne h.1.symm), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem fockAct1_diag (p q r s : ℕ) (a : Ix p q) :
    fockAct1 p q r s (Eab a a) = ∑ c : Ix r s, omE ((a, c) : Ln p q r s) (a, c) := by
  classical
  unfold FockH1Action.fockAct1
  rw [LinearMap.comp_apply, LinearMap.flip_apply, Matrix.kroneckerMapBilinear_apply_apply, omAct_apply']
  rw [sum_diag_of _ (fun l : FockH1Action.Ln p q r s => l.1 = a)]
  · rw [show (∑ l : FockH1Action.Ln p q r s, if l.1 = a then FockH1Action.omE l l else 0) =
        ∑ x : FockH1Action.Ix p q, ∑ y : FockH1Action.Ix r s,
          if x = a then FockH1Action.omE ((x, y) : FockH1Action.Ln p q r s) (x, y) else 0 from Fintype.sum_prod_type _]
    rw [Fintype.sum_eq_single a (fun x hx => by simp [hx])]
    simp
  · intro l l'
    obtain ⟨x, y⟩ := l
    obtain ⟨x', y'⟩ := l'
    simp only [Matrix.kroneckerMap_apply, LinearMap.mul_apply', FockH1Action.Eab, Matrix.single_apply,
      Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> aesop

def W1 {p q r s : ℕ} (a : Ix p q) (α : Ln p q r s →₀ ℕ) : ℚ :=
  ∑ c : Ix r s, lw ((a, c) : Ln p q r s) α

theorem fockAct1_monomial (p q r s : ℕ) (a : Ix p q) (β : Ln p q r s →₀ ℕ) :
    fockAct1 p q r s (Eab a a) (MvPolynomial.monomial β (1 : ℂ)) =
      ((W1 a β : ℚ) : ℂ) • MvPolynomial.monomial β (1 : ℂ) := by
  rw [fockAct1_diag, LinearMap.sum_apply]
  simp only [omE_diag_monomial, W1, Rat.cast_sum, Finset.sum_smul]

theorem coeff_of_diag {σ : Type*} (T : Module.End ℂ (MvPolynomial σ ℂ)) (f : (σ →₀ ℕ) → ℂ)
    (hT : ∀ β, T (MvPolynomial.monomial β 1) = f β • MvPolynomial.monomial β 1)
    (P : MvPolynomial σ ℂ) (α : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (T P) α = f α * AddMonoidAlgebra.coeff P α := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have hu : MvPolynomial.monomial u a = a • MvPolynomial.monomial u (1 : ℂ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hu, map_smul, hT, smul_smul, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_monomial]
    by_cases h : u = α
    · subst h
      simp only [if_true, smul_eq_mul, mul_one]
      ring
    · simp only [h, if_false, smul_eq_mul, mul_zero]
  | add p₁ p₂ h₁ h₂ =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, h₁, h₂, mul_add]

theorem wt_of_isHW {p q : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) (h : IsHW act μ v) :
    v ≠ 0 ∧ ∀ a, (act (Eab a a) - ((μ a : ℚ) : ℂ) • (LinearMap.id : Module.End ℂ V)) v = 0 := by
  unfold FockH1Action.IsHW at h
  unfold FockH1Action.hwSub at h
  refine ⟨h.1, fun a => ?_⟩
  have hw := (Submodule.mem_inf.1 h.2).1
  simp only [FockH1Action.wtSub, Submodule.mem_iInf, LinearMap.mem_ker] at hw
  exact hw a

end PI.FockOneDegW.Diag
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.OneDegOfHalves
section
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW

def Harm2 {p q r s : ℕ} (P : Pol p q r s) : Prop :=
  ∀ Z : Mat r s, IsPC Z → minusPart (fockAct2 p q r s Z) P = 0

def FirstHalf : Prop := ∀ p q r s : ℕ,
  ∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P →
    (∀ Z : Mat r s, IsPC Z → minusPart ((fockAct2 p q r s) Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d

def SecondHalf : Prop := ∀ p q r s : ℕ,
  ∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P →
    (∀ Z : Mat p q, IsPC Z → minusPart ((fockAct1 p q r s) Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d

theorem oneDeg_of_halves (h1 : FirstHalf) (h2 : SecondHalf) : PI.FockDegreeTwoParts.OneDeg :=
  fun p q r s => ⟨h1 p q r s, h2 p q r s⟩

def posOp {p q r s : ℕ} (a b : Ix p q) : Module.End ℂ (Pol p q r s) :=
  ∑ c : Ix r s, if linePos ((a, c) : Ln p q r s) = true then
    LinearMap.mulLeft ℂ (X ((a, c) : Ln p q r s)) ∘ₗ (pderiv ((b, c) : Ln p q r s)).toLinearMap
  else 0

def negOp {p q r s : ℕ} (a b : Ix p q) : Module.End ℂ (Pol p q r s) :=
  ∑ c : Ix r s, if linePos ((a, c) : Ln p q r s) = true then 0
  else LinearMap.mulLeft ℂ (X ((a, c) : Ln p q r s)) ∘ₗ (pderiv ((b, c) : Ln p q r s)).toLinearMap

def kShift (r s : ℕ) {p q : ℕ} : Ix p q → ℚ
  | .inl _ => cPair r s
  | .inr _ => -cPair r s

def lowOp {p q r s : ℕ} (c d : Ix r s) : Module.End ℂ (Pol p q r s) :=
  ∑ a : Ix p q, if linePos ((a, d) : Ln p q r s) = true then
    (pderiv ((a, c) : Ln p q r s)).toLinearMap ∘ₗ (pderiv ((a, d) : Ln p q r s)).toLinearMap
  else 0

def InnerFacts : Prop := ∀ (σ : Type) (P Q Q' : MvPolynomial σ ℂ) (c : ℂ),
  fockInner P (Q + Q') = fockInner P Q + fockInner P Q' ∧
  fockInner P (c • Q) = c * fockInner P Q ∧
  fockInner Q P = starRingEnd ℂ (fockInner P Q) ∧
  ((fockInner P P).im = 0 ∧ 0 ≤ (fockInner P P).re) ∧
  (fockInner P P = 0 → P = 0) ∧
  ∀ l : σ, fockInner (X l * P) Q = fockInner P (pderiv l Q)

def OpsK : Prop := ∀ p q r s : ℕ, ∀ a b : Ix p q, sameBlock a b →
  fockAct1 p q r s (Eab a b) =
    posOp a b - negOp b a +
      (if a = b then (((kShift r s a : ℚ) : ℂ) • (1 : Module.End ℂ (Pol p q r s))) else 0)

def HarmIff : Prop := ∀ p q r s : ℕ, ∀ P : Pol p q r s,
  Harm2 P ↔ ∀ c d : Ix r s, ¬ sameBlock c d → lowOp (p := p) (q := q) c d P = 0

def HwHarmDeg : Prop := ∀ p q r s : ℕ, ∀ (μ : Ix p q → ℚ) (e : ℕ) (v : Pol p q r s),
  v ∈ homog (Ix p q × Ix r s) e → IsHW (fockAct1 p q r s) μ v → Harm2 v →
    (e : ℚ) = degW (cPair r s) μ

def Reduction : Prop := HwHarmDeg → FirstHalf

def Swap : Prop := FirstHalf → SecondHalf

theorem oneDeg_of (hT : HwHarmDeg) (hR : Reduction) (hS : Swap) : PI.FockDegreeTwoParts.OneDeg :=
  oneDeg_of_halves (hR hT) (hS (hR hT))

end PI.FockOneDegW
end
end

