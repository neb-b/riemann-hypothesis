module

public import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementD
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.Bundle0001
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementF

@[expose] public section

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.InvariantFactorPaths.PW MvPolynomial Finset

noncomputable def EX (p : ℕ) [Fact p.Prime] {K s : ℕ} (LL : Letters (K + 1)) (c : ℤ) (a b : Fin (s + 1)) :
    MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p] :=
  Fin.cases
    (Fin.cases ((((c : ℤ) : ℚ_[p]) • LinearMap.id - eulW p K (s + 1))) (fun j => dW p K (Fin.castSucc j)) b)
    (fun i => Fin.cases (Uop p LL c (univ.erase (Fin.last s)) (Fin.castSucc i))
      (fun j => glAct p LL (K + 1) (Fin.castSucc i) (Fin.castSucc j)) b) a

def wtX {K s : ℕ} (LL : Letters (K + 1)) (c : ℤ) (m : Fin (K + 1) × Fin (s + 1) →₀ ℕ) : Fin (s + 1) → ℤ :=
  Fin.cases (c - ∑ a : Fin (s + 1), (m (Fin.last K, a) : ℤ)) (fun i => wt LL (K + 1) (Fin.castSucc i) m)

def GXExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K s : ℕ) (LL : Letters (K + 1)) (c : ℤ), LL.vec (Fin.last K) = true →
    ∃ G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1),
      G.E = EX p LL c ∧ ∀ μ x m, AddMonoidAlgebra.coeff (G.comp μ x) m = if wtX LL c m = μ then AddMonoidAlgebra.coeff x m else 0

def UDivInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) (LL : Letters (K + 1)) (c : ℤ) (Cs : Finset (Fin r)) (a : Fin r) (k : ℕ), a ∈ Cs →
    ∀ x ∈ IntPol p (Fin (K + 1) × Fin r),
      ((k.factorial : ℚ_[p]))⁻¹ • ((Uop p LL c Cs a) ^ k) x ∈ IntPol p (Fin (K + 1) × Fin r)

def DWDivInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) (a : Fin r) (k : ℕ),
    ∀ x ∈ IntPol p (Fin (K + 1) × Fin r),
      ((k.factorial : ℚ_[p]))⁻¹ • ((dW p K a) ^ k) x ∈ IntPol p (Fin (K + 1) × Fin r)

def XVanish : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (ρ : Fin r) (c : ℤ) (o : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true →
    c + (∑ i : Fin (K + 1), if i = Fin.last K then 0 else (LL.deg i : ℤ)) < o →
    Pol p r (setLast LL o) ⊓ FreeOf p (Fin.last K, ρ) ⊓ TypesLE p LL (K + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ) = ⊥

def ResSatL (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (c0 : ℕ) : Prop :=
  ∀ x ∈ XSp p LL J M ρ, x ∈ IntPol p (Fin (K + 1) × Fin r) →
    ∃ h ∈ Y p LL J M, h ∈ IntPol p (Fin (K + 1) × Fin r) ∧ initPart (Fin.last K, ρ) 0 h = ((p : ℚ_[p]) ^ c0) • x

def ResSatLThm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true →
    ResSatL p LL J M ρ (2 * (r.choose 2 * Nat.log p (4 * LL.total + r - 1)))

def GradedBoundOfSaturation : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (e1 c0 : ℕ) (κ : ℝ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true →
    (∀ o ≤ LLw.deg (Fin.last K), HypP p (setLast LLw o) ρ e1 ∧ HypE p (setLast LLw o) ρ e1) →
    (∀ e ≤ LLw.deg (Fin.last K), ResSatL p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ c0) →
    (((K + 5) * e1 + 2 * c0 : ℕ) : ℝ) ≤ κ → GramDeterminantGradedHypothesis p LLw J M ρ κ

end Formalism.InvariantFactorPaths.L4
