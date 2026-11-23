module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.RankGapBounds.Bundle0001
public import Formalism.RankGapBounds.TheoremALocOfLemmaA
public import Formalism.PieriBlockIdeals.Bundle0001

@[expose] public section

-- bundled from Formalism.PieriBlockIdeals.StatementLA
section
open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LA

open Formalism.GradedWeylDivisibility

def lamU (r n : ℕ) (ν : Fin n → ℕ) : Fin r → ℤ :=
  fun a => (rowNu (r := r) ν a : ℤ) + ((r : ℤ) - 1 - (a.val : ℤ))

def InclZ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (l e : ℕ) : Prop :=
  ∃ m : ℕ, ¬ l ∣ m ∧ ∀ x ∈ dualWeyl ℤ r n ν, ((m * l ^ e : ℕ) : ℤ) • x ∈ weyl ℤ r n hn ν

def LemmaAZ : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ r n hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r n ν) l)

def exZ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (l : ℕ) : ℕ := sInf {e : ℕ | InclZ r n hn ν l e}

def ExZSpec : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ r n hn ν l (exZ r n hn ν l)

def ExactExponentRankTwo : Prop :=
  ∀ (n : ℕ) (ν : Fin n → ℕ) (l : ℕ),
    Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 n ν) l =
      Formalism.RankGapBounds.JumpSetsAlt.maxVal l (rowNu (r := 2) ν 0 - rowNu (r := 2) ν 1)

def binForm (R : Type) [CommRing R] (d : ℕ) :
    (Fin (d + 1) → R) →ₗ[R] MvPolynomial (Fin 2 × Fin 1) R :=
  ∑ i : Fin (d + 1), (LinearMap.proj i : (Fin (d + 1) → R) →ₗ[R] R).smulRight
    ((X ((0 : Fin 2), (0 : Fin 1)) : MvPolynomial (Fin 2 × Fin 1) R) ^ (d - i.val) *
      X ((1 : Fin 2), (0 : Fin 1)) ^ i.val)

def LatticeInclusionTrivialWeight : Prop :=
  ∀ (r : ℕ) (hn : 0 ≤ r) (ν : Fin 0 → ℕ) (l : ℕ), l.Prime →
    InclZ r 0 hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r 0 ν) l)

def LatticeInclusionRankOne : Prop :=
  ∀ (n : ℕ) (hn : n ≤ 1) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ 1 n hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 1 n ν) l)

def LemmaAZ_r2n1 : Prop :=
  ∀ (hn : 1 ≤ 2) (ν : Fin 1 → ℕ) (l : ℕ), l.Prime →
    InclZ 2 1 hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 1 ν) l)

def LemmaAZ_r2n2 : Prop :=
  ∀ (hn : 2 ≤ 2) (ν : Fin 2 → ℕ), Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ 2 2 hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 2 ν) l)

def LatticeInclusionRankLeTwo : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r), r ≤ 2 → ∀ ν : Fin n → ℕ, Antitone ν → ∀ l : ℕ, l.Prime →
    InclZ r n hn ν l (Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU r n ν) l)

def SharpInclusionRankTwoOneColumn : Prop :=
  ∀ (hn : 1 ≤ 2) (ν : Fin 1 → ℕ) (l e : ℕ), l.Prime →
    (InclZ 2 1 hn ν l e ↔ Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0) ≤ e)

def SharpInclusionRankTwoTwoColumns : Prop :=
  ∀ (hn : 2 ≤ 2) (ν : Fin 2 → ℕ), Antitone ν → ∀ l e : ℕ, l.Prime →
    (InclZ 2 2 hn ν l e ↔ Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0 - ν 1) ≤ e)

end Formalism.CohomologicalDescent.LA
end
end

-- bundled from Formalism.PieriBlockIdeals.StatementLD
section
open MvPolynomial

namespace Formalism.CohomologicalDescent.LD

open Formalism.GradedWeylDivisibility

def boxesOfContent {q : ℕ} (lam2 tau : Fin q → ℕ) (c : ℤ) : ℕ :=
  (Finset.univ.filter fun a : Fin q => (lam2 a : ℤ) ≤ c + (a.val : ℤ) ∧ c + (a.val : ℤ) < (tau a : ℤ)).card

def colLen {q : ℕ} (lam2 tau : Fin q → ℕ) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun a : Fin q => lam2 a ≤ j ∧ j < tau a).card

def shapes (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) : Finset (Fin q → ℕ) :=
  (Fintype.piFinset fun a : Fin q => Finset.Icc (lam2 a) (lam2 a + i)).filter fun tau =>
    (∀ a b : Fin q, a ≤ b → tau b ≤ tau a) ∧ ∑ a, tau a = ∑ a, lam2 a + i ∧
      (∀ b : Fin q, ∀ j < tau b, colLen lam2 tau j ≤ p) ∧ boxesOfContent lam2 tau (w : ℤ) = 0

def mu (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) (c : ℤ) : ℕ :=
  (shapes p w i lam2).sup fun tau => boxesOfContent lam2 tau c

def Dn (p w i : ℕ) {q : ℕ} (lam2 : Fin q → ℕ) : ℤ :=
  ∏ k ∈ Finset.range (q + w + i), ((w : ℤ) - ((k : ℤ) - (q : ℤ))) ^ mu p w i lam2 ((k : ℤ) - (q : ℤ))

noncomputable def nablaWt (r : ℕ) (ν μ : Fin r → ℕ) : Submodule ℤ (MvPolynomial (Fin r × Fin r) ℤ) :=
  dualWeyl ℤ r r ν ⊓ weightedHomogeneousSubmodule ℤ (rowW r r) μ

def KilledAt (l r : ℕ) (ν μ : Fin r → ℕ) (c : ℤ) : Prop :=
  ∀ x ∈ nablaWt r ν μ, ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ (m * c) • x ∈ weyl ℤ r r le_rfl ν

def ExpLe (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ) : Prop := KilledAt l r ν μ ((l : ℤ) ^ e)

def blockWt (p q w : ℕ) (κ : Fin q → ℕ) : Fin (p + q) → ℕ := Fin.append (fun _ : Fin p => w) κ

def blockWtLast (p q w : ℕ) (κ : Fin q → ℕ) : Fin (q + p) → ℕ := Fin.append κ (fun _ : Fin p => w)

def IsDepth (p q w : ℕ) (μ : Fin (p + q) → ℕ) (i : ℕ) : Prop :=
  ∑ a : Fin p, μ (Fin.castAdd q a) + i = p * w

def IsDepthLast (p q w : ℕ) (μ : Fin (q + p) → ℕ) (i : ℕ) : Prop :=
  ∑ a : Fin p, μ (Fin.natAdd q a) = p * w + i

def depth2 {r : ℕ} (ξ : Fin r → ℤ) (lam μ : Fin r → ℕ) : ℤ := ∑ a, ξ a * ((lam a : ℤ) - (μ a : ℤ))

def LemmaDGradedAt (l p q w : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (p + q) → ℤ) : Prop :=
  ∀ (i' : ℤ) (eL : ℕ),
    (∀ μ2 : Fin q → ℕ, depth2 ξ (blockWt p q w lam2) (blockWt p q w μ2) ≤ i' → ExpLe l q lam2 μ2 eL) →
    ∀ (i : ℕ) (μ : Fin (p + q) → ℕ), IsDepth p q w μ i → depth2 ξ (blockWt p q w lam2) μ ≤ i' →
      ExpLe l (p + q) (blockWt p q w lam2) μ (eL + padicValInt l (Dn p w i lam2))

def LemmaDGraded : Prop :=
  ∀ (l p q w : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (p + q) → ℤ), l.Prime → Antitone lam2 → (∀ b, lam2 b ≤ w) →
    Antitone ξ → LemmaDGradedAt l p q w lam2 ξ

def LemmaDLast : Prop :=
  ∀ (l p q w M : ℕ) (lam2 : Fin q → ℕ), l.Prime → Antitone lam2 → (∀ b, w ≤ lam2 b ∧ lam2 b ≤ M) →
    ∀ eL : ℕ, (∀ μ2 : Fin q → ℕ, ExpLe l q lam2 μ2 eL) →
      ∀ (i : ℕ) (μ : Fin (q + p) → ℕ), IsDepthLast p q w μ i →
        ExpLe l (q + p) (blockWtLast p q w lam2) μ
          (eL + padicValInt l (Dn p (M - w) i fun b : Fin q => M - lam2 (Fin.rev b)))

def DnNeZero : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ), Dn p w i lam2 ≠ 0

def MuSupport : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ) (c : ℤ), (∀ b, lam2 b ≤ w) → mu p w i lam2 c ≠ 0 →
    -(q : ℤ) ≤ c ∧ c < (w : ℤ) + (i : ℤ)

def ExpLeMono : Prop :=
  ∀ (l r : ℕ) (ν μ : Fin r → ℕ) (e e' : ℕ), e ≤ e' → ExpLe l r ν μ e → ExpLe l r ν μ e'

def MuLe : Prop :=
  ∀ (p w i q : ℕ) (lam2 : Fin q → ℕ) (c : ℤ), mu p w i lam2 c ≤ p

def MuRange : Prop :=
  ∀ (p w i q m : ℕ) (lam2 : Fin q → ℕ) (c : ℤ), (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) → mu p w i lam2 c ≠ 0 →
    (m : ℤ) - (q : ℤ) < c ∧ c < (w : ℤ)

def DnDvd : Prop :=
  ∀ (p w i q m : ℕ) (lam2 : Fin q → ℕ), (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) →
    Dn p w i lam2 ∣ (((w + q - m - 1).factorial ^ p : ℕ) : ℤ)

def DnVal : Prop :=
  ∀ (l p w i q m : ℕ) (lam2 : Fin q → ℕ), l.Prime → (∀ b, m ≤ lam2 b ∧ lam2 b ≤ w) →
    (l - 1) * padicValInt l (Dn p w i lam2) ≤ p * (w + q - m - 1)

end Formalism.CohomologicalDescent.LD
end

