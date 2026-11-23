module

public import Mathlib
public import Formalism.PieriBlockIdeals.LemmaDSkeletonUnit

@[expose] public section

-- bundled from Formalism.PieriBlockIdeals.StatementLC
section
namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

def colSeq {q n : ℕ} (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q) (j : Fin n) : ℕ := κ j.val (ρ j)

def cseq {q n : ℕ} (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q) (j : Fin n) : ℤ :=
  (κ j.val (ρ j) : ℤ) - ((ρ j).val : ℤ)

def IsContentSeq {q n : ℕ} (lam2 : Fin q → ℕ) (c : Fin n → ℤ) : Prop :=
  ∃ (tau : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ ∧ cseq κ ρ = c

def IsWt (K : Type*) {P M : Type*} {q n : ℕ} [Field K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (lam2 : Fin q → ℕ) (c : Fin n → ℤ) (z : Tens (Fin q) P M n) : Prop :=
  Cas K EM 0 z = ((casVal lam2 : ℤ) : K) • z ∧ ∀ j : Fin n, xJM K EM j z = ((c j : ℤ) : K) • z

def meas {n : ℕ} (col : Fin n → ℕ) : ℕ := ∑ l : Fin n, (n - l.val) * col l

def SwapPath : Prop :=
  ∀ (q n : ℕ) (lam2 tau : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ →
    ∀ (j : Fin n) (hj : j.val + 1 < n), colSeq κ ρ ⟨j.val + 1, hj⟩ < colSeq κ ρ j →
    2 ≤ cseq κ ρ j - cseq κ ρ ⟨j.val + 1, hj⟩ ∧
      ∃ κ' : ℕ → Fin q → ℕ, IsPath n lam2 tau κ' (ρ ∘ Equiv.swap j ⟨j.val + 1, hj⟩) ∧
        cseq κ' (ρ ∘ Equiv.swap j ⟨j.val + 1, hj⟩) = cseq κ ρ ∘ Equiv.swap j ⟨j.val + 1, hj⟩ ∧
        colSeq κ' (ρ ∘ Equiv.swap j ⟨j.val + 1, hj⟩) = colSeq κ ρ ∘ Equiv.swap j ⟨j.val + 1, hj⟩

def SameCol : Prop :=
  ∀ (q n : ℕ) (lam2 tau : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ →
    ∀ (j : Fin n) (hj : j.val + 1 < n), colSeq κ ρ ⟨j.val + 1, hj⟩ = colSeq κ ρ j →
    cseq κ ρ ⟨j.val + 1, hj⟩ = cseq κ ρ j - 1 ∧
      ¬ IsContentSeq lam2 (cseq κ ρ ∘ Equiv.swap j ⟨j.val + 1, hj⟩)

def MeasSwap : Prop :=
  ∀ (n : ℕ) (col : Fin n → ℕ) (j : Fin n) (hj : j.val + 1 < n), col ⟨j.val + 1, hj⟩ < col j →
    meas (col ∘ Equiv.swap j ⟨j.val + 1, hj⟩) < meas col

def MonoRun : Prop :=
  ∀ (q n : ℕ) (lam2 tau : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ →
    (∀ (j : Fin n) (hj : j.val + 1 < n), colSeq κ ρ j ≤ colSeq κ ρ ⟨j.val + 1, hj⟩) →
    ∀ p j0 : ℕ, p < LD.colLen lam2 tau j0 →
    ∃ i : ℕ, i + p < n ∧ ∀ l : Fin n, i ≤ l.val → l.val ≤ i + p → colSeq κ ρ l = j0

def WtIff : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (lam2 : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q),
    κ 0 = lam2 → (∀ j : Fin n, κ (j.val + 1) = κ j.val + Pi.single (ρ j) 1) → ∀ z : Tens (Fin q) P M n,
    ((∀ j ≤ n, Cas K EM j z = ((casVal (κ j) : ℤ) : K) • z) ↔ IsWt K EM lam2 (cseq κ ρ) z)

def CasFromX : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (lam2 : Fin q → ℕ) (c : Fin n → ℤ) (z : Tens (Fin q) P M n),
    IsWt K EM lam2 c z → ∀ l ≤ n, Cas K EM l z =
      ((casVal lam2 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < l), (2 * c i + (q : ℤ)) : ℤ) : K) • z

def Exchange : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (lam2 : Fin q → ℕ) (c : Fin n → ℤ) (z : Tens (Fin q) P M n)
    (j : Fin n) (hj : j.val + 1 < n), IsWt K EM lam2 c z → c j ≠ c ⟨j.val + 1, hj⟩ →
    IsWt K EM lam2 (c ∘ Equiv.swap j ⟨j.val + 1, hj⟩)
      (permY K (Equiv.swap j ⟨j.val + 1, hj⟩) z + (((c j - c ⟨j.val + 1, hj⟩ : ℤ) : K)⁻¹) • z)

def PermXWt : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (lam2 : Fin q → ℕ) (c : Fin n → ℤ) (z : Tens (Fin q) P M n)
    (σ : Equiv.Perm (Fin n)), IsWt K EM lam2 c z → IsWt K EM lam2 c (permX K σ z)

def ToSymYX : Prop :=
  ∀ (K R P M : Type) [CommRing K] [AddCommGroup M] [Module K M] [DecidableEq R] [DecidableEq P] [Fintype R] [Fintype P]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (z : Tens R P M n), toSym K (permY K σ z) = toSym K (permX K σ⁻¹ z)

def NoTuple : Prop :=
  ∀ (K V J : Type) [Field K] [AddCommGroup V] [Module K V] (T : J → Module.End K V) (TT : Set (J → K)) (E : Set V),
    (∀ e ∈ E, ∃ t ∈ TT, ∀ j, T j e = t j • e) → ∀ v ∈ Submodule.span K E, ∀ t0 : J → K, t0 ∉ TT →
    (∀ j, T j v = t0 j • v) → v = 0

def NoWt : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (lam2 : Fin q → ℕ),
    (⨆ tau, PathSpace K (P := P) EM n lam2 tau) = ⊤ →
    ∀ (c : Fin n → ℤ) (z : Tens (Fin q) P M n), IsWt K EM lam2 c z → ¬ IsContentSeq lam2 c → z = 0

def GoodSwap : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq P] [Fintype P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (lam2 : Fin q → ℕ) (c : Fin n → ℤ)
    (j : Fin n) (hj : j.val + 1 < n), 2 ≤ c j - c ⟨j.val + 1, hj⟩ →
    (∀ z : Tens (Fin q) P M n, IsWt K EM lam2 (c ∘ Equiv.swap j ⟨j.val + 1, hj⟩) z → toSym K z = 0) →
    ∀ z : Tens (Fin q) P M n, IsWt K EM lam2 c z → toSym K z = 0

def AntiStep : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (lam2 : Fin q → ℕ),
    (⨆ tau, PathSpace K (P := P) EM n lam2 tau) = ⊤ →
    ∀ (c : Fin n → ℤ) (z : Tens (Fin q) P M n) (j : Fin n) (hj : j.val + 1 < n), IsWt K EM lam2 c z →
    c ⟨j.val + 1, hj⟩ = c j - 1 → ¬ IsContentSeq lam2 (c ∘ Equiv.swap j ⟨j.val + 1, hj⟩) →
    permY K (Equiv.swap j ⟨j.val + 1, hj⟩) z = - z

def Anti : Prop :=
  ∀ (K R P M : Type) [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq R] [DecidableEq P]
    [Fintype R] [Fintype P] (n i : ℕ), i + Fintype.card P < n → ∀ u : Tens R P M n,
    (∀ (j : Fin n) (hj : j.val + 1 < n), i ≤ j.val → j.val < i + Fintype.card P →
      permY K (Equiv.swap j ⟨j.val + 1, hj⟩) u = - u) →
    toSym K u = 0

def ColumnsFromPieri : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [CharZero K] [AddCommGroup M] [Module K M] [DecidableEq P] [Fintype P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (lam2 : Fin q → ℕ),
    (⨆ tau, PathSpace K (P := P) EM n lam2 tau) = ⊤ →
    ∀ tau, (∃ b : Fin q, ∃ j < tau b, Fintype.card P < LD.colLen lam2 tau j) →
      ∀ z ∈ PathSpace K (P := P) EM n lam2 tau, toSym K z = 0

end Formalism.CohomologicalDescent.LC
end

-- bundled from Formalism.PieriBlockIdeals.StatementLP
section
namespace Formalism.CohomologicalDescent.LP

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

section Defs

variable {K N : Type*} [CommRing K] [AddCommGroup N] [Module K N] {q : ℕ}

def IsHW (T : Fin q → Fin q → Module.End K N) (μ : Fin q → K) (v : N) : Prop :=
  (∀ a b, a < b → T a b v = 0) ∧ ∀ a, T a a v = μ a • v

def Stab (T : Fin q → Fin q → Module.End K N) (S : Submodule K N) : Prop :=
  ∀ a b, ∀ x ∈ S, T a b x ∈ S

def casOp (T : Fin q → Fin q → Module.End K N) : Module.End K N := ∑ b, ∑ b', T b b' * T b' b

end Defs

structure FormMod {K N : Type*} [Field K] [LinearOrder K] [AddCommGroup N] [Module K N] {q : ℕ}
    (T : Fin q → Fin q → Module.End K N) (B : LinearMap.BilinForm K N) : Prop where

  gl : GlRel T

  symm : ∀ x y, B x y = B y x

  pos : ∀ x, x ≠ 0 → 0 < B x x

  adj : ∀ a b x y, B (T a b x) y = B x (T b a y)

  diag : ∀ a, ⨆ μ : K, Module.End.eigenspace (T a a) μ = ⊤

structure Tower {K N : Type*} [Field K] [LinearOrder K] [AddCommGroup N] [Module K N] {q : ℕ} (n : ℕ)
    (D ε : ℕ → Fin q → Fin q → Module.End K N) (B : LinearMap.BilinForm K N) : Prop where

  form : ∀ j ≤ n, FormMod (D j) B

  step : ∀ j < n, ∀ a b, D (j + 1) a b = D j a b + ε j a b

  unit_mul : ∀ j < n, ∀ a b c d, ε j a b * ε j c d = if b = c then ε j a d else 0

  unit_one : ∀ j < n, ∑ a, ε j a a = 1

  comm : ∀ i j, i ≤ j → j < n → ∀ a b c d, Commute (D i a b) (ε j c d)

def tensForm {K R P M : Type*} [CommRing K] [AddCommGroup M] [Module K M] [Fintype R] [Fintype P] [DecidableEq R] [DecidableEq P]
    (n : ℕ) (B : LinearMap.BilinForm K M) : LinearMap.BilinForm K (Tens R P M n) :=
  ∑ g : Fin n → R × P, B.comp (LinearMap.proj g) (LinearMap.proj g)

def epsY (K : Type*) {R P M : Type*} [CommRing K] [AddCommGroup M] [Module K M] [DecidableEq R] [DecidableEq P] (n : ℕ)
    (j : ℕ) (a b : R) : Module.End K (Tens R P M n) := if h : j < n then unitY K ⟨j, h⟩ a b else 0

def ExistsHW : Prop :=
  ∀ (K N : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (T : Fin q → Fin q → Module.End K N), GlRel T → (∀ a, ⨆ μ : K, Module.End.eigenspace (T a a) μ = ⊤) →
    ∀ C : Submodule K N, Stab T C → C ≠ ⊥ → ∃ v ∈ C, v ≠ 0 ∧ ∃ μ, IsHW T μ v

def CompleteRed : Prop :=
  ∀ (K N : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (T : Fin q → Fin q → Module.End K N) (B : LinearMap.BilinForm K N), FormMod T B →
    ∀ S S' : Submodule K N, Stab T S → Stab T S' → (∀ v ∈ S, ∀ μ, IsHW T μ v → v ∈ S') → S ≤ S'

def HWDominant : Prop :=
  ∀ (K N : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup N] [Module K N]
    (T : Fin q → Fin q → Module.End K N) (B : LinearMap.BilinForm K N), FormMod T B →
    ∀ (v : N) (μ : Fin q → K), v ≠ 0 → IsHW T μ v → ∀ a b, a < b → μ b ≤ μ a

def CasCentral : Prop :=
  ∀ (K N : Type) (q : ℕ) [CommRing K] [AddCommGroup N] [Module K N] (T : Fin q → Fin q → Module.End K N), GlRel T →
    ∀ c d, Commute (casOp T) (T c d)

def StepHW : Prop :=
  ∀ (K N : Type) (q : ℕ) [CommRing K] [AddCommGroup N] [Module K N] (T ε : Fin q → Fin q → Module.End K N),
    (∀ a b c d, ε a b * ε c d = if b = c then ε a d else 0) → ∑ a, ε a a = 1 → (∀ a b c d, Commute (T a b) (ε c d)) →
    ∀ (z : N) (μ : Fin q → K), z ≠ 0 → IsHW (fun a b => T a b + ε a b) μ z →
    ∃ b, ε b b z ≠ 0 ∧ IsHW T (μ - Pi.single b 1) (ε b b z)

def GeneratedHW : Prop :=
  ∀ (K N : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup N] [Module K N]
    (T : Fin q → Fin q → Module.End K N) (B : LinearMap.BilinForm K N), FormMod T B → ∀ κ : Fin q → K,
    (∀ S : Submodule K N, Stab T S → (∀ v, IsHW T κ v → v ∈ S) → S = ⊤) →
    ∀ (v : N) (μ : Fin q → K), v ≠ 0 → IsHW T μ v → μ = κ

def TowerPieri : Prop :=
  ∀ (K N : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (n : ℕ) (D ε : ℕ → Fin q → Fin q → Module.End K N) (B : LinearMap.BilinForm K N) (lam2 : Fin q → ℕ), Tower n D ε B →
    (∀ (v : N) (μ : Fin q → K), v ≠ 0 → IsHW (D 0) μ v → μ = fun b => (lam2 b : K)) →
    Submodule.span K {z : N | ∃ (tau : Fin q → ℕ) (κ : ℕ → Fin q → ℕ) (ρ : Fin n → Fin q), IsPath n lam2 tau κ ρ ∧
      ∀ j ≤ n, casOp (D j) z = ((casVal (κ j) : ℤ) : K) • z} = ⊤

def TensTower : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup M] [Module K M] [DecidableEq P] [Fintype P]
    (EM : Fin q → Fin q → Module.End K M) (B : LinearMap.BilinForm K M) (n : ℕ), FormMod EM B →
    Tower n (fun j => (Dpart K EM j : Fin q → Fin q → Module.End K (Tens (Fin q) P M n))) (epsY K n) (tensForm n B)

def TensBase : Prop :=
  ∀ (K P M : Type) (q : ℕ) [CommRing K] [AddCommGroup M] [Module K M] [DecidableEq P]
    (EM : Fin q → Fin q → Module.End K M) (n : ℕ) (κ : Fin q → K),
    (∀ (v : M) (μ : Fin q → K), v ≠ 0 → IsHW EM μ v → μ = κ) →
    ∀ (z : Tens (Fin q) P M n) (μ : Fin q → K), z ≠ 0 → IsHW (Dpart K EM 0) μ z → μ = κ

def Pieri : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [DecidableEq P] [Fintype P] (EM : Fin q → Fin q → Module.End K M) (B : LinearMap.BilinForm K M) (lam2 : Fin q → ℕ), FormMod EM B →
    (∀ (v : M) (μ : Fin q → K), v ≠ 0 → IsHW EM μ v → μ = fun b => (lam2 b : K)) →
    ∀ n : ℕ, (⨆ tau, PathSpace K (P := P) EM n lam2 tau) = ⊤

def PieriGenerated : Prop :=
  ∀ (K P M : Type) (q : ℕ) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [DecidableEq P] [Fintype P] (EM : Fin q → Fin q → Module.End K M) (B : LinearMap.BilinForm K M) (lam2 : Fin q → ℕ), FormMod EM B →
    (∀ S : Submodule K M, Stab EM S → (∀ v, IsHW EM (fun b => (lam2 b : K)) v → v ∈ S) → S = ⊤) →
    ∀ n : ℕ, (⨆ tau, PathSpace K (P := P) EM n lam2 tau) = ⊤

end Formalism.CohomologicalDescent.LP
end

