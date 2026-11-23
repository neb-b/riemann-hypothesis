module

public import Formalism.LocalToGlobal.AlgebraicTheory.StatementC
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.AlgebraicTheory.StatementD
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (cmL CmOK matH Sesq altE IsSelfDual IsHerm IsPosDef IsLat IsReps imgLat Th alphaQ opU taylorMv)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.G (linSub)
open Formalism.L2.Th1.GD (LocNorm InMul frameM)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

section Defs

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def cLat (c : ℂ) (Λ : AddSubgroup V) : AddSubgroup V := imgLat (c • (LinearMap.id : V →ₗ[ℂ] V)) Λ

def xiHat (H : Sesq V) (q : ℕ) (Ψ : V → ℂ) (Sb : Finset V) (a : V) : ℂ :=
  ((q : ℂ))⁻¹ * ∑ b ∈ Sb, Ψ b * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H b a : ℂ))

def xiG (H : Sesq V) (α : V → ℂ) (θ : V → ℂ) (q : ℕ) (Ψ : V → ℂ) (Sa Sb : Finset V) (z : V) : ℂ :=
  ∑ a ∈ Sa, xiHat H q Ψ Sb a * α a * opU H a θ z

end Defs

def serLin {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {n ν κ : Type} [Fintype n] [DecidableEq n] [Fintype ν] [Fintype κ]
    (h : Matrix n n ℂ) (F : (n → ℂ) → ℂ) (r : κ → ℂ) (t : κ → n → ℂ) (Mat : n → ν → ℂ_[p]) : MvPowerSeries ν ℂ_[p] :=
  linSub Mat (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => ∑ k, r k * opU (matH h) (t k) F z))

def XiEt : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsHerm (matH h) → IsPosDef (matH h) → IsLat Λ →
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι →
  ∀ π : ℂ, IsQInt dK π → π * conj π = (p : ℂ) → ‖ι (conj π)‖ < 1 →
  ∀ Sa Sb : Finset (n → ℂ), IsReps (cLat (conj π) Λ) (cLat (conj π / π) Λ) Sa → IsReps (cLat (conj π) Λ) Λ Sb →
  ∀ Ψ : (n → ℂ) → ℂ, (∀ b ∈ Sb, ‖ι (Ψ b)‖ ≤ 1) →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖ι (r k)‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ dK ha hdK lam hlam) Λ (v j)) →
  ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ ‖(p : ℂ_[p])‖) →
    JetsIntegral (MvPowerSeries.C ((p : ℂ_[p]) ^ Fintype.card n) *
      serLin ι h (xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) θ (p ^ Fintype.card n) Ψ Sa Sb) r t
        (frameM (ι : ℂ →+* ℂ_[p]) v A))

def ScalarConst : Prop :=
  ∀ (dK : ℕ) (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsHerm (matH h) → IsPosDef (matH h) → IsLat Λ → IsSelfDual (matH h) Λ →
    Formalism.L2.Th1.H.IsSemiChar (matH h) Λ (alphaQ (Real.sqrt dK / 2) (matH h)) →
    Formalism.L2.Th1.H.AtMostLine (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ →
  ∀ (p : ℕ), p.Prime → ∀ π : ℂ, π * conj π = (p : ℂ) → conj π ≠ π →
    (∀ x ∈ Λ, π • x ∈ Λ) → (∀ x ∈ Λ, conj π • x ∈ Λ) → (∃ u w : ℂ, (∀ x ∈ Λ, u • x ∈ Λ) ∧ (∀ x ∈ Λ, w • x ∈ Λ) ∧ u * π + w * conj π = 1) →
  ∀ Sa : Finset (n → ℂ), IsReps (cLat (conj π) Λ) (cLat (conj π / π) Λ) Sa →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ, θ ≠ 0 →
    Sa.card = p ^ Fintype.card n ∧
    ∃ c : ℂ, c ^ 8 = (conj π / π) ^ (4 * Fintype.card n) ∧
      ∀ z, θ ((π / conj π) • z) =
        c * ((Real.sqrt ((p : ℝ) ^ Fintype.card n) : ℝ) : ℂ)⁻¹ *
          ∑ a ∈ Sa, alphaQ (Real.sqrt dK / 2) (matH h) a * opU (matH h) a θ z

def XiSwap : Prop :=
  ∀ (dK : ℕ) (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsHerm (matH h) → IsSelfDual (matH h) Λ →
    Formalism.L2.Th1.H.IsSemiChar (matH h) Λ (alphaQ (Real.sqrt dK / 2) (matH h)) →
  ∀ (q : ℕ), 0 < q → ∀ π : ℂ, π ≠ 0 → (∀ x ∈ Λ, π • x ∈ Λ) → (∀ x ∈ Λ, conj π • x ∈ Λ) →
  ∀ Sa Sb : Finset (n → ℂ), IsReps (cLat (conj π) Λ) (cLat (conj π / π) Λ) Sa → IsReps (cLat (conj π) Λ) Λ Sb →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ, ∀ C' : ℂ, C' ≠ 0 →
    (∀ z, θ ((π / conj π) • z) = C' * ∑ a ∈ Sa, alphaQ (Real.sqrt dK / 2) (matH h) a * opU (matH h) a θ z) →
  ∀ (Ψ : (n → ℂ) → ℂ) (z : n → ℂ),
    xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) θ q Ψ Sa Sb z =
      (C' * (q : ℂ))⁻¹ * ∑ b ∈ Sb, Ψ b * alphaQ (Real.sqrt dK / 2) (matH h) b *
        opU (matH h) ((π / conj π) • b) θ ((π / conj π) • z)

def XiConn : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsHerm (matH h) → IsPosDef (matH h) → IsLat Λ →
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι →
  ∀ π : ℂ, IsQInt dK π → π * conj π = (p : ℂ) → ‖ι (conj π)‖ = 1 →
  ∀ Sa Sb : Finset (n → ℂ), IsReps (cLat (conj π) Λ) (cLat (conj π / π) Λ) Sa → IsReps (cLat (conj π) Λ) Λ Sb →
  ∀ Ψ : (n → ℂ) → ℂ, (∀ b ∈ Sb, ‖ι (Ψ b)‖ ≤ 1) →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖ι (r k)‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ dK ha hdK lam hlam) Λ (v j)) →
  ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ 1) →
    JetsIntegral (serLin ι h (xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) θ (p ^ Fintype.card n) Ψ Sa Sb) r t
      (frameM (ι : ℂ →+* ℂ_[p]) v A))

def SelfDualLatticeThetaPadicIntegrality : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsHerm (matH h) → IsPosDef (matH h) → IsLat Λ →
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι →
  ∀ π : ℂ, IsQInt dK π → π * conj π = (p : ℂ) →
  ∀ Sa Sb : Finset (n → ℂ), IsReps (cLat (conj π) Λ) (cLat (conj π / π) Λ) Sa → IsReps (cLat (conj π) Λ) Λ Sb →
  ∀ Ψ : (n → ℂ) → ℂ, (∀ b ∈ Sb, ‖ι (Ψ b)‖ ≤ 1) →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖ι (r k)‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ dK ha hdK lam hlam) Λ (v j)) →
  ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ ‖ι (conj π)‖) →
    JetsIntegral (MvPowerSeries.C ((p : ℂ_[p]) ^ Fintype.card n) *
      serLin ι h (xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) θ (p ^ Fintype.card n) Ψ Sa Sb) r t
        (frameM (ι : ℂ →+* ℂ_[p]) v A))

end Formalism.L2.AlgTh
end
end

-- bundled from Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (cmL CmOK matH IsSelfDual IsLat IsHerm IsPosDef Th alphaQ inter relIdx)
open Formalism.L2.Th1.GD (LocNorm)

def hPow {n : Type} (I : Type) [DecidableEq I] (h : Matrix n n ℂ) : Matrix (n × I) (n × I) ℂ :=
  fun w w' => if w.2 = w'.2 then h w.1 w'.1 else 0

def latPow {n : Type} (I : Type) (Λ : AddSubgroup (n → ℂ)) : AddSubgroup (n × I → ℂ) where
  carrier := {z | ∀ i, (fun k => z (k, i)) ∈ Λ}
  zero_mem' := fun _ => Λ.zero_mem
  add_mem' := fun hx hy i => Λ.add_mem (hx i) (hy i)
  neg_mem' := fun hx i => Λ.neg_mem (hx i)

def fnPow {n : Type} (I : Type) [Fintype I] (θ : (n → ℂ) → ℂ) (z : n × I → ℂ) : ℂ := ∏ i, θ fun k => z (k, i)

def LocNormScale : Prop :=
  ∀ (a₀ : ℕ) (b₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0)
    (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (c : ℂ), ‖ι c‖ ≤ 1 →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι → LocNorm a₀ b₀ dK ha hdK lam hlam h Λ (c • θ) p ι

def LocNormPow : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι →
  ∀ (I : Type) [Fintype I] [DecidableEq I],
    LocNorm a₀ b₀ dK ha hdK lam hlam (hPow I h) (latPow I Λ) (fnPow I θ) p ι

def LocNormInter : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ₁ Λ₂ : AddSubgroup (n → ℂ)),
    IsHerm (matH h) → IsPosDef (matH h) → IsLat Λ₁ → IsLat Λ₂ →
    IsSelfDual (matH h) Λ₁ → IsSelfDual (matH h) Λ₂ →
    (∀ x ∈ Λ₁, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ₁) → (∀ x ∈ Λ₂, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ₂) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ₁,
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), relIdx Λ₁ Λ₂ ≠ 0 → relIdx Λ₂ Λ₁ ≠ 0 → ¬ p ∣ relIdx Λ₁ Λ₂ →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ₁ θ p ι →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ₂ (inter (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ₁ Λ₂ θ) p ι

end Formalism.L2.AlgTh
end
end

