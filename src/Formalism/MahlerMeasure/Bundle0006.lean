module

public import Formalism.MahlerMeasure.MahlerMeasureProofs.Bundle0002
public import Formalism.MahlerMeasure.MahlerMeasureProofs.Bundle0003
public import Formalism.MahlerMeasure.MahlerMeasureProofs.Bundle0001
public import Formalism.MahlerMeasure.Bundle0003
public import Formalism.MahlerMeasure.Bundle0005

@[expose] public section

-- bundled from Formalism.MahlerMeasure.FinalD
section
namespace Formalism.GM.Top
open Formalism.GM
theorem smithZp : SmithZp := smith_form_p_adic_integers
theorem lieMat : LieMat := lieMat_of mahler_binomial_unit_ball
theorem lieRoots : LieRoots := lieRoots_of gauss_norm_multiplicative
theorem valuation_window_lower_bound : ValuationWindowLowerBound := by
  intro p _ K _ _ _ n del₀ h E c lead roots t₀ U V d hc hU hV hUd hVd hE hdel hlead hdet hsm
  exact lieRoots p K h _ E _ lead roots t₀ hE hlead hdet
    (lieMat p K n del₀ h E c t₀ U V d hc hU hV hUd hVd hE hdel hsm)
end Formalism.GM.Top
end

-- bundled from Formalism.MahlerMeasure.StatementT
section
namespace Formalism.GM.M

open MvPolynomial Finset

def HypP (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (ρ : Fin r) (e1 : ℕ) : Prop :=
  (∀ j ≤ N, ∀ Cs : Finset (Fin r), (Cs = univ ∨ Cs = univ.erase ρ) → ∀ T : Set (Fin r → ℤ), CsSaturated Cs T →
    ∃ P, IsTypeProj p LL j Cs T P ∧ (∀ F G, fock p (P F) G = fock p F (P G)) ∧
      ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r)) ∧
  (∀ (j j' : ℕ) (Cs Cs' : Finset (Fin r)) (T T' : Set (Fin r → ℤ)) (P P'), j ≤ j' → Cs' ⊆ Cs →
    (Cs = univ ∨ Cs = univ.erase ρ) → (Cs' = univ ∨ Cs' = univ.erase ρ) →
    IsTypeProj p LL j Cs T P → IsTypeProj p LL j' Cs' T' P' → P ∘ₗ P' = P' ∘ₗ P)

def HypW (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (e1 : ℕ) : Prop :=
  ∀ j ≤ N, ∀ la : Fin r → ℤ, ∀ x ∈ IsoC p LL j univ la ⊓ Pol p r LL, x ∈ IntPol p (Fin N × Fin r) →
    ((p : ℚ_[p]) ^ e1) • x ∈ ⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p])
      (_ : h ∈ HWC p LL j univ la ⊓ Pol p r LL ∧ h ∈ IntPol p (Fin N × Fin r)), WeylLat p LL j h

def HypE (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (ρ : Fin r) (e1 : ℕ) : Prop :=
  ∀ j ≤ N, ∀ la : Fin r → ℤ, ∃ P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
    P ∘ₗ P = P ∧ LinearMap.range P = HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la ∧
    LinearMap.ker P ⊓ WtSpC p LL j univ la =
      (⨆ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ d < c),
        Submodule.map (glAct p LL j c d) ⊤) ⊓ WtSpC p LL j univ la ∧
    (∀ F G, F ∈ WtSpC p LL j univ la → G ∈ WtSpC p LL j univ la → fock p (P F) G = fock p F (P G)) ∧
    ∀ F ∈ PolZ p r LL, F ∈ WtSpC p LL j univ la → ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r)

def GramDeterminantGradedHypothesis (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (κ : ℝ) : Prop :=
  ∀ (w : Fin r → ℤ) (e k : ℕ) (g : Fin k → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
    LinearIndependent ℤ_[p] g → Submodule.span ℤ_[p] (Set.range g) = grLat p LLw J M ρ w (Fin.last K, ρ) e →
    (p : ℝ) ^ (-(κ * k)) ≤ ‖(Matrix.of fun a b => fock p (g a) (g b) / ∏ i, ((LLw.deg i).factorial : ℚ_[p])).det‖

def BadCrit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Vs : Type) [AddCommGroup Vs] [Module ℚ_[p] Vs] [Module ℤ_[p] Vs]
    [IsScalarTower ℤ_[p] ℚ_[p] Vs]
    (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (L L₁ : Submodule ℤ_[p] Vs) (D : ℤ),
    Module.Finite ℤ_[p] L → L₁ ≤ L →
    (∀ (a : ℤ_[p]) (x : Vs), a ≠ 0 → x ∈ L → a • x ∈ L₁ → x ∈ L₁) →
    (∀ u ∈ L₁, (∀ (a : ℤ_[p]) (x : Vs), x ∈ L₁ → u = a • x → IsUnit a) →
      ∃ u' ∈ L, (p : ℝ) ^ (-D) ≤ ‖be u u'‖) →
    bad p (fun x y => be x y) L D ≤ Module.finrank ℤ_[p] L - Module.finrank ℤ_[p] L₁

end Formalism.GM.M
end

