module

public import Mathlib

@[expose] public section

-- bundled from Formalism.EllipticTorsion.IsoExpand
section
universe u

namespace Formalism.ELL

def quadDiff {M T : Type u} [AddCommGroup M] [AddCommGroup T] (φ : M → T) (a b : M) : T :=
  φ (a + b) - φ a - φ b

def QuadHyp {O S M T : Type u} [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T] (N : AddSubgroup T) (bar : O → O) (nrm : O → S) (φ : M → T) : Prop :=
  (∀ a a' b : M, quadDiff φ (a + a') b - quadDiff φ a b - quadDiff φ a' b ∈ N) ∧
  φ 0 ∈ N ∧
  (∀ (α : O) (t : M), φ (α • t) - nrm α • φ t ∈ N) ∧
  (∀ (α : O) (a b : M), quadDiff φ (α • a) b - quadDiff φ a (bar α • b) ∈ N)

def IsoExpand : Prop :=
  ∀ (O S M T : Type u) [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T] (N : AddSubgroup T) (bar : O → O) (nrm : O → S) (φ : M → T), QuadHyp N bar nrm φ →
    ∀ (n m : ℕ) (y : Fin m → Fin n → O) (t : Fin m → M),
      (∑ i, φ (∑ e, y e i • t e))
        - ((∑ e, (∑ i, nrm (y e i)) • φ (t e))
            + (∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'),
                quadDiff φ (t e) ((∑ i, bar (y e i) * y e' i) • t e'))) ∈ N

def IsoVanish : Prop :=
  ∀ (O S M T : Type u) [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T] (N : AddSubgroup T) (bar : O → O) (nrm : O → S) (φ : M → T), QuadHyp N bar nrm φ →
    ∀ (n m : ℕ) (y : Fin m → Fin n → O) (t : Fin m → M),
      (∀ e e', ∑ i, bar (y e i) * y e' i = 0) → (∀ e, ∑ i, nrm (y e i) = 0) →
        (∑ i, φ (∑ e, y e i • t e)) ∈ N

end Formalism.ELL
end

-- bundled from Formalism.EllipticTorsion.WSeriesUnique
section
open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

def WFixed {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R) : Prop :=
  constantCoeff w = 0 ∧
  w = X ^ 3 + C W.a₁ * X * w + C W.a₂ * X ^ 2 * w + C W.a₃ * w ^ 2 + C W.a₄ * X * w ^ 2
      + C W.a₆ * w ^ 3

def WSeriesUnique : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R), ∃! w : PowerSeries R, WFixed W w

def WSeriesLead : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R), WFixed W w →
    coeff 0 w = 0 ∧ coeff 1 w = 0 ∧ coeff 2 w = 0 ∧ coeff 3 w = 1

section Points

variable {K : Type u} [Field K] {σ : Type}

def xOf (w : PowerSeries K) (s : MvPowerSeries σ K) : FractionRing (MvPowerSeries σ K) :=
  algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) s /
    algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s)

def yOf (w : PowerSeries K) (s : MvPowerSeries σ K) : FractionRing (MvPowerSeries σ K) :=
  -1 / algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s)

end Points

def WPoint : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K), WFixed W w →
    ∀ (σ : Type) [Finite σ] (s : MvPowerSeries σ K), MvPowerSeries.constantCoeff s = 0 → s ≠ 0 →
      (W.map (algebraMap K (FractionRing (MvPowerSeries σ K)))).toAffine.Nonsingular
        (xOf w s) (yOf w s)

def WFormalGroup : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K), WFixed W w →
    ∃ F : FormalGroup K,
      (∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F.toPowerSeries ∈
        Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)) ∧
      let z₁ : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0
      let z₂ : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1
      let W' := (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine
      let ℓ := (yOf w z₁ - yOf w z₂) / (xOf w z₁ - xOf w z₂)
      xOf w F.toPowerSeries = W'.addX (xOf w z₁) (xOf w z₂) ℓ ∧
      yOf w F.toPowerSeries = W'.addY (xOf w z₁) (xOf w z₂) (yOf w z₁) ℓ

end Formalism.ELL
end
end

