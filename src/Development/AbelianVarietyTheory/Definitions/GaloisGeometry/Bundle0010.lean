module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry
section
noncomputable section

namespace GlobalTheory.ThStr

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField Classical

variable {l : ℕ} [Fact l.Prime]

def laS (l : ℕ) [Fact l.Prime] (d : ℕ) (s : ZMod d) : MvPowerSeries (ZMod d) ℂ_[l] :=
  fun n => ∑ e ∈ Finset.range ((n.sum fun _ k => k) + 1),
    if n = Finsupp.single (s - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e)) then ((l : ℂ_[l]) ^ e)⁻¹ else 0

def laAt {d : ℕ} {κ : Type} (ι : ZMod d → κ) (s : ZMod d) : MvPowerSeries κ ℂ_[l] :=
  MvPowerSeries.subst (fun r : ZMod d => (MvPowerSeries.X (ι r) : MvPowerSeries κ ℂ_[l])) (laS l d s)

end GlobalTheory.ThStr
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualOm
section
noncomputable section

namespace GlobalTheory.ThBe0

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

variable {l : ℕ} [Fact l.Prime]

def lg {κ : Type} (k : κ) : MvPowerSeries κ ℂ_[l] :=
  PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries κ ℂ_[l]) (logF l)

structure IsFrob (σ : ℂ_[l] →+* ℂ_[l]) : Prop where
  norm_eq : ∀ x, ‖σ x‖ = ‖x‖
  lift : ∀ x ∈ Wp l, ∃ y ∈ Wp l, σ x = x ^ l + (l : ℂ_[l]) * y

def at2 {κ : Type} (b0 : MvPowerSeries (Fin 2) ℂ_[l]) (x y : MvPowerSeries κ ℂ_[l]) : MvPowerSeries κ ℂ_[l] :=
  MvPowerSeries.subst (fun i : Fin 2 => if i = 0 then x else y) b0

structure IsBe0 (σ : ℂ_[l] →+* ℂ_[l]) (b0 : MvPowerSeries (Fin 2) ℂ_[l]) : Prop where
  coef : CoefWf b0
  axes : ∀ n, MvPowerSeries.coeff n b0 ≠ 0 → n 0 ≠ 0 ∧ n 1 ≠ 0
  add₁ : SimeqW (at2 b0 (lg 0 + lg 1) (lg 2) : MvPowerSeries (Fin 3) ℂ_[l]) (at2 b0 (lg 0) (lg 2) + at2 b0 (lg 1) (lg 2))
  add₂ : SimeqW (at2 b0 (lg 0) (lg 1 + lg 2) : MvPowerSeries (Fin 3) ℂ_[l]) (at2 b0 (lg 0) (lg 1) + at2 b0 (lg 0) (lg 2))
  conj : ∀ α ∈ Wp l, σ (σ α) = α →
    SimeqW (at2 b0 (MvPowerSeries.C α * lg 0) (lg 1) : MvPowerSeries (Fin 2) ℂ_[l]) (at2 b0 (lg 0) (MvPowerSeries.C (σ α) * lg 1))

structure DualOm (σ : ℂ_[l] →+* ℂ_[l]) (d : ℕ) {ρ : Type} [Fintype ρ] [DecidableEq ρ] (om om' : ρ → ℂ_[l]) : Prop where
  card : 2 * Fintype.card ρ = d
  mem : ∀ r, om r ∈ Wp l ∧ om' r ∈ Wp l
  fix : ∀ r, (σ ^ d) (om r) = om r ∧ (σ ^ d) (om' r) = om' r
  dual : ∀ r r', ∑ i ∈ Finset.range (d / 2), (σ ^ (2 * i)) (om r * om' r') = if r = r' then 1 else 0

def zOm (σ : ℂ_[l] →+* ℂ_[l]) {d : ℕ} {ρ : Type} [Fintype ρ] (om om' : ρ → ℂ_[l]) (s : ZMod d) : MvPowerSeries (ρ ⊕ ρ) ℂ_[l] :=
  if Even s.val then ∑ r, MvPowerSeries.C ((σ ^ s.val) (om r)) * lg (Sum.inl r)
  else ∑ r, MvPowerSeries.C ((σ ^ s.val) (om' r)) * lg (Sum.inr r)

end GlobalTheory.ThBe0
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MtType
section
noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions NumberField

def MtType {D : D7} (u : D.what₂.Word) (mt : ℕ → D.Dt →* ℂˣ) : Prop :=
  letI := D.host.cmStar
  ∀ (i : ℕ) (h : i < D.R.m), (∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ mt (i + 1) k ^ n = 1) ∧
    ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hcW u τ).e ⟨i, h⟩) ∧
      ∀ z : unitary D.host.E, ((mt (i + 1) (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ

end GlobalTheory.KerJ
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical

namespace GlobalTheory.KerStd

def StdBases (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) : Prop :=
  (∀ τ, LocBasisW D (tauEmb D lam τ) L (P τ)) ∧
  ((IsResidueClassZero D p ∨ IsSg D p) → ∀ z : Bool × HH D,
    ((P (tauPl D (posPl D p z 1))).map D.host.conj).transpose * P (tauPl D z) = 1) ∧
  (p = D.host.d → DualB D P)

def stdSer (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ} (κ : D.what₂.Tau → ℂ_[p])
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : MvPowerSeries ((Bool × HH D) × Fin N × Fin N') ℂ_[p] :=
  atLin (fun k (j : (Bool × HH D) × Fin N × Fin N') =>
    κ k.1 * chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))) (fun j => MvPowerSeries.X j) F

end GlobalTheory.KerStd
end
end

