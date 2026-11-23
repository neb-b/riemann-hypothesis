module

public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0012

@[expose] public section

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.DefsRepRec
section
noncomputable section

namespace Formalism.L2.KerInert.RepRec

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

def DataRec {p : ℕ} [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (D : D7) (cl : ℕ)
    (Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) : Prop :=
  ∃ S : Finset ℕ, SNum S cl ∧ p ∉ S ∧ ∀ j La La' y, IntOff S (Ξ j La La' y)

def ClAway (p cl : ℕ) : Prop := 0 < cl ∧ ¬ p ∣ cl

def XiAway {p : ℕ} [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (D : D7)
    (Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) : Prop :=
  ∃ S₀ : Finset ℕ, p ∉ S₀ ∧ ∀ j La La' y, IntOff S₀ (Ξ j La La' y)

end Formalism.L2.KerInert.RepRec
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.FrameInt
section
noncomputable section

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (wittFractionAlgebraCp Frm tw rank_eq)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)

def twE (v : X.Pl) (s : Fin (X.G.P.n' v)) : X.G.P.Qq v →+* ℂ_[p] :=
  letI := wittFractionAlgebraCp p
  letI := Formalism.L2.G.Pend.algKfC E.toCEmb
  tw X ℂ_[p] v s

def wE (p : ℕ) [Fact p.Prime] (w : WW p) : ℂ_[p] :=
  letI := wittFractionAlgebraCp p
  algebraMap (K0 p) ℂ_[p] (algebraMap (WW p) (K0 p) w)

variable (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  {j : ℕ} {L0 : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j L0 La')

def Gp (v : X.Pl) : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v) :=
  M (j + 1) La' v * (φ.g' v : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v))

def Gpi (v : X.Pl) : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v) :=
  (((φ.g' v)⁻¹ : GL _ _) : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)) *
    (M (j + 1) La' v)⁻¹

def Gm (v : X.Pl) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) :=
  M j L0 v * (φ.g v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))

def Gmi (v : X.Pl) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) :=
  (((φ.g v)⁻¹ : GL _ _) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) * (M j L0 v)⁻¹

variable (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

def LamPosG (lam : Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) : Prop :=
  ∀ v s x, lamC lam (embT D (pos ⟨v, s⟩) x) = twE X E v s (ρ v (if IsOddPos s then D.host.conj x else x))

def FrobTw : Prop :=
  ∃ (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (twK : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), X.G.P.Qq v →+* MaximalUnramifiedExtension p) (wK : WW p →+* MaximalUnramifiedExtension p),
    UnrOK (MaximalUnramifiedExtension p) p σ ∧ (∀ v s x, ((twK v s x : MaximalUnramifiedExtension p) : ℂ_[p]) = twE X E v s x) ∧
    (∀ v s x, σ (twK v s x) = twK v (finRotate _ s) x) ∧ (∀ w, ((wK w : MaximalUnramifiedExtension p) : ℂ_[p]) = wE p w) ∧
    (∀ w, σ (wK w) = wK (sigW p w)) ∧ (∀ w, ‖((wK w : MaximalUnramifiedExtension p) : ℂ_[p])‖ ≤ 1)

def MInv : Prop := ∀ j (La : X.Lt j) (v : X.Pl), IsUnit (M j La v).det

end Formalism.L2.KerInert.RepFrame
end
end

