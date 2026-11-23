module

public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0003
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.BeProp
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.BeWInertOfSigma
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PadicNormTwoHundredSixteenEqOneOfFiveLe
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.HurwitzSubstituteTwoSeries
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.LocalLevelIsKOneAtT
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AdmissibleThirdOfSecondEleventh
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0013

@[expose] public section

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.FinalA
section
namespace Formalism.L2.KerInert

open Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend

def FactsA : Prop := Sigma.InvAlg ∧ Sigma.SecondEisensteinAlgebraic ∧ EndIntInert ∧ PhNormOKInert

theorem beWInert_ofA (h : FactsA) : BeWInert :=
  beWInert_of_sigma (Sigma.sigmaCurveInert_of h.1 h.2.1) h.2.2.1 h.2.2.2

theorem beProp_ofA (h : FactsA) (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ)
    [Fact p.Prime] (g : G1 p) (hLT : LTIso g) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hin : InertK D p)
    (hW : ModelOverW g.lam g.abelian₂ g.C) : Formalism.MainNotions.FormalGroupSystem.BeProp p (beLT hLT) :=
  beta_property_of_weight D cc δ p g hLT hAt h5 hin hW (beWInert_ofA h D p cc δ g hAt h5 hin hW)

theorem admissible_second_of_facts (h : FactsA) (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ)
    [Fact p.Prime] (g : G1 p) (hLT : LTIso g) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hin : InertK D p)
    (hW : ModelOverW g.lam g.abelian₂ g.C) (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (Y : Formalism.MainNotions.FormalGroupSystem.Pend X) (hY : Y.be = beLT hLT) :
    Formalism.MainNotions.FormalGroupSystem.adm2c D X Y :=
  admissible_second_at_place D cc δ p g hLT hAt h5 hin hW (beWInert_ofA h D p cc δ g hAt h5 hin hW) X Y hY

theorem admissible_eleventh_of_facts (h : FactsA) (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (p : ℕ)
    [Fact p.Prime] (g : G1 p) (hLT : LTIso g) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hin : InertK D p)
    (hW : ModelOverW g.lam g.abelian₂ g.C) (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (Y : Formalism.MainNotions.FormalGroupSystem.Pend X) (hY : Y.be = beLT hLT) :
    Formalism.MainNotions.FormalGroupSystem.adm11 D X Y :=
  Jet.adm11OfBeProp D p X Y (hY ▸ beProp_ofA h D cc δ p g hLT hAt h5 hin hW)

end Formalism.L2.KerInert
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.FrameLatMap
section
noncomputable section

open scoped Matrix

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.L2.G.Pend (Frm)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)

def TwInt : Prop :=
  ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)) (w : X.G.P.W v), ‖twE X E v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) w)‖ ≤ 1

variable (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

end Formalism.L2.KerInert.RepFrame
end
end

