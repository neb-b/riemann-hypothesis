module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2

structure HostSz {R : Ranks} (H : Formalism.BasicNotions.Host R) (L : ℝ) : Prop where
  rank : 62 ≤ R.r
  len : 4 ≤ L
  deg : Real.log R.f ≤ L
  g : ∀ i, Real.log (H.g i) ≤ 9 * L + 1
  p : Real.log H.pde ≤ L ∧ Real.log H.pde' ≤ L
  rd : Real.log |((discr H.E : ℤ) : ℝ)| / (2 * R.f) ≤ 2 * L

def poR (R : Ranks) (L : ℝ) : ℝ := 19 * (R.f : ℝ) * (R.r : ℝ) ^ 2 * L + 198 * (R.f : ℝ) ^ 2 * L

def xiOrd {R : Ranks} (H : Formalism.BasicNotions.Host R) (N : ℕ) : ℕ :=
  2 * classNumber H.E * Nat.card (𝓞 H.E ⧸ Ideal.span {(N : 𝓞 H.E)})ˣ

def JointQ (D : D7) : Prop :=
  FieldOK0 D D.host.pde ∧ FieldOK0 D D.host.pde' ∧ (∃ xi, XiOK D D.host.pde xi) ∧ (∃ xi, XiOK D D.host.pde' xi) ∧
    ∀ L : ℝ, HostSz D.host L → Sz (FO D) (poR D.R L) (poR D.R L)

end GlobalTheory.FieldSize
