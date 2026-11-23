module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.FormalDegreeBessel.Bundle0001
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.PeriodIntegrals.Bundle0005
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Formalism.GradedWeylDivisibility.Bundle0001
public import Formalism.PeriodIntegrals.Bundle0015

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.AlgValsFin
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace PI.AlgValsFin

def AlgValsFin (L : Type) [Field L] [NumberField L] : Prop :=
  ∀ (χ : HChar L) (s : ℝ) (m : (L →+* ℂ) → ℤ),
    (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) * ∏ φ : L →+* ℂ, ((‖φ (k : L)‖ : ℝ) : ℂ) ^ (s : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) →
    ∃ C : Subfield ℂ, FiniteDimensional ℚ C ∧ χ.ValuesIn s C.subtype

end PI.AlgValsFin
end
end

-- bundled from Formalism.PeriodIntegrals.BesselL2FixAtZero
section
noncomputable section

namespace PI.BesselL2FixAtZero

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff ENNReal
open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Defs

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def ellA (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r) : ℂ :=
  if h : a.val + 1 < r then g (Formalism.QuantumDeterminants.eI k r a) (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩)
  else (g *ᵥ z) (Formalism.QuantumDeterminants.eI k r a)

def psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℂ :=
  Complex.exp (Complex.I * ((∑ a, c a * ellA k r z g a).re : ℂ))

end Defs

end PI.BesselL2FixAtZero
end
end

-- bundled from Formalism.PeriodIntegrals.BesselMapUniq
section
noncomputable section

namespace PI.BesselMapUniq

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
open PI.UpqRep

section Bessel

def ellA (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r) : ℂ :=
  if h : a.val + 1 < r then g (Formalism.QuantumDeterminants.eI k r a) (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩)
  else (g *ᵥ z) (Formalism.QuantumDeterminants.eI k r a)

def psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℂ :=
  Complex.exp (Complex.I * ((∑ a, c a * ellA k r z g a).re : ℂ))

end Bessel

section Smooth

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsCWCont {Wp : Type*} [NormedAddCommGroup Wp]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (B : H → Wp) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
    (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ v ∈ smoothVecs (k := k) (r := r) σ, ‖B v‖ ≤ C * (Ws.map fun w => ‖dsigW σ w v‖).sum

def IsBesselMapSm {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ)
    (ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (B : H → Wp) : Prop :=
  (∀ v ∈ smoothVecs (k := k) (r := r) σ, ∀ w ∈ smoothVecs (k := k) (r := r) σ, B (v + w) = B v + B w) ∧
    (∀ (c : ℂ), ∀ v ∈ smoothVecs (k := k) (r := r) σ, B (c • v) = c • B v) ∧
    (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ v ∈ smoothVecs (k := k) (r := r) σ,
      B (σ (h * m) v) = ψ m • π h (B v)) ∧
    IsCWCont (k := k) (r := r) σ B

end Smooth

def BesselMapUniq : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDSHpk k r ε lam σ → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    (∀ a, c a ≠ 0) → IsHCTypeW k r z u π →
    ∀ B₁ B₂ : H → Wp, IsBesselMapSm (k := k) (r := r) z (psiGen k r z c) σ π B₁ →
      IsBesselMapSm (k := k) (r := r) z (psiGen k r z c) σ π B₂ →
      ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ v ∈ smoothVecs (k := k) (r := r) σ, a • B₁ v + b • B₂ v = 0

end PI.BesselMapUniq
end
end

-- bundled from Formalism.PeriodIntegrals.BesselPeriodGGP
section
noncomputable section

namespace PI.BesselPeriodGGP

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff ENNReal
open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def eps48 (k r : ℕ) : Fin (2 * r + k + 1) → Bool :=
  fun i => if i.val < k - 1 then true else decide ((i.val - (k - 1)) % 2 = 0)

section Defs

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsHaarOn {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (Formalism.QuantumDeterminants.lmulM s) = μ

def IsQuotMeas (μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)) : Prop :=
  ∀ f : Formalism.QuantumDeterminants.Mt k r → ENNReal, Measurable f →
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂ν

def IsSPsiEquiv {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ)
    (ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (W : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) : Prop :=
  ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
    W (h * m * g) = ψ m • π h (W g)

def l2SG {Wp : Type*} [NormedAddCommGroup Wp] (ν : Measure (Formalism.QuantumDeterminants.Mt k r))
    (W : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) : ENNReal :=
  ∫⁻ x, (‖W (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂ν

def rconv {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (μG : Measure (Formalism.QuantumDeterminants.Mt k r))
    (e : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ)
    (W : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp :=
  fun x => ∫ g, e (Matrix.of g) • W (x * Matrix.of g) ∂μG

def fdegH (μG : Measure (Formalism.QuantumDeterminants.Mt k r))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H) : ℝ :=
  ‖w‖ ^ 4 / ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG

def eFun (μG : Measure (Formalism.QuantumDeterminants.Mt k r))
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ℂ :=
  (fdegH μG σ w : ℂ) * star ⟪w, σ g w⟫_ℂ

end Defs

end PI.BesselPeriodGGP
end
end

-- bundled from Formalism.PeriodIntegrals.CdHaarScale
section
noncomputable section

open MeasureTheory

namespace PI.CdHaarScale

abbrev umat {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

def CdTieAt (cd : Formalism.BasicNotions.CDHaar) (n : ℕ) (ε : Fin n → Bool) (c : NNReal) : Prop :=
  ∀ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
      ((c : ENNReal) • Formalism.REAL.muG ε) A =
        cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}

end PI.CdHaarScale

namespace PI

def CdHaarScale : Prop :=
  ∀ (cd : Formalism.BasicNotions.CDHaar) (n : ℕ) (ε : Fin n → Bool), ∃ c : NNReal, 0 < c ∧ PI.CdHaarScale.CdTieAt cd n ε c

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.DSInfCharCap
section
noncomputable section

namespace PI.DSInfCharCap

section RealPlaces

open scoped InnerProductSpace Matrix

def thetaJ {n : ℕ} (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  -(Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε)

def dsigC {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Y : Matrix (Fin n) (Fin n) ℂ) (v : H) : H :=
  PI.PhMeasCore.dsig σ ((1 / 2 : ℂ) • (Y + thetaJ ε Y)) v +
    Complex.I • PI.PhMeasCore.dsig σ ((1 / (2 * Complex.I)) • (Y - thetaJ ε Y)) v

def dsigCW {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : List (Matrix (Fin n) (Fin n) ℂ) → H → H
  | [], v => v
  | Y :: w, v => dsigC ε σ Y (dsigCW ε σ w v)

def unitM {n : ℕ} (ab : Fin n × Fin n) : Matrix (Fin n) (Fin n) ℂ := Matrix.single ab.1 ab.2 1

def Egl (n : ℕ) : Fin n → Fin n → FreeAlgebra ℂ (Fin n × Fin n) := fun a b => FreeAlgebra.ι ℂ (a, b)

def actU {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (p : FreeAlgebra ℂ (Fin n × Fin n)) (v : H) : H :=
  Finsupp.sum (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).coeff
    fun (w : FreeMonoid (Fin n × Fin n)) (c : ℂ) => c • dsigCW ε σ (w.toList.map unitM) v

end RealPlaces

def DSInfCharCap : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDS ε lam σ →
    ∀ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ, ∀ Y : ℂ,
      actU ε σ (Formalism.REAL.qdet (Egl n) (Y + ((n : ℂ) - 1) / 2)) v =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v

end PI.DSInfCharCap
end
end

-- bundled from Formalism.PeriodIntegrals.HookBound
section
noncomputable section

namespace PI

def stdGram {N : ℕ} (ν : Fin N → ℕ) {r : ℕ} (e : Module.Basis (Fin r) ℤ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν)) :
    Matrix (Fin r) (Fin r) ℚ :=
  Matrix.of fun i j =>
    Formalism.GradedWeylDivisibility.fockQ (MvPolynomial.map (Int.castRingHom ℚ) (e i : MvPolynomial (Fin N × Fin N) ℤ))
              (MvPolynomial.map (Int.castRingHom ℚ) (e j : MvPolynomial (Fin N × Fin N) ℤ)) /
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν)

def MuStd {N : ℕ} (ν : Fin N → ℕ) (μ : ℝ) : Prop :=
  ∃ (r : ℕ) (e : Module.Basis (Fin r) ℤ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν)), 0 < r ∧
    μ = -Real.log ((stdGram ν e).det : ℝ) / r

def cNu {N : ℕ} (ν : Fin N → ℕ) : ℝ :=
  (Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl ν) : ℝ) / ∏ l, ((ν l).factorial : ℝ)

def HookBound : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (ν : Fin N → ℕ), Antitone ν →
    1 ≤ cNu ν ∧ cNu ν ≤ ((ν ⟨0, hN⟩ : ℝ) + N) ^ (N * (N - 1) / 2)

def StdSlopeLow : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (μ : ℝ), Antitone ν → MuStd ν μ →
    -((∑ l, (ν l : ℝ)) * Real.log N + Real.log (cNu ν)) ≤ μ

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.NUnimodLoc
section
noncomputable section

open Matrix MeasureTheory

namespace PI.NUnimodLoc

abbrev uMat {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

section Real

variable {n r : ℕ}

def hJ (ε : Fin n → Bool) (x y : Fin n → ℂ) : ℂ := star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)

def spanLt (e : Fin r → Fin n → ℂ) (a : ℕ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (e '' {b | b.1 < a})

def InS (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) ∧ (g - 1) *ᵥ z ∈ spanLt e r

def InN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  InS e z g ∧ ∀ y, (∀ a, hJ ε (e a) y = 0) → (g - 1) *ᵥ y ∈ spanLt e r

end Real

structure IsFrameJ {r k : ℕ} (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 : Fin (2 * r + k + 1) → ℂ) : Prop where
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ff : ∀ a b, hJ ε (f a) (f b) = 0
  ef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0
  ez : ∀ a, hJ ε (e a) z0 = 0
  fz : ∀ a, hJ ε (f a) z0 = 0
  zz : hJ ε z0 z0 = -1
  ww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0
  ew : ∀ c a, hJ ε (e c) (wf a) = 0
  fw : ∀ c a, hJ ε (f c) (wf a) = 0
  zw : ∀ a, hJ ε z0 (wf a) = 0

def NUnimodLoc : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 z : Fin (2 * r + k + 1) → ℂ) (c : ℂ),
    IsFrameJ ε e f wf z0 → c ≠ 0 → z0 = c • z →
    ∀ μ : Measure (Formalism.REAL.UJ ε), SigmaFinite μ → μ ≠ 0 → μ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}ᶜ = 0 →
      (∀ s ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}, μ.map (fun x => s * x) = μ) →
      ∀ s ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}, μ.map (fun x => x * s) = μ

end PI.NUnimodLoc
end
end

-- bundled from Formalism.PeriodIntegrals.QmBorderES
section
namespace PI

def QmBorderES : Prop := BorderE ∧ BorderS

end PI
end

-- bundled from Formalism.PeriodIntegrals.QmBorderFull
section
namespace PI

def QmBorderFull : Prop := BorderFull

end PI
end

-- bundled from Formalism.PeriodIntegrals.QmColExp
section
namespace PI

def QmColExp : Prop := ExpFirstCol ∧ ExpLastCol

end PI
end

-- bundled from Formalism.PeriodIntegrals.QmMove
section
namespace PI

def QmMove : Prop := MoveVec ∧ MoveCov

end PI
end

