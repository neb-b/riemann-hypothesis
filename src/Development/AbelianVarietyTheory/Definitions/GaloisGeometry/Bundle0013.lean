module

public import Mathlib
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0002
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.IsHypPair
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.RenameBlockSingleVariableSeries
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.HermitianForms.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetLL

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (thetaS phFF NormRel)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog at1 lgF)

namespace GlobalTheory.KerStd

def CurveData (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) : Prop :=
  5 ≤ l ∧ ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖ε‖ = 1 ∧ (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) ∧
    UnrOK (MaximalUnramifiedExtension l) l σ ∧ IsLawOfLog l F ∧
    ∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α

def HostLog (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) {n : Type} [Fintype n] (Θ : MvPowerSeries n ℂ_[l]) : Prop :=
  Formalism.DworkPowerSeriesWeights.Integral
    (Formalism.DworkPowerSeriesWeights.mvExp (∑ i : n, at1 i (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) : MvPowerSeries n ℂ_[l]) *
      (MvPowerSeries.subst (fun i : n => (at1 i (lgF ℂ_[l] l) : MvPowerSeries n ℂ_[l])) Θ : MvPowerSeries n ℂ_[l]))

abbrev HypPair {K : Type} [NormedField K] (σ : K →+* K) {E n : Type} [DecidableEq E] [Fintype n] (f f' : E → n → K) : Prop :=
  Formalism.L2.Th1.Top.IsHypPair σ f f'

def thOrth (D : D7) {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (F₀ : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    MvPowerSeries (Fin r) ℂ_[p] :=
  MvPowerSeries.subst (fun k : D.what₂.Tau × Fin N' × Fin N =>
    ∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * MvPowerSeries.X i) F₀

def HostAt {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime]
    (lam : Qbar →+* ℂ_[p]) : Prop :=
  ∃ (c : ℂ_[p]) (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)),
    ‖c‖ = 1 ∧ CurveData p g2 g3 s2 ε σ F ∧
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' L L' → ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        LocBasis D p (YYl D L L') b ∧ TaylorLogMetric.Orthonormal D b ∧
        ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → HostLog p g2 g3 s2 ε (thOrth D lam c b G)

theorem HostLog.iff_phSum (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) {n : Type} [Fintype n] (Θ : MvPowerSeries n ℂ_[l]) :
    HostLog l g2 g3 s2 ε Θ ↔ Formalism.DworkPowerSeriesWeights.Integral
      (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (Formalism.L2.Th1.Top.phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) *
        (MvPowerSeries.subst (fun i : n => (at1 i (lgF ℂ_[l] l) : MvPowerSeries n ℂ_[l])) Θ : MvPowerSeries n ℂ_[l])) :=
  Iff.rfl

theorem HostLog.constantCoeff_subst {K σ τ : Type} [Field K] [Finite σ] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ K) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f : MvPowerSeries τ K) = MvPowerSeries.constantCoeff f := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have e : f = (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) + MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by ring
  conv_lhs => rw [e]
  rw [MvPowerSeries.subst_add hs, map_add (f := _), MvPowerSeries.constantCoeff_subst_eq_zero hs ha (by simp), zero_add,
    MvPowerSeries.subst_C]
  simp

end GlobalTheory.KerStd
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
section
noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV NumberField IsDedekindDomain

abbrev StabDat {D : D7} {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) : Type :=
  ∀ i, C.cls i → Set (Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E × ℂ)

section Gen

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}

def LawAt (O : GL3Theta.LiftObj D C) (i : ℕ) (g : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E × ℂ) (f : C.Y i → ℂ) : Prop :=
  ∀ y y' : C.Y i, (∀ τ, O.frm i y τ = g.1.map (TaylorLogMetric.embT D τ) * O.frm i y' τ) → f y = g.2 * f y'

def FormsAre (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (O : GL3Theta.LiftObj D C)
    (G : StabDat C) : Prop :=
  (∀ i, i ≤ D.R.m → ∀ φ ∈ M.Fi i, ∀ c, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) (φ c)) ∧
  ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ φ : C.cls i → C.Y i → ℂ,
    φ ∈ M.Fi i ↔ ∀ c, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) (φ c) ∧ ∀ g ∈ G i c, LawAt O i g (φ c)

def TermLaw (O : GL3Theta.LiftObj D C) (i : ℕ) (c : C.cls i) (c' : C.cls (i + 1))
    (g : Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.host.E × ℂ) : Prop :=
  g.1.det ≠ 0 ∧ ∃ k : ℂ,
    (∀ z : TaylorLogMetric.VC D (D.R.N i) (D.R.N (i + 1)),
      O.Th i c c' (fun τ => (g.1.map (TaylorLogMetric.embT D τ) * Matrix.of (z τ) : Matrix _ _ ℂ)) = k * O.Th i c c' z) ∧
    g.2 = k * ∏ τ, TaylorLogMetric.embT D τ g.1.det ^ (-C.sDiv i τ)

end Gen

def matE {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) : Matrix (Fin n) (Fin n) D.host.E :=
  (LinearMap.toMatrix' γ.toLinearMap).map s.iE

end GlobalTheory.KerJ
end
end

