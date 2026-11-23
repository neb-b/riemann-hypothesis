module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open Formalism.IndefR.Lift (liftInt)
open GlobalTheory.Cusp (constTerm frameFlag)
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def adel {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin m) (Fin n) (AE D) := x.map (incA D)

abbrev ct {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin n) (Fin m) D.host.E :=
  Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) x

def IsWittStep (B B' : HSp D) (t : ℕ) (ι : B'.V →ₗ[D.host.E] B.V) (C : Matrix (Fin B.rank) (Fin t) D.host.E) : Prop :=
  B'.rank + 2 * t = B.rank ∧ HSpace.IsIsomEmb B' B ι ∧ IsIsoSub B C ∧ ct (frameMat B B' ι) * B.gram * C = 0

theorem isWittLower_iff (B B' : HSp D) (t : ℕ) : IsWittLower B B' t ↔ ∃ ι C, IsWittStep B B' t ι C :=
  ⟨fun ⟨h, ι, h1, C, h2, h3⟩ => ⟨ι, C, h, h1, h2, h3⟩, fun ⟨ι, C, h, h1, h2, h3⟩ => ⟨h, ι, h1, C, h2, h3⟩⟩

theorem exists_isWittStep_iff (B : HSp D) (t : ℕ) :
    (∃ B' ι C, IsWittStep B B' t ι C ∧ B'.SigOK) ↔ t ≤ GlobalTheory.Cusp.wittIndex B := by
  rw [← GlobalTheory.Cusp.exists_isWittLower_iff]
  exact ⟨fun ⟨B', ι, C, h, h'⟩ => ⟨B', (isWittLower_iff _ _ _).2 ⟨ι, C, h⟩, h'⟩,
    fun ⟨B', h, h'⟩ => let ⟨ι, C, h⟩ := (isWittLower_iff _ _ _).1 h; ⟨B', ι, C, h, h'⟩⟩

def IsLeviElt (B B' : HSp D) {t : ℕ} (ι : B'.V →ₗ[D.host.E] B.V) (C : Matrix (Fin B.rank) (Fin t) D.host.E)
    (a : GL (Fin t) (AE D)) (h' : GA D B') (m : GA D B) : Prop :=
  HMul.hMul (Formalism.L2.Theta.mt B m) (adel C) = HMul.hMul (adel C) a.val ∧
    HMul.hMul (Formalism.L2.Theta.mt B m) (adel (frameMat B B' ι)) =
      HMul.hMul (adel (frameMat B B' ι)) (Formalism.L2.Theta.mt B' h')

def IsAutCharGL (t : ℕ) (μ : GL (Fin t) (AE D) →* Circle) : Prop :=
  Continuous μ ∧ ∀ a : GL (Fin t) D.host.E, μ (Matrix.GeneralLinearGroup.map (incA D) a) = 1

def IsAutCharU (V : HSp D) (ξ : GA D V →* Circle) : Prop := Continuous ξ ∧ ∀ γ ∈ GQ V, ξ γ = 1

def detPow {t : ℕ} (a : GL (Fin t) (AE D)) (n : ℕ) : ℝ :=
  (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((n : ℝ) / 2)

def ratMx (D : D7) (m n : ℕ) : AddSubgroup (Mx D m n) :=
  ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range

section Target

variable (ψ : AddChar (AF D.host.F) ℂ) (S T T' : HSp D) {t : ℕ} (ι : T'.V →ₗ[D.host.E] T.V)
  (C : Matrix (Fin T.rank) (Fin t) D.host.E)

def resT (μ : Measure (Mx D t S.rank)) (𝓖 : Set (Mx D t S.rank)) (φ : WO S T → ℂ) : WO S T' → ℂ :=
  fun w' => ∫ y in 𝓖, φ (adel C * (y : Matrix (Fin t) (Fin S.rank) (AE D)) +
    adel (frameMat T T' ι) * (w' : Matrix (Fin T'.rank) (Fin S.rank) (AE D))) ∂μ

end Target

section Source

variable (ψ : AddChar (AF D.host.F) ℂ) (S S' T : HSp D) {t : ℕ} (ι : S'.V →ₗ[D.host.E] S.V)
  (C : Matrix (Fin S.rank) (Fin t) D.host.E)

def resS (μ : Measure (Mx D T.rank t)) (𝓖 : Set (Mx D T.rank t)) (φ : WO S T → ℂ) : WO S' T → ℂ :=
  fun w' => ∫ y in 𝓖, φ ((y : Matrix (Fin T.rank) (Fin t) (AE D)) * adel (ct C * S.gram) +
    (w' : Matrix (Fin T.rank) (Fin S'.rank) (AE D)) * adel (S'.gram⁻¹ * ct (frameMat S S' ι) * S.gram)) ∂μ

end Source

end GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)

def stdParabolic (k : Type) [Field k] (r a : ℕ) : Subgroup (GL (Fin r) k) where
  carrier := {g | ∀ i j : Fin r, j.val < a → a ≤ i.val → (g : Matrix (Fin r) (Fin r) k) i j = 0}
  one_mem' := fun i j hj hi => Matrix.one_apply_ne (by rintro rfl; omega)
  mul_mem' := fun {g h} hg hh i j hj hi => by
    rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l.val < a
    · rw [hg i l hl hi, zero_mul]
    · rw [hh l j hj (not_lt.1 hl), mul_zero]
  inv_mem' := fun {g} hg i j hj hi => by
    have hb : (g : Matrix (Fin r) (Fin r) k).BlockTriangular fun l => if l.val < a then (0 : ℕ) else 1 := by
      intro i j h
      by_cases h1 : j.val < a <;> by_cases h2 : i.val < a <;> simp [h1, h2] at h
      exact hg i j h1 (not_lt.1 h2)
    letI := g.invertible
    have := Matrix.blockTriangular_inv_of_blockTriangular hb
    rw [Matrix.coe_units_inv]
    exact this (by simp [hj, not_lt.2 hi])

def InConjParabolic {k : Type} [Field k] {r : ℕ} (H : Subgroup (GL (Fin r) k)) (a : ℕ) : Prop :=
  ∃ g : GL (Fin r) k, ∀ p ∈ H, g⁻¹ * p * g ∈ stdParabolic k r a

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def parAt {D : D7} {V : HSp D} (𝔉 : IsoFlag V) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) : Subgroup (GL (Fin V.rank) (Fv D.host.F v)) :=
  (PLoc 𝔉 v).map (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))

def ParabolicAtSplitPlaces : Prop :=
  ∀ (D : D7) (V : HSp D), Odd V.rank → ∀ (T : TypeDataG V) (𝔉 : IsoFlag V), 𝔉.Proper →
    ∃ a : ℕ, 0 < a ∧ 2 * a + 1 ≤ V.rank ∧ ∀ v : T.S,
      InConjParabolic (parAt 𝔉 (T.frame v)) a ∧ InConjParabolic (parAt 𝔉 (T.frame v)) (V.rank - a)

def UnipIntegralsVanish {D : D7} {V : HSp D} (𝔉 : IsoFlag V) (f : GA D V → ℂ) : Prop :=
  ∀ (ν : Measure (NA 𝔉)) [ν.IsHaarMeasure] (x y : GA D V),
    Integrable (fun n : NA 𝔉 => f (x * n * y)) ν ∧ ∫ n : NA 𝔉, f (x * n * y) ∂ν = 0

def TestFnConstTermVanish : Prop :=
  ∀ (D : D7) (V : HSp D), Odd V.rank → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V), HypH (k := fun v : T.S => ResF v.1) T.τ → ∀ (U : AuxiliaryPlaceHermitianSpace V)
    (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) [∀ w, (μa w).IsHaarMeasure]
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) [∀ v, (μf v).IsHaarMeasure]
    (f : GA D V → ℂ), IsTestFnG M T U μa μf f →
    ∀ 𝔉 : IsoFlag V, 𝔉.Proper → UnipIntegralsVanish 𝔉 f ∧ UnipIntegralsVanish 𝔉 (starFn f)

def ParabolicAndConstTerm : Prop := ParabolicAtSplitPlaces ∧ TestFnConstTermVanish

end GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
section
noncomputable section

open MeasureTheory
open Formalism.REAL (UJ)
open Formalism.MainNotions.S (IsURepOn UJset allPos)
open GlobalTheory.Dec (HasInfChar IsSqIntIrr UEquiv)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open GlobalTheory.OpTrace (HasTrace repOp)
open GlobalTheory.RealInd (IsIrrAdm groupRep)

namespace GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation

def HasWideGaps {r : ℕ} (lam : Fin r → ℤ) : Prop :=
  StrictAnti lam ∧ ∀ i j : Fin r, (j : ℕ) = i + 1 → (r : ℤ) ≤ lam i - lam j

def IsDiscreteWithInfChar {r : ℕ} (ε : Fin r → Bool) (lam : Fin r → ℤ) {X : Type} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] (D : Matrix (Fin r) (Fin r) ℂ → (X →L[ℂ] X)) : Prop :=
  IsSqIntIrr ε D ∧ HasInfChar ε (fun a => (lam a : ℂ)) D

def PseudoCoeffSeparation : Prop :=
  ∀ (r : ℕ), Odd r → ∀ (ε : Fin r → Bool) (lam : Fin r → ℤ), HasWideGaps lam →
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
      (D : Matrix (Fin r) (Fin r) ℂ → (X →L[ℂ] X)) (hD : IsDiscreteWithInfChar ε lam D)
      (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (f : UJ ε → ℂ), IsPseudoCoeff (ujMat ε) μ (ujRep hD.1.2.2.1) f →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
      (π : Matrix (Fin r) (Fin r) ℂ → (V →L[ℂ] V)) (hπ : IsIrrAdm ε π) (c : ℂ),
      HasTrace (repOp (groupRep ε hπ.2.1.1) μ f) c → c ≠ 0 →
        HasInfChar ε (fun a => (lam a : ℂ)) π ∧ (IsURepOn (UJset ε) π → UEquiv ε π D ∧ c = 1)

end GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TraceKernelDecomposition
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.Mem.Th
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceKernelDecomposition

section Core

variable {X : Type} [MeasurableSpace X] {ν : Measure X}

def HasRows (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (β : X → Lp ℂ 2 ν) : Prop :=
  ∀ φ : Lp ℂ 2 ν, B φ =ᵐ[ν] fun x => ⟪β x, φ⟫_ℂ

def TraceIsDiagonal (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (K : X → X → ℂ) : Prop :=
  IsTraceClass T ∧ Integrable (fun x => K x x) ν ∧ trace T = ∫ x, K x x ∂ν

end Core

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsCcInf (θ : InfF D) (V : HSp D) (f : GA D V → ℂ) : Prop :=
  Continuous f ∧ HasCompactSupport f ∧
    (∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ g, f (g * k) = f g) ∧
    ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

def MapsIntoCusp (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA D V → ℂ) : Prop :=
  ∀ F : DividedPowerChartLift V μ, RopG V μ f F ∈ L2cusp V μ

end GlobalTheory.IndefiniteRowSideFullHecke.TraceKernelDecomposition

end
end

