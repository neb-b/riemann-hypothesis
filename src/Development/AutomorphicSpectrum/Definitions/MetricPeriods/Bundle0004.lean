module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField Matrix MeasureTheory GlobalTheory.CompanionTheory.Ar GroundTheory.Automorphic GroundTheory.Heights₂.Heights.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

structure GroupDict (F : UnivFam (E := E) Ψ j j' n g Λ) where

  h : HermitianForm (maximalRealSubfield E) E (Fin (j + j') → E)

  e : Λ →+ (Fin (j + j') → E)
  e_inj : Function.Injective e
  e_smul : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x

  Dn : ℕ
  integral : IsDIntegral h Dn e.range
  orth : ∀ x y, h.toSesq (e x) (e y) = 0 ↔ ∀ a : 𝓞 E, F.form (a • x) y = 0

  M : Majorant h (Pi.basisFun E (Fin (j + j')))

  κ : ℝ
  κ_pos : 0 < κ

  π : archUnitary h (Pi.basisFun E (Fin (j + j'))) → Fin n → ℂ
  π_cont : Continuous π
  π_range : Set.range π = ballDom F.q
  π_fibre : ∀ a b, π a = π b ↔ a⁻¹ * b ∈ M.stab
  len : ∀ a x, (F.R (π a)).normSq x = κ * M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (e x))) ^ 2

  α : latticeStab h e.range ≃* autGrp (E := E) F.form
  α_eq : ∀ γ x, e ((α γ).1 x) = ((γ : h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (e x)
  α_act : ∀ (γ : latticeStab h e.range) a,
    (F.R (π a)).EqvBy (F.R (π (archEmbed h (Pi.basisFun E (Fin (j + j'))) γ * a))) (α γ).1
  act : ∀ a₀, ∃ (A : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ A (ballDom F.q) ∧
    DifferentiableOn ℂ G (ballDom F.q) ∧ (∀ a, π (a₀ * a) = A (π a)) ∧
    ∀ t ∈ ballDom F.q, ballPot F.q (A t) = ballPot F.q t + (G t).re

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsAdapted
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights TensorProduct

structure LinPt (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] (V : Type) [AddCommGroup V] [Module L V]
    [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] where

  ρ : 𝓞 E →+* Module.End L V

  σ : Ψ ⊕ Ψ → (𝓞 E →+* L)
  σ_bij : Function.Bijective σ
  σ_inj : ∀ s, Function.Injective (σ s)

  Λ : Submodule (𝓞 L) V
  fg : Λ.FG
  span : Submodule.span L (Λ : Set V) = ⊤
  stable : ∀ a, ∀ x ∈ Λ, ρ a x ∈ Λ

  I : AddSubgroup V
  I_le : ∀ x ∈ I, x ∈ Λ
  I_stable : ∀ a, ∀ x ∈ I, ρ a x ∈ I
  I_basis : ∃ (r : ℕ) (e : Fin r → V), LinearIndependent L e ∧ AddSubgroup.closure (Set.range e) = I

  Bq : HermitianBundle.{0} L

  f : Λ →ₗ[𝓞 L] Bq.carrier
  ker : ∀ x : Λ, f x = 0 ↔ (x : V) ∈ Submodule.span (𝓞 L) (I : Set V)
  full : ∀ y : Bq.carrier, ∃ (a : 𝓞 L) (x : Λ), a ≠ 0 ∧ f x = a • y
  orth : ∀ s s', s ≠ s' → OrthAt Bq (((eigSp ρ (σ s)).restrictScalars (𝓞 L)).comap Λ.subtype |>.map f)
    (((eigSp ρ (σ s')).restrictScalars (𝓞 L)).comap Λ.subtype |>.map f)

namespace LinPt

variable {E L Ψ : Type} [Field E] [NumberField E] [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V)

def eig (s : Ψ ⊕ Ψ) : Submodule (𝓞 L) V := A.Λ ⊓ (eigSp A.ρ (A.σ s)).restrictScalars (𝓞 L)

def tor (s : Ψ ⊕ Ψ) : Submodule (𝓞 L) V := Submodule.span (𝓞 L) (A.I : Set V) ⊓ (eigSp A.ρ (A.σ s)).restrictScalars (𝓞 L)

def img (s : Ψ ⊕ Ψ) : Submodule (𝓞 L) A.Bq.carrier := ((A.eig s).comap A.Λ.subtype).map A.f

def fam (s : Ψ ⊕ Ψ) {r k : ℕ} (v : Fin r → V) (q : Fin k → A.Λ) : Fin (r + k) → V :=
  Fin.append (fun a => eigComp A.ρ (A.σ s) (v a)) fun c => (q c : V)

def IsAdapted (s : Ψ ⊕ Ψ) {r k : ℕ} (v : Fin r → V) (q : Fin k → A.Λ) : Prop :=
  LinearIndependent L (A.fam s v q) ∧ Submodule.span L (Set.range (A.fam s v q)) = eigSp A.ρ (A.σ s)

def gramDet (ι : L →+* ℂ) {k : ℕ} (q : Fin k → A.Λ) : ℝ :=
  (Matrix.of fun c c' => (A.Bq.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] A.f (q c))
    ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] A.f (q c'))).det.re

def labDeg (s : Ψ ⊕ Ψ) (F : Submodule (𝓞 L) V) {r k : ℕ} (v : Fin r → V) (q : Fin k → A.Λ) : ℝ :=
  (logIdx F (A.fam s v q) - (∑ ι : L →+* ℂ, Real.log (A.gramDet ι q)) / 2) / Module.finrank ℚ L

def phiDeg [Fintype Ψ] (lab : Ψ → Ψ ⊕ Ψ) (F : Ψ → Submodule (𝓞 L) V) {r k : ℕ} (v : Fin r → V)
    (q : Ψ → Fin k → A.Λ) : ℝ :=
  ∑ τ, A.labDeg (lab τ) (F τ) v (q τ) - Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) / 2 +
    Fintype.card Ψ * r / 2 * Real.log (4 * Real.pi)

end LinPt

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

