module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.HeightsSetAll

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplierLine
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.LineModel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem mem_of_aeval (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) (h0 : aeval y g = 0) : g ∈ mCoordIdeal y := by
  show g ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker, ProjLine.mConeMap_eq_of_isMultiHomog y hg, h0, map_zero, zero_mul]

theorem eval_map_eq (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    eval z (map (Int.castRingHom ℂ) f) = aeval z f := by
  rw [eval_map, aeval_def]; rfl

theorem ptsOver_complex (P : Ideal (MRing ι)) : ptsOver ℂ P = mcPts P := by
  ext z
  simp only [ptsOver, mcPts, Set.mem_setOf_eq, eval_map_eq]

theorem hasVal_unique (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) {𝕜 : Type} [Field 𝕜]
    {z : (Σ k, ι k) → 𝕜} (hz : z ∈ ptsOver 𝕜 (mCoordIdeal y)) {w w' : 𝕜}
    (h : HasVal y a s z w) (h' : HasVal y a s z w') : w = w' := by
  obtain ⟨dg, dh, g, h, hg, hh, hd, e1, n1, v1⟩ := h
  obtain ⟨dg', dh', g', h', hg', hh', hd', e1', n1', v1'⟩ := h'
  have hdeg : dg' + dh = dg + dh' := by
    funext k
    have := hd k; have := hd' k
    simp only [Pi.add_apply]; omega
  have hom : IsMultiHomog (g * h' + -(g' * h)) (dg + dh') :=
    ProjLine.mhAdd (ProjLine.mhMul hg hh') (ProjLine.mhNeg (hdeg ▸ ProjLine.mhMul hg' hh))
  have h0 := hz.2 _ (mem_of_aeval y hom (by simp only [map_add (f := _), map_neg, map_mul, e1, e1']; ring))
  simp only [map_add (f := _), map_neg, map_mul, v1, v1'] at h0
  have : (w - w') * (aeval z h * aeval z h') = 0 := by linear_combination h0
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (mul_ne_zero n1 n1'))

end General

open ProjLine

end GlobalTheory.CompanionTheory.Ar.Small.LineModel
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsFundSet
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField Matrix MeasureTheory GlobalTheory.CompanionTheory.Ar
open scoped ComplexOrder

section Ball

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

def ballMat (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (τ : Ψ) : Matrix (Fin j) (Fin j') ℂ :=
  Matrix.of fun a b => t (q (τ, a, b))

def ballDom (q : Ψ × Fin j × Fin j' ≃ Fin n) : Set (Fin n → ℂ) :=
  {t | ∀ τ, (1 - (ballMat q t τ)ᴴ * ballMat q t τ).PosDef}

def ballPot (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ℝ :=
  -∑ τ, Real.log (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re

def ballDens (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ℝ := Real.exp ((j + j' : ℕ) * ballPot q t)

end Ball

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

def autGrp (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) : Subgroup (Λ ≃ₗ[𝓞 E] Λ) where
  carrier := {γ | ∀ x y, form (γ x) (γ y) = form x y}
  one_mem' _ _ := rfl
  mul_mem' {a b} ha hb x y := by
    show form (a (b x)) (a (b y)) = form x y
    rw [ha, hb]
  inv_mem' {a} ha x y := by
    have h := ha (a.symm x) (a.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h
    exact h.symm

def RiemLat.HasSig {Ψ : Type} (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (j j' : ℕ) : Prop :=
  ∀ τ, Module.finrank ℂ (eigSp R.B (σ τ)) = j' ∧ Module.finrank ℂ (eigSp R.B ((starRingEnd ℂ).comp (σ τ))) = j

def RiemLat.EqvBy (R R' : RiemLat E g Λ) (γ : Λ ≃ₗ[𝓞 E] Λ) : Prop :=
  ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, R'.P (γ x) = h (R.P x)


variable (E) in
structure UnivFam (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] where

  q : Ψ × Fin j × Fin j' ≃ Fin n

  σ : Ψ → (𝓞 E →+* ℂ)
  cm : IsCMFam σ

  form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ

  R : (Fin n → ℂ) → RiemLat E g Λ
  form_eq : ∀ t, (R t).form = form
  hol : IsHolFam (ballDom q) R
  sig : ∀ t ∈ ballDom q, (R t).HasSig σ j j'

  b : Ψ → Fin j' → (Fin n → ℂ) → Fin g → ℂ
  frames : IsEigFrames (ballDom q) (fun t => (R t).B) σ b
  logDet_eq : ∀ t ∈ ballDom q, (R t).logDet (fun τ i => b τ i t) = ballPot q t
  univ : ∀ R' : RiemLat E g Λ, R'.form = form → R'.HasSig σ j j' → ∃! t, t ∈ ballDom q ∧ (R t).EqvBy R' 1

namespace UnivFam

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (F : UnivFam E Ψ j j' n g Λ)

def Eqv (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (t t' : Fin n → ℂ) : Prop := ∃ γ ∈ Γ, (F.R t).EqvBy (F.R t') γ

def IsFundSet (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)) : Prop :=
  MeasurableSet FF ∧ FF ⊆ ballDom F.q ∧ (∀ t ∈ ballDom F.q, ∃ t' ∈ FF, F.Eqv Γ t t') ∧
    ∀ t ∈ FF, ∀ t' ∈ FF, F.Eqv Γ t t' → t = t'

def IsArith (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) : Prop := Γ ≤ autGrp F.form ∧ Γ.relIndex (autGrp F.form) ≠ 0

end UnivFam

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt

variable {K : Type} [Field K] [NumberField K]

def sqAt (E : HermitianBundle.{0} K) (σ : K →+* ℂ) (x : Fibre σ E.carrier) : ℝ :=
  ((E.metric.form σ).inner x x).re

def OrthAt (E : HermitianBundle.{0} K) (F F' : Submodule (𝓞 K) E.carrier) : Prop :=
  ∀ (σ : K →+* ℂ), ∀ x ∈ F, ∀ y ∈ F',
    (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] y) = 0

structure SatFlag (E : HermitianBundle.{0} K) (r : ℕ) where

  F : Fin (r + 1) → Submodule (𝓞 K) E.carrier
  mono : Monotone F
  sat : ∀ i, E.Saturated (F i)
  rank : ∀ i, E.rank (F i) = i

namespace SatFlag

variable {E : HermitianBundle.{0} K} {r : ℕ}

def top (A : SatFlag E r) : Submodule (𝓞 K) E.carrier := A.F (Fin.last r)

def grDeg (A : SatFlag E r) (i : Fin r) : ℝ := E.normDegree (A.F i.succ) - E.normDegree (A.F i.castSucc)

end SatFlag

structure FlagPair (E : HermitianBundle.{0} K) (Ψ : Type) (j k : ℕ) where

  W : Ψ → SatFlag E j

  S : Ψ → SatFlag E k

namespace FlagPair

variable {E : HermitianBundle.{0} K} {Ψ : Type} [Fintype Ψ] {j k : ℕ}

def lamDeg (A : FlagPair E Ψ j k) (lam : Ψ → Fin (j + k) → ℝ) : ℝ :=
  ∑ τ, (-(∑ i : Fin j, lam τ (Fin.castAdd k i) * (A.W τ).grDeg i) +
    ∑ i : Fin k, lam τ (Fin.natAdd j i) * (A.S τ).grDeg i.rev)

def flatDeg (A : FlagPair E Ψ j k) (τ : Ψ) : ℝ := E.normDegree (A.W τ).top - E.normDegree (A.S τ).top

def part (A : FlagPair E Ψ j k) : Ψ ⊕ Ψ → Submodule (𝓞 K) E.carrier :=
  Sum.elim (fun τ => (A.W τ).top) (fun τ => (A.S τ).top)

def IsOrthFull (A : FlagPair E Ψ j k) : Prop :=
  (∀ a b, a ≠ b → OrthAt E (A.part a) (A.part b)) ∧ Fintype.card Ψ * (j + k) = Module.finrank (𝓞 K) E.carrier

end FlagPair

end GlobalTheory.CompanionTheory.Ar
end
end

