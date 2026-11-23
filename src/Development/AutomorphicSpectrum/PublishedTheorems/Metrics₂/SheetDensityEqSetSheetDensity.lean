module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

namespace CxInt

section Integral

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

def setFibre (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (y : Fin e → ℂ) : Set (((k : K) → ι k) → ℂ) :=
  {w | ∃ z ∈ S, segre z = w ∧ Ψ w = Fin.cons 1 y}

def IsSetSheet (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) : Prop :=
  segre (γ y) = w ∧ ∀ᶠ y' in 𝓝 y,
    DifferentiableAt ℂ γ y' ∧ γ y' ∈ S ∧ Ψ (segre (γ y')) = Fin.cons 1 y'

def setSheetDensity (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : ℝ := by
  classical
  exact if hγ : ∃ γ, IsSetSheet S Ψ y w γ then
    g (hγ.choose y) * maDensity (fun j y' => φ j (hγ.choose y')) y
  else 0

def IsSetGoodProj (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Prop :=
  ∀ z ∈ S, Ψ (segre z) ≠ 0

def logNormC (A : HermLine ι) (s : MRingOver ℂ ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (‖eval z s‖ / A.h z)

def IsCxVar (Q : Ideal (MRingOver ℂ ι)) (d : ℕ) : Prop :=
  Nonempty K ∧ IsMultiProjPrime Q ∧
    ringKrullDim (MRingOver ℂ ι ⧸ Q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

theorem sheetDensity_eq_setSheetDensity (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    sheetDensity P Ψ = setSheetDensity (mcPts P) Ψ := rfl

end Integral

theorem mcPts_eq_conePts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    mcPts P = ReciprocityTheory.AnForm.R.conePts (P.map (map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι)) := by
  ext z
  simp only [mcPts, ReciprocityTheory.AnForm.R.conePts, Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun h f hf => ?_, fun h f hf => h _ (Ideal.mem_map_of_mem _ hf)⟩
  have hle : P ≤ Ideal.comap (map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι)
      (RingHom.ker (eval z)) :=
    fun g hg => Ideal.mem_comap.mpr (RingHom.mem_ker.mpr (h g hg))
  exact RingHom.mem_ker.mp (Ideal.map_le_of_le_comap hle hf)

end CxInt


end GlobalTheory.CompanionTheory.Ar.Pub
