module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ChiLawAmbOf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0009
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

section An

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem eNat_analytic (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (hθ : AnalyticOnNhd ℂ B.thMM Set.univ) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    AnalyticOnNhd ℂ (B.eNat χ N N' L L') Set.univ := by
  have hT := entireStatements_holds
  have h0 : AnalyticOnNhd ℂ (B.thZero N N') Set.univ := hT.2 _ B.thMM N N' hθ
  have h1 : AnalyticOnNhd ℂ (B.thHalf N N' L) Set.univ := hT.1 _ _ _ _ _ _ _ _ h0
  have h2 : AnalyticOnNhd ℂ (B.thMoved N N' L L') Set.univ := hT.1 _ _ _ _ _ _ _ _ h1
  intro z _
  exact analyticAt_const.mul (h2 z (Set.mem_univ _))

variable {X : Fields} (s : Seam D X) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem eOmega_ambOf {σ₀ : X.K →+* ℂ} (hN : NatOk s cc δ χ cD σ₀) (a b : ℕ) : (ambOf s B χ cD : Amb X).EOmega a b := by
  obtain ⟨hcc, hδ, -, -, -, -, -⟩ := hN
  intro N N' _ _
  have hA := eNat_analytic B χ (Formalism.L2.KerInert.AlgP.thMM_analytic B (B.stdOK hcc hδ)) a b (s.lat N) (s.lat N')
  have hc : ContDiff ℂ ⊤ (B.eNat χ a b (s.lat N) (s.lat N')) := hA.contDiff
  exact hc.comp (contDiff_pi.2 fun τ => contDiff_apply ℂ _ (s.iT.symm τ))

end An

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word)
  {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

end Main

end Formalism.L2.Ker
