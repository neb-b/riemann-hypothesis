module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPAmbOfTiesD
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.Bundle0004
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkThindEq
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Formalism.LocalToGlobal.Columns.ChainOneOk
public import Formalism.LocalToGlobal.Columns.ReductionExistsInLatticeStabilizerHolds
public import Formalism.LocalToGlobal.Columns.Bundle0031
public import Formalism.LocalToGlobal.Columns.BlockTriangularMulVecMemPartialFlag
public import Formalism.LocalToGlobal.Columns.ReducedMatrixExtensionEntry
public import Formalism.LocalToGlobal.Columns.Bundle0033
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.SymLevEnt

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker.Cd.CarC

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {G : ChGlob X R.m} (u : Pr.Word)
  {D : Car} (s : Cd.Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ) (χ : Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem thIndEq_ambOf_car (hok : s.Ok) (hcc : Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : Cd.TaylorLogMetric.IsChi D χ)
    {a b : ℕ} (ha : Even a) (hb : Even b) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) {D' : ℕ} (hD : 0 < D')
    (hLa : (Cd.ambOf s B χ cD : Amb X).LaHyp a b Sall) : (Cd.ambOf s B χ cD : Amb X).ThIndEq a b Sall D' :=
  theta_coset_indicator_natural X _ a b Sall D' (ambOf_conj s B χ cD hok) hD hLa
    (eqLaw_ambOf_of s B χ cD hok (Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SqG.eqP_car B hcc hδ χ hχ) ha hb)

theorem thEquivP_ambOf_tiesD (hok : s.Ok) (hcc : Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hχ : Cd.TaylorLogMetric.IsChi D χ)
    (hX : X.AbelianUnramifiedExtensionConditions) (hPr : Pr.Ok) (hsel : IsSel X sel)
    (hg : XiOffG Pr (mu : Chr X.F X.E X.K)) (hT : LawTies W Ch sel mu cst G) (hTu : 0 < Pr.T u) {i : ℕ} (hi : i < R.m) (e : X.Tau → ℤ)
    (he : ∀ τ, (e τ : ℚ) = (W.row τ).e ⟨i, hi⟩)
    (hLa : (Cd.ambOf s B χ cD : Amb X).LaHyp (R.N i) (R.N (i + 1)) (Sall sel mu u))
    (hrat : (Cd.ambOf s B χ cD : Amb X).JetsRatDeg (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (stepDeg W u i)) :
    ThEquivP (stepT W Ch sel mu cst (Cd.ambOf s B χ cD) u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      (colValF W sel mu u i).rho (colValF W sel mu u (i + 1)).rho := by
  have he' : ∀ τ, (e τ : ℚ) = (W.hc u τ).e ⟨i, hi⟩ := by
    intro τ
    rw [he τ, ← hT.2.2.2 u τ]
    rfl
  exact thEquivP_stepT_ofD W Ch sel mu cst (Cd.ambOf s B χ cD) u hi e he' hrat (eOmega_ambOf_of s B χ cD (B.stdOK hcc hδ) _ _)
    (thIndEq_ambOf_car s B χ cD hok hcc hδ hχ (even_rankN R i) (even_rankN R (i + 1)) _ (modulus_pos sel mu cst u hTu) hLa)
    (chiLaw_ambOf_of s B χ cD hok hχ (even_rankN R i) (even_rankN R (i + 1)))
    (muProdLaw_of hX hPr hsel hg hT i hi e he _) (muProdLaw_of hX hPr hsel hg hT i hi e he _)

end Step

section All

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {u : Pr.Word} {m2 : ℕ}
  {D : Car} (s : Cd.Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ) (χ : Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

end All

end Formalism.L2.Ker.Cd.CarC
