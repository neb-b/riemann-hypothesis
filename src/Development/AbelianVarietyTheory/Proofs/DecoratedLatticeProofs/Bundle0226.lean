module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsPeriodLatticeIff
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0074

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelAdaptedCharAbs
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW GlobalTheory.Core.Rk.SWQ
open Formalism.UG (IsUnifV qV Ov ordL diagJ)
open GlobalTheory.LFun (KGL toCompl IsSplitChart IsSatVecGL satEig)
open scoped Classical

noncomputable section

namespace GlobalTheory.Core.Rk.SecPar

end GlobalTheory.Core.Rk.SecPar

namespace GlobalTheory.Core.Rk.SecPar

open GlobalTheory.LFun

end GlobalTheory.Core.Rk.SecPar

namespace GlobalTheory.Core.Rk.SecPar
open GlobalTheory.LFun

theorem cw_incA {D : D7} {q : FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)} (h : w.under (𝓞 D.host.F) = q)
    (x : D.host.E) : cw h (incA D x) = algebraMap D.host.E (w.adicCompletion D.host.E) x := by
  show toCompl h (compFin _ _ q (1 ⊗ₜ x)) = _
  simp [compFin, toCompl]

end GlobalTheory.Core.Rk.SecPar

namespace GlobalTheory.Core.Rk.SecPar
open GlobalTheory.LFun

end GlobalTheory.Core.Rk.SecPar

namespace GlobalTheory.Core.Rk.SecPar
open GlobalTheory.LFun

end GlobalTheory.Core.Rk.SecPar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIff
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.ChartRat

variable {D : D7}

theorem mem_GF_iff {n : ℕ} (g : G D n) : g ∈ GF D n ↔ mat g ∈ ratMx D (n + n) (n + n) := by
  constructor
  · rintro ⟨γ, -, h⟩
    exact ⟨γ.1, congrArg Units.val h⟩
  · rintro ⟨γ, hγ⟩
    replace hγ : rat γ = mat g := hγ
    have h : γᴴ * Jst D n * γ = Jst D n := by
      apply rat_injective
      rw [rat_mul, rat_mul, rat_conjTranspose, hγ]
      exact g.2
    have hdet : γ.det ≠ 0 := by
      intro h0
      have hu : IsUnit (mat g).det := Matrix.isUnits_det_units _
      rw [← hγ, rat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at hu
      have h01 : (0 : AE D) = 1 := isUnit_zero_iff.1 hu
      exact zero_ne_one (incA_injective (D := D) (by rw [map_zero, map_one]; exact h01))
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero γ hdet, h, Units.ext hγ⟩

end GlobalTheory.StdUnn.ChartRat

namespace GlobalTheory.StdUnn

theorem chart_mem_GF_iff : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank,
    IsChart A μ κ → ∀ g, g ∈ GQ (dblSp A) ↔ κ g ∈ GF D A.rank := by
  intro D A μ hμ κ hκ g
  obtain ⟨-, hdet, -⟩ := _root_.GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ
  have hTi : rat (Tm A μ)⁻¹ * rat (Tm A μ) = 1 := by
    rw [← rat_mul, Matrix.nonsing_inv_mul _ hdet, rat_one]
  have hTi' : rat (Tm A μ) * rat (Tm A μ)⁻¹ = 1 := by
    rw [← rat_mul, Matrix.mul_nonsing_inv _ hdet, rat_one]
  have e1 : mat (κ g) = rat (Tm A μ)⁻¹ * (mt (dblSp A) g * rat (Tm A μ)) := by
    rw [← hκ g, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
  have e2 : mt (dblSp A) g = rat (Tm A μ) * mat (κ g) * rat (Tm A μ)⁻¹ := by
    rw [hκ g, Matrix.mul_assoc, hTi', Matrix.mul_one]
  rw [GlobalTheory.MixModel.mem_GQ_iff, ChartRat.mem_GF_iff]
  constructor
  · intro h
    rw [e1]
    exact ratMx_mul (rat_mem _) (ratMx_mul h (rat_mem _))
  · intro h
    rw [e2]
    exact ratMx_mul (ratMx_mul (rat_mem _) h) (rat_mem _)

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartSiegelLeviDetEq
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

open Matrix GlobalTheory.Doubling

theorem chart_lowerLeft_zero {D : D7} {n : ℕ} {g : G D n} (hg : g ∈ P D n) (i j : Fin n) :
    mat g (Fin.natAdd n i) (Fin.castAdd n j) = 0 := by
  have hx : (Pi.single (Fin.castAdd n j) 1 : Fin (n + n) → AE D) ∈ upperHalf D n := by
    rw [upperHalf, LinearMap.mem_ker]
    funext k
    rw [LinearMap.funLeft_apply, Pi.zero_apply, finSumFinEquiv_apply_right]
    exact Pi.single_eq_of_ne (fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega) _
  have h1 := (hg (Pi.single (Fin.castAdd n j) 1)).1 hx
  rw [upperHalf, LinearMap.mem_ker] at h1
  have h2 := congrFun h1 i
  rw [LinearMap.funLeft_apply, Pi.zero_apply, finSumFinEquiv_apply_right, mulVec_single_one] at h2
  exact h2

end GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn

open Matrix GlobalTheory.Doubling

theorem chart_levi_mul {D : D7} {A : HSp D} {μ : D.host.E} {κ : GA D (dblSp A) ≃* G D A.rank}
    (hκ : IsChart A μ κ) (p : GA D (dblSp A)) (hp : κ p ∈ P D A.rank) :
    leviMat finSumFinEquiv (mt (dblSp A) p) * rat A.gram⁻¹ = rat A.gram⁻¹ * blkA (mat (κ p)) := by
  ext i j
  have h := congrFun (congrFun (hκ p) (Fin.castAdd A.rank i)) (Fin.castAdd A.rank j)
  simp only [Matrix.mul_apply, Fin.sum_univ_add] at h
  simp only [Matrix.mul_apply, leviMat, blkA, toBlocks₁₁, toBlocks₁₂, Matrix.of_apply, submatrix_apply, add_mul,
    Finset.sum_add_distrib, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  simp only [Tm, rat, Matrix.map_apply, submatrix_apply, id, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inl, fromCols_apply_inr, dblDec, stackRows,
    fromRows_apply_inl, fromRows_apply_inr, chart_lowerLeft_zero hp, mul_zero, Finset.sum_const_zero, add_zero] at h
  simp only [Matrix.add_apply, Matrix.of_apply, add_mul, Finset.sum_add_distrib, rat, Matrix.map_apply]
  exact h.symm

end GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn

open Matrix GlobalTheory.Doubling

theorem chart_aP_eq_det : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank,
    IsChart A μ κ → ∀ (p : siegel A) (a : GL (Fin A.rank) (AE D)), blkA (mat (κ p)) = a.1 →
      aP A p = Matrix.GeneralLinearGroup.det a := by
  intro D A μ hμ κ hκ p a ha
  have hP : κ p ∈ P D A.rank := (_root_.GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P D A μ hμ κ hκ p).1 p.2
  have h1 := congrArg Matrix.det (chart_levi_mul hκ p hP)
  rw [ha, Matrix.det_mul, Matrix.det_mul] at h1
  have hu : IsUnit (rat (D := D) A.gram⁻¹).det := by
    rw [rat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    rw [Matrix.det_nonsing_inv]
    rw [Ring.inverse_eq_inv']
    exact inv_ne_zero (gram_det_ne A)
  refine Units.ext ?_
  change (leviMat finSumFinEquiv (mt (dblSp A) (p : GA D (dblSp A)))).det = a.1.det
  exact hu.mul_left_cancel (by rw [mul_comm]; exact h1)

end GlobalTheory.StdUnn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHZeroRight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ContrComb

variable {D : D7}

theorem symplOH_zero_right (S T : HSp D) (x : WO S T) : symplOH S T x 0 = 0 := by
  simp [symplOH, symplO, hO]

theorem symplOH_zero_left (S T : HSp D) (x : WO S T) : symplOH S T 0 x = 0 := by
  simp [symplOH, symplO, hO]

theorem heis_left {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (ψ : AddChar (AF D.host.F) ℂ) (l : Link B B'.L B'.ζ)
    (S : HSp D) (vL : VolM D B'.L.rank S.rank) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) (a : WO B.A S)
    (u : WO B.A S) (v : WO S B'.A) :
    heisO ψ B.A S a (fun u' => contr l S vL f₁ f₂ u' v) u =
      contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (a, 0)) f₁) f₂ u v := by
  simp only [heisO, contr]
  rw [← integral_const_mul]
  congr 1
  funext w
  have h1 : (B.o.resS S).symm (u, l.κ S w) + (B.o.resS S).symm (a, 0) = (B.o.resS S).symm (u + a, l.κ S w) := by
    rw [← map_add (f := _)]; simp
  rw [B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_right, add_zero, h1]
  ring

theorem heis_right {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (ψ : AddChar (AF D.host.F) ℂ) (l : Link B B'.L B'.ζ)
    (S : HSp D) (vL : VolM D B'.L.rank S.rank) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) (b : WO S B'.A)
    (u : WO B.A S) (v : WO S B'.A) :
    heisO ψ S B'.A b (contr l S vL f₁ f₂ u) v =
      contr l S vL f₁ (heisO ψ S B'.V₀ ((B'.o.resT S).symm (b, 0)) f₂) u v := by
  simp only [heisO, contr]
  rw [← integral_const_mul]
  congr 1
  funext w
  have h1 : (B'.o.resT S).symm (v, w) + (B'.o.resT S).symm (b, 0) = (B'.o.resT S).symm (v + b, w) := by
    rw [← map_add (f := _)]; simp
  rw [B'.o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_right, add_zero, h1]
  ring

end GlobalTheory.ContrComb
end

noncomputable section
namespace GlobalTheory.ContrComb

variable {D : D7}

def extL {V₀ A L S : HSp D} (o : OrthDec V₀ A L) : WO A S →+ WO V₀ S :=
  (o.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

def extR {V₀ A L S : HSp D} (o : OrthDec V₀ A L) : WO S A →+ WO S V₀ :=
  (o.resT S).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

theorem extL_apply {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO A S) : extL (S := S) o u = (o.resS S).symm (u, 0) := rfl

theorem extR_apply {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO S A) : extR (S := S) o u = (o.resT S).symm (u, 0) := rfl

theorem continuous_extL {V₀ A L S : HSp D} (o : OrthDec V₀ A L) : Continuous (extL (S := S) o) :=
  (o.continuous_resS_symm S).comp (continuous_id.prodMk continuous_const)

theorem continuous_extR {V₀ A L S : HSp D} (o : OrthDec V₀ A L) : Continuous (extR (S := S) o) :=
  (o.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const)

theorem extL_inf {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO A S) (h : u.map (infPart D) = 0) :
    (extL (S := S) o u).map (infPart D) = 0 := by
  rw [extL_apply, OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
  change (u * o.pA).map (infPart D) = 0
  rw [Matrix.map_mul, h, Matrix.zero_mul]

theorem extR_inf {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO S A) (h : u.map (infPart D) = 0) :
    (extR (S := S) o u).map (infPart D) = 0 := by
  rw [extR_apply, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
  change (o.jA * u).map (infPart D) = 0
  rw [Matrix.map_mul, h, Matrix.mul_zero]

theorem extL_half {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (e : AE D) (u : WO A S) (h : IsHalf e u) :
    IsHalf e (extL (S := S) o u) := by
  intro i j
  rw [extL_apply, OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
  change e * (u * o.pA) i j = (u * o.pA) i j
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, h i]

theorem extR_half {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (e : AE D) (u : WO S A) (h : IsHalf e u) :
    IsHalf e (extR (S := S) o u) := by
  intro i j
  rw [extR_apply, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
  change e * (o.jA * u) i j = (o.jA * u) i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h k j]

end GlobalTheory.ContrComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaZeroMeanLogNormConjugatesOfWeber
section
noncomputable section

namespace GlobalTheory.Theta0MeanCore

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
open scoped nonZeroDivisors
open GlobalTheory.Theta0MeanProof (lemA lemD log_normSq log_area sum_log_nonneg bound_le_half log_d_le half_le_log_v)

theorem core (hP : PeriodLatticeAgreement.LatticePeriodEta) (hW : ThetaConstantWeber.ThetaWeberStatement) {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hth : ∀ (a b : Fin 2) (τ : ℂ), 1 / 2 ≤ τ.im → ‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ ≤ C₀)
    (D : D7) (hJ : Formalism.MainNotions.GL3Theta.admJ D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ) (hS : SignedLogMeans.HidaSetting D cc δ M t) :
    SignedLogMeans.meanLog M (lamOf D cc δ) t ≤ SignedLogMeans.bound D ∧
      SignedLogMeans.meanPosLog M (lamOf D cc δ) t ≤
        SignedLogMeans.meanLog M (lamOf D cc δ) t + ((1 / 4) * Real.log D.host.d + max 0 (2 * Real.log C₀)) := by
  classical
  have hArea := _root_.GlobalTheory.MeanLogArea.mean_log_area D cc δ M t hS
  obtain ⟨X, hX0, hXi, hXρ⟩ := _root_.GlobalTheory.IntegralXCore.exists_integral_theta_ratio hP hW D hJ cc δ M t hS
  have hInt := sum_log_nonneg M X hX0 hXi
  have hB := _root_.GlobalTheory.ConjLatticeCore.conj_lattice_core D cc δ M t hS
  have hT0 := hS.2.2.2
  set Λ := lamOf D cc δ with hΛ
  choose hdisc c hc x hx hΛeq using hB
  have hA := fun ρ => lemA D (c ρ) (hc ρ) (x ρ) (hx ρ)
  choose hstab ω τ hω hτ hLat hy1 hy2 using hA
  have hLat' : ∀ ρ, JacobiThetaHalfCharacteristic.IsPeriodLattice (lamConj M ρ Λ) (ω ρ) (τ ρ) := by
    intro ρ; rw [hΛeq ρ]; exact hLat ρ
  have htn : ∀ ρ, t ρ ∉ lamConj M ρ Λ := by
    intro ρ ht
    apply (hT0 ρ).2.1
    rw [hΛeq ρ] at ht ⊢
    exact hstab ρ _ ht
  have hNρ := fun ρ => GlobalTheory.Proof.ThetaZeroNormGlobalInterpolation.normTheta0 _ (ω ρ) (τ ρ) (t ρ) (hω ρ) (hτ ρ) (hLat' ρ) (hT0 ρ).1 (htn ρ)
  have hex : ∀ ρ, ∃ ab : Fin 2 × Fin 2, JacobiThetaHalfCharacteristic.IsEvenChar ab.1 ab.2 ∧
      JacobiThetaHalfCharacteristic.thetaChar ab.1 ab.2 (t ρ / ω ρ) (τ ρ) = 0 := fun ρ => (hNρ ρ).1.exists
  choose ab hab0 hab1 using hex
  set th : (M →ₐ[ℚ] ℂ) → ℝ := fun ρ => ‖JacobiThetaHalfCharacteristic.thetaChar (ab ρ).1 (ab ρ).2 0 (τ ρ)‖ with hthdef
  set et : (M →ₐ[ℚ] ℂ) → ℝ := fun ρ => ‖ModularForm.eta (τ ρ)‖ with hetdef
  have F1 : ∀ ρ, 0 < th ρ ∧ Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) =
      -(1 / 2) * Real.log 2 - (1 / 2) * Real.log (τ ρ).im - 2 * Real.log (th ρ) :=
    fun ρ => log_normSq (hNρ ρ).2.1 (hτ ρ) ((hNρ ρ).2.2 _ _ (hab0 ρ) (hab1 ρ))
  have F2 := fun ρ => log_area hP (hω ρ) (hτ ρ) (hLat' ρ) (hdisc ρ)
  have F3 : ∀ ρ, Real.log ‖ρ X‖ = 12 * (Real.log (th ρ) - Real.log (et ρ)) := by
    intro ρ
    rw [hXρ ρ (ω ρ) (τ ρ) (hω ρ) (hτ ρ) (hLat' ρ) _ _ (hab0 ρ) (hab1 ρ), Real.log_pow,
      Real.log_div (F1 ρ).1.ne' (F2 ρ).1.ne']
    push_cast; ring

  set n : ℝ := (Module.finrank ℚ M : ℝ) with hn
  have hcard : (Finset.univ : Finset (M →ₐ[ℚ] ℂ)).card = Module.finrank ℚ M := by
    rw [Finset.card_univ]; exact AlgHom.card ℚ M ℂ
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Module.finrank_pos
  set St := ∑ ρ, Real.log (th ρ)
  set Se := ∑ ρ, Real.log (et ρ)
  set Sy := ∑ ρ, Real.log (τ ρ).im
  have e1 : ∑ ρ, Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) = -(1 / 2) * Real.log 2 * n - (1 / 2) * Sy - 2 * St := by
    rw [Finset.sum_congr rfl fun ρ _ => (F1 ρ).2]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul]
    rw [hn]; ring
  have e2 : ∑ ρ, Real.log (area (lamConj M ρ Λ)) = (Real.log 4 + 2 * Real.log Real.pi) * n + Sy + 4 * Se := by
    rw [Finset.sum_congr rfl fun ρ _ => (F2 ρ).2]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul]
    rw [hn]; ring
  have e3 : 0 ≤ St - Se := by
    have : ∑ ρ : M →ₐ[ℚ] ℂ, Real.log ‖ρ X‖ = 12 * (St - Se) := by
      rw [Finset.sum_congr rfl fun ρ _ => F3 ρ, ← Finset.mul_sum, Finset.sum_sub_distrib]
    linarith
  rw [e2] at hArea
  have hA2 : (Real.log 4 + 2 * Real.log Real.pi) * n + Sy + 4 * Se = (Real.log Real.pi + ClassMeanPeriods.classMeanValue D) * n := by
    rw [← hArea]; field_simp
  have hsd : 0 < Real.sqrt (D.host.d : ℝ) := Real.sqrt_pos.2 (by
    have := GlobalTheory.Theta0MeanCompare.one_le_d D; linarith)
  have hcmv : ClassMeanPeriods.classMeanValue D = Real.eulerMascheroniConstant + Real.log 2 + Real.log Real.pi -
      Real.log (Real.sqrt D.host.d) - logDerivativeAtOne D := by
    unfold ClassMeanPeriods.classMeanValue
    rw [Real.log_div (by positivity) hsd.ne', Real.log_mul two_ne_zero Real.pi_ne_zero]; ring
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  constructor
  · unfold SignedLogMeans.meanLog
    rw [div_le_iff₀ hnpos]
    change ∑ ρ, Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) ≤ _
    rw [e1]
    unfold SignedLogMeans.bound
    rw [hcmv, hl4] at hA2
    nlinarith
  ·
    have hK : ∀ ρ, max 0 (Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ))) ≤
        Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) + ((1 / 4) * Real.log D.host.d + max 0 (2 * Real.log C₀)) := by
      intro ρ
      have hd1 : 0 ≤ Real.log (D.host.d : ℝ) := Real.log_nonneg (GlobalTheory.Theta0MeanCompare.one_le_d D)
      have hm := le_max_right 0 (2 * Real.log C₀)
      have hm0 := le_max_left 0 (2 * Real.log C₀)
      have h1 := (F1 ρ).2
      have h2 : Real.log (th ρ) ≤ Real.log C₀ :=
        Real.log_le_log (F1 ρ).1 (hth _ _ _ (hy1 ρ))
      have h3 : Real.log (2 * (τ ρ).im) ≤ Real.log (Real.sqrt D.host.d) :=
        Real.log_le_log (by linarith [hτ ρ]) (hy2 ρ)
      rw [Real.log_mul two_ne_zero (hτ ρ).ne'] at h3
      have h4 : Real.log (Real.sqrt (D.host.d : ℝ)) = (1 / 2) * Real.log D.host.d := by
        rw [Real.log_sqrt (by positivity)]; ring
      apply max_le
      · change _ ≤ Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) + _
        rw [h1]; linarith
      · linarith
    set K := (1 / 4) * Real.log D.host.d + max 0 (2 * Real.log C₀)
    have hs := Finset.sum_le_sum fun ρ (_ : ρ ∈ (Finset.univ : Finset (M →ₐ[ℚ] ℂ))) => hK ρ
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul] at hs
    unfold SignedLogMeans.meanPosLog SignedLogMeans.meanLog
    change (∑ ρ, max 0 (Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)))) / n ≤
      (∑ ρ, Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ))) / n + K
    rw [div_add' _ _ _ hnpos.ne', div_le_div_iff_of_pos_right hnpos]
    rw [hn]; linarith

theorem theta0Mean (hP : PeriodLatticeAgreement.LatticePeriodEta) (hW : ThetaConstantWeber.ThetaWeberStatement) :
    SignedLogMeans.Theta0Mean := by
  have hJ : ∀ D : D7, Formalism.MainNotions.GL3Theta.admJ D := fun D =>
    (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D ⟨GlobalTheory.InducedType.restrict_K D, GlobalTheory.InducedType.sum_eq_trace D⟩).1
  obtain ⟨C₀, hC₀, hth⟩ := lemD
  set C := max 0 (2 * Real.log C₀) with hCdef
  have hC0 : 0 ≤ C := le_max_left _ _
  refine ⟨⟨fun D cc δ M _ t hS => (core hP hW hC₀ hth D (hJ D) cc δ M t hS).1,
    fun D cc δ M _ t hS L hL => ?_, ⟨1 / 2, by norm_num, fun D cc δ M _ t hS L hL => ?_⟩⟩,
    ⟨C, hC0, fun D cc δ M _ t hS => ?_⟩, ⟨1 + 2 * C, by linarith, fun D cc δ M _ t hS L hL => ?_⟩⟩
  · have := (core hP hW hC₀ hth D (hJ D) cc δ M t hS).1
    rw [GlobalTheory.Theta0MeanCompare.bound_eq] at this
    exact this.trans (GlobalTheory.Theta0MeanCompare.kronBound_le D hL)
  · exact (core hP hW hC₀ hth D (hJ D) cc δ M t hS).1.trans (bound_le_half D hL)
  · obtain ⟨h1, h2⟩ := core hP hW hC₀ hth D (hJ D) cc δ M t hS
    linarith
  · obtain ⟨h1, h2⟩ := core hP hW hC₀ hth D (hJ D) cc δ M t hS
    have a1 := bound_le_half D hL
    have a2 := log_d_le D hL
    have a3 : 1 / 2 ≤ L := by have := half_le_log_v D; have := abs_nonneg (logDerivativeAtOne D); linarith
    have a4 : C ≤ 2 * C * L := by nlinarith
    linarith

end GlobalTheory.Theta0MeanCore
end
end

