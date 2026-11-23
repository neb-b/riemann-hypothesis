module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0301
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0165
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateEvaluationMapHasLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjRowLev

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem e_left (k : X.B.I.Gf) (hk : k ∈ X.K2) (y : X.B.I.Gf) : X.B.e y = X.chi2 k * X.B.e (k * y) := by
  obtain ⟨-, hKm, hKi, hχm, hχn⟩ := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hK : ∀ z, z ∈ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw ↔ z ∈ X.K2 := fun z => Iff.rfl
  rw [X.e_eq y, X.e_eq (k * y)]
  by_cases hy : y ∈ X.K2
  · have hky : k * y ∈ X.K2 := hKm k hk y hy
    rw [if_pos ((hK y).2 hy), if_pos ((hK _).2 hky)]
    change star (X.chi2 y) / _ = X.chi2 k * (star (X.chi2 (k * y)) / _)
    rw [hχm k hk y hy, star_mul', ← mul_div_assoc, ← mul_assoc]
    have h1 : X.chi2 k * star (X.chi2 k) = 1 := by
      rw [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχn k hk]; simp
    rw [h1, one_mul]
  · have hky : k * y ∉ X.K2 := fun h' => hy (by simpa using hKm _ (hKi k hk) _ h')
    rw [if_neg (fun h' => hy ((hK y).1 h')), if_neg (fun h' => hky ((hK _).1 h')), mul_zero]

theorem R_comp_Re (k : X.B.I.Gf) (hk : k ∈ X.K2) :
    (X.B.R (1, k)).comp X.B.Re = X.chi2 k • X.B.Re := by
  obtain ⟨R1, Rm, Rn, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous X.B
  obtain ⟨-, hT⟩ := X.B.Re_spec
  have p1 : (fun g : X.B.I.Gf => X.B.R (1, g)) 1 = 1 := R1
  have pm : ∀ a b : X.B.I.Gf, X.B.R (1, a * b) = X.B.R (1, a) * X.B.R (1, b) := by
    intro a b; rw [← Rm]; simp
  have pn : ∀ (g : X.B.I.Gf) v, ‖X.B.R (1, g) v‖ = ‖v‖ := fun g v => Rn _ v
  refine ContinuousLinearMap.ext fun y => ?_
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, inner_smul_right,
    GlobalTheory.IdemProj.inner_rep (fun g : X.B.I.Gf => X.B.R (1, g)) p1 pm pn, hT, hT, ← integral_const_mul,
    ← integral_mul_left_eq_self (fun h => X.chi2 k * (X.B.e h * ⟪x, X.B.R (1, h) y⟫_ℂ)) k]
  congr 1
  funext h
  have e1 : ⟪X.B.R (1, k⁻¹) x, X.B.R (1, h) y⟫_ℂ = ⟪x, X.B.R (1, k * h) y⟫_ℂ := by
    rw [← GlobalTheory.IdemProj.inner_rep (fun g : X.B.I.Gf => X.B.R (1, g)) p1 pm pn, pm]
    rfl
  show X.B.e h * ⟪X.B.R (1, k⁻¹) x, X.B.R (1, h) y⟫_ℂ = X.chi2 k * (X.B.e (k * h) * ⟪x, X.B.R (1, k * h) y⟫_ℂ)
  rw [e1, e_left X k hk h, mul_assoc]

end GlobalTheory.ConjRowLev

namespace GlobalTheory.ConjRowMult


open GlobalTheory.ConjRowLev in
theorem conjMap_lev : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ u : M.Vec, ∀ k ∈ J, ∀ g : GA D (D.sp.Y 0), GlobalTheory.ConjRowMult.conjMap X M c Φ h t u (g * k) = χ k * GlobalTheory.ConjRowMult.conjMap X M c Φ h t u g := by
  intro _ D X h θ S M J χ t c _ _ _ _ hM _ Φ hΦ hrep u k hk g
  obtain ⟨-, hCL⟩ := hM
  obtain ⟨hJ, hχ⟩ := hCL k
  have hk0 := hJ.1 hk
  obtain ⟨h1, h2⟩ : (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).1 = 1 ∧ (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).2 ∈ X.K2 := hk0
  set k' := (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).2 with hk'
  have hsplit : g * k * t⁻¹ = (g * t⁻¹) * (t⁻¹⁻¹ * k * t⁻¹) := by group
  have hι : iotaX X h (g * k * t⁻¹) = iotaX X h (g * t⁻¹) * ((1, k') : X.B.I.GA) := by
    rw [hsplit, map_mul]
    congr 1
    exact Prod.ext h1 rfl
  obtain ⟨ψ, hψ⟩ := hrep u
  have hR : X.B.R (1, k') (Φ (X.B.tens (vecC X M c u))) = X.chi2 k' • Φ (X.B.tens (vecC X M c u)) := by
    obtain ⟨T0, -, rfl⟩ := hΦ
    have := congrArg (fun L => L (T0 (X.B.tens (vecC X M c u)))) (R_comp_Re X k' h2)
    simpa using this
  have a := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ ((1, k') : X.B.I.GA)
  rw [hR] at a
  have key := congrFun (Formalism.L2.SG.EvalTOntoRep.contRep_unique X a (Formalism.L2.SG.EvalTOntoRep.contRep_smul X (X.chi2 k') hψ))
  rw [conjMap_apply, conjMap_apply, contRepL_spec X hψ, hι, key, Pi.smul_apply, smul_eq_mul, star_mul', ← hχ hk]
  rfl

end GlobalTheory.ConjRowMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffOfHeisenbergDerivativeClosedClass
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField
open GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ContDiff Topology

namespace GlobalTheory.HeisSmooth

open GlobalTheory.OrientedHeis GlobalTheory.FockCompare GlobalTheory.Unf.MatCoef

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {S T : HSp D}

theorem differentiableAt_phase (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {M : ℝ →+ WO S T} (hM : Continuous M)
    (hMf : ∀ s, (M s).map (finPart D) = 0) (w : WO S T) :
    DifferentiableAt ℝ (fun s : ℝ => ψ (symplOH S T w (M s))) 0 := by
  have hlin : ∀ s : ℝ, piW θ T S (M s) = s • piW θ T S (M 1) := fun s => by
    have := map_real_smul ((piW θ T S).comp M) ((continuous_pi' h.inf T S).comp hM) s 1
    simpa using this
  have e : (fun s : ℝ => ψ (symplOH S T w (M s))) = fun s : ℝ =>
      Complex.exp (-(Real.pi * Complex.I) * ((s * omO S T (piW θ T S w) (piW θ T S (M 1)) : ℝ) : ℂ)) := by
    funext s
    rw [← h.iota_pi (hMf s), psi_symplOH h hψ, hlin, LinearMap.map_smul, smul_eq_mul]
  rw [e]
  exact ((((hasDerivAt_id (0 : ℝ)).mul_const (omO S T (piW θ T S w) (piW θ T S (M 1)))).ofReal_comp).const_mul
      (-(Real.pi * Complex.I))).cexp.differentiableAt

theorem hasDerivAt_line (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {M : ℝ →+ WO S T} (hM : Continuous M)
    (hMf : ∀ s, (M s).map (finPart D) = 0) {f : WO S T → ℂ} {w : WO S T} {c : ℂ}
    (hd : HasDerivAt (fun s : ℝ => heisO ψ S T (M s) f w) c 0) :
    HasDerivAt (fun s : ℝ => f (w + M s)) (c + -deriv (fun s : ℝ => ψ (symplOH S T w (M s))) 0 * f w) 0 := by
  have hp := (differentiableAt_phase h hψ hM hMf w).hasDerivAt
  have hne : ∀ s, ψ (symplOH S T w (M s)) ≠ 0 := fun s h0 => by
    have := AddChar.map_add_eq_mul ψ (symplOH S T w (M s)) (-(symplOH S T w (M s)))
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
    exact one_ne_zero this
  have h0 : symplOH S T w (M 0) = 0 := by
    rw [map_zero]
    simp [symplOH, symplO, hO]
  have e : (fun s : ℝ => f (w + M s)) = fun s => heisO ψ S T (M s) f w / ψ (symplOH S T w (M s)) := by
    funext s
    rw [heisO, mul_div_cancel_left₀ _ (hne s)]
  rw [e]
  refine (hd.div hp (hne 0)).congr_deriv ?_
  have h1 : heisO ψ S T (M 0) f w = f w := by
    rw [heisO, h0, AddChar.map_zero_eq_one, one_mul, map_zero, add_zero]
  rw [h1, h0, AddChar.map_zero_eq_one]
  ring

theorem contDiff_of_heis_closed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (V : Set (WO S T → ℂ)), (∀ f ∈ V, Continuous f) →
    (∀ f ∈ V, ∀ M : ℝ →+ WO S T, Continuous M → (∀ t, (M t).map (finPart D) = 0) →
      ∃ f' ∈ V, ∀ w, HasDerivAt (fun t : ℝ => heisO ψ S T (M t) f w) (f' w) 0) →
    ∀ f ∈ V, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) →
      ∀ w, ContDiff ℝ ∞ fun t => f (w + L t) := by
  intro D ψ hψ S T V hc hd f hf k L hL hLf u
  obtain ⟨⟨θ, hθ⟩, -⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  haveI : IsTopologicalAddGroup (Formalism.L2.Theta.AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
  haveI : ContinuousAdd (WO S T) := inferInstance
  let P : ((Fin k → ℝ) → ℂ) → Prop := fun F => ∃ f ∈ V, F = fun t => f (u + L t)
  refine contDiff_of_partials P ?_ ?_ _ ⟨f, hf, rfl⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact (hc f hf).comp (continuous_const.add hL)
  · rintro _ ⟨f, hf, rfl⟩ i
    let E : ℝ →ₗ[ℝ] (Fin k → ℝ) := LinearMap.toSpanSingleton ℝ (Fin k → ℝ) (Pi.single i 1)
    let M : ℝ →+ WO S T := L.comp E.toAddMonoidHom
    have hM : Continuous M := hL.comp E.continuous_of_finiteDimensional
    have hMf : ∀ s, (M s).map (finPart D) = 0 := fun s => hLf _
    obtain ⟨f', hf', hD⟩ := hd f hf M hM hMf
    refine ⟨2, ![fun _ => 1, fun t => -deriv (fun s : ℝ => ψ (symplOH S T (u + L t) (M s))) 0],
      ![fun t => f' (u + L t), fun t => f (u + L t)], fun j => ?_, fun j => ?_, fun t => ?_⟩
    · fin_cases j
      · exact contDiff_const
      · exact contDiff_phase h hψ hL hM hMf u
    · fin_cases j
      · exact ⟨f', hf', rfl⟩
      · exact ⟨f, hf, rfl⟩
    · have e : (fun s : ℝ => f (u + L (t + s • Pi.single i 1))) = fun s => f ((u + L t) + M s) := by
        funext s
        have : E s = s • Pi.single i 1 := rfl
        rw [map_add (f := _), add_assoc, ← this]
        rfl
      rw [e]
      convert hasDerivAt_line h hψ hM hMf (hD (u + L t)) using 1
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul]

end GlobalTheory.HeisSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaEqSumSchrodingerFunctionPeriodisatio
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

noncomputable section

namespace GlobalTheory.Core.Rk.SchPeriod

theorem theta_eq_sum_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ x : Mx D B.rank A.rank, (Summable fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E => ‖sch ψ A B ν 𝓨 f (x + rat ξ)‖) ∧ HasSum (fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E => sch ψ A B ν 𝓨 f (x + rat ξ)) (f ((dblDec A).extX B x)) := by
  intro D ψ hψ A B ν 𝓨 hcov f hf x
  have hF : IsThetaFunO ψ (dblSp A) B (heisO ψ (dblSp A) B ((dblDec A).extX B x) f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ (dblSp A) B).1 _ _ hf
  have h1 := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) ⟨ν, 𝓨, hcov⟩ f hf).1
  have h5 := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) ⟨ν, 𝓨, hcov⟩ _ hF).2.2.2.2 0
  have h0 : heisO ψ (dblSp A) B ((dblDec A).extX B x) f ((dblDec A).ext0 B 0) = f ((dblDec A).extX B x) := by
    rw [map_zero]
    simp only [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]
  have H : HasSum (fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E => sch ψ A B ν 𝓨 f (x + rat ξ))
      (f ((dblDec A).extX B x)) := by
    rw [h0] at h5
    convert h5 using 1
    funext ξ
    rw [h1, add_comm]
    rfl
  exact ⟨summable_norm_iff.2 H.summable, H⟩

end GlobalTheory.Core.Rk.SchPeriod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaSeriesLawAndLevel
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThetaSeriesLaw

open Filter Topology
open scoped TensorProduct

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)

def bt (x y : Mx D T.rank ρ) : AF D.host.F := symplOH S T (d.extX T x) (d.extY T y)

theorem bt_add_left (x x' y : Mx D T.rank ρ) : bt d T (x + x') y = bt d T x y + bt d T x' y := by
  rw [bt, map_add (f := _), GlobalTheory.OrientedHeis.symplOH_add_left]; rfl

theorem bt_add_right (x y y' : Mx D T.rank ρ) : bt d T x (y + y') = bt d T x y + bt d T x y' := by
  rw [bt, map_add (f := _), GlobalTheory.OrientedHeis.symplOH_add_right]; rfl

theorem bt_zero_right (x : Mx D T.rank ρ) : bt d T x 0 = 0 := by
  rw [bt, map_zero, GlobalTheory.FinTranslate.symplOH_zero_right]

theorem symplO_bt (x y : Mx D T.rank ρ) : symplO S T (d.extX T x) (d.extY T y) = bt d T x y + bt d T x y := by
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  unfold bt symplOH
  linear_combination (-symplO S T (d.extX T x) (d.extY T y)) * h2

theorem psi_bt_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (ξ η : Matrix (Fin T.rank) (Fin ρ) D.host.E) : ψ (bt d T (rat ξ) (rat η)) = 1 := by
  obtain ⟨a, ha⟩ := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_rat D S T (ξ * d.qX) (η * d.qY)
  rw [ratW_eq, ratW_eq, rat_mul, rat_mul] at ha
  have : bt d T (rat ξ) (rat η) = algebraMap D.host.F (AF D.host.F) (1 / 2 * a) := by
    rw [map_mul, ← ha]; rfl
  rw [this]; exact hψ.2.2.1 _

theorem symplOH_coord (h0 : d.j0 = 0) (w w' : WO S T) :
    symplOH S T w w' = bt d T (w ⬝ d.jX) (w' ⬝ d.jY) - bt d T (w' ⬝ d.jX) (w ⬝ d.jY) := by
  have h : ∀ w : WO S T, w = d.extX T (w ⬝ d.jX) + d.extY T (w ⬝ d.jY) := fun w => by
    have := (d.coordS T).left_inv w
    change d.extX T (w ⬝ d.jX) + d.ext0 T (w ⬝ d.j0) + d.extY T (w ⬝ d.jY) = w at this
    rw [h0, Matrix.mul_zero, map_zero, add_zero] at this
    exact this.symm
  conv_lhs => rw [h w, h w']
  rw [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right,
    d.symplOH_extX_extX, d.symplOH_extY_extY, symplOH_skew S T (d.extX T (w' ⬝ d.jX)), zero_add, add_zero,
    sub_eq_add_neg]
  rfl

theorem map_mul_zero {R : Type} [CommRing R] (q : AE D →+* R) {l m n : ℕ} {x : Mx D l m} (hx : x.map q = 0)
    (y : Mx D m n) : (x ⬝ y : Mx D l n).map q = 0 := by
  rw [Matrix.map_mul, hx, Matrix.zero_mul]

theorem snd_bt {x : Mx D T.rank ρ} (hx : x.map (finPart D) = 0) (y : Mx D T.rank ρ) : (bt d T x y).2 = 0 := by
  have h := GlobalTheory.OrientedHeis.snd_symplO (S := S) (T := T) (x := d.extX T x) (y := d.extY T y)
    (Or.inl (map_mul_zero _ hx _))
  change _ * sndA D.host.F (symplO S T (d.extX T x) (d.extY T y)) = 0
  rw [h, mul_zero]

theorem bt_eq_pair (x : Mx D T.rank ρ) {y : Mx D T.rank ρ} (hy : y.map (infPart D) = 0) :
    bt d T x y = pairA D.host.F 0 (bt d T x y).2 := by
  have h := GlobalTheory.OrientedHeis.fst_symplO (S := S) (T := T) (x := d.extX T x) (y := d.extY T y)
    (Or.inr (map_mul_zero _ hy _))
  refine Prod.ext ?_ rfl
  change _ * fstA D.host.F (symplO S T (d.extX T x) (d.extY T y)) = 0
  rw [h, mul_zero]

theorem exists_section (D : D7) : ∃ s : Af D.host.F ⊗[D.host.F] D.host.E → AE D, Continuous s ∧
    ∀ z, finPart D (s z) = z := by
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨fun z => e.symm (0, z), hc.comp (continuous_const.prodMk continuous_id), fun z => ?_⟩
  have := (he (e.symm (0, z))).2
  rw [e.apply_symm_apply] at this
  exact this.symm

theorem exists_open_ann {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (Z : Set (Mx D T.rank ρ))
    {K : Set (Matrix (Fin T.rank) (Fin ρ) (Af D.host.F ⊗[D.host.F] D.host.E))} (hK : IsCompact K)
    (hZ : ∀ z ∈ Z, z.map (finPart D) ∈ K) :
    ∃ V : AddSubgroup (Mx D T.rank ρ), IsOpen (V : Set (Mx D T.rank ρ)) ∧
      ∀ b ∈ V, b.map (infPart D) = 0 → ∀ z ∈ Z, ψ (bt d T z b) = 1 := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  obtain ⟨s, hs, hsf⟩ := exists_section D
  have hadd : ∀ z a b, ψ (pairA D.host.F 0 (bt d T z (a + b)).2) =
      ψ (pairA D.host.F 0 (bt d T z a).2) * ψ (pairA D.host.F 0 (bt d T z b).2) := fun z a b => by
    rw [← AddChar.map_add_eq_mul, bt_add_right]
    congr 1
    exact Prod.ext (add_zero _).symm rfl
  have hzero : ∀ z, ψ (pairA D.host.F 0 (bt d T z 0).2) = 1 := fun z => by
    rw [bt_zero_right]; exact ψ.map_zero_eq_one
  let V : AddSubgroup (Mx D T.rank ρ) :=
    { carrier := {b | ∀ z ∈ Z, ψ (pairA D.host.F 0 (bt d T z b).2) = 1}
      zero_mem' := fun z _ => hzero z
      add_mem' := fun {a b} ha hb z hz => by rw [hadd, ha z hz, hb z hz, one_mul]
      neg_mem' := fun {a} ha z hz => by
        have := hadd z a (-a)
        rw [add_neg_cancel, hzero, ha z hz, one_mul] at this
        exact this.symm }
  refine ⟨V, V.isOpen_of_mem_nhds (g := 0) ?_, fun b hb h0 z hz => ?_⟩
  · have hK' : IsCompact ((fun k => k.map s) '' K) := hK.image (continuous_id.matrix_map hs)
    have hc : Continuous fun p : Mx D T.rank ρ × Mx D T.rank ρ => (bt d T p.2 p.1).2 :=
      continuous_snd.comp (GlobalTheory.OrientedHeis.continuous_symplOH (continuous_snd.matrix_mul continuous_const)
        (continuous_fst.matrix_mul continuous_const))
    have hev : ∀ᶠ b in 𝓝 (0 : Mx D T.rank ρ), ∀ z ∈ (fun k => k.map s) '' K,
        ψ (pairA D.host.F 0 (bt d T z b).2) = 1 := by
      refine hK'.eventually_forall_of_forall_eventually fun z _ => ?_
      exact hc.continuousAt.preimage_mem_nhds (x := (0, z)) (t := {a | ψ (pairA D.host.F 0 a) = 1})
        (by rw [bt_zero_right]; exact GlobalTheory.FinTranslate.ker_mem_nhds hψ.1 hψ.2.1)
    refine Filter.mem_of_superset hev fun b hb z hz => ?_
    have h1 := hb _ ⟨_, hZ z hz, rfl⟩
    have h2 : (z - (z.map (finPart D)).map s).map (finPart D) = 0 := by
      ext i j
      exact (RingHom.map_sub _ _ _).trans (sub_eq_zero.2 (hsf _).symm)
    have h3 : (bt d T z b).2 = (bt d T ((z.map (finPart D)).map s) b).2 := by
      have h4 := bt_add_left d T (z - (z.map (finPart D)).map s) ((z.map (finPart D)).map s) b
      rw [sub_add_cancel] at h4
      rw [h4]
      exact (congrArg (· + _) (snd_bt d T h2 b)).trans (zero_add _)
    rw [h3]; exact h1
  · rw [bt_eq_pair d T z h0]; exact hb z hz

variable {d T} {ψ : AddChar (AF D.host.F) ℂ} {φ : Mx D T.rank ρ → ℂ} {f : WO S T → ℂ}

theorem addChar_theta_law_rearrangement_identity {R : Type} [AddCommGroup R] (χ : AddChar R ℂ) (a b c e g h : R) (t : ℂ) (ha : χ a = 1) (hg : χ g = 1) :
    χ (-(a + b + (c + e))) * (χ (c + e + (g + h) + (c + e + (g + h))) * t) =
      χ (-(b - c)) * χ (-e) * (χ (e + h + (e + h)) * t) := by
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  rw [← one_mul (χ _ * χ _ * χ _), ← hg, ← one_mul (χ _ * (χ _ * χ _ * χ _)), ← hg, ← one_mul (χ (-_) * χ _), ← ha]
  simp only [← AddChar.map_add_eq_mul]
  congr 1
  abel

theorem law (hψ : IsCharAF D.host.F ψ) (h0 : d.j0 = 0)
    (hf : ∀ w : WO S T, f w = ψ (-(bt d T (w ⬝ d.jX) (w ⬝ d.jY))) * ∑' ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E,
      ψ (symplO S T (d.extX T (w ⬝ d.jX + rat ξ)) (d.extY T (w ⬝ d.jY))) * φ (w ⬝ d.jX + rat ξ))
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T) :
    f (rat γ + w) = ψ (-(symplOH S T (rat γ) w)) * f w := by
  have hX : (rat γ ⬝ d.jX : Mx D T.rank ρ) = rat (γ * d.e) := (rat_mul _ _).symm
  have hY : (rat γ ⬝ d.jY : Mx D T.rank ρ) = rat (γ * d.e') := (rat_mul _ _).symm
  rw [hf, hf, symplOH_coord d T h0, Matrix.add_mul, Matrix.add_mul, hX, hY]
  generalize γ * d.e = ξ₀
  generalize γ * d.e' = η₀
  generalize (w ⬝ d.jX : Mx D T.rank ρ) = x
  generalize (w ⬝ d.jY : Mx D T.rank ρ) = y
  rw [← mul_assoc, ← tsum_mul_left, ← tsum_mul_left]
  refine Eq.trans (tsum_congr fun ξ => ?_) ((Equiv.addLeft ξ₀).tsum_eq _)
  have e : rat ξ₀ + x + rat ξ = x + rat (Equiv.addLeft ξ₀ ξ) := by
    rw [Equiv.coe_addLeft, rat_add]; abel
  rw [e]
  generalize Equiv.addLeft ξ₀ ξ = ζ
  have h1 := psi_bt_rat d T hψ ξ₀ η₀
  have h2 := psi_bt_rat d T hψ ζ η₀
  simp only [symplO_bt, bt_add_left]
  simp only [bt_add_right]
  exact addChar_theta_law_rearrangement_identity ψ _ _ _ _ _ _ _ h1 h2

theorem level (hψ : IsCharAF D.host.F ψ) (h0 : d.j0 = 0) (hφ : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ)
    (hf : ∀ w : WO S T, f w = ψ (-(bt d T (w ⬝ d.jX) (w ⬝ d.jY))) * ∑' ξ : Matrix (Fin T.rank) (Fin ρ) D.host.E,
      ψ (symplO S T (d.extX T (w ⬝ d.jX + rat ξ)) (d.extY T (w ⬝ d.jY))) * φ (w ⬝ d.jX + rat ξ)) :
    ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  obtain ⟨U, hU, hUφ⟩ := hφ.level
  obtain ⟨K, hK, hKφ⟩ := hφ.supp
  obtain ⟨V, hV, hVψ⟩ := exists_open_ann d T hψ {z | φ z ≠ 0} hK hKφ
  let rX : WO S T →+ Mx D T.rank ρ := AddMonoidHom.mk' (fun w => w ⬝ d.jX) fun _ _ => Matrix.add_mul _ _ _
  let rY : WO S T →+ Mx D T.rank ρ := AddMonoidHom.mk' (fun w => w ⬝ d.jY) fun _ _ => Matrix.add_mul _ _ _
  have cX : Continuous rX := continuous_id.matrix_mul continuous_const
  have cY : Continuous rY := continuous_id.matrix_mul continuous_const
  refine ⟨U.comap rX ⊓ V.comap rY, (hU.preimage cX).inter (hV.preimage cY), fun u hu hi => ?_⟩
  have ha := hUφ (u ⬝ d.jX) hu.1 (map_mul_zero _ hi _)
  have hb := hVψ (u ⬝ d.jY) hu.2 (map_mul_zero _ hi _)
  funext w
  rw [heisO, hf, hf, symplOH_coord d T h0, Matrix.add_mul, Matrix.add_mul]
  generalize (u ⬝ d.jX : Mx D T.rank ρ) = a at ha ⊢
  generalize (u ⬝ d.jY : Mx D T.rank ρ) = b at hb ⊢
  generalize (w ⬝ d.jX : Mx D T.rank ρ) = x
  generalize (w ⬝ d.jY : Mx D T.rank ρ) = y
  rw [← mul_assoc, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun ξ => ?_
  rw [add_right_comm x a, ha]
  generalize x + rat ξ = z
  by_cases hz : φ z = 0
  · simp only [hz, mul_zero]
  have h1 := hb z hz
  have h2 := hb (z + a) (by rwa [Set.mem_setOf_eq, ha])
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  rw [← one_mul (ψ (-bt d T x y) * ψ _), ← h1, ← one_mul (ψ (bt d T z b) * _), ← h2]
  simp only [← AddChar.map_add_eq_mul, symplO_bt, bt_add_left, bt_add_right]
  congr 1
  abel

theorem law_and_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (φ : Mx D B.rank A.rank → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → ∀ f : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ (HMul.hMul w (dblDec A).jX + rat ξ)) → (∀ γ w, f (ratW B (dblSp A) γ + w) = ψ (-(symplOH (dblSp A) B (ratW B (dblSp A) γ) w)) * f w) ∧ ∃ U : AddSubgroup (WO (dblSp A) B), IsOpen (U : Set (WO (dblSp A) B)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ (dblSp A) B u f = f := by
  intro D ψ hψ A B φ hφ f hf
  have h0 : (dblDec A).j0 = 0 := rat_zero
  exact ⟨law hψ.1 h0 hf, level hψ.1 h0 hφ hf⟩

end GlobalTheory.ThetaSeriesLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOfSameDoubleCosetCompletionRowRepresentativesStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_same_doubleCoset_completion_rowRepresentatives : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s), Set.InjOn (DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J ) {g : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k | ∃ b : L.β (j + 1), IsGL ι (L.h (j + 1) b P) g} := by
  first | exact @GlobalTheory.TwBridge.RepsInj.reps_injOn | exact GlobalTheory.TwBridge.RepsInj.reps_injOn | (intros; apply GlobalTheory.TwBridge.RepsInj.reps_injOn <;> assumption)
end

