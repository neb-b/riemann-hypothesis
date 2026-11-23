module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergDerivWeilTranslateContinuousCombinatio
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeisLineComb

open GlobalTheory.WeilVacMove GlobalTheory.FockCompare

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem actO_actO_inv (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  unfold actO
  rw [inv_inv]
  calc HMul.hMul (HMul.hMul (mt T h) (HMul.hMul (HMul.hMul (mt T h⁻¹) x) (mt S g))) (mt S g⁻¹)
      = HMul.hMul (HMul.hMul (HMul.hMul (mt T h) (mt T h⁻¹)) x) (HMul.hMul (mt S g) (mt S g⁻¹)) := by
        simp only [Matrix.mul_assoc]
    _ = x := by rw [← GlobalTheory.WeilVacMove.mt_mul, ← GlobalTheory.WeilVacMove.mt_mul, mul_inv_cancel, mul_inv_cancel, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.mt_one, Matrix.one_mul, Matrix.mul_one]

theorem dLine_apply {θ : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ)
    {lam : AF D.host.F →+ ℂ} (hl : Continuous lam) (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a))
    {L : ℝ →+ WO S T} (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    dLine ψ S T L f w = phase lam S T (L 1) w * f w +
      fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (piW θ T S (L 1)) := by
  have hline := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 L ⟨hL, hL0⟩
  have hfs := ((smooth_iff_sm_and_real_lines D θ σ h T S).1 f).1 hf.smooth
  have e : (fun t : ℝ => heisO ψ S T (L t) f w) = fun t : ℝ => Complex.exp (t * phase lam S T (L 1) w) *
      f (w + iotaW σ T S (t • piW θ T S (L 1))) := by
    funext t
    rw [heisO, psi_sympl_line hl hlam hL hL0, ← hline t]
  unfold dLine
  rw [e]
  exact (hasDerivAt_exp_mul _ _ f hfs _ w).deriv

theorem dLine_eq_sum (hψ : IsStdChar D ψ (-1)) {θ : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (h : Chart θ σ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (RW T S)) {L : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (N : ι → ℝ →+ WO S T) (hN : ∀ i, Continuous (N i))
    (hN0 : ∀ i t, (N i t).map (finPart D) = 0) (hN1 : ∀ i, piW θ T S (N i 1) = b i) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    dLine ψ S T L f = ∑ i, ((b.coord i (piW θ T S (L 1)) : ℝ) : ℂ) • dLine ψ S T (N i) f := by
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  funext w
  let A : RW T S →+ ℂ := AddMonoidHom.mk' (fun v => lam (symplOH S T w (iotaW σ T S v))) fun u v => by
    rw [map_add (f := _), symplOH_add_right, map_add (f := _)]
  have hA : Continuous A := hl.comp (continuous_symplOH S T continuous_const (h.continuous_iota T S))
  let A' : RW T S →L[ℝ] ℂ := A.toRealLinearMap hA
  let B : RW T S →L[ℝ] ℂ := fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0
  let Φ : RW T S →ₗ[ℝ] ℂ := (LinearMap.mulRight ℝ (f w)).comp A'.toLinearMap + B.toLinearMap
  have key : ∀ (K : ℝ →+ WO S T), Continuous K → (∀ t, (K t).map (finPart D) = 0) →
      dLine ψ S T K f w = Φ (piW θ T S (K 1)) := by
    intro K hK hK0
    rw [dLine_apply h hl hlam hK hK0 hf]
    have e1 : K 1 = iotaW σ T S (piW θ T S (K 1)) := by
      have := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 K ⟨hK, hK0⟩ 1
      rwa [one_smul] at this
    have e2 : lam (symplOH S T w (K 1)) = A (piW θ T S (K 1)) := by
      show _ = lam (symplOH S T w (iotaW σ T S (piW θ T S (K 1))))
      rw [← e1]
    show lam (symplOH S T w (K 1)) * f w + _ = _
    rw [e2]
    rfl
  rw [Finset.sum_apply, key L hL hL0]
  simp only [Pi.smul_apply, smul_eq_mul]
  simp only [fun i => key (N i) (hN i) (hN0 i), hN1]
  conv_lhs => rw [← b.sum_repr (piW θ T S (L 1))]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Complex.real_smul, Module.Basis.coord_apply]

theorem dLine_om_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → ∃ (m : ℕ) (N : Fin m → ℝ →+ WO S T) (c : Fin m → GA D S × GA D T → ℂ), (∀ i, Continuous (N i)) ∧ (∀ i s, (N i s).map (finPart D) = 0) ∧ (∀ i, Continuous (c i)) ∧ ∀ p f, IsThetaFunO ψ S T f → GlobalTheory.WeilVacMove.dLine ψ S T M (om p f) = ∑ i, c i p • om p (GlobalTheory.WeilVacMove.dLine ψ S T (N i) f) := by
  intro D ψ S T χS χT om hW M hM hM0
  have hψ := hW.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  let b := Module.finBasis ℝ (RW T S)
  let N : Fin (Module.finrank ℝ (RW T S)) → ℝ →+ WO S T := fun i =>
    (iotaW σ T S).comp (ContinuousLinearMap.toSpanSingleton ℝ (b i)).toLinearMap.toAddMonoidHom
  have hN : ∀ i, Continuous (N i) := fun i =>
    (h.continuous_iota T S).comp (ContinuousLinearMap.toSpanSingleton ℝ (b i)).continuous
  have hN0 : ∀ i t, (N i t).map (finPart D) = 0 := fun i t => h.real_iota T S _
  have hN1 : ∀ i, piW θ T S (N i 1) = b i := fun i => by
    show piW θ T S (iotaW σ T S ((1 : ℝ) • b i)) = b i
    rw [h.pi_iota, one_smul]
  let Mp : GA D S × GA D T → ℝ →+ WO S T := fun p =>
    AddMonoidHom.mk' (fun s => actO S T p.1⁻¹ p.2⁻¹ (M s)) fun s t => by rw [map_add (f := _), actO_add]
  have hMp : ∀ p, Continuous (Mp p) := fun p =>
    (continuous_const.matrix_mul hM).matrix_mul continuous_const
  have hMp0 : ∀ p t, (Mp p t).map (finPart D) = 0 := fun p t => by
    show (actO S T p.1⁻¹ p.2⁻¹ (M t)).map (finPart D) = 0
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hM0 t, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨_, N, fun i p => ((b.coord i (piW θ T S (Mp p 1)) : ℝ) : ℂ), hN, hN0, fun i => ?_, fun p f hf => ?_⟩
  · have hc : Continuous fun p : GA D S × GA D T => actO S T p.1⁻¹ p.2⁻¹ (M 1) := by
      unfold actO
      exact (((GlobalTheory.MixModel.continuous_mt T).comp (continuous_snd.inv)).matrix_mul continuous_const).matrix_mul
        ((GlobalTheory.MixModel.continuous_mt S).comp continuous_fst.inv.inv)
    exact Complex.continuous_ofReal.comp ((LinearMap.continuous_of_finiteDimensional (b.coord i)).comp
      ((continuous_pi' hθ T S).comp hc))
  · obtain ⟨g, k⟩ := p
    have e := om_dLine hW g k (hMp (g, k)) (hMp0 (g, k)) hM hM0 (fun t => (actO_actO_inv g k (M t)).symm) hf
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e, dLine_eq_sum hψ h b (hMp (g, k)) (hMp0 (g, k)) N hN hN0 hN1 hf, map_sum]
    simp only [map_smul]

end GlobalTheory.HeisLineComb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOneParamDerivOrthDecJoinedEqSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BiJoinDeriv

open GlobalTheory.BiTransfer GlobalTheory.WeilVacMove GlobalTheory.FockCompare

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem dLine_apply' {S T : HSp D} {θ : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ)
    {lam : AF D.host.F →+ ℂ} (hl : Continuous lam) (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a))
    {L : ℝ →+ WO S T} (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    dLine ψ S T L f w = phase lam S T (L 1) w * f w +
      fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (piW θ T S (L 1)) := by
  have hline := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 L ⟨hL, hL0⟩
  have hfs := ((smooth_iff_sm_and_real_lines D θ σ h T S).1 f).1 hf.smooth
  have e : (fun t : ℝ => heisO ψ S T (L t) f w) = fun t : ℝ => Complex.exp (t * phase lam S T (L 1) w) *
      f (w + iotaW σ T S (t • piW θ T S (L 1))) := by
    funext t
    rw [heisO, psi_sympl_line hl hlam hL hL0, ← hline t]
  unfold dLine
  rw [e]
  exact (hasDerivAt_exp_mul _ _ f hfs _ w).deriv

theorem dLine_add_line (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {L L' : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (hL' : Continuous L') (hL0' : ∀ t, (L' t).map (finPart D) = 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    dLine ψ S T (L + L') f = dLine ψ S T L f + dLine ψ S T L' f := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have hS : Continuous (L + L') := hL.add hL'
  have hS0 : ∀ t, ((L + L') t).map (finPart D) = 0 := fun t => by
    ext i j
    have h := congrFun (congrFun (hL0 t) i) j
    have h' := congrFun (congrFun (hL0' t) i) j
    simpa [Matrix.map_apply, (finPart D).map_add] using congrArg₂ (· + ·) h h'
  funext w
  rw [Pi.add_apply, dLine_apply' h hl hlam hS hS0 hf, dLine_apply' h hl hlam hL hL0 hf, dLine_apply' h hl hlam hL' hL0' hf,
    AddMonoidHom.add_apply, map_add, ContinuousLinearMap.map_add]
  have e : phase lam S T (L 1 + L' 1) w = phase lam S T (L 1) w + phase lam S T (L' 1) w := by
    show lam (symplOH S T w (L 1 + L' 1)) = lam (symplOH S T w (L 1)) + lam (symplOH S T w (L' 1))
    rw [symplOH_add_right, map_add (f := _)]
  rw [e]
  ring

variable {W A A' : HSp D} (d : OrthDec W A (GlobalTheory.ChiGrid.negSp A')) (S : HSp D)

theorem inl_fst_add_inr_snd (x : WO W S) : inlH d S (fstH d S x) + inrH d S (sndH d S x) = x := by
  rw [inlH_apply, inrH_apply, fstH_apply, sndH_apply, ← map_add (f := _), Prod.mk_add_mk, add_zero, zero_add]
  have : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S A' (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger A' S (d.resS S x).2) = (d.resS S x).2 :=
    GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger_dagger A' S _
  rw [this, Prod.mk.eta, AddEquiv.symm_apply_apply]

theorem dLine_inlH (G : WO A S → WO S A' → ℂ) (M : ℝ →+ WO A S) :
    dLine ψ W S ((inlH d S).comp M) (join d S G) = join d S (fun u v => dLine ψ A S M (fun u' => G u' v) u) := by
  funext x
  simp only [dLine, join_apply]
  congr 1
  funext t
  simp only [AddMonoidHom.comp_apply, heisO, symplOH_split d, map_add (fstH d S), map_add (sndH d S), fst_inl, snd_inl,
    GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, join_apply]

theorem dLine_inrH (G : WO A S → WO S A' → ℂ) (M : ℝ →+ WO S A') :
    dLine ψ W S ((inrH d S).comp M) (join d S G) = join d S (fun u v => dLine ψ S A' M (G u) v) := by
  funext x
  simp only [dLine, join_apply]
  congr 1
  funext t
  simp only [AddMonoidHom.comp_apply, heisO, symplOH_split d, map_add (fstH d S), map_add (sndH d S), fst_inr, snd_inr,
    GlobalTheory.WeilVacMove.symplOH_zero_right, zero_add, add_zero, join_apply]

end GlobalTheory.BiJoinDeriv

namespace GlobalTheory.BiJoinDeriv

open GlobalTheory.BiTransfer GlobalTheory.WeilVacMove

theorem dLine_join : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W A S A' : HSp D) (d : OrthDec W A (GlobalTheory.ChiGrid.negSp A')) (G : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' G → ∀ M : ℝ →+ WO W S, Continuous M → (∀ s, (M s).map (finPart D) = 0) → (∀ s, (GlobalTheory.BiTransfer.fstH d S (M s)).map (finPart D) = 0) ∧ (∀ s, (GlobalTheory.BiTransfer.sndH d S (M s)).map (finPart D) = 0) ∧ GlobalTheory.WeilVacMove.dLine ψ W S M (GlobalTheory.BiTransfer.join d S G) = GlobalTheory.BiTransfer.join d S fun u v => GlobalTheory.WeilVacMove.dLine ψ A S ((GlobalTheory.BiTransfer.fstH d S).comp M) (fun u' => G u' v) u + GlobalTheory.WeilVacMove.dLine ψ S A' ((GlobalTheory.BiTransfer.sndH d S).comp M) (G u) v := by
  intro D ψ hψ W A S A' d G hG M hM hM0
  have h1 : ∀ s, (fstH d S (M s)).map (finPart D) = 0 := fun s => map_mul_eq_zero_left _ (hM0 s) _
  have h2 : ∀ s, (sndH d S (M s)).map (finPart D) = 0 := fun s => fin_dagger A' S (map_mul_eq_zero_left _ (hM0 s) _)
  refine ⟨h1, h2, ?_⟩
  have hj := isThetaFunO_join d hG
  have eM : M = (inlH d S).comp ((fstH d S).comp M) + (inrH d S).comp ((sndH d S).comp M) := by
    ext1 t
    exact (inl_fst_add_inr_snd d S (M t)).symm
  rw [eM, dLine_add_line hψ ((continuous_inlH d S).comp ((continuous_fstH d S).comp hM)) (fun t => map_inlH d S _ (h1 t))
    ((continuous_inrH d S).comp ((continuous_sndH d S).comp hM)) (fun t => fin_inrH d S (h2 t)) hj,
    dLine_inlH, dLine_inrH, ← eM]
  funext x
  simp only [Pi.add_apply, join_apply]

end GlobalTheory.BiJoinDeriv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaPartialFourierIntegralMemAdelicSchwartz
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.IkSchwartz

open GlobalTheory.SchwartzBruhatTensor GlobalTheory.PartialIntegral

abbrev AEf (D : D7) : Type := Af D.host.F ⊗[D.host.F] D.host.E

theorem exists_split {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (m n : ℕ) :
    ∃ e : Mx D m n ≃ₜ+ (D.what₂.Tau → Fin m → Fin n → ℂ) × (Fin m → Fin n → AEf D),
      ∀ x, e x = (fun τ i j => compAt θ τ x i j, fun i j => finPart D (x i j)) := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨s, hsc, hsf, hsi⟩ := exists_finSection D
  refine ⟨{ toFun := fun x => (fun τ i j => compAt θ τ x i j, fun i j => finPart D (x i j))
            invFun := fun p => s.mapMatrix (Matrix.of p.2) + chartM σ m n p.1
            left_inv := fun x => (decomp hσ hsf hsi x).symm
            right_inv := fun p => Prod.ext ?_ ?_
            map_add' := fun x y => Prod.ext ?_ ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun x => rfl⟩
  · funext τ i j
    show θ τ (infPart D (s (p.2 i j) + σ fun τ => p.1 τ i j)) = p.1 τ i j
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hsi, hσ.comp, RingHom.map_zero, zero_add]
  · funext i j
    show finPart D (s (p.2 i j) + σ fun τ => p.1 τ i j) = p.2 i j
    rw [RingHom.map_add (f := _), hsf, hσ.fin, add_zero]
  · funext τ i j
    show θ τ (infPart D (x i j + y i j)) = θ τ (infPart D (x i j)) + θ τ (infPart D (y i j))
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _)]
  · funext i j
    exact (finPart D).map_add _ _
  · exact (continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.FockCompare.continuous_comp hθ τ).comp (continuous_id.matrix_elem i j)).prodMk
      (continuous_pi fun i => continuous_pi fun j =>
        (GlobalTheory.Member.continuous_finPart D).comp (continuous_id.matrix_elem i j))
  · haveI := (lattice_Mx D m n).1
    refine Continuous.add ?_ ((continuous_chartM hσ.cont m n).comp continuous_fst)
    exact continuous_pi fun i => continuous_pi fun j =>
      hsc.comp ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))

def lmul {R : Type} [CommRing R] {m t : ℕ} (n : ℕ) (J : Matrix (Fin m) (Fin t) R) (x : Fin t → Fin n → R) :
    Fin m → Fin n → R := J ⬝ Matrix.of x

theorem continuous_lmul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m t : ℕ} (n : ℕ)
    (J : Matrix (Fin m) (Fin t) R) : Continuous (lmul n J) :=
  Continuous.matrix_mul (A := fun _ => J) (B := fun x : Matrix (Fin t) (Fin n) R => x) continuous_const continuous_id

def lmulC {ι : Type} {m t : ℕ} (n : ℕ) (J : ι → Matrix (Fin m) (Fin t) ℂ) :
    (ι → Fin t → Fin n → ℂ) →ₗ[ℝ] (ι → Fin m → Fin n → ℂ) where
  toFun c τ := lmul n (J τ) (c τ)
  map_add' c c' := funext fun τ => Matrix.mul_add (J τ) (Matrix.of (c τ)) (Matrix.of (c' τ))
  map_smul' r c := funext fun τ => Matrix.mul_smul (J τ) r (Matrix.of (c τ))

variable {D : D7} {T T' : HSp D} {t : ℕ} (d : HypDec T T' t) {R : Type} [CommRing R] (φ : AE D →+* R) {n : ℕ}

theorem map_emb (x : Mx D t n) (a : Mx D T'.rank n) :
    (fun i j => φ ((d.jX ⬝ x + d.j0 ⬝ a : Mx D T.rank n) i j)) =
      lmul n (d.jX.map φ) (fun i j => φ (x i j)) + lmul n (d.j0.map φ) (fun i j => φ (a i j)) := by
  show (d.jX ⬝ x + d.j0 ⬝ a : Mx D T.rank n).map φ = d.jX.map φ ⬝ x.map φ + d.j0.map φ ⬝ a.map φ
  ext i j
  simp [Matrix.mul_apply, map_sum]

theorem pX_emb (x : Fin t → Fin n → R) (a : Fin T'.rank → Fin n → R) :
    lmul n (d.pX.map φ) (lmul n (d.jX.map φ) x + lmul n (d.j0.map φ) a) = x := by
  show d.pX.map φ ⬝ (d.jX.map φ ⬝ Matrix.of x + d.j0.map φ ⬝ Matrix.of a) = Matrix.of x
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, d.pX_jX, d.pX_j0,
    Matrix.map_one _ φ.map_zero φ.map_one, Matrix.map_zero _ φ.map_zero, Matrix.one_mul, Matrix.zero_mul, add_zero]

theorem wittHyperbolic_projAnisotropic_leftMul_embedding (x : Fin t → Fin n → R) (a : Fin T'.rank → Fin n → R) :
    lmul n (d.p0.map φ) (lmul n (d.jX.map φ) x + lmul n (d.j0.map φ) a) = a := by
  show d.p0.map φ ⬝ (d.jX.map φ ⬝ Matrix.of x + d.j0.map φ ⬝ Matrix.of a) = Matrix.of a
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, d.p0_jX, d.p0_j0,
    Matrix.map_one _ φ.map_zero φ.map_one, Matrix.map_zero _ φ.map_zero, Matrix.one_mul, Matrix.zero_mul, zero_add]

theorem map_emb_fin (x : Mx D t n) (a : Mx D T'.rank n) :
    (fun i j => finPart D ((d.jX ⬝ x + d.j0 ⬝ a : Mx D T.rank n) i j)) =
      lmul n (d.jX.map (finPart D)) (fun i j => finPart D (x i j)) +
        lmul n (d.j0.map (finPart D)) (fun i j => finPart D (a i j)) := map_emb d (finPart D) x a


set_option maxHeartbeats 800000 in
theorem pure {θ : InfFam D} (hθ : IsInfFam θ) (μ : Measure (Mx D t n)) [μ.IsAddHaarMeasure]
    (f : SchwartzMap (D.what₂.Tau → Fin T.rank → Fin n → ℂ) ℂ) (g : (Fin T.rank → Fin n → AEf D) → ℂ)
    (hg : g ∈ WeilM.SB (Fin T.rank → Fin n → AEf D)) (Φ : Mx D T.rank n → ℂ)
    (hΦ : Φ = fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))) :
    (∀ a : Mx D T'.rank n, Integrable (fun x : Mx D t n => Φ (d.jX ⬝ x + d.j0 ⬝ a)) μ) ∧ ikS d μ Φ ∈ schwartzA θ T'.rank n := by
  haveI : IsModuleTopology (Af D.host.F) (AEf D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AEf D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  haveI : LocallyCompactSpace (AEf D) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AEf D) := e0.secondCountableTopology
  haveI : T2Space (AEf D) := e0.isEmbedding.t2Space
  letI : MeasurableSpace (Fin t → Fin n → AEf D) := borel _
  haveI : BorelSpace (Fin t → Fin n → AEf D) := ⟨rfl⟩
  haveI : BorelSpace (Mx D t n) := ⟨rfl⟩
  haveI := (lattice_Mx D t n).1
  obtain ⟨e, he⟩ := exists_split hθ t n
  let μr : Measure (D.what₂.Tau → Fin t → Fin n → ℂ) := Measure.addHaar
  let ν : Measure (Fin t → Fin n → AEf D) := Measure.addHaar
  obtain ⟨c, hc⟩ := exists_integral_split e μ μr ν
  let φ : D.what₂.Tau → AE D →+* ℂ := fun τ => (θ τ).comp (infPart D)
  obtain ⟨hf1, h, hh⟩ := schwartz_partial μr f (lmulC n fun τ => d.jX.map (φ τ)) (lmulC n fun τ => d.j0.map (φ τ))
    (fun x a hxa => by
      refine ⟨funext fun τ => ?_, funext fun τ => ?_⟩
      · have h0 : lmul n (d.jX.map (φ τ)) (x τ) + lmul n (d.j0.map (φ τ)) (a τ) = 0 := congrFun hxa τ
        rw [← pX_emb d (φ τ) (x τ) (a τ), h0]
        exact Matrix.mul_zero _
      · have h0 : lmul n (d.jX.map (φ τ)) (x τ) + lmul n (d.j0.map (φ τ)) (a τ) = 0 := congrFun hxa τ
        rw [← wittHyperbolic_projAnisotropic_leftMul_embedding d (φ τ) (x τ) (a τ), h0]
        exact Matrix.mul_zero _)
  obtain ⟨hg1, hg2, hg3⟩ := locallyConstant_partial ν hg.1 hg.2 (continuous_lmul n (d.jX.map (finPart D)))
    (continuous_lmul n (d.j0.map (finPart D))) (continuous_lmul n (d.pX.map (finPart D)))
    (continuous_lmul n (d.p0.map (finPart D))) (pX_emb d (finPart D)) (wittHyperbolic_projAnisotropic_leftMul_embedding d (finPart D))
  have key : ∀ a : Mx D T'.rank n, (fun x : Mx D t n => Φ (d.jX ⬝ x + d.j0 ⬝ a)) = fun x =>
      f (lmulC n (fun τ => d.jX.map (φ τ)) (e x).1 + lmulC n (fun τ => d.j0.map (φ τ)) fun τ i j => compAt θ τ a i j) *
      g (lmul n (d.jX.map (finPart D)) (e x).2 + lmul n (d.j0.map (finPart D)) fun i j => finPart D (a i j)) := by
    intro a
    funext x
    have h2 : (fun τ i j => compAt θ τ (d.jX ⬝ x + d.j0 ⬝ a : Mx D T.rank n) i j) =
        lmulC n (fun τ => d.jX.map (φ τ)) (fun τ i j => compAt θ τ x i j) +
          lmulC n (fun τ => d.j0.map (φ τ)) fun τ i j => compAt θ τ a i j := funext fun τ => map_emb d (φ τ) x a
    rw [hΦ, he]
    exact congrArg₂ (· * ·) (congrArg f h2) (congrArg g (map_emb_fin d x a))
  refine ⟨fun a => by rw [key a]; exact (hc _ _ (hf1 _) (hg1 _)).1, ?_⟩
  have e2 : ikS d μ Φ = c • fun a : Mx D T'.rank n => h (fun τ i j => compAt θ τ a i j) *
      (fun b => ∫ y, g (lmul n (d.jX.map (finPart D)) y + lmul n (d.j0.map (finPart D)) b) ∂ν)
        (fun i j => finPart D (a i j)) := by
    funext a
    refine (congrArg (fun F => ∫ x, F x ∂μ) (key a)).trans ?_
    refine (hc _ _ (hf1 _) (hg1 _)).2.trans ?_
    rw [← hh]
    rfl
  rw [e2]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨h, _, ⟨hg2, hg3⟩, rfl⟩)

theorem ikS_mem_schwartzA : ∀ (D : D7), ∀ θ : InfFam D, IsInfFam θ → ∀ (T T' : HSp D) (t n : ℕ) (d : HypDec T T' t) (μ : Measure (Mx D t n)) (𝓕 : Set (Mx D t n)), IsCovolOne (ratMx D t n) μ 𝓕 → ∀ Φ ∈ schwartzA θ T.rank n, ikS d μ Φ ∈ schwartzA θ T'.rank n := by
  intro D θ hθ T T' t n d μ 𝓕 hμ Φ hΦ
  haveI := hμ.1
  suffices h : (∀ a : Mx D T'.rank n, Integrable (fun x : Mx D t n => Φ (d.jX ⬝ x + d.j0 ⬝ a)) μ) ∧ ikS d μ Φ ∈ schwartzA θ T'.rank n from h.2
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, h⟩ := h
    exact pure d hθ μ f g hg Φ h
  | zero =>
    refine ⟨fun a => integrable_zero _ _ _, ?_⟩
    have : ikS d μ (0 : Mx D T.rank n → ℂ) = 0 := funext fun a => integral_zero _ _
    rw [this]
    exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    refine ⟨fun a => (h1.1 a).add (h2.1 a), ?_⟩
    have : ikS d μ (Φ + Ψ) = ikS d μ Φ + ikS d μ Ψ := funext fun a => integral_add (h1.1 a) (h2.1 a)
    rw [this]
    exact Submodule.add_mem _ h1.2 h2.2
  | smul c Φ _ h =>
    refine ⟨fun a => (h.1 a).smul c, ?_⟩
    have : ikS d μ (c • Φ) = c • ikS d μ Φ := funext fun a => integral_smul c _
    rw [this]
    exact Submodule.smul_mem _ c h.2

end GlobalTheory.RegSch.IkSchwartz

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaHeisenbergDeriv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BiDeriv

open GlobalTheory.BiTransfer

variable {D : D7}

theorem dLine_inl (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (G : WO A S → WO S A' → ℂ) (M : ℝ →+ WO A S) :
    GlobalTheory.WeilVacMove.dLine ψ _ S ((inlH (sumDec A (GlobalTheory.ChiGrid.negSp A')) S).comp M) (join (sumDec A (GlobalTheory.ChiGrid.negSp A')) S G) =
      join (sumDec A (GlobalTheory.ChiGrid.negSp A')) S (fun u v => GlobalTheory.WeilVacMove.dLine ψ A S M (fun u' => G u' v) u) := by
  funext x
  simp only [GlobalTheory.WeilVacMove.dLine, join_apply]
  congr 1
  funext t
  simp only [AddMonoidHom.comp_apply, heisO, join_apply, map_add, fst_inl, snd_inl, add_zero]
  rw [symplOH_split (sumDec A (GlobalTheory.ChiGrid.negSp A')) S, fst_inl, snd_inl,
    GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero]

theorem dLine_inr (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (G : WO A S → WO S A' → ℂ) (M : ℝ →+ WO S A') :
    GlobalTheory.WeilVacMove.dLine ψ _ S ((inrH (sumDec A (GlobalTheory.ChiGrid.negSp A')) S).comp M) (join (sumDec A (GlobalTheory.ChiGrid.negSp A')) S G) =
      join (sumDec A (GlobalTheory.ChiGrid.negSp A')) S (fun u v => GlobalTheory.WeilVacMove.dLine ψ S A' M (G u) v) := by
  funext x
  simp only [GlobalTheory.WeilVacMove.dLine, join_apply]
  congr 1
  funext t
  simp only [AddMonoidHom.comp_apply, heisO, join_apply, map_add, fst_inr, snd_inr, add_zero]
  rw [symplOH_split (sumDec A (GlobalTheory.ChiGrid.negSp A')) S, fst_inr, snd_inr,
    GlobalTheory.WeilVacMove.symplOH_zero_right, zero_add]

theorem isBiTheta_dLine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A S A' : HSp D) (G : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' G → (∀ M : ℝ →+ WO A S, Continuous M → (∀ s, (M s).map (finPart D) = 0) → IsBiTheta ψ A S A' fun u v => GlobalTheory.WeilVacMove.dLine ψ A S M (fun u' => G u' v) u) ∧ ∀ M' : ℝ →+ WO S A', Continuous M' → (∀ s, (M' s).map (finPart D) = 0) → IsBiTheta ψ A S A' fun u v => GlobalTheory.WeilVacMove.dLine ψ S A' M' (G u) v := by
  intro D ψ hψ A S A' G hG
  have hj := isThetaFunO_join (sumDec A (GlobalTheory.ChiGrid.negSp A')) hG
  refine ⟨fun M hM hM0 => ?_, fun M hM hM0 => ?_⟩
  · have h := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ (L := (inlH (sumDec A (GlobalTheory.ChiGrid.negSp A')) S).comp M) ((continuous_inlH _ S).comp hM)
      (fun t => map_inlH _ S _ (hM0 t)) hj).2
    rw [dLine_inl] at h
    exact isBiTheta_of_join _ h
  · have h := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ (L := (inrH (sumDec A (GlobalTheory.ChiGrid.negSp A')) S).comp M) ((continuous_inrH _ S).comp hM)
      (fun t => fin_inrH _ S (hM0 t)) hj).2
    rw [dLine_inr] at h
    exact isBiTheta_of_join _ h

end GlobalTheory.BiDeriv

end
end

