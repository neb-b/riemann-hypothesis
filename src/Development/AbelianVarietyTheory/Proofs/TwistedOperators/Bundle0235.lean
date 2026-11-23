module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransferOfFundamentalDomains
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionIsotropicSplitSmoothRealPoints
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerSmooth

open GlobalTheory.WeilVacMove

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {k : ℕ}

def rayHom (v : Fin k → ℝ) : ℝ →+ (Fin k → ℝ) where
  toFun s := s • v
  map_zero' := zero_smul _ _
  map_add' a b := add_smul a b v

theorem continuous_rayHom (v : Fin k → ℝ) : Continuous (rayHom v) :=
  continuous_id.smul continuous_const

def coordC (i : Fin k) : (Fin k → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

theorem clm_eq_sum (l : (Fin k → ℝ) →L[ℝ] ℂ) : l = ∑ i, l (Pi.single i 1) • coordC i := by
  ext v
  have e : ∀ i, (Pi.single i (v i) : Fin k → ℝ) = v i • Pi.single i (1 : ℝ) := by
    intro i; ext j; by_cases h : j = i
    · subst h; simp
    · simp [h]
  conv_lhs => rw [← Finset.univ_sum_single v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, e, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, coordC, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, smul_eq_mul, Complex.real_smul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem hasFDerivAt_coord (hψ : IsStdChar D ψ (-1)) {M : (Fin k → ℝ) →+ WO S T} (hM : Continuous M)
    (hM0 : ∀ t, (M t).map (finPart D) = 0) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g)
    {lam : AF D.host.F →+ ℂ} (hl : Continuous lam)
    (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)) (p : WO S T) (t : Fin k → ℝ) :
    HasFDerivAt (fun t' => g (p + M t'))
      (∑ i, (dLine ψ S T (M.comp (rayHom (Pi.single i 1))) g (p + M t) -
        phase lam S T (M (Pi.single i 1)) (p + M t) * g (p + M t)) • coordC i) t := by
  have hs := hg.smooth k M hM hM0 p
  have hd : HasFDerivAt (fun t' => g (p + M t')) (fderiv ℝ (fun t' => g (p + M t')) t) t :=
    ((hs.differentiable (by simp)) t).hasFDerivAt
  convert hd using 1
  conv_rhs => rw [clm_eq_sum (fderiv ℝ (fun t' => g (p + M t')) t)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  set e : Fin k → ℝ := Pi.single i 1
  set N : ℝ →+ WO S T := M.comp (rayHom e)
  have hN : Continuous N := hM.comp (continuous_rayHom e)
  have hN0 : ∀ s, (N s).map (finPart D) = 0 := fun s => hM0 _
  have hN1 : N 1 = M e := by simp [N, rayHom]
  set x := p + M t
  set ph := phase lam S T (M e) x
  have hline : HasDerivAt (fun s : ℝ => t + s • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add t
  have h1 : HasDerivAt (fun s : ℝ => g (p + M (t + s • e))) (fderiv ℝ (fun t' => g (p + M t')) t e) 0 := by
    have hd' : HasFDerivAt (fun t' => g (p + M t')) (fderiv ℝ (fun t' => g (p + M t')) t) (t + (0 : ℝ) • e) := by
      rw [zero_smul, add_zero]; exact hd
    exact hd'.comp_hasDerivAt (0 : ℝ) hline
  have h0 : HasDerivAt (fun s : ℝ => (s : ℂ) * -ph) (-ph) 0 := by
    simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id (0 : ℝ))).mul_const (-ph)
  have hh := (hasDerivAt_zero_and_isTheta hψ hN hN0 hg).1 x
  have h2 := h0.cexp.mul hh
  have eq : (fun s : ℝ => g (p + M (t + s • e))) =
      fun s : ℝ => Complex.exp ((s : ℂ) * -ph) * heisO ψ S T (N s) g x := by
    funext s
    have hp := psi_sympl_line hl hlam hN hN0 x s
    rw [hN1] at hp
    rw [heisO, hp, ← mul_assoc, ← Complex.exp_add]
    have : (s : ℂ) * -ph + s * ph = 0 := by ring
    rw [this, Complex.exp_zero, one_mul]
    simp only [N, x, AddMonoidHom.comp_apply, rayHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_add (f := _), add_assoc]
  rw [eq] at h1
  have hz : N 0 = 0 := map_zero N
  have h3 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * -ph) * heisO ψ S T (N s) g x)
      (dLine ψ S T N g x - ph * g x) 0 := by
    refine h2.congr_deriv ?_
    rw [hz, heisO_zero]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    ring
  exact (h1.unique h3).symm

end GlobalTheory.TowerSmooth

namespace GlobalTheory.TowerSmooth

open GlobalTheory.WeilVacMove

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {k : ℕ}

theorem contDiff_integral (hψ : IsStdChar D ψ (-1)) {X : Type} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] {q : X → WO S T} (hq : Continuous q)
    {M : (Fin k → ℝ) →+ WO S T} (hM : Continuous M) (hM0 : ∀ t, (M t).map (finPart D) = 0)
    (b : Fin k → AF D.host.F) (hb : ∀ i y, symplOH S T (q y) (M (Pi.single i 1)) = b i)
    (g : WO S T → ℂ) (hg : IsThetaFunO ψ S T g) : ContDiff ℝ ∞ fun t => ∫ y, g (q y + M t) ∂ν := by
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  let a : Fin k → (Fin k → ℝ) → ℂ := fun i t => lam (b i) + phase lam S T (M (Pi.single i 1)) (M t)
  have ha : ∀ i y t, phase lam S T (M (Pi.single i 1)) (q y + M t) = a i t := by
    intro i y t
    rw [map_add (f := _)]
    congr 1
    show lam (symplOH S T (q y) (M (Pi.single i 1))) = lam (b i)
    rw [hb]
  have haC : ∀ i, ContDiff ℝ ∞ (a i) := fun i =>
    contDiff_const.add (contDiff_additive ((phase lam S T (M (Pi.single i 1))).comp M)
      (hl.comp (continuous_symplOH S T hM continuous_const)))
  let G : (WO S T → ℂ) → (Fin k → ℝ) → ℂ := fun h t => ∫ y, h (q y + M t) ∂ν
  let N : Fin k → ℝ →+ WO S T := fun i => M.comp (rayHom (Pi.single i 1))
  have hN : ∀ i, Continuous (N i) := fun i => hM.comp (continuous_rayHom _)
  have hN0 : ∀ i s, (N i s).map (finPart D) = 0 := fun i s => hM0 _
  have hdt : ∀ h, IsThetaFunO ψ S T h → ∀ i, IsThetaFunO ψ S T (dLine ψ S T (N i) h) := fun h hh i =>
    (hasDerivAt_zero_and_isTheta hψ (hN i) (hN0 i) hh).2
  have hcq : ∀ t, Continuous fun y => q y + M t := fun t => hq.add continuous_const
  have hint : ∀ h, IsThetaFunO ψ S T h → ∀ t, Integrable (fun y => h (q y + M t)) ν := by
    intro h hh t
    obtain ⟨C, hC⟩ := exists_bound hψ hh
    exact Integrable.of_bound (hh.cont.comp (hcq t)).aestronglyMeasurable C (ae_of_all _ fun y => hC _)
  have hder : ∀ h, IsThetaFunO ψ S T h → ∀ t₀, HasFDerivAt (G h)
      (∑ i, (G (dLine ψ S T (N i) h) t₀ - a i t₀ * G h t₀) • coordC i) t₀ := by
    intro h hh t₀
    obtain ⟨C0, hC0⟩ := exists_bound hψ hh
    have hCd : ∀ i, ∃ C : ℝ, ∀ w, ‖dLine ψ S T (N i) h w‖ ≤ C := fun i => exists_bound hψ (hdt h hh i)
    choose Cd hCd using hCd
    have hA : ∀ i, ∃ C : ℝ, ∀ t ∈ Metric.closedBall t₀ 1, ‖a i t‖ ≤ C := fun i =>
      (isCompact_closedBall t₀ 1).exists_bound_of_continuousOn (haC i).continuous.continuousOn
    choose A hA using hA
    have hA0 : ∀ i, 0 ≤ A i := fun i =>
      (norm_nonneg _).trans (hA i t₀ (Metric.mem_closedBall_self zero_le_one))
    let F' : (Fin k → ℝ) → X → (Fin k → ℝ) →L[ℝ] ℂ := fun t y =>
      ∑ i, (dLine ψ S T (N i) h (q y + M t) - a i t * h (q y + M t)) • coordC i
    have hF' : ∀ y t, HasFDerivAt (fun t => h (q y + M t)) (F' t y) t := by
      intro y t
      have := hasFDerivAt_coord hψ hM hM0 hh hl hlam (q y) t
      simp only [ha] at this
      exact this
    have hbd : ∀ y, ∀ t ∈ Metric.ball t₀ 1, ‖F' t y‖ ≤ ∑ i, (Cd i + A i * C0) * ‖coordC (k := k) i‖ := by
      intro y t ht
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add (hCd i _) ?_)) (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_mul (hA i t (Metric.ball_subset_closedBall ht)) (hC0 _) (norm_nonneg _) (hA0 i)
    have hF'm : AEStronglyMeasurable (F' t₀) ν := by
      refine Continuous.aestronglyMeasurable ?_
      refine continuous_finsetSum _ fun i _ => ?_
      exact (((hdt h hh i).cont.comp (hcq t₀)).sub (continuous_const.mul (hh.cont.comp (hcq t₀)))).smul
        continuous_const
    have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := fun t y => h (q y + M t))
      (F' := F') (x₀ := t₀) (bound := fun _ => ∑ i, (Cd i + A i * C0) * ‖coordC (k := k) i‖)
      (Metric.ball_mem_nhds t₀ zero_lt_one)
      (Filter.Eventually.of_forall fun t => (hh.cont.comp (hcq t)).aestronglyMeasurable) (hint h hh t₀) hF'm
      (ae_of_all _ hbd) (integrable_const _) (ae_of_all _ fun y t _ => hF' y t)
    refine key.congr_fderiv ?_
    have hi : ∀ i, Integrable (fun y => (dLine ψ S T (N i) h (q y + M t₀) - a i t₀ * h (q y + M t₀)) • coordC i) ν :=
      fun i => ((hint _ (hdt h hh i) t₀).sub ((hint h hh t₀).const_mul _)).smul_const _
    show ∫ y, (∑ i, (dLine ψ S T (N i) h (q y + M t₀) - a i t₀ * h (q y + M t₀)) • coordC i) ∂ν = _
    rw [integral_finsetSum _ fun i _ => hi i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_const, integral_sub (hint _ (hdt h hh i) t₀) ((hint h hh t₀).const_mul _),
      integral_const_mul]
  have hn : ∀ n : ℕ, ∀ h, IsThetaFunO ψ S T h → ContDiff ℝ n (G h) := by
    intro n
    induction n with
    | zero =>
      intro h hh
      exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (hder h hh t).continuousAt)
    | succ n ih =>
      intro h hh
      rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
      refine ⟨_, ?_, hder h hh⟩
      refine ContDiff.sum fun i _ => ?_
      exact ((ih _ (hdt h hh i)).sub ((contDiff_infty.1 (haC i) n).mul (ih h hh))).smul contDiff_const
  exact contDiff_infty.2 fun n => hn n g hg

end GlobalTheory.TowerSmooth

namespace GlobalTheory.TowerSmooth

open GlobalTheory.WeilVacMove

theorem res_smooth : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), (∀ (y y' : Mx D W.rank r) (x x' : WO V' W), symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = symplOH V' W x x') → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ f, IsThetaFunO ψ V W f → ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO V' W), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => res V V' W C B μ 𝓨 f (w + L t) := by
  intro D V V' W r C B hform ψ hψ μ 𝓨 hcov f hf k L hL hL0 w
  have : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, hcov.2.2]; exact ENNReal.one_lt_top⟩
  let mid : WO V' W →+ WO V W :=
    { toFun := midPart V V' W B
      map_zero' := by simp [midPart]
      map_add' := fun x y => by simp [midPart, Matrix.add_mul] }
  have hmid : Continuous mid := continuous_id.matrix_mul continuous_const
  have hmid0 : ∀ x : WO V' W, x.map (finPart D) = 0 → (mid x).map (finPart D) = 0 := by
    intro x hx
    simp only [mid, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    unfold midPart
    rw [Matrix.map_mul, hx, Matrix.zero_mul]
  have hiso0 : isoPart V W C 0 = 0 := by simp [isoPart]
  have hq : Continuous fun y : Mx D W.rank r => isoPart V W C y + midPart V V' W B w :=
    (continuous_id.matrix_mul continuous_const).add continuous_const
  have hb : ∀ i y, symplOH V W (isoPart V W C y + midPart V V' W B w) ((mid.comp L) (Pi.single i 1)) =
      symplOH V' W w (L (Pi.single i 1)) := by
    intro i y
    have := hform y 0 w (L (Pi.single i 1))
    rwa [hiso0, zero_add] at this
  have key := contDiff_integral hψ (μ.restrict 𝓨) hq (hmid.comp hL) (fun t => hmid0 _ (hL0 t)) _ hb f hf
  convert key using 1
  funext t
  show ∫ y in 𝓨, f (isoPart V W C y + midPart V V' W B (w + L t)) ∂μ = _
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  show f (isoPart V W C y + mid (w + L t)) = f (isoPart V W C y + midPart V V' W B w + mid (L t))
  rw [map_add (f := _), add_assoc]
  rfl

end GlobalTheory.TowerSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedRowEvaluationSquareIntegrableNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvalNormTransfer

theorem castGA_mem_GFset {I I' : AutInst} (h : I = I') (x : I.GA) :
    castGA h x ∈ I'.GFset ↔ x ∈ I.GFset := by
  subst h; exact Iff.rfl

theorem iotaX_rat {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (g : GA D (D.sp.Y 0)) : g ∈ GQ (D.sp.Y 0) ↔ (iotaX X h).toMulEquiv g ∈ X.B.I.GFset := by
  rw [Formalism.IndefR.RationalEmbedding.iota_rat D g]
  exact (castGA_mem_GFset h.symm _).symm

theorem borel_inst {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : BorelSpace X.B.I.GA := by
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology X.B.I
  infer_instance

theorem exists_map_eq_smul {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (ν : Measure (GA D (D.sp.Y 0))) [ν.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧
      Measure.map (iotaX X h).toMulEquiv.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • ν := by
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology X.B.I
  obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.IndefR.Eqv.ga_facts D (D.sp.Y 0)
  haveI := X.B.haar
  haveI := X.B.sf
  haveI : BorelSpace X.B.I.GA := inferInstance
  haveI : (X.B.I.muA X.B.μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  set μ' := Measure.map (iotaX X h).toMulEquiv.symm (X.B.I.muA X.B.μf) with hμ'
  haveI hH : μ'.IsHaarMeasure :=
    (iotaX X h).toMulEquiv.symm.isHaarMeasure_map _ (iotaX X h).symm.continuous (iotaX X h).continuous
  refine ⟨(Measure.haarScalarFactor μ' ν : ℝ), ?_, ?_⟩
  · exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure μ' ν
  · rw [ENNReal.ofReal_coe_nnreal, ← ENNReal.smul_def]
    exact Measure.isMulLeftInvariant_eq_smul μ' ν

theorem evalTranslate_norm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ t ∈ GfC (Yc D 0), ∃ c : ℝ, 0 < c ∧ ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → ∀ S ∈ EP R F, MemLp (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) 2 (muX X) ∧ ∫ x, ‖(fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) x‖ ^ 2 ∂(muX X) = c * (ipM (MP R) R.ν0 R.fd0 S S).re ∧ ((ipM (MP R) R.ν0 R.fd0 S S).re = 0 → S = 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL hG hM t ht
  haveI hνH : R.ν0.IsHaarMeasure := hM.ν0.1.1
  obtain ⟨c, hc, hmap⟩ := @exists_map_eq_smul D X h R.ν0 hνH
  obtain ⟨hι, hιs⟩ := measurable_of_borel X (iotaX X h) (borel_inst X)
  have hTr : SquareIntegrableTransfer R.ν0 R.fd0 X (iotaX X h).toMulEquiv t c :=
    squareIntegrableTransfer_of_rational_points R.ν0 R.fd0 X _ t c hι hιs hc hmap hνH hM.ν0.2 (iotaX_rat X h)
  refine ⟨c, hc, fun v₀ hv S hS => ?_⟩
  have hI := _root_.GlobalTheory.GoodRowsLevel.eeat_sub_principal R hM
  have hS' : S ∈ R.EEat (R.levR F true) := hS
  have hMult : S ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F true)))
      (levChi _ (R.βY 0) (R.dat0 (R.levR F true))) := hS'.1
  have hcl := Formalism.IndefR.PeterssonHilbertSpace.mult_cont_left (M := R.MY 0) (θ := R.θ) (J := _) (χ := _) hMult v₀
  have hip := hI.2.2 _ S hS' S hS'
  have := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (Yc D 0)
  have hL2 : MemLp (S v₀) 2 (R.ν0.restrict R.fd0) := by
    refine (memLp_two_iff_integrable_sq_norm hcl.1.measurable.aestronglyMeasurable).2
      (((hip v₀ v₀).1).norm.congr (.of_forall fun x => ?_))
    simp only [norm_mul, norm_star, sq]
  obtain ⟨hm, hn⟩ := hTr (S v₀) hcl.1 hcl.2 hL2
  refine ⟨hm, hn.trans (congrArg (c * ·) (re_ipM_eq ⟨_, hip⟩ hv).symm), ?_⟩
  intro h0
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 (hI.2.1 _ hS')
  have hx : inner ℂ x x = ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e x) (R.HE.e x) := hM.HE.2.2 x x
  have hre : ‖x‖ ^ 2 = (ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e x) (R.HE.e x)).re := by
    rw [← hx]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) x).symm
  have h00 : ‖x‖ ^ 2 = 0 := hre.trans h0
  rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h00
  rw [h00]
  exact map_zero R.HE.e

end GlobalTheory.EvalNormTransfer
end
end

