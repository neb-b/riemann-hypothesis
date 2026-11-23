module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Formalism.LocalToGlobal.Columns.ChainTwAn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsGLExistsUnique
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0218

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaWordLimitsSmoothAlongRealPoints
section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaDens


open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.Size in
theorem sm_of_tendstoUniformly_words {G R A : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    [FiniteDimensional ℝ R] [Fintype A] (ι : R →+ G) (p : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (hp : ∀ x, p (ι x) = x)
    (v : A → R) (c : A → R →L[ℝ] ℝ) (hv : ∀ x, ∑ a, c a x • v a = x) (g : List A → ℕ → G → ℂ)
    (hg : ∀ l j, Sm ι (g l j)) (hd : ∀ a l j, g (a :: l) j = hD ι p om (v a) (g l j)) (F : List A → G → ℂ)
    (hF : ∀ l, TendstoUniformly (g l) (F l) Filter.atTop) (l : List A) : Sm ι (F l) := by
  intro w
  refine _root_.GlobalTheory.contDiff_of_class_tendstoLocallyUniformly v c hv (fun φ => ∃ l, φ = fun y => F l (w + ι y)) ?_ _ ⟨l, rfl⟩
  rintro _ ⟨l, rfl⟩
  have hU : ∀ l, TendstoLocallyUniformly (fun j y => g l j (w + ι y)) (fun y => F l (w + ι y)) Filter.atTop :=
    fun l => ((hF l).comp fun y => w + ι y).tendstoLocallyUniformly
  refine ⟨fun j y => g l j (w + ι y), fun j => (hg l j w).differentiable (by simp), hU l, fun a => ?_⟩
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : R => (om.flip (v a) (p w + x) : ℝ) :=
    (LinearMap.toContinuousLinearMap (om.flip (v a))).contDiff.comp (contDiff_const.add contDiff_id)
  have hα : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun x : R => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h1)
  refine ⟨_, hα, _, ⟨a :: l, rfl⟩, ?_⟩
  have hc : Continuous fun y => F l (w + ι y) :=
    (hU l).continuous (Filter.Eventually.of_forall fun j => (hg l j w).continuous).frequently
  have h0 : TendstoLocallyUniformly
      (fun (_ : ℕ) (x : R) => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ))
      (fun x : R => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ)) Filter.atTop :=
    fun U hU x => ⟨Set.univ, Filter.univ_mem, Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hU⟩
  have h2 := (h0.mul₀ (hU l) hα.continuous hc).add (hU (a :: l))
  have e : (fun j y => fderiv ℝ (fun y => g l j (w + ι y)) y (v a)) = fun j x =>
      (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ) * g l j (w + ι x) + g (a :: l) j (w + ι x) := by
    funext j x
    rw [hd, hD_eq_fderiv ι p om _ (hg l j), map_add p, hp, LinearMap.flip_apply]
    have := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : R => g l j (w + ι y)) (x := 0) x
    rw [add_zero] at this
    have e2 : (fun y : R => g l j (w + ι x + ι y)) = fun y => g l j (w + ι (x + y)) := by
      funext y
      rw [map_add (f := _), add_assoc]
    rw [← this, e2]
    ring
  rw [e]
  exact h2

theorem sum_coord_single {τs : Type} [Fintype τs] {m n : ℕ} (x : τs → Fin m → Fin n → ℂ)
    (v : τs × Fin m × Fin n × Bool → τs → Fin m → Fin n → ℂ)
    (hv : ∀ a τ i j, v a τ i j = if τ = a.1 then
      Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) i j else 0) :
    ∑ a : τs × Fin m × Fin n × Bool,
      (if a.2.2.2 then (x a.1 a.2.1 a.2.2.1).im else (x a.1 a.2.1 a.2.2.1).re) • v a = x := by
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, hv, Fintype.sum_prod_type, Matrix.single_apply]
  rw [Finset.sum_eq_single τ (fun b _ hb => by simp [hb.symm]) (by simp),
    Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp),
    Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp [add_comm]


open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.Size in
theorem contDiff_of_tendstoUniformly_words : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (u : ℕ → WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (u j)) → ∀ F : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) → WO S T → ℂ, (∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop) → ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => F l (w + L t) := by
  intro D ψ hψ θ hθ S T u hu F hF l
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  refine ((smooth_iff_sm_and_real_lines D θ σ h T S).1 (F l)).2 ?_
  let z : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun a =>
    Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)
  let c : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool → RW T S →L[ℝ] ℝ := fun a =>
    (if a.2.2.2 then Complex.imCLM else Complex.reCLM).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin S.rank => ℂ) a.2.2.1).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin T.rank => Fin S.rank → ℂ) a.2.1).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin T.rank → Fin S.rank → ℂ) a.1)))
  refine sm_of_tendstoUniformly_words (iotaW σ T S) (piW θ T S) (omO S T) (h.pi_iota T S)
    (fun a => piW θ T S (lineAt θ a.1 (z a) 1)) c (fun x => ?_) (fun l j => wordAct (heisDer ψ θ) l (u j))
    (fun l j => theta_sm h (theta_word hψ hθ l (hu j)))
    (fun a l j => dLine_eq_hD h hψ (isRealDir_lineAt hθ a.1 (z a)) _) F hF l
  refine Eq.trans ?_ (sum_coord_single x (fun a => piW θ T S (lineAt θ a.1 (z a) 1)) fun a τ i j => ?_)
  · refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    obtain ⟨τ, i, j, b⟩ := a
    cases b <;> rfl
  · have := congrFun (congrFun ((GlobalTheory.OrientedHeis.isLineAt_lineAt hθ a.1 (z a)).2.2 1 τ) i) j
    refine Eq.trans this ?_
    split_ifs <;> simp [z, *]

end GlobalTheory.ThetaDens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslatedEvaluationRowsConjLinearBijection
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem star_comp_const_smul_eq_conj_smul {α : Type*} (a : ℂ) (F : α → ℂ) :
    (fun x => star ((a • F) x)) = (starRingEnd ℂ a) • (fun x => star (F x)) := by
  funext x
  simp [star_mul']

end GlobalTheory.Core.Mi

namespace GlobalTheory.Core.Mi


set_option maxHeartbeats 2000000 in
theorem evalAll_rows : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → ConjVec X h θ M v₀ → EvalAll X h θ M J χ t v₀ ∧ ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1 := by
  intro hDS hCusp D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj
  have hnorm : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1 := by
    intro τ
    obtain ⟨c, -, hc⟩ := hConj
    have h1 := (X.low (X.pl.symm τ)).1
    rw [← (c τ).norm_map, hc τ]
    exact h1
  have hne : ∀ τ, (v₀ τ : M.H τ) ≠ 0 := fun τ h0 => by
    have := hnorm τ; rw [h0, norm_zero] at this; exact zero_ne_one this
  have hfun := _root_.GlobalTheory.Core.Mi.rowFun_evS hCusp D X h θ S M J χ t hθ hMat
  obtain ⟨f, hf⟩ : ∃ f : MultT θ M J χ → L2X X, ∀ T : MultT θ M J χ, ((f T : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
      evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) :=
    ⟨fun T => ((hfun T.1 T.2 (PiTensorProduct.tprod ℂ v₀)).2).toLp _, fun T => MemLp.coeFn_toLp _⟩
  have hmem : ∀ T : MultT θ M J χ, star (f T) ∈ HHX X := fun T =>
    _root_.GlobalTheory.Core.Mi.SeeHH.conj_evS_mem_HHX hCusp D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj T.1 T.2 (f T) (hf T)
  have hstar : ∀ T : MultT θ M J χ, ((star (f T) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
      fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x) := fun T => by
    filter_upwards [Lp.coeFn_star (f T), hf T] with x h1 h2
    rw [h1, Pi.star_apply, h2]
  have e1 : ∀ T T' : MultT θ M J χ, (fun x => star (evS X h t ((T + T').1 (PiTensorProduct.tprod ℂ v₀)) x)) =
      (fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)) +
        (fun x => star (evS X h t (T'.1 (PiTensorProduct.tprod ℂ v₀)) x)) := by
    intro T T'
    rw [Submodule.coe_add, LinearMap.add_apply]
    funext x
    exact star_add _ _
  have e2 : ∀ (a : ℂ) (T : MultT θ M J χ), (fun x => star (evS X h t ((a • T).1 (PiTensorProduct.tprod ℂ v₀)) x)) =
      (starRingEnd ℂ a) • (fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)) := by
    intro a T
    rw [Submodule.coe_smul, LinearMap.smul_apply]
    generalize T.1 (PiTensorProduct.tprod ℂ v₀) = F
    exact star_comp_const_smul_eq_conj_smul a (evS X h t F)
  let j : MultT θ M J χ →ₗ⋆[ℂ] HHX X :=
    { toFun := fun T => ⟨star (f T), hmem T⟩
      map_add' := fun T T' => by
        apply Subtype.ext
        show star (f (T + T')) = star (f T) + star (f T')
        apply Lp.ext
        refine (hstar (T + T')).trans ?_
        rw [e1]
        exact ((hstar T).add (hstar T')).symm.trans (Lp.coeFn_add _ _).symm
      map_smul' := fun a T => by
        apply Subtype.ext
        rw [Submodule.coe_smul]
        apply Lp.ext
        refine (hstar (a • T)).trans ?_
        rw [e2]
        exact ((hstar T).const_smul (starRingEnd ℂ a)).symm.trans (Lp.coeFn_smul _ _).symm }
  have hj : ∀ T, (((j T : HHX X) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
      fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x) := hstar
  refine ⟨⟨j, ⟨?_, ?_⟩, hj⟩, hnorm⟩
  · rw [injective_iff_map_eq_zero]
    intro T hT
    have h0 : (((j T : HHX X) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] 0 := by
      rw [hT]; exact Lp.coeFn_zero _ _ _
    have hev : evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) =ᵐ[muX X] 0 := by
      filter_upwards [hj T, h0] with x h1 h2
      rw [h2] at h1
      have h3 := congrArg star h1
      rw [star_star] at h3
      rw [← h3]
      exact star_zero _
    exact Subtype.ext (_root_.GlobalTheory.Core.Mi.multT_eq_zero_of_evS_ae D X h θ S M J χ t v₀ hθ hne T.1 T.2 hev)
  · intro ψ
    have hψ : star (star (ψ : L2X X)) ∈ HHX X := by rw [star_star]; exact ψ.2
    obtain ⟨T, hT, hTe⟩ := _root_.GlobalTheory.Core.SeeOnto.see_onto hDS D X h θ S M J χ t v₀ hS hθ hGap hIdE hMat hConj
      (star (ψ : L2X X)) hψ
    refine ⟨⟨T, hT⟩, ?_⟩
    apply Subtype.ext
    apply Lp.ext
    refine (hj ⟨T, hT⟩).trans ?_
    filter_upwards [Lp.coeFn_star (ψ : L2X X), hTe] with x h2 h3
    rw [h2, Pi.star_apply] at h3
    rw [← h3, star_star]

end GlobalTheory.Core.Mi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralTwistPrimeEqDeepFiniteSum
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwSumAgree

theorem sumAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → SumAgree Ch sel mu cst σ₀ P ι s W ν := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hok hAt
  have hPA := GlobalTheory.T.parahoric_test_functions_agree_rational_points X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hAt
  have hiL := GlobalTheory.Proof.TwistSupportPeriodicLevels.ofTwist_support_periodic_levels k s (Fin R.k ⊕ Fin (s + 1)) (Fin R.t)
    (Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2)) (XIx (Fin R.k) (Fin R.t)) W.δ W.tame W.η
    (fun j c h => GlobalTheory.StepData.plainFrame (stdOrd (Fin R.k) (Fin R.t) j c h)) (LatFrame.refl k _) (fun _ _ _ => rfl)
  intro j c h a b g g' hag hbg' ha hb hD
  have hm := hAt.steps
  refine ⟨j + 1, j + 1, fun A' B' hA hB e' e hoe' hoe x => ?_⟩
  obtain ⟨E', hE', hg⟩ := id hag
  obtain ⟨E, hE, hg'⟩ := id hbg'
  have hj : j < R.m := by omega
  have hom := GlobalTheory.TwBridge.Model.om_agree Ch sel mu cst σ₀ P ι s W hAt hok j (c + 1) (c + 1 + 1) hj E' E a b g g' hg hg'
    ((W.T s R).Phi j (c + 1) (by omega)) (PhiAt Ch mu cst.sharp j P.1)
    (fun y => hPA.1 j (c + 1) (by omega) E' E hE' hE y)
  obtain ⟨h1, h2⟩ := GlobalTheory.T.completionMatrix_boundedRationalAut_integral ι W.ϖ P.1 hAt.nmem hAt.compl j (c + 1 + 1) a g hag ha
  obtain ⟨h1', h2'⟩ := GlobalTheory.T.completionMatrix_boundedRationalAut_integral ι W.ϖ P.1 hAt.nmem hAt.compl (j + 1) (c + 1) b g' hbg' hb
  have hSP := _root_.GlobalTheory.StepData.om_support_period W.ϖ ((W.unif W.ϖ).2 le_rfl) j ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega))
    (hiL.1 j (c + 1) (by omega)) (hiL.2.1 j (c + 1) (by omega)) g g' h1 h2 h1' h2'
  have hpsi : ∀ z, IntAt P.1 ((qOf P.1 : X.E) ^ (j + 1) * z) → (W.ψ (ι z) : ℂ) = σ₀ (cst.psi P z) :=
    fun z hz => hAt.psi z (twAn_qpow_mul (by omega) hz)
  have o1 : GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun z => (e' z).val) (R.N j)) E' := by
    rintro (z | z)
    · exact (hE' _).trans (hoe' z).symm
    · exact hE' _
  have o2 : GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun z => (e z).val) (R.N (j + 1))) E := by
    rintro (z | z)
    · exact (hE _).trans (hoe z).symm
    · exact hE _
  exact GlobalTheory.T.unfoldingIntegral_positionOne_eq_finite_sum X.E X.K k P.1 (qOf P.1) ι W.ϖ σ₀ W.ψ ν (cst.psi P) (j + 1) hAt.compl W.unif W.cond hν hpsi
    (XIx (Fin R.k) (Fin R.t) j) (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) (R.N j) (cOf R j) (R.N (j + 1)) (cOf R (j + 1))
    A' B' (by omega) (by unfold cOf; omega) (by unfold cOf; omega) hA hB e' e E' E o1 o2 _ _ _ hom hSP.1 hSP.2 x

end GlobalTheory.TwSumAgree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicSplit

open scoped NNReal ENNReal

section General

variable {A B : Type} [Group A] [Group B] [TopologicalSpace A] [TopologicalSpace B]
  [IsTopologicalGroup A] [IsTopologicalGroup B] [LocallyCompactSpace A] [LocallyCompactSpace B]
  [SecondCountableTopology A] [SecondCountableTopology B] [T2Space A] [T2Space B]
  [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B]

theorem rightInv_of_prod (h : ∀ μ : Measure (A × B), μ.IsHaarMeasure → μ.IsMulRightInvariant)
    (ν : Measure B) (hν : ν.IsHaarMeasure) : ν.IsMulRightInvariant := by
  refine ⟨fun b => ?_⟩
  let μA : Measure A := Measure.haar
  haveI := h (μA.prod ν) inferInstance
  set c := Measure.haarScalarFactor (ν.map (· * b)) ν
  have hc : ν.map (· * b) = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  have h1 : (μA.prod ν).map (· * ((1 : A), b)) = μA.prod (ν.map (· * b)) := by
    have e : (fun x : A × B => x * ((1 : A), b)) = Prod.map id (· * b) := by
      funext x
      simp [Prod.ext_iff]
    rw [e, ← Measure.map_prod_map _ _ measurable_id (measurable_mul_const b), Measure.map_id]
  have h3 : μA.prod ν = (c : ℝ≥0∞) • μA.prod ν := by
    rw [← Measure.prod_smul_right, ← ENNReal.smul_def, ← hc, ← h1, map_mul_right_eq_self]
  obtain K : TopologicalSpace.PositiveCompacts (A × B) := Classical.arbitrary _
  have hpos : 0 < μA.prod ν K := Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty
  have hfin : μA.prod ν K < ⊤ := K.isCompact.measure_lt_top
  have h4 := congrArg (fun m : Measure (A × B) => m K) h3
  simp only [Measure.smul_apply, smul_eq_mul] at h4
  have h5 : (c : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hpos.ne' hfin.ne).1 (h4.symm.trans (one_mul _).symm)
  rw [hc, ENNReal.smul_def, h5, one_smul]

end General

section Restr

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def restrEquiv (P Q R : Subgroup G) (e : P × Q ≃ₜ* G) (he : ∀ p, e p = p.1.1 * p.2.1)
    (hs : ∀ a ∈ P, ∀ b ∈ Q, a * b ∈ R → a ∈ R ∧ b ∈ R) :
    R.subgroupOf P × R.subgroupOf Q ≃ₜ* R where
  toFun x := ⟨e (x.1.1, x.2.1), by
    rw [he]; exact R.mul_mem (Subgroup.mem_subgroupOf.1 x.1.2) (Subgroup.mem_subgroupOf.1 x.2.2)⟩
  invFun r :=
    have hr : ((e.symm r.1).1 : G) * (e.symm r.1).2 ∈ R := by rw [← he, e.apply_symm_apply]; exact r.2
    (⟨(e.symm r.1).1, Subgroup.mem_subgroupOf.2 (hs _ (e.symm r.1).1.2 _ (e.symm r.1).2.2 hr).1⟩,
     ⟨(e.symm r.1).2, Subgroup.mem_subgroupOf.2 (hs _ (e.symm r.1).1.2 _ (e.symm r.1).2.2 hr).2⟩)
  left_inv x := by
    have h : e.symm (e (x.1.1, x.2.1)) = (x.1.1, x.2.1) := e.symm_apply_apply _
    ext
    · exact congrArg (fun p => (p.1 : G)) h
    · exact congrArg (fun p => (p.2 : G)) h
  right_inv r := Subtype.ext (e.apply_symm_apply r.1)
  map_mul' x y := Subtype.ext (by
    change e ((x * y).1.1, (x * y).2.1) = e (x.1.1, x.2.1) * e (y.1.1, y.2.1)
    rw [← map_mul]; rfl)
  continuous_toFun := by
    refine Continuous.subtype_mk (e.continuous.comp ?_) _
    exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have h0 : Continuous fun r : R => e.symm r.1 := e.symm.continuous.comp continuous_subtype_val
    exact (Continuous.subtype_mk (continuous_fst.comp h0) _).prodMk (Continuous.subtype_mk (continuous_snd.comp h0) _)

variable [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem rightInv_restr (P Q R : Subgroup G) (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
    (hR : IsClosed (R : Set G)) (e : P × Q ≃ₜ* G) (he : ∀ p, e p = p.1.1 * p.2.1)
    (hs : ∀ a ∈ P, ∀ b ∈ Q, a * b ∈ R → a ∈ R ∧ b ∈ R)
    (hu : ∀ μ : Measure R, μ.IsHaarMeasure → μ.IsMulRightInvariant) :
    ∀ ν : Measure (R.subgroupOf Q), ν.IsHaarMeasure → ν.IsMulRightInvariant := by
  haveI : LocallyCompactSpace P := hP.locallyCompactSpace
  haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  haveI : LocallyCompactSpace R := hR.locallyCompactSpace
  have hRP : IsClosed ((R.subgroupOf P : Subgroup P) : Set P) := hR.preimage continuous_subtype_val
  have hRQ : IsClosed ((R.subgroupOf Q : Subgroup Q) : Set Q) := hR.preimage continuous_subtype_val
  haveI : LocallyCompactSpace (R.subgroupOf P) := hRP.locallyCompactSpace
  haveI : LocallyCompactSpace (R.subgroupOf Q) := hRQ.locallyCompactSpace
  intro ν hν
  refine rightInv_of_prod (A := R.subgroupOf P) (fun μ hμ => ?_) ν hν
  haveI := hμ
  exact GlobalTheory.UpqUnimodular.isMulRightInvariant_of_continuousMulEquiv (restrEquiv P Q R e he hs) μ
    (hu _ (ContinuousMulEquiv.isHaarMeasure_map μ (restrEquiv P Q R e he hs)))

end Restr

section Adelic

open GlobalTheory.AdelicU

variable {D : D7}

theorem ofInf_projInf_of_mem (V : HSp D) {a : GA D V} (ha : a ∈ GinfC V) :
    ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram a) = a := by
  have h := ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram a
  rwa [mem_infPts.1 ha, map_one, mul_one] at h

theorem ofFin_projFin_of_mem (V : HSp D) {b : GA D V} (hb : b ∈ GfC V) :
    ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram b) = b := by
  have h := ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram b
  rwa [mem_finPts.1 hb, map_one, one_mul] at h

theorem commute_GinfC_GfC (V : HSp D) {a b : GA D V} (ha : a ∈ GinfC V) (hb : b ∈ GfC V) : a * b = b * a := by
  rw [← ofInf_projInf_of_mem V ha, ← ofFin_projFin_of_mem V hb]
  exact commute_ofInf_ofFin _ _ _ _

def splitEquiv (V : HSp D) : GinfC V × GfC V ≃ₜ* GA D V where
  toFun p := p.1.1 * p.2.1
  invFun g := (⟨ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g), mem_infPts.2 (by simp)⟩,
    ⟨ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g), mem_finPts.2 (by simp)⟩)
  left_inv p := by
    have h1 : projInf D.sp.cm.sig V.gram p.2.1 = 1 := mem_finPts.1 p.2.2
    have h2 : projFin D.sp.cm.sig V.gram p.1.1 = 1 := mem_infPts.1 p.1.2
    ext
    · change ofInf _ _ (projInf _ _ (p.1.1 * p.2.1)) = p.1.1
      rw [map_mul, h1, mul_one, ofInf_projInf_of_mem V p.1.2]
    · change ofFin _ _ (projFin _ _ (p.1.1 * p.2.1)) = p.2.1
      rw [map_mul, h2, one_mul, ofFin_projFin_of_mem V p.2.2]
  right_inv g := ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram g
  map_mul' p q := by
    change p.1.1 * q.1.1 * (p.2.1 * q.2.1) = p.1.1 * p.2.1 * (q.1.1 * q.2.1)
    rw [mul_assoc, ← mul_assoc q.1.1, commute_GinfC_GfC V q.1.2 p.2.2, mul_assoc, mul_assoc]
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun :=
    (((continuous_ofInf _ _).comp (continuous_projInf _ _)).subtype_mk _).prodMk
      (((continuous_ofFin _ _).comp (continuous_projFin _ _)).subtype_mk _)

theorem splitEquiv_apply (V : HSp D) (p : GinfC V × GfC V) : splitEquiv V p = p.1.1 * p.2.1 := rfl

theorem isClosed_GinfC' (V : HSp D) : IsClosed (GinfC V : Set (GA D V)) := isClosed_infPts _ _
theorem isClosed_GfC' (V : HSp D) : IsClosed (GfC V : Set (GA D V)) := isClosed_finPts _ _

end Adelic

theorem adelic_split : ∀ (D : D7) (V : HSp D), IsClosed (GinfC V : Set (GA D V)) ∧ IsClosed (GfC V : Set (GA D V)) ∧ (∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b = b * a) ∧ (∃ e : (GinfC V × GfC V) ≃ₜ GA D V, ∀ p, e p = p.1 * p.2) ∧ (∀ μ : Measure (GfC V), μ.IsHaarMeasure → μ.IsMulRightInvariant) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), ((∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ jacGrp d → a ∈ jacGrp d ∧ b ∈ jacGrp d) ∧ (∀ μ : Measure (jacGrp d), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ μ : Measure ((jacGrp d).subgroupOf (GfC V)), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), (∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ besGrp d o → a ∈ besGrp d o ∧ b ∈ besGrp d o) ∧ (∀ μ : Measure (besGrp d o), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ μ : Measure ((besGrp d o).subgroupOf (GfC V)), μ.IsHaarMeasure → μ.IsInvInvariant := by
  intro D V
  have hi := isClosed_GinfC' V
  have hf := isClosed_GfC' V
  haveI : LocallyCompactSpace (GinfC V) := hi.locallyCompactSpace
  haveI : LocallyCompactSpace (GfC V) := hf.locallyCompactSpace
  refine ⟨hi, hf, fun a ha b hb => commute_GinfC_GfC V ha hb, ⟨(splitEquiv V).toHomeomorph, fun p => rfl⟩,
    fun μ hμ => rightInv_of_prod (A := GinfC V) (fun m hm => ?_) μ hμ, fun V₀ ρ d => ?_⟩
  · haveI := hm
    exact GlobalTheory.UpqUnimodular.isMulRightInvariant_of_continuousMulEquiv (splitEquiv V) m
      (GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V _ inferInstance)
  have hJ := GlobalTheory.jacGrp_isClosed D V V₀ ρ d
  haveI : LocallyCompactSpace (jacGrp d) := hJ.locallyCompactSpace
  refine ⟨⟨_root_.GlobalTheory.jacGrp_split_inf_fin D V V₀ ρ d, fun μ hμ => ?_, fun μ hμ => ?_⟩, fun A L o => ?_⟩
  · haveI := hμ
    haveI := _root_.GlobalTheory.JacUnimod.jacGrp_rightInv D V V₀ ρ d μ hμ
    exact GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  · have hc : IsClosed (((jacGrp d).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) :=
      hJ.preimage continuous_subtype_val
    haveI : LocallyCompactSpace ((jacGrp d).subgroupOf (GfC V)) := hc.locallyCompactSpace
    haveI := hμ
    haveI := rightInv_restr (GinfC V) (GfC V) (jacGrp d) hi hf hJ (splitEquiv V) (splitEquiv_apply V)
      (_root_.GlobalTheory.jacGrp_split_inf_fin D V V₀ ρ d) (_root_.GlobalTheory.JacUnimod.jacGrp_rightInv D V V₀ ρ d) μ hμ
    exact GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  have hB := GlobalTheory.BesClosed.besGrp_isClosed D V V₀ A L ρ d o
  haveI : LocallyCompactSpace (besGrp d o) := hB.locallyCompactSpace
  refine ⟨_root_.GlobalTheory.BesSplit.besGrp_split D V V₀ A L ρ d o, fun μ hμ => ?_, fun μ hμ => ?_⟩
  · haveI := hμ
    haveI := _root_.GlobalTheory.BesUnimod.besGrp_isMulRightInvariant D V V₀ A L ρ d o μ hμ
    exact GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  · have hc : IsClosed (((besGrp d o).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) :=
      hB.preimage continuous_subtype_val
    haveI : LocallyCompactSpace ((besGrp d o).subgroupOf (GfC V)) := hc.locallyCompactSpace
    haveI := hμ
    haveI := rightInv_restr (GinfC V) (GfC V) (besGrp d o) hi hf hB (splitEquiv V) (splitEquiv_apply V)
      (_root_.GlobalTheory.BesSplit.besGrp_split D V V₀ A L ρ d o) (_root_.GlobalTheory.BesUnimod.besGrp_isMulRightInvariant D V V₀ A L ρ d o) μ hμ
    exact GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ

end GlobalTheory.AdelicSplit
end
end

