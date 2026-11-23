module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0542
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0562
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodGroupsReduceSplitPlaceFamilySucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0623

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnQuotHeightPowMulNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspFormApprox

variable {D : D7} {V : HSp D} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}

theorem integrableOn_one (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) :
    IntegrableOn (fun _ => (1 : ℝ)) 𝓕 μ := by
  simpa using GlobalTheory.Size.integrableOn_inv_quotHeight_pow (V := V) 0 hμ h𝓕

theorem integrableOn_of_le (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) {f : GA D V → ℝ}
    (hf : Continuous f) (h0 : ∀ g, 0 ≤ f g) {C : ℝ} (hC : ∀ g, f g ≤ C) :
    IntegrableOn f 𝓕 μ ∧ ∫ g in 𝓕, f g ∂μ ≤ C * ∫ _g in 𝓕, (1 : ℝ) ∂μ := by
  have h1 := integrableOn_one hμ h𝓕
  have hC' : IntegrableOn (fun _ => C * (1 : ℝ)) 𝓕 μ := h1.const_mul C
  have hi : IntegrableOn f 𝓕 μ := by
    refine Integrable.mono' hC' hf.aestronglyMeasurable (.of_forall fun g => ?_)
    rw [Real.norm_of_nonneg (h0 g), mul_one]
    exact hC g
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (.of_forall fun g => h0 g) hC' (.of_forall fun g => by simpa using hC g)

theorem integrableOn_quotHeight_pow_mul_norm (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ)
    {N : GlobalTheory.Grid.Node D} {μ : Measure (GA D N.V)} {𝓕 : Set (GA D N.V)} (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ N.V) 𝓕 μ) {φ : GA D N.V → ℂ} (hφ : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ) (b : ℕ) :
    IntegrableOn (fun g => GlobalTheory.Grow.quotHeight N.V g ^ b * ‖φ g‖) 𝓕 μ := by
  have hr := (GlobalTheory.Size.rapidDecSm_of_cuspForm hP hθ hφ.1 hφ.2.1).rapidDec
  obtain ⟨C, hC⟩ := hr.decay b
  refine (integrableOn_of_le hμ h𝓕 (((GlobalTheory.Grow.continuous_quotHeight N.V).pow b).mul hr.continuous.norm)
    (fun g => mul_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos N.V g).le b) (norm_nonneg _)) (C := C)
    (fun g => by rw [mul_comm]; exact hC g)).1

theorem weighted_uniform_approx_cusp_forms {θ : InfFam D} {N : GlobalTheory.Grid.Node D} {μ : Measure (GA D N.V)} {𝓕 : Set (GA D N.V)}
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ N.V) 𝓕 μ) {φ : GA D N.V → ℂ} (hc : Continuous φ) (b : ℕ)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧
      ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ b ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (Fs : Fin n → N.Maps) (vs : Fin n → SmT N.M), (∀ k, Fs k ∈ N.Cusp θ) ∧
      IntegrableOn (fun g => GlobalTheory.Grow.quotHeight N.V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖) 𝓕 μ ∧
      ∫ g in 𝓕, GlobalTheory.Grow.quotHeight N.V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖ ∂μ ≤ ε := by
  intro ε hε
  set I := ∫ _g in 𝓕, (1 : ℝ) ∂μ
  have hI : 0 ≤ I := integral_nonneg fun _ => zero_le_one
  obtain ⟨n, F, v, hF, h⟩ := hu (ε / (I + 1)) (div_pos hε (by linarith))
  have hcs : Continuous fun g => ∑ l, F l (v l) g := by
    have := continuous_finsetSum Finset.univ fun l _ =>
      GlobalTheory.BaseChain.multT_apply_continuous θ N.M ∅ 1 (F l) (hF l) (v l)
    simpa using this
  have hcf : Continuous fun g => GlobalTheory.Grow.quotHeight N.V g ^ b * ‖(∑ l, F l (v l) g) - φ g‖ :=
    ((GlobalTheory.Grow.continuous_quotHeight N.V).pow b).mul (hcs.sub hc).norm
  obtain ⟨hi, hle⟩ := integrableOn_of_le hμ h𝓕 hcf
    (fun g => mul_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos N.V g).le b) (norm_nonneg _)) (C := ε / (I + 1))
    (fun g => by rw [mul_comm, norm_sub_rev]; exact h g)
  refine ⟨n, F, v, hF, hi, hle.trans ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

end GlobalTheory.CuspFormApprox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableScalarActionMultiplicityMapValues
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ValAct

theorem integral_mul_multT_eq : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ t ∈ MultT θ M J χ, ∀ (w : M.Vec) (m : Measure (GinfC V)), m.IsHaarMeasure → ∀ (α : GinfC V → ℂ) (c : ℂ), Integrable α m → (∀ b : ∀ τ, M.H τ, ∫ h, α h * coefR θ M b (fun τ => w τ) h ∂m = c * ∏ τ, ⟪b τ, (w τ : M.H τ)⟫_ℂ) → ∀ x, ∫ h, α h * t (PiTensorProduct.tprod ℂ w) (x * h) ∂m = c * t (PiTensorProduct.tprod ℂ w) x := by
  intro hP D θ hθ V S M J χ t ht w m hm α c hα hc
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  obtain ⟨i1, i2, i3, i4, i5⟩ := Formalism.IndefR.Eqv.ga_facts D V
  obtain ⟨-, -, -, -, -, j6, j7, j8⟩ := GlobalTheory.RealMeasOne.ginfC_facts V
  haveI := hm
  haveI := Formalism.IndefR.Eqv.gQ_countable D V
  have hT : PiTensorProduct.lift.symm t ∈ Mult (Formalism.IndefR.Eqv.thetaC D) M J χ := (mem_multT _ M J χ t).1 ht
  have hTv : ∀ (v : M.Vec) g, (PiTensorProduct.lift.symm t) v g = t (PiTensorProduct.tprod ℂ v) g := fun v g => rfl
  have hEq := Formalism.IndefR.AutomorphicEvaluation.eqCont_of_mem hT
  obtain ⟨haut, hcusp, -⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP D V S M _ hθ J χ t ht (PiTensorProduct.tprod ℂ w)
  obtain ⟨B, hB⟩ := GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ haut hcusp
  have hφc : Continuous (t (PiTensorProduct.tprod ℂ w)) := GlobalTheory.BaseChain.multT_apply_continuous _ M J χ t ht _
  have htr : ∀ (h : GinfC V) y, t (PiTensorProduct.tprod ℂ w) (y * h) =
      t (PiTensorProduct.tprod ℂ (Formalism.L2.SG.EvalTEquiv.transl M h w)) y := fun h y => by
    have := Formalism.L2.SG.EvalTEquiv.equiv_ginf hθ hEq h.2 w y
    rwa [hTv, hTv] at this
  let μ : Measure (GA D V) := Measure.haar
  obtain ⟨𝓕, -, h𝓕⟩ := Formalism.IndefR.Eqv.fundDomExists_holds D V
  have hfd := h𝓕 μ
  have hfin : μ 𝓕 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 inferInstance hfd
  obtain ⟨κ, hκ⟩ := _root_.GlobalTheory.SchurConst.schurMult_all hP D _ hθ V S M J χ μ 𝓕 inferInstance hfd hθ inferInstance hfd _ hT _ hT
  have hS : ∀ v v' : M.Vec, ∫ g in 𝓕, star (t (PiTensorProduct.tprod ℂ v) g) * t (PiTensorProduct.tprod ℂ v') g ∂μ =
      κ * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ := fun v v' => by
    have := (hκ v v').2
    simp only [hTv] at this
    exact this
  have hcoef : ∀ (b : ∀ τ, M.H τ) (h : GinfC V), coefR (Formalism.IndefR.Eqv.thetaC D) M b (fun τ => w τ) h =
      ∏ τ, ⟪b τ, (Formalism.L2.SG.EvalTEquiv.transl M h w τ : M.H τ)⟫_ℂ := fun b h => by
    simp only [coefR, Formalism.L2.SG.EvalTEquiv.transl_apply]
  refine _root_.GlobalTheory.rightConv_eq_smul_of_inner_translates (GQ V) μ 𝓕 hfd hfin m α hα _ hφc B hB
    (GlobalTheory.BaseChain.multT_apply_left _ M J χ t ht _) c fun h' => ?_
  have hψc : Continuous fun x => star (t (PiTensorProduct.tprod ℂ w) (x * (h' : GA D V))) :=
    (hφc.comp (continuous_id.mul continuous_const)).star
  rw [(GlobalTheory.T.integral_fundamentalDomain_convolution_comm_of_bounded μ 𝓕 hfin m α hα _ _ hψc hφc B B (fun g => by rw [norm_star]; exact hB _) hB).2.2]
  have e1 : ∀ h : GinfC V, ∫ x in 𝓕, star (t (PiTensorProduct.tprod ℂ w) (x * (h' : GA D V))) *
      t (PiTensorProduct.tprod ℂ w) (x * (h : GA D V)) ∂μ =
      κ * ∏ τ, ⟪(Formalism.L2.SG.EvalTEquiv.transl M h' w τ : M.H τ), (Formalism.L2.SG.EvalTEquiv.transl M h w τ : M.H τ)⟫_ℂ := by
    intro h
    simp only [htr]
    exact hS _ _
  simp_rw [e1]
  have e2 : ∫ x in 𝓕, star (t (PiTensorProduct.tprod ℂ w) (x * (h' : GA D V))) * t (PiTensorProduct.tprod ℂ w) x ∂μ =
      κ * ∏ τ, ⟪(Formalism.L2.SG.EvalTEquiv.transl M h' w τ : M.H τ), (w τ : M.H τ)⟫_ℂ := by
    simp only [htr]
    exact hS _ _
  rw [e2]
  have e3 := hc (fun τ => (Formalism.L2.SG.EvalTEquiv.transl M h' w τ : M.H τ))
  simp only [hcoef] at e3
  simp_rw [mul_left_comm _ κ]
  rw [integral_const_mul, e3]

end GlobalTheory.ValAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtEnlargePlaceIdempotentLatticeIndicator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ThetaEnlarge

theorem isThetaAt_enlarge : ∀ {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)},
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ {f₀ : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set _) (ΛT : Set _) f₀ →
    ∀ {e e' : AE D} {P P' : Finset (Pl D.host.E)}, IsIdemSum e P → IsIdemSum e' P' → P' ⊆ P →
    ∀ {Φ g : WO S T → ℂ}, IsSBHalf e' (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) Φ →
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e' (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀ Φ g →
    IsSBHalf e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)
        (GlobalTheory.HalfProd.prodHalf e' (e - e') (halfInd (e - e') (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)) Φ) ∧
      IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀
        (GlobalTheory.HalfProd.prodHalf e' (e - e') (halfInd (e - e') (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)) Φ) g := by
  intro D S T ψ θ sS sT ΛS ΛT hS hT f₀ hvac e e' P P' he he' hsub Φ g hΦ hg
  obtain ⟨b, rfl, hb, hab⟩ := GlobalTheory.RowLocVec.exists_compl_idem hsub he he'
  have ha := GlobalTheory.PlaceDatum.idemSum_mul_self he'
  rw [add_sub_cancel_left]
  exact GlobalTheory.RowLocVec.isThetaAt_extend hvac.1 hS hT he ha hb hab hvac.2.lat hΦ hg

end GlobalTheory.ThetaEnlarge

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatRowAnnOpen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.AnnOpen

theorem latRow_ann_open : All fun {D} _ _ {sc} {G} W _ => ∀ i, i < D.R.m → ∃ U : Set (WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))),
    IsOpen U ∧ (0 : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))) ∈ U ∧
    ∀ u' ∈ U, MxAt (fun _ => True) u' → ∀ u ∈ latRow G i, W.ψ (symplO _ _ u u') = 1 := by
  intro D hq T L μ0 hL sc G W M hM i hi
  have sdG : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := by
    intro i hi
    cases i with
    | zero =>
      obtain ⟨c, hc⟩ := (hL.βY 0 (by have := D.R.two_le_m; omega) : ∃ c, _)
      exact Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
    | succ i => exact (G.sp.V_is (i + 1) 0 (by omega) hi (by omega)).sd
  have hS : IsSelfDualC (G.pS (.chi i 0)) (G.latS (.chi i 0)) := isSelfDualC_neg (sdG (i + 1) hi)
  have hT : IsSelfDualC (G.pT (.chi i 0)) (G.latT (.chi i 0)) := sdG i hi.le
  have hfin := _root_.GlobalTheory.AscFin.DepLat.finLat_depLat G (.chi i 0) hS hT
  obtain ⟨U, hU, h0, hUA⟩ := hfin.opn
  refine ⟨U, hU, h0, fun u' hu' hfu' u hu => ?_⟩
  have hu'R : u' ∈ latRow G i := hUA u' hu' hfu'
  have key := (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ hS hT (fun _ => True) u (hfin.fin u hu)).1 hu.1 u' hu'R.1
  have e : symplO (G.pS (.chi i 0)) (G.pT (.chi i 0)) u u' = -symplO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) u u' := by
    have hinv : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E), (-A)⁻¹ = -A⁻¹ := by
      intro n A
      by_cases h : IsUnit A.det
      · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
      · have h' : ¬ IsUnit (-A).det := by
          rw [Matrix.det_neg]
          intro hu
          exact h (isUnit_of_mul_isUnit_right hu)
        rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]
    simp only [symplO, hO, negSp_gram, hinv, Matrix.neg_apply, map_neg, neg_mul, mul_neg, Finset.sum_neg_distrib]
  rw [e, AddChar.map_neg_eq_inv] at key
  exact inv_eq_one.mp key

end GlobalTheory.AscFin.AnnOpen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffIntegralOnUnitHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


open GlobalTheory.RowLatChi in
theorem GlobalTheory.ColLatDict.mem_latO_iff_intM : ∀ {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)} {βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)}, IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ {e₁ : AE D} {P₁ : Finset (Pl D.host.E)}, IsIdemSum e₁ P₁ → (∀ w ∈ P₁, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ z : WO S T, IsHalf e₁ z → (z ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔ ∀ w ∈ P₁, GlobalTheory.StepData.IntM ((GlobalTheory.FunObj.Comparison₂.fr βT βS (z.map (toEAf D))).map (cpt (D := D) w))) := by
  intro D S T ΛS ΛT βS βT hS hT hβS hβT e₁ P₁ hI hAA z hz
  have key : ∀ w, GlobalTheory.StepData.IntM ((GlobalTheory.FunObj.Comparison₂.fr βT βS (z.map (toEAf D))).map (cpt (D := D) w)) ↔
      ∀ a b, Valued.v (cpt (D := D) w (Comparison₂.fr βT βS (z.map (toEAf D)) a b)) ≤ 1 := fun w => by
    rw [intM_iff]; rfl
  simp only [key]
  constructor
  · intro h w hw a b
    exact int_of_mem_latO hS hβS hβT w (hAA w hw).1 h a b
  · intro h
    exact mem_latO_of_mem_hatMx hS hI (fun w hw => (hAA w hw).2) hz (mem_hatMx_of_int hβS hβT hI hz h)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneCosetDecompositionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.CosetFJ

variable {D : D7}

theorem coset_of_places {V₀ W W₀ : HSp D} {ρ σ : ℕ} (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (ψ : AddChar (AF D.host.F) ℂ) (K : Subgroup (GA D W))
    (S : Finset (GlobalTheory.FinPl.Pl D)) :
    (∀ v ∈ S, ∀ g ∈ grpAt W (· = v), Cond dW p x y ψ (· = v) g →
      ∃ r ∈ Rgrp W x, r ∈ grpAt W (· = v) ∧ ∃ k ∈ K, k ∈ grpAt W (· = v) ∧ g = r * k) →
    ∀ g ∈ grpAt W (· ∈ S), Cond dW p x y ψ (· ∈ S) g →
      ∃ r ∈ Rgrp W x, r ∈ grpAt W (· ∈ S) ∧ ∃ k ∈ K, k ∈ grpAt W (· ∈ S) ∧ g = r * k := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ g hg _
    have e : g = 1 := GlobalTheory.QRed.grpAt_eq_one (fun v => by simp) hg
    exact ⟨1, one_mem _, one_mem _, 1, one_mem _, one_mem _, by rw [e, one_mul]⟩
  | insert v s hv ih =>
    intro hloc g hg hc
    obtain ⟨g₁, hg₁, g₂, hg₂o, rfl⟩ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).1 g
    have mono : ∀ {P : GlobalTheory.FinPl.Pl D → Prop} {a : GA D W}, (∀ w, P w → w ∈ insert v s) → a ∈ grpAt W P →
        a ∈ grpAt W (· ∈ insert v s) := fun hP ha => GlobalTheory.DStepSuppSecond.grpAt_mono hP ha
    have hg₁' : g₁ ∈ grpAt W (· ∈ insert v s) := mono (fun w hw => by simp [hw]) hg₁
    have hg₂ : g₂ ∈ grpAt W (· ∈ insert v s) := by
      have := mul_mem (inv_mem hg₁') hg
      rwa [inv_mul_cancel_left] at this
    have hg₂s : g₂ ∈ grpAt W (· ∈ s) :=
      GlobalTheory.QRed.grpAt_of_off (fun w hw => by rcases Finset.mem_insert.1 hw with h | h; exacts [Or.inl h.symm, Or.inr h])
        hg₂ hg₂o
    have hcomm : g₁ * g₂ = g₂ * g₁ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).2.1 g₁ hg₁ g₂ hg₂o
    have hdisj : ∀ w, w = v → ¬ w ∈ s := fun w hw hws => hv (hw ▸ hws)
    have hg₁o : g₁ ∈ grpOff W (· ∈ s) := GlobalTheory.QRed.grpAt_off hdisj hg₁
    have hc₁ := _root_.GlobalTheory.AscFin.Cond.of_mul_grpOff dW p x y ψ _ _ g₁ g₂ (fun w hw => by simp [hw]) hg₁ hg₂o hcomm hc
    have hc₂ := _root_.GlobalTheory.AscFin.Cond.of_mul_grpOff dW p x y ψ _ _ g₂ g₁ (fun w hw => Finset.mem_insert_of_mem hw) hg₂s hg₁o hcomm.symm
      (hcomm ▸ hc)
    obtain ⟨r₁, hr₁, hr₁a, k₁, hk₁, hk₁a, e₁⟩ := hloc v (Finset.mem_insert_self v s) g₁ hg₁ hc₁
    obtain ⟨r₂, hr₂, hr₂a, k₂, hk₂, hk₂a, e₂⟩ :=
      ih (fun w hw => hloc w (Finset.mem_insert_of_mem hw)) g₂ hg₂s hc₂
    have hk₁r₂ : k₁ * r₂ = r₂ * k₁ := GlobalTheory.SeeSawLastValue.grpAt_comm hdisj hk₁a hr₂a
    refine ⟨r₁ * r₂, mul_mem hr₁ hr₂, mul_mem (mono (fun w hw => by simp [hw]) hr₁a)
      (mono (fun w hw => Finset.mem_insert_of_mem hw) hr₂a), k₁ * k₂, mul_mem hk₁ hk₂,
      mul_mem (mono (fun w hw => by simp [hw]) hk₁a) (mono (fun w hw => Finset.mem_insert_of_mem hw) hk₂a), ?_⟩
    rw [e₁, e₂]
    calc r₁ * k₁ * (r₂ * k₂) = r₁ * (k₁ * r₂) * k₂ := by simp only [mul_assoc]
      _ = r₁ * r₂ * (k₁ * k₂) := by rw [hk₁r₂]; simp only [mul_assoc]

theorem one_coset_decomposition_base : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ g ∈ grpAt _ (fun v => v ∈ G.pl.S0), Cond (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (fun v => v ∈ G.pl.S0) g → ∃ r ∈ Rgrp _ (xFB F σ h'), r ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ ∃ k ∈ lev G (.grid (2 * σ + 2) 0), k ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ g = r * k := by
  intro D hD T L μ0 hL sc G W M hM F _hF σ h h' g hg hc
  refine coset_of_places (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (lev G (.grid (2 * σ + 2) 0)) G.pl.S0 ?_ g hg hc
  intro v hv g hg hc
  obtain ⟨u, a, ha, hoff⟩ := hc.pt
  obtain ⟨k, hk, hka, hk'⟩ := _root_.GlobalTheory.CosetFJ.besselOrbit_at_badPlace_eq_congruenceTranslate D hD T L μ0 hL sc G W M hM F _hF σ h h' v hv g hg u a ha hoff
  obtain ⟨r, hr, hra, e⟩ := GlobalTheory.T.exists_unitriangularStabilizer_of_principal_move _ (xFB F σ h') (· = v) g k u hg hka hk'
  exact ⟨r, hr, hra, k⁻¹, inv_mem hk, inv_mem hka, e⟩

end GlobalTheory.CosetFJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowChainLastStepVectorEqThetaOfDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipTopChain


open Classical in
theorem transport {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (k : ℕ)
    (P : Finset (Pl D.host.E)) (ψ : AddChar (AF D.host.F) ℂ) (e : AE D)
    {S S' : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)}
    {X Y : LSp D} (hX : X = ⟨S, ΛS⟩) (hY : Y = ⟨S', ΛS'⟩)
    {βS : GL (Fin X.sp.rank) (EAf D)} {βT : GL (Fin Y.sp.rank) (EAf D)} {βS₀ : GL (Fin S.rank) (EAf D)}
    {βT₀ : GL (Fin S'.rank) (EAf D)} (h1 : HEq βS βS₀) (h2 : HEq βT βT₀)
    {f₀ g : WO X.sp Y.sp → ℂ} {f₀' g' : WO S S' → ℂ} (h3 : HEq f₀ f₀') (h4 : HEq g g')
    (ha : X.sp.rank = D.R.r + k * D.R.t) (hb : Y.sp.rank = D.R.r + (k + 1) * D.R.t)
    (ha' : S.rank = D.R.r + k * D.R.t) (hb' : S'.rank = D.R.r + (k + 1) * D.R.t)
    (Ω : Matrix (Fin S'.rank) (Fin S.rank) (EAf D) → ℂ)
    (hN : ∀ N, IsIntM N → Ω N = ∏ w ∈ P, stepFn L t w k
      ((N.map (cpt (D := D) w)).submatrix (Comparison₂.ixOf G t w hb') (Comparison₂.ixOf G t w ha')))
    (hθ : IsThetaAt ψ (symplO S S') (heisO ψ S S') e (latO S S' (ΛS : Set _) (ΛS' : Set _) fun _ => True) 1 f₀'
      (fun x => if IsHalf e x ∧ IsIntM (frMapO S S' βS₀ βT₀ x) then Ω (frMapO S S' βS₀ βT₀ x) else 0) g') :
    IsThetaAt ψ (symplO X.sp Y.sp) (heisO ψ X.sp Y.sp) e (latO X.sp Y.sp (X.lat : Set _) (Y.lat : Set _) fun _ => True) 1 f₀
      (fun x => if IsHalf e x ∧ IsIntM (Comparison₂.fr βT βS (x.map (toEAf D))) then
        ∏ w ∈ P, stepFn L t w k (((Comparison₂.fr βT βS (x.map (toEAf D))).map (cpt (D := D) w)).submatrix
          (Comparison₂.ixOf G t w hb) (Comparison₂.ixOf G t w ha)) else 0) g := by
  subst hX hY
  obtain rfl := eq_of_heq h1
  obtain rfl := eq_of_heq h2
  obtain rfl := eq_of_heq h3
  obtain rfl := eq_of_heq h4
  convert hθ using 2
  rename_i x
  by_cases h : IsHalf e x ∧ IsIntM (Comparison₂.fr βT βS (x.map (toEAf D)))
  · have h' : IsHalf e x ∧ IsIntM (frMapO S S' βS βT x) := h
    rw [if_pos h, if_pos h']
    exact (hN _ h.2).symm
  · have h' : ¬ (IsHalf e x ∧ IsIntM (frMapO S S' βS βT x)) := h
    rw [if_neg h, if_neg h']

end GlobalTheory.FlipTopChain

namespace GlobalTheory.FlipTopChain

theorem colY_eq_m {D : D7} {T : Type} (L : LevCh D T) : ∀ n, n = D.R.m → columnBlock L n = ⟨D.sp.X', L.ΛX⟩ := by
  rintro _ rfl; exact colY_m L

theorem colFrame_eq_m {D : D7} {T : Type} (L : LevCh D T) : ∀ n, n = D.R.m → HEq (colFrame L n) L.βX := by
  rintro _ rfl; exact colFrame_m L


set_option maxHeartbeats 1600000 in
theorem last_step_theta : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {large₂ : SizeData₂ D},
    HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is → ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)) (hj : (j : ℕ) + 1 = D.R.m),
    HEq g (R.vX t) → ∃ e' : AE D, IsIdemSum e' (GlobalTheory.FlipTop.topPl R.toLevCh t) ∧
      IsThetaAt ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e' (latO (ch.G.pS (.mu t 0 j)) (ch.G.pT (.mu t 0 j)) (ch.G.latS (.mu t 0 j) : Set _) (ch.G.latT (.mu t 0 j) : Set _) fun _ => True) 1 (ch.rm.vT 0 j)
        (GlobalTheory.FlipTop.topFn ch.S.B t e' j (GlobalTheory.FlipTop.rank_col ch.G (by omega)) (GlobalTheory.FlipTop.rank_col ch.G (by omega))) g := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R F large₂ hS ch hch t j g hj hg
  obtain ⟨k, hk⟩ := j
  simp only at hj
  obtain rfl : k = D.R.m - 1 := by omega
  obtain ⟨-, e', he', hθ⟩ := hS.core.chain.vX t
  refine ⟨e', he', ?_⟩
  have hm : D.R.m - 1 < D.R.m := hk
  have hb' : D.sp.X'.rank = D.R.r + (D.R.m - 1 + 1) * D.R.t := by
    rw [hj]; exact D.sp.X'_rank
  have hN := (Comparison₂.local_factors ch.S.B t hS.core.lev).2.2 (D.R.m - 1) hm _ hb'
  have hchi : R.toLevCh.chi (D.R.m - 1 + 1) = R.toLevCh.chi D.R.m := by rw [hj]
  rw [hchi] at hN
  unfold GlobalTheory.FlipTop.topFn
  exact transport ch.G t (D.R.m - 1) _ ch.W.ψ e' (X := ch.G.node (.grid 0 (D.R.m - 1)))
    (Y := ch.G.node (.grid 0 (D.R.m - 1 + 1))) (colY_lt R.toLevCh hm) (colY_eq_m R.toLevCh _ hj)
    (colFrame_lt R.toLevCh hm) (colFrame_eq_m R.toLevCh _ hj) (hch.vac.2 _ hj) hg _ _ (Comparison₂.rank_Yc hm.le) hb' _ hN
    (hch.weil.ψ ▸ hθ)

end GlobalTheory.FlipTopChain

end
end

