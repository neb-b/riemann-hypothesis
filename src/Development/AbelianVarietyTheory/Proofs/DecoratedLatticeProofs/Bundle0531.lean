module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0324
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocXiEqMulMidXi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0486
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0134
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiStdEqConstMulLocXi
public import Formalism.LocalToGlobal.Columns.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0468

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PenultimateDatumUnchangedFramesCongruentOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.penultimateDatum_unchanged_frames_congruent_one : ∀ {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (s : ℕ) (P : Formalism.L2.Col.rowSG Pr sel mu), P.1 ∈ Pr.vGs → R.m = s + 2 → (∀ a : X.E, Formalism.L2.Col.IntAt P.1 a → Formalism.L2.Col.redP P.1 a = 0 → Formalism.L2.Col.IntAt P.1 (a / (Formalism.L2.Col.qOf P.1 : X.E))) → ∀ (f : Formalism.L2.Col.Sp X.E (R.N s) ≃ₗ[X.E] Formalism.L2.Col.Sp X.E (R.N s)) (f' : Formalism.L2.Col.Sp X.E (R.N (s + 1)) ≃ₗ[X.E] Formalism.L2.Col.Sp X.E (R.N (s + 1))), f ∈ Formalism.L2.Col.GLint X.E (R.N s) P.1 → (∀ x ∈ Formalism.L2.Col.stdAt X.E (R.N s) P.1, Formalism.L2.Col.redV P.1 (f x) = Formalism.L2.Col.redV P.1 x) → f' ∈ Formalism.L2.Col.GLint X.E (R.N (s + 1)) P.1 → (∀ x ∈ Formalism.L2.Col.stdAt X.E (R.N (s + 1)) P.1, Formalism.L2.Col.redV P.1 (f' x) = Formalism.L2.Col.redV P.1 x) → ∀ (x : Formalism.L2.Col.HomE X.E (R.N s) (R.N (s + 1))) (y : Formalism.L2.Col.Sp X.E (R.N (s + 1))), Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 (Formalism.L2.Col.inFr f f' x) (f'.symm y) = Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 x y := by
  intro X Pr R Ch sel S₀ mu cst s P hP hm hd f f' hf hr hf' hr' x y
  exact GlobalTheory.PenPsiInv.psiAt_one_inFr Ch sel mu cst s P hP hm hd f f' hf hr hf' hr' x y
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinSumModerateGrowthConvergent
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.EisConvGrowth

theorem eis_modGrowth : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ (μ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ → (V.rank : ℝ) / 2 < s₁.re → GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V φ) := by
  intro D V a ha hI μ s₁ φ hφ h
  haveI := t2Space_adeleRing' (F := D.host.F)
  obtain ⟨C₁, hC₁⟩ : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C * (hgt V a g : ℝ) ^ (s₁.re + (V.rank : ℝ) / 2) :=
    hI.exists_norm_le continuous_absE (isCompact_Khat V a) hφ
  obtain ⟨C₂, hC₂, h₂⟩ := GlobalTheory.SWAbsGrowth.hgt_mul_le V a ha
  set τ : ℝ := s₁.re + (V.rank : ℝ) / 2 with hτ
  have hτ0 : 0 ≤ τ := by
    have : (0 : ℝ) ≤ (V.rank : ℝ) / 2 := by positivity
    linarith
  have hs := GlobalTheory.Eis.sphConv D V a hI s₁.re h
  set S := ∑' q : GlobalTheory.Eis.SiegelCosets V, (hgt V a (q.out : GQ (dblSp V)) : ℝ) ^ τ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  set M : ℕ := ⌈τ⌉₊ with hM
  refine ⟨max C₁ 0 * (max C₂ 1) ^ M * S, 2 * V.rank * M, fun y => ?_⟩
  set H := GlobalTheory.Grow.height (dblSp V) y with hH
  have hH1 : 1 ≤ H := GlobalTheory.Grow.one_le_height _ y
  set K := max C₂ 1 * H ^ (2 * V.rank) with hK
  have hone : 1 ≤ K := one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ hH1)
  set c := max C₁ 0 * K ^ M with hc
  have hq : ∀ x : GA D (dblSp V), ‖φ (x * y)‖ ≤ c * (hgt V a x : ℝ) ^ τ := by
    intro x
    refine (hC₁ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (by positivity)).trans ?_
    rw [hc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
    have h3 : (hgt V a (x * y) : ℝ) ≤ hgt V a x * K :=
      (h₂ x y).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (NNReal.coe_nonneg _))
    refine (Real.rpow_le_rpow (NNReal.coe_nonneg _) h3 hτ0).trans ?_
    rw [Real.mul_rpow (NNReal.coe_nonneg _) (by positivity), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [← Real.rpow_natCast _ M]
    exact Real.rpow_le_rpow_of_exponent_le hone (Nat.le_ceil τ)
  have hsum : HasSum (fun q : GlobalTheory.Eis.SiegelCosets V => c * (hgt V a (q.out : GQ (dblSp V)) : ℝ) ^ τ) (c * S) :=
    hs.hasSum.mul_left c
  have hb : ‖GlobalTheory.Eis.eis V φ y‖ ≤ c * S := tsum_of_norm_bounded hsum fun q => hq _
  refine hb.trans (le_of_eq ?_)
  rw [hc, hK, mul_pow, ← pow_mul]
  ring

end GlobalTheory.EisConvGrowth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsNeZeroOfLValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem sphFun_of_isParamFun : ∀ (D : D7) (V : HSp D) (Λ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Lat V) (Sf : Finset (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D)) (f : GA D V → ℂ)
    (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.LFun.IsParamFun D.sp.cm.sig V.gram Λ (Sf : Set (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D)) f B →
    GlobalTheory.Core.Rk.IP.SphFun V Λ Sf f := by
  intro D V Λ Sf f B hf v hv k hk g
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hx := (hf v (by simpa using hv) w hw).mem_fixed
  have := congrFun (hx ⟨k, hk⟩) g
  simpa [GlobalTheory.PRep.rightReg, LinearMap.funLeft] using this

theorem upNe_of_heckeForm : ∀ D : D7, GlobalTheory.Core.Rk.IP.HeckeForm D → MetEx D → LevFacts D → ZetaNe D → UpNe D := by
  intro D hHF _ _ hZ hgap c hc k hk s s' hs hs' p hp u B hB hL
  obtain ⟨mX, hmX⟩ : ∃ mX : Measure (WO s.V s'.V) × Set (WO s.V s'.V), IsCovolOne (ratL s'.V s.V) mX.1 mX.2 := by
    obtain ⟨ξ, f₀, hv⟩ := hp.vec
    exact hv.1.2.norm.1
  obtain ⟨φ, v, hvK, hZ'⟩ := hZ hgap c hc k hk s s' hs hs' p hp mX.1 mX.2 hmX
  refine ⟨φ, v, hvK, ?_⟩
  obtain ⟨hu0, hpar⟩ := hB
  obtain ⟨hI, hInt⟩ := hZ' u hu0
  have hF : PiLocalization₂.val u v ≠ 0 := by
    intro h0
    apply hI
    have : ∀ g, p.zint mX.1 mX.2 φ (PiLocalization₂.val u v) g = 0 := by
      intro g; simp [Step.zint, h0, PiLocalization₂.pet, Lift.pet, rTr]
    simp [this]
  have hparF := hpar v hF
  obtain ⟨cA, a, hcA, hcart, hJ, hmaj, hmaj_eq, hA0⟩ := _root_.GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame D c hc k hk.le s hs
  obtain ⟨-, -, -, hcartB, -, -, -, -⟩ := _root_.GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame D c hc (k + 1) hk s' hs'
  have hu1 : (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := hA0 u v hvK
  obtain ⟨hwitt, htwo⟩ := GlobalTheory.T.thetaChainStage_wittIndex_lt_and_places_two_split D c (k + 1) s' hk hs'
  obtain ⟨hfock, -, hunrT⟩ := _root_.GlobalTheory.ChainOnto.fock_sph D hgap c hc k hk s s' hs hs' p hp
  obtain ⟨-, -, hoff⟩ := _root_.GlobalTheory.Core.Rk.IP.hgtL_props D s.V s.Λ a hs.selfDual hmaj
  have hmeas : MeasurableSet (intOff c s) := (hoff c.S).1.measurableSet
  have hr1 : 1 ≤ s.V.rank := by
    rw [hs.rank]; simp only [Ranks.rankY, Ranks.r]; have := D.R.two_le_m; omega
  have ht1 : 1 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hrk : s'.V.rank = s.V.rank + D.R.t := by rw [hs'.rank, hs.rank]; simp only [Ranks.rankY]; ring
  have hPair : GlobalTheory.Core.Rk.IP.Pair c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
      mX.1 mX.2 :=
    { setting := ⟨hr1, ht1, hrk, hc.inf, hs.sigOK, hcA, hcart, hcartB, hJ⟩
      maj := hmaj
      maj_eq := hmaj_eq
      weil := hp.weil
      covol := hmX }
  have hUnr : GlobalTheory.Core.Rk.IP.Unram c.ψ s.V s'.V (c.chT (k + 1)) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) :=
    ⟨hs.selfDual, hs'.selfDual, fun w _ h2 => htwo w h2, hunrT, (hfock φ).2, (hfock φ).2⟩
  have hsph := sphFun_of_isParamFun D s.V s.Λ c.S _ B hparF
  set F := PiLocalization₂.val u v with hFdef
  have hAut : Formalism.L2.Theta.IsAutFunSm c.θ s.V (fun g => conj (F g)) := hu1.1.1
  have hFl : ∀ γ ∈ GQ s.V, ∀ g, F (γ * g) = F g := fun γ hγ g => by
    simpa using congrArg (starRingEnd ℂ) (hAut.left γ hγ g)
  have hFc : Continuous F := by
    have h := hAut.cont.star
    change Continuous (fun g => star (star (F g))) at h
    simpa only [star_star] using h
  have hΦ : IsThetaFunO c.ψ s.V s'.V (p.pt φ) := (hfock φ).1.1
  have hθl : ∀ h, ∀ γ ∈ GQ s.V, ∀ g, thetaKO p.ω (γ * g) h (p.pt φ) = thetaKO p.ω g h (p.pt φ) := by
    intro h γ hγ g
    have e : ((γ * g, h) : GA D s.V × GA D s'.V) = (γ, 1) * (g, h) := by simp
    simp only [thetaKO, e, map_mul, Module.End.mul_apply]
    exact hp.weil.om_aut γ hγ 1 (one_mem _) _ (hp.weil.om_pres _ _ hΦ)
  have hθc : ∀ h, Continuous fun g => thetaKO p.ω g h (p.pt φ) := fun h =>
    (hp.weil.om_cont _ hΦ 0).comp (continuous_id.prodMk continuous_const)
  have hrc : ∀ g, GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F x)) (fun x => conj (F x)) g = conj (s.pet (rTr s.V g F) F) := by
    intro g
    have := _root_.GlobalTheory.ChainOnto.integral_autMeasure_eq_setIntegral D s.V s.ν s.fd hs.haar hs.fund (fun x => conj (F (x * g)) * conj (conj (F x)))
      (fun γ hγ x => by simp only [mul_assoc, hFl γ hγ]) (by fun_prop)
    simp only [GlobalTheory.Core.Rk.IP.rcoef, PiLocalization₂.pet, Lift.pet, rTr]
    rw [← integral_conj]
    simp only [map_mul]
    exact this
  have hup : ∀ h, GlobalTheory.Core.Rk.IP.up p.ω s.ν (p.pt φ) (fun x => conj (F x)) h = conj (p.up φ F h) := by
    intro h
    have := _root_.GlobalTheory.ChainOnto.integral_autMeasure_eq_setIntegral D s.V s.ν s.fd hs.haar hs.fund (fun g => thetaKO p.ω g h (p.pt φ) * conj (F g))
      (fun γ hγ x => by simp only [hθl h γ hγ, hFl γ hγ]) (by have := hθc h; fun_prop)
    simp only [GlobalTheory.Core.Rk.IP.up, Step.up]
    rw [← integral_conj]
    simp only [map_mul, Complex.conj_conj]
    exact this
  have hsZ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V = (D.R.t : ℂ) / 2 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, hrk]; push_cast; ring
  have hwz : ∀ g, GlobalTheory.Core.Rk.IP.wcoef p.ω mX.1 mX.2 (p.pt φ) (p.pt φ) g *
      GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F x)) (fun x => conj (F x)) g = p.zint mX.1 mX.2 φ F g := by
    intro g; simp only [Step.zint, hrc]; rfl
  have hint : ∃ s₁ : ℝ, s₁ < (D.R.t : ℝ) / 2 ∧ IntegrableOn (GlobalTheory.Core.Rk.IP.integrand p.ω s.ν mX.1 mX.2 s.Λ a (p.pt φ)
      (p.pt φ) (fun x => conj (F x)) (fun x => conj (F x)) s₁) (GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S) s.ν := by
    obtain ⟨s₁, hs₁, hi⟩ := hInt a hmaj hmaj_eq
    refine ⟨s₁, hs₁, hi.congr_fun (fun g hg => ?_) hmeas⟩
    simp only [GlobalTheory.Core.Rk.IP.integrand, GlobalTheory.Doubling.npow, (hoff c.S).2 g hg, hsZ, hrc]
    simp only [Step.zint, coefW, GlobalTheory.Core.Rk.IP.wcoef, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, hgtS]
    ring
  obtain ⟨-, -, -, hval⟩ := hHF c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
    mX.1 mX.2 hPair (Or.inr hwitt) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) (hfock φ).1 (hfock φ).1 hUnr s.ν s'.ν hs.haar hs'.haar
    _ hu1 _ hu1 B hparF hsph hint
  obtain ⟨l, hl0, hlv⟩ := hL
  have key := hval l hlv
  intro hup0
  have hz : GlobalTheory.Core.Rk.IP.up p.ω s.ν (p.pt φ) (fun x => conj (F x)) = 0 := by
    funext h; rw [hup, hup0]; simp
  rw [hz] at key
  have hlhs : GlobalTheory.Cusp.petersson s'.V s'.ν (0 : GA D s'.V → ℂ) 0 = 0 := by
    simp [GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet, GlobalTheory.AutomorphicL2Unitary.descend]
  rw [hlhs] at key
  have hvol : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν := by
    have := hs'.haar; exact GlobalTheory.RallisIP.Model.vol_pos s'.ν
  have hd : GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E (c.S : Set (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D)) s.V.rank s'.V.rank
      ((D.R.t : ℂ) / 2) ≠ 0 := by
    refine ((GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero D _ _ _).2 _ ?_).1
    simp only [Complex.div_ofNat_re, Complex.natCast_re]; positivity
  have hI' : ∫ g in GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S, GlobalTheory.Core.Rk.IP.wcoef p.ω mX.1 mX.2 (p.pt φ) (p.pt φ) g *
      GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F x)) (fun x => conj (F x)) g ∂s.ν ≠ 0 := by
    simp only [hwz]; exact hI
  have hvolC : ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ s'.V s'.ν : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hvol.ne'
  exact hI' (by
    have := key.symm
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hvolC
      · exact absurd h (div_ne_zero hl0 hd)
    · exact h)

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFiniteFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

namespace GlobalTheory.Fam.LevelFrames


open _root_.Formalism.L2.Col in
theorem redV_eq_of_near {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    {f : Sp E n ≃ₗ[E] Sp E n} (hf : ∀ i j : Fin n, P.valuation E (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) < 1)
    {y : Sp E n} (hy : y ∈ stdAt E n P) : redV P (f y) = redV P y := by
  funext i
  have hy' := GlobalTheory.TopStep.mem_stdAt.1 hy
  have e : f y i - y i = ∑ j, (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) * y j := by
    simp only [_root_.sub_mul, Finset.sum_sub_distrib, ← Fin.ext_iff, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [pi_eq_sum_univ' y, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  have h : P.valuation E (f y i - y i) < 1 := by
    rw [e]
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' ((GlobalTheory.AtTypeExists.intAt_iff _ _).1 (hy' j))) (hf i j)
  obtain ⟨h1, h2⟩ := twRed0_of_val P h
  have h3 := reduction_add h1 (hy' i)
  rw [sub_add_cancel, h2, zero_add] at h3
  exact h3


end GlobalTheory.Fam.LevelFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel

set_option maxHeartbeats 1000000

namespace GlobalTheory.Fam.TopLoc

theorem locTop_eq_of_type : ∀ {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S S' : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S) (mu' : Formalism.L2.DIV.Tup X.F X.E X.K S')
   (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (cst' : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu')) (P : Formalism.L2.Col.rowSG Pr sel mu) (P' : Formalism.L2.Col.rowSG Pr sel mu'),
   P.1 = P'.1 → P.1 ∈ Pr.vGs → cst.sharp = cst'.sharp →
   (∀ a, Formalism.L2.Col.IntAt P.1 a → cst.psi P (a / (Formalism.L2.Col.qOf P.1 : X.E)) = Formalism.L2.Col.psi0P Ch P.1 (Formalism.L2.Col.redP P.1 a)) →
   (∀ a, Formalism.L2.Col.IntAt P'.1 a → cst'.psi P' (a / (Formalism.L2.Col.qOf P'.1 : X.E)) = Formalism.L2.Col.psi0P Ch P'.1 (Formalism.L2.Col.redP P'.1 a)) →
   ∀ m2 y y', (∀ i, Formalism.L2.Col.IntAt P.1 ((Formalism.L2.Col.qOf P.1 : X.E) * y' i)) →
     GlobalTheory.TopStep.locTop Ch sel mu cst m2 P y y' = GlobalTheory.TopStep.locTop Ch sel mu' cst' m2 P' y y' := by
  intro X Pr R Ch sel S S' mu mu' cst cst' P P' hPP hmem hsh hpsi hpsi' m2 y y' hy
  have hmem' : P'.1 ∈ Pr.vGs := hPP ▸ hmem
  unfold GlobalTheory.TopStep.locTop Formalism.L2.Col.PhiTop Formalism.L2.Col.ftY
  rw [if_pos hmem, if_pos hmem', hsh, if_pos hmem, if_pos hmem', ← hPP]
  congr 1
  split_ifs with hη
  · set η := Formalism.L2.Col.atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y with hηdef
    have hq : ((Formalism.L2.Col.qOf P.1 : ℕ) : X.E) ≠ 0 :=
      Nat.cast_ne_zero.2 fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    have hsum : η ((Formalism.L2.Col.qOf P.1 : X.E) • y') = ∑ i, ((Formalism.L2.Col.qOf P.1 : X.E) * y' i) * η (Pi.single i 1) := by
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [pi_eq_sum_univ' ((Formalism.L2.Col.qOf P.1 : X.E) • y'), map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, Pi.smul_apply, smul_eq_mul]
    have hε : Formalism.L2.Col.IntAt P.1 (Formalism.L2.Col.epsSg : X.E) := by
      simpa [Formalism.L2.Col.epsSg] using Formalism.L2.Col.IntAt.coe P.1 (-1)
    have hint : Formalism.L2.Col.IntAt P.1 ((Formalism.L2.Col.epsSg : X.E) * η ((Formalism.L2.Col.qOf P.1 : X.E) • y')) := by
      refine hε.mul ?_
      rw [hsum]
      exact GlobalTheory.TopStep.intAt_sum _ fun i _ => (hy i).mul (hη i)
    have hb : (Formalism.L2.Col.epsSg : X.E) * η y' = (Formalism.L2.Col.epsSg : X.E) * η ((Formalism.L2.Col.qOf P.1 : X.E) • y') / (Formalism.L2.Col.qOf P.1 : X.E) := by
      rw [map_smul, smul_eq_mul]; field_simp
    have e1 := hpsi _ hint
    have e2 := hpsi' _ (hPP ▸ hint)
    rw [← hPP] at e2
    rw [hb, e1, e2]
  · rfl

section Normal
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SymChain GlobalTheory.SymChain.UnifChange GlobalTheory.Fam.MidLoc

theorem exists_normal_top {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s κ : ℕ} (S : SymData k s κ) (ϖ' : kˣ) (h : valuation k ((ϖ' : k) - (S.ϖ : k)) < valuation k (S.ϖ : k)) (τ : ℕ) :
    ∃ S' : SymData k s κ, S'.ϖ = ϖ' ∧ S'.ψ = S.ψ ∧ (∀ j, j ≤ s + 2 → S'.μ j = S.μ j) ∧
      (∀ j, s + 2 < j → S'.μ j = 1) ∧ (S'.T (Fin τ)).PhiTop = (S.T (Fin τ)).PhiTop := by
  let S₁ : SymData k s κ :=
    { S with ϖ := ϖ', unif := isUnif_of_near S.unif h, sym := isSymLevel_of_near S.cond S.unif h S.sym }
  have hTop : (S₁.T (Fin τ)).PhiTop = (S.T (Fin τ)).PhiTop :=
    transport_iterPhi S.P S.μ S.tame (s + 1) (near_refl _) (near_typeFrame h _)
  let μ : ℕ → kˣ →* ℂˣ := fun j => if j ≤ s + 2 then S₁.μ j else 1
  have ht : ∀ j, IsTame (μ j) := fun j => by
    simp only [μ]
    split_ifs
    · exact S₁.tame j
    · exact fun _ _ => rfl
  have e : ∀ j, 1 ≤ j → j ≤ s + 2 → μ j = S₁.μ j := fun j _ hj => if_pos hj
  exact ⟨withMu S₁ μ ht, rfl, rfl, fun j hj => if_pos hj, fun j hj => if_neg (by omega),
    (withMu_le S₁ μ ht e (Fin τ)).2.1.trans hTop⟩

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}

end Normal

end GlobalTheory.Fam.TopLoc
end

