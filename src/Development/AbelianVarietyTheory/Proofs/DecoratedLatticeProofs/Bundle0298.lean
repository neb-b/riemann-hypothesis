module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAdeleIdempotentOfFMulSelf
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0087
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0281
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousPf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.RdLaw
variable {D : D7}

theorem PM_map {r : ℕ} {B : Type} [CommRing B] (f : AE D →+* B) (M : Matrix (Fin r) (Fin r) (AE D)) :
    (PM M).map f = f (eps D) • M.map f + f (1 - eps D) • (1 : Matrix (Fin r) (Fin r) B) := by
  ext i j
  simp only [PM, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_add (f := _), map_mul]
  split_ifs <;> simp

theorem cT_PM {r : ℕ} (M : Matrix (Fin r) (Fin r) (AE D)) :
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (PM M) =
      eps D • cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M + (1 - eps D) • (1 : Matrix (Fin r) (Fin r) (AE D)) := by
  unfold cT
  rw [PM_map, RingHom.map_sub, RingHom.map_one, sig_eps, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
    Matrix.transpose_one]

theorem PM_unit {r : ℕ} (J M : Matrix (Fin r) (Fin r) (AE D))
    (hM : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M * J * M = J) :
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (PM M) * J * PM M = J := by
  rw [cT_PM, PM]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    eps_mul_self, one_sub_mul_self, eps_mul_one_sub, mul_comm (1 - eps D) (eps D), zero_smul, add_zero, zero_add, hM]
  rw [← add_smul, add_sub_cancel, one_smul]

def PGL (D : D7) (r : ℕ) : GL (Fin r) (AE D) →* GL (Fin r) (AE D) where
  toFun g := ⟨PM g.1, PM (g⁻¹).1, by rw [← PM_mul, Units.mul_inv, PM_one], by rw [← PM_mul, Units.inv_mul, PM_one]⟩
  map_one' := Units.ext PM_one
  map_mul' a b := Units.ext (PM_mul a.1 b.1)

theorem PGL_mem (V : HSp D) (g : GL (Fin V.rank) (AE D)) (hg : g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram) :
    PGL D V.rank g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
  PM_unit _ g.1 hg

def pf (V : HSp D) (h : GA D V) : GA D V :=
  (⟨PGL D V.rank (matHom V h), PGL_mem V (matHom V h) (Subtype.property (h : ↥(HR (AF D.host.F) D.sp.cm.sig V.gram)))⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)

theorem mt_pf (V : HSp D) (h : GA D V) : Formalism.L2.Theta.mt V (pf V h) = PM (Formalism.L2.Theta.mt V h) := rfl

theorem pf_one (V : HSp D) : pf V 1 = 1 := by
  apply Subtype.ext
  show PGL D V.rank (matHom V 1) = 1
  rw [map_one, map_one]

theorem pf_fin (V : HSp D) (h : GA D V) : pf V h ∈ GfC V := by
  show infHom V (pf V h) = 1
  apply Units.ext
  show (Formalism.L2.Theta.mt V (pf V h)).map (infPart D) = 1
  rw [mt_pf, PM_map, infPart_eps, RingHom.map_sub, RingHom.map_one, infPart_eps, sub_zero, zero_smul, zero_add, one_smul]

theorem finM_pf (V : HSp D) (h : GA D V) : finM V rfl (pf V h) = finM V rfl h := by
  rw [finM_rfl, finM_rfl, mt_pf, PM_map, toEAf_eps, RingHom.map_sub, RingHom.map_one, toEAf_eps, sub_self, zero_smul, add_zero, one_smul]

theorem continuous_pf (V : HSp D) : Continuous (pf V) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hm : Continuous fun h : GA D V => Formalism.L2.Theta.mt V h :=
    Units.continuous_val.comp continuous_subtype_val
  have hP : Continuous fun M : Matrix (Fin V.rank) (Fin V.rank) (AE D) => PM M :=
    (continuous_const_smul _).add continuous_const
  refine Continuous.subtype_mk (f := fun h => PGL D V.rank (matHom V h)) (Units.continuous_iff.2 ⟨hP.comp hm, ?_⟩) _
  have e : (fun h : GA D V => ((PGL D V.rank (matHom V h))⁻¹ : GL (Fin V.rank) (AE D)).val) =
      fun h => PM (Formalism.L2.Theta.mt V h⁻¹) := by
    funext h
    rw [← map_inv, ← map_inv]; rfl
  rw [e]
  exact hP.comp (hm.comp continuous_inv)

end GlobalTheory.AdForm.RdLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalRowBoundFromWindowWidthThree
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Rk

theorem exp_add_exp_le_exp_max_succ {C₁ C₂ y : ℝ} (hy : 1 ≤ y) :
    Real.exp (C₁ * y) + Real.exp (C₂ * y) ≤ Real.exp ((max C₁ C₂ + 1) * y) := by
  have hy0 : 0 ≤ y := by linarith
  have a1 : Real.exp (C₁ * y) ≤ Real.exp (max C₁ C₂ * y) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hy0)
  have a2 : Real.exp (C₂ * y) ≤ Real.exp (max C₁ C₂ * y) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) hy0)
  have a3 : (2 : ℝ) ≤ Real.exp y := by
    have := Real.add_one_le_exp y
    linarith
  have e : Real.exp ((max C₁ C₂ + 1) * y) = Real.exp (max C₁ C₂ * y) * Real.exp y := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hp := Real.exp_pos (max C₁ C₂ * y)
  nlinarith

theorem diagonalRow_bound_from_windowWidthThree : Formalism.L2.SG.Pf.WuDecayOfGap → On {3} VanishingGramTermsBound → On {3} CollS → OneOn {3} true →
    OneOn {3} false →
    GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) := by
  intro hW hG hCo h1 h2 Cg cb Cu cT CT hcb hcT
  obtain ⟨C₁, hC₁, t₁, H₁⟩ := h1 Cg cb Cu cT CT hcb hcT
  obtain ⟨C₂, _, t₂, H₂⟩ := h2 Cg cb Cu cT CT hcb hcT
  obtain ⟨tG, HG⟩ := hG Cg cb Cu cT CT hcb hcT
  obtain ⟨tC, HC⟩ := hCo Cg cb Cu cT CT hcb hcT
  refine ⟨max C₁ C₂ + 1, max (max (max t₁ t₂) (max tG tC)) 29, max (max (max t₁ t₂) (max tG tC)) 29,
    by linarith [le_max_left C₁ C₂], ?_⟩
  intro C' Cl hC' hCl D L u hT hE hD
  obtain ⟨⟨large₂, hL, h8, h1G⟩, hR⟩ := hE
  obtain ⟨hTies, hAdm, hHL, hNW, hTF⟩ := hD
  subst hL
  have hS0 : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT := ⟨h8, hHL.2⟩
  have hD0 : StandingNumericalData D 3 := _root_.GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu D hNW hR
  have hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT 3 := ⟨hS0, hD0, by norm_num⟩
  obtain ⟨S, hF, hLT⟩ := hT.trueD.sTies
  have m1 : ∀ {a b c d e : ℝ}, max (max (max a b) (max c d)) 29 ≤ e →
      a ≤ e ∧ b ≤ e ∧ c ≤ e ∧ d ≤ e ∧ 29 ≤ e := by
    intro a b c d e h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> refine le_trans ?_ h <;> simp
  obtain ⟨a1, a2, a3, a4, a5⟩ := m1 hC'
  obtain ⟨b1, b2, b3, b4, b5⟩ := m1 hCl
  obtain ⟨c⟩ := _root_.GlobalTheory.Core.Diag.concK_of_finX hW D large₂ C' Cl Cg cb Cu cT CT S a5 b5 hF hLT hTF hS0
  have hAC : (c.Y.tO u u).AbsConv := kExp_absConv_tied.2 D c.X c.Y u u c.tie
  have g0 := HG 3 rfl C' Cl a3 b3 D large₂ c.X c.Y c.hF c.hI u h1G hTies hAdm hH0 c.tie hAC
  have gc := HC 3 rfl C' Cl a4 b4 D large₂ c.X c.Y c.hF c.hI u h1G hTies hAdm hH0 c.tie hAC
  have o1 := H₁ 3 rfl C' Cl a1 b1 D large₂ c.X c.Y u hTies hH0 c.tie hAC
  have o2 := H₂ 3 rfl C' Cl a2 b2 D large₂ c.X c.Y u hTies hH0 c.tie hAC
  simp only [if_true, Bool.false_eq_true, if_false] at o1 o2
  have hf : (1 : ℝ) ≤ D.R.f := by
    have h4 : D.R.m ^ 4 ≤ D.R.f := hHL.2.2.1
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by have := D.R.two_le_m; omega)
    exact_mod_cast le_trans this h4
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hL1 : 1 < large₂.sc.L := hHL.1
  have hy : 1 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
    have : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := one_le_pow₀ hm
    have h2' : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 * D.R.f := one_le_mul_of_one_le_of_one_le this hf
    exact one_le_mul_of_one_le_of_one_le h2' hL1.le
  have hg : ∀ C, gamL D large₂.sc.L C = Real.exp (C * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)) := by
    intro C; unfold gamL; congr 1; ring
  have hsum : gamL D large₂.sc.L C₁ + gamL D large₂.sc.L C₂ ≤ gamL D large₂.sc.L (max C₁ C₂ + 1) := by
    rw [hg, hg, hg]; exact exp_add_exp_le_exp_max_succ hy
  have key := _root_.GlobalTheory.Core.Diag.sDiagAt_of_points D c large₂ C' Cl Cg cb Cu cT CT 3 (gamL D large₂.sc.L C₁) (gamL D large₂.sc.L C₂)
    (gamL D large₂.sc.L (max C₁ C₂ + 1)) u a5 b5 hH0 (Real.exp_pos _).le (Real.exp_pos _).le hsum g0 gc o1 o2
  unfold SDiagAt at key
  show TwoTerm D u _ _
  unfold TwoTerm
  rw [d0_eq]
  have e1 : gamL D large₂.sc.L (max C₁ C₂ + 1) = Real.exp ((max C₁ C₂ + 1) * mfL D large₂.sc.L) := by
    rw [hg]; rfl
  have e2 : Real.exp (-((1 / 2 : ℝ) * D.R.k * D.R.f * Real.log D.R.k)) = Real.exp (-(kfk D / 2)) := by
    unfold kfk; congr 1; ring
  have e3 : Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k)) = Real.exp (-kfk D) := by
    unfold kfk; rfl
  rw [e1, e2, e3] at key
  refine le_trans key (le_of_eq ?_)
  ring

end GlobalTheory.Core.Rk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingBasicIdentityUnfolding
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

namespace GlobalTheory.Core.Rk.BasicId

open Filter Set GlobalTheory.Eis

theorem measurable_tsum_of_summable' {X I : Type} [MeasurableSpace X] [Countable I]
    (F : I → X → ℂ) (hF : ∀ i, Measurable (F i)) (hs : ∀ x, Summable fun i => F i x) :
    Measurable fun x => ∑' i, F i x :=
  measurable_of_tendsto_metrizable' (atTop : Filter (Finset I))
    (f := fun s x => ∑ i ∈ s, F i x) (fun s => Finset.measurable_sum s fun i _ => hF i)
    (tendsto_pi_nhds.2 fun x => (hs x).hasSum)

theorem out_mul_inv_mem {D : D7} (V : HSp D) (x : GQ (dblSp V)) :
    (((mk ((siegel V).subgroupOf (GQ (dblSp V))) x).out : GQ (dblSp V)) : GA D (dblSp V)) *
      ((x : GA D (dblSp V)))⁻¹ ∈ siegel V := by
  obtain ⟨γ, e⟩ := mk_eq_iff.1 (Quotient.out_eq (mk ((siegel V).subgroupOf (GQ (dblSp V))) x))
  have e' := congrArg (fun z : GQ (dblSp V) => (z : GA D (dblSp V))) e
  simp only [Subgroup.coe_mul] at e'
  rw [← e', mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  exact inv_mem (Subgroup.mem_subgroupOf.1 γ.2)

theorem basicIdentity_unfold : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → IsCuspFun V f₁ → GlobalTheory.Eis.BasicIdentity V μ m φ f₁ f₂ := by
  intro D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂ hcusp
  haveI := hm
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have hL : LeftInv (siegelQ V) φ := leftInv_of_mem hμ hφ
  have hφc : Continuous φ := hφ.2.1

  have hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) :=
    _root_.GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual D V (frameLat V) a (GlobalTheory.Core.Rk.AbsConv.isSelfDualC_frameLat V) ha
  have hS : SphConv V a := GlobalTheory.Eis.sphConv D V a hI
  have hσ : (V.rank : ℝ) / 2 < ((s.re : ℂ)).re := by simpa using hs
  have hconvS : ∀ g, EisConv V (sph V a (s.re : ℂ)) g := fun g => (((sphConv_iff hI).1 hS).1 _ hσ).2 g
  have h2 : ∀ g, sph V a (s.re : ℂ) g = (((hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) : ℝ) : ℂ) := fun g => by
    rw [Complex.ofReal_cpow (NNReal.coe_nonneg _)]; push_cast; rfl
  have hr0 : ∀ g, 0 ≤ (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := fun g =>
    Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hn : ∀ g, ‖sph V a (s.re : ℂ) g‖ = (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := fun g => by
    rw [h2, Complex.norm_real, Real.norm_of_nonneg (hr0 g)]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C * (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := by
    haveI := t2Space_adeleRing' (F := D.host.F)
    exact hI.exists_norm_le continuous_absE (isCompact_Khat V a) hφ
  have hsum : ∀ y, Summable fun q : SiegelCosets V => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * y) :=
    fun y => Summable.of_norm (((hconvS y).of_norm_le (C := max C 0) fun g =>
      (hC g).trans (by rw [hn]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hr0 g))) : EisConv V φ y)

  set P : Set (SiegelCosets V) := {q | ∃ δ ∈ GQ V, ((q.out : GQ (dblSp V)) : GA D (dblSp V)) * (io V (δ, 1))⁻¹ ∈ siegel V}
    with hP
  let e0 : GQ V → P := fun δ => ⟨mk _ ⟨io V ((δ : GA D V), 1), io_mem_GQ V δ.2 (one_mem _)⟩,
    ⟨δ, δ.2, out_mul_inv_mem V ⟨io V ((δ : GA D V), 1), io_mem_GQ V δ.2 (one_mem _)⟩⟩⟩
  have hbij : Function.Bijective e0 := by
    refine ⟨fun δ δ' h => injective_mk_io (congrArg Subtype.val h), fun q => ?_⟩
    obtain ⟨δ, hδ, hq⟩ := q.2
    refine ⟨⟨δ, hδ⟩, Subtype.ext ?_⟩
    have hm' : (q.1.out : GQ (dblSp V)) * (⟨io V (δ, 1), io_mem_GQ V hδ (one_mem _)⟩ : GQ (dblSp V))⁻¹ ∈
        (siegel V).subgroupOf (GQ (dblSp V)) := Subgroup.mem_subgroupOf.2 (by simpa using hq)
    exact (mk_eq_iff.2 ⟨⟨_, hm'⟩, by simp⟩).trans q.1.out_eq
  have hterm : ∀ (δ : GQ V) y, φ ((((e0 δ).1.out : GQ (dblSp V)) : GA D (dblSp V)) * y) = φ (io V ((δ : GA D V), 1) * y) :=
    fun δ y => term_mk hL y ⟨io V ((δ : GA D V), 1), io_mem_GQ V δ.2 (one_mem _)⟩
  obtain ⟨Eo, hEo⟩ : ∃ Eo : GA D (dblSp V) → ℂ, Eo = fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y) := ⟨_, rfl⟩
  obtain ⟨En, hEn⟩ : ∃ En : GA D (dblSp V) → ℂ, En = fun y => ∑' q : {q : GlobalTheory.Eis.SiegelCosets V // ¬ ∃ δ ∈ GQ V,
      ((q.out : GQ (dblSp V)) : GA D (dblSp V)) * (io V (δ, 1))⁻¹ ∈ siegel V},
      φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y) := ⟨_, rfl⟩
  have hEoP : ∀ y, Eo y = ∑' q : P, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y) := fun y => by
    rw [hEo, ← (Equiv.ofBijective e0 hbij).tsum_eq]
    exact tsum_congr fun δ => (hterm δ y).symm
  have hsumO : ∀ y, Summable fun δ : GQ V => φ (io V ((δ : GA D V), 1) * y) := fun y => by
    have := ((Equiv.ofBijective e0 hbij).summable_iff (f := fun q : P =>
      φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y))).2 ((hsum y).subtype (fun q => q ∈ P))
    exact this.congr fun δ => hterm δ y
  have hsplit : ∀ y, eis V φ y = Eo y + En y := fun y => by
    rw [hEoP, hEn]
    exact ((hsum y).tsum_subtype_add_tsum_subtype_compl P).symm

  have hEoInv : ∀ γ ∈ (GQ V).prod (GQ V), ∀ y, Eo (io V γ * y) = Eo y := by
    rintro ⟨γ₁, γ₂⟩ ⟨h1, h2⟩ y
    let e : GQ V ≃ GQ V := (Equiv.mulLeft (⟨γ₂, h2⟩ : GQ V)⁻¹).trans (Equiv.mulRight ⟨γ₁, h1⟩)
    rw [hEo]
    show ∑' δ : GQ V, φ (io V ((δ : GA D V), 1) * (io V (γ₁, γ₂) * y)) = ∑' δ : GQ V, φ (io V ((δ : GA D V), 1) * y)
    rw [← e.tsum_eq (fun δ : GQ V => φ (io V ((δ : GA D V), 1) * y))]
    refine tsum_congr fun δ => ?_
    have hd : io V ((δ : GA D V), 1) * (io V (γ₁, γ₂) * y) = io V (γ₂, γ₂) * (io V (((e δ : GQ V) : GA D V), 1) * y) := by
      rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
      congr 2
      refine Prod.ext ?_ ?_
      · simp [e, mul_assoc]
      · simp
    rw [hd, hL _ ⟨(io_mem_siegel V).2 rfl, io_mem_GQ V h2 h2⟩]
  have hi : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ Eo f₁ f₂) := fun γ hγ g => by
    simp only [dblIntegrand, map_mul (io V), hEoInv γ hγ, Prod.fst_mul, Prod.snd_mul, h₁.1 _ hγ.1, h₂.1 _ hγ.2,
      map_mul (detA V), map_mul μ, apply_detA hμ hγ.2, one_mul]

  have hEom : Measurable Eo := by
    rw [hEo]
    exact measurable_tsum_of_summable' (fun δ : GQ V => fun y => φ (io V ((δ : GA D V), 1) * y))
      (fun δ => (hφc.comp (continuous_const.mul continuous_id)).measurable) hsumO
  have hDm : Measurable (dblIntegrand V μ Eo f₁ f₂) := by
    have e : dblIntegrand V μ Eo f₁ f₂ = fun g => Eo (io V g) * dblIntegrand V μ (fun _ => 1) f₁ f₂ g :=
      funext fun g => by simp only [dblIntegrand]; ring
    rw [e]
    exact (hEom.comp (continuous_io V).measurable).mul
      (continuous_dblIntegrand hμ continuous_const h₁.continuous h₂.continuous).measurable

  have h𝓕 := isFundamentalDomain_stdDom (GQ V) m
  have habs := GlobalTheory.Core.Rk.AbsConv.absConv_unfolded D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂
  have hfin := habs.1 _ h𝓕
  have hmeasq : ∀ q : SiegelCosets V, AEMeasurable (fun x =>
      ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ)
      ((m.prod m).restrict (stdDom (GQ V) ×ˢ stdDom (GQ V))) := fun q =>
    (continuous_dblIntegrand hμ (hφc.comp (continuous_const.mul continuous_id)) h₁.continuous
      h₂.continuous).measurable.enorm.aemeasurable
  have hpt : ∀ x, ‖dblIntegrand V μ Eo f₁ f₂ x‖ₑ ≤ ∑' q : SiegelCosets V,
      ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ := fun x => by
    simp only [GlobalTheory.Core.Rk.AbsConv.enorm_dblIntegrand]
    rw [ENNReal.tsum_mul_right]
    gcongr ?_ * _
    rw [hEoP]
    exact enorm_tsum_le_tsum_enorm.trans (tsum_comp_le_tsum_of_injective (f := fun q : P => q.1) Subtype.val_injective
      (fun q : SiegelCosets V => ‖φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * io V x)‖ₑ))
  have hOn : IntegrableOn (dblIntegrand V μ Eo f₁ f₂) (stdDom (GQ V) ×ˢ stdDom (GQ V)) (m.prod m) := by
    refine ⟨hDm.aestronglyMeasurable, ?_⟩
    show ∫⁻ x in stdDom (GQ V) ×ˢ stdDom (GQ V), ‖dblIntegrand V μ Eo f₁ f₂ x‖ₑ ∂m.prod m < ⊤
    calc _ ≤ ∫⁻ x in stdDom (GQ V) ×ˢ stdDom (GQ V), ∑' q : SiegelCosets V,
          ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ ∂m.prod m :=
          lintegral_mono hpt
      _ = _ := lintegral_tsum hmeasq
      _ < ⊤ := hfin.lt_top
  have hEoC : DblConv V μ m Eo f₁ f₂ := (dblConv_iff hi hDm h𝓕).2 hOn

  have hQ : ∀ q, dblIntegrandQ V μ (eis V φ) f₁ f₂ q = dblIntegrandQ V μ Eo f₁ f₂ q + dblIntegrandQ V μ En f₁ f₂ q :=
    fun q => by simp only [dblIntegrandQ, dblIntegrand, hsplit]; ring
  have hEnI : Integrable (dblIntegrandQ V μ En f₁ f₂) ((autMeasure V m).prod (autMeasure V m)) :=
    (habs.2.2.sub hEoC.2).congr (Eventually.of_forall fun q => by simp only [Pi.sub_apply, hQ]; ring)
  have h6 := GlobalTheory.T.doubling_integral_negligible_orbits_eq_zero_cuspForm D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂ hcusp
  have h7 := _root_.GlobalTheory.Core.Rk.OpenOrbit.open_orbit D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂
  rw [← hEn] at h6
  rw [← hEo] at h7
  refine ⟨habs.2, h7.1, ?_⟩
  show ∫ q, dblIntegrandQ V μ (eis V φ) f₁ f₂ q ∂(autMeasure V m).prod (autMeasure V m) = _
  rw [integral_congr_ae (Eventually.of_forall hQ), integral_add hEoC.2 hEnI, h7.2, h6, add_zero]

end GlobalTheory.Core.Rk.BasicId

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPrimeToDvdAway
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HalfTmul

theorem exists_prime_to_dvd_away {R : Type} [CommRing R] [IsDedekindDomain R] (SS : Finset (HeightOneSpectrum R))
    (m : R) (hm : m ≠ 0) : ∃ t : R, t ≠ 0 ∧ (∀ Q ∈ SS, t ∉ Q.asIdeal) ∧
      ∀ Q : HeightOneSpectrum R, Q ∉ SS → ∃ u : R, u ∉ Q.asIdeal ∧ ∃ w : R, u * t = m * w := by
  classical
  have hI : Ideal.span {m} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hm
  have hfac : ∀ Q : HeightOneSpectrum R, ∃ n : ℕ, ∃ J : Ideal R, ¬ Q.asIdeal ∣ J ∧ Ideal.span {m} = Q.asIdeal ^ n * J :=
    fun Q => WfDvdMonoid.max_power_factor hI Q.prime.irreducible
  choose n J hJ using hfac
  have hT := Ideal.finite_factors hI
  obtain ⟨t0, ht0⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := SS ∪ hT.toFinset) (fun Q => Q.asIdeal)
    (fun Q => if Q ∈ SS then 1 else n Q) (fun Q _ => Q.prime) (fun Q _ Q' _ h e => h (HeightOneSpectrum.ext e))
    (fun Q => if (Q : HeightOneSpectrum R) ∈ SS then 1 else 0)
  have hone : ∀ Q : HeightOneSpectrum R, (1 : R) ∉ Q.asIdeal := fun Q h1 =>
    Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hSS : ∀ Q ∈ SS, t0 ∉ Q.asIdeal := by
    intro Q hQ hmem
    have h := ht0 Q (Finset.mem_union_left _ hQ)
    simp only [if_pos hQ, pow_one] at h
    exact hone Q (by simpa using Q.asIdeal.sub_mem hmem h)
  have hgood : ∀ Q : HeightOneSpectrum R, Q ∉ SS → ∃ u : R, u ∉ Q.asIdeal ∧ ∃ w : R, u * t0 = m * w := by
    intro Q hQ
    by_cases hQT : Q.asIdeal ∣ Ideal.span {m}
    · have h := ht0 Q (Finset.mem_union_right _ (hT.mem_toFinset.2 hQT))
      simp only [if_neg hQ, sub_zero] at h
      obtain ⟨hnd, hEq⟩ := hJ Q
      rw [Ideal.dvd_iff_le] at hnd
      obtain ⟨u, huJ, huQ⟩ := SetLike.not_le_iff_exists.1 hnd
      refine ⟨u, huQ, ?_⟩
      have hmem : t0 * u ∈ Ideal.span {m} := by
        rw [hEq]; exact Ideal.mul_mem_mul h huJ
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 hmem
      exact ⟨w, by rw [mul_comm u, hw]⟩
    · refine ⟨m, ?_, t0, rfl⟩
      intro hmem
      exact hQT (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hmem))
  by_cases h0 : t0 = 0
  · refine ⟨m, hm, ?_, fun Q _ => ⟨1, hone Q, 1, by ring⟩⟩
    intro Q hQ
    exact absurd (h0 ▸ Q.asIdeal.zero_mem) (hSS Q hQ)
  · exact ⟨t0, h0, hSS, hgood⟩

theorem tmul_mem_of {E : Type} [Field E] [NumberField E] [StarRing E] {W : Type} [AddCommGroup W] [Module E W]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] (M : Submodule (𝓞 E) W) (SS : Finset (HeightOneSpectrum (𝓞 E)))
    (c : ℕ) (hc : 0 < c) (y : W) (hy : y ∈ twist₂ M c (expS SS)) (t : 𝓞 E)
    (ht : ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ SS → ∃ u : 𝓞 E, u ∉ Q.asIdeal ∧ ∃ w : 𝓞 E, u * t = (c : 𝓞 E) ^ 2 * w) :
    ((t : E) * (c : E)⁻¹) • y ∈ M := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have hcast : ∀ (r : 𝓞 E) (z : W), (r : E) • z = r • z := fun r z => IsScalarTower.algebraMap_smul E r z
  have hcy : (c : E) • y ∈ M := by
    have h := (GlobalTheory.CommonReps.mem_twO_zero M c _).1 (GlobalTheory.CommonReps.natsmul_mem_twO M c _ _ (fun Q => by
      rcases expS_cases SS Q with h | h | h <;> rw [h] <;> norm_num) hy)
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at h
  apply Formalism.L2.Ker.mem_of_forall_locP M
  intro Q
  by_cases hQ : Q ∈ SS
  · have h1 := (Formalism.L2.Ker.mem_twO M c _ y).1 hy Q
    simp only [expS, if_pos hQ, zpow_one] at h1
    obtain ⟨s, hs, hsy⟩ := h1
    refine ⟨s, hs, ?_⟩
    have e : s • (((t : E) * (c : E)⁻¹) • y) = t • (s • ((c : E)⁻¹ • y)) := by
      rw [← hcast s, ← hcast t, ← hcast s]
      simp only [smul_smul]
      congr 1; ring
    rw [e]; exact M.smul_mem t hsy
  · obtain ⟨u, hu, w, huw⟩ := ht Q hQ
    refine ⟨u, hu, ?_⟩
    have huwE : (u : E) * (t : E) = (c : E) ^ 2 * (w : E) := by
      have := congrArg (fun r : 𝓞 E => (r : E)) huw
      simpa using this
    have e : u • (((t : E) * (c : E)⁻¹) • y) = w • ((c : E) • y) := by
      rw [← hcast u, ← hcast w]
      simp only [smul_smul]
      congr 1
      field_simp
      linear_combination huwE
    rw [e]; exact M.smul_mem w hcy

theorem exists_tmul_mem_perO : ∀ (D : D7) (a b : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ), 0 < c → ∀ y ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∃ t : 𝓞 D.host.E, t ≠ 0 ∧ (∀ Q ∈ SS, t ∉ Q.asIdeal) ∧ ((t : D.host.E) * (c : D.host.E)⁻¹) • y ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
  intro D a b N N' SS c hc y hy
  obtain ⟨t, ht0, hSS, hgood⟩ := exists_prime_to_dvd_away SS ((c : 𝓞 D.host.E) ^ 2)
    (pow_ne_zero _ (by exact_mod_cast hc.ne'))
  exact ⟨t, ht0, hSS, tmul_mem_of _ SS c hc y hy t hgood⟩

end GlobalTheory.HalfTmul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenusTypePlaceSetNotConjugatePlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genusTypePlaceSet_not_conjugatePlaces : ∀ {D : D7} (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → (∃ e, IsIdemSum e Pg) → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP' := by
  first | exact @GlobalTheory.SeeConjPg.pg_places_not_isConjPl | exact GlobalTheory.SeeConjPg.pg_places_not_isConjPl | (intros; apply GlobalTheory.SeeConjPg.pg_places_not_isConjPl <;> assumption)
end

