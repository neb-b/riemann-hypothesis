module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0242
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodMajorantLevelConjUnitaryAdelicMaximalCompact
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch

theorem good_level_conj_stab : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D)), IsMaj T b → HasIw d (Kmax T b) → ∀ l : Lvl T, l.Good → HasIw d l.K ∧ IsCompact (l.K : Set (GA D T)) ∧ ∃ q : stab d, ConjBy (q : GA D T) l.K (Kmax T b) := by
  intro D T T₀ r d b hb hIw l hl
  have hL0 : GlobalTheory.EisCont.IsLevel T (AdelicU.frameLat T) b :=
    ⟨(AdelicU.SelfDual.isLattice_frameLat T).toIsLattice, AdelicU.SelfDual.isSelfDualAt_frameLat D T, hb⟩
  have hL : GlobalTheory.EisCont.IsLevel T l.L l.c := ⟨hl.1.toIsLattice, hl.2.1, hl.2.2⟩
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.EisCont.LevelConj.exists_conj D T (AdelicU.frameLat T) l.L b l.c hL0 hL
  obtain ⟨q, k₀, hk₀, hgq⟩ := hIw g
  have hconj : ConjBy (q : GA D T) l.K (Kmax T b) := by
    intro k
    have h1 : k ∈ l.K ↔ g⁻¹ * k * g ∈ Kmax T b := hg k
    rw [h1, hgq]
    constructor
    · intro h
      have := (Kmax T b).mul_mem (hk₀) ((Kmax T b).mul_mem h ((Kmax T b).inv_mem hk₀))
      simpa [mul_assoc] using this
    · intro h
      have := (Kmax T b).mul_mem ((Kmax T b).inv_mem hk₀) ((Kmax T b).mul_mem h hk₀)
      simpa [mul_assoc] using this
  haveI : Submodule.IsFullLattice D.host.E l.L := hl.1
  refine ⟨?_, isCompact_levelAll (AdelicU.isCMExt_host D) _ _ _, q, hconj⟩
  intro h
  obtain ⟨q₁, k₁, hk₁, e⟩ := hIw (h * q)
  refine ⟨q₁ * q⁻¹, (q : GA D T) * k₁ * (q : GA D T)⁻¹, ?_, ?_⟩
  · rw [hconj]
    simpa [mul_assoc] using hk₁
  · have : h = (q₁ : GA D T) * k₁ * (q : GA D T)⁻¹ := by rw [← e]; group
    rw [this]; simp [mul_assoc]

end GlobalTheory.RegSch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodPositionSplitLinesReadCompletionsAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocCongr

variable {D : D7}

theorem mul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {z : Fin S.rank → AE D} (hz : z ∈ latV S L P) :
    (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) ∈ latA S L P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (0 : Fin S.rank → AE D) i) = 0 := by
      funext i; simp
    rw [this]; exact zero_mem _
  | add z z' _ _ hz hz' =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (z + z') i) =
        (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) + (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z' i) := by
      funext i; simp [mul_add]
    rw [this]; exact add_mem hz hz'
  | neg z _ hz =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (-z) i) =
        -(fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) := by
      funext i; simp
    rw [this]; exact neg_mem hz

theorem latA_le_of_latV_le {S : HSp D} {L L' : Lat S} {P : Pl D → Prop} (h : latV S L P ≤ latV S L' P) :
    latA S L P ≤ latA S L' P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩
  have hz : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) ∈ latV S L P :=
    AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
  have hm := mul_mem_latA (L := L') ha (h hz)
  have key : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
      fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [SetLike.mem_coe, key]
  exact hm

theorem latA_congr {S : HSp D} {L L' : Lat S} {P : Pl D → Prop} (h : latV S L P = latV S L' P) :
    latA S L P = latA S L' P :=
  le_antisymm (latA_le_of_latV_le h.le) (latA_le_of_latV_le h.ge)

theorem latO_congr {S T : HSp D} {LS LS' : Lat S} {LT LT' : Lat T} (hS : IsSelfDualC S LS) (hS' : IsSelfDualC S LS')
    (hT : IsSelfDualC T LT) (hT' : IsSelfDualC T LT') {P : Pl D → Prop} (eS : latV S LS P = latV S LS' P)
    (eT : latV T LT P = latV T LT' P) :
    latO S T (LS : Set _) (LT : Set _) P = latO S T (LS' : Set _) (LT' : Set _) P := by
  ext u
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT, GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS' LT' hS' hT', eS,
    latA_congr eT]

theorem monoAt_congr {S S₀ : HSp D} {ρ : ℕ} {d : HypDec S S₀ ρ} {L L' : Lat S} {L₀ L₀' : Lat S₀} {v : Pl D}
    (e : latV S L (· = v) = latV S L' (· = v)) (e₀ : latV S₀ L₀ (· = v) = latV S₀ L₀' (· = v)) (H : MonoAt d L L₀ v) :
    MonoAt d L' L₀' v := by
  unfold MonoAt at H ⊢
  rw [← e, ← e₀]
  exact H

theorem orthAt_congr {S A B : HSp D} {o : OrthDec S A B} {L L' : Lat S} {LA : Lat A} {LB : Lat B} {v : Pl D}
    (e : latV S L (· = v) = latV S L' (· = v)) (H : OrthAt o L LA LB v) : OrthAt o L' LA LB v := by
  unfold OrthAt at H ⊢
  rw [← e]
  exact H

theorem primAt_congr {ψ : AddChar (AF D.host.F) ℂ} {S S₀ : HSp D} {ρ : ℕ} {d : HypDec S S₀ ρ} {L L' : Lat S} {v : Pl D}
    (e : latV S L (· = v) = latV S L' (· = v)) (H : PrimAt ψ d L v) : PrimAt ψ d L' v := by
  unfold PrimAt at H ⊢
  rw [← e]
  exact H

theorem colsAt_congr {V V₀ W : HSp D} {ρ : ℕ} {d : HypDec V V₀ ρ} {x : Mx D W.rank ρ} {LV LV' : Lat V} {LW LW' : Lat W}
    {v : Pl D} (e : latV V LV (· = v) = latV V LV' (· = v)) (eW : latV W LW (· = v) = latV W LW' (· = v))
    (H : ColsAt d x LV LW v) : ColsAt d x LV' LW' v := by
  unfold ColsAt at H ⊢
  rw [← e, ← latA_congr eW]
  exact H

end GlobalTheory.LocCongr

namespace GlobalTheory.LocCongr

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem goodBF_congr {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} {LV LV' : Lat B.V} {LV₀ LV₀' : Lat B.V₀} {LW LW' : Lat J.W}
    {LW₀ : Lat J.W₀} {v : Pl D} (sV : IsSelfDualC B.V LV') (sV₀ : IsSelfDualC B.V₀ LV₀') (sW : IsSelfDualC J.W LW')
    (eV : latV B.V LV (· = v) = latV B.V LV' (· = v)) (eV₀ : latV B.V₀ LV₀ (· = v) = latV B.V₀ LV₀' (· = v))
    (eW : latV J.W LW (· = v) = latV J.W LW' (· = v)) (H : GoodBF ψ B J LV LV₀ LW LW₀ v) :
    GoodBF ψ B J LV' LV₀' LW' LW₀ v :=
  { tame := H.tame
    sdV := sV
    sdV₀ := sV₀
    sdW := sW
    sdW₀ := H.sdW₀
    monoV := monoAt_congr eV eV₀ H.monoV
    monoW := monoAt_congr eW rfl H.monoW
    prim := primAt_congr eV H.prim
    cols := colsAt_congr eV eW H.cols
    last := by
      rw [← latO_congr H.sdV₀ sV₀ H.sdW sW eV₀ eW]
      exact H.last }

theorem adaptFB_congr {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} {LV LV' : Lat J.W} {LV₀ : Lat J.W₀}
    {LW LW' : Lat B.V} {LW₀ LW₀' : Lat B.V₀} {v : Pl D} (sV : IsSelfDualC J.W LV') (sW : IsSelfDualC B.V LW')
    (sW₀ : IsSelfDualC B.V₀ LW₀') (eV : latV J.W LV (· = v) = latV J.W LV' (· = v))
    (eW : latV B.V LW (· = v) = latV B.V LW' (· = v)) (eW₀ : latV B.V₀ LW₀ (· = v) = latV B.V₀ LW₀' (· = v))
    (H : AdaptFB ψ J B LV LV₀ LW LW₀ v) : AdaptFB ψ J B LV' LV₀ LW' LW₀' v :=
  { tame := H.tame
    sdV := sV
    sdV₀ := H.sdV₀
    sdW := sW
    sdW₀ := sW₀
    monoV := monoAt_congr eV rfl H.monoV
    monoW := monoAt_congr eW eW₀ H.monoW
    prim := primAt_congr eV H.prim
    cols := colsAt_congr eV eW H.cols }

theorem goodAt_splitAt_congr : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀)
    (x : Pl D), (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) ∧ IsSelfDualC (c.V j) (N j) ∧
      latV (c.V j) (N j) (· = x) = latV (c.V j) (v.N j) (· = x)) →
    (∀ j ρ h, IsSelfDualC _ (o.M j ρ h) ∧ IsSelfDualC _ (M j ρ h) ∧ latV _ (M j ρ h) (· = x) = latV _ (o.M j ρ h) (· = x)) →
    (GoodAt v o x → GoodAt { v with N := N } { o with M := M } x) ∧
      (SplitAt v o x → SplitAt { v with N := N } { o with M := M } x) := by
  intro D c v k _ _ _ _ ι o N M x hN hM
  refine ⟨fun hg => ⟨fun j ρ h => ?_, fun j σ h => ?_⟩, fun hs => ⟨fun j ρ h => ?_, fun j h => ?_⟩⟩
  · have h0 := hN j (by omega)
    have h1 := hN (j + 1) (by omega)
    exact goodBF_congr h0.2.1 (hM j ρ h).2.1 h1.2.1 h0.2.2.symm (hM j ρ h).2.2.symm h1.2.2.symm (hg.bf j ρ h)
  · have h1 := hN (j + 1) (by omega)
    have h2 := hN (j + 1 + 1) (by omega)
    exact adaptFB_congr h1.2.1 h2.2.1 (hM (j + 1 + 1) σ (idx_step h)).2.1 h1.2.2.symm h2.2.2.symm
      (hM (j + 1 + 1) σ (idx_step h)).2.2.symm (hg.fb j σ h)
  · obtain ⟨LL, hLL, hO⟩ := hs.core j ρ h
    exact ⟨LL, hLL, orthAt_congr (hM j ρ h).2.2.symm hO⟩
  · obtain ⟨LL, LZ, h1, h2, h3, h4, h5⟩ := hs.top j h
    exact ⟨LL, LZ, h1, h2, orthAt_congr (hM j 0 h).2.2.symm h3, h4, h5⟩

end GlobalTheory.LocCongr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfGeneratedPointActsScalarOnLatticeVacua
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfGenScalar

theorem addChar_ne_zero {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := by
  intro h
  have h1 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem exists_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (z : WO S T),
    z ∈ AddSubgroup.closure {u | u ∈ Λ ∧ ∃ e, IsSplitIdem D e ∧ IsHalf e u} →
    ∃ c : ℂ, ∀ f, IsLatVac (heisO ψ S T) Λ f → heisO ψ S T z f = c • f := by
  intro D ψ S T Λ z hz
  induction hz using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨huΛ, e, he, hh⟩ := hu
    exact ⟨1, fun f hf => by rw [one_smul]; exact hf.2 e he u huΛ hh⟩
  | zero => exact ⟨1, fun f _ => by rw [one_smul]; exact GlobalTheory.SplitScalar.heisO_zero ψ S T f⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨cx, hcx⟩ := ihx
    obtain ⟨cy, hcy⟩ := ihy
    refine ⟨(ψ (symplOH S T x y))⁻¹ * (cx * cy), fun f hf => ?_⟩
    have h1 := GlobalTheory.SplitScalar.heisO_heisO ψ S T x y f
    rw [hcy f hf, GlobalTheory.SplitScalar.heisO_smul, hcx f hf, smul_smul] at h1
    have hne := addChar_ne_zero ψ (symplOH S T x y)
    rw [mul_smul, mul_comm cx cy, h1, smul_smul, inv_mul_cancel₀ hne, one_smul]
  | neg x _ ihx =>
    obtain ⟨cx, hcx⟩ := ihx
    by_cases h0 : cx = 0
    · refine ⟨0, fun f hf => ?_⟩
      have h1 := GlobalTheory.SplitScalar.heisO_heisO ψ S T (-x) x f
      rw [hcx f hf, h0, zero_smul, neg_add_cancel, GlobalTheory.SplitScalar.heisO_zero] at h1
      have hf0 : f = 0 := by
        have h2 : heisO ψ S T (-x) (0 : WO S T → ℂ) = 0 := by
          simpa using GlobalTheory.SplitScalar.heisO_smul ψ S T (-x) 0 (0 : WO S T → ℂ)
        rw [h2] at h1
        exact (smul_eq_zero.1 h1.symm).resolve_left (addChar_ne_zero ψ _)
      subst hf0
      rw [zero_smul]
      simpa using GlobalTheory.SplitScalar.heisO_smul ψ S T (-x) 0 (0 : WO S T → ℂ)
    · refine ⟨ψ (symplOH S T (-x) x) / cx, fun f hf => ?_⟩
      have h1 := GlobalTheory.SplitScalar.heisO_heisO ψ S T (-x) x f
      rw [hcx f hf, GlobalTheory.SplitScalar.heisO_smul, neg_add_cancel, GlobalTheory.SplitScalar.heisO_zero] at h1
      rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ h0, one_smul]

end GlobalTheory.HalfGenScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtHeisenbergThetaSeriesStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_heisenberg_thetaSeries : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (φ : Mx D B.rank A.rank → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → ∀ f : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ (HMul.hMul w (dblDec A).jX + rat ξ)) → ∀ M : ℝ →+ WO (dblSp A) B, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ φ' : Mx D B.rank A.rank → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' ∧ ∀ f' : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f' w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ' (HMul.hMul w (dblDec A).jX + rat ξ)) → ∀ w, HasDerivAt (fun t : ℝ => heisO ψ (dblSp A) B (M t) f w) (f' w) 0 := by
  first | exact @GlobalTheory.Core.Rk.OntoDer.hasDerivAt_heisO_thetaSeries | exact GlobalTheory.Core.Rk.OntoDer.hasDerivAt_heisO_thetaSeries | (intros; apply GlobalTheory.Core.Rk.OntoDer.hasDerivAt_heisO_thetaSeries <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionLeClosureIsotropicHalves
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HalfGen

variable {D : D7}

theorem list_sum_pair {ι : Type} (l : List ι) (α : ι → Af D.host.F) :
    (l.map fun i => pairA D.host.F 0 (α i) ⊗ₜ[D.host.F] (1 : D.host.E)).sum =
      pairA D.host.F 0 (l.map α).sum ⊗ₜ[D.host.F] (1 : D.host.E) := by
  induction l with
  | nil => simp [GlobalTheory.FinPlLoc.pairA_zero]
  | cons a l ih => simp [List.map_cons, List.sum_cons, ih, GlobalTheory.FinPlLoc.pairA_add, TensorProduct.add_tmul]

theorem sum_splitIdem_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} {p : ι → SplitPt D k} {I : List ι} {P : Pl D → Prop} (h : Places p I P) :
    (I.map fun i => (p i).e + cA D (p i).e).sum = GlobalTheory.FinPlLoc.idem D P := by
  classical
  choose ε hε hεe using fun i => (p i).above
  choose α hαe hα1 hα0 using hε
  have hterm : ∀ i, (p i).e + cA D (p i).e = pairA D.host.F 0 (α i) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    intro i
    rw [hεe i, hαe i]
    rfl
  rw [List.map_congr_left (fun i _ => hterm i), list_sum_pair]
  unfold GlobalTheory.FinPlLoc.idem
  congr 2
  refine RestrictedProduct.ext _ _ fun w => ?_
  show evalV D.host.F w (I.map α).sum = evalV D.host.F w (GlobalTheory.FinPlLoc.ePl D P)
  rw [GlobalTheory.FinPlLoc.evalV_ePl, map_list_sum, List.map_map, ← List.sum_toFinset _ h.nodup]
  by_cases hw : P w
  · rw [if_pos hw]
    obtain ⟨j, rfl⟩ := (h.mem w).1 hw
    have hj : ∀ i, evalV D.host.F (p j).v (α i) = if i = j then 1 else 0 := by
      intro i
      split_ifs with hij
      · subst hij; exact hα1 i
      · exact hα0 i _ fun hv => hij (h.inj hv.symm)
    simp only [Function.comp_apply, hj]
    rw [Finset.sum_ite_eq' , if_pos (List.mem_toFinset.2 (h.all j))]
  · rw [if_neg hw]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact hα0 i w fun hv => hw ((h.mem w).2 ⟨i, hv⟩)

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, hsum⟩ := he
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hε, ?_⟩
  · rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2]
  · rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, hsum]

theorem smul_mem_halves {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : Pl D → Prop} {e : AE D} (he : IsSplitIdem D e) {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    e • u ∈ {x | x ∈ latO S T LS LT P ∧ ∃ e, IsSplitIdem D e ∧ IsHalf e x} := by
  have hee : e * e = e := he.1
  refine ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT P e ?_ u hu, e, he, ?_⟩
  · exact GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D e) (by rw [← map_mul, hee])
  · rw [GlobalTheory.SplitScalar.isHalf_iff, smul_smul, hee]

theorem entry_mem_idAt {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : Pl D → Prop} {u : WO S T} (hu : u ∈ latO S T LS LT P) : ∀ i j, u i j ∈ idAt D P := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, -, hα, a, -, s, -, t, -, rfl⟩ := hy
    exact fun i j => GlobalTheory.FinPlLoc.pair_mem_idAt P α hα _
  | zero => exact fun i j => zero_mem _
  | add y z _ _ hy hz => exact fun i j => add_mem (hy i j) (hz i j)
  | neg y _ hy => exact fun i j => neg_mem (hy i j)

theorem latO_le_closure_halves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), ∀ u ∈ latO S T LS LT P, u ∈ AddSubgroup.closure {x | x ∈ latO S T LS LT P ∧ ∃ e, IsSplitIdem D e ∧ IsHalf e x} := by
  intro D k _ _ _ _ ι p I P h S T LS LT u hu
  have hsum := sum_splitIdem_eq h
  have hu' : GlobalTheory.FinPlLoc.idem D P • u = u := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (GlobalTheory.FinPlLoc.mem_idAt_iff P _).1 (entry_mem_idAt hu i j)
  have hdec : u = (I.map fun i => (p i).e • u + cA D (p i).e • u).sum := by
    conv_lhs => rw [← hu', ← hsum, List.sum_smul, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, add_smul]
  rw [hdec]
  refine AddSubgroup.list_sum_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact add_mem (AddSubgroup.subset_closure (smul_mem_halves (p i).split hu))
    (AddSubgroup.subset_closure (smul_mem_halves (isSplitIdem_cA (p i).split) hu))

end GlobalTheory.HalfGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabiliserFinitePlaceStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_isotropic_stabiliser_finite_place : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r), (∀ v : FinPl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → ∀ (v : FinPl D) (y : Gv T v), ∃ q k : Gv T v, emb D.sp.cm.sig T.gram v q ∈ stab d ∧ k ∈ stabLoc D.sp.cm.sig T.gram (frameLat T) v ∧ y = q * k := by
  first | exact @GlobalTheory.Core.Rk.IwFin.iwasawa_fin | exact GlobalTheory.Core.Rk.IwFin.iwasawa_fin | (intros; apply GlobalTheory.Core.Rk.IwFin.iwasawa_fin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastPeriodClassesGiveTailReading
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem tailRd_of_clsT : ∀ (D : D7) (c : Comm D) (t : Tup c) (ρ : RealD c) (A : ClsT ρ t), A.Is → t.cP ≠ 0 → t.TailRd := by
  intro D c t ρ A hA hcP n h ψ hψ ψ' hψ' a H F
  have e1 := hA.tail n h ψ hψ F
  have e2 := hA.tail n h ψ' hψ' F
  have key : ∀ β (x : A.cl), A.ell n h β x F (ρ.low n h fun z => t.rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) =
      a * A.ell n h β x F (ρ.low n h fun z => t.rd n β ψ' ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) := by
    intro β x
    have : (fun z => t.rd n β ψ ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) =
        a • (fun z => t.rd n β ψ' ((ρ.fr n).symm z) ((c.oT n h).emb (A.h x, 1))) := by
      funext z
      rw [H β ((ρ.fr n).symm z)]
      rfl
    rw [this, map_smul, map_smul, smul_eq_mul]
  simp_rw [key] at e1
  have e3 : t.cP * t.tail n h ψ F = t.cP * (a * t.tail n h ψ' F) := by
    rw [← e1, mul_left_comm t.cP a, ← e2]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  exact mul_left_cancel₀ hcP e3

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResidueSupportSinglePlaceToConjugatePairSlotStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueSupport_single_place_to_conjugatePair_position : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP') → ∀ R : Formalism.L2.Herm.intAf D.host.F D.host.E → Prop, (∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ Q' : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q'.asIdeal → Q' ≠ Q → resS D.host.F Q' s = 0) ∧ R s) → ∀ PP ∈ Pg, (∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ PP' ∈ Pg, (PP' ≠ PP → resS D.host.F PP' s = 0) ∧ resS D.host.F PP' (sigInt (instOf D) s) = 0) ∧ R s) ∧ ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ PP' ∈ Pg, resS D.host.F PP' s = 0 ∧ (PP' ≠ PP → resS D.host.F PP' (sigInt (instOf D) s) = 0)) ∧ R s := by
  first | exact @GlobalTheory.ConjSlot.intersection_update_fsHerm_neg_one | exact GlobalTheory.ConjSlot.intersection_update_fsHerm_neg_one | (intros; apply GlobalTheory.ConjSlot.intersection_update_fsHerm_neg_one <;> assumption)
end

