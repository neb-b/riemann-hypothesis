module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLocalZetaNonvanishingOfReal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.ZetaNeProof

variable {D : D7}

theorem coefW_mul_lev {c : Com D} {s s' : PiLocalization₂ D} (p : Step c s s') (m : Measure (WO s.V s'.V))
    (X : Set (WO s.V s'.V)) (φ : PolF D s'.V.rank s.V.rank)
    (hlaw : ∀ κ ∈ Lev.levG s.V s.β s.L, (p.ω (κ, 1)) (p.pt φ) = Lev.levChi s.V s.β s.L κ • p.pt φ)
    (b : GA D s.V) (κ : GA D s.V) (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    coefW p.ω m X (p.pt φ) (b * κ) = Lev.levChi s.V s.β s.L κ * coefW p.ω m X (p.pt φ) b := by
  have hmul : p.ω (b * κ, 1) = p.ω (b, 1) * p.ω (κ, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hv : p.ω (b * κ, 1) (p.pt φ) = Lev.levChi s.V s.β s.L κ • p.ω (b, 1) (p.pt φ) := by
    rw [hmul, Module.End.mul_apply, hlaw κ hκ, map_smul]
  unfold coefW
  rw [hv, ← integral_const_mul]
  congr 1
  funext w
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem hgtS_mul_lev {c : Com D} {s : PiLocalization₂ D} (hs : IsSelfDualC s.V s.Λ)
    (hstab : ∀ k ∈ Lev.levG s.V s.β s.L, ∀ v,
      GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v)
    (a : GL (Fin s.V.rank) (AE D)) (b : GinfC s.V) (κ : GA D s.V) (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    hgtS c s a ((b : GA D s.V) * κ) =
      ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V)) := by
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.ChainOnto.hgt_one_components D s.V s.Λ hs
  have hκf : κ ∈ GfC s.V := (Subgroup.mem_inf.mp hκ).1
  unfold hgtS
  have hA : ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w ((b : GA D s.V) * κ) =
      GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V) := by
    intro w
    rw [map_mul, h2 κ hκf w, mul_one]
  have hF : ∀ v ∈ c.S, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v
      (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v ((b : GA D s.V) * κ)) = 1 := by
    intro v _
    rw [map_mul, h3 b b.2 v, one_mul]
    exact h1 v _ (hstab κ hκ v)
  simp only [hA]
  rw [Finset.prod_eq_one hF, mul_one]

theorem zetaNe_of_real : ∀ D : D7, MetEx D → LevFacts D → LevelLaw D → CoefSupp D → RealZeta D → ZetaNe D := by
  intro D hMet hLev hLaw hSupp hRZ
  intro hng c hc k hk s s' hs hs' p hp m X hcov
  obtain ⟨φ, v, hvK, hR⟩ := hRZ hng c hc k hk s s' hs hs' p hp m X hcov
  have hkm : k ≤ D.R.m := hk.le
  obtain ⟨ipD, ip, hip⟩ := hMet c hc k hkm s hs
  obtain ⟨_, _, hLF3, _, _, hLF6⟩ := hLev c hc k hkm s hs
  obtain ⟨hmOff, _, hAsub, _, mR, hmR, hint⟩ := _root_.GlobalTheory.ChainOnto.HaarInf.pushforward_haar_real D hLev c hc k hkm s hs
  have hpet := _root_.GlobalTheory.ChainOnto.PetCoef.petco D c hc k hkm s hs ipD ip hip
  have hlaw := (hLaw hng c hc k hk s s' hs hs' p hp φ).1
  have hsupp := hSupp hng c hc k hk s s' hs hs' p hp m X hcov φ
  obtain ⟨hz, hzI⟩ := hR mR hmR
  refine ⟨φ, PiTensorProduct.tprod ℂ v, Submodule.subset_span ⟨v, hvK, rfl⟩, ?_⟩
  intro u hu
  have hipu : ip u u ≠ 0 := by
    intro h0
    have := hip.pos u hu
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this
  have hcipu : conj (ip u u) ≠ 0 := (map_ne_zero _).mpr hipu

  have hlawZ : ∀ (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L,
      p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) ((b : GA D s.V) * κ) =
        conj (ip u u) * (coefW p.ω m X (p.pt φ) (b : GA D s.V) *
          conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) := by
    intro b κ hκ
    unfold Step.zint
    rw [coefW_mul_lev p m X φ hlaw _ κ hκ, hpet u v b κ hκ]
    have hn : Lev.levChi s.V s.β s.L κ * conj (Lev.levChi s.V s.β s.L κ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hLF6 κ hκ]
      norm_num
    simp only [map_mul]
    linear_combination (conj (ip u u) * coefW p.ω m X (p.pt φ) (b : GA D s.V) *
      conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) * hn

  have hoff : ∀ g ∈ intOff c s \ {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L},
      p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) g = 0 := by
    rintro g ⟨hg, hgA⟩
    unfold Step.zint
    rw [hsupp g hg hgA, zero_mul]
  have hzInt : Integrable (fun g : GinfC s.V => coefW p.ω m X (p.pt φ) (g : GA D s.V) *
      conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) mR := by
    by_contra hni
    exact hz (integral_undef hni)
  refine ⟨?_, ?_⟩
  · rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero hmOff hAsub hoff]
    rw [(hint _ _ (hzInt.const_mul (conj (ip u u))) hlawZ).2, integral_const_mul]
    exact mul_ne_zero hcipu hz
  · intro a hmaj hcomp
    obtain ⟨s₁, hs₁, hI⟩ := hzI a hmaj hcomp
    refine ⟨s₁, hs₁, ?_⟩
    refine IntegrableOn.of_forall_diff_eq_zero (s := {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L}) ?_ hmOff ?_
    · refine (hint _ _ (hI.const_mul (conj (ip u u))) ?_).1
      intro b κ hκ
      rw [hlawZ b κ hκ, hgtS_mul_lev hs.selfDual hLF3 a b κ hκ, mul_assoc]
    · intro g hg
      rw [hoff g hg, zero_mul]

end GlobalTheory.ChainOnto.ZetaNeProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageFiniteLevelEqProductLocalLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw.LevLoc

variable {D : D7}

def LocOK {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (PP : Pl D.host.E) (y : GL (Fin n) (Formalism.L2.DIV.kP PP)) : Prop :=
  (PP ∈ L.Pg → y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) ∧ Formalism.L2.DIV.upperLeftBlock L.hr y = 1) ∧
    (PP ∈ L.Q → y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 L.r))

theorem locOK_one {n : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (PP : Pl D.host.E) : LocOK L PP 1 :=
  ⟨fun _ => ⟨one_mem _, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _⟩, fun _ => one_mem _⟩

theorem mem_lev_iff {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (hP : L.P.H = ⊥) (x : GL (Fin n) (Lev.EAf D)) :
    x ∈ Formalism.L2.DIV.lev D.sp.cm J β L ↔ x ∈ Formalism.L2.DIV.UA D.sp.cm J ∧ x ∈ Formalism.L2.DIV.St β ∧
      ∀ PP, LocOK L PP (Formalism.L2.DIV.redFn β PP x) := by
  rw [Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev, hP, Subgroup.mem_bot]
  constructor
  · rintro ⟨⟨hU, hS, hg, hq⟩, hr⟩
    exact ⟨hU, hS, fun PP => ⟨fun h => ⟨hg PP h, congrFun hr ⟨PP, h⟩⟩, fun h => hq PP h⟩⟩
  · rintro ⟨hU, hS, h⟩
    exact ⟨⟨hU, hS, fun PP hP => ((h PP).1 hP).1, fun PP hP => (h PP).2 hP⟩, funext fun PP => ((h PP.1).1 PP.2).2⟩

theorem finE_gAt_mem_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (g : GA D V) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hv : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) :
    Lev.finE V (gAt V (.inl v) g) ∈ Formalism.L2.DIV.St β := by
  refine (_root_.GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hfr _).2 fun w => ?_
  show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram w
    (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)) ∈ _
  by_cases e : w = v
  · subst e
    rw [GlobalTheory.AdelicU.proj_emb_self]
    exact hv
  · rw [GlobalTheory.AdelicU.proj_emb_ne _ _ e]
    exact one_mem _

theorem red_local {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (g : GA D V) (hg : Lev.finE V g ∈ Formalism.L2.DIV.St β) (PP : Pl D.host.E) :
    Formalism.L2.DIV.redFn β PP (Lev.finE V g) =
      Formalism.L2.DIV.redFn β PP (Lev.finE V (gAt V (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)) := by
  set v := (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
  set k := gAt V (.inl v) g with hkdef
  have hk : Lev.finE V k ∈ Formalism.L2.DIV.St β := finE_gAt_mem_St hfr g v ((_root_.GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hfr g).1 hg v)
  have hpk : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k = GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g := by
    show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v
      (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)) = _
    rw [GlobalTheory.AdelicU.proj_emb_self]
  have h2 : Lev.finE V (k⁻¹ * g) ∈ Formalism.L2.DIV.St β := by
    rw [map_mul, map_inv]; exact mul_mem (inv_mem hk) hg
  have h3 : Formalism.L2.DIV.redFn β PP (Lev.finE V (k⁻¹ * g)) = 1 :=
    _root_.GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP h2 (by rw [map_mul, map_inv, hpk, inv_mul_cancel])
  have e : g = k * (k⁻¹ * g) := by group
  conv_lhs => rw [e]
  rw [map_mul, Formalism.L2.DIV.redFn_mul hk h2, h3, mul_one]

end GlobalTheory.ChainTw.LevLoc

namespace GlobalTheory.ChainTw.LevLoc


open Classical in
theorem levLoc : ∀ D : D7, ForStageQ D fun c w _ s => MeasurableSet (levSet s) ∧ MeasurableSet (intOff c s) ∧ (∀ g, g ∈ levSet s ↔ g ∈ intOff c s ∧ ∀ v ∈ c.S, gAt s.V (.inl v) g ∈ Lev.levG s.V s.β s.L) ∧ (∀ g ∈ levSet s, ∃ b : GinfC s.V, ∃ κ ∈ Lev.levG s.V s.β s.L, g = (b : GA D s.V) * κ) ∧ (∀ κ ∈ Lev.levG s.V s.β s.L, ‖Lev.levChi s.V s.β s.L κ‖ = 1 ∧ ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) ∧ ∃ mR, IsLevMeas s mR := by
  intro D c w hw j _ s hs
  obtain ⟨hr, hL, hfl⟩ := hs
  have hfr : Formalism.L2.DIV.IsFrame s.β s.Λ := hfl.frame
  haveI : s.ν.IsHaarMeasure := hfl.haar
  have hsd : IsSelfDualC s.V s.Λ := hfl.selfDual
  have hP : s.L.P.H = ⊥ := by rw [hL]; rfl
  have hPl : ∀ PP, PP ∈ s.L.Pg ∨ PP ∈ s.L.Q → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ c.S := by
    intro PP hPP
    have h1 : PP ∈ c.Pg := by
      rw [hw.union, Finset.mem_union]
      rw [hL] at hPP
      exact hPP
    unfold Com.S
    exact Finset.mem_image_of_mem _ h1
  set V := s.V
  set K := Lev.levG s.V s.β s.L

  have h3 : ∀ k ∈ K, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram s.Λ v :=
    fun k hk v => (_root_.GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V s.β s.Λ hfr k).1 (GlobalTheory.ChainOnto.LevelFacts.finE_mem_St hk) v

  have h1 : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ K := by
    obtain ⟨U, hU, hUk⟩ := _root_.GlobalTheory.ChainOnto.LevelOpen.exists_open_princ D V s.β (s.L.Pg ∪ s.L.Q)
    refine ⟨U, hU, fun k hk hkf => ⟨hkf, ?_⟩⟩
    exact GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm V.gram s.β s.L _ (GlobalTheory.LevSplit.finE_mem_UA V k) (hUk k hk).1
      fun PP hPP => (hUk k hk).2 PP (Finset.mem_union.2 hPP)

  have hloc : ∀ g, g ∈ levSet s ↔ g ∈ intOff c s ∧ ∀ v ∈ c.S, gAt s.V (.inl v) g ∈ K := by
    intro g
    constructor
    · intro hg
      obtain ⟨-, hS, hl⟩ := (mem_lev_iff V.gram s.β s.L hP _).1 hg
      refine ⟨fun v _ => (_root_.GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V s.β s.Λ hfr g).1 hS v, fun v _ => ?_⟩
      have hkS := finE_gAt_mem_St hfr g v ((_root_.GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V s.β s.Λ hfr g).1 hS v)
      refine ⟨GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC V v _, ?_⟩
      refine (mem_lev_iff V.gram s.β s.L hP _).2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hkS, fun PP => ?_⟩
      by_cases e : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v
      · subst e
        rw [← red_local hfr g hS PP]
        exact hl PP
      · rw [_root_.GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V s.β _ PP hkS (GlobalTheory.AdelicU.proj_emb_ne _ _ e _)]
        exact locOK_one _ _
    · rintro ⟨hI, hK⟩
      have hS : Lev.finE V g ∈ Formalism.L2.DIV.St s.β := by
        refine (_root_.GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V s.β s.Λ hfr g).2 fun v => ?_
        by_cases hv : v ∈ c.S
        · have := h3 _ (hK v hv) v
          have e : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (gAt s.V (.inl v) g) = GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g := by
            show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v
              (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)) = _
            rw [GlobalTheory.AdelicU.proj_emb_self]
          rw [e] at this
          exact this
        · exact hI v hv
      refine (mem_lev_iff V.gram s.β s.L hP _).2 ⟨GlobalTheory.LevSplit.finE_mem_UA V g, hS, fun PP => ?_⟩
      by_cases hPP : PP ∈ s.L.Pg ∨ PP ∈ s.L.Q
      · rw [red_local hfr g hS PP]
        exact ((mem_lev_iff V.gram s.β s.L hP _).1 (hK _ (hPl PP hPP)).2).2.2 PP
      · exact ⟨fun h => absurd (Or.inl h) hPP, fun h => absurd (Or.inr h) hPP⟩
  let A : Subgroup (GA D V) := (Formalism.L2.DIV.lev D.sp.cm V.gram s.β s.L).comap (Lev.finE V)
  have hAset : (A : Set (GA D V)) = levSet s := rfl
  have hfinK : ∀ g ∈ A, (GlobalTheory.AutMult.toFin V g : GA D V) ∈ K := fun g hg =>
    ⟨(GlobalTheory.AutMult.toFin V g).2, Subgroup.mem_comap.2 (by rw [GlobalTheory.ChainOnto.HaarInf.finE_toFin]; exact Subgroup.mem_comap.1 hg)⟩
  have hAopen : IsOpen (A : Set (GA D V)) := by
    obtain ⟨U, hU, hUK⟩ := h1
    let Lf : Subgroup (GfC V) := K.subgroupOf (GfC V)
    have hLf : IsOpen (Lf : Set (GfC V)) := by
      refine Subgroup.isOpen_mono (H₁ := U.subgroupOf (GfC V)) (fun k hk => ?_) (hU.preimage continuous_subtype_val)
      exact hUK k hk k.2
    have e : (A : Set (GA D V)) = GlobalTheory.AutMult.toFin V ⁻¹' (Lf : Set (GfC V)) := by
      ext g
      refine ⟨fun hg => hfinK g hg, fun hg => ?_⟩
      have := Subgroup.mem_comap.1 hg.2
      refine Subgroup.mem_comap.2 ?_
      rw [← GlobalTheory.ChainOnto.HaarInf.finE_toFin]; exact this
    rw [e]; exact hLf.preimage (GlobalTheory.AutMult.continuous_toFin V)
  have hAint : (A : Set (GA D V)) ⊆ intOff c s := fun g hg => ((hloc g).1 hg).1
  let I : Subgroup (GA D V) :=
    { carrier := intOff c s
      mul_mem' := fun {a b} ha hb v hv => by rw [map_mul]; exact mul_mem (ha v hv) (hb v hv)
      one_mem' := fun v _ => by rw [map_one]; exact one_mem _
      inv_mem' := fun {a} ha v hv => by rw [map_inv]; exact inv_mem (ha v hv) }
  have hIopen : IsOpen (I : Set (GA D V)) := Subgroup.isOpen_mono (H₁ := A) hAint hAopen
  have hker : {g : GA D V | g ∈ A ∧ GlobalTheory.AutMult.toInf V g = 1} = (K : Set (GA D V)) := by
    ext g
    simp only [Set.mem_setOf_eq, GlobalTheory.ChainOnto.HaarInf.toInf_eq_one_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hKc : IsCompact (K : Set (GA D V)) :=
    GlobalTheory.T.isCompact_finite_adelic_subgroup_integral_open D V s.Λ hsd K inf_le_left h3 h1
  have hpi : ∀ b : GinfC V, GlobalTheory.AutMult.toInf V ((GinfC V).subtype b) = b := fun b => GlobalTheory.AutMult.toInf_coe b
  have hiA : ∀ b : GinfC V, (GinfC V).subtype b ∈ A := fun b => by
    refine Subgroup.mem_comap.2 ?_
    rw [Subgroup.subtype_apply, GlobalTheory.ChainOnto.HaarInf.finE_of_mem_ginfC V b.2]; exact one_mem _
  have hHaar : (Measure.map (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V)))).IsHaarMeasure :=
    _root_.GlobalTheory.ChainOnto.map_restrict_isHaar (GA D V) (GinfC V) s.ν A (GinfC V).subtype (GlobalTheory.AutMult.toInf V) hAopen
      continuous_subtype_val (GlobalTheory.AutMult.continuous_toInf V) hpi hiA (hker ▸ hKc)
  refine ⟨hAopen.measurableSet, hIopen.measurableSet, hloc, fun g hg => ?_, fun κ hκ =>
    ⟨GlobalTheory.ChainOnto.LevelFacts.levChi_norm s.β s.L κ, h3 κ hκ⟩, ?_⟩
  · exact ⟨GlobalTheory.AutMult.toInf V g, GlobalTheory.AutMult.toFin V g, hfinK g hg, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩
  refine ⟨_, hHaar, fun f F hf hF => ?_⟩
  have hmeas : AEMeasurable (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V))) :=
    (GlobalTheory.AutMult.continuous_toInf V).measurable.aemeasurable
  have hFA : ∀ g ∈ (A : Set (GA D V)), F g = f (GlobalTheory.AutMult.toInf V g) := fun g hg => by
    conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
    exact hF _ _ (hfinK g hg)
  have hint : IntegrableOn (fun g => f (GlobalTheory.AutMult.toInf V g)) (A : Set (GA D V)) s.ν :=
    (integrable_map_measure hf.aestronglyMeasurable hmeas).1 hf
  refine ⟨hint.congr_fun (fun g hg => (hFA g hg).symm) hAopen.measurableSet, ?_⟩
  rw [← hAset, setIntegral_congr_fun hAopen.measurableSet hFA, integral_map hmeas hf.aestronglyMeasurable]

end GlobalTheory.ChainTw.LevLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaDoubleAbsoluteSumSobolevBound
section
namespace I195MixedCoordinates_6edf13e9c2ea736a34004c3c

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_6edf13e9c2ea736a34004c3c

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

namespace GlobalTheory.Unf.DoubleSum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

section Source

variable {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ)

theorem mixS_add (hψ : IsStdChar D ψ (-1)) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (x : Mx D T.rank ρ) : (_root_.I195MixedCoordinates_6edf13e9c2ea736a34004c3c.source d) T ψ v.μ v.𝓕 (f + g) x = (_root_.I195MixedCoordinates_6edf13e9c2ea736a34004c3c.source d) T ψ v.μ v.𝓕 f x + (_root_.I195MixedCoordinates_6edf13e9c2ea736a34004c3c.source d) T ψ v.μ v.𝓕 g x := by
  funext w
  have h1 := d.integrableOn_mixS hψ.1.1 v.covol hf x w
  have h2 := d.integrableOn_mixS hψ.1.1 v.covol hg x w
  change d.mixS T ψ v.μ v.𝓕 (f + g) x w = d.mixS T ψ v.μ v.𝓕 f x w + d.mixS T ψ v.μ v.𝓕 g x w
  simp only [HypDec.mixS, HypDec.integrandS_eq, Pi.add_apply, mul_add] at h1 h2 ⊢
  exact integral_add h1 h2

theorem mixS_smul (c : ℂ) (f : WO S T → ℂ) (x : Mx D T.rank ρ) :
    (_root_.I195MixedCoordinates_6edf13e9c2ea736a34004c3c.source d) T ψ v.μ v.𝓕 (c • f) x = c • (_root_.I195MixedCoordinates_6edf13e9c2ea736a34004c3c.source d) T ψ v.μ v.𝓕 f x := by
  funext w
  change d.mixS T ψ v.μ v.𝓕 (c • f) x w = c • d.mixS T ψ v.μ v.𝓕 f x w
  simp only [HypDec.mixS, HypDec.integrandS_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]


variable (T) in
def dualPt (ρ : ℕ) : Mx D ρ T.rank →+ Mx D T.rank ρ where
  toFun b := adj (incA D D.host.xi0⁻¹ • (b * giA T))
  map_zero' := by rw [Matrix.zero_mul, smul_zero, adj_zero]
  map_add' _ _ := by rw [Matrix.add_mul, smul_add, adj_add]

theorem symplO_dualPt (x : Mx D T.rank ρ) (b : Mx D ρ T.rank) :
    symplO S T (d.extX T x) (d.extY T (dualPt T ρ b)) = Algebra.trace (AF D.host.F) (AE D) (x * b).trace := by
  have h := d.hO_ext T x 0 0 (dualPt T ρ b) 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, trace_zero] at h
  rw [symplO_eq, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero, pairS]
  congr 1
  rw [show dualPt T ρ b = adj (incA D D.host.xi0⁻¹ • (b * giA T)) from rfl, adj_adj, Matrix.smul_mul, trace_smul, smul_eq_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_mul, Matrix.mul_assoc, giA_gA_cancel, trace_mul_comm]

end Source

section Target

variable {S T T₀ : HSp D} {σ : ℕ} (d : HypDec T T₀ σ) (v : VolM D σ S.rank)

end Target

section Double

variable {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec T T₀ σ) (v : VolM D T.rank ρ)
  (v' : VolM D σ S₀.rank)


end Double

end GlobalTheory.Unf.DoubleSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorSourceRealPointCommuteHeisenbergComb
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.SeeSaw.RealComm

variable {D : D7}

theorem map_mul_gen {A B m n : Type} [CommRing A] [CommRing B] [Fintype n] (φ : A →+* B) (u : Matrix m n A) (g : Matrix n n A) :
    (u * g).map φ = u.map φ * g.map φ := Matrix.map_mul

theorem actO_real_fin (S T : HSp D) {z : GA D S} (hz : z ∈ GinfC S) {u : WO S T} (hu : u.map (infPart D) = 0) :
    actO S T z 1 u = u := by
  have h1 : Formalism.L2.Theta.mt T 1 = 1 := rfl
  have hz' : finHom S z⁻¹ = 1 := (GinfC S).inv_mem hz
  have h2 : (Formalism.L2.Theta.mt S z⁻¹).map (finPart D) = 1 := congrArg Units.val hz'
  rw [actO, h1, Matrix.one_mul]
  have h3 := map_mul_gen (finPart D) u (Formalism.L2.Theta.mt S z⁻¹)
  have h4 := map_mul_gen (infPart D) u (Formalism.L2.Theta.mt S z⁻¹)
  rw [h2, Matrix.mul_one] at h3
  rw [hu, Matrix.zero_mul, ← hu] at h4
  exact Matrix.ext fun i j => GlobalTheory.SplitScalar.adele_ext (congrFun (congrFun h4 i) j) (congrFun (congrFun h3 i) j)

theorem om_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ z ∈ GinfC S, ∀ c : WO S T →₀ ℂ, IsFinComb c → ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → om (z, 1) (comb ψ S T c g) = comb ψ S T c (om (z, 1) g) := by
  intro D ψ S T χS χT om H z hz c hc g hg
  unfold comb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [map_smul, H.om_heis z 1 u g hg, actO_real_fin S T hz (hc u hu)]

end GlobalTheory.SeeSaw.RealComm
end

