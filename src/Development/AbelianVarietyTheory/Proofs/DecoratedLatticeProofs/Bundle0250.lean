module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaCocycleProductOfRationalUnipotents
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumNonzeroCuspForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealCentreActsByCharacterOnIsotypicSlices
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0231
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankOneIsEquivalenceNonzeroGramTerms
section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One


open Formalism.L2.SG.NGCut.CorankRelation in
theorem corankOne_isEquivalence_nonzeroGram_terms : CorankOneIsEquivalenceOnRow := by
  intro D X Y u u' _hT
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : ∀ t ∈ (Y.tO u u').nzSet, Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    intro t ht h
    apply ht
    show Formalism.L2.SG.TermOp.Gt t = 0
    unfold Formalism.L2.SG.TermOp.Gt
    rw [if_pos ((Formalism.L2.SG.Pf.SatGram.gterm_G Y t).trans h)]
  have hlat : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
      Submodule.IsFullLattice D.host.E t.lam := fun t => ((Y.rowsOK u).1 t.lam t.mem).1.1
  have hLF : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
      IsLift t.lam (lf D (X.Fu u)) := fun t => ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), IsLift t.lam t.frame :=
    fun t => t.rep.2.2.2.2.1
  refine ⟨fun t ht => ?_, fun t ht t' ht' hr h1 => ?_, fun t ht t' ht' t'' ht'' hr1 hr2 h1 h2 => ?_⟩
  · show Formalism.L2.SG.TermOp.s0T t t = 1
    unfold Formalism.L2.SG.TermOp.s0T
    rw [if_pos ⟨rfl, rfl⟩, mul_inv_cancel]
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t.frame 1 (hLF t) (hLt t) (hGv t ht)).2
      (Th_one _ _ _)
  · have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
    have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
    have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := h1
    show Formalism.L2.SG.TermOp.s0T t' t = 1
    unfold Formalism.L2.SG.TermOp.s0T at h1' ⊢
    rw [if_pos ⟨hlam, hlam'⟩] at h1'
    rw [if_pos ⟨hlam.symm, hlam'.symm⟩, ← hlam]
    have hth := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
      (hGv t ht)).1 h1'
    have hL' : IsLift t.lam t'.frame := by rw [hlam]; exact hLt t'
    have hsym := Th_symm D.R.k hdim t.lam (hlat t) _ t.frame t'.frame (t'.lin * t.lin⁻¹) (hLF t) (hLt t) hL'
      (hGv t ht) (hGv t' ht') (frame_mem_iff t t') hth
    have hinv : (t'.lin * t.lin⁻¹)⁻¹ = t.lin * t'.lin⁻¹ := by group
    rw [hinv] at hsym
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t.frame _ (hLF t) hL' (hGv t' ht')).2 hsym
  · have hl1 : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr1
    have hl1' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr1
    have hl2 : t'.lam = t''.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr2
    have hl2' : t'.lam' = t''.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr2
    have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := h1
    have h2' : Formalism.L2.SG.TermOp.s0T t' t'' = 1 := h2
    show Formalism.L2.SG.TermOp.s0T t t'' = 1
    unfold Formalism.L2.SG.TermOp.s0T at h1' h2' ⊢
    rw [if_pos ⟨hl1, hl1'⟩] at h1'
    rw [if_pos ⟨hl2, hl2'⟩, ← hl1] at h2'
    rw [if_pos ⟨hl1.trans hl2, hl1'.trans hl2'⟩]
    have hL' : IsLift t.lam t'.frame := by rw [hl1]; exact hLt t'
    have hth1 := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
      (hGv t ht)).1 h1'
    have hth2 := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t''.frame _ (hLF t) hL'
      (hGv t' ht')).1 h2'
    have htr := Th_trans t.lam _ t.frame t'.frame t''.frame (t'.lin * t.lin⁻¹) (t''.lin * t'.lin⁻¹)
      (fun x hx => (frame_mem_iff t' t'' x).1 hx) hth1 hth2
    have hmul : (t''.lin * t'.lin⁻¹) * (t'.lin * t.lin⁻¹) = t''.lin * t.lin⁻¹ := by group
    rw [hmul] at htr
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t''.frame _ (hLF t) (hLt t) (hGv t ht)).2 htr

end GlobalTheory.Core.One
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankOneOfSameFlagDoubleCoset
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna
  Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One

namespace GlobalTheory.Core.OneCoset

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem frame_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (a : Fin (r + 1)) :
    frame (mapLF γ F) a = γ (frame F a) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  induction a using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast i => simp [frame, FlagG.fvec, mapFlag]

theorem Xflag_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) :
    Xflag (mapLF γ F) j = (Xflag F j).map (γ : S.V →ₗ[E] S.V) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  show Submodule.span E ((fun a => γ (F.fl.e a)) '' {i | i.1 < j}) =
    (Submodule.span E (F.fl.e '' {i | i.1 < j})).map (γ : S.V →ₗ[E] S.V)
  rw [Submodule.map_span, Set.image_image]
  rfl

theorem orth_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (x : S.V)
    (hx : x ∈ orth S (Xsp (mapLF γ F))) : γ.symm x ∈ orth S (Xsp F) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro y hy
  have hy' : γ y ∈ Xsp (mapLF γ F) := by
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF γ hγ]; simpa using hy
  have := hx (γ y) hy'
  rw [← hγ y (γ.symm x)]
  simpa using this

end Gen

theorem conj_mem_NRat {D : D7} {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (F : LFlag (D.sp.Y 0) D.R.rS T) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hn : n ∈ NRat F) : γ * n * γ⁻¹ ∈ NRat (mapLF γ F) := by
  obtain ⟨hn0, hn1, hn2⟩ := hn
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hγ hn0) ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ), ?_, ?_⟩
  · intro j x hx
    rw [Xflag_mapLF γ hγ] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨n y - y, hn1 j y hy, ?_⟩
    show γ (n y - y) = γ (n (γ.symm (γ y))) - γ y
    simp
  · intro x hx
    have h := hn2 _ (orth_mapLF γ hγ F x hx)
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF γ hγ]
    show γ.symm (γ (n (γ.symm x)) - x) ∈ Xsp F
    simpa using h

theorem corankOne_of_same_flagDoubleCoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ t t' : TauC Y u u', t.G ≠ 0 → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' →
      nmlOf Y u u' t = nmlOf Y u u' t' → (Y.tO u u').s0 t t' = 1 := by
  intro D X Y u u' t t' hG hr hn
  have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hlat : Submodule.IsFullLattice D.host.E t.lam :=
    { toIsLattice := hrow.2.1.1
      span_eq_top := GlobalTheory.LoopC.Base.span_eq_top_of_unimodular
        (VS D).hT (VS D).herm (VS D).nondeg hrow.2.1.1 hrow.2.1.2.1 }
  have hLF : IsLift t.lam (lf D (X.Fu u)) := hrow.2.1.2.2.1
  have hLt : IsLift t.lam t.frame := t.rep.2.2.2.2.1
  have hLt' : IsLift t'.lam t'.frame := t'.rep.2.2.2.2.1
  have hGv : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    rw [← Formalism.L2.SG.Pf.SatGram.gterm_G Y t]; exact hG
  have hone : ∀ {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T), (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F :=
    fun F => ⟨(Formalism.HermitianLatticesTheory.isom _).one_mem, fun j x _ => by simp, fun x _ => by simp⟩
  have hmem : t'.lin ∈ nmlOf Y u u' t := by
    rw [hn]; exact ⟨1, hone _, 1, hone _, by simp⟩
  obtain ⟨n, hn1, n', hn2, heq⟩ := hmem
  have hm : t.lin * n' * t.lin⁻¹ ∈ NRat t.frame := conj_mem_NRat t.lin t.rep.2.2.1 _ n' hn2
  have hβ : t'.lin * t.lin⁻¹ = n * (t.lin * n' * t.lin⁻¹) := by rw [heq]; group
  have hfr : ∀ a, frame t'.frame a = (n * (t.lin * n' * t.lin⁻¹)) (frame t.frame a) := by
    intro a
    unfold GTerm.frame
    rw [frame_mapLF t'.lin t'.rep.2.2.1, frame_mapLF t.lin t.rep.2.2.1, ← hβ]
    show t'.lin _ = t'.lin (t.lin.symm (t.lin _))
    simp
  have hTh := GlobalTheory.DcosetCompl.th_eq_hp D t.lam (lf D (X.Fu u)) t.frame t'.frame hlat rfl hLt.2 hLt'.2 n hn1 _ hm hfr
  rw [← hβ] at hTh
  have hs0 : Lat.s0 t.lam (lf D (X.Fu u)) t.frame t'.frame (t'.lin * t.lin⁻¹) D.R.k = 1 :=
    (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hlat _ t.frame t'.frame _ hLF hLt hGv).2 hTh
  show s0T t t' = 1
  unfold s0T
  rw [if_pos ⟨hlam, hlam'⟩]
  exact hs0

end GlobalTheory.Core.OneCoset
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftReductionToFockVectorsUniform
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CenAvg

theorem exists_central_average_uniform : ∀ (D : D7), BiAct D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A S A' : HSp D)
    (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k₀ : KerDat A S) (k₀' : KerDat S A'), k₀.Is ψ θ x y →
    k₀'.Is ψ θ y z → ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → IsBiSmooth C →
    (∃ φ₀ : GA D A → ℂ, IsContAut A φ₀ ∧ HasCen A χ φ₀ ∧ φ₀ ≠ 0) →
    ∃ (C₁ : WO A S → WO S A' → ℂ) (χ₁ : GA D A → ℂ), IsBiVac ψ A S A' x.L y.L z.L C₁ ∧ IsBiSmooth C₁ ∧
      (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k₀.om (a, 1) (fun u => C₁ u v) = χ₁ a • fun u => C₁ u v) ∧
      ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z →
        (∀ a ∈ GinfC A, ∀ b ∈ GinfC S, ∀ f, IsThetaFunO ψ A S f → k.om (a, b) f = k₀.om (a, b) f) →
        ∀ φ, IsContAut A φ → HasCen A χ φ →
          biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) =
            biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C₁) := by
  intro D hB ψ θ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ C hv hs ⟨φ₀, hφ₀, hc₀, hne⟩
  obtain ⟨χA, χS, ha⟩ := hk₀.weil
  obtain ⟨χS', χA', hb⟩ := hk₀'.weil
  obtain ⟨i1, -, i3, i4, i5, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D A
  let Z : Subgroup (GA D A) := GinfC A ⊓ Subgroup.center (GA D A)
  have hcl : IsClosed (Subgroup.center (GA D A) : Set (GA D A)) := by
    have : (Subgroup.center (GA D A) : Set (GA D A)) = ⋂ g, {a | g * a = a * g} := by
      ext a
      simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_iInter fun g => isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  haveI : CompactSpace Z := isCompact_iff_compactSpace.mp ((_root_.GlobalTheory.SeeSaw.isCompact_ginfC_of_defSp D A x hx).inter_right hcl)
  let ν : Measure Z := GlobalTheory.haarProb Z
  obtain ⟨h₀, hh₀⟩ := Function.ne_iff.1 hne
  have hh : φ₀ h₀ ≠ 0 := hh₀
  have hmul : ∀ a b : Z, χ (a * b : Z) = χ a * χ b := by
    intro a b
    apply mul_right_cancel₀ hh
    rw [← hc₀ _ (a * b).2.1 (a * b).2.2, Subgroup.coe_mul, ← mul_assoc, hc₀ _ b.2.1 b.2.2, hc₀ _ a.2.1 a.2.2]
    ring
  have hone : χ 1 = 1 := by
    apply mul_right_cancel₀ hh
    rw [← hc₀ _ (one_mem _) (one_mem _), mul_one, one_mul]
  have hcont : Continuous fun a : Z => χ a := by
    have : (fun a : Z => χ a) = fun a : Z => φ₀ (h₀ * a) / φ₀ h₀ := by
      funext a
      rw [hc₀ _ a.2.1 a.2.2, mul_div_cancel_right₀ _ hh]
    rw [this]
    exact (hφ₀.2.comp (continuous_const.mul continuous_subtype_val)).div_const _
  have hj : ∀ a : Z, (a : GA D A) ∈ GinfC A := fun a => a.2.1
  have hC := GlobalTheory.FrComb.biTheta_of_vac hx.sd hy.sd hz.sd hv hs
  refine ⟨avg k₀.om ν Subtype.val (fun a => χ a) C, fun a => χ a⁻¹,
    isBiVac_avg ν ha hb hB continuous_subtype_val hj hcont hC hv,
    (isBiTheta_avg ν ha hb hB continuous_subtype_val hj hcont hC).smooth, fun a ha1 ha2 v => ?_, ?_⟩
  · funext u
    rw [om_avg ν ha hb hB continuous_subtype_val hj hcont hC]
    let a' : Z := ⟨a, ha1, ha2⟩
    simp only [Pi.smul_apply, smul_eq_mul, avg]
    rw [← integral_const_mul, ← integral_mul_left_eq_self (μ := ν)
      (fun b : Z => χ a⁻¹ * (χ b * k₀.om (b, 1) (fun u' => C u' v) u)) a']
    congr 1
    funext b
    have e : χ a⁻¹ * χ a = 1 := by
      have := hmul a'⁻¹ a'
      rw [inv_mul_cancel] at this
      exact this.symm.trans hone
    rw [hmul, ← mul_assoc, ← mul_assoc]
    change _ = χ a⁻¹ * χ a * χ b * k₀.om (a * b, 1) (fun u' => C u' v) u
    rw [e, one_mul]
  intro k k' hk hk' hag φ hφ hcφ
  obtain ⟨χA₁, χS₁, ha₁⟩ := hk.weil
  obtain ⟨χS₁', χA₁', hb₁⟩ := hk'.weil
  have eavg : avg k₀.om ν Subtype.val (fun a => χ a) C = avg k.om ν Subtype.val (fun a => χ a) C := by
    funext u v
    simp only [avg]
    congr 1
    funext a
    rw [hag a a.2.1 1 (GinfC S).one_mem _ (hv.left v).1]
  rw [eavg]
  have hG := GlobalTheory.FrComb.biTheta_combL ha₁.std (GlobalTheory.FrComb.biTheta_combR ha₁.std hC hk'.fin) hk.fin
  rw [biComb_avg ν ha₁ hb₁ hB continuous_subtype_val hj hcont hC hk.fin hk'.fin]
  change IsBiTheta ψ A S A' (biComb ψ A S A' k.c k'.c C) at hG
  generalize biComb ψ A S A' k.c k'.c C = G at hG
  funext h₂
  unfold biLift
  congr 1
  funext h₁
  have hF : IsContAut A fun h => φ h * k'.om (h₁, h₂) (fun v => k.om (h, h₁) (fun u => G u v) 0) 0 := by
    refine ⟨fun γ hγ g => ?_, hφ.2.mul ?_⟩
    · have : ∀ v, k.om (γ * g, h₁) (fun u => G u v) 0 = k.om (g, h₁) (fun u => G u v) 0 := fun v => by
        rw [← ha₁.om_aut γ hγ 1 (one_mem _) _ (ha₁.om_pres (g, h₁) _ (GlobalTheory.FrComb.slice_left hG v)), ← Module.End.mul_apply,
          ← map_mul, Prod.mk_mul_mk, one_mul]
      simp only [this, hφ.1 γ hγ g]
    · exact (hB ψ A S A' _ _ _ _ _ _ ha₁ hb₁ G hG).2.2.2.comp
        (show Continuous fun h : GA D A => ((h, h₁), (h₁, h₂), (0 : WO A S), (0 : WO S A')) from
          (continuous_id.prodMk continuous_const).prodMk continuous_const)
  rw [← integral_mean ν hx.cpt x.vol continuous_subtype_val hF]
  congr 1
  funext h
  rw [ker_avg ν ha₁ hb₁ hB continuous_subtype_val hj hcont hG, ← integral_const_mul]
  congr 1
  funext a
  rw [hcφ _ a.2.1 a.2.2]
  ring

end GlobalTheory.CenAvg

namespace GlobalTheory.SeeSaw

theorem fockRed_uniform : ∀ D : D7, BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k₀ : KerDat A S) (k₀' : KerDat S A'), k₀.Is ψ θ x y → k₀'.Is ψ θ y z → ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → IsBiSmooth C → ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank), ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → k.vac = k₀.vac → k'.vac = k₀'.vac → (∀ a ∈ GinfC A, ∀ b ∈ GinfC S, ∀ f, IsThetaFunO ψ A S f → k.om (a, b) f = k₀.om (a, b) f) → (∀ a ∈ GinfC S, ∀ b ∈ GinfC A', ∀ f, IsThetaFunO ψ S A' f → k'.om (a, b) f = k₀'.om (a, b) f) → ∀ φ, IsContAut A φ → HasCen A χ φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) = ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ) := by
  intro D hBi hCF hLS ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ C hC hsm
  by_cases h0 : ∃ φ₀ : GA D A → ℂ, IsContAut A φ₀ ∧ HasCen A χ φ₀ ∧ φ₀ ≠ 0
  · obtain ⟨C₁, χ₁, hC₁, hs₁, he₁, heq₁⟩ :=
      GlobalTheory.CenAvg.exists_central_average_uniform D hBi ψ θ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ C hC hsm h0
    obtain ⟨χ₃, h₃⟩ := _root_.GlobalTheory.CentreTarget.centre_target_char D hBi hCF hLS ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ₁ C₁ hC₁ he₁
    obtain ⟨C₂, χ₂, hC₂, he₂, hf₂, heq₂⟩ :=
      _root_.GlobalTheory.AvgMidUnif.exists_isotypic_uniform D hBi hCF hLS ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ₁ χ₃ C₁ hC₁ hs₁ he₁ h₃
    obtain ⟨n, P, P', hp⟩ := _root_.GlobalTheory.SeeSaw.FinRank.biVac_sum_fock D hCF ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ₁ χ₂ C₂ hC₂ he₂ hf₂
    refine ⟨n, P, P', fun k k' hk hk' hv hv' hag hag' φ hφ hcen => ?_⟩
    rw [heq₁ k k' hk hk' hag φ hφ hcen, heq₂ k k' hk hk' hag hag' φ hφ,
      _root_.GlobalTheory.SeeSaw.biLift_biComb_fockSum D hBi hCF hLS ψ θ hθ A S A' x y z hx hy hz k k' hk hk' n P P' C₂ (by rw [hv, hv']; exact hp) φ hφ]
  · refine ⟨0, Fin.elim0, Fin.elim0, fun k k' _ _ _ _ _ _ φ hφ hcen => ?_⟩
    have e : φ = 0 := by
      by_contra hne
      exact h0 ⟨φ, hφ, hcen, hne⟩
    subst e
    funext h₂
    simp [biLift]

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCompactSubgroupConjHermitianSpace
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.LatMove

theorem stab_conj_iff {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (M M' : Set (ι → R)) (B X : GL ι R)
    (hB : ∀ Y, Y ∈ M ↔ B.1 *ᵥ Y ∈ M') :
    (∀ Y, Y ∈ M' ↔ X.1 *ᵥ Y ∈ M') ↔ (∀ Y, Y ∈ M ↔ (B⁻¹ * X * B).1 *ᵥ Y ∈ M) := by
  have key : ∀ Y, B.1 *ᵥ ((B⁻¹ * X * B).1 *ᵥ Y) = X.1 *ᵥ (B.1 *ᵥ Y) := fun Y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      show B * (B⁻¹ * X * B) = X * B by group]
  constructor
  · intro h Y
    rw [hB Y, hB, key]
    exact h _
  · intro h Y
    have hY : B.1 *ᵥ ((B⁻¹).1 *ᵥ Y) = Y := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have := h ((B⁻¹).1 *ᵥ Y)
    rw [hB, hB, key, hY] at this
    exact this

theorem map_conj_of_eq_one {G H : Type} [Group G] [Group H] (f : G →* H) {g : G} (hg : f g = 1) (x : G) :
    f (g⁻¹ * x * g) = f x := by
  rw [map_mul, map_mul, map_inv, hg, inv_one, one_mul, mul_one]

theorem map_conj' {G H : Type} [Group G] [Group H] (f : G →* H) (g x : G) :
    f (g⁻¹ * x * g) = (f g)⁻¹ * f x * f g := by
  rw [map_mul, map_mul, map_inv]

section General

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

theorem mem_KFin_conj (h : Q = dblGram finSumFinEquiv J) {L L' : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} (g : GLoc σ J v)
    (hg : ∀ z, z ∈ latLoc F L v ↔ (GlobalTheory.AdelicU.matHom _ σ J g).val *ᵥ z ∈ latLoc F L' v) (x : GLoc σ Q v) :
    x ∈ GlobalTheory.Doubling.KFin σ Q L' v ↔ (ioH _ σ h (g, g))⁻¹ * x * ioH _ σ h (g, g) ∈ GlobalTheory.Doubling.KFin σ Q L v := by
  refine mem_stabLoc.trans (Iff.trans ?_ mem_stabLoc.symm)
  rw [map_conj', matHom_ioH, latLoc_sumLat, latLoc_sumLat]
  refine stab_conj_iff (SetLike.coe (sumLat finSumFinEquiv (latLoc F L v) (latLoc F L v)))
    (SetLike.coe (sumLat finSumFinEquiv (latLoc F L' v) (latLoc F L' v))) _ _ fun Y => ?_
  rw [← pairVec_eta finSumFinEquiv Y, val_blkGL, blkMat_mulVec, SetLike.mem_coe, SetLike.mem_coe,
    pairVec_mem_sumLat, pairVec_mem_sumLat]
  exact and_congr (hg _) (hg _)

theorem mem_KAd_conj (h : Q = dblGram finSumFinEquiv J) {L L' : Submodule (𝓞 E) (Fin n → E)} (k : GAd σ J)
    (hk : k ∈ finPts σ J)
    (hL : ∀ (v : HeightOneSpectrum (𝓞 F)) z,
      z ∈ latLoc F L v ↔ (GlobalTheory.AdelicU.matHom _ σ J (proj σ J v k)).val *ᵥ z ∈ latLoc F L' v)
    (a : GL (Fin n) (AF F ⊗[F] E)) (x : GAd σ Q) :
    x ∈ KAd σ Q L' a ↔ (ioH _ σ h (k, k))⁻¹ * x * ioH _ σ h (k, k) ∈ KAd σ Q L a := by
  refine mem_KAd.trans (Iff.trans (and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)) mem_KAd.symm)
  · rw [map_conj', proj_ioH]
    exact mem_KFin_conj h _ (hL v) _
  · rw [map_conj_of_eq_one _ (by rw [projArch_ioH, mem_finPts_iff_forall.1 hk w, ioH_one])]

end General

theorem mem_KAd_io_conj : ∀ (D : D7) (A : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (k : GA D A), k ∈ GfC A →
    (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (z : Fin A.rank → TensorProduct D.host.F (Fv D.host.F v) D.host.E),
      z ∈ latLoc D.host.F L v ↔
        (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig A.gram (proj D.sp.cm.sig A.gram v k)).val *ᵥ z ∈ latLoc D.host.F L' v) →
    ∀ (a : GL (Fin A.rank) (AE D)) (x : GA D (dblSp A)), x ∈ KAd D.sp.cm.sig (dblSp A).gram L' a ↔
      (io A (k, k))⁻¹ * x * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a :=
  fun D A _ _ k hk hL a x => mem_KAd_conj (σ := D.sp.cm.sig) (gram_hdbl A) k hk hL a x

end GlobalTheory.LatMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdelePrescribedResiduesAndConjStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralAdele_prescribed_residues_and_conj : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP') → ∀ u u' : ∀ PP : Pl D.host.E, kP PP, ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP ∈ Pg, resS D.host.F PP s = u PP ∧ resS D.host.F PP (sigInt (instOf D) s) = u' PP := by
  first | exact @GlobalTheory.ConjResidueSurj.exists_res_and_conj | exact GlobalTheory.ConjResidueSurj.exists_res_and_conj | (intros; apply GlobalTheory.ConjResidueSurj.exists_res_and_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteElementsActFockVectorsThroughDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockFin

theorem pt_finite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T) (k : KerDat S T), x.Is → y.Is → k.Is ψ θ x y → ∀ P, IsThetaFunO ψ S T (k.pt ψ θ x y P) ∧ ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ p : ℂ, k.om (g, h) (comb ψ S T k.c k.vac) = p • comb ψ S T k.c k.vac → k.om (g, h) (k.pt ψ θ x y P) = p • k.pt ψ θ x y P := by
  intro D ψ θ hθ S T x y k _ _ hk P
  obtain ⟨χS, χT, hW⟩ := hk.weil
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hvac : IsThetaFunO ψ S T k.vac := hk.vac.2.theta
  have hc : IsThetaFunO ψ S T (comb ψ S T k.c k.vac) :=
    Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
      fun u hu => GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hvac (hk.fin u hu))
  have hop : ∀ g ∈ GfC S, ∀ h ∈ GfC T,
      IsThetaFunO ψ S T (k.pt ψ θ x y P) ∧
        k.om (g, h) (k.pt ψ θ x y P) = pureTensorO ψ θ S T x.s y.s x.B y.B (k.om (g, h) (comb ψ S T k.c k.vac)) P :=
    fun g hg h hh => GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT k.om hW hθ x.s x.s x.B x.B y.s y.s y.B y.B g h
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.one_mul]) _ hc P
  refine ⟨(hop 1 (one_mem _) 1 (one_mem _)).1, fun g hg h hh p hp => ?_⟩
  rw [(hop g hg h hh).2, hp, GlobalTheory.FiniteFock.pureTensorO_smul]
  rfl

end GlobalTheory.FockFin
end
end

