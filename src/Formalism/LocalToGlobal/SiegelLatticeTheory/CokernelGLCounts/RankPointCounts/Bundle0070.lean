module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0067
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RgFwdSup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SharpDualSpans.GlueConvPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0066
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0064

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlobalCountOfModule
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG8

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem rgHyp_of (M : Model F E) (hM : M.OK) {r n : ℕ} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    (hn : Module.finrank E V = n) (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂') (hyp : LocalCountHypotheses H t₁ f₂ f₂' φ φ')
    (Λ₂ : Submodule M.L.O V) (hg : H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩)
    (hth : ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ')
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩)
    (hθ : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H _ m₂ ↔ GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂) :
    ∃ ψ, RGHyp H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ ψ θ φ φ' := by
  have hT₁ := hyp.1.1
  have hT₂ := hg.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hT₁.2.1.2.1, hT₁.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hT₁.2.2.1.2.1, hT₁.2.2.1.2.2.1⟩
  have hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)) := hT₂.2.2.2.1
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT₁.2.2.2.1
  obtain ⟨ψ, -, hψc⟩ := corrIso_holds M r n V H hn t₁ f₂ f₂' φ φ' hyp hD₂
  have hU₁ : IsCompl (Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (H.W0 t₁.f t₁.f') :=
    isCompl_span_frames_W0 H t₁.f t₁.f' t₁.T t₁.T' hF₁ hF₁' hD₁ (isUnit_Gdet H _ _ _ _ hT₁.2.2.2.2.1)
  have hU₂ : IsCompl (Submodule.span E (Set.range (Sum.elim f₂ f₂'))) (H.W0 f₂ f₂') :=
    isCompl_span_frames_W0 H f₂ f₂' t₁.T t₁.T' hyp.2.1 hyp.2.2.1 hD₂ (isUnit_Gdet H _ _ _ _ hT₂.2.2.2.2.1)
  have hZ₁ : IsUnit (H.Zhat t₁.f t₁.f').det := by rw [← Dl_succ]; exact hD₁
  have hZ₁' : IsUnit (H.Zhat t₁.f' t₁.f).det := det_Zhat_swap_unit H _ _ hZ₁
  have hzφ : φ (H.mkW t₁.f ⟨t₁.f (Fin.last r), z_mem_perpX H hF₁⟩) =
      H.mkW f₂ ⟨f₂ (Fin.last r), z_mem_perpX H hyp.2.1⟩ := by
    have e := hyp.2.2.2.2.1 ⟨_, z_mem_perpX H hF₁⟩ ⟨_, z_mem_perpX H hyp.2.1⟩ rfl rfl
    simpa using e
  have hzφ' : φ' (H.mkW t₁.f' ⟨t₁.f' (Fin.last r), z_mem_perpX H hF₁'⟩) =
      H.mkW f₂' ⟨f₂' (Fin.last r), z_mem_perpX H hyp.2.2.1⟩ := by
    have e := hyp.2.2.2.2.2 ⟨_, z_mem_perpX H hF₁'⟩ ⟨_, z_mem_perpX H hyp.2.2.1⟩ rfl rfl
    simpa using e
  obtain ⟨u, hu⟩ := hD₂
  have hoφ : φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩) =
      ((↑u⁻¹ : E) * H.Dl t₁.f t₁.f' (r + 1)) • H.mkW f₂ ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩ := by
    have e : H.Dl f₂ f₂' (r + 1) • φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩) =
        H.Dl t₁.f t₁.f' (r + 1) • H.mkW f₂ ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩ :=
      hyp.2.2.2.1.2.2.2.1 _ _ rfl rfl
    rw [← hu] at e
    calc φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩)
        = (↑u⁻¹ : E) • ((u : E) • φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e, smul_smul]
  obtain ⟨u', hu'⟩ : IsUnit (M.L.cj (H.Dl f₂ f₂' (r + 1))) := by rw [← hu]; exact (Units.isUnit u).map _
  have hoφ' : φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩) =
      ((↑u'⁻¹ : E) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1))) • H.mkW f₂' ⟨H.om' f₂' f₂, om'_mem_perpX H _ _⟩ := by
    have e : M.L.cj (H.Dl f₂ f₂' (r + 1)) • φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩) =
        M.L.cj (H.Dl t₁.f t₁.f' (r + 1)) • H.mkW f₂' ⟨H.om' f₂' f₂, om'_mem_perpX H _ _⟩ :=
      hyp.2.2.2.1.2.2.2.2.1 _ _ (om'_swap H _ _) (om'_swap H _ _)
    rw [← hu'] at e
    calc φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩)
        = (↑u'⁻¹ : E) • ((u' : E) • φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e, smul_smul]
  have hC2'' := cond_second_of_iso H t₁.f' t₁.f f₂' f₂ t₁.T' t₁.T' hF₁' hyp.2.2.1 hZ₁' φ' _ hzφ' hoφ'
  refine ⟨ψ, {
    hU₂ := hU₂
    hU₁ := hU₁
    hsd₁ := hT₁.1
    hsd₂ := hT₂.1
    hMM₁ := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hyp.1.2.1 i)
    hMM₂ := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hg.2.1 i)
    hth := fun w => hth w (ψ w) ((hψc _ _).2 ⟨w.2, rfl⟩)
    hθ := ?_
    hsurj₁ := surj_MMsharp M hM H t₁ hyp.1 hU₁
    hC1 := fun w => by
      obtain ⟨_, _, c₁, _⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
      exact c₁
    hC1' := fun w => by
      obtain ⟨_, _, _, c₂⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
      exact c₂
    hC2 := cond_second_of_iso H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T hF₁ hyp.2.1 hZ₁ φ _ hzφ hoφ
    hC2' := fun v hv hvp => by
      rw [← U_swap] at hv
      obtain ⟨v', hv', hv'p, e⟩ := hC2'' v hv hvp
      rw [U_swap] at hv'
      exact ⟨v', hv', hv'p, e⟩ }⟩
  intro m₁ m₂
  rw [hθ m₁ m₂]
  constructor
  · rintro ⟨n₁, n₂, hc, h1, h2⟩
    obtain ⟨hn₁, hψn⟩ := (hψc _ _).1 hc
    exact ⟨⟨n₁, hn₁⟩, h1, by rw [hψn]; exact h2⟩
  · rintro ⟨w, h1, h2⟩
    exact ⟨w, ψ w, (hψc _ _).2 ⟨w.2, rfl⟩, h1, h2⟩

theorem claimRG_at (M : Model F E) (r n : ℕ) (hM : M.OK) : ClaimRG M r n := by
  intro hsome V _ _ H hn t₁ f₂ f₂' φ φ' hyp Λ₂ hg hth θ hθ
  obtain ⟨g, hs⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨ψ, D⟩ := rgHyp_of M hM H hn t₁ f₂ f₂' φ φ' hyp Λ₂ hg hth θ hθ
  have core1 := fun hI => Set.Subset.antisymm (rg_fwd_sub H g D hI) (rg_fwd_sup H g D hI)
  have core2 := fun hG => Set.Subset.antisymm (rg_bwd_sub H g D hG) (rg_bwd_sup H g D hG)
  have hL1 := Lset_eq_snd H hM g hs t₁ hyp.1 D.hU₁
  have hL1' := Lset_eq_fst H hM g hs t₁ hyp.1 D.hU₁
  have hL2 := Lset_eq_snd H hM g hs (⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) hg D.hU₂
  have hL2' := Lset_eq_fst H hM g hs (⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) hg D.hU₂
  constructor
  · intro hR
    refine ⟨fun h => absurd (hs.symm.trans h) (by simp), fun g' hg' => ?_⟩
    rw [Option.some.inj (hg'.symm.trans hs)]
    exact core1 (hR.2.2.2.2 g hs)
  · rintro ⟨-, hGR⟩
    have hI := core2 (hGR g hs)
    have e : φ '' (Prod.snd '' H.iotaGraph g t₁) = Prod.snd '' (Prod.map φ' φ '' H.iotaGraph g t₁) := by
      rw [Set.image_image, Set.image_image]
      rfl
    have e' : φ' '' (Prod.fst '' H.iotaGraph g t₁) = Prod.fst '' (Prod.map φ' φ '' H.iotaGraph g t₁) := by
      rw [Set.image_image, Set.image_image]
      rfl
    refine ⟨(congrArg (φ '' ·) hL1).trans (e.trans ((congrArg (Prod.snd '' ·) hI).trans hL2.symm)),
      hyp.2.2.2.2.1,
      (congrArg (φ' '' ·) hL1').trans (e'.trans ((congrArg (Prod.fst '' ·) hI).trans hL2'.symm)),
      hyp.2.2.2.2.2, fun g' hg' => ?_⟩
    rw [Option.some.inj (hg'.symm.trans hs)]
    exact hI

theorem claimR_at (M : Model F E) (r n : ℕ) (hM : M.OK) : ClaimR M r n :=
  claimR_of_modes M r n (claimRL_at M r n hM) (claimRG_at M r n hM)

theorem localCount_of_module (M : Model F E) (r n : ℕ) (hM : M.OK) (h0 : ModSide0 M r n M.split.isSome)
    (hU : ModSideU M r n M.split.isSome) : Formalism.MainNotions.ThinScalesBound.FamilyLocalModel M r n :=
  localCount_of_glue M r n hM (PI.LocCntLat.GE.glueEta_holds M r) (PI.LocCntLat.GC.glueConv_holds M r)
    (genOfPrim_holds M r n) (claimR_at M r n hM) h0 hU

theorem globalCount_of_module (D : Formalism.BasicNotions.D7)
    (h0 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ModSide0 M D.R.rS D.R.r M.split.isSome))
    (hU : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ModSideU M D.R.rS D.R.r M.split.isSome)) : Formalism.MainNotions.ThinScalesBound.T2 D := by
  intro F _ _ _ E _ _ _ _ M hM
  exact localCount_of_module M D.R.rS D.R.r hM (h0 F E M hM) (hU F E M hM)

end RG8

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqAna
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps

namespace Formalism.L2.SG.Pf.MainEqAna

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def AnaAtG (CSt CB : ℝ) (C1 C0n A : ℕ) {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    {P : Type} [Fintype P] (B : S3.MassData P) (Ire : ℝ) : Prop :=
  ∃ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (cSt e1 : ℝ),
    Formalism.L2.SG.RealObj.NuQOK X u u νL ∧ Formalism.L2.SG.RealObj.NuQOK X u u νB ∧
    0 ≤ cSt ∧ cSt ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) ∧ 0 ≤ e1 ∧ e1 ≤ 2 ∧
    AmpVanishG Y u νL ∧
    LocalInputG (genT (Y.tO u u)) (NOfG Y u νL νB ng) C1 C0n ∧
    PN.GenMassInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA) e1 ∧
    PN.MeasureInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) cSt ∧
    PN.PointSumInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) (A * (D.R.rS + 1) ^ 2)
      (Real.exp (CB * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * D.R.f * Real.log large₂.sc.b) * Ire)

def StepAnalyticCG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∀ A : ℕ, ∃ CB CSt : ℝ, 0 ≤ CB ∧ 0 ≤ CSt ∧
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
        AnaAtG CSt CB C1 C0n A large₂ Y u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Ire

section Pin

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

private theorem Jw_sc_eq_smul {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) (s : X.B.I.Ginf → NNReal)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (w : Point D.host.E (D.R.rS + 1)) :
    Jw Y u u (sc s ν) w = ((s (RealObj.gamW X u u w) : NNReal) : ℝ) • Jw Y u u ν w := by
  simp only [Jw, OO, sc, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal]
  rw [smul_comm]

theorem ampVanishG_sc (s : X.B.I.Ginf → NNReal) (hs : ∀ γ, 0 < s γ) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (h : AmpVanishG Y u ν) : AmpVanishG Y u (sc s ν) := by
  intro c γ ν' hJ
  refine h c γ ν' ?_
  unfold J2of at hJ ⊢
  split_ifs at hJ ⊢ with hc
  · rw [Jw_sc_eq_smul, LinearMap.map_smul_of_tower, norm_smul, mul_pow] at hJ
    rcases mul_eq_zero.mp hJ with h1 | h1
    · exfalso
      have hp : (0 : ℝ) < ((s (RealObj.gamW X u u hc.choose) : NNReal) : ℝ) := hs _
      have : (0 : ℝ) < ‖((s (RealObj.gamW X u u hc.choose) : NNReal) : ℝ)‖ ^ 2 :=
        pow_pos (norm_pos_iff.mpr hp.ne') 2
      linarith
    · exact h1
  · rfl

theorem measureInputG_sc (s : X.B.I.Ginf → NNReal) (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (c : ℝ)
    (hs : ∀ γ, (s γ : ℝ) ^ 2 ≤ c) (ng : PN.Pts D.host.E D.R.rS → ℝ) :
    PN.MeasureInput (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν ng) c := by
  intro γ _
  simp only [NOfG]
  unfold J2of
  split_ifs with hc
  · rw [Jw_sc_eq_smul, LinearMap.map_smul_of_tower, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact ⟨by positivity, mul_le_mul_of_nonneg_right (hs _) (by positivity)⟩
  · simp

theorem ampVanishG_of_term (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (h : ∀ t ∈ (Y.tO u u).genSet, J2of Y u u ν (ptPN t) = 0 → (Y.tO u u).vec t = 0) : AmpVanishG Y u ν := by
  intro c γ ν' hJ
  unfold grpGC
  refine (tsum_congr fun t => ?_).trans tsum_zero
  by_cases ht : t ∈ (Y.tO u u).genSet ∩ {t | clsG Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν'}
  · rw [Set.indicator_of_mem ht]
    exact h t ht.1 (by rw [ht.2.2.1]; exact hJ)
  · simp [Set.indicator, ht]

end Pin

def StepTermVanishG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ ν, Pinned X u u ν → ∀ t ∈ (Y.tO u u).genSet, J2of Y u u ν (ptPN t) = 0 → (Y.tO u u).vec t = 0

def StepLocGenPinnedG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 C0n : ℕ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u ν →
      ∃ (s : X.B.I.Ginf → NNReal) (ng : PN.Pts D.host.E D.R.rS → ℝ) (e1 : ℝ),
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧ 0 ≤ e1 ∧ e1 ≤ 2 ∧
        LocalInputG (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν ng) C1 C0n ∧
        PN.GenMassInput (genT (Y.tO u u)) (NOfG Y u (sc s ν) ν ng)
          (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u X0 ψ sd C Th vR Q i0 i0' νq).AA) e1

end Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqAna

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNormOne
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.BesselShellMomentBounds Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.L2.SG.RowsConc
  Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps

namespace Formalism.L2.SG.NGCut.LeadingMinorIntegrality.Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGCut in
theorem stepNormOneG_of
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hAt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    StepNormOneG := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u _ νL νB ng γ hγ => ?_⟩
  obtain ⟨c, ν, t, ht, hv, -, hpt, -⟩ := hγ
  have hG : t.toTerm.G ≠ 0 := by
    intro h
    apply ht.1
    show Gt t = 0
    have h' : t.G = 0 := h
    simp [Gt, h']
  have hrel : t.toTerm.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := hOV D X Y u u t hr
    show vec (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨w, hw⟩ := hAt D X Y u u t.toTerm hG hrel
  have hat := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hw, hrel⟩
  obtain ⟨F', ⟨hP, -⟩, hGv, hcell⟩ := hat
  have hrow := (Y.rowsOK u).1 t.toTerm.lam t.toTerm.mem
  have hun := hrow.2.1.2.1
  have hz := hrow.2.1.2.2.1.1
  have hX := hrow.2.2
  have hz' := hP.1.1
  have hX' := hP.2.2.2
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ t.toTerm.lam := PtPf.frame_mem _ hz hX
  have hF' : ∀ b, frame F' b ∈ t.toTerm.lam := PtPf.frame_mem _ hz' hX'
  rw [← hpt]
  show 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) ∧
    1 ≤ NDPt D.host.rdE (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm))
  have hlead : ∀ q, q ≤ D.R.rS + 1 → ∃ o ∈ dI D ^ (q * (2 * D.R.rS + 1 - q)),
      (o : D.host.E) = leadingPrincipalMinor (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) q := fun q hq => by
    obtain ⟨o, ho, e⟩ := lead_mem hun (lf D (X.Fu u)) F' hz hX hz' hX' q hq
    exact ⟨o, ho, e.trans (lead_cell _ _ hcell q).symm⟩
  constructor
  · have hGeq := gpt_eq (T := Tu D u) (T' := Tu D u) (lf D (X.Fu u)) F' _ hcell
    obtain ⟨o1, ho1, e1⟩ := hlead (D.R.rS + 1) le_rfl
    obtain ⟨o0, ho0, e0⟩ := hlead D.R.rS (Nat.le_succ _)
    obtain ⟨o1', ho1', e1'⟩ := star_mem_pow _ o1 ho1
    obtain ⟨o0', ho0', e0'⟩ := star_mem_pow _ o0 ho0
    have ex1 : (D.R.rS + 1) * (2 * D.R.rS + 1 - (D.R.rS + 1)) + (D.R.rS + 1) * (2 * D.R.rS + 1 - (D.R.rS + 1)) =
        2 * D.R.rS * (D.R.rS + 1) := by
      rw [show 2 * D.R.rS + 1 - (D.R.rS + 1) = D.R.rS by omega]; ring
    have ex0 : D.R.rS * (2 * D.R.rS + 1 - D.R.rS) + D.R.rS * (2 * D.R.rS + 1 - D.R.rS) =
        2 * D.R.rS * (D.R.rS + 1) := by
      rw [show 2 * D.R.rS + 1 - D.R.rS = D.R.rS + 1 by omega]; ring
    have hm1 : o1 * o1' ∈ dI D ^ (2 * D.R.rS * (D.R.rS + 1)) := by
      rw [← ex1, pow_add]; exact Ideal.mul_mem_mul ho1 ho1'
    have hm0 : o0 * o0' ∈ dI D ^ (2 * D.R.rS * (D.R.rS + 1)) := by
      rw [← ex0, pow_add]; exact Ideal.mul_mem_mul ho0 ho0'
    refine one_le_NGPt _ _ (o1 * o1' - (((Tu D u : ℕ) * (Tu D u : ℕ) : ℕ) : 𝓞 D.host.E) * (o0 * o0'))
      (Ideal.sub_mem _ hm1 (Ideal.mul_mem_left _ _ hm0)) ?_ (by rw [hGeq]; exact hGv)
    have e1a : algebraMap (𝓞 D.host.E) D.host.E o1 = leadingPrincipalMinor (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) (D.R.rS + 1) := e1
    have e0a : algebraMap (𝓞 D.host.E) D.host.E o0 = leadingPrincipalMinor (ptMat (Formalism.L2.SG.PairVal.ptOf t.toTerm)) D.R.rS := e0
    have e1b : algebraMap (𝓞 D.host.E) D.host.E o1' = star (algebraMap (𝓞 D.host.E) D.host.E o1) := e1'
    have e0b : algebraMap (𝓞 D.host.E) D.host.E o0' = star (algebraMap (𝓞 D.host.E) D.host.E o0) := e0'
    show algebraMap (𝓞 D.host.E) D.host.E _ = _
    unfold GPt
    rw [dlast_eq, dr_eq, map_sub, map_mul, map_mul, map_mul, map_natCast, e1b, e0b, e1a, e0a]
  · refine one_le_NDPt _ fun a => ?_
    have hj : endIdx (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) a ≤ D.R.rS + 1 :=
      (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)).1.sizeUpTo_le _
    obtain ⟨o, ho, e⟩ := hlead _ hj
    have hE := PtPf.blockEndMinors_of_cell _ (PtPf.zhatOM_isIntegral _ _ hun hF hF') _ hcell
    exact ⟨o, ho, by rw [e, endMin_eq], (hE a).2⟩


open Formalism.L2.SG.TermOp.Vanish in
theorem stepNormOneG_of_leaves (hA : AvgCore) (hU : GinfUnimod) (hN : NLamNinf) (hC : ChiTrivialC) (hG : PsiInfChar)
    (h1 : RClosedC) (h2 : RODiscreteC) (h3 : RCocompactC) (h4 : NonRelCharC)
    (hAt : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
      (t : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u)), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    Formalism.L2.SG.Pf.MainEqSteps.StepNormOneG := by
  refine stepNormOneG_of ?_ hAt
  intro D X Y u u'
  unfold Formalism.L2.SG.TermOp.KExpCut.OOVanish
  intro t ht
  exact ooVanish_of hA hU hN hC hG h1 h2 h3 h4 Y t ht

end Formalism.L2.SG.NGCut.LeadingMinorIntegrality.Gen
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MulVecInj
section
noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

section Lift

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  (M : Formalism.MainNotions.S.Loc.Model F E) {m : ℕ}

def mu (Z : M.Mat (m + 1)) (v : Fin (m + 1) → M.R) : E :=
  ((Z.Z.map M.R.subtype)⁻¹.mulVec fun i => (v i : E)) (Fin.last m)

theorem mu_add (Z : M.Mat (m + 1)) (v w : Fin (m + 1) → M.R) : mu M Z (v + w) = mu M Z v + mu M Z w := by
  unfold mu
  have e : (fun i => ((v + w) i : E)) = (fun i => (v i : E)) + fun i => (w i : E) := by
    funext i
    simp
  rw [e, Matrix.mulVec_add]
  rfl

theorem mu_smul (Z : M.Mat (m + 1)) (a : M.R) (v : Fin (m + 1) → M.R) : mu M Z (a • v) = (a : E) * mu M Z v := by
  unfold mu
  have e : (fun i => ((a • v) i : E)) = (a : E) • fun i => (v i : E) := by
    funext i
    simp
  rw [e, Matrix.mulVec_smul]
  rfl

theorem mu_sum (Z : M.Mat (m + 1)) {ι : Type} (s : Finset ι) (f : ι → Fin (m + 1) → M.R) :
    mu M Z (∑ i ∈ s, f i) = ∑ i ∈ s, mu M Z (f i) := by
  exact map_sum (AddMonoidHom.mk' (mu M Z) (mu_add M Z)) f s

theorem coe_mulVec (Z : M.Mat (m + 1)) (x : Fin (m + 1) → M.R) :
    (fun i => ((Z.Z.mulVec x) i : E)) = (Z.Z.map M.R.subtype).mulVec fun j => (x j : E) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply]

theorem mu_Z (Z : M.Mat (m + 1)) (x : Fin (m + 1) → M.R) : mu M Z (Z.Z.mulVec x) = (x (Fin.last m) : E) := by
  unfold mu
  rw [coe_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ Z.unit, Matrix.one_mulVec]

theorem mulVec_inj (Z : M.Mat (m + 1)) {x y : Fin (m + 1) → M.R} (h : Z.Z.mulVec x = Z.Z.mulVec y) : x = y := by
  have h1 := congrArg (fun v => fun i => ((v i : M.R) : E)) h
  rw [coe_mulVec, coe_mulVec] at h1
  have h2 := congrArg (fun v => (Z.Z.map M.R.subtype)⁻¹.mulVec v) h1
  simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ Z.unit, Matrix.one_mulVec] at h2
  funext i
  exact Subtype.ext (congrFun h2 i)

theorem lam_mk (Z : M.Mat (m + 1)) (v : Fin (m + 1) → M.R) :
    M.lam Z (Submodule.Quotient.mk v) = M.Rsub.mkQ (mu M Z v) := rfl

theorem mu_e (Z : M.Mat (m + 1)) :
    mu M Z (Pi.single (Fin.last m) 1) = (Z.Z.map M.R.subtype)⁻¹ (Fin.last m) (Fin.last m) := by
  unfold mu
  have e : (fun i => (((Pi.single (Fin.last m) (1 : M.R) : Fin (m + 1) → M.R) i : M.R) : E)) =
      (Pi.single (Fin.last m) (1 : E) : Fin (m + 1) → E) := by
    funext i
    by_cases h : i = Fin.last m <;> simp [h]
  rw [e, Matrix.mulVec_single]
  simp

def headK (Z : M.Mat (m + 1)) : Submodule M.R (Fin (m + 1) → M.R) :=
  (LinearMap.ker (LinearMap.proj (R := M.R) (φ := fun _ : Fin (m + 1) => M.R) (Fin.last m))).map Z.Z.mulVecLin

theorem mem_headK (Z : M.Mat (m + 1)) {y : Fin (m + 1) → M.R} :
    y ∈ headK M Z ↔ ∃ x, x (Fin.last m) = 0 ∧ Z.Z.mulVec x = y := by
  simp [headK, Submodule.mem_map, LinearMap.mem_ker]

end Lift

def LiftOrb : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ (m : ℕ) (Z Z' : M.Mat (m + 1)), Nonempty (M.Iso Z Z') →
    (Z.Z.map M.R.subtype)⁻¹ (Fin.last m) (Fin.last m) = (Z'.Z.map M.R.subtype)⁻¹ (Fin.last m) (Fin.last m) →
    ∃ l ρ : Matrix (Fin (m + 1)) (Fin (m + 1)) M.R, IsUnit l.det ∧ IsUnit ρ.det ∧
      (∀ i, l i (Fin.last m) = if i = Fin.last m then 1 else 0) ∧
      (∀ j, ρ (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧ Z'.Z = l * Z.Z * ρ

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

