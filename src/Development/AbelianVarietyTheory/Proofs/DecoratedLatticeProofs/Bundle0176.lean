module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0158
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.LevelFacts

variable {D : D7}

theorem places_of_stage {c : Com D} {j : ℕ} {s : PiLocalization₂ D} (hs : s.Is c j) : s.L.Pg = c.Pg ∧ s.L.Q = ∅ := by
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  rw [hL]
  exact ⟨rfl, rfl⟩

theorem mem_levG_of_red {c : Com D} {j : ℕ} {s : PiLocalization₂ D} (hs : s.Is c j) {k : GA D s.V} (hk : k ∈ GfC s.V)
    (hS : Lev.finE s.V k ∈ St s.β) (hr : ∀ PP ∈ c.Pg, redFn s.β PP (Lev.finE s.V k) = 1) :
    k ∈ Lev.levG s.V s.β s.L ∧ Lev.levChi s.V s.β s.L k = 1 := by
  obtain ⟨hPg, hQ⟩ := places_of_stage hs
  have h' : ∀ PP, PP ∈ s.L.Pg ∨ PP ∈ s.L.Q → redFn s.β PP (Lev.finE s.V k) = 1 := by
    rintro PP (h | h)
    · exact hr PP (hPg ▸ h)
    · rw [hQ] at h; simp at h
  refine ⟨⟨hk, GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm s.V.gram s.β s.L _ (GlobalTheory.LevSplit.finE_mem_UA s.V k) hS h'⟩, ?_⟩
  unfold Lev.levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one s.β s.L _ h', Units.val_one]

theorem finE_mem_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {k : GA D V}
    (hk : k ∈ Lev.levG V β L) : Lev.finE V k ∈ St β :=
  parLev_St (lev_le_parLev hk.2)

theorem emb_mem_GfC (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (k : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v) :
    GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k ∈ GfC V := by
  rw [GlobalTheory.AdelicU.GfC_eq]
  exact GlobalTheory.AdelicU.mem_finPts.2 (by simp)

theorem levChi_norm {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (k : GA D V) :
    ‖Lev.levChi V β L k‖ = 1 := by
  obtain ⟨n, hn, h⟩ := (GlobalTheory.LevSplit.levFn_finOrd β L (Lev.finE V k)).exists_pow_eq_one
  have h2 : (Lev.levChi V β L k) ^ n = 1 := by
    unfold Lev.levChi
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h2 hn.ne'

theorem levChi_mul {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {k k' : GA D V}
    (hk : k ∈ Lev.levG V β L) (hk' : k' ∈ Lev.levG V β L) :
    Lev.levChi V β L (k * k') = Lev.levChi V β L k * Lev.levChi V β L k' := by
  have e := (levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩
  have e' : levFn β L (Lev.finE V k * Lev.finE V k') = levFn β L (Lev.finE V k) * levFn β L (Lev.finE V k') := e
  unfold Lev.levChi
  rw [map_mul, e', Units.val_mul]

end GlobalTheory.ChainOnto.LevelFacts

namespace GlobalTheory.ChainOnto.LevelFacts

theorem levFacts : ∀ D : D7, LevFacts D := by
  intro D c _ j _ s hs
  have hfr := hs.frame
  have hPS : ∀ PP ∈ c.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ c.S := fun PP hPP => by
    classical
    unfold Com.S
    exact Finset.mem_image_of_mem _ hPP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨U, hU, hUk⟩ := _root_.GlobalTheory.ChainOnto.LevelOpen.exists_open_princ D s.V s.β c.Pg
    exact ⟨U, hU, fun k hk hkf => mem_levG_of_red hs hkf (hUk k hk).1 (hUk k hk).2⟩
  · intro v hv k hk
    have hSt : Lev.finE s.V (GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v k) ∈ St s.β := by
      refine (_root_.GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D s.V s.β s.Λ hfr _).2 fun w => ?_
      by_cases e : w = v
      · subst e
        rw [GlobalTheory.AdelicU.proj_emb_self]
        exact hk
      · rw [GlobalTheory.AdelicU.proj_emb_ne _ _ e]
        exact one_mem _
    refine mem_levG_of_red hs (emb_mem_GfC s.V v k) hSt fun PP hPP => ?_
    · refine _root_.GlobalTheory.ChainOnto.RedOne.redFn_eq_one D s.V s.β _ PP hSt ?_
      have hne : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := fun e => hv (e ▸ hPS PP hPP)
      exact GlobalTheory.AdelicU.proj_emb_ne _ _ hne k
  · intro k hk v
    exact (_root_.GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D s.V s.β s.Λ hfr k).1 (finE_mem_St hk) v
  · intro k hkf hint h1
    have hSt : Lev.finE s.V k ∈ St s.β := by
      refine (_root_.GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D s.V s.β s.Λ hfr k).2 fun v => ?_
      by_cases hv : v ∈ c.S
      · rw [h1 v hv]; exact one_mem _
      · exact hint v hv
    exact mem_levG_of_red hs hkf hSt fun PP hPP => _root_.GlobalTheory.ChainOnto.RedOne.redFn_eq_one D s.V s.β k PP hSt (h1 _ (hPS PP hPP))
  · intro k hk k' hk'
    exact levChi_mul hk hk'
  · intro k _
    exact levChi_norm s.β s.L k

end GlobalTheory.ChainOnto.LevelFacts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageCuspFormMapEqZeroOfValueZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStage_cuspFormMap_eq_zero_of_value_zero : ∀ D : D7, MetEx D → ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0 := by
  first | exact @GlobalTheory.ChainOnto.val_eq_zero_imp | exact GlobalTheory.ChainOnto.val_eq_zero_imp | (intros; apply GlobalTheory.ChainOnto.val_eq_zero_imp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepCharsUnramifiedOffS
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem step_chars_unrAt : ∀ (D : D7) (c : Com D), c.Is → ∀ k < D.R.m, ∀ v ∉ c.S, ∀ w : HeightOneSpectrum (𝓞 D.host.E),
    w.under (𝓞 D.host.F) = v → UnrAt (c.chS (k + 1)) w ∧ UnrAt (c.chT (k + 1)) w := by
  intro D c hc k hk v hv w hw
  have hμ : UnrAt (c.μ (k + 1)) w := by
    have := hc.unr ⟨k, hk⟩ w
    exact this (by rw [GlobalTheory.LFun.above, Set.mem_setOf_eq, hw]; exact hv)
  have hη : UnrAt c.η⁻¹ w := (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 w).inv
  have hμη : UnrAt (c.μ (k + 1) * c.η⁻¹) w := hμ.mul hη
  unfold Com.chS Com.chT Lift.chrStep
  split_ifs <;> exact ⟨by assumption, by assumption⟩

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainUpwardInductionFixedMetric
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_tprod_ne_zero_of_cc {D : D7} {c : Com D} {s : PiLocalization₂ D} (z : s.CC c) (hz : z ≠ 0) :
    ∃ v : s.M.Vec, PiTensorProduct.tprod ℂ v ≠ 0 := by
  by_contra hne
  push_neg at hne
  apply hz
  apply Subtype.ext
  show (z : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = 0
  apply LinearMap.ext_on (PiTensorProduct.span_tprod_eq_top (R := ℂ) (s := fun τ => s.M.sm τ))
  rintro w ⟨v, rfl⟩
  simp [hne v]

theorem ip_unique {D : D7} {c : Com D} {s : PiLocalization₂ D} {ipD ipD' : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip ip' : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (h : IsMet c s ipD ip) (h' : IsMet c s ipD' ip')
    (z : s.CC c) (hz : z ≠ 0) (x y : s.CC c) : ip x y = ip' x y := by
  obtain ⟨v, hv⟩ := exists_tprod_ne_zero_of_cc z hz
  have d : ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) =
      ipD' (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) := by rw [h.pure, h'.pure]
  have dne : ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    intro h0
    have := h.posD _ hv
    rw [h0] at this
    simp at this
  have e1 := h.schur x y (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v)
  have e2 := h'.schur x y (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v)
  rw [e1, ← d] at e2
  exact mul_right_cancel₀ dne e2

theorem thetaChain_upward_induction_fixed_metric {D : D7} (hMet : MetEx D) (hSU : StepUp D) (hgap : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D) {c : Com D} (hc : c.Is)
    {s₀ : PiLocalization₂ D} (hs₀ : s₀.Is c 0) {ipD₀ ip₀} (h₀ : IsMet c s₀ ipD₀ ip₀) {u : s₀.CC c} {B : GlobalTheory.LFun.Fam D.host.E}
    (hu : IsPar u B) (hL : ∀ k < D.R.m, LNe c (c.chT (k + 1)) (chainPar c B k)) {k : ℕ} {s : PiLocalization₂ D}
    {Θ : s.CC c →ₗ[ℂ] s₀.CC c} (hR : Reach c s₀ k s Θ) : k ≤ D.R.m → s.Is c k ∧
      ∀ ipD ip, IsMet c s ipD ip → ∃ x : s.CC c, (∀ y, ip y x = ip₀ (Θ y) u) ∧ IsPar x (chainPar c B k) := by
  induction hR with
  | zero =>
    intro _
    refine ⟨hs₀, fun ipD ip h => ⟨u, fun y => ?_, hu⟩⟩
    exact ip_unique h h₀ u hu.1 y u
  | @step k s Θ _ s' hs' p hp ih =>
    intro hk
    obtain ⟨hsk, ih⟩ := ih (by omega)
    refine ⟨hs', fun ipD' ip' h' => ?_⟩
    obtain ⟨ipD, ip, hm⟩ := hMet c hc k (by omega) s hsk
    obtain ⟨x, hx, hxp⟩ := ih ipD ip hm
    obtain ⟨x', hx', hx'p⟩ := hSU hgap c hc k (by omega) s s' hsk hs' p hp ipD ip ipD' ip' hm h' x (chainPar c B k) hxp
      (hL k (by omega))
    refine ⟨x', fun y => ?_, ?_⟩
    · rw [hx', hx]
      rfl
    · rw [chainPar_succ]
      exact hx'p

theorem reach_is {D : D7} {c : Com D} {s₀ : PiLocalization₂ D} (hs₀ : s₀.Is c 0) {k : ℕ} {s : PiLocalization₂ D} {Θ : s.CC c →ₗ[ℂ] s₀.CC c}
    (hR : Reach c s₀ k s Θ) : s.Is c k := by
  cases hR with
  | zero => exact hs₀
  | step _ hs' _ _ => exact hs'

theorem chainUp_of : ∀ D : D7, MetEx D → ParBoundW D → ChainLW D → StepUp D → ChainUp D := by
  intro D hMet hPB hCL hSU hgap c hc s₀ hs₀ k hk s Θ hR
  refine ⟨reach_is hs₀ hR, fun ipD₀ ip₀ ipD ip h₀ h u B hu => ?_⟩
  have hb := hPB c hc 0 (Nat.zero_le _) s₀ hs₀ u B hu
  have hr : s₀.V.rank = D.R.r := by rw [hs₀.rank]; simp [Formalism.BasicNotions.Ranks.rankY]
  rw [hr] at hb
  exact (thetaChain_upward_induction_fixed_metric hMet hSU hgap hc hs₀ h₀ hu (fun k hk => hCL c hc B hb k hk) hR hk).2 ipD ip h

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelMulConjCuspFormIntegrableOn
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.ThetaFirstVar

open GlobalTheory.Size

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}

theorem thetaKO_left_fst (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (h : GA D W) :
    ∀ γ ∈ GQ V, ∀ g, thetaKO ω (γ * g) h f = thetaKO ω g h f := fun γ hγ g => by
  have e : ((γ * g, h) : GA D V × GA D W) = (γ, 1) * (g, h) := by simp
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hf)

theorem thetaKO_continuous_fst (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (h : GA D W) :
    Continuous fun g => thetaKO ω g h f :=
  (hω.om_cont f hf 0).comp (Continuous.prodMk_left h)

theorem thetaKO_modGrowth_fst (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f)
    (h : GA D W) : GlobalTheory.Grow.ModGrowth V fun g => thetaKO ω g h f := by
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne V W
  obtain ⟨C, -, hC⟩ := (H V W rfl rfl).real ψ hθ hU
  refine ⟨C * (sobO ψ θ μ 𝓕 d f).toReal * GlobalTheory.Grow.height W h ^ A, A, fun g => ?_⟩
  rw [mul_assoc _ (GlobalTheory.Grow.height W h ^ A), ← mul_pow, mul_comm (GlobalTheory.Grow.height W h)]
  exact (hC χS χT ω hω μ 𝓕 hμ f hl).2 g h

theorem thetaKO_mul_conj_integrableOn : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ (u : WO S T → ℂ) (y : GA D S → ℂ), IsThetaFunO ψ S T u → IsAutFunSm θ S y → IsCuspFun S y → ∀ (a : GA D S) (x : GA D T), IntegrableOn (fun g => thetaKO om g x u * conj (y (g * a))) 𝓕 ν := by
  intro hP D ψ S T χS χT om hω θ hθ ν 𝓕 hν h𝓕 u y hu hy hc a x
  have : BorelSpace (GA D S) := ⟨rfl⟩
  have hR : GlobalTheory.Grow.RapidDec S fun g => conj (y (g * a)) :=
    ((GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hy hc).mul_right a).conj
  exact hR.integrableOn_modGrowth_mul hν h𝓕 (thetaKO_modGrowth_fst hθ hω hu x) (thetaKO_left_fst hω hu x)
    (thetaKO_continuous_fst hω hu x).measurable.aestronglyMeasurable

end GlobalTheory.ChainOnto.ThetaFirstVar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLatticeVacuumNonsplitPlaceVacuumAtPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)
namespace GlobalTheory.VacInertAt

variable {D : D7}

theorem half_eq_two_smul {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal) (S T : HSp D) (u : WO S T)
    (hu : u ∈ latO S T (L0c D S) (L0c D T) fun _ => True)
    (hh : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u) :
    ∃ u' ∈ latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E))
      (fun x => x = v), u = 2 • u' := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have h2F : (2 : D.host.F) ≠ 0 := two_ne_zero
  set γ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F := α * algebraMap D.host.F _ ((2 : D.host.F)⁻¹) with hγdef
  have hγ : γ ∈ intAf D.host.F := fun w => by
    rw [hγdef, map_mul, AlgHom.commutes]
    by_cases hw : w = v
    · subst hw
      rw [h1, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap, map_inv₀]
      have : HeightOneSpectrum.valuation D.host.F w (2 : D.host.F) = 1 := by
        rw [← map_ofNat (algebraMap (𝓞 D.host.F) D.host.F) 2, HeightOneSpectrum.valuation_of_algebraMap]
        exact HeightOneSpectrum.intValuation_eq_one_iff.2 h2
      rw [this, inv_one]
    · rw [h0 w hw, zero_mul]; exact zero_mem _
  have hγv : ∀ w, ¬ w = v → evalV D.host.F w γ = 0 := fun w hw => by
    rw [hγdef, map_mul, h0 w hw, zero_mul]
  have hαγ : α = γ + γ := by
    rw [← two_mul, hγdef, mul_comm α, ← mul_assoc, ← map_ofNat (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) 2,
      ← map_mul, mul_inv_cancel₀ h2F, map_one, one_mul]
  set a₀ := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 γ) with ha₀
  let φ : WO S T →+ WO S T := DistribSMul.toAddMonoidHom (WO S T) a₀
  have key : latO S T (L0c D S) (L0c D T) (fun _ => True) ≤
      (latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E))
        (fun x => x = v)).comap φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, -, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨γ * β, GlobalTheory.VacLat.intAf_mul hγ hβ,
      fun w hw => by rw [map_mul, hγv w hw, zero_mul], a, ha, s, by rw [← hermitianSpaceBaseLattice_eq_frameLattice]; exact hs, t,
      by rw [← hermitianSpaceBaseLattice_eq_frameLattice]; exact ht, ?_⟩
    ext i j
    simp only [φ, DistribSMul.toAddMonoidHom_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [ha₀, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.VacLat.pairA_mul]
  refine ⟨a₀ • u, key hu, ?_⟩
  have he : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = a₀ + a₀ := by
    rw [ha₀, ← map_add (f := _), hαγ]
    congr 1
    exact Prod.ext (add_zero 0).symm rfl
  ext i j
  rw [two_nsmul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ← add_mul, ← he]
  exact (hh i j).symm

theorem isVacAt_of_vacFin : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)),
    w.under (𝓞 D.host.F) = v → Formalism.DivisionValues.conjPl w = w → ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ),
    VacFin ψ S T v f → IsVacAt ψ S T w f := by
  intro D v w hv hw ψ S T f hf
  obtain ⟨ε, hε, -, hc, hpi⟩ := GlobalTheory.VacFixInert.inert_data hw
  have h2 := GlobalTheory.VacFixInert.two_not_mem hc
  rw [hv] at hε h2
  refine ⟨hf.1, fun e f' he u hu hhalf => ?_⟩
  have hee := (hpi e f' he).1
  have hh : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u := by
    rcases hhalf with h | h
    · rw [hee] at h; exact h
    · rw [hee, GlobalTheory.IdemSupport.cA_algebraMap] at h; exact h
  obtain ⟨u', hu', rfl⟩ := half_eq_two_smul hε h2 S T u hu hh
  exact hf.2.1 u' hu'

end GlobalTheory.VacInertAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLatticeVacuumSplitPlaceVacuumAtPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)

noncomputable section

namespace GlobalTheory.VacSplit

theorem isVacAt_of_vacFin : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → Formalism.DivisionValues.conjPl w ≠ w → ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ), VacFin ψ S T v f → IsVacAt ψ S T w f := by
  intro D v w hvw hw ψ S T f hf
  refine ⟨hf.1, fun e f' he u hu hhalf => ?_⟩
  have he' := he
  obtain ⟨hid, rfl⟩ := GlobalTheory.CentralShift.split_of_primeIdem hw he
  obtain ⟨v', ε, hε, hf', hv'⟩ := GlobalTheory.VacLat.place_of_primeIdem he'
  rw [hvw] at hv'
  subst hv'
  have hfu : ∀ i j, (e + Formalism.L2.Theta.cA D e) * u i j = u i j := by
    have h1 := hid.1.1
    have h2 := hid.1.2.1
    have h3 : Formalism.L2.Theta.cA D e * Formalism.L2.Theta.cA D e = Formalism.L2.Theta.cA D e := by rw [← map_mul, h1]
    have h4 : Formalism.L2.Theta.cA D e * e = 0 := by rw [mul_comm]; exact h2
    rcases hhalf with h | h <;> intro i j
    · have h' : e * u i j = u i j := h i j
      rw [← h', ← mul_assoc, add_mul, h1, h4, add_zero]
    · have h' : Formalism.L2.Theta.cA D e * u i j = u i j := h i j
      rw [← h', ← mul_assoc, add_mul, h2, h3, zero_add]
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have hα : α ∈ intAf D.host.F := fun w' => by
    by_cases hw' : w' = v
    · subst hw'; rw [h1]; exact one_mem _
    · rw [h0 w' hw']; exact zero_mem _
  set a₀ := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) with ha₀
  let φ : WO S T →+ WO S T := DistribSMul.toAddMonoidHom (WO S T) a₀
  have key : latO S T (L0c D S) (L0c D T) (fun _ => True) ≤
      (latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E))
        fun u => u = v).comap φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, -, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨α * β, GlobalTheory.VacLat.intAf_mul hα hβ,
      fun v'' hv'' => by rw [map_mul, h0 v'' hv'', zero_mul], a, ha, s, ?_, t, ?_, ?_⟩
    · show S.frame.equivFun.symm s ∈ S.L0
      rw [Module.Basis.equivFun_symm_apply]; exact hs
    · show T.frame.equivFun.symm t ∈ T.L0
      rw [Module.Basis.equivFun_symm_apply]; exact ht
    · ext i j
      simp only [φ, DistribSMul.toAddMonoidHom_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      rw [ha₀, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.VacLat.pairA_mul]
  have hum : u ∈ latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E))
      fun u => u = v := by
    have hk := key hu
    have hφ : φ u = u := by
      ext i j
      have hx := hfu i j
      rw [hf'] at hx
      exact hx
    rwa [AddSubgroup.mem_comap, hφ] at hk
  rcases hhalf with h | h
  · exact hf.2.2 e hid.1 u hum h
  · refine hf.2.2 (Formalism.L2.Theta.cA D e) ⟨by rw [← map_mul, hid.1.1], ?_, ?_⟩ u hum h
    · rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm]; exact hid.1.2.1
    · obtain ⟨w', η, hη, hwη⟩ := hid.1.2.2
      exact ⟨w', η, hη, by rw [GlobalTheory.DualPairCheck.cA_cA, add_comm]; exact hwη⟩

end GlobalTheory.VacSplit

end
end

