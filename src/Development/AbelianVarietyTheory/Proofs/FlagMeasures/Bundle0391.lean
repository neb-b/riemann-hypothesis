module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameFixingIsometrySplitRowLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0267
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0265
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0165
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureQuotientUnitaryJVectorStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthComplementUnitVectorSameFields
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0234
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0389
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalIntegralsTermsOneDoubleCoset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardMiddleLatticesOverGenusLattice
section
noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.GluingNum

variable (D : D7)

abbrev jz (z : (VS D).V) : ((D.sp.X 0).V × D.host.E) →ₗ[𝓞 D.host.E] (VS D).V :=
  ((D.sp.iXY 0).coprod (LinearMap.toSpanSingleton D.host.E (VS D).V z)).restrictScalars (𝓞 D.host.E)

theorem jz_apply (z : (VS D).V) (p : (D.sp.X 0).V × D.host.E) :
    jz D z p = D.sp.iXY 0 p.1 + p.2 • z := rfl

theorem mem_Wb (v : (hS D).V) : v ∈ Wb D ↔
    (∀ a, (hS D).hT (D.sp.hypE a) v = 0) ∧ ∀ a, (hS D).hT (D.sp.hypF a) v = 0 := by
  unfold Wb
  rw [Formalism.MainNotions.mem_orth_iff]
  constructor
  · intro h
    exact ⟨fun a => h _ (Submodule.subset_span (Or.inl ⟨a, rfl⟩)),
      fun a => h _ (Submodule.subset_span (Or.inr ⟨a, rfl⟩))⟩
  · rintro ⟨h1, h2⟩ x hx
    have : Submodule.span D.host.E (Set.range D.sp.hypE ∪ Set.range D.sp.hypF) ≤
        LinearMap.ker ((hS D).hT.flip v) := by
      refine Submodule.span_le.2 ?_
      rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
      · exact h1 a
      · exact h2 a
    exact this hx

theorem eq_zero_of_mem_X {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (he : F0.e = D.sp.hypE)
    {x : (hS D).V} (hx : x ∈ F0.X) (hw : x ∈ Wb D) : x = 0 := by
  unfold FlagG.X at hx
  rw [he] at hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
  have h2 := ((mem_Wb D _).1 hw).2
  have hc : ∀ b, c b = 0 := by
    intro b
    have h := Formalism.MainNotions.hT_swap_zero (h2 b)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, D.sp.hyp_ef,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at h
    simpa using h
  simp [hc]

theorem iXY_mem_Wb (w : (D.sp.X 0).V) : D.sp.iXY 0 w ∈ Wb D :=
  (mem_Wb D _).2 ⟨fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthX a w).1,
    fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthX a w).2⟩

theorem zmOf_mem_Wb (u : D.what₂.Word) : D.zmOf u ∈ Wb D :=
  Submodule.smul_mem _ _ ((mem_Wb D _).2 ⟨fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthz a).1,
    fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthz a).2⟩)

theorem jz_mem_Wb (u : D.what₂.Word) (p : (D.sp.X 0).V × D.host.E) : jz D (D.zmOf u) p ∈ Wb D := by
  rw [jz_apply]
  exact (Wb D).add_mem (iXY_mem_Wb D _) ((Wb D).smul_mem _ (zmOf_mem_Wb D u))

theorem exists_jz (u : D.what₂.Word) (F0 : Fb D u) (hT : Tu D u ≠ 0) (he : F0.e = D.sp.hypE)
    (hz : F0.z = D.zmOf u) {v : (hS D).V} (hv : v ∈ Wb D) : ∃ p, jz D (D.zmOf u) p = v := by
  have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
  have hT' : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT
  set c : D.host.E := -((hS D).hT F0.z v) / ((Tu D u : ℕ) : D.host.E) with hc
  have hvz : v - c • D.zmOf u ∈ Wb D := (Wb D).sub_mem hv ((Wb D).smul_mem _ (zmOf_mem_Wb D u))
  have h1 : v - c • D.zmOf u ∈ orth (hS D) (Xplus (lf D F0)) := by
    rw [Formalism.MainNotions.mem_orth_iff]
    refine Formalism.MainNotions.hT_zero_of_mem_Xplus F0 (fun a => ?_) ?_
    · rw [he]; exact ((mem_Wb D _).1 hvz).1 a
    · rw [← hz, map_sub, map_smul, F0.z_norm, smul_eq_mul, hc]
      field_simp
      ring
  rw [← hW] at h1
  obtain ⟨_, ⟨w, rfl⟩, x, hx, hs⟩ := Submodule.mem_sup.1 h1
  have hx0 : x = 0 := by
    refine eq_zero_of_mem_X D F0 he hx ?_
    have : x = (v - c • D.zmOf u) - D.sp.iXY 0 w := by rw [← hs]; abel
    rw [this]
    exact (Wb D).sub_mem hvz (iXY_mem_Wb D w)
  refine ⟨(w, c), ?_⟩
  rw [hx0, add_zero] at hs
  rw [jz_apply, hs]
  simp

theorem comap_sup_X (u : D.what₂.Word) (F0 : Fb D u) (he : F0.e = D.sp.hypE)
    (L : LatV D) (hL : L ≤ toO (hS D) (Wb D)) :
    (L ⊔ toO (hS D) F0.X).comap (jz D (D.zmOf u)) = L.comap (jz D (D.zmOf u)) := by
  apply le_antisymm _ (Submodule.comap_mono le_sup_left)
  intro p hp
  obtain ⟨l, hl, x, hx, hs⟩ := Submodule.mem_sup.1 hp
  have hx0 : x = 0 := by
    refine eq_zero_of_mem_X D F0 he hx ?_
    have : x = jz D (D.zmOf u) p - l := by rw [← hs]; abel
    rw [this]
    exact (Wb D).sub_mem (jz_mem_Wb D u p) (hL hl)
  rw [hx0, add_zero] at hs
  change jz D (D.zmOf u) p ∈ L
  rw [← hs]; exact hl

theorem mem_Lsub {T : D.host.E} (F : Fg D T) (Λ : LatV D) (v : (hS D).V) :
    v ∈ Lsub Λ F ↔ v ∈ orth (hS D) (Xsp F) ∧
      ∃ l ∈ Λ, l ∈ orth (hS D) (Xsp F) ∧ v - l ∈ Xsp F := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨l, hl, x, hx, hs⟩ := Submodule.mem_sup.1 h1
    refine ⟨h2, l, hl.1, hl.2, ?_⟩
    rw [← hs]; simpa using hx
  · rintro ⟨h2, l, hl, hl', hx⟩
    refine ⟨Submodule.mem_sup.2 ⟨l, ⟨hl, hl'⟩, v - l, hx, by abel⟩, h2⟩

theorem Lsub_gmap {T : D.host.E} (F : Fg D T) (Λ : LatV D) (n : (hS D).V ≃ₗ[D.host.E] (hS D).V)
    (hn : FixFr D F n) : Lsub (Formalism.HermitianLatticesTheory.gmap n Λ) F = Lsub Λ F := by
  obtain ⟨h1, h2, h3⟩ := hn
  have key : ∀ l, n l ∈ orth (hS D) (Xsp F) ↔ l ∈ orth (hS D) (Xsp F) := by
    intro l
    have he : ∀ a, (hS D).hT (F.fl.e a) (n l) = (hS D).hT (F.fl.e a) l := by
      intro a
      have := h2 a.castSucc
      simp only [frame, FlagG.fvec, Fin.snoc_castSucc] at this
      conv_lhs => rw [← this]
      exact h1 _ _
    rw [Formalism.MainNotions.mem_orth_iff, Formalism.MainNotions.mem_orth_iff]
    constructor
    · intro h
      exact Formalism.MainNotions.hT_zero_of_mem_X F.fl (fun a => by
        rw [← he]; exact h _ (Submodule.subset_span ⟨a, rfl⟩))
    · intro h
      exact Formalism.MainNotions.hT_zero_of_mem_X F.fl (fun a => by
        rw [he]; exact h _ (Submodule.subset_span ⟨a, rfl⟩))
  ext v
  rw [mem_Lsub, mem_Lsub]
  refine and_congr_right (fun _ => ⟨?_, ?_⟩)
  · rintro ⟨_, ⟨l, hl, rfl⟩, hl', hx⟩
    have hl2 : l ∈ orth (hS D) (Xsp F) := (key l).1 hl'
    refine ⟨l, hl, hl2, ?_⟩
    have := (Xsp F).add_mem hx (h3 l hl2)
    convert this using 1
    change v - l = v - n l + (n l - l)
    abel
  · rintro ⟨l, hl, hl', hx⟩
    refine ⟨n l, ⟨l, hl, rfl⟩, (key l).2 hl', ?_⟩
    have := (Xsp F).sub_mem hx (h3 l hl')
    convert this using 1
    abel

theorem le_Wb_of_mem (u : D.what₂.Word) {M : LatW D} {L : LatV D} (hL : L ∈ glueSet D u M) :
    L ≤ toO (hS D) (Wb D) := by
  intro x hx
  change x ∈ Wb D
  rw [← hL.2.1]
  exact Submodule.subset_span hx

theorem comap_jz_inl (z : (VS D).V) (L : LatV D) :
    (L.comap (jz D z)).comap ((LinearMap.inl D.host.E (D.sp.X 0).V D.host.E).restrictScalars (𝓞 D.host.E)) =
      L.comap ((D.sp.iXY 0).restrictScalars (𝓞 D.host.E)) := by
  ext w
  change jz D z (w, 0) ∈ L ↔ D.sp.iXY 0 w ∈ L
  rw [jz_apply]
  simp

theorem gluingNum : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ M ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)), {𝓛 : Submodule (𝓞 D.host.E) ((D.sp.X 0).V × D.host.E) | (∃ Λ', IsRowLat D F0 Λ' ∧ (Lsub Λ' (lf D F0)).comap (((D.sp.iXY 0).coprod (LinearMap.toSpanSingleton D.host.E (VS D).V F0.z)).restrictScalars (𝓞 D.host.E)) = 𝓛) ∧ 𝓛.comap ((LinearMap.inl D.host.E (D.sp.X 0).V D.host.E).restrictScalars (𝓞 D.host.E)) = M}.ncard = (Tu D u - 1) ^ D.R.f := by
  intro D u hp h3 hs F0 he hz Λ hΛ M hM
  have hB : IsBase D u F0 := ⟨he, hz⟩
  have h1 : 1 ≤ Tu D u := by omega
  rw [← (GlobalTheory.T.ncard_gluedMiddleLattices_eq_pow_prime_sub_one D u F0 Λ hp h3 hs hB hΛ M hM).2]
  have hinj : Set.InjOn (fun L : LatV D => L.comap (jz D (D.zmOf u))) (glueSet D u M) := by
    have aux : ∀ L₁ ∈ glueSet D u M, ∀ L₂ : LatV D,
        L₁.comap (jz D (D.zmOf u)) = L₂.comap (jz D (D.zmOf u)) → L₁ ≤ L₂ := by
      intro L₁ h₁ L₂ h x hx
      obtain ⟨p, rfl⟩ := exists_jz D u F0 hp.ne_zero he hz (le_Wb_of_mem D u h₁ hx)
      have : p ∈ L₁.comap (jz D (D.zmOf u)) := hx
      rw [h] at this
      exact this
    intro L₁ h₁ L₂ h₂ h
    exact le_antisymm (aux L₁ h₁ L₂ h) (aux L₂ h₂ L₁ h.symm)
  rw [← hinj.ncard_image]
  congr 1
  ext 𝓛
  rw [hz]
  constructor
  · rintro ⟨⟨Λ', hΛ', rfl⟩, hc⟩
    obtain ⟨n, hn, hsp, hrow⟩ := _root_.GlobalTheory.LoopC.RowSplit.main D u F0 Λ' hB hΛ' h1
    obtain ⟨hg, hL⟩ := (GlobalTheory.T.splitRowLattice_middle_iff_gluedLattice D u F0 _ h1 hB hrow).1 hsp
    have e : (Lsub Λ' (lf D F0)).comap (jz D (D.zmOf u)) =
        (Formalism.HermitianLatticesTheory.gmap n Λ' ⊓ toO (hS D) (Wb D)).comap (jz D (D.zmOf u)) := by
      rw [← Lsub_gmap D (lf D F0) Λ' n hn, hL, comap_sup_X D u F0 he _ inf_le_right]
    refine ⟨Formalism.HermitianLatticesTheory.gmap n Λ' ⊓ toO (hS D) (Wb D),
      ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, ?_⟩, e.symm⟩
    rw [← comap_jz_inl D (D.zmOf u), ← e]
    exact hc
  · rintro ⟨L, hL, rfl⟩
    obtain ⟨hrow, hsp, hW⟩ := (GlobalTheory.T.splitRowLattice_middle_iff_gluedLattice D u F0 Λ h1 hB hΛ).2 M L hL
    have hL' := ((GlobalTheory.T.splitRowLattice_middle_iff_gluedLattice D u F0 _ h1 hB hrow).1 hsp).2
    refine ⟨⟨_, hrow, ?_⟩, ?_⟩
    · rw [hL', hW]
      exact comap_sup_X D u F0 he L (le_Wb_of_mem D u hL)
    · exact (comap_jz_inl D (D.zmOf u) L).trans hL.2.2.2.2.2

end GlobalTheory.LoopC.GluingNum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianSumStabiliserUnfolding
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem real_quot {n m : ℕ} (ε : Fin n → Bool) (ε' : Fin m → Bool) (s : Bool) (x₀ : Fin n → ℂ)
    (B : Matrix (Fin n) (Fin m) ℂ) (j : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε) (hn : m + 1 = n)
    (h1 : qEps ε x₀ = sgn ℝ s) (h2 : star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0)
    (h3 : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε')
    (h4 : ∀ g, uMat (j g) *ᵥ x₀ = x₀ ∧ uMat (j g) * B = B * uMat g) (c c' : ℝ) (hc : IsGauge ε c)
    (hc' : IsGauge ε' c') (b : Formalism.REAL.UJ ε → ENNReal) (hb : Measurable b)
    (hb1 : ∀ g, ∫⁻ h, b (j h * g) ∂(Formalism.REAL.muG ε') = 1) :
    ENNReal.ofReal c * ∫⁻ g, ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ x₀)) * b g ∂(Formalism.REAL.muG ε) =
      ENNReal.ofReal c' * ENNReal.ofReal (2 ^ n * gaussDens ε (sgn ℝ s)) := by
  subst hn
  obtain ⟨c₀, h0, -, hu⟩ := _root_.GlobalTheory.GaugeConst.gauge_exists_pos_unique m ε'
  have hpos : 0 < c' := hu c' hc' ▸ h0
  have hne : ENNReal.ofReal c' ≠ 0 := (ENNReal.ofReal_pos.2 hpos).ne'
  have hinv : (ENNReal.ofReal c')⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hne
  have hmul : ENNReal.ofReal c' * (ENNReal.ofReal c')⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hne ENNReal.ofReal_ne_top
  have key := _root_.GlobalTheory.GaugeQuot.gauge_quotient m ε ε' s x₀ B j h1 h2 h3 h4 c c' hc hc'
    (fun g => (ENNReal.ofReal c')⁻¹ * b g) (hb.const_mul _) (fun g => by
      rw [lintegral_const_mul' _ _ hinv, hb1, mul_one, hmul])
  rw [← key]
  simp_rw [mul_left_comm _ (ENNReal.ofReal c')⁻¹]
  rw [lintegral_const_mul' _ _ hinv, mul_left_comm _ (ENNReal.ofReal c')⁻¹, ← mul_assoc (ENNReal.ofReal c'),
    hmul, one_mul]

theorem exists_rat (I : AutInst) : ∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset ∧ (Γ : Set I.GA).Countable ∧
    DiscreteTopology Γ := by
  obtain ⟨⟨Γ, hΓ⟩, hc, hf⟩ := _root_.GlobalTheory.RatDiscrete.subgroup_countable_discrete I
  obtain ⟨-, -, h3, h4⟩ := _root_.GlobalTheory.adelicStab_isCompact_isOpen I
  refine ⟨Γ, hΓ, hΓ ▸ hc, ?_⟩
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : I.GA)
  have hfin : ((fun γ : Γ => (γ : I.GA)) ⁻¹' C).Finite := by
    refine Set.Finite.subset (Set.Finite.preimage Subtype.val_injective.injOn (hf C hC)) ?_
    intro γ hγ
    exact ⟨hΓ ▸ γ.2, hγ⟩
  have hn : ((fun γ : Γ => (γ : I.GA)) ⁻¹' C) ∈ nhds (1 : Γ) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hC1
  exact discreteTopology_of_isOpen_singleton_one (isOpen_singleton_of_finite_mem_nhds _ hn hfin)

theorem gauge_pos {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) : 0 < c := by
  obtain ⟨c₀, h0, -, hu⟩ := _root_.GlobalTheory.GaugeConst.gauge_exists_pos_unique n ε
  exact hu c h ▸ h0

theorem haar_muA (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] :
    (I.muA μf).IsHaarMeasure ∧ (I.muA μf).IsMulRightInvariant := by
  obtain ⟨-, -, h3, h4⟩ := _root_.GlobalTheory.adelicStab_isCompact_isOpen I
  have := _root_.GlobalTheory.CongTop.secondCountable_finiteAdelicPoints I
  refine ⟨?_, ⟨(_root_.GlobalTheory.AdelicUnimod.adelic_unimodular I μf).2.1⟩⟩
  unfold AutInst.muA
  haveI : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := Measure.pi.isHaarMeasure _
  exact Measure.prod.instIsHaarMeasure _ _

theorem unfold_sib (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E)
    (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf) (hp : IsPerp D s x A xf)
    (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
    (c' : InfinitePlace I.F → ℝ) (μf' : Measure D.inst.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure]
    (fund : Set I.GA) (hc : IsGaugeAll I c) (hc' : IsGaugeAll D.inst c') (hf : I.IsFundDom (I.muA μf) fund) :
    ENNReal.ofReal (∏ v, c v) * (∫⁻ g in fund, gaussSum I (sgn I.E s) g ∂(I.muA μf)) / μf I.Kset =
      gaugeVol D.inst c' μf' * ENNReal.ofReal (2 ^ (I.n * I.f) * ∏ v, gaussDens (I.ε v) (sgn ℝ s)) := by
  obtain ⟨hKc, hKo, i1, i2⟩ := _root_.GlobalTheory.adelicStab_isCompact_isOpen I
  obtain ⟨hKc', hKo', i1', i2'⟩ := _root_.GlobalTheory.adelicStab_isCompact_isOpen D.inst
  have i3 := _root_.GlobalTheory.CongTop.secondCountable_finiteAdelicPoints I
  have i3' := _root_.GlobalTheory.CongTop.secondCountable_finiteAdelicPoints D.inst
  obtain ⟨i4, -⟩ := haar_muA I μf
  obtain ⟨i4', i5'⟩ := haar_muA D.inst μf'
  have i6' : μf'.IsMulRightInvariant := ⟨(_root_.GlobalTheory.AdelicUnimod.adelic_unimodular D.inst μf').2.2.2.1⟩
  obtain ⟨jf, hjf, hrange⟩ := _root_.GlobalTheory.StabUnfold.exists_finEmb I D s x A xf hp
  have hloc := GlobalTheory.T.isOrthComplementOfUnitVector_at_real_place I D s x A xf hp
  choose jv hjc hjv using fun v => GlobalTheory.T.exists_closedEmbedding_orthogonalUnitary_realPlace I.n D.n (I.ε v) (D.ε v) s _ _ hp.1 (hloc v).1 (hloc v).2.1
    (hloc v).2.2
  obtain ⟨hK, hKg⟩ := GlobalTheory.T.mem_congruence_level_iff_orthEmbedding I D s x A xf hp jf hjf
  have hjfc := _root_.GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg I D.inst jf xf hKg
  have hj : Topology.IsClosedEmbedding (embA D jv jf) :=
    (Topology.IsClosedEmbedding.piMap hjc).prodMap hjfc
  obtain ⟨Γ, hΓ, hΓc, -⟩ := exists_rat I
  obtain ⟨Γ', hΓ', -, hΓd⟩ := exists_rat D.inst
  have hS : ((Γ'.map (embA D jv jf) : Subgroup I.GA) : Set I.GA) = stabF I x := by
    rw [Subgroup.coe_map, hΓ']
    exact _root_.GlobalTheory.StabUnfold.image_rational_eq_stab I D s x A xf hp jv jf hjv hjf
  obtain ⟨hopen, hmv, hleft, hright, hreal⟩ := _root_.GlobalTheory.StabUnfold.gaussAt_meas_inv I x
  have hind : Measurable ({h : I.Gf | x ∈ lamX I (1, h)}.indicator (1 : I.Gf → ENNReal)) :=
    measurable_one.indicator hopen.measurableSet
  have hΦ : Measurable (gaussAt I x) := by
    unfold gaussAt
    exact (Finset.measurable_prod _ fun v _ => (hmv v).comp ((measurable_pi_apply v).comp measurable_fst)).mul
      (hind.comp measurable_snd)
  have hinv : ∀ h g, gaussAt I x (embA D jv jf h * g) = gaussAt I x g := by
    intro h g
    unfold gaussAt
    congr 1
    · refine Finset.prod_congr rfl fun v _ => ?_
      exact congrArg (fun y => ENNReal.ofReal (gauss y)) (hreal v _ (g.1 v) (hjv v (h.1 v)).1)
    · have := hleft (jf h.2) g.2 (hjf h.2).1
      rw [show (embA D jv jf h * g).2 = jf h.2 * g.2 from rfl]
      by_cases hg : x ∈ lamX I (1, g.2)
      · rw [Set.indicator_of_mem (show _ ∈ {h : I.Gf | x ∈ lamX I (1, h)} from this.2 hg),
          Set.indicator_of_mem (show _ ∈ {h : I.Gf | x ∈ lamX I (1, h)} from hg)]
        rfl
      · rw [Set.indicator_of_notMem (show _ ∉ {h : I.Gf | x ∈ lamX I (1, h)} from fun h' => hg (this.1 h')),
          Set.indicator_of_notMem (show _ ∉ {h : I.Gf | x ∈ lamX I (1, h)} from hg)]
  obtain ⟨ι, hι, r, hr1, hr2, hr3⟩ := GlobalTheory.T.latticeGaussianSumOfLength_eq_tsum_stabilizer_cosets I s x hp.2.1
  have hmem : ∀ γ, γ ∈ Γ ↔ γ ∈ I.GFset := fun γ => by rw [← hΓ]; rfl
  have hmemS : ∀ γ, γ ∈ Γ'.map (embA D jv jf) ↔ γ ∈ stabF I x := fun γ => by rw [← hS]; rfl
  have horb := _root_.GlobalTheory.StabUnfold.lintegral_tsum_cosets_eq_covol I.GA Γ (Γ'.map (embA D jv jf)) (I.muA μf) fund (gaussAt I x) ι r hΓc
    (fun γ h => (hmem γ).2 ((hmemS γ).1 h).1) (fun γ _ => (_root_.GlobalTheory.AdelicUnimod.adelic_unimodular I μf).1 γ) hf.1
    (fun y => by obtain ⟨γ, h1, h2⟩ := hf.2.1 y; exact ⟨γ, (hmem γ).2 h1, h2⟩)
    (fun γ h => hf.2.2 γ ((hmem γ).1 h)) hΦ
    (by rintro _ ⟨h, -, rfl⟩ g; exact hinv h g) (fun i => (hmem _).2 (hr1 i))
    (fun γ h => by simp only [hmemS]; exact hr2 γ ((hmem γ).1 h))
  have i7 : ∀ v, (Formalism.REAL.muG (D.ε v)).IsMulRightInvariant := fun v => ⟨Formalism.REAL.indefinite_unitary_unimodular _ _⟩
  choose bv hbv hbv1 using fun v => GlobalTheory.T.exists_measurable_lintegral_coset_eq_one_closedSubgroup _ _ (Formalism.REAL.muG (D.ε v)) (jv v) (hjc v)
  obtain ⟨bf, hbf, hbf1, hbf2⟩ := _root_.GlobalTheory.StabUnfold.exists_cutoff_doubleCoset I.Gf D.inst.Gf μf μf' jf hjfc (Ksub I) (Ksub D.inst) xf
    {h : I.Gf | x ∈ lamX I (1, h)} hKo hKo' hKc' hK (fun g => by
      constructor
      · intro hg
        obtain ⟨h, h1, k, hk, e⟩ := GlobalTheory.T.stabilizer_transitive_adelic_unit_length_vectors I s x xf g hp.2.1 hp.2.2.2.2.1 hg
        obtain ⟨h', rfl⟩ := hrange h h1
        exact ⟨h', k, hk, e⟩
      · rintro ⟨h, k, hk, rfl⟩
        exact (hright _ k hk).2 ((hleft _ _ (hjf h).1).2 hp.2.2.2.2.1))
  have hb : Measurable fun g : I.GA => (∏ v, bv v (g.1 v)) * bf g.2 :=
    (Finset.measurable_prod _ fun v _ => (hbv v).comp ((measurable_pi_apply v).comp measurable_fst)).mul
      (hbf.comp measurable_snd)
  have hb1 : ∀ g : I.GA, ∫⁻ h, (∏ v, bv v ((embA D jv jf h * g).1 v)) * bf (embA D jv jf h * g).2
      ∂(D.inst.muA μf') = 1 := by
    intro g
    have := _root_.GlobalTheory.StabUnfold.lintegral_pi_prod_mul _ _ (fun v => Formalism.REAL.muG (D.ε v)) _ μf' (fun v h => bv v (jv v h * g.1 v))
      (fun h => bf (jf h * g.2))
      (fun v => (hbv v).comp (((hjc v).continuous.mul continuous_const).measurable))
      (hbf.comp ((hjfc.continuous.mul continuous_const).measurable))
    simp only [hbv1, hbf1, Finset.prod_const_one, mul_one] at this
    exact this
  have hun := _root_.GlobalTheory.GenUnfold.covol_withDensity_eq I.GA D.inst.GA (I.muA μf) (D.inst.muA μf') (embA D jv jf) hj Γ' (gaussAt I x) _ hΦ hb
    hinv hb1
  have hint : ∫⁻ g, gaussAt I x g * ((∏ v, bv v (g.1 v)) * bf g.2) ∂(I.muA μf) =
      (∏ v, ∫⁻ g, ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x)) * bv v g ∂(Formalism.REAL.muG (I.ε v))) *
        (μf I.Kset / μf' D.inst.Kset) := by
    have := _root_.GlobalTheory.StabUnfold.lintegral_pi_prod_mul _ _ (fun v => Formalism.REAL.muG (I.ε v)) _ μf
      (fun v g => ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x)) * bv v g)
      (fun g => {h : I.Gf | x ∈ lamX I (1, h)}.indicator 1 g * bf g)
      (fun v => (hmv v).mul (hbv v)) (hind.mul hbf)
    rw [hbf2] at this
    refine Eq.trans (lintegral_congr fun g => ?_) this
    unfold gaussAt
    rw [Finset.prod_mul_distrib, mul_mul_mul_comm]
  have hq := fun v => real_quot (I.ε v) (D.ε v) s _ _ (jv v) hp.1 (hloc v).1 (hloc v).2.1 (hloc v).2.2 (hjv v)
    (c v) (c' v) (hc v) (hc' v) (bv v) (hbv v) (hbv1 v)
  have hs : sgn ℝ s ≠ 0 := by unfold sgn; split_ifs <;> norm_num
  have hd : ∀ v, 0 ≤ gaussDens (I.ε v) (sgn ℝ s) := fun v => ((_root_.GlobalTheory.GaussMean.Density.gaussDens_spec _ (I.ε v)).1 _ hs).2
  have hprod := Finset.prod_congr (s₁ := Finset.univ) rfl fun v _ => hq v
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← ENNReal.ofReal_prod_of_nonneg fun v _ => (gauge_pos (hc v)).le,
    ← ENNReal.ofReal_prod_of_nonneg fun v _ => (gauge_pos (hc' v)).le,
    ← ENNReal.ofReal_prod_of_nonneg fun v _ => mul_nonneg (by positivity) (hd v), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, (_root_.GlobalTheory.FlagMeas.instance_numbers I).2.2.2.2.1, ← pow_mul] at hprod
  have hK0 : μf I.Kset ≠ 0 := (hKo.measure_pos μf ⟨1, (Ksub I).one_mem⟩).ne'
  have hKt : μf I.Kset ≠ ⊤ := hKc.measure_lt_top.ne
  simp_rw [hr3]
  rw [horb, hun, hint, hΓ', gaugeVol, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  generalize covol D.inst.GFset (D.inst.muA μf') Set.univ = a
  generalize (μf' D.inst.Kset)⁻¹ = t
  have h1 := ENNReal.mul_inv_cancel hK0 hKt
  calc _ = a * t * (ENNReal.ofReal (∏ v, c v) * ∏ v, ∫⁻ g, ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x)) *
        bv v g ∂(Formalism.REAL.muG (I.ε v))) * (μf I.Kset * (μf I.Kset)⁻¹) := by ring
    _ = _ := by rw [hprod, h1]; ring

theorem gaugeUnfold : GaugeUnfold := by
  intro I I' e s x A xf _ hp c μf _ _ c' μf' _ _ fund hc hc' hf
  obtain ⟨D, B, hD, hvol⟩ := _root_.GlobalTheory.PerpReduce.exists_sib I I' e s x A xf hp
  obtain ⟨μ, h1, h2⟩ := _root_.GlobalTheory.CongTop.exists_haar_sigmaFinite D.inst
  choose d _ hd _ using fun v => _root_.GlobalTheory.GaugeConst.gauge_exists_pos_unique D.n (D.ε v)
  rw [← hvol d μ c' μf' hd hc']
  exact unfold_sib I D s x B xf hD c μf d μ fund hc hd hf

end GlobalTheory.StabUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassIntegralLatticesDiscriminantOrderLeStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_integralLattices_discriminantOrder_le : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → 1 ≤ Module.finrank K V → ∀ (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K), h'.IsSymm → ∀ I : Submodule (𝓞 K) V', IsOrthoLattice h' I (Module.finrank K V) → ∀ n : ℕ, 1 ≤ n → orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ ENNReal.ofReal (mass h' I * (n : ℝ) ^ (((Module.finrank K V : ℝ) + Real.logb 2 (Module.finrank ℚ K)) / 2)) := by
  first | exact @GlobalTheory.Mass.SpaceMass.main | exact GlobalTheory.Mass.SpaceMass.main | (intros; apply GlobalTheory.Mass.SpaceMass.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalIntegralsTermsOneDoubleCosetStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbital_integrals_terms_one_doubleCoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ t₀ : TauC Y u u', t₀.relevant → t₀.G ≠ 0 → ∀ w, w = Formalism.L2.SG.PairVal.ptOf t₀.toTerm → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) ∧ ∃ T : X.Vpi u' →L[ℂ] X.Vpi u, ‖Formalism.L2.SG.PackageTie.hsEmb T‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (haveI := FiniteDimensional.complete ℂ (X.Vpi u); OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' w))‖ ∧ ∀ (t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (xn xm : X.B.I.GA), n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → RatLink X xn n → RatLink X xm m → ∃ (μR : Measure X.B.I.Ginf) (K : Set X.B.I.Ginf), Formalism.L2.SG.VolPin.IsPinnedR t w μR ∧ (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, ∃! s, s ∈ ROinf t ∧ s * y ∈ K) ∧ OOt t = (((μR K).toReal : ℂ) * ((X.psiInfU u xn.1)⁻¹ * X.psiInfU u' xm.1)) • T := by
  first | exact @GlobalTheory.CosetOrbital.coset_orbital_form | exact GlobalTheory.CosetOrbital.coset_orbital_form | (intros; apply GlobalTheory.CosetOrbital.coset_orbital_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankConditionOfColumnsEqualSymmetricLevel
section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem mu0Tie_of_colsTiedSym : ∀ (D : D7), Formalism.L2.Forms.ColsTiedSym D → ∀ u : D.what₂.Word, StandardLattice.Mu0Tie D u :=
  fun _ C u => Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u

end GlobalTheory
end

