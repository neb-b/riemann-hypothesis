module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0216
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRadialMapUnitaryLeviBlockProduct
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso.MapRadial

theorem continuous_hs {n : ℕ} : Continuous (Formalism.REAL.hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold Formalism.REAL.hs
  fun_prop

theorem hs_nonneg' {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs g := by
  unfold Formalism.REAL.hs
  positivity

theorem measurable_hs_uMat {n : ℕ} (ε : Fin n → Bool) :
    Measurable fun g : Formalism.REAL.UJ ε => Formalism.REAL.hs (uMat g - 1) := by
  have : Continuous fun g : Formalism.REAL.UJ ε => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  exact (continuous_hs.comp (this.sub continuous_const)).measurable

theorem measurable_hs_loc (j : ℕ) : Measurable fun x : Fin j → Fin j → ℂ =>
    Formalism.REAL.hs (Matrix.of x - 1) + Formalism.REAL.hs ((Matrix.of x)⁻¹ - 1) := by
  have h0 : Continuous fun x : Fin j → Fin j → ℂ => Matrix.of x := continuous_id
  have h1 : Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).det := h0.matrix_det.measurable
  have h2 : ∀ r s, Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).adjugate r s :=
    fun r s => (h0.matrix_adjugate.matrix_elem r s).measurable
  refine (continuous_hs.comp (h0.sub continuous_const)).measurable.add ?_
  unfold Formalism.REAL.hs
  refine Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun s _ => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact (((h1.inv.mul (h2 r s)).sub measurable_const).norm).pow_const 2

theorem isRadial_map_lev : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ → (∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) → ∀ c : ℝ, IsGauge ε₀ c → IsRadial (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) (fun g => Formalism.REAL.hs (uMat g - 1)) (n₀ ^ 2 + 2 * ∑ i, j i ^ 2) := by
  intro n n₀ a j ε ε₀ B B₀ hF θ hθ hθe c hc
  have hG : IsRadial (ENNReal.ofReal c • Formalism.REAL.muG ε₀) (fun g => Formalism.REAL.hs (uMat g - 1)) (n₀ ^ 2) := by
    have := ((GlobalTheory.GaugeWhole.gauge_whole n₀ ε₀).1 c hc).2.2.2
    simpa [IsRadial] using this
  haveI : SigmaFinite (Formalism.REAL.muG ε₀) := by
    unfold Formalism.REAL.muG
    infer_instance
  have hP := _root_.GlobalTheory.LeviIso.isRadial_pi a (fun i => Fin (j i) → Fin (j i) → ℂ)
    (fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)) _ (fun i => 2 * j i ^ 2)
    (fun i => measurable_hs_loc (j i)) (fun i x => add_nonneg (hs_nonneg' _) (hs_nonneg' _))
    (fun i => GlobalTheory.T.hasEuclideanBallVolume_haarComplexGL_inverse (j i))
  have h2 := _root_.GlobalTheory.LeviIso.isRadial_prod _ _ _ _ _ _ _ _
    (Finset.measurable_sum _ fun i _ => (measurable_hs_loc (j i)).comp (measurable_pi_apply i))
    (measurable_hs_uMat ε₀)
    (fun x => Finset.sum_nonneg fun i _ => add_nonneg (hs_nonneg' _) (hs_nonneg' _))
    (fun g => hs_nonneg' _) hP hG
  have hd : n₀ ^ 2 + 2 * ∑ i, j i ^ 2 = ∑ i, 2 * j i ^ 2 + n₀ ^ 2 := by
    rw [Finset.mul_sum, add_comm]
  rw [hd]
  have hae1 : ∀ᵐ x ∂(Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)),
      ∀ i, (Matrix.of (x i)).det ≠ 0 := by
    refine ae_all_iff.2 fun i => ?_
    have h0 : ∀ᵐ y ∂(haarLoc (j i)), (Matrix.of y).det ≠ 0 := by
      rw [ae_iff]
      simpa using (haarLoc_conj_and_null (j i)).2
    exact (Measure.quasiMeasurePreserving_eval
      (fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)) i).ae (Measure.ae_smul_measure h0 _)
  have hae := (Measure.quasiMeasurePreserving_fst (ν := ENNReal.ofReal c • Formalism.REAL.muG ε₀)).ae hae1
  unfold IsRadial at h2 ⊢
  refine h2.congr fun r => ?_
  rw [Measure.map_apply hθ (measurableSet_le (measurable_hs_uMat ε).sqrt measurable_const)]
  congr 1
  refine measure_congr ?_
  filter_upwards [hae] with z hz
  have e := hs_lev_sub_one n n₀ a j ε ε₀ B B₀ hF (fun i => Matrix.of (z.1 i)) (uMat z.2)
  rw [← hθe z hz] at e
  exact Iff.of_eq (congrArg (fun t => Real.sqrt t ≤ r) e.symm)

end GlobalTheory.LeviIso.MapRadial
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupSigmaFiniteUnique
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeSubHaar

open Topology

open MeasureTheory NumberField Matrix Finset in
open Topology in
private theorem uMat_one_flag_measures {n : ℕ} {ε : Fin n → Bool} : _root_.Formalism.MainNotions.S.uMat (1 : _root_.Formalism.REAL.UJ ε) = 1 := by
  have h1 := _root_.GlobalTheory.GaugeSubLoc.uMat_mul (1 : _root_.Formalism.REAL.UJ ε) 1
  have h2 := _root_.GlobalTheory.GaugeSubLoc.uMat_mul_inv (1 : _root_.Formalism.REAL.UJ ε)
  rw [mul_one] at h1
  rw [inv_one, ← h1] at h2
  exact h2

open MeasureTheory NumberField Matrix Finset in
open Topology in
private theorem comap_subtype_val_haar_properties {n : ℕ} {ε : Fin n → Bool}
    (S : Subgroup (_root_.Formalism.REAL.UJ ε)) (hS : IsClosed (S : Set (_root_.Formalism.REAL.UJ ε))) (d : ℕ)
    (μ : Measure (_root_.Formalism.REAL.UJ ε)) (h : _root_.GlobalTheory.FlagMeas.IsGaugeSub (S : Set (_root_.Formalism.REAL.UJ ε)) d μ) :
    Measure.map (Subtype.val : S → _root_.Formalism.REAL.UJ ε) (μ.comap Subtype.val) = μ ∧
      (μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε)).IsMulLeftInvariant ∧
      IsFiniteMeasureOnCompacts (μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε)) ∧
      μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε) ≠ 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hme : MeasurableEmbedding (Subtype.val : S → _root_.Formalism.REAL.UJ ε) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  set ν := μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε) with hν
  have hmap : Measure.map Subtype.val ν = μ := by
    rw [hme.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 h1)
  have hinv : ν.IsMulLeftInvariant := by
    refine ⟨fun s => ?_⟩
    have key : Measure.map Subtype.val (Measure.map (s * ·) ν) = Measure.map Subtype.val ν := by
      rw [Measure.map_map hme.measurable (measurable_const_mul s)]
      have hcomp : (Subtype.val ∘ (s * ·)) =
          (fun g : _root_.Formalism.REAL.UJ ε => (s : _root_.Formalism.REAL.UJ ε) * g) ∘ Subtype.val := by
        funext x; rfl
      rw [hcomp, ← Measure.map_map (measurable_const_mul _) hme.measurable, hmap]
      exact h2 s s.2
    have := congrArg (Measure.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε)) key
    rwa [hme.comap_map, hme.comap_map] at this
  set f : _root_.Formalism.REAL.UJ ε → ℝ := fun g => √(_root_.Formalism.REAL.hs (_root_.Formalism.MainNotions.S.uMat g - 1)) with hfdef
  have hf : Continuous f := by
    simp only [hfdef, _root_.Formalism.REAL.hs]
    have := _root_.GlobalTheory.GaugeConst.continuous_uMat ε
    fun_prop
  have hf1 : f 1 = 0 := by simp [hfdef, _root_.Formalism.REAL.hs, uMat_one_flag_measures]
  revert h3
  change Filter.Tendsto _ _ (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) → _
  intro h3
  have hL0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hLtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hev := (h3.eventually (isOpen_Ioo.mem_nhds ⟨pos_iff_ne_zero.2 hL0, lt_top_iff_ne_top.2 hLtop⟩)).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)
  obtain ⟨r, ⟨hpos, htop⟩, hr⟩ := hev.exists
  set B := {g | f g ≤ r} with hBdef
  have hB0 : μ B ≠ 0 := by
    intro h0
    change 0 < μ B / _ at hpos
    rw [h0, ENNReal.zero_div] at hpos
    exact lt_irrefl _ hpos
  have hBtop : μ B ≠ ⊤ := by
    intro h0
    change μ B / _ < ⊤ at htop
    rw [h0, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at htop
    exact lt_irrefl _ htop
  have hνB : ν (Subtype.val ⁻¹' B) = μ B := by rw [← hme.map_apply, hmap]
  refine ⟨hmap, hinv, ?_, ?_⟩
  · refine ⟨fun K hK => ?_⟩
    have hUo : IsOpen (Subtype.val ⁻¹' {g | f g < r} : Set S) :=
      (isOpen_lt hf continuous_const).preimage continuous_subtype_val
    have hUne : (Subtype.val ⁻¹' {g | f g < r} : Set S).Nonempty :=
      ⟨1, by simp only [Set.mem_preimage, Set.mem_setOf_eq, OneMemClass.coe_one, hf1]; exact hr⟩
    have hUtop : ν (Subtype.val ⁻¹' {g | f g < r}) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono (Set.preimage_mono
        (show {g | f g < r} ⊆ B from fun g (hg : f g < r) => (le_of_lt hg : f g ≤ r))))
      rw [hνB]; exact hBtop
    exact measure_lt_top_of_isCompact_of_isMulLeftInvariant _ hUo hUne hUtop hK
  · intro h0
    apply hB0
    rw [← hνB, h0, Measure.coe_zero, Pi.zero_apply]


open MeasureTheory NumberField Matrix Finset in
open Topology in
theorem _root_.GlobalTheory.GaugeSubHaar.isGaugeSub_haar : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (_root_.Formalism.REAL.UJ ε)), IsClosed (S : Set (_root_.Formalism.REAL.UJ ε)) → ∀ (d : ℕ) (μ : Measure (_root_.Formalism.REAL.UJ ε)), _root_.GlobalTheory.FlagMeas.IsGaugeSub (S : Set (_root_.Formalism.REAL.UJ ε)) d μ → SigmaFinite μ ∧ IsFiniteMeasureOnCompacts μ ∧ ∀ μ', _root_.GlobalTheory.FlagMeas.IsGaugeSub (S : Set (_root_.Formalism.REAL.UJ ε)) d μ' → μ' = μ := by
  intro n ε S hS d μ hμ
  have hme : MeasurableEmbedding (Subtype.val : S → _root_.Formalism.REAL.UJ ε) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  obtain ⟨hmap, hinv, hfin, hne⟩ := comap_subtype_val_haar_properties S hS d μ hμ
  set ν := μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε) with hν
  have hfinμ : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => by
    rw [← hmap, hme.map_apply]
    exact (hS.isClosedEmbedding_subtypeVal.isCompact_preimage hK).measure_lt_top⟩
  haveI : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (_root_.Formalism.REAL.UJ ε) := inferInstance
  haveI : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  refine ⟨inferInstance, hfinμ, fun μ' hμ' => ?_⟩
  obtain ⟨hmap', hinv', hfin', -⟩ := comap_subtype_val_haar_properties S hS d μ' hμ'
  set ν' := μ'.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε) with hν'
  have hcover : ∃ k, ν (compactCovering S k) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    rw [← Measure.measure_univ_eq_zero, ← iUnion_compactCovering]
    exact measure_iUnion_null hcon
  obtain ⟨k, hk⟩ := hcover
  haveI : ν.IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact _ (isCompact_compactCovering S k) hk
  haveI : ν.IsHaarMeasure := { }
  have hsmul := Measure.isMulLeftInvariant_eq_smul ν' ν
  set c := ν'.haarScalarFactor ν with hc
  have hμc : μ' = c • μ := by
    rw [← hmap', hsmul, Measure.map_smul c hme.measurable.aemeasurable, hmap]
  obtain ⟨-, -, h3⟩ := hμ
  obtain ⟨-, -, h3'⟩ := hμ'
  rw [hμc] at h3'
  revert h3 h3'
  change Filter.Tendsto _ _ (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) →
    Filter.Tendsto _ _ (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) → _
  intro h3 h3'
  have hL0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hLtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have h4 := ENNReal.Tendsto.const_mul h3 (Or.inr (ENNReal.coe_ne_top (r := c)))
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_div_assoc] at h3'
  have heq := tendsto_nhds_unique h4 h3'
  have hc1 : (c : ENNReal) = 1 := by
    rw [← ENNReal.mul_left_inj hL0 hLtop, one_mul]
    exact heq
  rw [hμc, ENNReal.coe_eq_one.1 hc1, one_smul]

end GlobalTheory.GaugeSubHaar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUpUniMul
section
namespace GlobalTheory.UpperUnipotentMulFlagMeasures

theorem isUpUni_mul {N : ℕ} {K : Type} [inst : Field K] {A B : Matrix (Fin N) (Fin N) K}
    (hA : Formalism.MainNotions.S.IsUpUni A) (hB : Formalism.MainNotions.S.IsUpUni B) : Formalism.MainNotions.S.IsUpUni (A * B) := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [(hA i k).1 hk, zero_mul]
    · rw [(hB k j).1 (lt_of_lt_of_le hji hk), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hA i i).2 rfl, (hB i i).2 rfl, mul_one]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hA i k).1 h, zero_mul]
      · rw [(hB k i).1 h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

end GlobalTheory.UpperUnipotentMulFlagMeasures
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalScalarEqOneAtPlaceOverTypePrimes
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HL

theorem GCoord.c_eq_one_of_gS_mem : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) {T T' : D.host.E} (F00 : LFlag (D.sp.Y 0) D.R.rS T) (F'0 : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS) (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → G.c (below D P) = 1 := by
  intro D X Y T T' F00 F'0 FP G c P hP
  set p : PlF D := below D P with hp
  have hmem : ∀ n : ℕ, ((n : 𝓞 D.host.F) ∈ p.asIdeal ↔ ((n : 𝓞 D.host.E)) ∈ P.asIdeal) := by
    intro n
    show (n : 𝓞 D.host.F) ∈ Ideal.comap _ P.asIdeal ↔ _
    rw [Ideal.mem_comap, map_natCast]
  have hg : ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
    have h1 : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := (hmem _).2 hP
    simp only [Formalism.MainNotions.S.Lat.gS, Nat.cast_mul] at h1
    rcases p.isPrime.mem_or_mem h1 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hg
  have hchar : Loc.resChar p = D.host.g i := by
    have hz : ((D.host.g i : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
      exact hi
    have hd : ringChar (𝓞 D.host.F ⧸ p.asIdeal) ∣ D.host.g i := ringChar.dvd hz
    exact (Nat.prime_dvd_prime_iff_eq (D.s.atP p).ellPrime.out (D.host.g_prime i)).1 hd
  have hgp : gpart p = D.host.g i := by
    have hne := D.host.g_ne
    fin_cases i
    · simp [gpart, hchar]
    · simp [gpart, hchar, Ne.symm hne]
  have hδ := Y.δ_pin p i hi
  have hne : ∀ j, ((D.host.g j : ℕ) : D.host.E) ≠ 0 := fun j => Nat.cast_ne_zero.2 (D.host.g_prime j).ne_zero
  have hneF : ∀ j, ((D.host.g j : ℕ) : D.host.F) ≠ 0 := fun j => Nat.cast_ne_zero.2 (D.host.g_prime j).ne_zero
  have key := c.c_eq p
  have hone : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((G.c p).val) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep 1 := by
    rw [key]
    change algebraMap _ _ (Y.δ p) * _ = _
    rw [hδ, ← (D.s.atP p).compat, ← map_mul, map_one]
    have h1 : algebraMap D.host.F D.host.E ((D.host.g 0 : D.host.F) * D.host.g 1 / D.host.g i) *
        ((uP p : ℚ) : D.host.E) = 1 := by
      simp only [uP, hgp, Formalism.MainNotions.S.Lat.gS, map_div₀, map_mul, map_natCast]
      push_cast
      have := hne 0; have := hne 1; have := hne i
      field_simp
    rw [h1, map_one]
  haveI : Nontrivial (D.s.atP p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  have hv : ((G.c p).val : (D.s.atP p).Fp) = 1 :=
    (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective hone
  exact Units.ext hv

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalScalarMulEqDifferentGenMulTheta
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

theorem GCoord.c_mul_gS_eq_delta_theta : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → gS D ≠ 0 ∧ ∀ p, (G.c p : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) * (gS D : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) = (show ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp from Y.δ p) * (G.S p).th := by
  intro D X Y u u' _ _ w F00 F'0 FP _ _ _ G c t₀ ρ U U' _
  have hg : gS D ≠ 0 := by
    show D.host.g 0 * D.host.g 1 ≠ 0
    exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  refine ⟨hg, fun p => ?_⟩

  have hE : ((gS D : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr hg
  haveI : Nontrivial (D.s.atP p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  let cp : (D.s.atP p).Fp := (G.c p).val
  have hc : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep cp =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Y.δ p) * (D.s.atP p).ιE (uP p : D.host.E) := c.c_eq p
  have hu : ((uP p : ℚ) : D.host.E) * ((gS D : ℕ) : D.host.E) = ((gpart p : ℕ) : D.host.E) := by
    rw [uP, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, div_mul_cancel₀ _ hE]
  have h1 : cp * ((gS D : ℕ) : (D.s.atP p).Fp) = (Y.δ p) * ((gpart p : ℕ) : (D.s.atP p).Fp) := by
    apply (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective
    rw [map_mul, map_mul, map_natCast, map_natCast, hc, mul_assoc]
    congr 1
    rw [← map_natCast (D.s.atP p).ιE, ← map_natCast (D.s.atP p).ιE, ← map_mul, hu]

  have h2 : ((G.S p).th : (D.s.atP p).Fp) = ((gpart p : ℕ) : (D.s.atP p).Fp) := by
    have hA := (Y.agree p).2.2.2.2.2
    have hs := D.s_split p
    have wc := c.c p
    rcases hM : (Y.M p).split with _ | g <;> rcases hD : (D.s.atP p).split with _ | sg
    ·
      have hgg : (G.S p).gg = false := wc.gg_none hM
      have hn : Loc.resChar p ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
        rw [← hs, hD]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      have hgp : gpart p = 1 := by unfold gpart; rw [if_neg hn.1, if_neg hn.2]
      rw [Frames.th, hgg, hgp]
      exact (if_neg (by decide)).trans Nat.cast_one.symm
    · simp [hM, hD] at hA
    · simp [hM, hD] at hA
    · have hgs := wc.gg_some g hM
      simp only [hM, hD] at hA
      have hn : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
        rw [← hs, hD]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      have hq := sg.q_eq
      have hgp : gpart p = Loc.resChar p := by
        unfold gpart
        rcases hn with h | h
        · rw [if_pos h, h]
        · by_cases h0 : Loc.resChar p = D.host.g 0
          · rw [if_pos h0, h0]
          · rw [if_neg h0, if_pos h, h]
      simp only [Frames.th, hgs.1, if_true, hgs.2, hA.2, hgp]
      exact hq
  exact h1.trans (congrArg (Y.δ p * ·) h2.symm)

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedRowLatticeTermIsLattice
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

theorem isLattice_map_equiv {E : Type} [Field E] [NumberField E] {V W : Type} [AddCommGroup V] [Module E V]
    [AddCommGroup W] [Module E W] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (e : V ≃ₗ[E] W) (Λ : Submodule (𝓞 E) V) (hΛ : Submodule.IsLattice E Λ) :
    Submodule.IsLattice E (Λ.map (((e : V →ₗ[E] W)).restrictScalars (𝓞 E))) := by
  exact Submodule.IsLattice.of_fg E (hΛ.fg.map _)

theorem term_lat_isLattice : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (t : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V), Submodule.IsLattice D.host.E (c.lat ρ t.lam) := by
  intro D X Y u u' Z T T' F0 F0' FP G c t ρ
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hL : Submodule.IsLattice D.host.E t.lam := hrow.1.1.toIsLattice
  exact isLattice_map_equiv (ρ.trans c.e) t.lam hL

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularMulInvSuperdiagonalSumSub
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem unitriangular_mul_superdiagonal_add {E : Type} [Field E] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) E)
    (hX0 : ∀ i j, j < i → X i j = 0) (hX1 : ∀ i, X i i = 1)
    (hY0 : ∀ i j, j < i → Y i j = 0) (hY1 : ∀ i, Y i i = 1) :
    (∀ i j, j < i → (X * Y) i j = 0) ∧ (∀ i, (X * Y) i i = 1) ∧
    (∀ (a : Fin n) (h : a.val + 1 < n), (X * Y) a ⟨a.val + 1, h⟩ = X a ⟨a.val + 1, h⟩ + Y a ⟨a.val + 1, h⟩) := by
  refine ⟨fun i j hij => ?_, fun i => ?_, fun a h => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rcases lt_or_ge k i with hk | hk
    · rw [hX0 i k hk, zero_mul]
    · rw [hY0 k j (lt_of_lt_of_le hij hk), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [hX1, hY1]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · rw [hX0 i k hk, zero_mul]
      · rw [hY0 k i hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  · set b : Fin n := ⟨a.val + 1, h⟩ with hb
    have hab : a ≠ b := by
      intro e; have := congrArg Fin.val e; simp [hb] at this
    rw [Matrix.mul_apply, Fintype.sum_eq_add a b hab]
    · rw [hX1, hY1, one_mul, mul_one, add_comm]
    · rintro k ⟨hka, hkb⟩
      rcases lt_or_ge k a with hk | hk
      · rw [hX0 a k hk, zero_mul]
      · have hk' : a.val < k.val := lt_of_le_of_ne hk (fun e => hka (Fin.ext e.symm))
        have hk'' : b.val < k.val := by
          have : k.val ≠ a.val + 1 := fun e => hkb (Fin.ext (by simp [hb, e]))
          simp [hb]; omega
        rw [hY0 k b hk'', mul_zero]

theorem unitri_mul_inv_sgUp : ∀ {E : Type} [Field E] {n : ℕ} (B C : Matrix (Fin n) (Fin n) E), (∀ i j, j < i → B i j = 0) → (∀ i, B i i = 1) → (∀ i j, j < i → C i j = 0) → (∀ i, C i i = 1) → (∀ i j, j < i → (B * C⁻¹) i j = 0) ∧ (∀ i, (B * C⁻¹) i i = 1) ∧ Formalism.L2.SG.PairVal.sgUp (B * C⁻¹) = Formalism.L2.SG.PairVal.sgUp B - Formalism.L2.SG.PairVal.sgUp C := by
  intro E _ n B C hB0 hB1 hC0 hC1
  obtain ⟨hD0, hD1⟩ := Formalism.L2.SG.TermLoc.inv_unitri C hC0 hC1
  obtain ⟨hP0, hP1, hP2⟩ := unitriangular_mul_superdiagonal_add B C⁻¹ hB0 hB1 hD0 hD1
  obtain ⟨-, -, hQ2⟩ := unitriangular_mul_superdiagonal_add C C⁻¹ hC0 hC1 hD0 hD1
  have hdet : IsUnit C.det := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hC0 i j hij)]; simp [hC1]
  have hCC : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hdet
  refine ⟨hP0, hP1, ?_⟩
  unfold Formalism.L2.SG.PairVal.sgUp
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs with h
  · have hq := hQ2 a h
    rw [hCC, Matrix.one_apply_ne] at hq
    · rw [hP2 a h]; linear_combination -hq
    · intro e; have := congrArg Fin.val e; simp at this
  · simp

end GlobalTheory
end

