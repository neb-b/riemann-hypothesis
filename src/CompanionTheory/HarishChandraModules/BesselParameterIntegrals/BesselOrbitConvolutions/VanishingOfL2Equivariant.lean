module

public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.VanishingOfL2Equivariant

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section
set_option maxHeartbeats 3200000

namespace Formalism.FourierDecayAlt.P

namespace UnipotentHaarMeasurability
open Formalism.FourierDecayAlt.ThreeDimData

namespace G

theorem vanishing_of_L2_equivariant {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)}
    {w0 : H} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hBC : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv) (hIn : CompanionTheory.D.Upq.BesselFunctionalConstruction.Inputs)
    (hS : Side k r ε lam h σ w0 z c u π μW μN μG νq)
    {x : H} (hx : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) {v : H} (hv : IsAdm σ w0 v)
    (hl : ∀ ξ : Wp, PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g x) v ξ) = 0) :
    be z c π σ μW μN x v = 0 := by
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨-, hBC2, hBC3, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  ext ξ
  let K := Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)
  let F : Mx k r → Wp := fun g => be z c π σ μW μN (σ g x) v ξ
  have hc : ContinuousOn F K :=
    (hBC3 x hx v hv).clm_apply continuousOn_const
  have heq : ∀ hh ∈ Formalism.QuantumDeterminants.UWset k r z,
      ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ g ∈ K,
        F (hh * n * g) = Formalism.QuantumDeterminants.psi k r z c n • π hh (F g) := by
    intro hh hhW n hn g hg
    have hhn : hh * n ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hhW.1 hn.1
    have hm : σ (hh * n * g) = (σ (hh * n)).comp (σ g) := TranslationBesselVanishing.sigma_mul hσ hhn hg
    dsimp only [F]
    rw [hm, ContinuousLinearMap.comp_apply,
      hBC2 v hv hh hhW n hn (σ g x) (TranslationBesselVanishing.smooth_translate hσ hx hg)]
    rfl
  classical
  let S : Set (Formalism.QuantumDeterminants.Mt k r) := {g | Matrix.of g ∈ K}
  let G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ :=
    S.indicator fun g => (‖F (Matrix.of g)‖₊ : ℝ≥0∞) ^ 2
  have hSm : MeasurableSet S := uh_meas
  have hGc : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r =>
      (‖F (Matrix.of g)‖₊ : ℝ≥0∞) ^ 2) S :=
    (ENNReal.continuous_pow 2).comp_continuousOn
      ((ENNReal.continuous_coe.comp continuous_nnNorm).comp_continuousOn hc)
  have hGm : Measurable G := hGc.measurable_piecewise continuousOn_const hSm
  have hGzero {g : Formalism.QuantumDeterminants.Mt k r} (hg : g ∈ S) :
      G g = 0 ↔ F (Matrix.of g) = 0 := by
    simp [G, Set.indicator_of_mem hg]
  have hνint : ∫⁻ g, G g ∂νq = 0 := by
    apply nonpos_iff_eq_zero.mp
    calc
      ∫⁻ g, G g ∂νq ≤ PI.BesselPeriodGGP.l2SG νq F :=
        lintegral_mono (Set.indicator_le_self S _)
      _ = 0 := hl ξ
  have hmu := DDSmoothness.muSof_facts hW hN
  have hνS : ∀ᵐ g ∂νq, g ∈ S := DDSmoothness.ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  have := hW.1
  have := hN.1
  have hWae :
      ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 hW.2.2.1)
  have hNae :
      ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (ae_iff.2 hN.2.2.1)
  have hμint : ∫⁻ g, G g ∂μG = 0 := by
    rw [hq G hGm]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hνS, (lintegral_eq_zero_iff hGm).mp hνint] with g hg hg0
    let mulPair (p : Formalism.QuantumDeterminants.Mt k r ×
        Formalism.QuantumDeterminants.Mt k r) : Formalism.QuantumDeterminants.Mt k r :=
      fun i j => (Matrix.of p.1 * Matrix.of p.2) i j
    let mulRight (s : Formalism.QuantumDeterminants.Mt k r) : Formalism.QuantumDeterminants.Mt k r :=
      fun i j => (Matrix.of s * Matrix.of g) i j
    have hmul : Continuous mulPair := continuous_fst.matrix_mul continuous_snd
    have hright : Continuous mulRight := continuous_id.matrix_mul continuous_const
    change (∫⁻ s, (G ∘ mulRight) s ∂Measure.map mulPair (μW.prod μN)) = 0
    rw [lintegral_map (hGm.comp hright.measurable) hmul.measurable]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hWae, hNae] with p hpW hpN
    apply (hGzero (DDSmoothness.uh_mul (DDSmoothness.uh_mul hpW.1 hpN.1) hg)).mpr
    change F (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) = 0
    rw [heq (Matrix.of p.1) hpW (Matrix.of p.2) hpN (Matrix.of g) hg,
      (hGzero hg).mp hg0, map_zero, smul_zero]
  have hμS : ∀ᵐ g ∂μG, g ∈ S := ae_iff.2 hG.2.2.1
  have hμF : ∀ᵐ g ∂μG, F (Matrix.of g) = 0 := by
    filter_upwards [hμS, (lintegral_eq_zero_iff hGm).mp hμint] with g hg hg0
    exact (hGzero hg).mp hg0
  have hF1 : F 1 = 0 := by
    by_contra hne
    obtain ⟨V, hVo, hV⟩ := (continuousOn_iff'.mp hc) {0}ᶜ isOpen_compl_singleton
    have h1V : (1 : Mx k r) ∈ V := by
      have h1 : (1 : Mx k r) ∈ F ⁻¹' {0}ᶜ ∩ K :=
        ⟨hne, Formalism.QuantumDeterminants.WeylGroupFacts.uh_one⟩
      rw [hV] at h1
      exact h1.1
    have hVae : ∀ᵐ g : Formalism.QuantumDeterminants.Mt k r ∂μG, Matrix.of g ∉ V := by
      filter_upwards [hμS, hμF] with g hg hg0 hgV
      have hg' : Matrix.of g ∈ V ∩ K := ⟨hgV, hg⟩
      rw [← hV] at hg'
      exact hg'.1 hg0
    have hVnull : μG (Matrix.of ⁻¹' V) = 0 := by
      change μG {g | Matrix.of g ∈ V} = 0
      simpa only [not_not] using ae_iff.mp hVae
    let O (g : K) : Set (Formalism.QuantumDeterminants.Mt k r) :=
      Formalism.QuantumDeterminants.lmulM (g : Mx k r)⁻¹ ⁻¹' (Matrix.of ⁻¹' V)
    have hlmul (a : Mx k r) : Continuous (Formalism.QuantumDeterminants.lmulM a) :=
      continuous_const.matrix_mul continuous_id
    have hVo' : IsOpen (Matrix.of ⁻¹' V : Set (Formalism.QuantumDeterminants.Mt k r)) :=
      hVo.preimage continuous_id
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable O
      (fun g => hVo'.preimage (hlmul (g : Mx k r)⁻¹))
    have hOnull (g : K) : μG (O g) = 0 := by
      dsimp only [O]
      rw [← Measure.map_apply (hlmul (g : Mx k r)⁻¹).measurable hVo'.measurableSet,
        hG.2.2.2 _ (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv g.2), hVnull]
    have hSnull : μG S = 0 := by
      refine measure_mono_null (t := ⋃ g ∈ T, O g) ?_
        ((measure_biUnion_null_iff hTc).mpr fun g _ => hOnull g)
      intro g hg
      rw [hT]
      refine Set.mem_iUnion.mpr ⟨⟨Matrix.of g, hg⟩, ?_⟩
      change (Matrix.of g)⁻¹ * Matrix.of g ∈ V
      rw [Matrix.nonsing_inv_mul (Matrix.of g)
        (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg)]
      exact h1V
    apply hG.2.1
    rw [← Measure.measure_univ_eq_zero, ← Set.union_compl_self S]
    exact measure_union_null hSnull hG.2.2.1
  have hσ1 : σ 1 = 1 := by
    obtain ⟨P, hP, hD⟩ := hσ
    have hPu := Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.mp hP.2)
    simpa [Matrix.nonsing_inv_mul P hPu] using hD.2.2.1.1.1
  simpa [F, hσ1] using hF1

theorem zeroCaseDD_of (hBC : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv) (hNI : CompanionTheory.D.Upq.BesselFunctionalConstruction.NormIdSm) (hSch : SchurH) : CompanionTheory.D.Upq.BesselFunctionalConstruction.ZeroCaseDD := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hDD v hv x hx
  refine vanishing_of_L2_equivariant hBC hIn hS hx (Or.inl hv) (fun ξ => ?_)
  rw [(hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v (Or.inl hv) ξ).1, hDD v hv v hv]
  simp

theorem zeroCase_of (hBC : CompanionTheory.D.Upq.BesselFunctionalConstruction.BeConv) (hNI : CompanionTheory.D.Upq.BesselFunctionalConstruction.NormIdSm) (hSch : SchurH) : CompanionTheory.D.Upq.BesselFunctionalConstruction.ZeroCase := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hDD v hv x hx
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  have hA := zeroCaseDD_of hBC hNI hSch hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hDD
  have hvs : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := hIn.2.2.1 k r ε lam H σ hlam hσ v hv

  have hB : ∀ u ∈ DDsp σ w0, be z c π σ μW μN u v = 0 := by
    intro u hu
    have h1 : be z c π σ μW μN v u = 0 := hA u hu v hvs
    have h2 := (hBC4 u hu v (Or.inr hv)).2
    rw [h1] at h2
    have h3 := congrArg ContinuousLinearMap.adjoint h2
    rwa [ContinuousLinearMap.adjoint_adjoint, map_zero] at h3

  have hw0n : ‖w0‖ = 1 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    exact hn1
  have hw0ne : w0 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hw0n; exact zero_ne_one hw0n
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hdeg : PI.BesselPeriodGGP.fdegH μG σ w0 = d := DDSmoothness.fdeg_eq hd hSd hw0ne
  have hw0DD : w0 ∈ DDsp σ w0 := by
    refine Submodule.subset_span ⟨1, Formalism.QuantumDeterminants.WeylGroupFacts.uh_one, ?_⟩
    have hσ1 : σ 1 = 1 := by
      obtain ⟨P, hP, hD⟩ := hσ
      have hPu := Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.mp hP.2)
      simpa [Matrix.nonsing_inv_mul P hPu] using hD.2.2.1.1.1
    simp [hσ1]
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := DDSmoothness.DD_smooth hIn.2.2.1 hlam hσ hw0 w0 hw0DD
  have hmu := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  have hC : ∀ ξ : Wp, ⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ = 0 := by
    intro ξ
    obtain ⟨hNv, him, hre⟩ := hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS w0 hw0s v (Or.inr hv) ξ
    have hL : PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g w0) v ξ) = 0 := by
      unfold PI.BesselPeriodGGP.l2SG
      refine (lintegral_congr_ae (hae.mono fun g hg => ?_)).trans lintegral_zero
      have hgD : σ (Matrix.of g) w0 ∈ DDsp σ w0 := Submodule.subset_span ⟨Matrix.of g, hg, rfl⟩
      simp [hB _ hgD]
    rw [hL, hdeg, hw0n] at hNv
    have h0 : 1 ^ 2 * (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).re / d ≤ 0 := ENNReal.ofReal_eq_zero.mp hNv.symm
    have hre0 : (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).re = 0 := by
      have : (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).re ≤ 0 := by
        rw [one_pow, one_mul] at h0
        exact (div_nonpos_iff.mp h0).elim (fun h => absurd h.2 (not_le.mpr hd)) (fun h => h.1)
      linarith
    exact Complex.ext hre0 him
  have hvv : be z c π σ μW μN v v = 0 := by
    have hlin : (be z c π σ μW μN v v : Wp →ₗ[ℂ] Wp) = 0 := by
      rw [← inner_map_self_eq_zero]
      intro ξ
      rw [← inner_conj_symm]
      simp [hC ξ]
    ext ξ
    have := LinearMap.congr_fun hlin ξ
    simpa using this

  refine vanishing_of_L2_equivariant hBC hIn hS hx (Or.inr hv) (fun ξ => ?_)
  rw [(hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v (Or.inr hv) ξ).1, hvv]
  simp

end G

end UnipotentHaarMeasurability

end Formalism.FourierDecayAlt.P

end
