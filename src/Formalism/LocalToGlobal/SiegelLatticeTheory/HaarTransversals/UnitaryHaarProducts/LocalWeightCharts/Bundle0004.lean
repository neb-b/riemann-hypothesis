module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.InstLocallyCompactSpace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.UnitMulStar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NotMidCases
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.OpnContinuous
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ANonzeroOf
section
noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas
open scoped ENNReal InnerProductSpace

namespace WlocSk.ANz

variable {k r : ℕ}

theorem haarG_pos {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hμ : IsHaarOn (Gr k r) μG) {U : Set (Mat k r)}
    (hU : IsOpen U) {x : Mat k r} (hxU : x ∈ U) (hxG : x ∈ Gr k r) :
    0 < μG {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ U ∩ Gr k r} := by
  obtain ⟨c, hc0, -, hμeq⟩ := WlocSk.HM.haar_unique (Gr k r) WlocSk.HM.uh_clsub μG hμ
  have hVm : MeasurableSet {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ U ∩ Gr k r} :=
    (hU.preimage WlocSk.Grp.continuous_of).measurableSet.inter
      (WlocSk.Grp.isClosed_Gr.preimage WlocSk.Grp.continuous_of).measurableSet
  have hvt : Continuous (WlocSk.HM.Grp.vt :
      WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub → Formalism.QuantumDeterminants.Mt k r) := WlocSk.HM.Grp.embt.continuous
  have hO : IsOpen ((fun a => Matrix.of (WlocSk.HM.Grp.vt a)) ⁻¹' U :
      Set (WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub)) :=
    hU.preimage (WlocSk.Grp.continuous_of.comp hvt)
  have hne : ((fun a => Matrix.of (WlocSk.HM.Grp.vt a)) ⁻¹' U :
      Set (WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub)).Nonempty :=
    ⟨WlocSk.HM.Grp.mk x hxG, hxU⟩
  have hpos := hO.measure_pos (Measure.haar : Measure (WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub)) hne
  rw [hμeq, Measure.smul_apply, smul_eq_mul, WlocSk.HM.hmeas, Measure.map_apply hvt.measurable hVm]
  refine ENNReal.mul_pos hc0 (ne_of_gt (lt_of_lt_of_le hpos (measure_mono ?_)))
  intro a ha
  exact ⟨ha, WlocSk.HM.Grp.mem a⟩

theorem aNonzero_of (hSG : SGrp) (hPU : PiUnit) (hSP : SProd) (hAE : AEquiv) (hAC : ACont) :
    ANonzero := by
  intro hNV k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp hR hCW
  obtain ⟨hset, hDS, hHC, hLU, hG, -, -, hW, hN, -, -⟩ := id hyp
  obtain ⟨hk1, hev, hz, hT, hc, hu, hl, hI, hH2, hGB⟩ := hset
  have hk2 : 2 ≤ k := by obtain ⟨m, hm⟩ := hev; omega
  obtain ⟨x, x₀, hx, hx₀, hne⟩ :=
    hNV k r z c u v b hk2 hev hz hT hc hu hl hI hH2 hGB H σ hDS Vp π hHC w hLU μW μN hW hN
  have hFi : Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ * star (psiGen k r z c (Matrix.of p.2))) •
        π (Matrix.of p.1)⁻¹) (μW.prod μN) := by
    by_contra hni
    exact hne (integral_undef hni)
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Vp, (∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ * star (psiGen k r z c (Matrix.of p.2))) •
        π (Matrix.of p.1)⁻¹ ∂(μW.prod μN)) ξ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (ContinuousLinearMap.ext hall)
  rw [ContinuousLinearMap.integral_apply hFi] at hξ
  set A := Af z c σ π μW μN w x₀ ξ with hAdef
  have hAx : A x ≠ 0 := hξ
  have hcont : ContinuousOn A (Gr k r) :=
    hAC k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
  have hequiv : IsSPsiEquiv z (psiGen k r z c) π A :=
    hAE k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
  obtain ⟨hWG, hNG, -, hNg, -⟩ := hSG k r z c hz hT
  have hπ := (hPU k r z u Vp π hz hT hHC).2

  have hApos : 0 < ‖A x‖ := norm_pos_iff.mpr hAx
  obtain ⟨ε, hε, hεlt⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < ‖A x‖ := ⟨‖A x‖ / 2, half_pos hApos, half_lt_self hApos⟩
  have hevn : ∀ᶠ y in nhdsWithin x (Gr k r), ε < ‖A y‖ :=
    (hcont x hx).norm.eventually (lt_mem_nhds hεlt)
  obtain ⟨U, hUo, hxU, hUsub⟩ := mem_nhdsWithin.mp hevn

  set V : Set (Formalism.QuantumDeterminants.Mt k r) := {y | Matrix.of y ∈ U ∩ Gr k r} with hVdef
  have hVm : MeasurableSet V :=
    (hUo.preimage WlocSk.Grp.continuous_of).measurableSet.inter
      (WlocSk.Grp.isClosed_Gr.preimage WlocSk.Grp.continuous_of).measurableSet
  have hμV : 0 < μG V := haarG_pos hG hUo hxU hx

  obtain ⟨cS, hcS0, -, hunf⟩ := unfold_of hSP hyp
  have hfm : Measurable (V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)) := measurable_one.indicator hVm
  have := hW.1
  have := hN.1
  set g : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun x => ∫⁻ p, V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
      (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) with hgdef
  have hU' : ∫⁻ x, g x ∂ν = cS * μG V := by
    have h := hunf _ hfm
    rw [lintegral_indicator_one hVm] at h
    exact h
  have hjoint : Measurable (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (fun i j => (Matrix.of (mulP q.2) * Matrix.of q.1) i j)) := by
    refine hfm.comp (Continuous.measurable ?_)
    exact (WlocSk.Grp.continuous_of.comp (continuous_mulP.comp continuous_snd)).matrix_mul
      (WlocSk.Grp.continuous_of.comp continuous_fst)
  have hgm : Measurable g := hjoint.lintegral_prod_right'
  set P : Set (Formalism.QuantumDeterminants.Mt k r) := {x | 0 < g x} with hPdef
  have hPm : MeasurableSet P := measurableSet_lt measurable_const hgm
  have hPpos : ν P ≠ 0 := by
    intro h0
    have hae : ∀ᵐ x ∂ν, g x = 0 := by
      refine ae_iff.mpr (measure_mono_null (fun x hx => ?_) h0)
      exact pos_iff_ne_zero.mpr hx
    have h1 : ∫⁻ x, g x ∂ν = 0 := by rw [lintegral_congr_ae hae, lintegral_zero]
    rw [h1] at hU'
    exact (ENNReal.mul_pos hcS0 hμV.ne').ne' hU'.symm

  have hTae : ∀ᵐ p ∂(μW.prod μN),
      Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
    have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z :=
      Measure.quasiMeasurePreserving_fst.ae (ae_iff.mpr hW.2.2.1)
    have h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
      Measure.quasiMeasurePreserving_snd.ae (ae_iff.mpr hN.2.2.1)
    filter_upwards [h1, h2] with p hp1 hp2
    exact ⟨hp1, hp2⟩

  have key : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ Gr k r → 0 < g x → ε < ‖A (Matrix.of x)‖ := by
    intro x hxG hgx
    by_contra hle
    apply hgx.ne'
    have hae : ∀ᵐ p ∂(μW.prod μN), V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
        (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) = 0 := by
      filter_upwards [hTae] with p hp
      apply Set.indicator_of_notMem
      intro hpV
      have h1 : ε < ‖A (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ := hUsub hpV
      have h2 : ‖A (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ = ‖A (Matrix.of x)‖ := by
        rw [hequiv _ hp.1 _ hp.2 _ hxG, norm_smul, (hNg _ hp.2 _ hp.2).2.2.2.2, hπ _ hp.1, one_mul]
      exact hle (h2 ▸ h1)
    show ∫⁻ p, V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
        (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) = 0
    rw [lintegral_congr_ae hae, lintegral_zero]
  have hνG : ∀ᵐ x ∂ν, Matrix.of x ∈ Gr k r := ae_iff.mpr (nu_conc_of hSG hyp)
  have hlow : ∀ᵐ x ∂ν, P.indicator (fun _ => ENNReal.ofReal ε ^ 2) x ≤
      (‖A (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [hνG] with x hxG
    by_cases hxP : x ∈ P
    · rw [Set.indicator_of_mem hxP]
      have hb : ENNReal.ofReal ε ≤ (‖A (Matrix.of x)‖₊ : ℝ≥0∞) := by
        refine ENNReal.ofReal_le_of_le_toReal ?_
        rw [ENNReal.coe_toReal, coe_nnnorm]
        exact (key x hxG hxP).le
      gcongr
    · rw [Set.indicator_of_notMem hxP]
      exact bot_le
  refine ⟨x₀, hx₀, ξ, fun hzero => ?_⟩
  have hmono : ∫⁻ x, P.indicator (fun _ => ENNReal.ofReal ε ^ 2) x ∂ν ≤
      ∫⁻ x, (‖A (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν := lintegral_mono_ae hlow
  have hz' : ∫⁻ x, (‖A (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν = 0 := hzero
  rw [lintegral_indicator_const hPm, hz'] at hmono
  have hne0 : ENNReal.ofReal ε ^ 2 * ν P ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hε).ne') hPpos
  exact hne0 (le_zero_iff.mp hmono)

end WlocSk.ANz
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.DecayR
section
noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas Matrix
open scoped InnerProductSpace ENNReal

namespace WlocSk.DecayR

lemma opn_conj {n : ℕ} {P g : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Formalism.L2.SG.WuDecay.opn (P⁻¹ * g * P) = Formalism.L2.SG.WuDecay.opn g := by
  unfold Formalism.L2.SG.WuDecay.opn
  have h1 : star P * P = 1 := by
    first
      | exact Unitary.star_mul_self_of_mem hP
      | exact unitary.star_mul_self_of_mem hP
  have h2 : P * star P = 1 := by
    first
      | exact Unitary.mul_star_self_of_mem hP
      | exact unitary.mul_star_self_of_mem hP
  have hPinv : P⁻¹ = star P := Matrix.inv_eq_left_inv h1
  have hU1 : star (Matrix.toEuclideanCLM (𝕜 := ℂ) P) * Matrix.toEuclideanCLM (𝕜 := ℂ) P = 1 := by
    rw [← map_star, ← map_mul, h1, map_one]
  have hU2 : Matrix.toEuclideanCLM (𝕜 := ℂ) P * star (Matrix.toEuclideanCLM (𝕜 := ℂ) P) = 1 := by
    rw [← map_star, ← map_mul, h2, map_one]
  have hU : Matrix.toEuclideanCLM (𝕜 := ℂ) P ∈ unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    ⟨hU1, hU2⟩
  have hUs : star (Matrix.toEuclideanCLM (𝕜 := ℂ) P) ∈
      unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := by
    refine ⟨?_, ?_⟩
    · rw [star_star]
      exact hU2
    · rw [star_star]
      exact hU1
  rw [hPinv, map_mul, map_mul, map_star, CStarRing.norm_mul_mem_unitary _ hU,
    CStarRing.norm_mem_unitary_mul _ hUs]

variable {k r : ℕ}

lemma transport {ε : Fin (2 * r + k + 1) → Bool} {P' : Mat k r} (hP' : IsCayleyU k r ε P')
    {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : IsHaarOn (Gr k r) μG) :
    ∃ cc : ℝ≥0∞, cc ≠ 0 ∧ cc ≠ ⊤ ∧ μG = (cc • PI.UpqRep.muG ε).map (Port.conjPrime₂ ε P') := by
  have : SigmaFinite μG := hG.1
  have hPJ' : P'ᴴ * PI.UpqRep.Jm ε * P' = PI.UpqRep.Hpk k r := hP'.1.2
  have hconc : μG {x | Matrix.of x ∉ PI.UpqRep.UH (P'ᴴ * PI.UpqRep.Jm ε * P')} = 0 := by
    rw [hPJ']; exact hG.2.2.1
  have hinv : ∀ s ∈ PI.UpqRep.UH (P'ᴴ * PI.UpqRep.Jm ε * P'),
      μG.map (fun x => Matrix.of.symm (s * Matrix.of x)) = μG := by
    rw [hPJ']; intro s hs; exact hG.2.2.2 s hs
  exact Port.haar_transport ε P' hP'.1.1 μG hG.2.1 hconc hinv

theorem decay_estimate : WlocSk.Decay := by
  intro hCW k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp
  obtain ⟨hS, hσ, _, hw, hG, _⟩ := hyp
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨P', hP', hLow⟩ := hw
  have hDS' := OneP.isDS_cayley hP hP' hDS
  obtain ⟨_, _, _, _, _, _, hHC, _, _, hGap⟩ := hS
  have hC := hCW k r v b hHC hGap H (fun g => σ (P'⁻¹ * g * P')) hDS' w hLow
  obtain ⟨cc, _, hctop, hμ⟩ := transport hP' hG
  have hE := Port.conjP_measurableEmbedding (eps48 k r) P' hP'.1.1
  rw [hμ, hE.lintegral_map, lintegral_smul_measure]
  refine ENNReal.mul_lt_top hctop.lt_top (lt_of_eq_of_lt (lintegral_congr fun g => ?_) hC)
  show ‖⟪w, σ (P'⁻¹ * uMat g * P') w⟫_ℂ‖ₑ *
      ENNReal.ofReal (Formalism.L2.SG.WuDecay.opn (P'⁻¹ * uMat g * P') ^ N1H k r) =
    ‖⟪w, σ (P'⁻¹ * uMat g * P') w⟫_ℂ‖ₑ *
      ENNReal.ofReal (‖Matrix.toEuclideanCLM (𝕜 := ℂ) (uMat g)‖ ^
        (4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt (2 * ((r + 1 : ℕ) : ℝ))))
  rw [opn_conj hP'.2]
  rfl

theorem reproducing_formula_holds : WlocSk.ReprodG := by
  intro hR k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp
  obtain ⟨_, hσ, _, hw, hG, _⟩ := hyp
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨P', hP', hLow⟩ := hw
  have hDS' := OneP.isDS_cayley hP hP' hDS
  obtain ⟨α', Ω', a', hΩc, hαm, hαs, hαb, hαi, hαe⟩ :=
    hR _ (eps48 k r) (lam48 k r v b) H (fun g => σ (P'⁻¹ * g * P')) hDS' w hLow.2
  obtain ⟨cc, hc0, hctop, hμ⟩ := transport hP' hG
  have hE := Port.conjP_measurableEmbedding (eps48 k r) P' hP'.1.1
  have hct : 0 < cc.toReal := ENNReal.toReal_pos hc0 hctop
  set ψ := Port.conjPrime₂ (eps48 k r) P' with hψ
  set f : Formalism.REAL.UJ (eps48 k r) → ℂ := fun g => (cc.toReal⁻¹ : ℝ) • α' g with hf
  set α : Mat k r → ℂ := fun y => Function.extend ψ f (fun _ => 0) (Matrix.of.symm y) with hα
  have hαψ : ∀ g, α (Matrix.of (ψ g)) = f g := fun g => hE.injective.extend_apply _ _ g
  have hcase : ∀ y : Mat k r, α y ≠ 0 → ∃ g, ψ g = Matrix.of.symm y ∧ α y = f g := by
    intro y hy
    by_cases h : ∃ g, ψ g = Matrix.of.symm y
    · obtain ⟨g, hg⟩ := h
      refine ⟨g, hg, ?_⟩
      show Function.extend ψ f (fun _ => 0) (Matrix.of.symm y) = f g
      rw [← hg]; exact hE.injective.extend_apply _ _ g
    · exact absurd (Function.extend_apply' f (fun _ => (0 : ℂ)) _ h) hy
  have hcont : Continuous fun g : Formalism.REAL.UJ (eps48 k r) => P'⁻¹ * uMat g * P' :=
    (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul
      continuous_const
  have hinv := OneP.unit_inv hP'.2
  have h1 := OneP.unit_star_mul hP'.2
  have h2 := OneP.unit_mul_star hP'.2
  refine ⟨α, (fun g => P'⁻¹ * uMat g * P') '' Ω', cc.toReal⁻¹ * max a' 0, hΩc.image hcont, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rintro _ ⟨g, _, rfl⟩
    have hg : (uMat g)ᴴ * Formalism.REAL.Jm (eps48 k r) * uMat g = Formalism.REAL.Jm (eps48 k r) := g.2
    show (P'⁻¹ * uMat g * P')ᴴ * Formalism.QuantumDeterminants.Hpk k r * (P'⁻¹ * uMat g * P') = Formalism.QuantumDeterminants.Hpk k r
    rw [← hP'.1.2, hinv]
    calc (P'ᴴ * uMat g * P')ᴴ * (P'ᴴ * Formalism.REAL.Jm (eps48 k r) * P') * (P'ᴴ * uMat g * P')
        = P'ᴴ * (uMat g)ᴴ * (P' * P'ᴴ) * Formalism.REAL.Jm (eps48 k r) * (P' * P'ᴴ) * uMat g * P' := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = P'ᴴ * ((uMat g)ᴴ * Formalism.REAL.Jm (eps48 k r) * uMat g) * P' := by
          rw [h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = P'ᴴ * Formalism.REAL.Jm (eps48 k r) * P' := by rw [hg]
  · have hfm : Measurable f := hαm.const_smul (cc.toReal⁻¹ : ℝ)
    exact hE.measurable_extend hfm measurable_const
  · intro y hy
    obtain ⟨g, hg, hyg⟩ := hcase y hy
    have hg0 : α' g ≠ 0 := by
      intro h0; apply hy; rw [hyg, hf]; simp [h0]
    refine ⟨g, hαs g hg0, ?_⟩
    rw [← Matrix.of.apply_symm_apply y, ← hg]
    rfl
  · intro y
    have hcn : 0 ≤ cc.toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
    by_cases hy : α y = 0
    · rw [hy, norm_zero]; exact mul_nonneg hcn (le_max_right _ _)
    · obtain ⟨g, _, hyg⟩ := hcase y hy
      rw [hyg, hf]
      simp only
      rw [norm_smul, Real.norm_of_nonneg hcn]
      exact mul_le_mul_of_nonneg_left ((hαb g).trans (le_max_left _ _)) hcn
  · have hfun : (fun x : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of x) • σ (Matrix.of x) w) ∘ ψ =
        fun g => (cc.toReal⁻¹ : ℝ) • (α' g • σ (P'⁻¹ * uMat g * P') w) := by
      funext g
      simp only [Function.comp]
      rw [hαψ, hf, smul_assoc]
      rfl
    rw [hμ, hE.integrable_map_iff, hfun]
    exact (hαi.smul_measure hctop).smul _
  · have hfun : (fun x : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of x) • σ (Matrix.of x) w) ∘ ψ =
        fun g => (cc.toReal⁻¹ : ℝ) • (α' g • σ (P'⁻¹ * uMat g * P') w) := by
      funext g
      simp only [Function.comp]
      rw [hαψ, hf, smul_assoc]
      rfl
    rw [hμ, hE.integral_map, integral_smul_measure]
    have hpt : ∀ x, α (Matrix.of (ψ x)) • σ (Matrix.of (ψ x)) w =
        (cc.toReal⁻¹ : ℝ) • (α' x • σ (P'⁻¹ * uMat x * P') w) := fun x => congrFun hfun x
    simp_rw [hpt]
    rw [integral_smul]
    have he : ∫ g, α' g • σ (P'⁻¹ * uMat g * P') w ∂(PI.UpqRep.muG (eps48 k r)) = w := hαe
    rw [he, smul_smul, mul_inv_cancel₀ hct.ne', one_smul]

end WlocSk.DecayR

section Check
end Check
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.HaarWN
section
noncomputable section

open MeasureTheory

namespace WlocSk

open HM

theorem uw_finite {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) : IsFiniteMeasure (hmeas (Formalism.QuantumDeterminants.UWset k r z) (uw_clsub z)) := by
  have : CompactSpace (Grp (Formalism.QuantumDeterminants.UWset k r z : Set (Mx k r)) (uw_clsub z)) :=
    isCompact_iff_compactSpace.mp (compactW z hz hT)
  refine ⟨?_⟩
  unfold hmeas
  rw [Measure.map_apply (val_cemb _ _).continuous.measurable MeasurableSet.univ, Set.preimage_univ]
  exact isCompact_univ.measure_lt_top

theorem haar_measure_unipotent_nilradical : HaarWN := by
  intro k r z hz hT
  exact ⟨hmeas (Formalism.QuantumDeterminants.UWset k r z) (uw_clsub z), haarNm k r, hmeas_haar _ _, haarNm_haar,
    uw_finite z hz hT, haarNm_compact⟩

end WlocSk
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilradicalHaarUnique
section
noncomputable section

open MeasureTheory Formalism.MainNotions.S
open scoped ENNReal

namespace WlocSk

theorem nilradical_haar_unique : NUniq := by
  intro k r μ μ' hμ hμ'
  obtain ⟨c, hc0, hct, hc⟩ := HM.n_unique μ hμ
  obtain ⟨c', hc0', hct', hc'⟩ := HM.n_unique μ' hμ'
  refine ⟨c / c', ENNReal.div_ne_top hct hc0', ?_⟩
  rw [hc, hc', smul_smul, ENNReal.div_mul_cancel hc0' hct']

end WlocSk
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.SubgroupHypothesisHolds
section
open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S WlocSk.UnitaryGroupBasics

noncomputable section

theorem subgroup_hypothesis_holds : WlocSk.SGrp := by
  intro k r z c hz _
  refine ⟨fun h hh => hh.1, fun m hm => hm.1, ?_, ?_, ?_⟩
  · intro h hh h' hh'
    exact ⟨uw_mul hh hh', uw_inv hh, Matrix.mul_nonsing_inv _ (isUnit_of_uh hh.1)⟩
  · intro m hm m' hm'
    exact ⟨mem_n_mul hm hm', mem_n_inv hm, Matrix.mul_nonsing_inv _ (isUnit_of_uh hm.1),
      psiGen_mul z c hz hm hm', psiGen_norm z c m⟩
  · intro h hh m hm
    exact ⟨uw_conj_mem hh hm, psiGen_conj z c hh⟩
end
end

