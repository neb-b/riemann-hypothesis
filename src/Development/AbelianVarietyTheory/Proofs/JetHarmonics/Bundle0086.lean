module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0082
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0046
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0084

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCayleySideBoundStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_cayley_side_bound : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (Q : Mx k r) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∀ g ∈ GG k r, ∀ (a : Fin r) (w : R.smSub), (lenA k r z g a.succ / lenA k r z g a.castSucc) ^ 2 * ‖l (R.σ g w)‖ ^ 2 ≤ ∑ c, ∑ e, ‖l (R.σ g (E c e w))‖ ^ 2 := by
  first | exact @GlobalTheory.MomentPointwise.pointwise | exact GlobalTheory.MomentPointwise.pointwise | (intros; apply GlobalTheory.MomentPointwise.pointwise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFormalDegreePairing
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besPhInt_bilin {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (X X' : Wq →L[ℂ] Wp) :
    ∃ T : (Wp →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wq) →L[ℂ] ℂ, ∀ P Q, T P Q = B.hsInner (P.comp (X.comp Q)) X' := by
  refine ⟨∑ i, ((ContinuousLinearMap.compL ℂ (Wq →L[ℂ] Wq) Wp ℂ (innerSL ℂ (X' (stdOrthonormalBasis ℂ Wq i)))).comp
    ((ContinuousLinearMap.compL ℂ (Wq →L[ℂ] Wq) Wp Wp).flip
      (X.comp (ContinuousLinearMap.apply ℂ Wq (stdOrthonormalBasis ℂ Wq i))))), fun P Q => ?_⟩
  simp [B.hsInner, B.hsVec, PiLp.inner_apply]

theorem besPhInt_rank {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (X X' : Wq →L[ℂ] Wp)
    (a a' : Wp) (b b' : Wq) :
    B.hsInner (((innerSL ℂ a).smulRight a').comp (X.comp ((innerSL ℂ b').smulRight b))) X' =
      ⟪a, X b⟫_ℂ * star ⟪a', X' b'⟫_ℂ := by
  have hb : X' b' = ∑ i, ⟪stdOrthonormalBasis ℂ Wq i, b'⟫_ℂ • X' (stdOrthonormalBasis ℂ Wq i) := by
    conv_lhs => rw [← (stdOrthonormalBasis ℂ Wq).sum_repr' b']
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have h2 : star ⟪a', X' b'⟫_ℂ = ⟪X' b', a'⟫_ℂ := inner_conj_symm _ _
  rw [h2, hb, sum_inner, Finset.mul_sum]
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_smul,
    inner_smul_right, inner_smul_left, inner_conj_symm]
  ring

theorem besPhInt_xi {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r) :
    B.xiTau D (1, 1) p = Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of p.1.2) *
      star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd (Matrix.of p.2.2)) := by
  unfold B.xiTau Formalism.QuantumDeterminants.psi B.lam
  rw [show ∀ x : ℂ, star x = (starRingEnd ℂ) x from fun _ => rfl, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem besPhInt_xi_cont {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) :
    Continuous (B.xiTau D (1, 1)) := by
  have h : ∀ z, Continuous (fun m : Formalism.QuantumDeterminants.Mt k r => Formalism.QuantumDeterminants.ell k r z (Matrix.of m)) := by
    intro z
    unfold Formalism.QuantumDeterminants.ell
    refine continuous_finsetSum _ fun a _ => ?_
    split_ifs
    · simp only [Matrix.of_apply]
      fun_prop
    · simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
      fun_prop
  have h1 := (h D.z).comp (continuous_snd.comp (continuous_fst (X := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (Y := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)))
  have h2 := (h D.z').comp (continuous_snd.comp (continuous_snd (X := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (Y := Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)))
  unfold B.xiTau B.lam
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact (continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul h1))).sub
    (continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul h2)))

theorem integral_xi_mul_Ph : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ x' ∈ R.TK, ∀ y' ∈ R.TK, ∀ X X' : Wq →L[ℂ] Wp, Integrable (B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X')) D.μSS ∧ ∫ p, B.xiTau D (1, 1) p * B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p ∂D.μSS = ⟪l x, X (l' y)⟫_ℂ * star ⟪l x', X' (l' y')⟫_ℂ / (dd : ℂ) := by
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' dd hDS _ _ hl hl' hdd x hx y hy x' hx' y' hy' X X'
  obtain ⟨hmul, hone, hinn, -, hTK, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS
  have hsf : ∀ {U : Set (B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}, B.IsHaarOn U μ → SigmaFinite μ := by
    intro U μ h
    have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    infer_instance
  haveI := hsf D.haarW
  haveI := hsf D.haarN
  haveI := hsf D.haarW'
  have hN := (_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r D.μN).2.1.2 D.haarN
  have hW := ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r D.μW).2.2 D.z D.z_mem D.T_pos D.k_pos).2 D.haarW
  have hW' := ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r D.μW').2.2 D.z' D.z'_mem D.T'_pos D.k_pos).2 D.haarW'
  obtain ⟨-, -, -, -, mA, aeA⟩ := _root_.GlobalTheory.sParam_measurePreserving k r D.z D.μW D.μN D.k_pos D.z_mem D.T_pos hW hN
  obtain ⟨-, -, -, mB, -, aeB⟩ := _root_.GlobalTheory.sParam_measurePreserving k r D.z' D.μW' D.μN D.k_pos D.z'_mem D.T'_pos hW' hN
  obtain ⟨psn, -, psinv, -, -, -⟩ := _root_.GlobalTheory.BesselPsi.psi_character k r D.z Formalism.QuantumDeterminants.cStd D.z_mem
  obtain ⟨psn', -, -, pscj, -, -⟩ := _root_.GlobalTheory.BesselPsi.psi_character k r D.z' Formalism.QuantumDeterminants.cStd D.z'_mem
  obtain ⟨iA, eA⟩ := hl.2 x' (hTK x' hx') x hx
  obtain ⟨iB, eB⟩ := hl'.2 y (hTK y hy) y' hy'
  have iA' := mA.integrable_comp_of_integrable iA
  have iB' := mB.integrable_comp_of_integrable iB
  have eA' := integral_map mA.measurable.aemeasurable (mA.map_eq.symm ▸ iA.aestronglyMeasurable)
  have eB' := integral_map mB.measurable.aemeasurable (mB.map_eq.symm ▸ iB.aestronglyMeasurable)
  rw [mA.map_eq] at eA'
  rw [mB.map_eq] at eB'
  unfold be at eA eB
  rw [eA] at eA'
  rw [eB] at eB'
  obtain ⟨T, hT⟩ := besPhInt_bilin X X'
  have hI := integral_prod_bilin T iA' iB'
  have hInt := iA'.op_fst_snd (op := fun P Q => T P Q) (by fun_prop) ⟨‖T‖, T.le_opNorm₂⟩ iB'
  simp only [Function.comp_apply] at hI hInt
  rw [← eA', ← eB', hT, besPhInt_rank] at hI
  have hae : ∀ᵐ p ∂D.μSS, D.inSS p := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN)).ae aeA,
      (Measure.quasiMeasurePreserving_snd (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN)).ae aeB] with p h1 h2
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  have key : ∀ p : B.SS k r, D.inSS p →
      B.xiTau D (1, 1) p * B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p =
      T (beInt D.z Formalism.QuantumDeterminants.cStd D.π R.σ x' x
          (((fun i j => ((Matrix.of p.1.1)⁻¹ : Mx k r) i j), (fun i j => ((Matrix.of p.1.2)⁻¹ : Mx k r) i j))))
        (beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y y'
          (((fun i j => (Matrix.of p.2.1 : Mx k r) i j),
            (fun i j => ((Matrix.of p.2.1)⁻¹ * Matrix.of p.2.2 * Matrix.of p.2.1 : Mx k r) i j)))) / (dd : ℂ) := by
    intro p hp
    rw [(GlobalTheory.T.bessel_formal_degree_identity hH k r ε mu R Wp Wq D dd hDS hdd x y x' y' X X' p hp).2, besPhInt_xi, ← hT]
    obtain ⟨h1, h2, h3, h4⟩ := hp
    have hof : ∀ M : Mx k r, Matrix.of (fun i j => M i j) = M := fun M => rfl
    unfold beInt JF.sL JF.sR
    simp only [hof]
    generalize Matrix.of p.1.1 = a at *
    generalize Matrix.of p.1.2 = n at *
    generalize Matrix.of p.2.1 = a' at *
    generalize Matrix.of p.2.2 = n' at *
    obtain ⟨ai, aa, aa'⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv h1.1
    obtain ⟨ni, nn, nn'⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv h2.1
    obtain ⟨bi, bb, bb'⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv h3.1
    have e1 : a⁻¹⁻¹ = a := Matrix.inv_eq_right_inv aa'
    have e2 : a' * (a'⁻¹ * n' * a') = n' * a' := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, bb, Matrix.one_mul]
    have e3 : ⟪x, R.σ (a⁻¹ * n⁻¹) x'⟫_ℂ = ⟪R.σ (n * a) x, x'⟫_ℂ := by
      have hna := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul h2.1 h1.1
      have hna' := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul ai ni
      rw [← hinn _ hna, ← hmul _ hna _ hna']
      have : n * a * (a⁻¹ * n⁻¹) = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc a, aa, Matrix.one_mul, nn]
      rw [this, hone]
    rw [e1, e2, e3, (psinv n h2).2, (pscj a' h3 n' h4).2.2.2, star_star]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hae' := hae.mono key
  have hInt' : Integrable (fun p => B.xiTau D (1, 1) p *
      B.Ph D (fun g => ⟪x, R.σ g y⟫_ℂ • X) (fun g => ⟪x', R.σ g y'⟫_ℂ • X') p) D.μSS :=
    (hInt.div_const (dd : ℂ)).congr (hae'.mono fun p hp => hp.symm)
  have hn : ∀ p, ‖B.xiTau D (1, 1) p‖ = 1 := by
    intro p
    rw [besPhInt_xi, norm_mul, norm_star, psn, psn', one_mul]
  refine ⟨?_, ?_⟩
  · have := hInt'.bdd_mul (c := 1) (f := fun p => star (B.xiTau D (1, 1) p))
      (besPhInt_xi_cont D).star.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by rw [norm_star, hn])
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    have h1 : star (B.xiTau D (1, 1) p) * B.xiTau D (1, 1) p = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hn]; simp
    simp only
    rw [← mul_assoc, h1, one_mul]
  · rw [integral_congr_ae hae', integral_div]
    exact congrArg (· / (dd : ℂ)) hI

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapGrowthBound
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselEquiv

theorem integral_smul_comp_of_measurePreserving {X Wp : Type} [MeasurableSpace X] [NormedAddCommGroup Wp]
    [NormedSpace ℂ Wp] [CompleteSpace Wp] {μ : Measure X} {T : X → X} (hT : MeasurePreserving T μ μ)
    {F F' : X → (Wp →L[ℂ] Wp)} (hF : Integrable F μ) (c : ℂ) (A : Wp →L[ℂ] Wp)
    (h : ∀ᵐ p ∂μ, F' p = c • A.comp (F (T p))) :
    ∫ p, F' p ∂μ = c • A.comp (∫ p, F p ∂μ) := by
  have hFT : Integrable (fun p => F (T p)) μ := hT.integrable_comp_of_integrable hF
  have e1 : ∫ p, F (T p) ∂μ = ∫ p, F p ∂μ := by
    have := integral_map (μ := μ) (φ := T) (f := F) hT.measurable.aemeasurable
      (by rw [hT.map_eq]; exact hF.aestronglyMeasurable)
    rw [hT.map_eq] at this
    exact this.symm
  rw [integral_congr_ae h, integral_smul, ← e1]
  congr 1
  exact (ContinuousLinearMap.compL ℂ Wp Wp Wp A).integral_comp_comm hFT

theorem be_equivariant : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ g ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ (g * m) w) v = Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m • (π g).comp (be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hS v hv w hw g hg m hm
  have hint := (GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS v hv).1 w hw
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, -, -⟩ := hS
  obtain ⟨hψ1, hψm, -, hψc, hUW, hNG⟩ := _root_.GlobalTheory.BesselPsi.psi_character k r z Formalism.QuantumDeterminants.cStd hz
  obtain ⟨hmp, -, -, -, -, hae⟩ := _root_.GlobalTheory.sParam_measurePreserving k r z μW μN hok.1 hz hT hW hN
  have hσ := (GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS).1
  have hπm := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ).2.1
  have hGm : ∀ a ∈ GG k r, ∀ b ∈ GG k r, a * b ∈ GG k r := by
    intro a ha b hb
    have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
    have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
    show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
    calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [ha', hb']
  unfold be
  refine integral_smul_comp_of_measurePreserving (hmp g hg m hm).1 hint _ _ ?_
  filter_upwards [hae] with p hp
  obtain ⟨ha, hn⟩ := hp
  have key : ∀ a ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r,
      (⟪v, R.σ (a * n) (R.σ (g * m) w)⟫_ℂ * star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd n)) • π a⁻¹ =
      Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m • (π g).comp
        ((⟪v, R.σ (a * g * (g⁻¹ * n * g * m)) w⟫_ℂ *
          star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (g⁻¹ * n * g * m))) • π (a * g)⁻¹) := by
    intro a ha n hn
    obtain ⟨hag, -, haG⟩ := hUW a ha g hg
    have hgG := (hUW g hg g hg).2.2
    obtain ⟨-, hgg, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hg
    obtain ⟨hagi, -, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hag
    obtain ⟨-, hc, -, hcψ⟩ := hψc g hg n hn
    have e1 : a * g * (g⁻¹ * n * g * m) = a * n * (g * m) := by
      calc a * g * (g⁻¹ * n * g * m) = a * (g * g⁻¹) * n * (g * m) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hgg, Matrix.mul_one]
    have e2 : g * (a * g)⁻¹ = a⁻¹ := by
      rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, hgg, Matrix.one_mul]
    have e3 : Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m * star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd m) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ1 m]; simp
    rw [e1, hσ _ (hGm a haG n (hNG n hn)) _ (hGm g hgG m (hNG m hm)), (hψm _ hc m hm).2, hcψ,
      ContinuousLinearMap.comp_smul, ← hπm g hg _ hagi, e2, smul_smul, star_mul']
    congr 1
    linear_combination (-(⟪v, R.σ (a * n) (R.σ (g * m) w)⟫_ℂ * star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd n))) * e3
  exact key _ ha _ hn

end GlobalTheory.BesselEquiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapPairing
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besselIntegral_sesquilinear : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → (∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ w' ∈ R.sm, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (w + w') v = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w' v ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (a • w) v = a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK, ∀ v' ∈ R.TK, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (v + v') = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v' ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (a • v) = star a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v := by
  intro H k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq h1 h2 h3 h4
  have hc := GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap H k r ε mu h R Wp z π u μW μN μG νq h1 h2 h3 h4
  refine ⟨fun v hv w hw w' hw' a => ⟨?_, ?_⟩, fun w hw v hv v' hv' a => ⟨?_, ?_⟩⟩
  · unfold be
    rw [← integral_add ((hc v hv).1 w hw) ((hc v hv).1 w' hw')]
    congr 1
    funext p
    simp [beInt, add_mul, add_smul]
  · unfold be
    rw [← integral_smul]
    congr 1
    funext p
    simp [beInt, smul_smul, mul_assoc]
  · unfold be
    rw [← integral_add ((hc v hv).1 w hw) ((hc v' hv').1 w hw)]
    congr 1
    funext p
    simp [beInt, add_mul, add_smul]
  · unfold be
    rw [← integral_smul]
    congr 1
    funext p
    simp [beInt, smul_smul, mul_assoc, mul_left_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselPeriodAdjointPairStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (l : R.H → Wp) (l' : R.H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsCoef R l l' F s → B.CkOn ⊤ (B.GV k r) F ∧ ∀ m : ℕ, B.InCC (aOf r h - 1) m F := by
  first | exact @GlobalTheory.isCoef_ckOn_inCC | exact GlobalTheory.isCoef_ckOn_inCC | (intros; apply GlobalTheory.isCoef_ckOn_inCC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingGapBoundDual
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besselInner_haar {k r : ℕ} {U : Set (Mx k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} (h : B.IsHaarOn U μ) :
    PI.BesselPeriodGGP.IsHaarOn U μ :=
  ⟨Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite h, h.ne_zero, h.conc, h.left⟩

theorem besselInner_integral {k r : ℕ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    (D : B.RealPlaceData k r Wp Wq)
    (hmul : ∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v))
    (huni : ∀ g ∈ GG k r, ∀ v w, ⟪R.σ g v, R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ)
    {γ : Mx k r} (hγ : γ ∈ GG k r) (x y : R.H) (X : Wq →L[ℂ] Wp)
    (a : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (ha1 : Matrix.of a.1 ∈ GG k r) (ha2 : Matrix.of a.2 ∈ GG k r)
    (hint : Integrable (beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y (R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x))
      (D.μW'.prod D.μN)) :
    ∫ b, JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ (a, b) ∂(D.μW'.prod D.μN) =
      Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of a.2) • (D.π (Matrix.of a.1)).comp (X.comp
        (be D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ D.μW' D.μN y (R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x))) := by
  obtain ⟨-, -, -, hT, -, hae⟩ := _root_.GlobalTheory.sParam_measurePreserving k r D.z' D.μW' D.μN D.k_pos D.z'_mem D.T'_pos
    (besselInner_haar D.haarW') (besselInner_haar D.haarN)
  obtain ⟨-, -, -, hconj, hW, hN⟩ := _root_.GlobalTheory.BesselPsi.psi_character k r D.z' Formalism.QuantumDeterminants.cStd D.z'_mem
  set v := R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x with hv
  set G := beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y v with hG
  set T : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r := fun p =>
    ((fun i j => (Matrix.of p.1 : Mx k r) i j),
      (fun i j => ((Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1 : Mx k r) i j)) with hTdef
  let L : (Wq →L[ℂ] Wq) →L[ℂ] (Wq →L[ℂ] Wp) :=
    Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of a.2) •
      ContinuousLinearMap.compL ℂ Wq Wq Wp ((D.π (Matrix.of a.1)).comp X)
  have hL : ∀ A, L A = Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of a.2) •
      (D.π (Matrix.of a.1)).comp (X.comp A) := fun A => rfl
  have key : (fun b => JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ (a, b)) =ᵐ[D.μW'.prod D.μN]
      fun b => L (G (T b)) := by
    filter_upwards [hae] with b hb
    obtain ⟨hb1, hb2⟩ := hb
    have hb1G : Matrix.of b.1 ∈ GG k r := (hW _ hb1 _ hb1).2.2
    have hb2G : Matrix.of b.2 ∈ GG k r := hN _ hb2
    have u1 := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh ha1
    have u2 := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh ha2
    have u3 := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hγ
    have u4 := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hb1G
    have hg0 : γ⁻¹ * Matrix.of a.2 * Matrix.of a.1 ∈ GG k r :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hγ) ha2) ha1
    have hs : B.sgs (a, b) γ ∈ GG k r :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul
        (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha1) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha2)) hγ) hb2G) hb1G
    have e1 : (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) * B.sgs (a, b) γ =
        Matrix.of b.1 * ((Matrix.of b.1)⁻¹ * Matrix.of b.2 * Matrix.of b.1) := by
      simp only [B.sgs, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ u1,
        Matrix.mul_nonsing_inv_cancel_left _ _ u2, Matrix.mul_nonsing_inv_cancel_left _ _ u4,
        Matrix.nonsing_inv_mul_cancel_left _ _ u3]
    have e2 : ⟪x, R.σ (B.sgs (a, b) γ) y⟫_ℂ =
        ⟪v, R.σ (Matrix.of b.1 * ((Matrix.of b.1)⁻¹ * Matrix.of b.2 * Matrix.of b.1)) y⟫_ℂ := by
      rw [← e1, hmul _ hg0 _ hs, hv, huni _ hg0]
    have e3 := (hconj _ hb1 _ hb2).2.2.2
    have e4 : G (T b) = (⟪v, R.σ (Matrix.of b.1 * ((Matrix.of b.1)⁻¹ * Matrix.of b.2 * Matrix.of b.1)) y⟫_ℂ *
        star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd ((Matrix.of b.1)⁻¹ * Matrix.of b.2 * Matrix.of b.1))) •
        D.π' (Matrix.of b.1)⁻¹ := rfl
    rw [hL, e4, e3, ← e2]
    ext w
    simp only [JF.integrand, JF.xiP, B.rho, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      map_smul, smul_smul]
    congr 1
    ring
  have hGT : Integrable (fun b => G (T b)) (D.μW'.prod D.μN) := hT.integrable_comp_of_integrable hint
  rw [integral_congr_ae key, L.integral_comp_comm hGT, ← hL]
  congr 1
  have h2 := integral_map hT.aemeasurable (f := G) (by rw [hT.map_eq]; exact hint.aestronglyMeasurable)
  rw [hT.map_eq] at h2
  exact h2.symm

theorem besselJ_coef_through_right : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ Bb : R.H → Wp → Wq → Wp, (∀ x b c (t : ℂ), Bb x (t • b) c = t • Bb x b c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = Bb x (X (l' y)) c := by
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' hDS hgap hOK _ hl' γ hγ
  obtain ⟨hmul, -, huni, -, hsm, hTK, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS
  refine ⟨fun x b c => ∫ a : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of a.2) *
        ⟪l' (R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x), c⟫_ℂ) • D.π (Matrix.of a.1) b ∂(D.μW.prod D.μN), ?_, ?_⟩
  · intro x b c t
    simp only
    rw [← integral_smul]
    congr 1
    funext a
    rw [map_smul, smul_comm]
  intro x hx y hy X c
  have hcoef : IsCoef R l l' (fun g => ⟪x, R.σ g y⟫_ℂ • X) ⟪l x, X (l' y)⟫_ℂ :=
    ⟨1, fun _ => x, fun _ => y, fun _ => X, fun _ => ⟨hx, hy⟩, fun g _ => by simp, by simp⟩
  have hcc := (GlobalTheory.isCoef_ckOn_inCC hH k r ε mu h R Wp Wq l l' _ _ hDS hgap hOK hcoef).2 0
  have hI := (Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq D _ _ (_root_.GlobalTheory.thresholds_of_gapOK k r h hOK).1 hcc).1 γ hγ
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have hJ : B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ =
      ∫ p, JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) := rfl
  have hI' : Integrable (JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ)
      ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) := hI
  rw [hJ, integral_prod _ hI', ContinuousLinearMap.integral_apply hI'.integral_prod_left]
  obtain ⟨-, -, -, -, -, hae⟩ := _root_.GlobalTheory.sParam_measurePreserving k r D.z D.μW D.μN D.k_pos D.z_mem D.T_pos
    (besselInner_haar D.haarW) (besselInner_haar D.haarN)
  obtain ⟨-, -, -, -, hW, hN⟩ := _root_.GlobalTheory.BesselPsi.psi_character k r D.z Formalism.QuantumDeterminants.cStd D.z_mem
  refine integral_congr_ae ?_
  filter_upwards [hae] with a ha
  have ha1 : Matrix.of a.1 ∈ GG k r := (hW _ ha.1 _ ha.1).2.2
  have ha2 : Matrix.of a.2 ∈ GG k r := hN _ ha.2
  have hg0 : γ⁻¹ * Matrix.of a.2 * Matrix.of a.1 ∈ GG k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hγ.1) ha2) ha1
  obtain ⟨hint, hbe⟩ := hl'.2 y (hsm y hy) _ (hTK _ hg0 x hx)
  rw [besselInner_integral R D hmul huni hγ.1 x y X a ha1 ha2 hint, hbe]
  simp [smul_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCayleyWeightedStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_tensor_cayley_weighted : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (ep : Fin (2 * r + k + 1) → ℝ) (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)) (F : ∀ s, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (RI s).smSub), (∀ s, (RI s).IsDS ε (muI s)) → TensH dualM (Formalism.QuantumDeterminants.Hpk k r) R RI io pr ep → PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → (∀ s, (RI s).IsE Q (F s)) → ∃ (io' : ∀ s, (RI s).smSub →ₗ[ℂ] (Fin (2 * r + k + 1) → R.smSub)) (pr' : ∀ s, (Fin (2 * r + k + 1) → R.smSub) →ₗ[ℂ] (RI s).smSub), AlgTens ε E (fun s => (RI s).smSub) F io' pr' ∧ ∀ s x, ((pr' s x : (RI s).smSub) : (RI s).H) = ∑ c, pr s c (∑ d, Q d c • ((x d : R.smSub) : R.H)) := by
  first | exact @GlobalTheory.CayleyTens.algTens_cayley | exact GlobalTheory.CayleyTens.algTens_cayley | (intros; apply GlobalTheory.CayleyTens.algTens_cayley <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLowestKFiniteVectorDiscreteSeriesStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∃ w : R.smSub, ‖w‖ = 1 ∧ R.KFin (w : R.H) ∧ Formalism.REAL.KHighest ε E (Formalism.QuantumDeterminants.lowK ε mu) w ∧ FiniteDimensional ℂ (Formalism.REAL.kSpan ε E w) := by
  first | exact @GlobalTheory.LowestVector.exists_lowest_vector | exact GlobalTheory.LowestVector.exists_lowest_vector | (intros; apply GlobalTheory.LowestVector.exists_lowest_vector <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsometricBesselSideBoundStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (Bm : R.H → Wp), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → (∀ w ∈ R.sm, MemLp (fun x : Formalism.QuantumDeterminants.Mt k r => Bm (R.σ (Matrix.of x) w)) 2 νq) ∧ ∀ w ∈ R.sm, ∀ w' ∈ R.sm, ∫ x, ⟪Bm (R.σ (Matrix.of x) w'), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = ⟪w', w⟫_ℂ := by
  first | exact @GlobalTheory.isoBessel_polarised | exact GlobalTheory.isoBessel_polarised | (intros; apply GlobalTheory.isoBessel_polarised <;> assumption)
end

