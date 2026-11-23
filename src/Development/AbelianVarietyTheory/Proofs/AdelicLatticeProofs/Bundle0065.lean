module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.FockCompare
open scoped TensorProduct ContDiff Topology Pointwise

namespace GlobalTheory.OrientedHeis

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem taylor_bound {φ φ' φ'' : ℝ → ℂ} (h1 : ∀ s, HasDerivAt φ (φ' s) s) (h2 : ∀ s, HasDerivAt φ' (φ'' s) s) {C : ℝ}
    (hC : ∀ s, ‖φ'' s‖ ≤ C) {t : ℝ} (ht : 0 < t) : ‖(t : ℂ)⁻¹ * (φ t - φ 0) - φ' 0‖ ≤ C * t := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have a : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖φ' s - φ' 0‖ ≤ C * (s - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (fun s _ => (h2 s).hasDerivWithinAt) fun s _ => hC s
  have d : ∀ s : ℝ, HasDerivAt (fun s : ℝ => φ s - (s : ℂ) * φ' 0) (φ' s - φ' 0) s := fun s => by
    have := (h1 s).sub ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (φ' 0))
    rw [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] at this
    exact this
  have b := norm_image_sub_le_of_norm_deriv_le_segment' (C := C * t) (a := 0) (b := t)
    (fun s _ => (d s).hasDerivWithinAt) (fun s hs => (a s ⟨hs.1, hs.2.le⟩).trans
      (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hC0)) t ⟨ht.le, le_rfl⟩
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  have e : (t : ℂ)⁻¹ * (φ t - φ 0) - φ' 0 = (t : ℂ)⁻¹ * (φ t - t * φ' 0 - (φ 0 - ((0 : ℝ) : ℂ) * φ' 0)) := by
    field_simp
    simp
    ring
  rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht.le, inv_mul_le_iff₀ ht]
  linarith

theorem eq_zero_of_lintegral_eq_zero {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure]
    (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (f : G → ℂ) (hf : Continuous f)
    (hp : ∀ γ ∈ Γ, ∀ w, ‖f (γ + w)‖ = ‖f w‖) (h0 : ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = 0) : f = 0 := by
  have ho : IsOpen {w | f w ≠ 0} := isOpen_ne_fun hf continuous_const
  have h1 := (lintegral_eq_zero_iff (hf.measurable.enorm.pow_const 2)).1 h0
  have h2 : μ ({w | f w ≠ 0} ∩ 𝓕) = 0 := by
    rw [← Measure.restrict_apply ho.measurableSet]
    refine measure_mono_null (fun w hw => ?_) h1
    simpa using hw
  have h3 := h𝓕.measure_zero_of_invariant _ (fun γ => by
    ext w
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    show f (((-γ : Γ) : G) + w) ≠ 0 ↔ f w ≠ 0
    rw [← norm_ne_zero_iff, hp _ (-γ).2, norm_ne_zero_iff]) h2
  have h4 := (ho.measure_eq_zero_iff μ).1 h3
  funext w
  by_contra hw
  exact (Set.eq_empty_iff_forall_notMem.1 h4) w hw

theorem lintegral_eq_zero_of_approx {G : Type} [MeasurableSpace G] (ν : Measure G) (hν : ν Set.univ = 1) (δ : G → ℂ)
    (C C' : ℝ) (h : ∀ t : ℝ, 0 < t → ∃ a b r : G → ℂ, δ = a - b ∧ ∫⁻ w, ‖a w‖ₑ ^ 2 ∂ν = ∫⁻ w, ‖r w‖ₑ ^ 2 ∂ν ∧
      (∀ w, ‖r w‖ ≤ C * t) ∧ ∀ w, ‖b w‖ ≤ C' * t) : ∫⁻ w, ‖δ w‖ₑ ^ 2 ∂ν = 0 := by
  have en : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have key : ∀ t : ℝ, 0 < t → ∫⁻ w, ‖δ w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (2 * (C * t) ^ 2 + 2 * (C' * t) ^ 2) := by
    intro t ht
    obtain ⟨a, b, r, e, h1, h2, h3⟩ := h t ht
    have h4 : ∫⁻ w, ‖r w‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal ((C * t) ^ 2) := by
      refine (lintegral_mono (g := fun _ => ENNReal.ofReal ((C * t) ^ 2)) fun w => ?_).trans ?_
      · show ‖r w‖ₑ ^ 2 ≤ _
        rw [en]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (h2 w) 2)
      · rw [lintegral_const, hν, mul_one]
    calc ∫⁻ w, ‖δ w‖ₑ ^ 2 ∂ν ≤ ∫⁻ w, (2 * ‖a w‖ₑ ^ 2 + ENNReal.ofReal (2 * (C' * t) ^ 2)) ∂ν := by
          refine lintegral_mono fun w => ?_
          show ‖δ w‖ₑ ^ 2 ≤ 2 * ‖a w‖ₑ ^ 2 + ENNReal.ofReal (2 * (C' * t) ^ 2)
          rw [en, en, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h5 : ‖δ w‖ ≤ ‖a w‖ + ‖b w‖ := by rw [e]; exact norm_sub_le _ _
          have h6 := pow_le_pow_left₀ (norm_nonneg _) h5 2
          have h7 := pow_le_pow_left₀ (norm_nonneg _) (h3 w) 2
          nlinarith [sq_nonneg (‖a w‖ - ‖b w‖)]
      _ = 2 * ∫⁻ w, ‖a w‖ₑ ^ 2 ∂ν + ENNReal.ofReal (2 * (C' * t) ^ 2) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num), lintegral_const, hν, mul_one]
      _ ≤ 2 * ENNReal.ofReal ((C * t) ^ 2) + ENNReal.ofReal (2 * (C' * t) ^ 2) := by
          rw [h1]; gcongr
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (p := 2) (q := (C * t) ^ 2) (by norm_num),
            ENNReal.ofReal_ofNat]
  have hc : Continuous fun t : ℝ => ENNReal.ofReal (2 * (C * t) ^ 2 + 2 * (C' * t) ^ 2) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, ENNReal.ofReal_zero] at ht
  exact le_antisymm (ge_of_tendsto ht (eventually_nhdsWithin_of_forall key)) bot_le

variable {D : D7} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem theta_norm_periodic (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
  rintro _ ⟨γ, rfl⟩ w
  have := congrArg norm (hf.quasi γ w)
  rw [norm_mul, hψ.1.2.1, one_mul] at this
  exact this

theorem theta_bounded (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun w => ?_⟩
  obtain ⟨γ, hγ, h⟩ := hc w
  rw [← theta_norm_periodic hψ hf γ hγ w]
  exact hC _ h

theorem heisO_zero (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  have h : symplOH S T w 0 = 0 := by
    have := symplOH_add_right w 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  unfold heisO
  rw [h, AddChar.map_zero_eq_one, one_mul, add_zero]

theorem quotient_bound (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WO S T} (hL : IsRealDir T S L)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ w,
      ‖((t : ℂ)⁻¹ • (heisO ψ S T (L t) f - f) - dLine ψ S T L f) w‖ ≤ C * t := by
  have h1 := theta_dLine hθ hψ hL hf
  obtain ⟨C, hC⟩ := theta_bounded hψ (theta_dLine hθ hψ hL h1)
  refine ⟨C, fun t ht w => ?_⟩
  have := taylor_bound (hasDerivAt_heisO hθ hψ hL hf w) (hasDerivAt_heisO hθ hψ hL h1 w) (C := C) (fun s => by
    unfold heisO
    rw [norm_mul, hψ.1.2.1, one_mul]
    exact hC _) ht
  rw [L.map_zero, heisO_zero, heisO_zero] at this
  exact this

variable {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_dLine (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T)
    {L L' : ℝ →+ WO S T} (hL : IsRealDir T S L) (hL' : IsRealDir T S L') (hLL : ∀ t, L' t = actO S T g h (L t))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (dLine ψ S T L f) = dLine ψ S T L' (om (g, h) f) := by
  have hψ := hom.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WA T S) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, h1⟩, -⟩ := GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WA T S) (ratL T S) K hK hc
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hf' := hom.om_pres (g, h) f hf
  have hδ := theta_sub (theta_dLine hθ hψ hL' hf') (hom.om_pres (g, h) _ (theta_dLine hθ hψ hL hf))
  obtain ⟨C, hC⟩ := quotient_bound hθ hψ hL hf
  obtain ⟨C', hC'⟩ := quotient_bound hθ hψ hL' hf'
  refine (sub_eq_zero.1 (eq_zero_of_lintegral_eq_zero (G := WA T S) (ratL T S) μ 𝓕 h𝓕 _ hδ.cont
    (theta_norm_periodic hψ hδ) ?_)).symm
  refine lintegral_eq_zero_of_approx (μ.restrict 𝓕) (by rw [Measure.restrict_apply_univ, h1]) _ C C' fun t ht => ?_
  have theta_smul_local (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
      IsThetaFunO ψ S T (c • f) := by
    refine ⟨?_, ?_, hf.cont.const_smul c, ?_⟩
    · intro γ w
      rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
    ·
      obtain ⟨U, hU, h1⟩ := hf.level
      refine ⟨U, hU, fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu h0) w
      unfold heisO at e1 ⊢
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
    · intro k L h1 h2 w
      exact contDiff_const.mul (hf.smooth k L h1 h2 w)
  have hr := theta_sub (theta_smul_local (t : ℂ)⁻¹ (theta_sub (theta_heisO_real hθ hψ (hL.2 t) hf) hf))
    (theta_dLine hθ hψ hL hf)
  refine ⟨_, _, _, ?_, hom.om_unit μ 𝓕 hμ h𝓕 (g, h) _ hr, hC t ht, hC' t ht⟩
  rw [map_sub, map_smul, map_sub, hom.om_heis g h _ f hf, hLL]
  abel

theorem isLineAt_lineAt (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) :
    IsLineAt θ τ z (lineAt θ τ z) :=
  Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)

theorem isRealDir_lineAt (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    IsRealDir T S (lineAt θ τ z) := ⟨(isLineAt_lineAt hθ τ z).1, (isLineAt_lineAt hθ τ z).2.1⟩

theorem compAt_mul (τ : D.what₂.Tau) {k m n : ℕ} (x : Mx D k m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D k n) = compAt θ τ x * compAt θ τ y :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_mt_mul_inv (τ : D.what₂.Tau) (g : GA D S) : compAt θ τ (mt S g) * compAt θ τ (mt S g⁻¹) = 1 := by
  have e : mt S g * mt S g⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  rw [← compAt_mul]
  erw [e]
  exact Matrix.map_one _ (((θ τ).comp (infPart D)).map_zero) (((θ τ).comp (infPart D)).map_one)

theorem lineAt_move (hθ : IsInfFam θ) (g : GA D S) (h : GA D T) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    lineAt θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) t = actO S T g h (lineAt θ τ z t) := by
  have hL := isLineAt_lineAt hθ τ z
  let L : ℝ →+ WO S T :=
    { toFun := fun t => actO S T g h (lineAt θ τ z t)
      map_zero' := by unfold actO; rw [AddMonoidHom.map_zero, Matrix.mul_zero, Matrix.zero_mul]
      map_add' := fun s t => by unfold actO; rw [AddMonoidHom.map_add (f := _), Matrix.mul_add, Matrix.add_mul] }
  have hL' : IsLineAt θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) L := by
    refine ⟨(continuous_const.matrix_mul hL.1).matrix_mul continuous_const, fun t => ?_, fun t τ' => ?_⟩
    · show (actO S T g h (lineAt θ τ z t)).map (finPart D) = 0
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, hL.2.1, Matrix.mul_zero, Matrix.zero_mul]
    · show compAt θ τ' (actO S T g h (lineAt θ τ z t)) = _
      unfold actO
      rw [compAt_mul, compAt_mul, hL.2.2]
      split_ifs with e
      · rw [e, Matrix.mul_smul, Matrix.smul_mul]
      · rw [Matrix.mul_zero, Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hL']
  rfl

theorem theta_dRho (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) :=
  theta_dLine hθ hψ (isRealDir_lineAt hθ τ z) hf

theorem om_dRho (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) (om (g, h) f) :=
  om_dLine hom hθ g h (isRealDir_lineAt hθ τ z) (isRealDir_lineAt hθ τ _) (lineAt_move hθ g h τ z) hf

end GlobalTheory.OrientedHeis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealPlaceSymplecticFormPositiveComplexStru
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OrientedRealForm

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

theorem map_inv_of_det_ne {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E) (h : G.det ≠ 0) :
    (G.map φ)⁻¹ = G⁻¹.map φ := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.2 h), Matrix.map_one _ φ.map_zero φ.map_one]

theorem trace_eq_sum {m n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin m) (Fin m) ℂ)
    (x y : Matrix (Fin m) (Fin n) ℂ) :
    (P * yᴴ * Q * x).trace = ∑ a, ∑ b, ∑ e, ∑ d, P a b * starRingEnd ℂ (y e b) * Q e d * x d a := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]
  rfl

variable {D : D7}

theorem formAt_eq (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    formAt S T τ x y =
      2 * (tauE D τ D.host.xi0 * ((gramAt D S τ)⁻¹ * yᴴ * gramAt D T τ * x).trace).re := by
  rw [trace_eq_sum]
  unfold formAt gramAt
  rw [map_inv_of_det_ne _ _ (gram_det_ne S)]
  rfl

theorem realPlace_imaginaryGenerator_re_eq_zero (τ : D.what₂.Tau) : (tauE D τ D.host.xi0).re = 0 := by
  have h := tauE_star τ D.host.xi0
  rw [GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg] at h
  have h2 := congrArg Complex.re h
  rw [Complex.neg_re, Complex.conj_re] at h2
  linarith

theorem cplxO_add {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (x y : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (x + y) = cplxO s t x + cplxO s t y := by
  unfold cplxO
  rw [Matrix.mul_add, Matrix.add_mul, smul_add]

theorem cplxO_smul {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (c • x) = c • cplxO s t x := by
  unfold cplxO
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]

def jO (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) : RW T S →ₗ[ℝ] RW T S where
  toFun z := fun τ => cplxO (sS τ) (sT τ) (z τ)
  map_add' x y := by funext τ; exact cplxO_add _ _ _ _
  map_smul' c x := by funext τ; exact cplxO_smul _ _ c _

theorem exists_real_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ (om : GlobalTheory.FockCompare.RW T S →ₗ[ℝ] GlobalTheory.FockCompare.RW T S →ₗ[ℝ] ℝ) (J : GlobalTheory.FockCompare.RW T S →ₗ[ℝ] GlobalTheory.FockCompare.RW T S), (∀ x y : WO S T, y.map (finPart D) = 0 → ψ (symplOH S T x y) = Complex.exp (-(Real.pi * Complex.I) * (om (GlobalTheory.FockCompare.piW θ T S x) (GlobalTheory.FockCompare.piW θ T S y) : ℝ))) ∧ (∀ z τ, J z τ = cplxO (sS τ) (sT τ) (z τ)) ∧ (∀ v, om v v = 0) ∧ (∀ v, J (J v) = -v) ∧ (∀ x y, om x (J y) = om y (J x)) ∧ ∀ v, v ≠ 0 → 0 < om v (J v) := by
  intro D ψ θ S T sS sT hψ hθ hS hT
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have key := fun τ => GlobalTheory.CartanTrace.cplxO_pos T.rank S.rank (gramAt D S τ) (sS τ) (gramAt D T τ) (sT τ) (tauE D τ D.host.xi0)
    (realPlace_imaginaryGenerator_re_eq_zero τ) (xi_zero_im_pos D τ) (hS τ) (hT τ)
  have hom : ∀ x y : RW T S, omO S T x y = ∑ τ, formAt S T τ (x τ) (y τ) := fun _ _ => rfl
  have hJ : ∀ (z : RW T S) τ, jO S T sS sT z τ = cplxO (sS τ) (sT τ) (z τ) := fun _ _ => rfl
  refine ⟨omO S T, jO S T sS sT, fun x y hy => ?_, hJ, omO_self h, fun v => ?_, fun x y => ?_, fun v hv => ?_⟩
  · rw [← psi_symplOH h hψ, h.iota_pi (V := T) (W := S) hy]
  · funext τ
    exact (key τ).2.1 (v τ)
  · rw [hom, hom]
    refine Finset.sum_congr rfl fun τ _ => ?_
    refine (formAt_eq S T τ _ _).trans (Eq.trans ?_ (formAt_eq S T τ _ _).symm)
    exact congrArg (2 * ·) ((key τ).2.2.1 (x τ) (y τ))
  · rw [hom]
    have hp : ∀ τ, v τ ≠ 0 → 0 < formAt S T τ (v τ) (jO S T sS sT v τ) := fun τ h0 =>
      lt_of_lt_of_eq (mul_pos two_pos ((key τ).2.2.2 (v τ) h0)) (formAt_eq S T τ _ _).symm
    obtain ⟨τ₀, h₀⟩ := Function.ne_iff.1 hv
    refine Finset.sum_pos' (fun τ _ => ?_) ⟨τ₀, Finset.mem_univ _, hp τ₀ h₀⟩
    by_cases h0 : v τ = 0
    · rw [h0]
      simp [formAt]
    · exact (hp τ h0).le

end GlobalTheory.OrientedRealForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrientedFormLaws

theorem sum_mul_left {A : Type} [CommRing A] {m n : ℕ} (c : A →+* A) (P : Fin n → Fin n → A)
    (Q : Fin m → Fin m → A) (t : A) (x y : Matrix (Fin m) (Fin n) A) :
    (∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * Q e d * (x.map fun z => t * z) d a) =
      t * ∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * Q e d * x d a := by
  simp only [Finset.mul_sum, Matrix.map_apply]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring

theorem sum_mul_right {A : Type} [CommRing A] {m n : ℕ} (c : A →+* A) (P : Fin n → Fin n → A)
    (Q : Fin m → Fin m → A) (t : A) (x y : Matrix (Fin m) (Fin n) A) :
    (∑ a, ∑ b, ∑ e, ∑ d, P a b * c ((y.map fun z => t * z) e b) * Q e d * x d a) =
      c t * ∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * Q e d * x d a := by
  simp only [Finset.mul_sum, Matrix.map_apply, map_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring

variable {D : D7} {S T : HSp D}

theorem hO_mul_left (t : Formalism.L2.Theta.AE D) (x y : WO S T) :
    hO S T (x.map fun z => t * z) y = t * hO S T x y :=
  sum_mul_left (cA D) (fun i k => incA D (S.gram⁻¹ i k)) (fun i k => incA D (T.gram i k)) t x y

theorem hO_mul_right (t : Formalism.L2.Theta.AE D) (x y : WO S T) :
    hO S T x (y.map fun z => t * z) = cA D t * hO S T x y :=
  sum_mul_right (cA D) (fun i k => incA D (S.gram⁻¹ i k)) (fun i k => incA D (T.gram i k)) t x y

theorem hO_rat (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hO S T (M.map (incA D)) (N.map (incA D)) = incA D (GlobalTheory.LatVac.hRat S T M N) := by
  unfold hO GlobalTheory.LatVac.hRat
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA, map_sum, RingHom.map_mul]

theorem symplOH_rat (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (M.map (incA D)) (N.map (incA D)) = algebraMap D.host.F (AF D.host.F)
      (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T M N)) := by
  have h2 : ∀ x, incA D x = (1 : AF D.host.F) ⊗ₜ[D.host.F] x := fun x => rfl
  rw [symplOH, symplO, hO_rat, ← RingHom.map_mul, h2, GlobalTheory.LatVac.trace_tmul, one_mul, RingHom.map_mul]

theorem hO_half (e : Formalism.L2.Theta.AE D) (u : WO S T) (he : e * cA D e = 0) (hu : IsHalf e u) : hO S T u u = 0 := by
  have h : (u.map fun z => e * z) = u := by
    funext i j
    exact hu i j
  have h1 := hO_mul_left e u u
  have h2 := hO_mul_right e u u
  rw [h] at h1 h2
  rw [h1, h2, ← mul_assoc, he, zero_mul]

theorem symplOH_laws : ∀ (D : D7) (S T : HSp D), (∀ x y z : WO S T, symplOH S T (x + y) z = symplOH S T x z + symplOH S T y z) ∧ (∀ x y z : WO S T, symplOH S T x (y + z) = symplOH S T x y + symplOH S T x z) ∧ (∀ x : WO S T, symplOH S T x x = 0) ∧ (∀ x y : WO S T, symplOH S T x y + symplOH S T x y = symplO S T x y) ∧ Continuous (fun q : WO S T × WO S T => symplOH S T q.1 q.2) ∧ (∀ g ∈ ratL T S, ∀ g' ∈ ratL T S, ∃ a : D.host.F, symplOH S T g g' = algebraMap D.host.F (AF D.host.F) a) ∧ (∀ (a : AE D) (x y : WO S T), symplOH S T (x.map fun z => a * z) y = symplOH S T x (y.map fun z => cA D a * z)) ∧ (∀ (e a : AE D) (u : WO S T), e * cA D e = 0 → IsHalf e u → symplOH S T (u.map fun z => a * z) u = 0) ∧ ∀ x y : WO S T, x.map (finPart D) = 0 → y.map (infPart D) = 0 → symplOH S T x y = 0 := by
  intro D S T
  refine ⟨GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_self,
    fun x y => ?_, GlobalTheory.OrientedHeis.continuous_symplOH continuous_fst continuous_snd, ?_, fun a x y => ?_,
    fun e a u he hu => ?_, fun x y hx hy => (GlobalTheory.OrientedHeis.symplOH_fin_real hy hx).2⟩
  · unfold symplOH
    rw [← add_mul, ← RingHom.map_add (f := _), add_halves, RingHom.map_one, one_mul]
  · rintro _ ⟨M, rfl⟩ _ ⟨N, rfl⟩
    exact ⟨_, symplOH_rat M N⟩
  · unfold symplOH symplO
    rw [hO_mul_left, hO_mul_right, GlobalTheory.DualPairCheck.cA_cA]
  · unfold symplOH symplO
    rw [hO_mul_left, hO_half e u he hu, mul_zero, mul_zero, LinearMap.map_zero, mul_zero]

end GlobalTheory.OrientedFormLaws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SymplecticAdelicFormBiadditiveAlternatingRationa
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.SymplecticOrthogonalSesquilinear

theorem trace_one_tmul {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem eq_zero_of_eq_neg {F R : Type} [Field F] [CharZero F] [CommRing R] [Algebra F R] {a : R} (h : a = -a) :
    a = 0 := by
  have h2 : (2 : F) • a = 0 := by rw [two_smul]; exact eq_neg_iff_add_eq_zero.1 h
  exact (smul_eq_zero_iff_right two_ne_zero).1 h2

theorem map_sesq {E A : Type} [CommRing E] [CommRing A] (ι : E →+* A) (c : A →+* A) (s : E → E)
    (hc : ∀ e, c (ι e) = ι (s e)) {m n : ℕ} (ξ : E) (P : Fin m → Fin m → E) (Q : Fin n → Fin n → E)
    (x y : Fin n → Fin m → E) :
    ι ξ * ∑ a, ∑ b, ∑ c', ∑ d, ι (P a b) * c (ι (y c' b)) * ι (Q c' d) * ι (x d a) =
      ι (ξ * ∑ a, ∑ b, ∑ c', ∑ d, P a b * s (y c' b) * Q c' d * x d a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hc]

theorem symplO_rat (D : D7) (S T : HSp D) (γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ∃ a : D.host.F, symplO S T (ratW T S γ) (ratW T S γ') = algebraMap D.host.F (AF D.host.F) a := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have h : ∃ e : D.host.E, incA D D.host.xi0 * hO S T (ratW T S γ) (ratW T S γ') = incA D e :=
    ⟨_, map_sesq (incA D) (cA D) star GlobalTheory.DualPairCheck.cA_incA D.host.xi0 (fun a b => S.gram⁻¹ a b)
      (fun a b => T.gram a b) γ γ'⟩
  obtain ⟨e, he⟩ := h
  refine ⟨Algebra.trace D.host.F D.host.E e, ?_⟩
  unfold symplO
  rw [he]
  exact trace_one_tmul _ e

theorem symplO_alt : ∀ (D : D7) (S T : HSp D), (∀ x x' y : WO S T, symplO S T (x + x') y = symplO S T x y + symplO S T x' y) ∧ (∀ x y y' : WO S T, symplO S T x (y + y') = symplO S T x y + symplO S T x y') ∧ (∀ x y : WO S T, symplO S T x y = -symplO S T y x) ∧ (∀ x : WO S T, symplO S T x x = 0) ∧ ∀ γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ a : D.host.F, symplO S T (ratW T S γ) (ratW T S γ') = algebraMap D.host.F (AF D.host.F) a := by
  intro D S T
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun x y => GlobalTheory.WeilVacMove.symplO_skew S T y x,
    fun x => eq_zero_of_eq_neg (F := D.host.F) (GlobalTheory.WeilVacMove.symplO_skew S T x x), symplO_rat D S T⟩
  · unfold symplO hO
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]
  · unfold symplO hO
    simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

end GlobalTheory.SymplecticOrthogonalSesquilinear
end

