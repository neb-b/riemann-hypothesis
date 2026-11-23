module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0008

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeEquivA
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

theorem measurable_lmul_mt (a : Mat k r) :
    @Measurable (Mt k r) (Mt k r) _ _ (fun x => (a * Matrix.of x : Mat k r)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem sigmaFinite_of_haarOn {U : Set (Mat k r)} {μ : Measure (Mt k r)} (hH : IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => hH.finite_compact K hK⟩
  infer_instance

theorem ae_mem_of_haarOn {U : Set (Mat k r)} {μ : Measure (Mt k r)} (hH : IsHaarOn U μ) :
    ∀ᵐ x ∂μ, (Matrix.of x : Mat k r) ∈ U := ae_iff.mpr hH.conc

theorem inner_sig_move (X : SigData k r) (g : Mat k r) (hg : g ∈ GV k r) (hgi : g⁻¹ ∈ GV k r)
    (hgg : g * g⁻¹ = 1) (a b : X.Hs) : ⟪X.σ g a, b⟫_ℂ = ⟪a, X.σ g⁻¹ b⟫_ℂ := by
  obtain ⟨h1, h2⟩ := X.rep.1
  have hσ : X.σ g (X.σ g⁻¹ b) = b := by
    have h3 := h2 g hg g⁻¹ hgi
    rw [hgg, h1] at h3
    have h4 := congrArg (fun L => L b) h3
    simpa using h4.symm
  let L : X.Hs →ₗᵢ[ℂ] X.Hs := ⟨(X.σ g : X.Hs →ₗ[ℂ] X.Hs), fun v => X.rep.2.1 g hg v⟩
  calc ⟪X.σ g a, b⟫_ℂ = ⟪L a, L (X.σ g⁻¹ b)⟫_ℂ := by rw [show L (X.σ g⁻¹ b) = b from hσ]; rfl
    _ = ⟪a, X.σ g⁻¹ b⟫_ℂ := L.inner_map_map a _

theorem psiD_norm {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (m : Mat k r) :
    ‖psiD D m‖ = 1 := by
  unfold psiD psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem psiD_star_mul {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (m : Mat k r) :
    star (psiD D m) * psiD D m = 1 := by
  rw [Complex.star_def, Complex.conj_mul', psiD_norm]
  simp

end ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

theorem gv_mul {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r) : a * b ∈ GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

private theorem hpk_sq_lemma : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single
    (⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩ :
      Fin (2 * r + k + 1))]
  · simp only [Hpk, Matrix.one_apply, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | (norm_num; done) | omega
  · intro l _ hl
    rw [Ne, Fin.ext_iff] at hl
    simp only [Hpk, Fin.ext_iff, Fin.val_mk] at hl ⊢
    split_ifs at hl ⊢ <;> first | (simp; done) | omega
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem isUnit_det_of_mem_GV' {a : Mat k r} (ha : a ∈ GV k r) : IsUnit a.det := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have h1 : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
    calc (Hpk k r * aᴴ * Hpk k r) * a = Hpk k r * (aᴴ * Hpk k r * a) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ha', hpk_sq_lemma]
  exact Matrix.isUnit_det_of_left_inverse h1

theorem gv_inv {a : Mat k r} (ha : a ∈ GV k r) : a⁻¹ ∈ GV k r := by
  have h1 : a * a⁻¹ = 1 := ReciprocityTheory.ChartRestriction.DS.Xi.StepA.UH_mul_inv k r ha
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
    _ = (a * a⁻¹)ᴴ * Hpk k r * (a * a⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1]; simp

theorem gv_inv_mul {a : Mat k r} (ha : a ∈ GV k r) : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a (isUnit_det_of_mem_GV' ha)

theorem gv_mul_inv {a : Mat k r} (ha : a ∈ GV k r) : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a (isUnit_det_of_mem_GV' ha)

theorem gv_inv_inv {a : Mat k r} (ha : a ∈ GV k r) : a⁻¹⁻¹ = a := Matrix.nonsing_inv_nonsing_inv a (isUnit_det_of_mem_GV' ha)

theorem fix_inv {a : Mat k r} (ha : a ∈ GV k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : a *ᵥ v = v) :
    a⁻¹ *ᵥ v = v := by
  calc a⁻¹ *ᵥ v = a⁻¹ *ᵥ (a *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, gv_inv_mul ha, Matrix.one_mulVec]

theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ} {a : Mat k r} (ha : a ∈ UWset k r z) : a⁻¹ ∈ UWset k r z := by
  simp only [UWset, Set.mem_setOf_eq] at ha ⊢
  obtain ⟨ha1, ha2, ha3⟩ := ha
  exact ⟨gv_inv ha1, fun i => ⟨fix_inv ha1 (ha2 i).1, fix_inv ha1 (ha2 i).2⟩, fix_inv ha1 ha3⟩

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

structure BEFacts (D : RealPlaceData k r Wp Wp) : Prop where
  nmul : ∀ a ∈ Nset k r, ∀ b ∈ Nset k r, a * b ∈ Nset k r
  ninv : ∀ a ∈ Nset k r, a⁻¹ ∈ Nset k r
  nrm : ∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, h * m * h⁻¹ ∈ Nset k r ∧ psiD D (h * m * h⁻¹) = psiD D m
  pmul : ∀ a ∈ Nset k r, ∀ b ∈ Nset k r, psiD D (a * b) = psiD D a * psiD D b
  conj : ∀ h ∈ UWset k r D.z, D.μN.map (conjM h) = D.μN

theorem beFacts_of (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) : BEFacts D := by
  obtain ⟨hB2, hBS, hR1, hBC, hUWb, hCH, hLB, hJ, hPh, hRB, hRA, hUn, hAe, hDJ, hIN, hUWN, hEll, hNS⟩ := h
  refine ⟨fun a ha b hb => (hNS k r).2.1 a ha b hb, fun a ha => (hNS k r).2.2 a ha, ?_, ?_, ?_⟩
  · intro g hg m hm
    obtain ⟨hmem, hell⟩ := hUWN k r D.z D.z_mem g hg m hm
    refine ⟨hmem, ?_⟩
    simp only [psiD, psi, hell]
  · intro a ha b hb
    simp only [psiD, psi, hEll k r D.z D.z_mem a ha b hb, mul_add, Complex.add_re, Complex.ofReal_add,
      Complex.exp_add]
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hCI, _⟩ := hB2
    have hc := hCI k r Wp Wp D
    exact fun g hg => hc g (Set.mem_union_left _ hg)

end ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBetaInfA
section
noncomputable section

open MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.BetaInfA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem ccle_five_four {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {F : Mat k r → E} {c : ℝ}
    (h : CCle A 5 F c) : CCle A 4 F c := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun u v hu hv hl g hg => h2 u v hu hv (by omega) g hg⟩
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg, hf, he⟩ := h1 g₀ hg₀
  exact ⟨U, f', hU, hg, hf.of_le (by exact_mod_cast (by norm_num : (4 : ℕ) ≤ 5)), he⟩

theorem inCC_five_four {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {F : Mat k r → E}
    (h : InCC A 5 F) : InCC A 4 F := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, ccle_five_four hc⟩

theorem continuous_lam (z : Fin (2 * r + k + 1) → ℂ) :
    Continuous fun n : Mt k r => lam k r z (Matrix.of n) := by
  unfold Formalism.FourierDecayAlt.B.lam Formalism.QuantumDeterminants.ell
  refine Complex.continuous_re.comp (continuous_const.mul (continuous_finsetSum _ fun a _ => ?_))
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop

theorem continuous_xiTau_prod (D : RealPlaceData k r Wp Wq) :
    Continuous fun x : (ℝ × ℝ) × SS k r => xiTau D x.1 x.2 := by
  have h1 := continuous_lam (k := k) (r := r) D.z
  have h2 := continuous_lam (k := k) (r := r) D.z'
  unfold Formalism.FourierDecayAlt.B.xiTau
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact ((continuous_fst.comp continuous_fst).mul
      (h1.comp (continuous_snd.comp (continuous_fst.comp continuous_snd)))).sub
    ((continuous_snd.comp continuous_fst).mul
      (h2.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))))

theorem norm_xiTau (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (p : SS k r) : ‖xiTau D τ p‖ = 1 := by
  unfold Formalism.FourierDecayAlt.B.xiTau
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_cf (D : RealPlaceData k r Wp Wq) {P : SS k r → ℂ} (hP : Integrable P D.μSS) :
    Continuous fun τ : ℝ × ℝ => ∫ p, xiTau D τ p * P p ∂D.μSS := by
  refine continuous_of_dominated (bound := fun p => ‖P p‖) (fun τ => ?_) (fun τ => ?_) hP.norm ?_
  · exact ((continuous_xiTau_prod D).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
      hP.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => by simp only [norm_mul, norm_xiTau, one_mul, le_refl]
  · exact Filter.Eventually.of_forall fun p =>
      ((continuous_xiTau_prod D).comp (continuous_id.prodMk continuous_const)).mul continuous_const

theorem integrable_test {w : ℝ → ℝ} (hw : IsTest w) : Integrable (fun x => (w x : ℂ)) volume := (hw.1.continuous.integrable_of_hasCompactSupport hw.2.1).ofReal

theorem integrable_test2 {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Integrable (fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ)) volume := by
  have h := MeasureTheory.Integrable.mul_prod (integrable_test h₁) (integrable_test h₂)
  rw [Measure.volume_eq_prod]
  push_cast
  exact h

theorem inner_om (w₁ w₂ : ℝ → ℝ) (a b : ℝ) :
    ∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((τ.1 * a - τ.2 * b : ℝ) : ℂ)) = om w₁ a * om w₂ (-b) := by
  have e : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((τ.1 * a - τ.2 * b : ℝ) : ℂ)) =
      ((w₁ τ.1 : ℂ) * Complex.exp (Complex.I * ((τ.1 * a : ℝ) : ℂ))) *
        ((w₂ τ.2 : ℂ) * Complex.exp (Complex.I * ((τ.2 * -b : ℝ) : ℂ))) := by
    intro τ
    push_cast
    rw [show Complex.I * ((τ.1 : ℂ) * a - τ.2 * b) =
      Complex.I * (τ.1 * a) + Complex.I * (τ.2 * -b) by ring, Complex.exp_add]
    ring
  rw [Measure.volume_eq_prod, integral_congr_ae (Filter.Eventually.of_forall e)]
  exact MeasureTheory.integral_prod_mul
    (fun x : ℝ => (w₁ x : ℂ) * Complex.exp (Complex.I * ((x * a : ℝ) : ℂ)))
    (fun y : ℝ => (w₂ y : ℂ) * Complex.exp (Complex.I * ((y * -b : ℝ) : ℂ)))

theorem sigmaFinite_haarOn {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

theorem sigmaFinite_SS (D : RealPlaceData k r Wp Wq) : SigmaFinite D.μSS := by
  haveI := sigmaFinite_haarOn D.haarW
  haveI := sigmaFinite_haarOn D.haarN
  haveI := sigmaFinite_haarOn D.haarW'
  unfold RealPlaceData.μSS
  infer_instance

theorem fubini_cf (D : RealPlaceData k r Wp Wq) {P : SS k r → ℂ} (hP : Integrable P D.μSS)
    {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    ∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * ∫ p, xiTau D τ p * P p ∂D.μSS =
      ∫ p, om w₁ (lam k r D.z (Matrix.of p.1.2)) * om w₂ (-lam k r D.z' (Matrix.of p.2.2)) * P p ∂D.μSS := by
  haveI := sigmaFinite_SS D
  have hint : Integrable (fun x : (ℝ × ℝ) × SS k r =>
      ((w₁ x.1.1 * w₂ x.1.2 : ℝ) : ℂ) * (xiTau D x.1 x.2 * P x.2)) (volume.prod D.μSS) := by
    refine (MeasureTheory.Integrable.mul_prod (integrable_test2 h₁ h₂) hP).mono ?_ ?_
    · haveI : OpensMeasurableSpace ((ℝ × ℝ) × SS k r) := Prod.opensMeasurableSpace
      exact (integrable_test2 h₁ h₂).aestronglyMeasurable.comp_fst.mul
        ((continuous_xiTau_prod D).aestronglyMeasurable.mul hP.aestronglyMeasurable.comp_snd)
    · exact Filter.Eventually.of_forall fun x => by simp only [norm_mul, norm_xiTau, one_mul, le_refl]
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap (f := fun τ p => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (xiTau D τ p * P p)) hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  have e : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * (xiTau D τ p * P p) =
      (((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * Complex.exp (Complex.I *
        ((τ.1 * lam k r D.z (Matrix.of p.1.2) - τ.2 * lam k r D.z' (Matrix.of p.2.2) : ℝ) : ℂ))) * P p :=
    fun τ => by unfold Formalism.FourierDecayAlt.B.xiTau; ring
  simp only [e]
  rw [integral_mul_const, inner_om]

theorem isOpen_Quad : IsOpen Quad := isOpen_Ioi.prod isOpen_Ioi

theorem integrable_test_mul {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) {f : ℝ × ℝ → ℂ}
    (hf : ContinuousOn f Quad) : Integrable (fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * f τ) volume := by
  have hK : IsCompact (tsupport w₁ ×ˢ tsupport w₂) := h₁.2.1.prod h₂.2.1
  have hKQ : tsupport w₁ ×ˢ tsupport w₂ ⊆ Quad := Set.prod_mono h₁.2.2 h₂.2.2
  have hc : ContinuousOn (fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * f τ)
      (tsupport w₁ ×ˢ tsupport w₂) := by
    refine ContinuousOn.mul ?_ (hf.mono hKQ)
    exact (Complex.continuous_ofReal.comp ((h₁.1.continuous.comp continuous_fst).mul
      (h₂.1.continuous.comp continuous_snd))).continuousOn
  refine MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero
    (hc.integrableOn_compact (μ := volume) hK) ?_
  intro τ hτ
  rw [Set.mem_prod, not_and_or] at hτ
  rcases hτ with h | h
  · simp [image_eq_zero_of_notMem_tsupport h]
  · simp [image_eq_zero_of_notMem_tsupport h]

theorem betaInf_eq_of (D : RealPlaceData k r Wp Wq) [FiniteDimensional ℂ Wq] (A : ℝ) (hAe : AeFromTests)
    (hRB : RegBound D A) (hRA : RegAverage D A) {F F' : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : InCC A 4 F) (hF' : InCC A 4 F') (hP : Integrable (Ph D F F') D.μSS) :
    betaInf D F F' = ∫ p, xiTau D (1, 1) p * Ph D F F' p ∂D.μSS := by
  obtain ⟨-, hcont, -⟩ := hRB
  have hc1 : ContinuousOn (fun τ => betaInfTau D τ F F') Quad := hcont F F' hF hF'
  have hc2 : ContinuousOn (fun τ : ℝ × ℝ => ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS) Quad :=
    (continuous_cf D hP).continuousOn
  have hae := hAe (fun _ => 0)
    (fun τ => betaInfTau D τ F F' - ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS)
    aemeasurable_const (hc1.sub hc2) (fun w₁ w₂ h₁ h₂ _ _ => by
      refine ⟨by simp, ?_⟩
      simp only [mul_zero, MeasureTheory.lintegral_zero, ENNReal.toReal_zero, Complex.ofReal_zero]
      simp_rw [mul_sub]
      rw [integral_sub (integrable_test_mul h₁ h₂ hc1) (integrable_test_mul h₁ h₂ hc2),
        (hRA F F' hF hF' w₁ w₂ h₁ h₂).2, fubini_cf D hP h₁ h₂, sub_self])
  have h0 : (fun τ => betaInfTau D τ F F' - ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS)
      =ᵐ[volume.restrict Quad] fun _ => 0 := by
    filter_upwards [hae] with τ hτ
    simpa using hτ.2.symm
  have heq := Measure.eqOn_open_of_ae_eq h0 isOpen_Quad (hc1.sub hc2) continuousOn_const
  have h11 : ((1 : ℝ), (1 : ℝ)) ∈ Quad := by
    unfold Quad
    exact ⟨by norm_num, by norm_num⟩
  show betaInfTau D (1, 1) F F' = _
  exact sub_eq_zero.mp (heq h11)

end ReciprocityTheory.ChartRestriction.DS.Mult1.BetaInfA
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDiagExists
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem isHaarOn_smul_of {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (hμ : IsHaarOn U μ)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) : IsHaarOn U (c • μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [smul_apply, hμ.conc, smul_zero]
  · intro a ha
    have hcont : Continuous (lmulM (k := k) (r := r) a) :=
      continuous_const.matrix_mul continuous_id
    rw [Measure.map_smul c hcont.measurable.aemeasurable, hμ.left a ha]
  · intro a ha
    have hcont : Continuous (rmulF a) := continuous_id.matrix_mul continuous_const
    rw [Measure.map_smul c hcont.measurable.aemeasurable, hμ.right a ha]
  · intro K hK
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hct) (hμ.finite_compact K hK)
  · intro h0
    apply hμ.ne_zero
    ext s _
    have h1 := congrArg (fun ν : Measure (Mt k r) => ν s) h0
    simp only [smul_apply, smul_eq_mul, FunLike.coe_zero, Pi.zero_apply, mul_eq_zero] at h1
    simpa [hc0] using h1

theorem stDiagExists (h : UnitaryGroupStructuralFacts) : StDiagExists := by
  unfold StDiagExists
  intro k r Wp _ _ _ z π hk hz hT hrep hun hcont hirr
  unfold UnitaryGroupStructuralFacts at h
  obtain ⟨hB2, hBS, -⟩ := h
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.InductiveHeisenbergInputs at hB2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCW, -⟩ := hB2
  obtain ⟨D, hDz, hDz', hDπ, hDπ', -⟩ :=
    hBS k r Wp Wp z z π π hk hz hz hT hT hrep hrep hun hun hcont hcont
  have hcomp : IsCompact (UWset k r z) := hCW k r z hz hT
  have hW : IsHaarOn (UWset k r z) D.μW := by
    have h0 := D.haarW
    rw [hDz] at h0
    exact h0
  have hm0 : D.μW Set.univ ≠ 0 := by
    intro h0
    exact hW.ne_zero (Measure.measure_univ_eq_zero.mp h0)
  have hmt : D.μW Set.univ ≠ ∞ := by
    have h1 : D.μW Set.univ ≤ D.μW (UWset k r z) + D.μW (UWset k r z)ᶜ :=
      measure_univ_le_add_compl _
    rw [hW.conc, add_zero] at h1
    exact ne_top_of_le_ne_top (hW.finite_compact _ hcomp).ne h1
  have hc0 : (D.μW Set.univ)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hmt
  have hct : (D.μW Set.univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hm0
  have hH : IsHaarOn (UWset k r D.z) ((D.μW Set.univ)⁻¹ • D.μW) :=
    isHaarOn_smul_of D.haarW hc0 hct
  have hH' : IsHaarOn (UWset k r D.z') ((D.μW Set.univ)⁻¹ • D.μW) := by
    rw [hDz', ← hDz]
    exact hH
  let D' : RealPlaceData k r Wp Wp :=
    { D with
      μW := (D.μW Set.univ)⁻¹ • D.μW
      μW' := (D.μW Set.univ)⁻¹ • D.μW
      haarW := hH
      haarW' := hH' }
  refine ⟨D', hDz, hDπ, ?_⟩
  refine ⟨hDz'.trans hDz.symm, hDπ'.trans hDπ.symm, rfl, ?_, ?_⟩
  · show ((D.μW Set.univ)⁻¹ • D.μW) Set.univ = 1
    rw [smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hm0 hmt]
  · show Formalism.MainNotions.S.IsIrredOn (UWset k r D.z) D.π
    rw [hDz, hDπ]
    exact hirr

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroupB
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace InvGrp

variable {k r : ℕ}

theorem continuous_lmulM (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  unfold lmulM; fun_prop

theorem map_invol_eq (HU : HaarUnique) {U : Set (Mat k r)} (hU : IsClosedSubgroup U) {μ : Measure (Mt k r)}
    (hμ : IsHaarOn U μ) (f : Mt k r → Mt k r) (hf : Continuous f) (hff : ∀ x, f (f x) = x)
    (hfU : ∀ x : Mt k r, (x : Mat k r) ∈ U → (f x : Mat k r) ∈ U)
    (hl : ∀ a ∈ U, ∃ b ∈ U, ∀ x, lmulM a (f x) = f (lmulM b x)) : μ.map f = μ := by
  have hfm : Measurable f := hf.measurable
  have hUc : IsClosed (show Set (Mt k r) from U) := hU.closed
  have hUm : MeasurableSet (show Set (Mt k r) from U) := hUc.measurableSet
  have h1 : (μ.map f) Uᶜ = 0 := by
    rw [Measure.map_apply hfm hUm.compl]
    refine measure_mono_null (fun x hx => ?_) hμ.conc
    intro hxU
    exact hx (hfU x hxU)
  have h2 : ∀ a ∈ U, (μ.map f).map (lmulM a) = μ.map f := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hl a ha
    rw [Measure.map_map (continuous_lmulM a).measurable hfm]
    have : lmulM a ∘ f = f ∘ lmulM b := funext hab
    rw [this, ← Measure.map_map hfm (continuous_lmulM b).measurable, hμ.left b hb]
  have h3 : ∀ K : Set (Mt k r), IsCompact K → (μ.map f) K < ∞ := by
    intro K hK
    rw [Measure.map_apply hfm hK.measurableSet]
    have : f ⁻¹' K = f '' K := by
      ext x; constructor
      · intro hx; exact ⟨f x, hx, hff x⟩
      · rintro ⟨y, hy, rfl⟩; show f (f y) ∈ K; rw [hff]; exact hy
    rw [this]
    exact hμ.finite_compact _ (hK.image hf)
  obtain ⟨c, hc⟩ := HU k r U μ (μ.map f) hU hμ h1 h2 h3
  have hff' : f ∘ f = id := funext hff
  have hback : (μ.map f).map f = μ := by
    rw [Measure.map_map hfm hfm, hff', Measure.map_id]
  have hcc : (c * c) • μ = μ := by
    conv_rhs => rw [← hback]
    rw [hc, Measure.map_smul c hfm.aemeasurable, hc, smul_smul]

  obtain ⟨K, hK, hK0⟩ : ∃ K : Set (Mt k r), IsCompact K ∧ μ K ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hμ.ne_zero
    have : μ Set.univ = 0 := by
      rw [← Metric.iUnion_closedBall_nat (0 : Mt k r)]
      exact measure_iUnion_null fun n => hcon _ (isCompact_closedBall _ _)
    exact Measure.measure_univ_eq_zero.mp this
  have hKt : μ K ≠ ∞ := (hμ.finite_compact K hK).ne
  have hval : ((c * c : ℝ≥0) : ℝ≥0∞) * μ K = 1 * μ K := by
    have := congrArg (fun ν : Measure (Mt k r) => ν K) hcc
    simpa using this
  have hc1 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hK0 hKt).mp hval
  have hc2 : (c : ℝ) * c = 1 := by
    have : c * c = 1 := by exact_mod_cast hc1
    exact_mod_cast this
  have hcpos : (0 : ℝ) ≤ c := c.2
  have hc3 : c = 1 := by
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  rw [hc, hc3, one_smul]

end InvGrp

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

