module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOn
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0171
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnipotentMulVecMiddleVec
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaIntegrationFormulaConstant

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreVolumeNormalFormStabiliser
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.FibreVolume

variable {k r : ℕ}

theorem hpk_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1

theorem GG_one : (1 : Mat k r) ∈ GG k r := (uHGroup _ _ hpk_unit).1

theorem GG_mul {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r :=
  (uHGroup _ _ hpk_unit).2.1 a ha b hb

theorem GG_unit {a : Mat k r} (ha : a ∈ GG k r) : IsUnit a.det := ((uHGroup _ _ hpk_unit).2.2 a ha).1

theorem GG_inv {a : Mat k r} (ha : a ∈ GG k r) : a⁻¹ ∈ GG k r := ((uHGroup _ _ hpk_unit).2.2 a ha).2

theorem N_sub_S (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨GG_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩, n, hn, (one_mul n).symm⟩

theorem continuous_two (a b : Mat k r) : Continuous (fun x : Mt k r => (a * Matrix.of x * b : Mat k r)) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem measurable_two (a b : Mat k r) :
    Measurable (fun x : Mt k r => (Matrix.of.symm (a * Matrix.of x * b) : Mt k r)) :=
  Continuous.measurable (α := Mt k r) (γ := Mt k r) (continuous_two a b)

def twoEquiv (a b : Mat k r) (ha : IsUnit a.det) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := Matrix.of.symm (a * Matrix.of x * b)
  invFun x := Matrix.of.symm (a⁻¹ * Matrix.of x * b⁻¹)
  left_inv x := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hb]
  right_inv x := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul,
      Matrix.nonsing_inv_mul_cancel_right _ _ hb]
  measurable_toFun := measurable_two a b
  measurable_invFun := measurable_two _ _

theorem map_twoEquiv {μ : Measure (Mt k r)} {a b : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det)
    (hl : μ.map (lmulM a) = μ) (hr : μ.map (rmulM b) = μ) : μ.map (twoEquiv a b ha hb) = μ := by
  have h1 : Measurable (lmulM a : Mt k r → Mt k r) :=
    Continuous.measurable (α := Mt k r) (γ := Mt k r)
      (continuous_const.matrix_mul (continuous_id (X := Mat k r)))
  have h2 : Measurable (rmulM b : Mt k r → Mt k r) := (continuous_rmulM b).measurable
  have : (twoEquiv a b ha hb : Mt k r → Mt k r) = rmulM b ∘ lmulM a := rfl
  rw [this, ← Measure.map_map h2 h1, hl, hr]

theorem Tz_eq {z z' : Fin (2 * r + k + 1) → ℂ} {g : Mat k r} {c : ℂ} (hg : g ∈ GG k r) (hc : ‖c‖ = 1)
    (h : g *ᵥ z' = c • z) : Tz k r z' = Tz k r z := by
  have h1 : herm (Hpk k r) (g *ᵥ z') (g *ᵥ z') = herm (Hpk k r) z' z' := by
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
    unfold herm
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']
  have h2 : herm (Hpk k r) (c • z) (c • z) = herm (Hpk k r) z z := by
    have hcc : star c * c = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hc]; simp
    unfold herm
    rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul, hcc, one_smul]
  unfold Tz
  rw [← h1, h, h2]

theorem fibre_volume : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (De s : ℝ) (μR : Measure (Mt k r)), 1 ≤ j → j + 2 ≤ k → DeOK k r z z' γ De → 0 < s → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → ∀ g₁ ∈ GG k r, lebN k r {n | Yj k r hj z z' γ (Matrix.of n * g₁) = 0} = 0 ∧ ∀ φ, SubCut (GG k r) μR φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ (rmulM g₁ n) * (Eset0 k r hj z z' γ R₀ y).indicator 1 (rmulM g₁ n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol0 k r j R₀ De y / s) := by
  intro k r j hj z z' γ De s μR h1 h2 hDe hs hN g₁ hg₁
  obtain ⟨hz, hz', hT, n₁, hn₁, n₂, hn₂, g₀, β, c, hg₀, rfl, rfl⟩ := hN
  obtain ⟨n₀, hn₀, a, ha, m, hm, κ, hκ, hg⟩ := GlobalTheory.T.iwasawa_decomposition_isotropic_flag k r g₁ hg₁
  have hT' : 0 < Tz k r z' := by rw [Tz_eq hg₀.1 hg₀.2.1 hg₀.2.2.1]; exact hT
  have hDe₀ : DeOK k r z z' g₀ De := by
    refine ⟨hDe.1, fun l hl => ?_⟩
    have := hDe.2 l hl
    rwa [dInv k r z z' hz hz' n₁ (N_sub_S z hn₁) n₂ (N_sub_S z' hn₂)] at this
  have key := _root_.GlobalTheory.Amp.FibreNormal.fibre_volume k r j hj z z' g₀ β c hz hz' hT hg₀ h1 h2 De hDe₀ m hm a ha
  set A : Mat k r := uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m with hA
  have hg' : g₁ = n₀ * A * κ := by rw [hg, hA]; simp only [Matrix.mul_assoc]
  clear_value A
  have u₀ := GG_unit hn₀.1
  have u₂ := GG_unit hn₂.1
  have uκ := GG_unit hκ.1
  have hAG : A ∈ GG k r := by
    have : A = n₀⁻¹ * g₁ * κ⁻¹ := by
      rw [hg', ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₀, Matrix.one_mul,
        Matrix.mul_nonsing_inv_cancel_right _ _ uκ]
    rw [this]; exact GG_mul (GG_mul (GG_inv hn₀.1) hg₁) (GG_inv hκ.1)
  have hH := _root_.GlobalTheory.Amp.NHaar.isHaarOn_lebN k r
  have hU := ((_root_.GlobalTheory.SgInf.unimodular_S_N_UW k r z hz hT (lebN k r)).2.1 hH).1
  set T := twoEquiv n₂ n₀ u₂ u₀ with hTdef
  have hmap : (lebN k r).map T = lebN k r := map_twoEquiv u₂ u₀ (hH.2.2.2 _ hn₂) (hU.1 _ hn₀)
  have hae : ∀ᵐ n ∂(lebN k r), Matrix.of n ∈ Nset k r := hH.2.2.1
  have hTof : ∀ n, (Matrix.of (T n) : Mat k r) = n₂ * Matrix.of n * n₀ := fun n => rfl
  have hγ : n₁ * g₀ * n₂ ∈ GG k r := GG_mul (GG_mul hn₁.1 hg₀.1) hn₂.1
  have hY : ∀ n : Mt k r, Matrix.of n ∈ Nset k r →
      Yj k r hj z z' (n₁ * g₀ * n₂) (Matrix.of n * g₁) = Yj k r hj z z' g₀ (Matrix.of (T n) * A) := by
    intro n hn
    rw [(_root_.GlobalTheory.Amp.YjInv.yj_invariant k r j hj z z' g₀ hz hz' hg₀.1 _ (GG_mul hn.1 hg₁)).2.1 n₁ hn₁ n₂ hn₂, hTof,
      ← (_root_.GlobalTheory.Amp.YjInv.yj_invariant k r j hj z z' g₀ hz hz' hg₀.1 _
        (GG_mul (GG_mul (GG_mul hn₂.1 hn.1) hn₀.1) hAG)).1 κ hκ, hg']
    simp only [Matrix.mul_assoc]
  refine ⟨?_, fun φ hφ R₀ y hR hy => ?_⟩
  · have h0 := key.1
    rw [← hmap, MeasurableEquiv.map_apply] at h0
    rw [← h0]
    apply measure_congr
    filter_upwards [hae] with n hn
    change (Yj k r hj z z' (n₁ * g₀ * n₂) (Matrix.of n * g₁) = 0) ↔ (Yj k r hj z z' g₀ (Matrix.of (T n) * A) = 0)
    rw [hY n hn]
  · have hE : ∀ n : Mt k r, Matrix.of n ∈ Nset k r →
        (rmulM g₁ n ∈ Eset0 k r hj z z' (n₁ * g₀ * n₂) R₀ y ↔ rmulM A (T n) ∈ Eset0 k r hj z z' g₀ R₀ y) := by
      intro n hn
      have hx : Matrix.of (T n) * A ∈ GG k r := GG_mul (GG_mul (GG_mul hn₂.1 hn.1) hn₀.1) hAG
      have e1 : Sg2 k r z' (Matrix.of n * g₁) = Sg2 k r z' (Matrix.of (T n) * A) := by
        rw [← (_root_.GlobalTheory.Amp.TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z' hz' hT').2.1 _ hx n₂⁻¹ (N_sub_S z' ((nSubgroup k r).2.2 _ hn₂)) κ hκ, hTof, hg']
        simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₂, Matrix.one_mul]
      have e2 : Sg2 k r z (n₁ * g₀ * n₂ * (Matrix.of n * g₁)) = Sg2 k r z (g₀ * (Matrix.of (T n) * A)) := by
        rw [← (_root_.GlobalTheory.Amp.TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z hz hT).2.1 _ (GG_mul hg₀.1 hx) n₁ (N_sub_S z hn₁) κ hκ, hTof, hg']
        simp only [Matrix.mul_assoc]
      simp only [Eset0, Set.mem_setOf_eq, of_rmulM]
      rw [e1, e2, hY n hn]
      exact and_congr_left fun _ => iff_of_true (GG_mul hn.1 hg₁) hx
    set ψ : Mt k r → ℝ≥0∞ := fun x =>
      ENNReal.ofReal s * φ (Matrix.of.symm (n₂⁻¹ * Matrix.of x * (n₀⁻¹ * g₁))) with hψ
    have hψT : ∀ n, ψ (T n) = ENNReal.ofReal s * φ (rmulM g₁ n) := by
      intro n
      have : n₂⁻¹ * Matrix.of (T n) * (n₀⁻¹ * g₁) = Matrix.of n * g₁ := by
        rw [hTof]
        simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₂, Matrix.one_mul,
          Matrix.mul_nonsing_inv_cancel_right _ _ u₀]
      simp only [hψ, this]; rfl
    have hsub : SubCut (Nset k r) (lebR0 k r j β) ψ := by
      refine ⟨(hφ.1.comp (measurable_two _ _)).const_mul _, fun x hx => ?_⟩
      have hw : n₂⁻¹ * Matrix.of x * (n₀⁻¹ * g₁) ∈ GG k r :=
        GG_mul (GG_mul (GG_inv hn₂.1) hx.1) (GG_mul (GG_inv hn₀.1) hg₁)
      have h := hφ.2 (Matrix.of.symm (n₂⁻¹ * Matrix.of x * (n₀⁻¹ * g₁))) hw
      have hc : (conjM n₂⁻¹ : Mt k r → Mt k r) =
          twoEquiv n₂⁻¹ n₂⁻¹⁻¹ (GG_unit (GG_inv hn₂.1)) (GG_unit (GG_inv (GG_inv hn₂.1))) := rfl
      rw [hc, lintegral_map_equiv, lintegral_smul_measure, smul_eq_mul,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
      refine le_of_eq_of_le (lintegral_congr fun ρ => ?_) h
      have : n₂⁻¹ * (Matrix.of ρ * Matrix.of x) * (n₀⁻¹ * g₁) =
          n₂⁻¹ * Matrix.of ρ * n₂⁻¹⁻¹ * (n₂⁻¹ * Matrix.of x * (n₀⁻¹ * g₁)) := by
        rw [Matrix.nonsing_inv_nonsing_inv _ u₂]
        simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ u₂]
      exact congrArg (fun w : Mat k r => ENNReal.ofReal s * φ (Matrix.of.symm w)) this
    have h := key.2 ψ hsub R₀ y hR hy
    rw [← hmap, lintegral_map_equiv] at h
    have h' : ENNReal.ofReal s * ∫⁻ n, φ (rmulM g₁ n) *
        (Eset0 k r hj z z' (n₁ * g₀ * n₂) R₀ y).indicator 1 (rmulM g₁ n) ∂(lebN k r) ≤
        ENNReal.ofReal (fibVol0 k r j R₀ De y) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) h
      filter_upwards [hae] with n hn
      rw [hψT, ← mul_assoc]
      refine congrArg (fun t => ENNReal.ofReal s * φ (rmulM g₁ n) * t) ?_
      by_cases hm : rmulM g₁ n ∈ Eset0 k r hj z z' (n₁ * g₀ * n₂) R₀ y
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem ((hE n hn).1 hm)]; rfl
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm ((hE n hn).2 h))]
    rw [ENNReal.ofReal_div_of_pos hs, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hs))
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact h'

end GlobalTheory.Amp.FibreVolume
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreVolumeTwoFlagsGeneralPosition
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.FibreVolumeGen

variable {k r : ℕ}

theorem hpk_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

theorem GG_mul {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r :=
  (uHGroup _ (Hpk k r) hpk_unit).2.1 a ha b hb

theorem GG_unit {a : Mat k r} (ha : a ∈ GG k r) : IsUnit a.det :=
  ((uHGroup _ (Hpk k r) hpk_unit).2.2 a ha).1

theorem GG_inv {a : Mat k r} (ha : a ∈ GG k r) : a⁻¹ ∈ GG k r :=
  ((uHGroup _ (Hpk k r) hpk_unit).2.2 a ha).2

theorem continuous_two (a b : Mat k r) : Continuous (fun x : Mt k r => (a * Matrix.of x * b : Mat k r)) :=
  (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem measurable_two (a b : Mat k r) :
    Measurable (fun x : Mt k r => (Matrix.of.symm (a * Matrix.of x * b) : Mt k r)) := by
  have h : Continuous (fun x : Mt k r => (Matrix.of.symm (a * Matrix.of x * b) : Mt k r)) := continuous_two a b
  exact h.measurable

def twoEquiv (a b : Mat k r) (ha : IsUnit a.det) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := Matrix.of.symm (a * Matrix.of x * b)
  invFun x := Matrix.of.symm (a⁻¹ * Matrix.of x * b⁻¹)
  left_inv x := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hb]
  right_inv x := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul,
      Matrix.nonsing_inv_mul_cancel_right _ _ hb]
  measurable_toFun := measurable_two a b
  measurable_invFun := measurable_two _ _

theorem map_twoEquiv {μ : Measure (Mt k r)} {a b : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det)
    (hl : μ.map (lmulM a) = μ) (hr : μ.map (rmulM b) = μ) : μ.map (twoEquiv a b ha hb) = μ := by
  have hla : Measurable (lmulM a : Mt k r → Mt k r) := by
    have h : (lmulM a : Mt k r → Mt k r) = fun x => (Matrix.of.symm (a * Matrix.of x * 1) : Mt k r) := by
      funext x; apply Matrix.of.injective; (rw [Equiv.apply_symm_apply, Matrix.mul_one]) <;> rfl
    rw [h]; exact measurable_two a 1
  have hrb : Measurable (rmulM b : Mt k r → Mt k r) := (GlobalTheory.SgInf.continuous_rmulM b).measurable
  have h1 : (twoEquiv a b ha hb : Mt k r → Mt k r) = rmulM b ∘ lmulM a := rfl
  rw [h1, ← Measure.map_map hrb hla, hl, hr]

theorem fibre_volume : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r) (De s : ℝ) (μR : Measure (Mt k r)), 1 ≤ r → 2 * r + 6 ≤ k → TwoFl k r z z' γ → DeOK k r z z' γ De → 0 < s → NormR k r γ s μR → ∀ g₁ ∈ GG k r, lebN k r {n | Yv k r z z' γ (Matrix.of n * g₁) = 0} = 0 ∧ ∀ φ, SubCut (GG k r) μR φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ (rmulM g₁ n) * (Eset k r z z' γ R₀ y).indicator 1 (rmulM g₁ n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol k r R₀ De y / s) := by
  intro k r z z' γ De s μR hr hk hTF hDe hs hNR g₁ hg₁
  obtain ⟨n₁, hn₁, n₂, hn₂, g₀, β, hNorm, rfl, rfl⟩ := hNR
  obtain ⟨hz, hz', hT, hT', -, hGf, hDr⟩ := hTF
  have hg₀G : g₀ ∈ GG k r := hNorm.1
  have hn₁S : n₁ ∈ Sset k r z := GlobalTheory.Amp.YInv.N_sub_S z hn₁
  have hn₂S : n₂ ∈ Sset k r z' := GlobalTheory.Amp.YInv.N_sub_S z' hn₂
  have hn₂G : n₂ ∈ GG k r := hn₂.1
  have hu2 : IsUnit n₂.det := GG_unit hn₂G
  have hn₂i : n₂⁻¹ ∈ Nset k r := (nSubgroup k r).2.2 n₂ hn₂
  have hn₂iS : n₂⁻¹ ∈ Sset k r z' := GlobalTheory.Amp.YInv.N_sub_S z' hn₂i
  have c1 : ∀ B : Mat k r, n₂ * (n₂⁻¹ * B) = B := fun B => Matrix.mul_nonsing_inv_cancel_left n₂ B hu2
  have c2 : ∀ B : Mat k r, n₂⁻¹ * (n₂ * B) = B := fun B => Matrix.nonsing_inv_mul_cancel_left n₂ B hu2

  have hDmin : ∀ l, Dmin k r z z' (n₁ * g₀ * n₂) l = Dmin k r z z' g₀ l :=
    fun l => dInv k r z z' hz hz' n₁ hn₁S n₂ hn₂S g₀ l
  have hGf0 : Gf k r z z' (n₁ * g₀ * n₂) = Gf k r z z' g₀ := gInv k r z z' hz hz' n₁ hn₁S n₂ hn₂S g₀
  have hDr0 : Dr k r z z' (n₁ * g₀ * n₂) = Dr k r z z' g₀ := by unfold Dr; rw [hDmin]
  have hTF0 : TwoFl k r z z' g₀ := ⟨hz, hz', hT, hT', hg₀G, by rw [← hGf0]; exact hGf, by rw [← hDr0]; exact hDr⟩
  have hDe0 : DeOK k r z z' g₀ De := by
    refine ⟨hDe.1, fun l hl hne => ?_⟩
    rw [← hDmin] at hne ⊢
    exact hDe.2 l hl hne

  obtain ⟨n', hn', a, ha, m, hm, κ, hκ, hdec⟩ := GlobalTheory.Amp.Iwa.iwasawa k r (n₂ * g₁) (GG_mul hn₂G hg₁)
  have hB := _root_.GlobalTheory.Amp.FibNf.fibre_bound k r z z' g₀ β De hr hk hTF0 hNorm hDe0 m hm a ha
  set A := uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m with hA
  have hn'G : n' ∈ GG k r := hn'.1
  have hdec' : n₂ * g₁ = n' * A * κ := by rw [hdec, hA]; simp only [mul_assoc]
  have c3 : ∀ B : Mat k r, n'⁻¹ * (n' * B) = B := fun B => Matrix.nonsing_inv_mul_cancel_left n' B (GG_unit hn'G)
  have hAK : A * κ ∈ GG k r := by
    have : A * κ = n'⁻¹ * (n₂ * g₁) := by rw [hdec']; simp only [mul_assoc, c3]
    rw [this]; exact GG_mul (GG_inv hn'G) (GG_mul hn₂G hg₁)
  have hg : n₂⁻¹ * (n' * (A * κ)) = g₁ := by rw [← mul_assoc n' A, ← hdec', c2]

  have hl2 : (lebN k r).map (lmulM n₂) = lebN k r := (_root_.GlobalTheory.Amp.NHaar.isHaarOn_lebN k r).2.2.2 n₂ hn₂
  have hr2 : (lebN k r).map (rmulM (n₂⁻¹ * n')) = lebN k r :=
    ((_root_.GlobalTheory.SgInf.unimodular_S_N_UW k r z hz hT (lebN k r)).2.1 (_root_.GlobalTheory.Amp.NHaar.isHaarOn_lebN k r)).1.1 _ ((nSubgroup k r).2.1 _ hn₂i _ hn')
  have hu' : IsUnit (n₂⁻¹ * n').det := GG_unit (GG_mul (GG_inv hn₂G) hn'G)
  obtain ⟨e, he_map, he⟩ : ∃ e : Mt k r ≃ᵐ Mt k r, (lebN k r).map e = lebN k r ∧
      ∀ n, Matrix.of (e n) = n₂ * Matrix.of n * (n₂⁻¹ * n') :=
    ⟨twoEquiv n₂ (n₂⁻¹ * n') hu2 hu', map_twoEquiv hu2 hu' hl2 hr2, fun _ => rfl⟩
  have key : ∀ n : Mt k r, Matrix.of n * g₁ = n₂⁻¹ * (Matrix.of (e n) * A) * κ := by
    intro n; rw [he n]; simp only [mul_assoc, c2, hg]

  have hYv : ∀ W : Mat k r, Yv k r z z' (n₁ * g₀ * n₂) (n₂⁻¹ * W * κ) = Yv k r z z' g₀ W := by
    intro W
    rw [GlobalTheory.Amp.YInv.Yv_N hz hz' g₀ hn₁ hn₂]
    have : n₂ * (n₂⁻¹ * W * κ) = W * κ := by simp only [mul_assoc, c1]
    rw [this, GlobalTheory.Amp.YInv.Yv_K z z' g₀ W hκ.1 hκ.2]
  have hGGW : ∀ W : Mat k r, n₂⁻¹ * W * κ ∈ GG k r ↔ W ∈ GG k r := by
    intro W
    constructor
    · intro h
      have : W = n₂ * (n₂⁻¹ * W * κ) * κ⁻¹ := by
        simp only [mul_assoc, c1, Matrix.mul_nonsing_inv _ (GG_unit hκ.1), Matrix.mul_one]
      rw [this]; exact GG_mul (GG_mul hn₂G h) (GG_inv hκ.1)
    · intro h; exact GG_mul (GG_mul (GG_inv hn₂G) h) hκ.1
  have hSg' : ∀ W ∈ GG k r, Sg k r z' (n₂⁻¹ * W * κ) = Sg k r z' W :=
    fun W hW => ((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').1 W hW n₂⁻¹ hn₂iS κ hκ).2
  have hSg : ∀ W ∈ GG k r, Sg k r z (n₁ * g₀ * n₂ * (n₂⁻¹ * W * κ)) = Sg k r z (g₀ * W) := by
    intro W hW
    have : n₁ * g₀ * n₂ * (n₂⁻¹ * W * κ) = n₁ * (g₀ * W) * κ := by simp only [mul_assoc, c1]
    rw [this]; exact ((GlobalTheory.Amp.LInv.lengths_basic k r z hz).1 (g₀ * W) (GG_mul hg₀G hW) n₁ hn₁S κ hκ).2
  refine ⟨?_, ?_⟩
  · have hset : {n : Mt k r | Yv k r z z' (n₁ * g₀ * n₂) (Matrix.of n * g₁) = 0} =
        e ⁻¹' {ν | Yv k r z z' g₀ (Matrix.of ν * A) = 0} := by
      ext n; simp only [Set.mem_setOf_eq, Set.mem_preimage, key n, hYv]
    rw [hset, ← MeasurableEquiv.map_apply, he_map]
    exact hB.1
  · intro φ hφ R₀ y hR₀ hy
    have hl : ∀ (b : Mat k r) (x : Mt k r), Matrix.of (lmulM b x) = b * Matrix.of x := fun _ _ => rfl
    have hc : ∀ (b : Mat k r) (x : Mt k r), Matrix.of (conjM b x) = b * Matrix.of x * b⁻¹ := fun _ _ => rfl
    have hmeas : ∀ (f : Mt k r → Mt k r) (b c : Mat k r), (∀ x, Matrix.of (f x) = b * Matrix.of x * c) →
        Measurable f := by
      intro f b c h
      have : f = fun x => (Matrix.of.symm (b * Matrix.of x * c) : Mt k r) :=
        funext fun x => Matrix.of.injective (by rw [h] <;> rfl)
      rw [this]; exact measurable_two b c
    obtain ⟨P, hPm, hP⟩ : ∃ P : Mt k r → Mt k r, Measurable P ∧
        ∀ ν, Matrix.of (P ν) = n₂⁻¹ * Matrix.of ν * (A * κ) :=
      ⟨fun ν => Matrix.of.symm (n₂⁻¹ * Matrix.of ν * (A * κ)), measurable_two _ _, fun _ => rfl⟩

    have hsub : SubCut (Nset k r) (lebR k r β) (fun ν => ENNReal.ofReal s * φ (P ν)) := by
      refine ⟨(hφ.1.comp hPm).const_mul _, fun x hx => ?_⟩
      have hx0 : Matrix.of (P x) ∈ GG k r := by
        rw [hP, mul_assoc]; exact GG_mul (GG_inv hn₂G) (GG_mul hx.1 hAK)
      have h1 := hφ.2 (P x) hx0
      have hm1 : Measurable fun ρ : Mt k r => φ (lmulM (Matrix.of ρ) (P x)) :=
        hφ.1.comp (hmeas _ 1 (Matrix.of (P x)) fun ρ => by simp only [hl, Matrix.one_mul])
      have hm2 : Measurable (conjM n₂⁻¹ : Mt k r → Mt k r) := hmeas _ n₂⁻¹ n₂⁻¹⁻¹ fun x => hc _ _
      rw [lintegral_map hm1 hm2, lintegral_smul_measure] at h1
      have hPl : ∀ ρ : Mt k r, P (lmulM (Matrix.of ρ) x) = lmulM (Matrix.of (conjM n₂⁻¹ ρ)) (P x) := by
        intro ρ
        apply Matrix.of.injective
        simp only [hl, hc, hP, Matrix.nonsing_inv_nonsing_inv _ hu2, mul_assoc, c1]
      calc ∫⁻ ρ, ENNReal.ofReal s * φ (P (lmulM (Matrix.of ρ) x)) ∂lebR k r β
          = ENNReal.ofReal s * ∫⁻ ρ, φ (P (lmulM (Matrix.of ρ) x)) ∂lebR k r β :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal s * ∫⁻ ρ, φ (lmulM (Matrix.of (conjM n₂⁻¹ ρ)) (P x)) ∂lebR k r β := by
            congr 1; exact lintegral_congr fun ρ => by rw [hPl ρ]
        _ ≤ 1 := by first | exact h1 | (rw [smul_eq_mul] at h1; exact h1)
    have hmain := hB.2 (fun ν => ENNReal.ofReal s * φ (P ν)) hsub R₀ y hR₀ hy
    have hmem : ∀ n : Mt k r, rmulM g₁ n ∈ Eset k r z z' (n₁ * g₀ * n₂) R₀ y ↔
        rmulM A (e n) ∈ Eset k r z z' g₀ R₀ y := by
      intro n
      simp only [Eset, Set.mem_setOf_eq, GlobalTheory.SgInf.of_rmulM]
      rw [key n]
      generalize Matrix.of (e n) * A = W
      rw [hGGW W, hYv W]
      constructor
      · rintro ⟨hW, h1, h2, h3, h4⟩
        rw [hSg' W hW] at h1; rw [hSg W hW] at h2; exact ⟨hW, h1, h2, h3, h4⟩
      · rintro ⟨hW, h1, h2, h3, h4⟩
        exact ⟨hW, by rw [hSg' W hW]; exact h1, by rw [hSg W hW]; exact h2, h3, h4⟩
    have hpt : ∀ n : Mt k r, rmulM g₁ n = P (e n) := by
      intro n
      apply Matrix.of.injective
      rw [GlobalTheory.SgInf.of_rmulM, hP, key n]
      simp only [mul_assoc]
    have hint : ∫⁻ n, φ (rmulM g₁ n) * (Eset k r z z' (n₁ * g₀ * n₂) R₀ y).indicator 1 (rmulM g₁ n) ∂lebN k r
        = ∫⁻ ν, φ (P ν) * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A ν) ∂lebN k r := by
      calc _ = ∫⁻ n, (fun ν => φ (P ν) * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A ν)) (e n) ∂lebN k r := by
            refine lintegral_congr fun n => ?_
            have hind : (Eset k r z z' (n₁ * g₀ * n₂) R₀ y).indicator (1 : Mt k r → ℝ≥0∞) (rmulM g₁ n) =
                (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A (e n)) := by
              by_cases h : rmulM g₁ n ∈ Eset k r z z' (n₁ * g₀ * n₂) R₀ y
              · simp only [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem n).1 h), Pi.one_apply]
              · have h' : rmulM A (e n) ∉ Eset k r z z' g₀ R₀ y := fun h' => h ((hmem n).2 h')
                first
                  | rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
                  | rw [Set.indicator_of_not_mem h, Set.indicator_of_not_mem h']
                  | simp [Set.indicator, h, h']
            dsimp only
            rw [hind, hpt n]
        _ = ∫⁻ ν, φ (P ν) * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A ν) ∂((lebN k r).map e) :=
            (lintegral_map_equiv (fun ν => φ (P ν) * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A ν)) e).symm
        _ = _ := by rw [he_map]
    have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
    rw [hint, ENNReal.ofReal_div_of_pos hs,
      ENNReal.le_div_iff_mul_le (Or.inl hs0) (Or.inl ENNReal.ofReal_ne_top),
      mul_comm _ (ENNReal.ofReal s), ← lintegral_const_mul' (ENNReal.ofReal s) _ ENNReal.ofReal_ne_top]
    refine le_trans (le_of_eq ?_) hmain
    refine lintegral_congr fun ν => ?_
    simp only [mul_assoc]

end GlobalTheory.Amp.FibreVolumeGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneCountingHypotheses
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem one_le_rkR_of_ne {n : ℕ} (ε : Fin n → Bool) {a c : Fin n} (h : ε a ≠ ε c) : 1 ≤ rkR ε := by
  unfold rkR
  rw [le_min_iff]
  constructor
  · refine Finset.card_pos.2 ?_
    cases ha : ε a
    · exact ⟨c, by simpa [ha] using h⟩
    · exact ⟨a, by simp [ha]⟩
  · refine Finset.card_pos.2 ?_
    cases ha : ε a
    · exact ⟨a, by simp [ha]⟩
    · exact ⟨c, by simpa [ha] using h⟩

theorem countHyp_isKTypeOf_lowKSub : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) := by
  intro B Cg n₀ d p q b hn₀ hC v
  obtain ⟨-, -, -, -, -, -, hrk, -, -, -, -, -, h, -, hgap, -, -, h8, -, -⟩ :=
    countHyp_numerics B Cg n₀ d p q b hn₀ hC
  refine GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub _ _ _ _ _ (hC.1 v).1 (hC.1 v).2.1 fun a c hac => ?_
  have hq : (1 : ℝ) ≤ q := by
    have := one_le_rkR_of_ne _ hac
    rw [hrk v] at this
    exact_mod_cast this
  have hg : h ≤ |B.lam v a - B.lam v c| := hgap v a c hac
  have hn : (0 : ℝ) ≤ B.I.n := Nat.cast_nonneg _
  nlinarith

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryIwasawaIntegrationFormulaRealPlace
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem iwasawaFormula : IwasawaFormula := by
  intro n ε p q hp hq a j hj W hW c μN μM μK hc hN hM hK0 hK1 hKinv φ hφ
  obtain ⟨κ, -, -, hκ⟩ := _root_.GlobalTheory.IwasawaShape.iwasawa_shape n ε p q hp hq a j hj W hW μN μM μK hN hM hK0 hK1 hKinv
  have hconst := _root_.GlobalTheory.IwConst.iwasawa_constant n ε p q hp hq a j hj W hW μN μM μK hN hM hK0 hK1 hKinv c κ hc hκ
  rw [hκ φ hφ, ← mul_assoc, hconst]

end GlobalTheory.FlagMeas
end

