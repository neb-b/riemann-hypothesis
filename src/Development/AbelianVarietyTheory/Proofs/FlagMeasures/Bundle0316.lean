module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0297
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0017
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaProductGaugeSandwichNearOne
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwSand

theorem exists_le_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] (f g : V → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hfs : ∀ s : ℝ, 0 ≤ s → ∀ v, f (s • v) = s * f v)
    (hgs : ∀ s : ℝ, 0 ≤ s → ∀ v, g (s • v) = s * g v) (hg0 : ∀ v, 0 ≤ g v) (hd : ∀ v, g v = 0 → v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v, f v ≤ C * g v := by
  have hf0 : f 0 = 0 := by simpa using hfs 0 le_rfl 0
  have hg0' : g 0 = 0 := by simpa using hgs 0 le_rfl 0
  rcases (Metric.sphere (0 : V) 1).eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun v => ?_⟩
    have hv : v = 0 := by
      by_contra hv
      have hmem : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
        simp [norm_smul, hv]
      rw [hS] at hmem
      exact hmem
    subst hv
    simp [hf0, hg0']
  · have hK := isCompact_sphere (0 : V) 1
    obtain ⟨u0, hu0, hmin⟩ := hK.exists_isMinOn hS hg.continuousOn
    obtain ⟨u1, -, hmax⟩ := hK.exists_isMaxOn hS hf.continuousOn
    have hm : 0 < g u0 := by
      rcases (hg0 u0).lt_or_eq with h | h
      · exact h
      · exfalso
        have h0 := hd u0 h.symm
        subst h0
        simp at hu0
    refine ⟨max (f u1) 0 / g u0 + 1, by positivity, fun v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp [hf0, hg0']
    have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hw : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
      simp [norm_smul, hr.ne']
    have hvw : v = ‖v‖ • (‖v‖⁻¹ • v) := by
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hfv : f v = ‖v‖ * f (‖v‖⁻¹ • v) := by
      conv_lhs => rw [hvw]
      exact hfs _ hr.le _
    have hgv : g v = ‖v‖ * g (‖v‖⁻¹ • v) := by
      conv_lhs => rw [hvw]
      exact hgs _ hr.le _
    have h1 : f (‖v‖⁻¹ • v) ≤ f u1 := isMaxOn_iff.mp hmax _ hw
    have h2 : g u0 ≤ g (‖v‖⁻¹ • v) := isMinOn_iff.mp hmin _ hw
    have hgw : 0 ≤ g (‖v‖⁻¹ • v) := hg0 _
    rw [hfv, hgv]
    calc ‖v‖ * f (‖v‖⁻¹ • v) ≤ ‖v‖ * max (f u1) 0 :=
          mul_le_mul_of_nonneg_left (h1.trans (le_max_left _ _)) hr.le
      _ = max (f u1) 0 / g u0 * (‖v‖ * g u0) := by field_simp
      _ ≤ max (f u1) 0 / g u0 * (‖v‖ * g (‖v‖⁻¹ • v)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hr.le) (by positivity)
      _ ≤ (max (f u1) 0 / g u0 + 1) * (‖v‖ * g (‖v‖⁻¹ • v)) :=
          mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hr.le hgw)

variable {n : ℕ}

theorem nrm_le_add_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : nrm X ≤ nrm Y + nrm (X - Y) := by
  have h := nrm_add_le Y (X - Y)
  rwa [add_sub_cancel] at h

theorem abs_nrm_sub_le (X Y : Matrix (Fin n) (Fin n) ℂ) : |nrm X - nrm Y| ≤ nrm (X - Y) := by
  have h1 := nrm_le_add_sub X Y
  have h2 := nrm_le_add_sub Y X
  have h3 : nrm (Y - X) = nrm (X - Y) := by rw [← neg_sub, nrm_neg]
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem abs_len_sub_le {d : ℕ} (x y : Fin d → ℝ) : |len x - len y| ≤ len (x - y) := by
  have h1 : len x ≤ len y + len (x - y) := by
    have h := len_add_le y (x - y)
    rwa [add_sub_cancel] at h
  have h2 : len y ≤ len x + len (y - x) := by
    have h := len_add_le x (y - x)
    rwa [add_sub_cancel] at h
  have h3 : len (y - x) = len (x - y) := by rw [← neg_sub, len_neg]
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem nrm_prod_sub_le (a b c X Y Z : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (hs1 : s ≤ 1) (ha : nrm (a - 1) ≤ s)
    (hb : nrm (b - 1) ≤ s) (hc : nrm (c - 1) ≤ s) (hX : nrm (a - 1 - X) ≤ s ^ 2) (hY : nrm (b - 1 - Y) ≤ s ^ 2)
    (hZ : nrm (c - 1 - Z) ≤ s ^ 2) : nrm (a * b * c - 1 - (X + Y + Z)) ≤ 7 * s ^ 2 := by
  have hs0 : 0 ≤ s := (nrm_nonneg _).trans ha
  have key : a * b * c - 1 - (X + Y + Z) =
      ((a - 1 - X) + (b - 1 - Y) + (c - 1 - Z)) +
        ((a - 1) * (b - 1) + (a - 1) * (c - 1) + (b - 1) * (c - 1)) + (a - 1) * (b - 1) * (c - 1) := by
    noncomm_ring
  have pr2 : ∀ P Q : Matrix (Fin n) (Fin n) ℂ, nrm P ≤ s → nrm Q ≤ s → nrm (P * Q) ≤ s ^ 2 := by
    intro P Q hP hQ
    calc nrm (P * Q) ≤ nrm P * nrm Q := nrm_mul_le _ _
      _ ≤ s * s := mul_le_mul hP hQ (nrm_nonneg _) hs0
      _ = s ^ 2 := (sq s).symm
  have e1 : nrm ((a - 1 - X) + (b - 1 - Y) + (c - 1 - Z)) ≤ 3 * s ^ 2 := by
    have := nrm_add_le ((a - 1 - X) + (b - 1 - Y)) (c - 1 - Z)
    have := nrm_add_le (a - 1 - X) (b - 1 - Y)
    linarith
  have e2 : nrm ((a - 1) * (b - 1) + (a - 1) * (c - 1) + (b - 1) * (c - 1)) ≤ 3 * s ^ 2 := by
    have := nrm_add_le ((a - 1) * (b - 1) + (a - 1) * (c - 1)) ((b - 1) * (c - 1))
    have := nrm_add_le ((a - 1) * (b - 1)) ((a - 1) * (c - 1))
    have := pr2 _ _ ha hb
    have := pr2 _ _ ha hc
    have := pr2 _ _ hb hc
    linarith
  have e3 : nrm ((a - 1) * (b - 1) * (c - 1)) ≤ s ^ 2 := by
    calc nrm ((a - 1) * (b - 1) * (c - 1)) ≤ nrm ((a - 1) * (b - 1)) * nrm (c - 1) := nrm_mul_le _ _
      _ ≤ s ^ 2 * s := mul_le_mul (pr2 _ _ ha hb) hc (nrm_nonneg _) (sq_nonneg _)
      _ ≤ s ^ 2 * 1 := mul_le_mul_of_nonneg_left hs1 (sq_nonneg _)
      _ = s ^ 2 := mul_one _
  rw [key]
  have := nrm_add_le (((a - 1 - X) + (b - 1 - Y) + (c - 1 - Z)) +
        ((a - 1) * (b - 1) + (a - 1) * (c - 1) + (b - 1) * (c - 1))) ((a - 1) * (b - 1) * (c - 1))
  have := nrm_add_le ((a - 1 - X) + (b - 1 - Y) + (c - 1 - Z))
        ((a - 1) * (b - 1) + (a - 1) * (c - 1) + (b - 1) * (c - 1))
  linarith

theorem real_sandwich {C η s σ γ : ℝ} (hC : 0 < C) (hη : 0 < η) (hγ : 0 ≤ γ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2)
    (hs' : s ≤ η / (1 + η) / (14 * C)) (h1 : s ≤ C * γ + s ^ 2) (h2 : |σ - γ| ≤ 7 * s ^ 2) :
    γ ≤ (1 + η) * σ ∧ σ ≤ (1 + η) * γ ∧ s ≤ 2 * C * γ := by
  have hδη : η / (1 + η) ≤ η := div_le_self hη.le (by linarith)
  have hδ : η / (1 + η) * (1 + η) = η := div_mul_cancel₀ η (by positivity)
  have h3 : s ≤ 2 * C * γ := by nlinarith [mul_nonneg hs0 (sub_nonneg.2 hs)]
  have h4 : s * (14 * C) ≤ η / (1 + η) := by
    rwa [le_div_iff₀ (by positivity)] at hs'
  have h5 : 7 * s ^ 2 ≤ η / (1 + η) * γ := by
    nlinarith [mul_le_mul_of_nonneg_left h3 hs0, mul_le_mul_of_nonneg_right h4 hγ]
  obtain ⟨hl, hr⟩ := abs_le.mp h2
  refine ⟨?_, ?_, h3⟩
  · have hpos : 0 ≤ (1 + η) * (σ - γ + η / (1 + η) * γ) :=
      mul_nonneg (by linarith) (by linarith)
    have hδγ : η / (1 + η) * (1 + η) * γ = η * γ := by rw [hδ]
    nlinarith
  · nlinarith [mul_le_mul_of_nonneg_right hδη hγ]

theorem gau_sandwich : ∀ (n : ℕ) (ε : Fin n → Bool) (SN SM MainNotions : Set (Formalism.REAL.UJ ε)), ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε SN EN → IsCut ε SM EM → IsCut ε MainNotions EK → IsON EL → (∀ v, gau EN EM EK EL v = 0 → v = 0) → ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ ∀ u ∈ SN, ∀ m ∈ SM, ∀ k ∈ MainNotions, nrm (uMat u - 1) < t → nrm (uMat m - 1) < t → nrm (uMat k - 1) < t → ∀ σ γ : ℝ, σ = max (nrm (uMat (u * m * k) - 1)) (len (crd EL (uMat k - 1))) → γ = gau EN EM EK EL (crd EN (uMat u - 1), crd EM (uMat m - 1), crd EK (uMat k - 1)) → γ ≤ (1 + η) * σ ∧ σ ≤ (1 + η) * γ ∧ nrm (uMat u - 1) ≤ C * γ ∧ nrm (uMat m - 1) ≤ C * γ ∧ nrm (uMat k - 1) ≤ C * γ := by
  intro n ε SN SM MainNotions dN dM dK dL EN EM EK EL hN hM hK hL hdef
  obtain ⟨C0, hC0, hC0le⟩ := exists_le_mul
    (fun v : (Fin dN → ℝ) × (Fin dM → ℝ) × (Fin dK → ℝ) => max (len v.1) (max (len v.2.1) (len v.2.2)))
    (gau EN EM EK EL)
    ((continuous_len.comp continuous_fst).max ((continuous_len.comp (continuous_fst.comp continuous_snd)).max
      (continuous_len.comp (continuous_snd.comp continuous_snd))))
    (continuous_gau EN EM EK EL)
    (by
      intro s hs v
      simp only [Prod.smul_fst, Prod.smul_snd, len_smul, abs_of_nonneg hs]
      rw [mul_max_of_nonneg _ _ hs, mul_max_of_nonneg _ _ hs])
    (fun s hs v => gau_smul EN EM EK EL s hs v) (gau_nonneg EN EM EK EL) hdef
  refine ⟨2 * C0, by positivity, fun η hη => ?_⟩
  refine ⟨min (1 / 2) (η / (1 + η) / (14 * C0)), lt_min (by norm_num) (by positivity), ?_⟩
  intro u hu m hm k hk hut hmt hkt σ γ hσ hγ
  set s := max (nrm (uMat u - 1)) (max (nrm (uMat m - 1)) (nrm (uMat k - 1))) with hs_def
  have hst : s < min (1 / 2) (η / (1 + η) / (14 * C0)) := max_lt hut (max_lt hmt hkt)
  have hs12 : s ≤ 1 / 2 := (hst.trans_le (min_le_left _ _)).le
  have hsη : s ≤ η / (1 + η) / (14 * C0) := (hst.trans_le (min_le_right _ _)).le
  have hsu : nrm (uMat u - 1) ≤ s := le_max_left _ _
  have hsm : nrm (uMat m - 1) ≤ s := (le_max_left _ _).trans (le_max_right _ _)
  have hsk : nrm (uMat k - 1) ≤ s := (le_max_right _ _).trans (le_max_right _ _)
  have hs0 : 0 ≤ s := (nrm_nonneg _).trans hsu
  have hs2 : ∀ x : ℝ, 0 ≤ x → x ≤ s → x ^ 2 ≤ s ^ 2 := fun x hx hxs => pow_le_pow_left₀ hx hxs 2

  have aN := GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt n ε SN dN EN hN u hu
  have aM := GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt n ε SM dM EM hM m hm
  have aK := GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt n ε MainNotions dK EK hK k hk
  set X := cmb EN (crd EN (uMat u - 1))
  set Y := cmb EM (crd EM (uMat m - 1))
  set Z := cmb EK (crd EK (uMat k - 1))
  have aN' : nrm (uMat u - 1 - X) ≤ s ^ 2 := aN.trans (hs2 _ (nrm_nonneg _) hsu)
  have aM' : nrm (uMat m - 1 - Y) ≤ s ^ 2 := aM.trans (hs2 _ (nrm_nonneg _) hsm)
  have aK' : nrm (uMat k - 1 - Z) ≤ s ^ 2 := aK.trans (hs2 _ (nrm_nonneg _) hsk)
  have hmul : uMat (u * m * k) = uMat u * uMat m * uMat k := by
    simp [uMat]
  have hprod : nrm (uMat (u * m * k) - 1 - (X + Y + Z)) ≤ 7 * s ^ 2 := by
    rw [hmul]
    exact nrm_prod_sub_le _ _ _ X Y Z s (by linarith) hsu hsm hsk aN' aM' aK'
  have hγ' : γ = max (nrm (X + Y + Z)) (len (crd EL Z)) := by
    rw [hγ]; rfl
  have d1 : |nrm (uMat (u * m * k) - 1) - nrm (X + Y + Z)| ≤ 7 * s ^ 2 :=
    (abs_nrm_sub_le _ _).trans hprod
  have d2 : |len (crd EL (uMat k - 1)) - len (crd EL Z)| ≤ 7 * s ^ 2 := by
    refine (abs_len_sub_le _ _).trans ?_
    rw [← crd_sub]
    refine (len_crd_le hL _).trans ?_
    nlinarith [sq_nonneg s]
  have hσγ : |σ - γ| ≤ 7 * s ^ 2 := by
    rw [hσ, hγ']
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le d1 d2)

  have hγ0 : 0 ≤ γ := by rw [hγ]; exact gau_nonneg _ _ _ _ _
  have hbound := hC0le (crd EN (uMat u - 1), crd EM (uMat m - 1), crd EK (uMat k - 1))
  rw [← hγ] at hbound
  have lN : len (crd EN (uMat u - 1)) ≤ C0 * γ := (le_max_left _ _).trans hbound
  have lM : len (crd EM (uMat m - 1)) ≤ C0 * γ := ((le_max_left _ _).trans (le_max_right _ _)).trans hbound
  have lK : len (crd EK (uMat k - 1)) ≤ C0 * γ := ((le_max_right _ _).trans (le_max_right _ _)).trans hbound
  have near : ∀ {d : ℕ} (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin n) ℂ), IsON E →
      len (crd E W) ≤ C0 * γ → nrm (W - cmb E (crd E W)) ≤ s ^ 2 → nrm W ≤ C0 * γ + s ^ 2 := by
    intro d E W hE h1 h2
    have h3 := nrm_le_add_sub W (cmb E (crd E W))
    rw [nrm_cmb hE] at h3
    linarith
  have bN := near EN _ hN.isON lN aN'
  have bM := near EM _ hM.isON lM aM'
  have bK := near EK _ hK.isON lK aK'
  have h1 : s ≤ C0 * γ + s ^ 2 := max_le bN (max_le bM bK)
  obtain ⟨r1, r2, r3⟩ := real_sandwich hC0 hη hγ0 hs0 hs12 hsη h1 hσγ
  refine ⟨r1, r2, ?_, ?_, ?_⟩ <;> linarith

end GlobalTheory.IwSand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeSpanEInfToO
section
open NumberField

namespace GlobalTheory.SpanInfDenominators

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (Λ : Submodule (𝓞 E) V) (x : V)
    (hx : x ∈ Submodule.span E (Λ : Set V)) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • x ∈ Λ := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, hcy⟩ := hy
    obtain ⟨c', hc', hcz⟩ := hz
    refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
    have e1 : (c * c') • y = c' • (c • y) := by rw [mul_comm, mul_smul]
    have e2 : (c * c') • z = c • (c' • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact Λ.add_mem (Λ.smul_mem _ hcy) (Λ.smul_mem _ hcz)
  | smul a y _ hy =>
    obtain ⟨c, hc, hcy⟩ := hy
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) a
    have hd : (d : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero d.2
    refine ⟨(d : 𝓞 E) * c, mul_ne_zero hd hc, ?_⟩
    have key : ((d : 𝓞 E) * c) • (a • y) = n • (c • y) := by
      rw [← algebraMap_smul E ((d : 𝓞 E) * c) (a • y), ← algebraMap_smul E n (c • y),
        ← algebraMap_smul E c y, smul_smul, smul_smul, map_mul]
      congr 1
      rw [← hnd]
      ring
    rw [key]
    exact Λ.smul_mem n hcy

theorem le_spanE_inf_toO {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsFullLattice E Λ) (U : Submodule E S.V) :
    U ≤ Formalism.MainNotions.S.Lat.spanE S (Λ ⊓ Formalism.MainNotions.S.Lat.toO S U) := by
  intro x hx
  have hxs : x ∈ Submodule.span E (Λ : Set S.V) := by
    rw [hΛ.span_eq_top]
    trivial
  obtain ⟨c, hc, hcx⟩ := exists_smul_mem Λ x hxs
  have hcU : c • x ∈ U := by
    rw [← algebraMap_smul E c x]
    exact U.smul_mem _ hx
  have hmem : c • x ∈ Λ ⊓ Formalism.MainNotions.S.Lat.toO S U := Submodule.mem_inf.2 ⟨hcx, hcU⟩
  have hc' : algebraMap (𝓞 E) E c ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]
  have hx' : x = (algebraMap (𝓞 E) E c)⁻¹ • (c • x) := by
    rw [← algebraMap_smul E c x, smul_smul, inv_mul_cancel₀ hc', one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.SpanInfDenominators
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureFundamentalDomainLtOfDeepPointBound
section
open MeasureTheory NumberField Formalism.MainNotions.S GlobalTheory.Count

namespace GlobalTheory.DeepArith

theorem one_le_f (I : AutInst) : 1 ≤ I.f := Module.finrank_pos

theorem one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  unfold AutInst.rd
  refine Real.one_le_rpow ?_ (by positivity)
  have h := Int.one_le_abs (discr_ne_zero I.E)
  exact_mod_cast h

theorem deep_mul_volume_le (hV : GlobalTheory.FlagMeas.AbsoluteVolume) (B : RowsAut) (Cg : ℝ) (n₀ : ℕ)
    (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ) (c : InfinitePlace B.I.F → ℝ) (x : B.I.GA)
    (hn₀ : 8 ≤ n₀) (hq : 1 ≤ q) (hC : CountHyp B Cg n₀ d p q b) (hc : ∀ v, IsGauge (B.I.ε v) (c v))
    (hx : least B.I x < tauStar B q b) :
    B.I.muA B.μf B.fund < ⊤ ∧
    (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * Real.sqrt B.I.f * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b
        (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ (16 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) *
      (6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^
        GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f *
      (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (∏ v, c v) /
      (B.μf (B.I.Kg B.g)).toReal * (B.I.muA B.μf B.fund).toReal ≤
      Real.exp (-((B.I.n : ℝ) ^ 2 * B.I.f)) := by
  obtain ⟨-, hsig, hn', hq2, -, -, hb, -, -, hg, -⟩ := hC
  have hn : 8 ≤ B.I.n := hn₀.trans hn'
  have hc0 : ∀ v, 0 < c v := fun v => by
    obtain ⟨c', h0, -, hu⟩ := GlobalTheory.GaugeConst.exists_unique_isGauge B.I.n (B.I.ε v)
    rw [hu _ (hc v)]; exact h0
  have hf := one_le_f B.I
  have hrd := one_le_rd B.I
  have hnR : (8 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  have hfR : (1 : ℝ) ≤ B.I.f := by exact_mod_cast hf
  have hgR : (1 : ℝ) ≤ B.g := by exact_mod_cast hg
  have hfr : B.I.rd ≤ B.I.f * B.I.rd := by nlinarith
  have hX : 2 * (B.I.f * B.I.rd) ≤ bigX B b := by
    have h1 : (2 : ℝ) ≤ B.g * b := by nlinarith
    have h2 : (2 : ℝ) ≤ B.I.n * (B.g * b) := by nlinarith
    have : bigX B b = (B.I.n * (B.g * b)) * (B.I.f * B.I.rd) := by unfold bigX; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right h2 (by linarith)
  have hX2 : 2 ≤ bigX B b := by linarith
  have hvol := hV B.I p q hsig hq2 hn (bigX B b) hX2 (by linarith) (by nlinarith) c B.μf hc
  obtain ⟨hcov, -⟩ := _root_.GlobalTheory.CovolRat.covol_eq_inter_fund B.I B.μf B.fund Set.univ B.fund_spec MeasurableSet.univ
    (fun _ _ _ _ => Set.mem_univ _)
  obtain ⟨hidx, hKg0, hKfin⟩ := GlobalTheory.CongIndex.measure_Kset_le B.I B.μf B.g hg
  have hKgfin : B.μf (B.I.Kg B.g) ≠ ⊤ :=
    ne_top_of_le_ne_top hKfin.ne (measure_mono fun _ h => h.1)
  unfold GlobalTheory.FlagMeas.gaugeVol at hvol
  rw [hcov, Set.univ_inter, ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top) (Or.inl hKfin.ne)] at hvol
  set N : ℕ := B.I.n ^ 2 * B.I.f with hN
  set m : ℝ := (B.μf (B.I.Kg B.g)).toReal with hm
  have hm0 : 0 < m := ENNReal.toReal_pos hKg0.ne' hKgfin
  have hcp : 0 < ∏ v, c v := Finset.prod_pos fun v _ => hc0 v
  have hXp : 0 < bigX B b := by linarith
  have hgp : (0 : ℝ) < B.g := by linarith
  set Y : ℝ := (B.g : ℝ) ^ (2 * N) * bigX B b ^ N with hY
  have hY0 : 0 < Y := by positivity
  have hv2 : ENNReal.ofReal (∏ v, c v) * B.I.muA B.μf B.fund ≤ ENNReal.ofReal (Y * m) := by
    refine (hvol.trans (mul_le_mul' le_rfl hidx)).trans_eq ?_
    rw [show Y * m = bigX B b ^ N * ((B.g : ℝ) ^ (2 * N) * m) by rw [hY]; ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      hm, ENNReal.ofReal_toReal hKgfin, ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hfin : B.I.muA B.μf B.fund < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 hcp).ne'] at hv2
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hv2)
  refine ⟨hfin, ?_⟩
  have hv3 : (∏ v, c v) * (B.I.muA B.μf B.fund).toReal ≤ Y * m := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcp.le, ENNReal.toReal_ofReal (by positivity)] at this
  have hl : 0 < least B.I x := ((GlobalTheory.CountSteps.steps B.I x 1 one_pos).2.2.2.2.2.2.2.2 (by omega)).1
  have ha := (GlobalTheory.deep_region_exponents B.I.n B.I.f q B.I.rd B.g b (least B.I x) hn hf hq hq2 hrd hb hgR hl
    hx.le).2
  have hbe : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * N + N) =
      Real.sqrt B.I.n * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe
    have : (B.I.n : ℝ) ^ ((3 : ℝ) / 2) = B.I.n * Real.sqrt B.I.n := by
      rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
        Real.sqrt_eq_rpow]
    rw [this]; norm_num
  have hd : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B = N := rfl
  rw [hd, hbe, show 16 * q * N = 2 * (8 * q * N) by ring]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh
  rw [← hN] at ha
  generalize (2 * ((B.I.n : ℝ) ^ 2 * Real.sqrt B.I.f * B.g * B.I.rd * (2 * least B.I x) ^ ((1 : ℝ) / q) / 4) *
    Real.sqrt B.I.f * (Real.sqrt B.I.n * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) +
      3 * ((8 * q * N + N : ℕ) : ℝ))) ^ (2 * (8 * q * N)) = u at ha ⊢
  generalize (6 * (Real.sqrt B.I.n * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) +
      3 * ((8 * q * N + N : ℕ) : ℝ))) ^ N = v at ha ⊢
  generalize (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * N) = w at ha ⊢
  have h1 : u * v * Real.exp B.I.f * w ≤ Real.exp (-(N : ℝ)) / Y := by
    rw [le_div_iff₀ hY0]
    refine le_of_eq_of_le ?_ ha
    rw [hY]; unfold bigX; ring
  have hNc : (N : ℝ) = (B.I.n : ℝ) ^ 2 * (B.I.f : ℝ) := by rw [hN]; push_cast; ring
  calc u * v * Real.exp B.I.f * w * (∏ v, c v) / m * (B.I.muA B.μf B.fund).toReal
      ≤ Real.exp (-(N : ℝ)) / Y * (∏ v, c v) / m * (B.I.muA B.μf B.fund).toReal := by gcongr
    _ = Real.exp (-(N : ℝ)) / Y / m * ((∏ v, c v) * (B.I.muA B.μf B.fund).toReal) := by ring
    _ ≤ Real.exp (-(N : ℝ)) / Y / m * (Y * m) := by gcongr
    _ = Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) := by
        rw [hNc]; field_simp

end GlobalTheory.DeepArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemUnitaryGroupGramMatrixIffMapSymm
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

private theorem host_star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  haveI := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ (star x) = starRingEnd ℂ (D.host.φ₀ x) :=
    NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) (φ := D.host.φ₀) (x := x)
  have h2 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := by
    rw [← D.embE_φ₀, RingHom.comp_apply, RingHom.comp_apply, D.embE_conj, D.starLL_cx]
  rw [h1, h2]

theorem mem_UJ_gramN_iff_map_symm : ∀ (D : D7) (X : HidaSetting D) (g : GL (Fin (D.R.N 0)) D.host.E), g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) ↔ (((g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map X.ιE.symm).map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map X.ιE.symm = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm := by
  intro D X g

  have hc : ∀ y : D.host.E, X.ιE.symm ((Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) y) =
      starRingEnd X.B.I.E (X.ιE.symm y) := by
    intro y
    apply X.ιE.injective
    rw [starRingEnd_apply, X.ιE_conj, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact host_star_eq_conj D y
  have hm : ∀ A B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E,
      (A * B).map X.ιE.symm = A.map X.ιE.symm * B.map X.ιE.symm := by
    intro A B
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, map_sum]
  have hb : ∀ A : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E,
      (A.map X.ιE.symm).map (starRingEnd X.B.I.E) =
        (A.map (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)).map X.ιE.symm := by
    intro A
    ext i j
    exact (hc (A i j)).symm
  have hT : ∀ A : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E,
      Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) A =
        (A.map (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E))ᵀ := by
    intro A
    unfold Formalism.UG.cT
    first
      | rfl
      | (ext i j; rfl)
  have hinj : Function.Injective
      (fun A : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E => A.map X.ιE.symm) :=
    Matrix.map_injective X.ιE.symm.injective
  refine Iff.trans (Iff.rfl : _ ↔ Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)
      (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) * Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) *
      (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) ?_
  rw [hT, hb, ← Matrix.transpose_map (f := ⇑X.ιE.symm), ← hm, ← hm]
  exact hinj.eq_iff.symm

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalMatrixRepresentsAdelicPointInFrame
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.St

theorem repF_of_rational : ∀ (D : D7) (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), IsAdeleIso X ιA → ∀ (h : X.B.I.Gf) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E), X.B.I.fmat h = γ₀.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), y.1.1 = (y₀.map X.ιE).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) → RepF X wt ιA h y := by
  intro D X wt ιA hA h γ₀ y₀ hf hq y hy j
  have hs : ∀ i, ιA.symm (y.1.1 i j) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (y₀ i j) := by
    intro i
    rw [hy, RingEquiv.symm_apply_eq, Matrix.map_apply, Matrix.map_apply, hA.1]
  simp_rw [hs]
  have hl : X.B.I.fmat h *ᵥ qA X wt j =
      fun k => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((γ₀ *ᵥ X.crd (qFr wt j)) k) := by
    rw [hf]
    funext k
    show (γ₀.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ
      ((Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) ∘ X.crd (qFr wt j))) k = _
    rw [← RingHom.map_mulVec]
  rw [hl, hq j]
  funext k
  set_option synthInstance.maxHeartbeats 100000 in
    simp [qA, incl, Finset.sum_apply, map_sum, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.St
end

