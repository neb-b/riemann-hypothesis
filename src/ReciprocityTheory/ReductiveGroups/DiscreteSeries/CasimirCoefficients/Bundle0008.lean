module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IdThmA
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}

namespace IdA

lemma isOpen_omega : IsOpen (OmegaSet n) := by
  have e : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z
    simp [OmegaSet]
  rw [e]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_ne_fun (contDiff_lead (m := 0) _).continuous continuous_const

lemma continuous_toMK : Continuous fun k : KG ε => toMK k :=
  (continuous_toM ε).comp continuous_subtype_val

lemma continuous_toMK_inv : Continuous fun k : KG ε => toMK k⁻¹ :=
  continuous_toMK.comp continuous_inv

lemma continuous_P (T : KType ε Λ) : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ := by
  have h : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  exact (h.mul continuous_const).mul (h.comp continuous_inv)

lemma continuous_cline (a b : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun p : ℂ × KG ε => toMK p.2⁻¹ * (a + p.1 • b) * toMK p.2 :=
  ((continuous_toMK_inv.comp continuous_snd).matrix_mul
    (continuous_const.add (continuous_fst.smul continuous_const))).matrix_mul
    (continuous_toMK.comp continuous_snd)

lemma cline_eq (k : KG ε) (a b : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    toMK k⁻¹ * (a + s • b) * toMK k = toMK k⁻¹ * a * toMK k + s • (toMK k⁻¹ * b * toMK k) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

lemma hasDerivAt_cline (k : KG ε) (a b : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    HasDerivAt (fun s : ℂ => toMK k⁻¹ * (a + s • b) * toMK k) (toMK k⁻¹ * b * toMK k) s := by
  have h := ((hasDerivAt_id s).smul_const (toMK k⁻¹ * b * toMK k)).const_add (toMK k⁻¹ * a * toMK k)
  simp only [id, one_smul] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => cline_eq k a b s)

lemma hasDerivAt_intK [CompactSpace (KG ε)] (T : KType ε Λ) (F F' : ℂ → KG ε → (T.V →L[ℂ] T.V))
    {S : Set ℂ} (hS : IsOpen S)
    (hF : ContinuousOn (fun p : ℂ × KG ε => F p.1 p.2) (S ×ˢ Set.univ))
    (hF' : ContinuousOn (fun p : ℂ × KG ε => F' p.1 p.2) (S ×ˢ Set.univ))
    (hd : ∀ s ∈ S, ∀ k, HasDerivAt (fun s => F s k) (F' s k) s) {s0 : ℂ} (hs0 : s0 ∈ S) :
    HasDerivAt (fun s => ∫ k, F s k ∂(muK ε)) (∫ k, F' s0 k ∂(muK ε)) s0 := by
  have : IsFiniteMeasureOnCompacts (muK ε) := by unfold muK; infer_instance
  have : IsFiniteMeasure (muK ε) := inferInstance
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hS s0 hs0
  have hcl : Metric.closedBall s0 (r / 2) ⊆ S :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hK : IsCompact (Metric.closedBall s0 (r / 2) ×ˢ (Set.univ : Set (KG ε))) :=
    (isCompact_closedBall s0 _).prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hF'.mono (Set.prod_mono hcl le_rfl))
  have hin : ∀ s ∈ Metric.ball s0 (r / 2), s ∈ S := fun s hs => hcl (Metric.ball_subset_closedBall hs)
  have hc : ∀ s ∈ S, Continuous (F s) := fun s hs =>
    hF.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hs, trivial⟩
  have hc' : Continuous (F' s0) :=
    hF'.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hs0, trivial⟩
  have hi : Integrable (F s0) (muK ε) :=
    integrableOn_univ.mp ((hc s0 hs0).continuousOn.integrableOn_compact isCompact_univ)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (Metric.ball_mem_nhds s0 (half_pos hr))
    (Filter.eventually_of_mem (Metric.ball_mem_nhds s0 (half_pos hr))
      fun s hs => (hc s (hin s hs)).aestronglyMeasurable)
    hi hc'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k s hs => hC (s, k) ⟨Metric.ball_subset_closedBall hs, trivial⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k s hs => hd s (hin s hs) k)).2

def dPhi2 (μ : Fin n → ℤ) (p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  fderiv ℂ (PhiM μ) p.1 p.2

lemma contDiffAt_dPhi2 (μ : Fin n → ℤ) {p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ}
    (hp : p.1 ∈ OmegaSet n) : ContDiffAt ℂ 1 (dPhi2 μ) p := by
  have hf : ContDiffAt ℂ 2 (Function.uncurry fun (_ : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)
      (y : Matrix (Fin n) (Fin n) ℂ) => PhiM μ y) (p, p.1) :=
    (contDiffAt_phiM μ hp (m := 2)).comp (p, p.1) contDiffAt_snd
  exact (hf.fderiv contDiffAt_fst (by norm_num)).clm_apply contDiffAt_snd

lemma continuousOn_dPhi2 (μ : Fin n → ℤ) : ContinuousOn (dPhi2 μ) (OmegaSet n ×ˢ Set.univ) :=
  fun p hp => (contDiffAt_dPhi2 μ hp.1).continuousAt.continuousWithinAt

lemma continuousOn_fderiv_dPhi2 (μ : Fin n → ℤ) :
    ContinuousOn (fderiv ℂ (dPhi2 μ)) (OmegaSet n ×ˢ Set.univ) :=
  ContDiffOn.continuousOn_fderiv_of_isOpen (fun p hp => (contDiffAt_dPhi2 μ hp.1).contDiffWithinAt)
    (isOpen_omega.prod isOpen_univ) le_rfl

end IdA

theorem line_int_differentiableAt (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hUo : IsOpen U) (hU : ∀ z ∈ U, ∀ k : KG ε, toMK k⁻¹ * z * toMK k ∈ OmegaSet n)
    (a₀ a₁ b₀ b₁ : Matrix (Fin n) (Fin n) ℂ) {s₀ : ℂ} (hs₀ : a₀ + s₀ • a₁ ∈ U) :
    DifferentiableAt ℂ (fun s : ℂ => ∫ k, IdA.dPhi2 μ (toMK k⁻¹ * (a₀ + s • a₁) * toMK k,
      toMK k⁻¹ * (b₀ + s • b₁) * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε)) s₀ := by
  have := compactSpace_KG ε
  have hS : IsOpen ((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) :=
    hUo.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hγ : Continuous fun p : ℂ × KG ε =>
      (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2, toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2) :=
    (IdA.continuous_cline a₀ a₁).prodMk (IdA.continuous_cline b₀ b₁)
  have hmaps : Set.MapsTo (fun p : ℂ × KG ε =>
      (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2, toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2))
      (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ) (OmegaSet n ×ˢ Set.univ) :=
    fun p hp => ⟨hU _ hp.1 p.2, trivial⟩
  have hP : ContinuousOn (fun p : ℂ × KG ε => T.op p.2 * projW T * T.op p.2⁻¹)
      (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ) :=
    ((IdA.continuous_P T).comp continuous_snd).continuousOn
  have hd1 : Continuous fun p : ℂ × KG ε => (toMK p.2⁻¹ * a₁ * toMK p.2, toMK p.2⁻¹ * b₁ * toMK p.2) :=
    (((IdA.continuous_toMK_inv.comp continuous_snd).matrix_mul continuous_const).matrix_mul
      (IdA.continuous_toMK.comp continuous_snd)).prodMk
    (((IdA.continuous_toMK_inv.comp continuous_snd).matrix_mul continuous_const).matrix_mul
      (IdA.continuous_toMK.comp continuous_snd))
  have hF : ContinuousOn (fun p : ℂ × KG ε => IdA.dPhi2 μ (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2,
      toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2) • (T.op p.2 * projW T * T.op p.2⁻¹))
      (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ) :=
    ((IdA.continuousOn_dPhi2 μ).comp hγ.continuousOn hmaps).smul hP
  have hF' : ContinuousOn (fun p : ℂ × KG ε => fderiv ℂ (IdA.dPhi2 μ)
      (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2, toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2)
      (toMK p.2⁻¹ * a₁ * toMK p.2, toMK p.2⁻¹ * b₁ * toMK p.2) • (T.op p.2 * projW T * T.op p.2⁻¹))
      (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ) :=
    (((IdA.continuousOn_fderiv_dPhi2 μ).comp hγ.continuousOn hmaps).clm_apply hd1.continuousOn).smul hP
  have hd : ∀ s ∈ (fun s : ℂ => a₀ + s • a₁) ⁻¹' U, ∀ k : KG ε, HasDerivAt
      (fun s => IdA.dPhi2 μ (toMK k⁻¹ * (a₀ + s • a₁) * toMK k, toMK k⁻¹ * (b₀ + s • b₁) * toMK k) •
        (T.op k * projW T * T.op k⁻¹))
      (fderiv ℂ (IdA.dPhi2 μ) (toMK k⁻¹ * (a₀ + s • a₁) * toMK k, toMK k⁻¹ * (b₀ + s • b₁) * toMK k)
        (toMK k⁻¹ * a₁ * toMK k, toMK k⁻¹ * b₁ * toMK k) • (T.op k * projW T * T.op k⁻¹)) s := by
    intro s hs k
    have hq := (IdA.hasDerivAt_cline k a₀ a₁ s).prodMk (IdA.hasDerivAt_cline k b₀ b₁ s)
    have hD := ((IdA.contDiffAt_dPhi2 μ (p := (toMK k⁻¹ * (a₀ + s • a₁) * toMK k,
      toMK k⁻¹ * (b₀ + s • b₁) * toMK k)) (hU _ hs k)).differentiableAt one_ne_zero).hasFDerivAt
    exact (hD.comp_hasDerivAt s hq).smul_const (T.op k * projW T * T.op k⁻¹)
  exact (IdA.hasDerivAt_intK T _ _ hS hF hF' hd hs₀).differentiableAt

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCas
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem isUpperTri_one : IsUpperTri (1 : Matrix (Fin n) (Fin n) ℂ) :=
  fun _ _ h => Matrix.one_apply_ne h.ne'

private theorem diag_line (a l : Fin n) (t : ℂ) :
    (1 + t • Matrix.single a a (1 : ℂ)) l l = if l = a then 1 + t else 1 := by
  by_cases h : l = a
  · subst h
    simp
  · have : ¬(a = l ∧ a = l) := fun h' => h h'.1.symm
    simp [h, Matrix.single_apply_of_ne (h := this)]

private theorem diag_prod (μ : Fin n → ℤ) (a : Fin n) (t : ℂ) :
    ∏ l, ((if l = a then 1 + t else 1) : ℂ) ^ (-μ l) = (1 + t) ^ (-μ a) := by
  rw [Finset.prod_eq_single a (fun l _ hl => by simp [hl]) (by simp)]
  simp

private theorem hasDerivAt_scale (μ : Fin n → ℤ) (a : Fin n) (c : ℂ) :
    HasDerivAt (fun t : ℂ => (1 + t) ^ (-μ a) * c) (-(μ a : ℂ) * c) 0 := by
  have h1 : HasDerivAt (fun t : ℂ => 1 + t) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℂ)).const_add 1
  have h2 := (hasDerivAt_zpow (-μ a) (1 + 0 : ℂ) (Or.inl (by simp))).comp (0 : ℂ) h1
  simpa [Function.comp_def] using h2.mul_const c

private theorem eventually_ne_line : ∀ᶠ t : ℂ in nhds 0, 1 + t ≠ 0 :=
  (continuous_const.add continuous_id).continuousAt.eventually_ne (by simp)

theorem lhol_phiM_lower (μ : Fin n → ℤ) {a b : Fin n} (hab : b < a) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) : Lhol (Matrix.single a b 1) (PhiM μ) z = 0 := by
  have hconst : ∀ t : ℂ, PhiM μ (z + t • (Matrix.single a b 1 * z)) = PhiM μ z := by
    intro t
    have hc : IsLowerTri (1 + t • Matrix.single a b (1 : ℂ)) := by
      intro i j hij
      have : ¬(a = i ∧ b = j) := fun ⟨h1, h2⟩ => by
        subst h1; subst h2; exact absurd (hab.trans hij) (lt_irrefl _)
      simp [Matrix.one_apply_ne hij.ne, Matrix.single_apply_of_ne (h := this)]
    have hcd : ∀ l, (1 + t • Matrix.single a b (1 : ℂ)) l l = 1 := by
      intro l
      have : ¬(a = l ∧ b = l) := fun ⟨h1, h2⟩ => hab.ne' (h1.trans h2.symm)
      simp [Matrix.single_apply_of_ne (h := this)]
    obtain ⟨-, h⟩ := phiM_tri_mul μ hc isUpperTri_one (fun l => by rw [hcd l]; exact one_ne_zero)
      (fun l => by simp) hz
    have e : (1 + t • Matrix.single a b (1 : ℂ)) * z * 1 = z + t • (Matrix.single a b 1 * z) := by
      rw [Matrix.mul_one, add_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [← e, h, Finset.prod_eq_one (fun l _ => by rw [hcd l, Matrix.one_apply_eq, mul_one, _root_.one_zpow]),
      one_mul]
  have hd := hasDerivAt_line (differentiableAt_phiM μ hz) (Matrix.single a b 1 * z)
  have h0 : HasDerivAt (fun t : ℂ => PhiM μ (z + t • (Matrix.single a b 1 * z))) 0 0 := by
    simp only [hconst]
    exact hasDerivAt_const _ _
  exact hd.unique h0

theorem lhol_phiM_diag (μ : Fin n → ℤ) (a : Fin n) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Lhol (Matrix.single a a 1) (PhiM μ) z = -(μ a : ℂ) * PhiM μ z := by
  have key : ∀ t : ℂ, 1 + t ≠ 0 →
      PhiM μ (z + t • (Matrix.single a a 1 * z)) = (1 + t) ^ (-μ a) * PhiM μ z := by
    intro t ht
    have hc : IsLowerTri (1 + t • Matrix.single a a (1 : ℂ)) := by
      intro i j hij
      have : ¬(a = i ∧ a = j) := fun ⟨h1, h2⟩ => hij.ne (h1.symm.trans h2)
      simp [Matrix.one_apply_ne hij.ne, Matrix.single_apply_of_ne (h := this)]
    obtain ⟨-, h⟩ := phiM_tri_mul μ hc isUpperTri_one
      (fun l => by rw [diag_line]; split_ifs <;> simp [ht]) (fun l => by simp) hz
    have e : (1 + t • Matrix.single a a (1 : ℂ)) * z * 1 = z + t • (Matrix.single a a 1 * z) := by
      rw [Matrix.mul_one, add_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [← e, h]
    congr 1
    simp only [Matrix.one_apply_eq, mul_one, diag_line]
    exact diag_prod μ a t
  have hev : (fun t : ℂ => PhiM μ (z + t • (Matrix.single a a 1 * z))) =ᶠ[nhds 0]
      fun t => (1 + t) ^ (-μ a) * PhiM μ z := by
    filter_upwards [eventually_ne_line] with t ht using key t ht
  have hd := hasDerivAt_line (differentiableAt_phiM μ hz) (Matrix.single a a 1 * z)
  exact hd.unique ((hasDerivAt_scale μ a _).congr_of_eventuallyEq hev)

theorem lhol_lhol_phiM (μ : Fin n → ℤ) (a b : Fin n) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) :
    Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) (PhiM μ)) z =
      ((casCoef μ a b : ℝ) : ℂ) * PhiM μ z := by
  have hO : IsOpen (OmegaSet n) := isOpen_omega
  have hlow : ∀ a b : Fin n, b < a →
      Lhol (Matrix.single b a 1) (Lhol (Matrix.single a b 1) (PhiM μ)) z = 0 := by
    intro a b hab
    have hev : Lhol (Matrix.single a b (1 : ℂ)) (PhiM μ) =ᶠ[nhds z] fun _ => (0 : ℂ) := by
      filter_upwards [hO.mem_nhds hz] with w hw using lhol_phiM_lower μ hab hw
    show fderiv ℂ (Lhol (Matrix.single a b (1 : ℂ)) (PhiM μ)) z _ = 0
    rw [hev.fderiv_eq]
    simp
  have e1 := lhol_phiM_diag μ a hz
  have e2 := lhol_phiM_diag μ b hz
  unfold Lhol at e1 e2
  rcases lt_trichotomy a b with h | rfl | h
  · rw [hlow b a h, casCoef, if_neg h.ne, if_neg (not_lt.mpr h.le)]
    simp
  · have hev : Lhol (Matrix.single a a (1 : ℂ)) (PhiM μ) =ᶠ[nhds z] fun w => -(μ a : ℂ) * PhiM μ w := by
      filter_upwards [hO.mem_nhds hz] with w hw using lhol_phiM_diag μ a hw
    have hf : fderiv ℂ (fun w => -(μ a : ℂ) * PhiM μ w) z = -(μ a : ℂ) • fderiv ℂ (PhiM μ) z :=
      ((differentiableAt_phiM μ hz).hasFDerivAt.const_mul (-(μ a : ℂ))).fderiv
    show fderiv ℂ (Lhol (Matrix.single a a (1 : ℂ)) (PhiM μ)) z _ = _
    rw [hev.fderiv_eq]
    erw [hf]
    rw [_root_.smul_apply, smul_eq_mul, e1, casCoef, if_pos rfl, if_neg (lt_irrefl a)]
    push_cast
    ring
  · rw [lhol_comm (contDiffAt_phiM μ hz) _ _, hlow a b h]
    simp only [Matrix.single_mul_single_same, mul_one, sub_mul, map_sub]
    rw [e1, e2, casCoef, if_neg h.ne', if_pos h]
    push_cast
    ring

theorem casL_phiM (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) : casL (PhiM μ) z = ((casVal lam : ℝ) : ℂ) * PhiM μ z := by
  show ∑ a, ∑ b, Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) (PhiM μ)) z = _
  simp only [lhol_lhol_phiM μ _ _ hz, ← Finset.sum_mul]
  rw [← sum_casCoef μ lam hμ]
  push_cast
  rfl

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

