module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
public import Mathlib

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ParabolicSubgroupEquality
section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.PSubFlag

open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S GlobalTheory.FlagMeas Formalism.MainNotions.S

variable {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ}

def Pm (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A - A)

def Pp (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A + A)

theorem mem_Vm {x : Fin n → ℂ} : x ∈ Vm A ↔ ∃ z, Pm A *ᵥ z = x := by
  simp only [Vm, LinearMap.mem_range, Matrix.toLin'_apply, Pm]

theorem mem_Wm {y : Fin n → ℂ} : y ∈ Wm A ↔ Pp A *ᵥ y = 0 := by
  simp only [Wm, LinearMap.mem_ker, Matrix.toLin'_apply, Pp]

theorem anti (hA : IsGrad ε A) : Formalism.REAL.Jm ε * A = -(A * Formalism.REAL.Jm ε) := by
  have h := hA.1
  unfold Formalism.REAL.inG at h
  rw [hA.2.1] at h
  exact eq_neg_of_add_eq_zero_right h

theorem Pm_conj (hA : IsGrad ε A) : (Pm A)ᴴ = Pm A := by
  simp [Pm, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hA.2.1]

theorem Pm_J (hA : IsGrad ε A) : Pm A * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Pp A := by
  have h := anti hA
  have h2 : Formalism.REAL.Jm ε * (A * A) = A * A * Formalism.REAL.Jm ε := by
    rw [← Matrix.mul_assoc, h, Matrix.neg_mul, Matrix.mul_assoc, h, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  simp only [Pm, Pp, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h, h2, sub_eq_add_neg, Matrix.neg_mul]

theorem Pp_Pm (hA : IsGrad ε A) : Pp A * Pm A = 0 := by
  have h := hA.2.2.1
  have e : (A * A + A) * (A * A - A) = 0 := by
    have : (A * A + A) * (A * A - A) = (A * A * A) * A - A * A := by
      simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    rw [this, h, sub_self]
  simp only [Pp, Pm, Matrix.smul_mul, Matrix.mul_smul, e, smul_zero]

theorem Vm_le_Wm (hA : IsGrad ε A) : Vm A ≤ Wm A := by
  intro x hx
  obtain ⟨z, rfl⟩ := mem_Vm.1 hx
  rw [mem_Wm, Matrix.mulVec_mulVec, Pp_Pm hA, Matrix.zero_mulVec]

theorem mem_Wm_iff (hA : IsGrad ε A) (y : Fin n → ℂ) :
    y ∈ Wm A ↔ ∀ x ∈ Vm A, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
  have key : ∀ z, star (Pm A *ᵥ z) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = star z ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (Pp A *ᵥ y)) := by
    intro z
    rw [Matrix.star_mulVec, Pm_conj hA, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Pm_J hA,
      Matrix.mulVec_mulVec]
  constructor
  · intro hy x hx
    obtain ⟨z, rfl⟩ := mem_Vm.1 hx
    rw [key, mem_Wm.1 hy, Matrix.mulVec_zero, dotProduct_zero]
  · intro h
    have h1 := h _ (mem_Vm.2 ⟨Formalism.REAL.Jm ε *ᵥ (Pp A *ᵥ y), rfl⟩)
    rw [key, dotProduct_star_self_eq_zero] at h1
    have h2 := congrArg (Formalism.REAL.Jm ε *ᵥ ·) h1
    simp only [Matrix.mulVec_mulVec, Formalism.REAL.Jm_mul_self, ← Matrix.mul_assoc, Matrix.one_mul, Matrix.mulVec_zero] at h2
    exact mem_Wm.2 h2

theorem isoFlag (hA : IsGrad ε A) : IsIsoFlag ε (fun _ : Fin 1 => rk A) (W A) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro i k h
    fin_cases i <;> fin_cases k <;> simp_all [W]
  · intro i
    fin_cases i
    show Module.finrank ℂ (Vm A) = Module.finrank ℂ (⊥ : Submodule ℂ (Fin n → ℂ)) + rk A
    simp [rk]
  · intro x hx y hy
    exact (mem_Wm_iff hA y).1 (Vm_le_Wm hA hy) x hx

theorem keeps_of_stable (g : Formalism.REAL.UJ ε) {S : Submodule ℂ (Fin n → ℂ)} (h : ∀ y ∈ S, uMat g *ᵥ y ∈ S) :
    Keeps (uMat g) S :=
  Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)
    (GlobalTheory.RealIwasawa.finrank_map_toLin _ _ (GlobalTheory.RealIwasawa.uMat_inv_mul g) S)

theorem stable_of_keeps {g : Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℂ (Fin n → ℂ)} (h : Keeps g S) :
    ∀ y ∈ S, g *ᵥ y ∈ S := fun y hy => by
  have : Matrix.toLin' g y ∈ S.map (Matrix.toLin' g) := Submodule.mem_map_of_mem hy
  rw [h, Matrix.toLin'_apply] at this
  exact this

theorem flagN_fix {u : Formalism.REAL.UJ ε} (hu : u ∈ flagN ε (W A)) {y : Fin n → ℂ} (hy : y ∈ Vm A) :
    uMat u *ᵥ y = y := by
  have h : uMat u *ᵥ y - y ∈ (⊥ : Submodule ℂ (Fin n → ℂ)) := hu.1 0 y hy
  exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 h)

theorem flagN_stable_Wm (hA : IsGrad ε A) {u : Formalism.REAL.UJ ε} (hu : u ∈ flagN ε (W A)) {y : Fin n → ℂ}
    (hy : y ∈ Wm A) : uMat u *ᵥ y ∈ Wm A := by
  have h : uMat u *ᵥ y - y ∈ Vm A := hu.2 y ((mem_Wm_iff hA y).1 hy)
  have := add_mem (Vm_le_Wm hA h) hy
  simpa using this

theorem flagM_stable_Vm {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) {y : Fin n → ℂ} (hy : y ∈ Vm A) :
    uMat m *ᵥ y ∈ Vm A :=
  (hm 1 y hy).1

theorem flagM_stable_Wm (hA : IsGrad ε A) {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) {y : Fin n → ℂ}
    (hy : y ∈ Wm A) : uMat m *ᵥ y ∈ Wm A := by
  refine (mem_Wm_iff hA _).2 fun x hx => ?_
  have hx' : uMat m⁻¹ *ᵥ x ∈ Vm A :=
    GlobalTheory.RealIwasawa.inv_stable _ _ (GlobalTheory.RealIwasawa.uMat_inv_mul m) (Vm A)
      (fun z hz => flagM_stable_Vm hm hz) x hx
  have e : x = uMat m *ᵥ (uMat m⁻¹ *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, GlobalTheory.RealIwasawa.uMat_mul_inv, Matrix.one_mulVec]
  have h0 := (mem_Wm_iff hA y).1 hy _ hx'
  rw [e, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    GlobalTheory.RealIwasawa.uMat_form]
  exact h0

theorem psubEq : PSubEq := by
  intro n ε A hA g
  constructor
  · intro hg
    have hp : ∀ i, ∀ y ∈ W A i, uMat g *ᵥ y ∈ W A i := by
      intro i y hy
      fin_cases i
      · have : y = 0 := (Submodule.mem_bot ℂ).1 hy
        rw [this, Matrix.mulVec_zero]
        exact zero_mem _
      · exact stable_of_keeps hg.1 y hy
    obtain ⟨m, hm, hu⟩ := GlobalTheory.RealIwasawa.exists_unip_mul_levi (isoFlag hA) g hp
    exact ⟨g * m⁻¹, hu, m, hm, by group⟩
  · rintro ⟨u, hu, m, hm, rfl⟩
    refine ⟨?_, ?_⟩
    · exact keeps_mul (keeps_of_stable u fun y hy => by rw [flagN_fix hu hy]; exact hy)
        (keeps_of_stable m fun y hy => flagM_stable_Vm hm hy)
    · exact keeps_mul (keeps_of_stable u fun y hy => flagN_stable_Wm hA hu hy)
        (keeps_of_stable m fun y hy => flagM_stable_Wm hA hm hy)

end GlobalTheory.CompanionTheory.PSubFlag
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SlabStatement
section
open MeasureTheory Set
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.SlabLemma

noncomputable def wt (c t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * c * t))

lemma wt_add (c s t : ℝ) : wt c (s + t) = wt c s * wt c t := by
  show ENNReal.ofReal (Real.exp (2 * c * (s + t))) =
    ENNReal.ofReal (Real.exp (2 * c * s)) * ENNReal.ofReal (Real.exp (2 * c * t))
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

lemma wt_ne_zero (c t : ℝ) : wt c t ≠ 0 := by
  show ENNReal.ofReal (Real.exp (2 * c * t)) ≠ 0
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

lemma measurable_wt (c : ℝ) : Measurable (wt c) := by
  show Measurable fun t => ENNReal.ofReal (Real.exp (2 * c * t))
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.ennreal_ofReal

noncomputable def unitInd : ℝ → ℝ≥0∞ := (Ico (0 : ℝ) 1).indicator 1

lemma measurable_unitInd : Measurable unitInd := by
  show Measurable ((Ico (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞))
  exact measurable_const.indicator measurableSet_Ico

lemma lintegral_unitInd (x : ℝ) : ∫⁻ t, unitInd (x - t) = 1 := by
  show ∫⁻ t, (Ico (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) (x - t) = 1
  rw [lintegral_sub_left_eq_self (fun y => (Ico (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) y) x,
    lintegral_indicator_one measurableSet_Ico, Real.volume_Ico, sub_zero, ENNReal.ofReal_one]

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

noncomputable def line (F : G → ℝ≥0∞) (a : ℝ → G) (c : ℝ) (p : G × G) : ℝ≥0∞ :=
  ∫⁻ t, F (p.1 * p.2 * a t) * wt c t

lemma measurable_line {F : G → ℝ≥0∞} {a : ℝ → G} (c : ℝ) (hF : Measurable F) (ha : Measurable a) :
    Measurable (line F a c) := by
  have hm : Measurable fun q : (G × G) × ℝ => F (q.1.1 * q.1.2 * a q.2) * wt c q.2 :=
    (hF.comp ((measurable_fst.fst.mul measurable_fst.snd).mul (ha.comp measurable_snd))).mul
      ((measurable_wt c).comp measurable_snd)
  exact hm.lintegral_prod_right'

lemma line_shift {F : G → ℝ≥0∞} {a : ℝ → G} {c : ℝ} (hadd : ∀ s t, a (s + t) = a s * a t) (u m : G) (s : ℝ)
    (hF : Measurable F) (ha : Measurable a) :
    line F a c (u, m * a s) = wt c (-s) * line F a c (u, m) := by
  show ∫⁻ t, F (u * (m * a s) * a t) * wt c t = wt c (-s) * ∫⁻ t, F (u * m * a t) * wt c t
  rw [← lintegral_sub_right_eq_self (fun t => F (u * (m * a s) * a t) * wt c t) s,
    ← lintegral_const_mul _ (show Measurable fun t => F (u * m * a t) * wt c t from
      (hF.comp (measurable_const.mul ha)).mul (measurable_wt c))]
  refine lintegral_congr fun t => ?_
  have h1 : u * (m * a s) * a (t - s) = u * m * a t := by
    have h2 : s + (t - s) = t := by ring
    rw [mul_assoc u m, mul_assoc u, mul_assoc m, ← hadd, h2]
  rw [h1, sub_eq_add_neg, wt_add]
  ring

lemma slab_identity (μM : Measure G) [SFinite μM] {S : Set G} {a : ℝ → G} {δ : G → ℝ≥0∞} {τ : G → ℝ} {c : ℝ}
    (hSc : μM Sᶜ = 0) (ha : Measurable a) (hδ : Measurable δ) (hτ : Measurable τ)
    (hinv : ∀ t, μM.map (· * a t) = μM)
    (hδa : ∀ m ∈ S, ∀ t, δ (m * a t) = δ m * wt c t)
    (hτa : ∀ m ∈ S, ∀ t, τ (m * a t) = τ m + t)
    {H : G → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ m, unitInd (τ m) * δ m * ∫⁻ t, H (m * a t) * wt c t ∂volume ∂μM = ∫⁻ m, δ m * H m ∂μM := by
  have hSae : ∀ᵐ m ∂μM, m ∈ S := ae_iff.mpr hSc
  have hU : Measurable fun m => unitInd (τ m) := measurable_unitInd.comp hτ
  have e1 : ∀ m, unitInd (τ m) * δ m * ∫⁻ t, H (m * a t) * wt c t ∂volume =
      ∫⁻ t, unitInd (τ m) * δ m * (H (m * a t) * wt c t) := fun m =>
    (lintegral_const_mul _ ((hH.comp (measurable_const.mul ha)).mul (measurable_wt c))).symm
  have hmeas : Measurable (Function.uncurry fun (m : G) (t : ℝ) =>
      unitInd (τ m) * δ m * (H (m * a t) * wt c t)) :=
    ((hU.comp measurable_fst).mul (hδ.comp measurable_fst)).mul
      ((hH.comp (measurable_fst.mul (ha.comp measurable_snd))).mul ((measurable_wt c).comp measurable_snd))
  have hmeas2 : Measurable (Function.uncurry fun (t : ℝ) (m : G) => unitInd (τ m - t) * (δ m * H m)) :=
    (measurable_unitInd.comp ((hτ.comp measurable_snd).sub measurable_fst)).mul
      ((hδ.comp measurable_snd).mul (hH.comp measurable_snd))
  have e2 : ∀ t, ∫⁻ m, unitInd (τ m) * δ m * (H (m * a t) * wt c t) ∂μM =
      ∫⁻ m, unitInd (τ m - t) * (δ m * H m) ∂μM := by
    intro t
    have hg : Measurable fun m => unitInd (τ m - t) * (δ m * H m) :=
      (measurable_unitInd.comp (hτ.sub measurable_const)).mul (hδ.mul hH)
    have hf : Measurable fun m : G => m * a t := measurable_id.mul measurable_const
    conv_rhs => rw [← hinv t]
    rw [lintegral_map hg hf]
    refine lintegral_congr_ae (hSae.mono fun m hm => ?_)
    show unitInd (τ m) * δ m * (H (m * a t) * wt c t) =
      unitInd (τ (m * a t) - t) * (δ (m * a t) * H (m * a t))
    rw [hτa m hm t, hδa m hm t, add_sub_cancel_right]
    ring
  calc ∫⁻ m, unitInd (τ m) * δ m * ∫⁻ t, H (m * a t) * wt c t ∂volume ∂μM
      = ∫⁻ m, ∫⁻ t, unitInd (τ m) * δ m * (H (m * a t) * wt c t) ∂volume ∂μM := lintegral_congr e1
    _ = ∫⁻ t, ∫⁻ m, unitInd (τ m) * δ m * (H (m * a t) * wt c t) ∂μM ∂volume :=
      lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ t, ∫⁻ m, unitInd (τ m - t) * (δ m * H m) ∂μM ∂volume := lintegral_congr e2
    _ = ∫⁻ m, ∫⁻ t, unitInd (τ m - t) * (δ m * H m) ∂volume ∂μM :=
      lintegral_lintegral_swap hmeas2.aemeasurable
    _ = ∫⁻ m, δ m * H m ∂μM := by
      refine lintegral_congr fun m => ?_
      rw [lintegral_mul_const _ (show Measurable fun t => unitInd (τ m - t) from
          measurable_unitInd.comp (measurable_const.sub measurable_id)),
        lintegral_unitInd, one_mul]

end GlobalTheory.CompanionTheory.SlabLemma


open GlobalTheory.CompanionTheory.SlabLemma in
theorem GlobalTheory.CompanionTheory.SlabLemma.slab : CompanionTheory.RgExh.Dec.N.S.Slab := by
  intro G _ _ _ μN μM _ _ S a δ τ c hSm hSc ha hδ hτ hadd hS hinv hδa hτa hδ0 F hF hfin
  have hSae : ∀ᵐ m ∂μM, m ∈ S := ae_iff.mpr hSc
  have hline : Measurable (line F a c) := measurable_line c hF ha
  have hmeasF : Measurable fun q : G × G => δ q.2 * F (q.1 * q.2) :=
    (hδ.comp measurable_snd).mul (hF.comp (measurable_fst.mul measurable_snd))
  have hae1 : ∀ᵐ u ∂μN, ∫⁻ m, δ m * F (u * m) ∂μM < ⊤ :=
    ae_lt_top hmeasF.lintegral_prod_right' hfin.ne
  have key : ∀ᵐ u ∂μN, ∀ᵐ m ∂μM, line F a c (u, m) < ⊤ := by
    refine hae1.mono fun u hu => ?_
    have hid : ∫⁻ m, unitInd (τ m) * δ m * line F a c (u, m) ∂μM = ∫⁻ m, δ m * F (u * m) ∂μM := by
      have h := slab_identity μM hSc ha hδ hτ hinv hδa hτa (H := fun x => F (u * x))
        (hF.comp (measurable_const.mul measurable_id))
      refine Eq.trans (lintegral_congr fun m => ?_) h
      show unitInd (τ m) * δ m * ∫⁻ t, F (u * m * a t) * wt c t =
        unitInd (τ m) * δ m * ∫⁻ t, F (u * (m * a t)) * wt c t
      simp only [mul_assoc]
    have hfin2 : ∫⁻ m, unitInd (τ m) * δ m * line F a c (u, m) ∂μM < ⊤ := hid ▸ hu
    have hmeas3 : Measurable fun m => unitInd (τ m) * δ m * line F a c (u, m) :=
      ((measurable_unitInd.comp hτ).mul hδ).mul (hline.comp (measurable_const.prodMk measurable_id))
    have hae2 := ae_lt_top hmeas3 hfin2.ne
    have hshift : ∀ k : ℤ, ∀ᵐ m ∂μM,
        unitInd (τ (m * a k)) * δ (m * a k) * line F a c (u, m * a k) < ⊤ := by
      intro k
      have hf : AEMeasurable (fun m : G => m * a k) μM := (measurable_id.mul measurable_const).aemeasurable
      rw [← hinv k] at hae2
      exact ae_of_ae_map hf hae2
    have hall : ∀ᵐ m ∂μM, ∀ k : ℤ,
        unitInd (τ (m * a k)) * δ (m * a k) * line F a c (u, m * a k) < ⊤ := ae_all_iff.mpr hshift
    filter_upwards [hall, hSae] with m hm hmS
    have hmk : m * a ((-⌊τ m⌋ : ℤ) : ℝ) ∈ S := hS m hmS _
    have hmem : τ m + ((-⌊τ m⌋ : ℤ) : ℝ) ∈ Ico (0 : ℝ) 1 := by
      constructor <;> push_cast <;> linarith [Int.floor_le (τ m), Int.lt_floor_add_one (τ m)]
    have hU1 : unitInd (τ (m * a ((-⌊τ m⌋ : ℤ) : ℝ))) = 1 := by
      rw [hτa m hmS]
      exact (Set.indicator_of_mem hmem 1).trans rfl
    have h1 := hm (-⌊τ m⌋)
    rw [hU1, one_mul] at h1
    have hL : line F a c (u, m * a ((-⌊τ m⌋ : ℤ) : ℝ)) < ⊤ := by
      rcases ENNReal.mul_lt_top_iff.mp h1 with h | h | h
      · exact h.2
      · exact absurd h (hδ0 _ hmk)
      · rw [h]
        exact ENNReal.zero_lt_top
    rw [line_shift hadd u m _ hF ha] at hL
    rcases ENNReal.mul_lt_top_iff.mp hL with h | h | h
    · exact h.2
    · exact absurd h (wt_ne_zero _ _)
    · rw [h]
      exact ENNReal.zero_lt_top
  have hset : MeasurableSet {p : G × G | line F a c p < ⊤} := measurableSet_lt hline measurable_const
  have hprod : ∀ᵐ p ∂μN.prod μM, line F a c p < ⊤ := (Measure.ae_prod_iff_ae_ae hset).mpr key
  filter_upwards [hprod] with p hp
  exact lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hp
end

