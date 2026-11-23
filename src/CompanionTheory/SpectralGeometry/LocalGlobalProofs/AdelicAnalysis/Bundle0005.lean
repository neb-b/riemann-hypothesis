module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0003
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MatrixInductionTransvectionDiagonal

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IwasawaDecompositionAdelicSL2
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Iwasawa

variable {F : Type} [Field F] [NumberField F]

def IntAt (b : F) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  algebraMap F (A F) b v ∈ v.adicCompletionIntegers F


open Classical in
def idem (b : F) : A F :=
  ⟨fun v => if IntAt b v then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : IntAt b v
    · simpa [h] using (v.adicCompletionIntegers F).one_mem
    · simpa [h] using (v.adicCompletionIntegers F).zero_mem⟩


open Classical in
def scale (b : F) : A F :=
  ⟨fun v => if IntAt b v then 1 else (algebraMap F (A F) b v)⁻¹,
    Filter.Eventually.of_forall fun v => by
      by_cases h : IntAt b v
      · simpa [h] using (v.adicCompletionIntegers F).one_mem
      · simpa [h] using ((v.adicCompletionIntegers F).mem_or_inv_mem _).resolve_left h⟩


open Classical in
def scaleInv (b : F) : A F :=
  ⟨fun v => if IntAt b v then 1 else algebraMap F (A F) b v, by
    filter_upwards [(algebraMap F (A F) b).2] with v hv
    have h : IntAt b v := hv
    simpa [h] using (v.adicCompletionIntegers F).one_mem⟩

theorem mul_at (x y : A F) (v : HeightOneSpectrum (𝓞 F)) : (x * y) v = x v * y v := rfl
theorem add_at (x y : A F) (v : HeightOneSpectrum (𝓞 F)) : (x + y) v = x v + y v := rfl
theorem sub_at (x y : A F) (v : HeightOneSpectrum (𝓞 F)) : (x - y) v = x v - y v := rfl
theorem one_at (v : HeightOneSpectrum (𝓞 F)) : (1 : A F) v = 1 := rfl

theorem idem_int {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : IntAt b v) : idem b v = 1 :=
  if_pos h
theorem idem_not {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : ¬ IntAt b v) : idem b v = 0 :=
  if_neg h
theorem scale_int {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : IntAt b v) : scale b v = 1 :=
  if_pos h
theorem scale_not {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : ¬ IntAt b v) :
    scale b v = (algebraMap F (A F) b v)⁻¹ :=
  if_neg h
theorem scaleInv_int {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : IntAt b v) : scaleInv b v = 1 :=
  if_pos h
theorem scaleInv_not {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : ¬ IntAt b v) :
    scaleInv b v = algebraMap F (A F) b v :=
  if_neg h

theorem ne_zero_of_not_int {b : F} {v : HeightOneSpectrum (𝓞 F)} (h : ¬ IntAt b v) :
    algebraMap F (A F) b v ≠ 0 := fun h0 =>
  h (by unfold IntAt; rw [h0]; exact (v.adicCompletionIntegers F).zero_mem)

theorem scale_mul_scaleInv (b : F) : scale b * scaleInv b = 1 := by
  refine FiniteAdeleRing.ext F fun v => ?_
  rw [mul_at, one_at]
  by_cases h : IntAt b v
  · rw [scale_int h, scaleInv_int h, one_mul]
  · rw [scale_not h, scaleInv_not h, inv_mul_cancel₀ (ne_zero_of_not_int h)]

theorem scale_combo (b : F) :
    scale b * idem b + (1 - idem b) * (scale b * algebraMap F (A F) b) = 1 := by
  refine FiniteAdeleRing.ext F fun v => ?_
  rw [add_at, mul_at, mul_at, mul_at, sub_at, one_at]
  by_cases h : IntAt b v
  · rw [scale_int h, idem_int h]; ring
  · rw [scale_not h, idem_not h, inv_mul_cancel₀ (ne_zero_of_not_int h)]; ring

theorem idem_mem (b : F) : idem b ∈ Oh F := fun v => by
  by_cases h : IntAt b v
  · rw [idem_int h]; exact (v.adicCompletionIntegers F).one_mem
  · rw [idem_not h]; exact (v.adicCompletionIntegers F).zero_mem

theorem scale_mem (b : F) : scale b ∈ Oh F := fun v => by
  by_cases h : IntAt b v
  · rw [scale_int h]; exact (v.adicCompletionIntegers F).one_mem
  · rw [scale_not h]
    exact ((v.adicCompletionIntegers F).mem_or_inv_mem _).resolve_left h

theorem Oh_one : (1 : A F) ∈ Oh F := fun v => (v.adicCompletionIntegers F).one_mem

theorem Oh_neg {x : A F} (hx : x ∈ Oh F) : -x ∈ Oh F := fun v =>
  (v.adicCompletionIntegers F).neg_mem _ (hx v)

theorem Oh_sub {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x - y ∈ Oh F := fun v =>
  (v.adicCompletionIntegers F).sub_mem (hx v) (hy v)

theorem Oh_mul {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x * y ∈ Oh F := fun v =>
  (v.adicCompletionIntegers F).mul_mem _ _ (hx v) (hy v)

theorem scale_mul_mem (b : F) : scale b * algebraMap F (A F) b ∈ Oh F := fun v => by
  rw [mul_at]
  by_cases h : IntAt b v
  · rw [scale_int h, one_mul]; exact h
  · rw [scale_not h, inv_mul_cancel₀ (ne_zero_of_not_int h)]
    exact (v.adicCompletionIntegers F).one_mem

def scaleUnit (b : F) : (A F)ˣ :=
  ⟨scale b, scaleInv b, scale_mul_scaleInv b, by rw [mul_comm]; exact scale_mul_scaleInv b⟩

def kMat (b : F) : SL(2, A F) :=
  ⟨!![idem b - 1, idem b; -scale b, -(scale b * algebraMap F (A F) b)], by
    rw [Matrix.det_fin_two_of]
    linear_combination scale_combo b⟩

theorem image_scale (b : F) :
    (fun x => scale b * x) '' Oh F = {x | x ∈ Oh F ∧ algebraMap F (A F) b * x ∈ Oh F} := by
  ext x
  constructor
  · rintro ⟨o, ho, rfl⟩
    refine ⟨Oh_mul (scale_mem b) ho, ?_⟩
    have : algebraMap F (A F) b * (scale b * o) = (scale b * algebraMap F (A F) b) * o := by ring
    show algebraMap F (A F) b * (scale b * o) ∈ Oh F
    rw [this]
    exact Oh_mul (scale_mul_mem b) ho
  · rintro ⟨hx, hbx⟩
    refine ⟨scaleInv b * x, fun v => ?_, ?_⟩
    · rw [mul_at]
      by_cases h : IntAt b v
      · rw [scaleInv_int h, one_mul]; exact hx v
      · rw [scaleInv_not h]; exact hbx v
    · show scale b * (scaleInv b * x) = x
      rw [← mul_assoc, scale_mul_scaleInv, one_mul]

theorem w_n_eq {R : Type} [CommRing R] (β e : R) (u : Rˣ) (k : SL(2, R))
    (h00 : k 0 0 = e - 1) (h01 : k 0 1 = e) (h10 : k 1 0 = -(u : R))
    (h11 : k 1 1 = -((u : R) * β)) (h : (u : R) * e + (1 - e) * ((u : R) * β) = 1) :
    wMat * nMat β = nMat ((e - 1) * (u : R)) * mMat u * k := by
  have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.mul_inv
  have hk : (k : Matrix (Fin 2) (Fin 2) R) = !![e - 1, e; -(u : R), -((u : R) * β)] := by
    rw [Matrix.eta_fin_two (k : Matrix (Fin 2) (Fin 2) R), h00, h01, h10, h11]
  apply Subtype.ext
  change (!![0, 1; -1, 0] * !![1, β; 0, 1] : Matrix (Fin 2) (Fin 2) R) =
    !![1, (e - 1) * (u : R); 0, 1] * !![(u : R), 0; 0, ((u⁻¹ : Rˣ) : R)] *
      (k : Matrix (Fin 2) (Fin 2) R)
  rw [hk]
  simp only [Matrix.mul_fin_two]
  have entries : ∀ a b c d a' b' c' d' : R, a = a' → b = b' → c = c' → d = d' →
      (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R) = !![a', b'; c', d'] := by
    rintro _ _ _ _ _ _ _ _ rfl rfl rfl rfl
    rfl
  refine entries _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · linear_combination ((e - 1) * (u : R)) * hu
  · linear_combination -h + ((e - 1) * (u : R) * β) * hu
  · linear_combination hu
  · linear_combination β * hu

theorem iwasawa_w_n : ∀ (F : Type) [Field F] [NumberField F], ∀ b : F,
    ∃ (y : A F) (a : (A F)ˣ) (k : SL(2, A F)), (∀ i j, k i j ∈ Oh F) ∧
      wMat * nMat (algebraMap F (A F) b) = nMat y * mMat a * k ∧
      (fun x => (a : A F) * x) '' Oh F = {x | x ∈ Oh F ∧ algebraMap F (A F) b * x ∈ Oh F} := by
  intro F _ _ b
  refine ⟨(idem b - 1) * scale b, scaleUnit b, kMat b, ?_, ?_, image_scale b⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact Oh_sub (idem_mem b) Oh_one
    · exact idem_mem b
    · exact Oh_neg (scale_mem b)
    · exact Oh_neg (scale_mul_mem b)
  · exact w_n_eq _ (idem b) (scaleUnit b) (kMat b) rfl rfl rfl rfl (scale_combo b)

end GlobalTheory.CompanionTheory.SW.Iwasawa
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeBallCountRatioBound
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic.Packing

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Λ : Type} [AddCommGroup Λ]

def Sep (e : Λ →+ V) (r R : ℝ) (s : Finset Λ) : Prop :=
  (∀ l ∈ s, ‖e l‖ ≤ R) ∧ (s : Set Λ).Pairwise fun a b => r ≤ ‖e a - e b‖

theorem Sep.card_le {e : Λ →+ V} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {s : Finset Λ}
    (hs : Sep e r R s) : (s.card : ℝ) ≤ (3 * R / r) ^ Module.finrank ℝ V := by
  classical
  have hinj : Set.InjOn e (s : Set Λ) := by
    intro a ha b hb hab
    by_contra hne
    have : r ≤ ‖e a - e b‖ := hs.2 ha hb hne
    rw [hab, sub_self, norm_zero] at this
    linarith
  have hcard : (s.image e).card = s.card := Finset.card_image_of_injOn hinj
  have h1 := GlobalTheory.finset_card_le_of_separated (s.image e) hr (hr.le.trans hrR) (0 : V)
    (by
      intro a ha
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 ha
      simpa using hs.1 l hl)
    (by
      intro a ha b hb hab
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
      have hlm : l ≠ m := fun h => hab (by rw [h])
      rw [dist_eq_norm]
      exact hs.2 hl hm hlm)
  rw [hcard] at h1
  exact h1.trans (GlobalTheory.one_add_two_mul_div_pow_le hr hrR _)

theorem exists_max_sep (e : Λ →+ V) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ∃ s : Finset Λ, Sep e r R s ∧ ∀ t : Finset Λ, Sep e r R t → t.card ≤ s.card := by
  let S : Set ℕ := {n | ∃ s : Finset Λ, Sep e r R s ∧ s.card = n}
  have hne : S.Nonempty := ⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩
  have hbd : BddAbove S := by
    refine ⟨⌊(3 * R / r) ^ Module.finrank ℝ V⌋₊, ?_⟩
    rintro n ⟨s, hs, rfl⟩
    exact Nat.le_floor (Sep.card_le hr hrR hs)
  obtain ⟨s, hs, hc⟩ := Nat.sSup_mem hne hbd
  exact ⟨s, hs, fun t ht => hc ▸ le_csSup hbd ⟨t, ht, rfl⟩⟩

theorem Sep.exists_near {e : Λ →+ V} {r R : ℝ} (hr : 0 < r) {s : Finset Λ}
    (hs : Sep e r R s) (hmax : ∀ t : Finset Λ, Sep e r R t → t.card ≤ s.card)
    {l : Λ} (hl : ‖e l‖ ≤ R) : ∃ t ∈ s, ‖e (l - t)‖ ≤ r := by
  classical
  by_contra hcon
  push_neg at hcon
  have hns : l ∉ s := fun h => by
    have := hcon l h
    simp only [sub_self, map_zero, norm_zero] at this
    linarith
  have hins : Sep e r R (insert l s) := by
    refine ⟨?_, ?_⟩
    · intro m hm
      rcases Finset.mem_insert.1 hm with rfl | hm
      · exact hl
      · exact hs.1 m hm
    · rw [Finset.coe_insert]
      refine Set.pairwise_insert.2 ⟨hs.2, ?_⟩
      intro b hb _
      have h := hcon b hb
      rw [map_sub] at h
      exact ⟨h.le, by rw [norm_sub_rev]; exact h.le⟩
  have := hmax _ hins
  rw [Finset.card_insert_of_notMem hns] at this
  omega

end GlobalTheory.CompanionTheory.Adelic.Packing


open GlobalTheory.CompanionTheory.Adelic.Packing in
theorem GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Type)
      [AddCommGroup Λ] (e : Λ →+ V) (r R : ℝ), 0 < r → r ≤ R →
      ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤
        ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) *
          ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) l := by
  intro V _ _ _ Λ _ e r R hr hrR
  classical
  obtain ⟨s, hs, hmax⟩ := exists_max_sep e hr hrR
  set f : Λ → ℝ≥0∞ := Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) with hf
  have hpt : ∀ l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤
      ∑ t ∈ s, f (l - t) := by
    intro l
    by_cases hl : ‖e l‖ ≤ R
    · obtain ⟨t, ht, hlt⟩ := hs.exists_near hr hmax hl
      have h1 : f (l - t) = 1 := Set.indicator_of_mem (s := {l : Λ | ‖e l‖ ≤ r}) hlt _
      calc Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤ 1 :=
            Set.indicator_le_self' (fun _ _ => zero_le) l
        _ = f (l - t) := h1.symm
        _ ≤ ∑ t ∈ s, f (l - t) :=
            Finset.single_le_sum (f := fun t => f (l - t)) (fun _ _ => zero_le) ht
    · rw [Set.indicator_of_notMem (by simpa using hl)]
      exact zero_le
  have hshift : ∀ t : Λ, ∑' l : Λ, f (l - t) = ∑' l : Λ, f l := fun t =>
    (Equiv.subRight t).tsum_eq f
  have hcard : (s.card : ℝ≥0∞) ≤ ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) := by
    have h3 : (s.card : ℝ) ≤ (5 * R / r) ^ Module.finrank ℝ V := by
      refine (Sep.card_le hr hrR hs).trans (pow_le_pow_left₀ (by have := hr.le.trans hrR; positivity) ?_ _)
      have := hr.le.trans hrR
      gcongr
      norm_num
    calc (s.card : ℝ≥0∞) = ENNReal.ofReal (s.card : ℝ) := (ENNReal.ofReal_natCast _).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h3
  calc ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l
      ≤ ∑' l : Λ, ∑ t ∈ s, f (l - t) := ENNReal.tsum_le_tsum hpt
    _ = ∑ t ∈ s, ∑' l : Λ, f (l - t) := by
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ = (s.card : ℝ≥0∞) * ∑' l : Λ, f l := by
        simp only [hshift, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by gcongr
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MapMulVecEqOfTransposeMulMulEq
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic.OrthHaar

section Equiv

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def mulVecEquiv (A : Matrix ι ι R) (h : IsUnit A.det) : (ι → R) ≃ₜ+ (ι → R) where
  toFun x := A *ᵥ x
  invFun x := A⁻¹ *ᵥ x
  left_inv x := by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A h]
  right_inv x := by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A h]
  map_add' x y := Matrix.mulVec_add A x y
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem transvection_mulVec_apply (i j : ι) (c : R) (f : ι → R) (k : ι) :
    (Matrix.transvection i j c *ᵥ f) k = f k + if k = i then c * f j else 0 := by
  by_cases hk : k = i
  · subst hk
    simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec]
  · simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec, hk]

end Equiv

section Measure

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem measurePreserving_transvection (ν : Measure R) [ν.IsAddHaarMeasure] {i j : ι}
    (hij : i ≠ j) (c : R) :
    MeasurePreserving (fun x : ι → R => Matrix.transvection i j c *ᵥ x)
      (Measure.pi fun _ => ν) (Measure.pi fun _ => ν) := by
  let p : ι → Prop := fun k => k ≠ i
  let α : Type := { x // p x }
  let β : Type := { x // ¬p x }
  let g : (α → R) → (β → R) → β → R := fun a b => (fun _ => c * a ⟨j, hij.symm⟩) + b
  let F : (α → R) × (β → R) → (α → R) × (β → R) := fun q => (id q.1, g q.1 q.2)
  let e : (ι → R) ≃ᵐ (α → R) × (β → R) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => R) p
  have key : (fun x : ι → R => Matrix.transvection i j c *ᵥ x) = e.symm ∘ F ∘ e := by
    ext f k
    rw [transvection_mulVec_apply]
    by_cases hk : k = i
    · subst hk
      simp [e, F, g, p, α, β, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, add_comm]
    · simp [e, F, g, p, α, β, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hk]
  rw [key]
  have A : MeasurePreserving e (Measure.pi fun _ => ν) _ :=
    measurePreserving_piEquivPiSubtypeProd (fun _ => ν) p
  have B : MeasurePreserving F
      ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν))
      ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν)) := by
    have g_meas : Measurable (Function.uncurry g) := by
      have : Continuous (Function.uncurry g) := by
        unfold Function.uncurry
        simp only [g]
        fun_prop
      exact this.measurable
    exact (MeasurePreserving.id _).skew_product g_meas
      (Filter.Eventually.of_forall fun a => map_add_left_eq_self _ _)
  exact (A.symm e).comp (B.comp A)


open Classical in
noncomputable def scale (A : Matrix ι ι R) : ℝ≥0 := by
  classical
  exact if h : IsUnit A.det then addEquivAddHaarChar (mulVecEquiv A h) else 1

theorem scale_of_isUnit {A : Matrix ι ι R} (h : IsUnit A.det) :
    scale A = addEquivAddHaarChar (mulVecEquiv A h) := by
  classical
  exact dite_eq_left h

theorem scale_mul {A B : Matrix ι ι R} (hA : IsUnit A.det) (hB : IsUnit B.det) :
    scale (A * B) = scale A * scale B := by
  have hAB : IsUnit (A * B).det := by
    rw [Matrix.det_mul]
    exact hA.mul hB
  have e : mulVecEquiv (A * B) hAB = (mulVecEquiv B hB).trans (mulVecEquiv A hA) :=
    ContinuousAddEquiv.ext fun x => (Matrix.mulVec_mulVec x A B).symm
  rw [scale_of_isUnit hAB, scale_of_isUnit hA, scale_of_isUnit hB, e, addEquivAddHaarChar_trans,
    mul_comm]

theorem scale_transvection {i j : ι} (hij : i ≠ j) (c : R) :
    scale (Matrix.transvection i j c) = 1 := by
  have h : IsUnit (Matrix.transvection i j c).det := by
    rw [Matrix.det_transvection_of_ne _ _ hij]
    exact isUnit_one
  have hmp := measurePreserving_transvection (Measure.addHaar : Measure R) hij c
  have e : (Measure.pi fun _ : ι => (Measure.addHaar : Measure R)).map (mulVecEquiv _ h) =
      Measure.pi fun _ : ι => (Measure.addHaar : Measure R) := hmp.map_eq
  have one : ∀ (m : Measure (ι → R)) [m.IsAddHaarMeasure],
      m = Measure.pi (fun _ : ι => (Measure.addHaar : Measure R)) →
      Measure.addHaarScalarFactor (Measure.pi fun _ : ι => (Measure.addHaar : Measure R)) m = 1 := by
    rintro m _ rfl
    exact Measure.addHaarScalarFactor_self _
  rw [scale_of_isUnit h,
    addEquivAddHaarChar_eq (Measure.pi fun _ : ι => (Measure.addHaar : Measure R))]
  exact one _ e

theorem transpose_transvection (i j : ι) (c : R) :
    (Matrix.transvection i j c)ᵀ = Matrix.transvection j i c := by
  simp [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one]

theorem scale_transpose (hsr : ∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b))
    (A : Matrix ι ι R) (hA : IsUnit A.det) : scale Aᵀ = scale A := by
  refine _root_.GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction R hsr ι (fun A => scale Aᵀ = scale A) ?_ ?_ ?_ A hA
  · intro i j c hij
    simp only [transpose_transvection]
    rw [scale_transvection hij, scale_transvection hij.symm]
  · intro D _
    simp only [Matrix.diagonal_transpose]
  · intro A B hA hB (eA : scale Aᵀ = scale A) (eB : scale Bᵀ = scale B)
    show scale (A * B)ᵀ = scale (A * B)
    rw [Matrix.transpose_mul, scale_mul (by rwa [Matrix.det_transpose])
      (by rwa [Matrix.det_transpose]), scale_mul hA hB, eA, eB, mul_comm]

end Measure

theorem map_mulVec_eq_of_transpose_mul_mul_eq :
    ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
      [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R],
      (∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b)) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → R)) [μ.IsAddHaarMeasure]
        (B g : Matrix ι ι R), IsUnit B.det → gᵀ * B * g = B →
        μ.map (fun x => g *ᵥ x) = μ := by
  intro R _ _ _ _ _ _ _ _ hsr ι _ _ μ _ B g hB h
  have hg2 : g.det * g.det = 1 := by
    have e := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at e
    have e2 : B.det * (g.det * g.det) = B.det * 1 := by linear_combination e
    exact hB.mul_left_cancel e2
  have hg : IsUnit g.det := isUnit_iff_exists_inv.mpr ⟨_, hg2⟩
  have hgt : IsUnit gᵀ.det := by rwa [Matrix.det_transpose]
  have hpos : 0 < scale B := by
    rw [scale_of_isUnit hB]
    exact addEquivAddHaarChar_pos _
  have hsq : scale g ^ 2 = 1 := by
    have e := congrArg scale h
    rw [scale_mul (by rw [Matrix.det_mul]; exact hgt.mul hB) hg, scale_mul hgt hB,
      scale_transpose hsr g hg] at e
    apply mul_left_cancel₀ hpos.ne'
    calc scale B * scale g ^ 2 = scale g * scale B * scale g := by ring
      _ = scale B := e
      _ = scale B * 1 := (mul_one _).symm
  have h1 : scale g = 1 := (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 hsq
  have hmap := addEquivAddHaarChar_smul_map μ (mulVecEquiv g hg)
  rw [← scale_of_isUnit hg, h1, one_smul] at hmap
  exact hmap

end GlobalTheory.CompanionTheory.Adelic.OrthHaar
end

