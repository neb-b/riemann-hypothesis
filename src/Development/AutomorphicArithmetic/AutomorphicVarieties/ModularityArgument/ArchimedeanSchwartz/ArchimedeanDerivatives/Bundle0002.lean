module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ShiftOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import GroundTheory.AutomorphicForms.RealGroupsHaar
public import GroundTheory.AutomorphicForms.GL2.InnerProductParamHolo

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.IntegralHWMul
section
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep
open scoped ContDiff
open GlobalTheory.HenQ.DetDParts (top_add_one_le fderiv_fderiv_comm integrable_mul_of_tsupport integral_partial_mul)

namespace UpperTheory.V.Z.Inf

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private def hD (u : E × E) (f : E → ℂ) (x : E) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f x u.1 - Complex.I * fderiv ℝ f x u.2)

private def hW (w : List (E × E)) (g : E → ℂ) : E → ℂ := List.foldr hD g w

private theorem contDiff_fd {g : E → ℂ} (hg : ContDiff ℝ ∞ g) (a : E) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ g x a) :=
  (hg.fderiv_right top_add_one_le).clm_apply contDiff_const

private theorem contDiffOn_fd {U : Set E} (hU : IsOpen U) {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g U) (a : E) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℝ g x a) U :=
  (hg.fderiv_of_isOpen hU top_add_one_le).clm_apply contDiffOn_const

private theorem contDiff_hD (u : E × E) {g : E → ℂ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (hD u g) :=
  contDiff_const.mul ((contDiff_fd hg _).sub (contDiff_const.mul (contDiff_fd hg _)))

private theorem contDiffOn_hD {U : Set E} (hU : IsOpen U) (u : E × E) {g : E → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) : ContDiffOn ℝ ∞ (hD u g) U :=
  contDiffOn_const.mul ((contDiffOn_fd hU hg _).sub (contDiffOn_const.mul (contDiffOn_fd hU hg _)))

private theorem tsupport_hD (u : E × E) (g : E → ℂ) : tsupport (hD u g) ⊆ tsupport g := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra h
  apply hx
  have h0 : fderiv ℝ g x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h' => h (tsupport_fderiv_subset ℝ h'))
  simp [hD, h0]

private theorem contDiff_hW (w : List (E × E)) {g : E → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (hW w g) := by
  induction w with
  | nil => exact hg
  | cons u w ih => exact contDiff_hD u ih

private theorem contDiffOn_hW {U : Set E} (hU : IsOpen U) (w : List (E × E)) {g : E → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) : ContDiffOn ℝ ∞ (hW w g) U := by
  induction w with
  | nil => exact hg
  | cons u w ih => exact contDiffOn_hD hU u ih

private theorem tsupport_hW (w : List (E × E)) (g : E → ℂ) : tsupport (hW w g) ⊆ tsupport g := by
  induction w with
  | nil => exact subset_rfl
  | cons u w ih => exact (tsupport_hD u _).trans ih

private theorem compact_hW (w : List (E × E)) {g : E → ℂ} (hc : HasCompactSupport g) :
    HasCompactSupport (hW w g) :=
  hc.mono' ((subset_tsupport _).trans (tsupport_hW w g))

private theorem fderiv_hD {U : Set E} (hU : IsOpen U) {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g U)
    {x : E} (hx : x ∈ U) (u : E × E) (v : E) :
    fderiv ℝ (hD u g) x v = (1 / 2 : ℂ) * (fderiv ℝ (fun y => fderiv ℝ g y u.1) x v -
      Complex.I * fderiv ℝ (fun y => fderiv ℝ g y u.2) x v) := by
  have hd : ∀ a : E, DifferentiableAt ℝ (fun y => fderiv ℝ g y a) x := fun a =>
    ((contDiffOn_fd hU hg a).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have h := (((hd u.1).hasFDerivAt.sub ((hd u.2).hasFDerivAt.const_mul Complex.I)).const_mul
    (1 / 2 : ℂ)).fderiv
  have e : hD u g = fun y => (1 / 2 : ℂ) *
      (((fun y => fderiv ℝ g y u.1) - fun y => Complex.I * fderiv ℝ g y u.2) y) := rfl
  rw [e, h]
  simp

private theorem hD_comm {U : Set E} (hU : IsOpen U) {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g U)
    {x : E} (hx : x ∈ U) (u v : E × E) : hD u (hD v g) x = hD v (hD u g) x := by
  have c := fderiv_fderiv_comm hU hg hx
  rw [hD, hD.eq_1 v (hD u g), fderiv_hD hU hg hx, fderiv_hD hU hg hx, fderiv_hD hU hg hx,
    fderiv_hD hU hg hx, c v.1 u.1, c v.2 u.1, c v.1 u.2, c v.2 u.2]
  ring

private theorem hW_perm {U : Set E} (hU : IsOpen U) {l l' : List (E × E)} (h : l.Perm l') {g : E → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) : Set.EqOn (hW l g) (hW l' g) U := by
  induction h with
  | nil => exact fun _ _ => rfl
  | cons a _ ih =>
    intro x hx
    have := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) ih)
    show hD a _ x = hD a _ x
    unfold hW at this
    simp only [hD, this]
  | swap a b l =>
    intro x hx
    exact hD_comm hU (contDiffOn_hW hU l hg) hx b a
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

variable {μ : Measure E} [μ.IsAddHaarMeasure]

private theorem integral_hD_mul {U : Set E} (hU : IsOpen U) {Ψ g : E → ℂ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hc : HasCompactSupport Ψ) (hs : tsupport Ψ ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (u : E × E) :
    ∫ x, hD u Ψ x * g x ∂μ = -∫ x, Ψ x * hD u g x ∂μ := by
  have i1 : ∀ a : E, Integrable (fun x => fderiv ℝ Ψ x a * g x) μ := fun a =>
    integrable_mul_of_tsupport hU hg.continuousOn (contDiff_fd hΨ a).continuous
      (hc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans hs)
  have i2 : ∀ a : E, Integrable (fun x => Ψ x * fderiv ℝ g x a) μ := fun a =>
    integrable_mul_of_tsupport hU (contDiffOn_fd hU hg a).continuousOn hΨ.continuous hc hs
  have e1 : (fun x => hD u Ψ x * g x) = fun x => (1 / 2 : ℂ) *
      (fderiv ℝ Ψ x u.1 * g x - Complex.I * (fderiv ℝ Ψ x u.2 * g x)) := by
    funext x; simp only [hD]; ring
  have e2 : (fun x => Ψ x * hD u g x) = fun x => (1 / 2 : ℂ) *
      (Ψ x * fderiv ℝ g x u.1 - Complex.I * (Ψ x * fderiv ℝ g x u.2)) := by
    funext x; simp only [hD]; ring
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_sub (i1 _) ((i1 _).const_mul _),
    integral_sub (i2 _) ((i2 _).const_mul _), integral_const_mul, integral_const_mul,
    integral_partial_mul hU hΨ hc hs hg, integral_partial_mul hU hΨ hc hs hg]
  ring

private theorem integral_hW_mul {U : Set E} (hU : IsOpen U) {Φ : E → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ) (hs : tsupport Φ ⊆ U) (w : List (E × E)) :
    ∀ f : E → ℂ, ContDiffOn ℝ ∞ f U →
      ∫ x, hW w Φ x * f x ∂μ = (-1) ^ w.length * ∫ x, Φ x * hW w.reverse f x ∂μ := by
  induction w with
  | nil => intro f _; simp [hW]
  | cons u w ih =>
    intro f hf
    have step := integral_hD_mul (μ := μ) hU (contDiff_hW w hΦ) (compact_hW w hc)
      ((tsupport_hW w Φ).trans hs) hf u
    have e : hW (u :: w).reverse f = hW w.reverse (hD u f) := by
      simp [hW, List.foldr_append]
    show ∫ x, hD u (hW w Φ) x * f x ∂μ = _
    rw [step, ih _ (contDiffOn_hD hU u hf), e, List.length_cons, pow_succ]
    ring

end General

section Specific

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private def word (τ : K →+* ℂ) (p : Equiv.Perm (Fin n)) (l : List (Fin n)) : List (Lie K n × Lie K n) :=
  l.map fun j => (toL (single (p j) j (atEmb τ 1)), toL (single (p j) j (atEmb τ Complex.I)))

private theorem foldr_pd_eq (τ : K →+* ℂ) (p : Equiv.Perm (Fin n)) (F : Lie K n → ℂ) (l : List (Fin n)) :
    l.foldr (fun j G => pd τ (p j) j G) F = hW (word τ p l) F := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons, word, List.map_cons]
    rw [ih]
    rfl

private theorem detD_eq (τ : K →+* ℂ) (G : Lie K n → ℂ) :
    detD τ G = fun x => ∑ p : Equiv.Perm (Fin n),
      (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℂ) * hW (word τ p (List.finRange n)) G x := by
  funext x
  simp only [detD, foldr_pd_eq]

private theorem length_word (τ : K →+* ℂ) (p : Equiv.Perm (Fin n)) :
    (word τ p (List.finRange n)).length = n := by
  simp [word]

end Specific

end UpperTheory.V.Z.Inf

open UpperTheory.V.Z.Inf in
theorem UpperTheory.V.Z.Inf.parts :
    UpperTheory.V.Z.Inf.Parts := by
  intro K _ _ _ n τ Φ hT
  obtain ⟨hΦ, hc, hs⟩ := hT
  have hU : IsOpen (invSet K n) := isOpen_invSet
  haveI h1 : (volume : Measure (Cinf K)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI h2 : (volume : Measure (Fin n → Cinf K)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI h3 : (volume : Measure (Lie K n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hsub : tsupport (detD τ Φ) ⊆ tsupport Φ := by
    refine closure_minimal ?_ (isClosed_tsupport _)
    intro x hx
    by_contra h
    apply hx
    rw [detD_eq]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [image_eq_zero_of_notMem_tsupport (fun h' => h (tsupport_hW _ _ h')), mul_zero]
  refine ⟨⟨?_, hc.mono' ((subset_tsupport _).trans hsub), hsub.trans hs⟩, ?_⟩
  · rw [detD_eq]
    refine ContDiff.sum (fun p _ => ?_)
    exact contDiff_const.mul (contDiff_hW _ hΦ)
  · intro F hF
    rw [detD_eq, detD_eq]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [integral_finsetSum, integral_finsetSum, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun p _ => ?_
      set w := word τ p (List.finRange n)
      set c : ℂ := (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℂ)
      have h1 : ∫ x, c * hW w Φ x * F x = c * ∫ x, hW w Φ x * F x := by
        simp_rw [mul_assoc]; exact integral_const_mul _ _
      have h2 : ∫ x, Φ x * (c * hW w F x) = c * ∫ x, Φ x * hW w F x := by
        simp_rw [mul_left_comm (Φ _) (c)]; exact integral_const_mul _ _
      have h3 : ∫ x, Φ x * hW w.reverse F x = ∫ x, Φ x * hW w F x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ invSet K n
        · simp only
          rw [hW_perm hU (List.reverse_perm w) hF hx]
        · simp only
          rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), zero_mul, zero_mul]
      rw [h1, h2, integral_hW_mul hU hΦ hc hs w F hF, length_word, h3]
      ring
    · intro p _
      have hcont : ContinuousOn (fun x => (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℂ) *
          hW (word τ p (List.finRange n)) F x) (invSet K n) :=
        continuousOn_const.mul (contDiffOn_hW hU _ hF).continuousOn
      exact integrable_mul_of_tsupport hU hcont hΦ.continuous hc hs
    · intro p _
      have hi := (integrable_mul_of_tsupport (μ := volume) hU hF.continuousOn
        (contDiff_hW (word τ p (List.finRange n)) hΦ).continuous
        (compact_hW _ hc) ((tsupport_hW _ _).trans hs)).const_mul (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℂ)
      simpa only [mul_assoc] using hi
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.IsOpenEmbeddingVal
section
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GroundTheory.Automorphic

namespace UpperTheory.V.Z.Inf

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private def lm (y : Lie K n) : Lie K n →ₗ[ℝ] Lie K n :=
  LinearMap.mulLeft ℝ (A := Matrix (Fin n) (Fin n) (InfinitePlace K → ℂ)) (Matrix.of y)

private def placeOut (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Lie K n ≃ₗ[ℝ] (InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) where
  toFun x v := Matrix.of fun i j => x i j v
  invFun y i j v := y v i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem det_lm (y : Lie K n) : LinearMap.det (lm y) = nrm y ^ n := by
  classical
  set e := placeOut K n
  have hc : e.toLinearMap ∘ₗ lm y ∘ₗ e.symm.toLinearMap =
      LinearMap.pi (fun v => ((LinearMap.mulLeft ℂ (e y v)).restrictScalars ℝ) ∘ₗ LinearMap.proj v) := by
    apply LinearMap.ext; intro x
    funext v i j
    show (Matrix.of y * Matrix.of (fun i j v => x v i j)) i j v = ∑ k, y i k v * x v k j
    rw [Matrix.mul_apply, Finset.sum_apply]
    rfl
  rw [← LinearMap.det_conj _ e, hc, LinearMap.det_pi, nrm, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [det_restrictScalars_mulLeft, Fintype.card_fin]
  congr 3
  rw [show (Matrix.of y).det v = Pi.evalRingHom _ v (Matrix.of y).det from rfl, RingHom.map_det]
  rfl

private theorem nrm_lm (y x : Lie K n) : nrm (lm y x) = nrm y * nrm x := by
  show ∏ w, ‖(Matrix.of y * Matrix.of x).det w‖ ^ 2 = _
  simp only [nrm, Matrix.det_mul, Pi.mul_apply, norm_mul, mul_pow, Finset.prod_mul_distrib]

private theorem nrm_nonneg (x : Lie K n) : 0 ≤ nrm x :=
  Finset.prod_nonneg fun _ _ => by positivity

private theorem nrm_pos_iff (x : Lie K n) : 0 < nrm x ↔ x ∈ invSet K n := by
  have h : x ∈ invSet K n ↔ IsUnit (Matrix.of x).det := Matrix.isUnit_iff_isUnit_det (Matrix.of x)
  rw [h, Pi.isUnit_iff, (nrm_nonneg x).lt_iff_ne, ne_comm, nrm, Finset.prod_ne_zero_iff]
  simp

private theorem continuous_nrm : Continuous (nrm : Lie K n → ℝ) := by
  refine continuous_finsetProd _ fun w _ => (Continuous.norm ?_).pow 2
  exact (continuous_apply w).comp
    (continuous_id (X := Matrix (Fin n) (Fin n) (InfinitePlace K → ℂ))).matrix_det

private theorem isOpenEmbedding_val :
    Topology.IsOpenEmbedding (Units.val : GL (Fin n) (Cinf K) → Matrix (Fin n) (Fin n) (Cinf K)) := by
  refine ⟨Units.isEmbedding_val_mk' (f := fun x => Ring.inverse x.det • x.adjugate) ?_ ?_, ?_⟩
  · intro x hx
    have hd : IsUnit x.det := (Matrix.isUnit_iff_isUnit_det x).1 hx
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.smul (M := Cinf K) (f := fun x : Matrix (Fin n) (Fin n) (Cinf K) => Ring.inverse x.det) ?_
      ((continuous_id (X := Matrix (Fin n) (Fin n) (Cinf K))).matrix_adjugate).continuousAt
    exact ContinuousAt.comp_of_eq (NormedRing.inverse_continuousAt hd.unit)
      ((continuous_id (X := Matrix (Fin n) (Fin n) (Cinf K))).matrix_det).continuousAt hd.unit_spec.symm
  · intro u
    rw [Matrix.coe_units_inv, Matrix.inv_def]
  · have : Set.range (Units.val : GL (Fin n) (Cinf K) → Matrix (Fin n) (Fin n) (Cinf K)) = {x | IsUnit x} := by
      ext x; exact ⟨fun ⟨u, hu⟩ => hu ▸ u.isUnit, fun h => ⟨h.unit, h.unit_spec⟩⟩
    rw [this]
    exact isOpen_invSet (E := K) (a := n)

private theorem addHaar_vol : (volume : Measure (Lie K n)).IsAddHaarMeasure := by
  haveI : (volume : Measure (Cinf K)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin n → Cinf K)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

private theorem measurable_dens : Measurable fun x : Lie K n => ENNReal.ofReal ((nrm x)⁻¹ ^ n) :=
  ENNReal.measurable_ofReal.comp (continuous_nrm.measurable.inv.pow_const _)

private theorem map_lm (y : Lie K n) (hy : y ∈ invSet K n) :
    Measure.map (lm y) ((volume : Measure (Lie K n)).withDensity fun x => ENNReal.ofReal ((nrm x)⁻¹ ^ n)) =
      (volume : Measure (Lie K n)).withDensity fun x => ENNReal.ofReal ((nrm x)⁻¹ ^ n) := by
  haveI := addHaar_vol (K := K) (n := n)
  have hp := (nrm_pos_iff y).2 hy
  have hdet : LinearMap.det (lm y) ≠ 0 := by rw [det_lm]; positivity
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Lie K n)) hdet
  refine map_withDensity_eq_of_scale (volume : Measure (Lie K n)) measurable_dens (lm y)
    (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero hdet))).ne' ENNReal.ofReal_ne_top hmap fun x => ?_
  rw [det_lm, nrm_lm, abs_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity), mul_inv, mul_pow,
    inv_pow (nrm y)]

end UpperTheory.V.Z.Inf

open UpperTheory.V.Z.Inf in
theorem UpperTheory.V.Z.Inf.haarL :
    UpperTheory.V.Z.Inf.HaarL := by
  intro K _ _ _ n _ _
  haveI := addHaar_vol (K := K) (n := n)
  set w : Lie K n → ENNReal := fun x => ENNReal.ofReal ((nrm x)⁻¹ ^ n) with hw
  set μL : Measure (Lie K n) := (volume : Measure (Lie K n)).withDensity w with hμL
  set e : GL (Fin n) (Cinf K) → Lie K n := fun g => toL g.val with he
  have hOE : Topology.IsOpenEmbedding e := isOpenEmbedding_val
  have hE : MeasurableEmbedding e := hOE.measurableEmbedding
  have hwm : Measurable w := measurable_dens
  have happ : ∀ s, Measure.comap e μL s = μL (e '' s) := fun s => hE.comap_apply _ s
  have hmem : ∀ g, e g ∈ invSet K n := fun g => g.isUnit
  have hpos : ∀ g, 0 < nrm (e g) := fun g => (nrm_pos_iff _).2 (hmem g)
  refine ⟨Measure.comap e μL, ?_, ?_⟩
  · refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
    · intro C hC
      rw [happ]
      have hC' : IsCompact (e '' C) := hC.image hOE.continuous
      have hmeas : MeasurableSet (e '' C) := hC'.isClosed.measurableSet
      have hcont : Continuous (fun g : GL (Fin n) (Cinf K) => (nrm (e g))⁻¹ ^ n) :=
        ((continuous_nrm.comp hOE.continuous).inv₀ fun g => (hpos g).ne').pow _
      obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
      rw [hμL, withDensity_apply _ hmeas]
      calc ∫⁻ x in e '' C, w x ∂volume
          ≤ ∫⁻ _ in e '' C, ENNReal.ofReal B ∂volume := by
            refine setLIntegral_mono' hmeas fun x hx => ?_
            obtain ⟨g, hg, rfl⟩ := hx
            exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hB g hg))
        _ = ENNReal.ofReal B * volume (e '' C) := setLIntegral_const _ _
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC'.measure_lt_top
    · intro g
      ext s hs
      have hm : Measurable (fun h : GL (Fin n) (Cinf K) => g * h) :=
        (continuous_const.mul continuous_id).measurable
      rw [Measure.map_apply hm hs, happ, happ]
      have hmeas : MeasurableSet (e '' s) := hE.measurableSet_image.2 hs
      have h1 : e '' ((fun h => g * h) ⁻¹' s) = (lm (e g)) ⁻¹' (e '' s) :=
        image_val_preimage_mul_left g s
      rw [h1, ← Measure.map_apply (lm (e g)).continuous_of_finiteDimensional.measurable hmeas,
        map_lm _ (hmem g)]
    · intro U hU hne
      rw [happ, ne_eq, hμL, withDensity_apply_eq_zero' hwm.aemeasurable]
      have hsub : {x | w x ≠ 0} ∩ e '' U = e '' U := by
        refine Set.inter_eq_right.2 ?_
        rintro _ ⟨g, _, rfl⟩
        exact (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 (hpos g)) _)).ne'
      rw [hsub]
      exact (hOE.isOpenMap U hU).measure_ne_zero volume (hne.image _)
  · have hr : Set.range e = invSet K n := by
      ext x
      exact ⟨fun ⟨g, hg⟩ => hg ▸ hmem g, fun h => ⟨IsUnit.unit h, rfl⟩⟩
    rw [hE.map_comap, hr, hμL, restrict_withDensity isOpen_invSet.measurableSet]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.TestEx
section
open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

namespace UpperTheory.V.Z.Inf

private theorem testEx_gen {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {U : Set E} (hU : IsOpen U) {f : E → ℂ} (hf : ContinuousOn f U) {A : E → ℝ} (hA : Continuous A)
    (hA0 : ∀ x ∈ U, 0 < A x) {x₀ : E} (hx₀ : x₀ ∈ U) (h0 : f x₀ ≠ 0) :
    ∃ Φ : E → ℂ, (ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ U) ∧
      (Differentiable ℂ fun s : ℂ => ∫ x, Φ x * f x * ((A x : ℝ) : ℂ) ^ s ∂μ) ∧
      ∃ s : ℂ, ∫ x, Φ x * f x * ((A x : ℝ) : ℂ) ^ s ∂μ ≠ 0 := by
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  set c : ℂ := starRingEnd ℂ (f x₀) with hc
  have hre : 0 < (c * f x₀).re := by
    rw [hc, mul_comm, Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_pos.2 h0
  have hca : ContinuousAt (fun x => (c * f x).re) x₀ :=
    Complex.continuous_re.continuousAt.comp (continuousAt_const.mul (hf.continuousAt (hU.mem_nhds hx₀)))
  have hW : U ∩ {x | 0 < (c * f x).re} ∈ 𝓝 x₀ :=
    inter_mem (hU.mem_nhds hx₀) (hca.eventually (lt_mem_nhds hre))
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hW
  let ψ : ContDiffBump x₀ := ⟨ε / 2, ε, by positivity, by linarith⟩
  have hψz : ∀ x, x ∉ closedBall x₀ ε → ψ x = 0 := fun x hx => by
    by_contra h
    have : x ∈ Function.support ψ := h
    rw [ψ.support_eq] at this
    exact hx (ball_subset_closedBall this)
  have hKc : IsCompact (closedBall x₀ ε) := isCompact_closedBall _ _
  have hKU : closedBall x₀ ε ⊆ U := fun x hx => (hball hx).1
  let F : ℂ → E → ℂ := fun s x => (ψ x : ℂ) * f x * ((A x : ℝ) : ℂ) ^ s
  have hFz : ∀ s x, x ∉ closedBall x₀ ε → F s x = 0 := fun s x hx => by
    simp only [F, hψz x hx, Complex.ofReal_zero, zero_mul]
  have hts : ∀ {G : E → ℂ}, (∀ x, x ∉ closedBall x₀ ε → G x = 0) → tsupport G ⊆ closedBall x₀ ε := fun h =>
    closure_minimal (fun x hx => by by_contra h'; exact hx (h x h')) isClosed_closedBall
  have hJ : ContinuousOn (fun p : ℂ × E => F p.1 p.2) (univ ×ˢ U) := by
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact (Complex.continuous_ofReal.comp (ψ.continuous.comp continuous_snd)).continuousOn
    · exact hf.comp continuousOn_snd fun p hp => hp.2
    · exact ContinuousOn.cpow (Complex.continuous_ofReal.comp (hA.comp continuous_snd)).continuousOn
        continuousOn_fst fun p hp => Complex.ofReal_mem_slitPlane.2 (hA0 _ hp.2)
  have hFc : ∀ s, Continuous (F s) := fun s => by
    have : ContinuousOn (F s) U :=
      hJ.comp (f := fun x : E => (s, x)) (by fun_prop) fun x hx => ⟨trivial, hx⟩
    exact this.continuous_of_tsupport_subset hU ((hts (hFz s)).trans hKU)
  have hFi : ∀ s, Integrable (F s) μ := fun s =>
    (hFc s).integrable_of_hasCompactSupport (HasCompactSupport.intro hKc (hFz s))
  have hΦz : ∀ x, x ∉ closedBall x₀ ε → (ψ x : ℂ) = 0 := fun x hx => by
    rw [hψz x hx, Complex.ofReal_zero]
  refine ⟨fun x => (ψ x : ℂ), ⟨?_, HasCompactSupport.intro hKc hΦz, (hts hΦz).trans hKU⟩, ?_, 0, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ψ.contDiff
  · rw [← differentiableOn_univ]
    refine GroundTheory.Automorphic.PseudoEisenstein.differentiableOn_integral_of_bound (F := F) isOpen_univ
      (fun x => ?_) (fun s _ => (hFc s).aestronglyMeasurable) fun s₀ _ => ?_
    · by_cases hx : x ∈ closedBall x₀ ε
      · refine Differentiable.differentiableOn ?_
        exact (differentiable_id.const_cpow (Or.inl (by exact_mod_cast (hA0 x (hKU hx)).ne'))).const_mul _
      · simp only [hFz _ x hx]
        exact differentiableOn_const _
    · obtain ⟨C, hC⟩ := ((isCompact_closedBall s₀ 1).prod hKc).exists_bound_of_continuousOn
        (hJ.mono (prod_mono (subset_univ _) hKU))
      refine ⟨1, one_pos, subset_univ _, (closedBall x₀ ε).indicator fun _ => C, ?_, fun s hs x => ?_⟩
      · rw [integrable_indicator_iff isClosed_closedBall.measurableSet]
        exact integrableOn_const hKc.measure_lt_top.ne
      · by_cases hx : x ∈ closedBall x₀ ε
        · rw [indicator_of_mem hx]
          exact hC (s, x) ⟨hs, hx⟩
        · rw [indicator_of_notMem hx, hFz s x hx, norm_zero]
  · intro hz
    change ∫ x, F 0 x ∂μ = 0 at hz
    have hr : ∀ x, (c * F 0 x).re = ψ x * (c * f x).re := fun x => by
      simp only [F, Complex.cpow_zero, mul_one]
      rw [mul_left_comm, Complex.re_ofReal_mul]
    have hrc : Continuous fun x => (c * F 0 x).re :=
      Complex.continuous_re.comp (continuous_const.mul (hFc 0))
    have hr0 : 0 ≤ fun x => (c * F 0 x).re := fun x => by
      change 0 ≤ (c * F 0 x).re
      by_cases hx : x ∈ closedBall x₀ ε
      · rw [hr]
        exact mul_nonneg ψ.nonneg (le_of_lt (hball hx).2)
      · rw [hFz 0 x hx]; simp
    have hri : Integrable (fun x => (c * F 0 x).re) μ := ((hFi 0).const_mul c).re
    have hpos : 0 < ∫ x, (c * F 0 x).re ∂μ := by
      rw [integral_pos_iff_support_of_nonneg hr0 hri]
      refine hrc.isOpen_support.measure_pos μ ⟨x₀, ?_⟩
      change (c * F 0 x₀).re ≠ 0
      rw [hr, ψ.one_of_mem_closedBall (mem_closedBall_self ψ.rIn_pos.le), one_mul]
      exact hre.ne'
    have h1 := integral_re ((hFi 0).const_mul c)
    simp only [RCLike.re_to_complex] at h1
    rw [h1, integral_const_mul, hz, mul_zero, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos

end UpperTheory.V.Z.Inf

theorem UpperTheory.V.Z.Inf.testEx :
    UpperTheory.V.Z.Inf.TestEx := by
  intro K _ _ _ n f hf ⟨x₀, hx₀, h0⟩
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Fin n → GlobalTheory.CuspRep.Cinf K)) := Measure.pi.isAddHaarMeasure _
  haveI : Measure.IsAddHaarMeasure (volume : Measure (GlobalTheory.CuspRep.Lie K n)) := Measure.pi.isAddHaarMeasure _
  refine UpperTheory.V.Z.Inf.testEx_gen volume GlobalTheory.CuspRep.isOpen_invSet hf (A := UpperTheory.V.Z.Inf.nrm) ?_ ?_ hx₀ h0
  · unfold UpperTheory.V.Z.Inf.nrm
    refine continuous_finsetProd _ fun w _ => Continuous.pow (Continuous.norm ?_) 2
    exact (continuous_apply w).comp (Continuous.matrix_det continuous_id)
  · intro x hx
    have hu : IsUnit (Matrix.of x).det := (Matrix.isUnit_iff_isUnit_det _).1 hx
    unfold UpperTheory.V.Z.Inf.nrm
    refine Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 ?_) 2
    exact (hu.map (Pi.evalMonoidHom _ w)).ne_zero
end

