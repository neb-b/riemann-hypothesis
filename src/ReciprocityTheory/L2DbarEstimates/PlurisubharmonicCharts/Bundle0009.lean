module

public import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0006
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalc

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
section
open MeasureTheory Filter Topology Complex ComplexConjugate
open scoped ContDiff ENNReal ComplexOrder

namespace ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

universe u

variable {n : ℕ}

private theorem contDiffAt_ofReal_comp' {f : V n → ℝ} {x : V n} {m : WithTop ℕ∞} (hf : ContDiffAt ℝ m f x) :
    ContDiffAt ℝ m (fun v => ((f v : ℝ) : ℂ)) x := by
  first
  | exact Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  | exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x hf).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun v => by simp)
  | fun_prop

private theorem fderiv_wdb_apply_of_hasFDerivAt_flip {g : V n → ℂ} {x : V n} (k : Fin n)
    (hlin : ∀ v : V n, HasFDerivAt (fun y => fderiv ℝ g y v) ((fderiv ℝ (fderiv ℝ g) x).flip v) x)
    (u : V n) : fderiv ℝ (wdb n k g) x u =
      (fderiv ℝ (fderiv ℝ g) x u (bas n k) +
        Complex.I * fderiv ℝ (fderiv ℝ g) x u (Complex.I • bas n k)) / 2 := by
  have h3 := ((hlin (bas n k)).add ((hlin (Complex.I • bas n k)).const_mul Complex.I)).mul_const
    ((2 : ℂ)⁻¹)
  have hw : wdb n k g = fun y =>
      (fderiv ℝ g y (bas n k) + Complex.I * fderiv ℝ g y (Complex.I • bas n k)) * (2 : ℂ)⁻¹ := by
    funext y
    simp only [wdb]
    ring
  rw [hw]
  first
  | rw [(show HasFDerivAt (𝕜 := ℝ) (fun y => (fderiv ℝ g y (bas n k) +
      Complex.I * fderiv ℝ g y (Complex.I • bas n k)) * (2 : ℂ)⁻¹) _ x from h3).fderiv]
  | erw [h3.fderiv]
  simp [div_eq_mul_inv]
  try ring

theorem cmpb_det_nonneg {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hL : ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => ((f v : ℝ) : ℂ)) x ξ).re) :
    0 ≤ (cHess n (fun v => ((f v : ℝ) : ℂ)) x).det.re := by
  set g : V n → ℂ := fun v => ((f v : ℝ) : ℂ) with hgeq
  have hg2 : ContDiffAt ℝ 2 g x := contDiffAt_ofReal_comp' hf
  have hD : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg2.fderiv_right (m := 1) (by first | exact one_add_one_eq_two.le | norm_num)).differentiableAt (by first | exact one_ne_zero | exact le_rfl)
  have hsym : ∀ u v : V n, fderiv ℝ (fderiv ℝ g) x u v = fderiv ℝ (fderiv ℝ g) x v u := by
    have hs : IsSymmSndFDerivAt ℝ g x := by
      first
      | exact hg2.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
      | exact hg2.isSymmSndFDerivAt (by simp [minSmoothness])
      | exact hg2.isSymmSndFDerivAt le_rfl
    exact fun u v => hs u v
  have hlin : ∀ v : V n, HasFDerivAt (fun y => fderiv ℝ g y v)
      ((fderiv ℝ (fderiv ℝ g) x).flip v) x := by
    intro v
    have h := hD.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
    first
    | simpa using h
    | (convert h using 1; simp)
  have hval : ∀ u v : V n, fderiv ℝ (fun y => fderiv ℝ g y v) x u = fderiv ℝ (fderiv ℝ g) x u v := by
    intro u v
    rw [(hlin v).fderiv, ContinuousLinearMap.flip_apply]
  have hc1 : ∀ y v : V n, (starRingEnd ℂ) (fderiv ℝ g y v) = fderiv ℝ g y v := by
    intro y v
    have e : fderiv ℝ ((Complex.conjCLE : ℂ → ℂ) ∘ g) y =
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g y) := Complex.conjCLE.comp_fderiv
    have hg' : (Complex.conjCLE : ℂ → ℂ) ∘ g = g := by
      funext z; simp [hgeq]
    rw [hg'] at e
    have := congrArg (fun L : V n →L[ℝ] ℂ => L v) e
    simpa using this.symm
  have hc2 : ∀ u v : V n, (starRingEnd ℂ) (fderiv ℝ (fderiv ℝ g) x u v) = fderiv ℝ (fderiv ℝ g) x u v := by
    intro u v
    have e : fderiv ℝ ((Complex.conjCLE : ℂ → ℂ) ∘ fun y => fderiv ℝ g y v) x =
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ (fun y => fderiv ℝ g y v) x) :=
      Complex.conjCLE.comp_fderiv
    have hh : (Complex.conjCLE : ℂ → ℂ) ∘ (fun y => fderiv ℝ g y v) = fun y => fderiv ℝ g y v := by
      funext z; simpa using hc1 z v
    rw [hh] at e
    have := congrArg (fun L : V n →L[ℝ] ℂ => L u) e
    rw [← hval u v]
    simpa using this.symm
  have key : ∀ (k : Fin n) (u : V n), fderiv ℝ (wdb n k g) x u =
      (fderiv ℝ (fderiv ℝ g) x u (bas n k) +
        Complex.I * fderiv ℝ (fderiv ℝ g) x u (Complex.I • bas n k)) / 2 :=
    fun k u => fderiv_wdb_apply_of_hasFDerivAt_flip k hlin u
  have hH : ∀ j k : Fin n, cHess n g x j k =
      (fderiv ℝ (fderiv ℝ g) x (bas n j) (bas n k) +
        fderiv ℝ (fderiv ℝ g) x (Complex.I • bas n j) (Complex.I • bas n k) +
        Complex.I * (fderiv ℝ (fderiv ℝ g) x (bas n j) (Complex.I • bas n k) -
          fderiv ℝ (fderiv ℝ g) x (Complex.I • bas n j) (bas n k))) / 4 := by
    intro j k
    simp only [cHess, Matrix.of_apply, wd, key]
    linear_combination (-(fderiv ℝ (fderiv ℝ g) x (Complex.I • bas n j) (Complex.I • bas n k)) / 4) *
      Complex.I_sq
  have hHerm : (cHess n g x).IsHermitian := by
    refine Matrix.IsHermitian.ext fun j k => ?_
    show (starRingEnd ℂ) (cHess n g x k j) = cHess n g x j k
    rw [hH k j, hH j k]
    simp only [map_div₀, map_add (f := _), map_sub, map_mul, Complex.conj_I, hc2, map_ofNat]
    linear_combination (1 / 4 : ℂ) * hsym (bas n k) (bas n j) +
      (1 / 4 : ℂ) * hsym (Complex.I • bas n k) (Complex.I • bas n j) -
      (Complex.I / 4) * hsym (bas n k) (Complex.I • bas n j) +
      (Complex.I / 4) * hsym (Complex.I • bas n k) (bas n j)
  have hq : ∀ v : Fin n → ℂ,
      dotProduct (star v) (Matrix.mulVec (cHess n g x) v) = leviV n g x (star v) := by
    intro v
    simp only [dotProduct, Matrix.mulVec, leviV, cHess, Matrix.of_apply, Finset.mul_sum,
      Pi.star_apply, starRingEnd_apply, star_star]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hnn : ∀ v : Fin n → ℂ, 0 ≤ dotProduct (star v) (Matrix.mulVec (cHess n g x) v) := by
    intro v
    have him : (dotProduct (star v) (Matrix.mulVec (cHess n g x) v)).im = 0 := by
      first
      | simpa using hHerm.im_star_dotProduct_mulVec_self v
      | exact hHerm.im_star_dotProduct_mulVec_self v
    have hre : 0 ≤ (dotProduct (star v) (Matrix.mulVec (cHess n g x) v)).re := by
      rw [hq v]; exact hL (star v)
    exact Complex.le_def.2 ⟨by simpa using hre, by simpa using him.symm⟩
  have hPSD : (cHess n g x).PosSemidef := by
    first
    | exact ⟨hHerm, hnn⟩
    | exact ⟨hHerm, fun v => hnn v⟩
    | refine ⟨hHerm, fun v => ?_⟩
      have h := hnn ⇑v
      convert h using 1
      simp [Finsupp.sum_fintype, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hdet := hPSD.det_nonneg
  simpa using (Complex.le_def.1 hdet).1

theorem cmpb_leviV_const (c : ℝ) (x : V n) (ξ : Fin n → ℂ) :
    leviV n (fun _ => ((c : ℝ) : ℂ)) x ξ = 0 := by
  have h : ∀ k, wdb n k (fun _ : V n => ((c : ℝ) : ℂ)) = fun _ => 0 := by
    intro k; funext y; simp [wdb]
  simp [leviV, h, wd]

theorem cmpb_cHess_congr {g₁ g₂ : V n → ℂ} {x : V n} (h : g₁ =ᶠ[𝓝 x] g₂) :
    cHess n g₁ x = cHess n g₂ x := by
  have hw : ∀ k, wdb n k g₁ =ᶠ[𝓝 x] wdb n k g₂ := by
    intro k
    have hn : ∀ᶠ y in 𝓝 x, g₁ =ᶠ[𝓝 y] g₂ := by
      first
      | exact h.eventuallyEq_nhds
      | exact h.eventually_nhds
    filter_upwards [hn] with y hy
    simp only [wdb, hy.fderiv_eq]
  ext j k
  simp only [cHess, Matrix.of_apply, wd, (hw k).fderiv_eq]

theorem cmpb_cHess_add_const (g : V n → ℂ) (c : ℂ) (x : V n) :
    cHess n (fun v => g v + c) x = cHess n g x := by
  have h : ∀ k, wdb n k (fun v => g v + c) = wdb n k g := by
    intro k; funext y; simp only [wdb, fderiv_add_const]
  ext j k
  simp only [cHess, Matrix.of_apply, h]

section Atlas

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

namespace WeightedAtlas

end WeightedAtlas

end Atlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DifferentiableAtLocalCoordinates
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem isCoveringMapOn_of_proper {n : ℕ} {E : Type*} [TopologicalSpace E] [T2Space E] (z : E → V n)
    (U : Set (V n)) (hU : IsOpen U) (hz : ∀ x, z x ∈ U) (hl : IsLocalHomeomorph z)
    (hp : ∀ K : Set (V n), IsCompact K → K ⊆ U → IsCompact (z ⁻¹' K)) :
    IsCoveringMapOn z U ∧ ∀ y, (z ⁻¹' {y}).Finite := by
  let g : E → U := fun x => ⟨z x, hz x⟩
  have hgc : Continuous g := hl.continuous.subtype_mk _
  have hgl : IsLocalHomeomorph g :=
    IsLocalHomeomorph.of_comp (g := Subtype.val) (by simpa [Function.comp_def, g] using hl)
      hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph hgc
  have hgp : IsProperMap g := by
    refine isProperMap_iff_isCompact_preimage.2 ⟨hgc, fun K hK => ?_⟩
    have h1 := hp (Subtype.val '' K) (hK.image continuous_subtype_val)
      (by rintro _ ⟨y, -, rfl⟩; exact y.2)
    have h2 : g ⁻¹' K = z ⁻¹' (Subtype.val '' K) := by
      ext x; simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx; exact ⟨g x, hx, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have : y = g x := Subtype.ext hyx
        rw [← this]; exact hy
    rw [h2]; exact h1
  have hfib : ∀ y (hy : y ∈ U), (z ⁻¹' {y}).Finite := by
    intro y hy
    have h2 : z ⁻¹' {y} = g ⁻¹' {⟨y, hy⟩} := by
      ext x; simp [g, Subtype.ext_iff]
    rw [h2]
    refine (hgp.isCompact_preimage isCompact_singleton).finite ?_
    refine (hgl.isLocalHomeomorphOn.mono (Set.subset_univ _)).isDiscrete_of_image ?_
    refine (Set.subsingleton_singleton.anti (Set.image_preimage_subset _ _)).isDiscrete
  refine ⟨?_, fun y => ?_⟩
  · refine IsCoveringMapOn.of_isCoveringMap_subtype hU hz ?_
    refine isCoveringMap_iff_isCoveringMapOn_univ.2 ?_
    refine hgp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn (fun x _ => ?_)
      hgl.isLocalHomeomorphOn
    have h2 : g ⁻¹' {x} = z ⁻¹' {(x : V n)} := by
      ext x'; simp [g, Subtype.ext_iff]
    rw [h2]; exact hfib x x.2
  · by_cases hy : y ∈ U
    · exact hfib y hy
    · convert Set.finite_empty
      ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h; exact hy (h ▸ hz x)

section atlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem transition_zero_eq_one (A : WeightedAtlas n Y ι La) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) : A.g 0 i j y = 1 := by
  have h := A.g_add 0 0 i j y hi hj
  rw [add_zero] at h
  have hne := A.g_ne 0 i j y hi hj
  exact mul_left_cancel₀ hne ((h.symm).trans (mul_one _).symm)

theorem transition_nsmul_eq_pow (A : WeightedAtlas n Y ι La) (la : La) (m : ℕ) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    A.g (m • la) i j y = A.g la i j y ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero, transition_zero_eq_one A i j y hi hj]
  | succ k ih => rw [succ_nsmul, A.g_add _ _ i j y hi hj, ih, pow_succ]

theorem weight_zero_eq_zero (A : WeightedAtlas n Y ι La) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) : A.ph 0 i y = 0 := by
  have h := A.ph_add 0 0 i y hi
  rw [add_zero] at h
  linarith

theorem weight_nsmul_eq_mul (A : WeightedAtlas n Y ι La) (la : La) (m : ℕ) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) : A.ph (m • la) i y = m * A.ph la i y := by
  induction m with
  | zero => rw [zero_nsmul, weight_zero_eq_zero A i y hi]; simp
  | succ k ih => rw [succ_nsmul, A.ph_add _ _ i y hi, ih]; push_cast; ring

theorem ratio_pow_chart_independent (A : WeightedAtlas n Y ι La) (la : La) (m : ℕ) (F w0 : ι → Y → ℂ)
    (hF : A.IsSec (m • la) F) (hw : A.IsSec la w0) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    F i y / w0 i y ^ m = F j y / w0 j y ^ m := by
  rw [hF.2 i j y (Set.mem_univ y) hi hj, hw.2 i j y (Set.mem_univ y) hi hj,
    transition_nsmul_eq_pow A la m i j y hi hj, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (A.g_ne la i j y hi hj))

theorem ne_zero_of_overlap_ne_zero (A : WeightedAtlas n Y ι La) (la : La) (w0 : ι → Y → ℂ)
    (hw : A.IsSec la w0) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) (h : w0 j y ≠ 0) :
    w0 i y ≠ 0 := by
  rw [hw.2 i j y (Set.mem_univ y) hi hj]
  exact mul_ne_zero (A.g_ne la i j y hi hj) h

theorem localCoordinates_eq_zmap (A : WeightedAtlas n Y ι La) (la : La) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (hw : A.IsSec la w0) (hs : ∀ k, A.IsSec la (s k)) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) :
    A.zLoc w0 s i (A.chart i y) = A.zmap w0 s y := by
  simp only [zLoc, zmap, (A.chart i).left_inv hi]
  congr 1
  funext k
  have := ratio_pow_chart_independent A la 1 (s k) w0 (by rw [one_nsmul]; exact hs k) hw i (A.pick y) y hi
    (A.mem_pick y)
  simpa using this

end atlas

theorem holo_restrict_open {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n) (u : M → ℂ)
    (hu : Holo n z u) (S : Set M) (hS : IsOpen S) [Nonempty S] :
    Holo n (fun x : S => z x) (fun x : S => u x) := by
  intro e he
  let f := hS.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : S → M)
  have hc : IsChart n z (f.symm.trans e) := by
    intro x hx
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage, f, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] at hx
    obtain ⟨⟨x', rfl⟩, hx2⟩ := hx
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, f,
      hS.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv] at hx2 ⊢
    exact he hx2
  have h2 := hu _ hc
  have ht : (f.symm.trans e).target = e.target := by
    simp [f]
  rw [ht] at h2
  refine h2.congr (fun v hv => ?_)
  simp [f, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]

theorem sub_isBigO_of_det_ne_zero {n : ℕ} {q : V n → V n} {D : V n →L[ℂ] V n} {a : V n}
    (hq : HasFDerivAt q D a) (hD : LinearMap.det (D : V n →ₗ[ℂ] V n) ≠ 0) :
    (fun x => x - a) =O[𝓝 a] (fun x => q x - q a) := by
  let E : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero (D : V n →ₗ[ℂ] V n) hD).toContinuousLinearEquiv
  have hE : ∀ x, E x = D x := by
    intro x
    rfl
  have h1 : (fun x => x - a) =O[𝓝 a] (fun x => D (x - a)) := by
    simpa [hE] using E.isBigO_sub_rev (𝓝 a) a
  have h3 : (fun x => D (x - a) - (q x - q a)) =o[𝓝 a] (fun x => D (x - a)) := by
    have := (hq.isLittleO.trans_isBigO h1).neg_left
    refine this.congr_left (fun x => ?_)
    abel
  have h4 := h3.right_isBigO_sub
  refine h1.trans (h4.congr_right (fun x => ?_))
  abel

section atlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem differentiableAt_localCoordinates (A : WeightedAtlas n Y ι La) (la : La) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (hw : A.IsSec la w0) (hs : ∀ k, A.IsSec la (s k)) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (h0 : w0 i y ≠ 0) :
    DifferentiableAt ℂ (A.zLoc w0 s i) (A.chart i y) := by
  have hT : (A.chart i).target ∈ 𝓝 (A.chart i y) :=
    (A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)
  have hd : ∀ F : ι → Y → ℂ, A.IsSec la F →
      DifferentiableAt ℂ (fun v => F i ((A.chart i).symm v)) (A.chart i y) := by
    intro F hF
    have := hF.1 i
    simp only [Set.preimage_univ, Set.inter_univ] at this
    exact (this.differentiableAt hT)
  rw [differentiableAt_euclidean]
  intro k
  simp only [zLoc, PiLp.toLp_apply, div_eq_mul_inv]
  refine (hd (s k) (hs k)).mul ((hd w0 hw).inv ?_)
  simpa [(A.chart i).left_inv hi] using h0

end atlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

