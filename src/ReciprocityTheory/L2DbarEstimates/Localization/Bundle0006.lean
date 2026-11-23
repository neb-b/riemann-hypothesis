module

public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports
public import ReciprocityTheory.L2DbarEstimates.Localization.LocalizeA
public import ReciprocityTheory.L2DbarEstimates.Localization.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.Localization.Localize
section
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem localize (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hMD : MultDivStatement n M) (hMS : MultSStatement n M) :
    LocalizeStatement n M := by
  intro z hz H G D S hG hD hS hGD hGS hcG hcD hcS
  have := loc_weaklyLocallyCompact n z hz
  have hK : IsCompact (tsupport G ∪ tsupport D ∪ tsupport S) := (hcG.union hcD).union hcS
  set K := tsupport G ∪ tsupport D ∪ tsupport S with hKdef
  obtain ⟨K', hK', hKK'⟩ := exists_compact_superset hK
  obtain ⟨N, e, χ, he, hχs, hχc, hχsub, -, -, hχK⟩ :=
    exists_chart_partition n z hz K' univ hK' isOpen_univ (subset_univ _)
  have hck : ∀ i, Ck n z 1 (fun y => (χ i y : ℂ)) := fun i => SmoothR.ckR n z 1 (χ i) (hχs i)
  have hoff : ∀ x, x ∉ K → G x = 0 ∧ D x = 0 ∧ S x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport fun h => hx (Or.inl (Or.inl h)),
     image_eq_zero_of_notMem_tsupport fun h => hx (Or.inl (Or.inr h)),
     image_eq_zero_of_notMem_tsupport fun h => hx (Or.inr h)⟩
  have hone : ∀ x ∈ K, ∑ i, (χ i x : ℂ) = 1 := fun x hx => by
    rw [← Complex.ofReal_sum, hχK x (interior_subset (hKK' hx)), Complex.ofReal_one]
  have hev : ∀ x ∈ K, (fun y => ∑ i, (χ i y : ℂ)) =ᶠ[𝓝 x] fun _ => (1 : ℂ) := fun x hx => by
    filter_upwards [isOpen_interior.mem_nhds (hKK' hx)] with y hy
    rw [← Complex.ofReal_sum, hχK y (interior_subset hy), Complex.ofReal_one]
  have hdz : ∀ x ∈ K, ∀ j, ∑ i, d n z j (fun y => (χ i y : ℂ)) x = 0 := fun x hx j => by
    rw [← loc_d_sum n z Finset.univ _ hck j x, loc_d_congr n z hz j _ _ x (hev x hx), d_const]
  have hdbz : ∀ x ∈ K, ∀ j, ∑ i, db n z j (fun y => (χ i y : ℂ)) x = 0 := fun x hx j => by
    rw [← loc_db_sum n z Finset.univ _ hck j x, loc_db_congr n z hz j _ _ x (hev x hx), db_const]
  have sG : ∀ x, G x = ∑ i, locG (χ i) G x := fun x => by
    by_cases hx : x ∈ K
    · simp only [locG]; rw [← Finset.sum_smul, hone x hx, one_smul]
    · simp [locG, (hoff x hx).1]
  have sD : ∀ x, D x = ∑ i, locD n z (χ i) G D x := fun x => by
    by_cases hx : x ∈ K
    · simp only [locD, Finset.sum_add_distrib, ← Finset.sum_mul, hone x hx, one_mul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, hdz x hx, zero_mul, Finset.sum_const_zero, add_zero]
    · simp [locD, (hoff x hx).1, (hoff x hx).2.1]
  have sS : ∀ x j k, S x j k = ∑ i, locS n z (χ i) G S x j k := fun x j k => by
    by_cases hx : x ∈ K
    · simp only [locS, wedge, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        hone x hx, one_mul, hdbz x hx, zero_mul, sub_self, add_zero]
    · simp [locS, wedge, (hoff x hx).1, (hoff x hx).2.2]
  have hP := fun i => loc_piece n z hz hMD hMS (χ i) (hχs i) (hχc i) (e i).source
    ((hχsub i).trans inter_subset_left) G D S hG hD hS hGD hGS
  choose K0 hK0 happ using fun i => H (e i) _ _ _ (he i) (hP i).1 (hP i).2.1 (hP i).2.2.1
    (hP i).2.2.2.1 (hP i).2.2.2.2.1 (hP i).2.2.2.2.2.1 (hP i).2.2.2.2.2.2.1
    (hP i).2.2.2.2.2.2.2.1 (hP i).2.2.2.2.2.2.2.2.1 (hP i).2.2.2.2.2.2.2.2.2.1
    (hP i).2.2.2.2.2.2.2.2.2.2
  refine ⟨⋃ i, K0 i, isCompact_iUnion hK0, fun δ hδ => ?_⟩
  obtain ⟨δ', hδ'0, hδ'⟩ := ENNReal.exists_pos_mul_lt (a := (N : ℝ≥0∞) * N) (b := δ)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) (ENNReal.natCast_ne_top N)) hδ.ne'
  choose g hgT hg0 hg1 hg2 hg3 using fun i => happ i δ' hδ'0
  have hgc : ∀ i j, Ck n z 2 (fun x => g i x j) := fun i j => (hgT i j).1
  have hgc1 : ∀ i j, Ck n z (0 + 1) (fun x => g i x j) := fun i j =>
    Ck.mono n z 1 2 (by norm_num) _ (hgc i j)
  have hfun : ∀ j, (fun x => (∑ i, g i x) j) = fun x => ∑ i, g i x j := fun j =>
    funext fun x => loc_sum_apply _ j
  have hvan : ∀ x, x ∉ ⋃ i, K0 i → ∑ i, g i x = 0 := fun x hx =>
    Finset.sum_eq_zero fun i _ => hg0 i x fun h => hx (mem_iUnion.2 ⟨i, h⟩)
  have hgcont : ∀ i, Continuous (g i) := fun i => by
    have : Continuous (fun x => WithLp.toLp 2 (fun j => g i x j)) :=
      (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => Ck.continuous n z hz 2 _ (hgc i j))
    exact this
  have hdivc : ∀ i, Continuous (divF n z (g i)) := fun i => by
    unfold divF
    exact continuous_finsetSum _ fun j _ => Ck.continuous n z hz 0 _ (Ck.d n z 0 j _ (hgc1 i j))
  have hsbc : ∀ i, Continuous (sbar n z (g i)) := fun i => by
    unfold sbar
    exact continuous_pi fun j => continuous_pi fun k =>
      (Ck.continuous n z hz 0 _ (Ck.db n z 0 j _ (hgc1 i k))).sub
        (Ck.continuous n z hz 0 _ (Ck.db n z 0 k _ (hgc1 i j)))
  have hdiv : ∀ x, divF n z (fun x => ∑ i, g i x) x = ∑ i, divF n z (g i) x := fun x => by
    simp only [divF]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfun j, loc_d_sum n z Finset.univ (fun i y => g i y j) (fun i => hgc1 i j) j x]
  have hsb : ∀ x j k, sbar n z (fun x => ∑ i, g i x) x j k = ∑ i, sbar n z (g i) x j k :=
    fun x j k => by
    simp only [sbar]
    rw [hfun k, hfun j, loc_db_sum n z _ (fun i y => g i y k) (fun i => hgc1 i k) j x,
      loc_db_sum n z _ (fun i y => g i y j) (fun i => hgc1 i j) k x, Finset.sum_sub_distrib]
  refine ⟨fun x => ∑ i, g i x, fun j => ⟨?_, ?_⟩, hvan, ?_, ?_, ?_⟩
  · rw [hfun j]; exact loc_ck_sum n z 2 _ _ fun i => hgc i j
  · refine HasCompactSupport.intro (isCompact_iUnion hK0) fun x hx => ?_
    show (∑ i, g i x) j = 0
    rw [hvan x hx]; rfl
  · unfold nV
    refine loc_lintegral_sum_lt (vol n z) _ (fun i x => ENNReal.ofReal (‖g i x - locG (χ i) G x‖ ^ 2 *
      Real.exp (-(fun _ : M => (0 : ℝ)) x))) (fun i => loc_aem _ _ ((hgcont i).aestronglyMeasurable.sub
      (hP i).1.1)) (fun x => ?_) δ' δ (fun i => hg1 i) hδ'
    simp only [neg_zero, Real.exp_zero, mul_one]
    have : (∑ i, g i x) - G x = ∑ i, (g i x - locG (χ i) G x) := by
      rw [Finset.sum_sub_distrib, ← sG x]
    rw [this]
    exact loc_ofReal_le _ (fun i => by positivity) _ (loc_norm_sum_sq _)
  · unfold wint
    refine loc_lintegral_sum_lt (vol n z) _ (fun i x => ENNReal.ofReal
      (‖divF n z (g i) x - locD n z (χ i) G D x‖ ^ 2 * Real.exp (-(fun _ : M => (0 : ℝ)) x)))
      (fun i => loc_aem _ _ ((hdivc i).aestronglyMeasurable.sub (hP i).2.1.1)) (fun x => ?_) δ' δ
      (fun i => hg2 i) hδ'
    simp only [neg_zero, Real.exp_zero, mul_one]
    have : divF n z (fun x => ∑ i, g i x) x - D x =
        ∑ i, (divF n z (g i) x - locD n z (χ i) G D x) := by
      rw [hdiv x, Finset.sum_sub_distrib, ← sD x]
    rw [this]
    exact loc_ofReal_le _ (fun i => by positivity) _ (loc_norm_sum_sq _)
  · unfold n2
    refine loc_lintegral_sum_lt (vol n z) _ (fun i x => ENNReal.ofReal
      (sq2 n (sbar n z (g i) x - locS n z (χ i) G S x) * Real.exp (-(fun _ : M => (0 : ℝ)) x)))
      (fun i => aemeasurable_unweighted_two_form _ _ ((hsbc i).aestronglyMeasurable.sub (hP i).2.2.1.1)) (fun x => ?_) δ' δ
      (fun i => hg3 i) hδ'
    simp only [neg_zero, Real.exp_zero, mul_one]
    have : sbar n z (fun x => ∑ i, g i x) x - S x =
        fun j k => ∑ i, (sbar n z (g i) x - locS n z (χ i) G S x) j k := by
      funext j k
      simp only [Pi.sub_apply]
      rw [hsb x j k, sS x j k, Finset.sum_sub_distrib]
    rw [this]
    exact loc_ofReal_le _ (fun i => two_form_norm_sq_nonneg _ _) _ (two_form_sq_finset_sum_le _)

end

end ReciprocityTheory.L2DbarEstimates.F
end

-- bundled from ReciprocityTheory.L2DbarEstimates.Localization.MultAdj
section
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem multAdj (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : MultAdjStatement n M := by
  intro z hz ph₁ ph₂ η f w h1s h2s hηs hf hw hW g hg
  beta_reduce
  haveI : IsFiniteMeasureOnCompacts (vol n z) := ReciprocityTheory.L2DbarEstimates.vol_isFiniteMeasureOnCompacts n z hz
  have he : ReciprocityTheory.L2DbarEstimates.Smooth n z (fun y => (η y : ℂ)) := hηs
  have hgs : ReciprocityTheory.L2DbarEstimates.Smooth n z g := hg.1
  have hψs : ReciprocityTheory.L2DbarEstimates.Smooth n z (fun y => (η y : ℂ) * g y) :=
    ReciprocityTheory.L2DbarEstimates.Smooth.mul n z _ _ he hgs
  have hψ : IsTest n z (fun y => (η y : ℂ) * g y) := ⟨hψs, hg.2.mul_left⟩
  have h1 := hW _ hψ
  beta_reduce at h1
  have hc1 : Continuous ph₁ := multA_contR z hz ph₁ h1s
  have hc2 : Continuous ph₂ := multA_contR z hz ph₂ h2s
  have hcη : Continuous η := multA_contR z hz η hηs
  have hcg : Continuous g := ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz g hgs
  have hgc : HasCompactSupport (fun x => conj (g x)) := hg.2.comp_left (map_zero _)
  have hin : ∀ (h : M → ℂ) (x : M) (v : V n),
      ⟪dbarF n z h x, v⟫_ℂ = ∑ j, conj (db n z j h x) * v j := by
    intro h x v
    simp [dbarF, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hdbψ : ∀ j x, db n z j (fun y => (η y : ℂ) * g y) x =
      db n z j (fun y => (η y : ℂ)) x * g x + (η x : ℂ) * db n z j g x := fun j x =>
    ReciprocityTheory.L2DbarEstimates.db_mul n z _ _ (ReciprocityTheory.L2DbarEstimates.Smooth.ck n z 1 _ he)
      (ReciprocityTheory.L2DbarEstimates.Smooth.ck n z 1 _ hgs) j x
  have hconj : ∀ j x, conj (db n z j (fun y => (η y : ℂ)) x) = d n z j (fun y => (η y : ℂ)) x :=
    fun j x => by rw [ReciprocityTheory.L2DbarEstimates.db_ofReal, Complex.conj_conj]
  have hcomp : ∀ (v : V n) (j : Fin n), ‖v j‖ ^ 2 ≤ ‖v‖ ^ 2 := fun v j => by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    exact Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  have hE1 : Continuous (fun x => (Real.exp (-ph₁ x) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp hc1.neg)
  have hE2 : Continuous (fun x => (Real.exp (-ph₂ x) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp hc2.neg)
  have hfj : ∀ j, AEStronglyMeasurable (fun x => f x j) (vol n z) := fun j =>
    (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp_aestronglyMeasurable hf.1
  have hfb : ∀ j, ∫⁻ x, ENNReal.ofReal (‖f x j‖ ^ 2 * Real.exp (-ph₂ x)) ∂vol n z < ⊤ :=
    fun j => lt_of_le_of_lt (lintegral_mono fun x => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (hcomp (f x) j) (Real.exp_pos _).le)) hf.2
  have hfE : ∀ j K, IsCompact K →
      IntegrableOn (fun x => f x j * (Real.exp (-ph₂ x) : ℂ)) K (vol n z) := fun j K hK =>
    (multA_intOn_w _ _ ph₂ hc2 (hfj j) (hfb j) K hK).mul_continuousOn hE2.continuousOn hK
  have hwE : ∀ K, IsCompact K →
      IntegrableOn (fun x => w x * (Real.exp (-ph₁ x) : ℂ)) K (vol n z) := fun K hK =>
    (multA_intOn_w _ w ph₁ hc1 hw.1 hw.2 K hK).mul_continuousOn hE1.continuousOn hK
  have hP : Integrable (fun x => ∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) *
      conj (db n z j (fun y => (η y : ℂ) * g y) x)) (vol n z) := by
    refine MeasureTheory.integrable_finsetSum _ (fun j _ => ?_)
    exact multA_int_mul _ _ _ (hfE j)
      (Complex.continuous_conj.comp (ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _
        (ReciprocityTheory.L2DbarEstimates.Smooth.db n z j _ hψs)))
      ((hψ.2.mono' ((subset_tsupport _).trans
        (ReciprocityTheory.L2DbarEstimates.tsupport_db_subset n z j _))).comp_left (map_zero _))
  have hR : Integrable (fun x => ∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) *
      (d n z j (fun y => (η y : ℂ)) x * conj (g x))) (vol n z) := by
    refine MeasureTheory.integrable_finsetSum _ (fun j _ => ?_)
    exact multA_int_mul _ _ _ (hfE j)
      ((ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ (ReciprocityTheory.L2DbarEstimates.Smooth.d n z j _ he)).mul
        (Complex.continuous_conj.comp hcg)) hgc.mul_left
  have hQ : Integrable (fun x => w x * (Real.exp (-ph₁ x) : ℂ) *
      ((η x : ℂ) * conj (g x))) (vol n z) :=
    multA_int_mul _ _ _ hwE ((Complex.continuous_ofReal.comp hcη).mul
      (Complex.continuous_conj.comp hcg)) hgc.mul_left
  have hE : ∀ x, (Real.exp (ph₁ x - ph₂ x) : ℂ) * (Real.exp (-ph₁ x) : ℂ) =
      (Real.exp (-ph₂ x) : ℂ) := fun x => by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have eA : ∀ x, ⟪dbarF n z g x, (η x : ℂ) • f x⟫_ℂ * (Real.exp (-ph₂ x) : ℂ) =
      (∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) * conj (db n z j (fun y => (η y : ℂ) * g y) x)) -
      ∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) * (d n z j (fun y => (η y : ℂ)) x * conj (g x)) := by
    intro x
    rw [hin, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hdbψ, map_add (f := _), map_mul, map_mul, hconj, Complex.conj_ofReal]
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have eB : ∀ x, conj (g x) * ((η x : ℂ) * w x - (Real.exp (ph₁ x - ph₂ x) : ℂ) *
      ∑ j, d n z j (fun y => (η y : ℂ)) x * f x j) * (Real.exp (-ph₁ x) : ℂ) =
      w x * (Real.exp (-ph₁ x) : ℂ) * ((η x : ℂ) * conj (g x)) -
      ∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) * (d n z j (fun y => (η y : ℂ)) x * conj (g x)) := by
    intro x
    rw [← hE x, mul_sub, sub_mul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun j _ => by ring)
  have eP : ∀ x, ⟪dbarF n z (fun y => (η y : ℂ) * g y) x, f x⟫_ℂ * (Real.exp (-ph₂ x) : ℂ) =
      ∑ j, f x j * (Real.exp (-ph₂ x) : ℂ) * conj (db n z j (fun y => (η y : ℂ) * g y) x) := by
    intro x
    rw [hin, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have eQ : ∀ x, conj ((η x : ℂ) * g x) * w x * (Real.exp (-ph₁ x) : ℂ) =
      w x * (Real.exp (-ph₁ x) : ℂ) * ((η x : ℂ) * conj (g x)) := by
    intro x
    rw [map_mul, Complex.conj_ofReal]
    ring
  rw [funext eP, funext eQ] at h1
  rw [funext eA, funext eB, integral_sub hP hR, integral_sub hQ hR, h1]

theorem multS (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : MultSStatement n M := by
  intro z hz η f σ hηs hf hσ hW φ hφ j k
  beta_reduce
  haveI : IsFiniteMeasureOnCompacts (vol n z) := ReciprocityTheory.L2DbarEstimates.vol_isFiniteMeasureOnCompacts n z hz
  have he : ReciprocityTheory.L2DbarEstimates.Smooth n z (fun y => (η y : ℂ)) := hηs
  have hφs : ReciprocityTheory.L2DbarEstimates.Smooth n z φ := hφ.1
  have hψs : ReciprocityTheory.L2DbarEstimates.Smooth n z (fun y => (η y : ℂ) * φ y) :=
    ReciprocityTheory.L2DbarEstimates.Smooth.mul n z _ _ he hφs
  have hψ : IsTest n z (fun y => (η y : ℂ) * φ y) := ⟨hψs, hφ.2.mul_left⟩
  have h1 := hW _ hψ j k
  beta_reduce at h1
  have hcφ : Continuous φ := ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz φ hφs
  have hdbψ : ∀ i x, db n z i (fun y => (η y : ℂ) * φ y) x =
      db n z i (fun y => (η y : ℂ)) x * φ x + (η x : ℂ) * db n z i φ x := fun i x =>
    ReciprocityTheory.L2DbarEstimates.db_mul n z _ _ (ReciprocityTheory.L2DbarEstimates.Smooth.ck n z 1 _ he)
      (ReciprocityTheory.L2DbarEstimates.Smooth.ck n z 1 _ hφs) i x
  have hint : ∀ (a : Fin n) (c : M → ℂ), Continuous c → HasCompactSupport c →
      Integrable (fun x => f x a * c x) (vol n z) := fun a c hc hcs =>
    multA_int_mul _ _ c (fun K hK => integrableOn_compact_of_locL2 _ _ (locL2_form_component _ f hf a) K hK) hc hcs
  have hcψ : ∀ i, Continuous (db n z i (fun y => (η y : ℂ) * φ y)) := fun i =>
    ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ (ReciprocityTheory.L2DbarEstimates.Smooth.db n z i _ hψs)
  have hsψ : ∀ i, HasCompactSupport (db n z i (fun y => (η y : ℂ) * φ y)) := fun i =>
    hψ.2.mono' ((subset_tsupport _).trans (ReciprocityTheory.L2DbarEstimates.tsupport_db_subset n z i _))
  have hcη : ∀ i, Continuous (fun x => db n z i (fun y => (η y : ℂ)) x * φ x) := fun i =>
    (ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ (ReciprocityTheory.L2DbarEstimates.Smooth.db n z i _ he)).mul hcφ
  have hH : Integrable (fun x => f x k * db n z j (fun y => (η y : ℂ) * φ y) x -
      f x j * db n z k (fun y => (η y : ℂ) * φ y) x) (vol n z) :=
    (hint k _ (hcψ j) (hsψ j)).sub (hint j _ (hcψ k) (hsψ k))
  have hW' : Integrable (fun x => f x k * (db n z j (fun y => (η y : ℂ)) x * φ x) -
      f x j * (db n z k (fun y => (η y : ℂ)) x * φ x)) (vol n z) :=
    (hint k _ (hcη j) hφ.2.mul_left).sub (hint j _ (hcη k) hφ.2.mul_left)
  have hS : Integrable (fun x => σ x j k * ((η x : ℂ) * φ x)) (vol n z) :=
    multA_int_mul _ _ _ (fun K hK => integrableOn_compact_of_locL2 _ _ (locL2_two_form_component _ σ hσ j k) K hK)
      (ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ hψs) hψ.2
  have eL : ∀ x, ((η x : ℂ) • f x) k * db n z j φ x - ((η x : ℂ) • f x) j * db n z k φ x =
      (f x k * db n z j (fun y => (η y : ℂ) * φ y) x -
        f x j * db n z k (fun y => (η y : ℂ) * φ y) x) -
      (f x k * (db n z j (fun y => (η y : ℂ)) x * φ x) -
        f x j * (db n z k (fun y => (η y : ℂ)) x * φ x)) := by
    intro x
    rw [hdbψ, hdbψ]
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have eR : ∀ x, ((η x : ℂ) * σ x j k +
      wedge (fun i => db n z i (fun y => (η y : ℂ)) x) (fun i => f x i) j k) * φ x =
      σ x j k * ((η x : ℂ) * φ x) +
      (f x k * (db n z j (fun y => (η y : ℂ)) x * φ x) -
        f x j * (db n z k (fun y => (η y : ℂ)) x * φ x)) := by
    intro x
    simp only [wedge]
    ring
  rw [funext eL, funext eR, integral_sub hH hW', integral_add hS hW', h1]
  ring

theorem multDiv (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : MultDivStatement n M := by
  intro z hz η G D hηs hG hD hW φ hφ
  beta_reduce
  haveI : IsFiniteMeasureOnCompacts (vol n z) := ReciprocityTheory.L2DbarEstimates.vol_isFiniteMeasureOnCompacts n z hz
  have he : ReciprocityTheory.L2DbarEstimates.Smooth n z (fun y => (η y : ℂ)) := hηs
  have hφs : ReciprocityTheory.L2DbarEstimates.Smooth n z φ := hφ.1
  have hψs : ReciprocityTheory.L2DbarEstimates.Smooth n z (fun y => (η y : ℂ) * φ y) :=
    ReciprocityTheory.L2DbarEstimates.Smooth.mul n z _ _ he hφs
  have hψ : IsTest n z (fun y => (η y : ℂ) * φ y) := ⟨hψs, hφ.2.mul_left⟩
  have h1 := hW _ hψ
  beta_reduce at h1
  have hcφ : Continuous φ := ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz φ hφs
  have hdψ : ∀ j x, d n z j (fun y => (η y : ℂ) * φ y) x =
      d n z j (fun y => (η y : ℂ)) x * φ x + (η x : ℂ) * d n z j φ x := fun j x =>
    ReciprocityTheory.L2DbarEstimates.d_mul n z _ _ (ReciprocityTheory.L2DbarEstimates.Smooth.ck n z 1 _ he)
      (ReciprocityTheory.L2DbarEstimates.Smooth.ck n z 1 _ hφs) j x
  have hGj : ∀ j K, IsCompact K → IntegrableOn (fun x => G x j) K (vol n z) := fun j K hK =>
    integrableOn_compact_of_locL2 _ _ (locL2_form_component _ G hG j) K hK
  have hI1 : Integrable (fun x => ∑ j, G x j * d n z j (fun y => (η y : ℂ) * φ y) x) (vol n z) := by
    refine MeasureTheory.integrable_finsetSum _ (fun j _ => ?_)
    exact multA_int_mul _ _ _ (hGj j)
      (ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ (ReciprocityTheory.L2DbarEstimates.Smooth.d n z j _ hψs))
      (hψ.2.mono' ((subset_tsupport _).trans (ReciprocityTheory.L2DbarEstimates.tsupport_d_subset n z j _)))
  have hI2 : Integrable (fun x => ∑ j, G x j * (d n z j (fun y => (η y : ℂ)) x * φ x))
      (vol n z) := by
    refine MeasureTheory.integrable_finsetSum _ (fun j _ => ?_)
    exact multA_int_mul _ _ _ (hGj j)
      ((ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ (ReciprocityTheory.L2DbarEstimates.Smooth.d n z j _ he)).mul hcφ)
      hφ.2.mul_left
  have hI3 : Integrable (fun x => D x * ((η x : ℂ) * φ x)) (vol n z) :=
    multA_int_mul _ _ _ (fun K hK => integrableOn_compact_of_locL2 _ _ hD K hK)
      (ReciprocityTheory.L2DbarEstimates.Smooth.continuous n z hz _ hψs) hψ.2
  have hL : ∀ x, ∑ j, ((η x : ℂ) • G x) j * d n z j φ x =
      (∑ j, G x j * d n z j (fun y => (η y : ℂ) * φ y) x) -
      ∑ j, G x j * (d n z j (fun y => (η y : ℂ)) x * φ x) := by
    intro x
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hdψ]
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have hR : ∀ x, ((η x : ℂ) * D x + ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j) * φ x =
      D x * ((η x : ℂ) * φ x) + ∑ j, G x j * (d n z j (fun y => (η y : ℂ)) x * φ x) := by
    intro x
    rw [add_mul, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [funext hL, funext hR, integral_sub hI1 hI2, integral_add hI3 hI2, h1]
  ring

end

end ReciprocityTheory.L2DbarEstimates.F
end

