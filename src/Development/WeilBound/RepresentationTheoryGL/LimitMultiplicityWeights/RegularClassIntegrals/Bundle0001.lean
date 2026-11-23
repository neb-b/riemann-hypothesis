module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph
public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PBoundT
section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PBoundT

lemma entry {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ)
    (h : (diagonal l)ᴴ * J * diagonal l = J) (i j : Fin n) (hJ : J i j ≠ 0) :
    star (l i) * l j = 1 := by
  have e := congrFun (congrFun h i) j
  rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul] at e
  have e2 : (star (l i) * l j - 1) * J i j = 0 := by
    simp only [Pi.star_apply] at e
    linear_combination e
  exact sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right hJ)

lemma norm_entry {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ)
    (h : (diagonal l)ᴴ * J * diagonal l = J) (i j : Fin n) (hJ : J i j ≠ 0) :
    ‖l i‖ * ‖l j‖ = 1 := by
  have e := congrArg (fun x : ℂ => ‖x‖) (entry J l h i j hJ)
  simpa [norm_mul, norm_star] using e

end MainStatements.WeightKernel.PBoundT

namespace MainStatements.WeightKernel

open PBoundT in
theorem boundT : BoundT := by
  intro n J l hdet hinj hl a b ha
  refine ⟨max b (max (1 / a) 1), ?_⟩
  intro τ hτ hbd j
  have col : ∃ i, J i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    have : J.det = 0 := Matrix.det_eq_zero_of_column_eq_zero j hc
    rw [this] at hdet
    exact not_isUnit_zero hdet
  obtain ⟨i, hij⟩ := col
  have hl2 := norm_entry J l hl i j hij
  have hτ2 := norm_entry J τ hτ i j hij
  rcases lt_trichotomy ‖l j‖ 1 with hlt | heq | hgt
  · have hli : 1 < ‖l i‖ := by
      by_contra hc
      push_neg at hc
      have h0 : 0 ≤ ‖l j‖ := norm_nonneg _
      nlinarith
    have ha' := (hbd i hli).1
    have hτj : ‖τ j‖ ≤ 1 / a := by
      rw [le_div_iff₀ ha]
      have h0 : 0 ≤ ‖τ j‖ := norm_nonneg _
      nlinarith
    exact le_trans hτj (le_trans (le_max_left _ _) (le_max_right _ _))
  · have hli : ‖l i‖ = 1 := by
      rw [heq, mul_one] at hl2
      exact hl2
    have ent := entry J l hl i j hij
    have hsq : l i * star (l i) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hli]
      simp
    have hij' : l i = l j := by
      have : l i * (star (l i) * l j) = l i := by rw [ent, mul_one]
      rw [← mul_assoc, hsq, one_mul] at this
      exact this.symm
    have hieq : i = j := hinj hij'
    subst hieq
    have h0 : 0 ≤ ‖τ i‖ := norm_nonneg _
    have h1 : ‖τ i‖ = 1 := by nlinarith
    rw [h1]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  · exact le_trans (hbd j hgt).2 (le_max_left _ _)

end MainStatements.WeightKernel

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PBumpOn
section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel

theorem bumpOn : BumpOn := by
  intro H _ _ _ _ _ _ _ _ n ι hemb C hC
  have hK : IsCompact (matCoord ι '' C) := hC.image hemb.continuous
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  let f : ContDiffBump (0 : Fin n → Fin n → ℂ) :=
    ⟨max r 1, max r 1 + 1, lt_of_lt_of_le one_pos (le_max_right _ _), by linarith⟩
  refine ⟨fun g => ((f (matCoord ι g) : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
  · refine HasCompactSupport.intro (hemb.isCompact_preimage (isCompact_closedBall (0 : Fin n → Fin n → ℂ) (max r 1 + 1))) ?_
    intro g hg
    simp only [Set.mem_preimage, Metric.mem_closedBall, not_le] at hg
    have : f (matCoord ι g) = 0 := f.zero_of_le_dist hg.le
    simp [this]
  · refine ⟨fun x => ((f x : ℝ) : ℂ), ?_, fun g => rfl⟩
    exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · intro y hy
    have hm : matCoord ι y ∈ Metric.closedBall (0 : Fin n → Fin n → ℂ) (max r 1) :=
      Metric.closedBall_subset_closedBall (le_max_left _ _) (hr ⟨y, hy, rfl⟩)
    have : f (matCoord ι y) = 1 := f.one_of_mem_closedBall hm
    simp [this]

end MainStatements.WeightKernel

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PClosedGraph
section
open MeasureTheory Set Filter Topology

noncomputable section

namespace MainStatements.WeightKernel.PClosedGraph

variable {Ω I : Type} [MeasurableSpace Ω] {m : Measure Ω} {u : I → Ω → ℂ}

lemma summable_norm_lp (a : lp (fun _ : I => ℂ) 1) : Summable (fun i => ‖a i‖) := by
  have h := (memℓp_gen_iff (p := (1 : ENNReal)) (by norm_num)).1 (lp.memℓp a)
  simpa using h

lemma norm_lp_eq (a : lp (fun _ : I => ℂ) 1) : ‖a‖ = ∑' i, ‖a i‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp

lemma summable_mul {x : Ω} {M : ℝ} (hM : ∀ i, ‖u i x‖ ≤ M) (a : I → ℂ) (ha : Summable fun i => ‖a i‖) :
    Summable (fun i => a i * u i x) := by
  refine Summable.of_norm_bounded (ha.mul_right M) fun i => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM i) (norm_nonneg _)

lemma norm_tsum_mul_le {x : Ω} {M : ℝ} (hM : ∀ i, ‖u i x‖ ≤ M) (a : lp (fun _ : I => ℂ) 1) :
    ‖∑' i, a i * u i x‖ ≤ ‖a‖ * M := by
  have ha := summable_norm_lp a
  have hs := summable_mul hM a ha
  calc ‖∑' i, a i * u i x‖ ≤ ∑' i, ‖a i * u i x‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' i, ‖a i‖ * M := by
        refine Summable.tsum_le_tsum (fun i => ?_) hs.norm (ha.mul_right M)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hM i) (norm_nonneg _)
    _ = ‖a‖ * M := by rw [tsum_mul_right, norm_lp_eq]

lemma tsum_single [DecidableEq I] (i : I) (x : Ω) : ∑' j, (lp.single 1 i (1 : ℂ) : lp (fun _ : I => ℂ) 1) j * u j x = u i x := by
  rw [tsum_eq_single i]
  · simp [lp.single_apply]
  · intro j hj
    simp [lp.single_apply, Pi.single_apply, hj]

end MainStatements.WeightKernel.PClosedGraph

open MainStatements.WeightKernel.PClosedGraph in
theorem MainStatements.WeightKernel.closedGraph : MainStatements.WeightKernel.ClosedGraph := by
  intro Ω I _ m u hbd hint
  choose M hM using hbd
  let Tf : lp (fun _ : I => ℂ) 1 → Ω → ℂ := fun a x => ∑' i, a i * u i x
  have hTi : ∀ a : lp (fun _ : I => ℂ) 1, Integrable (Tf a) m := fun a => hint a (summable_norm_lp a)
  have hadd : ∀ a b : lp (fun _ : I => ℂ) 1, Tf (a + b) = Tf a + Tf b := by
    intro a b
    funext x
    simp only [Tf, Pi.add_apply, lp.coeFn_add, add_mul]
    exact Summable.tsum_add (summable_mul (hM x) a (summable_norm_lp a))
      (summable_mul (hM x) b (summable_norm_lp b))
  have hsmul : ∀ (c : ℂ) (a : lp (fun _ : I => ℂ) 1), Tf (c • a) = fun x => c • Tf a x := by
    intro c a
    funext x
    simp only [Tf, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact tsum_mul_left
  let T : lp (fun _ : I => ℂ) 1 →ₗ[ℂ] Lp ℂ 1 m :=
    { toFun := fun a => Integrable.toL1 (Tf a) (hTi a)
      map_add' := by
        intro a b
        rw [← Integrable.toL1_add, Integrable.toL1_eq_toL1_iff]
        exact Filter.Eventually.of_forall (congrFun (hadd a b))
      map_smul' := by
        intro c a
        simp only [RingHom.id_apply]
        rw [← Integrable.toL1_smul, Integrable.toL1_eq_toL1_iff]
        exact Filter.Eventually.of_forall (congrFun (hsmul c a)) }
  have hTapp : ∀ a, T a = Integrable.toL1 (Tf a) (hTi a) := fun a => rfl
  have hcont : Continuous T := by
    refine T.continuous_of_seq_closed_graph fun s a y hs hy => ?_
    have hmeas := tendstoInMeasure_of_tendsto_Lp hy
    obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
    apply Lp.ext
    filter_upwards [hae, (hTi a).coeFn_toL1, ae_all_iff.2 (fun n => (hTi (s n)).coeFn_toL1)]
      with x hx1 hx2 hx3
    rw [hTapp a, hx2]
    have hpt : Tendsto (fun n => Tf (s n) x) atTop (𝓝 (Tf a x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hlim : Tendsto (fun n => ‖s n - a‖ * M x) atTop (𝓝 0) := by
        have h0 : Tendsto (fun n => ‖s n - a‖) atTop (𝓝 0) := by
          rw [← tendsto_iff_norm_sub_tendsto_zero]
          exact hs
        simpa using h0.mul_const (M x)
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
      have e : Tf (s n) x - Tf a x = Tf (s n - a) x := by
        have := congrFun (hadd (s n - a) a) x
        simp only [sub_add_cancel, Pi.add_apply] at this
        rw [this]
        ring
      rw [e]
      exact norm_tsum_mul_le (hM x) (s n - a)
    have hsub := hpt.comp hns.tendsto_atTop
    refine tendsto_nhds_unique hx1 ?_
    refine hsub.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [hTapp, hx3]
  let T' : lp (fun _ : I => ℂ) 1 →L[ℂ] Lp ℂ 1 m := ⟨T, hcont⟩
  refine ⟨‖T'‖, fun i => ?_⟩
  classical
  let e : lp (fun _ : I => ℂ) 1 := lp.single 1 i (1 : ℂ)
  have hTe : Tf e = u i := funext fun x => tsum_single i x
  have hint_i : Integrable (u i) m := hTe ▸ hTi e
  refine ⟨hint_i, ?_⟩
  have hn : ‖T e‖ = ∫ x, ‖u i x‖ ∂m := by
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [(hTi e).coeFn_toL1] with x hx
    rw [hTapp, hx, hTe]
  have hle : ‖T' e‖ ≤ ‖T'‖ * ‖e‖ := T'.le_opNorm e
  have he : ‖e‖ = 1 := by
    rw [lp.norm_single (by norm_num)]
    simp
  rw [← hn]
  calc ‖T e‖ = ‖T' e‖ := rfl
    _ ≤ ‖T'‖ * ‖e‖ := hle
    _ = ‖T'‖ := by rw [he, mul_one]
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PFdRight
section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PFdRight

end MainStatements.WeightKernel.PFdRight

theorem MainStatements.WeightKernel.fdRight : MainStatements.WeightKernel.FDRight := by
  intro G _ _ _ _ _ _ Γ _ μ _ _ 𝓕 h𝓕 F hF g
  have h2 : IsFundamentalDomain Γ ((fun x : G => x * g⁻¹) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  have key : ∫ x in 𝓕, F (x * g) ∂μ = ∫ x in (fun x : G => x * g⁻¹) ⁻¹' 𝓕, F x ∂μ := by
    rw [← Set.image_mul_right,
      (measurePreserving_mul_right μ g).setIntegral_image_emb (measurableEmbedding_mulRight g) F 𝓕]
  rw [key]
  exact h2.setIntegral_eq h𝓕 (fun γ x => by rw [Subgroup.smul_def, smul_eq_mul]; exact hF γ γ.2 x)
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PIdentOne
section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PIdentOne

def gR {H : Type} [Group H] [TopologicalSpace H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ) (s : H)
    (B : Mx n × Mx n → ℝ) (φ : H → ℝ) (z h : H) : ℝ :=
  B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) * φ (h⁻¹ * s * h)

def G {H : Type} [Group H] [TopologicalSpace H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ) (s : H)
    (B : Mx n × Mx n → ℝ) (φ : H → ℝ) (z h : H) : ℂ :=
  (gR ι s B φ z h : ℂ)

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] {n : ℕ} {ι : H →* Matrix (Fin n) (Fin n) ℂ}
    {s : H} {B : Mx n × Mx n → ℝ} {φ : H → ℝ}

theorem gR_cont (hι : Continuous (matCoord ι)) (hB : IsWeight ι s B) (hφc : Continuous φ) (z : H) :
    Continuous (gR ι s B φ z) := by
  unfold gR
  have hBc : Continuous B := hB.smooth.continuous
  exact (hBc.comp (continuous_const.prodMk (hι.comp (continuous_const.mul continuous_id)))).mul
    (hφc.comp ((continuous_inv.mul continuous_const).mul continuous_id))

theorem gR_supp (hB : IsWeight ι s B) (hφ : HasCompactSupport φ) (z : H) :
    HasCompactSupport (gR ι s B φ z) := by
  obtain ⟨K, hK, hKp⟩ := hB.proper {z⁻¹ * s * z} (tsupport φ) isCompact_singleton hφ
  refine HasCompactSupport.intro (hK.image (continuous_const_mul z)) fun h hh => ?_
  by_contra hne
  apply hh
  refine ⟨z⁻¹ * h, hKp z (z⁻¹ * h) (Set.mem_singleton _) ?_ ?_, mul_inv_cancel_left z h⟩
  · rw [mul_inv_cancel_left z h]
    exact subset_tsupport _ (fun h0 => hne (by simp [gR, h0]))
  · exact fun h0 => hne (by simp [gR, h0])

theorem fiber (hB : IsWeight ι s B) (dt : Measure (cent s)) [dt.IsMulRightInvariant] (z h : H) :
    ∫ t : cent s, G ι s B φ z (t * h) ∂dt = ∫ t : cent s, G ι s B φ 1 (t * h) ∂dt := by
  obtain ⟨t₀, ht₀, e⟩ := hB.shift z h 1 h
  have key : ∀ v : H, v * s = s * v → (v * h)⁻¹ * s * (v * h) = h⁻¹ * s * h := fun v hv => by
    calc (v * h)⁻¹ * s * (v * h) = h⁻¹ * (v⁻¹ * (s * v)) * h := by group
      _ = h⁻¹ * (v⁻¹ * (v * s)) * h := by rw [hv]
      _ = h⁻¹ * s * h := by group
  have hc : ∀ u : cent s, ((u : H) * h)⁻¹ * s * (u * h) = h⁻¹ * s * h := fun u => key u (mem_cent.1 u.2)
  calc ∫ t : cent s, G ι s B φ z (t * h) ∂dt
        = ∫ t : cent s, G ι s B φ 1 (((t * ⟨t₀, ht₀⟩ : cent s) : H) * h) ∂dt := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          simp only [G, gR]
          rw [hc t, hc (t * ⟨t₀, ht₀⟩), ← mul_assoc z⁻¹, e t t.2]
          simp [mul_assoc]
    _ = _ := integral_mul_right_eq_self (fun t : cent s => G ι s B φ 1 ((t : H) * h)) ⟨t₀, ht₀⟩

theorem integral_eq (hι : Continuous (matCoord ι)) (hB : IsWeight ι s B) (μ : Measure H) [μ.IsHaarMeasure]
    (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (hφc : Continuous φ)
    (hφ : HasCompactSupport φ) (z : H) :
    ∫ h, G ι s B φ z h ∂μ = ∫ h, G ι s B φ 1 h ∂μ := by
  have hi : ∀ w, Integrable (G ι s B φ w) μ := fun w =>
    (Complex.continuous_ofReal.comp (gR_cont hι hB hφc w)).integrable_of_hasCompactSupport
      ((gR_supp hB hφ w).comp_left Complex.ofReal_zero)
  have w1 := (weil_integral (dt := dt) (isClosed_cent s) (hi z)).2.2
  have w2 := (weil_integral (dt := dt) (isClosed_cent s) (hi 1)).2.2
  rw [← w1, ← w2]
  exact congrArg (quotInt _ dt μ) (funext fun x => fiber hB dt z x)

theorem orig_eq (μ : Measure H) [μ.IsHaarMeasure] (z : H) :
    ∫ k, (B (matCoord ι (z⁻¹ * s * z), matCoord ι k) : ℂ) * (φ (k⁻¹ * (z⁻¹ * s * z) * k) : ℂ) ∂μ =
      ∫ h, G ι s B φ z h ∂μ := by
  refine (integral_mul_left_eq_self (μ := μ) (fun k => (B (matCoord ι (z⁻¹ * s * z), matCoord ι k) : ℂ) *
    (φ (k⁻¹ * (z⁻¹ * s * z) * k) : ℂ)) z⁻¹).symm.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [G, gR, Complex.ofReal_mul]
  rw [show (z⁻¹ * h)⁻¹ * (z⁻¹ * s * z) * (z⁻¹ * h) = h⁻¹ * s * h by group]

theorem ne_zero (hι : Continuous (matCoord ι)) (hB : IsWeight ι s B) (μ : Measure H) [μ.IsHaarMeasure]
    (hφc : Continuous φ) (hφ : HasCompactSupport φ) (hφ0 : ∀ y, 0 ≤ φ y) (hφs : 0 < φ s) :
    ∫ h, G ι s B φ 1 h ∂μ ≠ 0 := by
  have hpos : 0 < ∫ h, gR ι s B φ 1 h ∂μ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (gR_cont hι hB hφc 1)
      (gR_supp hB hφ 1) (fun h => mul_nonneg (hB.nonneg _) (hφ0 _)) ?_
    simp only [gR, inv_one, one_mul, mul_one]
    exact (mul_pos hB.pos hφs).ne'
  simp only [G]
  rw [integral_complex_ofReal]
  exact_mod_cast hpos.ne'

end MainStatements.WeightKernel.PIdentOne

theorem MainStatements.WeightKernel.identOne : IdentOne := by
  intro H _ _ _ _ _ _ _ _ n ι hι s B hB μ _ dt _ _ φ hφc hφ hφ0 hφs
  exact ⟨_, PIdentOne.ne_zero hι hB μ hφc hφ hφ0 hφs, fun z =>
    (PIdentOne.orig_eq μ z).trans (PIdentOne.integral_eq hι hB μ dt hφc hφ z)⟩

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.PIdentTwo
section
open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel

theorem identTwo : IdentTwo := by
  intro H _ _ _ _ _ _ _ _ n ι hc s B hB μ _ _ dt _ _ φ hφc hφs hO h
  have : μ.IsInvInvariant := GlobalTheory.SqIntRep.isInvInvariant_of_unimodular μ
  set f : H → ℂ := fun z => φ (z⁻¹ * s * z) * (B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) : ℂ) with hfdef
  set F : H → ℂ := fun k => φ (k * (h⁻¹ * s * h) * k⁻¹) *
    (B (matCoord ι (k * (h⁻¹ * s * h) * k⁻¹), matCoord ι k) : ℂ) with hFdef
  have hsub : ∫ k, F k ∂μ = ∫ z, f z ∂μ := by
    have h1 := integral_mul_right_eq_self (μ := μ) (fun k => F k) h
    have h2 := integral_inv_eq_self (fun k => F (k * h)) μ
    rw [← h1, ← h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have e : z⁻¹ * h * (h⁻¹ * s * h) * (z⁻¹ * h)⁻¹ = z⁻¹ * s * z := by group
    simp only [hFdef, hfdef, e]
  have hBc : Continuous B := hB.smooth.continuous
  have hfc : Continuous f := by
    have h1 : Continuous fun z : H => z⁻¹ * s * z := by fun_prop
    have h2 : Continuous fun z : H => z⁻¹ * h := by fun_prop
    exact (hφc.comp h1).mul (Complex.continuous_ofReal.comp (hBc.comp ((hc.comp h1).prodMk (hc.comp h2))))
  obtain ⟨K, hK, hKp⟩ := hB.proper (tsupport φ) {h⁻¹ * s * h} hφs isCompact_singleton
  have hfs : HasCompactSupport f := by
    refine HasCompactSupport.intro (hK.image (f := fun k => h * k⁻¹) (by fun_prop)) fun z hz => ?_
    by_contra hne
    apply hz
    have hne' : φ (z⁻¹ * s * z) * (B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) : ℂ) ≠ 0 := hne
    have m1 : z⁻¹ * s * z ∈ tsupport φ := subset_tsupport _ (left_ne_zero_of_mul hne')
    have m2 : B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) ≠ 0 := by
      intro h0; apply hne'; rw [h0]; simp
    have m3 : (z * (z⁻¹ * h))⁻¹ * s * (z * (z⁻¹ * h)) ∈ ({h⁻¹ * s * h} : Set H) := by
      rw [mul_inv_cancel_left]; exact Set.mem_singleton _
    exact ⟨z⁻¹ * h, hKp z (z⁻¹ * h) m1 m3 m2, by group⟩
  have hfi : Integrable f μ := hfc.integrable_of_hasCompactSupport hfs
  have hW := (weil_integral (T := cent s) (dt := dt) (dh := μ) (isClosed_cent s) hfi).2.2
  set κ : ℂ := ∫ t : cent s, (B (matCoord ι s, matCoord ι ((t : H)⁻¹)) : ℂ) ∂dt with hκ
  have hfib : ∀ x, ∫ t : cent s, f (t * x) ∂dt = φ (x⁻¹ * s * x) * κ := by
    intro x
    obtain ⟨t₀, ht₀, hsh⟩ := hB.shift x h 1 1
    have e1 : ∀ t : cent s, ((t : H) * x)⁻¹ * s * ((t : H) * x) = x⁻¹ * s * x := by
      intro t
      have hts := mem_cent.1 t.2
      have : (t : H)⁻¹ * s * t = s := by rw [mul_assoc, ← hts, inv_mul_cancel_left]
      calc ((t : H) * x)⁻¹ * s * ((t : H) * x) = x⁻¹ * ((t : H)⁻¹ * s * t) * x := by group
        _ = x⁻¹ * s * x := by rw [this]
    have e2 : ∀ t : cent s, f (t * x) = φ (x⁻¹ * s * x) *
        (B (matCoord ι s, matCoord ι ((((⟨t₀, ht₀⟩ : cent s)⁻¹ * t : cent s) : H)⁻¹)) : ℂ) := by
      intro t
      have hs' := hsh (t : H)⁻¹ (inv_mem t.2)
      simp only [inv_one, one_mul, mul_one] at hs'
      have hco : (t : H)⁻¹ * t₀ = ((((⟨t₀, ht₀⟩ : cent s)⁻¹ * t : cent s) : H))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv]
      simp only [hfdef, e1]
      rw [show ((t : H) * x)⁻¹ * h = x⁻¹ * (t : H)⁻¹ * h by group, hs', hco]
    simp_rw [e2]
    rw [integral_const_mul]
    congr 1
    exact integral_mul_left_eq_self (fun t : cent s => (B (matCoord ι s, matCoord ι ((t : H))⁻¹) : ℂ)) _
  have hfun : (fun x => ∫ t : cent s, f (t * x) ∂dt) = fun x => conjFn s φ x * κ := funext fun x => hfib x
  show ∫ k, F k ∂μ = 0
  rw [hsub, ← hW, hfun]
  have h0 := hO.2
  unfold quotInt descend at h0 ⊢
  show ∫ q, conjFn s φ q.out * κ ∂quotMeas (cent s) dt μ = 0
  rw [integral_mul_const, h0, zero_mul]

end MainStatements.WeightKernel

end
end

