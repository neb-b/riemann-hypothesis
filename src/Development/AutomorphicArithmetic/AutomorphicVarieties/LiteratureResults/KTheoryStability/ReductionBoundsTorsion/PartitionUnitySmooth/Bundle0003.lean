module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GProper
section
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

private theorem qR_smul_VR {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N) (c : ℝ)
    (z : VR L N) : qR h (c • z) = c ^ 2 * qR h z := by
  show ∑ w, (star ((c • z) w) ⬝ᵥ mat h w *ᵥ (c • z) w).re =
    c ^ 2 * ∑ w, (star (z w) ⬝ᵥ mat h w *ᵥ z w).re
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : (c • z) w = (c : ℂ) • z w := by
    ext i; simp [Complex.real_smul]
  rw [e, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp [smul_eq_mul, Complex.conj_ofReal]
  ring

private theorem qR_pos_of_mem_Pos_of_VR_ne_zero {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hp : h ∈ Pos L N) (z : VR L N) (hz : z ≠ 0) : 0 < qR h z := by
  obtain ⟨w0, hw0⟩ : ∃ w, z w ≠ 0 := by
    by_contra hc; push_neg at hc; exact hz (funext hc)
  show 0 < ∑ w, (star (z w) ⬝ᵥ mat h w *ᵥ z w).re
  have hnn : ∀ w, 0 ≤ (star (z w) ⬝ᵥ mat h w *ᵥ z w).re := fun w => by
    have := (hp w).posSemidef.dotProduct_mulVec_nonneg (z w)
    exact (Complex.nonneg_iff.mp this).1
  have hpos : 0 < (star (z w0) ⬝ᵥ mat h w0 *ᵥ z w0).re := (hp w0).re_dotProduct_pos hw0
  exact Finset.sum_pos' (fun w _ => hnn w) ⟨w0, Finset.mem_univ _, hpos⟩

private theorem continuous_qR_comp {L : Type} [Field L] [NumberField L] {N : ℕ} {X : Type*}
    [TopologicalSpace X] {f : X → HS L N} {g : X → VR L N} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => qR (f x) (g x) := by
  show Continuous fun x => ∑ w, (star (g x w) ⬝ᵥ mat (f x) w *ᵥ g x w).re
  refine continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_
  have h1 : Continuous fun x => g x w := (continuous_apply w).comp hg
  have h2 : Continuous fun x => mat (f x) w :=
    (continuous_apply w).comp (continuous_subtype_val.comp hf)
  exact h1.star.dotProduct (h2.matrix_mulVec h1)

private theorem qR_zero_right {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N) :
    qR h 0 = 0 := by
  simpa using qR_smul_VR h 0 0

private theorem exists_pos_smul_unit_sphere_eq_of_ne_zero {L : Type} [Field L] [NumberField L] {N : ℕ} (z : VR L N)
    (hz : z ≠ 0) : ∃ r : ℝ, 0 < r ∧ ∃ u ∈ Metric.sphere (0 : VR L N) 1, z = r • u := by
  refine ⟨‖z‖, norm_pos_iff.mpr hz, ‖z‖⁻¹ • z, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]

private theorem ne_zero_of_mem_unit_sphere_VR {L : Type} [Field L] [NumberField L] {N : ℕ}
    (u : VR L N) (hu : u ∈ Metric.sphere (0 : VR L N) 1) : u ≠ 0 := by
  rintro rfl
  simp at hu

private theorem exists_qR_le_mul_qR_on_compact_subset_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} (K : Set (HS L N))
    (hK : IsCompact K) (hKP : K ⊆ Pos L N) (h0 : HS L N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ K, ∀ z, qR h0 z ≤ C * qR h z := by
  have hS : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere 0 1
  have hc : ContinuousOn (fun p : HS L N × VR L N => qR h0 p.2 / qR p.1 p.2)
      (K ×ˢ Metric.sphere (0 : VR L N) 1) := by
    refine ContinuousOn.div ?_ (continuous_qR_comp continuous_fst continuous_snd).continuousOn ?_
    · exact (continuous_qR_comp continuous_const continuous_snd).continuousOn
    · rintro ⟨h, z⟩ ⟨hh, hz⟩
      exact (qR_pos_of_mem_Pos_of_VR_ne_zero h (hKP hh) z (ne_zero_of_mem_unit_sphere_VR z hz)).ne'
  obtain ⟨C, hC⟩ := (hK.prod hS).bddAbove_image hc
  refine ⟨max C 0, le_max_right _ _, fun h hh z => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp [qR_zero_right]
  obtain ⟨r, -, u, hu, rfl⟩ := exists_pos_smul_unit_sphere_eq_of_ne_zero z hz
  have hpu : 0 < qR h u := qR_pos_of_mem_Pos_of_VR_ne_zero h (hKP hh) u (ne_zero_of_mem_unit_sphere_VR u hu)
  have hb : qR h0 u / qR h u ≤ C := hC ⟨(h, u), ⟨hh, hu⟩, rfl⟩
  have h1 : qR h0 u ≤ max C 0 * qR h u := by
    rw [div_le_iff₀ hpu] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpu.le)
  rw [qR_smul_VR, qR_smul_VR]
  calc r ^ 2 * qR h0 u ≤ r ^ 2 * (max C 0 * qR h u) := mul_le_mul_of_nonneg_left h1 (sq_nonneg r)
    _ = max C 0 * (r ^ 2 * qR h u) := by ring

private theorem eventually_nhds_unit_sphere_of_mem_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hp : h ∈ Pos L N) :
    ∀ᶠ k in nhds h, ∀ u ∈ Metric.sphere (0 : VR L N) 1,
      |qR k u - qR h u| - 1 / 2 * qR h u < 0 := by
  have hS : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere 0 1
  have c1 : Continuous fun p : HS L N × VR L N => qR p.1 p.2 :=
    continuous_qR_comp continuous_fst continuous_snd
  have c2 : Continuous fun p : HS L N × VR L N => qR h p.2 :=
    continuous_qR_comp continuous_const continuous_snd
  refine hS.eventually_forall_of_forall_eventually fun u hu => ?_
  have hpu : 0 < qR h u := qR_pos_of_mem_Pos_of_VR_ne_zero h hp u (ne_zero_of_mem_unit_sphere_VR u hu)
  set f : HS L N × VR L N → ℝ := fun p => |qR p.1 p.2 - qR h p.2| - 1 / 2 * qR h p.2 with hf
  have hcont : Continuous f :=
    ((c1.sub c2).abs).sub (continuous_const.mul c2)
  have hv : f (h, u) < 0 := by
    show |qR h u - qR h u| - 1 / 2 * qR h u < 0
    rw [sub_self, abs_zero, zero_sub, neg_lt_zero]
    linarith
  have h2 : ∀ᶠ p in nhds (h, u), f p < 0 := hcont.continuousAt.eventually (Iio_mem_nhds hv)
  filter_upwards [h2] with p hp'
  exact hp'

private theorem eventually_nhds_abs_qR_sub_le_half_of_mem_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hp : h ∈ Pos L N) :
    ∀ᶠ k in nhds h, ∀ z : VR L N, |qR k z - qR h z| ≤ 1 / 2 * qR h z := by
  filter_upwards [eventually_nhds_unit_sphere_of_mem_Pos h hp] with k hk z
  rcases eq_or_ne z 0 with rfl | hz
  · rw [qR_zero_right, qR_zero_right]
    norm_num
  obtain ⟨r, -, u, hu, rfl⟩ := exists_pos_smul_unit_sphere_eq_of_ne_zero z hz
  rw [qR_smul_VR, qR_smul_VR, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg r)]
  have h1 : |qR k u - qR h u| ≤ 1 / 2 * qR h u := by linarith [hk u hu]
  calc r ^ 2 * |qR k u - qR h u| ≤ r ^ 2 * (1 / 2 * qR h u) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg r)
    _ = 1 / 2 * (r ^ 2 * qR h u) := by ring

theorem pf_GProper : GProper := by
  intro hB L _ _ N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨?_, ?_⟩
    · have hu : Pos L 0 = Set.univ := by
        ext h
        simp only [Set.mem_univ, iff_true]
        intro w
        refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => absurd (Subsingleton.elim x 0) hx
        exact h.2 w
      rw [hu]
      exact isOpen_univ
    · intro K _ _
      apply Set.Subsingleton.finite
      intro a _ b _
      exact Units.ext (Subsingleton.elim _ _)
  obtain ⟨hPos, hEq, -, hCl, -, -⟩ := hB L N hN
  refine ⟨?_, ?_⟩
  · refine isOpen_iff_mem_nhds.mpr fun h hh => ?_
    filter_upwards [eventually_nhds_abs_qR_sub_le_half_of_mem_Pos h hh] with k hk
    exact (hCl (1 / 2) (by norm_num) le_rfl h hh k hk).1
  intro K hK hKP
  rcases K.eq_empty_or_nonempty with rfl | ⟨h0, hh0⟩
  · simp
  obtain ⟨C, hC0, hC⟩ := exists_qR_le_mul_qR_on_compact_subset_Pos K hK hKP h0
  have hbd : ∀ i : Fin N, ∃ B : ℝ, ∀ h ∈ K, q h (Pi.single i 1 : UpperTheory.V.KT.Lat L N) ≤ B := by
    intro i
    have hc : Continuous fun h : HS L N => qR h (toR (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) :=
      continuous_qR_comp continuous_id continuous_const
    obtain ⟨B, hB'⟩ := hK.bddAbove_image hc.continuousOn
    exact ⟨B, fun h hh => hB' ⟨h, hh, rfl⟩⟩
  choose B hBd using hbd
  have hF : (⋃ i, {v : UpperTheory.V.KT.Lat L N | q h0 v ≤ C * B i}).Finite :=
    Set.finite_iUnion fun i => (hPos h0 (hKP hh0)).2.2.2.2 _
  have hmaps : ∀ γ ∈ {γ : Gm L N | ∃ h ∈ K, ac γ h ∈ K},
      (fun i : Fin N => γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) ∈
        Set.pi Set.univ (fun _ => ⋃ i, {v : UpperTheory.V.KT.Lat L N | q h0 v ≤ C * B i}) := by
    rintro γ ⟨h, hh, hγ⟩ i -
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    show q h0 (γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) ≤ C * B i
    calc q h0 (γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N))
        ≤ C * q h (γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) := hC h hh _
      _ = C * q (ac γ h) (Pi.single i 1 : UpperTheory.V.KT.Lat L N) := by rw [hEq]
      _ ≤ C * B i := mul_le_mul_of_nonneg_left (hBd i _ hγ) hC0
  have hinj : Set.InjOn (fun γ : Gm L N => fun i : Fin N => γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N))
      {γ : Gm L N | ∃ h ∈ K, ac γ h ∈ K} := by
    intro a _ b _ hab
    have hinv : (a⁻¹ : Gm L N) = b⁻¹ := by
      apply Units.ext
      ext j i
      have e := congrFun (congrFun hab i) j
      change ((↑(a⁻¹ : GL (Fin N) (𝓞 L)) : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ Pi.single i 1) j =
        ((↑(b⁻¹ : GL (Fin N) (𝓞 L)) : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ Pi.single i 1) j at e
      simpa [Matrix.mulVec_single_one] using e
    exact inv_injective hinv
  exact Set.Finite.of_finite_image ((Set.Finite.pi fun _ => hF).subset (Set.image_subset_iff.mpr hmaps)) hinj

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GRSmooth
section
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

private theorem sm_rho_nonneg (x : ℝ) : 0 ≤ rho x := Real.smoothTransition.nonneg _

private theorem toR_zero : toR (0 : UpperTheory.V.KT.Lat L N) = 0 := by
  unfold toR
  funext w a
  simp

private theorem q_zero_right (h : HS L N) : q h 0 = 0 := by
  unfold q qR
  rw [toR_zero]
  simp

private theorem rk_zero_right (h : HS L N) : rk h 0 = 0 := by
  ext w i j
  unfold rk mkHS
  simp [toR_zero, vecMulVec]

private theorem contDiff_hs_entry (w : InfinitePlace L) (i j : Fin N) :
    ContDiff ℝ ⊤ (fun h : HS L N => (h : InfinitePlace L → Fin N → Fin N → ℂ) w i j) := by
  have hc : ContDiff ℝ ⊤ (fun h : HS L N => (h : InfinitePlace L → Fin N → Fin N → ℂ)) :=
    (HSsub L N).subtypeL.contDiff
  exact contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 hc w) i) j

private theorem contDiff_qR_left (x : VR L N) : ContDiff ℝ ⊤ (fun h : HS L N => qR h x) := by
  unfold qR mat
  apply ContDiff.sum
  intro w _
  refine Complex.reCLM.contDiff.comp ?_
  simp only [dotProduct, mulVec, Matrix.of_apply]
  apply ContDiff.sum
  intro i _
  refine contDiff_const.mul ?_
  apply ContDiff.sum
  intro j _
  exact (contDiff_hs_entry w i j).mul contDiff_const

private theorem contDiff_rk_left (v : UpperTheory.V.KT.Lat L N) : ContDiff ℝ ⊤ (fun h : HS L N => rk h v) := by
  obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional (HSsub L N)
  have e : (fun h : HS L N => rk h v) =
      fun h => P ((rk h v : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ) := by
    funext h
    rw [hP]
  rw [e]
  refine P.contDiff.comp ?_
  have hm : ∀ w i, ContDiff ℝ ⊤
      (fun h : HS L N => (of ((h : InfinitePlace L → Fin N → Fin N → ℂ) w) *ᵥ toR v w) i) := by
    intro w i
    simp only [mulVec, dotProduct, Matrix.of_apply]
    apply ContDiff.sum
    intro j _
    exact (contDiff_hs_entry w i j).mul contDiff_const
  unfold rk mkHS mat
  refine contDiff_pi.2 fun w => contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [vecMulVec, Matrix.of_apply, Pi.star_apply]
  exact (hm w i).mul (Complex.conjCLE.contDiff.comp (hm w j))

private theorem smoothTransition_eq_zero_of_four_mul_le (y t : ℝ) (ht : 0 < t) (hy : 4 * t ≤ y) :
    Real.smoothTransition ((4 - y / t) / 3) = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have : 4 ≤ y / t := (le_div_iff₀ ht).2 (by linarith)
  linarith

private theorem contDiff_rho : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) rho := by
  unfold rho
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem pf_GRSmooth : GRSmooth := by
  classical
  unfold GRSmooth Basic RSmooth
  intro hB L _ _ N hN μ hμ
  obtain ⟨h1, -, ⟨c, C, hc, hcmp⟩, -⟩ := hμ
  obtain ⟨hP, -⟩ := hB L N hN
  unfold ret
  apply contDiffOn_of_locally_contDiffOn
  intro h0 hh0
  have hl0 : 0 < lam h0 := (hP h0 hh0).1
  have hd0 : 0 < lamD h0 := by
    unfold lamD
    exact (hP _ (hP h0 hh0).2.2.2.1).1
  have hμ0 : 0 < μ h0 := lt_of_lt_of_le (mul_pos hc hd0) (hcmp h0 hh0).1
  obtain ⟨n1, hn1⟩ := pow_unbounded_of_one_lt (8 / μ h0) (by norm_num : (1:ℝ) < 4)
  obtain ⟨S, hSf, hS⟩ := locfin L N h0 hh0 (4 * (4:ℝ) ^ n1)
  have hq : ∀ᶠ k in nhds h0, ∀ v ∈ S, v ≠ 0 → lam h0 / 2 < q k v := by
    refine (Filter.eventually_all_finite hSf).2 ?_
    intro v _
    by_cases hv : v = 0
    · exact Filter.Eventually.of_forall (fun _ hne => absurd hv hne)
    · have hcont : ContinuousAt (fun k : HS L N => q k v) h0 :=
        (contDiff_qR_left (toR v)).continuous.continuousAt
      have hlt : lam h0 / 2 < q h0 v := by
        have := (hP h0 hh0).2.1 v hv
        linarith
      filter_upwards [hcont.eventually (lt_mem_nhds hlt)] with k hk _ using hk
  have hμe : ∀ᶠ k in nhdsWithin h0 (Pos L N), μ h0 / 2 < μ k :=
    (h1.continuousOn.continuousWithinAt hh0).eventually (lt_mem_nhds (by linarith))
  have hall : ∀ᶠ k in nhdsWithin h0 (Pos L N), μ h0 / 2 < μ k ∧
      (∀ y ∉ S, 4 * (4:ℝ) ^ n1 < q k y) ∧ (∀ v ∈ S, v ≠ 0 → lam h0 / 2 < q k v) :=
    hμe.and ((hS.filter_mono nhdsWithin_le_nhds).and (hq.filter_mono nhdsWithin_le_nhds))
  obtain ⟨u, hu, h0u, hsub⟩ := mem_nhdsWithin.1 hall
  refine ⟨u, hu, h0u, ?_⟩
  set m : ℝ := min (lam h0 / 2) (4 * (4:ℝ) ^ n1) with hmEq
  have hm : 0 < m := lt_min (by linarith) (by positivity)
  obtain ⟨n0, hn0⟩ := pow_unbounded_of_one_lt (4 / m) (by norm_num : (1:ℝ) < 4)
  set S' : Finset (UpperTheory.V.KT.Lat L N) := insert 0 hSf.toFinset with hSEq
  have key : ∀ h ∈ Pos L N ∩ u,
      μ h • h + ∑ᶠ k : ℤ, rho ((4:ℝ) ^ k * μ h) • term ((4:ℝ) ^ k) h =
      μ h • h + ∑ k ∈ Finset.Icc (-(n0:ℤ)) (n1:ℤ), rho ((4:ℝ) ^ k * μ h) •
        ((((4:ℝ) ^ k) ^ 2 * ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k))⁻¹ •
          ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k) • rk h v) := by
    intro h hh
    obtain ⟨hμh, hSq, hSq0⟩ := hsub ⟨hh.2, hh.1⟩
    have hfar : ∀ k : ℤ, k ≤ (n1:ℤ) → ∀ v ∉ S', 4 * (4:ℝ) ^ k ≤ qR h (toR v) := by
      intro k hk v hv
      have hvS : v ∉ S := fun hvS => hv (Finset.mem_insert_of_mem (hSf.mem_toFinset.2 hvS))
      have h2 := hSq v hvS
      have h3 : (4:ℝ) ^ k ≤ (4:ℝ) ^ (n1:ℤ) := zpow_le_zpow_right₀ (by norm_num) hk
      rw [zpow_natCast] at h3
      have h4 : q h v = qR h (toR v) := rfl
      linarith
    have hterm : ∀ k : ℤ, k ≤ (n1:ℤ) → term ((4:ℝ) ^ k) h =
        ((((4:ℝ) ^ k) ^ 2 * ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k))⁻¹ •
          ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k) • rk h v) := by
      intro k hk
      have ht : (0:ℝ) < (4:ℝ) ^ k := by positivity
      unfold term zed
      rw [finsum_eq_sum_of_support_subset _ (s := S') ?_, finsum_eq_sum_of_support_subset _ (s := S') ?_]
      · rfl
      all_goals
        refine Function.support_subset_iff'.2 fun v hv => ?_
        have hrz : rho (qR h (toR v) / (4:ℝ) ^ k) = 0 := by
          unfold rho
          exact smoothTransition_eq_zero_of_four_mul_le _ _ ht (hfar k hk v hv)
        first
          | exact hrz
          | rw [show rho (q h v / (4:ℝ) ^ k) = 0 from hrz, zero_smul]
    have hsmall : ∀ k : ℤ, k < -(n0:ℤ) → term ((4:ℝ) ^ k) h = 0 := by
      intro k hk
      have ht : (0:ℝ) < (4:ℝ) ^ k := by positivity
      have hk4 : 4 * (4:ℝ) ^ k < m := by
        have h3 : (4:ℝ) ^ k ≤ (4:ℝ) ^ (-(n0:ℤ)) := zpow_le_zpow_right₀ (by norm_num) hk.le
        rw [_root_.zpow_neg, zpow_natCast] at h3
        have h5 : ((4:ℝ) ^ n0)⁻¹ < m / 4 := by
          rw [inv_lt_comm₀ (by positivity) (by positivity)]
          calc (m / 4)⁻¹ = 4 / m := by field_simp
            _ < 4 ^ n0 := hn0
        linarith
      unfold term
      rw [finsum_eq_zero_of_forall_eq_zero, smul_zero]
      intro v
      by_cases hv : v = 0
      · rw [hv, rk_zero_right, smul_zero]
      · have hqv : m ≤ q h v := by
          by_cases hvS : v ∈ S
          · exact le_trans (min_le_left _ _) (hSq0 v hvS hv).le
          · exact le_trans (min_le_right _ _) (hSq v hvS).le
        have hrz : rho (q h v / (4:ℝ) ^ k) = 0 := by
          unfold rho
          exact smoothTransition_eq_zero_of_four_mul_le _ _ ht (by linarith)
        rw [hrz, zero_smul]
    have hbig : ∀ k : ℤ, (n1:ℤ) < k → rho ((4:ℝ) ^ k * μ h) = 0 := by
      intro k hk
      unfold rho
      apply Real.smoothTransition.zero_of_nonpos
      have h3 : (4:ℝ) ^ (n1:ℤ) ≤ (4:ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) hk.le
      rw [zpow_natCast] at h3
      have h6 : 8 / μ h0 * (μ h0 / 2) = 4 := by field_simp; ring
      have h7 : 8 / μ h0 * (μ h0 / 2) ≤ (4:ℝ) ^ k * μ h := by
        apply mul_le_mul (by linarith) hμh.le (by positivity) (by positivity)
      linarith
    congr 1
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (-(n0:ℤ)) (n1:ℤ)) ?_]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [hterm k (Finset.mem_Icc.1 hk).2]
    · refine Function.support_subset_iff'.2 fun k hk => ?_
      simp only [Finset.coe_Icc, Set.mem_Icc, not_and_or, not_le] at hk
      rcases hk with hk | hk
      · show rho ((4:ℝ) ^ k * μ h) • term ((4:ℝ) ^ k) h = 0
        rw [hsmall k hk, smul_zero]
      · show rho ((4:ℝ) ^ k * μ h) • term ((4:ℝ) ^ k) h = 0
        rw [hbig k hk, zero_smul]
  refine ContDiffOn.congr ?_ key
  refine (h1.mono Set.inter_subset_left).smul contDiffOn_id |>.add ?_
  refine ContDiffOn.sum fun k _ => ?_
  have hr : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun h : HS L N => rho ((4:ℝ) ^ k * μ h)) (Pos L N ∩ u) :=
    contDiff_rho.comp_contDiffOn (contDiffOn_const.mul (h1.mono Set.inter_subset_left))
  have hz : ∀ v : UpperTheory.V.KT.Lat L N, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun h : HS L N => rho (qR h (toR v) / (4:ℝ) ^ k)) (Pos L N ∩ u) := fun v =>
    (contDiff_rho.comp (((contDiff_qR_left (toR v)).of_le le_top).div_const _)).contDiffOn
  have hinv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun h : HS L N => (((4:ℝ) ^ k) ^ 2 * ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k))⁻¹) (Pos L N ∩ u) := by
    refine ContDiffOn.inv (contDiffOn_const.mul (ContDiffOn.sum fun v _ => hz v)) ?_
    intro h _
    have ht : (0:ℝ) < (4:ℝ) ^ k := by positivity
    have hone : (1:ℝ) ≤ ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k) := by
      have h0mem : (0 : UpperTheory.V.KT.Lat L N) ∈ S' := by
        rw [hSEq]
        exact Finset.mem_insert_self _ _
      have hle := Finset.single_le_sum (f := fun v => rho (qR h (toR v) / (4:ℝ) ^ k))
        (fun v _ => sm_rho_nonneg _) h0mem
      have hq0 : qR h (toR 0) = 0 := q_zero_right h
      have hr0 : rho 0 = 1 := by
        unfold rho
        exact Real.smoothTransition.one_of_one_le (by norm_num)
      simp only [hq0, zero_div, hr0] at hle
      exact hle
    have : 0 < ((4:ℝ) ^ k) ^ 2 * ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k) := by positivity
    exact this.ne'
  have hsum : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun h : HS L N => ∑ v ∈ S', rho (qR h (toR v) / (4:ℝ) ^ k) • rk h v)
      (Pos L N ∩ u) := by
    refine ContDiffOn.sum fun v _ => ?_
    exact ContDiffOn.smul (hz v) (((contDiff_rk_left v).of_le le_top).contDiffOn)
  exact hr.smul (hinv.smul hsum)

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end

