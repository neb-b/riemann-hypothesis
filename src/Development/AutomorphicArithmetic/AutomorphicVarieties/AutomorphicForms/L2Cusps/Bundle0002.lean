module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0002
public import GroundTheory.AutomorphicForms.L2LocalComponents

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.BandDom
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem retract_zpow_mul (n : ℤ) (g : GA E a) :
    retractOne (splitCentre E a 1 ^ n * g) = retractOne g := by
  rw [retractOne_mul, splitEq_holds E a 1, ← map_zpow, retractOne_centralSection, one_mul]

private theorem one_lt_mod (ha : 0 < a) : (1 : ℝ) < (detModule E a (splitCentre E a 1) : ℝ) := by
  rw [splitEq_holds E a 1, detModule_centralSection ha]
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  exact Real.one_lt_exp_iff.2 (by positivity)

private theorem coe_mul_mem_band (x : G1 E a) (g : GA E a) : (x : GA E a) * g ∈ band E a ↔ g ∈ band E a := by
  simp only [band, Set.mem_setOf_eq, map_mul, mem_normOneGL_iff_detModule.1 x.2, one_mul]

private theorem zpow_mul_mem_band (ha : 0 < a) (n : ℤ) (g : GA E a) :
    splitCentre E a 1 ^ n * g ∈ band E a ↔
      (detModule E a g : ℝ) ∈ Set.Ico ((detModule E a (splitCentre E a 1) : ℝ) ^ (-n))
        ((detModule E a (splitCentre E a 1) : ℝ) ^ (-n + 1)) := by
  have hy := one_lt_mod (E := E) ha
  have hy0 : (0 : ℝ) < (detModule E a (splitCentre E a 1) : ℝ) := zero_lt_one.trans hy
  simp only [band, Set.mem_setOf_eq, map_mul, map_zpow, ha.ne', false_or, Set.mem_Ico]
  rw [← Subtype.coe_le_coe, ← Subtype.coe_lt_coe, Positive.val_mul, Positive.coe_zpow, Positive.val_one,
    zpow_add_one₀ hy0.ne', zpow_neg, ← one_div, div_le_iff₀' (zpow_pos hy0 n), one_div,
    lt_inv_mul_iff₀ (zpow_pos hy0 n)]

private theorem exists_zpow_mul_mem_band (g : GA E a) : ∃ n : ℤ, splitCentre E a 1 ^ n * g ∈ band E a := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · exact ⟨0, Or.inl ha⟩
  · obtain ⟨n, hn⟩ := exists_mem_Ico_zpow (detModule E a g).2 (one_lt_mod (E := E) ha)
    exact ⟨-n, (zpow_mul_mem_band ha _ g).2 (by rwa [neg_neg])⟩

private theorem zpow_eq_of_mem_band {g : GA E a} {m n : ℤ} (hm : splitCentre E a 1 ^ m * g ∈ band E a)
    (hn : splitCentre E a 1 ^ n * g ∈ band E a) : splitCentre E a 1 ^ m = splitCentre E a 1 ^ n := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact Units.ext (Subsingleton.elim _ _)
  · have hy := one_lt_mod (E := E) ha
    rw [zpow_mul_mem_band ha] at hm hn
    have h1 := (zpow_lt_zpow_iff_right₀ hy).1 (hm.1.trans_lt hn.2)
    have h2 := (zpow_lt_zpow_iff_right₀ hy).1 (hn.1.trans_lt hm.2)
    rw [show m = n by omega]

end UpperTheory.V.KernelIndexFullLattice

open UpperTheory.V.KernelIndexFullLattice in
theorem UpperTheory.V.KernelIndexFullLattice.bandDom_holds :
    UpperTheory.V.KernelIndexFullLattice.BandDom := by
  intro E _ _ _ a D hD g
  obtain ⟨⟨x, hx⟩, hxD, huniq⟩ := hD (retractOne g)
  obtain ⟨n, hn⟩ := exists_zpow_mul_mem_band g
  obtain ⟨γ, hγ⟩ := id hx
  have hγ' : ratGL E a γ = (x : GA E a) := hγ
  refine ⟨⟨(x : GA E a) * splitCentre E a 1 ^ n, mem_latticeGL_iff.2 ⟨γ, n, by rw [hγ']⟩⟩, ⟨?_, ?_⟩, ?_⟩
  · change retractOne ((x : GA E a) * splitCentre E a 1 ^ n * g) ∈ D
    rw [mul_assoc, retractOne_coe_mul, retract_zpow_mul]
    exact hxD
  · change (x : GA E a) * splitCentre E a 1 ^ n * g ∈ band E a
    rw [mul_assoc, coe_mul_mem_band]
    exact hn
  · rintro ⟨l, hl⟩ ⟨h1, h2⟩
    obtain ⟨δ, m, rfl⟩ := mem_latticeGL_iff.1 hl
    let y : G1 E a := ⟨ratGL E a δ, rationalGL_le_normOneGL ⟨δ, rfl⟩⟩
    change retractOne ((y : GA E a) * splitCentre E a 1 ^ m * g) ∈ D at h1
    change (y : GA E a) * splitCentre E a 1 ^ m * g ∈ band E a at h2
    rw [mul_assoc, retractOne_coe_mul, retract_zpow_mul] at h1
    rw [mul_assoc, coe_mul_mem_band] at h2
    have e : y = x := congrArg Subtype.val (huniq ⟨y, ⟨δ, rfl⟩⟩ h1)
    refine Subtype.ext ?_
    change (y : GA E a) * splitCentre E a 1 ^ m = (x : GA E a) * splitCentre E a 1 ^ n
    rw [e, zpow_eq_of_mem_band h2 hn]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.ContMem
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

theorem contMem_holds : ContMem := by
  intro E _ _ _ a μ _ μ₁ _ hp φ hφ h
  obtain ⟨hc, hl, hz, hcu⟩ := mem_cuspCont.1 hφ
  have hL : IsLeftInvariant φ := fun γ g => hl γ g
  have hcusp : AutomorphicForm.IsCuspidal φ := UpperTheory.constantTerm_eq_zero_of_isCuspidal E a φ hL hc hcu
  have hr : ∀ g : GA E a, φ (retractOne g : G1 E a) = φ g := fun g => by
    obtain ⟨t, ht⟩ := exists_split (E := E) (a := a) splitEq_holds (Reduction.detModule E a g)
    have h1 := hz t (retractOne g : G1 E a)
    rw [← h1, splitCentre_comm, coe_retractOne, ← ht, inv_mul_cancel_right]
  have hΦ : cuspQuot hL ∘ quotMap E a = descend (latticeGL E a) φ := by
    funext q
    change cuspQuot hL (RightCosetSpace.mk (Γ1 E a) (retractOne q.out)) = φ q.out
    rw [cuspQuot_mk]
    exact hr q.out
  have hm : MemLp (cuspQuot hL) 2 (RightCosetSpace.quotientMeasure (Γ1 E a) μ₁) := by
    have hs := (continuous_cuspQuot hL hc).aestronglyMeasurable
      (μ := Measure.map (quotMap E a) (quotMeasure (latticeGL E a) μ))
    rw [← hp.map_eq, memLp_map_measure_iff hs hp.aemeasurable, hΦ]
    exact h.2
  have hv : hm.toLp _ ∈ cuspidalL2 μ₁ := by
    change IsCuspidalL2 μ₁ (hm.toLp _)
    intro r h0 h1
    filter_upwards [ae_ctFun_congr μ₁ r (MemLp.coeFn_toLp hm)] with y hy
    rw [constantTermL2, hy]
    simpa only [ctFun, cuspQuot_mk, Subgroup.coe_mul, coe_unipOne, constantTerm, Pi.zero_apply]
      using hcusp r h0 h1 y
  refine ⟨⟨hm.toLp _, hv⟩, Lp.ext ?_⟩
  have hQuot : (cmp hp ⟨hm.toLp _, hv⟩ : Quot (latticeGL E a) → ℂ)
      =ᵐ[quotMeasure (latticeGL E a) μ] cuspQuot hL ∘ quotMap E a :=
    (Lp.coeFn_compMeasurePreserving _ hp).trans
      (hp.quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp hm))
  rw [hΦ] at hQuot
  exact hQuot.trans h.coeFn_toL2.symm

end UpperTheory.V.KernelIndexFullLattice
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.DenseHolds
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum

theorem UpperTheory.V.KernelIndexFullLattice.dense_holds (K : Type) [Field K] [NumberField K]
    (n : ℕ) (μ₁ : Measure (Reduction.normOneGL (K := K) (n := n))) [μ₁.IsHaarMeasure] :
    ((centralCuspForms K n).map (cuspVecL μ₁)).topologicalClosure = ⊤ :=
  topologicalClosure_map_centralCuspForms μ₁
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.MuHaar
section
open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.KernelIndexFullLattice

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem one_lt_top (ha : 0 < a) : 1 < detModule E a (splitCentre E a 1) := by
  rw [splitEq_holds E a 1, detModule_centralSection ha]
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  change (1 : ℝ) < Real.exp _
  exact Real.one_lt_exp_iff.2 (by positivity)

private theorem band_zero : band E 0 = Set.univ := Set.eq_univ_of_forall fun _ => Or.inl rfl

private theorem band_pos (ha : 0 < a) :
    band E a = detModule E a ⁻¹' Set.Ico 1 (detModule E a (splitCentre E a 1)) := by
  ext g
  simp only [band, Set.mem_setOf_eq, ha.ne', false_or, Set.mem_preimage, Set.mem_Ico]

private theorem measurableSet_band : MeasurableSet (band E a) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [band_zero]; exact MeasurableSet.univ
  · rw [band_pos ha]
    have hc : Continuous fun g : GA E a => (detModule E a g : ℝ) :=
      continuous_subtype_val.comp continuous_detModule
    exact hc.measurable (measurableSet_Ico (a := (1 : ℝ)) (b := (detModule E a (splitCentre E a 1) : ℝ)))

private theorem meas_retract : Measurable (retractOne : GA E a → G1 E a) := continuous_retractOne.measurable

private theorem muOne_apply (μ : Measure (GA E a)) {A : Set (G1 E a)} (hA : MeasurableSet A) :
    muOne μ A = μ (retractOne ⁻¹' A ∩ band E a) := by
  rw [muOne, Measure.map_apply meas_retract hA, Measure.restrict_apply (meas_retract hA)]

omit [_root_.NumberField.IsTotallyComplex E] in
private theorem retract_mul_left (x : G1 E a) (g : GA E a) :
    retractOne ((x : GA E a) * g) = x * retractOne g := by
  ext1
  rw [coe_retractOne, Subgroup.coe_mul, coe_retractOne, map_mul, (mem_normOneGL_iff_detModule).1 x.2, one_mul,
    mul_assoc]

private theorem band_mul_left (x : G1 E a) (g : GA E a) : (x : GA E a) * g ∈ band E a ↔ g ∈ band E a := by
  simp only [band, Set.mem_setOf_eq, map_mul, (mem_normOneGL_iff_detModule).1 x.2, one_mul]

private theorem isCompact_posIcc (s t : {r : ℝ // 0 < r}) : IsCompact (Set.Icc s t) := by
  refine (Topology.IsInducing.subtypeVal (t := {r : ℝ | 0 < r})).isCompact_iff.2 ?_
  convert isCompact_Icc (a := (s : ℝ)) (b := (t : ℝ)) using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, s.2.trans_le hx.1⟩, hx, rfl⟩

end

theorem UpperTheory.V.KernelIndexFullLattice.muHaar_holds :
    UpperTheory.V.KernelIndexFullLattice.MuHaar := by
  intro E _ _ _ a μ _
  have h1 : (muOne μ).IsMulLeftInvariant := by
    refine ⟨fun x => ?_⟩
    ext A hA
    have hm : Measurable fun y : G1 E a => x * y := measurable_const_mul x
    rw [Measure.map_apply hm hA, muOne_apply μ (hm hA), muOne_apply μ hA,
      ← measure_preimage_mul μ (x : GA E a) (retractOne ⁻¹' A ∩ band E a)]
    congr 1
    ext g
    simp only [Set.mem_inter_iff, Set.mem_preimage, retract_mul_left, band_mul_left]
  have h2 : IsFiniteMeasureOnCompacts (muOne μ) := by
    refine ⟨fun C hC => ?_⟩
    rw [muOne_apply μ hC.measurableSet]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have : Subsingleton (GA E 0) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
      exact (Set.toFinite _).isCompact.measure_lt_top
    · have hc : Continuous fun p : G1 E a × {r : ℝ // 0 < r} => (p.1 : GA E a) * centralSection E a p.2 :=
        (continuous_subtype_val.comp continuous_fst).mul (continuous_centralSection.comp continuous_snd)
      refine lt_of_le_of_lt (measure_mono ?_)
        ((hC.prod (isCompact_posIcc 1 (detModule E a (splitCentre E a 1)))).image hc).measure_lt_top
      rintro g ⟨hg, hb⟩
      rw [band_pos ha] at hb
      refine ⟨(retractOne g, detModule E a g), ⟨hg, hb.1, hb.2.le⟩, ?_⟩
      change (retractOne g : GA E a) * centralSection E a (detModule E a g) = g
      rw [coe_retractOne, inv_mul_cancel_right]
  have h3 : (muOne μ).IsOpenPosMeasure := by
    refine ⟨fun U hU hne => ?_⟩
    obtain ⟨x, hx⟩ := hne
    have hO : IsOpen (retractOne ⁻¹' U : Set (GA E a)) := hU.preimage continuous_retractOne
    rw [muOne_apply μ hU.measurableSet]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have : Subsingleton (GA E 0) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
      rw [band_zero, Set.inter_univ]
      refine hO.measure_ne_zero μ ⟨1, ?_⟩
      change retractOne _ ∈ U
      rwa [Subsingleton.elim (retractOne _) x]
    · obtain ⟨s, hs1, hs2⟩ : ∃ s : {r : ℝ // 0 < r}, 1 < s ∧ s < detModule E a (splitCentre E a 1) := by
        obtain ⟨s, h1, h2⟩ := exists_between (show (1 : ℝ) < (detModule E a (splitCentre E a 1) : ℝ) from one_lt_top ha)
        exact ⟨⟨s, one_pos.trans h1⟩, h1, h2⟩
      have hc : Continuous fun g : GA E a => (detModule E a g : ℝ) :=
        continuous_subtype_val.comp continuous_detModule
      have hI : IsOpen (detModule E a ⁻¹' Set.Ioo 1 (detModule E a (splitCentre E a 1)) : Set (GA E a)) :=
        (isOpen_Ioo (a := (1 : ℝ)) (b := (detModule E a (splitCentre E a 1) : ℝ))).preimage hc
      have hd : detModule E a ((x : GA E a) * centralSection E a s) = s := by
        rw [map_mul, (mem_normOneGL_iff_detModule).1 x.2, detModule_centralSection ha, one_mul]
      have hr : retractOne ((x : GA E a) * centralSection E a s) = x := by
        ext1
        rw [coe_retractOne, hd, mul_inv_cancel_right]
      have hp := (hO.inter hI).measure_ne_zero μ ⟨(x : GA E a) * centralSection E a s, by
        rw [Set.mem_preimage, hr]; exact hx, by rw [Set.mem_preimage, hd]; exact ⟨hs1, hs2⟩⟩
      intro h0
      refine hp (measure_mono_null ?_ h0)
      rw [band_pos ha]
      exact Set.inter_subset_inter_right _ (Set.preimage_mono Set.Ioo_subset_Ico_self)
  exact {}
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.PvFinHolds
section
open NumberField MeasureTheory
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

private theorem UpperTheory.V.KernelIndexFullLattice.pvFin_abs {G E M : Type} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [AddCommGroup M] [Module ℂ M]
    (C : Subgroup G) [IsTopologicalGroup C] [CompactSpace C] [T2Space C] (ρ : BanachRep G E)
    (σ : Representation ℂ C M) (hσ : CompactRep.IsKFinite σ) (j : M →ₗ[ℂ] E) (hj : Function.Injective j)
    (hjσ : ∀ (k : C) m, j (σ k m) = ρ k (j m)) (F : Submodule ℂ M)
    (hF : ∀ (c : Submodule (MonoidAlgebra ℂ C) σ.asModule)
      (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ C) σ.asModule),
      FiniteDimensional ℂ (LinearMap.range (CompactRep.kProj hσ hc ∘ₗ F.subtype)))
    (v : E) (hv : FiniteDimensional ℂ (ρ.kSpan C v)) :
    ∃ N : Submodule ℂ E, FiniteDimensional ℂ N ∧ ∀ P : E →L[ℂ] E,
      (∀ (k : C) x, P (ρ k x) = ρ k (P x)) → (∀ x ∈ ρ.kSpan C v, ∃ m ∈ F, j m = P x) → P v ∈ N := by
  let S : Subrepresentation (ρ.restrict C).toRepresentation :=
    ⟨ρ.kSpan C v, fun k _ hw => ρ.map_mem_kSpan_of_mem C hw k⟩
  have hc : Representation.HasContinuousCoeff (W := ρ.kSpan C v) S.toRepresentation := by
    intro φ w
    refine φ.continuous_of_finiteDimensional.comp ?_
    exact Continuous.subtype_mk ((ρ.continuous_orbit (w : E)).comp continuous_subtype_val) _
  obtain ⟨N, hN, hN'⟩ := UpperTheory.V.KernelIndexFullLattice.homFin_holds C M (ρ.kSpan C v) σ hσ S.toRepresentation hc F hF
  refine ⟨N.map j, inferInstance, fun P hP hPF => ?_⟩
  have hr : ∀ x : ρ.kSpan C v, ((P : E →ₗ[ℂ] E) ∘ₗ (ρ.kSpan C v).subtype) x ∈ LinearMap.range j := by
    intro x
    obtain ⟨m, -, hm⟩ := hPF x x.2
    exact ⟨m, hm⟩
  let f : ρ.kSpan C v →ₗ[ℂ] M := (LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range j) _ hr
  have hf : ∀ x, j (f x) = P x := fun x =>
    congrArg Subtype.val ((LinearEquiv.ofInjective j hj).apply_symm_apply ⟨_, hr x⟩)
  refine ⟨f ⟨v, ρ.mem_kSpan_self C v⟩, hN' f (fun k x => hj ?_) (fun x => ?_) _, hf _⟩
  · rw [hjσ, hf, hf, ← hP]
    rfl
  · obtain ⟨m, hm, e⟩ := hPF x x.2
    rwa [hj ((hf x).trans e.symm)]

theorem UpperTheory.V.KernelIndexFullLattice.pvFin_holds :
    UpperTheory.V.KernelIndexFullLattice.PvFin := by
  intro K _ _ n μ₁ _ π U hUc hUo v hv hfin
  let j : π.carrier →ₗ[ℂ] CuspL2 μ₁ := cuspVecL μ₁ ∘ₗ π.carrier.subtype
  have hj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).2 fun m hm => Subtype.ext ?_
    exact eq_zero_of_cuspVecL_eq_zero (μ := μ₁) (π.le_central m.2) hm
  obtain ⟨N, hN, hN'⟩ := UpperTheory.V.KernelIndexFullLattice.pvFin_abs (archCompact K n) (archRepT μ₁) π.toModule.gk.σ
    π.toModule.gk.isKFinite j hj (fun k m => cuspToL2_sigma μ₁ k (π.le_central m.2))
    (fixedVectors π.toModule.τ U) (π.isAdmissible.2 U hUc hUo) v hfin
  refine ⟨N, hN, fun P hPk hPu hP => hN' P hPk fun x hx => ?_⟩
  have hxU : ∀ u ∈ U, cuspRepT μ₁ (retractOne (finEmb K n u)) x = x := by
    intro u hu
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      simp only [archRepT_apply]
      have hcomm : retractOne (finEmb K n u) * archP K n k = archP K n k * retractOne (finEmb K n u) := by
        rw [← retract_infEmb (k : archGroup K n), ← retractOne_mul, ← retractOne_mul,
          infEmb_mul_finEmb_comm (k : archGroup K n) u]
      have h1 := (cuspRepT μ₁).map_mul_apply (retractOne (finEmb K n u)) (archP K n k) v
      have h2 := (cuspRepT μ₁).map_mul_apply (archP K n k) (retractOne (finEmb K n u)) v
      rw [hv u hu, ← hcomm, h1] at h2
      exact h2
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  obtain ⟨φ, hφ, e⟩ := hP x
  refine ⟨⟨φ, hφ⟩, fun u hu => hj ?_, e⟩
  have h := cuspToL2_finRepCusp μ₁ u (π.le_central hφ)
  rw [e, ← hPu u hu, hxU u hu, ← e] at h
  exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.QuotMk
section
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem UpperTheory.V.KernelIndexFullLattice.quotMk_holds :
    UpperTheory.V.KernelIndexFullLattice.QuotMk := by
  intro E _ _ _ a g
  have h0 : mk (latticeGL E a) (Quotient.out (mk (latticeGL E a) g)) = mk (latticeGL E a) g :=
    Quotient.out_eq _
  obtain ⟨⟨l, hl⟩, e⟩ := mk_eq_iff.1 h0.symm
  obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hl
  have hγ1 : AdelicGLn.diagonal E a γ ∈ Reduction.normOneGL (K := E) (n := a) := Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩
  have hγΓ : (⟨AdelicGLn.diagonal E a γ, hγ1⟩ : Reduction.normOneGL (K := E) (n := a)) ∈ UpperTheory.V.KernelIndexFullLattice.Γ1 E a := ⟨γ, rfl⟩
  have h1 : retractOne (ratGL E a γ * splitCentre E a 1 ^ n * g) =
      (⟨AdelicGLn.diagonal E a γ, hγ1⟩ : Reduction.normOneGL (K := E) (n := a)) * retractOne g := by
    have h2 := retractOne_coe_mul (⟨AdelicGLn.diagonal E a γ, hγ1⟩ : Reduction.normOneGL (K := E) (n := a))
      (splitCentre E a 1 ^ n * g)
    have h3 : retractOne (K := E) (n := a) (splitCentre E a 1 ^ n * g) = retractOne g := by
      rw [← splitCentre_intCast, UpperTheory.V.KernelIndexFullLattice.splitEq_holds, retractOne_mul, retractOne_centralSection, one_mul]
    rw [h3] at h2
    rw [mul_assoc]
    exact h2
  unfold UpperTheory.V.KernelIndexFullLattice.quotMap
  rw [← e]
  exact (congrArg _ h1).trans (RightCosetSpace.mk_mul_of_mem hγΓ _)
end

