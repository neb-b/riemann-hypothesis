module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.FibExGram
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SmulMemHermR
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SdExCore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SdExChar

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.GramMapFibreExistence
section
noncomputable section

namespace PI.OmFibreUniq.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology
open PI.OmFibreUniq PI.VolStabSW PI.VolStabSW.TensAllW PI.VolStabSW.OmFibG
open scoped TensorProduct

theorem densAll_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ)
    (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure) :
    DensAll μ (gramR (Fv F v) σ J) Subtype.val ν
      {X : Fin a → Fin n → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have hfree := isOpen_linIndep (Module.finBasis F E) (Fv F v) (isOpen_units_Fv F v) (lip_field _)
    (a := a) (M := n)
  obtain ⟨t1, t2, t3, t4, t5, _t6, t7⟩ := tensFacts_of_fib σ n J a (Fv F v) hσ hJ hfree
  have := hμ
  have := hν
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (HermR (Fv F v) σ a) :=
    t4.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have hNA : HasCOSub (Fin a → Fin n → Fv F v ⊗[F] E) := by
    obtain ⟨π, h0, hπ⟩ := exists_pow_tendsto_zero_Fv v
    exact hasCOSub_of_lat (latSub (Module.finBasis F E) v a n)
      (PositiveNearLattice.isClopen_latV (Module.finBasis F E) v a n).isOpen
      (PositiveNearLattice.isCompact_latV (Module.finBasis F E) v a n) π h0 hπ
  have hC : DensCosB (scaledB (Fv F v) (latSub (Module.finBasis F E) v a n)) μ
      (gramR (Fv F v) σ J) Subtype.val ν
      {X : Fin a → Fin n → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
    intro x hx
    obtain ⟨N, hN, hd⟩ := gramFilt_all σ hσ n J hJ hdet a v _ (Module.finBasis F E) x hx
    refine ⟨N, hN, fun y hy Λ0 hB _ _ hsub => ?_⟩
    obtain ⟨Λ, H, D, h0, hΛo, hΛc, hΛa, hHo, hHc, hHb, hD, hyp⟩ := hd y hy Λ0 hB hsub
    subst h0
    exact densCos_of_filt henselCount_holds cosDens_holds μ ν (gramR (Fv F v) σ J) Subtype.val
      Subtype.val_injective (gramH (Fv F v) σ hσ J hJ) (Continuous.subtype_mk t5 _)
      (fun _ => rfl) y Λ H hΛo hΛc hΛa hHo hHc hHb D hD hyp
  have hLC := densLC_of_cosB _ _ (isCOBasis_latSub (Module.finBasis F E) v a n) hC
  exact (densAll_iff _ _ _ _ _).2 (densApprox_lc μ _ _ ν _ t7 hNA hLC)

theorem gram_map_fibre_existence : FibEx := by
  intro F E _ _ _ _ _ σ n J v a hCM hJ μ ν hμ hν
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have hfree := isOpen_linIndep (Module.finBasis F E) (Fv F v) (isOpen_units_Fv F v) (lip_field _)
    (a := a) (M := n)
  exact fib_of_tens DiscreteGroups.fibOfDens_holds (tensFacts_of_fib σ n J a (Fv F v) hσ hJ.1 hfree) μ ν
    hμ hν (densAll_gen σ hσ J hJ.1 hJ.2 v a μ ν hμ hν)

end PI.OmFibreUniq.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SdExAbs
section
noncomputable section

namespace PI.OmFibreUniq.W.SdAbs

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter NumberField IsDedekindDomain
open PI.VolStabSW.SdUniqW PI.OmFibreUniq.W.SdCore PI.OmFibreUniq.W.SdChar
open scoped ENNReal

section Abs

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  {V : Type} [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul (Fv F v) V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (B : V → V → Fv F v)

theorem B_zero_left (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) (y : V) : B 0 y = 0 := by
  have := hBs 0 0 y
  rwa [zero_smul, zero_mul] at this

theorem haar_smul_preimage (μ0 : Measure V) [μ0.IsAddHaarMeasure] (a : Fv F v) (ha : a ≠ 0) :
    ∃ c : ℝ≥0∞, ∀ S, MeasurableSet S → μ0 ((fun y : V => a • y) ⁻¹' S) = c * μ0 S := by
  let e : V ≃+ V := (LinearEquiv.smulOfNeZero (Fv F v) V a ha).toAddEquiv
  have he : Continuous e := by
    show Continuous fun y : V => a • y
    exact continuous_const_smul a
  have hes : Continuous e.symm := by
    show Continuous fun y : V => a⁻¹ • y
    exact continuous_const_smul a⁻¹
  haveI := AddEquiv.isAddHaarMeasure_map μ0 e he hes
  refine ⟨(Measure.addHaarScalarFactor (μ0.map e) μ0 : ℝ≥0∞), fun S hS => ?_⟩
  have hmap : μ0.map e = Measure.addHaarScalarFactor (μ0.map e) μ0 • μ0 :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have h := Measure.map_apply (μ := μ0) he.measurable hS
  rw [hmap, Measure.smul_apply] at h
  show μ0 (e ⁻¹' S) = _
  rw [← h]
  rfl

theorem exists_selfDual_measure (ψ0 : Fv F v → ℂ) (hψc : Continuous ψ0) (hψa : ∀ r s, ψ0 (r + s) = ψ0 r * ψ0 s)
    (hψn : ∀ r, ‖ψ0 r‖ = 1) (hnt : ∃ y, ψ0 y ≠ 1)
    (hBa : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hBs : ∀ (c : Fv F v) x y, B (c • x) y = c * B x y) (hBsym : ∀ x y, B x y = B y x)
    (hBjc : Continuous (fun p : V × V => B p.1 p.2)) (hD : DualAt v B) :
    ∃ μ : Measure V, SelfDual μ (fun x y => ψ0 (B x y)) := by
  obtain ⟨π, hπ0, hπt, -⟩ := PI.VolStabSW.exists_unif_Fv v
  set χ : V → V → ℂ := fun x y => ψ0 (B x y) with hχdef
  have hχc : Continuous (fun p : V × V => χ p.1 p.2) :=
    hψc.comp hBjc
  have hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y := fun x t y => by
    simp only [hχdef]; rw [hBa, hψa]
  have hsym : ∀ x y, χ x y = χ y x := fun x y => by simp only [hχdef]; rw [hBsym]
  have hn : ∀ x y, ‖χ x y‖ = 1 := fun x y => hψn _
  obtain ⟨L, hLc, hLo, hsL, hK⟩ := hD
  have hBzr : ∀ x, B x 0 = 0 := fun x => by rw [hBsym]; exact B_zero_left v B hBs x
  have hQ : ∀ᶠ q in 𝓝 (0 : V), ∀ x ∈ (L : Set V), B x q ∈ Aset v ψ0 := by
    have hP : ∀ x ∈ (L : Set V), ∀ᶠ z : V × V in 𝓝 ((0 : V), x), B z.2 z.1 ∈ Aset v ψ0 :=
      fun x _ => by
        have hc : Continuous fun z : V × V => B z.2 z.1 :=
          hBjc.comp (continuous_snd.prodMk continuous_fst)
        exact (hc.tendsto ((0 : V), x)).eventually_mem
          (by rw [show B ((0 : V), x).2 ((0 : V), x).1 = 0 from hBzr x]
              exact Aset_mem_nhds v ψ0 hψc hψa hψn)
    exact hLc.eventually_forall_of_forall_eventually (P := fun q x => B x q ∈ Aset v ψ0) hP
  have hNo0 : IsOpen (ann χ (L : Set V)) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have ht : Tendsto (fun y' : V => y' - y) (𝓝 y) (𝓝 0) := by
      have := (continuous_sub_right y).tendsto y
      rwa [sub_self] at this
    filter_upwards [ht hQ] with y' hy'
    intro x hx
    have hq : ψ0 (B x (y' - y)) = 1 := by
      have := hy' x hx 1 (one_mem _)
      rwa [one_mul] at this
    have hyx := hy x hx
    show ψ0 (B x y') = 1
    have e1 : y' = y + (y' - y) := by abel
    rw [e1, hBsym, hBa, hψa, hBsym y, hBsym (y' - y)]
    rw [show ψ0 (B x y) = 1 from hyx, hq, one_mul]
  have hNcl : IsClosed (ann χ (L : Set V)) := isClosed_ann χ hχc L
  have hNc0 : IsCompact (ann χ (L : Set V)) := by
    obtain ⟨y0, hy0⟩ := hnt
    obtain ⟨K, hKc, hKs⟩ := hK y0
    refine hKc.of_isClosed_subset hNcl fun y hy => hKs fun x hx => ?_
    apply mem_of_psi v ψ0 y0 _ hy0
    intro s hs'
    obtain ⟨x', hx', hB'⟩ := hsL s hs' x hx
    rw [← hB' y]
    exact hy x' hx'

  set M : ℕ → AddSubgroup V := fun k => L.comap (DistribSMul.toAddMonoidHom V (π ^ k))
    with hMdef
  have hMset : ∀ k, (M k : Set V) = (fun x => π ^ k • x) ⁻¹' (L : Set V) := fun k => rfl
  have hπk : ∀ k, π ^ k ≠ 0 := fun k => pow_ne_zero k hπ0
  have hann : ∀ k, ann χ (M k : Set V) = (fun y => (π ^ k)⁻¹ • y) ⁻¹' ann χ (L : Set V) := by
    intro k
    ext y
    constructor
    · intro hy x hx
      have hx' : (π ^ k)⁻¹ • x ∈ (M k : Set V) := by
        show π ^ k • ((π ^ k)⁻¹ • x) ∈ L
        rwa [smul_smul, mul_inv_cancel₀ (hπk k), one_smul]
      have := hy _ hx'
      simp only [hχdef] at this ⊢
      rwa [hBs, hBsym, ← hBs, hBsym] at this
    · intro hy x hx
      have := hy _ hx
      change ψ0 (B (π ^ k • x) ((π ^ k)⁻¹ • y)) = 1 at this
      simp only [hχdef]
      rwa [hBs, hBsym, hBs, hBsym, ← mul_assoc, mul_inv_cancel₀ (hπk k), one_mul] at this
  have hMo : ∀ k, IsOpen (M k : Set V) := fun k => by
    rw [hMset]; exact hLo.preimage (continuous_const_smul _)
  have hMc : ∀ k, IsCompact (M k : Set V) := fun k => by
    rw [hMset]
    exact (Homeomorph.smulOfNeZero (π ^ k) (hπk k)).isCompact_preimage.2 hLc
  have hNo : ∀ k, IsOpen (ann χ (M k : Set V)) := fun k => by
    rw [hann]; exact hNo0.preimage (continuous_const_smul _)
  have hNc : ∀ k, IsCompact (ann χ (M k : Set V)) := fun k => by
    rw [hann]
    exact (Homeomorph.smulOfNeZero ((π ^ k)⁻¹) (inv_ne_zero (hπk k))).isCompact_preimage.2 hNc0
  have hex : ∀ y, ∀ᶠ k in atTop, y ∈ M k := by
    intro y
    have ht : Tendsto (fun k => π ^ k • y) atTop (𝓝 0) := by simpa using hπt.smul_const y
    exact (ht.eventually_mem (hLo.mem_nhds L.zero_mem)).mono fun k hk => hk
  have hsh : ∀ U ∈ 𝓝 (0 : V), ∀ᶠ k in atTop, ann χ (M k : Set V) ⊆ U := by
    intro U hU
    have hP : ∀ w ∈ ann χ (L : Set V), ∀ᶠ z : Fv F v × V in 𝓝 ((0 : Fv F v), w), z.1 • z.2 ∈ U :=
      fun w _ => (continuous_smul.tendsto ((0 : Fv F v), w)).eventually_mem
        (by rw [show ((0 : Fv F v), w).1 • ((0 : Fv F v), w).2 = (0 : V) by simp]; exact hU)
    have hev := hNc0.eventually_forall_of_forall_eventually (P := fun c w => c • w ∈ U) hP
    filter_upwards [hπt.eventually hev] with k hk y hy
    rw [hann] at hy
    have := hk _ hy
    rwa [smul_smul, mul_inv_cancel₀ (hπk k), one_smul] at this

  let μ0 : Measure V := Measure.addHaar
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet
  have hNm : MeasurableSet (ann χ (L : Set V)) := hNcl.measurableSet
  have hL0 : μ0 (L : Set V) ≠ 0 := (hLo.measure_pos μ0 ⟨0, L.zero_mem⟩).ne'
  have hLt : μ0 (L : Set V) ≠ ⊤ := hLc.measure_lt_top.ne
  have hgen : ∀ k, μ0 (M k : Set V) * μ0 (ann χ (M k : Set V)) =
      μ0 (L : Set V) * μ0 (ann χ (L : Set V)) := by
    intro k
    obtain ⟨c1, hc1⟩ := haar_smul_preimage v μ0 (π ^ k) (hπk k)
    obtain ⟨c2, hc2⟩ := haar_smul_preimage v μ0 ((π ^ k)⁻¹) (inv_ne_zero (hπk k))
    have hid : (fun y : V => (π ^ k)⁻¹ • y) ⁻¹' ((fun y : V => π ^ k • y) ⁻¹' (L : Set V)) =
        (L : Set V) := by
      ext y; simp [smul_smul, mul_inv_cancel₀ (hπk k)]
    have hm1 : MeasurableSet ((fun y : V => π ^ k • y) ⁻¹' (L : Set V)) :=
      hLm.preimage (continuous_const_smul _).measurable
    have h12 : c2 * c1 = 1 := by
      have := hc2 _ hm1
      rw [hid, hc1 _ hLm, ← mul_assoc] at this
      have h3 : μ0 (L : Set V) * (μ0 (L : Set V))⁻¹ = 1 := ENNReal.mul_inv_cancel hL0 hLt
      calc c2 * c1 = c2 * c1 * μ0 (L : Set V) * (μ0 (L : Set V))⁻¹ := by
            rw [mul_assoc (c2 * c1), h3, mul_one]
        _ = 1 := by rw [← this, h3]
    rw [hann, hMset, hc1 _ hLm, hc2 _ hNm]
    calc c1 * μ0 (L : Set V) * (c2 * μ0 (ann χ (L : Set V)))
        = (c2 * c1) * (μ0 (L : Set V) * μ0 (ann χ (L : Set V))) := by ring
      _ = _ := by rw [h12, one_mul]
  exact selfDual_of_pairs χ hχc hχ hsym hn M hMc hMo hNc hNo hex hsh μ0
    (fun k => (hgen k).trans (hgen 0).symm)

end Abs

end PI.OmFibreUniq.W.SdAbs
end
end

