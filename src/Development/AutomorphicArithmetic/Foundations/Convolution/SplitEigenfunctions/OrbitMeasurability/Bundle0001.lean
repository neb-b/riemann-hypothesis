module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
public import GroundTheory.AutomorphicForms.GL2.GJGlobalMean
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0002
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.HermitianStandardVector
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0002
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.AbsUnf
section
noncomputable section

open MeasureTheory Measure Set
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

private theorem invInvariant {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure]
    [ν.IsMulRightInvariant] : ν.IsInvInvariant := by
  constructor
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, ν.inv = c • ν :=
    ⟨haarScalarFactor ν.inv ν, by
      have := isMulLeftInvariant_eq_smul ν.inv ν
      rwa [ENNReal.smul_def] at this⟩
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts H) := inferInstance
  have hpos : ν K ≠ 0 := (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have hfin : ν K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hsq : ν = (c * c) • ν := by
    conv_lhs => rw [← Measure.inv_inv ν, hc]
    rw [Measure.inv_def (c • ν), Measure.map_smul _ measurable_inv.aemeasurable, ← Measure.inv_def, hc, smul_smul]
  have h1 : c * c = 1 := by
    have : (c * c) * ν K = 1 * ν K := by
      rw [one_mul]; conv_rhs => rw [hsq]
      simp
    exact (ENNReal.mul_left_inj hpos hfin).1 this
  have h2 : c = 1 := by
    rcases lt_trichotomy c 1 with h | h | h
    · exact absurd h1 (ne_of_lt (by
        calc c * c ≤ c * 1 := by gcongr
          _ < 1 := by simpa using h))
    · exact h
    · exact absurd h1 (ne_of_gt (by
        calc 1 < c := h
          _ = 1 * c := by simp
          _ ≤ c * c := by gcongr))
  rw [hc, h2, one_smul]

private theorem unf {G H ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    [Countable ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι] (μ : Measure G) (ν : Measure H)
    [μ.IsHaarMeasure] [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G) (Γ' : Subgroup G) (Γ : Subgroup H)
    [Countable Γ'] [Countable Γ] (DG : Set G) (DH : Set H) (r : ι → G) (hj : Continuous j)
    (hinj : Function.Injective j) (hDG : IsFundamentalDomain Γ' DG μ) (hDH : IsFundamentalDomain Γ DH ν)
    (hr : ∀ i, r i ∈ Γ') (hjΓ : ∀ δ ∈ Γ, j δ ∈ Γ') (hdec : ∀ γ ∈ Γ', ∃! i, ∃ δ ∈ Γ, γ = r i * j δ)
    (f : G × G → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ γ ∈ Γ', ∀ x y, f (γ * x, y) = f (x, y)) :
    ∫⁻ p : G × ι, ∫⁻ g, f (p.1, j g * ((r p.2)⁻¹ * p.1)) ∂ν ∂((μ.restrict DG).prod Measure.count) =
      ∫⁻ y, ∫⁻ g in DH, f (j g * y, y) ∂ν ∂μ := by
  haveI := invInvariant ν
  have hjm : Measurable j := hj.measurable
  have hrm : Measurable r := Measurable.of_discrete
  let e : ι × Γ → Γ' := fun q => ⟨r q.1 * j q.2, Γ'.mul_mem (hr _) (hjΓ _ q.2.2)⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨i, δ⟩ ⟨i', δ'⟩ h
      have h' : r i * j δ = r i' * j δ' := congrArg Subtype.val h
      have hi : i = i' := (hdec _ (Γ'.mul_mem (hr i) (hjΓ _ δ.2))).unique ⟨δ, δ.2, rfl⟩ ⟨δ', δ'.2, h'⟩
      subst hi
      have : δ = δ' := Subtype.ext (hinj (mul_left_cancel h'))
      rw [this]
    · rintro ⟨γ, hγ⟩
      obtain ⟨i, ⟨δ, hδ, h⟩, -⟩ := hdec γ hγ
      exact ⟨(i, ⟨δ, hδ⟩), Subtype.ext h.symm⟩

  let K : G → ℝ≥0∞ := fun x => ∫⁻ g in DH, f (x, (j g)⁻¹ * x) ∂ν
  have hK : Measurable K := by
    refine Measurable.lintegral_prod_right' (f := fun q : G × H => f (q.1, (j q.2)⁻¹ * q.1)) ?_
    exact hf.comp (by fun_prop)
  have h1 : ∀ x i, ∫⁻ g, f (x, j g * ((r i)⁻¹ * x)) ∂ν =
      ∑' δ : Γ, ∫⁻ g in DH, f (x, (j g)⁻¹ * (((e (i, δ) : Γ') : G)⁻¹ * x)) ∂ν := by
    intro x i
    rw [← lintegral_inv_eq_self (μ := ν) (fun g => f (x, j g * ((r i)⁻¹ * x))), hDH.lintegral_eq_tsum'']
    refine tsum_congr fun δ => lintegral_congr fun g => ?_
    simp [e, Subgroup.smul_def, mul_assoc]
  have h2 : ∀ x, ∑' i, ∫⁻ g, f (x, j g * ((r i)⁻¹ * x)) ∂ν = ∑' γ : Γ', K ((γ : G)⁻¹ * x) := by
    intro x
    simp_rw [h1]
    rw [← ENNReal.tsum_prod' (f := fun q : ι × Γ => ∫⁻ g in DH, f (x, (j g)⁻¹ * (((e q : Γ') : G)⁻¹ * x)) ∂ν),
      ← (Equiv.ofBijective e he).tsum_eq (fun γ : Γ' => K ((γ : G)⁻¹ * x))]
    refine tsum_congr fun q => lintegral_congr fun g => ?_
    have := hinv _ (Γ'.inv_mem (e q).2) x ((j g)⁻¹ * (((e q : Γ') : G)⁻¹ * x))
    simpa [K] using this.symm
  have hmeasL : Measurable fun q : (G × ι) × H => f (q.1.1, j q.2 * ((r q.1.2)⁻¹ * q.1.1)) :=
    hf.comp (by fun_prop)
  have hmeasR : Measurable fun p : G × ι => ∫⁻ g, f (p.1, j g * ((r p.2)⁻¹ * p.1)) ∂ν :=
    hmeasL.lintegral_prod_right'
  rw [lintegral_prod _ hmeasR.aemeasurable]
  simp_rw [lintegral_count]
  simp_rw [h2]
  rw [lintegral_tsum (f := fun (γ : Γ') x => K ((γ : G)⁻¹ * x))
    fun γ => (hK.comp (measurable_const_mul _)).aemeasurable]
  have h3 : ∫⁻ x, K x ∂μ = ∑' γ : Γ', ∫⁻ x in DG, K ((γ : G)⁻¹ * x) ∂μ := by
    rw [hDG.lintegral_eq_tsum' K]
    refine tsum_congr fun γ => lintegral_congr fun x => ?_
    simp [Subgroup.smul_def]
  rw [← h3]
  have hF : Measurable (Function.uncurry fun (x : G) (g : H) => f (x, (j g)⁻¹ * x)) :=
    hf.comp (by fun_prop)
  have hF' : Measurable (Function.uncurry fun (y : G) (g : H) => f (j g * y, y)) :=
    hf.comp (by fun_prop)
  rw [show ∫⁻ x, K x ∂μ = ∫⁻ g in DH, ∫⁻ x, f (x, (j g)⁻¹ * x) ∂μ ∂ν from
      lintegral_lintegral_swap hF.aemeasurable,
    lintegral_lintegral_swap hF'.aemeasurable]
  refine lintegral_congr fun g => ?_
  rw [← lintegral_mul_left_eq_self (fun x => f (x, (j g)⁻¹ * x)) (j g)]
  simp

theorem absUnf : AbsUnf := by
  intro G H ι _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ _ j Γ' Γ _ _ DG DH r φ c hj hinj hDG hDH hfin hr hjΓ hdec
    hφ hφinv hbd hc hci
  obtain ⟨B₀, hB₀⟩ := hbd
  have hjm : Measurable j := hj.measurable
  have hrm : Measurable r := Measurable.of_discrete
  have U := fun (f : G × G → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ γ ∈ Γ', ∀ x y, f (γ * x, y) = f (x, y)) =>
    unf μ ν j Γ' Γ DG DH r hj hinj hDG hDH hr hjΓ hdec f hf hinv
  refine ⟨fun B hB => ?_, ?_⟩
  · have hBe : ∀ x, ‖φ x‖ₑ ≤ ENNReal.ofReal B := fun x => by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hB x)
    calc ∫⁻ p : G × ι, ‖(∫ g, c (j g * ((r p.2)⁻¹ * p.1)) ∂ν) * φ p.1‖ₑ ∂((μ.restrict DG).prod Measure.count)
        ≤ ∫⁻ p : G × ι, ∫⁻ g, ‖c (j g * ((r p.2)⁻¹ * p.1)) * φ p.1‖ₑ ∂ν ∂((μ.restrict DG).prod Measure.count) := by
          refine lintegral_mono fun p => ?_
          rw [← integral_mul_const]
          exact enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y, ∫⁻ g in DH, ‖c y * φ (j g * y)‖ₑ ∂ν ∂μ :=
          U (fun q => ‖c q.2 * φ q.1‖ₑ) (by fun_prop) (fun γ hγ x y => by simp only [hφinv γ hγ x])
      _ ≤ ∫⁻ y, ∫⁻ g in DH, ‖c y‖ₑ * ENNReal.ofReal B ∂ν ∂μ := by
          refine lintegral_mono fun y => lintegral_mono fun g => ?_
          rw [enorm_mul]
          gcongr
          exact hBe _
      _ = ENNReal.ofReal B * ν DH * ∫⁻ y, ‖c y‖ₑ ∂μ := by
          simp_rw [setLIntegral_const, mul_assoc]
          rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne), mul_comm, mul_assoc]
  · let P₁ : Measure ((G × ι) × H) := ((μ.restrict DG).prod Measure.count).prod ν
    let P₂ : Measure (G × H) := μ.prod (ν.restrict DH)
    let T₁ : (G × ι) × H → ℂ × G := fun q => (φ q.1.1, j q.2 * ((r q.1.2)⁻¹ * q.1.1))
    let T₂ : G × H → ℂ × G := fun q => (φ (j q.2 * q.1), q.1)
    have hT₁ : Measurable T₁ := by fun_prop
    have hT₂ : Measurable T₂ := by fun_prop
    have hmap : P₁.map T₁ = P₂.map T₂ := by
      ext S hS
      rw [← lintegral_indicator_one hS, ← lintegral_indicator_one hS, lintegral_map (measurable_one.indicator hS) hT₁,
        lintegral_map (measurable_one.indicator hS) hT₂]
      have hm : Measurable (S.indicator (1 : ℂ × G → ℝ≥0∞)) := measurable_one.indicator hS
      have hu := U (fun q => S.indicator (1 : ℂ × G → ℝ≥0∞) (φ q.1, q.2)) (hm.comp (by fun_prop))
        (fun γ hγ x y => by simp only [hφinv γ hγ x])
      have e₁ : ∫⁻ a, S.indicator (1 : ℂ × G → ℝ≥0∞) (T₁ a) ∂P₁ =
          ∫⁻ p, ∫⁻ g, S.indicator (1 : ℂ × G → ℝ≥0∞) (T₁ (p, g)) ∂ν ∂((μ.restrict DG).prod Measure.count) :=
        lintegral_prod _ (hm.comp hT₁).aemeasurable
      have e₂ : ∫⁻ a, S.indicator (1 : ℂ × G → ℝ≥0∞) (T₂ a) ∂P₂ =
          ∫⁻ y, ∫⁻ g in DH, S.indicator (1 : ℂ × G → ℝ≥0∞) (T₂ (y, g)) ∂ν ∂μ :=
        lintegral_prod _ (hm.comp hT₂).aemeasurable
      rw [e₁, e₂]
      exact hu
    let h : ℂ × G → ℂ := fun w => c w.2 * w.1
    have hh : Measurable h := by fun_prop
    haveI : IsFiniteMeasure (ν.restrict DH) := ⟨by simpa using hfin⟩
    have hI₂ : Integrable (h ∘ T₂) P₂ := by
      refine ((hci.comp_fst (ν.restrict DH)).norm.mul_const B₀).mono' (hh.comp hT₂).aestronglyMeasurable
        (ae_of_all _ fun q => ?_)
      simp only [h, T₂, Function.comp, norm_mul, norm_norm]
      gcongr
      exact hB₀ _
    have hI : Integrable h (P₂.map T₂) :=
      (integrable_map_measure hh.aestronglyMeasurable hT₂.aemeasurable).2 hI₂
    have hI₁ : Integrable (h ∘ T₁) P₁ :=
      (integrable_map_measure hh.aestronglyMeasurable hT₁.aemeasurable).1 (hmap ▸ hI)
    calc ∫ p : G × ι, (∫ g, c (j g * ((r p.2)⁻¹ * p.1)) ∂ν) * φ p.1 ∂((μ.restrict DG).prod Measure.count)
        = ∫ p : G × ι, ∫ g, (h ∘ T₁) (p, g) ∂ν ∂((μ.restrict DG).prod Measure.count) := by
          refine integral_congr_ae (ae_of_all _ fun p => ?_)
          simp only [h, T₁, Function.comp]
          rw [integral_mul_const]
      _ = ∫ q, (h ∘ T₁) q ∂P₁ := (integral_prod _ hI₁).symm
      _ = ∫ w, h w ∂(P₁.map T₁) := (integral_map hT₁.aemeasurable hh.aestronglyMeasurable).symm
      _ = ∫ w, h w ∂(P₂.map T₂) := by rw [hmap]
      _ = ∫ q, (h ∘ T₂) q ∂P₂ := integral_map hT₂.aemeasurable hh.aestronglyMeasurable
      _ = ∫ y, ∫ g in DH, (h ∘ T₂) (y, g) ∂ν ∂μ := integral_prod _ hI₂
      _ = ∫ y, c y * ∫ g in DH, φ (j g * y) ∂ν ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          simp only [h, T₂, Function.comp]
          rw [integral_const_mul]

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.BddE
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical Pointwise

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.bddE :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.BddE := by
  intro E _ _ _ P φ hφ C hC
  obtain ⟨c, C₀, hc, hC₀, hred⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.redE E
  have hC' : IsCompact ((gl (F := E) '' C₀) * C) := (hC₀.image continuous_gl).mul hC
  obtain ⟨hL, -, hd⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.decE E P φ hφ
  obtain ⟨B, hB⟩ := hd _ hC' c hc 0
  refine ⟨B, fun h k hk => ?_⟩
  obtain ⟨γ, u, b, k₀, hk₀, hg, hb⟩ := hred h
  have e1 : φ.1 (gl h * k) = φ.1 (gl (nU u * mD b) * (gl k₀ * k)) := by
    rw [← mul_assoc, ← gl_mul, ← hg, gl_mul, gl_ratS, mul_assoc, hL.2]
  have h1 := hB u b (gl k₀ * k) (Set.mul_mem_mul ⟨k₀, hk₀, rfl⟩ hk) hb
  rw [e1]
  simpa using h1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.ExistsForm0
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent

noncomputable section

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

private theorem exists_form0 {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    {v : LL μ} (hv : v ∈ cuspidalL2 μ) (h0 : v ≠ 0) :
    ∃ V, IsSummand μ V ∧ ∃ f ∈ formsIn μ V, inner ℂ v (clsL μ f) ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 : (⨆ V : {V // IsSummand μ V}, V.1) ≤ (ℂ ∙ v)ᗮ := iSup_le fun V => by
    rw [← (formsIrr K n μ V.1 V.2).2.2.2]
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rintro _ ⟨f, hf, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 (hc _ V.2 f hf)
  have h2 := Submodule.topologicalClosure_minimal _ h1 (Submodule.isClosed_orthogonal _)
  rw [summandsSpan K n μ] at h2
  exact h0 (inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (h2 hv)))

private theorem oneInt (f : (AutomorphicForm.UPos 2 1 → A ℚ) → ℂ) :
    ∫ y in GroundTheory.Global.fundamentalSet ℚ, f (fun _ => y) ∂GroundTheory.Global.adeleMeasure ℚ =
      ∫ Y in unipFundamentalDomain ℚ 2 1, f Y ∂unipMeasure ℚ 2 1 := by
  let _ : Unique (AutomorphicForm.UPos 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩
  have hm : MeasurePreserving (MeasurableEquiv.funUnique (AutomorphicForm.UPos 2 1) (A ℚ)) (unipMeasure ℚ 2 1)
      (GroundTheory.Global.adeleMeasure ℚ) := by
    convert measurePreserving_funUnique (GroundTheory.Global.adeleMeasure ℚ) (AutomorphicForm.UPos 2 1)
  rw [← hm.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _)]
  congr 1
  · congr 1
    ext Y
    simp [unipFundamentalDomain, Unique.forall_iff]
  · funext Y
    congr 1
    funext p
    simp [Subsingleton.elim p default]

private theorem unip_eq (y : A ℚ) : (unipGL (fun _ : AutomorphicForm.UPos 2 1 => y) : GL (Fin 2) (A ℚ)) = gl (nU y) := by
  ext i j
  change unipMatrix (fun _ : AutomorphicForm.UPos 2 1 => y) i j = (!![1, y; 0, 1] : Matrix (Fin 2) (Fin 2) (A ℚ)) i j
  fin_cases i <;> fin_cases j <;> simp [unipMatrix, blockEntry_apply]

private theorem cusp_conj {F : GL (Fin 2) (A ℚ) → ℂ}
    (h : ∀ x, ∫ b in GroundTheory.Global.fundamentalSet ℚ, F (gl (nU b) * x) ∂(GroundTheory.Global.adeleMeasure ℚ) = 0) :
    IsCuspidal (fun x : AdelicGLn.AdelicGL ℚ 2 => starRingEnd ℂ (F x)) := by
  intro r hr hr2 g
  obtain rfl : r = 1 := by omega
  rw [constantTerm, ← oneInt (fun X => starRingEnd ℂ (F (unipGL X * g)))]
  simp only [unip_eq]
  rw [integral_conj, h g, map_zero]

private theorem exists_one {F : GL (Fin 2) (A ℚ) → ℂ} (hF : Bd F) (h0 : F ≠ 0) :
    ∃ x : normOneGL (K := ℚ) (n := 2), F (x : AdelicGLn.AdelicGL ℚ 2) ≠ 0 := by
  obtain ⟨g, hg⟩ := Function.ne_iff.1 h0
  refine ⟨retractOne g, ?_⟩
  rw [coe_retractOne, ← centralSection_inv_mul_comm, ← map_inv, hF.cen]
  exact hg

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

open UpperTheory.ConvolutionTheory.RankTwoDescent.Cp in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.pairL : UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.PairL := by
  intro μ _ F hF hne hct
  have hfin := Reduction.isFiniteMeasure_quotientMeasure (K := ℚ) (n := 2) μ
  set ψ : AdelicGLn.AdelicGL ℚ 2 → ℂ := fun x => starRingEnd ℂ (F x) with hψdef
  have hψc : Continuous ψ := continuous_star.comp hF.cont
  have hψl : IsLeftInvariant ψ := fun γ g => congrArg (starRingEnd ℂ) (hF.left γ g)
  obtain ⟨C, hC⟩ := hF.bdd
  have hbd : ∃ C, ∀ g ∈ normOneGL (K := ℚ) (n := 2), ‖ψ g‖ ≤ C := ⟨C, fun g _ => by simpa [hψdef] using hC g⟩
  have hm := GJGlobal.memLp_cuspQuot_of_bounded μ hψc hψl hbd
  have hv : hm.toLp _ ∈ cuspidalL2 μ := GJGlobal.toLp_cuspQuot_mem_cuspidalL2 μ hψc hψl (cusp_conj hct) hbd
  have hv0 : hm.toLp _ ≠ 0 := fun h => by
    obtain ⟨x, hx⟩ := exists_one hF hne
    have h1 : cuspQuot hψl =ᵐ[quotientMeasure (rationalGLOne (K := ℚ) (n := 2)) μ] 0 := by
      refine (MemLp.coeFn_toLp hm).symm.trans ?_
      rw [h]
      exact Lp.coeFn_zero _ _ _
    have h2 : (fun y : normOneGL (K := ℚ) (n := 2) => ψ y) =ᵐ[μ] 0 :=
      QuasiMeasurePreserving.ae_eq_comp (quasiMeasurePreserving_mk _ μ) h1
    have h3 : starRingEnd ℂ (F (x : AdelicGLn.AdelicGL ℚ 2)) = 0 :=
      congrFun ((Continuous.ae_eq_iff_eq μ (hψc.comp continuous_subtype_val) continuous_const).1 h2) x
    exact hx ((map_eq_zero _).1 h3)
  obtain ⟨V, hV, f, hf, hi⟩ := exists_form0 μ hv hv0
  obtain ⟨hs, hne, hirr, -⟩ := formsIrr ℚ 2 μ V hV
  have hiπ := hs.isIrreducible_iff.2 ⟨hne, hirr⟩
  let π := Fb.ofIrr (formsIn μ V) hs hiπ
  have hπ : Fb.carrier π = formsIn μ V := Fb.carrier_ofIrr _ hs hiπ
  have hfπ : f ∈ Fb.carrier π := by rwa [hπ]
  refine ⟨π, ?_, Fb.ofCusp ℚ 2 f, Fb.mem_carrier.1 hfπ, fun hz => hi ?_⟩
  · intro φ hφ s g
    rw [← Fb.map_carrier π, hπ] at hφ
    obtain ⟨ψ', hψ', rfl⟩ := hφ
    exact hψ'.1 s g
  · rw [L2.inner_def, ← hz]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hm, (clsBasic ℚ 2 μ).2.2.2 f hf.1] with q e1 e2
    rw [e1, e2, RCLike.inner_apply]
    have e3 : cuspQuot hψl q = ψ (Quotient.out q : normOneGL (K := ℚ) (n := 2)) := by
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    rw [e3]
    simp [hψdef, Fb.ofCusp]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.FormBd
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private theorem dM_fin (t : (A ℚ)ˣ) (ht : (t : A ℚ).1 = 1) :
    finGL ℚ 2 (Matrix.GeneralLinearGroup.map (pFin ℚ) (dM t)) = dM t := by
  have h := TR.infGL_mul_finGL (dM t)
  have h1 : Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (dM t) = 1 := by
    have ht' : TR.pInf ℚ (t : A ℚ) = 1 := by
      change (TR.infEq ℚ).symm (t : A ℚ).1 = 1
      rw [ht]; exact map_one _
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ht']
  rw [h1, map_one, one_mul] at h
  exact h

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.formBd :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.FormBd := by
  intro π hπ f hf
  have hL := (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero ℚ π f hf).1
  refine ⟨⟨hL.1, hL.2, ?_, fun s x => hπ f hf s x⟩, fun t ht => ?_⟩
  · obtain ⟨φ, hφ⟩ := LinearMap.mem_range.mp (Fb.mem_range_ofCusp.2 (π.cusp f hf))
    obtain ⟨B₀, hB₀⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms φ.2
    subst hφ
    refine ⟨B₀, fun x => ?_⟩
    have h2 : (centralSection ℚ 2 (detModule ℚ 2 x))⁻¹ * x ∈ normOneGL (K := ℚ) (n := 2) := by
      rw [mem_normOneGL_iff_detModule, map_mul, map_inv, detModule_centralSection two_pos, inv_mul_cancel]
    have h3 := hπ _ hf (detModule ℚ 2 x) ((centralSection ℚ 2 (detModule ℚ 2 x))⁻¹ * x)
    rw [mul_inv_cancel_left] at h3
    rw [h3]
    exact hB₀ _ h2
  · have h := π.stable (.fin (Matrix.GeneralLinearGroup.map (pFin ℚ) (dM t))) f hf
    refine ⟨_, h, fun x => ?_⟩
    change f.1 (x * finGL ℚ 2 (Matrix.GeneralLinearGroup.map (pFin ℚ) (dM t))) = _
    rw [dM_fin t ht.1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.QuadraticFormRationalPoints
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

variable {E : Type} [Field E] [NumberField E]

private theorem rp_injective : Function.Injective (rp : (Fin 4 → ℚ) → V4 ℚ) := by
  intro ξ ξ' h
  funext i
  exact AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ (congrFun h i)

private theorem quadraticForm_rational_points (δ : ℚ) (ξ : Fin 4 → ℚ) : q4 δ (rp ξ) = rt (qr δ ξ) := by
  simp [q4, qr, rp, map_sub, map_mul, map_pow]


variable (E) in
private noncomputable def jE : G1 ℚ →* G1 E := Matrix.SpecialLinearGroup.map (am E)

private theorem gl_jE (g : G1 ℚ) : gl (jE E g) = em E (gl g) := by
  apply Units.ext
  ext i j
  rfl

private theorem continuous_jE : Continuous (jE E) := by
  have h : Continuous fun g : G1 ℚ => (g.1).map (am E) :=
    continuous_subtype_val.matrix_map continuous_am
  exact h.subtype_mk _

private theorem injective_jE : Function.Injective (jE E) := by
  intro g g' h
  apply Subtype.ext
  ext i j
  exact am_injective (E := E) (congrFun (congrFun (congrArg Subtype.val h) i) j)

private theorem jE_ratS (g : Matrix.SpecialLinearGroup (Fin 2) ℚ) :
    jE E (ratS ℚ g) = ratS E (Matrix.SpecialLinearGroup.map (algebraMap ℚ E) g) := by
  apply Subtype.ext
  ext i j
  exact am_rt (g i j)

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

open UpperTheory.ConvolutionTheory.RankTwoDescent.Cp in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.reps :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Reps := by
  intro E _ _ _ D
  obtain ⟨h1, h2, h3⟩ := orbS E D
  obtain ⟨ρ1, -⟩ := orb1 E D
  choose γ hγ using fun i : Orb D.δ => h1 i.1 i.2
  refine ⟨jE E, fun i => ratS E (γ i), gl_jE, continuous_jE, injective_jE,
    fun i => ⟨⟨γ i, rfl⟩, hγ i⟩, ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨_, (jE_ratS g).symm⟩
  · rintro _ ⟨c, rfl⟩
    obtain ⟨ρ, hρ⟩ := ρ1 c
    have hq : qr D.δ (ρ X0) = qr D.δ X0 := by
      apply AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ
      change UpperTheory.ConvolutionTheory.R2.rt _ = UpperTheory.ConvolutionTheory.R2.rt _
      rw [← quadraticForm_rational_points, ← quadraticForm_rational_points, ← hρ, D.quadForm_act, nu_gl]
      simp
    let i : Orb D.δ := ⟨ρ X0, hq⟩
    have hi : rp i.1 = D.act (gl (ratS E c)) (rp X0) := (hρ X0).symm
    have hfix : ∀ x : G1 ℚ, D.act (gl (jE E x)) (rp X0) = rp X0 := fun x =>
      (h2 (jE E x)).2 ⟨x, gl_jE x⟩
    have hstab : D.act (gl (ratS E ((γ i)⁻¹ * c))) (rp X0) = rp X0 := by
      have e : ratS E ((γ i)⁻¹ * c) = (ratS E (γ i))⁻¹ * ratS E c := by rw [map_mul, map_inv]
      rw [e, gl_mul, gl_inv, D.act_mul, ← hi, hγ i, D.act_inv_act]
    obtain ⟨g, hg⟩ := (h3 _).1 hstab
    have hj : ratS E ((γ i)⁻¹ * c) = jE E (ratS ℚ g) := gl_injective (hg.trans (gl_jE _).symm)
    refine ⟨i, ⟨ratS ℚ g, ⟨g, rfl⟩, ?_⟩, ?_⟩
    · rw [← hj, map_mul, map_inv, mul_inv_cancel_left]
    · rintro i' ⟨_, ⟨g', rfl⟩, hi'⟩
      apply Subtype.ext
      apply rp_injective
      rw [hγ i', hi, hi', gl_mul, D.act_mul, hfix]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.ZDom
section
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.zDom :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.ZDom := by
  intro E _ _
  refine ⟨normOneMeasure_normOneFundamentalDomain_lt_top E,
    measurableSet_normOneFundamentalDomain E, ?_⟩
  have hc : Continuous (fun z : ↥(IdeleGroup.normOneSubgroup E) =>
      ((z : IdeleGroup E) : (A E)ˣ)) := continuous_subtype_val
  refine ⟨_, (isCompact_closure_normOneFundamentalDomain E).image hc, ?_⟩
  intro z hz
  exact ⟨z, subset_closure hz, rfl⟩
end

