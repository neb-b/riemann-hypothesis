module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
public import GroundTheory.AutomorphicForms.CompactFormulaCountable
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0001
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MatchOne
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem haar_ex {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] {K : Set G} (hc : IsCompact K) (ho : IsOpen K) (h1 : (1 : G) ∈ K) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m K = 1 := by
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨K, hc⟩, by
    show (interior K).Nonempty
    rw [ho.interior_eq]; exact ⟨1, h1⟩⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self (K₀ := K₀)⟩

private theorem haar_uniq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {K : Set G} {m m' : Measure G}
    (hm : m.IsHaarMeasure) (hm' : m'.IsHaarMeasure) (h : m K = 1) (h' : m' K = 1) : m = m' := by
  have e := Measure.isMulLeftInvariant_eq_smul m m'
  have e2 : m K = (Measure.haarScalarFactor m m' • m') K := by rw [← e]
  rw [h, Measure.smul_apply, h', ENNReal.smul_def, smul_eq_mul, mul_one] at e2
  have e3 : Measure.haarScalarFactor m m' = 1 := by exact_mod_cast e2.symm
  rw [e3, one_smul] at e
  exact e

private theorem gl_top (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [LocallyCompactSpace R] [SecondCountableTopology R] (n : ℕ) :
    LocallyCompactSpace (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact ⟨inferInstance, Units.isEmbedding_embedProduct.secondCountableTopology⟩

private theorem gl_int {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] (n : ℕ)
    (O : Subring R) (hc : IsCompact (O : Set R)) (ho : IsOpen (O : Set R)) :
    IsCompact {g : GL (Fin n) R | (∀ i j, g i j ∈ O) ∧ ∀ i j, (g⁻¹ : GL (Fin n) R) i j ∈ O} ∧
    IsOpen {g : GL (Fin n) R | (∀ i j, g i j ∈ O) ∧ ∀ i j, (g⁻¹ : GL (Fin n) R) i j ∈ O} := by
  let S : Subring (Matrix (Fin n) (Fin n) R) := (RingHom.mapMatrix O.subtype).range
  have hS : ∀ A : Matrix (Fin n) (Fin n) R, A ∈ S ↔ ∀ i j, A i j ∈ O := by
    intro A
    constructor
    · rintro ⟨B, rfl⟩ i j
      exact (B i j).2
    · intro h
      exact ⟨Matrix.of fun i j => ⟨A i j, h i j⟩, rfl⟩
  constructor
  · have e : {g : GL (Fin n) R | (∀ i j, g i j ∈ O) ∧ ∀ i j, (g⁻¹ : GL (Fin n) R) i j ∈ O} =
        (S.toSubmonoid.units : Set (GL (Fin n) R)) := by
      ext g
      rw [SetLike.mem_coe, Submonoid.mem_units_iff, Subring.mem_toSubmonoid, Subring.mem_toSubmonoid, hS, hS]
      rfl
    rw [e]
    apply Submonoid.units_isCompact
    have : (S.toSubmonoid : Set (Matrix (Fin n) (Fin n) R)) =
        Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (O : Set R) := by
      ext A
      change A ∈ S ↔ ∀ i ∈ Set.univ, ∀ j ∈ Set.univ, A i j ∈ (O : Set R)
      rw [hS]
      simp
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc
  · simp only [Set.setOf_and, Set.setOf_forall]
    refine IsOpen.inter ?_ ?_
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage (Units.continuous_val.matrix_elem i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage ((Units.continuous_val.matrix_elem i j).comp continuous_inv)

open ValuativeRel in
private theorem unitSet_top {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : Pl F) :
    IsCompact (unitSet E n v) ∧ IsOpen (unitSet E n v) ∧ (1 : GL (Fin n) (CompletionsOver E v)) ∈ unitSet E n v := by
  let O : Subring (CompletionsOver E v) :=
    ⨅ w : PlacesOver E v, (𝒪[w.1.adicCompletion E]).comap
      (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)
  have hO : (O : Set (CompletionsOver E v)) =
      Set.pi Set.univ fun w : PlacesOver E v => (𝒪[w.1.adicCompletion E] : Set (w.1.adicCompletion E)) := by
    ext x
    simp [O, Subring.mem_iInf]
  have hc : IsCompact (O : Set (CompletionsOver E v)) := by
    rw [hO]
    exact isCompact_univ_pi fun w => isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[w.1.adicCompletion E]))
  have ho : IsOpen (O : Set (CompletionsOver E v)) := by
    rw [hO]
    exact isOpen_set_pi Set.finite_univ fun w _ => Valuation.isOpen_integer
  have e : unitSet E n v = {g : GL (Fin n) (CompletionsOver E v) | (∀ i j, g i j ∈ O) ∧
      ∀ i j, (g⁻¹ : GL (Fin n) (CompletionsOver E v)) i j ∈ O} := by
    ext g
    simp only [unitSet, Set.mem_setOf_eq, GLnLocal.mem_integralGL_iff, ← map_inv, O, Subring.mem_iInf, Subring.mem_comap]
    exact ⟨fun h => ⟨fun i j w => (h w).1 i j, fun i j w => (h w).2 i j⟩,
      fun h w => ⟨fun i j => h.1 i j w, fun i j => h.2 i j w⟩⟩
  refine ⟨e ▸ (gl_int n O hc ho).1, e ▸ (gl_int n O hc ho).2, fun w => ?_⟩
  rw [map_one]
  exact one_mem _

theorem UpperTheory.ConvolutionTheory.GM.matchOne :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (v : Pl F),
    (∃ (_ : MeasurableSpace (GL (Fin n) (CompletionsOver E v))) (_ : BorelSpace (GL (Fin n) (CompletionsOver E v)))
      (_ : MeasurableSpace (GL (Fin n) (v.adicCompletion F))) (_ : BorelSpace (GL (Fin n) (v.adicCompletion F)))
      (mE : Measure (GL (Fin n) (CompletionsOver E v))) (mF : Measure (GL (Fin n) (v.adicCompletion F))),
      mE.IsHaarMeasure ∧ mF.IsHaarMeasure ∧ mE (unitSet E n v) = 1 ∧ mF (GLnLocal.integralGL (v.adicCompletion F) n) = 1) ∧
    ∀ [MeasurableSpace (GL (Fin n) (CompletionsOver E v))] [BorelSpace (GL (Fin n) (CompletionsOver E v))]
      [MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [BorelSpace (GL (Fin n) (v.adicCompletion F))]
      (mE : Measure (GL (Fin n) (CompletionsOver E v))) (mF : Measure (GL (Fin n) (v.adicCompletion F))),
      mE.IsHaarMeasure → mF.IsHaarMeasure → mE (unitSet E n v) = 1 → mF (GLnLocal.integralGL (v.adicCompletion F) n) = 1 →
      ∀ (c : ℂ) (φ : GL (Fin n) (CompletionsOver E v) → ℂ) (f : GL (Fin n) (v.adicCompletion F) → ℂ),
      Match (incFin E v) (galFin σ v) (Module.finrank F E) mE mF c φ f → MatchAt σ v c φ f := by
  intro F E _ _ _ _ _ σ n v
  obtain ⟨lE, sE⟩ := gl_top (CompletionsOver E v) n
  obtain ⟨lF, sF⟩ := gl_top (v.adicCompletion F) n
  obtain ⟨hc, ho, h1⟩ := unitSet_top (E := E) n v
  constructor
  · borelize (GL (Fin n) (CompletionsOver E v))
    borelize (GL (Fin n) (v.adicCompletion F))
    obtain ⟨mE, hE, hE1⟩ := haar_ex hc ho h1
    obtain ⟨mF, hF, hF1⟩ := haar_ex (GLnLocal.isCompact_integralGL (v.adicCompletion F) n)
      (GLnLocal.isOpen_integralGL (v.adicCompletion F) n) (one_mem _)
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, mE, mF, hE, hF, hE1, hF1⟩
  · intro aE bE aF bF mE mF hE hF hE1 hF1 c φ f hM aE' bE' aF' bF' mE' mF' hE' hF' hE1' hF1'
    obtain rfl : aE = aE' := bE.measurable_eq.trans bE'.measurable_eq.symm
    obtain rfl : aF = aF' := bF.measurable_eq.trans bF'.measurable_eq.symm
    obtain rfl : mE = mE' := haar_uniq hE hE' hE1 hE1'
    obtain rfl : mF = mF' := haar_uniq hF hF' hF1 hF1'
    exact hM
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.StepFin
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private noncomputable def trCc {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (h : G)
    (β : CompactlySupportedContinuousMap G ℂ) : CompactlySupportedContinuousMap G ℂ where
  toFun x := β (h⁻¹ * x)
  continuous_toFun := β.continuous.comp (continuous_const_mul h⁻¹)
  hasCompactSupport' := by
    refine HasCompactSupport.intro (β.hasCompactSupport.isCompact.image (continuous_const_mul h))
      fun x hx => ?_
    by_contra hne
    exact hx ⟨h⁻¹ * x, subset_tsupport _ hne, by simp⟩

private theorem map_integrated_trCc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts ν] (π : UnitaryRep G H) (h : G)
    (β : CompactlySupportedContinuousMap G ℂ) (v : H) :
    π h (π.integrated ν (UnitaryRep.ccToL1 ν β) v) =
      π.integrated ν (UnitaryRep.ccToL1 ν (trCc h β)) v := by
  have e := π.map_comp_integrated ν h (UnitaryRep.ccToL1 ν β)
  have e2 : UnitaryRep.leftTranslate ν h (UnitaryRep.ccToL1 ν β) =
      UnitaryRep.ccToL1 ν (trCc h β) := by
    refine Lp.ext ?_
    have hc := (β.continuous.memLp_of_hasCompactSupport (μ := ν) (p := 1) β.hasCompactSupport).coeFn_toLp
    have hc' := ((trCc h β).continuous.memLp_of_hasCompactSupport (μ := ν) (p := 1)
      (trCc h β).hasCompactSupport).coeFn_toLp
    filter_upwards [UnitaryRep.coeFn_leftTranslate ν h (UnitaryRep.ccToL1 ν β), hc',
      (measurePreserving_mul_left ν h⁻¹).quasiMeasurePreserving.ae_eq_comp hc] with x h1 h2 h3
    rw [h1]
    change (UnitaryRep.ccToL1 ν β : G → ℂ) (h⁻¹ * x) = (UnitaryRep.ccToL1 ν (trCc h β)) x
    rw [show (UnitaryRep.ccToL1 ν β : G → ℂ) (h⁻¹ * x) = β (h⁻¹ * x) from h3,
      show (UnitaryRep.ccToL1 ν (trCc h β) : G → ℂ) x = trCc h β x from h2]
    rfl
  rw [e2] at e
  exact congrArg (fun A : H →L[ℂ] H => A v) e

private theorem ccToL1_smul {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (a : ℂ) (f : CompactlySupportedContinuousMap G ℂ) :
    UnitaryRep.ccToL1 ν (a • f) = a • UnitaryRep.ccToL1 ν f := by
  unfold UnitaryRep.ccToL1
  rw [← MemLp.toLp_const_smul]
  rfl

private theorem ccToL1_finsetSum {G ι : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (s : Finset ι) (f : ι → CompactlySupportedContinuousMap G ℂ) :
    UnitaryRep.ccToL1 ν (∑ i ∈ s, f i) = ∑ i ∈ s, UnitaryRep.ccToL1 ν (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    unfold UnitaryRep.ccToL1
    exact MemLp.toLp_zero _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    unfold UnitaryRep.ccToL1
    rw [← MemLp.toLp_add]
    rfl

private theorem integrated_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {G ι : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (π : UnitaryRep G H) (s : Finset ι) (a : ι → ℂ)
    (f : ι → CompactlySupportedContinuousMap G ℂ) :
    π.integrated ν (UnitaryRep.ccToL1 ν (∑ i ∈ s, a i • f i)) = ∑ i ∈ s, a i • π.integrated ν (UnitaryRep.ccToL1 ν (f i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ccToL1_finsetSum, map_sum]
  simp only [ccToL1_smul, map_smul]

private theorem Ofin_sum {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] {ι : Type*} (s : Finset ι) (a : ι → ℂ) (f : ι → TF K n) :
    Ofin μ m (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i • Ofin μ m (f i) :=
  integrated_sum m ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj) s a f

private theorem rhoF_comp_Ofin {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (y : AdelicGLn.FiniteAdelicGL K n) (e : TF K n) :
    rhoF μ y ∘L Ofin μ m e = Ofin μ m (trCc y e) := by
  refine ContinuousLinearMap.ext fun v => ?_
  exact map_integrated_trCc m
    ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj) y e v

private theorem cf_local {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (y : GL (Fin n) (w.adicCompletion K))
    (x : AdelicGLn.FiniteAdelicGL K n) : cf w (AdelicGLn.localEmbedding w y * x) = y * cf w x := by
  unfold cf
  rw [map_mul, finAt_mul, (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.1]

private theorem exists_cover {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G)
    (hJ : IsOpen (J : Set G)) (h : G → ℂ) (hc : HasCompactSupport h) :
    ∃ t : Finset (G ⧸ J), ∀ y, h y ≠ 0 → (QuotientGroup.mk y : G ⧸ J) ∈ t := by
  have hop : ∀ c : G ⧸ J, IsOpen ((QuotientGroup.mk : G → G ⧸ J) ⁻¹' {c}) := fun c => by
    have : (QuotientGroup.mk : G → G ⧸ J) ⁻¹' {c} = (fun g => c.out⁻¹ * g) ⁻¹' (J : Set G) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      exact eq_comm
    rw [this]
    exact hJ.preimage (continuous_const_mul _)
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover _ hop fun y _ =>
    Set.mem_iUnion.2 ⟨QuotientGroup.mk y, rfl⟩
  refine ⟨t, fun y hy => ?_⟩
  obtain ⟨c, hc', hyc⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport _ hy))
  rw [show (QuotientGroup.mk y : G ⧸ J) = c from hyc]
  exact hc'

private theorem coset_sum {G : Type*} [Group G] (J : Subgroup G) (h : G → ℂ) (hinv : ∀ k ∈ J, ∀ x, h (x * k) = h x)
    (t : Finset (G ⧸ J)) (ht : ∀ y, h y ≠ 0 → (QuotientGroup.mk y : G ⧸ J) ∈ t) (y : G) :
    ∑ c ∈ t, h c.out * (J : Set G).indicator (1 : G → ℂ) (c.out⁻¹ * y) = h y := by
  classical
  have hind : ∀ c : G ⧸ J, (J : Set G).indicator (1 : G → ℂ) (c.out⁻¹ * y) = if (QuotientGroup.mk y : G ⧸ J) = c then 1 else 0 := fun c => by
    have : c.out⁻¹ * y ∈ (J : Set G) ↔ (QuotientGroup.mk y : G ⧸ J) = c := by
      rw [SetLike.mem_coe, ← QuotientGroup.eq, QuotientGroup.out_eq']
      exact eq_comm
    by_cases hh : (QuotientGroup.mk y : G ⧸ J) = c
    · rw [if_pos hh, Set.indicator_of_mem (this.2 hh)]; rfl
    · rw [if_neg hh, Set.indicator_of_notMem (fun q => hh (this.1 q))]
  have hout : h (QuotientGroup.mk y : G ⧸ J).out = h y := by
    have hk : (QuotientGroup.mk y : G ⧸ J).out⁻¹ * y ∈ J := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    have := hinv _ hk (QuotientGroup.mk y : G ⧸ J).out
    rw [mul_inv_cancel_left] at this
    exact this.symm
  simp only [hind, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hm
  · exact hout
  · by_contra hne
    exact hm (ht y (Ne.symm hne))

theorem UpperTheory.ConvolutionTheory.GM.stepFin :
    StepFin := by
  intro K _ _ n hn μ _ m _ w J hJ h hc hinv r hr e₀ e₁ h0 h1
  have htr : ∀ (y : GL (Fin n) (w.adicCompletion K)) x,
      trCc (AdelicGLn.localEmbedding w y) e₀ x =
        r x * (J : Set _).indicator 1 (y⁻¹ * cf w x) := fun y x => by
    show e₀ ((AdelicGLn.localEmbedding w y)⁻¹ * x) = _
    rw [h0, ← map_inv, hr, cf_local]
  refine ⟨fun u => ?_, ?_⟩
  · refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 _).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have e : trCc (AdelicGLn.localEmbedding w k) e₀ = e₀ := by
      ext x
      rw [htr, h0]
      congr 1
      by_cases hx : cf w x ∈ (J : Set _)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (J.mul_mem (J.inv_mem hk) hx)]; rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
        intro q
        exact hx (by simpa using J.mul_mem hk q)
    have := congrArg (fun A : LL μ →L[ℂ] LL μ => A u) (rhoF_comp_Ofin μ m (AdelicGLn.localEmbedding w k) e₀)
    simpa [e] using this
  · obtain ⟨t, ht⟩ := exists_cover J hJ h hc
    have hfs : (∑ᶠ c : GL (Fin n) (w.adicCompletion K) ⧸ J, h c.out • rhoL μ w c.out) = ∑ c ∈ t, h c.out • rhoL μ w c.out := by
      refine finsum_eq_sum_of_support_subset _ fun c hc' => ?_
      have hne : h c.out ≠ 0 := fun q => hc' (by simp [q])
      have := ht _ hne
      rwa [QuotientGroup.out_eq'] at this
    have he : e₁ = ∑ c ∈ t, h c.out • trCc (AdelicGLn.localEmbedding w c.out) e₀ := by
      ext x
      rw [h1, CompactlySupportedContinuousMap.sum_apply]
      simp only [CompactlySupportedContinuousMap.smul_apply, htr, smul_eq_mul]
      rw [← coset_sum J h hinv t ht (cf w x), Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [hfs, he]
    rw [Ofin_sum]
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← rhoF_comp_Ofin]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.SumSmulApply
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

namespace UpperTheory.ConvolutionTheory.GM

section

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]

private theorem sum_smul_apply {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → TG K n) (g : normOneGL (K := K) (n := n)) :
    (∑ i ∈ s, c i • f i) g = ∑ i ∈ s, c i * f i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, CompactlySupportedContinuousMap.add_apply, ih]
    simp

private theorem rop_add (a b : TG K n) : Rop μ (a + b) = Rop μ a + Rop μ b := by
  have h : UnitaryRep.ccToL1 μ (a + b) = UnitaryRep.ccToL1 μ a + UnitaryRep.ccToL1 μ b := by
    unfold UnitaryRep.ccToL1
    rw [← MemLp.toLp_add]
    rfl
  unfold Rop
  rw [h]
  exact ContinuousLinearMap.map_add _ _ _

private theorem rop_smul (c : ℂ) (a : TG K n) : Rop μ (c • a) = c • Rop μ a := by
  have h : UnitaryRep.ccToL1 μ (c • a) = c • UnitaryRep.ccToL1 μ a := by
    unfold UnitaryRep.ccToL1
    rw [← MemLp.toLp_const_smul]
    rfl
  unfold Rop
  rw [h]
  exact ContinuousLinearMap.map_smul _ _ _

private theorem rop_zero : Rop μ (0 : TG K n) = 0 := by
  simpa using rop_smul (μ := μ) (0 : ℂ) (0 : TG K n)

private theorem rop_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → TG K n) :
    Rop μ (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • Rop μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rop_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, rop_add, rop_smul, ih]

private theorem twK_fin (θ : Twist μ) (f : TG K n) (x : normOneGL (K := K) (n := n)) :
    (Function.support fun γ : Gam K n => f (x⁻¹ * (γ : G1 K n) * θ.e x)).Finite :=
  finite_support_automorphicKernel (Gam K n) f (x, θ.e x)

private theorem twK_sum (θ : Twist μ) {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → TG K n)
    (x : normOneGL (K := K) (n := n)) : twK θ (∑ i ∈ s, c i • f i) x = ∑ i ∈ s, c i * twK θ (f i) x := by
  unfold twK
  simp only [sum_smul_apply]
  rw [finsum_sum_comm]
  · exact Finset.sum_congr rfl fun i _ => (mul_finsum _ _).symm
  · intro i _
    refine (twK_fin θ (f i) x).subset fun γ hγ h0 => hγ ?_
    simp only [Function.mem_support, not_not] at h0 ⊢
    simp only [Function.mem_support, ne_eq, Decidable.not_not] at *
    rw [h0, mul_zero]

private theorem twK_cont (θ : Twist μ) (f : TG K n) : Continuous (twK θ f) := by
  have h : Continuous fun x : normOneGL (K := K) (n := n) => automorphicKernel (Gam K n) f (x, θ.e x) :=
    (continuous_automorphicKernel (Gam K n) f).comp (continuous_id.prodMk θ.e.continuous)
  exact h

private theorem twK_left (θ : Twist μ) (f : TG K n) {δ : normOneGL (K := K) (n := n)} (hδ : δ ∈ Gam K n)
    (x : normOneGL (K := K) (n := n)) : twK θ f (δ * x) = twK θ f x := by
  have h1 := automorphicKernel_smul_left (Gam K n) f ⟨δ, hδ⟩ x (θ.e (δ * x))
  have h2 := automorphicKernel_smul_right (Gam K n) f ⟨θ.e δ, (θ.mem_gam δ).2 hδ⟩ x (θ.e x)
  have e1 : twK θ f (δ * x) =
      automorphicKernel (Gam K n) f ((⟨δ, hδ⟩ : Gam K n) • x, θ.e (δ * x)) := rfl
  have e2 : θ.e (δ * x) = (⟨θ.e δ, (θ.mem_gam δ).2 hδ⟩ : Gam K n) • θ.e x := by
    rw [map_mul]
    rfl
  rw [e1, h1, e2, h2]
  rfl

private theorem twKQ_mk (θ : Twist μ) (f : TG K n) (x : normOneGL (K := K) (n := n)) :
    twKQ θ f (mk (Gam K n) x) = twK θ f x := by
  obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1
    (show mk (Gam K n) (Quotient.out (mk (Gam K n) x)) = mk (Gam K n) x from Quotient.out_eq _)
  change twK θ f (Quotient.out (mk (Gam K n) x)) = _
  rw [← hγ]
  exact twK_left θ f γ.2 x

private theorem twKQ_int (θ : Twist μ) (f : TG K n) (Z : ℝ) (h : ∀ x, Z < qht x → twK θ f x = 0) :
    Integrable (twKQ θ f) (quotientMeasure (Gam K n) μ) := by
  haveI := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  have hc : Continuous (twKQ θ f) :=
    (isOpenQuotientMap_mk (Gam K n)).isQuotientMap.continuous_iff.2
      ((twK_cont θ f).congr fun x => (twKQ_mk θ f x).symm)
  obtain ⟨C, hC, hcov⟩ := UpperTheory.exists_compact_fundamental_set_of_height_le K n Z
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (twK_cont θ f).continuousOn
  have hm : AEStronglyMeasurable (twKQ θ f) (quotientMeasure (Gam K n) μ) := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact hc.aestronglyMeasurable
  refine Integrable.of_bound hm (max M 0) (Eventually.of_forall fun y => ?_)
  change ‖twK θ f (Quotient.out y)‖ ≤ _
  by_cases hz : Z < qht (Quotient.out y)
  · rw [h _ hz, norm_zero]
    exact le_max_right _ _
  · obtain ⟨g, hg, c, hc', e⟩ := hcov _ (not_lt.1 hz)
    rw [e, twK_left θ f hg]
    exact (hM c hc').trans (le_max_left _ _)

end

end UpperTheory.ConvolutionTheory.GM

theorem UpperTheory.ConvolutionTheory.GM.twLin :
    TwLin := by
  intro K _ _ n _ μ _ θ ι s c f Z h
  refine ⟨rop_sum s c f, fun x hx => ?_, ?_⟩
  · rw [twK_sum]
    exact Finset.sum_eq_zero fun i hi => by rw [h i hi x hx, mul_zero]
  · have e : ∀ y, twKQ θ (∑ i ∈ s, c i • f i) y = ∑ i ∈ s, c i * twKQ θ (f i) y :=
      fun y => twK_sum θ s c f _
    unfold twInt
    simp only [e]
    rw [integral_finsetSum _ fun i hi => (twKQ_int θ (f i) Z (h i hi)).const_mul _]
    simp only [integral_const_mul]
end

