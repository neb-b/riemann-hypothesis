module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatLin
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G

variable {F : Type} [Field F] [NumberField F]

private def eQ : Fin 3 ⊕ Unit ≃ Fin 4 where
  toFun := Sum.elim ![0, 2, 3] fun _ => 1
  invFun := ![.inl 0, .inr (), .inl 1, .inl 2]
  left_inv := by
    rintro (i | ⟨⟩)
    · fin_cases i <;> rfl
    · rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

private theorem reindex_mem {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    (fun z : Fin 3 ⊕ Unit → A F => φ fun i => z (eQ.symm i)) ∈ schwartzBruhatPi (K := F) (ι := Fin 3 ⊕ Unit) := by
  let M : Matrix (Fin 4) (Fin 3 ⊕ Unit) F := (1 : Matrix (Fin 4) (Fin 4) F).submatrix id eQ
  let N : Matrix (Fin 3 ⊕ Unit) (Fin 4) F := (1 : Matrix (Fin 4) (Fin 4) F).submatrix eQ id
  have hNM : N * M = 1 := by
    have h := Matrix.submatrix_mul (1 : Matrix (Fin 4) (Fin 4) F) (1 : Matrix (Fin 4) (Fin 4) F)
      eQ id eQ Function.bijective_id
    rw [Matrix.mul_one, Matrix.submatrix_one_equiv] at h
    exact h.symm
  have hMN : M * N = 1 := by
    have h := Matrix.submatrix_mul (1 : Matrix (Fin 4) (Fin 4) F) (1 : Matrix (Fin 4) (Fin 4) F)
      id eQ id eQ.bijective
    rw [Matrix.mul_one, Matrix.submatrix_id_id] at h
    exact h.symm
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi M N hNM hMN hφ
  have hx : ∀ x : Fin 3 ⊕ Unit → A F, (M.map (algebraMap F (A F)) *ᵥ x) = fun i => x (eQ.symm i) := by
    intro x
    funext i
    have hM : ∀ j k, M j k = if j = eQ k then (1 : F) else 0 := fun j k => by
      change (1 : Matrix (Fin 4) (Fin 4) F) j (eQ k) = _
      exact Matrix.one_apply
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hM]
    rw [Finset.sum_eq_single (eQ.symm i)]
    · simp
    · intro b _ hb
      have : i ≠ eQ b := fun h => hb (by simp [h])
      simp [this]
    · simp
  simpa only [hx] using h

private theorem integrable_slice (φ : S4 F) (v : V4 F) :
    Integrable (fun s : A F => φ.1 (Function.update v 1 s)) (adeleMeasure F) := by
  have h := GroundTheory.Heights₂.Theta.integrable_partialFourierPi_slice (reindex_mem φ.2)
    (fun i : Fin 3 => v (eQ (.inl i)))
  have hmp := measurePreserving_funUnique (adeleMeasure F) Unit
  refine (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).1 ?_
  refine h.congr (Eventually.of_forall fun y => ?_)
  have : (fun i => (Sum.elim (fun i : Fin 3 => v (eQ (.inl i))) y : Fin 3 ⊕ Unit → A F) (eQ.symm i)) =
      Function.update v 1 (MeasurableEquiv.funUnique Unit (A F) y) := by
    funext i
    fin_cases i <;> simp [eQ]
  simp only [Function.comp]
  rw [this]

private theorem integrable_term (φ : S4 F) (v : V4 F) :
    Integrable (fun s : A F => φ.1 (Function.update v 1 s) * ψ (-(s * v 1))) (adeleMeasure F) := by
  have hs := integrable_slice φ v
  have hc : Continuous fun s : A F => ψ (-(s * v 1)) :=
    continuous_subtype_val.comp ((continuous_adelicChar (K := F)).comp
      (continuous_id.mul continuous_const).neg)
  exact hs.mono (hs.1.mul hc.aestronglyMeasurable)
    (Eventually.of_forall fun s => by rw [norm_mul, ψ, Circle.norm_coe, mul_one])

end UpperTheory.ConvolutionTheory.R2.G

theorem UpperTheory.ConvolutionTheory.R2.G.hatLin :
    ∀ (F : Type) [Field F] [NumberField F], ∃ H : S4 F →ₗ[ℂ] S4 F, ∀ φ, (H φ).1 = hat φ.1 := by
  intro F _ _
  have hadd : ∀ φ χ : S4 F, hat (φ + χ).1 = hat φ.1 + hat χ.1 := by
    intro φ χ
    funext v
    simp only [hat, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (integrable_term φ v) (integrable_term χ v)
  have hsmul : ∀ (c : ℂ) (φ : S4 F), hat (c • φ).1 = c • hat φ.1 := by
    intro c φ
    funext v
    simp only [hat, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  refine ⟨{ toFun := fun φ => ⟨hat φ.1, (UpperTheory.ConvolutionTheory.R2.D.hatMem F φ).1⟩
            map_add' := fun φ χ => Subtype.ext (hadd φ χ)
            map_smul' := fun c φ => Subtype.ext (hsmul c φ) }, fun φ => rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ProdExt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.prodExt :
    ∀ (Ω X Z : Type) [MeasurableSpace Ω] [MeasurableSpace X] [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [SecondCountableTopology Z] [T2Space Z] (ν : Measure Ω) (r : Ω → X) (s : Ω → Z) (ρ : Ω → ℂ),
    TopologicalSpace.IsTopologicalBasis {T : Set Z | IsCompact T ∧ IsOpen T} → Measurable r → Measurable s → Integrable ρ ν →
    (∀ (S : Set X) (T : Set Z), MeasurableSet S → IsCompact T → IsOpen T → ∫ ω, S.indicator 1 (r ω) * (T.indicator 1 (s ω) * ρ ω) ∂ν = 0) →
    ∀ Q : X × Z → ℂ, Measurable Q → (∀ x, ‖Q x‖ ≤ 1) → ∫ ω, Q (r ω, s ω) * ρ ω ∂ν = 0 := by
  intro Ω X Z _ _ _ _ _ _ _ ν r s ρ hB hr hs hρ H Q hQ hQ1
  have hφ : Measurable (fun ω => (r ω, s ω)) := hr.prodMk hs

  obtain ⟨e, he, heU⟩ : ∃ e : ℕ → Set Z, (∀ n, IsCompact (e n) ∧ IsOpen (e n)) ∧ ⋃ n, e n = Set.univ := by
    obtain ⟨T, hTc, hTs, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable
      {T : Set Z | IsCompact T ∧ IsOpen T} (fun t ht => ht.2)
    have hne : (insert ∅ T).Nonempty := Set.insert_nonempty _ _
    obtain ⟨e, he⟩ := (hTc.insert ∅).exists_eq_range hne
    refine ⟨e, fun n => ?_, ?_⟩
    · have hn : e n ∈ insert ∅ T := he ▸ Set.mem_range_self n
      rcases hn with hn | hn
      · rw [hn]; exact ⟨isCompact_empty, isOpen_empty⟩
      · exact hTs hn
    · rw [← Set.sUnion_range, ← he, Set.sUnion_insert, Set.empty_union, hTU, hB.sUnion_eq]

  have hmass : ∫ ω, ρ ω ∂ν = 0 := by
    have hF : ∀ n, ∫ ω, (Set.accumulate e n).indicator (1 : Z → ℂ) (s ω) * ρ ω ∂ν = 0 := by
      intro n
      have hc : IsCompact (Set.accumulate e n) := isCompact_accumulate (fun i => (he i).1) n
      have ho : IsOpen (Set.accumulate e n) := by
        rw [Set.accumulate_def]
        exact isOpen_iUnion (fun i => isOpen_iUnion (fun _ => (he i).2))
      have := H Set.univ (Set.accumulate e n) MeasurableSet.univ hc ho
      simpa using this
    have hlim : Tendsto (fun n => ∫ ω, (Set.accumulate e n).indicator (1 : Z → ℂ) (s ω) * ρ ω ∂ν)
        atTop (𝓝 (∫ ω, ρ ω ∂ν)) := by
      refine tendsto_integral_of_dominated_convergence (fun ω => ‖ρ ω‖) ?_ hρ.norm ?_ ?_
      · intro n
        have hm : MeasurableSet (Set.accumulate e n) :=
          (isCompact_accumulate (fun i => (he i).1) n).isClosed.measurableSet
        exact (((measurable_one.indicator hm).comp hs).aestronglyMeasurable).mul hρ.1
      · intro n
        refine Eventually.of_forall (fun ω => ?_)
        by_cases h : s ω ∈ Set.accumulate e n <;> simp [h]
      · refine Eventually.of_forall (fun ω => ?_)
        have hmem : s ω ∈ ⋃ n, e n := heU ▸ Set.mem_univ _
        obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hmem
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop n] with m hm
        have : s ω ∈ Set.accumulate e m := Set.mem_accumulate.2 ⟨n, hm, hn⟩
        simp [this]
    have := tendsto_nhds_unique hlim (by simp only [hF]; exact tendsto_const_nhds)
    exact this

  have hgen : (inferInstance : MeasurableSpace (X × Z)) =
      MeasurableSpace.generateFrom (Set.image2 (· ×ˢ ·) {S : Set X | MeasurableSet S}
        {T : Set Z | IsCompact T ∧ IsOpen T}) := by
    have hD : IsCountablySpanning {T : Set Z | IsCompact T ∧ IsOpen T} := ⟨e, he, heU⟩
    have h1 : ‹MeasurableSpace Z› = MeasurableSpace.generateFrom {T : Set Z | IsCompact T ∧ IsOpen T} :=
      (BorelSpace.measurable_eq).trans hB.borel_eq_generateFrom
    have := generateFrom_prod_eq (isCountablySpanning_measurableSet (α := X)) hD
    rw [MeasurableSpace.generateFrom_measurableSet, ← h1] at this
    exact this
  have hpi : IsPiSystem (Set.image2 (· ×ˢ ·) {S : Set X | MeasurableSet S}
      {T : Set Z | IsCompact T ∧ IsOpen T}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod
      (fun a ha b hb _ => ⟨ha.1.inter hb.1, ha.2.inter hb.2⟩)
  have hset : ∀ A : Set (X × Z), MeasurableSet A → ∫ ω in (fun ω => (r ω, s ω)) ⁻¹' A, ρ ω ∂ν = 0 := by
    intro A hA
    induction A, hA using MeasurableSpace.induction_on_inter hgen hpi with
    | empty => simp
    | basic t ht =>
      obtain ⟨S, hS, T, hT, rfl⟩ := ht
      have hTm : MeasurableSet T := hT.2.measurableSet
      have hm : MeasurableSet ((fun ω => (r ω, s ω)) ⁻¹' (S ×ˢ T)) := hφ (hS.prod hTm)
      rw [← integral_indicator hm, ← H S T hS hT.1 hT.2]
      congr 1
      funext ω
      by_cases h1 : r ω ∈ S <;> by_cases h2 : s ω ∈ T <;> simp [Set.indicator, h1, h2]
    | compl t htm ih =>
      rw [Set.preimage_compl, setIntegral_compl (hφ htm) hρ, ih, hmass, sub_zero]
    | iUnion f hd hm ih =>
      rw [Set.preimage_iUnion, integral_iUnion (fun i => hφ (hm i))
        (fun i j hij => (hd hij).preimage _) hρ.integrableOn]
      simp [ih]

  have hint : ∀ (f : Ω → ℂ) (C : ℝ), Measurable f → (∀ ω, ‖f ω‖ ≤ C) →
      Integrable (fun ω => f ω * ρ ω) ν := fun f C hf hC =>
    hρ.bdd_mul hf.aestronglyMeasurable (Eventually.of_forall hC)
  have hsimple : ∀ g : SimpleFunc (X × Z) ℂ, ∫ ω, g (r ω, s ω) * ρ ω ∂ν = 0 := by
    intro g
    induction g using SimpleFunc.induction with
    | const c hA =>
      rename_i A
      have hm : MeasurableSet ((fun ω => (r ω, s ω)) ⁻¹' A) := hφ hA
      have h0 := hset A hA
      rw [← integral_indicator hm] at h0
      have : (fun ω => (SimpleFunc.piecewise A hA (SimpleFunc.const _ c) (SimpleFunc.const _ 0)) (r ω, s ω) * ρ ω)
          = fun ω => c * ((fun ω => (r ω, s ω)) ⁻¹' A).indicator ρ ω := by
        funext ω
        by_cases h : (r ω, s ω) ∈ A <;> simp [Set.indicator, h, Set.piecewise]
      rw [this, integral_const_mul, h0, mul_zero]
    | add hd hf hg =>
      rename_i f g
      obtain ⟨Cf, hCf⟩ := f.exists_forall_norm_le
      obtain ⟨Cg, hCg⟩ := g.exists_forall_norm_le
      have hif := hint (fun ω => f (r ω, s ω)) Cf (f.measurable.comp hφ) (fun ω => hCf _)
      have hig := hint (fun ω => g (r ω, s ω)) Cg (g.measurable.comp hφ) (fun ω => hCg _)
      simp only [SimpleFunc.coe_add, Pi.add_apply, add_mul]
      rw [integral_add hif hig, hf, hg, add_zero]

  have hSM : StronglyMeasurable Q := hQ.stronglyMeasurable
  have hlim : Tendsto (fun n => ∫ ω, hSM.approxBounded 1 n (r ω, s ω) * ρ ω ∂ν) atTop
      (𝓝 (∫ ω, Q (r ω, s ω) * ρ ω ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => ‖ρ ω‖) ?_ hρ.norm ?_ ?_
    · intro n
      exact (((hSM.approxBounded 1 n).measurable.comp hφ).aestronglyMeasurable).mul hρ.1
    · intro n
      refine Eventually.of_forall (fun ω => ?_)
      rw [norm_mul]
      have := hSM.norm_approxBounded_le zero_le_one n (r ω, s ω)
      calc _ ≤ 1 * ‖ρ ω‖ := by gcongr
        _ = ‖ρ ω‖ := one_mul _
    · refine Eventually.of_forall (fun ω => ?_)
      exact (hSM.tendsto_approxBounded_of_norm_le (hQ1 _)).mul_const _
  exact tendsto_nhds_unique hlim (by simp only [hsimple]; exact tendsto_const_nhds)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.PtMove
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem conj_ne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)
    {ξ : Fin 2 → F} (hξ : ξ ≠ 0) : algebraMap F E (ξ 0) - algebraMap F E (ξ 1) * D.θ ≠ 0 := by
  intro h
  have hl := Fintype.linearIndependent_iff.1 D.b.linearIndependent ![ξ 0, -ξ 1] (by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, D.b0, D.b1, Algebra.smul_def, map_neg]
    simp only [Matrix.cons_val_fin_one, mul_one, map_neg]
    linear_combination h)
  apply hξ
  ext i
  fin_cases i
  · simpa using hl 0
  · simpa using hl 1

private theorem coe_al {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)
    (ξ : Fin 2 → F) (h : algebraMap F E (ξ 0) - algebraMap F E (ξ 1) * D.θ ≠ 0) :
    ((al D ξ : (A E)ˣ) : A E) = D.mkE (rt (ξ 0)) (-rt (ξ 1)) := by
  have e := D.mkE_rt (ξ 0) (-ξ 1)
  have e' : -rt (ξ 1) = (rt (-ξ 1) : A F) := (map_neg _ _).symm
  rw [e', e, al, dite_eq_right h, IdeleGroup.coe_diagonal]
  simp [sub_eq_add_neg]

private theorem vcD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) (x : G1 F) :
    (gl (cD t x)).val = !![x 0 0, x 0 1 * ((t⁻¹ : (A F)ˣ) : A F); (t : A F) * x 1 0, x 1 1] := rfl

private theorem vgl {F : Type} [Field F] [NumberField F] (x : G1 F) : (gl x).val = x.1 := rfl

private theorem vmD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) :
    (gl (mD t)).val = !![(t : A F), 0; 0, ((t⁻¹ : (A F)ˣ) : A F)] := rfl

private theorem cD_dM {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) (x : G1 F) :
    gl (cD t x) * dM t = dM t * gl x := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, vcD, vgl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc] <;> ring

private theorem dM_mD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) : dM t * gl (mD t) = aE t := by
  refine Units.ext ?_
  rw [Units.val_mul, vmD]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM, aE, Matrix.mul_apply, Fin.sum_univ_two]

private theorem pt_move {F : Type} [Field F] [NumberField F] (t n : (A F)ˣ) (g : G1 F) :
    gl (cD t (mD t * g)) * dM (t * n) = aE t * (gl g * dM n) := by
  rw [UpperTheory.ConvolutionTheory.R2.dM_mul, ← mul_assoc, cD_dM, gl_mul, ← mul_assoc (dM t), dM_mD, mul_assoc]

theorem UpperTheory.ConvolutionTheory.R2.G.wxPt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (ξ : Fin 2 → F), ξ ≠ 0 → ∃ t : Fˣ, ∀ f : GL (Fin 2) (A F) → ℂ, Pp.Lf f → ∀ φ h g,
    w1 W f φ (aE (al D ξ) * h) (cD (IdeleGroup.diagonal F t) (mD (IdeleGroup.diagonal F t) * g)) = wx W f φ h ξ g := by
  intro F E _ _ _ _ _ _ _ D W ξ hξ
  have hz := conj_ne D hξ
  have hα := coe_al D ξ hz
  set α := al D ξ with hαdef
  let t : Fˣ := Units.map (Algebra.norm F : E →* F) (Units.mk0 _ hz)
  have hT : ideleNorm F E α = IdeleGroup.diagonal F t := by
    rw [hαdef, al, dite_eq_right hz, ideleNorm_diagonal]
  have hco : D.co (α : A E) = ![rt (ξ 0), -rt (ξ 1)] := by rw [hα, D.co_mkE]
  have ht : (t : F) = ξ 0 ^ 2 - D.δ * ξ 1 ^ 2 := by
    haveI := AdeleBaseChange.nontrivial_adeleRing F
    apply (algebraMap F (A F)).injective
    have h1 := D.coe_ideleNorm α
    rw [hT, IdeleGroup.coe_diagonal, hco] at h1
    simpa using h1
  refine ⟨t, fun f hf φ h g => ?_⟩
  set T := IdeleGroup.diagonal F t with hTdef
  have hnu : nu F (aE α * h) = T * nu F h := by rw [nu_mul, nu_aE, hT]
  have hpoint : ![T * (0 : A F), ((T⁻¹ : (A F)ˣ) : A F) * ((ideleNorm F E α : (A F)ˣ) * 1),
      T * D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE 1 0) 0, T * D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE 1 0) 1] = pt ξ := by
    have hb : am E (T : A F) * ((α⁻¹ : (A E)ˣ) : A E) = D.mkE (rt (ξ 0)) (rt (ξ 1)) := by
      rw [← hT, D.am_ideleNorm, mul_comm (α : A E), mul_assoc, Units.mul_inv, mul_one, hα, D.bar_mkE, neg_neg]
    have hc := D.co_am_mul (T : A F) ((α⁻¹ : (A E)ˣ) : A E)
    rw [hb, D.co_mkE] at hc
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
    rw [D.mkE_one, mul_one, hT]
    simp [pt, ← h0, ← h1]
  have hhat : hat (W.Om (cD T (mD T * g)) (W.L (aE α * h) φ)).1 ![0, 1, 1, 0] = hat (W.Om g (W.L h φ)).1 (pt ξ) := by
    have hcm : W.Om (cD T (mD T * g)) (W.L (aE α) (W.L h φ)) = W.L (aE α) (W.Om (mD T * g) (W.L h φ)) := by
      have := W.comm (aE α) (mD T * g)
      rw [nu_aE, hT] at this
      exact (LinearMap.congr_fun this (W.L h φ)).symm
    rw [map_mul, Module.End.mul_apply, hcm]
    have hS := hatSt F E D W
    have e1 := hS.aE α (W.Om (mD T * g) (W.L h φ)) 0 1 1 0
    have e2 := hS.m T (W.Om g (W.L h φ))
    have e3 : ((W.η.1 T : ℂˣ) : ℂ) = 1 := by rw [← hT, W.η_norm]; rfl
    have e4 : ab T = 1 := ab_diagonal t
    rw [e1, map_mul, Module.End.mul_apply, e2, e3, e4]
    have hv := hpoint
    rw [← hv]
    simp
  have hw : ∫ b in fundamentalSet F, f (gl (nU b) * (gl g * dM (nu F h))) * ψ (rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b) ∂(adeleMeasure F) =
      Wf f (aE T * (gl g * dM (nu F h))) := by
    rw [← ht]
    exact Pp.wfT F f hf t _
  simp only [w1, wx]
  rw [hhat, hnu, pt_move, hw]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.TransN
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem nu_nE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) (u : Fin 2 → A F) (h : GL (Fin 2) (A E)) :
    nu F (nE D u * h) = nu F h := by
  have hd : Matrix.GeneralLinearGroup.det (nE D u) = 1 := by
    exact Units.ext (nU (D.mkE (u 0) (u 1))).2
  simp only [nu, map_mul, hd, one_mul]

private theorem cD_unit {F : Type} [Field F] [NumberField F] (g : G1 F) : cD (1 : (A F)ˣ) g = g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD]

private theorem om_L {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D)
    (u : Fin 2 → A F) (h : GL (Fin 2) (A E)) (φ : S4 F) (g : G1 F) :
    W.Om g (W.L (nE D u * h) φ) = W.L (nE D u) (W.Om g (W.L h φ)) := by
  have hn : nu F (nE D u) = 1 := by
    have := nu_nE D u 1
    rw [mul_one] at this
    rw [this]
    simp [nu]
  have hc := W.comm (nE D u) g
  rw [hn, cD_unit] at hc
  rw [map_mul, Module.End.mul_apply]
  exact (LinearMap.congr_fun hc (W.L h φ)).symm

theorem UpperTheory.ConvolutionTheory.R2.G.transN :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) (u : Fin 2 → A F), T0 W M f φ (nE D u * h) = T0 W M f φ h ∧
    ∀ ξ, Wx W M f φ (nE D u * h) ξ = chi D.δ ξ u * Wx W M f φ h ξ := by
  intro F E _ _ _ _ _ _ _ D W M f φ h u
  have hH : St.Hat W := hatSt F E D W
  have hnu := nu_nE D u h
  constructor
  · unfold T0
    refine setIntegral_congr_fun M.meas fun g _ => ?_
    have hrow : ThRow 0 0 (W.Om g (W.L (nE D u * h) φ)).1 = ThRow 0 0 (W.Om g (W.L h φ)).1 := by
      rw [om_L]
      unfold ThRow
      refine tsum_congr fun ξ => ?_
      have := hH.nE (u 0) (u 1) (W.Om g (W.L h φ)) 0 (rt (ξ 0)) (rt (ξ 1))
      simpa [nE, zero_mul, neg_zero, ψ] using this
    simp only [hnu, hrow]
  · intro ξ
    have hpt : ∀ g, wx W f φ (nE D u * h) ξ g = chi D.δ ξ u * wx W f φ h ξ g := by
      intro g
      unfold wx
      rw [hnu, om_L]
      have := hH.nE (u 0) (u 1) (W.Om g (W.L h φ)) 1 (rt (ξ 0)) (rt (ξ 1))
      have e : hat (W.L (nE D u) (W.Om g (W.L h φ))).1 (pt ξ) =
          chi D.δ ξ u * hat (W.Om g (W.L h φ)).1 (pt ξ) := by
        simpa only [one_mul, chi, pt, nE] using this
      rw [e]
      ring
    unfold Wx Meas.I0
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [iw, hpt]
    ring
end

