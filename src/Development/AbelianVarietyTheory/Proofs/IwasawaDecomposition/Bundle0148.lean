module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnSymmetricLevelAtTypePrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemInvMulDifferent
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.Mem.Per
open scoped Pointwise nonZeroDivisors

namespace GlobalTheory.Mem.EigenLine

variable {R : Ranks} (H : Host R)

theorem half_ne_zero :
    ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 := by
  refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
  intro h0
  have hd : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  apply hd
  have := H.𝔟_spec.1
  rw [h0, Ideal.bot_mul] at this
  exact this

theorem half_mul_inv :
    ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) * H.AA0 = 1 :=
  mul_inv_cancel₀ (half_ne_zero H)

theorem inv_mul_different :
    H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) =
      ((H.conj • H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
  have h : differentIdeal (𝓞 H.K) (𝓞 H.E) = H.𝔟 * (H.conj • H.𝔟) := H.𝔟_spec.1
  rw [h, FractionalIdeal.coeIdeal_mul, ← mul_assoc, mul_comm H.AA0, half_mul_inv, one_mul]

theorem mem_inv_mul_different (x : H.E) :
    x ∈ H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔
      ∃ b ∈ H.𝔟, x = H.conj ((b : 𝓞 H.E) : H.E) := by
  rw [inv_mul_different, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [Ideal.pointwise_smul_def] at hc
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
      (MulSemiringAction.toRingEquiv _ (𝓞 H.E) H.conj).surjective).1 hc
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨H.conj • b, Ideal.smul_mem_pointwise_smul _ _ _ hb, rfl⟩

theorem map_mem_ellLat {LL : Type} [Field LL] [NumberField LL] (embE : H.E →+* LL)
    (g : R.GG) (x : H.E)
    (hx : x ∈ H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E)) :
    embE (H.sigmaOf g x) ∈ ellLat H embE g := by
  refine FractionalIdeal.mul_induction_on hx ?_ ?_
  · intro i hi j hj
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
    exact Submodule.subset_span ⟨i, hi, b, hb, rfl⟩
  · intro a b ha hb
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ ha hb

theorem ellT_eq_ellLat : ∀ (D : D7) (M : IntermediateField ℚ ℂ) [NumberField M] (embE : D.host.E →+* M),
    (∀ x, ((embE x : M) : ℂ) = D.host.φ₀ x) → ∀ τ : D.what₂.Tau,
      ellT D M τ = ellLat D.host embE (D.eTau τ).1 := by
  intro D M _ embE hE τ
  have hτ : ∀ (τ : D.what₂.Tau) x, embT D τ x = ((embE (D.host.sigmaOf (D.eTau τ).1 x) : M) : ℂ) := by
    intro τ x
    rw [hE]
    rfl
  have hM : ∀ τ x, embT D τ x ∈ M := fun τ x => by
    rw [hτ]
    exact Subtype.property _
  let φ : D.host.E →+* M := embE.comp (((D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)).comp
    (D.host.conj : D.host.E →+* D.host.E))
  have hφ : ∀ y, φ y = embE (D.host.sigmaOf (D.eTau τ).1 (D.host.conj y)) := fun _ => rfl
  have hone := half_mul_inv D.host
  apply le_antisymm
  · intro x hx
    rw [GlobalTheory.Glob.mem_ellT_iff hM] at hx
    have key : ∀ z ∈ ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * D.host.AA0,
        x * φ z ∈ ellLat D.host embE (D.eTau τ).1 := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz ?_ ?_
      · intro i hi j hj
        obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
        have hint : IsIntegral ℤ (x * φ j) := by
          refine (isIntegral_algHom_iff (M.val.toRingHom.toIntAlgHom) M.val.injective).1 ?_
          have := hx j hj
          rw [hτ] at this
          exact this
        let c : 𝓞 M := ⟨x * φ j, hint⟩
        have : c • φ (b : D.host.E) ∈ ellLat D.host embE (D.eTau τ).1 :=
          Submodule.smul_mem _ _ (map_mem_ellLat D.host embE _ _
            ((mem_inv_mul_different D.host _).2 ⟨b, hb, rfl⟩))
        convert this using 1
        change x * φ (b * j) = x * φ j * φ b
        rw [map_mul]; ring
      · intro a b ha hb
        rw [map_add (f := _), mul_add]
        exact Submodule.add_mem _ ha hb
    have := key 1 (hone ▸ FractionalIdeal.one_mem_one _)
    simpa using this
  · unfold ellLat
    rw [Submodule.span_le]
    rintro x ⟨a, ha, d, hd, rfl⟩
    obtain ⟨b, hb, hab⟩ := (mem_inv_mul_different D.host (a * (d : D.host.E))).1
      (FractionalIdeal.mul_mem_mul ha ((FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩))
    rw [SetLike.mem_coe, GlobalTheory.Glob.mem_ellT_iff hM]
    intro y hy
    have h1 : (b : D.host.E) * y ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
      hone ▸ FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨b, hb, rfl⟩) hy
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [← hτ, hab, ← map_mul, ← map_mul, ← hr]
    exact map_isIntegral_int ((embT D τ).comp (D.host.conj : D.host.E →+* D.host.E)) r.isIntegral_coe

end GlobalTheory.Mem.EigenLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyStandardLocalHaarMeasures
section
noncomputable section

namespace GlobalTheory.GaugeEx.StdExist

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

def coordHomeo {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    (R ⊗[F] E) ≃ₜ (Fin d → R) where
  toEquiv := (Algebra.TensorProduct.basis R b).equivFun.toEquiv
  continuous_toFun := by
    haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
    exact IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
  continuous_invFun := by
    haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
    exact IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem isCompact_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  exact isCompact_iff_compactSpace.2 this

theorem isOpen_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
  Valued.isOpen_valuationSubring _

theorem intV_eq {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    intV b v = coordHomeo b (Fv F v) ⁻¹'
      (Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
  ext y
  simp only [intV, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]
  rfl

theorem isCompact_intV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (intV b v) := by
  rw [intV_eq, Homeomorph.isCompact_preimage]
  exact isCompact_univ_pi fun _ => isCompact_integers v

theorem isOpen_intV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (intV b v) := by
  rw [intV_eq]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integers v).preimage
    (coordHomeo b (Fv F v)).continuous

def intK (v : HeightOneSpectrum (𝓞 F)) : TopologicalSpace.PositiveCompacts (Fv F v) where
  carrier := v.adicCompletionIntegers F
  isCompact' := isCompact_integers v
  interior_nonempty' := by
    rw [(isOpen_integers v).interior_eq]
    exact ⟨0, zero_mem _⟩

def intVK {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    TopologicalSpace.PositiveCompacts (Fv F v ⊗[F] E) where
  carrier := intV b v
  isCompact' := isCompact_intV b v
  interior_nonempty' := by
    rw [(isOpen_intV b v).interior_eq]
    exact ⟨0, fun k => by simp⟩

theorem nonempty_stdMeas (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) : Nonempty (StdMeas b) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  exact ⟨{
    lamI := Measure.addHaar
    lamV := fun v => Measure.addHaarMeasure (intVK b v)
    nuI := Measure.addHaar
    nuV := fun v => Measure.addHaarMeasure (intK v)
    haar_lamI := inferInstance
    haar_lamV := fun v => inferInstance
    haar_nuI := inferInstance
    haar_nuV := fun v => inferInstance
    lamV_int := fun v => Measure.addHaarMeasure_self (K₀ := intVK b v)
    nuV_int := fun v => Measure.addHaarMeasure_self (K₀ := intK v) }⟩

end GlobalTheory.GaugeEx.StdExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalUnitMono
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

namespace GlobalTheory.FockParseval

open MvPolynomial GlobalTheory.FockSeq

variable {σ : Type} [DecidableEq σ]

def unitMono (F : Fock σ) (α : σ →₀ ℕ) : F.H := (wt α)⁻¹ • F.ι (monomial α 1)


omit [DecidableEq σ] in
theorem conj_wt (α : σ →₀ ℕ) : (starRingEnd ℂ) (wt α) = wt α := Complex.conj_ofReal _


omit [DecidableEq σ] in
theorem wt_mul_self (α : σ →₀ ℕ) : wt α * wt α = (mfact α : ℕ) := by
  rw [← star_wt_mul, conj_wt]

theorem orthonormal_unitMono (F : Fock σ) : Orthonormal ℂ (unitMono F) := by
  classical
  rw [orthonormal_iff_ite]
  intro α β
  rw [unitMono, unitMono, inner_smul_left, inner_smul_right, F.fockIP, ← mfact_cast, map_inv₀, conj_wt]
  by_cases h : α = β
  · subst h
    have := wt_ne_zero α
    rw [if_pos rfl, if_pos rfl, ← wt_mul_self]
    field_simp
  · simp [h]

theorem dense_span_unitMono (F : Fock σ) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (unitMono F))).topologicalClosure := by
  intro x _
  refine closure_mono ?_ (F.dense x)
  rintro _ ⟨f, rfl⟩
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => rw [map_add (f := _)]; exact Submodule.add_mem _ hf hg
  | monomial α c =>
    have e : F.ι (monomial α c) = (c * wt α) • unitMono F α := by
      rw [unitMono, smul_smul, mul_assoc, mul_inv_cancel₀ (wt_ne_zero α), mul_one, ← map_smul, smul_monomial]
      simp
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

theorem inner_unitMono {F : Fock σ} {v : F.H} {E : MvPowerSeries σ ℂ} (h : HasCoeff F v E) (α : σ →₀ ℕ) :
    inner ℂ (unitMono F α) v = wt α * MvPowerSeries.coeff α E := by
  have := wt_ne_zero α
  rw [unitMono, inner_smul_left, h α, ← mfact_cast, map_inv₀, conj_wt, ← wt_mul_self]
  field_simp

theorem parseval (σ : Type) [DecidableEq σ] (F : Fock σ) (v w : F.H) (E E' : MvPowerSeries σ ℂ)
    (hv : HasCoeff F v E) (hw : HasCoeff F w E') :
    Summable (fun α : σ →₀ ℕ => (GlobalTheory.FockSeq.mfact α : ℝ) * ‖MvPowerSeries.coeff α E‖ ^ 2) ∧
      inner ℂ v w = ∑' α : σ →₀ ℕ, (GlobalTheory.FockSeq.mfact α : ℂ) * (starRingEnd ℂ) (MvPowerSeries.coeff α E) *
        MvPowerSeries.coeff α E' := by
  refine ⟨((orthonormal_unitMono F).inner_products_summable v).congr fun α => ?_, ?_⟩
  · rw [inner_unitMono hv, norm_mul, mul_pow, wt, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  · let b := HilbertBasis.mk (orthonormal_unitMono F) (dense_span_unitMono F)
    rw [← b.tsum_inner_mul_inner v w]
    refine tsum_congr fun α => ?_
    rw [HilbertBasis.coe_mk, ← inner_conj_symm, inner_unitMono hv, inner_unitMono hw, map_mul, conj_wt,
      ← wt_mul_self]
    ring

end GlobalTheory.FockParseval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureSmulFactorsEqSmul
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.ProdScale

theorem finite_mulSupport_sub {ι : Type} (r : ι → ℝ≥0) (hr : (Function.mulSupport r).Finite)
    (p : ι → Prop) : (Function.mulSupport fun v : {v // p v} => (r v.1 : ℝ)).Finite := by
  refine (hr.preimage (f := (Subtype.val : {v // p v} → ι)) Subtype.val_injective.injOn).subset ?_
  intro v hv h
  exact hv (by simp [h])

theorem summable_scale {ι : Type} (f : ι → ℝ) (r : ι → ℝ≥0) (hf : Summable fun v => |f v - 1|)
    (hr : (Function.mulSupport r).Finite) : Summable fun v => |r v * f v - 1| := by
  refine hf.congr_cofinite ?_
  filter_upwards [hr.compl_mem_cofinite] with v hv
  have : r v = 1 := by simpa using hv
  simp [this]

theorem finprod_eq {ι : Type} (r : ι → ℝ≥0) (hr : (Function.mulSupport r).Finite) (S : Finset ι) :
    ((∏ᶠ v, r v : ℝ≥0) : ℝ) = (∏ v ∈ S, (r v : ℝ)) * ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := by
  have h0 : (Function.mulSupport fun v => (r v : ℝ)).Finite :=
    hr.subset fun v hv h => hv (by simp [h])
  have h1 : ((∏ᶠ v, r v : ℝ≥0) : ℝ) = ∏ᶠ v, (r v : ℝ) :=
    NNReal.toRealHom.toMonoidHom.map_finprod hr
  rw [h1, ← tprod_eq_finprod (L := SummationFilter.unconditional ι) h0, ← Finset.tprod_subtype' S (fun v => (r v : ℝ))]
  exact (Multipliable.tprod_mul_tprod_compl (f := fun v => (r v : ℝ)) (s := (S : Set ι))
    (multipliable_of_hasFiniteMulSupport (finite_mulSupport_sub r hr _))
    (multipliable_of_hasFiniteMulSupport (finite_mulSupport_sub r hr _))).symm

theorem tprod_scale {ι : Type} (f : ι → ℝ) (r : ι → ℝ≥0) (hf : Summable fun v => |f v - 1|)
    (hr : (Function.mulSupport r).Finite) (S : Finset ι) :
    ∏' v : {v // v ∉ S}, ((r v.1 : ℝ) * f v.1) =
      (∏' v : {v // v ∉ S}, (r v.1 : ℝ)) * ∏' v : {v // v ∉ S}, f v.1 := by
  refine Multipliable.tprod_mul
    (multipliable_of_hasFiniteMulSupport (finite_mulSupport_sub r hr _)) ?_
  have h := multipliable_one_add_of_summable (f := fun v : {v // v ∉ S} => f v.1 - 1)
    (hf.subtype (fun v => v ∉ S))
  simpa using h

theorem finprod_ennreal {ι : Type} (r : ι → ℝ≥0) (hr : (Function.mulSupport r).Finite)
    (S : Finset ι) :
    ∃ c : ℝ≥0, (∏ᶠ v, r v) = (∏ v ∈ S, r v) * c ∧ (c : ℝ) = ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := by
  have h0 : 0 ≤ ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := by
    rw [tprod_eq_finprod (finite_mulSupport_sub r hr _)]
    exact finprod_nonneg fun v => (r v.1).2
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (c : ℝ) = ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := ⟨⟨_, h0⟩, rfl⟩
  refine ⟨c, ?_, hc⟩
  apply NNReal.coe_injective
  rw [finprod_eq r hr S, ← hc]
  simp

theorem isProd_smul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ri : ℝ≥0)
    (r : HeightOneSpectrum (𝓞 F) → ℝ≥0) (h : IsProd b ν mi mv)
    (hr : (Function.mulSupport r).Finite) :
    IsProd b ((ri * ∏ᶠ v, r v) • ν) (ri • mi) (fun v => r v • mv v) := by
  obtain ⟨⟨hi, hv, hs⟩, hf⟩ := h
  have key : ∀ v, ((r v • mv v) (latV b v)).toReal = r v * (mv v (latV b v)).toReal := by
    intro v
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]
  refine ⟨⟨inferInstance, fun v => inferInstance, ?_⟩, ?_⟩
  · simp only [key]
    exact summable_scale _ r hs hr
  · intro S fi fv hfi hfv
    obtain ⟨c, hc, hc'⟩ := finprod_ennreal r hr S
    have ht : tailProd b (fun v => r v • mv v) S = c * tailProd b mv S := by
      unfold tailProd
      simp only [key]
      rw [tprod_scale (fun v => (mv v (latV b v)).toReal) r hs hr S, ← hc',
        ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    rw [Measure.restrict_smul, lintegral_smul_measure, hf S fi fv hfi hfv, ht, hc]
    simp only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib]
    push_cast
    ring

end GlobalTheory.GaugeEx.ProdScale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnSymmetricLevelAtTypePrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowType_mul_on_symmetricLevel_at_typePrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), j < R.m → P ∈ Pr.vGs → ∀ g ∈ Jat (Pr := Pr) (R := R) true j P, ∀ g' ∈ Jat (Pr := Pr) (R := R) true j P, lamRow Ch mu true j P (g * g').toLinearMap = lamRow Ch mu true j P g.toLinearMap * lamRow Ch mu true j P g'.toLinearMap := by
  first | exact @GlobalTheory.SymLevelMul.lamRow_mul | exact GlobalTheory.SymLevelMul.lamRow_mul | (intros; apply GlobalTheory.SymLevelMul.lamRow_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeOneAddPrimeSmulEqOneStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowType_one_add_prime_smul_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), j < R.m → ∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, y x ∈ lamYat (Pr := Pr) (R := R) j P) → lamRow Ch mu sharp j P (LinearMap.id + (qOf P : X.E) • y) = 1 := by
  first | exact @GlobalTheory.Mem.Col2.IdxEx.Cong.lamRow_cong | exact GlobalTheory.Mem.Col2.IdxEx.Cong.lamRow_cong | (intros; apply GlobalTheory.Mem.Col2.IdxEx.Cong.lamRow_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsGenerateIdealAlongComapOfTwisted
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjSpace

namespace GlobalTheory.ProjBlowup

variable {X W : Scheme.{0}} {L : LB X} {m : ℕ}

theorem mem_ideal_of_locally (I : W.IdealSheafData) (A : W.affineOpens) (b : Γ(W, A.1))
    (h : ∀ y ∈ A.1, ∃ (B : W.affineOpens) (e : B.1 ≤ A.1), y ∈ B.1 ∧ resG W e b ∈ I.ideal B) :
    b ∈ I.ideal A := by
  have hk : ∀ B : W.affineOpens, I.ideal B = RingHom.ker (I.subschemeι.app B.1).hom := fun B => by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  rw [hk, RingHom.mem_ker]
  refine ext_germ fun z hz => ?_
  obtain ⟨B, e, hzB, this⟩ := h _ hz
  rw [hk, RingHom.mem_ker, app_resG] at this
  rw [← germ_resG (I.subschemeι.preimage_mono e) z hzB, this, map_zero, map_zero]

theorem appLE_mem_ideal_comap (J : X.IdealSheafData) (g : W ⟶ X) (V : X.affineOpens) (A : W.affineOpens)
    (h : A.1 ≤ g ⁻¹ᵁ V.1) {a : Γ(X, V.1)} (ha : a ∈ J.ideal V) :
    (g.appLE V.1 A.1 h).hom a ∈ (J.comap g).ideal A :=
  (comap_le_iff J g _).1 le_rfl V a ha A h

theorem exists_affine_pair (g : W ⟶ X) (U : X.Opens) (A : W.Opens) (y : W) (hy : y ∈ A) (hU : g y ∈ U) :
    ∃ (V : X.affineOpens) (B : W.affineOpens), V.1 ≤ U ∧ B.1 ≤ A ∧ B.1 ≤ g ⁻¹ᵁ V.1 ∧ y ∈ B.1 := by
  obtain ⟨_, ⟨V, hV', rfl⟩, hyV, hV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hU U.isOpen
  obtain ⟨_, ⟨B, hB', rfl⟩, hyB, hB⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ A ⊓ g ⁻¹ᵁ V from ⟨hy, hyV⟩) (A ⊓ g ⁻¹ᵁ V).isOpen
  exact ⟨⟨V, hV'⟩, ⟨B, hB'⟩, hV, fun x hx => (hB hx).1, fun x hx => (hB hx).2, hyB⟩

theorem Generates.ideal_comap_top_le [IsAffine W] {J : X.IdealSheafData} {σ : Fin (m + 1) → L.Sec}
    (hJ : Generates J σ) (g : W ⟶ X) (k : L.ι) (h : ⊤ ≤ g ⁻¹ᵁ L.U k) :
    (J.comap g).ideal ⟨⊤, isAffineOpen_top W⟩ ≤
      Ideal.span (Set.range fun j => (g.appLE (L.U k) ⊤ h).hom ((σ j).f k)) := by
  set K : Ideal Γ(W, ⊤) := Ideal.span (Set.range fun j => (g.appLE (L.U k) ⊤ h).hom ((σ j).f k)) with hK
  have key : J.comap g ≤ Scheme.IdealSheafData.ofIdealTop K := by
    refine (comap_le_iff _ _ _).2 fun U a ha A hA => mem_ideal_of_locally _ _ _ fun y hy => ?_
    obtain ⟨V, B, hV, hB, hBV, hyB⟩ := exists_affine_pair g (U.1 ⊓ L.U k) A.1 y hy ⟨hA hy, h trivial⟩
    refine ⟨B, hB, hyB, ?_⟩
    have h1 : resG X (hV.trans inf_le_left) a ∈ J.ideal V :=
      J.ideal_le_comap_ideal (U := V) (V := U) (hV.trans inf_le_left) ha
    rw [hJ.2 k V (hV.trans inf_le_right)] at h1
    have h2 : resG W hB (resG W hA ((g.app U.1).hom a)) =
        (g.appLE V.1 B.1 hBV).hom (resG X (hV.trans inf_le_left) a) := by
      rw [appLE_resG, resG_resG]
      rfl
    rw [h2]
    rw [← Ideal.mem_comap]
    refine Ideal.span_le.2 ?_ h1
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, appLE_resG, ← resG_appLE g h le_top]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)
  refine (key _).trans ?_
  simp

theorem Generates.generatesAlong_comap {J : X.IdealSheafData} {σ : Fin (m + 1) → L.Sec}
    (hJ : Generates J σ) (g : W ⟶ X) : GeneratesAlong (J.comap g) σ g := by
  refine ⟨by rw [← Scheme.Hom.preimage_iSup, hJ.1, Scheme.Hom.preimage_top], fun k A h => le_antisymm ?_ ?_⟩
  · intro s hs
    have : IsAffine A.1.toScheme := A.2
    have hA : ⊤ ≤ A.1.ι ⁻¹ᵁ A.1 := A.1.ι_preimage_self.ge
    have h1 := appLE_mem_ideal_comap (J.comap g) A.1.ι A ⟨⊤, isAffineOpen_top _⟩ hA hs
    rw [← Scheme.IdealSheafData.comap_comp] at h1
    have h2 := hJ.ideal_comap_top_le (A.1.ι ≫ g) k (hA.trans (A.1.ι.preimage_mono h)) h1
    have hb : Function.Bijective (A.1.ι.appLE A.1 ⊤ hA).hom := ConcreteCategory.bijective_of_isIso _
    rw [← Ideal.comap_map_of_bijective _ hb (I := Ideal.span _), Ideal.mem_comap, Ideal.map_span,
      ← Set.range_comp]
    convert h2 using 3
    funext j
    exact appLE_appLE _ _ h hA _
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    refine mem_ideal_of_locally _ _ _ fun y hy => ?_
    obtain ⟨V, B, hV, hB, hBV, hyB⟩ := exists_affine_pair g (L.U k) A.1 y hy (h hy)
    refine ⟨B, hB, hyB, ?_⟩
    have h1 : resG X hV ((σ j).f k) ∈ J.ideal V := by
      rw [hJ.2 k V hV]
      exact Ideal.subset_span ⟨j, rfl⟩
    have h2 := appLE_mem_ideal_comap J g V B hBV h1
    rw [appLE_resG] at h2
    rwa [resG_appLE]

theorem generatesAlong_comap_of_generates (X W : Scheme.{0}) (J : X.IdealSheafData) (L : LB X) (m : ℕ)
    (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (hJ : Generates J σ) : GeneratesAlong (J.comap g) σ g :=
  hJ.generatesAlong_comap g

end GlobalTheory.ProjBlowup
end
end

