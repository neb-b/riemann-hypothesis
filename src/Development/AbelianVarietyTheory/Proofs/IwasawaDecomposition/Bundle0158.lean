module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RePosOfIsMultIP
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchurConst

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem left_cont_of_mem (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M)
    (hT : T ∈ Mult θ M J χ) (v : M.Vec) :
    Continuous (T v) ∧ ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g := by
  unfold Mult at hT
  induction hT using Submodule.span_induction with
  | mem x hx => exact ⟨(IsMultMap.aut hx v).cont, (IsMultMap.aut hx v).left⟩
  | zero => exact ⟨continuous_const, fun _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    refine ⟨hx.1.add hy.1, fun γ hγ g => ?_⟩
    show x v (γ * g) + y v (γ * g) = x v g + y v g
    rw [hx.2 γ hγ, hy.2 γ hγ]
  | smul a x _ hx =>
    refine ⟨hx.1.const_smul a, fun γ hγ g => ?_⟩
    show a • x v (γ * g) = a • x v g
    rw [hx.2 γ hγ]

theorem eq_zero_of_ae (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) (φ : GA D V → ℂ) (hc : Continuous φ)
    (hL : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) (h2 : ∀ᵐ g ∂(μ.restrict 𝓕), φ g = 0) : φ = 0 := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ V)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ V) μ
  let t : Set (GA D V) := {g | φ g ≠ 0}
  have ht : IsOpen t := hc.isOpen_preimage _ isOpen_ne
  have htm : MeasurableSet t := ht.measurableSet
  have h3 : μ (t ∩ 𝓕) = 0 := by
    rw [← Measure.restrict_apply htm]
    exact ae_iff.1 h2
  have hinv : ∀ γ : GQ V, γ • t = t := by
    intro γ
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show φ (((γ⁻¹ : GQ V) : GA D V) * g) ≠ 0 ↔ φ g ≠ 0
    rw [hL _ (γ⁻¹).2]
  have h4 : μ t = 0 := hF.measure_zero_of_invariant t hinv h3
  have h5 : t = ∅ := (ht.measure_eq_zero_iff μ).1 h4
  funext g
  by_contra hg
  have : g ∈ t := hg
  rw [h5] at this
  exact this

theorem exists_vec (M : DSModel V S) (h : ∀ τ, M.sm τ ≠ ⊥) :
    ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0 := by
  choose w hw hw0 using fun τ => (Submodule.ne_bot_iff _).1 (h τ)
  refine ⟨fun τ => ⟨w τ, hw τ⟩, Finset.prod_ne_zero_iff.2 fun τ _ => ?_⟩
  exact fun e => hw0 τ (inner_self_eq_zero.1 e)

theorem isMultiplicityInner_add_smul_right (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' T'' : MMap M)
    {a b : ℂ} (c : ℂ) (h : IsMultIP M μ 𝓕 T T' a) (h' : IsMultIP M μ 𝓕 T T'' b) :
    IsMultIP M μ 𝓕 T (T' + c • T'') (a + c * b) := by
  intro v v'
  have e : (fun g => star (T v g) * (T' + c • T'') v' g) =
      fun g => star (T v g) * T' v' g + c * (star (T v g) * T'' v' g) := by
    funext g
    show star (T v g) * (T' v' g + c * T'' v' g) = _
    ring
  have i2 : IntegrableOn (fun g => c * (star (T v g) * T'' v' g)) 𝓕 μ := (h' v v').1.const_mul c
  rw [e]
  refine ⟨(h v v').1.add i2, ?_⟩
  rw [integral_add (h v v').1 i2, integral_const_mul, (h v v').2, (h' v v').2]
  ring

theorem isMultiplicityInner_symm (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M)
    {a : ℂ} (h : IsMultIP M μ 𝓕 T T' a) : IsMultIP M μ 𝓕 T' T (star a) := by
  intro v v'
  have e : (fun g => star (T' v g) * T v' g) = fun g => (starRingEnd ℂ) (star (T v' g) * T' v g) := by
    funext g
    rw [starRingEnd_apply, star_mul, star_star]
  rw [e]
  refine ⟨?_, ?_⟩
  · exact (Complex.conjCLE.toContinuousLinearMap.integrable_comp (h v' v).1 :)
  · rw [integral_conj, (h v' v).2, map_mul, map_prod]
    simp only [inner_conj_symm]
    rfl

theorem re_pos_of_isMultIP (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) (T : MMap M) {a : ℂ} (h : IsMultIP M μ 𝓕 T T a) (v : M.Vec)
    (hc : Continuous (T v)) (hL : ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g) (h0 : T v ≠ 0) : 0 < a.re := by
  obtain ⟨hi, he⟩ := h v v
  have e : (fun g => star (T v g) * T v g) = fun g => ((‖T v g‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  rw [e] at hi he
  have hi' : IntegrableOn (fun g => ‖T v g‖ ^ 2) 𝓕 μ := by
    have := hi.re
    simp only [RCLike.re_to_complex, Complex.ofReal_re] at this
    exact this
  rw [integral_complex_ofReal] at he
  have e2 : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = ((∏ τ, ‖(v τ : M.H τ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [e2] at he
  have he' := congrArg Complex.re he
  rw [Complex.ofReal_re, Complex.re_mul_ofReal] at he'
  have hp : 0 ≤ ∏ τ, ‖(v τ : M.H τ)‖ ^ 2 := Finset.prod_nonneg fun τ _ => by positivity
  have hnn : 0 ≤ ∫ g in 𝓕, ‖T v g‖ ^ 2 ∂μ := integral_nonneg fun g => by positivity
  have hne : ∫ g in 𝓕, ‖T v g‖ ^ 2 ∂μ ≠ 0 := by
    intro hz
    have := (integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi').1 hz
    refine h0 (eq_zero_of_ae μ 𝓕 hμ hF _ hc hL ?_)
    filter_upwards [this] with g hg
    simpa using hg
  have hpos : 0 < a.re * ∏ τ, ‖(v τ : M.H τ)‖ ^ 2 := he' ▸ lt_of_le_of_ne hnn hne.symm
  by_contra hn
  exact absurd hpos (not_lt.2 (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hn) hp))

theorem ipM_posDef : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M J χ μ 𝓕 → (∀ τ, M.sm τ ≠ ⊥) → (∀ T ∈ Mult θ M J χ, ∀ T' ∈ Mult θ M J χ, ∀ T'' ∈ Mult θ M J χ, ∀ c : ℂ, ipM M μ 𝓕 T (T' + c • T'') = ipM M μ 𝓕 T T' + c * ipM M μ 𝓕 T T'' ∧ ipM M μ 𝓕 T' T = star (ipM M μ 𝓕 T T')) ∧ ∀ T ∈ Mult θ M J χ, T ≠ 0 → 0 < (ipM M μ 𝓕 T T).re := by
  intro D θ V S M J χ μ 𝓕 hθ hμ hF hS hsm
  obtain ⟨v0, hv0⟩ := exists_vec M hsm
  have hs : ∀ T ∈ Mult θ M J χ, ∀ T' ∈ Mult θ M J χ, IsMultIP M μ 𝓕 T T' (ipM M μ 𝓕 T T') :=
    fun T hT T' hT' => ipM_spec M μ 𝓕 T T' (hS hθ hμ hF T hT T' hT')
  refine ⟨fun T hT T' hT' T'' hT'' c => ⟨?_, ?_⟩, fun T hT h0 => ?_⟩
  · exact hasPeterssonInner_unique M μ 𝓕 _ _ v0 hv0
      (hs T hT _ (Submodule.add_mem _ hT' (Submodule.smul_mem _ c hT'')))
      (isMultiplicityInner_add_smul_right M μ 𝓕 T T' T'' c (hs T hT T' hT') (hs T hT T'' hT''))
  · exact hasPeterssonInner_unique M μ 𝓕 _ _ v0 hv0 (hs T' hT' T hT) (isMultiplicityInner_symm M μ 𝓕 T T' (hs T hT T' hT'))
  · obtain ⟨v, hv⟩ : ∃ v, T v ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact h0 (MultilinearMap.ext hn)
    have := left_cont_of_mem θ M J χ T hT v
    exact re_pos_of_isMultIP M μ 𝓕 hμ hF T (hs T hT T hT) v this.1 this.2 hv

end GlobalTheory.SchurConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductTailSplitFiniteFactors
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.TailSplit

theorem tprod_split {ι : Type} (a : ι → ℝ) (ha : Summable fun v => |a v - 1|) (S T S' : Finset ι)
    (h : ∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) (hd : Disjoint S T) :
    ∏' v : {v : ι // v ∉ S}, a v.1 = (∏ v ∈ T, a v) * ∏' v : {v : ι // v ∉ S'}, a v.1 := by
  classical
  have e1 : ∏' v : {v : ι // v ∉ S}, a v.1 = ∏' v, Set.mulIndicator {v | v ∉ S} a v :=
    tprod_subtype {v | v ∉ S} a
  have e2 : ∏' v : {v : ι // v ∉ S'}, a v.1 = ∏' v, Set.mulIndicator {v | v ∉ S'} a v :=
    tprod_subtype {v | v ∉ S'} a
  have m2 : Multipliable fun v => Set.mulIndicator {v | v ∉ S'} a v := by
    have : Summable fun v => ‖Set.mulIndicator {v | v ∉ S'} a v - 1‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => ?_) ha
      by_cases hv : v ∈ S'
      · simp [Set.mulIndicator, hv]
      · simp [Set.mulIndicator, hv]
    simpa using multipliable_one_add_of_summable this
  have m1 : HasProd (fun v => Set.mulIndicator (T : Set ι) a v) (∏ v ∈ T, a v) := by
    have : HasProd (fun v => Set.mulIndicator (T : Set ι) a v)
        (∏ v ∈ T, Set.mulIndicator (T : Set ι) a v) :=
      hasProd_prod_of_ne_finset_one fun v hv => by simp [Set.mulIndicator, hv]
    rwa [Finset.prod_congr rfl (fun v hv => Set.mulIndicator_of_mem (by simpa using hv) a)] at this
  rw [e1, e2, ← (m1.mul m2.hasProd).tprod_eq]
  refine tprod_congr fun v => ?_
  by_cases hS : v ∈ S
  · have hT : v ∉ T := Finset.disjoint_left.1 hd hS
    simp [Set.mulIndicator, h, hS, hT]
  · by_cases hT : v ∈ T <;> simp [Set.mulIndicator, h, hS, hT]

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (S T S' : Finset (HeightOneSpectrum (𝓞 F))), Conv b mi mv → (∀ v, v ∈ S' ↔ v ∈ S ∨ v ∈ T) → Disjoint S T → tailProd b mv S = (∏ v ∈ T, mv v (latV b v)) * tailProd b mv S' := by
  intro F E _ _ _ _ _ d b n M mi mv S T S' hc h hd
  obtain ⟨-, hfin, hsum⟩ := hc
  have hne : ∀ v, mv v (latV b v) ≠ ∞ := by
    intro v
    have hk : IsCompact (intV b v) :=
      ((GlobalTheory.GaugeEx.IntBasis.main F E (AlgHom.id F E) d b).1 v).1
    have hk2 : IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
      have : (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
          Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => intV b v := by
        ext Y
        rw [mem_latV_iff]
        simp [Set.mem_pi]
      rw [this]
      exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hk
    have := hfin v
    exact hk2.measure_lt_top.ne
  unfold tailProd
  rw [tprod_split (fun v => (mv v (latV b v)).toReal) hsum S T S' h hd,
    ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg),
    ENNReal.ofReal_prod_of_nonneg fun _ _ => ENNReal.toReal_nonneg]
  congr 1
  exact Finset.prod_congr rfl fun v _ => ENNReal.ofReal_toReal (hne v)

end GlobalTheory.GaugeEx.TailSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumEqTraceOriented
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

namespace GlobalTheory.OrientedSmall

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {R : Type} [CommRing R] (c : R →+* R) {n m : ℕ}

theorem sum_eq_trace_oriented (P : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R)
    (x y : Matrix (Fin m) (Fin n) R) :
    ∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * K e d * x d a = (P * (y.map c)ᵀ * K * x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b, ∑ e, ∑ d, P a b * c (y e b) * K e d * x d a
      = ∑ e, ∑ b, ∑ d, P a b * c (y e b) * K e d * x d a := Finset.sum_comm
    _ = ∑ e, ∑ d, ∑ b, P a b * c (y e b) * K e d * x d a := Finset.sum_congr rfl fun e _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem trace_coord (J P : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R)
    (hPJ : P * J = 1) (hP : P.map c = Pᵀ) (x y : Matrix (Fin m) (Fin n) R) :
    (P * (y.map c)ᵀ * K * x).trace = ((((y * P)ᵀ).map c)ᵀ * Jᵀ * (x * P)ᵀ * Kᵀ).trace := by
  have e1 : Jᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hPJ, Matrix.transpose_one]
  rw [Matrix.transpose_map, Matrix.transpose_transpose, Matrix.map_mul, hP, Matrix.transpose_mul]
  calc (P * (y.map c)ᵀ * K * x).trace
      = (P * (y.map c)ᵀ * (K * x)).trace := by simp only [Matrix.mul_assoc]
    _ = (K * x * (P * (y.map c)ᵀ)).trace := Matrix.trace_mul_comm _ _
    _ = (K * x * (P * (y.map c)ᵀ))ᵀ.trace := (Matrix.trace_transpose _).symm
    _ = (y.map c * Pᵀ * xᵀ * Kᵀ).trace := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = (y.map c * Pᵀ * (Jᵀ * Pᵀ) * xᵀ * Kᵀ).trace := by rw [e1, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem act_coord (J P g g' : Matrix (Fin n) (Fin n) R) (h : Matrix (Fin m) (Fin m) R)
    (hPJ : P * J = 1) (hg : (g.map c)ᵀ * J * g = J) (hgg : g * g' = 1) (x : Matrix (Fin m) (Fin n) R) :
    (h * x * g' * P)ᵀ = g.map c * (x * P)ᵀ * hᵀ := by
  have hJP : J * P = 1 := mul_eq_one_comm.1 hPJ
  have key : g' * P = P * (g.map c)ᵀ := by
    calc g' * P = (P * J) * g' * P := by rw [hPJ, Matrix.one_mul]
      _ = P * ((g.map c)ᵀ * J * g) * g' * P := by rw [hg]
      _ = P * (g.map c)ᵀ * (J * ((g * g') * P)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hgg, Matrix.one_mul, hJP, Matrix.mul_one]
  rw [Matrix.mul_assoc (h * x), key]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

end Generic

variable {D : D7}

theorem cA_incA (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp [cA, sigR, incA, inclR, CMData.sig, starRingEnd_apply]

theorem gram_conjTranspose (V : HSp D) : V.gramᴴ = V.gram := by
  refine Matrix.ext fun i j => ?_
  exact V.herm.eq (V.frame j) (V.frame i)

theorem gramInv_mul (V : HSp D) : (V.gram⁻¹).map (incA D) * V.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem gramInv_map (V : HSp D) :
    ((V.gram⁻¹).map (incA D)).map (cA D) = ((V.gram⁻¹).map (incA D))ᵀ := by
  have h : (V.gram⁻¹)ᴴ = V.gram⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, gram_conjTranspose]
  ext i j
  have := congrFun (congrFun h j) i
  rw [Matrix.conjTranspose_apply] at this
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  rw [cA_incA, this]

theorem mt_mul_inv (V : HSp D) (g : GA D V) :
    Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem hO_eq (S T : HSp D) (hr : S.rank ≤ T.rank) (x y : WO S T) :
    hO S T x y = hHom S T (toTWsmall S T y) (toTWsmall S T x) := by
  unfold hO hHom
  rw [if_pos hr]
  have s := sum_eq_trace (cA D) (S.gram.map (incA D)) (T.gram.map (incA D))
    (toTWsmall S T y) (toTWsmall S T x)
  have s' := sum_eq_trace_oriented (cA D) ((S.gram⁻¹).map (incA D)) (T.gram.map (incA D)) x y
  simp only [Matrix.map_apply] at s s'
  rw [s, s']
  exact trace_coord (cA D) _ _ _ (gramInv_mul S) (gramInv_map S) x y

theorem bridgeSmall (D : D7) : BridgeSmall D := by
  intro S T hr
  refine ⟨fun x y => ?_, fun g h x => ?_⟩
  · unfold symplO sympl
    rw [hO_eq S T hr]
  · unfold actHom
    rw [if_pos hr]
    exact act_coord (cA D) _ _ _ _ _ (gramInv_mul S) (mt_rel S g) (mt_mul_inv S g) x

end GlobalTheory.OrientedSmall

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightedProjectiveEmbeddingSep
section
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory

namespace GlobalTheory.AmpleSeparateOverRing

theorem isSeparated_toSpecZ (R : Type) [CommRing R] (n : ℕ) :
    IsSeparated (specZIsTerminal.from (PSpace R n)) := by
  have : IsProper (PSpace.str R n) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R n
  rw [specZIsTerminal.hom_ext (specZIsTerminal.from (PSpace R n)) (PSpace.str R n ≫ specZIsTerminal.from _)]
  infer_instance

theorem exists_ample_model (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R)
    (ι : Type) (L : ι → LB X) (hL : ∀ i, (L i).IsLB) (M : ι → ℕ)
    (t : ∀ i, Fin (M i + 1) → (L i).Sec)
    (ht : ∀ i, ⨆ m, nonzeroLocus (t i m) = ⊤) (w : ι → ℕ) (hw : ∀ i, 1 ≤ w i)
    (T : Finset ι) :
    ∃ (Q : Scheme.{0}) (Ψ : X ⟶ Q) (r : Q ⟶ Sp R) (N : LB Q) (hN : IsAmpleLB N), IsSeparated r ∧
      Ψ ≫ r = f ∧
      CechPic.cls (N.pull Ψ) (LB.isLB_pull hN.isLB Ψ) = ∑ i ∈ T, (w i : ℤ) • CechPic.cls (L i) (hL i) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (a a' : Sp K ⟶ X), a ≫ Ψ = a' ≫ Ψ →
        a ≫ f = a' ≫ f ∧ ∀ i ∈ T,
          a ≫ ProjSpace.toProj f (t i) (ht i) = a' ≫ ProjSpace.toProj f (t i) (ht i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨Sp R, f, 𝟙 _, LB.triv _, isAmpleLB_of_isAffine (LB.isLB_triv _), inferInstance,
      Category.comp_id _, ?_, ?_⟩
    · rw [Finset.sum_empty]
      exact map_zero (CechPic.pull f)
    · intro K _ _ a a' h
      exact ⟨h, by simp⟩
  | insert i T hi ih =>
    obtain ⟨Q, Ψ, r, N, hN, hr, hΨ, hc, hinj⟩ := ih
    have hO1 := ProjSpace.O1_isLB R (M i)
    have hO : IsAmpleLB (lbPow (ProjSpace.O1 R (M i)) (w i)) :=
      (isAmpleLB_pow_iff hO1 (hw i)).2 (isAmple_projective_O_one R (M i))
    have : IsSeparated (specZIsTerminal.from (PSpace R (M i))) := isSeparated_toSpecZ R (M i)
    have hNp := LB.isLB_pull hN.isLB (pullback.fst (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i))))
    have hOq := LB.isLB_pull hO.isLB (pullback.snd (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i))))
    have hN' := CechPic.isLB_tens hNp hOq
    have hA : IsAmpleLB (CechPic.tens
        (N.pull (pullback.fst (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i)))))
        ((lbPow (ProjSpace.O1 R (M i)) (w i)).pull
          (pullback.snd (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i)))))) := by
      refine hN.box hO hN' (IsPullback.of_hasPullback _ _) ?_
      refine (CechPic.cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN' hNp) hOq)).1 ?_
      rw [CechPic.cls_div (LB.isLB_div hN' hNp) hOq, CechPic.cls_div hN' hNp, CechPic.cls_tens hNp hOq]
      abel
    refine ⟨_, pullback.lift Ψ (ProjSpace.toProj f (t i) (ht i)) (specZIsTerminal.hom_ext _ _),
      pullback.fst _ _ ≫ r, _, hA, inferInstance, by rw [← Category.assoc, pullback.lift_fst, hΨ], ?_, ?_⟩
    · rw [Finset.sum_insert hi, ← hc]
      have e := (CechPic.cls_eq_iff (LB.isLB_pull hO1 (ProjSpace.toProj f (t i) (ht i))) (hL i)).2
        (ProjSpace.lbIso_pullback_O1_toProj f (t i) (ht i))
      rw [← e, CechPic.cls_pull hN' _, CechPic.cls_tens hNp hOq, map_add (f := _), CechPic.cls_pull hN.isLB,
        CechPic.cls_pull hO.isLB, ← CechPic.pull_comp, ← CechPic.pull_comp, pullback.lift_fst,
        pullback.lift_snd, CechPic.cls_lbPow hO1, map_nsmul, CechPic.cls_pull hN.isLB,
        CechPic.cls_pull hO1, add_comm, natCast_zsmul]
    · intro K _ _ a a' h
      have h1 : a ≫ Ψ = a' ≫ Ψ := by
        have := congrArg (· ≫ pullback.fst (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i)))) h
        simp only [Category.assoc] at this
        rwa [pullback.lift_fst] at this
      have h2 : a ≫ ProjSpace.toProj f (t i) (ht i) = a' ≫ ProjSpace.toProj f (t i) (ht i) := by
        have := congrArg (· ≫ pullback.snd (specZIsTerminal.from Q) (specZIsTerminal.from (PSpace R (M i)))) h
        simp only [Category.assoc] at this
        rwa [pullback.lift_snd] at this
      obtain ⟨e1, e2⟩ := hinj K a a' h1
      refine ⟨e1, fun j hj => ?_⟩
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact h2
      · exact e2 j hj

end GlobalTheory.AmpleSeparateOverRing
end

