module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.BaseChangeIndex
public import GroundTheory.GlobalFields.LocalFieldAtPlace

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PBaseChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField TensorProduct ComplexAt GroundTheory.Heights₂.Heights

noncomputable section

section GramDet

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]


omit [NumberField K] [NumberField L] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] in
theorem baseChangeCoord_one_tmul (τ : L →+* ℂ) (e : E) :
    baseChangeCoord τ ((1 : ComplexAt τ) ⊗ₜ ((1 : 𝓞 L) ⊗ₜ[𝓞 K] e)) =
      (1 : ComplexAt (τ.comp (algebraMap K L))) ⊗ₜ e := by
  rw [baseChangeCoord_tmul]
  congr 1
  simp

theorem gramDet_baseChange (h : HermitianMetric K E) (τ : L →+* ℂ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : ι → E) :
    gramDet (h.baseChange L) τ (fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) =
      gramDet h (τ.comp (algebraMap K L)) s := by
  have hv : ∀ i j, inner ℂ (fibreVec (h.baseChange L) τ ((1 : 𝓞 L) ⊗ₜ[𝓞 K] s i))
      (fibreVec (h.baseChange L) τ ((1 : 𝓞 L) ⊗ₜ[𝓞 K] s j)) =
      inner ℂ (fibreVec h (τ.comp (algebraMap K L)) (s i))
        (fibreVec h (τ.comp (algebraMap K L)) (s j)) := by
    intro i j
    rw [fibreVec, fibreVec, FibreSpace.inner_equiv]
    change inner ℂ (FibreSpace.equiv h _ (baseChangeCoord τ _))
      (FibreSpace.equiv h _ (baseChangeCoord τ _)) = _
    rw [baseChangeCoord_one_tmul, baseChangeCoord_one_tmul]
    rfl
  simp only [gramDet]
  congr 2
  ext i j
  simp only [Matrix.gram_apply, hv]

end GramDet

theorem BaseChange.proof : BaseChange.Statement := by
  intro K _ _ L _ _ _ M
  classical
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := M.carrier)
  set N := Submodule.span (𝓞 K) (Set.range s)
  have hrank : Module.finrank (𝓞 L) (𝓞 L ⊗[𝓞 K] M.carrier) = Module.finrank (𝓞 K) M.carrier :=
    (TensorProduct.isBaseChange (𝓞 K) M.carrier (𝓞 L)).finrank_eq

  let b : Module.Basis (Fin (Module.finrank (𝓞 K) M.carrier)) (𝓞 K) N := Module.Basis.span hs
  let bL := Algebra.TensorProduct.basis (𝓞 L) b
  let f : 𝓞 L ⊗[𝓞 K] N →ₗ[𝓞 L] 𝓞 L ⊗[𝓞 K] M.carrier :=
    AlgebraTensorModule.lTensor (𝓞 L) (𝓞 L) N.subtype
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.injective_subtype
  have hfb : (f ∘ bL) = fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i := by
    funext i
    simp only [Function.comp_apply, bL, f, b, Algebra.TensorProduct.basis_apply,
      AlgebraTensorModule.lTensor_tmul, Submodule.subtype_apply]
    rw [Module.Basis.span_apply]
  have ht : LinearIndependent (𝓞 L) (fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) := by
    rw [← hfb]
    exact bL.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  have hspan : Submodule.span (𝓞 L) (Set.range fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) =
      LinearMap.range f := by
    rw [LinearMap.range_eq_map, ← bL.span_eq, Submodule.map_span, ← Set.range_comp, hfb]

  have hfin : Finite (M.carrier ⧸ N) := finite_quotient_span hs (Fintype.card_fin _)
  have hidx : Nat.card ((𝓞 L ⊗[𝓞 K] M.carrier) ⧸
      Submodule.span (𝓞 L) (Set.range fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i)) =
      Nat.card (M.carrier ⧸ N) ^ Module.finrank K L := by
    rw [hspan, ← card_tensor_integers L]
    exact Nat.card_congr (AlgebraTensorModule.tensorQuotientEquiv (𝓞 L) (𝓞 K) (𝓞 L) N).toEquiv.symm

  have hn : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  show arithDegree (M.metric.baseChange L) / Module.finrank ℚ L =
    arithDegree M.metric / Module.finrank ℚ K
  rw [arithDegree_eq (M.metric.baseChange L) ht (by rw [Fintype.card_fin]; exact hrank.symm),
    arithDegree_eq M.metric hs (Fintype.card_fin _), ← Module.finrank_mul_finrank ℚ K L]
  simp only [degreeWith, gramDet_baseChange]
  rw [hidx, sum_comp_algebraMap L (fun σ ↦ Real.log (gramDet M.metric σ s)), Nat.cast_pow,
    Real.log_pow, Nat.cast_mul]
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PDiagonalChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]

theorem span_fibreVec_eq_top (h : HermitianMetric K E) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    {s : ι → E} (hs : LinearIndependent (𝓞 K) s)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) :
    Submodule.span ℂ (Set.range fun i ↦ fibreVec h σ (s i)) = ⊤ := by
  set N := Submodule.span (𝓞 K) (Set.range s)
  have := finite_quotient_span hs hcard
  set m := Nat.card (E ⧸ N)
  have hm : 0 < m := Nat.card_pos
  have hmem : ∀ e : E, m • e ∈ N := fun e ↦
    (Submodule.Quotient.mk_eq_zero N).mp (by rw [Submodule.Quotient.mk_smul]; exact card_nsmul_eq_zero')
  set W := Submodule.span ℂ (Set.range fun i ↦ fibreVec h σ (s i))
  have h1 : ∀ e ∈ N, fibreVec h σ e ∈ W := by
    intro e he
    induction he using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp [fibreVec]
    | add x y _ _ hx hy => rw [fibreVec_add]; exact W.add_mem hx hy
    | smul a x _ hx => rw [fibreVec_smul]; exact W.smul_mem _ hx
  have h2 : ∀ e : E, fibreVec h σ e ∈ W := by
    intro e
    have := h1 _ (hmem e)
    rw [← Nat.cast_smul_eq_nsmul (𝓞 K) m e, fibreVec_smul] at this
    have hc : (σ ((m : 𝓞 K) : K)) = (m : ℂ) := by simp
    rw [hc] at this
    exact (W.smul_mem_iff (Nat.cast_ne_zero.mpr hm.ne')).mp this
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := (FibreSpace.equiv h σ).surjective x
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact W.zero_mem
  | add y z hy hz => rw [map_add (f := _)]; exact W.add_mem hy hz
  | tmul z e =>
    have hz : (z ⊗ₜ[𝓞 K] e : Fibre σ E) = ((ofComplex σ).symm z) • ((1 : ComplexAt σ) ⊗ₜ e) := by
      rw [← fibre_smul_eq, smul_tmul', smul_eq_mul, mul_one]
    rw [hz, map_smul]
    exact W.smul_mem _ (h2 e)

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PExactSequence
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField TensorProduct ComplexAt

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace HermitianBundle

variable (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F)

theorem quotFibreMap_mkQ_of_orthogonal (σ : K →+* ℂ) (x : Fibre σ M.carrier)
    (hx : FibreSpace.equiv M.metric σ x ∈ (subFibre M.metric σ F)ᗮ) :
    quotFibreMap M F hF σ (fibreMap σ F.mkQ x) = FibreSpace.equiv M.metric σ x := by
  have := quot_projective hF
  set V := subFibre M.metric σ F
  set z := fibreMap σ (quotSection M F hF) (fibreMap σ F.mkQ x) - x with hzdef
  have hex := lTensor_exact (ComplexAt σ) (LinearMap.exact_subtype_mkQ F) F.mkQ_surjective
  have h0 : F.mkQ.lTensor (ComplexAt σ) z = 0 := by
    change fibreMap σ F.mkQ z = 0
    rw [hzdef, map_sub, fibreMap_fibreMap, fibreMap_fibreMap,
      mkQ_comp_quotSection, LinearMap.id_comp, sub_self]
  obtain ⟨y, hy⟩ := (hex z).mp h0
  have hz : FibreSpace.equiv M.metric σ z ∈ V := ⟨y, congrArg (FibreSpace.equiv M.metric σ) hy⟩
  have hsplit : FibreSpace.equiv M.metric σ (fibreMap σ (quotSection M F hF) (fibreMap σ F.mkQ x)) =
      FibreSpace.equiv M.metric σ x + FibreSpace.equiv M.metric σ z := by
    rw [hzdef, map_sub]
    abel
  change Vᗮ.starProjection
      (FibreSpace.equiv M.metric σ (fibreMap σ (quotSection M F hF) (fibreMap σ F.mkQ x))) = _
  rw [hsplit, map_add (f := _), Submodule.starProjection_orthogonal_apply_eq_zero hz, add_zero,
    Submodule.starProjection_eq_self_iff.mpr hx]

def subQuotExtension : HermitianExtension (M.sub F) M (M.quot F hF) where
  incl := F.subtype
  proj := F.mkQ
  incl_injective := F.injective_subtype
  proj_surjective := F.mkQ_surjective
  exact := LinearMap.exact_subtype_mkQ F
  incl_isometric _ _ _ := rfl
  proj_coisometric σ x y hx hy := by
    have hmem : ∀ z : Fibre σ M.carrier,
        (∀ w, (M.metric.form σ).inner (F.subtype.lTensor (ComplexAt σ) w) z = 0) →
          FibreSpace.equiv M.metric σ z ∈ (subFibre M.metric σ F)ᗮ := by
      intro z hz
      rw [Submodule.mem_orthogonal]
      rintro u ⟨w, rfl⟩
      exact hz w
    change inner ℂ (quotFibreMap M F hF σ (fibreMap σ F.mkQ x))
      (quotFibreMap M F hF σ (fibreMap σ F.mkQ y)) = _
    rw [quotFibreMap_mkQ_of_orthogonal M F hF σ x (hmem x hx),
      quotFibreMap_mkQ_of_orthogonal M F hF σ y (hmem y hy)]
    rfl

end HermitianBundle

namespace LatticeLemmas

end LatticeLemmas

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField IsDedekindDomain TensorProduct ComplexAt
open GroundTheory.Heights₂.Heights

universe u v

noncomputable section

section Congr

variable {K : Type*} [Field K] [NumberField K]
variable {E E' : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] [AddCommGroup E'] [Module (𝓞 K) E'] [Module.Finite (𝓞 K) E']
  [Module.Projective (𝓞 K) E']

end Congr

section Lattices

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

end Lattices

theorem finrank_submodule_eq {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    (F : Submodule R M) (hF : ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x ∈ F) :
    Module.finrank R F = Module.finrank R M := by
  have h0 : Module.rank R (M ⧸ F) = 0 := by
    rw [rank_eq_zero_iff]
    intro x
    obtain ⟨x, rfl⟩ := F.mkQ_surjective x
    obtain ⟨a, ha, hax⟩ := hF x
    refine ⟨a, ha, ?_⟩
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hax
  have h := rank_quotient_add_rank_of_isDomain F
  rw [h0, zero_add] at h
  simp only [Module.finrank, h]

section Local

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


end Local

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalLatticeIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField IsDedekindDomain TensorProduct Module

noncomputable section

section Card

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem LocalLatticeIndex.norm_unit (u : (v.adicCompletionIntegers K)ˣ) :
    ‖((u : v.adicCompletionIntegers K) : v.adicCompletion K)‖ = 1 := by
  have h1 := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).1 u.isUnit
  have h0 : ((u : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
    intro h
    exact u.ne_zero (Subtype.ext h)
  rw [← GroundTheory.Global.normalizedAbv_apply, GroundTheory.Global.normalizedAbv_eq_zpow v h0]
  rw [show Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 from h1]
  simp

theorem LocalLatticeIndex.card_quot_span {a : v.adicCompletionIntegers K} (ha : a ≠ 0) :
    (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {a}) : ℝ) =
      ‖(a : v.adicCompletion K)‖⁻¹ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hne : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ≠ ⊥ := by
    rw [hϖ.maximalIdeal_eq, Ne, Ideal.span_singleton_eq_bot]
    exact hϖ.ne_zero
  have hcard : Nat.card (v.adicCompletionIntegers K ⧸
      Ideal.span {(u : v.adicCompletionIntegers K) * ϖ ^ n}) = Ideal.absNorm v.asIdeal ^ n := by
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime hne,
      Submodule.cardQuot_apply, ← GroundTheory.Global.natCard_residueField_adicCompletionIntegers v]
    rfl
  have hϖn : ‖(ϖ : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ :=
    GroundTheory.Global.normalizedAbv_of_irreducible v hϖ
  rw [hcard, Nat.cast_pow]
  push_cast
  rw [norm_mul, norm_pow, LocalLatticeIndex.norm_unit, hϖn, one_mul, inv_pow, inv_inv]

end Card

section General

variable {K : Type*} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
  {E : Type*} [AddCommGroup E] [Module (v.adicCompletion K) E]
  [Module (v.adicCompletionIntegers K) E]
  [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) E]

theorem LocalLatticeIndex.isTorsionFree (A : Submodule (v.adicCompletionIntegers K) E) :
    Module.IsTorsionFree (v.adicCompletionIntegers K) A := by
  refine .of_smul_eq_zero fun r x h => ?_
  have h' : algebraMap _ (v.adicCompletion K) r • (x : E) = 0 := by
    rw [algebraMap_smul, ← Submodule.coe_smul, h, Submodule.coe_zero]
  rcases smul_eq_zero.1 h' with hr | hx
  · exact Or.inl ((FaithfulSMul.algebraMap_injective _ (v.adicCompletion K)).eq_iff' (map_zero _) |>.1 hr)
  · exact Or.inr (Subtype.ext hx)

theorem LocalLatticeIndex.index_eq_det (A B : Submodule (v.adicCompletionIntegers K) E)
    (g : E ≃ₗ[v.adicCompletion K] E) (hfg : A.FG)
    (hsp : Submodule.span (v.adicCompletion K) (A : Set E) = ⊤)
    (hB : (B : Set E) = g '' A) (hBA : B ≤ A) :
    (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
      ‖LinearMap.det (g : E →ₗ[v.adicCompletion K] E)‖⁻¹ := by
  classical
  have := LocalLatticeIndex.isTorsionFree A
  have : Module.Finite (v.adicCompletionIntegers K) A := Module.Finite.iff_fg.2 hfg
  set ι := Module.Free.ChooseBasisIndex (v.adicCompletionIntegers K) A
  let b := Module.Free.chooseBasis (v.adicCompletionIntegers K) A

  have hli : LinearIndependent (v.adicCompletion K) (fun i => (b i : E)) := by
    rw [← LinearIndependent.iff_fractionRing (v.adicCompletionIntegers K) (v.adicCompletion K)]
    exact b.linearIndependent.map' A.subtype (Submodule.ker_subtype A)
  have hspanR : Submodule.span (v.adicCompletionIntegers K) (Set.range fun i => (b i : E)) = A := by
    have : (Set.range fun i => (b i : E)) = A.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hsp' : ⊤ ≤ Submodule.span (v.adicCompletion K) (Set.range fun i => (b i : E)) := by
    rw [← hsp]
    apply Submodule.span_le.2
    intro x hx
    have hx' : x ∈ Submodule.span (v.adicCompletionIntegers K) (Set.range fun i => (b i : E)) := by
      rw [hspanR]; exact hx
    exact Submodule.span_le_restrictScalars (v.adicCompletionIntegers K) (v.adicCompletion K) _ hx'
  let c : Basis ι (v.adicCompletion K) E := Basis.mk hli hsp'
  have hc : ∀ i, c i = (b i : E) := fun i => Basis.mk_apply hli hsp' i
  have hrepr : ∀ (x : A) (i : ι),
      c.repr (x : E) i = algebraMap _ (v.adicCompletion K) (b.repr x i) := by
    intro x i
    have hx : (x : E) = ∑ j, algebraMap _ (v.adicCompletion K) (b.repr x j) • c j := by
      calc (x : E) = ((∑ j, b.repr x j • b j : A) : E) := by rw [b.sum_repr]
        _ = ∑ j, algebraMap _ (v.adicCompletion K) (b.repr x j) • c j := by
          simp only [Submodule.coe_sum, Submodule.coe_smul, hc, algebraMap_smul]
    rw [hx, c.repr_sum_self]

  have hmaps : ∀ x ∈ A, (g.toLinearMap.restrictScalars (v.adicCompletionIntegers K)) x ∈ A := by
    intro x hx
    apply hBA
    show g x ∈ (B : Set E)
    rw [hB]
    exact ⟨x, hx, rfl⟩
  let φ : A →ₗ[v.adicCompletionIntegers K] A :=
    (g.toLinearMap.restrictScalars (v.adicCompletionIntegers K)).restrict hmaps
  have hφ : ∀ x : A, (φ x : E) = g x := fun x => rfl

  have hdet : LinearMap.det (g : E →ₗ[v.adicCompletion K] E) =
      algebraMap _ (v.adicCompletion K) (LinearMap.det φ) := by
    rw [← LinearMap.det_toMatrix c, ← LinearMap.det_toMatrix b, RingHom.map_det]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      LinearMap.toMatrix_apply, hc, LinearEquiv.coe_coe, ← hφ, hrepr]

  have hinj : Function.Injective φ := by
    intro x y h
    apply Subtype.ext
    apply g.injective
    rw [← hφ, ← hφ, h]
  have hrank : finrank _ (LinearMap.range φ) = finrank _ A := LinearMap.finrank_range_of_inj hinj
  set a := Submodule.smithNormalFormCoeffs b hrank
  let b' := Submodule.smithNormalFormTopBasis b hrank
  let ab := Submodule.smithNormalFormBotBasis b hrank
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b hrank

  have hcomap : Submodule.comap A.subtype B = LinearMap.range φ := by
    ext x
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range]
    constructor
    · intro hx
      have hx' : (x : E) ∈ (B : Set E) := hx
      rw [hB] at hx'
      obtain ⟨y, hy, hxy⟩ := hx'
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
    · rintro ⟨y, rfl⟩
      show g y ∈ (B : Set E)
      rw [hB]
      exact ⟨y, y.2, rfl⟩
  have hidx : B.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (A ⧸ LinearMap.range φ) := by
    rw [← hcomap, AddSubgroup.relIndex, AddSubgroup.index_eq_card]
    rfl
  have hq : Nat.card (A ⧸ LinearMap.range φ) =
      ∏ i, Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {a i}) := by
    rw [Nat.card_congr (Submodule.quotientEquivPiSpan (LinearMap.range φ) b hrank).toEquiv,
      Nat.card_pi]

  let w : Basis ι _ A := ab.map (LinearEquiv.ofInjective φ hinj).symm
  have hw : ∀ i, φ (w i) = a i • b' i := by
    intro i
    have h1 : φ (w i) = ((LinearEquiv.ofInjective φ hinj) (w i) : A) :=
      (LinearEquiv.ofInjective_apply _ _).symm
    rw [h1]
    simp only [w, Basis.map_apply, LinearEquiv.apply_symm_apply]
    exact Submodule.smithNormalFormBotBasis_def b hrank i
  have hdetprod : LinearMap.det φ * b'.det w = ∏ i, a i := by
    rw [← Basis.det_comp]
    have : (⇑φ ∘ ⇑w) = fun i => a i • b' i := funext hw
    rw [this, AlternatingMap.map_smul_univ, Basis.det_self, smul_eq_mul, mul_one]
  obtain ⟨u, hu⟩ := b'.isUnit_det w
  have hdetφ : LinearMap.det φ = (∏ i, a i) * ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) :
      v.adicCompletionIntegers K) := by
    rw [← hdetprod, ← hu, mul_assoc, Units.mul_inv, mul_one]
  have hu1 : ‖algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K)‖ = 1 :=
    LocalLatticeIndex.norm_unit v u⁻¹
  rw [hidx, hq, Nat.cast_prod, hdet, hdetφ, map_mul, map_prod, norm_mul, norm_prod, hu1, mul_one,
    ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun i _ => LocalLatticeIndex.card_quot_span v (ha i)

end General

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSublattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField GroundTheory.Heights₂.Heights

noncomputable section

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

