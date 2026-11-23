module

public import Mathlib
public import GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.CompletionsOverBasisRepr
public import GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol
public import GroundTheory.GlobalFields.FirstInequality

@[expose] public section

-- bundled from GroundTheory.GlobalFields.NormResidueSymbol.FunctorialInfinite
section
namespace GroundTheory.Global

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
  NumberField.ComplexEmbedding IdeleGroup
open scoped NumberField.LiesOver

noncomputable section

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']

theorem ideleNorm_infiniteEmbedding (v' : InfinitePlace K') (a : v'.Completionˣ) :
    ideleNorm K K' (infiniteEmbedding v' a) =
      infiniteEmbedding (v'.comap (algebraMap K K'))
        (LocalField.normUnits (v'.comap (algebraMap K K')).Completion v'.Completion a) := by
  classical
  apply Units.ext
  refine Prod.ext (funext fun w ↦ ?_) (FiniteAdeleRing.ext (K := K) fun v ↦ ?_)
  · rw [ideleNorm_fst]
    simp only [coe_infiniteEmbedding]
    by_cases hw : w = v'.comap (algebraMap K K')
    · subst hw
      rw [Finset.prod_eq_single (⟨v', (inferInstance : v'.LiesOver (v'.comap (algebraMap K K')))⟩ :
          (v'.comap (algebraMap K K')).placesOver K'),
        infiniteAdeleSingle_apply, infiniteAdeleSingle_apply, Pi.mulSingle_eq_same,
        Pi.mulSingle_eq_same, LocalField.coe_normUnits]
      · intro u _ hu
        rw [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne (fun h ↦ hu (Subtype.ext h)),
          map_one]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hw]
      refine Finset.prod_eq_one fun u _ ↦ ?_
      have hu : (u : InfinitePlace K') ≠ v' := by
        rintro h
        apply hw
        rw [← h]
        exact ((GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq w _).1 u.2).symm
      rw [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hu, map_one]
  · rw [ideleNorm_snd]
    exact Finset.prod_eq_one fun _ _ ↦ map_one _

variable {L L' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra K L]
  [Algebra K L'] [Algebra K' L'] [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']


omit [NumberField K] [NumberField K'] [NumberField L] [NumberField L'] in
theorem restrictNormal_restrictScalars_conjAt [IsGalois K L] [IsGalois K' L']
    (u' : InfinitePlace L') (hv : (u'.comap (algebraMap K' L')).IsReal) :
    ((conjAt K' u').restrictScalars K).restrictNormal L = conjAt K (u'.comap (algebraMap L L')) := by
  have h := isConj_conjAt_of_isReal L' hv
  have hr : IsConj (u'.embedding.comp (algebraMap L L'))
      (((conjAt K' u').restrictScalars K).restrictNormal L) := by
    rw [isConj_iff_forall]
    intro l
    rw [RingHom.comp_apply, RingHom.comp_apply, AlgEquiv.restrictNormal_commutes,
      AlgEquiv.restrictScalars_apply]
    exact h.eq _
  have hmk : mk (u'.embedding.comp (algebraMap L L')) =
      mk (u'.comap (algebraMap L L')).embedding := by
    rw [mk_embedding, ← comap_mk, mk_embedding]
  exact (conjOfEmbedding_eq ((isConj_iff_of_mk_eq hmk _).1 hr)).symm

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L']
  [IsMulCommutative (L' ≃ₐ[K'] L')]


omit [NumberField K] [NumberField K'] [NumberField L] [NumberField L'] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L'] [IsMulCommutative (L' ≃ₐ[K'] L')] in
theorem restrictNormal_restrictScalars_one [Normal K L] :
    ((1 : L' ≃ₐ[K'] L').restrictScalars K).restrictNormal L = 1 := by
  ext l
  apply (algebraMap L L').injective
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictScalars_apply, AlgEquiv.one_apply,
    AlgEquiv.one_apply]


omit [NumberField K] [NumberField K'] in
theorem extensionEmbeddingOfIsReal_normUnits (v' : InfinitePlace K') (hv' : v'.IsReal)
    (a : v'.Completionˣ) :
    extensionEmbeddingOfIsReal (hv'.comap (algebraMap K K'))
        (LocalField.normUnits (v'.comap (algebraMap K K')).Completion v'.Completion a : _) =
      extensionEmbeddingOfIsReal hv' a := by
  have hv := hv'.comap (algebraMap K K')
  have hfin : Module.finrank (v'.comap (algebraMap K K')).Completion v'.Completion = 1 :=
    (GroundTheory.Global.InfinitePlace.finrank_completion_eq_one_iff v').2
      fun h ↦ not_isComplex_iff_isReal.2 hv' h.2
  obtain ⟨c, hc⟩ := ((Algebra.finrank_eq_one_iff_bijective_algebraMap).1 hfin).2
    (a : v'.Completion)
  have e1 : (extensionEmbeddingOfIsReal hv'
      (algebraMap (v'.comap (algebraMap K K')).Completion v'.Completion c) : ℂ) =
        extensionEmbeddingOfIsReal hv c := by
    rw [extensionEmbeddingOfIsReal_apply]
    exact GroundTheory.Global.InfinitePlace.extensionEmbedding_algebraMap hv c
  rw [LocalField.coe_normUnits, ← hc, Algebra.norm_algebraMap, hfin, pow_one]
  exact (Complex.ofReal_injective e1).symm

theorem restrictNormal_infiniteLocalSymbol_norm (v' : InfinitePlace K') (a : v'.Completionˣ) :
    ((infiniteLocalSymbol L' v' a).restrictScalars K).restrictNormal L =
      infiniteLocalSymbol L (v'.comap (algebraMap K K'))
        (LocalField.normUnits (v'.comap (algebraMap K K')).Completion v'.Completion a) := by
  by_cases hv' : v'.IsReal
  · have hv := hv'.comap (algebraMap K K')
    obtain ⟨u'⟩ := IdeleNorm.nonempty_infinitePlacesOver (L := L') v'
    have hu'v' : (u' : InfinitePlace L').comap (algebraMap K' L') = v' :=
      (GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq v' _).1 u'.2
    have hu : ((u' : InfinitePlace L').comap (algebraMap L L')).LiesOver
        (v'.comap (algebraMap K K')) :=
      (GroundTheory.Global.InfinitePlace.liesOver_iff_comap_eq _ _).2 (by
        rw [← comap_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq K K' L',
          comap_comp, hu'v'])
    rw [infiniteLocalSymbol_apply L' v' hv' u', infiniteLocalSymbol_apply L _ hv ⟨_, hu⟩,
      extensionEmbeddingOfIsReal_normUnits v' hv' a]
    split_ifs
    · exact restrictNormal_restrictScalars_conjAt (u' : InfinitePlace L') (by rw [hu'v']; exact hv')
    · exact restrictNormal_restrictScalars_one
  · rw [infiniteLocalSymbol_of_not_isReal L' v' hv', MonoidHom.one_apply,
      restrictNormal_restrictScalars_one]
    by_cases hv : (v'.comap (algebraMap K K')).IsReal
    · obtain ⟨u⟩ := IdeleNorm.nonempty_infinitePlacesOver (L := L) (v'.comap (algebraMap K K'))
      rw [infiniteLocalSymbol_apply L _ hv u, if_neg]
      rw [not_lt, LocalField.coe_normUnits, GroundTheory.Global.InfinitePlace.extensionEmbeddingOfIsReal_norm
        hv (not_isReal_iff_isComplex.1 hv')]
      exact Complex.normSq_nonneg _
    · rw [infiniteLocalSymbol_of_not_isReal L _ hv, MonoidHom.one_apply]

end

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.NormResidueSymbol.Surjective
section
namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField

noncomputable section

section Trivial

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

theorem range_ideleNorm_eq_top_of_ideleSymbol_eq_one (h : ∀ x, ideleSymbol K L x = 1) :
    (ideleNorm K L).range = ⊤ := by
  classical
  refine eq_top_iff.2 fun x _ ↦ (IdeleNorm.mem_range_ideleNorm_iff_forall L x).2
    ⟨fun v ↦ ?_, fun v ↦ ?_⟩
  · obtain ⟨w⟩ := nonempty_placesOver L v
    have h1 : finiteProj v x ∈ (localSymbol L v).ker := by
      rw [MonoidHom.mem_ker, ← ideleSymbol_finiteEmbedding]
      exact h _
    rw [ker_localSymbol L v w] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨Pi.mulSingle w y, by rw [IdeleNorm.finiteLocalNorm_mulSingle]; exact hy⟩
  · obtain ⟨w⟩ := IdeleNorm.nonempty_infinitePlacesOver L v
    have h1 : infiniteProj v x ∈ (infiniteLocalSymbol L v).ker := by
      rw [MonoidHom.mem_ker, ← ideleSymbol_infiniteEmbedding]
      exact h _
    rw [ker_infiniteLocalSymbol L v w] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨Pi.mulSingle w y, by rw [IdeleNorm.infiniteLocalNorm_mulSingle]; exact hy⟩

end Trivial

universe u

section Cyclic

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

theorem finrank_eq_one_of_ideleSymbol_eq_one (h : ∀ x, ideleSymbol K L x = 1) :
    Module.finrank K L = 1 :=
  firstInequality.finrank_eq_one_of_sup_eq_top
    (top_le_iff.1 (range_ideleNorm_eq_top_of_ideleSymbol_eq_one L h ▸ le_sup_left))

end Cyclic

section Surjective

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

attribute [local instance] galCommGroup


omit [NumberField K] [NumberField L] [IsMulCommutative (L ≃ₐ[K] L)] in
theorem restrictNormal_fixedField_eq_one {N : Subgroup (L ≃ₐ[K] L)} [N.Normal] {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ N) : σ.restrictNormal (fixedField N) = 1 := by
  ext y
  change ((σ.restrictNormal (fixedField N) y : fixedField N) : L) = y
  exact (AlgEquiv.restrictNormal_commutes σ (fixedField N) y).trans
    ((mem_fixedField_iff N y).1 y.2 σ hσ)

theorem ideleSymbol_surjective : Function.Surjective (ideleSymbol K L) := by
  classical
  by_contra hs
  obtain ⟨σ, hσ⟩ := not_forall.1 hs
  set H := (ideleSymbol K L).range with hH
  have hσH : σ ∉ H := fun ⟨x, hx⟩ ↦ hσ ⟨x, hx⟩
  obtain ⟨ι, _, n, _, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite
    ((L ≃ₐ[K] L) ⧸ H)
  have hne : (QuotientGroup.mk' H σ) ≠ 1 := by
    rwa [ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨i, hi⟩ : ∃ i, e (QuotientGroup.mk' H σ) i ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hne ((MulEquiv.map_eq_one_iff e).1 (funext hall))
  set χ : (L ≃ₐ[K] L) →* Multiplicative (ZMod (n i)) :=
    (Pi.evalMonoidHom (fun j ↦ Multiplicative (ZMod (n j))) i).comp
      (e.toMonoidHom.comp (QuotientGroup.mk' H)) with hχ
  set N := χ.ker with hN
  have hHN : ∀ x, ideleSymbol K L x ∈ N := fun x ↦ by
    have hq : QuotientGroup.mk' H (ideleSymbol K L x) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ⟨x, rfl⟩
    rw [hN, MonoidHom.mem_ker, hχ, MonoidHom.comp_apply, MonoidHom.comp_apply, hq, map_one, map_one]
  have hσN : σ ∉ N := hi
  set F := fixedField N with hF
  have : IsCyclic (F ≃ₐ[K] F) := by
    have e1 : (F ≃ₐ[K] F) ≃* χ.range :=
      (IsGalois.normalAutEquivQuotient N).symm.trans (QuotientGroup.quotientKerEquivRange χ)
    exact isCyclic_of_surjective e1.symm.toMonoidHom e1.symm.surjective
  have hF1 : ∀ x, ideleSymbol K F x = 1 := fun x ↦ by
    rw [← restrictNormal_ideleSymbol F L x]
    exact restrictNormal_fixedField_eq_one (hHN x)
  have hbot : F = ⊥ := finrank_eq_one_iff.1 (finrank_eq_one_of_ideleSymbol_eq_one hF1)
  have htop : N = ⊤ := by
    rw [← fixingSubgroup_fixedField N, ← hF, hbot, fixingSubgroup_bot]
  exact hσN (htop ▸ Subgroup.mem_top σ)

end Surjective

end

end GroundTheory.Global
end

