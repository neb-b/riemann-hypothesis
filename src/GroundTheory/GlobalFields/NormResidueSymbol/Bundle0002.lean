module

public import Mathlib
public import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialLocal
public import GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.CompletionsOverBasisRepr
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
public import GroundTheory.GlobalFields.NormResidueSymbol.Rational

@[expose] public section

-- bundled from GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
section
namespace GroundTheory.Global

open IsDedekindDomain NumberField SemiLocal AdeleBaseChange IdeleGroup

noncomputable section

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']

theorem ideleNorm_finiteEmbedding (v' : HeightOneSpectrum (𝓞 K')) (a : (v'.adicCompletion K')ˣ) :
    ideleNorm K K' (finiteEmbedding v' a) =
      finiteEmbedding (below K v')
        (LocalField.normUnits ((below K v').adicCompletion K) (v'.adicCompletion K') a) := by
  classical
  apply Units.ext
  refine Prod.ext (funext fun w ↦ ?_) (FiniteAdeleRing.ext (K := K) fun v ↦ ?_)
  · rw [ideleNorm_fst]
    simp only [coe_finiteEmbedding]
    exact (Finset.prod_eq_one fun _ _ ↦ map_one _)
  · rw [ideleNorm_snd]
    simp only [coe_finiteEmbedding]
    by_cases hv : v = below K v'
    · subst hv
      rw [Finset.prod_eq_single (⟨v', inferInstance⟩ : PlacesOver K' (below K v')),
        finiteAdeleSingle_apply_self, finiteAdeleSingle_apply_self, LocalField.coe_normUnits]
      · intro w _ hw
        rw [finiteAdeleSingle_apply_of_ne (fun h ↦ hw (Subtype.ext h)), map_one]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [finiteAdeleSingle_apply_of_ne hv]
      refine Finset.prod_eq_one fun w _ ↦ ?_
      have hw : w.1 ≠ v' := by
        rintro h
        apply hv
        rw [← h]
        exact ((below_eq_iff w.1 v).2 w.2).symm
      rw [finiteAdeleSingle_apply_of_ne hw, map_one]

variable {L L' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra K L]
  [Algebra K L'] [Algebra K' L'] [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']


omit [NumberField K] [NumberField K'] [NumberField L'] in
theorem liesOver_trans_of_liesOver (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 K'))
    (u' : HeightOneSpectrum (𝓞 L')) [v'.asIdeal.LiesOver v.asIdeal]
    [u'.asIdeal.LiesOver v'.asIdeal] : u'.asIdeal.LiesOver v.asIdeal :=
  (below_eq_iff u' v).1 (by
    rw [← below_below (L := K'), (below_eq_iff u' v').2 inferInstance,
      (below_eq_iff v' v).2 inferInstance])

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L']
  [IsMulCommutative (L' ≃ₐ[K'] L')]

theorem restrictNormal_localSymbol_norm (v : HeightOneSpectrum (𝓞 K))
    (v' : HeightOneSpectrum (𝓞 K')) [v'.asIdeal.LiesOver v.asIdeal] (a : (v'.adicCompletion K')ˣ) :
    ((localSymbol L' v' a).restrictScalars K).restrictNormal L =
      localSymbol L v (LocalField.normUnits (v.adicCompletion K) (v'.adicCompletion K') a) := by
  obtain ⟨u'⟩ := nonempty_placesOver L' v'
  have : u'.1.asIdeal.LiesOver v.asIdeal := liesOver_trans_of_liesOver v v' u'.1
  have hu : (below L u'.1).asIdeal.LiesOver v.asIdeal :=
    (below_eq_iff _ v).1 (by rw [below_below, (below_eq_iff u'.1 v).2 inferInstance])
  let u : PlacesOver L v := ⟨below L u'.1, hu⟩
  have : u'.1.asIdeal.LiesOver u.1.asIdeal := liesOver_below (K := L) u'.1
  have : IsScalarTower (v.adicCompletion K) (v'.adicCompletion K') (u'.1.adicCompletion L') :=
    .of_algebraMap_eq fun r ↦ (completionMap_completionMap v v' u'.1 r).symm
  have := isMulCommutative_gal_adicCompletion L' v' u'
  have := isMulCommutative_gal_adicCompletion L v u
  let j : u.1.adicCompletion L →ₐ[v.adicCompletion K] u'.1.adicCompletion L' :=
    { completionMap u.1 u'.1 with
      commutes' := fun r ↦ completionMap_completionMap v u.1 u'.1 r }
  have hj : ∀ m : L, j (algebraMap L (u.1.adicCompletion L) m) =
      algebraMap L' (u'.1.adicCompletion L') (algebraMap L L' m) := fun m ↦ by
    change completionMap u.1 u'.1 _ = _
    rw [completionMap_algebraMap, IsScalarTower.algebraMap_apply L L' (u'.1.adicCompletion L')]
  ext l
  apply (algebraMap L L').injective
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictScalars_apply]
  apply (algebraMap L' (u'.1.adicCompletion L')).injective
  rw [algebraMap_localSymbol_apply L' v' u', ← hj, ← hj, algebraMap_localSymbol_apply L v u,
    normResidueSymbol_norm j]

end

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.NormResidueSymbol.RationalContinuous
section
namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField Topology
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace RationalSymbol

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract

theorem continuous_cycRestrict : Continuous cycRestrict := by
  have : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
  have h : @Normal ℚ maxCyclotomic _ _ (IntermediateField.algebra' maxCyclotomic) := by
    convert isGalois_maxCyclotomic.to_normal
  have hc := @InfiniteGalois.restrictNormalHom_continuous ℚ (AlgebraicClosure ℚ) _ _ _ maxCyclotomic h
  exact hc

theorem continuous_cycCharacter : Continuous cycCharacter := by
  have : T2Space Gal(maxCyclotomic/ℚ) := krullTopology_t2
  have hq : IsQuotientMap cycRestrict :=
    continuous_cycRestrict.isClosedMap.isQuotientMap continuous_cycRestrict cycRestrict_surjective
  rw [hq.continuous_iff]
  exact continuous_character.congr fun σ ↦ (cycCharacter_cycRestrict σ).symm

def cycCharacterHomeomorph : Gal(maxCyclotomic/ℚ) ≃ₜ* ℤ̂ˣ where
  toMulEquiv := cycCharacter
  continuous_toFun := continuous_cycCharacter
  continuous_invFun :=
    (continuous_cycCharacter.homeoOfEquivCompactToT2 (f := cycCharacter.toEquiv)).symm.continuous

def unitsPadicHomeomorph : (Π q : Nat.Primes, ℤ_[q])ˣ ≃ₜ* ℤ̂ˣ :=
  unitsContinuousMulEquiv padicEquiv.symm.toMulEquiv continuous_ofPadics continuous_toPadics

theorem unitPart_eq (x : IdeleClassGroup ℚ) :
    unitPart x = unitsPadicHomeomorph (RationalIdeles.ideleClassGroupEquiv x).2 :=
  Units.ext rfl

theorem continuous_unitPart : Continuous unitPart := by
  have h : (unitPart : IdeleClassGroup ℚ → ℤ̂ˣ) =
      unitsPadicHomeomorph ∘ Prod.snd ∘ RationalIdeles.ideleClassGroupEquiv :=
    funext unitPart_eq
  rw [h]
  exact unitsPadicHomeomorph.continuous.comp
    (continuous_snd.comp RationalIdeles.ideleClassGroupEquiv.continuous)

end RationalSymbol

end

end GroundTheory.Global
end

