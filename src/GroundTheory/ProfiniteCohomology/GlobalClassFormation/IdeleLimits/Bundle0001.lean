module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Levels
public import GroundTheory.GlobalFields.IdeleGroups.LocalHerbrandInfinite

@[expose] public section

-- bundled from GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.LevelsTrans
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global GroundTheory.Global.AdeleBaseChange
  FiniteSubfield IdeleLimit

noncomputable section

variable {K F E M : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (K ≤ M)] [Fact (F ≤ E)]
  [Fact (E ≤ M)] [Fact (F ≤ M)] [F.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]
  [M.1.fixingSubgroup.Normal]

theorem levelRestrict_levelRestrict (τ : M.1 ≃ₐ[K.1] M.1) :
    levelRestrict K F E (levelRestrict K E M τ) = levelRestrict K F M τ := by
  ext x
  have h1 := congrArg Subtype.val (coe_levelRestrict_apply (K := K) (F := F) (E := E)
    (levelRestrict K E M τ) x)
  have h2 := congrArg Subtype.val (coe_levelRestrict_apply (K := K) (F := E) (E := M) τ
    (algebraMap F.1 E.1 x))
  have h3 := congrArg Subtype.val (coe_levelRestrict_apply (K := K) (F := F) (E := M) τ x)
  exact h1.trans (h2.trans h3.symm)


set_option maxHeartbeats 2000000 in
theorem levelTransition_comp_levelTransition (n : ℕ) :
    levelTransition K F E n ≫ levelTransition K E M n = levelTransition K F M n := by
  unfold levelTransition cohomologyMapAlong
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  congr 1
  ext m x : 3
  apply Subtype.ext
  funext g
  change Additive.ofMul (ideleMap (Fact.out : E ≤ M) (ideleMap (Fact.out : F ≤ E)
      ((x.1 fun i => levelRestrict K F E (levelRestrict K E M (g i))).toMul))) =
    Additive.ofMul (ideleMap (Fact.out : F ≤ M) ((x.1 fun i => levelRestrict K F M (g i)).toMul))
  have hfun : (fun i => levelRestrict K F E (levelRestrict K E M (g i))) =
      fun i => levelRestrict K F M (g i) := funext fun i => levelRestrict_levelRestrict (g i)
  refine (congrArg Additive.ofMul (ideleMap_ideleMap (Fact.out : F ≤ E) (Fact.out : E ≤ M) _)).trans ?_
  rw [hfun]

end

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.LocalTransition
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField IsDedekindDomain GroundTheory.Global
  GroundTheory.Global.AdeleBaseChange FiniteSubfield IdeleLimit SemiLocal

open scoped Pointwise

noncomputable section

variable {K F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (F ≤ E)]
  [F.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]

section Finite

variable {v : HeightOneSpectrum (𝓞 K.1)} (w : PlacesOver F.1 v) (w' : PlacesOver E.1 v)
  [hw : w'.1.asIdeal.LiesOver w.1.asIdeal]

theorem algebraMap_levelRestrict_integers (σ : E.1 ≃ₐ[K.1] E.1) (x : 𝓞 F.1) :
    algebraMap (𝓞 F.1) (𝓞 E.1) (levelRestrict K F E σ • x) = σ • algebraMap (𝓞 F.1) (𝓞 E.1) x :=
  RingOfIntegers.ext (coe_levelRestrict_apply σ (x : F.1))


include hw in
theorem levelRestrict_mem_stabilizer {σ : E.1 ≃ₐ[K.1] E.1}
    (hσ : σ ∈ MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal) :
    levelRestrict K F E σ ∈ MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal := by
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  have hover : w.1.asIdeal = w'.1.asIdeal.comap (algebraMap (𝓞 F.1) (𝓞 E.1)) := hw.over
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, hover, Ideal.mem_comap, Ideal.mem_comap,
    ← map_inv, algebraMap_levelRestrict_integers, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hσ]


variable {w w'} in
def decompRestrict :
    MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal →*
      MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal where
  toFun σ := ⟨levelRestrict K F E σ, levelRestrict_mem_stabilizer w w' σ.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ _ _)

@[simp]
theorem coe_decompRestrict (σ : MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal) :
    ((decompRestrict (w := w) σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal) :
      F.1 ≃ₐ[K.1] F.1) = levelRestrict K F E σ :=
  rfl

theorem completionMap_decomposition_smul (σ : MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal)
    (a : w.1.adicCompletion F.1) :
    completionMap w.1 w'.1 (decompRestrict (w := w) σ • a) = σ • completionMap w.1 w'.1 a := by
  have h1 := MulAction.mem_stabilizer_iff.1 (decompRestrict (w := w) σ).2
  have h2 := MulAction.mem_stabilizer_iff.1 σ.2
  have := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F.1) (K := F.1) w.1).equalizer
    ((continuous_completionMap w.1 w'.1).comp (continuous_adicCompletionRingHomOf _ h1))
    ((continuous_adicCompletionRingHomOf _ h2).comp (continuous_completionMap w.1 w'.1))
    (funext fun x => by
      simp only [Function.comp_apply]
      rw [adicCompletionRingHomOf_algebraMap, completionMap_algebraMap, completionMap_algebraMap]
      simp only [IsScalarTower.algebraMap_apply F.1 E.1 (w'.1.adicCompletion E.1)]
      rw [adicCompletionRingHomOf_algebraMap, coe_decompRestrict, coe_levelRestrict_apply])
  exact congrFun this a


variable {w w'} in
def completionUnitsRep :
    Rep.res (decompRestrict (w := w) (w' := w'))
        (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
          (w.1.adicCompletion F.1)ˣ) ⟶
      Rep.ofMulDistribMulAction (MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal)
        (w'.1.adicCompletion E.1)ˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive
      (Units.map (completionMap w.1 w'.1 : w.1.adicCompletion F.1 →* w'.1.adicCompletion E.1))).toIntLinearMap,
    fun σ => LinearMap.ext fun a => congrArg Additive.ofMul (Units.ext
      (completionMap_decomposition_smul w w' σ
        (Additive.toMul (α := (w.1.adicCompletion F.1)ˣ) a : w.1.adicCompletion F.1)))⟩


variable (K F E) in
def localTransition (n : ℕ) :
    cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1.asIdeal)
        (w.1.adicCompletion F.1)ˣ) n ⟶
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1.asIdeal)
        (w'.1.adicCompletion E.1)ˣ) n :=
  cohomologyMapAlong decompRestrict continuous_of_discreteTopology completionUnitsRep n

end Finite

section Infinite

variable {v : InfinitePlace K.1} (w : v.placesOver F.1) (w' : v.placesOver E.1) [hw : w'.1.LiesOver w.1]


include hw in
theorem levelRestrict_mem_stabilizer_infinite {σ : E.1 ≃ₐ[K.1] E.1}
    (hσ : σ ∈ MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1) :
    levelRestrict K F E σ ∈ MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1 := by
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  have hover : w'.1.comap (algebraMap F.1 E.1) = w.1 := InfinitePlace.LiesOver.comap_eq w'.1 w.1
  have key : ∀ y : E.1, w'.1 (σ.symm y) = w'.1 y := fun y => by
    conv_rhs => rw [← hσ]
    rfl
  rw [← hover]
  refine InfinitePlace.ext _ _ fun x => ?_
  rw [InfinitePlace.smul_apply, InfinitePlace.comap_apply, InfinitePlace.comap_apply]
  have h1 : (levelRestrict K F E σ).symm x = levelRestrict K F E σ⁻¹ x := by
    rw [map_inv]
    rfl
  rw [h1, coe_levelRestrict_apply]
  exact key _


variable {w w'} in
def infDecompRestrict :
    MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1 →* MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1 where
  toFun σ := ⟨levelRestrict K F E σ, levelRestrict_mem_stabilizer_infinite w w' σ.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ _ _)

@[simp]
theorem coe_infDecompRestrict (σ : MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1) :
    ((infDecompRestrict (w := w) σ : MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1) :
      F.1 ≃ₐ[K.1] F.1) = levelRestrict K F E σ :=
  rfl

theorem infCompletionMap_decomposition_smul (σ : MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1)
    (a : w.1.Completion) :
    AbsoluteValue.Completion.map w.1.1 w'.1.1 (infDecompRestrict (w := w) σ • a) =
      σ • AbsoluteValue.Completion.map w.1.1 w'.1.1 a := by
  have := (AbsoluteValue.Completion.denseRange_coe w.1.1).equalizer
    ((AbsoluteValue.Completion.continuous_map w.1.1 w'.1.1).comp
      (continuous_completionRingHomOf (infDecompRestrict (w := w) σ).2))
    ((continuous_completionRingHomOf σ.2).comp
      (AbsoluteValue.Completion.continuous_map w.1.1 w'.1.1))
    (funext fun y => by
      simp only [Function.comp_apply]
      rw [completionRingHomOf_coe, AbsoluteValue.Completion.map_coe,
        AbsoluteValue.Completion.map_coe, completionRingHomOf_coe]
      refine congrArg (fun z : WithAbs w'.1.1 => (z : w'.1.Completion))
        (WithAbs.ofAbs_injective _ ?_)
      change algebraMap F.1 E.1 ((infDecompRestrict (w := w) σ : F.1 ≃ₐ[K.1] F.1) y.ofAbs) =
        (σ : E.1 ≃ₐ[K.1] E.1) (algebraMap F.1 E.1 y.ofAbs)
      rw [coe_infDecompRestrict, coe_levelRestrict_apply])
  exact congrFun this a


variable {w w'} in
def infCompletionUnitsRep :
    Rep.res (infDecompRestrict (w := w) (w' := w'))
        (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1) (w.1.Completion)ˣ) ⟶
      Rep.ofMulDistribMulAction (MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1) (w'.1.Completion)ˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (Units.map (AbsoluteValue.Completion.map w.1.1 w'.1.1 :
      w.1.Completion →* w'.1.Completion))).toIntLinearMap,
    fun σ => LinearMap.ext fun a => congrArg Additive.ofMul (Units.ext
      (infCompletionMap_decomposition_smul w w' σ
        (Additive.toMul (α := (w.1.Completion)ˣ) a : w.1.Completion)))⟩


variable (K F E) in
def infLocalTransition (n : ℕ) :
    cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (F.1 ≃ₐ[K.1] F.1) w.1)
        (w.1.Completion)ˣ) n ⟶
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer (E.1 ≃ₐ[K.1] E.1) w'.1)
        (w'.1.Completion)ˣ) n :=
  cohomologyMapAlong infDecompRestrict continuous_of_discreteTopology infCompletionUnitsRep n

end Infinite

end

end GroundTheory.ProfCoh
end

