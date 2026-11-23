module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0069
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0083
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0073
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0052
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSerreGraded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsNonzero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0067
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0066
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0062
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.UnipotentCharacter
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0004

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Contract
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.Inter

theorem Contract.pulledBackForms_topDensity_vanish : pointForm_holds.Statement :=
  pointForm_holds.proof (pointFormRank_holds.proof RatioAlgDep.proof) pointFormEuler_holds.proof

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GenDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights.Inter

theorem GenDeg.of_found (hRat : RatR.Statement) (hCyc : ArithmeticIntersectionCycle.Statement) (hInt : ArithmeticIntersectionIntegral.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.GenDegStatement :=
  PushforwardArithIntersection.proof arithVarZero hRat hCyc hInt

theorem GenDeg.of_pts (hPts : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) (hSec : IntersectionWithSection.Statement)
    (hCyc : ArithmeticIntersectionCycle.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.GenDegStatement :=
  GenDeg.of_found (RatR.proof hPts) hCyc (ArithmeticIntersectionIntegral.proof hPts hSec)

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiHSFull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

theorem SublatticeDegree.full : SublatticeDegree.Statement :=
  SublatticeDegree.proof SublatticeExtension.proof SpanningExtension.proof CovolumeLeGram.proof
    GramContraction.proof

theorem SuccessiveMinimaSpan.of_leaves (hC : KH.CondStatement) (hR : RelSectionsLarge.Statement) : SuccessiveMinimaSpan.Statement :=
  SuccessiveMinimaSpan.proof
    (SectionRingFinite.proof (SectionLatticeFinite.proof hC)
      (SectionSpanStep.proof (SpanStepHomog.proof (SpanStepLocal.proof (RelLatticeFinite.proof hR)))
        SerreGraded.proof))
    SectionBounded.proof SectionBoundedMul.proof

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCoordFibreDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem CoordFibreDeg.proof (hM : FibreMultiHomog.Statement) (hD : GenFibreChartDeg.Statement)
    (hR : CoordRatioDeg.Statement) : CoordFibreDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ _ y d G i hb hZ' hZ hi
  have : CharZero G.Φ' := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hmem : (C (n : ℤ) : MRing ι') ∈ mCoordIdeal y := by
      rw [← G.genericFibre_ker_target, RingHom.mem_ker]
      simpa using hn
    simp only [mCoordIdeal, RingHom.mem_ker, mConeMap] at hmem
    simpa using hmem
  have hMH : IsMultiHomogIdeal (mCoordIdeal y) := hZ'.2.1.2.1
  choose c hc using hZ.2.1.2.2
  have hx : ∀ k, G.x ⟨k, c k⟩ ≠ 0 := fun k h => hc k (by
    rw [← G.ker_x, RingHom.mem_ker, aeval_X]
    exact h)
  have hi' : ∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0 := fun k h => hi k (by
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact h)
  have h1 := Inter.ChartRankAdjoin.proof (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ'
    (fun q : Σ k : FibreBlock κ, fibreIdx ι' κ k => G.x' ⟨q.1.1, q.2⟩) i hi'
    (hM K ι K' ι' κ v (mCoordIdeal y) G hb hMH)
  exact h1.trans ((hD K ι K' ι' κ v (mCoordIdeal y) G c i hb hMH hx hi').trans
    (hR K ι K' ι' κ v Ω y G.Φ' G.x' hb G.genericFibre_ker_target))

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCoordRatioDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace CoordRatioDeg

def ratioField {S M : Type*} [Field M] [CharZero M] (R : S → S → Prop) (z : S → M) : IntermediateField ℚ M :=
  IntermediateField.adjoin ℚ {t | ∃ p q, R p q ∧ t = z p / z q}

theorem ratioField_map {S M N : Type*} [Field M] [CharZero M] [Field N] [CharZero N] (R : S → S → Prop)
    (z : S → M) (f : M →ₐ[ℚ] N) : (ratioField R z).map f = ratioField R (f ∘ z) := by
  rw [ratioField, IntermediateField.adjoin_map, ratioField]
  congr 1
  ext t
  constructor
  · rintro ⟨_, ⟨p, q, h, rfl⟩, rfl⟩
    exact ⟨p, q, h, by simp⟩
  · rintro ⟨p, q, h, rfl⟩
    exact ⟨_, ⟨p, q, h, rfl⟩, by simp⟩

theorem ratioField_congr {S M : Type*} [Field M] [CharZero M] {R : S → S → Prop} {z w : S → M}
    (h : ∀ p q, R p q → z p / z q = w p / w q) : ratioField R z = ratioField R w := by
  unfold ratioField
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    exact ⟨p, q, hpq, h p q hpq⟩
  · rintro ⟨p, q, hpq, rfl⟩
    exact ⟨p, q, hpq, (h p q hpq).symm⟩

theorem proof : CoordRatioDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ _ y Φ' _ _ x' hv hker
  let I : Ideal (MRing ι') := mCoordIdeal y
  let L := FractionRing (MvPolynomial K' Ω)
  have : CharZero L := charZero_of_injective_algebraMap (IsFractionRing.injective (MvPolynomial K' Ω) L)
  have h₁ : ∀ a ∈ I, (aeval x' : MRing ι' →ₐ[ℤ] Φ').toRingHom a = 0 := fun a ha => by
    rw [show I = _ from hker.symm] at ha
    exact RingHom.mem_ker.mp ha
  have h₂ : ∀ a ∈ I, (mConeMap y).toRingHom a = 0 := fun a ha => RingHom.mem_ker.mp ha
  let g₁ : MRing ι' ⧸ I →+* Φ' := Ideal.Quotient.lift I _ h₁
  have hg₁ : Function.Injective g₁ :=
    RingHom.lift_injective_of_ker_le_ideal I h₁ fun a ha => by
      change a ∈ mCoordIdeal y
      rw [← hker]
      exact ha
  let g₂ : MRing ι' ⧸ I →+* L := (algebraMap _ L).comp (Ideal.Quotient.lift I _ h₂)
  have hg₂ : Function.Injective g₂ :=
    (IsFractionRing.injective _ L).comp (RingHom.lift_injective_of_ker_le_ideal I h₂ fun a ha => ha)
  have : IsDomain (MRing ι' ⧸ I) := hg₁.isDomain g₁
  let F := FractionRing (MRing ι' ⧸ I)
  let f₁ : F →+* Φ' := IsFractionRing.lift hg₁
  have : CharZero F := ⟨fun m n h => by
    have h' := congrArg f₁ h
    rw [map_natCast, map_natCast] at h'
    exact_mod_cast h'⟩
  let f₂ : F →+* L := IsFractionRing.lift hg₂
  let xb : (Σ k', ι' k') → F := fun p => algebraMap _ F (Ideal.Quotient.mk I (X p))
  have e₁ : f₁.toRatAlgHom ∘ xb = x' := funext fun p => by
    simp [xb, f₁, g₁, IsFractionRing.lift_algebraMap]
  have e₂ : ∀ p, f₂ (xb p) = algebraMap _ L (C (y p) * X p.1) := fun p => by
    simp [xb, f₂, g₂, IsFractionRing.lift_algebraMap, mConeMap]
  let c : Ω →ₐ[ℚ] L := ((algebraMap (MvPolynomial K' Ω) L).comp C).toRatAlgHom
  have hT : ∀ k, algebraMap (MvPolynomial K' Ω) L (X k) ≠ 0 := fun k =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr (X_ne_zero k)
  have hr : ∀ p q : Σ k', ι' k', p.1 = q.1 → f₂ (xb p) / f₂ (xb q) = c (y p) / c (y q) := by
    intro p q h
    rw [e₂, e₂, h, map_mul, map_mul, mul_div_mul_right _ _ (hT _)]
    rfl
  change IntermediateField.relfinrank (ratioField (fun p q : Σ k, ι k => p.1 = q.1) (x' ∘ v))
      (ratioField (fun p q : Σ k', ι' k' => p.1 = q.1) x') =
    IntermediateField.relfinrank (ratioField (fun p q : Σ k, ι k => p.1 = q.1) (y ∘ v))
      (ratioField (fun p q : Σ k', ι' k' => p.1 = q.1) y)
  rw [← IntermediateField.relfinrank_map_map _ _ c, ratioField_map, ratioField_map, ← e₁,
    Function.comp_assoc, ← ratioField_map, ← ratioField_map,
    IntermediateField.relfinrank_map_map,
    ← IntermediateField.relfinrank_map_map _ _ f₂.toRatAlgHom, ratioField_map, ratioField_map]
  congr 1
  · refine ratioField_congr fun p q h => ?_
    simpa using hr (v p) (v q) (by rw [hv.2.2.1, hv.2.2.1, h])
  · exact ratioField_congr fun p q h => by simpa using hr p q h

end CoordRatioDeg

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGenFibreChartDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem GenFibreChartDeg.isMultiHomogIdeal_ker_rat {K' : Type} {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {Ω : Type} [Field Ω] [CharZero Ω] (x' : (Σ k', ι' k') → Ω)
    (h : IsMultiHomogIdeal (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω))) :
    IsMultiHomogIdeal (RingHom.ker (aeval x' : MRingOver ℚ ι' →ₐ[ℚ] Ω)) := by
  have hmap : ∀ g : MRing ι', aeval x' (qmap g) = aeval x' g := fun g => by
    rw [qmap, ← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
  have hker : RingHom.ker (aeval x' : MRingOver ℚ ι' →ₐ[ℚ] Ω) =
      (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω)).map qmap := by
    apply le_antisymm
    · intro f hf
      obtain ⟨N, hN, g, hg⟩ := exists_int_mul_eq_qmap f
      have hg0 : g ∈ RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω) := by
        rw [RingHom.mem_ker, ← hmap, ← hg, map_mul, RingHom.mem_ker.mp hf, mul_zero]
      have hmem : (N : MRingOver ℚ ι') * f ∈ (RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω)).map qmap := by
        rw [hg]
        exact Ideal.mem_map_of_mem _ hg0
      have hu : IsUnit (N : MRingOver ℚ ι') := by
        rw [show (N : MRingOver ℚ ι') = C (N : ℚ) by simp]
        exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast hN)).map C
      have h2 := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : MRingOver ℚ ι') hmem
      rwa [← mul_assoc, hu.val_inv_mul, one_mul] at h2
    · rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker, hmap]
      exact RingHom.mem_ker.mp hg
  rw [hker]
  obtain ⟨T, hT, hTe⟩ := h
  refine ⟨qmap '' T, ?_, by rw [hTe, Ideal.map_span]⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hT f hf
  exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ f hm) k⟩

theorem GenFibreChartDeg.proof (hT : GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.Statement)
    (hC : GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.Statement) : GenFibreChartDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' G _ c i hv hP hc hi
  have : CharZero G.Φ := (algebraMap G.Φ G.Φ').charZero
  have hx'0 : ∀ k, G.x' (v ⟨k, c k⟩) ≠ 0 := fun k => by
    rw [G.compat]
    exact (map_ne_zero _).2 (hc k)

  have hex : ∀ k', ∃ j : ι' k', G.x' ⟨k', j⟩ ≠ 0 := by
    intro k'
    by_cases hk : k' ∈ Set.range κ
    · obtain ⟨k, rfl⟩ := hk
      have key : ∀ q : Σ k', ι' k', q.1 = κ k → G.x' q ≠ 0 → ∃ j : ι' (κ k), G.x' ⟨κ k, j⟩ ≠ 0 := by
        rintro ⟨a, j⟩ rfl h
        exact ⟨j, h⟩
      exact key _ (hv.2.2.1 _) (hx'0 k)
    · exact ⟨i ⟨k', hk⟩, hi ⟨k', hk⟩⟩
  choose i' hi' using hex

  let t : K → G.Φ' := fun k => G.x' ⟨κ k, i' (κ k)⟩
  let Φ₁ := (IsScalarTower.toAlgHom ℚ G.Φ G.Φ').fieldRange
  let F₁ := blockFnField G.x'
  let F₀ := blockFnField (G.x' ∘ v)
  let E := IntermediateField.adjoin ℚ (Set.range t)
  let S := Set.range fun q : Σ k : FibreBlock κ, fibreIdx ι' κ k => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩
  have hF : ∀ p q : Σ k', ι' k', p.1 = q.1 → G.x' p / G.x' q ∈ F₁ :=
    fun p q h => IntermediateField.subset_adjoin _ _ ⟨p, q, h, rfl⟩
  have hF0 : ∀ p q : Σ k, ι k, p.1 = q.1 → G.x' (v p) / G.x' (v q) ∈ F₀ :=
    fun p q h => IntermediateField.subset_adjoin _ _ ⟨p, q, h, rfl⟩
  have hF01 : F₀ ≤ F₁ := IntermediateField.adjoin_le_iff.2 (by
    rintro _ ⟨p, q, h, rfl⟩
    exact hF (v p) (v q) (by rw [hv.2.2.1, hv.2.2.1, h]))
  have hmem : ∀ c, algebraMap G.Φ G.Φ' c ∈ Φ₁ := fun c => AlgHom.mem_fieldRange.2 ⟨c, rfl⟩

  have hchart : ∀ k, ∃ p₀ : Σ k, ι k, p₀.1 = k ∧ v p₀ = ⟨κ k, i' (κ k)⟩ := fun k => by
    obtain ⟨p₀, h⟩ := hv.2.2.2 ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    exact ⟨p₀, hv.1 ((hv.2.2.1 p₀).symm.trans (congrArg Sigma.fst h)), h⟩
  have ht1 : ∀ k, t k ∈ Φ₁ := fun k => by
    obtain ⟨p₀, -, h⟩ := hchart k
    show G.x' ⟨κ k, i' (κ k)⟩ ∈ Φ₁
    rw [← h, G.compat]
    exact hmem _
  have hrat : ∀ p : Σ k, ι k, G.x' (v p) / t p.1 ∈ F₀ := fun p => by
    obtain ⟨p₀, h1, h⟩ := hchart p.1
    show G.x' (v p) / G.x' ⟨κ p.1, i' (κ p.1)⟩ ∈ F₀
    rw [← h]
    exact hF0 p p₀ h1.symm

  have hΦ₁ : F₀ ⊔ E = Φ₁ := by
    refine le_antisymm (sup_le (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)) ?_
    · rintro _ ⟨p, q, -, rfl⟩
      show G.x' (v p) / G.x' (v q) ∈ Φ₁
      rw [G.compat, G.compat]
      exact div_mem (hmem _) (hmem _)
    · rintro _ ⟨k, rfl⟩
      exact ht1 k
    · intro z hz
      obtain ⟨c, rfl⟩ := AlgHom.mem_fieldRange.1 hz
      obtain ⟨f, g, -, rfl⟩ := G.gen c
      have hpoly : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) ∈ F₀ ⊔ E := by
        intro f
        induction f using MvPolynomial.induction_on with
        | C a =>
          rw [aeval_C, ← IsScalarTower.algebraMap_apply, algebraMap_int_eq, eq_intCast]
          exact intCast_mem _ a
        | add f g hf hg =>
          rw [map_add (f := _), map_add (f := _)]
          exact add_mem hf hg
        | mul_X f q hf =>
          rw [map_mul, map_mul, aeval_X, ← G.compat]
          refine mul_mem hf ?_
          rw [← div_mul_cancel₀ (G.x' (v q)) (hi' (κ q.1))]
          exact mul_mem ((le_sup_left : F₀ ≤ F₀ ⊔ E) (hrat q))
            ((le_sup_right : E ≤ F₀ ⊔ E) (IntermediateField.subset_adjoin _ _ ⟨q.1, rfl⟩))
      show IsScalarTower.toAlgHom ℚ G.Φ G.Φ' (aeval G.x f / aeval G.x g) ∈ F₀ ⊔ E
      rw [map_div₀]
      exact div_mem (hpoly f) (hpoly g)

  have hΦS : Φ₁ ⊔ IntermediateField.adjoin ℚ S = F₁ ⊔ E := by
    refine le_antisymm (sup_le ?_ ?_) (sup_le ?_ ?_)
    · rw [← hΦ₁]
      exact sup_le_sup_right hF01 E
    · refine (IntermediateField.adjoin_le_iff.2 ?_).trans le_sup_left
      rintro _ ⟨q, rfl⟩
      exact hF _ _ rfl
    · refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨⟨a, j⟩, ⟨b, l⟩, hab, rfl⟩
      dsimp only at hab
      subst hab
      by_cases ha : a ∈ Set.range κ
      · obtain ⟨k, rfl⟩ := ha
        obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, j⟩ ⟨k, rfl⟩
        obtain ⟨q, hq⟩ := hv.2.2.2 ⟨κ k, l⟩ ⟨k, rfl⟩
        have hpq : p.1 = q.1 := hv.1 ((hv.2.2.1 p).symm.trans
          ((congrArg Sigma.fst hp).trans ((congrArg Sigma.fst hq).symm.trans (hv.2.2.1 q))))
        rw [← hp, ← hq]
        exact (le_sup_left : Φ₁ ≤ _) (hΦ₁.le ((le_sup_left : F₀ ≤ F₀ ⊔ E) (hF0 p q hpq)))
      · rw [← div_div_div_cancel_right₀ (hi ⟨a, ha⟩) (G.x' ⟨a, j⟩) (G.x' ⟨a, l⟩)]
        refine (le_sup_right : IntermediateField.adjoin ℚ S ≤ _) (div_mem ?_ ?_)
        · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨a, ha⟩, j⟩, rfl⟩
        · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨a, ha⟩, l⟩, rfl⟩
    · rw [← hΦ₁]
      exact le_sup_right.trans le_sup_left

  have hy : IntermediateField.adjoin ℚ (Set.range fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩) = F₁ := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)
    · rintro _ ⟨q, rfl⟩
      exact hF _ _ rfl
    · rintro _ ⟨⟨a, j⟩, ⟨b, l⟩, hab, rfl⟩
      dsimp only at hab
      subst hab
      rw [← div_div_div_cancel_right₀ (hi' a) (G.x' ⟨a, j⟩) (G.x' ⟨a, l⟩)]
      exact div_mem (IntermediateField.subset_adjoin _ _ ⟨⟨a, j⟩, rfl⟩)
        (IntermediateField.subset_adjoin _ _ ⟨⟨a, l⟩, rfl⟩)
  have hker := GenFibreChartDeg.isMultiHomogIdeal_ker_rat G.x' (by rw [G.genericFibre_ker_target]; exact hP)
  have hindep : AlgebraicIndependent F₁ t := by
    have key : ∀ L : IntermediateField ℚ G.Φ', L = F₁ → AlgebraicIndependent L t →
        AlgebraicIndependent F₁ t := by
      rintro L rfl h
      exact h
    exact key _ hy ((hT ℚ G.Φ' K' ι' G.x' i' hi' hker).comp κ hv.1)

  refine (GroundTheory.Heights₂.Heights.Inter.FinrankAdjoinRange.proof ℚ G.Φ G.Φ' S).trans ?_
  change IntermediateField.relfinrank Φ₁ (Φ₁ ⊔ IntermediateField.adjoin ℚ S) = _
  rw [hΦS, ← hΦ₁]
  exact hC ℚ G.Φ' F₀ F₁ K t hF01 hindep

end GroundTheory.Heights₂.Heights.Targets
end
end

