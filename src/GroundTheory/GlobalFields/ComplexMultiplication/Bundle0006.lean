module

public import Mathlib
public import GroundTheory.GlobalFields.ComplexMultiplication.RespectsAddUniversal
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle0005
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionLift
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogeny

@[expose] public section

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraicUnivAdd
section
open Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian

noncomputable section

namespace GroundTheory.Global

universe u

variable {F : Type u} [Field F] {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]


omit [E.IsElliptic] in
theorem exists_univField_algHom {M : Type*} [Field M] [Algebra F M] [DecidableEq M]
    (σ : E.toAffine.FunctionField →ₐ[F] M) {u v : M}
    (h : (E.baseChange M).toAffine.Nonsingular u v)
    (hu : ∀ p : E.toAffine.FunctionField[X], p ≠ 0 → (p.map σ.toRingHom).eval u ≠ 0) :
    ∃ τ : univField E →ₐ[F] M,
      τ.comp (IsScalarTower.toAlgHom F E.toAffine.FunctionField (univField E)) = σ ∧
        τ (genX (E.baseChange E.toAffine.FunctionField)) = u ∧
          τ (genY (E.baseChange E.toAffine.FunctionField)) = v := by
  let _ : Algebra E.toAffine.FunctionField M := σ.toRingHom.toAlgebra
  have hc : ∀ a : F, algebraMap E.toAffine.FunctionField M (algebraMap F E.toAffine.FunctionField a) =
      algebraMap F M a := fun a ↦ σ.commutes a
  have hEq : ((E.baseChange E.toAffine.FunctionField).baseChange M).toAffine.Equation u v := by
    have e := (equation_iff _ _).1 h.1
    rw [equation_iff]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e ⊢
    rw [hc, hc, hc, hc, hc]
    exact e
  have htr : Transcendental E.toAffine.FunctionField u := by
    rintro ⟨p, hp0, hp⟩
    apply hu p hp0
    rw [eval_map]
    exact hp
  let τ := liftPoint (E.baseChange E.toAffine.FunctionField) hEq htr
  have _ : IsScalarTower F E.toAffine.FunctionField M :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (σ.commutes c).symm
  refine ⟨τ.restrictScalars F, AlgHom.ext fun a ↦ ?_, ?_, ?_⟩
  · rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, IsScalarTower.coe_toAlgHom']
    exact τ.commutes a
  · rw [AlgHom.restrictScalars_apply]
    exact liftPoint_genX _ _ _
  · rw [AlgHom.restrictScalars_apply]
    exact liftPoint_genY _ _ _

theorem univAdd_of_pair (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point)
    {M : Type*} [Field M] [Algebra F M] [DecidableEq M] (σ : E.toAffine.FunctionField →ₐ[F] M)
    {u v : M} (h : (E.baseChange M).toAffine.Nonsingular u v)
    (hu : ∀ p : E.toAffine.FunctionField[X], p ≠ 0 → (p.map σ.toRingHom).eval u ≠ 0)
    (hA : IsGenPt E (Point.map σ (genericPoint E))) (hB : IsGenPt E (Point.some u v h))
    (hAB : IsGenPt E (Point.map σ (genericPoint E) + Point.some u v h))
    (hQ : Point.map (genEval E _ hAB) Q =
      Point.map (genEval E _ hA) Q + Point.map (genEval E _ hB) Q) : UnivAdd Q := by
  obtain ⟨τ, hτ, hu', hv'⟩ := exists_univField_algHom σ h hu
  have c₁ : Point.map τ (univPt₁ E) = Point.map σ (genericPoint E) := by
    rw [univPt₁, Point.map_map, hτ]
  have c₂ : Point.map τ (univPt₂ E) = Point.some u v h := by
    rw [univPt₂, GroundTheory.Arith.Abelian.genericPoint, pointCongr_some, Point.map_some, Point.some.injEq]
    exact ⟨hu', hv'⟩
  apply Point.map_injective τ
  rw [map_add (f := _), ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₁₂ E)),
    ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₁ E)),
    ← map_genEval_map Q τ _ (isGenPt_map E τ (isGenPt_univPt₂ E)),
    genEval_congr E (by rw [map_add (f := _), c₁, c₂]) _ hAB, genEval_congr E c₁ _ hA,
    genEval_congr E c₂ _ hB]
  exact hQ

end GroundTheory.Global
end
end

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.ReductionEval
section
namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian

section Transport

theorem pointCongr_pointCongr {F : Type*} [Field F] [DecidableEq F]
    {V₁ V₂ V₃ : WeierstrassCurve F} (h₁ : V₁ = V₂) (h₂ : V₂ = V₃) (P : V₁.toAffine.Point) :
    pointCongr h₂ (pointCongr h₁ P) = pointCongr (h₁.trans h₂) P := by
  subst h₁; subst h₂; rfl

theorem pointMapRing_pointCongr {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
    (f : F →+* L) {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂) (P : V₁.toAffine.Point) :
    pointMapRing f V₂ (pointCongr h P) =
      pointCongr (congrArg (fun V => V.map f) h) (pointMapRing f V₁ P) := by
  subst h; rfl

theorem pointMapRing_congr {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
    {f g : F →+* L} (h : f = g) (V : WeierstrassCurve F) (P : V.toAffine.Point) :
    pointMapRing f V P = pointCongr (by rw [h]) (pointMapRing g V P) := by
  subst h; rfl

theorem pointMapRing_pointMapRing {F L L' : Type*} [Field F] [Field L] [Field L'] [DecidableEq F]
    [DecidableEq L] [DecidableEq L'] (f : F →+* L) (g : L →+* L') (V : WeierstrassCurve F)
    (P : V.toAffine.Point) :
    pointMapRing g (V.map f) (pointMapRing f V P) = pointMapRing (g.comp f) V P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rfl

theorem map_eq_pointCongr_pointMapRing {R F₁ F₂ : Type*} [CommRing R] [Field F₁] [Field F₂]
    [Algebra R F₁] [Algebra R F₂] [DecidableEq F₁] [DecidableEq F₂] (V : WeierstrassCurve R)
    (σ : F₁ →ₐ[R] F₂) (P : (V.baseChange F₁).toAffine.Point) :
    Point.map σ P = pointCongr (by
        show V.map (σ.toRingHom.comp (algebraMap R F₁)) = V.map (algebraMap R F₂)
        exact congrArg V.map σ.comp_algebraMap) (pointMapRing σ.toRingHom (V.baseChange F₁) P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact (map_zero (pointCongr _)).symm
  · rw [Point.map_some]
    obtain ⟨h', e⟩ := pointMapRing_some σ.toRingHom (V.baseChange F₁) h
    rw [e, pointCongr_some, Point.some.injEq]
    exact ⟨rfl, rfl⟩

theorem reducePoint_pointCongr {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (K : Type*) [Field K] [Algebra 𝒪 K] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
    {V₁ V₂ : WeierstrassCurve 𝒪} (h : V₁ = V₂) (P : (curveK K V₁).Point) :
    reducePoint K V₂ (pointCongr (congrArg (fun V => V.map (algebraMap 𝒪 K)) h) P) =
      pointCongr (congrArg (fun V => V.map (residue 𝒪)) h) (reducePoint K V₁ P) := by
  subst h; rfl

end Transport

section Eval

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)
  {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] (j : 𝒪 →+* Λ) [IsLocalHom j]
  (M : Type*) [Field M] [Algebra Λ M] [IsFractionRing Λ M] [Algebra K M] [DecidableEq M]
  [DecidableEq (ResidueField Λ)]

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] [IsDomain Λ]
  [IsDiscreteValuationRing Λ] [IsLocalHom j] [IsFractionRing Λ M] [DecidableEq M]
  [DecidableEq (ResidueField Λ)] in
theorem map_baseChange_eq_map_of
    (hjM : ∀ c : 𝒪, algebraMap K M (algebraMap 𝒪 K c) = algebraMap Λ M (j c)) :
    (W'.baseChange K).baseChange M = (W'.map j).map (algebraMap Λ M) := by
  show W'.map ((algebraMap K M).comp (algebraMap 𝒪 K)) = W'.map ((algebraMap Λ M).comp j)
  congr 1
  exact RingHom.ext hjM

variable {x y : Λ} (hxy : (W.map j).toAffine.Equation x y)
  (hx : Function.Injective (eval₂RingHom (ResidueField.map j) (residue Λ x)))

theorem map_fieldEvalRed_eq :
    ((W'.map (residue 𝒪)).baseChange (W.map (residue 𝒪)).toAffine.FunctionField).map
      (fieldEvalRed W j hxy hx) = (W'.map j).map (residue Λ) := by
  show W'.map (((fieldEvalRed W j hxy hx).comp (algebraMap (ResidueField 𝒪) _)).comp
    (residue 𝒪)) = W'.map ((residue Λ).comp j)
  congr 1
  refine RingHom.ext fun c => ?_
  simp [fieldEvalRed_algebraMap, ResidueField.map_residue]

variable [W'.IsElliptic]

theorem reducePoint_genEval
    (hjM : ∀ c : 𝒪, algebraMap K M (algebraMap 𝒪 K c) = algebraMap Λ M (j c))
    (hR : ((W.baseChange K).baseChange M).toAffine.Nonsingular (algebraMap Λ M x)
      (algebraMap Λ M y))
    (hRg : IsGenPt (W.baseChange K) (Point.some _ _ hR))
    (Q : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point) :
    reducePoint M (W'.map j) (pointCongr (map_baseChange_eq_map_of K W' j M hjM)
        (Point.map (genEval (W.baseChange K) _ hRg) Q)) =
      pointCongr (map_fieldEvalRed_eq W W' j hxy hx)
        (pointMapRing (fieldEvalRed W j hxy hx) _ (reduceFF K W W' Q)) := by
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  set σ := genEval (W.baseChange K) _ hRg
  have hσ : σ.toRingHom.comp (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField) =
      (algebraMap Λ M).comp (gaussLift W j hxy hx) := by
    apply comp_algebraMap_gaussLift
    · intro c
      show σ (algebraMap 𝒪 _ c) = _
      rw [IsScalarTower.algebraMap_apply 𝒪 K, σ.commutes, hjM]
    · exact genEval_genX _ _ hRg
    · exact genEval_genY _ _ hRg
  have c0 : (gaussCurve W W').map (gaussLift W j hxy hx) = W'.map j := by
    show W'.map ((gaussLift W j hxy hx).comp (algebraMap 𝒪 (gaussRing W))) = W'.map j
    exact congrArg W'.map (RingHom.ext (gaussLift_algebraMap_base W j hxy hx))
  set Q₀ := pointCongr (gaussCurve_map_functionField K W W').symm Q with hQ₀
  have hQ : Q = pointCongr (gaussCurve_map_functionField K W W') Q₀ := by
    rw [hQ₀, pointCongr_pointCongr]; rfl
  have key := reducePoint_pointMapRing (W.baseChange K).toAffine.FunctionField M hσ
    (gaussCurve W W') Q₀
  have lhs : pointCongr (map_baseChange_eq_map_of K W' j M hjM) (Point.map σ Q) =
      pointCongr (congrArg (fun V => V.map (algebraMap Λ M)) c0)
        (pointCongr (map_curveK_eq _ M hσ (gaussCurve W W')) (pointMapRing σ.toRingHom _ Q₀)) := by
    rw [map_eq_pointCongr_pointMapRing, hQ, pointMapRing_pointCongr, pointCongr_pointCongr,
      pointCongr_pointCongr, pointCongr_pointCongr]
  rw [lhs, reducePoint_pointCongr, key, pointMapRing_congr (residueField_map_gaussLift W j hxy hx),
    ← pointMapRing_pointMapRing]
  simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
  rw [pointMapRing_pointCongr]
  erw [pointCongr_pointCongr, pointCongr_pointCongr, pointCongr_pointCongr]
  · rfl
  · exact c0

end Eval

end

end GroundTheory.Global
end

