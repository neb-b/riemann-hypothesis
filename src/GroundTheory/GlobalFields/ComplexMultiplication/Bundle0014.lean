module

public import Mathlib
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle0012
public import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeField
public import GroundTheory.GlobalFields.ComplexMultiplication.RespectsAddUniversal
public import GroundTheory.GlobalFields.ComplexMultiplication.TorsionReduction

@[expose] public section

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.ReductionAtPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian

universe u

section Translate

variable {F : Type u} [Field F] [DecidableEq F] (E : WeierstrassCurve F) [E.IsElliptic]

theorem isGenPt_genericPoint_add_constMap (R : E.toAffine.Point) :
    IsGenPt E (genericPoint E + constMap E E.toAffine.FunctionField R) := by
  have hG : TransOver E F (genericPoint E) := transcendental_genX E
  have := hG.add_left (M := E.toAffine.FunctionField) R
  rw [add_comm]
  exact this.isGenPt

end Translate

section OverF

variable {F : Type u} [Field F] [DecidableEq F] {E E' : WeierstrassCurve F} [E.IsElliptic]
  [E'.IsElliptic] (Ω : Type u) [Field Ω] [Algebra F Ω] [DecidableEq Ω]


omit [DecidableEq F] in
theorem isogBaseChange_app (φ : Isogeny E E')
    (X : ((E.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point)
    (hX : IsGenPt (E.baseChange Ω) X)
    (hX' : IsGenPt E (X : (E.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point)) :
    (isogBaseChange (F' := Ω) φ).app X hX =
      φ.app (X : (E.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point) hX' := by
  have hg : ((genEval (E.baseChange Ω) X hX).restrictScalars F).comp (bcEmb (F' := Ω) E) =
      genEval E (X : (E.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point)
        hX' := by
    refine eq_genEval E _ ?_ _
    cases X with
    | zero => exact hX.elim
    | some u v hv =>
      simp only [GroundTheory.Arith.Abelian.genericPoint, Point.map_some]
      congr 1
      · show genEval (E.baseChange Ω) _ hX (bcEmb (F' := Ω) E (genX E)) = u
        rw [bcEmb_genX]; exact genEval_genX (E.baseChange Ω) _ hX
      · show genEval (E.baseChange Ω) _ hX (bcEmb (F' := Ω) E (genY E)) = v
        rw [bcEmb_genY]; exact genEval_genY (E.baseChange Ω) _ hX
  unfold Isogeny.app
  rw [isogBaseChange_val, ← hg, ← Point.map_map]
  generalize Point.map (W' := E') (bcEmb (F' := Ω) E) φ.1 = Y
  cases Y <;> rfl


omit [DecidableEq F] [E.IsElliptic] [DecidableEq Ω] in
theorem isGenPt_of_isGenPt_baseChange
    (X : ((E.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point)
    (h : IsGenPt (E.baseChange Ω) X) :
    IsGenPt E (X : (E.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point) := by
  cases X with
  | zero => exact h.elim
  | some x y _ => exact Transcendental.restrictScalars (algebraMap F Ω).injective h


omit [E.IsElliptic] in
theorem constMap_constMap_baseChange (V : WeierstrassCurve F) (R : V.toAffine.Point) :
    (constMap (V.baseChange Ω) (E.baseChange Ω).toAffine.FunctionField (constMap V Ω R) :
      (V.baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point) =
      constMap V (E.baseChange Ω).toAffine.FunctionField R := by
  cases R <;> rfl

theorem app_genericPoint_add_constMap [PerfectField F] [IsAlgClosed Ω] (φ : Isogeny E E')
    (R : E.toAffine.Point) :
    φ.app (genericPoint E + constMap E E.toAffine.FunctionField R)
        (isGenPt_genericPoint_add_constMap E R) =
      φ.1 + constMap E' E.toAffine.FunctionField (pointHomOver Ω φ R) := by
  set K' := (E.baseChange Ω).toAffine.FunctionField
  set ι := bcEmb (F' := Ω) E
  set Rω := constMap E Ω R
  set φΩ := isogBaseChange (F' := Ω) φ
  have hGΩ : IsGenPt (E.baseChange Ω) (genericPoint (E.baseChange Ω)) :=
    transcendental_genX (E.baseChange Ω)
  have hX := isGenPt_genericPoint_add_constMap (E.baseChange Ω) Rω
  have h1 := φΩ.app_add_constMap hGΩ Rω hX
  rw [φΩ.app_genericPoint hGΩ, ← constMap_pointHomOver] at h1
  have app_eq : ∀ {P P' : (E.baseChange K').toAffine.Point} (h : P = P') (hP : IsGenPt E P)
      (hP' : IsGenPt E P'), φ.app P hP = φ.app P' hP' := by
    intro P P' h hP hP'; subst h; rfl
  have e1 : Point.map ι (genericPoint E + constMap E E.toAffine.FunctionField R) =
      ((genericPoint (E.baseChange Ω) + constMap (E.baseChange Ω) K' Rω :
        ((E.baseChange Ω).baseChange K').toAffine.Point) : (E.baseChange K').toAffine.Point) := by
    rw [map_add (f := _), map_bcEmb_genericPoint, map_constMap, ← constMap_constMap_baseChange Ω E R]
    rfl
  have hX' := isGenPt_of_isGenPt_baseChange Ω _ hX
  apply Point.map_injective (W' := E') ι
  rw [Isogeny.map_app]
  refine (app_eq e1 _ hX').trans ?_
  rw [← isogBaseChange_app Ω φ _ hX hX', h1, map_add (f := _), map_constMap,
    ← constMap_constMap_baseChange Ω (E := E) E' (pointHomOver Ω φ R)]
  rfl

end OverF

section Reduction

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)
  [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

theorem reduceFF_constMap (V : WeierstrassCurve 𝒪) [V.IsElliptic]
    (c : (V.baseChange K).toAffine.Point) :
    reduceFF K W V (constMap (V.baseChange K) (W.baseChange K).toAffine.FunctionField c) =
      constMap (V.map (residue 𝒪)) (W.map (residue 𝒪)).toAffine.FunctionField
        (reducePoint K V c) := by
  have hσ : (algebraMap K (W.baseChange K).toAffine.FunctionField).comp (algebraMap 𝒪 K) =
      (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField).comp
        (algebraMap 𝒪 (gaussRing W)) := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  cases c with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | some X Y h =>
    by_cases hX : X ∈ Set.range (algebraMap 𝒪 K)
    · obtain ⟨x, rfl⟩ := hX
      obtain ⟨y, rfl⟩ := exists_y_of_equation K V h.1
      obtain ⟨h₁, e₁⟩ : ∃ h₁, constMap (V.baseChange K) (W.baseChange K).toAffine.FunctionField
          (Point.some _ _ h) = Point.some (algebraMap K (W.baseChange K).toAffine.FunctionField
            (algebraMap 𝒪 K x)) (algebraMap K (W.baseChange K).toAffine.FunctionField
              (algebraMap 𝒪 K y)) h₁ := ⟨_, rfl⟩
      have hx := RingHom.congr_fun hσ x
      have hy := RingHom.congr_fun hσ y
      simp only [RingHom.comp_apply] at hx hy
      obtain ⟨h₂, e₂⟩ := exists_some_eq h₁ hx hy
      obtain ⟨h₃, e₃⟩ := reduceFF_some K W V h₂
      rw [e₁, e₂, e₃]
      have e₄ := reducePoint_some_integral K V h
        (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
          (equation_residue V (equation_of_map K V h.1)))
      refine Eq.trans ?_ (congrArg (constMap (V.map (residue 𝒪))
        (W.map (residue 𝒪)).toAffine.FunctionField) e₄).symm
      show _ = Point.some _ _ _
      simp only [Point.some.injEq, gaussResidue_residue_algebraMap]
      exact ⟨rfl, rfl⟩
    · have hX' := map_notMem_range K (W.baseChange K).toAffine.FunctionField
        (f := algebraMap 𝒪 (gaussRing W)) hσ hX
      have e₄ := reducePoint_some_notMem K V h hX
      refine Eq.trans ?_ (congrArg (constMap (V.map (residue 𝒪))
        (W.map (residue 𝒪)).toAffine.FunctionField) e₄).symm
      obtain ⟨h₁, e₁⟩ : ∃ h₁, constMap (V.baseChange K) (W.baseChange K).toAffine.FunctionField
          (Point.some X Y h) = Point.some (algebraMap K (W.baseChange K).toAffine.FunctionField X)
            (algebraMap K (W.baseChange K).toAffine.FunctionField Y) h₁ := ⟨_, rfl⟩
      rw [e₁, map_zero]
      simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
        reductionHom_apply]
      rw [pointCongr_some, reducePoint_some_notMem _ (gaussCurve W V) _ hX', map_zero, map_zero]

variable [W.IsElliptic] [W'.IsElliptic]

theorem reduceFF_genericPoint_add_constMap (R : (W.baseChange K).toAffine.Point) :
    reduceFF K W W (genericPoint (W.baseChange K) +
        constMap (W.baseChange K) (W.baseChange K).toAffine.FunctionField R) =
      genericPoint (W.map (residue 𝒪)) +
        constMap (W.map (residue 𝒪)) (W.map (residue 𝒪)).toAffine.FunctionField
          (reducePoint K W R) := by
  rw [map_add (f := _), reduceFF_genericPoint, reduceFF_constMap]


set_option maxHeartbeats 1000000 in
theorem reduceIsogeny_app_add_constMap (φ : Isogeny (W.baseChange K) (W'.baseChange K))
    (R : (W.baseChange K).toAffine.Point) (S : (W'.baseChange K).toAffine.Point)
    (h : φ.app (genericPoint (W.baseChange K) +
        constMap (W.baseChange K) (W.baseChange K).toAffine.FunctionField R)
        (isGenPt_genericPoint_add_constMap _ R) =
      φ.1 + constMap (W'.baseChange K) (W.baseChange K).toAffine.FunctionField S) :
    (reduceIsogeny K W W' φ).app (genericPoint (W.map (residue 𝒪)) +
        constMap (W.map (residue 𝒪)) (W.map (residue 𝒪)).toAffine.FunctionField
          (reducePoint K W R)) (isGenPt_genericPoint_add_constMap _ _) =
      (reduceIsogeny K W W' φ).1 + constMap (W'.map (residue 𝒪))
        (W.map (residue 𝒪)).toAffine.FunctionField (reducePoint K W' S) := by
  have hR' : IsGenPt (W.map (residue 𝒪)) (reduceFF K W W (genericPoint (W.baseChange K) +
      constMap (W.baseChange K) (W.baseChange K).toAffine.FunctionField R)) := by
    rw [reduceFF_genericPoint_add_constMap]
    exact isGenPt_genericPoint_add_constMap _ _
  have key := reduceFF_map_genEval K W W W' (isGenPt_genericPoint_add_constMap _ R) hR' φ.1
  have h2 := congrArg (reduceFF K W W') h
  rw [map_add (f := _), reduceFF_constMap] at h2
  rw [reduceIsogeny_val, ← h2]
  unfold Isogeny.app at key ⊢
  rw [key, reduceIsogeny_val, genEval_congr _ (reduceFF_genericPoint_add_constMap K W R) hR']

end Reduction

section PointsOverPerfect

universe v w

variable {𝒪 : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type v) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {W W' : WeierstrassCurve 𝒪}
  [W.IsElliptic] [W'.IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
  [PerfectField K] [PerfectField (ResidueField 𝒪)]
  (Ω : Type v) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [DecidableEq Ω]
  (Ωk : Type w) [Field Ωk] [Algebra (ResidueField 𝒪) Ωk] [IsAlgClosed Ωk] [DecidableEq Ωk]

theorem reducePoint_pointHomOver (φ : Isogeny (W.baseChange K) (W'.baseChange K))
    (R : (W.baseChange K).toAffine.Point) :
    reducePoint K W' (pointHomOver Ω φ R) =
      pointHomOver Ωk (reduceIsogeny K W W' φ) (reducePoint K W R) := by
  have h := reduceIsogeny_app_add_constMap K W W' φ R _ (app_genericPoint_add_constMap Ω φ R)
  rw [app_genericPoint_add_constMap Ωk (reduceIsogeny K W W' φ) (reducePoint K W R),
    add_right_inj] at h
  exact (constMap_injective _ _ h).symm

end PointsOverPerfect

end

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.ReductionDegree
section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian IntermediateField
open scoped Polynomial.Bivariate

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)

section SlopeTestRemainingChoices

theorem exists_gaussResidue_eq (z : (W.map (residue 𝒪)).toAffine.FunctionField) :
    ∃ b : gaussRing W, gaussResidue W (residue _ b) = z := by
  obtain ⟨a, s, hs, rfl⟩ :=
    IsFractionRing.div_surjective (A := (W.map (residue 𝒪)).toAffine.CoordinateRing) z
  obtain ⟨a', rfl⟩ := coordReduce_surjective W a
  obtain ⟨s', rfl⟩ := coordReduce_surjective W s
  have hs' : s' ∈ (gaussPrime W).primeCompl := fun h =>
    nonZeroDivisors.ne_zero hs (RingHom.mem_ker.1 h)
  refine ⟨IsLocalization.mk' (gaussRing W) a' ⟨s', hs'⟩, ?_⟩
  have hspec := IsLocalization.mk'_spec (gaussRing W) a' ⟨s', hs'⟩
  have := congrArg (fun b => gaussResidue W (residue _ b)) hspec
  simp only [map_mul, gaussResidue_residue] at this
  have hne : algebraMap _ (W.map (residue 𝒪)).toAffine.FunctionField (coordReduce W s') ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (nonZeroDivisors.ne_zero hs)
  rw [eq_div_iff hne]
  exact this

end SlopeTestRemainingChoices

section Isog

variable [W.IsElliptic] [W'.IsElliptic] (φ : Isogeny (W.baseChange K) (W'.baseChange K))

theorem exists_isogeny_coords : ∃ (x y : gaussRing W)
    (h : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Nonsingular
      (algebraMap _ _ x) (algebraMap _ _ y)), φ.1 = Point.some _ _ h := by
  letI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  have hne : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W')
      (pointCongr (gaussCurve_map_functionField K W W').symm φ.1) ≠ 0 := by
    intro h0
    apply reduceFF_isogeny_ne_zero K W W' φ
    simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
    rw [pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff]
    exact h0
  obtain ⟨x, y, h, e⟩ := exists_integral_of_reducePoint_ne_zero _ _ hne
  have e' : φ.1 = pointCongr (gaussCurve_map_functionField K W W') (Point.some _ _ h) := by
    rw [← e, pointCongr_pointCongr]; rfl
  rw [pointCongr_some] at e'
  exact ⟨x, y, _, e'⟩


set_option maxHeartbeats 1000000 in
theorem degree_reduceIsogeny_le : (reduceIsogeny K W W' φ).degree ≤ φ.degree := by
  obtain ⟨x, y, h, hφ⟩ := exists_isogeny_coords K W W' φ
  have hjM : ∀ c : 𝒪, algebraMap K (W.baseChange K).toAffine.FunctionField (algebraMap 𝒪 K c) =
      algebraMap (gaussRing W) _ (algebraMap 𝒪 (gaussRing W) c) := fun c => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hxy : (W'.map (algebraMap 𝒪 (gaussRing W))).toAffine.Equation x y := by
    have h₁ : ((W'.map (algebraMap 𝒪 (gaussRing W))).map
        (algebraMap _ (W.baseChange K).toAffine.FunctionField)).toAffine.Equation
        (algebraMap _ _ x) (algebraMap _ _ y) := by
      rw [← map_baseChange_eq_map_of K W' (algebraMap 𝒪 (gaussRing W)) _ hjM]; exact h.1
    exact (WeierstrassCurve.Affine.map_equation (W'.map (algebraMap 𝒪 (gaussRing W))).toAffine
      (IsFractionRing.injective _ (W.baseChange K).toAffine.FunctionField) x y).mp h₁
  obtain ⟨h', hred⟩ := reduceFF_some K W W' h
  have hφ' : (reduceIsogeny K W W' φ).1 = Point.some _ _ h' := by
    rw [reduceIsogeny_val, hφ, hred]
  have hx : Function.Injective (eval₂RingHom (ResidueField.map (algebraMap 𝒪 (gaussRing W)))
      (residue _ x)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    have hT : Transcendental (ResidueField 𝒪) (gaussResidue W (residue _ x)) := by
      have := (reduceIsogeny K W W' φ).isGenPt
      rw [hφ'] at this
      exact this
    apply hT
    refine ⟨p, hp0, ?_⟩
    have key : aeval (gaussResidue W (residue _ x)) p = gaussResidue W
        (eval₂RingHom (ResidueField.map (algebraMap 𝒪 (gaussRing W))) (residue _ x) p) := by
      rw [aeval_def, coe_eval₂RingHom, Polynomial.hom_eval₂, gaussResidue_comp_residueField_map]
    rw [key, hp, map_zero]
  set g := gaussLift W' (algebraMap 𝒪 (gaussRing W)) hxy hx
  have hσ : (φ.comap : _ →+* _).comp (algebraMap (gaussRing W')
      (W'.baseChange K).toAffine.FunctionField) =
        (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField).comp g := by
    apply comp_algebraMap_gaussLift W' (algebraMap 𝒪 (gaussRing W)) hxy hx K
    · intro c
      show φ.comap (algebraMap 𝒪 _ c) = _
      rw [IsScalarTower.algebraMap_apply 𝒪 K, φ.comap.commutes, hjM]
    · show φ.comap (genX _) = _
      rw [φ.comap_genX, Isogeny.x, hφ]; rfl
    · show φ.comap (genY _) = _
      rw [φ.comap_genY, Isogeny.y, hφ]; rfl
  have hring : (gaussResidue W).comp (fieldEvalRed W' (algebraMap 𝒪 (gaussRing W)) hxy hx) =
      ((reduceIsogeny K W W' φ).comap : _ →+* _) := by
    apply ringHom_ext_functionField
    · intro c
      rw [RingHom.comp_apply, fieldEvalRed_algebraMap, ← RingHom.comp_apply,
        gaussResidue_comp_residueField_map]
      exact ((reduceIsogeny K W W' φ).comap.commutes c).symm
    · rw [RingHom.comp_apply, fieldEvalRed_genX]
      show _ = (reduceIsogeny K W W' φ).comap (genX _)
      rw [Isogeny.comap_genX, Isogeny.x, hφ']; rfl
    · rw [RingHom.comp_apply, fieldEvalRed_genY]
      show _ = (reduceIsogeny K W W' φ).comap (genY _)
      rw [Isogeny.comap_genY, Isogeny.y, hφ']; rfl
  have hres : (gaussResidue W).comp (ResidueField.map g) =
      ((reduceIsogeny K W W' φ).comap : _ →+* _).comp (gaussResidue W') := by
    rw [residueField_map_gaussLift, ← RingHom.comp_assoc, hring]
  haveI := φ.finiteDimensional
  haveI := (reduceIsogeny K W W' φ).finiteDimensional
  haveI : Module.Free (reduceIsogeny K W W' φ).comap.fieldRange
      (W.map (residue 𝒪)).toAffine.FunctionField := Module.Free.of_divisionRing _ _
  set bb := Module.finBasis (reduceIsogeny K W W' φ).comap.fieldRange
    (W.map (residue 𝒪)).toAffine.FunctionField
  choose b hb using fun i => exists_gaussResidue_eq W (bb i)
  have hli : LinearIndependent φ.comap.fieldRange
      (fun i => algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (b i)) := by
    classical
    rw [Fintype.linearIndependent_iff]
    intro c hc i₀
    by_contra hci
    choose f hf using fun i => AlgHom.mem_fieldRange.1 (c i).2
    obtain ⟨⟨s, hs⟩, hsf⟩ := IsLocalization.exist_integer_multiples
      (nonZeroDivisors (gaussRing W')) Finset.univ f
    choose a ha using fun i => hsf i (Finset.mem_univ i)

    have hrel : ∑ i, g (a i) * b i = 0 := by
      apply IsFractionRing.injective (gaussRing W) (W.baseChange K).toAffine.FunctionField
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero]
      have h1 := congrArg (fun z => φ.comap (algebraMap _ _ s) * z) hc
      simp only [mul_zero, Finset.mul_sum, Algebra.smul_def, IntermediateField.algebraMap_apply]
        at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← RingHom.comp_apply (algebraMap (gaussRing W) _) g, ← hσ, RingHom.comp_apply,
        ← mul_assoc]
      congr 1
      rw [← hf i, ← map_mul]
      show φ.comap (algebraMap _ _ (a i)) = φ.comap (algebraMap _ _ s * f i)
      rw [ha i, Algebra.smul_def]
    have hinj : ∀ z : gaussRing W', z ≠ 0 → g z ≠ 0 := fun z hz h0 => by
      have h2 : (φ.comap : (W'.baseChange K).toAffine.FunctionField →+*
          (W.baseChange K).toAffine.FunctionField) (algebraMap (gaussRing W')
          (W'.baseChange K).toAffine.FunctionField z) = 0 := by
        rw [← RingHom.comp_apply, hσ, RingHom.comp_apply, h0, map_zero]
      rw [map_eq_zero_iff _ (RingHom.injective _),
        map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h2
      exact hz h2
    have hai₀ : a i₀ ≠ 0 := by
      intro h0
      apply hci
      have := ha i₀
      rw [h0, map_zero, eq_comm, smul_eq_zero] at this
      rcases this with h1 | h1
      · exact (nonZeroDivisors.ne_zero hs h1).elim
      · exact Subtype.ext (by rw [← hf i₀, h1, map_zero]; rfl)
    obtain ⟨i₁, hi₁, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun i => a i ≠ 0)
      (fun i => IsDiscreteValuationRing.addVal (gaussRing W') (a i)) ⟨i₀, by simp [hai₀]⟩
    have hai₁ : a i₁ ≠ 0 := (Finset.mem_filter.1 hi₁).2
    have hdvd : ∀ i, a i₁ ∣ a i := fun i => by
      by_cases hi : a i = 0
      · rw [hi]; exact dvd_zero _
      · exact (IsDiscreteValuationRing.addVal_le_iff_dvd).1
          (hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩))
    choose a' ha' using hdvd
    have ha'₁ : a' i₁ = 1 := by
      have := ha' i₁
      exact (mul_eq_left₀ hai₁).1 this.symm
    have hrel' : ∑ i, g (a' i) * b i = 0 := by
      have : g (a i₁) * ∑ i, g (a' i) * b i = 0 := by
        rw [Finset.mul_sum, ← hrel]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ha' i, map_mul, mul_assoc]
      exact (mul_eq_zero.1 this).resolve_left (hinj _ hai₁)
    have hred' := congrArg (fun z => gaussResidue W (residue _ z)) hrel'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_zero, hb] at hred'
    have hcoef : ∀ i, gaussResidue W (residue _ (g (a' i))) =
        (reduceIsogeny K W W' φ).comap (gaussResidue W' (residue _ (a' i))) := fun i => by
      rw [← ResidueField.map_residue, ← RingHom.comp_apply, hres]; rfl
    have hli' := bb.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli'
    have h0 := hli' (fun i => ⟨(reduceIsogeny K W W' φ).comap (gaussResidue W' (residue _ (a' i))),
      ⟨_, rfl⟩⟩) (by
        simp only [Algebra.smul_def, IntermediateField.algebraMap_apply]
        rw [← hred']
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcoef])
      i₁
    have h1 := congrArg Subtype.val h0
    simp only [ha'₁, map_one, ZeroMemClass.coe_zero] at h1
    exact one_ne_zero h1
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at this
  exact this

theorem degree_reduceIsogeny : (reduceIsogeny K W W' φ).degree = φ.degree := by
  have h1 := degree_reduceIsogeny_le K W W' φ
  have h2 := degree_reduceIsogeny_le K W' W (dualOver φ)
  rw [degree_dualOver] at h2
  have hc := reduceIsogeny_comp K W W' W (dualOver φ) φ
  rw [dualOver_comp, reduceIsogeny_mulIsogeny] at hc
  have hdeg := congrArg Isogeny.degree hc
  rw [degree_mulIsogeny, Isogeny.degree_comp, Int.natAbs_natCast] at hdeg
  have hpos := φ.degree_pos
  have hpos' := (reduceIsogeny K W W' φ).degree_pos
  apply le_antisymm h1
  by_contra hlt
  push_neg at hlt
  have : (reduceIsogeny K W' W (dualOver φ)).degree * (reduceIsogeny K W W' φ).degree <
      φ.degree ^ 2 := by
    calc (reduceIsogeny K W' W (dualOver φ)).degree * (reduceIsogeny K W W' φ).degree
        ≤ φ.degree * (reduceIsogeny K W W' φ).degree := Nat.mul_le_mul_right _ h2
      _ < φ.degree * φ.degree := Nat.mul_lt_mul_of_pos_left hlt hpos
      _ = φ.degree ^ 2 := (sq _).symm
  omega

end Isog

section Hom

variable [W.IsElliptic] [W'.IsElliptic] [DecidableEq (ResidueField (gaussRing (gaussCurve W W)))]

end Hom

end

end GroundTheory.Global
end

