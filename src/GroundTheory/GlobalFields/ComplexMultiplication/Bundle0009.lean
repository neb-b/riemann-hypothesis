module

public import Mathlib
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle0008
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeron
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle0004
public import GroundTheory.GlobalFields.ComplexMultiplication.DualDescentField
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualQuadratic

@[expose] public section

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupActionIso
section
abbrev periodLatticeEnd (L : PeriodPair) : Subring ℂ where
  carrier := {a | ∀ z ∈ L.lattice, a * z ∈ L.lattice}
  zero_mem' z _ := by rw [zero_mul]; exact zero_mem _
  one_mem' z hz := by simpa only [one_mul] using hz
  add_mem' ha hb z hz := by rw [add_mul]; exact add_mem (ha z hz) (hb z hz)
  neg_mem' ha z hz := by rw [neg_mul]; exact neg_mem (ha z hz)
  mul_mem' ha hb z hz := by rw [mul_assoc]; exact ha _ (hb z hz)

open WeierstrassCurve WeierstrassCurve.Affine GroundTheory.Arith.Abelian

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

universe u

section Points

variable {F : Type u} [Field F] (C : VariableChange F) {E E' : WeierstrassCurve F}

theorem baseChange_smul_eq (L : Type*) [Field L] [Algebra F L] (h : C • E = E') :
    C.baseChange L • E.baseChange L = E'.baseChange L := by
  subst h
  exact map_variableChange _ _ _

theorem map_vcPoint {L L' : Type*} [Field L] [Algebra F L] [Field L'] [Algebra F L'] [DecidableEq L]
    [DecidableEq L'] (f : L →ₐ[F] L') (h : C • E = E') (P : (E.baseChange L).toAffine.Point) :
    Point.map f (vcPoint (C.baseChange L) (baseChange_smul_eq C L h) P) =
      vcPoint (C.baseChange L') (baseChange_smul_eq C L' h) (Point.map f P) := by
  rcases P with _ | ⟨x, y, hP⟩
  · rfl
  · rw [vcPoint_some, Point.map_some, Point.map_some, vcPoint_some, Point.some.injEq]
    have hC : (C.baseChange L).map (f : L →+* L') = C.baseChange L' :=
      VariableChange.map_baseChange C f
    constructor
    · have := map_vcX (C.baseChange L) (f : L →+* L') x
      rw [hC] at this
      exact this
    · have := map_vcY (C.baseChange L) (f : L →+* L') x y
      rw [hC] at this
      exact this

theorem vcPoint_vcPoint_of_eq_inv {L : Type*} [Field L] {W W₂ : WeierstrassCurve L}
    (D D' : VariableChange L) (hD : D' = D⁻¹) (h₁ : D • W = W₂) (h₂ : D' • W₂ = W)
    (P : W.toAffine.Point) : vcPoint D' h₂ (vcPoint D h₁ P) = P := by
  subst hD
  rcases P with _ | ⟨x, y, hP⟩
  · rfl
  · rw [vcPoint_some, vcPoint_some, Point.some.injEq]
    have hu := D.u.inv_mul
    simp only [vcX, vcY, VariableChange.inv_def, inv_inv]
    constructor
    · linear_combination x * (((D.u⁻¹ : Lˣ) : L) * D.u + 1) * hu
    · linear_combination y * ((((D.u⁻¹ : Lˣ) : L) * D.u) ^ 2 + ((D.u⁻¹ : Lˣ) : L) * D.u + 1) * hu

theorem vcPoint_eq_zero_iff {L : Type*} [Field L] {W W₂ : WeierstrassCurve L} (D : VariableChange L)
    (h : D • W = W₂) {P : W.toAffine.Point} : vcPoint D h P = 0 ↔ P = 0 := by
  constructor
  · intro e
    exact vcPoint_injective D h (e.trans (vcPoint_zero D h).symm)
  · rintro rfl
    rfl

end Points

section Hom

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] (C : VariableChange F)
  {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

def vcPt (h : C • E = E') : (E'.baseChange E.toAffine.FunctionField).toAffine.Point :=
  vcPoint (C.baseChange _) (baseChange_smul_eq C _ h) (genericPoint E)

theorem respectsAdd_vcPt (h : C • E = E') : RespectsAdd E E' (vcPt C h) := by
  intro L _ _ _ u₁ v₁ u₂ v₂ u₃ v₃ h₁ h₂ h₃ t₁ t₂ t₃ hs
  simp only [ratMapValue, vcPt]
  rw [map_vcPoint C _ h, map_vcPoint C _ h, map_vcPoint C _ h, map_liftPoint_genericPoint E h₁ t₁,
    map_liftPoint_genericPoint E h₂ t₂, map_liftPoint_genericPoint E h₃ t₃, ← vcPoint_add, hs]

def vcHom (h : C • E = E') : isogHom E E' := ⟨vcPt C h, respectsAdd_vcPt C h⟩

theorem vcPt_ne_zero (h : C • E = E') : vcPt C h ≠ 0 := by
  rw [vcPt, Ne, vcPoint_eq_zero_iff]
  exact isGenPt_ne_zero E isGenPt_genericPoint

theorem isGenPt_vcHom (h : C • E = E') : IsGenPt E' (vcHom C h).1 :=
  isGenPt_of_mem_isogHom (vcHom C h).2 (vcPt_ne_zero C h)

theorem map_vcHom {L : Type*} [Field L] [Algebra F L] [DecidableEq L]
    (g : E.toAffine.FunctionField →ₐ[F] L) (h : C • E = E') :
    Point.map g (vcHom C h).1 =
      vcPoint (C.baseChange L) (baseChange_smul_eq C L h) (Point.map g (genericPoint E)) :=
  map_vcPoint C g h (genericPoint E)

omit [IsAlgClosed F] [DecidableEq F] [E.IsElliptic] [E'.IsElliptic] in
theorem inv_smul_eq_of_smul_eq (h : C • E = E') : C⁻¹ • E' = E := by
  rw [← h, inv_smul_smul]

theorem homComp_vcHom_vcHom (D : VariableChange F) (hD : D = C⁻¹) (h : C • E = E')
    (h' : D • E' = E) : homComp (vcHom D h') (vcHom C h) = homId := by
  apply Subtype.ext
  rw [homComp_of_isGenPt _ _ (isGenPt_vcHom C h)]
  rw [map_vcHom, map_genEval_genericPoint]
  have hD' : D.baseChange E.toAffine.FunctionField = (C.baseChange E.toAffine.FunctionField)⁻¹ := by
    subst hD
    exact map_inv (VariableChange.mapHom (algebraMap F E.toAffine.FunctionField)) C
  exact vcPoint_vcPoint_of_eq_inv _ _ hD' (baseChange_smul_eq C _ h) (baseChange_smul_eq D _ h')
    (genericPoint E)

def vcEndEquiv (h : C • E = E') : isogEnd E ≃+* isogEnd E' where
  toFun f := homComp (vcHom C h) (homComp f (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h)))
  invFun g := homComp (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h)) (homComp g (vcHom C h))
  left_inv f := by
    simp only [homComp_assoc, homComp_vcHom_vcHom C C⁻¹ rfl h (inv_smul_eq_of_smul_eq C h),
      homComp_id_right]
    rw [← homComp_assoc, homComp_vcHom_vcHom C C⁻¹ rfl h (inv_smul_eq_of_smul_eq C h),
      homComp_id_left]
  right_inv g := by
    simp only [homComp_assoc,
      homComp_vcHom_vcHom C⁻¹ C (inv_inv C).symm (inv_smul_eq_of_smul_eq C h) h, homComp_id_right]
    rw [← homComp_assoc,
      homComp_vcHom_vcHom C⁻¹ C (inv_inv C).symm (inv_smul_eq_of_smul_eq C h) h, homComp_id_left]
  map_mul' f g := by
    simp only [isogEnd_mul_def, homComp_assoc]
    rw [← homComp_assoc (vcHom C⁻¹ _) (vcHom C h),
      homComp_vcHom_vcHom C C⁻¹ rfl h (inv_smul_eq_of_smul_eq C h), homComp_id_left]
  map_add' f g := by
    rw [homComp_add_left, homComp_add_right]

theorem vcEndEquiv_apply (h : C • E = E') (f : isogEnd E) :
    vcEndEquiv C h f = homComp (vcHom C h) (homComp f (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h))) :=
  rfl

end Hom

section Const

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F]
  {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

theorem homConst_homComp (R : isogHom E' E'') (Q : isogHom E E') :
    homConst E E'' (homComp R Q) = homConst E' E'' R * homConst E E' Q := by
  by_cases hQ : IsGenPt E' Q.1
  · set g := genEval E' Q.1 hQ
    have key : algebraMap F E.toAffine.FunctionField (homConst E' E'' R * homConst E E' Q) •
        invariantDifferential E = omegaAt E'' (homComp R Q).1 := by
      rw [homComp_of_isGenPt _ _ hQ, ← kpush_omegaAt, omegaAt_eq_homConst_smul,
        ← algebraMap_smul E'.toAffine.FunctionField (homConst E' E'' R) (invariantDifferential E'),
        kpush_smul, AlgHom.commutes,
        show invariantDifferential E' = omegaAt E' (genericPoint E') from rfl, kpush_omegaAt, map_genEval_genericPoint,
        omegaAt_eq_homConst_smul, ← algebraMap_smul E.toAffine.FunctionField (homConst E E' Q),
        smul_smul, ← map_mul]
    apply (algebraMap F E.toAffine.FunctionField).injective
    rw [algebraMap_homConst]
    have h2 := homCoeff_smul (homComp R Q)
    rw [← key] at h2
    exact smul_left_injective _ (invariantDifferential_ne_zero E) h2
  · rw [eq_zero_of_not_isGenPt Q hQ, homComp_zero_right, map_zero, map_zero, mul_zero]

theorem homConst_homId : homConst E E (homId : isogEnd E) = 1 := by
  apply (algebraMap F E.toAffine.FunctionField).injective
  rw [algebraMap_homConst, map_one]
  exact invCoeff_invariantDifferential E


variable (E) in
def endConst : isogEnd E →+* F where
  toFun := homConst E E
  map_one' := homConst_homId
  map_mul' f g := homConst_homComp f g
  map_zero' := map_zero _
  map_add' := map_add _

theorem endConst_apply (f : isogEnd E) : endConst E f = homConst E E f := rfl

theorem endConst_vcEndEquiv (C : VariableChange F) (h : C • E = E') (f : isogEnd E) :
    endConst E' (vcEndEquiv C h f) = endConst E f := by
  have e := homConst_homComp (vcHom C h) (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h))
  rw [homComp_vcHom_vcHom C⁻¹ C (inv_inv C).symm (inv_smul_eq_of_smul_eq C h) h,
    homConst_homId] at e
  rw [endConst_apply, endConst_apply, vcEndEquiv_apply, homConst_homComp, homConst_homComp]
  linear_combination (-(homConst E E f)) * e

end Const

section Complex

variable {E : WeierstrassCurve ℂ} [E.IsElliptic]

theorem endConst_latticeEndEquiv (L : PeriodPair) (α : periodLatticeEnd L) :
    endConst (weierstrassCurve L) (latticeEndEquiv L α) = α :=
  homConst_latticeEndEquiv L α

theorem range_endConst_weierstrassCurve (L : PeriodPair) :
    (endConst (weierstrassCurve L)).range = periodLatticeEnd L := by
  ext z
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨α, rfl⟩ := (latticeEndEquiv L).surjective f
    exact (endConst_latticeEndEquiv L α).symm ▸ α.2
  · intro hz
    exact ⟨latticeEndEquiv L ⟨z, hz⟩, endConst_latticeEndEquiv L ⟨z, hz⟩⟩

theorem endConst_injective : Function.Injective (endConst E) := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_weierstrassCurve E
  intro f g hfg
  apply (vcEndEquiv C hC).injective
  apply (latticeEndEquiv L).symm.injective
  apply Subtype.ext
  have hf := endConst_latticeEndEquiv L ((latticeEndEquiv L).symm (vcEndEquiv C hC f))
  have hg := endConst_latticeEndEquiv L ((latticeEndEquiv L).symm (vcEndEquiv C hC g))
  rw [RingEquiv.apply_symm_apply, endConst_vcEndEquiv] at hf hg
  rw [← hf, ← hg, hfg]

theorem range_endConst {L : PeriodPair} {C : VariableChange ℂ} (hC : C • E = weierstrassCurve L) :
    (endConst E).range = periodLatticeEnd L := by
  rw [← range_endConst_weierstrassCurve]
  ext z
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨vcEndEquiv C hC f, endConst_vcEndEquiv C hC f⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨f, rfl⟩ := (vcEndEquiv C hC).surjective g
    exact ⟨f, (endConst_vcEndEquiv C hC f).symm⟩

end Complex

end Elliptic
end GroundTheory.Global
end
end

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.DualDescentBase
section
namespace GroundTheory.Global

open Polynomial GroundTheory.Arith.Abelian IntermediateField
open WeierstrassCurve.Affine (Point equation_iff)

universe u

section BaseChange

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
  {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

theorem x_isogBaseChange (φ : Isogeny E E') :
    (isogBaseChange (F' := Ω) φ).x = bcEmb (F' := Ω) E φ.x := by
  classical
  obtain ⟨⟨x, y, h, he, -⟩, -⟩ := φ.2
  change xOf _ (isogBaseChange (F' := Ω) φ).1 = _
  rw [isogBaseChange_val, he, Point.map_some, Isogeny.x, he]
  rfl

theorem y_isogBaseChange (φ : Isogeny E E') :
    (isogBaseChange (F' := Ω) φ).y = bcEmb (F' := Ω) E φ.y := by
  classical
  obtain ⟨⟨x, y, h, he, -⟩, -⟩ := φ.2
  change yOf _ (isogBaseChange (F' := Ω) φ).1 = _
  rw [isogBaseChange_val, he, Point.map_some, Isogeny.y, he]
  rfl

theorem isogBaseChange_injective :
    Function.Injective (isogBaseChange (F' := Ω) : Isogeny E E' → _) := by
  intro φ ψ h
  apply Isogeny.ext_xy
  · have e := congrArg Isogeny.x h
    rw [x_isogBaseChange, x_isogBaseChange] at e
    exact (bcEmb (F' := Ω) E).injective e
  · have e := congrArg Isogeny.y h
    rw [y_isogBaseChange, y_isogBaseChange] at e
    exact (bcEmb (F' := Ω) E).injective e

theorem isogBaseChange_comp (ψ : Isogeny E' E'') (φ : Isogeny E E') :
    isogBaseChange (F' := Ω) (ψ.comp φ) =
      (isogBaseChange (F' := Ω) ψ).comp (isogBaseChange (F' := Ω) φ) := by
  apply Isogeny.ext_xy
  · rw [x_isogBaseChange, Isogeny.comp_alt, Isogeny.comp_alt, x_isogBaseChange,
      comap_isogBaseChange_bcEmb]
  · rw [y_isogBaseChange, Isogeny.comp_y, Isogeny.comp_y, y_isogBaseChange,
      comap_isogBaseChange_bcEmb]

theorem isogBaseChange_mulIsogeny (n : ℤ) (hn : n ≠ 0) :
    isogBaseChange (F' := Ω) (mulIsogeny E n hn) = mulIsogeny (E.baseChange Ω) n hn := by
  classical
  apply Subtype.ext
  show Point.map (W' := E) (bcEmb (F' := Ω) E) (n • genericPoint E) =
    n • genericPoint (E.baseChange Ω)
  rw [map_zsmul, map_bcEmb_genericPoint]
  rfl

theorem degree_isogBaseChange (φ : Isogeny E E') :
    (isogBaseChange (F' := Ω) φ).degree = φ.degree := by
  obtain ⟨r, hr⟩ := φ.exists_ratEmb_eq_x
  have hcop : IsCoprime (r.num.map (algebraMap F Ω)) (r.denom.map (algebraMap F Ω)) := by
    simpa using r.isCoprime_num_denom.map (mapRingHom (algebraMap F Ω))
  obtain ⟨h1, h2⟩ := num_denom_div_of_isCoprime (r.monic_denom.map (algebraMap F Ω)) hcop
  have hb : ∀ p : F[X], bcEmb (F' := Ω) E (aeval (genX E) p) =
      aeval (genX (E.baseChange Ω)) (p.map (algebraMap F Ω)) := by
    intro p
    rw [← aeval_algHom_apply, bcEmb_genX, aeval_map_algebraMap]
  have hx : ratEmb (E.baseChange Ω) (algebraMap _ _ (r.num.map (algebraMap F Ω)) /
      algebraMap _ _ (r.denom.map (algebraMap F Ω))) = (isogBaseChange (F' := Ω) φ).x := by
    rw [x_isogBaseChange, ← hr, ratEmb_div]
    conv_rhs => rw [← RatFunc.num_div_denom r]
    rw [ratEmb_div, map_div₀, hb, hb]
  rw [φ.degree_eq_max_natDegree hr, (isogBaseChange (F' := Ω) φ).degree_eq_max_natDegree hx, h1, h2,
    natDegree_map_eq_of_injective (algebraMap F Ω).injective,
    natDegree_map_eq_of_injective (algebraMap F Ω).injective]

end BaseChange

section Dual

variable {F : Type u} [Field F] {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
  [E''.IsElliptic]

theorem isogeny_degree_pos (φ : Isogeny E E') : 0 < φ.degree := by
  classical
  rw [← degree_isogBaseChange (Ω := AlgebraicClosure F)]
  exact Isogeny.degree_pos _

theorem isogeny_degree_ne_zero (φ : Isogeny E E') : (φ.degree : ℤ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (isogeny_degree_pos φ).ne'

theorem mulIsogeny_eq_dual_comp_isogBaseChange [DecidableEq (AlgebraicClosure F)] (φ : Isogeny E E') :
    mulIsogeny (E.baseChange (AlgebraicClosure F)) φ.degree (isogeny_degree_ne_zero φ) =
      (isogBaseChange (F' := AlgebraicClosure F) φ).dual.comp (isogBaseChange φ) := by
  rw [Isogeny.dual_comp]
  exact mulIsogeny_congr (by rw [degree_isogBaseChange]) _ _

theorem mulIsogeny_comap_mem_fieldRange (φ : Isogeny E E') (f : E.toAffine.FunctionField) :
    (mulIsogeny E φ.degree (isogeny_degree_ne_zero φ)).comap f ∈ φ.comap.fieldRange := by
  classical
  apply mem_fieldRange_comap_of_bcEmb (Ω := AlgebraicClosure F) φ
  rw [← comap_isogBaseChange_bcEmb, isogBaseChange_mulIsogeny,
    mulIsogeny_eq_dual_comp_isogBaseChange, Isogeny.comap_comp, AlgHom.comp_apply]
  exact ⟨_, rfl⟩

noncomputable def dualComapOver (φ : Isogeny E E') :
    E.toAffine.FunctionField →ₐ[F] E'.toAffine.FunctionField :=
  φ.comap.equivFieldRange.symm.toAlgHom.comp
    ((mulIsogeny E φ.degree (isogeny_degree_ne_zero φ)).comap.codRestrict
      φ.comap.fieldRange.toSubalgebra (mulIsogeny_comap_mem_fieldRange φ))

theorem comap_dualComapOver (φ : Isogeny E E') (f : E.toAffine.FunctionField) :
    φ.comap (dualComapOver φ f) = (mulIsogeny E φ.degree (isogeny_degree_ne_zero φ)).comap f := by
  have := φ.comap.equivFieldRange.apply_symm_apply
    ((mulIsogeny E φ.degree (isogeny_degree_ne_zero φ)).comap.codRestrict
      φ.comap.fieldRange.toSubalgebra (mulIsogeny_comap_mem_fieldRange φ) f)
  exact congrArg Subtype.val this

noncomputable def dualPtOver (φ : Isogeny E E') : (E.baseChange E'.toAffine.FunctionField).toAffine.Point :=
  Point.map (dualComapOver φ) (genericPoint E)

theorem isGenPt_dualPtOver (φ : Isogeny E E') : IsGenPt E (dualPtOver φ) :=
  isGenPt_map_genericPoint E _

theorem map_bcEmb_dualPtOver [DecidableEq (AlgebraicClosure F)] (φ : Isogeny E E') :
    (Point.map (W' := E) (bcEmb (F' := AlgebraicClosure F) E') (dualPtOver φ) :
      ((E.baseChange (AlgebraicClosure F)).baseChange
        (E'.baseChange (AlgebraicClosure F)).toAffine.FunctionField).toAffine.Point) =
      (isogBaseChange (F' := AlgebraicClosure F) φ).dual.1 := by
  have hD : (bcEmb (F' := AlgebraicClosure F) E').comp (dualComapOver φ) =
      ((isogBaseChange (F' := AlgebraicClosure F) φ).dual.comap.restrictScalars F).comp
        (bcEmb (F' := AlgebraicClosure F) E) := by
    apply AlgHom.ext
    intro f
    have key : (isogBaseChange (F' := AlgebraicClosure F) φ).comap
        (bcEmb (F' := AlgebraicClosure F) E' (dualComapOver φ f)) =
        (isogBaseChange (F' := AlgebraicClosure F) φ).comap
          ((isogBaseChange (F' := AlgebraicClosure F) φ).dual.comap
            (bcEmb (F' := AlgebraicClosure F) E f)) := by
      rw [comap_isogBaseChange_bcEmb, comap_dualComapOver, ← comap_isogBaseChange_bcEmb,
        isogBaseChange_mulIsogeny, mulIsogeny_eq_dual_comp_isogBaseChange, Isogeny.comap_comp,
        AlgHom.comp_apply]
    exact (isogBaseChange (F' := AlgebraicClosure F) φ).comap.injective key
  have hcast : ∀ X : (E.baseChange (E.baseChange (AlgebraicClosure F)).toAffine.FunctionField).toAffine.Point,
      Point.map (W' := E)
          ((isogBaseChange (F' := AlgebraicClosure F) φ).dual.comap.restrictScalars F) X =
        Point.map (W' := E.baseChange (AlgebraicClosure F))
          (isogBaseChange (F' := AlgebraicClosure F) φ).dual.comap X := by
    intro X
    cases X <;> rfl
  rw [dualPtOver, Point.map_map, hD, ← Point.map_map, hcast, map_bcEmb_genericPoint,
    Isogeny.map_comap_genericPoint]

end Dual

end GroundTheory.Global
end

