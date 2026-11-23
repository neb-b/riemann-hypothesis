module

public import Mathlib
public import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupAction
public import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeField
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.Bundle0006
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle0011

@[expose] public section

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.AlgebraicityHom
section
open WeierstrassCurve GroundTheory.Arith.Abelian
open WeierstrassCurve.Affine (Point)

noncomputable section

namespace GroundTheory.Global

universe u

section FFMap

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F')

theorem ffMap_surjective (hσ : Function.Surjective σ) (E : WeierstrassCurve F) :
    Function.Surjective (ffMap σ E) := by
  let R : IntermediateField F' (E.map σ).toAffine.FunctionField :=
    { (ffMap σ E).fieldRange with
      algebraMap_mem' := fun c => by
        obtain ⟨a, rfl⟩ := hσ c
        exact ⟨algebraMap F _ a, ffMap_algebraMap σ E a⟩ }
  have hR : R = ⊤ := by
    rw [eq_top_iff, ← adjoin_genX_genY (W := E.map σ), IntermediateField.adjoin_le_iff]
    rintro z (rfl | rfl)
    · exact ⟨genX E, ffMap_genX σ E⟩
    · exact ⟨genY E, ffMap_genY σ E⟩
  intro z
  have hz : z ∈ R := hR ▸ IntermediateField.mem_top
  exact hz

end FFMap

section BcPt

variable {F F' : Type u} [Field F] [Field F'] [Algebra F F'] (E E' : WeierstrassCurve F)

def bcPtMap : (E'.baseChange E.toAffine.FunctionField).toAffine.Point →+
    ((E'.baseChange F').baseChange (E.baseChange F').toAffine.FunctionField).toAffine.Point :=
  Point.map (W' := E') (bcEmb (F' := F') E)

end BcPt

section HomMap

variable {F F' : Type u} [Field F] [Field F'] [IsAlgClosed F] [IsAlgClosed F'] [DecidableEq F]
  [DecidableEq F'] (σ : F →+* F') {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
  [E''.IsElliptic]

def homPtMap : (E'.baseChange E.toAffine.FunctionField).toAffine.Point →+
    ((E'.map σ).baseChange (E.map σ).toAffine.FunctionField).toAffine.Point :=
  letI := σ.toAlgebra
  bcPtMap (F' := F') E E'

omit [IsAlgClosed F] [IsAlgClosed F'] [DecidableEq F] [DecidableEq F'] in
theorem homPtMap_isogeny (φ : Isogeny E E') : homPtMap σ φ.1 = (φ.map σ).1 := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  exact (isogBaseChange_val (F' := F') φ).symm

omit [IsAlgClosed F'] [DecidableEq F'] in
theorem homPtMap_mem (Q : isogHom E E') : homPtMap σ Q.1 ∈ isogHom (E.map σ) (E'.map σ) := by
  by_cases hQ : Q = 0
  · rw [hQ, ZeroMemClass.coe_zero, map_zero]
    exact zero_mem _
  · rw [← isogOfHom_val Q hQ, homPtMap_isogeny]
    exact ((isogOfHom Q hQ).map σ).toHom.2

def homMap : isogHom E E' →+ isogHom (E.map σ) (E'.map σ) where
  toFun Q := ⟨homPtMap σ Q.1, homPtMap_mem σ Q⟩
  map_zero' := Subtype.ext (map_zero (homPtMap σ))
  map_add' Q₁ Q₂ := Subtype.ext (map_add (homPtMap σ) Q₁.1 Q₂.1)

theorem homMap_toHom (φ : Isogeny E E') : homMap σ φ.toHom = (φ.map σ).toHom :=
  Subtype.ext rfl

theorem homConst_toHom (φ : Isogeny E E') : homConst E E' φ.toHom = invConst φ := by
  apply (algebraMap F E.toAffine.FunctionField).injective
  rw [algebraMap_homConst, algebraMap_invConst]
  rfl


omit [IsAlgClosed F] [IsAlgClosed F'] [DecidableEq F] [DecidableEq F'] in
theorem invConst_map (φ : Isogeny E E') : invConst (φ.map σ) = σ (invConst φ) := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  exact invConst_isogBaseChange (F' := F') φ

theorem homConst_homMap (Q : isogHom E E') :
    homConst (E.map σ) (E'.map σ) (homMap σ Q) = σ (homConst E E' Q) := by
  by_cases hQ : Q = 0
  · rw [hQ, map_zero, map_zero, map_zero, map_zero]
  · rw [← isogOfHom_toHom Q hQ, homMap_toHom, homConst_toHom, homConst_toHom, invConst_map]

theorem homMap_homComp (R : isogHom E' E'') (Q : isogHom E E') :
    homMap σ (homComp R Q) = homComp (homMap σ R) (homMap σ Q) := by
  by_cases hQ : Q = 0
  · simp only [hQ, homComp_zero_right, map_zero]
  by_cases hR : R = 0
  · simp only [hR, homComp_zero_left, map_zero]
  rw [← isogOfHom_toHom Q hQ, ← isogOfHom_toHom R hR, Isogeny.homComp_toHom, homMap_toHom,
    homMap_toHom, homMap_toHom, Isogeny.homComp_toHom, Isogeny.map_comp]

theorem homMap_one : homMap σ (1 : isogEnd E) = 1 := by
  rw [isogEnd_one_eq_mulIsogeny, homMap_toHom, Isogeny.map_mulIsogeny, ← isogEnd_one_eq_mulIsogeny]

def endMap : isogEnd E →+* isogEnd (E.map σ) where
  toFun := homMap σ
  map_one' := homMap_one σ
  map_mul' f g := homMap_homComp σ f g
  map_zero' := map_zero _
  map_add' := map_add _

theorem homMap_injective : Function.Injective (homMap σ : isogHom E E' → _) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro Q hQ
  by_contra h
  rw [← isogOfHom_toHom Q h, homMap_toHom] at hQ
  exact Isogeny.toHom_ne_zero _ hQ

theorem homMap_surjective (hσ : Function.Surjective σ) :
    Function.Surjective (homMap σ : isogHom E E' → _) := by
  intro P
  by_cases hP : P = 0
  · exact ⟨0, by rw [hP, map_zero]⟩
  set ψ := isogOfHom P hP
  obtain ⟨x, hx⟩ := ffMap_surjective σ hσ E ψ.x
  obtain ⟨y, hy⟩ := ffMap_surjective σ hσ E ψ.y
  refine ⟨(Isogeny.ofMap σ ψ x y hx hy).toHom, ?_⟩
  rw [homMap_toHom, Isogeny.map_ofMap, isogOfHom_toHom]

def endMapEquiv (σ : F ≃+* F') : isogEnd E ≃+* isogEnd (E.map (σ : F →+* F')) :=
  RingEquiv.ofBijective (endMap (σ : F →+* F'))
    ⟨homMap_injective (σ : F →+* F'), homMap_surjective (σ : F →+* F') σ.surjective⟩

end HomMap

section ConstSet

open Elliptic

variable {F F' : Type u} [Field F] [Field F'] [IsAlgClosed F] [IsAlgClosed F'] [DecidableEq F]
  [DecidableEq F']


variable (E E' : WeierstrassCurve F) [E.IsElliptic] [E'.IsElliptic] in
def homConstSet : AddSubgroup F := (homConst E E').range

variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem mem_homConstSet {c : F} :
    c ∈ homConstSet E E' ↔ ∃ Q : isogHom E E', homConst E E' Q = c :=
  AddMonoidHom.mem_range

theorem homConstSet_map (σ : F ≃+* F') :
    (homConstSet (E.map (σ : F →+* F')) (E'.map (σ : F →+* F')) : Set F') =
      σ '' homConstSet E E' := by
  ext z
  simp only [SetLike.mem_coe, mem_homConstSet, Set.mem_image]
  constructor
  · rintro ⟨P, rfl⟩
    obtain ⟨Q, rfl⟩ := homMap_surjective (E := E) (E' := E') (σ : F →+* F') σ.surjective P
    exact ⟨homConst E E' Q, ⟨Q, rfl⟩, (homConst_homMap (σ : F →+* F') Q).symm⟩
  · rintro ⟨c, ⟨Q, rfl⟩, rfl⟩
    exact ⟨homMap (σ : F →+* F') Q, homConst_homMap (σ : F →+* F') Q⟩

theorem homConst_vcHom_mul_inv (C : VariableChange F) (h : C • E = E') :
    homConst E' E (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h)) * homConst E E' (vcHom C h) = 1 := by
  rw [← homConst_homComp, homComp_vcHom_vcHom C C⁻¹ rfl h (inv_smul_eq_of_smul_eq C h), homConst_homId]

theorem homConstSet_le_mul {E₁ E₁' : WeierstrassCurve F} [E₁.IsElliptic] [E₁'.IsElliptic]
    (Q : isogHom E₁ E) (R : isogHom E' E₁') {z : F} (hz : z ∈ homConstSet E E') :
    homConst E' E₁' R * z * homConst E₁ E Q ∈ homConstSet E₁ E₁' := by
  obtain ⟨P, rfl⟩ := mem_homConstSet.1 hz
  exact mem_homConstSet.2
    ⟨homComp R (homComp P Q), by rw [homConst_homComp, homConst_homComp, mul_assoc]⟩

theorem homConstSet_vc {E₁ E₁' : WeierstrassCurve F} [E₁.IsElliptic] [E₁'.IsElliptic]
    (C C' : VariableChange F) (h : C • E = E₁) (h' : C' • E' = E₁') :
    ∃ c : F, c ≠ 0 ∧ (homConstSet E₁ E₁' : Set F) = (c * ·) '' homConstSet E E' := by
  set Q := vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h)
  set R := vcHom C' h'
  set Q' := vcHom C h
  set R' := vcHom C'⁻¹ (inv_smul_eq_of_smul_eq C' h')
  have e1 : homConst E₁ E Q * homConst E E₁ Q' = 1 := homConst_vcHom_mul_inv C h
  have e2 : homConst E₁' E' R' * homConst E' E₁' R = 1 := homConst_vcHom_mul_inv C' h'
  set c := homConst E' E₁' R * homConst E₁ E Q
  have hc : c * (homConst E₁' E' R' * homConst E E₁ Q') = 1 := by
    linear_combination (homConst E₁' E' R' * homConst E' E₁' R) * e1 + e2
  refine ⟨c, left_ne_zero_of_mul_eq_one hc, ?_⟩
  ext z
  simp only [SetLike.mem_coe, Set.mem_image]
  constructor
  · intro hz
    refine ⟨homConst E₁' E' R' * z * homConst E E₁ Q', homConstSet_le_mul Q' R' hz, ?_⟩
    linear_combination z * hc
  · rintro ⟨w, hw, rfl⟩
    have := homConstSet_le_mul Q R hw
    convert this using 1
    ring

end ConstSet

section Lattice

open Elliptic

theorem homConstSet_weierstrassCurve (L₁ L₂ : PeriodPair) :
    homConstSet (weierstrassCurve L₁) (weierstrassCurve L₂) = latticeHom L₁ L₂ := by
  ext z
  rw [mem_homConstSet]
  constructor
  · rintro ⟨Q, rfl⟩
    exact homConst_mem_latticeHom Q
  · intro hz
    exact ⟨latticeToHom ⟨z, hz⟩, homConst_latticeToHom ⟨z, hz⟩⟩

end Lattice

end GroundTheory.Global
end
end

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.ReductionIsogenyMap
section
namespace GroundTheory.Global

noncomputable section

open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)

section E1

theorem injective_eval₂_residue_gaussX₂ :
    Function.Injective (eval₂RingHom (ResidueField.map (liftJ₂ W W'))
      (residue _ (gaussX (gaussCurve W W')))) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro p hp
  have h1 := congrArg (gaussResidue (gaussCurve W W')) hp
  have hc : (gaussResidue (gaussCurve W W')).comp (ResidueField.map (liftJ₂ W W')) =
      (algebraMap (ResidueField (gaussRing W)) _).comp
        (ResidueField.map (algebraMap 𝒪 (gaussRing W))) := by
    rw [ResidueField.map_comp, ← RingHom.comp_assoc, gaussResidue_comp_residueField_map]
  rw [map_zero, coe_eval₂RingHom, Polynomial.hom_eval₂, gaussResidue_gaussX, hc,
    ← Polynomial.eval₂_map, ← aeval_def] at h1
  have hmap : p.map (ResidueField.map (algebraMap 𝒪 (gaussRing W))) = 0 := by
    by_contra hne
    exact transcendental_genX ((gaussCurve W W').map (residue (gaussRing W))) ⟨_, hne, h1⟩
  exact (Polynomial.map_eq_zero_iff (ResidueField.map _).injective).1 hmap

variable [DecidableEq (ResidueField (gaussRing (gaussCurve W W')))] [W.IsElliptic] [W'.IsElliptic]

theorem red₂_def (V : WeierstrassCurve 𝒪)
    (P : ((V.baseChange K).baseChange (liftField₂ K W W')).toAffine.Point) :
    red₂ K W W' V P = reducePoint (liftField₂ K W W') (V.map (liftJ₂ W W'))
      (pointCongr (map_baseChange_eq_map_of K V (liftJ₂ W W') (liftField₂ K W W')
        (liftJ₂_algebraMap K W W')) P) :=
  rfl

theorem red₂_genPt₂ : ∃ n, red₂ K W W' W' (genPt₂ K W W') = Point.some
    (residue _ (gaussX (gaussCurve W W'))) (residue _ (gaussY (gaussCurve W W'))) n := by
  obtain ⟨hT, eT⟩ := genPt₂_eq K W W'
  have h₁ : (curveK (liftField₂ K W W') (W'.map (liftJ₂ W W'))).Nonsingular
      (algebraMap _ (liftField₂ K W W') (gaussX (gaussCurve W W')))
      (algebraMap _ (liftField₂ K W W') (gaussY (gaussCurve W W'))) := by
    show ((W'.map (liftJ₂ W W')).map (algebraMap _ (liftField₂ K W W'))).toAffine.Nonsingular _ _
    rw [← map_baseChange_eq_map_of K W' (liftJ₂ W W') (liftField₂ K W W') (liftJ₂_algebraMap K W W')]
    exact hT
  have n := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    (equation_residue _ (equation_of_map _ _ h₁.1))
  refine ⟨n, ?_⟩
  rw [red₂, eT, pointCongr_some]
  exact reducePoint_some_integral _ _ h₁ n


set_option maxHeartbeats 1000000 in
theorem red₂_genEval_eq_zero
    {ψ : ((W.baseChange K).baseChange (W'.baseChange K).toAffine.FunctionField).toAffine.Point}
    (hψ : RespectsAdd (W'.baseChange K) (W.baseChange K) ψ)
    {P : ((W'.baseChange K).baseChange (liftField₂ K W W')).toAffine.Point}
    (hP : IsGenPt (W'.baseChange K) P) (hPT : IsGenPt (W'.baseChange K) (P + genPt₂ K W W'))
    (h0 : red₂ K W W' W' P = 0) :
    red₂ K W W' W (Point.map (genEval (W'.baseChange K) P hP) ψ) = 0 := by
  have hjM := liftJ₂_algebraMap K W W'
  have hTg : IsGenPt (W'.baseChange K) (genPt₂ K W W') := (transOver_genPt₂ K W W').isGenPt
  obtain ⟨nT, rT⟩ := red₂_genPt₂ K W W'
  obtain ⟨hT, eT⟩ := genPt₂_eq K W W'

  have rPT : red₂ K W W' W' (P + genPt₂ K W W') = red₂ K W W' W' (genPt₂ K W W') := by
    rw [red₂_add, h0, zero_add]
  have hne : reducePoint (liftField₂ K W W') (W'.map (liftJ₂ W W')) (pointCongr (map_baseChange_eq_map_of K W' (liftJ₂ W W') (liftField₂ K W W') hjM)
      (P + genPt₂ K W W')) ≠ 0 := by
    rw [← red₂_def, rPT, rT]; exact Point.some_ne_zero _
  obtain ⟨x₃, y₃, h₃, e₃⟩ := exists_integral_of_reducePoint_ne_zero _ _ hne
  have n₃ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    (equation_residue _ (equation_of_map _ _ h₃.1))
  have rP3 : red₂ K W W' W' (P + genPt₂ K W W') = Point.some _ _ n₃ := by
    rw [red₂_def, e₃, reducePoint_some_integral _ _ h₃ n₃]
  rw [rPT, rT, Point.some.injEq] at rP3
  obtain ⟨ex, ey⟩ := rP3
  have hPT' : P + genPt₂ K W W' = pointCongr (map_baseChange_eq_map_of K W' (liftJ₂ W W') (liftField₂ K W W') hjM).symm
      (Point.some _ _ h₃) := by
    rw [← e₃, pointCongr_pointCongr]; rfl
  rw [pointCongr_some] at hPT'
  obtain ⟨h₃', e₃'⟩ : ∃ h₃' : ((W'.baseChange K).baseChange (liftField₂ K W W')).toAffine.Nonsingular
      (algebraMap _ (liftField₂ K W W') x₃) (algebraMap _ (liftField₂ K W W') y₃), P + genPt₂ K W W' = Point.some _ _ h₃' :=
    ⟨_, hPT'⟩

  have hxy₃ : (W'.map (liftJ₂ W W')).toAffine.Equation x₃ y₃ :=
    (WeierstrassCurve.Affine.map_equation (W'.map (liftJ₂ W W')).toAffine (IsFractionRing.injective _ (liftField₂ K W W'))
      x₃ y₃).mp h₃.1
  have hT₁ : (curveK (liftField₂ K W W') (W'.map (liftJ₂ W W'))).Nonsingular (algebraMap _ (liftField₂ K W W') (gaussX (gaussCurve W W')))
      (algebraMap _ (liftField₂ K W W') (gaussY (gaussCurve W W'))) := by
    show ((W'.map (liftJ₂ W W')).map (algebraMap _ (liftField₂ K W W'))).toAffine.Nonsingular _ _
    rw [← map_baseChange_eq_map_of K W' (liftJ₂ W W') (liftField₂ K W W') hjM]; exact hT
  have hxyT : (W'.map (liftJ₂ W W')).toAffine.Equation (gaussX (gaussCurve W W')) (gaussY (gaussCurve W W')) :=
    (WeierstrassCurve.Affine.map_equation (W'.map (liftJ₂ W W')).toAffine (IsFractionRing.injective _ (liftField₂ K W W'))
      _ _).mp hT₁.1
  have hxT := injective_eval₂_residue_gaussX₂ W W'
  have hx₃ : Function.Injective (eval₂RingHom (ResidueField.map (liftJ₂ W W')) (residue _ x₃)) := by
    rw [← ex]; exact hxT
  have g₃ : IsGenPt (W'.baseChange K) (Point.some _ _ h₃') := e₃' ▸ hPT
  have gT : IsGenPt (W'.baseChange K) (Point.some _ _ hT) := eT ▸ hTg
  have m₃ := reducePoint_genEval (K := K) (W := W') (W' := W) (j := liftJ₂ W W') (M := liftField₂ K W W') (hxy := hxy₃)
    (hx := hx₃) hjM h₃' g₃ ψ
  have mT := reducePoint_genEval (K := K) (W := W') (W' := W) (j := liftJ₂ W W') (M := liftField₂ K W W') (hxy := hxyT)
    (hx := hxT) hjM hT gT ψ
  have hfe := fieldEvalRed_congr W' (liftJ₂ W W') hxy₃ hxyT hx₃ hxT ex.symm ey.symm

  have hadd := (respectsAdd_iff ψ).mp hψ (liftField₂ K W W') P (genPt₂ K W W') hP hTg hPT
  have hR : red₂ K W W' W (Point.map (genEval (W'.baseChange K) _ hPT) ψ) =
      red₂ K W W' W (Point.map (genEval (W'.baseChange K) _ hTg) ψ) := by
    rw [genEval_congr _ e₃' hPT g₃, genEval_congr _ eT hTg gT]
    rw [red₂_def, red₂_def, m₃, mT]
    apply point_ext_xy
    · rw [pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff, pointCongr_eq_zero_iff,
        pointMapRing_eq_zero_iff]
    · rw [xOf_pointCongr, xOf_pointMapRing, xOf_pointCongr, xOf_pointMapRing, hfe]
    · rw [yOf_pointCongr, yOf_pointMapRing, yOf_pointCongr, yOf_pointMapRing, hfe]
  rw [hadd, red₂_add] at hR
  exact add_eq_right.mp hR

end E1

section Isogeny

theorem reducePoint_some_ne_zero (V : WeierstrassCurve 𝒪) [V.IsElliptic] {X₀ Y₀ : K}
    (h : (curveK K V).Nonsingular X₀ Y₀) (hX : X₀ ∈ Set.range (algebraMap 𝒪 K)) :
    reducePoint K V (Point.some X₀ Y₀ h) ≠ 0 := by
  obtain ⟨x, rfl⟩ := hX
  obtain ⟨y, rfl⟩ := exists_y_of_equation K V h.1
  rw [reducePoint_some_integral K V h (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    (equation_residue V (equation_of_map K V h.1)))]
  exact Point.some_ne_zero _

variable [W.IsElliptic] [W'.IsElliptic]


set_option maxHeartbeats 1000000 in
theorem reduceFF_isogeny_ne_zero (φ : Isogeny (W.baseChange K) (W'.baseChange K)) :
    reduceFF K W W' φ.1 ≠ 0 := by
  letI : DecidableEq (ResidueField (gaussRing (gaussCurve W W'))) := Classical.decEq _
  letI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  letI : DecidableEq K := Classical.decEq K
  intro hφ
  have hP : IsGenPt (W'.baseChange K) (Point.map (IsScalarTower.toAlgHom K
      (W.baseChange K).toAffine.FunctionField (liftField₂ K W W')) φ.1) :=
    isGenPt_map _ _ φ.isGenPt
  have hPT : IsGenPt (W'.baseChange K) (Point.map (IsScalarTower.toAlgHom K
      (W.baseChange K).toAffine.FunctionField (liftField₂ K W W')) φ.1 + genPt₂ K W W') :=
    ((transOver_genPt₂ K W W').add_left φ.1).isGenPt
  have key := red₂_genEval_eq_zero K W W' (dualOver φ).respectsAdd hP hPT
    (red₂_map_of_reduceFF_eq_zero K W W' hφ)
  have hcomp := congrArg Subtype.val (dualOver_comp φ)
  rw [Isogeny.mulIsogeny_val] at hcomp
  have hc2 : Point.map (genEval (W'.baseChange K) φ.1 φ.isGenPt) (dualOver φ).1 =
      (φ.degree : ℤ) • GroundTheory.Arith.Abelian.genericPoint (W.baseChange K) := hcomp
  rw [genEval_map _ _ φ.isGenPt, ← Point.map_map, hc2] at key

  have hd : ((φ.degree : ℤ)) ≠ 0 := isogeny_degree_ne_zero φ
  have hne : reduceFF K W W ((φ.degree : ℤ) • GroundTheory.Arith.Abelian.genericPoint (W.baseChange K))
      ≠ 0 := by
    rw [reduceFF_zsmul_genericPoint]
    exact zsmul_genericPoint_ne_zero _ hd
  have hne' : reducePoint (W.baseChange K).toAffine.FunctionField (gaussCurve W W)
      (pointCongr (gaussCurve_map_functionField K W W).symm
        ((φ.degree : ℤ) • GroundTheory.Arith.Abelian.genericPoint (W.baseChange K))) ≠ 0 := by
    intro h0
    apply hne
    simp only [reduceFF, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, reductionHom_apply]
    rw [pointCongr_eq_zero_iff, pointMapRing_eq_zero_iff]
    exact h0
  obtain ⟨a, b, h, e⟩ := exists_integral_of_reducePoint_ne_zero _ _ hne'
  have e' : (φ.degree : ℤ) • GroundTheory.Arith.Abelian.genericPoint (W.baseChange K) =
      pointCongr (gaussCurve_map_functionField K W W) (Point.some _ _ h) := by
    rw [← e, pointCongr_pointCongr]; rfl
  rw [pointCongr_some] at e'
  rw [e'] at key
  have ha : ∀ g : gaussRing W, (IsScalarTower.toAlgHom K (W.baseChange K).toAffine.FunctionField
      (liftField₂ K W W')) (algebraMap (gaussRing W) _ g) =
        algebraMap (gaussRing (gaussCurve W W')) (liftField₂ K W W')
          (algebraMap (gaussRing W) _ g) := fun g => by
    rw [IsScalarTower.coe_toAlgHom', ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  rw [Point.map_some, red₂_def, pointCongr_some] at key
  exact reducePoint_some_ne_zero _ _ _ ⟨_, (ha a).symm⟩ key

theorem isGenPt_reduceFF_isogeny (φ : Isogeny (W.baseChange K) (W'.baseChange K)) :
    IsGenPt (W'.map (residue 𝒪)) (reduceFF K W W' φ.1) ∧
      RespectsAdd (W.map (residue 𝒪)) (W'.map (residue 𝒪)) (reduceFF K W W' φ.1) := by
  letI : DecidableEq (ResidueField (gaussRing (gaussCurve W W))) := Classical.decEq _
  have h := respectsAdd_reduceFF K W W' φ.1 φ.respectsAdd
  exact ⟨isGenPt_of_respectsAdd h (reduceFF_isogeny_ne_zero K W W' φ), h⟩

def reduceIsogeny (φ : Isogeny (W.baseChange K) (W'.baseChange K)) :
    Isogeny (W.map (residue 𝒪)) (W'.map (residue 𝒪)) :=
  ⟨reduceFF K W W' φ.1, isIsogeny_of_respectsAdd (isGenPt_reduceFF_isogeny K W W' φ).2
    (reduceFF_isogeny_ne_zero K W W' φ)⟩

theorem reduceIsogeny_val (φ : Isogeny (W.baseChange K) (W'.baseChange K)) :
    (reduceIsogeny K W W' φ).1 = reduceFF K W W' φ.1 :=
  rfl

theorem reduceIsogeny_comp (W'' : WeierstrassCurve 𝒪) [W''.IsElliptic]
    (ψ : Isogeny (W'.baseChange K) (W''.baseChange K))
    (φ : Isogeny (W.baseChange K) (W'.baseChange K)) :
    reduceIsogeny K W W'' (ψ.comp φ) = (reduceIsogeny K W' W'' ψ).comp (reduceIsogeny K W W' φ) :=
  Subtype.ext (reduceFF_map_genEval K W W' W'' φ.isGenPt (isGenPt_reduceFF_isogeny K W W' φ).1 ψ.1)

theorem reduceIsogeny_mulIsogeny (n : ℤ) (hn : n ≠ 0) :
    reduceIsogeny K W W (mulIsogeny (W.baseChange K) n hn) = mulIsogeny (W.map (residue 𝒪)) n hn :=
  Subtype.ext (reduceFF_zsmul_genericPoint K W n)

end Isogeny

end

end GroundTheory.Global
end

