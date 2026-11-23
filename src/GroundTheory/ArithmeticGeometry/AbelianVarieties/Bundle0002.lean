module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupReduction
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupFiltration
public import GroundTheory.LocalFields.FormalGroups.Basics
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsPullback
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.TorsionGalois
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.KernelCard
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisionPoints

@[expose] public section

-- bundled from GroundTheory.ArithmeticGeometry.AbelianVarieties.ReductionTorsion
section
namespace GroundTheory.Arith.Abelian

noncomputable section

open IsLocalRing

section Congr

variable {F : Type*} [Field F] [DecidableEq F]

def pointCongr {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

theorem pointCongr_some {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) {x y : F}
    (hxy : W₁.toAffine.Nonsingular x y) :
    pointCongr h (.some x y hxy) = .some x y (h ▸ hxy) := by
  subst h
  rfl

end Congr

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

variable [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [(W.map (algebraMap 𝒪 K)).IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

section Good

end Good

end

end GroundTheory.Arith.Abelian
end

-- bundled from GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilGaloisFunctionField
section
namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WithZero
open scoped Polynomial.Bivariate

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L] (W₀ : WeierstrassCurve K)

section Coord

theorem polynomial_map_galois (σ : L ≃ₐ[K] L) :
    (W₀.baseChange L).toAffine.polynomial.map (mapRingHom (σ : L →+* L)) =
      (W₀.baseChange L).toAffine.polynomial := by
  have h1 : (W₀.baseChange L).map (σ : L →+* L) = W₀.baseChange L :=
    WeierstrassCurve.map_baseChange (R := K) (S := K) W₀ (σ : L →ₐ[K] L)
  rw [← Affine.map_polynomial]
  exact congrArg (fun V : WeierstrassCurve L => V.toAffine.polynomial) h1

noncomputable def galCoord (σ : L ≃ₐ[K] L) :
    (W₀.baseChange L).toAffine.CoordinateRing ≃+* (W₀.baseChange L).toAffine.CoordinateRing :=
  Ideal.quotientEquiv _ _ (Polynomial.mapEquiv (Polynomial.mapEquiv σ.toRingEquiv)) (by
    have h : (Polynomial.mapEquiv (Polynomial.mapEquiv σ.toRingEquiv))
        (W₀.baseChange L).toAffine.polynomial = (W₀.baseChange L).toAffine.polynomial :=
      polynomial_map_galois W₀ σ
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun q => Ideal.span {q}) h.symm)

theorem galCoord_mk (σ : L ≃ₐ[K] L) (p : L[X][Y]) :
    galCoord W₀ σ (CoordinateRing.mk _ p) =
      CoordinateRing.mk _ (p.map (mapRingHom (σ : L →+* L))) :=
  rfl

end Coord

section FunctionField

noncomputable def galFF (σ : L ≃ₐ[K] L) :
    (W₀.baseChange L).toAffine.FunctionField ≃+* (W₀.baseChange L).toAffine.FunctionField :=
  IsFractionRing.ringEquivOfRingEquiv (galCoord W₀ σ)

theorem galFF_algebraMap_coord (σ : L ≃ₐ[K] L) (a : (W₀.baseChange L).toAffine.CoordinateRing) :
    galFF W₀ σ (algebraMap _ (W₀.baseChange L).toAffine.FunctionField a) =
      algebraMap _ (W₀.baseChange L).toAffine.FunctionField (galCoord W₀ σ a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

theorem galFF_algebraMap (σ : L ≃ₐ[K] L) (c : L) :
    galFF W₀ σ (algebraMap L (W₀.baseChange L).toAffine.FunctionField c) =
      algebraMap L (W₀.baseChange L).toAffine.FunctionField (σ c) := by
  have e : ∀ a : L, algebraMap L (W₀.baseChange L).toAffine.FunctionField a =
      algebraMap (W₀.baseChange L).toAffine.CoordinateRing _
        (CoordinateRing.mk _ (C (C a))) := fun a => rfl
  rw [e, e, galFF_algebraMap_coord, galCoord_mk]
  simp

theorem galFF_genX (σ : L ≃ₐ[K] L) : galFF W₀ σ (genX (W₀.baseChange L)) = genX (W₀.baseChange L) := by
  rw [genX, galFF_algebraMap_coord, galCoord_mk]
  simp

theorem galFF_genY (σ : L ≃ₐ[K] L) : galFF W₀ σ (genY (W₀.baseChange L)) = genY (W₀.baseChange L) := by
  rw [genY, galFF_algebraMap_coord, galCoord_mk]
  simp

theorem galFF_algebraMap_base (σ : L ≃ₐ[K] L) (k : K) :
    galFF W₀ σ (algebraMap K (W₀.baseChange L).toAffine.FunctionField k) =
      algebraMap K (W₀.baseChange L).toAffine.FunctionField k := by
  rw [IsScalarTower.algebraMap_apply K L, galFF_algebraMap, AlgEquiv.commutes]

theorem galFF_symm_algebraMap (σ : L ≃ₐ[K] L) (c : L) :
    (galFF W₀ σ).symm (algebraMap L (W₀.baseChange L).toAffine.FunctionField c) =
      algebraMap L (W₀.baseChange L).toAffine.FunctionField (σ.symm c) := by
  rw [RingEquiv.symm_apply_eq, galFF_algebraMap, AlgEquiv.apply_symm_apply]

theorem galFF_symm_genX (σ : L ≃ₐ[K] L) :
    (galFF W₀ σ).symm (genX (W₀.baseChange L)) = genX (W₀.baseChange L) := by
  rw [RingEquiv.symm_apply_eq, galFF_genX]

theorem galFF_symm_genY (σ : L ≃ₐ[K] L) :
    (galFF W₀ σ).symm (genY (W₀.baseChange L)) = genY (W₀.baseChange L) := by
  rw [RingEquiv.symm_apply_eq, galFF_genY]

theorem map_galFF_curve (σ : L ≃ₐ[K] L) :
    ((W₀.baseChange L).baseChange (W₀.baseChange L).toAffine.FunctionField).map
      (galFF W₀ σ : _ →+* _) =
      (W₀.baseChange L).baseChange (W₀.baseChange L).toAffine.FunctionField := by
  have e : ∀ a : K, galFF W₀ σ (algebraMap L (W₀.baseChange L).toAffine.FunctionField
      (algebraMap K L a)) = algebraMap L _ (algebraMap K L a) := fun a => by
    rw [galFF_algebraMap, AlgEquiv.commutes]
  ext <;> exact e _

noncomputable def galConj (σ : L ≃ₐ[K] L)
    (ψ : (W₀.baseChange L).toAffine.FunctionField →ₐ[L] (W₀.baseChange L).toAffine.FunctionField) :
    (W₀.baseChange L).toAffine.FunctionField →ₐ[L] (W₀.baseChange L).toAffine.FunctionField :=
  { ((galFF W₀ σ).toRingHom.comp ψ.toRingHom).comp (galFF W₀ σ).symm.toRingHom with
    commutes' := fun c => by
      change galFF W₀ σ (ψ ((galFF W₀ σ).symm (algebraMap L _ c))) = algebraMap L _ c
      rw [galFF_symm_algebraMap, ψ.commutes, galFF_algebraMap, AlgEquiv.apply_symm_apply] }

theorem galConj_apply (σ : L ≃ₐ[K] L)
    (ψ : (W₀.baseChange L).toAffine.FunctionField →ₐ[L] (W₀.baseChange L).toAffine.FunctionField)
    (f : (W₀.baseChange L).toAffine.FunctionField) :
    galConj W₀ σ ψ f = galFF W₀ σ (ψ ((galFF W₀ σ).symm f)) := rfl

end FunctionField

section AutPoint

variable {Fd : Type*} [Field Fd] (V : WeierstrassCurve Fd) (τ : Fd ≃+* Fd)
  (hV : V.map (τ : Fd →+* Fd) = V)

include hV in
theorem nonsingular_aut {x y : Fd} (h : V.toAffine.Nonsingular x y) :
    V.toAffine.Nonsingular (τ x) (τ y) := by
  have h1 := (Affine.map_nonsingular (W := V.toAffine) (f := (τ : Fd →+* Fd)) τ.injective x y).mpr h
  have hV' : V.toAffine.map (τ : Fd →+* Fd) = V.toAffine := hV
  rw [hV'] at h1
  exact h1

include hV in
theorem negY_aut (x y : Fd) : V.toAffine.negY (τ x) (τ y) = τ (V.toAffine.negY x y) := by
  have h1 := Affine.map_negY (W' := V.toAffine) (τ : Fd →+* Fd) x y
  have hV' : V.toAffine.map (τ : Fd →+* Fd) = V.toAffine := hV
  rw [hV'] at h1
  exact h1

include hV in
theorem addX_aut (x₁ x₂ ℓ : Fd) :
    V.toAffine.addX (τ x₁) (τ x₂) (τ ℓ) = τ (V.toAffine.addX x₁ x₂ ℓ) := by
  have h1 := Affine.map_addX (W' := V.toAffine) (τ : Fd →+* Fd) (x₁ := x₁) (x₂ := x₂) (ℓ := ℓ)
  have hV' : V.toAffine.map (τ : Fd →+* Fd) = V.toAffine := hV
  rw [hV'] at h1
  exact h1

include hV in
theorem addY_aut (x₁ x₂ y₁ ℓ : Fd) :
    V.toAffine.addY (τ x₁) (τ x₂) (τ y₁) (τ ℓ) = τ (V.toAffine.addY x₁ x₂ y₁ ℓ) := by
  have h1 := Affine.map_addY (W' := V.toAffine) (τ : Fd →+* Fd) (x₁ := x₁) (x₂ := x₂) (y₁ := y₁) (ℓ := ℓ)
  have hV' : V.toAffine.map (τ : Fd →+* Fd) = V.toAffine := hV
  rw [hV'] at h1
  exact h1

variable [DecidableEq Fd]

include hV in
theorem slope_aut (x₁ x₂ y₁ y₂ : Fd) :
    V.toAffine.slope (τ x₁) (τ x₂) (τ y₁) (τ y₂) = τ (V.toAffine.slope x₁ x₂ y₁ y₂) := by
  have h1 := Affine.map_slope (W := V.toAffine) (τ : Fd →+* Fd) x₁ x₂ y₁ y₂
  have hV' : V.toAffine.map (τ : Fd →+* Fd) = V.toAffine := hV
  rw [hV'] at h1
  exact h1

noncomputable def autPoint : V.toAffine.Point →+ V.toAffine.Point where
  toFun P := match P with
    | 0 => 0
    | .some x y h => .some (τ x) (τ y) (nonsingular_aut V τ hV h)
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = V.toAffine.negY x₂ y₂
    · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, Affine.Point.add_of_Y_eq (congr_arg τ hxy.1)
        (by rw [hxy.2, negY_aut V τ hV])]
    · have hxy' : ¬(τ x₁ = τ x₂ ∧ τ y₁ = V.toAffine.negY (τ x₂) (τ y₂)) := fun h =>
        hxy ⟨τ.injective h.1, τ.injective (by rw [h.2, negY_aut V τ hV])⟩
      rw [Affine.Point.add_some hxy, Affine.Point.add_some hxy']
      change Affine.Point.some _ _ _ = Affine.Point.some _ _ _
      simp only [Affine.Point.some.injEq]
      exact ⟨by rw [slope_aut V τ hV, addX_aut V τ hV],
        by rw [slope_aut V τ hV, addY_aut V τ hV]⟩

theorem autPoint_some {x y : Fd} (h : V.toAffine.Nonsingular x y) :
    autPoint V τ hV (.some x y h) = .some (τ x) (τ y) (nonsingular_aut V τ hV h) := rfl

end AutPoint

section Points

variable [DecidableEq L] [W₀.IsElliptic]

noncomputable def galFFPoint (σ : L ≃ₐ[K] L) :
    ((W₀.baseChange L).baseChange (W₀.baseChange L).toAffine.FunctionField).toAffine.Point →+
      ((W₀.baseChange L).baseChange (W₀.baseChange L).toAffine.FunctionField).toAffine.Point :=
  autPoint _ (galFF W₀ σ) (map_galFF_curve W₀ σ)


omit [DecidableEq L] in
theorem galFFPoint_genericPoint (σ : L ≃ₐ[K] L) :
    galFFPoint W₀ σ (genericPoint (W₀.baseChange L)) = genericPoint (W₀.baseChange L) := by
  rw [genericPoint, galFFPoint, autPoint_some]
  simp only [Affine.Point.some.injEq]
  exact ⟨galFF_genX W₀ σ, galFF_genY W₀ σ⟩


omit [W₀.IsElliptic] in
theorem galFFPoint_constPoint (σ : L ≃ₐ[K] L) (R : (W₀.baseChange L).toAffine.Point) :
    galFFPoint W₀ σ (constPoint (W₀.baseChange L) R) =
      constPoint (W₀.baseChange L) (galPointsHom K L W₀ σ R) := by
  cases R with
  | zero =>
    have h0 : (Affine.Point.zero : (W₀.baseChange L).toAffine.Point) = 0 := rfl
    rw [h0, map_zero, map_zero, map_zero, map_zero]
  | some x y h =>
    change autPoint _ _ _ (Affine.Point.some _ _ _) = Affine.Point.some _ _ _
    rw [autPoint_some]
    simp only [Affine.Point.some.injEq]
    exact ⟨galFF_algebraMap W₀ σ x, galFF_algebraMap W₀ σ y⟩

omit [DecidableEq L] in
theorem map_galConj_genericPoint (σ : L ≃ₐ[K] L)
    (ψ : (W₀.baseChange L).toAffine.FunctionField →ₐ[L] (W₀.baseChange L).toAffine.FunctionField) :
    Affine.Point.map (galConj W₀ σ ψ) (genericPoint (W₀.baseChange L)) =
      galFFPoint W₀ σ (Affine.Point.map ψ (genericPoint (W₀.baseChange L))) := by
  rw [genericPoint, Affine.Point.map_some, Affine.Point.map_some, galFFPoint, autPoint_some]
  simp only [Affine.Point.some.injEq]
  refine ⟨?_, ?_⟩
  · rw [galConj_apply, galFF_symm_genX]
  · rw [galConj_apply, galFF_symm_genY]
variable [IsAlgClosed L]

theorem galConj_translate (σ : L ≃ₐ[K] L) (R : (W₀.baseChange L).toAffine.Point) :
    galConj W₀ σ (translate (W₀.baseChange L) R) =
      translate (W₀.baseChange L) (galPointsHom K L W₀ σ R) := by
  apply algHom_eq_of_map_genericPoint
  rw [map_galConj_genericPoint, map_translate_genericPoint, map_add (f := _), galFFPoint_genericPoint,
    galFFPoint_constPoint, map_translate_genericPoint]

theorem galFF_translate (σ : L ≃ₐ[K] L) (R : (W₀.baseChange L).toAffine.Point)
    (f : (W₀.baseChange L).toAffine.FunctionField) :
    galFF W₀ σ (translate (W₀.baseChange L) R f) =
      translate (W₀.baseChange L) (galPointsHom K L W₀ σ R) (galFF W₀ σ f) := by
  rw [← galConj_translate, galConj_apply, RingEquiv.symm_apply_apply]

end Points

end GroundTheory.Arith.Abelian
end

-- bundled from GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilTranslate
section
namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
  [W.IsElliptic]

theorem translate_add (R S : W.toAffine.Point) :
    translate W (R + S) = (translate W R).comp (translate W S) := by
  apply algHom_eq_of_map_genericPoint
  rw [map_translate_genericPoint, ← Point.map_map, map_translate_genericPoint,
    map_add (Point.map (translate W R)), map_translate_genericPoint, map_constPoint,
    map_add (constPoint W), add_assoc]

theorem translate_translate (R S : W.toAffine.Point) (f : W.toAffine.FunctionField) :
    translate W R (translate W S f) = translate W (R + S) f := by
  rw [translate_add]
  rfl

theorem translate_injective (R : W.toAffine.Point) : Function.Injective (translate W R) :=
  (translate W R).toRingHom.injective

theorem translate_ne_zero (R : W.toAffine.Point) {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    translate W R f ≠ 0 :=
  (map_ne_zero_iff _ (translate_injective W R)).mpr hf

theorem valuationPoint_translate (P R : W.toAffine.Point) (f : W.toAffine.FunctionField) :
    valuationPoint W P (translate W R f) = valuationPoint W (P + R) f := by
  rw [← valuationInfty_translate, ← valuationInfty_translate, translate_translate]

theorem ordPoint_translate (P R : W.toAffine.Point) {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    ordPoint W P (translate W R f) = ordPoint W (P + R) f := by
  have h := valuationPoint_translate W P R f
  rw [valuationPoint_eq_exp W P (translate_ne_zero W R hf), valuationPoint_eq_exp W (P + R) hf,
    exp_inj] at h
  exact neg_injective h






theorem exists_zsmul_eq {n : ℤ} (hn : n ≠ 0) (Q : W.toAffine.Point) : ∃ P, n • P = Q := by
  classical
  cases Q with
  | zero => exact ⟨0, smul_zero n⟩
  | some xQ yQ hQ =>
    set p : F[X] := W.Φ n - C xQ * W.ΨSq n with hpdef
    have hlt : (C xQ * W.ΨSq n).natDegree < (W.Φ n).natDegree := by
      rw [natDegree_Φ]
      calc (C xQ * W.ΨSq n).natDegree ≤ (W.ΨSq n).natDegree := natDegree_C_mul_le _ _
        _ ≤ n.natAbs ^ 2 - 1 := natDegree_ΨSq_le W n
        _ < n.natAbs ^ 2 := by
          have : 0 < n.natAbs ^ 2 := pow_pos (Int.natAbs_pos.mpr hn) 2
          omega
    have hdeg : p.natDegree = n.natAbs ^ 2 := by
      rw [hpdef, natDegree_sub_eq_left_of_natDegree_lt hlt, natDegree_Φ]
    have hpos : 0 < p.natDegree := by rw [hdeg]; exact pow_pos (Int.natAbs_pos.mpr hn) 2
    have hdeg0 : p.degree ≠ 0 := (natDegree_pos_iff_degree_pos.mp hpos).ne'
    obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_root p hdeg0
    have hx₀' : (W.Φ n).eval x₀ = xQ * (W.ΨSq n).eval x₀ := by
      rw [IsRoot, hpdef, eval_sub, eval_mul, eval_C, sub_eq_zero] at hx₀
      exact hx₀
    have hψ : (W.ΨSq n).eval x₀ ≠ 0 := by
      intro h0
      obtain ⟨a, b, hab⟩ := isCoprime_Φ_ΨSq W n
      have := congrArg (eval x₀) hab
      rw [eval_add, eval_mul, eval_mul, h0, hx₀', h0, mul_zero, mul_zero, mul_zero, add_zero,
        eval_one] at this
      exact zero_ne_one this
    obtain ⟨y₀, hy₀⟩ := exists_equation W x₀
    have h₀ : W.toAffine.Nonsingular x₀ y₀ := equation_iff_nonsingular.mp hy₀
    have hne : n • Point.some x₀ y₀ h₀ ≠ 0 := fun h => hψ ((zsmul_eq_zero_iff W h₀ n).mp h)
    have hx : xOf W (n • Point.some x₀ y₀ h₀) = xQ := by
      rw [xOf_zsmul W h₀ n hψ, hx₀', mul_div_cancel_right₀ _ hψ]
    have key : ∀ {x y : F} (h : W.toAffine.Nonsingular x y), x = xQ →
        Point.some x y h = Point.some xQ yQ hQ ∨ Point.some x y h = -Point.some xQ yQ hQ := by
      rintro x y h rfl
      rcases Y_eq_of_X_eq h.1 hQ.1 rfl with hy | hy
      · left
        subst hy
        rfl
      · right
        rw [Point.neg_some]
        subst hy
        rfl
    obtain ⟨y', h', he⟩ := exists_eq_some_xOf W hne
    rcases key h' hx with e | e
    · exact ⟨_, he.trans e⟩
    · refine ⟨-Point.some x₀ y₀ h₀, ?_⟩
      rw [smul_neg, he, e, neg_neg]
end GroundTheory.Arith.Abelian
end

