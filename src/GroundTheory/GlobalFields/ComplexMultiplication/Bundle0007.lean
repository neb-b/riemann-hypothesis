module

public import Mathlib
public import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraicIsogeny
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenySeparable
public import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogenyExists
public import GroundTheory.GlobalFields.ComplexMultiplication.RespectsAddUniversal
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsTranslate

@[expose] public section

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraicConverse
section
open Filter Topology Set Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian KaehlerDifferential
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {L₁ L₂ : PeriodPair}

theorem homConst_ne_zero {Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)} (hQ : Q ≠ 0) :
    homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q ≠ 0 := by
  set φ := isogOfHom Q hQ
  have hsep : φ.IsSeparable := by
    have := φ.finiteDimensional
    exact Algebra.IsSeparable.of_integral _ _
  have h1 := (isSeparable_iff_isogConst_ne_zero φ).1 hsep
  have h2 : isogConst φ = homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q := by
    apply (algebraMap ℂ (weierstrassCurve L₁).toAffine.FunctionField).injective
    rw [algebraMap_isogConst, algebraMap_homConst]
    rfl
  rwa [← h2]

theorem homConst_injective :
    Function.Injective (homConst (weierstrassCurve L₁) (weierstrassCurve L₂)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro Q h
  by_contra hQ
  exact homConst_ne_zero hQ h

theorem exists_eq_constMap_of_omegaDeriv {W : WeierstrassCurve ℂ}
    (P : (W.baseChange MeroField).toAffine.Point) (h : omegaDeriv (omegaAt W P) = 0) :
    ∃ R : W.toAffine.Point, P = constMap W MeroField R := by
  rcases P with _ | ⟨u, v, hP⟩
  · exact ⟨0, (map_zero _).symm⟩
  obtain ⟨s₁, s₂⟩ := omegaAt_some_spec W hP
  have e₁ := congrArg omegaDeriv s₁
  have e₂ := congrArg omegaDeriv s₂
  rw [LinearMap.map_smul, h, smul_eq_mul, mul_zero, omegaDeriv_D, eq_comm] at e₁ e₂
  obtain ⟨c, rfl⟩ := exists_eq_algebraMap_of_germDeriv_eq_zero e₁
  obtain ⟨d, rfl⟩ := exists_eq_algebraMap_of_germDeriv_eq_zero e₂
  have hcd : W.toAffine.Nonsingular c d :=
    (W.toAffine.baseChange_nonsingular (f := Algebra.ofId ℂ MeroField)
      (algebraMap ℂ MeroField).injective c d).1 hP
  exact ⟨.some c d hcd, rfl⟩

theorem exists_map_ellEval_eq {Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)}
    (hQ : Q ≠ 0) :
    ∃ c : ℂ, Point.map (ellEval L₁) Q.1 =
      affinePoint L₂ (homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q) c
        (homConst_ne_zero hQ) := by
  set α := homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q
  have h0 : α ≠ 0 := homConst_ne_zero hQ
  have e := omegaAt_eq_homConst_smul Q
  have e' := congrArg (kpush (ellEval L₁)) e
  rw [kpush_omegaAt, kpush_const_smul, invariantDifferential, kpush_omegaAt,
    map_ellEval_genericPoint, basePoint_eq] at e'
  have hω : omegaDeriv (omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1)) =
      algebraMap ℂ MeroField α := by
    rw [e', ← algebraMap_smul MeroField, LinearMap.map_smul, omegaDeriv_affinePoint, smul_eq_mul,
      map_one, mul_one]
  have hD : omegaDeriv (omegaAt (weierstrassCurve L₂)
      (Point.map (ellEval L₁) Q.1 - affinePoint L₂ α 0 h0)) = 0 := by
    have h1 : omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1 - affinePoint L₂ α 0 h0) =
        omegaAt (weierstrassCurve L₂) (Point.map (ellEval L₁) Q.1) -
          omegaAt (weierstrassCurve L₂) (affinePoint L₂ α 0 h0) :=
      map_sub (omegaHom (weierstrassCurve L₂)) _ _
    rw [h1, map_sub, hω, omegaDeriv_affinePoint, sub_self]
  obtain ⟨R, hR⟩ := exists_eq_constMap_of_omegaDeriv _ hD
  obtain ⟨c, rfl⟩ := toPoint_surjective (L := L₂) R
  refine ⟨0 + c, ?_⟩
  rw [← affinePoint_add_constMap, ← hR]
  abel

theorem homConst_mem_latticeHom (Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)) :
    homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q ∈ latticeHom L₁ L₂ := by
  by_cases hQ : Q = 0
  · rw [hQ, map_zero]
    exact zero_mem _
  set α := homConst (weierstrassCurve L₁) (weierstrassCurve L₂) Q
  have h0 : α ≠ 0 := homConst_ne_zero hQ
  obtain ⟨c, hc⟩ := exists_map_ellEval_eq hQ
  have hg : IsGenPt (weierstrassCurve L₂) Q.1 := isGenPt_of_mem_isogHom Q.2 (fun h ↦ hQ (Subtype.ext h))
  obtain ⟨hne, hQs⟩ := eq_some_xOf_yOf _ (isGenPt_ne_zero _ hg)
  rw [hQs, Point.map_some, affinePoint, Point.some.injEq] at hc
  obtain ⟨f, hf, hfe⟩ := exists_isEllipticFunction_ellEval_eq L₁ (xOf _ Q.1)
  obtain ⟨g, hg', hge⟩ := exists_isEllipticFunction_ellEval_eq L₁ (yOf _ Q.1)
  rw [hfe, germ_eq_germ_iff hf.1 (meromorphic_weierstrassP_affine L₂ α c)] at hc
  rw [hge, germ_eq_germ_iff hg'.1 (meromorphic_derivWeierstrassP_half_affine L₂ α c)] at hc
  obtain ⟨hcx, hcy⟩ := hc
  intro l hl
  obtain ⟨z, h1, h2, h3, h4, h5, h6⟩ := nonempty_of_mem_codiscrete (hcx.and (hcy.and
    ((eventually_affine hcx one_ne_zero l).and ((eventually_affine hcy one_ne_zero l).and
    ((eventually_affine (eventually_notMem_lattice L₂) h0 c).and
    (eventually_affine (eventually_notMem_lattice L₂) h0 (α * l + c)))))))
  beta_reduce at h1 h2
  simp only [one_mul] at h3 h4
  rw [hf.2 z l hl] at h3
  rw [hg'.2 z l hl] at h4
  have e₁ : ℘[L₂] (α * z + (α * l + c)) = ℘[L₂] (α * z + c) := by
    rw [← h1, h3, show α * (z + l) + c = α * z + (α * l + c) by ring]
  have e₂ : ℘'[L₂] (α * z + (α * l + c)) = ℘'[L₂] (α * z + c) := by
    have := h2.symm.trans h4
    rw [show α * (z + l) + c = α * z + (α * l + c) by ring] at this
    linear_combination 2 * this.symm
  have hpt : toPoint L₂ (α * z + (α * l + c)) = toPoint L₂ (α * z + c) := by
    rw [toPoint_of_notMem h6, toPoint_of_notMem h5]
    exact point_some_congr e₁ (by rw [e₂])
  have := torusToPoint_injective (L := L₂) (a₁ := Torus.mk L₂ _) (a₂ := Torus.mk L₂ _) hpt
  rw [Torus.mk_eq_mk_iff] at this
  simpa using this

theorem latticeToHom_homConst (Q : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂)) :
    latticeToHom ⟨_, homConst_mem_latticeHom Q⟩ = Q :=
  homConst_injective (by rw [homConst_latticeToHom])

theorem latticeToHom_add (α β : latticeHom L₁ L₂) :
    latticeToHom (α + β) = latticeToHom α + latticeToHom β :=
  homConst_injective (by
    rw [map_add (f := _), homConst_latticeToHom, homConst_latticeToHom, homConst_latticeToHom]
    rfl)

theorem ellEval_comp_translate (L : PeriodPair) (z : ℂ) :
    (ellEval L).comp (translate (weierstrassCurve L) (toPoint L z)) =
      (affineComp 1 z one_ne_zero).comp (ellEval L) := by
  apply algHom_eq_of_map_genericPoint' (E := weierstrassCurve L)
  rw [← Point.map_map, map_translate_genericPoint, map_add (f := _), map_ellEval_genericPoint,
    show constPoint (weierstrassCurve L) (toPoint L z) =
      constMap (weierstrassCurve L) _ (toPoint L z) from rfl, map_constMap, basePoint_eq,
    affinePoint_add_constMap, ← Point.map_map, map_ellEval_genericPoint, basePoint_eq,
    map_affineComp_affinePoint]
  exact affinePoint_congr L _ _ (by ring) (by ring)

theorem homPt_latticeToHom (α : latticeHom L₁ L₂) (z : ℂ) :
    homPt (latticeToHom α) (toPoint L₁ z) = toPoint L₂ (α * z) := by
  by_cases h0 : (α : ℂ) = 0
  · rw [latticeToHom_of_eq_zero α h0, homPt_zero, AddMonoidHom.zero_apply, h0, zero_mul,
      toPoint_zero]
  apply homPt_eq_of
  apply Point.map_injective (ellEval L₁)
  rw [Point.map_map, ellEval_comp_translate, ← Point.map_map, latticeToHom_of_ne_zero α h0,
    map_ellEval_isogPt, map_affineComp_affinePoint, map_add, map_ellEval_isogPt, map_constMap,
    affinePoint_add_constMap]
  exact affinePoint_congr L₂ _ _ (by ring) (by ring)

section End

variable {L : PeriodPair}

theorem latticeToHom_mul (α β : latticeHom L L) (h : (α : ℂ) * β ∈ latticeHom L L) :
    latticeToHom ⟨_, h⟩ = latticeToHom α * latticeToHom β := by
  by_cases hα : (α : ℂ) = 0
  · rw [latticeToHom_of_eq_zero α hα, zero_mul, latticeToHom_of_eq_zero _ (by simp [hα])]
  by_cases hβ : (β : ℂ) = 0
  · rw [latticeToHom_of_eq_zero β hβ, mul_zero, latticeToHom_of_eq_zero _ (by simp [hβ])]
  have hg : IsGenPt (weierstrassCurve L) (latticeToHom β).1 := by
    rw [latticeToHom_of_ne_zero β hβ]
    exact isGenPt_isogPt _ _
  apply Subtype.ext
  apply Point.map_injective (ellEval L)
  have e : Point.map (ellEval L) (latticeToHom β).1 = affinePoint L β 0 hβ := by
    rw [latticeToHom_of_ne_zero β hβ, map_ellEval_isogPt]
  rw [isogEnd_mul_def, homComp_of_isGenPt _ _ hg, Point.map_map, ← genEval_map _ (ellEval L) hg,
    genEval_congr _ e _ (isGenPt_affinePoint L β 0 hβ), genEval_affinePoint, ← Point.map_map,
    latticeToHom_of_ne_zero α hα, map_ellEval_isogPt, map_affineComp_affinePoint,
    latticeToHom_of_ne_zero _ (mul_ne_zero hα hβ), map_ellEval_isogPt]
  exact affinePoint_congr L _ _ rfl (by ring)

end End

end Elliptic
end GroundTheory.Global
end
end

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.BaseChange
section
namespace GroundTheory.Global

open Polynomial WeierstrassCurve IntermediateField GroundTheory.Arith.Abelian
open WeierstrassCurve.Affine (Point equation_iff)

universe u

section FF

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F') (E : WeierstrassCurve F)

noncomputable def ffMap : E.toAffine.FunctionField →+* (E.map σ).toAffine.FunctionField :=
  letI := σ.toAlgebra
  (bcEmb (F' := F') E).toRingHom

theorem ffMap_genX : ffMap σ E (genX E) = genX (E.map σ) := by
  let _ := σ.toAlgebra
  exact bcEmb_genX (F' := F') E

theorem ffMap_genY : ffMap σ E (genY E) = genY (E.map σ) := by
  let _ := σ.toAlgebra
  exact bcEmb_genY (F' := F') E

theorem ffMap_algebraMap (a : F) :
    ffMap σ E (algebraMap F E.toAffine.FunctionField a) =
      algebraMap F' (E.map σ).toAffine.FunctionField (σ a) := by
  let _ := σ.toAlgebra
  exact (bcEmb (F' := F') E).commutes a

theorem ringHom_ext_functionField {W : WeierstrassCurve F} {L : Type*} [Field L]
    {f g : W.toAffine.FunctionField →+* L}
    (hc : ∀ a : F, f (algebraMap F _ a) = g (algebraMap F _ a)) (hx : f (genX W) = g (genX W))
    (hy : f (genY W) = g (genY W)) : f = g := by
  let _ : Algebra F L := (f.comp (algebraMap F W.toAffine.FunctionField)).toAlgebra
  let f' : W.toAffine.FunctionField →ₐ[F] L := { f with commutes' := fun a => rfl }
  let g' : W.toAffine.FunctionField →ₐ[F] L := { g with commutes' := fun a => (hc a).symm }
  have e : f' = g' := algHom_ext_gen W hx hy
  ext z
  exact DFunLike.congr_fun e z

noncomputable def ffCongr {C D : WeierstrassCurve F'} (h : C = D) :
    C.toAffine.FunctionField ≃+* D.toAffine.FunctionField := by
  subst h; exact RingEquiv.refl _

theorem ffCongr_genX {C D : WeierstrassCurve F'} (h : C = D) : ffCongr h (genX C) = genX D := by
  subst h; rfl

theorem ffCongr_genY {C D : WeierstrassCurve F'} (h : C = D) : ffCongr h (genY C) = genY D := by
  subst h; rfl

theorem ffCongr_algebraMap {C D : WeierstrassCurve F'} (h : C = D) (a : F') :
    ffCongr h (algebraMap F' C.toAffine.FunctionField a) = algebraMap F' D.toAffine.FunctionField a := by
  subst h; rfl

end FF

section Map

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F')
variable {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

omit [E.IsElliptic] [E'.IsElliptic] in
theorem _root_.GroundTheory.Arith.Abelian.Isogeny.val_eq (φ : Isogeny E E') : φ.1 = Point.some φ.x φ.y φ.nonsingular := by
  rcases φ with ⟨Q, ⟨x, y, h, rfl, hx⟩, hr⟩
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.ext_xy {φ ψ : Isogeny E E'} (hx : φ.x = ψ.x) (hy : φ.y = ψ.y) : φ = ψ := by
  apply Isogeny.ext'
  rw [φ.val_eq, ψ.val_eq]
  simp only [Point.some.injEq]
  exact ⟨hx, hy⟩

noncomputable def _root_.GroundTheory.Arith.Abelian.Isogeny.map (φ : Isogeny E E') : Isogeny (E.map σ) (E'.map σ) :=
  letI := σ.toAlgebra
  letI := Classical.decEq F'
  isogBaseChange (F' := F') φ

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_x (φ : Isogeny E E') : (φ.map σ).x = ffMap σ E φ.x := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  show xOf _ (isogBaseChange (F' := F') φ).1 = _
  rw [isogBaseChange_val, φ.val_eq, Point.map_some]
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_y (φ : Isogeny E E') : (φ.map σ).y = ffMap σ E φ.y := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  show yOf _ (isogBaseChange (F' := F') φ).1 = _
  rw [isogBaseChange_val, φ.val_eq, Point.map_some]
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.comap_map (φ : Isogeny E E') (f : E'.toAffine.FunctionField) :
    (φ.map σ).comap (ffMap σ E' f) = ffMap σ E (φ.comap f) := by
  have e : (φ.map σ).comap.toRingHom.comp (ffMap σ E') = (ffMap σ E).comp φ.comap.toRingHom := by
    apply ringHom_ext_functionField
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ffMap_algebraMap,
        AlgHom.commutes]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ffMap_genX,
        Isogeny.comap_genX, Isogeny.map_x]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ffMap_genY,
        Isogeny.comap_genY, Isogeny.map_y]
  exact DFunLike.congr_fun e f

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.comp_alt (ψ : Isogeny E' E'') (φ : Isogeny E E') : (ψ.comp φ).x = φ.comap ψ.x := by
  rw [Isogeny.x, Isogeny.comp_val, ψ.val_eq, Point.map_some]
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.comp_y (ψ : Isogeny E' E'') (φ : Isogeny E E') : (ψ.comp φ).y = φ.comap ψ.y := by
  rw [Isogeny.y, Isogeny.comp_val, ψ.val_eq, Point.map_some]
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_comp (ψ : Isogeny E' E'') (φ : Isogeny E E') :
    (ψ.comp φ).map σ = (ψ.map σ).comp (φ.map σ) := by
  apply Isogeny.ext_xy
  · rw [Isogeny.map_x, Isogeny.comp_alt, Isogeny.comp_alt, Isogeny.map_x, Isogeny.comap_map]
  · rw [Isogeny.map_y, Isogeny.comp_y, Isogeny.comp_y, Isogeny.map_y, Isogeny.comap_map]

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.map_mulIsogeny (n : ℤ) (hn : n ≠ 0) :
    (mulIsogeny E n hn).map σ = mulIsogeny (E.map σ) n hn := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  apply Subtype.ext
  show Point.map (W' := E) (bcEmb (F' := F') E) (n • genericPoint E) =
    n • genericPoint (E.baseChange F')
  rw [map_zsmul, map_bcEmb_genericPoint]
  rfl

end Map

section Congr

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F')
variable {C D C' D' C'' D'' : WeierstrassCurve F'} [C.IsElliptic] [D.IsElliptic] [C'.IsElliptic]
  [D'.IsElliptic] [C''.IsElliptic] [D''.IsElliptic]

noncomputable def _root_.GroundTheory.Arith.Abelian.Isogeny.congr (hC : C = D) (hC' : C' = D')
    (φ : Isogeny C C') : Isogeny D D' := by
  subst hC hC'; exact φ

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.congr_alt (hC : C = D) (hC' : C' = D') (φ : Isogeny C C') :
    (φ.congr hC hC').x = ffCongr hC φ.x := by
  subst hC hC'; rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.congr_y (hC : C = D) (hC' : C' = D') (φ : Isogeny C C') :
    (φ.congr hC hC').y = ffCongr hC φ.y := by
  subst hC hC'; rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.congr_rfl (φ : Isogeny C C') : φ.congr rfl rfl = φ :=
  rfl

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.degree_congr (hC : C = D) (hC' : C' = D')
    (φ : Isogeny C C') : (φ.congr hC hC').degree = φ.degree := by
  subst hC hC'; rfl

variable {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

noncomputable def _root_.GroundTheory.Arith.Abelian.Isogeny.mapOf (hE : E.map σ = D) (hE' : E'.map σ = D')
    (φ : Isogeny E E') : Isogeny D D' :=
  (φ.map σ).congr hE hE'

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.mapOf_alt (hE : E.map σ = D) (hE' : E'.map σ = D')
    (φ : Isogeny E E') : (φ.mapOf σ hE hE').x = ffCongr hE (ffMap σ E φ.x) := by
  rw [Isogeny.mapOf, Isogeny.congr_alt, Isogeny.map_x]

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.mapOf_y (hE : E.map σ = D) (hE' : E'.map σ = D')
    (φ : Isogeny E E') : (φ.mapOf σ hE hE').y = ffCongr hE (ffMap σ E φ.y) := by
  rw [Isogeny.mapOf, Isogeny.congr_y, Isogeny.map_y]

end Congr

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.RespectsAddGeneric
section
namespace GroundTheory.Global

noncomputable section

open Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian IntermediateField

universe u

variable {F : Type u} [Field F]

theorem exists_algebraMap_eq_of_isAlgebraic_ff (E : WeierstrassCurve F) [E.IsElliptic]
    {u : E.toAffine.FunctionField} (hu : IsAlgebraic F u) :
    ∃ a : F, algebraMap F E.toAffine.FunctionField a = u := by
  classical
  have hu' : IsAlgebraic (AlgebraicClosure F) (bcEmb (F' := AlgebraicClosure F) E u) :=
    (hu.algHom (bcEmb (F' := AlgebraicClosure F) E)).tower_top (AlgebraicClosure F)
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_isAlgebraic (E.baseChange (AlgebraicClosure F)) hu'
  exact exists_algebraMap_eq_of_bcEmb E hc.symm

variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem isGenPt_of_respectsAdd
    {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point} (hQ : RespectsAdd E E' Q)
    (h0 : Q ≠ 0) : IsGenPt E' Q := by
  classical
  rcases Q with _ | ⟨x, y, h⟩
  · exact absurd rfl h0
  · by_contra hx
    have hx' : IsAlgebraic F x := not_not.mp hx
    obtain ⟨a, rfl⟩ := exists_algebraMap_eq_of_isAlgebraic_ff E hx'
    have hy' : IsAlgebraic F y := by
      have := isIntegral_y E' F h.1 (mem_algebraicClosure_iff.2 (isAlgebraic_algebraMap a))
      exact mem_algebraicClosure_iff.1 this
    obtain ⟨b, rfl⟩ := exists_algebraMap_eq_of_isAlgebraic_ff E hy'
    have hc : (E'.baseChange F).toAffine.Nonsingular a b :=
      (E'.toAffine.baseChange_nonsingular (f := Algebra.ofId F E.toAffine.FunctionField)
        (algebraMap F _).injective a b).mp h
    have hQc : (Point.some _ _ h : (E'.baseChange E.toAffine.FunctionField).toAffine.Point) =
        Point.map (Algebra.ofId F E.toAffine.FunctionField) (Point.some _ _ hc) := by
      rw [Point.map_some, Point.some.injEq]; exact ⟨rfl, rfl⟩
    have key := (respectsAdd_iff _).mp hQ (univField E) (univPt₁ E) (univPt₂ E)
      (isGenPt_univPt₁ E) (isGenPt_univPt₂ E) (isGenPt_univPt₁₂ E)
    have hconst : ∀ (σ : E.toAffine.FunctionField →ₐ[F] univField E),
        Point.map σ (Point.some _ _ h) =
          Point.map (Algebra.ofId F (univField E)) (Point.some _ _ hc) := fun σ => by
      rw [hQc, Point.map_map]
      have e : σ.comp (Algebra.ofId F E.toAffine.FunctionField) = Algebra.ofId F (univField E) :=
        AlgHom.ext fun z => by
          rw [AlgHom.comp_apply, Algebra.ofId_apply, Algebra.ofId_apply, σ.commutes]
      rw [e]
    rw [hconst, hconst, hconst, left_eq_add] at key
    have := Point.map_injective (W' := E') (Algebra.ofId F (univField E))
      (key.trans (map_zero _).symm)
    exact Point.some_ne_zero hc this

theorem isIsogeny_of_respectsAdd
    {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point} (hQ : RespectsAdd E E' Q)
    (h0 : Q ≠ 0) : IsIsogeny E E' Q :=
  (isIsogeny_iff Q).mpr ⟨isGenPt_of_respectsAdd hQ h0, hQ⟩

end

end GroundTheory.Global
end

