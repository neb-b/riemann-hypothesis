module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.KernelCard
public import GroundTheory.ProfiniteCohomology.GaloisModules.Discrete
public import GroundTheory.ProfiniteCohomology.GaloisModules.FixedField

@[expose] public section

namespace GroundTheory.Arith.Abelian

open GroundTheory.ProfCoh IntermediateField AddSubgroup WeierstrassCurve

universe w u

section Action

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [DecidableEq L] (W : WeierstrassCurve K)

noncomputable def galPointsHom : Gal(L/K) →* AddMonoid.End (W.baseChange L).toAffine.Point where
  toFun σ := Affine.Point.map (W' := W.toAffine) (σ : L →ₐ[K] L)
  map_one' := by
    refine AddMonoidHom.ext fun P => ?_
    cases P <;> rfl
  map_mul' σ τ := by
    refine AddMonoidHom.ext fun P => ?_
    cases P <;> rfl

theorem galPointsHom_some (σ : Gal(L/K)) {x y : L}
    (h : (W.baseChange L).toAffine.Nonsingular x y) :
    ∃ h' : (W.baseChange L).toAffine.Nonsingular (σ x) (σ y),
      galPointsHom K L W σ (.some x y h) = .some (σ x) (σ y) h' :=
  ⟨_, rfl⟩

theorem galPointsHom_some_eq_self {σ : Gal(L/K)} {x y : L}
    (h : (W.baseChange L).toAffine.Nonsingular x y) (hx : σ x = x) (hy : σ y = y) :
    galPointsHom K L W σ (.some x y h) = .some x y h := by
  obtain ⟨h', e⟩ := galPointsHom_some K L W σ h
  rw [e]
  simp only [Affine.Point.some.injEq]
  exact ⟨hx, hy⟩

end Action

section Discrete

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [DecidableEq L] (W : WeierstrassCurve K)

variable [Algebra.IsIntegral K L]

end Discrete

section SepClosed

instance isElliptic_baseChange {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (W : WeierstrassCurve R) [W.IsElliptic] : (W.baseChange A).IsElliptic :=
  inferInstanceAs (W.map (algebraMap R A)).IsElliptic

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [DecidableEq L] [IsSepClosed L]
  (W : WeierstrassCurve K) [W.IsElliptic]

end SepClosed

end GroundTheory.Arith.Abelian
