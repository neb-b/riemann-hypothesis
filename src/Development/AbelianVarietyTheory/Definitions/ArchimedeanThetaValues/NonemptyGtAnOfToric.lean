module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CoeffFSumDerivEqFderiv
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ExistsChartComplexPoint
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.DegeneratingToriPeriodMapEqBaseOfYEqZero
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian

@[expose] public section

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

instance neZero_level_A : NeZero l.A := ⟨l.A_pos.ne'⟩

instance neZero_level_M : NeZero l.M := ⟨by have := l.three_le; omega⟩

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

structure GtAn₀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {b : O →+* ℂ}
    (a : ArcIn D l β ℂ b) extends @GtDict (𝓞 E) _ H.starRing _ _ a.D₀ a.mod a.oa where

  be_eq : letI := H.starRing; ∀ x y, a.be (eX x) (eX y) = A.be x y

structure GtAn [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {b : O →+* ℂ}
    (a : ArcIn D l β ℂ b) extends GtAn₀ a where

  sec : letI := H.starRing; toGtAn₀.toGtDict.SecFn



namespace GtAn₀

variable {b : O →+* ℂ} {a : ArcIn D l β ℂ b} (Λ : GtAn₀ a)

def y : letI := H.starRing; Λ.A.La →ₗ[𝓞 E] a.D₀.X :=
  letI := H.starRing; Λ.eX.toLinearMap ∘ₗ Λ.A.yLin

@[simp] theorem y_apply : letI := H.starRing; ∀ la : Λ.A.La, Λ.y la = Λ.eX la.y := by
  letI := H.starRing
  intro la
  show Λ.eX (Λ.A.yLin la) = Λ.eX la.y
  rw [AnArc.yLin_apply]

theorem y_onto : Function.Surjective Λ.y := by
  letI := H.starRing
  intro x
  obtain ⟨la, hla⟩ := Λ.A.yLin_surjective (Λ.eX.symm x)
  refine ⟨la, ?_⟩
  rw [y_apply, ← AnArc.yLin_apply, hla, LinearEquiv.apply_symm_apply]

theorem ker_y : letI := H.starRing; ∀ v, (Λ.ex₀ v).IsZero ↔ ∃ la, Λ.y la = 0 ∧ v = Λ.A.P0 la := by
  letI := H.starRing
  intro v
  rw [Λ.ker v]
  simp only [y_apply, LinearEquiv.map_eq_zero_iff]

theorem shift_be : letI := H.starRing; ∀ (w : ℂ) (la : Λ.A.La),
    IsTorusPt (Λ.ex₀ (w • Λ.A.N la)) fun x => eTwoPi (w * a.be (Λ.y la) x) := by
  letI := H.starRing
  intro w la
  have h := Λ.toGtDict.shift w la
  convert h using 3 with x
  rw [y_apply, ← Λ.be_eq, LinearEquiv.apply_symm_apply]

def Lifts {k : ℕ} [NeZero k] (p : Out.QkPt a.D₀ (FractionRing ℂ) k) : letI := H.starRing; Λ.A.La → Prop :=
  letI := H.starRing
  fun la => ∀ q', QkExt (algebraMap _ ℂ) p q' → Out.QkPt.Equiv a.D₀ ℂ (Λ.toGtDict.qk k la) q'

theorem exists_lifts {k : ℕ} [NeZero k] (p : Out.QkPt a.D₀ (FractionRing ℂ) k) : letI := H.starRing
    ∃ la : Λ.A.La, ∀ la', Λ.Lifts p la' ↔ ∃ m, la' = la + k • m := by
  letI := H.starRing
  have hf : (algebraMap (FractionRing ℂ) ℂ).comp (algebraMap (FractionRing ℂ) (FractionRing ℂ)) =
      algebraMap (FractionRing ℂ) ℂ := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  obtain ⟨q, hq, huniq⟩ := TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing ℂ) ℂ) hf p
  obtain ⟨la, rfl⟩ := Λ.toGtDict.qk_surjective k q
  refine ⟨la, fun la' => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨m, hm⟩ := (Λ.toGtDict.qk_equiv_iff k la' la).1 (h _ hq)
    exact ⟨-m, by rw [hm, smul_neg, add_neg_cancel_right]⟩
  · rintro ⟨m, rfl⟩ q' hq'
    rw [huniq q' hq']
    exact TorusExt.equiv_symm a.bimult (Λ.toGtDict.qk_equiv_add k la m)

end GtAn₀

abbrev GtAn.fn {b : O →+* ℂ} {a : ArcIn D l β ℂ b} (Λ : GtAn a) (j : ℕ) [NeZero j] : letI := H.starRing
    ∀ α : Λ.A.X, a.D₀.SecB j (Λ.eX α) ≃ Λ.A.Theta j α :=
  letI := H.starRing; Λ.sec.fn j

end GlobalTheory
