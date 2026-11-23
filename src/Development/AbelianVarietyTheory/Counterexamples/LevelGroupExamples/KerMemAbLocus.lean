module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084

@[expose] public section

noncomputable section

namespace GlobalTheory.DatAtCheck

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

abbrev fC (A : DatAt Y P) : A.R →+* ↥C.S := (intO ↥C.S).subtype.comp A.f

theorem ker_mem_abLocus (A : DatAt Y P) (q : Sp ↥C.S) : spMap (fC A) q ∈ A.ι ⁻¹' abLocus Y.t.G := by
  have e : spMap (fC A) ≫ A.ι = (P.y ≫ Y.jQ) ≫ pullback.fst _ _ := by
    refine Eq.trans ?_ (P.ext.trans (Category.assoc _ _ _).symm)
    rw [← A.fac, ← Category.assoc]
    exact congrArg (· ≫ A.ι) (Spec.map_comp (CommRingCat.ofHom A.f) (CommRingCat.ofHom (intO ↥C.S).subtype))
  have h : (P.y ≫ Y.jQ) q ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]; exact ⟨P.y q, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  exact h

theorem isOpen_locus (A : DatAt Y P) : IsOpen (A.ι ⁻¹' abLocus Y.t.G) := by
  have hab : A.ι ⁻¹' abLocus Y.t.G = abLocus A.t.G :=
    Set.ext fun q => abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 q
  rw [hab]
  exact AbLocusOpen.isOpen_abLocus_local A.t.G A.t.semi

theorem coord_ne_zero (A : DatAt Y P) (χ : A.Ylat) (r : A.R) (hr : PsiCoord A.U.D.toPre χ r) : fC A r ≠ 0 := by
  let q : Sp ↥C.S := (⊥ : PrimeSpectrum ↥C.S)
  have h := PsiCoordLocal.not_mem_of_coord (isOpen_locus A) (ker_mem_abLocus A q) (A.unitOn χ) hr
  intro h0
  apply h
  change fC A r ∈ (⊥ : Ideal ↥C.S)
  exact h0

theorem norm_le (A : DatAt Y P) (a : A.R) : ‖fC A a‖ ≤ 1 := (A.f a).2

theorem vPsiAt_eq (A : DatAt Y P) (χ : A.Ylat) : (∃ r, PsiCoord A.U.D.toPre χ r) ∧
    ∀ r, PsiCoord A.U.D.toPre χ r → vPsiAt A.U.D.toPre (fC A) p χ = -Real.logb p ‖fC A r‖ := by
  obtain ⟨⟨r₀, h₀, -⟩, hu, -⟩ := PsiCoordLocal.main A.R A.U.D A.normal χ
  have hex : ∃ r, PsiCoord A.U.D.toPre χ r := ⟨r₀, h₀⟩
  refine ⟨hex, fun r hr => ?_⟩
  obtain ⟨u, hu⟩ := hu _ _ hr hex.choose_spec
  have h1 : ‖fC A u‖ * ‖fC A (↑u⁻¹ : A.R)‖ = 1 := by rw [← norm_mul, ← map_mul]; simp
  have h2 := norm_le A u
  have h3 := norm_le A (↑u⁻¹ : A.R)
  have h4 : ‖fC A u‖ = 1 := by nlinarith [norm_nonneg (fC A u), norm_nonneg (fC A (↑u⁻¹ : A.R))]
  simp only [vPsiAt, dif_pos hex]
  rw [hu, map_mul, norm_mul, h4, one_mul]

theorem betaAdd (Y : Model Xo c β) (p : ℕ) : BetaAdd Y p := fun _ _ A =>
  (BetaAdd.main A.R A.U.D _ _ p A.normal (norm_le A) (coord_ne_zero A)).1

theorem beta_balanced (A : DatAt Y P) (x : 𝓞 E) (a b : A.Ylat) : A.beta (x • a) b = A.beta a (H.bar x • b) :=
  PeriodBalance.betaAt_balanced E H A.R A.t A.U _ _ p A.normal (norm_le A) (coord_ne_zero A) x a b

theorem beta_self_pos (hp : 1 < p) (A : DatAt Y P) (a : A.Ylat) (ha : a ≠ 0) : 0 < A.beta a a := by
  have h := (BetaAdd.main A.R A.U.D _ _ p A.normal (norm_le A) (coord_ne_zero A)).2 a
  obtain ⟨⟨r, hr, -, hm, -⟩, -⟩ := PsiCoordLocal.main A.R A.U.D A.normal a
  have h1 : ‖fC A r‖ < 1 := A.f_loc r (hm ha)
  have h2 : 0 < ‖fC A r‖ := norm_pos_iff.2 (coord_ne_zero A a r hr)
  have h3 := Real.logb_neg (b := p) (by exact_mod_cast hp) h2 h1
  have h4 := (vPsiAt_eq A a).2 r hr
  change 0 < betaAt A.U.D.toPre (fC A) p a a
  rw [h, h4]; linarith

end GlobalTheory.DatAtCheck
