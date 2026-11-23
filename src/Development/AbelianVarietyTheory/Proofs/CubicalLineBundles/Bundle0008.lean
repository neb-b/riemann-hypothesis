module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GeomSurj


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.GeomSurj.exists_lift_of_surjective {Ω : Type} [Field Ω] [IsAlgClosed Ω] {P A : Scheme.{0}}
    (ψ : P ⟶ A) [LocallyOfFiniteType ψ] [Surjective ψ] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω ⟶ A) :
    ∃ p : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω ⟶ P, x = p ≫ ψ := by
  have hΩ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω = Spec (CommRingCat.of Ω) := rfl
  haveI : JacobsonSpace (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω) := by rw [hΩ]; infer_instance
  haveI : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω) := by rw [hΩ]; infer_instance
  haveI : JacobsonSpace (pullback ψ x :) := LocallyOfFiniteType.jacobsonSpace (pullback.snd ψ x)
  obtain ⟨q₀, -⟩ := (pullback.snd ψ x).surjective (Classical.arbitrary _)
  obtain ⟨q, hq⟩ : (closedPoints (pullback ψ x :)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hc := closure_closedPoints (X := (pullback ψ x :))
    rw [h, closure_empty] at hc
    exact (hc ▸ Set.mem_univ q₀ : q₀ ∈ (∅ : Set _))
  haveI : LocallyOfFiniteType ((pullback ψ x).fromSpecResidueField q) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hq
  let g : Spec ((pullback ψ x).residueField q) ⟶ Spec (CommRingCat.of Ω) :=
    (pullback ψ x).fromSpecResidueField q ≫ pullback.snd ψ x
  have hg : LocallyOfFiniteType (Spec.map (Spec.preimage g)) := by
    rw [Spec.map_preimage]; dsimp only [g]; infer_instance
  have hft := HasRingHomProperty.Spec_iff.mp hg
  set f := Spec.preimage g with hf
  letI : Algebra Ω ((pullback ψ x).residueField q) := f.hom.toAlgebra
  haveI : Algebra.FiniteType Ω ((pullback ψ x).residueField q) := hft
  haveI : Module.Finite Ω ((pullback ψ x).residueField q) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  let φ : (pullback ψ x).residueField q →ₐ[Ω] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have key : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g = 𝟙 _ := by
    rw [← Spec.map_preimage g, ← hf, ← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of Ω)
    ext a
    exact φ.commutes a
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pullback ψ x).fromSpecResidueField q ≫
    pullback.fst ψ x, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition,
    ← Category.assoc (Scheme.fromSpecResidueField _ _), ← Category.assoc]
  change x = (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g) ≫ x
  rw [key, Category.id_comp]

end GlobalTheory.GeomSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PureTypeVectorSpansQuadraticLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace PureTypeVector

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.PureTypeVector.hermForm_smul_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : ℂ) (u v : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (z • u) (w • v) = z * starRingEnd ℂ w * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm u v := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul, Complex.star_def]
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.PureTypeVector.hermForm_self_im {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (v : Fin g → ℂ) :
    (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm v v).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  have key : ∀ u : Fin g → ℂ, star (star u ⬝ᵥ Hm.mulVec u) = star u ⬝ᵥ Hm.mulVec u := by
    intro u
    rw [← Matrix.star_dotProduct (Hm.mulVec u) u, Matrix.star_mulVec, hH.eq, ← Matrix.dotProduct_mulVec]
  have := key (star v)
  rw [star_star] at this
  exact this

end PureTypeVector


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.pureType_vector_spans_quadratic_lattice :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty Pe → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) →
  (∀ x y, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe x) (Pe y)).im = D.EF x y) →
  ∀ (ρ : ℂ) (a : D.La), ρ ^ 2 = -(H.d : ℂ) → (∀ i, ty i (H.rt : E) ≠ ρ → Pe a i = 0) →
  (∀ m n : ℤ, ((m : ℂ) + n * ((1 + Complex.I * Real.sqrt H.d) / 2)) • Pe a ∈ Pe.range) ∧
  ∀ z w : ℂ, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (z • Pe a) (w • Pe a) = ((D.EF (H.w0 • a) a).natAbs : ℂ) * (2 * z * starRingEnd ℂ w / Real.sqrt H.d) := by
  intro E _ _ _ H D g ty Pe Hm hP hH hpos hE ρ a hρ hsupp
  have hw0 : ∀ i, Pe (H.w0 • a) i = (1 + ρ) / 2 * Pe a i := by
    intro i
    rw [hP.1 H.w0 a i]
    by_cases hi : ty i (H.rt : E) = ρ
    · have h2 : (2 : ℂ) * ty i (H.w0 : E) = 1 + ty i (H.rt : E) := by
        have := congrArg (fun x : 𝓞 E => ty i (x : E)) H.two_weight_eq_one_add_root
        simp only [map_mul, map_add (f := _), map_one, RingOfIntegers.coe_eq_algebraMap, map_ofNat] at this
        linear_combination this
      rw [hi] at h2
      have h3 : ty i (H.w0 : E) = (1 + ρ) / 2 := by linear_combination h2 / 2
      rw [h3]
    · rw [hsupp i hi]
      simp
  have hw0' : Pe (H.w0 • a) = ((1 + ρ) / 2) • Pe a := funext fun i => by simp [hw0 i]
  have hsqd : ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 = H.d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hsq : ρ = Complex.I * Real.sqrt H.d ∨ ρ = -(Complex.I * Real.sqrt H.d) := by
    have hprod : (ρ - Complex.I * Real.sqrt H.d) * (ρ + Complex.I * Real.sqrt H.d) = 0 := by
      linear_combination hρ + hsqd - ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 * Complex.I_sq
    rcases mul_eq_zero.1 hprod with h | h
    · left
      linear_combination h
    · right
      linear_combination h
  constructor
  · intro m n
    rcases hsq with h | h
    · refine ⟨m • a + n • (H.w0 • a), ?_⟩
      rw [map_add (f := _), map_zsmul, map_zsmul]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply]
      simp only [smul_eq_mul, zsmul_eq_mul, hw0 i, h]
      ring
    · refine ⟨(m + n) • a - n • (H.w0 • a), ?_⟩
      rw [map_sub, map_zsmul, map_zsmul]
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply]
      simp only [smul_eq_mul, zsmul_eq_mul, hw0 i, h]
      push_cast
      ring
  · intro z w
    rw [_root_.GlobalTheory.PureTypeVector.hermForm_smul_smul]
    have him : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).im = 0 := _root_.GlobalTheory.PureTypeVector.hermForm_self_im hH _
    have hre : 0 ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re := by
      by_cases h0 : Pe a = 0
      · simp [h0, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm]
      · exact (hpos _ h0).le
    have hc : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (((1 + ρ) / 2) • Pe a) (Pe a) = (1 + ρ) / 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a) := by
      simpa using _root_.GlobalTheory.PureTypeVector.hermForm_smul_smul Hm ((1 + ρ) / 2) 1 (Pe a) (Pe a)
    have hEF := hE (H.w0 • a) a
    rw [hw0', hc] at hEF
    have hh : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a) = ((_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re : ℂ) :=
      Complex.ext rfl (by simp [him])
    have hs : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (Nat.cast_pos.2 H.d_prime.pos)
    have habs : |((D.EF (H.w0 • a) a : ℤ) : ℝ)| = (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re * Real.sqrt H.d / 2 := by
      rw [hh] at hEF
      have hnn : 0 ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re * Real.sqrt H.d / 2 :=
        div_nonneg (mul_nonneg hre hs.le) zero_le_two
      rcases hsq with h | h
      · rw [h] at hEF
        simp [Complex.mul_im, Complex.div_re, Complex.div_im] at hEF
        have he : ((D.EF (H.w0 • a) a : ℤ) : ℝ) = (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re * Real.sqrt H.d / 2 := by
          linarith
        rw [he, abs_of_nonneg hnn]
      · rw [h] at hEF
        simp [Complex.mul_im, Complex.div_re, Complex.div_im] at hEF
        have he : ((D.EF (H.w0 • a) a : ℤ) : ℝ) = -((_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re * Real.sqrt H.d / 2) := by
          linarith
        rw [he, abs_neg, abs_of_nonneg hnn]
    have hcast : (((D.EF (H.w0 • a) a).natAbs : ℕ) : ℂ) = ((|((D.EF (H.w0 • a) a : ℤ) : ℝ)| : ℝ) : ℂ) := by
      rw [Nat.cast_natAbs, ← Int.cast_abs, Complex.ofReal_intCast]
    have hs' : ((Real.sqrt H.d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
    rw [hcast, habs]
    conv_lhs => rw [hh]
    push_cast
    field_simp

end GlobalTheory
end

