module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.DegeneratingToriPeriodMapEqBaseOfYEqZero

@[expose] public section

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace AnArc

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

def perFactor (w : ℂ) (la : A.La) (v : A.V) : ℂ :=
  A.ah la.l (v.2 + A.ct la.y) * (A.psi la.y * eTwoPi (v.1 la.y) * eTwoPi (w * A.q la.y))⁻¹


open AlgebraicGeometry CategoryTheory Limits in
variable {O : Type} [CommRing O] [StarRing O] (A : _root_.GlobalTheory.AnArc O) in
open _root_.GlobalTheory.AnArc.La in
theorem _root_.GlobalTheory.AnArc.term_add_period {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (w : ℂ)
    (la : A.La) (μ : A.X) (v : A.V) :
    A.term j α th μ (v + A.Pw w la) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α μ) =
      A.perFactor w la v ^ j *
        (A.term j α th (μ + la.y) v *
          _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α (μ + la.y))) := by
  set y := la.y with hy
  set n := la.n with hn
  set l := la.l with hl
  set L : A.La := _root_.GlobalTheory.AnArc.La.mk 0 0 l
  set M : A.La := _root_.GlobalTheory.AnArc.La.mk 0 n 0
  set Y : A.La := _root_.GlobalTheory.AnArc.La.mk y 0 0
  have hPw : A.Pw w la = A.Pw w Y + A.P0 M + A.P0 L := by
    conv_lhs => rw [eq_add_parts la]
    rw [map_add (f := _), map_add (f := _), _root_.GlobalTheory.AnArc.degeneratingTori_periodMap_eq_base_of_y_eq_zero _ _ (mk_y _ _ _),
      _root_.GlobalTheory.AnArc.degeneratingTori_periodMap_eq_base_of_y_eq_zero _ _ (mk_y _ _ _)]
  set v' : A.V := v + A.P0 L + A.P0 M
  have hv : v + A.Pw w la = v' + A.Pw w Y := by
    rw [hPw]
    simp only [v']
    abel
  have key := A.term_add_Pw_y j α th w μ y v'
  rw [← hv] at key
  have hterm : A.term j α th (μ + y) v' =
      (A.chi l * Complex.exp (Real.pi * A.H v.2 l + Real.pi / 2 * A.H l l)) ^ j *
        A.term j α th (μ + y) v := by
    rw [_root_.GlobalTheory.AnArc.term_add_P0_n,
      _root_.GlobalTheory.AnArc.term_add_P0_l A h]
  have hv1 : v'.1 y = v.1 y + (n y : ℂ) + -(A.H (A.ct y) l / (2 * Complex.I)) := by
    simp [v', L, M, Prod.fst_add, _root_.GlobalTheory.AnArc.degeneratingTori_basePeriodMap_fst_apply, mk_y, mk_n, mk_l]
    ring
  set X : ℂ := A.psi y * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (v.1 y) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.q y)
  set X' : ℂ := A.psi y * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (v'.1 y) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.q y)
  have hX' : X' = X * Complex.exp (-(Real.pi * A.H (A.ct y) l)) := by
    simp only [X', X, hv1, _root_.GlobalTheory.AnArc.e_add, _root_.GlobalTheory.AnArc.e_intCast, _root_.GlobalTheory.AnArc.e_neg_div]
    ring
  have hX'0 : X' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Units.ne_zero _) (_root_.GlobalTheory.AnArc.e_ne_zero _)) (_root_.GlobalTheory.AnArc.e_ne_zero _)
  have hfac : A.perFactor w la v =
      A.chi l * Complex.exp (Real.pi * A.H v.2 l + Real.pi / 2 * A.H l l) * X'⁻¹ := by
    rw [_root_.GlobalTheory.AnArc.perFactor, ← hy, ← hl, _root_.GlobalTheory.AnArc.ah_add, hX']
    simp only [mul_inv, ← Complex.exp_neg, neg_neg, _root_.GlobalTheory.AnArc.ah, X]
    ring
  calc A.term j α th μ (v + A.Pw w la) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α μ)
      = (X' ^ j)⁻¹ *
          (X' ^ j * (A.term j α th μ (v + A.Pw w la) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α μ))) := by
        rw [inv_mul_cancel_left₀ (pow_ne_zero _ hX'0)]
    _ = _ := by
        rw [key, hterm, hfac]
        ring


open AlgebraicGeometry CategoryTheory Limits in
variable {O : Type} [CommRing O] [StarRing O] (A : _root_.GlobalTheory.AnArc O) in
theorem _root_.GlobalTheory.AnArc.Sum_add_period {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (w : ℂ)
    (la : A.La) (v : A.V) :
    A.Sum j α th w (v + A.Pw w la) = A.perFactor w la v ^ j * A.Sum j α th w v := by
  simp only [_root_.GlobalTheory.AnArc.Sum, A.term_add_period h w la]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addRight la.y).tsum_eq
    fun μ => A.term j α th μ v * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α μ)

def FSumShift (k : ℕ) [NeZero k] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (la : A.La) (z : A.V) : LaurentSeries ℂ :=
  HahnSeries.ofSuppBddBelow
    (fun n => ∑ μ ∈ A.level k (α + la.y) (n - A.be la.y α / k), A.term k α th μ (z + (k : ℂ)⁻¹ • A.P0 la))
    ⟨-A.be (α + la.y) (α + la.y) + A.be la.y α / k, fun n hn => by
      by_contra h
      exact hn (by simp only [A.level_eq_empty (j := k) (α := α + la.y) (n := n - A.be la.y α / k) (by omega),
        Finset.sum_empty])⟩

theorem coeff_FSumShift (k : ℕ) [NeZero k] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (la : A.La) (z : A.V) (n : ℤ) :
    (A.FSumShift k α th la z).coeff n =
      ∑ μ ∈ A.level k (α + la.y) (n - A.be la.y α / k), A.term k α th μ (z + (k : ℂ)⁻¹ • A.P0 la) := rfl

end AnArc

section Along

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

def IsRigFrame (L : RigLB G) (y : Sp ℂ ⟶ S) (e : V → (Sp ℂ ⟶ G.left)) (fr : L.L.ι → V → ℂ) : Prop :=
  (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.L.U j}) ∧ (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.L.U j → fr j z ≠ 0) ∧
    (∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.L.U j ⊓ L.L.U j') →
      fr j z = valAt' (e z) (L.L.U j ⊓ L.L.U j') (L.L.g j j').val * fr j' z) ∧
    ∀ j, ⊤ ≤ e 0 ⁻¹ᵁ L.L.U j → fr j 0 = valAt' y ((L.L.pull (eSec G)).U (fun _ => j)) (L.rig.s (fun _ => j)).val

variable {V' : Type} [NormedAddCommGroup V'] [NormedSpace ℂ V']


end Along

end GlobalTheory
