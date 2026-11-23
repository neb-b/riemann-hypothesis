module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Statements.GeometryStatements.NearRecordOfValue
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar.Top

def RootFlatOnHodge : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
    (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (bad : Finset ℕ) (M : RootModel (CMType H) (D.p + D.q))
    (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
    (o : RootOrigin Y bad M Fx),
    IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → (∀ r : ℕ, r ∈ bad ↔ r.Prime ∧ (r : ℤ) ∣ 2 * discr E * l.M') →
      o.𝔐.OmVB → ∀ τ, ∃ R : RootFlat M τ, NearRecord (D.p + D.q) bad (hostRd E) (hostLval H) R.ht

namespace OnHodge

section Tower

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {Xo : ∀ l : Level H, Moduli D l} {l : Level H} {c : Coeff l} {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)}

theorem hostRd_eq (E : Type) [Field E] [NumberField E] : hostRd E = rootDiscr E := by
  simp [hostRd, rootDiscr_def]

theorem S_two {T : RootTower (CMType H) (D.p + D.q)} (o : TowerOrigin Y T) : o.S 2 = T.bad := by
  ext r
  rw [o.S_iff, RootTower.InS]
  refine ⟨fun h => h.2.elim (fun h2 => ?_) id, fun h => ⟨((o.bad_iff r).1 h).1, Or.inr h⟩⟩
  obtain rfl : r = 2 := le_antisymm h2 h.1.two_le
  exact T.two_mem

theorem tower (h : RootFlatOnHodge) [IsAbelianGalois ℚ E] (hY : IsGlobal Xo l c Y)
    {T : RootTower (CMType H) (D.p + D.q)} (hT : IsTowerOf Y T) (a : T.Comp) (τ : CMType H) :
    ∃ R : RootFlat (T.M 2 a) τ, NearRecord (D.p + D.q) T.bad (hostRd E) (hostLval H) R.ht := by
  obtain ⟨o, ho⟩ := hT
  have h1 := T.j_pos
  have h2 := T.j_lt
  have h3 := o.j_eq
  rw [← S_two o]
  exact h E H D Xo l c Y (o.S 2) (T.M 2 a) (o.Sys a) (o.Fx a) (o.Or 2 a) hY (by omega) (by omega)
    (fun r => by rw [S_two o]; exact o.bad_iff r) (ho 2 a) τ

end Tower

theorem const_le : Real.eulerMascheroniConstant + Real.log (2 * Real.pi) + 2 * Real.log 2 ≤ 2 * Real.log 7 := by
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  have he : Real.exp (2 / 3) ≤ 1.9496 := by
    have h3 : Real.exp (2 / 3) ^ 3 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have h1 := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    refine le_of_pow_le_pow_left₀ three_ne_zero (by norm_num) ?_
    rw [h3]; nlinarith
  have h : Real.log (Real.exp (2 / 3) * (2 * Real.pi) * 2 ^ 2) ≤ Real.log (7 ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith [Real.exp_pos (2 / 3)])
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_exp,
    Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

end OnHodge

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Heights₂.Heights.LowerBoundFree

section Free

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W} (Hd : HodgeData D)

def corrW (U : ((Σ k, J k) → ℂ) → ℝ) (z : (Σ k, J k) → ℂ) : ℝ := phMu Hd z + U z / 2

variable {Hd} {M : XModel D} {w : ((Σ k, J k) → ℂ) → ℝ} (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w)

def PosU : Prop :=
  ∀ B p q : ℕ, 4 * D.f + 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    IsSemipositiveH (mCoordIdeal D.y) (MUc Hd S' B p q t') ∧ NefOnFibres (mCoordIdeal D.y) (MUc Hd S' B p q t').a ∧
      AmpleOnGenericFibre (mCoordIdeal D.y) (MUc Hd S' B p q t')

def ConjU : Prop :=
  ∀ B p q : ℕ, 4 * D.f + 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    IsConjInvariantH (MUc Hd S' B p q t')

def HtU (Ch rd Lval : ℝ) : Prop :=
  ∀ B p q : ℕ, 4 * D.f * D.N ^ 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ∀ P : Ideal (MRing J), IsArithVar P 1 → mCoordIdeal D.y ≤ P →
      -(Ch * D.f * D.j' * abelian₂ B rd Lval) - (p : ℝ) / q * D.KA ≤ htMUc Hd S' B p q t' P

variable (Hd)

def meanOf (U : ((Σ k, J k) → ℂ) → ℝ) : ℝ :=
  ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu Hd) U / degMu Hd

def MeanU (U : ((Σ k, J k) → ℂ) → ℝ) (Cu rd Lval : ℝ) : Prop :=
  1 ≤ D.j' → 3 * D.j' + 1 ≤ D.N → ∀ B : ℕ, 4 * D.f * D.N ^ 2 ≤ B → meanOf Hd U ≤ Cu * D.f * D.j' * abelian₂ B rd Lval

def twW (B : ℕ) (x : ((Σ k, J k) → ℂ) → ℝ) (z : (Σ k, J k) → ℂ) : ℝ := x z + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z)

end Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {II : IntersectionSystem} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
  [Algebra ℚ Ω] {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]

def admitted (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} (Or : CptOrigin Y S₀ Dc Hd)
    (B₁ : ℕ) : Prop :=
  Top.IsGlobal Xo l c Y ∧ Or.Good ∧ (∀ r : ℕ, r ∈ S₀ ↔ r.Prime ∧ (r : ℤ) ∣ 2 * discr E * l.M') ∧
    S₀.card ≤ 4 * Dc.f * Dc.N ^ 2 ∧ 4 * Dc.f + 2 ≤ B₁ ∧ (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ S₀) ∧ Dc.j' ≤ Dc.j

def NineGeoU (Ch Cu : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
    (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
    (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ)
    (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)),
    IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → S'.IsTied →
      PosU S' ∧ HtU S' Ch (hostRd E) (hostLval H) ∧ MeanU Hd U Cu (hostRd E) (hostLval H)

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

