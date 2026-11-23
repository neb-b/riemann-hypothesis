module

public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.DegreeRatioFormulaStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.HermitianCurvature.StatementSz
public import Formalism.HermitianCurvature.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0006
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0007
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLift
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0002

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.S

open Formalism.BasicNotions Formalism.MainNotions MeasureTheory

namespace AutInst

variable (I : AutInst)


open Classical in
def IsLevelCharIdem (μf : Measure I.Gf) (g₀ : ℕ) (e : I.Gf → ℂ) : Prop :=
  ∃ (K'' : Subgroup I.Gf) (χ : I.Gf → ℂ), IsOpen (K'' : Set I.Gf) ∧ IsCompact (K'' : Set I.Gf) ∧
    (K'' : Set I.Gf) ⊆ I.Kset ∧ (∀ k ∈ K'', I.UnipMod g₀ k) ∧
    (∀ k ∈ K'', ∀ k' ∈ K'', χ (k * k') = χ k * χ k') ∧ (∀ k ∈ K'', ‖χ k‖ = 1) ∧
    ∀ x, e x = if x ∈ K'' then (χ x)⁻¹ / ((μf (K'' : Set I.Gf)).toReal : ℂ) else 0

end AutInst

namespace CountE

open Formalism.MainNotions.PlaceDegreeData NumberField

variable (P : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop)

def CountIdempotentsClass (_D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ)
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ),
    HidaSetting I n₀ A b lam μf g g₀ e → P I μf g₀ e → CountData I lam σ w σs tens μf fund R e Re →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) →
    C * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ h →
    Real.log (I.f : ℝ) ≤ Real.sqrt (I.n : ℝ) →
    Real.log (Real.log b) ≤ cb * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) →
    |(I.Dcount σs μf fund R Re : ℝ) - I.Dstar (fdegAll I σ w) μf fund e| ≤
      Real.exp (-c * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) * I.Dstar (fdegAll I σ w) μf fund e

def RowsTieP (D : Formalism.BasicNotions.D7) (X : RowsAut) : Prop := RowsTie D X ∧ P X.I X.μf X.g₀ X.e

def CountRowsClass (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  ∀ (X : RowsAut) (b h : ℝ), RowsTieP P D X → HidaSetting X.I n₀ A b X.lam X.μf X.g X.g₀ X.e →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (X.I.ε v) (X.lam v) h) →
    C * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * Real.log (b * D.host.rdE) ≤ h →
    Real.log (D.R.f : ℝ) ≤ Real.sqrt (D.R.r : ℝ) →
    Real.log (Real.log b) ≤ cb * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ) →
    |(D.what₂.Dall : ℝ) - D.what₂.Dstar| ≤
      Real.exp (-(c * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ))) * D.what₂.Dstar

def CountAllPointsClass {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  0 < c ∧ 0 < cb ∧ ∀ x (i : Fm.Ix x), CountIdempotentsClass P (Fm.D x i) n₀ A C c cb

def CountRowsClassFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  0 < c ∧ 0 < cb ∧ ∀ x (i : Fm.Ix x), CountRowsClass P (Fm.D x i) n₀ A C c cb

theorem count_class_of_count {D : Formalism.BasicNotions.D7} {n₀ : ℕ} {A C c cb : ℝ} (h : PointsLemma D n₀ A C c cb) : CountIdempotentsClass P D n₀ A C c cb := by
  intro I b lam g g₀ e H _ _ _ σ w Hs _ _ _ σs tens μf _ fund R Re h' hS _ hc hg h1 h2 h3
  exact h I b lam g g₀ e H σ w Hs σs tens μf fund R Re h' hS hc hg h1 h2 h3

section Count

open Finset

variable {D : D7}

theorem admissibility_ten_of_rows_class (large₂ : SizeData₂ D) (X : RowsAut) (hX : RowsTieP P D X) (n0 : ℕ) (A C cb c : ℝ)
    (h : CountRowsClass P D n0 A C c cb) : AdmissibleBoundsFromSource.adm10 D large₂ n0 A C cb c := by
  intro hp
  obtain ⟨-, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := hp
  have hX' := hX.1
  obtain ⟨⟨pl, T⟩, t5, tsp⟩ := hX'
  have hn := T.n_eq
  have trd := T.rd_eq
  have tg0 := T.g0_eq
  have tg := T.g_eq
  have hq : ∀ v, X.I.pAt v = (univ.filter fun a : Fin D.R.r => epsS D.R a = true).card ∧
      X.I.qAt v = (univ.filter fun a : Fin D.R.r => epsS D.R a = false).card := by
    intro v
    have he := T.eps_eq v
    constructor
    · simp only [AutInst.pAt, he]
      exact card_cast hn (fun a => epsS D.R a = true)
    · simp only [AutInst.qAt, he]
      exact card_cast hn (fun a => epsS D.R a = false)
  have hS : PlaceDegreeData.HidaSetting X.I n0 A large₂.sc.b X.lam X.μf X.g X.g₀ X.e := by
    refine ⟨by rw [hn]; exact p2, ⟨_, _, hq, ?_⟩, p11, ?_, t5, ?_, X.e_adm, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hn]
      exact le_trans (Nat.pow_le_pow_left card_epsS_false 2) p3
    · rw [trd, hn]; exact p4
    · intro v a
      rw [T.lam_eq v a]; exact p5 _ _
    · rw [tg]
      exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
    · rw [tg]
      have : gg D = ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by unfold gg; push_cast; ring
      rw [← this]; exact p6
    · rw [tg0]; exact D.host.g_prime 0
    · rw [tg0, hn]; exact p7
    · exact tsp p8
  refine h X large₂.sc.b _ hX hS (fun v a c hac => ?_) le_rfl p10 p12
  rw [T.lam_eq v a, T.lam_eq v c]
  exact p9 _ _ _ (by rw [← T.eps_eq v a, ← T.eps_eq v c]; exact hac)

theorem count_rows_class_of_count_class (n₀ : ℕ) (A C c cb : ℝ) (hp : CountIdempotentsClass P D n₀ A C c cb) : CountRowsClass P D n₀ A C c cb := by
  intro X b h hT hS hg h1 h2 h3
  have hPX := hT.2
  obtain ⟨⟨pl, hA⟩, -, -⟩ := hT.1
  have hD := hA.D_eq
  have hDs : X.I.Dstar (PlaceDegreeData.fdegAll X.I X.σ X.w) X.μf X.fund X.e = D.what₂.Dstar := hA.Dstar_eq.symm
  have hf := hA.f_eq
  have hrd := hA.rd_eq
  have hn := hA.n_eq
  have hc : PlaceDegreeData.CountData X.I X.lam X.σ X.w X.σs X.tens X.μf X.fund X.R X.e X.Re :=
    ⟨hA.ds, hA.low, X.tens_spec, X.haar, X.fund_spec, X.R_spec, X.Re_spec⟩
  rw [← hn, ← hf, ← hrd] at h1
  rw [← hn, ← hf] at h2 h3
  have := hp X.I b X.lam X.g X.g₀ X.e X.H X.σ X.w X.Hs X.σs X.tens X.μf X.fund X.R X.Re h hS hPX hc hg h1 h2 h3
  have e1 : (X.I.Dcount X.σs X.μf X.fund X.R X.Re : ℝ) = (D.what₂.Dall : ℝ) := by exact_mod_cast hD
  rw [e1, hDs] at this
  rw [← hn, ← hf]
  convert this using 3
  ring

end Count

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Family

abbrev PLev : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop := fun I μf g₀ e => I.IsLevelCharIdem μf g₀ e

end CountE


open Classical in
def IsCharIdemFin {G : Type} [Group G] (f : MonoidAlgebra ℂ G) : Prop :=
  ∃ (U : Subgroup G) (χ : G → ℂ), (∀ a ∈ U, ∀ b ∈ U, χ (a * b) = χ a * χ b) ∧ (∀ a ∈ U, ‖χ a‖ = 1) ∧
    ∀ a, f.coeff a = if a ∈ U then (χ a)⁻¹ / (Nat.card U : ℂ) else 0

namespace AutInst

variable (I : AutInst)

structure RedDatum (g₁ g₂ : ℕ) : Type 1 where
  G₁ : Type
  G₂ : Type
  [grp₁ : Group G₁]
  [grp₂ : Group G₂]
  [fin₁ : Fintype G₁]
  [fin₂ : Fintype G₂]
  red : I.Gf → G₁ × G₂
  red_mul : ∀ x ∈ I.Kset, ∀ y ∈ I.Kset, red (x * y) = red x * red y
  red_surj : ∀ a : G₁ × G₂, ∃ x ∈ I.Kset, red x = a
  red_fib₁ : ∀ x ∈ I.Kset, ∀ y ∈ I.Kset, ((red x).1 = (red y).1 ↔ x⁻¹ * y ∈ I.Kg g₁)
  red_fib₂ : ∀ x ∈ I.Kset, ∀ y ∈ I.Kset, ((red x).2 = (red y).2 ↔ x⁻¹ * y ∈ I.Kg g₂)

attribute [instance] RedDatum.grp₁ RedDatum.grp₂ RedDatum.fin₁ RedDatum.fin₂


open Classical in
def IsCountIdem (μf : Measure I.Gf) (g₀ : ℕ) (e : I.Gf → ℂ) : Prop :=
  ∃ (a b p : ℕ) (R : I.RedDatum (g₀ ^ a) (p ^ b)) (f₀ : MonoidAlgebra ℂ R.G₁) (z ε₂ : MonoidAlgebra ℂ R.G₂),
    p.Prime ∧ p ≠ g₀ ∧ IsCharIdemFin f₀ ∧ (∀ x ∈ I.Kset, f₀.coeff (R.red x).1 ≠ 0 → I.UnipMod g₀ x) ∧
    IsCharIdemFin ε₂ ∧ z * z = z ∧ (∀ y : MonoidAlgebra ℂ R.G₂, z * y = y * z) ∧
    ∀ x, e x = if x ∈ I.Kset then
      f₀.coeff (R.red x).1 * (z * ε₂).coeff (R.red x).2 / ((μf (I.Kg (g₀ ^ a) ∩ I.Kg (p ^ b))).toReal : ℂ) else 0

end AutInst

namespace CountE

abbrev PCount : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop :=
  fun I μf g₀ e => I.IsLevelCharIdem μf g₀ e ∨ I.IsCountIdem μf g₀ e

end CountE

end Formalism.MainNotions.S
