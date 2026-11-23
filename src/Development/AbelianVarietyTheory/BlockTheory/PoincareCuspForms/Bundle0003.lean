module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.CurvatureFamilyNorm
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def de2 (X : Data E r) : Wt X.Ψ r := fun _ i => if (i : ℕ) < X.p0 then -1 else 1

def frameWt (X : Data E r) (a : Wt X.Ψ r) (h : ℤ) : Wt X.Ψ r := a + h • de2 X

def IsGap (X : Data E r) (i j : Fin r) : Prop := (j : ℕ) = i + 1 ∧ (j : ℕ) ≠ X.p0

def rd (X : Data E r) : ℝ := |(discr E : ℝ)| ^ (1 / (2 * (X.Ψ.card : ℝ)))

def RR (X : Data E r) : ℝ := rd X ^ 7

def dp (X : Data E r) : ℝ := 2 * (X.Ψ.card : ℝ) * X.p0

def g0half (r : ℕ) : ℕ := 5 ^ 4 * r

def g0 (r : ℕ) : ℕ := 2 * g0half r

def a1 (X : Data E r) : ℝ := (X.Ψ.card : ℝ) / (5 ^ 4 * rd X ^ 2)

def bb (X : Data E r) : ℝ := 5 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2

def Crh (X : Data E r) : ℝ := ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ)

structure Shape (X : Data E r) : Prop where
  p0_pos : 0 < X.p0
  witt : 2 * X.p0 ≤ r
  r_ge : 8 ≤ r
  D_ge : 2 ≤ nd X

structure Weights (X : Data E r) where
  shape : Shape X
  T : ℕ
  i : ℕ
  c : ℝ
  hW : ℕ
  hF : ℕ
  aK : Wt X.Ψ r
  aW : Wt X.Ψ r
  i_pos : 0 < i
  c_pos : 0 < c
  T_cols : (nd X + 2) * (2 * hW) + 2 * r ≤ T
  T_forty : 40 * (nd X + 2) ≤ T
  T_sq : 11 * nd X ^ 2 ≤ T
  cols_lo : 8 * X.Ψ.card * r + 4 ≤ 2 * hF
  cols_hi : 2 * hF ≤ 2 * hW
  Tcg : (T : ℝ) * c * g0 r ≤ 1
  cRR : (g0 r : ℝ) * X.Ψ.card * (X.p0 : ℝ) ^ 3 * RR X ^ 2 * c ≤ 1
  b_cut : bb X < 3.8 * T - 2 * T
  b_onto : bb X ^ 2 * Crh X + bb X < 1.9 * ((nd X : ℝ) + 2) * T
  gap_big : ∀ τ a b, IsGap X a b →
    ((T : ℤ) + nd X + 2) * ((T : ℤ) + nd X + 2 + 2 * r) ≤ aK τ a - aK τ b + 2
  plus_big : ∀ τ (a : Fin r), (a : ℕ) + 1 = r → 2 * (T : ℤ) ^ 2 ≤ aK τ a
  minus_big : ∀ τ (a : Fin r), (a : ℕ) = 0 → 2 * (T : ℤ) ^ 2 ≤ -aK τ a
  gap_div : ∀ τ a b, IsGap X a b →
    aK τ a - aK τ b + 2 - ((T : ℤ) + nd X + 2) * (aW τ a - aW τ b) ∈ Set.Ico (0 : ℤ) (T + nd X + 2)
  plus_div : ∀ τ (a : Fin r), (a : ℕ) + 1 = r →
    aK τ a - ((T : ℤ) + nd X + 2) * aW τ a - ((nd X : ℤ) + 2) * (2 * hW) - 2 * r ∈
      Set.Ico (0 : ℤ) (T + nd X + 2)
  minus_div : ∀ τ (a : Fin r), (a : ℕ) = 0 →
    -aK τ a - ((T : ℤ) + nd X + 2) * (-aW τ a) ∈ Set.Ico (0 : ℤ) (T + nd X + 2)

namespace Weights

variable {X : Data E r} (w : Weights X)

def L : Wt X.Ψ r := frameWt X w.aW w.hW

def Fp : Wt X.Ψ r := frameWt X (w.aK - (w.T : ℤ) • w.aW) w.hF

def twoG₁ : Wt X.Ψ r := (2 : ℤ) • w.L - de2 X

def G₂ : Wt X.Ψ r := ((nd X : ℤ) + 4) • w.L - w.Fp

def wEt : Wt X.Ψ r := frameWt X 0 (w.i * g0half r : ℕ)

def rem : Wt X.Ψ r := w.Fp - ((nd X : ℤ) + 2) • w.L - kapW X

def c1 : ℝ := RR X * w.T * w.c * dp X ^ 2 * X.p0 / 2

def t : ℝ := 1 + w.c1 / a1 X

end Weights

def lev (X : Data E r) (x0 : Frame X.Ψ r) (u : Frame X.Ψ r → ℝ) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun y => ((u (cpt X x0 y) : ℝ) : ℂ)) z ξ).re

def curv (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  lev X x0 (phla X la) z ξ

def curvDe (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  curv X x0 (de2 X) z ξ / 2

def omRh (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun y => ((rhF X x0 y : ℝ) : ℂ)) z ξ).re

def IsInv (X : Data E r) (u : Frame X.Ψ r → ℝ) : Prop :=
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, u (rmul x b) = u x) ∧ ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, u (lact γ x) = u x

def famNorm (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ :=
  Real.sqrt (∑ j, X.pnorm la (w j) x ^ 2)

structure ThetaInputs (X : Data E r) extends Weights X where

  N : ℕ
  w : Fin N → Frame X.Ψ r → ℂ
  et : Frame X.Ψ r → ℂ
  th₁ : Frame X.Ψ r → ℂ
  th₂ : Frame X.Ψ r → ℂ
  thp : Frame X.Ψ r → ℂ
  phi : Frame X.Ψ r → ℝ
  mu : ℝ
  ps0 : Frame X.Ψ r → ℝ
  w_cusp : ∀ j, w j ∈ X.SS toWeights.L
  et_bdd : X.IsBddSec toWeights.wEt et
  et_ne : ∃ x ∈ X.dom, et x ≠ 0
  th₁_cusp : th₁ ∈ X.SS toWeights.twoG₁
  th₁_ne : ∃ x ∈ X.dom, th₁ x ≠ 0
  th₂_cusp : th₂ ∈ X.SS toWeights.G₂
  th₂_ne : ∃ x ∈ X.dom, th₂ x ≠ 0
  thp_cusp : thp ∈ X.SS toWeights.Fp
  thp_ne : ∃ x ∈ X.dom, thp x ≠ 0
  phi_inv : IsInv X phi
  phi_nonneg : ∀ x ∈ X.dom, 0 ≤ phi x
  phi_lower : ∀ x ∈ X.dom, X.la1 x < Real.sqrt X.Ψ.card * Real.exp (-mu) →
    1 ≤ 4 * RR X * dp X ^ 2 * X.la1 x ^ 2 * phi x
  phi_upper : ∀ x ∈ X.dom, 2 * X.la1 x ^ 2 * phi x ≤ X.p0 * dp X ^ 2
  w_lower : ∃ C : ℝ, ∀ x ∈ X.dom, Real.exp (-(C + c * phi x)) ≤ famNorm X toWeights.L w x
  et_upper : ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm toWeights.wEt et x ≤ Real.exp (-(i * (phi x - C)))
  potential_smooth : ContDiffOn ℝ ∞ ps0 X.dom
  potential_invariant : IsInv X ps0
  potential_bounded : ∃ C : ℝ, ∀ x ∈ X.dom, ps0 x ≤ C
  curvature_lower_bound : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ, -(r * curvDe X x0 z ξ) ≤ lev X x0 ps0 z ξ
  potential_decay : ∃ A : ℝ, ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x ∈ X.dom, ∀ ξ, X.IsIso ξ →
    (∀ τ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1) →
    ps0 x ≤ C + A * Real.log (1 + 1 / X.la1 x) - 8 * Real.pi * (1 - 2 * η) * a1 X * ⨅ τ, X.tt ξ x τ
  curv_L : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ, ξ ≠ 0 → 0 < curv X x0 toWeights.L z ξ
  curv_G₁ : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ, ξ ≠ 0 →
    curvDe X x0 z ξ < curv X x0 toWeights.L z ξ
  margin_cut : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ,
    curv X x0 toWeights.L z ξ + 3.8 * T * omRh X x0 z ξ ≤
      curv X x0 ((2 : ℤ) • toWeights.L + toWeights.rem) z ξ
  margin_twist : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ,
    curv X x0 toWeights.L z ξ + (3.8 * T - 2 * T) * omRh X x0 z ξ ≤
      curv X x0 ((2 : ℤ) • toWeights.L + toWeights.rem) z ξ - toWeights.t * r * curvDe X x0 z ξ
  margin_onto : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ,
    1.9 * ((nd X : ℝ) + 2) * T * omRh X x0 z ξ ≤ curv X x0 (toWeights.Fp - kapW X) z ξ

end

end GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.LowSpanCombinations
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def hf (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) : ℝ :=
  X.c τ * X.maj x τ (Data.emb τ.1 ξ)

def ExtraBounds (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  ∃ A : ℝ,
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ → (∀ τ, hf X ξ x τ ≤ 1) →
      ps x ≤ C + A * Real.log (1 + 1 / X.la1 x) -
        8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ) ∧
    ∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C + A * Real.log (1 + 1 / X.la1 x)

def lowIdx (D T : ℕ) : Finset (Fin D → ℕ) :=
  (Fintype.piFinset fun _ : Fin D => Finset.range T).filter fun al => ∑ i, al i + D < T

theorem nonempty_cmType (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · have := (X.cmType τ).not.1 h
    exact ⟨⟨_, not_not.1 this⟩⟩

theorem tt_eq (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) :
    X.tt ξ x τ = 1 / hf X ξ x τ := rfl

end

end GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def castFrame {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (x : Frame Ψ r) : Frame Ψ' r :=
  fun τ => x ⟨τ.1, h.symm ▸ τ.2⟩

def castWt {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (la : Wt Ψ' r) : Wt Ψ r :=
  fun τ => la ⟨τ.1, h ▸ τ.2⟩

def deMul (Ψ : Finset (E →+* ℂ)) (r p0 s : ℕ) : Wt Ψ r :=
  fun _ i => if (i : ℕ) < p0 then -((s / 2 : ℕ) : ℤ) else ((s / 2 : ℕ) : ℤ)

def GapsGe {Ψ : Finset (E →+* ℂ)} (p0 : ℕ) (la : Wt Ψ r) (a : ℤ) : Prop :=
  ∀ (τ : Ψ) (i j : Fin r), (j : ℕ) = i + 1 → (j : ℕ) ≠ p0 → a ≤ la τ i - la τ j

def PairGe {Ψ : Finset (E →+* ℂ)} (la : Wt Ψ r) (a : ℝ) : Prop :=
  ∀ (τ : Ψ) (i j : Fin r), (i : ℕ) = 0 → (j : ℕ) = r - 1 → a ≤ ((la τ j - la τ i : ℤ) : ℝ)

structure TwoLevels (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (U C : Type) [Group U] [MulAction U C] where
  Ψ : Finset (E →+* ℂ)
  Gm : Matrix (Fin r) (Fin r) E
  p0 : ℕ
  ξ0 : E
  comp : C → DataX E r
  comp_Ψ : ∀ c, (comp c).Ψ = Ψ
  comp_Gm : ∀ c, (comp c).Gm = Gm
  comp_basePoint : ∀ c, (comp c).p0 = p0
  comp_ξ0 : ∀ c, (comp c).ξ0 = ξ0

  χ_one : ∀ c la, ∀ γ ∈ (comp c).Γ, (comp c).χ la γ = 1

  Γ_L' : ∀ c, ∀ γ ∈ (comp c).Γ, ∀ v,
    v ∈ (comp c).L' ↔ Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v ∈ (comp c).L'

  tr : U → C → GL (Fin r) E
  tr_herm : ∀ u c v w, herm Gm (Matrix.mulVec (tr u c : Matrix (Fin r) (Fin r) E) v)
    (Matrix.mulVec (tr u c : Matrix (Fin r) (Fin r) E) w) = herm Gm v w
  tr_Λ : ∀ u c v,
    v ∈ (comp c).Λ ↔ Matrix.mulVec (tr u c : Matrix (Fin r) (Fin r) E) v ∈ (comp (u • c)).Λ
  tr_L' : ∀ u c v,
    v ∈ (comp c).L' ↔ Matrix.mulVec (tr u c : Matrix (Fin r) (Fin r) E) v ∈ (comp (u • c)).L'
  tr_conj : ∀ u c γ, γ ∈ (comp c).Γ ↔ tr u c * γ * (tr u c)⁻¹ ∈ (comp (u • c)).Γ
  tr_mul : ∀ u v c, tr (u * v) c * (tr u (v • c) * tr v c)⁻¹ ∈ (comp ((u * v) • c)).Γ

  tr_faithful : ∀ u c, u • c = c → tr u c ∈ (comp c).Γ → u = 1

namespace TwoLevels

variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

def dom : Set (Frame M.Ψ r) := GG M.Ψ M.Gm M.p0

def dimX : ℕ := M.Ψ.card * (M.p0 * (r - M.p0))

def dimY : ℕ := M.Ψ.card * (r * (r - 1) / 2)

def upper (c : C) : Set (GL (Fin r) E) :=
  {β | ∃ u : U, u • c = c ∧ ∃ γ ∈ (M.comp c).Γ, β = γ * M.tr u c}

def UnipotentOver (g : ℕ) : Prop :=
  ∀ c, ∀ β ∈ M.upper c, ∀ P : Ideal (𝓞 E), P.IsPrime → (g : 𝓞 E) ∈ P → ∀ v ∈ (M.comp c).L',
    Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈ P • (M.comp c).L'

def SS (la : Wt M.Ψ r) : Set (C → Frame M.Ψ r → ℂ) :=
  {F | ∀ c, (fun x => F c (castFrame (M.comp_Ψ c) x)) ∈ (M.comp c).SS (castWt (M.comp_Ψ c) la)}

def pull (h : U) (F : C → Frame M.Ψ r → ℂ) : C → Frame M.Ψ r → ℂ :=
  fun c x => F (h • c) (lact (M.tr h c) x)

def res (F : C → Frame M.Ψ r → ℂ) : C → M.dom → ℂ := fun c x => F c x.1

def cusp (la : Wt M.Ψ r) : Submodule ℂ (C → M.dom → ℂ) := Submodule.span ℂ (M.res '' M.SS la)

def detTr [Fintype U] [DecidableEq U] (F : C → Frame M.Ψ r → ℂ) (c : C) (x : Frame M.Ψ r) : ℂ :=
  (Matrix.of fun h h' : U => M.pull (h * h') F c x).det

end TwoLevels

def SplitsCompletely (E : Type) [Field E] [NumberField E] (g : ℕ) : Prop :=
  g.Prime ∧ {P : Ideal (𝓞 E) | P.IsPrime ∧ (g : 𝓞 E) ∈ P}.ncard = Module.finrank ℚ E

def LevelHyp {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C) : Prop :=
  ∃ g : ℕ, SplitsCompletely E g ∧ 3 * r < g ∧ M.UnipotentOver g

def IndependentTranslates (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (U C : Type) [Group U] [Fintype U] [DecidableEq U] [Finite C] [MulAction U C]
    (M : TwoLevels E r U C), LevelHyp M →
    ∀ s : ℕ, Even s → 2 * r + 50 * r ^ 2 * M.dimX + 1 ≤ s →
      ∃ u0 ∈ M.SS (deMul M.Ψ r M.p0 s), ∀ c : C, ∃ x ∈ M.dom, M.detTr u0 c x ≠ 0

def kLog (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Wt Ψ r := fun _ a => 2 * (a : ℤ) - ((r : ℤ) - 1)

end

end GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
end

