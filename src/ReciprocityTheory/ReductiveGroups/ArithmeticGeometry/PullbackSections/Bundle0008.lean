module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LogSupSumLeOfNonvanishingDetLimit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SubMul
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def LieFacAddSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (x : ℝ)
    (a a' : (E →+* ℂ) × ℕ → ℕ), lieFac Dw x (a + a') = lieFac Dw x a * lieFac Dw x a'

def PnormMulSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la la' : Wt X.Ψ r)
    (P Q : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r), x ∈ X.dom →
      X.pnorm (la + la') (P * Q) x = X.pnorm la P x * X.pnorm la' Q x

def SupCMulSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (σ : c.F →+* ℂ)
    (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (f g : Rul Xo c), GoodEmb c σ → Even n → Even n' →
    supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) ≠ ⊤ → supE (U σ).X (laU (U σ) a' n') (rdU (U σ) g) ≠ ⊤ →
      supC Xo c U x σ (a + a') (n + n') (f * g) ≤ supC Xo c U x σ a n f * supC Xo c U x σ a' n' g

def RecSubMulSt : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), Formalism.MainNotions.Gaps.SizeBoundsAlt.SubMul (recPJ h j hj)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupNormFromNet
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def netNorm (U : Unf Xo c σ r) (la : ∀ k, Wt (U.X k).Ψ r) (NN : Finset (FPt U.X)) (P : FDSec U.X) : ℝ :=
  Real.sqrt ((NN.card : ℝ)⁻¹ * ∑ p ∈ NN, ((U.X p.1).pnorm (la p.1) (P p.1) p.2) ^ 2)

def NnOf (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (NN : Finset (FPt U.X)) (f : Rul Xo c) : ℝ :=
  dmet n (Module.finrank ℚ E / 2) r * netNorm U (laU U a n) NN (rdU U f)

def IsNet (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (NN : Finset (FPt U.X)) : Prop :=
  NN.Nonempty ∧ ∀ P ∈ holSub U.X (laU U a n),
    supN U.X (laU U a n) P ≤ 4 * Real.sqrt NN.card * netNorm U (laU U a n) NN P

def NetExistsSt : Prop :=
  ∃ Cn : ℝ, ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j)
    (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → SupBoundPageRows D large₂ ka →
    ∃ NN : Finset (FPt (T.U j σ).X), IsNet (T.U j σ) (wtA ka) ka.n NN ∧
      Real.log (16 * NN.card) ≤ Cn * Zb D large₂ ^ 3

set_option synthInstance.maxHeartbeats 400000 in
def AlgInjAtSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ),
    GoodEmb T.Q.c σ → ∀ (m : ℕ) (f : Fin m → T.C j ka),
      LinearIndependent T.Q.c.F f → LinearIndependent ℂ (fun i => rdU (T.U j σ) (f i : T.R j))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def vspActL {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) :
    ReciprocityTheory.ChartRestriction.G.I2.Vsp dim →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp dim where
  toFun := ReciprocityTheory.ChartRestriction.G.I2.act α
  map_add' v w := by
    ext i
    simp [ReciprocityTheory.ChartRestriction.G.I2.act, mul_add]
  map_smul' c v := by
    ext i
    simp [ReciprocityTheory.ChartRestriction.G.I2.act]
    ring

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCSteps
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

section FrRd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def IsFrRd {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) (Wu : UnitAt W) (kk : ℤ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L kk (Over.mk (U.un k x).x))) (θF : (Fin W.g → ℂ) → ℂ) : Prop :=
  ∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
    pt ≫ gxFst (U.un k x).x = (W.F.ex (W.ik k) W.Pm z).left →
    pt ≫ gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
    ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' pt ((LPow Xo.univ.t.G Xo.univ.t.PP.L kk (Over.mk (U.un k x).x)).U (fun _ => j))
      (F.f (fun _ => j)) = θF z * Wu.fr j z ^ kk

end FrRd

section BC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

end BC

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

