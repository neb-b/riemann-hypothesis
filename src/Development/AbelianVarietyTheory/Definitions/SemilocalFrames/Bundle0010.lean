module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.RealPlaceAnalysis.StatementU
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.LocalRingCardinality.SpanPowerMembership
public import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Jet

def IsDer {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) : Prop :=
  GlRel E ∧ IsUnitary ε E ∧
    (∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∀ v : V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) ((∑ a, ∑ b, X a b • E a b v : V) : H) 0) ∧
    ∀ (v : V) (y : H), SmoothOnG ε (fun g => ⟪y, σ g (v : H)⟫_ℂ)

def at1 {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (G : Arr V n 1) (a b : Fin n) : V :=
  arrOf V n 1 G (fun _ => (a, b))


namespace StdDer


end StdDer

end GlobalTheory.Jet
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
section
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

variable (D : D7) (large₂ : SizeData₂ D)

def HypZ (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop := StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ StandingNumericalData D C0 ∧ 1 ≤ C0

def MomIn (C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A →
      ∀ (a : Fin (D.R.rS + 1)) (q : ℕ), (q : ℝ) ≤ Cq * (D.R.rS : ℝ) ^ 3 →
        ∫⁻ x, ENNReal.ofReal (lA D.R.k D.R.rS W.z (Matrix.of x) a ^ (2 * q)) *
            (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS ≤
          ENNReal.ofReal (large₂.sc.b ^ (2 * C * D.R.m * q)) * l2SG W.νS A.Φ

def SchurSt (C' Cl Cg cb Cu cT CT C0 C1 C : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ A : LocS W, GoodS D (lamD D τ) A →
      ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec →
        MMv D w w' A μsec ≤
          ENNReal.ofReal ((Tr D w * Tr D w') ^ (D.R.k - 1) *
            ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ) * volUn D.R.r * volUn (D.R.k - 1) /
              (A.deg * volUn D.R.k ^ 2 * (2 * D.host.v) ^ (2 * D.R.rS * D.R.k))) *
            large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2))

def ABSr (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ S : LocS W, GoodS D lam' S →
      ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ', normWin D large₂ C1 θ' → ∀ νR, RMeas D W γ θ' νR →
        DminN W.z W.z' γ D.R.rS ≠ 0 →
          Integrable (fun x => (innerSL ℂ (S.Φ' (Matrix.of x))).smulRight (S.Φ (γ * Matrix.of x))) νR ∧
          ‖S.J νR γ‖ ≤ lossP large₂.sc.b C D.R.m W.z W.z' γ p *
            (C / (D.R.k * D.host.v)) ^ (D.R.rS * (D.R.k - 2 - D.R.rS)) *
            (‖DminN W.z W.z' γ D.R.rS‖ ^ (D.R.k - 2 - D.R.rS))⁻¹

def LocIn (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w' θ W, HypTT D w w' → GoodW D τ w w' θ W → ∀ A : LocS W, GoodS D (lamD D τ) A →
    MultOne W.z (psiS D W.z) A.σ W.π ∧ MultOne W.z' (psiS D W.z') A.σ W.π' ∧
      Decay A.σ (DD A.σ A.v0) (2 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 5)

def Big (Cl m₀ : ℝ) : Prop := D.host.rdE ≤ large₂.sc.b ∧ 1 ≤ Cl * D.R.m ∧ m₀ ≤ D.R.m

def BSch (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w' θ (W : LocW D.R.k D.R.rS), GoodW D τ w w' θ W → ∀ A : LocS W, GoodS D (lamD D τ) A → 0 < Tr D w →
    ∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) A.σ,
      l2SG W.νS (fun g => A.B (A.σ g v)) * (‖A.v0‖₊ : ℝ≥0∞) ^ 2 = l2SG W.νS A.Φ * (‖v‖₊ : ℝ≥0∞) ^ 2

def Sizes (Cl Cg CT : ℝ) : Prop :=
  1 < large₂.sc.L ∧ Real.log large₂.sc.b = large₂.sc.L ∧ Real.exp 1 < large₂.sc.b ∧ D.R.m = 2 * D.R.rS + 2 ∧
    D.R.r = 2 * D.R.rS + D.R.k + 1 ∧ Fintype.card D.what₂.Tau = D.R.f ∧ Cl ≤ D.R.m ∧ D.R.m ^ 4 ≤ D.R.k ∧
    1 ≤ D.host.v ∧ D.host.rdE = 2 * D.host.v ∧ D.host.ka = Real.pi / D.host.v ∧ 2 * D.host.v ≤ large₂.sc.b ∧
    1 ≤ gg D ∧ gg D ≤ large₂.sc.b ^ (2 * Cg) ∧ 8 ≤ Cg ∧ (D.R.k : ℝ) ≤ large₂.sc.b ^ Cg ∧
    (∀ w, Tr D w ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ))) ∧ (∀ w τ, 0 < Formalism.MainNotions.S.vand (uS D w τ) ∧ 0 < Tcrit D w τ) ∧
    ∀ τ (a c : Fin (2 * D.R.rS + D.R.k + 1)), a < c →
      Cl * D.R.k * (D.R.m : ℝ) ^ 4 < lamD D τ a - lamD D τ c

end GlobalTheory.Amp
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsSatFlagOne
section
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas.SatModel

open Formalism.MainNotions.S GlobalTheory.Count

theorem volU_pos (i : ℕ) : 0 < volU i := by
  unfold volU sphV
  have := Real.pi_pos
  refine mul_pos (Finset.prod_pos fun l _ => by positivity) (by positivity)

theorem cIw_pos (p q : ℕ) {a : ℕ} (j : Fin a → ℕ) : 0 < cIw p q j := by
  unfold cIw
  have := volU_pos
  refine div_pos (mul_pos (by positivity) (mul_pos (this _) (this _)))
    (mul_pos (mul_pos (Finset.prod_pos fun i _ => mul_pos (this _) (by positivity)) (this _)) (this _))

end GlobalTheory.FlagMeas.SatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

def Sg2 (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (x : Mat k r) : ℝ :=
  Finset.univ.fold max 1 fun a : Fin (r + 1) => max (lA k r z x a) (lA k r z x a)⁻¹

def Dj (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) : ℝ :=
  ‖Dmin k r z z' γ ⟨j, by omega⟩‖

def Yj (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ x : Mat k r) : ℝ :=
  gramProj (Ppos k r z z' γ x) (fun a : Fin j => x⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)))) / Dj k r hj z z' γ

def XstJ (k r j : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun a : {a : Fin r // a.val < j} => bvec (esI k r a.1))

def XJ (k r j : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun a : {a : Fin r // a.val < j} => bvec (eI k r a.1))

def IsNormal0 (k r : ℕ) {j : ℕ} (hj : j ≤ r) (β : Fin r → ℕ) (c : ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : Prop :=
  g ∈ GG k r ∧ ‖c‖ = 1 ∧ g *ᵥ z' = c • z ∧ Monotone β ∧
    (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) ∧
    (∀ a : Fin r, a.val < j → g⁻¹ *ᵥ bvec (eI k r a) ∈ XstJ k r j ∧ g *ᵥ bvec (eI k r a) ∈ XstJ k r j) ∧
    (∀ a : Fin r, j ≤ a.val → g *ᵥ bvec (eI k r a) = c • bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = c • bvec (esI k r a)) ∧
    BlockAnti (fun a : Fin j => β (Fin.castLE hj a)) ((Zr k r g).submatrix (Fin.castLE hj) (Fin.castLE hj))

abbrev PTop (k r j : ℕ) :=
  ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ) × ({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ)

abbrev PSec (k r j : ℕ) :=
  ({a : Fin r // a.val < j} → Fin (k + 1) → ℂ) × ({p : UT r // p.1.1.val < j} → ℂ) × ({a : Fin r // a.val < j} → ℝ)

def pTop (k r j : ℕ) (q : PTop k r j) : Mat k r :=
  pOf k r (fun a => if h : j ≤ a.val then q.1 ⟨a, h⟩ else 0, fun p => if h : j ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0,
    fun a => if h : j ≤ a.val then q.2.2 ⟨a, h⟩ else 0)

def pSec (k r j : ℕ) (q : PSec k r j) : Mat k r :=
  pOf k r (fun a => if h : a.val < j then q.1 ⟨a, h⟩ else 0, fun p => if h : p.1.1.val < j then q.2.1 ⟨p, h⟩ else 0,
    fun a => if h : a.val < j then q.2.2 ⟨a, h⟩ else 0)

def rEl (k r j : ℕ) (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) : Mat k r := uEmb k r (upperIn β q.1) * pTop k r j q.2

def sEl (k r j : ℕ) (β : Fin r → ℕ) (q : PSec k r j × (UToff β → ℂ)) : Mat k r := pSec k r j q.1 * uEmb k r (upperOff β q.2)

def lebR0 (k r j : ℕ) (β : Fin r → ℕ) : Measure (Mt k r) :=
  (volume : Measure ((UTin β → ℂ) × PTop k r j)).map fun q => Matrix.of.symm (rEl k r j β q)

def IsNormalFormStabilizerMeasure (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)) : Prop :=
  inWb k r z ∧ inWb k r z' ∧ 0 < Tz k r z ∧
    ∃ n₁ ∈ Nset k r, ∃ n₂ ∈ Nset k r, ∃ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), IsNormal0 k r hj β c z z' g₀ ∧
      γ = n₁ * g₀ * n₂ ∧ μR = (ENNReal.ofReal s • lebR0 k r j β).map (conjM n₂⁻¹)

def Eset0 (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (R₀ y : ℝ) : Set (Mt k r) :=
  {x | Matrix.of x ∈ GG k r ∧ Sg2 k r z' (Matrix.of x) ≤ R₀ ∧ Sg2 k r z (γ * Matrix.of x) ≤ R₀ ∧
    y < Yj k r hj z z' γ (Matrix.of x) ∧ Yj k r hj z z' γ (Matrix.of x) ≤ 2 * y}

def fibVol0 (k r j : ℕ) (R₀ De y : ℝ) : ℝ :=
  (4 * r : ℝ) ^ (4 * r ^ 2) * (R₀ ^ (2 * r) * De) ^ (8 * r ^ 2) *
    (Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ)) ^ (j * (k - 1 - j)) * (2 * y) ^ (2 * (k - 1 - j))

def TailBd {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] (z : Fin (2 * r + k + 1) → ℂ) (νS : Measure (Mt k r))
    (Φ : Mat k r → Wp) (q : ℕ) (H₁ : ℝ) : Prop :=
  ∀ la : ℝ, 0 < la →
    ∫⁻ x, Set.indicator {x : Mt k r | ∃ a : Fin (r + 1), la * H₁ ≤ max (lA k r z (Matrix.of x) a) (lA k r z (Matrix.of x) a)⁻¹}
        (fun x => (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) x ∂νS ≤
      ENNReal.ofReal (2 * (2 * r + 2 : ℝ) * la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ

def sgV (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (H₁ : ℝ) : ℝ :=
  Finset.univ.fold max 1 fun l : Fin (r + 1) => ‖Dmin k r z z' γ l.castSucc‖ / (2 * H₁) ^ (2 * r)

def degBd (k r j q : ℕ) (H₁ De D sg : ℝ) : ℝ :=
  16 * (4 * r + 4 : ℝ) * (4 * r : ℝ) ^ (4 * r ^ 2) * (2 * H₁) ^ (16 * r ^ 3 + 4 * r) * De ^ (8 * r ^ 2 + 2) *
    (8 * Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ)) ^ (j * (k - 1 - j)) * (D ^ (k - 1 - j))⁻¹ *
    sg ^ (-(((q : ℝ) - 16 * r ^ 3 - 4 * r - 1) / r))

end GlobalTheory.Amp
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsProjOnOne
section
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.Deep

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

def frame (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ :=
  I.P v * uMat (x.1 v)

def crd (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) (y : Fin I.n → I.E) : EuclideanSpace ℂ (Fin I.n) :=
  WithLp.toLp 2 ((frame I x v)⁻¹ *ᵥ fun i => I.φ v (y i))

def SatX (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) S

def SizesGe (I : AutInst) (x : I.GA) (B B' : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo : ℝ) : Prop :=
  ∀ N : Submodule (𝓞 I.E) (Fin I.n → I.E), B' < N → N ≤ B → lo ≤ Formalism.HN.sizeQ (bas I) (frm I x) N B'

def SizesLe (I : AutInst) (x : I.GA) (A A' : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi : ℝ) : Prop :=
  ∀ N : Submodule (𝓞 I.E) (Fin I.n → I.E), A' ≤ N →
    Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) A N → N ≠ A →
      Formalism.HN.sizeQ (bas I) (frm I x) A N ≤ hi

def omega (I : AutInst) (x : I.GA) (W : Submodule I.E (Fin I.n → I.E)) (ρ : ℝ) : Set I.GA :=
  {y | y.2 = x.2 ∧ ∃ A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ,
    (∀ v, Formalism.REAL.inG (I.ε v) (A v) ∧ Formalism.REAL.inG (I.ε v) (Z v)) ∧
    Real.sqrt (∑ v, Formalism.REAL.hs (A v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v)) ≤ ρ ∧
    (∀ v, uMat (y.1 v) = uMat (x.1 v) * NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧
    ∀ s t : ℝ, ∃ m : I.Ginf, ((m, 1) : I.GA) ∈ I.NA W ∧
      ∀ v, uMat (m v) * uMat (x.1 v) =
        uMat (x.1 v) * NormedSpace.exp ((s : ℂ) • A v) * NormedSpace.exp ((t : ℂ) • Z v)}

def IsReps (B : RowsAut) (T : B.Hs →L[ℂ] B.I.L2 B.μf B.fund) (Fr : B.Hs → B.I.GA → ℂ) : Prop :=
  ∀ P : ℕ, ∀ u ∈ VP B P, GlobalTheory.Dec.IsContRep B (T u) (Fr u) ∧
    (∀ k ∈ B.I.Kg B.g, ∀ y, Fr u (y * (1, k)) = Fr u y) ∧
    ∀ (E : gInf B) (y : B.I.GA),
      HasDerivAt (fun t : ℝ => Fr u (y * ((fun v => expU (t • E v)), 1))) (Fr (dAct B E u) y) 0

def vv (B : RowsAut) {D : ℕ} (Fr : Fin D → B.Hs → B.I.GA → ℂ) (u : B.Hs) (y : B.I.GA) :
    EuclideanSpace ℂ (Fin D) :=
  WithLp.toLp 2 fun i => Fr i u y

end GlobalTheory.Deep
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellAmp

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def pairMaj {k r : ℕ} (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) (p : PairSp k r) : ℝ :=
  Formalism.FourierDecayAlt.B.gN ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1) ^ (-b)

def coefF {k r : ℕ} (L : LocBessel k r) (v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : L.Wq →L[ℂ] L.Wp :=
  (innerSL ℂ ξ').smulRight (⟪v, L.σ g v'⟫_ℂ • ξ)

def CellData {k r : ℕ} (L : LocBessel k r) (μG : Measure (Mt k r))
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
    (ν : Measure (PairSp k r)) : Prop :=
  γ ∈ UH (Hpk k r) ∧ 0 < Gf k r L.z L.z' γ ∧ Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' γ) ∧
    IsRelStab L γ ∧ IsHaarOn (RStab k r γ) μR ∧ IsOrbQuot L γ μR ν ∧
    PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR

def OnePlace {k r : ℕ} (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp)
    (l' : L.Hs → L.Wq) : Prop :=
  GapAtLeast L.ε L.lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h ∧ L.c ≠ 0 ∧ PI.UpqRep.IsLowUnitH k r L.ε L.lam L.σ w0 ∧
    IsHaarOn (UH (Hpk k r)) μG ∧
    (∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) ∧
    (∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))

def OnePlaceKF {k r : ℕ} (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp)
    (l' : L.Hs → L.Wq) : Prop :=
  OnePlace L h μG w0 l l' ∧
    (∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v →
      Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) ∧
    (∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v →
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))

def AmpKF : Prop :=
  Formalism.FourierDecayAlt.ThreeDimData.Inputs →
  ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq),
    OnePlaceKF L h μG w0 l l' →
    ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
      (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν →
    ∀ b : ℝ, 0 ≤ b → Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b → Integrable (pairMaj γ b) ν →
    ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' →
    ∀ (ξ : L.Wp) (ξ' : L.Wq),
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w0 : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν

def GapCell (k r : ℕ) (h : ℝ) : Prop :=
  10 * ((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) + 2 * Formalism.FourierDecayAlt.ThreeDimData.AG k r + 4 ≤
    Formalism.FourierDecayAlt.ThreeDimData.aOf r h

def CellConv : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r))
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
    (ν : Measure (PairSp k r)),
    L.κN ≠ ⊤ → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → CellData L μG γ μR νR ν →
    Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat k r L.z L.z' γ) →
    ∃ b : ℝ, 0 ≤ b ∧ Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b ∧ Integrable (pairMaj γ b) ν

def amp {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (R : BranchingSupport.Rep k r) (l : R.H → Wp) (l' : R.H → Wq) (w : R.H)
    (ν : Measure (Mt k r)) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Wq →L[ℂ] Wp :=
  ampJ ν 1 (fun g => l (R.σ g w)) (fun g => l' (R.σ g w)) γ

end GlobalTheory.CellAmp

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SmallHostRootDiscriminantLe
section
noncomputable section

namespace GlobalTheory.Diag.PG.Wit

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField

variable {R : Ranks} {x eps : ℝ} {Del h : ℕ}



end GlobalTheory.Diag.PG.Wit

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ThresholdProductsBounded
section
namespace GlobalTheory.ThA

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.KB Finset NumberField MeasureTheory Formalism.QuantumDeterminants

noncomputable section

open Classical

section place

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end place

def PlExists : Prop :=
  ∃ Cb : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r) (l0 : ℕ),
    1 ≤ l0 → l0 ≤ P.k → 2 ≤ P.k → Bs.μW Set.univ = 1 → Bs.μW' Set.univ = 1 → Bs.μN = D.muN P.k P.r →
    D.IsBaseFrame Bs ν' m₀ → Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' →
    ∃ p : Pl P Wp Wq, p.l0 = l0 ∧ p.T.base = Bs ∧ p.ν' = ν' ∧ p.m₀ = m₀ ∧ InDDplus2 P l0 p.T.base Cb p.Θ

end

end GlobalTheory.ThA
end

