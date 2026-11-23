module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0012
public import Lemmata.GeneralBFactForm.Imports

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def phla {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) : ℝ := -2 * Real.log (X.nfac la x)

def IsBEq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  DifferentiableOn ℂ P X.dom ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x

def IsFundSet {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Prop :=
  MeasurableSet FF ∧ FF ⊆ OmF X x0 ∧
  (∀ z ∈ FF, ∀ z' ∈ FF, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r,
    cpt X x0 z' = lact γ (rmul (cpt X x0 z) b) → z = z') ∧
  ∀ᵐ z ∂muF X x0, ∃ z' ∈ FF, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
    cpt X x0 z = lact γ (rmul (cpt X x0 z') b)

def ExhaustFStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∃ S : EtaleStein (nd X) (OmF X x0), S.z = Subtype.val ∧ S.e = fun y => eF X x0 y.1

def MeasInvStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 x0' : Frame X.Ψ r), IsOrth X x0 → IsOrth X x0' →
    ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
    ∫⁻ z, φ (cpt X x0 z) ∂muF X x0 = ∫⁻ z, φ (cpt X x0' z) ∂muF X x0'

def ExtFStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (F : V (nd X) → ℂ),
    DifferentiableOn ℂ F (OmF X x0) →
    (∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom →
      ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0 < ⊤) →
    ∃ P : Frame X.Ψ r → ℂ, IsBEq X la P ∧ ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z

def FundSetStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∃ FF : Set (V (nd X)), IsFundSet X x0 FF

def IsMetricW {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) : Prop :=
  Measurable W ∧
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, W (rmul x b) = W x / ENNReal.ofReal (‖bchar la b‖ ^ 2)) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, W (lact γ x) = W x

def WLower {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x ∈ X.dom, ENNReal.ofReal (c * Real.exp (-phla X la x)) ≤ W x

def InAt {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (F : V (nd X) → ℂ) :
    Prop :=
  ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) ∂muF X x0 < ⊤

def InFF {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (FF : Set (V (nd X)))
    (f : Frame X.Ψ r → ℂ) : Prop :=
  ∫⁻ z in FF, ENNReal.ofReal (‖f (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z) ∂muF X x0 < ⊤

def PoinStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ),
    IsMetricW X la W → WLower X la W → 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb →
    ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) → InAt X x0 W bb F →
    IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) →
    (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) ∧
    X.IsBddSec la (poin X la P) ∧
    (∀ FF, IsFundSet X x0 FF → InFF X x0 W FF (poin X la P)) ∧
    (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x ∈ X.dom, IsOrth X x →
      ENNReal.ofReal ‖poin X la P x‖ ≤ ENNReal.ofReal C *
        ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom),
          (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ)) ∧
    ∀ (la' : Wt X.Ψ r) (g : Frame X.Ψ r → ℂ), X.IsSec la' g → ∀ x ∈ X.dom,
      poin X (la + la') (fun y => g y * P y) x = g x * poin X la P x

def OntoStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞)
    (Ps : Frame X.Ψ r → ℝ) (g1 : V (nd X) → ℂ) (bb m : ℝ),
    IsMetricW X la W → WLower X la W → 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb →
    bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m →
    DifferentiableOn ℂ g1 (OmF X x0) → (∃ z ∈ OmF X x0, g1 z ≠ 0) →
    ContDiffOn ℝ ∞ (fun z => Ps (cpt X x0 z)) {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} →
    (∀ z, z ∈ OmF X x0 → g1 z ≠ 0 → W (cpt X x0 z) = ENNReal.ofReal (Real.exp (-Ps (cpt X x0 z)))) →
    (∀ z, z ∈ OmF X x0 → g1 z ≠ 0 → ∀ ξ : Fin (nd X) → ℂ,
      m * (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re ≤
        (leviV (nd X) (fun w => ((Ps (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re) →
    (∀ P, X.IsBddSec la P → P ∈ X.SS la) →
    ∀ FF, IsFundSet X x0 FF →
    (∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS la, InFF X x0 W FF f →
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x) →
    ∀ f ∈ X.SS la, InFF X x0 W FF f →
    ∃ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧
      IsBEq X la P ∧ (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) ∧ ∀ x ∈ X.dom, poin X la P x = f x

def CuspStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (τ0 : X.Ψ), 0 < X.p0 → X.p0 < r →
    (∀ i j : Fin r, (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → la τ0 j ≤ la τ0 i) →
    (∀ i0 i1 : Fin r, (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → la τ0 i0 < la τ0 i1) →
    ∀ P, X.IsBddSec la P → P ∈ X.SS la

def RhGradFStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
    Complex.normSq (∑ j, wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) z * ξ j) ≤
      ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) *
        (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re

def ExhaustGStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ g1 : V (nd X) → ℂ,
    DifferentiableOn ℂ g1 (OmF X x0) →
    ∃ S : EtaleStein (nd X) {z | z ∈ OmF X x0 ∧ g1 z ≠ 0},
      S.z = Subtype.val ∧ S.e = fun y => eF X x0 y.1 + (‖g1 y.1‖ ^ 2)⁻¹

def KaUnfoldStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ FF, IsFundSet X x0 FF → ∀ bb : ℝ,
    4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∃ C : ℝ≥0∞, C < ⊤ ∧
    ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
      (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, φ (lact γ x) = φ x) →
      ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * φ (cpt X x0 z) ∂muF X x0 ≤
        C * ∫⁻ z in FF, φ (cpt X x0 z) ∂muF X x0

def PairUnfoldStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ),
    IsMetricW X la W → WLower X la W → 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb →
    ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) → InAt X x0 W bb F →
    IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) →
    ∀ FF, IsFundSet X x0 FF → ∀ f0 ∈ X.SS la, InFF X x0 W FF f0 →
      ∫ z in FF, poin X la P (cpt X x0 z) * (starRingEnd ℂ) (f0 (cpt X x0 z)) *
          ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0 =
        ∫ z, F z * (starRingEnd ℂ) (f0 (cpt X x0 z)) * ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0

def BigCellStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ),
    IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = 0) → ∀ x ∈ X.dom, P x = 0

def OmFConnStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → IsPreconnected (OmF X x0)

def OrthoStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∃ x1, IsOrth X x1 ∧ ∃ b ∈ Bor X.Ψ r, x = rmul x1 b

def VanishAtSStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x1 : Frame X.Ψ r), 0 < nd X → IsOrth X x1 → x1 ∈ X.dom →
    ∀ (u w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ρ : ℝ), 0 < ρ →
    DifferentiableOn ℂ (fun z => u (cpt X x1 z)) (Metric.ball 0 ρ) →
    (∀ k, DifferentiableOn ℂ (fun z => s k (cpt X x1 z)) (Metric.ball 0 ρ)) →
    DifferentiableOn ℂ (fun z => w0 (cpt X x1 z)) (Metric.ball 0 ρ) →
    w0 x1 ≠ 0 → (∀ k, s k x1 = 0) →
    (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      s k (cpt X x1 z) / w0 (cpt X x1 z) : V (nd X))) 0).det ≠ 0 →
    ∫⁻ z in Metric.ball 0 ρ, ENNReal.ofReal (‖u (cpt X x1 z)‖ ^ 2 *
      (∑ k, ‖s k (cpt X x1 z)‖ ^ 2) ^ (-(nd X : ℝ))) < ⊤ →
    u x1 = 0

def LUStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 →
    ∃ (Δ : Frame X.Ψ r → ℂ) (zOf : Frame X.Ψ r → V (nd X)) (bOf : Frame X.Ψ r → Frame X.Ψ r),
      Differentiable ℂ Δ ∧ (∀ x ∈ X.dom, ∀ ε > 0, ∃ y ∈ Metric.ball x ε, Δ y ≠ 0) ∧
      DifferentiableOn ℂ zOf {x | x ∈ X.dom ∧ Δ x ≠ 0} ∧
      DifferentiableOn ℂ bOf {x | x ∈ X.dom ∧ Δ x ≠ 0} ∧
      (∀ x ∈ X.dom, Δ x ≠ 0 → zOf x ∈ OmF X x0 ∧ bOf x ∈ Bor X.Ψ r ∧
        x = rmul (cpt X x0 (zOf x)) (bOf x)) ∧
      ∀ z ∈ OmF X x0, ∀ b ∈ Bor X.Ψ r, Δ (rmul (cpt X x0 z) b) ≠ 0 ∧
        zOf (rmul (cpt X x0 z) b) = z ∧ bOf (rmul (cpt X x0 z) b) = b

def FrameMeasStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ C : Set (Frame X.Ψ r), IsCompact C →
    C ⊆ X.dom → ∃ K : ℝ≥0∞, K < ⊤ ∧
    ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
      ∫⁻ x in C, G x ≤ K * ∫⁻ z in sat X x0 C, G (cpt X x0 z) ∂muF X x0

def FundSetMeasStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))), IsOrth X x0 → IsFundSet X x0 FF →
    (∃ x1, IsOrth X x1 ∧ ∃ CechHodgeFiltration, IsFundSet X x1 CechHodgeFiltration ∧ muF X x1 CechHodgeFiltration < ⊤) → muF X x0 FF < ⊤

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfB
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

noncomputable section

section Mat

variable {n : ℕ}

lemma inv_blockTriangular {α : Type*} [LinearOrder α] {b : Fin n → α} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.BlockTriangular b) (hd : M.det ≠ 0) : (M⁻¹).BlockTriangular b := by
  haveI : Invertible M := M.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hd)
  exact Matrix.blockTriangular_inv_of_blockTriangular hM

lemma det_lowerUni {N : Matrix (Fin n) (Fin n) ℂ} (hN : N.BlockTriangular OrderDual.toDual)
    (h1 : ∀ a, N a a = 1) : N.det = 1 := by
  rw [Matrix.det_of_lowerTriangular N hN]
  simp [h1]

theorem lu_unique {N N' U U' : Matrix (Fin n) (Fin n) ℂ}
    (hN : N.BlockTriangular OrderDual.toDual) (hN1 : ∀ a, N a a = 1)
    (hN' : N'.BlockTriangular OrderDual.toDual) (hN'1 : ∀ a, N' a a = 1)
    (hU : U.BlockTriangular id) (hU' : U'.BlockTriangular id) (hd : U'.det ≠ 0)
    (h : N * U = N' * U') : N = N' ∧ U = U' := by
  first | exact Bl.general_b_fact_form.goal1 .. | (apply Bl.general_b_fact_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_form.goal1 <;> assumption)

lemma lminor_last' (M : Matrix (Fin n) (Fin n) ℂ) : lminor M (Fin.last n) = M.det := by
  rfl

theorem lu_exists {M : Matrix (Fin n) (Fin n) ℂ} (hM : ∀ i : Fin (n + 1), lminor M i ≠ 0) :
    ∃ N U : Matrix (Fin n) (Fin n) ℂ, N.BlockTriangular OrderDual.toDual ∧ (∀ a, N a a = 1) ∧
      U.BlockTriangular id ∧ U.det ≠ 0 ∧ N * U = M := by
  classical
  let A : ∀ r : Fin n, Matrix (Fin r) (Fin r) ℂ := fun r =>
    M.submatrix (Fin.castLE r.isLt.le) (Fin.castLE r.isLt.le)
  have hA : ∀ r : Fin n, IsUnit (A r).det := fun r => isUnit_iff_ne_zero.mpr (hM r.castSucc)
  let x : ∀ r : Fin n, Fin r → ℂ := fun r =>
    -((fun j => M r (Fin.castLE r.isLt.le j)) ᵥ* (A r)⁻¹)
  have hx : ∀ r : Fin n, ∀ j : Fin r,
      ∑ i : Fin r, x r i * M (Fin.castLE r.isLt.le i) (Fin.castLE r.isLt.le j) =
        -M r (Fin.castLE r.isLt.le j) := by
    intro r j
    have hv : x r ᵥ* A r = -(fun j => M r (Fin.castLE r.isLt.le j)) := by
      simp only [x, Matrix.neg_vecMul, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hA r),
        Matrix.vecMul_one]
    have h := congrFun hv j
    simpa [Matrix.vecMul, dotProduct, A] using h

  let L : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun r c =>
    if h : c < r then x r ⟨c, h⟩ else if c = r then 1 else 0
  have hLlow : L.BlockTriangular OrderDual.toDual := by
    intro r c hrc
    have hrc' : r < c := OrderDual.toDual_lt_toDual.mp hrc
    simp [L, not_lt.mpr hrc'.le, hrc'.ne']
  have hL1 : ∀ a, L a a = 1 := fun a => by simp [L]
  have hLdet : L.det = 1 := det_lowerUni hLlow hL1
  have hLu : IsUnit L.det := by rw [hLdet]; exact isUnit_one
  have hrow : ∀ r c : Fin n, c < r → (L * M) r c = 0 := by
    intro r c hcr
    have e1 : ∀ k, L r k * M k c =
        (if h : k < r then x r ⟨k, h⟩ * M k c else 0) + (if k = r then M k c else 0) := by
      intro k
      by_cases h : k < r
      · simp [L, h, h.ne]
      · by_cases h' : k = r
        · subst h'
          simp [L]
        · simp [L, h, h']
    have hsub : ∑ k : Fin n, (if h : k < r then x r ⟨k, h⟩ * M k c else 0) =
        ∑ j : Fin r, x r j * M (Fin.castLE r.isLt.le j) c := by
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb r.isLt.le)))]
      · rw [Finset.sum_map]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj : (Fin.castLEEmb r.isLt.le j) < r := by
          show (j : ℕ) < r
          exact j.isLt
        rw [dite_eq_left hj]
        rfl
      · intro k _ hk
        have hk' : ¬ k < r := by
          intro h
          apply hk
          exact Finset.mem_map.mpr ⟨⟨k, h⟩, Finset.mem_univ _, Fin.ext rfl⟩
        rw [dite_eq_right hk']
    rw [Matrix.mul_apply, Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ r (fun k => M k c), if_pos (Finset.mem_univ _), hsub]
    have h := hx r ⟨c, hcr⟩
    have hc : Fin.castLE r.isLt.le (⟨c, hcr⟩ : Fin r) = c := Fin.ext rfl
    rw [hc] at h
    rw [h]
    ring
  refine ⟨L⁻¹, L * M, inv_blockTriangular hLlow (by rw [hLdet]; exact one_ne_zero), ?_, ?_, ?_, ?_⟩
  · intro a
    have h1 : (L * L⁻¹) a a = 1 := by
      rw [Matrix.mul_nonsing_inv L hLu]
      simp
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
    · rwa [hL1, one_mul] at h1
    · intro k _ hka
      rcases lt_or_gt_of_ne hka with h | h
      · have h0 : L⁻¹ k a = 0 := inv_blockTriangular hLlow (by rw [hLdet]; exact one_ne_zero)
          (OrderDual.toDual_lt_toDual.mpr h)
        rw [h0, mul_zero]
      · have h0 : L a k = 0 := hLlow (OrderDual.toDual_lt_toDual.mpr h)
        rw [h0, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · intro r c hcr
    exact hrow r c hcr
  · rw [Matrix.det_mul, hLdet, one_mul, ← lminor_last']
    exact hM _
  · rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul L hLu, Matrix.one_mul]

end Mat

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def Mt (v : Ix ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => v (τ, a, b)

def BC (ι : Type*) [Fintype ι] (r : ℕ) : Set (Ix ι r → ℂ) := {v | ∀ τ, ∀ i : Fin (r + 1), lminor (Mt v τ) i ≠ 0}

def sS (ι : Type*) (r : ℕ) : Set (Ix ι r → ℂ) := {w | ∀ τ b, w (τ, b, b) ≠ 0}

lemma Mt_lu (w : Ix ι r → ℂ) (τ : ι) : Mt (lu w) τ = (1 + sl w τ) * up w τ := by
  ext a b
  rfl

lemma one_add_sl_low (w : Ix ι r → ℂ) (τ : ι) : (1 + sl w τ).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
  simp [sl, Matrix.one_apply_ne hij'.ne, not_lt.mpr hij'.le]

lemma one_add_sl_diag (w : Ix ι r → ℂ) (τ : ι) (a : Fin r) : (1 + sl w τ) a a = 1 := by
  simp [sl]

lemma up_upper (w : Ix ι r → ℂ) (τ : ι) : (up w τ).BlockTriangular id := by
  intro i j hij
  have hij' : j < i := hij
  simp [up, hij']

lemma det_up (w : Ix ι r → ℂ) (τ : ι) : (up w τ).det = ∏ b, w (τ, b, b) := by
  rw [Matrix.det_of_upperTriangular (up_upper w τ)]
  simp [up]

lemma det_up_ne {w : Ix ι r → ℂ} (hw : w ∈ sS ι r) (τ : ι) : (up w τ).det ≠ 0 := by
  rw [det_up]
  exact Finset.prod_ne_zero_iff.mpr fun b _ => hw τ b

lemma eq_of_sl_up {w w' : Ix ι r → ℂ} (h1 : ∀ τ, sl w τ = sl w' τ) (h2 : ∀ τ, up w τ = up w' τ) : w = w' := by
  funext i
  obtain ⟨τ, a, b⟩ := i
  by_cases hba : b < a
  · have h := congrFun (congrFun (h1 τ) a) b
    simpa [sl, hba] using h
  · have h := congrFun (congrFun (h2 τ) a) b
    simpa [up, hba] using h

theorem lu_injOn : Set.InjOn (lu (ι := ι) (r := r)) (sS ι r) := by
  intro w hw w' hw' h
  have key : ∀ τ, (1 + sl w τ) = (1 + sl w' τ) ∧ up w τ = up w' τ := by
    intro τ
    have hM : (1 + sl w τ) * up w τ = (1 + sl w' τ) * up w' τ := by
      rw [← Mt_lu, ← Mt_lu, h]
    exact lu_unique (one_add_sl_low w τ) (one_add_sl_diag w τ) (one_add_sl_low w' τ)
      (one_add_sl_diag w' τ) (up_upper w τ) (up_upper w' τ) (det_up_ne hw' τ) hM
  exact eq_of_sl_up (fun τ => add_left_cancel (key τ).1) (fun τ => (key τ).2)

theorem BC_subset_image : BC ι r ⊆ lu '' sS ι r := by
  intro v hv
  choose N U hN hN1 hU hUd hNU using fun τ => lu_exists (M := Mt v τ) (hv τ)
  refine ⟨fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2 else U i.1 i.2.1 i.2.2, ?_, ?_⟩
  · intro τ b
    show (if b < b then N τ b b else U τ b b) ≠ 0
    rw [if_neg (lt_irrefl b)]
    intro h0
    have hdet : (U τ).det = ∏ b, U τ b b := Matrix.det_of_upperTriangular (hU τ)
    exact hUd τ (hdet ▸ Finset.prod_eq_zero (Finset.mem_univ b) h0)
  · have hsl : ∀ τ, 1 + sl (fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2
        else U i.1 i.2.1 i.2.2) τ = N τ := by
      intro τ
      ext a b
      rcases lt_trichotomy b a with h | h | h
      · simp [sl, h, Matrix.one_apply_ne (ne_of_gt h)]
      · subst h
        simp [sl, hN1]
      · have h0 : N τ a b = 0 := hN τ (OrderDual.toDual_lt_toDual.mpr h)
        simp [sl, not_lt.mpr h.le, Matrix.one_apply_ne (ne_of_lt h), h0]
    have hup : ∀ τ, up (fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2
        else U i.1 i.2.1 i.2.2) τ = U τ := by
      intro τ
      ext a b
      by_cases h : b < a
      · have h0 : U τ a b = 0 := hU τ h
        simp [up, h, h0]
      · simp [up, h]
    funext i
    obtain ⟨τ, a, b⟩ := i
    show ((1 + sl _ τ) * up _ τ : Matrix (Fin r) (Fin r) ℂ) a b = v (τ, a, b)
    rw [hsl, hup, hNU]
    rfl

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open Matrix
open scoped Matrix ComplexOrder ENNReal

noncomputable section

theorem SumBoundStatement_holds : SumBoundStatement := by
  intro f p q s hs Γ hd hU
  obtain ⟨c, hc, hsepΓ⟩ := sumBd_sep Γ hd hU
  obtain ⟨C, hC, hbound⟩ := sumBd_sum (p := p) (q := q) (f := f) hs hc
  refine ⟨C, hC, fun v hv => ?_⟩
  choose G hG hGw using fun k => sumBd_frame (hv k)
  let x : Γ → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := fun γ k =>
    ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * G k
  have hxU : ∀ a k, IsUpq (x a k) := fun a k => sumBd_isUpq_mul (hU a.1 a.2 k) (hG k)
  have hxsep : ∀ a b : Γ, a ≠ b → ∃ k i j,
      c ≤ ‖(x b k * (x a k)⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ := by
    intro a b hab
    have hmem : b.1 * a.1⁻¹ ∈ Γ := Γ.mul_mem b.2 (Γ.inv_mem a.2)
    have hne : b.1 * a.1⁻¹ ≠ 1 := fun h => hab (Subtype.ext (mul_inv_eq_one.mp h).symm)
    obtain ⟨k, i, j, hk⟩ := hsepΓ _ hmem hne
    refine ⟨k, i, j, le_of_le_of_eq hk ?_⟩
    have : x b k * (x a k)⁻¹ = (((b.1 * a.1⁻¹) k : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
      simp only [x, Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.coe_units_inv]
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (G k), sumBd_mul_inv (hG k), Matrix.one_mul]
    rw [this]
  calc ∑' γ : Γ, ENNReal.ofReal (∏ k, dpow (mob ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Zof v k)) s)
      = ∑' γ : Γ, ENNReal.ofReal (∏ k, (Complex.normSq (det (x γ k).toBlocks₂₂))⁻¹ ^ s) := by
        congr 1; funext γ
        rw [Finset.prod_congr rfl fun k _ => hGw k _ (hU γ.1 γ.2 k) s]
    _ ≤ C := hbound Γ x hxU hxsep

end
end ReciprocityTheory.ChartRestriction.G.AR.Up
end

