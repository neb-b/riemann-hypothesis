module

public import Mathlib
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.HermitianLattices.Bundle0003
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0001
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff ENNReal
open Formalism.MainNotions.S

noncomputable section

namespace Formalism.MainNotions.CayleySignature

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def lam48 (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Fin (2 * r + k + 1) → ℝ :=
  fun i => if h : i.val < k - 1 then v ⟨i.val, h⟩
    else -b ⟨i.val - (k - 1), by have := i.isLt; omega⟩

def eps48 (k r : ℕ) : Fin (2 * r + k + 1) → Bool :=
  fun i => if i.val < k - 1 then true else decide ((i.val - (k - 1)) % 2 = 0)

def InterlacingCondition (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  (∀ i : Fin (k - 1), v i < u ⟨i.val, by have := i.isLt; omega⟩ ∧
      u ⟨i.val + 1, by have := i.isLt; omega⟩ < v i) ∧
    ∀ h : 0 < k, -b ⟨0, by omega⟩ < u ⟨k - 1, by omega⟩

def HalfIntegralDifference (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ i s, ∃ j : ℤ, u i - lam48 k r v b s = (j : ℝ) + 1 / 2

def rk48 (k r : ℕ) : ℕ := 2 * r + k + 1

def GapBig (k r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∃ t : ℕ, Odd t ∧ rk48 k r + 5 ≤ t ∧ 1801 ≤ rk48 k r + t ∧
    ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      2 * ((rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 < b ⟨j.val + 1, hj⟩ - b j

def GapC (C : ℝ) (k r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
    C * (rk48 k r : ℝ) ^ 3 < b ⟨j.val + 1, hj⟩ - b j

def LowGapGe (h : ℝ) (r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2), h ≤ b ⟨j.val + 1, hj⟩ - b j

def RealPlaceNumericalSetting (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ)
    (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  1 ≤ k ∧ Even k ∧ Formalism.QuantumDeterminants.inWb k r z ∧ 0 < Formalism.QuantumDeterminants.Tz k r z ∧ (∀ a, c a ≠ 0) ∧
    Formalism.QuantumDeterminants.IsHCParam u ∧ Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) ∧ InterlacingCondition k r u v b ∧
    HalfIntegralDifference k r u v b ∧ GapBig k r b

end Formalism.MainNotions.CayleySignature
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
section
noncomputable section

namespace Formalism.MainNotions.PlaceDegreeData

open MeasureTheory NumberField Matrix Finset IsDedekindDomain
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S

def qOf {n : ℕ} (ε : Fin n → Bool) : ℕ := (univ.filter fun a => ε a = false).card

def pOf {n : ℕ} (ε : Fin n → Bool) : ℕ := (univ.filter fun a => ε a = true).card

def decBound {n : ℕ} (q : ℕ) (h : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.exp (-(h / 8) * min (Formalism.REAL.hs X) (Real.sqrt (Formalism.REAL.hs X) / Real.sqrt (2 * (q : ℝ))))

def fdegAll (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (w : ∀ v, H v) : ℝ :=
  ∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)

def HidaSetting (I : AutInst) (n₀ : ℕ) (A b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ)
    (μf : Measure I.Gf) (g g₀ : ℕ) (e : I.Gf → ℂ) : Prop :=
  n₀ ≤ I.n ∧ (∃ p q : ℕ, (∀ v, I.pAt v = p ∧ I.qAt v = q) ∧ q ^ 2 ≤ I.n) ∧ 2 ≤ b ∧
    Real.log (Real.log I.rd) ≤ I.n ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (lam v)) ∧ (∀ v a, |lam v a| ≤ b ^ 2) ∧
    I.IsAdmIdem μf g g₀ e ∧ 1 ≤ g ∧ (g : ℝ) ≤ b ^ A ∧ g₀.Prime ∧ 4 * I.n < g₀ ∧ SplitsCompl I.E g₀

def q0At (I : AutInst) (v : InfinitePlace I.F) : ℕ := min (I.pAt v) (I.qAt v)

section HC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end HC

def CountData (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (lam : InfinitePlace I.F → Fin I.n → ℝ)
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs))
    (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (e : I.Gf → ℂ)
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) : Prop :=
  (∀ v, IsDS (I.ε v) (lam v) (σ v)) ∧ (∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v)) ∧
    I.IsHilbTensor σ σs tens ∧ μf.IsHaarMeasure ∧ I.IsFundDom (I.muA μf) fund ∧
    I.IsRightReg μf fund R ∧ I.IsRConvF μf fund R e Re

def phA {G : Type*} [Group G] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (d : ℝ)
    (σ : G →* (H →L[ℂ] H)) (w : H) : G → ℂ :=
  fun g => (d : ℂ) * star ⟪w, σ g w⟫_ℂ

def IsOpIntA {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G) {Hp : Type*} [NormedAddCommGroup Hp]
    [InnerProductSpace ℂ Hp] (π : G →* (Hp →L[ℂ] Hp)) (φ : G → ℂ) (P : Hp →L[ℂ] Hp) : Prop :=
  Integrable φ μ ∧ ∀ x y : Hp, ⟪x, P y⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ

def PointsLemma (_D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ)
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ),
    HidaSetting I n₀ A b lam μf g g₀ e → CountData I lam σ w σs tens μf fund R e Re →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) →
    C * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ h →
    Real.log (I.f : ℝ) ≤ Real.sqrt (I.n : ℝ) →
    Real.log (Real.log b) ≤ cb * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) →
    |(I.Dcount σs μf fund R Re : ℝ) - I.Dstar (fdegAll I σ w) μf fund e| ≤
      Real.exp (-c * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) * I.Dstar (fdegAll I σ w) μf fund e

def RowsTie (D : Formalism.BasicNotions.D7) (X : RowsAut) : Prop :=
  (∃ pl : InfinitePlace X.I.F ≃ D.what₂.Tau, AutTie D X pl) ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (X.lam v)) ∧
    (SplitsCompl D.host.E (D.host.g 0) → SplitsCompl X.I.E X.g₀)

end Formalism.MainNotions.PlaceDegreeData
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.ThinScalesBound
section
noncomputable section

open ValuativeRel MeasureTheory ComplexConjugate ComplexOrder
open Formalism.MainNotions.S.Loc

namespace Formalism.MainNotions.ThinScalesBound


open scoped Classical in
def ThOK {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (m : ℕ) (s : ℕ+) (N : ℕ) (h : Fin N → Pt E m)
    (Th : E ⧸ M.Rsub → Fin N → Fin N → ℂ) : Prop :=
  let N0 := M.Kk m
  let Ns (t : Eˣ) (p q : Pt E m) :=
    ((M.modK ((t : E) * t) ^ ((s : ℕ) * ((s : ℕ) - 1) / 2) : ℝ) : ℂ) *
      M.Kk (m + s) (p.snoc t s) (q.snoc t s)

  (∀ x, (Matrix.of fun a b => Th x a b).PosSemidef) ∧

  (∀ x a b, M.detMod (h a) ≠ M.detMod (h b) → Th x a b = 0) ∧

  (∃ Λ : Submodule M.R E, IsCompact (Λ : Set E) ∧ IsOpen (Λ : Set E) ∧
    ∀ t ∉ Λ, ∀ a b, Th (Submodule.Quotient.mk t) a b = 0) ∧

  (∀ t : Eˣ, (Matrix.of fun a b => Th (Submodule.Quotient.mk (t : E)) a b -
      Ns t (h a) (h b)).PosSemidef) ∧

  (∀ c : ℝ, (Matrix.of fun (a b : {a : Fin N // M.detMod (h a) = c}) =>
      ((c⁻¹ ^ (2 * (s : ℕ)) : ℝ) : ℂ) * N0 (h a) (h b) - ∑' x : E ⧸ M.Rsub, Th x a b).PosSemidef) ∧

  ((s : ℕ) = 1 →
    (∀ (t : Eˣ) a b, Th (Submodule.Quotient.mk (t : E)) a b = Ns t (h a) (h b)) ∧
    ∀ a b, M.detMod (h a) = M.detMod (h b) →
      ∑' x : E ⧸ M.Rsub, Th x a b = ((M.detMod (h a))⁻¹ ^ 2 : ℝ) * N0 (h a) (h b)) ∧

  ((∀ a, M.InGLR (h a)) →
    (∀ a b, N0 (h a) (h b) = 1) ∧
    ∀ x, (Matrix.of fun a b => (if x = 0 then (1 : ℂ) else 0) * N0 (h a) (h b) -
      Th x a b).PosSemidef)

def FamilyTheoremThreePassage {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (g : SplitG M.L), M.split = some g →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t : Term V M r), H.IsTerm t →
  ∀ nn ∈ H.NGrp t.abelian₂ t.f, ∀ nn' ∈ H.NGrp t.abelian₂ t.f',
    (∀ x ∈ t.abelian₂, nn x - nn' x ∈ H.smulLat (algebraMap F E (g.q : F)) t.abelian₂) →
    ∃ uL uU : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      (∀ a b, uL a b ∈ M.R ∧ uU a b ∈ M.R) ∧
      (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      H.ZZplus ⟨t.abelian₂, fun a => nn (t.f a), fun a => nn' (t.f' a), t.T, t.T'⟩ =
        uL * H.ZZplus t * uU

def FrameK {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f : Fin (r + 1) → V) (T : F) : Prop :=
  (∀ a b : Fin (r + 1), (a ≠ Fin.last r ∨ b ≠ Fin.last r) → H.h (f a) (f b) = 0) ∧
    H.h (f (Fin.last r)) (f (Fin.last r)) = - algebraMap F E T

def FamilyLocalModel {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r), H.IsGeneric t₁ →
  ∀ (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'),
    FrameK H f₂ t₁.T → FrameK H f₂' t₁.T' →
    H.Ident t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' →
    H.SendsTo φ.toLinearMap 1 1 (t₁.f (Fin.last r)) (f₂ (Fin.last r)) →
    H.SendsTo φ'.toLinearMap 1 1 (t₁.f' (Fin.last r)) (f₂' (Fin.last r)) →
  let S : Set (Submodule M.L.O V) := {Λ₂ | H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
    H.Respects t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ'}
  let P₁ := H.ZZplus t₁
  let P₂ := HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T'
  (H.Dl t₁.f t₁.f' r = 0 →
    ∀ (Z₁ Z₂ : M.Mat (r + 1)), Z₁.Z.map M.R.subtype = P₁ → Z₂.Z.map M.R.subtype = P₂ →
      Nat.card S = M.nIso Z₁ Z₂) ∧
  (IsUnit (H.Dl t₁.f t₁.f' r) →
    ∀ (Y₁ Y₂ : M.Mat r) (be₁ be₂ al₁ al₂ : Fin r → M.R),
      (∀ a b : Fin r, (Y₁.Z a b : E) = P₁ a.castSucc b.castSucc ∧
        (Y₂.Z a b : E) = P₂ a.castSucc b.castSucc) →
      (∀ a : Fin r, (be₁ a : E) = P₁ a.castSucc (Fin.last r) ∧ (be₂ a : E) = P₂ a.castSucc (Fin.last r) ∧
        (al₁ a : E) = P₁ (Fin.last r) a.castSucc ∧ (al₂ a : E) = P₂ (Fin.last r) a.castSucc) →
      Nat.card S = M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂)

def AllLoc (P : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E],
    Model F E → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK → P M

def T2 (D : Formalism.BasicNotions.D7) : Prop := AllLoc (fun M => FamilyLocalModel M D.R.rS D.R.r)

end Formalism.MainNotions.ThinScalesBound

end
end

