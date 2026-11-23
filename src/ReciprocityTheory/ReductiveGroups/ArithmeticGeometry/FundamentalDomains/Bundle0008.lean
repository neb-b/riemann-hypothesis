module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Metric
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

def IsOrtho (x : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

abbrev Coord : Type := X.Ψ → Fin (r - X.p0) → Fin X.p0 → ℂ

def lowBlock (Z : X.Coord) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => (if a = b then 1 else 0) +
    if h : X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0 then
      Z τ ⟨(a : ℕ) - X.p0, by have := a.isLt; omega⟩ ⟨b, h.2⟩ else 0

def xZ (x : Frame X.Ψ r) (Z : X.Coord) : Frame X.Ψ r :=
  fun τ => (mat x τ * X.lowBlock Z τ : Matrix (Fin r) (Fin r) ℂ)

def opN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  sSup {t | ∃ v : Fin n → ℂ, v ≠ 0 ∧
    t = Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)}

def zN (Z : X.Coord) : ℝ := ⨆ τ : X.Ψ, opN (Matrix.of (Z τ))

end Data

def OrthonormalFlagTranslate : Prop :=
  ∀ (r : ℕ) (X : Data E r),
    (∀ x ∈ X.dom, ∃ b ∈ Bor X.Ψ r, X.IsOrtho (rmul x b)) ∧
    (∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ),
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x) →
      ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, X.pnorm la P (rmul x b) = X.pnorm la P x) ∧
    ∀ x ∈ X.dom, ∀ x' ∈ X.dom, X.SameFlag x x' → (∀ ξ : Fin r → E,
      X.Jz x = X.Jz x' ∧ X.Uz x ξ = X.Uz x' ξ ∧ X.aproj x ξ = X.aproj x' ξ) ∧ X.maj x = X.maj x'

def OrthonormalChartNormControl : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), x ∈ X.dom → X.IsOrtho x → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 10 →
    (∀ Z : X.Coord, X.zN Z ≤ ρ →
      X.xZ x Z ∈ X.dom ∧
      (∀ (la : Wt X.Ψ r) (w : ℝ), (∑ τ, X.spread la τ) ≤ w →
        |Real.log (X.nfac la (X.xZ x Z)) - Real.log (X.nfac la x)| ≤ 4 * w * r * X.zN Z ^ 2) ∧
      ∀ τ v, (1 - ρ) / (1 + ρ) * X.maj x τ v ≤ X.maj (X.xZ x Z) τ v ∧
        X.maj (X.xZ x Z) τ v ≤ (1 + ρ) / (1 - ρ) * X.maj x τ v) ∧
    ∀ G : Frame X.Ψ r → ℂ, DifferentiableOn ℂ G X.dom →
      DifferentiableOn ℂ (fun Z : X.Coord => G (X.xZ x Z)) {Z | X.zN Z < ρ}

def NearSupremumTransference : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 →
    ∀ x' ∈ X.dom, (∀ τ, (1 - d6rh c1 w) / (1 + d6rh c1 w) ≤ X.tt ξ x' τ ∧
      X.tt ξ x' τ ≤ (1 + d6rh c1 w) / (1 - d6rh c1 w)) →
    X.hatN la (X.fj la ξ ν P) x' ≤
      Real.exp 2 * sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y}

def SchwarzLemmaBall : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (γ : V → ℂ) (ρ S : ℝ), 0 < ρ →
    DifferentiableOn ℂ γ (closedBall 0 ρ) → (∀ Z ∈ closedBall (0 : V) ρ, ‖γ Z‖ ≤ Real.exp (9 / 4) * S) →
    S / 2 < ‖γ 0‖ → ‖γ 0‖ ≤ S → ∀ Z ∈ ball (0 : V) (ρ / 21), γ Z ≠ 0

def SplitData {r : ℕ} (X : DataX E r) (ξ : Fin r → E) (La : ℝ) (z : Frame X.Ψ r)
    (lam : Fin (r - 2) → Fin r → E) : Prop :=
  (∀ j, lam j ∈ X.L' ∧ herm X.Gm (lam j) ξ = 0) ∧
  LinearIndependent E (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E) ∧
  (∀ j k : Fin (r - 2), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) → herm X.Gm (lam j) (lam k) = 0) ∧
  (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → (∀ τ : X.Ψ, 0 < (τ.1 (herm X.Gm (lam j) (lam j))).re) ∧
    X.Jz z (X.ucomp z ξ (X.embV (lam j))) = I • X.ucomp z ξ (X.embV (lam j))) ∧
  (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → (∀ τ : X.Ψ, (τ.1 (herm X.Gm (lam j) (lam j))).re < 0) ∧
    X.Jz z (X.ucomp z ξ (X.embV (lam j))) = -(I • X.ucomp z ξ (X.embV (lam j)))) ∧
  ∀ j (τ : X.Ψ), ‖τ.1 (herm X.Gm (lam j) (lam j))‖ ≤ La ^ 2

def OrthonormalShortVectorBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 →
    ∀ x0 ∈ X.dom, X.IsOrtho x0 → X.SameFlag z0 x0 →
    ∃ (lam : Fin (r - 2) → Fin r → E) (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (Z1 : X.Coord),
      X.IsUnitaryC h1 ∧
      (∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
        X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) ∧
      (∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ) ∧
      SplitData X ξ (d6La r X.p0 (fdeg E) (dE E) (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w) (d6rh c1 w))
        (X.lmulC h1 z0) lam ∧
      X.SameFlag (X.lmulC h1 z0) (X.xZ x0 Z1) ∧ X.zN Z1 ≤ d6rh c1 w / 100

def IsotropicCoefficientSplitting : Prop :=
  ∀ (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ →
    ∃ f : (Fin r → E) → E, (∀ μ ∈ X.Λp ξ, f μ • ξ ∈ X.Λ) ∧
      (∀ μ ∈ X.Λp ξ, ∀ μ' ∈ X.Λp ξ, f (μ + μ') = f μ + f μ') ∧
      (∀ (α : 𝓞 E), ∀ μ ∈ X.Λp ξ, f ((α : E) • μ) = α * f μ) ∧
      ∀ e : E, e • ξ ∈ X.Λ → f (e • ξ) = e

def NoShortVectorLowerBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (ep0 : ℝ), X.IsIso ξ → 0 < ep0 → ∀ z ∈ X.FramesOverBasis ξ,
    (∀ x ∈ X.L', herm X.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : X.Ψ, ep0 ≤ X.maj z τ (X.ucomp z ξ (X.embV x) τ)) →
    ∀ δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ, ∃ μ ∈ X.Λp ξ, ∀ u ∈ X.Uz z ξ, ∀ τ : X.Ψ,
      X.maj z τ ((δ τ (u τ) - (dE E : ℂ) * (-τ.1 X.ξ0) *
          hermC τ.1 X.Gm (u τ) (X.ucomp z ξ (X.embV μ) τ)) • Data.emb τ.1 ξ) ≤
        frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0 ^ 2 * X.maj z τ (u τ)

def UnitaryUnipotentMove : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 →
    ∀ x0 ∈ X.dom, X.IsOrtho x0 → X.SameFlag z0 x0 →
    ∀ (lam : Fin (r - 2) → Fin r → E) (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (Z1 : X.Coord),
      X.IsUnitaryC h1 →
      (∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
        X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) →
      (∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ) →
      SplitData X ξ (d6La r X.p0 (fdeg E) (dE E) (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w) (d6rh c1 w))
        (X.lmulC h1 z0) lam →
      X.SameFlag (X.lmulC h1 z0) (X.xZ x0 Z1) → X.zN Z1 ≤ d6rh c1 w / 100 →
      ∀ n' : ℕ, 1000 * frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC
          (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w) / d6rh c1 w ≤ n' →
      ∃ (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (Z : X.Coord),
        X.IsUnitaryC n ∧ (∀ τ, Matrix.mulVec (n τ) (Data.emb τ.1 ξ) = Data.emb τ.1 ξ) ∧
        (∀ μ ∈ X.Λp ξ, ∃ e : E, e • ξ ∈ X.Λ ∧
          (n' : ℂ) • X.aproj (X.lmulC n (X.lmulC h1 z0)) ξ (X.embV μ) = X.embV (e • ξ)) ∧
        SplitData X ξ (d6La r X.p0 (fdeg E) (dE E) (flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w)
          (d6rh c1 w)) (X.lmulC n (X.lmulC h1 z0)) lam ∧
        X.SameFlag (X.lmulC n (X.lmulC h1 z0)) (X.xZ x0 Z) ∧ X.zN Z < d6rh c1 w / 21

end

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantFamilyNorms
section
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open scoped ComplexConjugate
noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} (X : Data E r)

theorem hG_of (τ : X.Ψ) : ∀ a b, τ.1 (X.Gm b a) = conj (τ.1 (X.Gm a b)) := by
  intro a b
  rw [← X.Gm_herm a b]
  first
    | simp [NumberField.IsCMField.complexEmbedding_complexConj]
    | rw [NumberField.IsCMField.complexEmbedding_complexConj]
    | simp [NumberField.IsCMField.complexConj_apply]
    | simp [NumberField.IsCMField.conj_complexEmbedding]
    | (simp only [cc]
       exact NumberField.IsCMField.complexEmbedding_complexConj ..)

theorem c_pos (τ : X.Ψ) : 0 < X.c τ := by
  unfold Data.c
  have h : (τ.1 X.ξ0) ≠ 0 := (map_ne_zero τ.1).mpr X.ξ0_ne
  have := norm_pos_iff.mpr h
  linarith

theorem hsg_of {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    ∀ i (h : i ≤ r), 0 < psgn X.p0 i * (gramF τ.1 X.Gm (famN (mat x τ) i h)).det.re := by
  intro i h
  unfold Data.dom GG at hx
  simp only [Set.mem_setOf_eq] at hx
  have h1 := (hx τ).2 ⟨i, Nat.lt_succ_of_le h⟩
  first
    | exact h1
    | (unfold dmin lminor gram gramF famN at h1
       exact h1)

theorem dmin_eq (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i = (gramF τ.1 X.Gm (famN (mat x τ) i (Nat.le_of_lt_succ i.isLt))).det := rfl

theorem famN_flow (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) (i : ℕ)
    (h : i ≤ r) : famN (mat (X.flowV e s x) τ) i h =
      flw (-I * X.c τ * s τ) (e τ) τ.1 X.Gm (famN (mat x τ) i h) := by
  unfold Data.flowV flw famN mat
  funext a c
  show ∑ b, X.flowMatV (e τ) τ (s τ) c b * x τ b (Fin.castLE h a) =
    x τ c (Fin.castLE h a) + (-I * (X.c τ : ℂ) * s τ *
      hermC τ.1 X.Gm (fun d => x τ d (Fin.castLE h a)) (e τ)) * e τ c
  unfold Data.flowMatV hermC
  simp only [Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem alpha_re (c : ℝ) (s : ℂ) : (-I * (c : ℂ) * s) + conj (-I * (c : ℂ) * s) =
    ((2 * c * s.im : ℝ) : ℂ) := by
  apply Complex.ext <;> simp <;> ring

theorem det_flowMat (e : Fin r → ℂ) (τ : X.Ψ) (s : ℂ) (he : hermC τ.1 X.Gm e e = 0) :
    (X.flowMatV e τ s).det = 1 := by
  unfold Data.flowMatV hermC at *
  have key : (of fun a b => (if a = b then (1 : ℂ) else 0) - I * (X.c τ : ℂ) * s * e a *
      ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) =
      1 + replicateCol Unit (fun a => -(I * (X.c τ : ℂ) * s * e a)) *
        replicateRow Unit (fun b => ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) := by
    ext a b
    simp [Matrix.one_apply, Matrix.mul_apply, sub_eq_add_neg]
  have hd : (fun b => ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) ⬝ᵥ
      (fun a => -(I * (X.c τ : ℂ) * s * e a)) = 0 := by
    calc (fun b => ∑ k, τ.1 (X.Gm b k) * (starRingEnd ℂ) (e k)) ⬝ᵥ
          (fun a => -(I * (X.c τ : ℂ) * s * e a))
        = -(I * (X.c τ : ℂ) * s) * ∑ a, ∑ b, e a * τ.1 (X.Gm a b) * (starRingEnd ℂ) (e b) := by
          simp only [dotProduct]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = 0 := by rw [he, mul_zero]
  rw [key, det_one_add_replicateCol_mul_replicateRow, hd, add_zero]

section Prof
variable {x : Frame X.Ψ r} (hx : x ∈ X.dom) (e : X.Ψ → Fin r → ℂ) (τ : X.Ψ)
include hx

theorem mt_famN (i : ℕ) (h : i ≤ r) : GramDeterminantReal.mt τ.1 X.Gm (famN (mat x τ) i h) (e τ) =
    (mN τ.1 X.Gm (mat x τ) (e τ) i : ℂ) := by
  rw [mt_eq (hG_of X τ) _ _ (unit_of X.p0 (mat x τ) (hsg_of X hx τ) i h), mN, pN, dite_eq_left h]
  exact Complex.ext rfl (by simp [hC_self_real (hG_of X τ)])

theorem dmin_flow (he : hermC τ.1 X.Gm (e τ) (e τ) = 0) (s : X.Ψ → ℂ) (i : ℕ) (h : i ≤ r) :
    (gramF τ.1 X.Gm (famN (mat (X.flowV e s x) τ) i h)).det =
      (gramF τ.1 X.Gm (famN (mat x τ) i h)).det *
        ((1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) i : ℝ) : ℂ) := by
  rw [famN_flow, det_flw (hG_of X τ) (e τ) he _ _ (unit_of X.p0 (mat x τ) (hsg_of X hx τ) i h),
    mt_famN X hx e τ i h, alpha_re]
  push_cast; ring

theorem maj_eq (he : hermC τ.1 X.Gm (e τ) (e τ) = 0) :
    X.maj x τ (e τ) = 2 * mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := by
  have : X.posPart x τ (e τ) = (GramDeterminantReal.mt τ.1 X.Gm (famN (mat x τ) X.p0 X.p0_le) (e τ)).re := rfl
  rw [Data.maj, this, mt_famN X hx e τ X.p0 X.p0_le, he, Complex.ofReal_re, Complex.zero_re, sub_zero]

theorem maj_flow (he : hermC τ.1 X.Gm (e τ) (e τ) = 0) (s : X.Ψ → ℂ)
    (h1 : 1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0 ≠ 0) :
    X.maj (X.flowV e s x) τ (e τ) = 2 * (mN τ.1 X.Gm (mat x τ) (e τ) X.p0 /
      (1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0)) := by
  have hα := alpha_re (X.c τ) (s τ)
  have hp : X.posPart (X.flowV e s x) τ (e τ) =
      (GramDeterminantReal.mt τ.1 X.Gm (famN (mat (X.flowV e s x) τ) X.p0 X.p0_le) (e τ)).re := rfl
  rw [Data.maj, hp, famN_flow, mt_flw (hG_of X τ) (e τ) he _ _
    (unit_of X.p0 (mat x τ) (hsg_of X hx τ) X.p0 X.p0_le), hα, mt_famN X hx e τ X.p0 X.p0_le, he,
    Complex.zero_re, sub_zero]
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_div,
      Complex.ofReal_re]
  · rw [hα, mt_famN X hx e τ X.p0 X.p0_le, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_add]
    exact_mod_cast h1

end Prof

end

end ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceFormIndependence
section
namespace ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma add_conj' (w : ℂ) : w + conj w = 2 * (w.re : ℂ) := by
  apply Complex.ext <;> simp <;> ring

lemma trace_re (X : Data E r) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ : X.Ψ, 2 * (τ.1 z).re := by
  classical
  apply Complex.ofReal_injective
  have hall : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ z := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := z)
    have h' : (algebraMap ℚ ℂ) (Algebra.trace ℚ E z) = ((Algebra.trace ℚ E z : ℚ) : ℂ) :=
      eq_ratCast _ _
    rw [← h', h]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)
  have hcc : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
  have hconj : ∑ σ ∈ X.Ψᶜ, σ z = ∑ σ ∈ X.Ψ, conj (σ z) := by
    apply Finset.sum_nbij' (fun σ => ComplexEmbedding.conjugate σ)
      (fun σ => ComplexEmbedding.conjugate σ)
    · intro σ hσ
      simp only [Finset.mem_compl, Finset.mem_coe] at hσ ⊢
      rw [X.cmType, hcc]
      exact hσ
    · intro σ hσ
      simp only [Finset.mem_compl, Finset.mem_coe] at hσ ⊢
      exact (X.cmType σ).mp hσ
    · intro σ _
      exact hcc σ
    · intro σ _
      exact hcc σ
    · intro σ _
      simp [ComplexEmbedding.conjugate_coe_eq]
  push_cast
  rw [hall, ← Finset.sum_add_sum_compl X.Ψ, hconj, ← Finset.sum_add_distrib,
    ← Finset.sum_coe_sort X.Ψ]
  exact Finset.sum_congr rfl fun τ _ => add_conj' _

end ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
end

