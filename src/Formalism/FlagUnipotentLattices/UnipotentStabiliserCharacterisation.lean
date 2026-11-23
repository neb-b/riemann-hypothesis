module

public import Mathlib
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.FormalDegreeBessel.StatementG

@[expose] public section

namespace Formalism.HermitianLatticeCounting.ExpansionTerms

section PartA
open Finset Real MeasureTheory NumberField

noncomputable def TruncationCutoff (K L t : ℝ) : ℝ := if t = 0 then 1 else min 1 ((L / t) ^ K)

def CenteredPolydisc {ι : Type} (ro : ℝ) (D : ι → ℂ) : Set (ι → ℂ) := {x | ∀ v, ‖x v - D v‖ < ro / 2}

def IsNormSeparated {ι : Type} [Fintype ι] (ro : ℝ) (S : Finset (ι → ℂ)) : Prop :=
  ∀ D ∈ S, ∀ D' ∈ S, D ≠ D' → ro ^ Fintype.card ι ≤ ∏ v, ‖D v - D' v‖

def SeparatedPolydiscsDisjoint : Prop :=
  ∀ (ι : Type) [Fintype ι] (ro : ℝ) (D D' : ι → ℂ), 0 < ro → D ≠ D' →
    ro ^ Fintype.card ι ≤ ∏ v, ‖D v - D' v‖ → Disjoint (CenteredPolydisc ro D) (CenteredPolydisc ro D')

def IdealNormProductLowerBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), aa ≠ 0 → ∀ x : E, x ∈ aa → x ≠ 0 →
      √(FractionalIdeal.absNorm aa : ℝ) ≤ ∏ w : InfinitePlace E, w x

def AlgebraicIntegerNormGeOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : 𝓞 K), x ≠ 0 →
    (1 : ℝ) ≤ ∏ w : InfinitePlace K, w (x : K) ^ w.mult

def InversePowerIntegralPi : Prop :=
  Integrable (fun x : ℂ => ((1 + ‖x‖ ^ 2) ^ 2)⁻¹) ∧ ∫ x : ℂ, ((1 + ‖x‖ ^ 2) ^ 2)⁻¹ = π

def SeparatedSetSumBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (ro : ℝ) (S : Finset (ι → ℂ)), 0 < ro → ro ≤ 1 → IsNormSeparated ro S →
    ∑ D ∈ S, ∏ v, ((1 + ‖D v‖ ^ 2) ^ 2)⁻¹ ≤ (16 / ro ^ 2) ^ Fintype.card ι

def IdealInversePowerSum : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), aa ≠ 0 → (FractionalIdeal.absNorm aa : ℝ) ≤ 1 →
    ∀ S : Finset E, (∀ D ∈ S, D ∈ aa) →
      ∑ D ∈ S, ∏ w : InfinitePlace E, ((1 + (w D) ^ 2) ^ 2)⁻¹ ≤
        16 ^ Fintype.card (InfinitePlace E) / (FractionalIdeal.absNorm aa : ℝ)

def CutoffIntegralFormula : Prop :=
  ∀ K L : ℝ, 2 < K → 0 < L →
    Integrable (fun x : ℂ => TruncationCutoff K L ‖x‖) ∧ ∫ x : ℂ, TruncationCutoff K L ‖x‖ = π * L ^ 2 * (K / (K - 2))

def SeparatedCutoffSum : Prop :=
  ∀ (ι : Type) [Fintype ι] (ro K : ℝ) (abelian₂ : ι → ℝ) (S : Finset (ι → ℂ)), 0 < ro → 2 < K →
    (∀ v, 0 < abelian₂ v) → IsNormSeparated ro S →
    ∑ sg ∈ S, ∏ v, TruncationCutoff K (abelian₂ v) ‖sg v‖ ≤
      ∏ v, (4 * (3 / 2 : ℝ) ^ K * (K / (K - 2)) * (max ro (abelian₂ v)) ^ 2 / ro ^ 2)

def GaussianLatticeCutoffSum : Prop :=
  ∀ (K abelian₂ : ℝ), 2 < K → 0 < abelian₂ → ∀ S : Finset GaussianInt,
    ∑ a ∈ S, TruncationCutoff K abelian₂ ‖(abelian₂ : ℂ) * GaussianInt.toComplex a‖ ≤ 4 * (3 / 2 : ℝ) ^ K * (K / (K - 2))

def ParitySign (s : ℕ) : ℤ := (-1) ^ (s * (s - 1) / 2)

def IndexedMinorEntry {F : Type} [Field F] {p : ℕ} (s : Fin p → ℕ) (t : Fin p → F) (a : Fin p) : F :=
  ∏ a' ∈ univ.filter (fun a' : Fin p => a' ≤ a), ((ParitySign (s a') : ℤ) : F) * t a' ^ s a'

def CompositionBlockProdBound : Prop :=
  ∀ (n : ℕ) (c : Composition n), ((c.blocks.prod : ℕ) : ℝ) ≤ Real.exp ((n : ℝ) / Real.exp 1)

def BlockEndMinorFibreFinite : Prop :=
  ∀ (F : Type) [Field F] (p : ℕ) (s : Fin p → ℕ) (d : Fin p → F) (T : Finset (Fin p → F)),
    (∀ a, 1 ≤ s a) → (∀ t ∈ T, (∀ a, t a ≠ 0) ∧ ∀ a, IndexedMinorEntry s t a = d a) → T.card ≤ ∏ a, s a

noncomputable def blockMinorWeight {E : Type} [Field E] [NumberField E] {r : ℕ}
    (γ : Σ c : Composition (r + 1), (Fin c.length → E)) : ℝ :=
  ∏ a : Fin γ.1.length, ∏ w : InfinitePlace E, (1 + (w (IndexedMinorEntry γ.1.blocksFun γ.2 a)) ^ 2) ^ 2

def BlockEndMinorsIntegral {E : Type} [Field E] {r : ℕ} (γ : Σ c : Composition (r + 1), (Fin c.length → E)) : Prop :=
  ∀ a : Fin γ.1.length, IsIntegral ℤ (IndexedMinorEntry γ.1.blocksFun γ.2 a) ∧ IndexedMinorEntry γ.1.blocksFun γ.2 a ≠ 0

def BlockMinorSumExplicit : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (r : ℕ)
    (S : Finset (Σ c : Composition (r + 1), (Fin c.length → E))), (∀ γ ∈ S, BlockEndMinorsIntegral γ) →
      ∑ γ ∈ S, (blockMinorWeight γ)⁻¹ ≤ 2 ^ r * Real.exp (((r : ℝ) + 1) / Real.exp 1) *
        16 ^ (Fintype.card (InfinitePlace E) * (r + 1))

def BlockMinorSumPowSixtyFour : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (r : ℕ)
    (S : Finset (Σ c : Composition (r + 1), (Fin c.length → E))), (∀ γ ∈ S, BlockEndMinorsIntegral γ) →
      ∑ γ ∈ S, (blockMinorWeight γ)⁻¹ ≤ 64 ^ (Fintype.card (InfinitePlace E) * (r + 1))

def ProdMaxInvLeProdMax : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : ι → ℝ), (∀ v, 0 < G v) → 1 ≤ ∏ v, G v →
    ∏ v, max 1 (1 / G v) ≤ ∏ v, max 1 (G v)

def NormGeOneMaxBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : ι → ℝ) (D : ι → ℂ) (A : ℕ), (∀ v, 0 < G v) → 1 ≤ ∏ v, G v →
    (∀ v, G v ≤ ‖D v‖ ^ 2) →
    ∏ v, max 1 (1 / G v) ^ A ≤ ∏ v, max 1 (G v) ^ A ∧
      ∏ v, max 1 (G v) ^ A ≤ ∏ v, (1 + ‖D v‖ ^ 2) ^ A

def SesquilinearTriangleBound : Prop :=
  ∀ (V ι : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (s : Finset ι) (a : ι → ℂ)
    (x : ι → V) (KK : ℝ), (∀ u v, B u v = star (B v u)) → (∀ u, 0 ≤ (B u u).re) →
    (∀ i ∈ s, (B (x i) (x i)).re ≤ KK) →
    (B (∑ i ∈ s, a i • x i) (∑ i ∈ s, a i • x i)).re ≤ (∑ i ∈ s, ‖a i‖) ^ 2 * KK

def MomentUpwardHolder : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (r q : ℕ)
    (l : Fin (r + 1) → Ω → ℝ) (H0 R : ℝ),
    (∀ a, Measurable (l a)) → (∀ a ω, 0 < l a ω) → 0 ≤ H0 → 0 ≤ R →
    (∀ q' ≤ (r + 1) * q, ∫⁻ ω, ENNReal.ofReal (l 0 ω ^ (2 * q')) ∂μ ≤ ENNReal.ofReal (H0 ^ (2 * q'))) →
    (∀ c : Fin r, ∀ q' ≤ (r + 1) * q,
      ∫⁻ ω, ENNReal.ofReal ((l c.succ ω / l c.castSucc ω) ^ (2 * q')) ∂μ ≤ ENNReal.ofReal (R ^ (2 * q'))) →
    ∀ a : Fin (r + 1),
      ∫⁻ ω, ENNReal.ofReal (l a ω ^ (2 * q)) ∂μ ≤ ENNReal.ofReal (H0 ^ (2 * q) * R ^ (2 * q * a.val))

def MomentProductBound : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (r q L : ℕ)
    (l : Fin (r + 1) → Ω → ℝ) (H1 : ℝ),
    (∀ a, Measurable (l a)) → (∀ a ω, 0 < l a ω) → 0 ≤ H1 → L ≤ r + 1 →
    (∀ a : Fin (r + 1), a.val < L →
      ∫⁻ ω, ENNReal.ofReal (l a ω ^ (2 * q * L)) ∂μ ≤ ENNReal.ofReal (H1 ^ (2 * q * L))) →
    ∫⁻ ω, ENNReal.ofReal ((∏ a ∈ univ.filter (fun a : Fin (r + 1) => a.val < L), l a ω) ^ (2 * q)) ∂μ ≤
      ENNReal.ofReal (H1 ^ (2 * q * L))

def IteratedHighestWeightBound : Prop :=
  ∀ (V P Λ : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup P] (jh : P → V) (Dop : Λ → Module.End ℂ V)
    (wt : Λ → ℕ) (N1 Ninf : P → ℕ) (lam : P) (Gam : ℝ) (c0 q0 : ℕ), 0 ≤ Gam →
    (∀ x y, N1 (x + y) ≤ N1 x + N1 y) → (∀ x y, Ninf (x + y) ≤ Ninf x + Ninf y) → N1 0 = 0 → Ninf 0 = 0 →
    (∀ μ l, N1 (μ - lam) + c0 ≤ q0 → ∃ a : P →₀ ℂ, Dop l (jh μ) = a.sum (fun ν c => c • jh (μ + ν)) ∧
      (a.sum fun _ c => ‖c‖) ≤ Gam ^ wt l ∧ ∀ ν ∈ a.support, N1 ν ≤ wt l ∧ Ninf ν ≤ 1) →
    ∀ (μ : P) (al : List Λ), N1 (μ - lam) + (al.map wt).sum + c0 ≤ q0 →
      ∃ a : P →₀ ℂ, (al.map Dop).prod (jh μ) = a.sum (fun ν c => c • jh (μ + ν)) ∧
        (a.sum fun _ c => ‖c‖) ≤ Gam ^ (al.map wt).sum ∧
        ∀ ν ∈ a.support, N1 ν ≤ (al.map wt).sum ∧ Ninf ν ≤ al.length

def LemSSupBound : Prop :=
  ∀ (φ : ℂ → ℂ) (x M : ℝ), Continuous φ → Integrable φ → 0 < x →
    (∀ s : ℂ, ‖∫ c : ℂ, Complex.exp (2 * Complex.I * ((s * c).im : ℂ)) * φ c‖ ≤ M * TruncationCutoff 3 x ‖s‖) →
    ∀ c, ‖φ c‖ ≤ 3 / π * x ^ 2 * M

end PartA

section PartB
open Finset Matrix Polynomial
open scoped ComplexConjugate TensorProduct

def IsLowerUnitriangular {d : ℕ} {R : Type*} [Zero R] [One R] (l : Matrix (Fin d) (Fin d) R) : Prop :=
  (∀ i, l i i = 1) ∧ ∀ i j, i < j → l i j = 0

def IsUpperUnitriangular {d : ℕ} {R : Type*} [Zero R] [One R] (u : Matrix (Fin d) (Fin d) R) : Prop :=
  (∀ i, u i i = 1) ∧ ∀ i j, j < i → u i j = 0

def leadingPrincipalMinor {d : ℕ} {R : Type*} [CommRing R] (Z : Matrix (Fin d) (Fin d) R) (q : ℕ) : R :=
  (Z.submatrix (fun i : {i : Fin d // (i : ℕ) < q} => i.1) (fun i : {i : Fin d // (i : ℕ) < q} => i.1)).det

def blockAntidiagonalMatrix {d : ℕ} {R : Type*} [Zero R] (c : Composition d) (t : Fin c.length → R) :
    Matrix (Fin d) (Fin d) R := fun i j =>
  if c.index i = c.index j ∧
      (i : ℕ) + (j : ℕ) + 1 = c.sizeUpTo (c.index i : ℕ) + c.sizeUpTo ((c.index i : ℕ) + 1)
  then t (c.index i) else 0

def mixedMinor {d : ℕ} {R : Type*} [CommRing R] (Z : Matrix (Fin d) (Fin d) R) (i j' : Fin d) : R :=
  (Z.submatrix (fun a : Fin ((i : ℕ) + 1) => Fin.castLE (Nat.succ_le_of_lt i.isLt) a)
    (fun b : Fin ((i : ℕ) + 1) =>
      if (b : ℕ) < (i : ℕ) then Fin.castLE (Nat.succ_le_of_lt i.isLt) b else j')).det

def LeadingMinorUnipotentInvariant : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (Z l u : Matrix (Fin d) (Fin d) R) (q : ℕ),
    IsLowerUnitriangular l → IsUpperUnitriangular u → leadingPrincipalMinor (l * Z * u) q = leadingPrincipalMinor Z q

def LeadingMinorVanishesOffBlockEnds : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (c : Composition d) (t : Fin c.length → R) (q : ℕ),
    q ≤ d → (∀ p : ℕ, q ≠ c.sizeUpTo p) → leadingPrincipalMinor (blockAntidiagonalMatrix c t) q = 0

def LeadingMinorAtBlockEnd : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (c : Composition d) (t : Fin c.length → R) (p : ℕ),
    leadingPrincipalMinor (blockAntidiagonalMatrix c t) (c.sizeUpTo p) =
      ∏ a ∈ univ.filter (fun a : Fin c.length => (a : ℕ) < p),
        (-1) ^ ((c.blocksFun a).choose 2) * t a ^ (c.blocksFun a)

def MixedMinorVanishing : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (c : Composition d) (t : Fin c.length → R)
    (l u : Matrix (Fin d) (Fin d) R), IsLowerUnitriangular l → IsUpperUnitriangular u →
    ∀ i j' : Fin d, (i : ℕ) = c.sizeUpTo (c.index i : ℕ) → c.index j' = c.index i →
      ((j' : ℕ) + 1 < c.sizeUpTo ((c.index i : ℕ) + 1) → mixedMinor (l * blockAntidiagonalMatrix c t * u) i j' = 0) ∧
      ((j' : ℕ) + 1 = c.sizeUpTo ((c.index i : ℕ) + 1) →
        mixedMinor (l * blockAntidiagonalMatrix c t * u) i j' = leadingPrincipalMinor (blockAntidiagonalMatrix c t) (i : ℕ) * t (c.index i))

def OrbitIntegralEntries : Prop :=
  ∀ (K : Type) [Field K] (O : Subring K) (d : ℕ) (c : Composition d) (t : Fin c.length → K),
    (∀ a, t a ≠ 0) → ∀ l u : Matrix (Fin d) (Fin d) K, IsLowerUnitriangular l → IsUpperUnitriangular u →
      (∀ i j, (l * blockAntidiagonalMatrix c t * u) i j ∈ O) →
        (∀ p : ℕ, leadingPrincipalMinor (blockAntidiagonalMatrix c t) (c.sizeUpTo p) ∈ O ∧ leadingPrincipalMinor (blockAntidiagonalMatrix c t) (c.sizeUpTo p) ≠ 0) ∧
        ∀ a : Fin c.length, leadingPrincipalMinor (blockAntidiagonalMatrix c t) (c.sizeUpTo (a : ℕ)) * t a ∈ O

def DualVectorNormSq : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ x y, h y x = conj (h x y)) →
    ∀ (r : ℕ) (y f' : Fin (r + 1) → V) (T T' : ℝ), T' ≠ 0 →
      (∀ a b, h (y a) (y b) = if a = Fin.last r ∧ b = Fin.last r then -(T : ℂ) else 0) →
      (∀ a b, h (f' a) (f' b) = if a = Fin.last r ∧ b = Fin.last r then -(T' : ℂ) else 0) →
      ∀ (x0 om : V) (al : ℂ),
        x0 ∈ Submodule.span ℂ (f' '' {b | b ≠ Fin.last r}) → (∀ b, h om (f' b) = 0) →
        (∑ a, (Matrix.of fun a b => h (y a) (f' b)).adjugate (Fin.last r) a • y a) = x0 + al • f' (Fin.last r) + om →
          h om om =
            (((Complex.normSq (Matrix.of fun a b => h (y a) (f' b)).det : ℝ) : ℂ) -
              (T : ℂ) * (T' : ℂ) *
                ((Complex.normSq (leadingPrincipalMinor (Matrix.of fun a b => h (y a) (f' b)) r) : ℝ) : ℂ)) / (T' : ℂ)

def IsSelfAdjointInvolution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (θ : V →ₗ[ℂ] V) : Prop :=
  (∀ x, θ (θ x) = x) ∧ ∀ x y, inner ℂ (θ x) y = inner ℂ x (θ y)

noncomputable def majorantHermitianForm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (θ : V →ₗ[ℂ] V) (x y : V) : ℂ :=
  inner ℂ (θ y) x

noncomputable def majorantDistance {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} (y : Fin n → V)
    (a : Fin n) : ℝ :=
  Metric.infDist (y a) (Submodule.span ℂ (y '' {b | b < a}) : Set V)

def GramDetEqProdDistances : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (l : ℕ) (y : Fin l → V),
    (Matrix.of fun a b => inner ℂ (y a) (y b)).det = ((∏ a, majorantDistance y a ^ 2 : ℝ) : ℂ)

def RankTwoOperatorSkewHermitian : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ x y, h y x = conj (h x y)) →
    ∀ e v x y : V, h (h x v • e - h x e • v) y + h x (h y v • e - h y e • v) = 0

def MajorantPhaseChoice : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (θ : V →ₗ[ℂ] V), IsSelfAdjointInvolution θ →
    ∀ (u y1 : V) (S : Set V), u ≠ 0 → (∀ w ∈ S, inner ℂ u w = 0) → inner ℂ u y1 = ((‖u‖ ^ 2 : ℝ) : ℂ) →
      ‖(Complex.I / (‖u‖ : ℂ)) • θ u‖ = 1 ∧
      (∀ w ∈ S, majorantHermitianForm θ w ((Complex.I / (‖u‖ : ℂ)) • θ u) = 0) ∧
      majorantHermitianForm θ y1 ((Complex.I / (‖u‖ : ℂ)) • θ u) = -Complex.I * (‖u‖ : ℂ)

def SkewOperatorFrobeniusBound : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (θ : V →ₗ[ℂ] V), IsSelfAdjointInvolution θ →
    ∀ (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ V) (e v : V),
      ∑ a, ∑ b, ‖inner ℂ (bs a) (majorantHermitianForm θ (bs b) v • e - majorantHermitianForm θ (bs b) e • v)‖ ^ 2 ≤ 4 * ‖e‖ ^ 2 * ‖v‖ ^ 2

def OffDiagonalOperatorBound : Prop :=
  ∀ (n j b bs : ℝ), 1 ≤ n → 0 ≤ j → 0 ≤ bs → j + 2 ≤ b / (8704 * n) → 8704 * n ^ 3 ≤ b → bs ≤ 2.02 * b →
    (n - 1) * (8 * (bs + j + 2) * (n ^ 2 + j + 2)) ≤ (b / 16) ^ 2

end PartB

section PartC
open Finset

def DegStepBound : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (s : Fin n), Function.Injective μ → (∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ)) →
    (Function.Injective (μ + Pi.single s 1) →
      1 / (n : ℝ) ≤ ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s') ∧
      ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s') ≤ n) ∧
    (Function.Injective (μ - Pi.single s 1) →
      1 / (n : ℝ) ≤ ∏ s' ∈ univ.erase s, (μ s - 1 - μ s') / (μ s - μ s') ∧
      ∏ s' ∈ univ.erase s, (μ s - 1 - μ s') / (μ s - μ s') ≤ n)

def DegSetBound : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (I : Finset (Fin n)), StrictAnti μ → (∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ)) →
    (∀ a b, a < b → 2 ≤ μ a - μ b) →
    ((n : ℝ) ^ I.card)⁻¹ ≤
        Formalism.QuantumDeterminants.fdegHC (fun a => μ a + if a ∈ I then 1 else 0) / Formalism.QuantumDeterminants.fdegHC μ ∧
      Formalism.QuantumDeterminants.fdegHC (fun a => μ a + if a ∈ I then 1 else 0) / Formalism.QuantumDeterminants.fdegHC μ ≤ (n : ℝ) ^ I.card

def FormalDegreeHypotheses (k M : ℕ) (lam mu : Fin (k + M) → ℝ) (u : Fin k → ℝ) (b bv ga q0 : ℝ) : Prop :=
  StrictAnti lam ∧ (∀ a c, ∃ z : ℤ, lam a - lam c = (z : ℝ)) ∧
  (∀ a i, ∃ z : ℤ, lam a - u i = (z : ℝ) + 1 / 2) ∧
  (∀ i : Fin k, lam (Fin.castAdd M i) < u i) ∧
  (∀ i j : Fin k, (i : ℕ) + 1 = (j : ℕ) → u j < lam (Fin.castAdd M i)) ∧
  (∀ a : Fin (k + M), (a : ℕ) + 1 < k → 0 ≤ lam a ∧ lam a ≤ bv / 8) ∧
  (∀ a : Fin (k + M), k ≤ (a : ℕ) + 1 → -2 * bv ≤ lam a ∧ lam a ≤ -bv) ∧
  (∀ a, |lam a| ≤ b) ∧ (∀ i, |u i| ≤ b) ∧
  (∀ a c : Fin (k + M), a < c → (c : ℕ) + 1 < k → ga ≤ lam a - lam c) ∧ 4 ≤ ga ∧
  (∀ a, ∃ z : ℤ, mu a - lam a = (z : ℝ)) ∧ StrictAnti mu ∧
  ∑ a, |mu a - lam a| ≤ q0 ∧ q0 ≤ ga / 8 ∧ q0 ≤ bv / 4 ∧ q0 ≤ b

def supL2RatioMajorant : Prop :=
  ∀ (k M : ℕ) (lam mu : Fin (k + M) → ℝ) (u : Fin k → ℝ) (b bv ga q0 : ℝ) (s : Fin (k + M)),
    1 ≤ k → 1 ≤ M → FormalDegreeHypotheses k M lam mu u b bv ga q0 → (∀ s', s' ≠ s → mu s - 1 ≠ mu s') →
    (∏ i, |mu s - 1 / 2 - u i|) / ∏ s' ∈ univ.erase s, |mu s - 1 - mu s'| ≤
      if (s : ℕ) + 1 < k then 64 * Real.exp 1 * Real.sqrt k * b ^ 3 else 16 * Real.exp 1 * b ^ 2

end PartC

section PartD
open Finset

def LeadingPrincipalMinor {R : Type*} [CommRing R] {d : ℕ} (Z : Matrix (Fin d) (Fin d) R) (l : ℕ) (h : l ≤ d) : R :=
  (Z.submatrix (Fin.castLE h) (Fin.castLE h)).det

end PartD

end Formalism.HermitianLatticeCounting.ExpansionTerms
