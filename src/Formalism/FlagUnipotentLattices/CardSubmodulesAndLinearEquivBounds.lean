module

public import Mathlib
public import Formalism.HyperbolicPlaceProducts.Bundle0001

@[expose] public section

open Module Matrix
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Formalism.HermitianLatticeCounting.LatticeSumBounds

def hs {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2)

def WeightedAMGM : Prop :=
  ∀ a b La : ℝ, 0 < La → |a * b| ≤ (La * a ^ 2 + b ^ 2 / La) / 2

def CommonLiftExpand : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (r : ℕ)
    (e e' : Fin r → V) (l₁ l₂ : V) (α α' : Fin r → ℂ),
    (∀ b, h l₁ (e' b) = 0) → (∀ a, h (e a) l₂ = 0) →
    h (l₁ + ∑ a, α a • e a) (l₂ + ∑ b, α' b • e' b) =
      h l₁ l₂ + ∑ a, ∑ b, α a * conj (α' b) * h (e a) (e' b)

def AbsA : Prop :=
  ∀ (U₁ U₂ : Type) [NormedAddCommGroup U₁] [InnerProductSpace ℂ U₁]
    [NormedAddCommGroup U₂] [InnerProductSpace ℂ U₂] (r : ℕ) (u : Fin r → U₁) (u' : Fin r → U₂)
    (Z : Matrix (Fin r) (Fin r) ℂ),
    (∀ w₁ w₂, ‖∑ a, ∑ b, inner ℂ (u a) w₁ * conj (inner ℂ (u' b) w₂) * Z a b‖ ≤
      2 * ‖w₁‖ * ‖w₂‖) →
    Real.sqrt ‖(Matrix.gram ℂ u).det‖ * Real.sqrt ‖(Matrix.gram ℂ u').det‖ * ‖Z.det‖ ≤ 2 ^ r

def WedgeHadamard : Prop :=
  ∀ (V₁ V₂ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ),
    (∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) →
    ∀ (j : ℕ) (y : Fin j → V₁) (y' : Fin j → V₂),
      ‖(Matrix.of fun a b => B (y a) (y' b)).det‖ ≤ (∏ a, ‖y a‖) * ∏ b, ‖y' b‖

def CramerUpper : Prop :=
  ∀ (R : Type) [CommRing R] (N l : ℕ) (hl : l ≤ N) (Lo W Up : Matrix (Fin N) (Fin N) R),
    (∀ i, Lo i i = 1) → (∀ i j, i < j → Lo i j = 0) → (∀ i, Up i i = 1) →
    (∀ i j, j < i → Up i j = 0) → (∀ i j : Fin N, (i : ℕ) < l → l ≤ (j : ℕ) → W i j = 0) →
    ∀ (c : Fin l) (b : Fin N),
      (∀ c' : Fin l, c < c' → Up (Fin.castLE hl c) (Fin.castLE hl c') = 0) →
      ((Lo * W * Up).submatrix (Fin.castLE hl)
          (fun j => if j = c then b else Fin.castLE hl j)).det =
        ((Lo * W * Up).submatrix (Fin.castLE hl) (Fin.castLE hl)).det * Up (Fin.castLE hl c) b

def GramHadamard : Prop :=
  ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (r : ℕ) (a : Fin r → U),
    Real.sqrt ‖(Matrix.gram ℂ a).det‖ ≤ ∏ b, ‖a b‖ ∧
    ∀ R : ℝ, (∀ b, ‖a b‖ ≤ R) → Real.sqrt ‖(Matrix.gram ℂ a).det‖ ≤ R ^ r

def LemmaP : Prop :=
  ∀ (ι : Type) [Fintype ι] (x : ι → ℝ) (Sg : Finset ι), (∀ v, 0 < x v) → 1 ≤ ∏ v, x v →
    ∏ v ∈ Sg, max (x v) (1 / x v) ≤ (∏ v, max 1 (x v)) ^ 2 ∧
    ∏ v ∈ Sg, max 1 (1 / x v) ≤ ∏ v, max 1 (x v)

def PThreshold : Prop :=
  ∀ (ι : Type) [Fintype ι] (x : ι → ℝ) (H : ℝ), 1 ≤ H → (∀ v, 0 ≤ x v) →
    ∏ v, max 1 (x v) ≤ H ^ Fintype.card ι * ∏ v, max 1 (x v / H)

def nv (k r : ℕ) (G T g v : ℝ) : ℝ :=
  (Real.exp 1 * Real.pi * G * g⁻¹ ^ (2 * r + 2) / (T * k * v)) ^ k

def expo (k r : ℕ) : ℝ := ((2 * r * (k - 2 - r) : ℕ) : ℝ) / (k : ℝ)

def xv (k r : ℕ) (C ν t g : ℝ) : ℝ := ν * t * g⁻¹ ^ (2 * r + 2) * (C / k) ^ expo k r

def MinI' : Prop :=
  ∀ (k r : ℕ) (C G T g v t Dr loss loss' JHS Jop dim : ℝ),
    r + 2 ≤ k → 0 < C → 0 < G → 0 < T → 0 < g → 0 < v → 0 < t → 0 < Dr → 1 ≤ loss' →
    0 < dim → 0 ≤ Jop → 0 ≤ JHS →
    (Real.exp 1 * Real.pi / (k * v)) ^ k * v⁻¹ ^ (2 * r * (k - 2 - r)) ≤ 1 →
    Dr ^ (2 * r + 4) ≤ loss →
    nv k r G T g v * JHS ^ 2 / dim ≤ loss * t⁻¹ ^ k →
    Jop ≤ loss' * (C / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r) →
    JHS ^ 2 ≤ dim * Jop ^ 2 →
    nv k r G T g v * JHS ^ 2 / dim ≤
      loss * loss' ^ 2 * t⁻¹ ^ k * (min 1 (xv k r C (G / (T * Dr ^ 2)) t g)) ^ k

def ChShSq : Prop :=
  ∀ sh ch : ℝ, 0 < sh → 0 ≤ ch → ch ^ 2 = sh ^ 2 + 1 →
    (1 ≤ sh → ((1 + ch) / sh) ^ 2 ≤ 6) ∧ (sh < 1 → (1 + ch) ^ 2 ≤ 6)

def MinII' : Prop :=
  ∀ (k r : ℕ) (C CT G T T' g v t Dr sh ch loss loss' JHS Jop dim : ℝ),
    1 ≤ r → 2 * r + 6 ≤ k → 0 < C → 0 < G → 0 < T → 0 < T' → 1 ≤ g → 0 < v → 0 < t →
    0 < Dr → 1 ≤ loss' → 0 < dim → 0 ≤ Jop → 0 ≤ JHS →
    v⁻¹ ^ k * (C / (k * v)) ^ (2 * r * (k - 2 - r)) ≤ 1 → Dr ^ (2 * r + 4) ≤ loss →
    0 < sh → 0 ≤ ch → ch ^ 2 = sh ^ 2 + 1 → G = T * T' * Dr ^ 2 * sh ^ 2 →
    T' / T ≤ CT → (k : ℝ) ^ (3 * r) ≤ g⁻¹ ^ (2 * r + 2) * T' * t →
    nv k r G T g v * JHS ^ 2 / dim ≤ loss * t⁻¹ ^ k →
    Jop ≤ loss' * (C / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r) →
    JHS ^ 2 ≤ dim * Jop ^ 2 →
    nv k r G T g v * JHS ^ 2 * ((1 + ch) / sh) ^ (2 * k) * T⁻¹ ^ k / dim ≤
      loss * loss' ^ 2 * (6 * Real.exp 1 * Real.pi * CT / (k * g ^ (2 * r + 2))) ^ k

def MinIIZero : Prop :=
  ∀ (k r : ℕ) (CT G T T' g v t loss JHS dim : ℝ),
    1 ≤ r → 1 ≤ k → 0 < G → 0 < T → 0 < T' → 1 ≤ g → 0 < v → 0 < t → 0 ≤ loss → 0 < dim →
    T' / T ≤ CT → (k : ℝ) ^ (3 * r) ≤ g⁻¹ ^ (2 * r + 2) * T' * t →
    nv k r G T g v * JHS ^ 2 / dim ≤ loss * t⁻¹ ^ k →
    nv k r G T g v * JHS ^ 2 * T⁻¹ ^ k / dim ≤ loss * (CT / (k * g ^ (2 * r + 2))) ^ k

def XiIdentity : Prop :=
  ∀ (mass mj : ℕ → ℝ) (k s : ℕ), (∀ j, 0 < mj j) → 0 < mass 2 →
    (∀ j, 3 ≤ j → mass j = mj j * mass (j - 1)) → 2 ≤ s → s + 2 ≤ k →
    mass s * mass (k - s) / mass k =
      mass 2 * (∏ j ∈ Finset.Ioc 2 s, mj j) / ∏ j ∈ Finset.Ioc (k - s) k, mj j

def mJ (f : ℕ) (v : ℝ) (Lv : ℕ → ℝ) (j : ℕ) : ℝ :=
  (((j - 1).factorial : ℝ) * (v / Real.pi) ^ j) ^ f * (Real.sqrt ((2 * v) ^ f))⁻¹ * Lv j

def zetaR (j : ℕ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ j

def PiPowFactorial : Prop :=
  ∀ k : ℕ, 3 ≤ k → Real.pi ^ (k - 1) / ((k - 2).factorial : ℝ) < 17

def StirlingInv : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    1 / ((k - 1).factorial : ℝ) ≤ (Real.exp 1 / k) ^ k * Real.sqrt (k / (2 * Real.pi))

def XiBound : Prop :=
  ∀ (f k s : ℕ) (v mass2 : ℝ) (Lv : ℕ → ℝ), 1 ≤ v → 0 ≤ mass2 → 2 ≤ s → s + 2 ≤ k →
    (∀ j, 3 ≤ j → ((zetaR j) ^ f)⁻¹ ≤ Lv j ∧ Lv j ≤ (zetaR j) ^ f) →
    mass2 * (∏ j ∈ Finset.Ioc 2 s, mJ f v Lv j) / ∏ j ∈ Finset.Ioc (k - s) k, mJ f v Lv j ≤
      mass2 * (2 * v) ^ f * Real.exp (0.72 * f) * 17 ^ f * Real.sqrt (k / (2 * Real.pi)) ^ f *
        Real.pi ^ ((s - 2) * (k - s - 2) * f) * (Real.exp 1 * Real.pi / (k * v)) ^ (k * f)

def Packing : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : AddSubgroup E) (l₀ R : ℝ), 0 < l₀ → 0 ≤ R → (∀ x ∈ Λ, x ≠ 0 → l₀ ≤ ‖x‖) →
    {x : E | x ∈ Λ ∧ ‖x‖ ≤ R}.Finite ∧
      ({x : E | x ∈ Λ ∧ ‖x‖ ≤ R}.ncard : ℝ) ≤ (1 + 2 * R / l₀) ^ finrank ℝ E

def TraceLower : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → ℝ), (∀ v, 0 ≤ a v) → 1 ≤ ∏ v, a v →
    (Fintype.card ι : ℝ) ≤ ∑ v, a v

def theta (j e : ℕ) (η q : ℝ) : ℝ := ∏ i ∈ Finset.Icc (j - e + 1) j, (1 - η ^ i * (q ^ i)⁻¹)

def ThetaBound : Prop :=
  ∀ (j e : ℕ) (η q : ℝ), e ≤ j → 2 ≤ q → (η = 1 ∨ η = -1) →
    0 < theta j e η q ∧ theta j e η q ≤ (3 / 2) ^ e ∧ theta j e η q ≤ 2 ^ e

def IdealNormLeCount : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : ℝ), 1 ≤ x →
    {I : Ideal (NumberField.RingOfIntegers K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x}.Finite ∧
    ({I : Ideal (NumberField.RingOfIntegers K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x}.ncard : ℝ) ≤
      x ^ (1 + Real.logb 2 (finrank ℚ K))

def ClassNumberBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E],
    (NumberField.classNumber E : ℝ) ≤
      |(NumberField.discr E : ℝ)| ^ ((1 + Real.logb 2 (finrank ℚ E)) / 2)

def CardSubmodulesOfIndexLePow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M]
    [Module (NumberField.RingOfIntegers E) M] [Module.Finite (NumberField.RingOfIntegers E) M]
    [Module.Projective (NumberField.RingOfIntegers E) M] (k j : ℕ), 1 ≤ j →
    finrank (NumberField.RingOfIntegers E) M ≤ k →
    {N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = j}.Finite ∧
      ({N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = j}.ncard : ℝ) ≤
        (j : ℝ) ^ ((k : ℝ) + Real.logb 2 (finrank ℚ E))

def CardSubmodulesAndLinearEquivBounds : Prop := Formalism.SLP.SubmoduleCountDed ∧ Formalism.SLP.GlobalBoundRefinements.AutCount

def UnipotentReduce : Prop :=
  ∀ (E : Type) [CommRing E] (O : Subring E) (FF : Set E) (N : ℕ) (u : Matrix (Fin N) (Fin N) E),
    (∀ x : E, ∃ a ∈ O, x + a ∈ FF) → (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) →
    ∃ n : Matrix (Fin N) (Fin N) E, (∀ i, n i i = 1) ∧ (∀ i j, j < i → n i j = 0) ∧
      (∀ i j, n i j ∈ O) ∧ ∀ i j, i < j → (u * n) i j ∈ FF

def LeadingMinorInvariant : Prop :=
  ∀ (R : Type) [CommRing R] (N l : ℕ) (hl : l ≤ N) (Lo W Up : Matrix (Fin N) (Fin N) R),
    (∀ i, Lo i i = 1) → (∀ i j, i < j → Lo i j = 0) → (∀ i, Up i i = 1) →
    (∀ i j, j < i → Up i j = 0) →
    ((Lo * W * Up).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (W.submatrix (Fin.castLE hl) (Fin.castLE hl)).det

def MinorBound : Prop :=
  ∀ (N : ℕ) (A w B : Matrix (Fin N) (Fin N) ℂ) (ρ P : ℝ), 1 ≤ ρ →
    (∀ i j, ‖A i j‖ ≤ ρ) → (∀ i j, ‖B i j‖ ≤ ρ) →
    (∀ (t : ℕ) (I J : Fin t → Fin N), ‖(w.submatrix I J).det‖ ≤ P) →
    ∀ (t : ℕ) (I J : Fin t → Fin N),
      ‖((A * w * B).submatrix I J).det‖ ≤ 4 ^ N * (N.factorial : ℝ) ^ 2 * ρ ^ (2 * N) * P

def MonomialMinor : Prop :=
  ∀ (N : ℕ) (σ : Equiv.Perm (Fin N)) (c : Fin N → ℂ) (t : ℕ) (I J : Fin t → Fin N),
    ‖((Matrix.of fun i j => if j = σ i then c i else 0 : Matrix (Fin N) (Fin N) ℂ).submatrix
      I J).det‖ ≤ ∏ i, max 1 ‖c i‖

def Transference : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (lam : ℝ), 0 < lam →
    (∀ y : E, y ≠ 0 → (∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) → lam ≤ ‖y‖) →
    ∀ x : E, ∃ l ∈ Λ, ‖x - l‖ * lam ≤ (finrank ℝ E : ℝ) / 2

def CoveringO : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], (∀ w : NumberField.InfinitePlace E, w.IsComplex) →
    ∀ x : NumberField.InfinitePlace E → ℂ, ∃ a : NumberField.RingOfIntegers E,
      ∀ w, ‖x w - w.embedding (a : E)‖ ≤
        Real.sqrt (finrank ℚ E) * |(NumberField.discr E : ℝ)| ^ (1 / (finrank ℚ E : ℝ))

def eichler {R V : Type*} [CommRing R] [StarRing R] [AddCommGroup V] [Module R V]
    (h : V →ₗ[R] V →ₗ⋆[R] R) (u σ : V) (τ : R) (x : V) : V :=
  x - h x σ • u + h x u • σ - (τ * h x u) • u

def HomRestrictIndex : Prop :=
  ∀ (O M X : Type) [CommRing O] [IsDedekindDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] (P : Submodule O M), ¬ IsField O → Finite (M ⧸ P) →
    Nat.card ((P →ₗ[O] X) ⧸ LinearMap.range (LinearMap.lcomp O X P.subtype)) =
      Nat.card (M ⧸ P) ^ finrank O X

def crossGram {K V : Type*} [CommRing K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ[K] V →ₗ⋆[K] K) {N : ℕ} (f f' : Fin N → V) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun a b => h (f' b) (f a)

def OmegaNorm : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ[K] V →ₗ⋆[K] K), (∀ x y, h y x = star (h x y)) →
    ∀ (r : ℕ) (f f' : Fin (r + 1) → V) (T T' : K) (x w : V) (ζ : K),
    (∀ a b, h (f a) (f b) = if a = Fin.last r ∧ b = Fin.last r then -T else 0) →
    (∀ a b, h (f' a) (f' b) = if a = Fin.last r ∧ b = Fin.last r then -T' else 0) →
    T ≠ 0 → x ∈ Submodule.span K (Set.range fun a : Fin r => f a.castSucc) →
    (∀ a, h w (f a) = 0) →
    ∑ b, (crossGram h f f').adjugate b (Fin.last r) • f' b = x + w + ζ • f (Fin.last r) →
    T * h w w = (crossGram h f f').det * star (crossGram h f f').det -
      T * T' * (((crossGram h f f').submatrix Fin.castSucc Fin.castSucc).det *
        star ((crossGram h f f').submatrix Fin.castSucc Fin.castSucc).det)

def BoxCount : Prop :=
  ∀ (ι : Type) [Fintype ι] (s : ℕ) (Λ : AddSubgroup (ι → EuclideanSpace ℂ (Fin s))) (ν : ℝ)
    (B : ι → ℝ), 0 < ν → (∀ v, 0 < B v) → (∀ x ∈ Λ, x ≠ 0 → ν ≤ ∏ v, ‖x v‖ ^ 2) →
    {x | x ∈ Λ ∧ ∀ v, ‖x v‖ ≤ B v}.Finite ∧
      ({x | x ∈ Λ ∧ ∀ v, ‖x v‖ ≤ B v}.ncard : ℝ) ≤
        9 ^ (s * Fintype.card ι) * (max 1 ((∏ v, B v ^ 2) / ν)) ^ s

def cofVec {R : Type*} [CommRing R] {r : ℕ} (Y : Matrix (Fin r) (Fin (r + 1)) R) (b : Fin (r + 1)) :
    R := (-1) ^ (b : ℕ) * (Y.submatrix id b.succAbove).det

def KernelRowSpace : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (Y : Matrix (Fin r) (Fin (r + 1)) R),
    Y *ᵥ cofVec Y = 0 ∧
    ∀ u : Fin (r + 1) → R, ∑ b, u b * cofVec Y b = 0 → ∀ b₀ : Fin (r + 1),
      (Y.submatrix id b₀.succAbove).det • u =
        ((fun c => u (b₀.succAbove c)) ᵥ* (Y.submatrix id b₀.succAbove).adjugate) ᵥ* Y

def CofVecAdjugate : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (b : Fin (r + 1)),
    Z.adjugate b (Fin.last r) = (-1) ^ r * cofVec (Z.submatrix Fin.castSucc id) b

def ProjQuotCard : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : Type) [AddCommGroup P]
    [Module (NumberField.RingOfIntegers E) P] [Module.Finite (NumberField.RingOfIntegers E) P]
    [Module.Projective (NumberField.RingOfIntegers E) P]
    (I : Ideal (NumberField.RingOfIntegers E)), I ≠ ⊥ →
    Nat.card (P ⧸ (I • (⊤ : Submodule (NumberField.RingOfIntegers E) P))) =
      Ideal.absNorm I ^ finrank (NumberField.RingOfIntegers E) P

def ChShBound : Prop :=
  ∀ sh ch : ℝ, 0 < sh → 0 ≤ ch → ch ^ 2 = sh ^ 2 + 1 → (1 + ch) / sh ≤ 3 * max 1 (1 / sh)

def ShInvPlace : Prop :=
  ∀ sh G T T' Dr : ℝ, 0 < sh → 0 < G → 0 < Dr → 1 ≤ T * T' → G = T * T' * Dr ^ 2 * sh ^ 2 →
    max 1 (1 / sh ^ 2) ≤ T * T' * max 1 (Dr ^ 2) * max 1 (1 / G)

def DegFactorBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (sh ch G Dr : ι → ℝ) (T T' HH : ℝ), 1 ≤ T * T' →
    (∀ v, 0 < sh v ∧ 0 ≤ ch v ∧ ch v ^ 2 = sh v ^ 2 + 1) → (∀ v, 0 < G v) → (∀ v, 0 < Dr v) →
    (∀ v, G v = T * T' * Dr v ^ 2 * sh v ^ 2) → (T * T') ^ Fintype.card ι ≤ HH →
    ∏ v, max 1 (Dr v ^ 2) ≤ HH → ∏ v, max 1 (1 / G v) ≤ HH →
    (∏ v, (1 + ch v) / sh v) ^ 2 ≤ 9 ^ Fintype.card ι * HH ^ 3

def DeNonDegBound : Prop :=
  ∀ (f s : ℕ) (g G₁ G₂ HH₁ HH₂ : ℝ), 2 ≤ g → 0 ≤ G₁ → 0 ≤ G₂ → G₁ ≤ HH₁ → G₂ ≤ HH₂ → 1 ≤ HH₁ →
    1 ≤ HH₂ →
    (2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) ≤ HH₁ * HH₂ ∧
      (2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) ≤ (HH₁ * HH₂) ^ 3

def DeDegBound : Prop :=
  ∀ (f s : ℕ) (g T G₁ G₂ K₁ K₂ HH₁ HH₂ : ℝ), 2 ≤ g → 1 ≤ T → 0 ≤ G₁ → 0 ≤ G₂ → G₁ ≤ HH₁ →
    G₂ ≤ HH₂ → 0 ≤ K₁ → 0 ≤ K₂ → K₁ ^ 2 ≤ 9 ^ f * HH₁ ^ 3 → K₂ ^ 2 ≤ 9 ^ f * HH₂ ^ 3 →
    9 ^ f ≤ HH₁ * HH₂ →
    (2 / g) ^ ((s - 2) * f) * Real.sqrt (G₁ * G₂) * T⁻¹ ^ f * K₁ * K₂ ≤ (HH₁ * HH₂) ^ 3

def NProduct : Prop :=
  ∀ (ι : Type) [Fintype ι] (k r : ℕ) (G vt : ι → ℝ) (T g v : ℝ), 1 ≤ k → 0 < T → 0 < g →
    (∀ w, 0 < vt w) → ∏ w, vt w = v ^ Fintype.card ι →
    ∏ w, nv k r (G w) T g (vt w) =
      (Real.exp 1 * Real.pi / (k * v)) ^ (k * Fintype.card ι) *
        ((∏ w, G w) * g⁻¹ ^ ((2 * r + 2) * Fintype.card ι) / T ^ Fintype.card ι) ^ k

def nTot (k f : ℕ) (v G₀ NT : ℝ) : ℝ :=
  (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) * (G₀ / NT) ^ k

def NonDegRow : Prop :=
  ∀ (k f s : ℕ) (g v NT G₁ G₂ Xi W count A₁ A₂ l₁ l₂ τ : ℝ), 1 ≤ k → 1 ≤ s → 0 < g → 0 < v →
    0 < NT → 0 < G₁ → 0 < G₂ → 0 ≤ Xi → 0 ≤ W → 0 ≤ A₁ → 0 ≤ A₂ → 0 ≤ τ →
    count ≤ ((2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) / NT) ^ k * Xi * W →
    nTot k f v G₁ NT * A₁ ^ 2 ≤ l₁ * τ → nTot k f v G₂ NT * A₂ ^ 2 ≤ l₂ * τ →
    count * A₁ * A₂ ≤ (2 / g) ^ ((s - 1) * k * f) * (k * v / (Real.exp 1 * Real.pi)) ^ (k * f) *
      Xi * W * Real.sqrt (l₁ * l₂) * τ

def DegRow : Prop :=
  ∀ (k f s : ℕ) (g v T NT G₁ G₂ K₁ K₂ Xi W count A₁ A₂ lam₁ lam₂ : ℝ), 1 ≤ k → 2 ≤ s → 0 < g →
    0 < v → 0 < T → 0 < NT → 0 < G₁ → 0 < G₂ → 0 < K₁ → 0 < K₂ → 0 ≤ Xi → 0 ≤ W → 0 ≤ A₁ →
    0 ≤ A₂ →
    count ≤ ((2 / g) ^ ((s - 2) * f) * Real.sqrt (G₁ * G₂) * T⁻¹ ^ f * K₁ * K₂ / NT) ^ k * Xi * W →
    nTot k f v G₁ NT * A₁ ^ 2 * K₁ ^ (2 * k) * T⁻¹ ^ (k * f) ≤ lam₁ →
    nTot k f v G₂ NT * A₂ ^ 2 * K₂ ^ (2 * k) * T⁻¹ ^ (k * f) ≤ lam₂ →
    count * A₁ * A₂ ≤ (2 / g) ^ ((s - 2) * k * f) * (k * v / (Real.exp 1 * Real.pi)) ^ (k * f) *
      Xi * W * Real.sqrt (lam₁ * lam₂)

def bigH (C : ℝ) (m f : ℕ) (b : ℝ) : ℝ := b ^ (C * (m : ℝ) ^ 2 * f)

def XiHyp (C : ℝ) (k m f : ℕ) (b v NT : ℝ) (Xi : ℕ → ℝ) : Prop :=
  (∀ s, 2 ≤ s → s + 2 ≤ k → 0 ≤ Xi s ∧
    ((k : ℝ) * v) ^ (k * f) * Xi s ≤ bigH C m f b ^ C * C ^ (s * k * f)) ∧
  (∀ s, s + 1 = k ∨ s = k → 0 ≤ Xi s ∧
    Xi s ≤ (C * k) ^ (k * f) * (bigH C m f b ^ (C * m) * NT) ^ (C * k))

def Params (C K₀ : ℝ) (k m f : ℕ) (b g v NT Gam : ℝ) : Prop :=
  4 ≤ m ∧ m ≤ f ∧ f ≤ k ∧ 2 ≤ b ∧ ((k : ℝ) * b) ^ 8 ≤ g ∧
  K₀ * (m : ℝ) ^ 5 * f * Real.log b ≤ k ∧ 1 ≤ v ∧ v ≤ b ∧ 1 ≤ NT ∧ NT ≤ b ^ (C * (m : ℝ) * f) ∧
  1 ≤ Gam ∧ Gam ≤ Real.exp (C * (m : ℝ) ^ 5 * f * Real.log b)

def ndRow (C : ℝ) (k m f s : ℕ) (b g v Gam : ℝ) (Xi : ℕ → ℝ) : ℝ :=
  (2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s * C ^ (k * f) *
    bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) * Gam

def NonDegSum : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ K₀ : ℝ, ∀ (k m f : ℕ) (b g v NT Gam : ℝ) (Xi : ℕ → ℝ),
    Params C K₀ k m f b g v NT Gam → XiHyp C k m f b v NT Xi →
    ∑ s ∈ Finset.Icc 2 k, ndRow C k m f s b g v Gam Xi ≤ (Real.sqrt g)⁻¹ ^ (k * f)

def degRow (C : ℝ) (k m f s : ℕ) (b g v Gam : ℝ) (Xi : ℕ → ℝ) : ℝ :=
  (2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s * C ^ (k * f) *
    bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) * Gam *
    Real.exp (C * (m : ℝ) ^ 6 * f * Real.log b) * (C / k) ^ (k * f)

def DegSum : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ K₀ : ℝ, ∀ (k m f : ℕ) (b g v NT Gam : ℝ) (Xi : ℕ → ℝ),
    Params C K₀ k m f b g v NT Gam → XiHyp C k m f b v NT Xi →
    ∑ s ∈ Finset.Icc 2 k, degRow C k m f s b g v Gam Xi ≤
      Real.exp (-((k : ℝ) * f * Real.log k) / 2) * (Gam ^ 2)⁻¹

def ChShPair : Prop :=
  ∀ sh₁ ch₁ sh₂ ch₂ : ℝ, 0 < sh₁ → 0 ≤ ch₁ → ch₁ ^ 2 = sh₁ ^ 2 + 1 → 0 < sh₂ → 0 ≤ ch₂ →
    ch₂ ^ 2 = sh₂ ^ 2 + 1 → (ch₁ + ch₂) / (sh₁ * sh₂) ≤ 4 / (min 1 sh₁ * min 1 sh₂)

def SmallTerm : Prop :=
  ∀ (ι : Type) [Fintype ι] (sh₁ ch₁ sh₂ ch₂ : ι → ℝ) (T T' g : ℝ), 0 < T → 0 < T' → 0 < g →
    (∀ v, 0 < sh₁ v ∧ 0 ≤ ch₁ v ∧ ch₁ v ^ 2 = sh₁ v ^ 2 + 1) →
    (∀ v, 0 < sh₂ v ∧ 0 ≤ ch₂ v ∧ ch₂ v ^ 2 = sh₂ v ^ 2 + 1) →
    Real.sqrt (T * T' / g ^ 2) ^ Fintype.card ι ≤ ∏ v, (ch₁ v + ch₂ v) / (sh₁ v * sh₂ v) →
    ∏ v, min (T' * sh₁ v ^ 2) T' ≤ (4 * Real.sqrt (T' / T) * g) ^ Fintype.card ι ∨
    ∏ v, min (T' * sh₂ v ^ 2) T' ≤ (4 * Real.sqrt (T' / T) * g) ^ Fintype.card ι

def SingleRowBound : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ K₀ : ℝ, ∀ (k r f : ℕ) (b g v NT Gam : ℝ),
    Params C K₀ k (2 * r + 2) f b g v NT Gam →
    C ^ f * bigH C (2 * r + 2) f b ^ (C * ((2 * r + 2 : ℕ) : ℝ) ^ 3) * Gam *
        Real.exp (C * ((2 * r + 2 : ℕ) : ℝ) ^ 6 * f * Real.log b) *
        Real.sqrt ((C * g⁻¹ ^ (2 * r + 1) * ((k : ℝ) ^ r)⁻¹) ^ (k * f)) ≤
      Real.exp (-((k : ℝ) * f * Real.log k))

def ExpSumLe' : Prop :=
  ∀ A x : ℝ, 1 ≤ A → 6 * Real.log (3 * A) ≤ x →
    A * (Real.exp (-4 * x) + Real.exp (-x / 2) + Real.exp (-x)) ≤ Real.exp (-x / 3)

def GainSqrt : Prop :=
  ∀ (k f : ℕ) (b g : ℝ), 1 ≤ k → 1 ≤ b → ((k : ℝ) * b) ^ 8 ≤ g →
    (Real.sqrt g)⁻¹ ^ (k * f) ≤ Real.exp (-4 * ((k : ℝ) * f * Real.log k))

def BoxCountO : Prop :=
  ∀ (ι : Type) [Fintype ι] (Λ : AddSubgroup (ι → ℂ)) (B : ι → ℝ), (∀ v, 0 < B v) →
    (∀ x ∈ Λ, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖) →
    {x | x ∈ Λ ∧ ∀ v, ‖x v‖ ≤ B v}.Finite ∧
      ({x | x ∈ Λ ∧ ∀ v, ‖x v‖ ≤ B v}.ncard : ℝ) ≤ ∏ v, (1 + 2 * B v) ^ 2 ∧
      ∏ v, (1 + 2 * B v) ^ 2 ≤ 9 ^ Fintype.card ι * ∏ v, max 1 (B v) ^ 2

def LatticeSum : Prop :=
  ∀ (ι : Type) [Fintype ι] (Λ : AddSubgroup (ι → ℂ)) (H₂ : ℝ), 1 ≤ H₂ →
    (∀ x ∈ Λ, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖) →
    Summable (fun D : Λ => ∏ v, ((max 1 (‖(D : ι → ℂ) v‖ / H₂)) ^ 3)⁻¹) ∧
      ∑' D : Λ, ∏ v, ((max 1 (‖(D : ι → ℂ) v‖ / H₂)) ^ 3)⁻¹ ≤ (41 * H₂ ^ 2) ^ Fintype.card ι

def FiniteOrderCongruence : Prop :=
  ∀ (N n : ℕ) (g : ℤ) (A B : Matrix (Fin N) (Fin N) ℤ), 3 ≤ g → 1 ≤ n → A ^ n = 1 →
    A = 1 + g • B → A = 1

end Formalism.HermitianLatticeCounting.LatticeSumBounds
