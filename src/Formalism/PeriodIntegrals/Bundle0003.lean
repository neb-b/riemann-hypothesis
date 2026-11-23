module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.FglTriFactor
section
noncomputable section

open Classical

namespace PI.FglTriFactor

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

section

variable {p : ℕ} [Fact p.Prime] (l ex : PowerSeries ℂ_[p]) {σ : Type*}

def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a l

def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x ex

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a + lg l b)

def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a - lg l b)

end

def IsWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Prop :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  wq = 1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3

def dX {A : Type*} [CommRing A] (f : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => ((n : A) + 1) * PowerSeries.coeff (n + 1) f

def omegaW {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  (-(2 : PowerSeries ℂ_[p]) * wq - X * dX wq) * (wq * (c W.a₁ * X + c W.a₃ * X ^ 3 * wq - 2))⁻¹

def flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) (omegaW W wq) / n

def T {p : ℕ} [Fact p.Prime] (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  (Xv 0) ^ 3 * PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (Xv 2 - Xv 1) +
    (Xv 1) ^ 3 * PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (Xv 0 - Xv 2) +
    (Xv 2) ^ 3 * PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (Xv 1 - Xv 0)

def Lemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → ‖W.Δ‖ = 1 →
    IsWq W wq → PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X →
    IntegralMv (add (flog W wq) ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    ∃ n : MvPowerSeries (Fin 3) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      T wq = add (flog W wq) ex (add (flog W wq) ex (Xv 0) (Xv 1)) (Xv 2) *
        sub (flog W wq) ex (Xv 0) (Xv 1) * sub (flog W wq) ex (Xv 1) (Xv 2) *
        sub (flog W wq) ex (Xv 2) (Xv 0) * n

end PI.FglTriFactor
end
end

-- bundled from Formalism.PeriodIntegrals.FinExtTop
section
noncomputable section

namespace PI.FinExtTop

structure PadicCoeff (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] : Prop where
  ring : IsTopologicalRing O
  compact : CompactSpace O
  t2 : T2Space O
  adic : IsAdic (IsLocalRing.maximalIdeal O)
  p_mem : (p : O) ∈ IsLocalRing.maximalIdeal O
  p_ne : (p : O) ≠ 0

structure FracTop (O : Type) [CommRing O] [IsDomain O] [TopologicalSpace O]
    [TopologicalSpace (FractionRing O)] : Prop where
  emb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))

structure IsFGTop (O M : Type) [CommRing O] [TopologicalSpace O] [AddCommGroup M] [Module O M]
    [TopologicalSpace M] : Prop where
  fg : Module.Finite O M
  t2 : T2Space M
  csmul : ContinuousSMul O M

end PI.FinExtTop

namespace PI


open PI.FinExtTop in
def FinExtTop : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [Module.Free O O']
    [Module.Finite O O'],
    PadicCoeff ℓ O →
    ∃ (_ : Algebra ℤ_[ℓ] O') (_ : IsScalarTower ℤ_[ℓ] O O') (_ : Module.Finite ℤ_[ℓ] O')
      (_ : TopologicalSpace O') (_ : IsModuleTopology O O')
      (_ : TopologicalSpace (FractionRing O')) (_ : IsTopologicalAddGroup (FractionRing O'))
      (_ : ContinuousSMul O' (FractionRing O')),
      Function.Injective (algebraMap ℤ_[ℓ] O') ∧ PadicCoeff ℓ O' ∧ FracTop O' ∧
      ∀ (X' d : Type) [Fintype d] [DecidableEq d]
        (R' : Subalgebra O' (X' → Matrix d d (FractionRing O'))), Module.Finite O' R' →
        ∃ (_ : TopologicalSpace R') (_ : IsModuleTopology O' R'),
          IsTopologicalAddGroup R' ∧ ContinuousConstSMul O' R' ∧ ContinuousMul R' ∧
          IsTopologicalRing R' ∧ IsFGTop O' R'

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.FlagGramNonneg
section
noncomputable section

open Matrix NumberField

namespace PI.FlagGramNonneg

def cT {A : Type} [CommRing A] (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

def Jpq (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)

def HasSignature {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n ℂ) (p q : ℕ) : Prop :=
  ∃ e : n ≃ Fin p ⊕ Fin q, ∃ P : GL (Fin p ⊕ Fin q) ℂ,
    cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * J.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q

def leadMinorE {E : Type} [Field E] {N : ℕ} (A : Matrix (Fin N) (Fin N) E) (l : ℕ) : E := by
  classical
  exact if h : l ≤ N then (A.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0

def gram {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {N : ℕ} (b : Module.Basis (Fin N) E V) : Matrix (Fin N) (Fin N) E :=
  fun i j => hT (b i) (b j)

def IsFlag {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (T : E) (e : Fin r → V) (z : V) : Prop :=
  LinearIndependent E e ∧ (∀ a b, hT (e a) (e b) = 0) ∧ (∀ a, hT (e a) z = 0) ∧ hT z z = -T

def fvec {V : Type} {r : ℕ} (e : Fin r → V) (z : V) : Fin (r + 1) → V :=
  Fin.snoc (α := fun _ => V) e z

def zhat {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (f f' : Fin (r + 1) → V) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  fun a b => hT (f a) (f' b)

def gval {E : Type} [Field E] [StarRing E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : E :=
  leadMinorE Z (r + 1) * star (leadMinorE Z (r + 1)) - T * T' * (leadMinorE Z r * star (leadMinorE Z r))

end PI.FlagGramNonneg

namespace PI

open PI.FlagGramNonneg

def FlagGramNonneg : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (hT : V →ₗ⋆[E] V →ₗ[E] E), hT.IsSymm → hT.Nondegenerate →
    ∀ (N : ℕ) (b : Module.Basis (Fin N) E V) (τ : E →+* ℂ),
    (∀ a, τ (star a) = starRingEnd ℂ (τ a)) →
    ∀ (p r T T' : ℕ), HasSignature ((gram hT b).map τ) p (r + 1) → 0 < T → 0 < T' →
    ∀ (e e' : Fin r → V) (z z' : V), IsFlag hT (T : E) e z → IsFlag hT (T' : E) e' z' →
      ∃ c : ℝ, 0 ≤ c ∧ τ (gval (zhat hT (fvec e z) (fvec e' z')) (T : E) (T' : E)) = c

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.FockRBlock
section
open MvPolynomial

noncomputable section

namespace PI.TO

def colW (r n : ℕ) : Fin r × Fin n → (Fin n → ℕ) := fun v => Pi.single v.2 1

def colAddGen (R : Type*) [CommRing R] {r n : ℕ} (l j : Fin n) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Option (Fin r × Fin n)) R :=
  aeval fun v => if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)

def dualWeyl (R : Type*) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  weightedHomogeneousSubmodule R (colW r n) ν ⊓
    ⨅ (l : Fin n) (j : Fin n) (_ : l < j),
      LinearMap.ker ((colAddGen R (r := r) l j).toLinearMap -
        (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).toLinearMap)

def genM (R : Type) [CommRing R] (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :=
  Matrix.of fun a s => X (a, s)

def Nv (R : Type) [CommRing R] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  if vec then X (c, 0) else (genM R m).adjugate (Fin.last m) c

def theta (R : Type) [CommRing R] (m : ℕ) (vec : Bool) :
    MvPolynomial (Fin (m + 1)) R →ₐ[R] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  aeval (Nv R m vec)

def Hd (R : Type) [CommRing R] (k d : ℕ) : Submodule R (MvPolynomial (Fin k) R) :=
  restrictSupport R {μ | ∑ c, μ c = d}

def fockR {σ R : Type*} [CommRing R] (f g : MvPolynomial σ R) : R :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R)

def word1 {K : Type} [CommRing K] {k : ℕ} (l : List (Fin k × Fin k)) (f : MvPolynomial (Fin k) K) : MvPolynomial (Fin k) K :=
  l.foldr (fun y f => X y.1 * pderiv y.2 f) f

def blockEmb (K : Type*) [CommRing K] {S : Type*} {k n : ℕ} (s : S) :
    MvPolynomial (Fin k × Fin n) K →ₐ[K] MvPolynomial (S × (Fin k × Fin n)) K :=
  rename fun v => (s, v)

def tensorLat (R K : Type*) [CommRing R] [CommRing K] [Algebra R K] {S : Type*} [Fintype S] {k n : ℕ}
    (M : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) : Submodule R (MvPolynomial (S × (Fin k × Fin n)) K) :=
  Submodule.span R {P | ∃ F : S → MvPolynomial (Fin k × Fin n) K, (∀ s, F s ∈ M s) ∧ P = ∏ s, blockEmb K s (F s)}

def multideg {ι : Type*} {n : ℕ} (m : ι × Fin n →₀ ℕ) (i : ι) : ℕ := ∑ c : Fin n, m (i, c)

def Pol (R : Type*) [CommSemiring R] {ι : Type*} (n : ℕ) (d : ι → ℕ) :
    Submodule R (MvPolynomial (ι × Fin n) R) :=
  MvPolynomial.restrictSupport R {m | ∀ i, multideg m i = d i}

section Multi

variable {S : Type} [Fintype S] [DecidableEq S]

def Th0 (R : Type) [CommRing R] (m : ℕ) (vec : S → Bool) :
    MvPolynomial (S × Fin (m + 1)) R →ₐ[R] MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) R :=
  aeval fun v => blockEmb R v.1 (Nv R m (vec v.1) v.2)

end Multi

def opWord {R : Type} [CommRing R] {n' k : ℕ} (l : List (Fin n' × (Fin k × Fin k))) (f : MvPolynomial (Fin n' × Fin k) R) :
    MvPolynomial (Fin n' × Fin k) R :=
  l.foldr (fun y f => X (y.1, y.2.1) * pderiv (y.1, y.2.2) f) f

def FockRBlock : Prop :=
  ∀ (K S : Type) [CommRing K] [Fintype S] (k n : ℕ) (F G : S → MvPolynomial (Fin k × Fin n) K),
    fockR (∏ s, blockEmb K s (F s)) (∏ s, blockEmb K s (G s)) = ∏ s, fockR (F s) (G s)

def OnePos : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (m : ℕ), 1 ≤ m → ∀ (vec : Bool) (d c : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν 0 ≤ c →
    ∀ β ∈ dualWeyl K (m + 1) (m + 1) ν, ∀ s ∈ dualWeyl K (m + 1) (m + 1) ν,
      ∃ (L : Finset (List (Fin (m + 1) × Fin (m + 1)))) (a : List (Fin (m + 1) × Fin (m + 1)) → K),
        (∀ l ∈ L, l.length ≤ c) ∧
        ∀ P ∈ Hd K (m + 1) d, ∀ Q ∈ Hd K (m + 1) d,
          fockR (theta K m vec P * s) (theta K m vec Q * β) =
            fockR (theta K m vec (∑ l ∈ L, a l • word1 l P)) (theta K m vec Q)

def TenOp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n' m : ℕ), 1 ≤ m → ∀ (vec : Fin n' → Bool) (TT : Finset (Fin n')) (d : Fin n' → ℕ)
    (c : ℕ) (ν : Fin n' → Fin (m + 1) → ℕ), (∀ t, Antitone (ν t)) → (∀ t ∈ TT, ν t 0 ≤ c) → (∀ t, t ∉ TT → ν t = 0) →
    ∀ β ∈ tensorLat K K (fun t => dualWeyl K (m + 1) (m + 1) (ν t)),
    ∀ s ∈ tensorLat K K (fun t => dualWeyl K (m + 1) (m + 1) (ν t)),
      ∃ (L : Finset (List (Fin n' × (Fin (m + 1) × Fin (m + 1))))) (a : List (Fin n' × (Fin (m + 1) × Fin (m + 1))) → K),
        (∀ l ∈ L, (∀ z ∈ l, z.1 ∈ TT) ∧ ∀ t, (l.filter fun z => z.1 = t).length ≤ c) ∧
        ∀ G ∈ Pol K (ι := Fin n') (m + 1) d, (∑ l ∈ L, a l • opWord l G) ∈ Pol K (ι := Fin n') (m + 1) d ∧
          ∀ H ∈ Pol K (ι := Fin n') (m + 1) d,
            fockR (Th0 K m vec G * s) (Th0 K m vec H * β) = fockR (Th0 K m vec (∑ l ∈ L, a l • opWord l G)) (Th0 K m vec H)

end PI.TO

namespace PI

def TenOp : Prop := PI.TO.FockRBlock → PI.TO.OnePos → PI.TO.TenOp

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.HermLatFin
section
open NumberField Matrix
open scoped ComplexOrder

noncomputable section

namespace PI.HermLatFin

def herm {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  ∑ i, ∑ j, σ (x i) * J i j * y j

def IsLat {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin n → E)) = ⊤

def admitted {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (T : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  IsLat L ∧ (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (herm σ J x y)) ∧
    ∀ y : Fin n → E, (∀ x ∈ L, IsIntegral ℤ (herm σ J x y)) → (T : E) • y ∈ L

def IsUJ {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J g : Matrix (Fin n) (Fin n) E) : Prop :=
  (g.map σ)ᵀ * J * g = J

def HermLatFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (T : ℕ),
    (∀ τ : E →+* ℂ, ∀ a : E, τ (σ a) = starRingEnd ℂ (τ a)) →
    (∀ τ : E →+* ℂ, (J.map τ).PosDef) →
    0 < T →
    ∃ S : Set (Submodule (𝓞 E) (Fin n → E)), S.Finite ∧
      ∀ L, admitted σ J T L → ∃ L' ∈ S, ∃ g : Matrix (Fin n) (Fin n) E, IsUJ σ J g ∧
        (fun x => g *ᵥ x) '' (L' : Set (Fin n → E)) = (L : Set (Fin n → E))

end PI.HermLatFin
end
end

-- bundled from Formalism.PeriodIntegrals.IndexUBound
section
namespace PI.IndexUBound

def IndexUBound : Prop :=
  ∀ (ι : Type) (S : Finset ι) (g : ι → ℕ) (r : ℕ) (y : ℝ),
    (∀ v ∈ S, 2 ≤ g v) → ∑ v ∈ S, 1 / ((g v : ℝ) - 1) ≤ y →
      (1 - y) * ∏ v ∈ S, (g v : ℝ) ^ (r * (r - 1) / 2) ≤
        ∏ v ∈ S, ∏ i ∈ Finset.Ico 1 r, ((g v : ℝ) ^ i - 1)

end PI.IndexUBound
end

-- bundled from Formalism.PeriodIntegrals.InertPrime
section
open NumberField

namespace PI

def InertPrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (b : K) (d p : ℕ), b ^ 2 = -(d : K) → p.Prime →
    jacobiSym (-(d : ℤ)) p = -1 → (Ideal.span {(p : 𝓞 K)}).IsPrime

end PI
end

-- bundled from Formalism.PeriodIntegrals.JetsPhW
section
noncomputable section

open Classical

namespace PI.JetsPhW

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

def dX {A : Type*} [CommRing A] (f : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => ((n : A) + 1) * PowerSeries.coeff (n + 1) f

def IsWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Prop :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  wq = 1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3

def omegaW {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  (-(2 : PowerSeries ℂ_[p]) * wq - X * dX wq) * (wq * (c W.a₁ * X + c W.a₃ * X ^ 3 * wq - 2))⁻¹

def flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) (omegaW W wq) / n

section Ops

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

def add (l ex : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex

def mulBy (l ex : PowerSeries ℂ_[p]) (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex

def phAt (ph : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a ph

def be (l ex ph : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  phAt ph (add l ex a b) - phAt ph a - phAt ph b

end Ops

def jet {p : ℕ} [Fact p.Prime] (ex ph : PowerSeries ℂ_[p]) (i : ℕ) : ℂ_[p] :=
  (i.factorial : ℂ_[p]) * PowerSeries.coeff i (PowerSeries.subst ex ph : PowerSeries ℂ_[p])

def cubeE {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  phAt ph (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2)) - phAt ph (add l ex (Xv 0) (Xv 1)) -
    phAt ph (add l ex (Xv 1) (Xv 2)) - phAt ph (add l ex (Xv 2) (Xv 0)) +
    phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2)

def High : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex ph : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X →
    Simeq (cubeE (flog W wq) ex ph) 0 →
    ∀ i : ℕ, i ≠ 1 → i ≠ 2 → IsIntP (jet ex ph i)

def One : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex ph : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X → p ≠ 2 →
    Simeq (phAt ph (mulBy (flog W wq) ex (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) (phAt ph (Xv ())) →
    IsIntP (jet ex ph 1)

def Two : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex ph : PowerSeries ℂ_[p]) (a b : ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X →
    Simeq (be (flog W wq) ex ph (mulBy (flog W wq) ex a (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be (flog W wq) ex ph (Xv 0) (mulBy (flog W wq) ex b (Xv 1))) →
    IsIntP ((a - b) * jet ex ph 2)

def Target : Prop := High ∧ One ∧ Two

def LogOk {p : ℕ} [Fact p.Prime] (l ex : PowerSeries ℂ_[p]) : Prop :=
  PowerSeries.constantCoeff ex = 0 ∧ PowerSeries.subst ex l = PowerSeries.X ∧
    ∃ v : PowerSeries ℂ_[p], (∀ n, IsIntP (PowerSeries.coeff n v)) ∧ v * dX l = 1

def InvOmega : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    ∃ v : PowerSeries ℂ_[p], (∀ n, IsIntP (PowerSeries.coeff n v)) ∧ v * dX (flog W wq) = 1

def HighG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), LogOk l ex →
    Simeq (cubeE l ex ph) 0 → ∀ i : ℕ, i ≠ 1 → i ≠ 2 → IsIntP (jet ex ph i)

def OneG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), LogOk l ex → p ≠ 2 →
    Simeq (phAt ph (mulBy l ex (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) (phAt ph (Xv ())) →
    IsIntP (jet ex ph 1)

def TwoG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (a b : ℂ_[p]), LogOk l ex →
    Simeq (be l ex ph (mulBy l ex a (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex b (Xv 1))) →
    IsIntP ((a - b) * jet ex ph 2)

def Glue : Prop := InvOmega → HighG → OneG → TwoG → Target

end PI.JetsPhW
end
end

-- bundled from Formalism.PeriodIntegrals.KerLat
section
noncomputable section
open NumberField

namespace PI.KerLat

def PerPair : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Module.finrank ℚ K = 2 → (∃ k : K, (φ k).im ≠ 0) → cc ≠ ⊥ → δ ≠ 0 →
      ∃ L : PeriodPair, L.lattice.toAddSubgroup = AddSubgroup.closure {w : ℂ | ∃ c ∈ cc, w = δ * φ (c : K)}

end PI.KerLat
end
end

