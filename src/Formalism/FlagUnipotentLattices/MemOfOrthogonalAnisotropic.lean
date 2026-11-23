module

public import Mathlib
public import Formalism.HyperbolicPlaceProducts.Bundle0001

@[expose] public section

noncomputable section

open scoped BigOperators
open Matrix

namespace Formalism.HermitianLatticeCounting.S6

structure HermSpace (K : Type) [Field K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V] where
  B : V →ₗ[K] V →ₗ⋆[K] K
  herm : ∀ x y : V, star (B x y) = B y x
  nondeg : ∀ x : V, (∀ y : V, B x y = 0) → x = 0

section Flags

variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]

structure FlagD (H : HermSpace K V) (r : ℕ) where
  e : Fin (r + 1) → V
  T : K
  indep : LinearIndependent K (fun a : Fin r => e a.castSucc)
  iso : ∀ a b : Fin r, H.B (e a.castSucc) (e b.castSucc) = 0
  zperp : ∀ a : Fin r, H.B (e a.castSucc) (e (Fin.last r)) = 0
  zz : H.B (e (Fin.last r)) (e (Fin.last r)) = -T
  hT : T ≠ 0

namespace FlagD

variable {H : HermSpace K V} {r : ℕ} (F : FlagD H r)

def z : V := F.e (Fin.last r)

def Xa (a : ℕ) : Submodule K V :=
  Submodule.span K ((fun b : Fin r => F.e b.castSucc) '' {b | b.val < a})

def X : Submodule K V := F.Xa r

def Aniso : Prop :=
  ∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → H.B w w = 0 → w ∈ F.X

def HasLevel (x : V) (a : Fin r) (al : K) : Prop :=
  al ≠ 0 ∧ x - al • F.e a.castSucc ∈ F.Xa a.val

def LieN (Y : V →ₗ[K] V) : Prop :=
  (∀ x y : V, H.B (Y x) y + H.B x (Y y) = 0) ∧
  (∀ a : Fin r, Y (F.e a.castSucc) ∈ F.Xa a.val) ∧
  (∀ y : V, (∀ a : Fin r, H.B (F.e a.castSucc) y = 0) → Y y ∈ F.X)

def DPsi (Y : V →ₗ[K] V) (s : K) : Prop :=
  ∃ c : Fin r → K, ∑ a, c a = s ∧
    ∀ a : Fin r, Y (F.e a.succ) - c a • F.e a.castSucc ∈ F.Xa a.val

def InN (g : V →ₗ[K] V) : Prop :=
  (∀ x y : V, H.B (g x) (g y) = H.B x y) ∧ Function.Bijective g ∧
  (∀ a : Fin r, g (F.e a.castSucc) - F.e a.castSucc ∈ F.Xa a.val) ∧
  (∀ y : V, (∀ a : Fin r, H.B (F.e a.castSucc) y = 0) → g y - y ∈ F.X)

def PosDefAt (σ : K →+* ℂ) : Prop :=
  ∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → w ∉ F.X → 0 < (σ (H.B w w)).re

end FlagD

variable {H : HermSpace K V} {r : ℕ}

def II (F F' : FlagD H r) : Submodule K V := F.X ⊓ F'.X

def Relevant (F F' : FlagD H r) : Prop :=
  ∀ Y : V →ₗ[K] V, F.LieN Y → F'.LieN Y → ∀ s s' : K, F.DPsi Y s → F'.DPsi Y s' →
    s + star s = s' + star s'

def Zhat (F F' : FlagD H r) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun a b => H.B (F.e a) (F'.e b)

def Dl (F F' : FlagD H r) (l : ℕ) (hl : l ≤ r + 1) : K :=
  ((Zhat F F').submatrix (Fin.castLE hl) (Fin.castLE hl)).det

def Gval (F F' : FlagD H r) : K :=
  Dl F F' (r + 1) le_rfl * star (Dl F F' (r + 1) le_rfl) -
    F.T * F'.T * (Dl F F' r (Nat.le_succ r) * star (Dl F F' r (Nat.le_succ r)))

def Gram (F F' : FlagD H r) : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K :=
  Matrix.of fun p q => H.B (Sum.elim F.e F'.e p) (Sum.elim F.e F'.e q)

def xv (H : HermSpace K V) (x v : V) : V →ₗ[K] V :=
  (H.B.flip v).smulRight x - (H.B.flip x).smulRight v

def V0 (F F' : FlagD H r) : Submodule K V :=
  F.X ⊔ F'.X ⊔ Submodule.span K {F.z, F'.z}

def SigPerp (F F' : FlagD H r) (σ : K →+* ℂ) : Prop :=
  ∃ z₀ : V, (∀ v ∈ F.X ⊔ F'.X, H.B v z₀ = 0) ∧ (σ (H.B z₀ z₀)).re < 0 ∧
    ∀ w : V, (∀ v ∈ F.X ⊔ F'.X, H.B v w = 0) → H.B w z₀ = 0 → w ≠ 0 → 0 < (σ (H.B w w)).re

def NFShape (F F' : FlagD H r) (j : ℕ) (c : K) : Prop :=
  c ≠ 0 ∧
  Module.finrank K (II F F') = r - j ∧
  (∀ x ∈ II F F', x ≠ 0 → ∃ (a : Fin r) (al al' : K),
    F.HasLevel x a al ∧ F'.HasLevel x a al' ∧ j ≤ a.val ∧ al = c * al') ∧
  (∀ a : Fin r, j ≤ a.val → ∃ x ∈ II F F', ∃ al al' : K, F.HasLevel x a al ∧ F'.HasLevel x a al') ∧
  II F F' ⊓ F.Xa j = ⊥ ∧ II F F' ⊓ F'.Xa j = ⊥ ∧
  F.X = F.Xa j ⊔ II F F' ∧ F'.X = F'.Xa j ⊔ II F F' ∧
  F'.z - c • F.z ∈ F.X ⊔ F'.X

def NFFull (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (c : K) : Prop :=
  NFShape F F' j c ∧
  c * star c * F.T = F'.T ∧
  Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0 ∧
  (∀ v ∈ V0 F F', (∀ w ∈ V0 F F', H.B v w = 0) ↔ v ∈ II F F') ∧
  Module.finrank K (V0 F F') = r + j + 1 ∧
  (∀ x ∈ F.X, (∀ w ∈ V0 F F', H.B w x = 0) ↔ x ∈ II F F') ∧
  (∀ x ∈ F'.X, (∀ w ∈ V0 F F', H.B w x = 0) ↔ x ∈ II F F') ∧
  (∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → ∃ x ∈ F.X, ∀ v ∈ V0 F F', H.B v (w - x) = 0) ∧
  (∀ w : V, (∀ a : Fin (r + 1), H.B (F'.e a) w = 0) → ∃ x ∈ F'.X, ∀ v ∈ V0 F F', H.B v (w - x) = 0)

def eich (H : HermSpace K V) (x v : V) (c : K) : V →ₗ[K] V :=
  LinearMap.id + xv H x v + c • (H.B.flip x).smulRight x

def IsLift (F F' : FlagD H r) (Wt : Submodule K V) : Prop :=
  (∀ w ∈ Wt, ∀ y ∈ V0 F F', H.B y w = 0) ∧ Wt ⊓ II F F' = ⊥ ∧
  ∀ w : V, (∀ y ∈ V0 F F', H.B y w = 0) → w ∈ Wt ⊔ II F F'

end Flags

def Y1 : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F : FlagD H r) (x v : V) (a : Fin r) (al : K),
    F.HasLevel x a al → (∀ b : Fin r, b ≤ a → H.B (F.e b.castSucc) v = 0) →
      (∀ y ∈ F.Xa (a.val + 1), xv H x v y = 0) ∧
      (∀ y : V, (∀ b : Fin r, H.B (F.e b.castSucc) y = 0) → xv H x v y ∈ K ∙ x) ∧
      F.LieN (xv H x v) ∧ F.DPsi (xv H x v) (al * H.B (F.e a.succ) v)

def LastVectorNotMemSup : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r), F.z ∉ F.X ⊔ F'.X

def PerpPerp : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : HermSpace K V) (S : Submodule K V) (w : V),
    (∀ v : V, (∀ s ∈ S, H.B s v = 0) → H.B w v = 0) → w ∈ S

def NFStep : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r) (x : V) (a a' : Fin r) (al al' : K),
    (∃ μ : K, μ + star μ ≠ 0) → Relevant F F' → x ∈ II F F' → F.HasLevel x a al → F'.HasLevel x a' al' →
      al • F.e a.succ - al' • F'.e a'.succ ∈ F.Xa (a.val + 1) ⊔ F'.Xa (a'.val + 1)

def NFCaseA : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r),
    (∃ μ : K, μ + star μ ≠ 0) → Relevant F F' → II F F' ≠ ⊥ →
      ∃ (j : ℕ) (c : K), j < r ∧ NFShape F F' j c

def NFCaseB : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r), Dl F F' r (Nat.le_succ r) ≠ 0 →
      ∃ x ∈ F.X, ∃ x' ∈ F'.X,
        (∀ w ∈ F.X ⊔ F'.X, H.B w (F.z - x) = 0) ∧ (∀ w ∈ F.X ⊔ F'.X, H.B w (F'.z - x') = 0) ∧
        H.B (F.z - x) (F.z - x) = -F.T ∧ H.B (F'.z - x') (F'.z - x') = -F'.T ∧
        Dl F F' (r + 1) le_rfl = Dl F F' r (Nat.le_succ r) * H.B (F.z - x) (F'.z - x') ∧
        Gval F F' = Dl F F' r (Nat.le_succ r) * star (Dl F F' r (Nat.le_succ r)) *
          (H.B (F.z - x) (F'.z - x') * star (H.B (F.z - x) (F'.z - x')) - F.T * F'.T)

def NFCaseC : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r), F.Aniso → F'.Aniso → II F F' = ⊥ → Dl F F' r (Nat.le_succ r) = 0 →
      Gval F F' = 0 → False

def NFDj : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (c : K), F'.Aniso →
      II F F' ⊓ F.Xa j = ⊥ → F'.X = F'.Xa j ⊔ II F F' → F'.z - c • F.z ∈ F.X ⊔ F'.X →
      Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0

def NFAbsC : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (c : K),
      F.X = F.Xa j ⊔ II F F' → F'.X = F'.Xa j ⊔ II F F' → F'.z - c • F.z ∈ F.X ⊔ F'.X →
      Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0 → c * star c * F.T = F'.T

def JointSpanRadical : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (c : K), F'.Aniso →
      II F F' ⊓ F.Xa j = ⊥ → II F F' ⊓ F'.Xa j = ⊥ →
      F.X = F.Xa j ⊔ II F F' → F'.X = F'.Xa j ⊔ II F F' → F'.z - c • F.z ∈ F.X ⊔ F'.X →
      Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0 →
        (∀ v ∈ V0 F F', (∀ w ∈ V0 F F', H.B v w = 0) ↔ v ∈ II F F') ∧
        Module.finrank K (V0 F F') = r + j + 1 ∧
        (∀ x ∈ F.X, (∀ w ∈ V0 F F', H.B w x = 0) ↔ x ∈ II F F')

def JointSpanComplement : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (c : K),
      F'.X = F'.Xa j ⊔ II F F' → F'.z - c • F.z ∈ F.X ⊔ F'.X →
      Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0 →
        ∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) →
          ∃ x ∈ F.X, ∀ v ∈ V0 F F', H.B v (w - x) = 0

def NFCUnique : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (c₁ c₂ : K),
      F'.z - c₁ • F.z ∈ F.X ⊔ F'.X → F'.z - c₂ • F.z ∈ F.X ⊔ F'.X → c₁ = c₂

def NFJZero : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (c : K), NFShape F F' 0 c →
      (∀ a : ℕ, F'.Xa a = F.Xa a) ∧
      (∀ a : Fin r, F'.e a.castSucc - c • F.e a.castSucc ∈ F.Xa a.val) ∧
      F'.z - c • F.z ∈ F.X

def AnisoOfPosDef : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (σ : K →+* ℂ)
    (H : HermSpace K V) (r : ℕ) (F : FlagD H r), F.PosDefAt σ → F.Aniso

def NFCaseBSig : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (σ : K →+* ℂ)
    (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r), 0 < (σ F.T).re → F.PosDefAt σ →
    Dl F F' r (Nat.le_succ r) ≠ 0 → SigPerp F F' σ

def NFCaseBConcl : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (σ : K →+* ℂ)
    (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r), (∀ x : K, σ (star x) = star (σ x)) →
    0 < (σ F.T).re → 0 < (σ F'.T).re → SigPerp F F' σ →
    Dl F F' r (Nat.le_succ r) ≠ 0 → Gval F F' = 0 →
      ∃ c : K, F'.z - c • F.z ∈ F.X ⊔ F'.X

def NormalForm : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (σ : K →+* ℂ) (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r),
    (∀ x : K, σ (star x) = star (σ x)) → 0 < (σ F.T).re → 0 < (σ F'.T).re →
    F.PosDefAt σ → F'.PosDefAt σ → Relevant F F' → Gval F F' = 0 →
      ∃ (j : ℕ) (hj : j ≤ r) (c : K), NFFull F F' j hj c

def ExtPowerBound : Prop :=
  ∀ (j m : ℕ) (A A' : Matrix (Fin j) (Fin m) ℂ) (Z : Matrix (Fin j) (Fin j) ℂ),
    (∀ w₁ w₂ : Fin m → ℂ, ∑ i, ‖w₁ i‖ ^ 2 ≤ 1 → ∑ i, ‖w₂ i‖ ^ 2 ≤ 1 →
      ‖∑ a, ∑ b, (A *ᵥ w₁) a * Z a b * star ((A' *ᵥ w₂) b)‖ ≤ 2) →
    Real.sqrt ‖(A * Aᴴ).det‖ * Real.sqrt ‖(A' * A'ᴴ).det‖ * ‖Z.det‖ ≤ 2 ^ j

def NormSgBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (r f : ℕ) (D sg : ι → ℝ) (H₁ Hh : ℝ), Fintype.card ι = f → 1 / 2 ≤ H₁ →
    (2 * H₁) ^ (4 * r * f) ≤ Hh → (∀ v, 0 ≤ D v) → (∀ v, 1 ≤ sg v) →
    (∀ v, D v / (2 * H₁) ^ (2 * r) ≤ sg v) →
      ∏ v, D v ^ 2 ≤ Hh * ∏ v, sg v ^ 2

def CfBound : Prop :=
  ∀ f x k : ℕ, 1 ≤ f → 1 ≤ x →
    ((2 * f : ℕ) : ℝ) ^ (Nat.primeFactorsList x).length * (x : ℝ) ^ k ≤
      (x : ℝ) ^ ((k : ℝ) + (1 + Real.logb 2 (2 * f)))

def SublatticeCount : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M]
    [Module (NumberField.RingOfIntegers E) M] [Module.Finite (NumberField.RingOfIntegers E) M]
    [Module.Projective (NumberField.RingOfIntegers E) M] (f x : ℕ),
    Module.finrank ℚ E = 2 * f → 1 ≤ x →
      {N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = x}.Finite ∧
      (({N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = x}.ncard : ℕ) : ℝ) ≤
        (x : ℝ) ^ ((Module.finrank (NumberField.RingOfIntegers E) M : ℝ) + (1 + Real.logb 2 (2 * f)))

def EichlerIsom : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (x v : V)
    (c : K), H.B x x = 0 → H.B x v = 0 → c + star c = -H.B v v →
      (∀ y y' : V, H.B (eich H x v c y) (eich H x v c y') = H.B y y') ∧
      (∀ y : V, eich H x (-v) (star c) (eich H x v c y) = y) ∧
      (∀ y : V, eich H x v c (eich H x (-v) (star c) y) = y)

def EichlerInR : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (x v : V) (c : K),
    x ∈ II F F' → (∀ y ∈ V0 F F', H.B y v = 0) → c + star c = -H.B v v →
      (∀ y ∈ V0 F F', eich H x v c y = y) ∧ F.InN (eich H x v c) ∧ F'.InN (eich H x v c) ∧
      (∀ w : V, (∀ y ∈ V0 F F', H.B y w = 0) → eich H x v c w = w + H.B w v • x)

def LiftTransitive : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r) (W₁ W₂ : Submodule K V),
    (∃ μ : K, μ + star μ ≠ 0) → F.Aniso → F'.Aniso → IsLift F F' W₁ → IsLift F F' W₂ →
      ∃ g : V →ₗ[K] V, F.InN g ∧ F'.InN g ∧ (∀ y ∈ V0 F F', g y = y) ∧ W₁.map g = W₂

def bEta {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]
    (h : U →ₗ[K] U →ₗ⋆[K] K) (η : U →ₗ[K] U) (x' x'' : U) : K := h x' (x'' - η x'')

def DetBBoundK : Prop :=
  ∀ (K U : Type) [Field K] [StarRing K] [AddCommGroup U] [Module K U] (σ : K →+* ℂ)
    (h : U →ₗ[K] U →ₗ⋆[K] K) (η : U →ₗ[K] U), (∀ x : K, σ (star x) = star (σ x)) →
    (∀ x y : U, star (h x y) = h y x) → (∀ w : U, w ≠ 0 → 0 < (σ (h w w)).re) →
    (∀ x y : U, h (η x) (η y) = h x y) → ∀ (s : ℕ) (u w : Fin s → U),
      ‖σ (Matrix.of fun a b => bEta h η (u a) (w b)).det‖ ≤
        2 ^ s * Real.sqrt ‖σ (Matrix.of fun a b => h (u a) (u b)).det‖ *
          Real.sqrt ‖σ (Matrix.of fun a b => h (w a) (w b)).det‖

def minkowskiExp (N p : ℕ) : ℕ := ∑ i ∈ Finset.range (N + 1), N / (p ^ i * (p - 1))

def minkowskiM (N : ℕ) : ℕ := ∏ p ∈ (Finset.range (N + 2)).filter Nat.Prime, p ^ minkowskiExp N p

def MinkowskiBound : Prop :=
  ∀ (N : ℕ) (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ)), Finite G →
    Nat.card G ∣ minkowskiM N

def MinkowskiDvdFactorial : Prop := ∀ N : ℕ, minkowskiM N ∣ (2 * N).factorial

def FinalSum : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k r f : ℕ) (b d : ℝ), 2 ≤ b → 1 ≤ f → 0 ≤ d →
    C₀ * ((2 * r + 2 : ℕ) : ℝ) ^ 6 * Real.log b ≤ (k : ℝ) * Real.log k →
      2 * d * (∑ j ∈ Finset.Icc 1 r,
          Real.exp (C * ((2 * r + 2 : ℕ) : ℝ) ^ 6 * f * Real.log b) * (C / k) ^ (j * (k - 1 - j) * f)) ^ 2 ≤
        d * Real.exp (-((k : ℝ) * f * Real.log k))

end Formalism.HermitianLatticeCounting.S6
