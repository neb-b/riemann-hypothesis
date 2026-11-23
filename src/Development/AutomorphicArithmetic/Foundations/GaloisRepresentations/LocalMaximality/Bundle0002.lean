module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0069

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
section
set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 GlobalTheory.W1.Lef
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {F : Type} [Field F] [Algebra ℂ F] {V V' : Type} [AddCommGroup V] [Module F V] [Module ℂ V] [IsScalarTower ℂ F V]
  [AddCommGroup V'] [Module F V'] [Module ℂ V'] [IsScalarTower ℂ F V']

def Lat (A : Subalgebra ℂ F) (M : Submodule ℂ V) : Prop :=
  (∀ a ∈ A, ∀ m ∈ M, a • m ∈ M) ∧ ∃ (n : ℕ) (v : Fin n → V) (φ : Fin n → V →ₗ[F] F), (∀ k, v k ∈ M) ∧ (∀ k, ∀ m ∈ M, φ k m ∈ A) ∧
    ∀ m ∈ M, m = ∑ k, φ k m • v k


variable (F V V') in
def actF : F ⊗[ℂ] F →ₐ[ℂ] Module.End ℂ (V ⊗[ℂ] V') :=
  (Module.endTensorEndAlgHom).comp (Algebra.TensorProduct.map (Algebra.lsmul ℂ ℂ V) (Algebra.lsmul ℂ ℂ V'))


variable (V') in
def ctrF (ψ : V →ₗ[F] F) : V ⊗[ℂ] V' →ₗ[ℂ] V' := TensorProduct.lift ((Algebra.lsmul ℂ ℂ V').toLinearMap ∘ₗ ψ.restrictScalars ℂ)

def f0 {d : ℕ} (x : Fin (d + 1) → Fˣ) (j : Fin (d + 1)) (l : Fin d) : F ⊗[ℂ] F :=
  ((x (j.succAbove l) : F) / x j) ⊗ₜ 1 - 1 ⊗ₜ ((x (j.succAbove l) : F) / x j)

def R0 {d : ℕ} (x : Fin (d + 1) → Fˣ) (I J : Finset (Fin (d + 1))) : Subalgebra ℂ (F ⊗[ℂ] F) :=
  (Algebra.TensorProduct.map (rA ℂ (xv x) I).val (rA ℂ (xv x) J).val).range

def omG {d : ℕ} (x : Fin (d + 1) → Fˣ) (i : Fin (d + 1)) : F := ∏ l, ((x l : F) / x i)


variable (V') in
def resP (ρ : F →ₗ[ℂ] ℂ) : F ⊗[ℂ] V' →ₗ[ℂ] V' := TensorProduct.lift ((LinearMap.lsmul ℂ V') ∘ₗ ρ)

end

section
variable {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

structure ZF {κ : Type} [LinearOrder κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K) : Prop where
  adm : (sysZ K x 0).admitted n z
  diag : ∀ l, Algebra.TensorProduct.lmul' ℂ (z l) = 0
  gen : ∀ i, Algebra.adjoin ℂ {b : K | b ∈ rB ℂ K (xv x) {i} ∧ ∃ l N, n l = (N, N) ∧
    z l = (((sysZ K x 0).X i ^ N * (sysZ K x 0).Y i ^ N : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) * (b ⊗ₜ 1 - 1 ⊗ₜ b)} = rB ℂ K (xv x) {i}

def IsDiag (τ : DR ℂ K →ₗ[K] K) (a : ℕ) (c : Finset (Two d ⊕ₗ Mi d) → DR ℂ K ⊗[ℂ] DR ℂ K) : Prop :=
  ∀ i j L, L.card = d → Acts (F := F) K τ a (c (uni (uni {i} {j}) L)) ((-1) ^ d * kap K x L)

abbrev pr (τ : DR ℂ K →ₗ[K] K) (ρ : F →ₗ[ℂ] ℂ) : (Finset (Fin (d + 1)) → DR ℂ K) →ₗ[ℂ] (Finset (Fin (d + 1)) → DR ℂ K) →ₗ[ℂ] ℂ :=
  cupPair ((LinearMap.mul ℂ (DR ℂ K)).compr₂ (trF ℂ τ ρ))

end

def GoodZ : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ a : ℕ, (sysZ K x a).Good ∧ (sysP K x a).Good ∧
  ∀ s t : Finset (Fin (d + 1)), s.Nonempty → s ⊆ t → omB ℂ K (rB ℂ K (xv x) s) a ≤ omB ℂ K (rB ℂ K (xv x) t) a

def LatOm : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (a : ℕ) (I : Finset (Fin (d + 1))), I.Nonempty →
  Lat (rA ℂ (xv x) I) (omB ℂ K (rB ℂ K (xv x) I) a) ∧
  ∀ w ∈ ⋀[K]^a Ω[K⁄ℂ], w ∈ Submodule.span F (omB ℂ K (rB ℂ K (xv x) I) a : Set (DR ℂ K))

def LatA : Prop := ∀ (F : Type) [Field F] [Algebra ℂ F] (d : ℕ) (x : Fin (d + 1) → Fˣ), IsPd ℂ (xv x) → ∀ (I : Finset (Fin (d + 1))), ∀ i ∈ I, Lat (rA ℂ (xv x) I) (omA ℂ (xv x) I) ∧
  (∀ y : F, y ∈ omA ℂ (xv x) I ↔ y / omG x i ∈ rA ℂ (xv x) I) ∧
  ∀ j, ∀ y ∈ omA ℂ (xv x) (insert j I), ∃ N : ℕ, ((x j : F) / x i) ^ N * y ∈ omA ℂ (xv x) I

def Reg0 : Prop := ∀ (F : Type) [Field F] [Algebra ℂ F] (d : ℕ) (x : Fin (d + 1) → Fˣ), IsPd ℂ (xv x) → ∀ (I J : Finset (Fin (d + 1))), ∀ j ∈ I, j ∈ J →
  Reg (Algebra.lmul ℂ (F ⊗[ℂ] F)) (Subalgebra.toSubmodule (R0 x I J)) (f0 x j)

def Ker0 : Prop := ∀ (F : Type) [Field F] [Algebra ℂ F] (d : ℕ) (x : Fin (d + 1) → Fˣ), IsPd ℂ (xv x) → ∀ (I J : Finset (Fin (d + 1))), ∀ j ∈ I, j ∈ J → ∀ m ∈ R0 x I J,
  Algebra.TensorProduct.lmul' ℂ m = 0 →
  m ∈ sm (Algebra.lmul ℂ (F ⊗[ℂ] F)) (Subalgebra.toSubmodule (R0 x I J)) (Set.range (f0 x j))

def RegLat : Prop := ∀ (F : Type) [Field F] [Algebra ℂ F] (d : ℕ) (x : Fin (d + 1) → Fˣ), IsPd ℂ (xv x) → ∀ (V V' : Type) [AddCommGroup V] [Module F V] [Module ℂ V] [IsScalarTower ℂ F V]
  [AddCommGroup V'] [Module F V'] [Module ℂ V'] [IsScalarTower ℂ F V'] (I J : Finset (Fin (d + 1))) (M : Submodule ℂ V)
  (M' : Submodule ℂ V'), Lat (rA ℂ (xv x) I) M → Lat (rA ℂ (xv x) J) M' → ∀ j ∈ I, j ∈ J →
  Reg (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') (f0 x j) ∧
  ∀ m ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M', (∀ ψ : V →ₗ[F] F, ctrF V' ψ m = 0) →
    m ∈ sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') (Set.range (f0 x j))

def DualForm : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ ψ : DR ℂ K →ₗ[F] F,
  (∃ w ∈ ⋀[K]^a Ω[K⁄ℂ], ∀ y ∈ ⋀[K]^(d - a) Ω[K⁄ℂ], ψ y = Algebra.trace F K (τ (y * w))) ∧
  ∃ w ∈ ⋀[K]^(d - a) Ω[K⁄ℂ], ∀ y ∈ ⋀[K]^a Ω[K⁄ℂ], ψ y = Algebra.trace F K (τ (w * y))

def ColZ : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ I J, ∀ i ∈ I, ∀ j ∈ J,
  KE (kos (sysZ K x a).act ((sysZ K x a).M I J) fun l => (sysZ K x a).r n11 (sysZ K x a).mu i j (dj j l)) d ∧
  ∀ m ∈ (sysZ K x a).M I J, Acts (F := F) K τ a m 0 →
    m ∈ sm (sysZ K x a).act ((sysZ K x a).M I J) (Set.range fun l => (sysZ K x a).r n11 (sysZ K x a).mu i j (dj j l))

def ColP : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ a I J, ∀ i ∈ I, ∀ j ∈ J,
  KE (kos (sysP K x a).act ((sysP K x a).M I J) fun l => (sysP K x a).r n11 (sysP K x a).mu i j (dj j l)) d ∧
  ∀ m ∈ (sysP K x a).M I J, mulP F K m = 0 →
    m ∈ sm (sysP K x a).act ((sysP K x a).M I J) (Set.range fun l => (sysP K x a).r n11 (sysP K x a).mu i j (dj j l))

def ActsLin : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a : ℕ,
  (∀ m m' c c', Acts (F := F) K τ a m c → Acts (F := F) K τ a m' c' →
    Acts (F := F) K τ a (m + m') (c + c') ∧ Acts (F := F) K τ a (m - m') (c - c')) ∧
  (∀ m c s, Acts (F := F) K τ a m c → Acts (F := F) K τ a (actZ K s m) (Algebra.TensorProduct.lmul' ℂ s * c)) ∧
  (∀ i j M m, m ∈ sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)) → Acts (F := F) K τ a m 0) ∧
  (∀ (u : (K ⊗[ℂ] K)ˣ) M m i j, m ∈ sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)) →
    Acts (F := F) K τ a (actZ K u m) 0) ∧
  (∀ (s : F ⊗[ℂ] K) m, mulP F K ((sysP K x a).act s m) =
    Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom ℂ F K) (AlgHom.id ℂ K) s • mulP F K m) ∧
  ∀ (s : F ⊗[ℂ] K) m w, muP F K τ (actZ K (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℂ F K) (AlgHom.id ℂ K) s) m) w =
    (sysP K x a).act s (muP F K τ m w)

def IdJ : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ j, ∃ m ∈ (sysZ K x a).M {j} {j}, Acts (F := F) K τ a m (algebraMap F K (omG x j))

def IdIJ : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ i j, ∃ m ∈ (sysZ K x a).M {i} {j}, Acts (F := F) K τ a m (algebraMap F K (omG x i))

def ZFam : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∃ (m : ℕ) (n : Fin m → ℕ × ℕ) (z : Fin m → K ⊗[ℂ] K), ZF K x n z

def KapInd : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
  (π : S →ₐ[ℂ] K), (∀ i, π (T.X i) = algebraMap F K (x i)) → (∀ i, π (T.Y i) = algebraMap F K (x i)) →
  ∀ i L, L.card = d → π (detC T.rowMu (uni {i} L)) = kap K x L

def ZCol : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K), ZF K x n z →
  ∀ i j, ∃ c ∈ ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) {i} {j}).Z d,
    ∀ L : Finset (Mi d), L.card = d → Acts (F := F) K τ a (c (uni L ∅)) ((-1) ^ d * kap K x L)

def ZEx : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K), ZF K x n z →
  ∃ c ∈ ((sysZ K x a).cx (app n11 n) (app (sysZ K x a).mu z)).Z (d + 2), IsDiag K x τ a (resK inlE c)

def PLift : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ a I J, I.Nonempty → J.Nonempty → ∀ w ∈ omB ℂ K (rB ℂ K (xv x) (I ∪ J)) a,
  ∃ y ∈ ((sysP K x a).colCx n11 (sysP K x a).mu I J).Z d, ∀ L, L.card = d → mulP F K (y L) = kap K x L • w

def PCmp : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (a p : ℕ), ∀ c ∈ ((sysP K x a).cx n11 (sysP K x a).mu).Z (d + p + 2),
  (∀ b L, d < L.card → c (uni b L) = 0) →
  ∀ γ ∈ (acx (mixF fun I J : Finset (Fin (d + 1)) => omB ℂ K (rB ℂ K (xv x) (I ∪ J)) a) fun _ => 1).B (p + 2),
  (∀ b L, L.card = d → mulP F K (c (uni b L)) = kap K x L • γ b) → c ∈ ((sysP K x a).cx n11 (sysP K x a).mu).B (d + p + 2)

def PTheta : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (a p : ℕ), ∀ β ∈ (omCx (rB ℂ K (xv x)) a).Z p,
  ∃ c ∈ ((sysP K x a).cx n11 (sysP K x a).mu).Z (d + p + 2), (∀ b L, d < L.card → c (uni b L) = 0) ∧
    (∀ b L, L.card = d → mulP F K (c (uni b L)) = kap K x L • ((-1 : ℤ) ^ ((p + 1) * d)) • edge2 β b) ∧
    ∀ J, c (uni (uni Finset.univ J) ∅) = 1 ⊗ₜ β J

def PCup : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (a p : ℕ), a ≤ d → ∀ c ∈ ((sysZ K x a).cx n11 (sysZ K x a).mu).Z (d + 2), IsDiag K x τ a c →
  ∀ α ∈ (omCx (rB ℂ K (xv x)) a).Z p,
  rcup (muP F K τ) p c α ∈ ((sysP K x a).cx n11 (sysP K x a).mu).Z (d + p + 2) ∧
    (∀ b L, d < L.card → rcup (muP F K τ) p c α (uni b L) = 0) ∧
    ∀ b L, L.card = d → mulP F K (rcup (muP F K τ) p c α (uni b L)) = kap K x L • ((-1 : ℤ) ^ (p * (d + 1) + d)) • edge1 α b

def PInt : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ (a p : ℕ), ∀ t ∈ (sysP K x a).mix.B (d + p + 2),
  (fun J => resP (DR ℂ K) ρ (t (uni Finset.univ J))) ∈ (omCx (rB ℂ K (xv x)) a).B p

def RCupTop : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ (a p : ℕ), a ≤ d → ∀ t ∈ (sysZ K x a).mix.B (d + 2), ∀ α ∈ (omCx (rB ℂ K (xv x)) a).Z p,
  (fun J => resP (DR ℂ K) ρ (∑ i, muP F K τ (t (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))))) ∈
    (omCx (rB ℂ K (xv x)) a).B p

def ZAct : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ (a p : ℕ), a ≤ d → ∀ c ∈ ((sysZ K x a).cx n11 (sysZ K x a).mu).Z (d + 2), IsDiag K x τ a c →
  ∀ α ∈ (omCx (rB ℂ K (xv x)) a).Z p,
  α - (fun J => resP (DR ℂ K) ρ (∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))))) ∈
    (omCx (rB ℂ K (xv x)) a).B p

def ZId : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ a : ℕ, a ≤ d → ∀ c ∈ ((sysZ K x a).cx n11 (sysZ K x a).mu).Z (d + 2), IsDiag K x τ a c →
  ∃ (m : ℕ) (p : Fin m → ℕ) (e f : Fin m → Finset (Fin (d + 1)) → DR ℂ K),
    (∀ k, p k ≤ d ∧ e k ∈ (omCx (rB ℂ K (xv x)) (d - a)).Z (d - p k) ∧ f k ∈ (omCx (rB ℂ K (xv x)) a).Z (p k)) ∧
    top c - ∑ k, join (TensorProduct.mk ℂ _ _) (e k) (f k) ∈ (sysZ K x a).mix.B (d + 2) ∧
    ∀ q : ℕ, ∀ α ∈ (omCx (rB ℂ K (xv x)) a).Z q,
      α - ∑ k ∈ Finset.univ.filter (fun k => p k = q), pr K τ ρ (e k) α • f k ∈ (omCx (rB ℂ K (xv x)) a).B q

def PrB : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ (a q : ℕ), a ≤ d → q ≤ d → ∀ e ∈ (omCx (rB ℂ K (xv x)) (d - a)).Z (d - q),
  ∀ y ∈ (omCx (rB ℂ K (xv x)) a).B q, pr K τ ρ e y = 0

end UpperTheory.Gal.productCup_of_system

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.EuclideanHeightMul
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace UpperTheory.Gal.productCup_of_system

section SlopeTestRemainingChoices

variable {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
  (act : S →ₐ[ℂ] Module.End ℂ E) (R : Subalgebra ℂ S) (M : Submodule ℂ E)

@[reducible] private def modR (h : Stab act R M) : Module R M where
  smul r m := ⟨act r m, h r r.2 m m.2⟩
  one_smul m := Subtype.ext (by
    change act ((1 : R) : S) (m : E) = m
    simp)
  mul_smul a b m := Subtype.ext (by
    change act ((a * b : R) : S) (m : E) = act a (act b m)
    simp [Module.End.mul_apply])
  smul_zero a := Subtype.ext (by
    change act a ((0 : M) : E) = 0
    simp)
  smul_add a m m' := Subtype.ext (by
    change act a ((m + m' : M) : E) = act a m + act a m'
    simp)
  add_smul a b m := Subtype.ext (by
    change act ((a + b : R) : S) (m : E) = act a m + act b m
    simp)
  zero_smul m := Subtype.ext (by
    change act ((0 : R) : S) (m : E) = 0
    simp)

variable {act R M}

private theorem mem_ofList_iff [Module R M] [IsScalarTower ℂ R M] (hsm : ∀ (a : R) (m : M), ((a • m : M) : E) = act a m)
    {d : ℕ} (f : Fin d → R) (k : ℕ) (x : M) :
    x ∈ (Ideal.ofList ((List.ofFn f).take k) • ⊤ : Submodule R M) ↔
      (x : E) ∈ sm act M ((fun j => (f j : S)) '' {j | j.val < k}) := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha n _
      have : ∀ n : M, ((a • n : M) : E) ∈ sm act M ((fun j => (f j : S)) '' {j | j.val < k}) := by
        refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
        · intro b hb n
          obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.1 hb
          have hi' : i < k := lt_of_lt_of_le hi (min_le_left _ _)
          have hid : i < d := by
            have := lt_of_lt_of_le hi (min_le_right _ _)
            simpa using this
          rw [hsm]
          refine Submodule.mem_iSup_of_mem ((f ⟨i, hid⟩ : S)) (Submodule.mem_iSup_of_mem
            ⟨⟨i, hid⟩, hi', rfl⟩ ?_)
          simpa using ⟨n, n.2, rfl⟩
        · intro n
          simp
        · intro a b _ _ ha hb n
          rw [add_smul]
          simpa using Submodule.add_mem _ (ha n) (hb n)
        · intro a b _ hb n
          rw [smul_eq_mul, mul_comm, mul_smul]
          exact hb (a • n)
      exact this n
    · intro a b ha hb
      simpa using Submodule.add_mem _ ha hb
  · intro hx
    have hle : sm act M ((fun j => (f j : S)) '' {j | j.val < k}) ≤
        ((Ideal.ofList ((List.ofFn f).take k) • ⊤ : Submodule R M).restrictScalars ℂ).map M.subtype := by
      refine iSup₂_le ?_
      rintro _ ⟨j, hj, rfl⟩ _ ⟨m, hm, rfl⟩
      have hmem : f j • (⟨m, hm⟩ : M) ∈ (Ideal.ofList ((List.ofFn f).take k) • ⊤ : Submodule R M) := by
        refine Submodule.smul_mem_smul (Ideal.subset_span ?_) Submodule.mem_top
        refine List.mem_take_iff_getElem.2 ⟨j.val, ?_, by simp⟩
        simpa using hj
      exact Submodule.mem_map.2 ⟨_, (Submodule.restrictScalars_mem ℂ _ _).2 hmem, hsm _ _⟩
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 (hle hx)
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact (Submodule.restrictScalars_mem ℂ _ _).1 hy

private theorem wd_coe [Module R M] [IsScalarTower ℂ R M]
    (hsm : ∀ (a : R) (m : M), ((a • m : M) : E) = act a m) {κ : Type} [LinearOrder κ] (r : κ → R)
    (c : Finset κ → M) (t : Finset κ) :
    ((wd (fun l => Algebra.lsmul ℂ ℂ M (r l)) c t : M) : E) =
      wd (fun l => act (r l)) (fun s => (c s : E)) t := by
  simp [wd, hsm]

private theorem koszulExact_of_regular (hK : KoszulExactBelowLengthOfWeaklyRegular) {κ : Type} [LinearOrder κ] [Fintype κ] (r : κ → S) {d : ℕ}
    (f : Fin d → S) (hS : Stab act R M) (hr : ∀ l, r l ∈ R) (hReg : Reg act M f)
    (hf : ∀ j, InSp R r (f j)) : KE (kos act M r) d := by
  letI := modR act R M hS
  have hsm : ∀ (a : R) (m : M), ((a • m : M) : E) = act a m := fun _ _ => rfl
  haveI : IsScalarTower ℂ R M := ⟨fun c a m => Subtype.ext (by
    change act ((c • a : R) : S) (m : E) = c • act a m
    simp)⟩
  have hfR : ∀ j, f j ∈ R := by
    intro j
    obtain ⟨a, ha, h⟩ := hf j
    rw [h]
    exact sum_mem fun l _ => R.mul_mem (ha l) (hr l)
  let r' : κ → R := fun l => ⟨r l, hr l⟩
  let f' : Fin d → R := fun j => ⟨f j, hfR j⟩
  have hreg : RingTheory.Sequence.IsWeaklyRegular M (List.ofFn f') := by
    refine ⟨fun i hi => ?_⟩
    have hid : i < d := by simpa using hi
    rw [isSMulRegular_on_quot_iff_lsmul_comap_le]
    intro x hx
    rw [Submodule.mem_comap, LinearMap.lsmul_apply, mem_ofList_iff hsm] at hx
    rw [mem_ofList_iff hsm]
    have hget : (List.ofFn f')[i] = f' ⟨i, hid⟩ := by simp
    rw [hget, hsm] at hx
    exact hReg ⟨i, hid⟩ x x.2 hx
  have hsp : ∀ g ∈ List.ofFn f', InSp (⊤ : Subalgebra ℂ R) r' g := by
    intro g hg
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    obtain ⟨a, ha, h⟩ := hf j
    refine ⟨fun l => ⟨a l, ha l⟩, fun _ => trivial, Subtype.ext ?_⟩
    simpa [f', r'] using h
  have key := hK d R M κ r' (List.ofFn f') (by simp) hreg hsp
  intro m hm c hc
  obtain ⟨hcC, hcD⟩ := hc
  have hcM : ∀ s, c s ∈ M := by
    intro s
    have : c s ∈ if (s.card : ℤ) = m then M else ⊥ := hcC s (Set.mem_univ s)
    split_ifs at this with h
    · exact this
    · rw [Submodule.mem_bot] at this
      exact this ▸ M.zero_mem
  let c' : Finset κ → M := fun s => ⟨c s, hcM s⟩
  have hc' : c' ∈ (kos (Algebra.lsmul ℂ ℂ M) (⊤ : Submodule ℂ M) r').Z m := by
    constructor
    · intro s _
      have : c s ∈ if (s.card : ℤ) = m then M else ⊥ := hcC s (Set.mem_univ s)
      change c' s ∈ if (s.card : ℤ) = m then (⊤ : Submodule ℂ M) else ⊥
      split_ifs at this ⊢ with h
      · trivial
      · rw [Submodule.mem_bot] at this ⊢
        exact Subtype.ext this
    · refine LinearMap.mem_ker.2 (funext fun t => Subtype.ext ?_)
      have := wd_coe hsm r' c' t
      exact this.trans (congrFun (LinearMap.mem_ker.1 hcD) t)
  obtain ⟨y, hy, hyc⟩ := key m hm hc'
  refine ⟨fun s => (y s : E), ?_, ?_⟩
  · intro s _
    have : y s ∈ if (s.card : ℤ) = m - 1 then (⊤ : Submodule ℂ M) else ⊥ := hy s (Set.mem_univ s)
    change (y s : E) ∈ if (s.card : ℤ) = m - 1 then M else ⊥
    split_ifs at this ⊢ with h
    · exact (y s).2
    · rw [Submodule.mem_bot] at this ⊢
      rw [this]
      rfl
  · funext t
    have h1 := wd_coe hsm r' y t
    have h2 : ((wd (fun l => Algebra.lsmul ℂ ℂ M (r' l)) y t : M) : E) = c t :=
      congrArg (fun z : Finset κ → M => ((z t : M) : E)) hyc
    exact h1.symm.trans h2

end SlopeTestRemainingChoices

end UpperTheory.Gal.productCup_of_system

end

theorem UpperTheory.Gal.productCup_of_system.firstCohomologyBound_of_boundaryBound :
    KoszulExactBelowLengthOfWeaklyRegular → K1 := by
  intro hK S E _ _ _ _ act κ _ _ R M r d f hS hr hReg hf
  exact koszulExact_of_regular hK r f hS hr hReg hf
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.KSubOf
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.kSub_of :
    FiltrationBoundaryCriterion → SubQEx → KSub := by
  intro gl sub S E _ _ _ _ act κ _ _ R M r hst hr
  refine ⟨?_, ?_⟩
  · intro d e hK m hm c hc
    have hW : WOk (fun _ : Finset κ => M) (fun l => act (r l)) := by
      refine ⟨fun i j => ?_, fun s i _ x hx => hst _ (hr i) x hx⟩
      show act (r i) * act (r j) = act (r j) * act (r i)
      rw [← map_mul, ← map_mul, mul_comm]
    have hQ := sub S E act κ M r d e hK
    have hcard : (img e).card = d := by simp [img]
    refine gl κ E (fun _ => M) (fun l => act (r l)) (img e) d m hW hQ c hc ?_
      ⟨0, Submodule.zero_mem _, fun _ _ => rfl, ?_⟩
    · intro s hs
      exfalso
      apply hs
      have h1 : (s ∩ img e).card ≤ (img e).card := Finset.card_le_card Finset.inter_subset_right
      rw [hcard] at h1
      exact_mod_cast h1
    · intro s hs
      have h1 : (s ∩ img e).card ≤ s.card := Finset.card_le_card Finset.inter_subset_left
      have hne : (s.card : ℤ) ≠ m := by
        have : ((s ∩ img e).card : ℤ) ≤ s.card := by exact_mod_cast h1
        omega
      have h2 : c s ∈ (if (s.card : ℤ) = m then M else ⊥ : Submodule ℂ E) := hc.1 s (Set.mem_univ s)
      rw [if_neg hne, Submodule.mem_bot] at h2
      rw [h2, map_zero]
      rfl
  · intro n c hc L
    obtain ⟨y, hy, rfl⟩ := hc
    have hval : ∀ i ∈ L, y (L.erase i) ∈ M := by
      intro i _
      have h2 : y (L.erase i) ∈ (if ((L.erase i).card : ℤ) = n - 1 then M else ⊥ : Submodule ℂ E) :=
        hy (L.erase i) (Set.mem_univ _)
      split_ifs at h2 with h
      · exact h2
      · rw [Submodule.mem_bot] at h2
        rw [h2]
        exact M.zero_mem
    have hexp : (kos act M r).D y L
        = ∑ i ∈ L, (GlobalTheory.cubeSign L i : ℤ) • act (r i) (y (L.erase i)) := by
      simp [kos, acx, wd]
    rw [hexp]
    refine Submodule.sum_mem _ fun i hi => ?_
    refine Submodule.smul_of_tower_mem _ _ ?_
    have h3 : act (r i) (y (L.erase i)) ∈ M.map (act (r i)) := ⟨_, hval i hi, rfl⟩
    exact (le_iSup₂_of_le (r i) (Set.mem_range_self i) le_rfl : M.map (act (r i)) ≤ sm act M (Set.range r)) h3
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.KoszulExactWeaklyRegular
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct Pointwise

section
variable {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]

end

section
variable {R κ : Type} [CommRing R] [Algebra ℂ R] [LinearOrder κ]
  {N N' : Type} [AddCommGroup N] [Module R N] [Module ℂ N] [IsScalarTower ℂ R N]
  [AddCommGroup N'] [Module R N'] [Module ℂ N'] [IsScalarTower ℂ R N']

end

section
variable {R κ : Type} [CommRing R] [Algebra ℂ R] [LinearOrder κ] [Fintype κ]

end

theorem UpperTheory.Gal.productCup_of_system.koszulExactBelowLengthOfWeaklyRegular_of_htpy :
    Htpy → KoszulExactBelowLengthOfWeaklyRegular :=
  _root_.UpperTheory.Reformulated.B.KoszulComplexHomotopy.koszulExactBelowLengthOfWeaklyRegular_of_htpy
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PTrLin
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.trLin_of :
    TrLin := by
  intro V _ _ ι _ φ v hv
  have hfin : FiniteDimensional ℂ V := by
    refine Module.Finite.of_surjective (Fintype.linearCombination ℂ v) ?_
    intro y
    exact ⟨fun k => φ k y, by rw [Fintype.linearCombination_apply]; exact (hv y).symm⟩
  refine ⟨hfin, fun u => ?_⟩
  have hu : u = ∑ k, dualTensorHom ℂ V V (φ k ⊗ₜ u (v k)) := by
    ext y
    rw [LinearMap.sum_apply]
    simp only [dualTensorHom_apply]
    conv_lhs => rw [hv y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp [map_smul]
  conv_lhs => rw [hu]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.trace_eq_contract_apply]
  simp
end

