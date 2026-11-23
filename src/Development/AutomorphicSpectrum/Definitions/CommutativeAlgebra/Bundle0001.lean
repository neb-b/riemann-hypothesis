module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
section
namespace GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E] [Module Ω E]

def LocFree (R : Subalgebra o Ω) (r : ℕ) (L : AddSubgroup E) : Prop :=
  (∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) ∧
  ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ R) ∧ (∀ l, c l ∈ R) ∧ ∑ l, c l * f l = 1 ∧
    ∀ l, ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, f l ^ n • e ∈ L) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q

def spanOver (R : Subalgebra o Ω) (S : Set E) : AddSubgroup E :=
  AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ S, v = a • e}

def GenDual (R : Subalgebra o Ω) (L : AddSubgroup E) {M : ℕ} (φ : Fin M → Module.Dual Ω E) : Prop :=
  (∀ l, ∀ v ∈ L, φ l v ∈ R) ∧
  ∀ ψ : Module.Dual Ω E, (∀ v ∈ L, ψ v ∈ R) → ∃ u : Fin M → Ω, (∀ l, u l ∈ R) ∧ ψ = ∑ l, u l • φ l

noncomputable def flagMinor {N M : ℕ} (φ : Fin M → Module.Dual Ω E) (w : Fin N → E) (i : ℕ) (hi : i ≤ N)
    (I : Fin i → Fin M) : Ω :=
  Matrix.det (Matrix.of fun a b : Fin i => φ (I a) (w (Fin.castLE hi b)))

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
section
namespace GlobalTheory.CompanionTheory.Ar.Crv

def lmuNum {T : Type} [Fintype T] (j q : ℕ) (μ w l : T → ℕ → ℝ) : ℝ :=
  -∑ τ, ((∑ i ∈ Finset.range j, μ τ (i + 1) * (w τ (i + 1) - w τ i)) +
    ∑ m ∈ Finset.range q, μ τ (j + m + 1) * (l τ (q - m - 1) - l τ (q - m)))

def GapCond {T : Type} [Fintype T] (p j q : ℕ) (μ : T → ℕ → ℝ) : Prop :=
  (∀ τ i, 1 ≤ i → i < j + q → μ τ (i + 1) ≤ μ τ i) ∧
    ∃ M g : ℝ, (∀ τ i, 1 ≤ i → i ≤ j + q → |μ τ i| ≤ M) ∧ (∀ τ, g ≤ μ τ j - μ τ (j + 1)) ∧
      4 * (Fintype.card T : ℝ) * M ≤ ((p : ℝ) - 2) * g

end GlobalTheory.CompanionTheory.Ar.Crv
end

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
section
noncomputable section

open scoped WithZero

namespace GlobalTheory.CompanionTheory.Ar.Crv

structure ACurve (K : Type) [Field K] where

  I : Type

  v : I → Valuation K (WithZero (Multiplicative ℤ))

  w : I → ℕ

  fin : ∀ x : K, x ≠ 0 → {i | v i x ≠ 1}.Finite

  prod : ∀ x : K, x ≠ 0 → ∑ᶠ i, (w i : ℤ) * WithZero.log (v i x) = 0

variable {K : Type} [Field K] (C : ACurve K)

section One

variable {V : Type} [AddCommGroup V] [Module K V]

def IsLatOf (i : C.I) {n : ℕ} (b : Module.Basis (Fin n) K V) (L : AddSubgroup V) : Prop :=
  ∀ x, x ∈ L ↔ ∀ q, C.v i (b.repr x q) ≤ 1

def IsBun (L : C.I → AddSubgroup V) : Prop :=
  (∀ i, ∃ b : Module.Basis (Fin (Module.finrank K V)) K V, IsLatOf C i b (L i)) ∧
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V, {i | ¬ IsLatOf C i b (L i)}.Finite


open Classical in
def locBasis [FiniteDimensional K V] (i : C.I) (L : AddSubgroup V) :
    Module.Basis (Fin (Module.finrank K V)) K V :=
  if h : ∃ b : Module.Basis (Fin (Module.finrank K V)) K V, IsLatOf C i b L then h.choose
  else Module.finBasis K V

def deg [FiniteDimensional K V] (L : C.I → AddSubgroup V) : ℤ :=
  ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (locBasis C i (L i))))

def sub (L : C.I → AddSubgroup V) (W : Submodule K V) : C.I → AddSubgroup W :=
  fun i => (L i).comap W.subtype.toAddMonoidHom

def quot (L : C.I → AddSubgroup V) (W : Submodule K V) : C.I → AddSubgroup (V ⧸ W) :=
  fun i => (L i).map W.mkQ.toAddMonoidHom

def subDeg [FiniteDimensional K V] (L : C.I → AddSubgroup V) (W : Submodule K V) : ℤ :=
  deg C (sub C L W)

end One

section Two

variable {V V' V'' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
  [AddCommGroup V''] [Module K V'']

def IsHom (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (f : V →ₗ[K] V') : Prop :=
  ∀ i, ∀ x ∈ L i, f x ∈ L' i

def ShortExact (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'')
    (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') : Prop :=
  Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g ∧
    (∀ i x, x ∈ L i ↔ f x ∈ L' i) ∧ ∀ i z, z ∈ L'' i ↔ ∃ y ∈ L' i, g y = z

def dualLat (L : C.I → AddSubgroup V) (B : V →ₗ[K] V' →ₗ[K] K) : C.I → AddSubgroup V' :=
  fun i =>
    { carrier := {y | ∀ x ∈ L i, C.v i (B x y) ≤ 1}
      zero_mem' := fun x _ => by simp
      add_mem' := fun {a b} ha hb x hx => by
        rw [map_add (f := _)]; exact (C.v i).map_add_le (ha x hx) (hb x hx)
      neg_mem' := fun {a} ha x hx => by
        rw [map_neg, Valuation.map_neg]; exact ha x hx }

def spanLat (L : C.I → AddSubgroup V) (φ : V → V') : C.I → AddSubgroup V' :=
  fun i => AddSubgroup.closure {y | ∃ (a : K) (x : V), C.v i a ≤ 1 ∧ x ∈ L i ∧ y = a • φ x}

end Two

def frobVec (p : ℕ) {d : ℕ} (x : Fin d → K) : Fin d → K := fun j => x j ^ p

def frobLat (p : ℕ) {d : ℕ} (L : C.I → AddSubgroup (Fin d → K)) : C.I → AddSubgroup (Fin d → K) :=
  spanLat C L (frobVec p)

def frobSub (p : ℕ) {d : ℕ} (W : Submodule K (Fin d → K)) : Submodule K (Fin d → K) :=
  Submodule.span K (frobVec p '' (W : Set (Fin d → K)))

def dotDual {d : ℕ} (L : C.I → AddSubgroup (Fin d → K)) : C.I → AddSubgroup (Fin d → K) :=
  dualLat C L (dotProductBilin K K)

def eig {O V : Type} [AddCommGroup V] [Module K V] (ρ : O → V →ₗ[K] V) (χ : O → K) : Submodule K V :=
  ⨅ a, LinearMap.ker (ρ a - χ a • LinearMap.id)

def IsSplit {O k S : Type} [CommRing O] [Field k] (χ : S → (O →+* k)) : Prop :=
  Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId k (S → k))
    (Pi.algHom ℤ (fun _ : S => k) fun s => (χ s).toIntAlgHom) (fun _ _ => Commute.all _ _) :
      TensorProduct ℤ k O →ₐ[k] (S → k))

structure ConjData (p : ℕ) (O : Type) [CommRing O] [StarRing O] (d : ℕ) where

  lie : C.I → AddSubgroup (Fin d → K)

  H : C.I → AddSubgroup ((Fin d → K) × (Fin d → K))

  lie_bun : IsBun C lie

  H_bun : IsBun C H

  ρ : O →+* Matrix (Fin d) (Fin d) K

  ρH : O →+* Module.End K ((Fin d → K) × (Fin d → K))

  ρH_hom : ∀ a, IsHom C H H (ρH a)

  ρH_fst : ∀ a y, (ρH a y).1 = (ρ a).mulVec y.1

  ρH_inr : ∀ a φ, ρH a (0, φ) = (0, (ρ (star a)).transpose.mulVec φ)

  hodge : ShortExact C (dotDual C lie) H lie (LinearMap.inr K _ _) (LinearMap.fst K _ _)

  α : (Fin d → K) →ₗ[K] (Fin d → K) × (Fin d → K)

  β : ((Fin d → K) × (Fin d → K)) →ₗ[K] (Fin d → K)

  conj : ShortExact C (frobLat C p lie) H (frobLat C p (dotDual C lie)) α β

  α_act : ∀ a u, α (((ρ a).map (· ^ p)).mulVec u) = ρH a (α u)

  β_act : ∀ a y, β (ρH a y) = ((ρ (star a)).transpose.map (· ^ p)).mulVec (β y)

namespace Inhab

section Line

open Polynomial IsDedekindDomain

variable (k : Type) [Field k]

end Line

section Const

def trivLat (d : ℕ) : C.I → AddSubgroup (Fin d → K) := fun i =>
  { carrier := {x | ∀ j, C.v i (x j) ≤ 1}
    zero_mem' := fun j => by simp
    add_mem' := fun ha hb j => (C.v i).map_add_le (ha j) (hb j)
    neg_mem' := fun ha j => by simpa using ha j }

theorem mem_trivLat {d : ℕ} {i : C.I} {x : Fin d → K} :
    x ∈ trivLat C d i ↔ ∀ j, C.v i (x j) ≤ 1 := Iff.rfl

theorem isBun_of_basis {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι]
    (b : Module.Basis ι K V) (L : C.I → AddSubgroup V)
    (h : ∀ i x, x ∈ L i ↔ ∀ q, C.v i (b.repr x q) ≤ 1) : IsBun C L := by
  let e : ι ≃ Fin (Module.finrank K V) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  have : ∀ i, IsLatOf C i (b.reindex e) (L i) := fun i x => by
    rw [h]; simp only [Module.Basis.repr_reindex_apply]
    exact ⟨fun H q => H _, fun H q => by simpa using H (e q)⟩
  exact ⟨fun i => ⟨_, this i⟩, b.reindex e, by simp [this]⟩

theorem mulVec_mem_trivLat {d : ℕ} {i : C.I} {M : Matrix (Fin d) (Fin d) K}
    (hM : ∀ r s, C.v i (M r s) ≤ 1) {x : Fin d → K} (hx : x ∈ trivLat C d i) :
    M.mulVec x ∈ trivLat C d i := fun r =>
  (C.v i).map_sum_le (s := Finset.univ) (f := fun s => M r s * x s) fun s _ =>
    ((C.v i).map_mul _ _).trans_le (mul_le_one' (hM r s) (hx s))

variable {V : Type} [AddCommGroup V] [Module K V]

def latOf (i : C.I) {n : ℕ} (b : Module.Basis (Fin n) K V) : AddSubgroup V where
  carrier := {x | ∀ q, C.v i (b.repr x q) ≤ 1}
  zero_mem' := fun q => by simp
  add_mem' := fun ha hb q => by
    rw [map_add (f := _), Finsupp.add_apply]; exact (C.v i).map_add_le (ha q) (hb q)
  neg_mem' := fun ha q => by simpa using ha q

theorem isLatOf_latOf (i : C.I) {n : ℕ} (b : Module.Basis (Fin n) K V) :
    IsLatOf C i b (latOf C i b) := fun _ => Iff.rfl

theorem v_det {i : C.I} {n : ℕ}
    {b b' : Module.Basis (Fin n) K V} {L : AddSubgroup V} (h : IsLatOf C i b L)
    (h' : IsLatOf C i b' L) : C.v i (b.det b') = 1 := by
  have key : ∀ {b b' : Module.Basis (Fin n) K V}, IsLatOf C i b L → IsLatOf C i b' L →
      C.v i (b.det b') ≤ 1 := by
    intro b b' h h'
    rw [Module.Basis.det_apply, Matrix.det_apply']
    refine (C.v i).map_sum_le fun σ _ => ?_
    rw [map_mul, map_prod]
    refine mul_le_one' ?_ (Finset.prod_le_one' fun q _ => (h _).1 ((h' _).2 fun r => ?_) _)
    · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]
    · by_cases e : q = r <;> simp [e, Finsupp.single_apply]
  have h1 : C.v i (b.det b') * C.v i (b'.det b) = 1 := by
    rw [← map_mul, Module.Basis.det_mul_det, Module.Basis.det_self, map_one]
  exact le_antisymm (key h h') (h1 ▸ mul_le_of_le_one_right' (key h' h))

theorem deg_eq [FiniteDimensional K V]
    {L : C.I → AddSubgroup V} (b : C.I → Module.Basis (Fin (Module.finrank K V)) K V)
    (h : ∀ i, IsLatOf C i (b i) (L i)) :
    deg C L = ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i))) := by
  refine finsum_congr fun i => ?_
  have hex : ∃ b : Module.Basis (Fin (Module.finrank K V)) K V, IsLatOf C i b (L i) := ⟨_, h i⟩
  have : IsLatOf C i (locBasis C i (L i)) (L i) := by
    rw [locBasis, dite_eq_left hex]; exact hex.choose_spec
  rw [← Module.Basis.det_mul_det _ (b i), map_mul, v_det C (h i) this, mul_one]

end Const

section Gauss

end Gauss

section Twist

variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module (RatFunc k) V]
  [FiniteDimensional (RatFunc k) V]

end Twist

end Inhab

end GlobalTheory.CompanionTheory.Ar.Crv
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ProIsoAt
section
namespace GlobalTheory.CompanionTheory.Ar

structure ProIso (O : Type) [CommRing O] {L L' : Type} [AddCommGroup L] [Module O L] [AddCommGroup L']
    [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') where

  a : ℕ → (L →ₗ[O] L')
  inj : ∀ n, 0 < n → ∀ x, (∃ y, a n x = n • y) ↔ ∃ y, x = n • y
  surj : ∀ n, 0 < n → ∀ y, ∃ x e, y = a n x + n • e
  isom : ∀ n : ℕ, 0 < n → ∀ x y, (n : ℤ) ∣ B' (a n x) (a n y) - B x y
  compat : ∀ n m, 0 < n → 0 < m → ∀ x, ∃ e, a (n * m) x = a n x + n • e

structure ProIsoAt (p : ℕ) (O : Type) [CommRing O] {L L' : Type} [AddCommGroup L] [Module O L]
    [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') where

  a : ℕ → (L →ₗ[O] L')
  inj : ∀ k x, (∃ y, a k x = p ^ k • y) ↔ ∃ y, x = p ^ k • y
  surj : ∀ k y, ∃ x e, y = a k x + p ^ k • e
  isom : ∀ k x y, ((p : ℤ) ^ k) ∣ B' (a k x) (a k y) - B x y
  compat : ∀ k x, ∃ e, a (k + 1) x = a k x + p ^ k • e

variable {O : Type} [CommRing O] {L L' L'' : Type} [AddCommGroup L] [Module O L] [AddCommGroup L']
  [Module O L'] [AddCommGroup L''] [Module O L''] {B : LinearMap.BilinForm ℤ L}
  {B' : LinearMap.BilinForm ℤ L'} {B'' : LinearMap.BilinForm ℤ L''}

def ProIso.IsInv (f : ProIso O B B') (g : ProIso O B' B) : Prop :=
  (∀ n, 0 < n → ∀ x, ∃ e, g.a n (f.a n x) = x + n • e) ∧ ∀ n, 0 < n → ∀ y, ∃ e, f.a n (g.a n y) = y + n • e

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
section
namespace GlobalTheory.CompanionTheory.Ar.BT

variable {R : Type} [CommRing R] {T H : Type} [CommGroup T] [CommGroup H]

def prodSpan (A : Subalgebra R (T → R)) : Submodule R (T × T → R) :=
  Submodule.span R {g | ∃ a ∈ A, ∃ b ∈ A, g = fun z => a z.1 * b z.2}

structure IsHopfOrder (A : Subalgebra R (T → R)) : Prop where

  finite : Module.Finite R A

  projective : Module.Projective R A

  full : ∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A

  comul : ∀ f ∈ A, (fun z : T × T => f (z.1 * z.2)) ∈ prodSpan A

  inv : ∀ f ∈ A, (fun x => f x⁻¹) ∈ A

def indOrder (ι : H →* T) (A : Subalgebra R (H → R)) : Subalgebra R (T → R) where
  carrier := {f | ∀ t, (fun h => f (t * ι h)) ∈ A}
  mul_mem' hf hg t := A.mul_mem (hf t) (hg t)
  add_mem' hf hg t := A.add_mem (hf t) (hg t)
  algebraMap_mem' r _ := A.algebraMap_mem r

def extOrder {R' : Type} [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) : Subalgebra R' (T → R') :=
  Algebra.adjoin R' {g | ∃ f ∈ A, g = fun t => φ (f t)}

def evalAt (A : Subalgebra R (T → R)) (t : T) : A →ₐ[R] R :=
  (Pi.evalAlgHom R (fun _ : T => R) t).comp A.val

def augIdeal (A : Subalgebra R (T → R)) : Ideal A := RingHom.ker (evalAt A 1)

abbrev omega (A : Subalgebra R (T → R)) : Type := (augIdeal A).Cotangent


open scoped Classical in
open Classical in
noncomputable def dlogChar (A : Subalgebra R (T → R)) (χ : T →* Rˣ) : omega A :=
  if h : (fun t => ((χ t : Rˣ) : R)) ∈ A then
    (augIdeal A).toCotangent ⟨⟨_, h⟩ - 1, by simp [augIdeal, evalAt, RingHom.mem_ker]⟩
  else 0

namespace OrderApi


omit [CommGroup T] in
theorem mul_mem_prodSpan {A : Subalgebra R (T → R)} {a b : T → R} (ha : a ∈ A) (hb : b ∈ A) :
    (fun z : T × T => a z.1 * b z.2) ∈ prodSpan A :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩

theorem mem_indOrder (ι : H →* T) (A : Subalgebra R (H → R)) (f : T → R) :
    f ∈ indOrder ι A ↔ ∀ t, (fun h => f (t * ι h)) ∈ A := Iff.rfl


omit [CommGroup T] in
theorem comp_mem_extOrder {R' : Type} [CommRing R'] (φ : R →+* R') {A : Subalgebra R (T → R)} {f : T → R}
    (hf : f ∈ A) : (fun t => φ (f t)) ∈ extOrder φ A :=
  Algebra.subset_adjoin ⟨f, hf, rfl⟩

theorem mem_augIdeal (A : Subalgebra R (T → R)) (f : A) : f ∈ augIdeal A ↔ (f : T → R) 1 = 0 := Iff.rfl

theorem dlogChar_of_mem (A : Subalgebra R (T → R)) (χ : T →* Rˣ) (h : (fun t => ((χ t : Rˣ) : R)) ∈ A) :
    dlogChar A χ =
      (augIdeal A).toCotangent ⟨⟨_, h⟩ - 1, by simp [augIdeal, evalAt, RingHom.mem_ker]⟩ := by
  rw [dlogChar, dite_eq_left h]

end OrderApi

namespace OrderEx

end OrderEx

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.ValNeBot
section
namespace GlobalTheory.CompanionTheory.Ar.Ref

open NumberField IsDedekindDomain

noncomputable section

variable {K : Type} [Field K] [NumberField K]

def vl (la : HeightOneSpectrum (𝓞 K)) (x : K) : ℤ := -WithZero.log (la.valuation K x)

structure PtSys (K : Type) [Field K] [NumberField K] (R : Type) [CommRing R] [Algebra K R] where

  Pt : HeightOneSpectrum (𝓞 K) → Type

  val : ∀ {la}, Pt la → R → EReal
  val_zero : ∀ {la} (y : Pt la), val y 0 = ⊤
  val_ne_bot : ∀ {la} (y : Pt la) f, val y f ≠ ⊥
  val_add : ∀ {la} (y : Pt la) f g, min (val y f) (val y g) ≤ val y (f + g)
  val_smul : ∀ {la} (y : Pt la) (a : K) f, a ≠ 0 → val y (a • f) = (((vl la a : ℤ) : ℝ) : EReal) + val y f
  val_mul : ∀ {la} (y : Pt la) f g, val y (f * g) = val y f + val y g

namespace PtSys

variable {R : Type} [CommRing R] [Algebra K R] (S : PtSys K R)

end PtSys

end

end GlobalTheory.CompanionTheory.Ar.Ref
end

