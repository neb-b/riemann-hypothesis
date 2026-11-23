module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Formalism.UnipotentAdelicQuotients.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DI

section Cochain

variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]

def delta (c : Finset ι → E) : Finset ι → E :=
  fun t => ∑ i ∈ t, cubeSign t i • c (t.erase i)

def Dtot (d : E →+ E) (c : Finset ι → E) : Finset ι → E :=
  fun t => delta c t + (-1 : ℤ) ^ t.card • d (c t)


omit [LinearOrder ι] in
def InCech (N : Finset ι → AddSubgroup E) (m : ℕ) (c : Finset ι → E) : Prop :=
  c ∅ = 0 ∧ (∀ s, c s ∈ N s) ∧ ∀ s, s.card ≠ m → c s = 0

def CechZero (N : Finset ι → AddSubgroup E) (b : ℕ) : Prop :=
  ∀ c, InCech N (b + 1) c → delta c = 0 → ∃ y, InCech N b y ∧ delta y = c


omit [LinearOrder ι] in
def InTot (T : ℕ → Finset ι → AddSubgroup E) (m : ℕ) (c : Finset ι → E) : Prop :=
  c ∅ = 0 ∧ (∀ q s, q + s.card = m → c s ∈ T q s) ∧ ∀ s, m < s.card → c s = 0

def HypZero (d : E →+ E) (T : ℕ → Finset ι → AddSubgroup E) (n : ℕ) : Prop :=
  ∀ c, InTot T (n + 1) c → Dtot d c = 0 → ∃ y, InTot T n y ∧ Dtot d y = c

structure CartierAt (d : E →+ E) (γ : E → E) (N T : ℕ → AddSubgroup E) : Prop where
  inj_zero : ∀ x ∈ N 0, γ x = 0 → x = 0
  inj_succ : ∀ a, ∀ x ∈ N (a + 1), ∀ z ∈ T a, γ x = d z → x = 0
  surj_zero : ∀ y ∈ T 0, d y = 0 → ∃ x ∈ N 0, y = γ x
  surj_succ : ∀ a, ∀ y ∈ T (a + 1), d y = 0 → ∃ x ∈ N (a + 1), ∃ z ∈ T a, y = γ x + d z

def cup (Φ : E → Finset ι → E) (c : Finset ι → E) : Finset ι → E :=
  fun u => ∑ j ∈ u, Φ (c (u.filter (· ≤ j))) (u.filter (j ≤ ·))

end Cochain

section Forms

variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]

structure IsOddDer (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) : Prop where
  mul : ∀ x y, d (x * y) = d x * y + CliffordAlgebra.involute x * d y
  sq : ∀ x, d (d x) = 0

structure IsExtD (k K : Type) [CommRing k] [CommRing K] [Algebra k K]
    (d : ExteriorAlgebra K Ω[K⁄k] →+ ExteriorAlgebra K Ω[K⁄k]) : Prop extends IsOddDer d where
  alg : ∀ a : K, d (algebraMap K _ a) = ExteriorAlgebra.ι K (KaehlerDifferential.D k K a)

def forms (B : Set K) (L : Set V) (q : ℕ) : AddSubgroup (ExteriorAlgebra K V) :=
  AddSubgroup.closure {x | ∃ b ∈ B, ∃ v : Fin q → V, (∀ k, v k ∈ L) ∧ x = b • ExteriorAlgebra.ιMulti K q v}

variable {ι : Type} [LinearOrder ι]


omit [LinearOrder ι] in
structure IsDatum (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V)
    (h : ι → ι → V →+ K) : Prop where
  f_smul : ∀ i (c : K) v, f i (c • v) = c ^ p • f i v
  h_smul : ∀ i j (c : K) v, h i j (c • v) = c ^ p * h i j v
  closed : ∀ i v, d (ExteriorAlgebra.ι K (f i v)) = 0
  dh : ∀ i j v, d (algebraMap K _ (h i j v)) = ExteriorAlgebra.ι K (f j v) - ExteriorAlgebra.ι K (f i v)
  cocycle : ∀ i j l v, h i j v + h j l v = h i l v

def Lop (f : ι → V →+ V) (h : ι → ι → V →+ K) (v : V) (y : Finset ι → ExteriorAlgebra K V) :
    Finset ι → ExteriorAlgebra K V := fun t =>
  if ht : t.Nonempty then
    (-1 : ℤ) ^ t.card • (ExteriorAlgebra.ι K (f (t.min' ht) v) * y t) +
      (if h2 : (t.erase (t.min' ht)).Nonempty then
        h (t.min' ht) ((t.erase (t.min' ht)).min' h2) v • y (t.erase (t.min' ht)) else 0)
  else 0


omit [LinearOrder ι] in
def oneC : Finset ι → ExteriorAlgebra K V := fun t => if t.card = 1 then 1 else 0

def prodL (f : ι → V →+ V) (h : ι → ι → V →+ K) (vs : List V) : Finset ι → ExteriorAlgebra K V :=
  vs.foldr (Lop f h) oneC

def alt (f : ι → V →+ V) (h : ι → ι → V →+ K) (a : ℕ) (v : Fin a → V) : Finset ι → ExteriorAlgebra K V :=
  ∑ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • prodL f h (List.ofFn (v ∘ σ))

def IsPhi (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K)
    (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) : Prop :=
  ∀ (c : K) (a : ℕ) (v : Fin a → V), Φ (c • ExteriorAlgebra.ιMulti K a v) = c ^ p • alt f h a v

def IsGamma (p : ℕ) (f : V →+ V) (γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V) : Prop :=
  (∀ c : K, γ (algebraMap K _ c) = algebraMap K _ (c ^ p)) ∧
    ∀ v, γ (ExteriorAlgebra.ι K v) = ExteriorAlgebra.ι K (f v)

end Forms

section Lift

variable {K Kt : Type} [CommRing K] [CommRing Kt]

structure IsFlatLift (p : ℕ) (π : Kt →+* K) : Prop where
  surj : Function.Surjective π
  ker : ∀ z, π z = 0 ↔ ∃ w, z = p * w
  ann : ∀ w, (p : Kt) * w = 0 ↔ π w = 0

def IsFrob (p : ℕ) (π : Kt →+* K) (F : Kt →+* Kt) : Prop := ∀ z, π (F z) = π z ^ p

def IsF (p : ℕ) (π : Kt →+* K) (F : Kt →+* Kt) (f : Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) : Prop :=
  (∀ (c : K) v, f (c • v) = c ^ p • f v) ∧ ∀ z w : Kt, F z = z ^ p + p * w →
    f (KaehlerDifferential.D ℤ K (π z)) =
      π z ^ (p - 1) • KaehlerDifferential.D ℤ K (π z) + KaehlerDifferential.D ℤ K (π w)

def IsH (p : ℕ) (π : Kt →+* K) (F F' : Kt →+* Kt) (h : Ω[K⁄ℤ] →+ K) : Prop :=
  (∀ (c : K) v, h (c • v) = c ^ p * h v) ∧ ∀ z w : Kt, F' z = F z + p * w →
    h (KaehlerDifferential.D ℤ K (π z)) = π w

def LogLift {ι : Type} (p : ℕ) (π : Kt →+* K) (F : ι → Kt →+* Kt) (s : Finset ι) (A : Set K) (g : K) : Prop :=
  ∃ z, π z = g ∧ ∀ i ∈ s, ∃ w, π w ∈ A ∧ F i z = z ^ p * (1 + p * w)

end Lift

end GlobalTheory.DI
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
section
noncomputable section

namespace GlobalTheory.UCls

open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def IsUA (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  IsUnit g.det ∧ ∀ x y, hermA c G (g *ᵥ x) (g *ᵥ y) = hermA c G x y

def IsKM (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    (k : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  IsUA c G k ∧ (∀ x ∈ hat F L, ∃ y ∈ hat F L, k *ᵥ x - x = M • y) ∧ ∀ x ∈ hat F L, ∃ y ∈ hat F L, k *ᵥ y = x

def ratM (F : Type) [Field F] [NumberField F] [Algebra F E] (γ : Matrix (Fin n) (Fin n) E) :
    Matrix (Fin n) (Fin n) (RA F E) :=
  γ.map fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ x

def UEquiv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    (g g' : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∃ γ : Matrix (Fin n) (Fin n) E, IsUA c G (ratM F γ) ∧ ∃ k, IsKM c G L M k ∧ g' = ratM F γ * g * k

def IsTA (c : E ≃ₐ[F] E) (t : RA F E) : Prop := t * sg (FiniteAdeleRing (𝓞 F) F) c t = 1

def TEquiv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) (t t' : RA F E) : Prop :=
  ∃ u : E, u * c u = 1 ∧ ∃ k, IsKM c G L M k ∧ t' = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ u) * t * k.det

def torusNo (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) : ℕ∞ :=
  ENat.card (Quot fun a b : {t // IsTA c t} => TEquiv c G L M a.1 b.1)


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.UCls.isKM_one (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (L : Set (Fin n → E)) (M : ℕ) :
    _root_.GlobalTheory.UCls.IsKM c G L M 1 := by
  refine ⟨⟨by simp, fun x y => by simp only [one_mulVec]⟩, fun x _ => ⟨0, ?_, ?_⟩,
    fun x hx => ⟨x, hx, one_mulVec x⟩⟩
  · exact (_root_.GlobalTheory.AdLat.hat F L).zero_mem
  · simp

end GlobalTheory.UCls
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
section
noncomputable section

namespace GlobalTheory.Shin

open Polynomial GlobalTheory.CuspGL
open scoped Classical

def nrmG {G Γ : Type} [Group G] [Group Γ] (φ : Γ →* MulAut G) (s : Γ) (l : ℕ) (δ : G) : G :=
  ((List.range l).map fun i => φ (s ^ i) δ).prod

def Kills {G : Type} [Group G] (φ Y : G → ℂ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V),
    ∑ᶠ g, star (Y g) * LinearMap.trace ℂ V (ρ g) = 0 → ∑ᶠ g, star (φ g) • ρ g = 0

namespace IsoPart

end IsoPart

def IsCl {G : Type} [Group G] (f : G → ℂ) : Prop := ∀ x y : G, f (y⁻¹ * x * y) = f x

def Reg (q m k : ℕ) : Prop := ∀ i : ℕ, 0 < i → i < m → ¬ k * q ^ i ≡ k [MOD q ^ m - 1]

section OneField

variable {F : Type} [Field F]

def ent {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : ℕ) : F :=
  if h : i < n ∧ j < n then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

def tl (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Matrix (Fin a) (Fin a) F := fun i j => ent M i j

def br (a b : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Matrix (Fin b) (Fin b) F :=
  fun i j => ent M (a + i) (a + j)

def InPar (a : ℕ) {n : ℕ} (x : GL (Fin n) F) : Prop :=
  ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → (x : Matrix (Fin n) (Fin n) F) i j = 0

def toG {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : GL (Fin n) F := if h : IsUnit M then h.unit else 1

def tlG (a : ℕ) {n : ℕ} (x : GL (Fin n) F) : GL (Fin a) F := toG (tl a (x : Matrix (Fin n) (Fin n) F))

def brG (a b : ℕ) {n : ℕ} (x : GL (Fin n) F) : GL (Fin b) F := toG (br a b (x : Matrix (Fin n) (Fin n) F))

def gal {F' : Type} [Field F'] (t : F →+* F') (n : ℕ) : GL (Fin n) F →* GL (Fin n) F' :=
  Matrix.GeneralLinearGroup.map t

def hcTw (t : F →+* F) (a b : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (n : ℕ) : GL (Fin n) F → ℂ :=
  fun x => (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹ *
    ∑ᶠ y : GL (Fin n) F, if InPar a (y⁻¹ * x * gal t n y) then
      α (tlG a (y⁻¹ * x * gal t n y)) * β (brG a b (y⁻¹ * x * gal t n y)) else 0

def hc (a b : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (n : ℕ) : GL (Fin n) F → ℂ :=
  hcTw (RingHom.id F) a b α β n

def psiG (S : F[X] → ℂ) (n : ℕ) : GL (Fin n) F → ℂ :=
  fun x => psi S (Fin n → F) (Matrix.toLin' (x : Matrix (Fin n) (Fin n) F))

def chG (S : F[X] → ℂ) (n : ℕ) : GL (Fin n) F → ℂ := fun x => S (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F))

def cusp (θ : AlgebraicClosure F →* ℂ) (m k : ℕ) : GL (Fin m) F → ℂ :=
  fun x => (-1) ^ (m - 1) * psiG (rootSum θ k) m x

def deg (L : List (ℕ × ℕ)) : ℕ := (L.map Prod.fst).sum

def J (θ : AlgebraicClosure F →* ℂ) (L : List (ℕ × ℕ)) : (n : ℕ) → GL (Fin n) F → ℂ :=
  List.rec (motive := fun _ => (n : ℕ) → GL (Fin n) F → ℂ) (fun _ _ => 1)
    (fun p L ih n => hc p.1 (deg L) (cusp θ p.1 p.2) (ih (deg L)) n) L

theorem J_nil (θ : AlgebraicClosure F →* ℂ) (n : ℕ) : J θ [] n = fun _ => 1 := rfl

theorem J_cons (θ : AlgebraicClosure F →* ℂ) (p : ℕ × ℕ) (L : List (ℕ × ℕ)) (n : ℕ) :
    J θ (p :: L) n = hc p.1 (deg L) (cusp θ p.1 p.2) (J θ L (deg L)) n := rfl

def HFree {n : ℕ} (Y : GL (Fin n) F → ℂ) : Prop :=
  0 < n → ∑ᶠ x ∈ {x : GL (Fin n) F | ∀ i j : Fin n, (j : ℕ) + 1 < n →
    (x : Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j}, Y x = 0

end OneField

section TwoFields

variable {F F' : Type} [Field F] [Field F'] [Algebra F F']

def galAct (F F' : Type) [Field F] [Field F'] [Algebra F F'] (n : ℕ) :
    (F' ≃ₐ[F] F') →* MulAut (GL (Fin n) F') where
  toFun t :=
    { toFun := gal (t : F' →+* F') n
      invFun := gal (t.symm : F' →+* F') n
      left_inv := fun x => by ext i j; simp [gal]
      right_inv := fun x => by ext i j; simp [gal]
      map_mul' := fun x y => map_mul _ x y }
  map_one' := by ext x i j; simp [gal]
  map_mul' s t := by ext x i j; simp [gal]

theorem galAct_apply (n : ℕ) (t : F' ≃ₐ[F] F') (x : GL (Fin n) F') :
    galAct F F' n t x = gal (t : F' →+* F') n x := rfl

def incl (F F' : Type) [Field F] [Field F'] [Algebra F F'] (n : ℕ) : GL (Fin n) F →* GL (Fin n) F' :=
  gal (algebraMap F F') n

def nrm (s : F' ≃ₐ[F] F') {n : ℕ} (δ : GL (Fin n) F') : GL (Fin n) F' :=
  nrmG (galAct F F' n) s (Module.finrank F F') δ

def IsNorm (s : F' ≃ₐ[F] F') {n : ℕ} (δ : GL (Fin n) F') (γ : GL (Fin n) F) : Prop :=
  IsConj (incl F F' n γ) (nrm s δ)

def shLift (s : F' ≃ₐ[F] F') {n : ℕ} (f : GL (Fin n) F → ℂ) (δ : GL (Fin n) F') : ℂ :=
  if h : ∃ γ, IsNorm s δ γ then f h.choose else 0

abbrev GHat (F F' : Type) [Field F] [Field F'] [Algebra F F'] (n : ℕ) : Type :=
  GL (Fin n) F' ⋊[galAct F F' n] (F' ≃ₐ[F] F')

def pullθ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ) :
    AlgebraicClosure F →* ℂ := θ.comp (ι : AlgebraicClosure F →* AlgebraicClosure F')

end TwoFields

def liftL (q l : ℕ) (L : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  L.flatMap fun p => (List.range l).map fun i => (p.1 / l, p.2 * q ^ i)

def liftAll (q l : ℕ) (L : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  L.flatMap fun p => if l ∣ p.1 then liftL q l [p] else [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))]

theorem isNorm_one {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') (n : ℕ) :
    IsNorm s (1 : GL (Fin n) F') (1 : GL (Fin n) F) := by
  have : nrm s (1 : GL (Fin n) F') = 1 := by
    unfold nrm nrmG
    apply List.prod_eq_one
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact map_one _
  unfold IsNorm
  rw [this, map_one]

end GlobalTheory.Shin

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
section
set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField

namespace GlobalTheory.ChowHt

structure IsChowForm {k : Type} [Field k] {N : ℕ} (I : Ideal (MvPolynomial (Fin N) k)) (D δ : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) k) : Prop where

  homog : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => δ) f

  irred : Irreducible (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f)

  zero_iff : ∀ u : Fin (D + 1) × Fin N → AlgebraicClosure k, MvPolynomial.aeval u f = 0 ↔
    ∃ y : Fin N → AlgebraicClosure k, y ≠ 0 ∧ (∀ g ∈ I, MvPolynomial.aeval y g = 0) ∧
      ∀ i, ∑ j, u (i, j) * y j = 0

def linSubst {R : Type} [CommRing R] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (f : MvPolynomial (Fin B × Fin N) R) : MvPolynomial (Fin B × Fin n) R :=
  MvPolynomial.aeval (fun p : Fin B × Fin N => ∑ k, C (M p.2 k) * X (p.1, k)) f

def frameNorm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖(A⁻¹.mulVec x) i‖ ^ 2)

def formHeight {F : Type} [Field F] [NumberField F] {B N n : ℕ} (δ : ℕ)
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin B × Fin N) F) : ℝ :=
  ((∑ᶠ v : FinitePlace F, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v (linSubst w f))) +
    ∑ σ : F →+* ℂ, (ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ f)) +
      (B : ℝ) * δ * (harmonic (N - 1) : ℝ) / 2)) / (Module.finrank ℚ F : ℝ)

def pointHeight {F : Type} [Field F] [NumberField F] {N n : ℕ}
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    {K : Type} [Field K] [NumberField K] [Algebra F K] (y : Fin N → K) : ℝ :=
  ((∑ᶠ v : FinitePlace K, Real.log (⨆ k, v (∑ j, algebraMap F K (w j k) * y j))) +
    ∑ τ : K →+* ℂ, Real.log (Real.sqrt
      (∑ i, ‖∑ j, A (τ.comp (algebraMap F K)) j i * τ (y j)‖ ^ 2))) / (Module.finrank ℚ K : ℝ)

def ConjCompat {F : Type} [Field F] {N : ℕ} (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ (σ : F →+* ℂ) (x : Fin N → ℂ),
    frameNorm (A ((starRingEnd ℂ).comp σ)) (fun j => (starRingEnd ℂ) (x j)) = frameNorm (A σ) x

end GlobalTheory.ChowHt
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
section
noncomputable section

open ZetaZeros.D.EllReg
open scoped BoundedContinuousFunction

namespace GlobalTheory.HCA

variable {d : ℕ}

def apOp (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (u : E d → ℂ) (x : E d) : ℂ :=
  ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d, a n w x * dw (List.ofFn w) u x

def symb (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (x ξ : E d) : ℂ :=
  ∑ w : Fin m → Fin d, a m w x * ∏ l, ((ξ (w l) : ℝ) : ℂ)

def oneSys (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) : Sys d Unit := ⟨fun _ => m, fun _ => a⟩


open Classical in
def ext0 (U : Set (E d)) (u : U → ℂ) (x : E d) : ℂ := by
  classical
  exact if hx : x ∈ U then u ⟨x, hx⟩ else 0

def solSet {ι : Type} (P : Sys d ι) (U : Set (E d)) : Set (U →ᵇ ℂ) := {u | WeakSol P U (ext0 U u)}


open scoped BoundedContinuousFunction in
variable {d : ℕ} in
theorem _root_.GlobalTheory.HCA.apOp_zero_one (u : _root_.ZetaZeros.D.EllReg.E d → ℂ) (x : _root_.ZetaZeros.D.EllReg.E d) :
    _root_.GlobalTheory.HCA.apOp 0 (fun _ _ _ => 1) u x = u x := by
  simp only [_root_.GlobalTheory.HCA.apOp, zero_add, Finset.range_one, Finset.sum_singleton,
    one_mul, Fintype.sum_unique, List.ofFn_zero]
  unfold _root_.ZetaZeros.D.EllReg.dw
  rfl


open scoped BoundedContinuousFunction in
variable {d : ℕ} in
theorem _root_.GlobalTheory.HCA.zero_mem_solSet {ι : Type} (P : _root_.ZetaZeros.D.EllReg.Sys d ι) (U : Set (_root_.ZetaZeros.D.EllReg.E d)) :
    (0 : U →ᵇ ℂ) ∈ _root_.GlobalTheory.HCA.solSet P U := by
  have h : _root_.GlobalTheory.HCA.ext0 U (0 : U →ᵇ ℂ) = fun _ => 0 := by
    funext x
    unfold _root_.GlobalTheory.HCA.ext0
    split_ifs <;> rfl
  show _root_.ZetaZeros.D.EllReg.WeakSol P U (_root_.GlobalTheory.HCA.ext0 U (0 : U →ᵇ ℂ))
  rw [h]
  unfold _root_.ZetaZeros.D.EllReg.WeakSol
  intro i φ _ _ _
  simp

end GlobalTheory.HCA

end
end

