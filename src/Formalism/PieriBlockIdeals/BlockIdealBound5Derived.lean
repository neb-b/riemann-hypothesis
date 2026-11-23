module

public import Mathlib
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.RankGapBounds.TheoremALocOfLemmaA
public import Formalism.PieriBlockIdeals.Bundle0001
public import Formalism.PieriBlockIdeals.Bundle0005
public import Formalism.PieriBlockIdeals.Bundle0003
public import Formalism.RankGapBounds.Bundle0001
public import Formalism.PieriBlockIdeals.LemmaWAssembled

@[expose] public section

noncomputable section

open TensorProduct MvPolynomial CategoryTheory CategoryTheory.Limits

namespace Formalism.CohomologicalDescent.DepthNonnegative

open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds

def ApplicationWindow : Prop :=
  LemmaDLastGraded → ∀ (l k j t q h : ℕ) (lam : ℕ → ℕ) (xm xp : ℤ), l.Prime → 1 ≤ t →
    (∀ a b, a ≤ b → b < k + j + t + q → lam b ≤ lam a) →
    (∀ a, k + j ≤ a → a < k + j + t → lam a = lam (k + j)) →
    lam 0 + (k + j + t + q) ≤ h + lam (k + j + t + q - 1) + 1 → h < l ^ 2 →
    (∀ a, a < k → xm ≤ UN (k + j + t + q) lam a ∧ UN (k + j + t + q) lam a ≤ xp) →
    (∀ a, k ≤ a → a < k + j → UN (k + j + t + q) lam a < xm) →
    UN (k + j + t + q) lam (k + j) < xm → xm ≤ xp → xp - UN (k + j + t + q) lam (k + j) ≤ (h : ℤ) →
    ∀ ecl : ℕ, (∀ μ : Fin k → ℕ, ExpLe l k (res k lam) μ ecl) →
      ∀ I : ℕ, ExpUpTo l (k + j + t + q) lam (varpi (k + j)) (I : ℤ)
        ⌊cPrime l k j t q h ecl xm xp (UN (k + j + t + q) lam (k + j)) (I : ℝ)⌋₊

def chainB {O : Type} [CommRing O] {ι : Type} [DecidableEq ι] {Nb : ι → Type} [∀ τ, AddCommGroup (Nb τ)]
    [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)) (s : Finset ι) : ∀ τ, Submodule O (Nb τ) :=
  fun τ => if τ ∈ s then ⊤ else B τ

def atFactor {O : Type} [CommRing O] {ι : Type} [DecidableEq ι] {Nb : ι → Type} [∀ τ, AddCommGroup (Nb τ)]
    [∀ τ, Module O (Nb τ)] (τ : ι) (p : Nb τ →ₗ[O] Nb τ) : (⨂[O] τ, Nb τ) →ₗ[O] (⨂[O] τ, Nb τ) :=
  PiTensorProduct.map (Function.update (fun _ => LinearMap.id) τ p)

def AtFactorTprod : Prop :=
  ∀ (O : Type) [CommRing O] (ι : Type) [Fintype ι] [DecidableEq ι] (Nb : ι → Type)
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (τ : ι) (p : Nb τ →ₗ[O] Nb τ) (x : ∀ τ, Nb τ),
    atFactor τ p (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ (p (x τ)))

def TensorWeightKill : Prop :=
  ∀ (O : Type) [CommRing O] (ι : Type) [Fintype ι] [DecidableEq ι] (Nb : ι → Type)
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)) (s : Finset ι) (a : ι)
    (p : Nb a →ₗ[O] Nb a) (l : O) (c : ℕ), a ∉ s → (∀ x, l ^ c • p x ∈ B a) →
    ∀ y ∈ tensSub (chainB B (insert a s)), l ^ c • atFactor a p y ∈ tensSub (chainB B s)

def ChainEnds : Prop :=
  ∀ (O : Type) [CommRing O] (ι : Type) [Fintype ι] [DecidableEq ι] (Nb : ι → Type)
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)),
    tensSub (chainB B ∅) = tensSub B ∧ tensSub (chainB B Finset.univ) = ⊤

def ChainMono : Prop :=
  ∀ (O : Type) [CommRing O] (ι : Type) [Fintype ι] [DecidableEq ι] (Nb : ι → Type)
    [∀ τ, AddCommGroup (Nb τ)] [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)) (s s' : Finset ι),
    s ⊆ s' → tensSub (chainB B s) ≤ tensSub (chainB B s')

def scaleSub {O : Type} [CommRing O] (A : Type) [Ring A] [Algebra O A] (V : Type) [AddCommGroup V]
    [Module O V] [Module A V] [IsScalarTower O A V] (c : O) : Submodule A V where
  carrier := {x | ∃ y : V, x = c • y}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩; exact ⟨y + z, by rw [smul_add]⟩
  smul_mem' := by rintro a _ ⟨y, rfl⟩; exact ⟨a • y, by rw [smul_comm]⟩

def IsSubquot (A : Type) [Ring A] (V G : Type) [AddCommGroup V] [Module A V] [AddCommGroup G]
    [Module A G] : Prop :=
  ∃ (E : Submodule A V) (ψ : E →ₗ[A] G), Function.Surjective ψ

def SimpleSubquotOfPower : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (V : Type) [AddCommGroup V]
    [Module O V] [Module A V] [IsScalarTower O A V] (ϖ : O) (n : ℕ) (F F' : Submodule A V),
    F ≤ F' → scaleSub A V (ϖ ^ n) ≤ F → IsSimpleModule A (F' ⧸ F.comap F'.subtype) →
    IsSubquot A (V ⧸ scaleSub A V ϖ) (F' ⧸ F.comap F'.subtype)

def SubquotIso : Prop :=
  ∀ (A : Type) [Ring A] (V G G' : Type) [AddCommGroup V] [Module A V] [AddCommGroup G] [Module A G]
    [AddCommGroup G'] [Module A G'], Nonempty (G ≃ₗ[A] G') → IsSubquot A V G → IsSubquot A V G'

def repOf (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    {K : Subgroup G} (jK : K →* A) (W : Type) [AddCommGroup W] [Module O W] [Module A W]
    [IsScalarTower O A W] : Representation O K W :=
  ((Algebra.lsmul O O W : A →ₐ[O] Module.End O W) : A →* Module.End O W).comp jK

abbrev Forms (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) (W : Type) [AddCommGroup W] [Module O W]
    [Module A W] [IsScalarTower O A W] : Submodule O (G → W) :=
  AMFK O Γ K (repOf O jK W)

def HeckeStable (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) (T : Type) [CommRing T] (V : Type)
    [AddCommGroup V] [Module O V] [Module A V] [IsScalarTower O A V] [Module T (Forms O Γ jK V)] :
    Prop :=
  ∀ (U : Submodule A V) (t : T) (f : Forms O Γ jK V), (∀ g, (f : G → V) g ∈ U) →
    ∀ g, ((t • f : Forms O Γ jK V) : G → V) g ∈ U

def HeckeNat (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) (T : Type) [CommRing T] (V W : Type)
    [AddCommGroup V] [Module O V] [Module A V] [IsScalarTower O A V] [AddCommGroup W] [Module O W]
    [Module A W] [IsScalarTower O A W] [Module T (Forms O Γ jK V)] [Module T (Forms O Γ jK W)] :
    Prop :=
  ∀ (U : Submodule A V) (ψ : U →ₗ[A] W) (t : T) (f : Forms O Γ jK V) (φ : Forms O Γ jK W)
    (hf : ∀ g, (f : G → V) g ∈ U) (hf' : ∀ g, ((t • f : Forms O Γ jK V) : G → V) g ∈ U),
    (∀ g, (φ : G → W) g = ψ ⟨(f : G → V) g, hf g⟩) →
    ∀ g, ((t • φ : Forms O Γ jK W) : G → W) g = ψ ⟨((t • f : Forms O Γ jK V) : G → V) g, hf' g⟩

def FormsStep : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (G : Type) [Group G] (Γ K : Subgroup G)
    (jK : K →* A) (T : Type) [CommRing T] (V W : Type) [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [AddCommGroup W] [Module O W] [Module A W] [IsScalarTower O A W]
    [Module T (Forms O Γ jK V)] [Module T (Forms O Γ jK W)] (S : Submonoid T)
    (F F' : Submodule A V) (ψ : F' →ₗ[A] W),
    HeckeStable O Γ jK T V → HeckeNat O Γ jK T V W → (∀ x : F', ψ x = 0 → (x : V) ∈ F) →
    Subsingleton (LocalizedModule S (Forms O Γ jK W)) →
    ∀ f : Forms O Γ jK V, (∀ g, (f : G → V) g ∈ F') →
      ∃ s ∈ S, ∀ g, ((s • f : Forms O Γ jK V) : G → V) g ∈ F

def FormsDevissage : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (G : Type) [Group G] (Γ K : Subgroup G)
    (jK : K →* A) (T : Type) [CommRing T] (V : Type) [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module T (Forms O Γ jK V)] (S : Submonoid T) (D₀ : Submodule O V)
    (D E : Submodule A V), IsNoetherian O V → IsArtinian O (V ⧸ D₀) → D₀ ≤ D.restrictScalars O →
    D ≤ E →
    (∀ F F' : Submodule A V, D ≤ F → F ⋖ F' → F' ≤ E →
      ∀ f : Forms O Γ jK V, (∀ g, (f : G → V) g ∈ F') →
        ∃ s ∈ S, ∀ g, ((s • f : Forms O Γ jK V) : G → V) g ∈ F) →
    ∀ f : Forms O Γ jK V, (∀ g, (f : G → V) g ∈ E) →
      ∃ s ∈ S, ∀ g, ((s • f : Forms O Γ jK V) : G → V) g ∈ D

def cTau {ι : Type} [DecidableEq ι] (T2 : Finset ι) (ex c' : ι → ℕ) (τ : ι) : ℕ :=
  if τ ∈ T2 then min (ex τ) (c' τ) else ex τ

def TheoremWCore : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (G : Type) [Group G] (Γ K : Subgroup G)
    (jK : K →* A) (ι : Type) [Fintype ι] [DecidableEq ι] (Nb : ι → Type) [∀ τ, AddCommGroup (Nb τ)]
    [∀ τ, Module O (Nb τ)] (B : ∀ τ, Submodule O (Nb τ)) [Module A (⨂[O] τ, Nb τ)]
    [IsScalarTower O A (⨂[O] τ, Nb τ)] (T : Type) [CommRing T] [Algebra O T]
    [Module T (Forms O Γ jK (⨂[O] τ, Nb τ))] [IsScalarTower O T (Forms O Γ jK (⨂[O] τ, Nb τ))]
    (S : Submonoid T) (l ϖ : O) (n₀ : ℕ) (ω : Type) (pr : ∀ τ, ω → Nb τ →ₗ[O] Nb τ) (e : ι → ω → A)
    (Λ : Type) (L : Λ → Type) [∀ μ, AddCommGroup (L μ)] [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)]
    [∀ μ, IsScalarTower O A (L μ)] [∀ μ, Module T (Forms O Γ jK (L μ))]
    (hwt : Λ → ι → ω) (depth : ι → ω → ℤ) (i : ι → ℤ) (T2 : Finset ι) (ex c' : ι → ℕ),
    IsNoetherian O (⨂[O] τ, Nb τ) → IsArtinian O ((⨂[O] τ, Nb τ) ⧸ tensSub B) → l ∣ ϖ ^ n₀ →
    (∀ (s : Finset ι) (a : A), ∀ x ∈ tensSub (chainB B s), a • x ∈ tensSub (chainB B s)) →
    (∀ τ w (x : ⨂[O] τ, Nb τ), e τ w • x = atFactor τ (pr τ w) x) →
    HeckeStable O Γ jK T (⨂[O] τ, Nb τ) → (∀ μ, HeckeNat O Γ jK T (⨂[O] τ, Nb τ) (L μ)) →
    (∀ (Gm : Type) [AddCommGroup Gm] [Module A Gm], IsSimpleModule A Gm →
      IsSubquot A ((⨂[O] τ, Nb τ) ⧸ scaleSub A (⨂[O] τ, Nb τ) ϖ) Gm → ∃ μ, Nonempty (Gm ≃ₗ[A] L μ)) →
    (∀ μ τ, ∃ z : L μ, e τ (hwt μ τ) • z ≠ 0) →
    (∀ μ, IsSubquot A ((⨂[O] τ, Nb τ) ⧸ scaleSub A (⨂[O] τ, Nb τ) ϖ) (L μ) →
      ¬ Subsingleton (LocalizedModule S (Forms O Γ jK (L μ))) → ∀ τ ∈ T2, depth τ (hwt μ τ) ≤ i τ) →
    (∀ τ, LatIncl l (B τ) (ex τ)) →
    (∀ τ ∈ T2, ∀ w, depth τ w ≤ i τ → ∀ x : Nb τ, l ^ c' τ • pr τ w x ∈ B τ) →
    ∀ y : LocalizedModule S (Forms O Γ jK (⨂[O] τ, Nb τ)),
      (algebraMap O T l) ^ (∑ τ, cTau T2 ex c' τ) • y ∈
        locSet S {x : Forms O Γ jK (⨂[O] τ, Nb τ) |
          (x : G → ⨂[O] τ, Nb τ) ∈ formsIn Γ K (repOf O jK (⨂[O] τ, Nb τ)) (tensSub B)}

abbrev NablaT (O : Type) [CommRing O] (N : ℕ) {ι : Type} (lam : ι → ℕ → ℕ) : Type :=
  ⨂[O] τ : ι, dualWeyl O N N (res N (lam τ))

def deltaIn (O : Type) [CommRing O] (N : ℕ) {ι : Type} (lam : ι → ℕ → ℕ) (τ : ι) :
    Submodule O (dualWeyl O N N (res N (lam τ))) :=
  (weyl O N N le_rfl (res N (lam τ))).comap (dualWeyl O N N (res N (lam τ))).subtype

def depthAt (N k : ℕ) {ι : Type} (j : ι → ℕ) (lam : ι → ℕ → ℕ) (τ : ι) (w : Fin N → ℕ) : ℤ :=
  depth2 (res N (varpi (k + j τ))) (res N (lam τ)) w

def cFloor (l N k t h : ℕ) {ι : Type} (lam : ι → ℕ → ℕ) (j q : ι → ℕ) (xm xp : ι → ℤ) (ecl i : ι → ℕ)
    (τ : ι) : ℕ :=
  ⌊cPrime l k (j τ) t (q τ) h (ecl τ) (xm τ) (xp τ) (UN N (lam τ) (k + j τ)) (i τ : ℝ)⌋₊

structure Shape (N k j t q h : ℕ) (lam : ℕ → ℕ) (xm xp : ℤ) : Prop where
  what₂ : k + j + t + q = N
  anti : ∀ a b, a ≤ b → b < N → lam b ≤ lam a
  block : ∀ a, k + j ≤ a → a < k + j + t → lam a = lam (k + j)
  spread : lam 0 + N ≤ h + lam (N - 1) + 1
  cloud : ∀ a, a < k → xm ≤ UN N lam a ∧ UN N lam a ≤ xp
  lows : ∀ a, k ≤ a → a < k + j → UN N lam a < xm
  above : UN N lam (k + j) < xm
  le : xm ≤ xp
  top : xp - UN N lam (k + j) ≤ (h : ℤ)

def TopInputs (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) {ι : Type} [DecidableEq ι] (l N k t h : ℕ)
    (lam : ι → ℕ → ℕ) (T2 : Finset ι) (j q : ι → ℕ) (xm xp : ι → ℤ) (ecl ex i : ι → ℕ)
    [Module A (NablaT O N lam)] [IsScalarTower O A (NablaT O N lam)] (T : Type) [CommRing T]
    [Module T (Forms O Γ jK (NablaT O N lam))] (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
    (e : ι → (Fin N → ℕ) → A) {Λ : Type} (L : Λ → Type) [∀ μ, AddCommGroup (L μ)]
    [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)] [∀ μ, IsScalarTower O A (L μ)]
    [∀ μ, Module T (Forms O Γ jK (L μ))] (hwt : Λ → ι → Fin N → ℕ) : Prop :=
  l.Prime ∧ (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : O)) ∧ Finite (O ⧸ Ideal.span {(l : O)}) ∧
  (l : O) ∣ ϖ ^ n₀ ∧ h < l ^ 2 ∧ 1 ≤ t ∧
  (∀ τ ∈ T2, Shape N k (j τ) t (q τ) h (lam τ) (xm τ) (xp τ)) ∧
  (∀ τ ∈ T2, ∀ μ : Fin k → ℕ, ExpLe l k (res k (lam τ)) μ (ecl τ)) ∧
  (∀ τ, LA.InclZ N N le_rfl (res N (lam τ)) l (ex τ)) ∧
  (∀ (s : Finset ι) (a : A), ∀ x ∈ tensSub (chainB (deltaIn O N lam) s),
    a • x ∈ tensSub (chainB (deltaIn O N lam) s)) ∧
  (∀ τ w (x : ∀ τ, dualWeyl O N N (res N (lam τ))) (y : dualWeyl O N N (res N (lam τ))),
    (y : MvPolynomial (Fin N × Fin N) O) =
      weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial (Fin N × Fin N) O) →
    e τ w • PiTensorProduct.tprod O x = PiTensorProduct.tprod O (Function.update x τ y)) ∧
  HeckeStable O Γ jK T (NablaT O N lam) ∧ (∀ μ, HeckeNat O Γ jK T (NablaT O N lam) (L μ)) ∧
  (∀ (Gm : Type) [AddCommGroup Gm] [Module A Gm], IsSimpleModule A Gm →
    IsSubquot A (NablaT O N lam ⧸ scaleSub A (NablaT O N lam) ϖ) Gm → ∃ μ, Nonempty (Gm ≃ₗ[A] L μ)) ∧
  (∀ μ τ, ∃ z : L μ, e τ (hwt μ τ) • z ≠ 0) ∧
  (∀ μ, IsSubquot A (NablaT O N lam ⧸ scaleSub A (NablaT O N lam) ϖ) (L μ) →
    ¬ Subsingleton (LocalizedModule S (Forms O Γ jK (L μ))) →
    ∀ τ ∈ T2, depthAt N k j lam τ (hwt μ τ) ≤ (i τ : ℤ))

def TopIncl (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] {G : Type} [Group G]
    (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A) {ι : Type} (l N : ℕ) (lam : ι → ℕ → ℕ)
    [Module A (NablaT O N lam)] [IsScalarTower O A (NablaT O N lam)] {T : Type} [CommRing T]
    [Algebra O T] [Module T (Forms O Γ jK (NablaT O N lam))] (S : Submonoid T) (J : ℕ) : Prop :=
  ∀ y : LocalizedModule S (Forms O Γ jK (NablaT O N lam)),
    (algebraMap O T (l : O)) ^ J • y ∈
      locSet S {x : Forms O Γ jK (NablaT O N lam) |
        (x : G → NablaT O N lam) ∈ formsIn Γ K (repOf O jK (NablaT O N lam)) (tensSub (deltaIn O N lam))}

def TheoremWTop : Prop :=
  LemmaDLastGraded →
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] (A : Type) [Ring A] [Algebra O A]
    (G : Type) [Group G] (Γ K : Subgroup G) (jK : K →* A) (ι : Type) [Fintype ι] [DecidableEq ι]
    (l N k t h : ℕ) (lam : ι → ℕ → ℕ) (T2 : Finset ι) (j q : ι → ℕ) (xm xp : ι → ℤ) (ecl ex i : ι → ℕ)
    [Module A (NablaT O N lam)] [IsScalarTower O A (NablaT O N lam)] (T : Type) [CommRing T]
    [Algebra O T] [Module T (Forms O Γ jK (NablaT O N lam))]
    [IsScalarTower O T (Forms O Γ jK (NablaT O N lam))] (S : Submonoid T) (ϖ : O) (n₀ : ℕ)
    (e : ι → (Fin N → ℕ) → A) (Λ : Type) (L : Λ → Type) [∀ μ, AddCommGroup (L μ)]
    [∀ μ, Module O (L μ)] [∀ μ, Module A (L μ)] [∀ μ, IsScalarTower O A (L μ)]
    [∀ μ, Module T (Forms O Γ jK (L μ))] (hwt : Λ → ι → Fin N → ℕ),
    TopInputs O A Γ jK l N k t h lam T2 j q xm xp ecl ex i T S ϖ n₀ e L hwt →
    TopIncl O Γ jK l N lam S (∑ τ, cTau T2 ex (cFloor l N k t h lam j q xm xp ecl i) τ) ∧
    sInf {J : ℕ | TopIncl O Γ jK l N lam S J} ≤
      ∑ τ, cTau T2 ex (cFloor l N k t h lam j q xm xp ecl i) τ




def ExpLeOfInclZ : Prop :=
  ∀ (r : ℕ) (ν μ : Fin r → ℕ) (l e : ℕ), LA.InclZ r r le_rfl ν l e → ExpLe l r ν μ e

def ExactExponentsFit : Prop :=
  ∀ (l N k : ℕ) (lam : ℕ → ℕ), l.Prime → Antitone (res N lam) → Antitone (res k lam) →
    LA.InclZ N N le_rfl (res N lam) l (LA.exZ N N le_rfl (res N lam) l) ∧
      ∀ μ : Fin k → ℕ, ExpLe l k (res k lam) μ (LA.exZ k k le_rfl (res k lam) l)

def TopInclMono : Prop :=
  ∀ (O : Type) [CommRing O] (A : Type) [Ring A] [Algebra O A] (G : Type) [Group G] (Γ K : Subgroup G)
    (jK : K →* A) (ι : Type) (l N : ℕ) (lam : ι → ℕ → ℕ) [Module A (NablaT O N lam)]
    [IsScalarTower O A (NablaT O N lam)] (T : Type) [CommRing T] [Algebra O T]
    [Module T (Forms O Γ jK (NablaT O N lam))] [IsScalarTower O T (Forms O Γ jK (NablaT O N lam))]
    (S : Submonoid T) (J J' : ℕ), J ≤ J' → TopIncl O Γ jK l N lam S J → TopIncl O Γ jK l N lam S J'

def cFloorCoarse (l N k t h : ℕ) {ι : Type} (lam : ι → ℕ → ℕ) (j q : ι → ℕ) (xm xp : ι → ℤ)
    (ecl i : ι → ℕ) (τ : ι) : ℕ :=
  ⌊cCoarse l k (j τ) t (q τ) h N (ecl τ) (xm τ) (xp τ) (UN N (lam τ) (k + j τ)) (i τ : ℝ)⌋₊


def DepthAsU : Prop :=
  ∀ (N c : ℕ) (lam : ℕ → ℕ) (w : Fin N → ℕ),
    depth2 (res N (varpi c)) (res N lam) w =
      ∑ a ∈ Finset.univ.filter (fun a : Fin N => (a : ℕ) < c),
        (UN N lam a - ((w a : ℤ) + (N : ℤ) - 1 - ((a : ℕ) : ℤ)))

end Formalism.CohomologicalDescent.DepthNonnegative
