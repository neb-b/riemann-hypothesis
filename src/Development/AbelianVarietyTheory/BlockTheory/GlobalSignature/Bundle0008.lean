module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.Columns.DecoFin

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect

section Abstract

variable {F Y : Type} [Field F] [AddCommGroup Y] [Module F Y] {c : ℕ}

def IsFrame (X : Submodule F Y) (a : Fin c → Y) : Prop :=
  LinearIndependent F a ∧ IsCompl X (Submodule.span F (Set.range a))

def flag (X : Submodule F Y) (a : Fin c → Y) (i : Fin c) : Submodule F Y :=
  X ⊔ Submodule.span F (a '' {l | l < i})

def IsUnip (X : Submodule F Y) (a : Fin c → Y) (n : Y ≃ₗ[F] Y) : Prop :=
  (∀ x ∈ X, n x = x) ∧ (∀ i : Fin c, i.1 = 0 → n (a i) = a i) ∧ ∀ i : Fin c, n (a i) - a i ∈ flag X a i

def IsExtOf (X : Submodule F Y) (a : Fin c → Y) (γ : X ≃ₗ[F] X) (g : Y ≃ₗ[F] Y) : Prop :=
  (∀ x : X, g x = (γ x : Y)) ∧ ∀ i, g (a i) = a i

def IsSemidirect (X : Submodule F Y) (a : Fin c → Y) (r : Y ≃ₗ[F] Y) : Prop :=
  ∃ (γ : X ≃ₗ[F] X) (g n : Y ≃ₗ[F] Y), IsExtOf X a γ g ∧ IsUnip X a n ∧ r = g * n

variable {O : Type} [CommRing O] [Algebra O F] [Module O Y] [IsScalarTower O F Y]

def moveBy (r : Y ≃ₗ[F] Y) (Λ : Submodule O Y) : Submodule O Y :=
  Λ.map (r.toLinearMap.restrictScalars O)

def normalForm (F : Type) [Field F] [Module F Y] [Algebra O F] (q : O) (M : Submodule O Y) (a : Fin c → Y)
    (e : Fin c → ℤ) (z : Y) : Submodule O Y :=
  M ⊔ ⨆ i : Fin c, Submodule.span O {(algebraMap O F q) ^ (e i) • (a i + if i.1 = 0 then z else 0)}

def inY (X : Submodule F Y) (L : Submodule O X) : Submodule O Y :=
  L.map (X.subtype.restrictScalars O)

end Abstract

def LatticeNormalForm : Prop :=
  ∀ (O F Y : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F]
    [AddCommGroup Y] [Module F Y] [Module O Y] [IsScalarTower O F Y]
    (q : O), Irreducible q →
    ∀ (c : ℕ) (X : Submodule F Y) (a : Fin c → Y), IsFrame X a →
    ∀ (L : Submodule O X), Submodule.IsFullLattice F L →
    ∀ (Λ : Submodule O Y), Submodule.IsFullLattice F Λ →
      ∃ (r : Y ≃ₗ[F] Y) (e : Fin c → ℤ) (z : Y), IsSemidirect X a r ∧ z ∈ X ∧
        moveBy r Λ = normalForm F q (inY X L) a e z

def LatticeNormalFormUnip : Prop :=
  ∀ (O F Y : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F]
    [AddCommGroup Y] [Module F Y] [Module O Y] [IsScalarTower O F Y]
    (q : O), Irreducible q →
    ∀ (c : ℕ) (X : Submodule F Y) (a : Fin c → Y), IsFrame X a →
    ∀ (Λ : Submodule O Y), Submodule.IsFullLattice F Λ →
      ∃ (n : Y ≃ₗ[F] Y) (e : Fin c → ℤ) (z : Y), IsUnip X a n ∧ z ∈ X ∧
        moveBy n Λ = normalForm F q (Λ ⊓ X.restrictScalars O) a e z


open Formalism.L2.Col in
def LatticeNormalFormCoord : Prop :=
  ∀ (O F : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F]
    (q : O), Irreducible q →
    ∀ (n c : ℕ) (L : Submodule O (Fin n → F)), Submodule.IsFullLattice F L →
    ∀ (Λ : Submodule O (Fin (n + c) → F)), Submodule.IsFullLattice F Λ →
      ∃ r ∈ Loc.R1 F n c, ∃ (e : Fin c → ℤ) (z : Fin n → F),
        moveBy r Λ = normalForm F q (L.map ((Loc.inX F n c).restrictScalars O))
          (fun i : Fin c => Loc.eN F (n + c) (n + i.1)) e (Loc.inX F n c z)

section Basic₂

variable {F Y : Type} [Field F] [AddCommGroup Y] [Module F Y] {c : ℕ}

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def nfGen (q n c : ℕ) (e : Fin c → ℤ) (z : Sp E n) (i : Fin c) : Sp E (n + c) :=
  ((q : E) ^ e i) • (Loc.eN E (n + c) (n + i.1) + if i.1 = 0 then Loc.inX E n c z else 0)

def nfLat (P : HeightOneSpectrum (𝓞 E)) (n c : ℕ) (e : Fin c → ℤ) (z : Sp E n) : Set (Sp E (n + c)) :=
  {y | ∃ l ∈ stdAt E n P, ∃ s : Fin c → E, (∀ i, IntAt P (s i)) ∧
    y = Loc.inX E n c l + ∑ i, s i • nfGen (qOf P) n c e z i}

end Lattice

variable {X : Fields} {Pr : Primes X} {R : Ranks}


variable (Pr) in
def NF (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  ∃ (e : Fin (cOf R j) → ℤ) (z : Sp X.E (R.N j)),
    (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧
    z ∈ stdAt X.E (R.N j) P ∧
    h '' (lamYat (Pr := Pr) (R := R) j P : Set (Sp X.E (R.N j + cOf R j))) = nfLat P (R.N j) (cOf R j) e z


variable (Pr) in
def Sandwich (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, ∃ y ∈ lamYat (Pr := Pr) (R := R) j P, h y = x) ∧
    ∀ x ∈ lamYat (Pr := Pr) (R := R) j P, ((qOf P : X.E) ^ j) • h x ∈ lamYat (Pr := Pr) (R := R) j P


variable (Pr R) in
def InclAt : Prop :=
  ∀ (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ h k : AutY X R j, NF Pr j P h →
    k ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P) → Sandwich Pr j P (h * k)

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)

theorem mem_lamYat {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (y : Sp X.E (R.N j + cOf R j)) :
    y ∈ lamYat (Pr := Pr) (R := R) j P ↔ ∀ l, IntAt P (y l) := by
  unfold lamYat LocE.lamY LocE.sclLat stdAt
  rw [if_neg hP, Submodule.mem_comap, mem_localization_standardLattice]
  simp [LocE.scE]

theorem nf_one (j : ℕ) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) : NF (R := R) Pr j P 1 := by
  refine ⟨0, 0, fun i => ⟨by simp, le_rfl⟩, zero_mem _, ?_⟩
  have key : ∀ (l : Sp X.E (R.N j)) (s : Fin (cOf R j) → X.E) (p : Fin (R.N j + cOf R j)),
      (Loc.inX X.E (R.N j) (cOf R j) l + ∑ i, s i • nfGen (qOf P) (R.N j) (cOf R j) 0 0 i :
        Sp X.E (R.N j + cOf R j)) p =
        Fin.addCases (motive := fun _ => X.E) l s p := by
    intro l s p
    refine Fin.addCases (fun a => ?_) (fun b => ?_) p
    · have : ∀ i : Fin (cOf R j), ¬ (a.1 = R.N j + i.1) := fun i => by omega
      simp [Loc.inX, nfGen, Loc.eN, Finset.sum_apply, this]
    · simp [Loc.inX, nfGen, Loc.eN, Finset.sum_apply, Fin.val_inj]
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, mem_lamYat hP, nfLat, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun a => x (Fin.castAdd _ a), (mem_localization_standardLattice _ _).2 fun a => hx _, fun b => x (Fin.natAdd _ b),
      fun b => hx _, ?_⟩
    funext p
    rw [key]
    refine Fin.addCases (fun a => ?_) (fun b => ?_) p <;> simp
  · rintro ⟨l, hl, s, hs, rfl⟩
    refine ⟨_, fun p => ?_, rfl⟩
    have hk := key l s p
    rw [Pi.add_apply] at hk
    rw [hk]
    refine Fin.addCases (fun a => ?_) (fun b => ?_) p
    · simpa using (mem_localization_standardLattice _ _).1 hl a
    · simpa using hs b

end GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance

open Formalism.L2.Col

section Defs

variable {E : Type} [Field E] [NumberField E]

theorem intAt_zero (P : HeightOneSpectrum (𝓞 E)) : IntAt P (0 : E) :=
  ⟨0, 1, one_notMem P, by simp⟩

theorem intAt_add {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a + b) := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine ⟨s' * r + s * r', s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  rw [map_add (f := _), map_mul, map_mul, map_mul, ← h, ← h']
  ring

theorem intAt_mul {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a * b) := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine ⟨r * r', s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  rw [map_mul, map_mul, ← h, ← h']
  ring

theorem intAt_neg {P : HeightOneSpectrum (𝓞 E)} {a : E} (ha : IntAt P a) : IntAt P (-a) := by
  obtain ⟨r, s, hs, h⟩ := ha
  exact ⟨-r, s, hs, by rw [map_neg, ← h]; ring⟩

theorem intAt_algebraMap (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) : IntAt P (algebraMap (𝓞 E) E r) :=
  ⟨r, 1, one_notMem P, by simp⟩

def DegOneUnram (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  (qOf P).Prime ∧ ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2

def IsLatAt (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (abelian₂ : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  (∀ u : E, IntAt P u → ∀ v ∈ abelian₂, u • v ∈ abelian₂) ∧
    ∃ m : ℕ, (∀ v : Fin N → E, (∀ l, IntAt P (v l)) → ((qOf P : E) ^ m) • v ∈ abelian₂) ∧
      ∀ v ∈ abelian₂, ∀ l, IntAt P ((qOf P : E) ^ m * v l)

def depthSub (P : HeightOneSpectrum (𝓞 E)) (D : ℕ) : AddSubgroup E where
  carrier := {a | IntAt P ((qOf P : E) ^ D * a)}
  add_mem' := fun {a b} ha hb => by
    show IntAt P _
    rw [mul_add]
    exact intAt_add ha hb
  zero_mem' := by
    show IntAt P _
    rw [mul_zero]
    exact intAt_zero P
  neg_mem' := fun {a} ha => by
    show IntAt P _
    rw [mul_neg]
    exact intAt_neg ha

def unfoldAB {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (A B : ℕ) {n' c' n c : ℕ}
    (Psi : Loc.SF E K (n' + c') (n + c)) : Loc.SF E K n' n :=
  Loc.E1 psi (LocE.valsQ E (qOf P) A B) (((qOf P : K) ^ B)⁻¹) Psi

end Defs

end GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StandardDeterminantUnit
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit

open Formalism.L2.Col

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def StdAtAll (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : Prop :=
  ∀ P ∈ ST, d.1.at P = stdAt E n P

def DetUnitAt (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (Q : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ g : Sp E n ≃ₗ[E] Sp E n, (∀ x : Sp E n, g x ∈ d.1.at Q ↔ x ∈ stdAt E n Q) →
    Q.valuation E (LinearMap.det (g : Sp E n →ₗ[E] Sp E n)) = 1

def SplitNonConj (ST : Finset (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ P ∈ ST, ∀ Q ∈ ST, Q ≠ conjPrime₂ P


variable (E n ST SG) in
def HasStdReps : Prop :=
  ∀ d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG), ∃ ga : UF E n, StdAtAll (((ga, 1) : UF E n × GLG (E := E) (n := n) (SG := SG)) • d)


end Generic

def Representatives : Prop :=
  ∀ (X : Fields), X.Ok → ∀ (Pr : Primes X), Pr.Ok → ∀ (u : Pr.Word) (n : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E)))
    (d : DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := SG)), ∃ ga : UF X.E n, ∀ P ∈ Pr.vT u,
      ((((ga, 1) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d).1.at P = stdAt X.E n P)

def RepresentativesSplit : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E))),
    SplitNonConj ST → HasStdReps E n ST SG

theorem splitNonConj_vT {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) : SplitNonConj (Pr.vT u) := by
  intro P hP Q hQ h
  apply conj_piT_notMem hPr u ⟨Q, hQ⟩
  change cO X.E (Pr.piT u) ∈ Q.asIdeal
  rw [h, mem_conjP, cO_cO]
  exact decoFin_mem_of_mem_divs hP

theorem representatives_of_split (h : RepresentativesSplit) : Representatives :=
  fun X _ _ hPr u n SG d => h X.E n _ SG (splitNonConj_vT hPr u) d

end GlobalTheory.IndefiniteRowSideFullHecke.StandardDeterminantUnit
end
end

