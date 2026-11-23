module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace

namespace GlobalTheory.FlagEmb

section Lin

variable {T : Type} (m : T → ℕ)

abbrev Let : Type := Σ τ : T, Fin (m τ)

abbrev CellVar : Type := Σ τ : T, {ij : Fin (m τ) × Fin (m τ) // ij.2 < ij.1}

abbrev Pm : Type := ∀ τ : T, Equiv.Perm (Fin (m τ))

variable {m} {S : Type} [CommRing S] {M : ℕ}

def cell (x : CellVar m → S) (τ : T) (i j : Fin (m τ)) : S :=
  if h : j < i then x ⟨τ, ⟨(i, j), h⟩⟩ else if i = j then 1 else 0

def cellVec {ι : Type} (c : Let m → ι → S) (w : Pm m) (x : CellVar m → S) : Let m → ι → S :=
  fun z => ∑ i, cell x z.1 i z.2 • c ⟨z.1, w z.1 i⟩

def wLet (w : Pm m) (z : Let m) : Let m := ⟨z.1, w z.1 z.2⟩

def Down {k : ℕ} (e : Fin k → Let m) : Prop :=
  Function.Injective e ∧ ∀ (l : Fin k) (j : Fin (m (e l).1)), j < (e l).2 → ∃ l', e l' = ⟨(e l).1, j⟩

def std (τ : T) (k : ℕ) (h : k ≤ m τ) : Fin k → Let m := fun l => ⟨τ, Fin.castLE h l⟩

theorem down_std (τ : T) (k : ℕ) (h : k ≤ m τ) : Down (std τ k h) := by
  refine ⟨fun a b hab => ?_, fun l j hj => ⟨⟨j, lt_trans hj l.2⟩, rfl⟩⟩
  have := congrArg (fun z : Let m => (z.2 : ℕ)) hab
  exact Fin.ext this


variable (m) in
abbrev En : Type := Σ k : ℕ, {e : Fin k → Let m // Down e}

abbrev stdEn (τ : T) (k : ℕ) (h : k ≤ m τ) : En m := ⟨k, std τ k h, down_std τ k h⟩

instance finite_en [Finite T] : Finite (En m) := by
  have := Fintype.ofFinite (Let m)
  refine Finite.of_surjective (fun a : Σ k : Fin (Fintype.card (Let m) + 1), {e : Fin k → Let m // Down e} =>
    (⟨a.1, a.2⟩ : En m)) ?_
  rintro ⟨k, e⟩
  have hk : k ≤ Fintype.card (Let m) := by simpa using Fintype.card_le_of_injective _ e.2.1
  exact ⟨⟨⟨k, Nat.lt_succ_of_le hk⟩, e⟩, rfl⟩

def plN (M k : ℕ) : ℕ := (M + 1) ^ k - 1

def plE (M k : ℕ) : Fin (plN M k + 1) ≃ (Fin k → Fin (M + 1)) :=
  (finCongr (Nat.sub_add_cancel (Nat.one_le_pow _ _ (Nat.succ_pos M)))).trans finFunctionFinEquiv.symm

def plk {ι : Type} {k : ℕ} (c : ι → Fin (M + 1) → S) (e : Fin k → ι) : Fin (plN M k + 1) → S :=
  fun q => (Matrix.of fun l l' => c (e l) (plE M k q l')).det

def lform {ι : Type} {k : ℕ} (D : ι → Fin (M + 1) → S) (ρ : Fin k → ι) : Fin (plN M k + 1) → S :=
  fun q => ∏ l, D (ρ l) (plE M k q l)


open Classical in
def LeftInv {ι : Type} (D c : ι → Fin M → S) : Prop := ∀ z z', ∑ r, D z r * c z' r = if z = z' then 1 else 0

def Tri {ι : Type} (c c' : Let m → ι → S) (d : Let m → S) : Prop :=
  ∀ z : Let m, c' z - d z • c z ∈ Submodule.span S ((fun j : Fin (m z.1) => c ⟨z.1, j⟩) '' {j | j < z.2})

def InBlock {ι : Type} (c c' : Let m → ι → S) : Prop :=
  ∀ z : Let m, c' z ∈ Submodule.span S (Set.range fun j : Fin (m z.1) => c ⟨z.1, j⟩)

theorem map_plk {ι : Type} {k : ℕ} {S' : Type} [CommRing S'] (φ : S →+* S') (c : ι → Fin (M + 1) → S) (e : Fin k → ι) :
    φ ∘ plk c e = plk (fun z => φ ∘ c z) e := by
  funext q
  simp only [plk, Function.comp_apply, RingHom.map_det]
  rfl

theorem map_cellVec {ι : Type} {S' : Type} [CommRing S'] (φ : S →+* S') (c : Let m → ι → S) (w : Pm m)
    (x : CellVar m → S) (z : Let m) : φ ∘ cellVec c w x z = cellVec (fun z => φ ∘ c z) w (φ ∘ x) z := by
  funext r
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cellVec, Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  unfold cell
  split_ifs <;> simp

theorem LeftInv.map {ι : Type} {S' : Type} [CommRing S'] (φ : S →+* S') {D c : ι → Fin M → S} (h : LeftInv D c) :
    LeftInv (fun z => φ ∘ D z) (fun z => φ ∘ c z) := fun z z' => by
  have := congrArg φ (h z z')
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul] at this
  refine this.trans ?_
  split_ifs <;> simp

end Lin

section Geo

variable {O K : Type} [CommRing O] [Field K] (β : O →+* K) {X : Scheme.{0}} (s : X ⟶ Sp O) {T : Type} {m : T → ℕ}
  {M : ℕ} {B : Type} (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1))

structure IsCover (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) : Prop where
  ovr : ∀ b, (V b).2.fromSpec ≫ s = spMap ((α b).comp β)
  inv : ∀ b, LeftInv (D b) (c b)
  compat : ∀ (k : Type) [Field k] b b' (φ : Γ(X, (V b).1) →+* k) (φ' : Γ(X, (V b').1) →+* k),
    spMap φ ≫ (V b).2.fromSpec = spMap φ' ≫ (V b').2.fromSpec →
      InBlock (fun z => φ ∘ c b z) (fun z => φ' ∘ c b' z)


variable (m) in
abbrev CR (U : X.affineOpens) : Type := MvPolynomial (CellVar m) Γ(X, U.1)


variable (m) in
def cbase (U : X.affineOpens) : Sp (CR m U) ⟶ X := spMap (MvPolynomial.C : Γ(X, U.1) →+* CR m U) ≫ U.2.fromSpec

def uvec {U : X.affineOpens} (c : Let m → Fin (M + 1) → Γ(X, U.1)) (w : Pm m) : Let m → Fin (M + 1) → CR m U :=
  cellVec (fun z => MvPolynomial.C ∘ c z) w MvPolynomial.X

variable (c : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1))

structure HasPlk {P : Scheme.{0}} (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1))
    (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)) : Prop where
  base : ∀ b w, h b w ≫ p0 = cbase m (V b)
  plk : ∀ b w en, ∃ hu, h b w ≫ p en =
    pt ((MvPolynomial.C : _ →+* CR m (V b)).comp ((α b).comp β)) (plk (uvec (c b) w) en.2.1) hu

structure IsPlk {P : Scheme.{0}} (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1))
    (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)) : Prop extends HasPlk β V α c p0 p h where
  proj : IsProjOver (p0 ≫ s)
  ovr : ∀ en, p en ≫ PSpace.str _ _ = p0 ≫ s
  ext : ∀ (Z : Scheme.{0}) (a a' : Z ⟶ P), a ≫ p0 = a' ≫ p0 → (∀ en, a ≫ p en = a' ≫ p en) → a = a'

def IsCellOpen {P : Scheme.{0}} (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (U : X.affineOpens)
    (D : Let m → Fin (M + 1) → Γ(X, U.1)) (w : Pm m) (W : P.Opens) : Prop :=
  ∀ (k : Type) [Field k] (z : Sp k ⟶ P), Set.range z ⊆ W ↔ ∃ φ : Γ(X, U.1) →+* k, z ≫ p0 = spMap φ ≫ U.2.fromSpec ∧
    ∀ τ j hj (b : O →+* k) v hv, z ≫ p (stdEn τ j hj) = pt b v hv →
      ∑ q, φ (lform D (wLet w ∘ std τ j hj) q) * v q ≠ 0

end Geo

section Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

abbrev Tn (R : Type) [CommRing R] : Type := Sp (DualNumber R) ⟶ t.G.left


open GlobalTheory.FactorDepth in
theorem exists_comb {R : Type} [CommRing R] {x : Sp R ⟶ X} {n : ℕ} {u : Fin n → Tn t R} (hu : ∀ j, IsTanAtG t x (u j))
    (a : Fin n → R) : ∃ w, IsTanAtG t x w ∧ IsCombAtG t x u a w :=
  ⟨_, isTanAtG_of _ (combT_tan _ (fun j => ovT (hu j)) (fun j => smT_zero_ovT _) a),
    (isCombAtG_iff t x (fun j => ovT (hu j)) a _).2 rfl⟩


open GlobalTheory.FactorDepth in
theorem comb_unique {R : Type} [CommRing R] {x : Sp R ⟶ X} {n : ℕ} {u : Fin n → Tn t R} (hu : ∀ j, IsTanAtG t x (u j))
    {a : Fin n → R} {w w' : Tn t R} (h : IsCombAtG t x u a w) (h' : IsCombAtG t x u a w') : w = w' :=
  ((isCombAtG_iff t x (fun j => ovT (hu j)) a _).1 h).symm.trans ((isCombAtG_iff t x (fun j => ovT (hu j)) a _).1 h')

theorem comb_tan {R : Type} [CommRing R] {x : Sp R ⟶ X} {n : ℕ} {u : Fin n → Tn t R} (hu : ∀ j, IsTanAtG t x (u j))
    {a : Fin n → R} {w : Tn t R} (h : IsCombAtG t x u a w) : IsTanAtG t x w := by
  obtain ⟨w', h1, h2⟩ := exists_comb t hu a
  exact comb_unique t hu h2 h ▸ h1


variable {Dw : Datum H}

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

end Lie

end GlobalTheory.FlagEmb
