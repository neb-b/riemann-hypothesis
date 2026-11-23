module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.XR

open AlgebraicGeometry CategoryTheory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {Ω : Type} [Field Ω]

abbrev TateIsoAt (D : Datum H) (t : SAB H X) {k : Type} [Field k] (x : Sp k ⟶ X) : Type :=
  TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))

def IsFullLevelAt (D : Datum H) (t : SAB H X) (ξ : Sp Ω ⟶ X) (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)) :
    Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k), ∃ I : TateIsoAt D t (spMap i ≫ ξ),
    (I.ζ N : k) = i z ∧ ∀ a, (I.ev N a).left = spMap i ≫ (ev a).left

end GlobalTheory.CompanionTheory.Ar.XR
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

def secVal {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) (W : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (f : Γ(Z, W)) : B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((x.appLE W ⊤ h).hom f)

def FullTorsion (G : Over X) [GrpObj G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (n : ℕ) : Prop :=
  ∀ (k : Type) [Field k] (i : Ω →+* k) (g : Over.mk (spMap i ≫ ξ) ⟶ G), g ^ n = 1 →
    ∃ x : Over.mk ξ ⟶ G, g.left = spMap i ≫ x.left

namespace LieModel

def IsHTAt (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) (x : Over.mk ξ ⟶ G) (q : Cpt ξ)
    (w : Module.Dual Ω E) : Prop :=
  w ∈ M.omLat q ∧ ∃ (W : G.left.Opens) (f : Γ(G.left, W)), (η[G]).left q.1 ∈ W ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (xk g : Over.mk (spMap i ≫ ξ) ⟶ G) (c : kˣ)
      (h : ⊤ ≤ g.left ⁻¹ᵁ W), xk.left = spMap i ≫ x.left → g ^ n = 1 →
        Out.WeilIs G L n xk g (unitOn c) → secVal (B := k) g.left W h f = c) ∧
    ∀ e v, M.Extends q e v → ∀ h : ⊤ ≤ v.left ⁻¹ᵁ W, ∃ r ∈ regAt ξ q,
      w e = genMap ξ q (secVal (B := DualNumber (X.presheaf.stalk q.1)) v.left W h f).snd + n * r

def htOm (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) : Lat ξ (Module.Dual Ω E) := fun q =>
  Submodule.span (regAt ξ q) {w | ∃ x : Over.mk ξ ⟶ G, x ^ n = 1 ∧ M.IsHTAt L n x q w}

def htOmEig (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
    (σ : O →+* Ω) : Lat ξ (Module.Dual Ω (eigSp ρ σ)) :=
  (M.htOm L n).map (eigSp ρ σ).subtype.dualMap

def htDual (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
    (σ : O →+* Ω) : Lat ξ E := fun q =>
  Submodule.span (regAt ξ q) {e | e ∈ eigSp ρ σ ∧ ∀ w ∈ M.htOm L n q, w e ∈ regAt ξ q}

def htW (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
    (σ : O →+* Ω) (𝔡 : Ideal O) : Lat ξ E := fun q =>
  Submodule.span (regAt ξ q) {e | e ∈ eigSp ρ σ ∧ ∀ d ∈ 𝔡, σ d • e ∈ M.htDual L n ρ σ q}

variable (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
  (σ : O →+* Ω)

theorem htOm_le (q : Cpt ξ) : M.htOm L n q ≤ M.omLat q :=
  Submodule.span_le.2 fun _ ⟨_, _, h⟩ => h.1

theorem mem_htDual_iff (q : Cpt ξ) (e : E) :
    e ∈ M.htDual L n ρ σ q ↔ e ∈ eigSp ρ σ ∧ ∀ w ∈ M.htOm L n q, w e ∈ regAt ξ q := by
  constructor
  · intro he
    induction he using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨(eigSp ρ σ).zero_mem, fun w _ => by simpa using (regAt ξ q).zero_mem⟩
    | add x y _ _ hx hy =>
      exact ⟨(eigSp ρ σ).add_mem hx.1 hy.1, fun w hw => by
        simpa using (regAt ξ q).add_mem (hx.2 w hw) (hy.2 w hw)⟩
    | smul c x _ hx =>
      refine ⟨(eigSp ρ σ).smul_mem (c : Ω) hx.1, fun w hw => ?_⟩
      have : w (c • x) = (c : Ω) * w x := by
        show w ((c : Ω) • x) = _
        rw [map_smul, smul_eq_mul]
      rw [this]
      exact (regAt ξ q).mul_mem c.2 (hx.2 w hw)
  · exact fun h => Submodule.subset_span h

theorem mem_eigSp_of_mem_htDual {q : Cpt ξ} {e : E} (he : e ∈ M.htDual L n ρ σ q) : e ∈ eigSp ρ σ :=
  ((M.mem_htDual_iff L n ρ σ q e).1 he).1

theorem mem_htDual (q : Cpt ξ) (e : eigSp ρ σ) :
    (e : E) ∈ M.htDual L n ρ σ q ↔ ∀ u ∈ M.htOmEig L n ρ σ q, u e ∈ regAt ξ q := by
  rw [mem_htDual_iff]
  constructor
  · rintro ⟨-, h⟩ u hu
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hu
    exact h w hw
  · intro h
    refine ⟨e.2, fun w hw => ?_⟩
    exact h _ (Submodule.mem_map.2 ⟨w, hw, rfl⟩)

theorem eigLat_le_htDual (q : Cpt ξ) : M.eigLat ρ σ q ≤ M.htDual L n ρ σ q :=
  fun e he => Submodule.subset_span ⟨he.2, fun w hw => (M.htOm_le L n q hw) e he.1⟩

end LieModel


open Classical in
def Lat.patch (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) : Lat ξ E := by
  classical
  exact fun q =>
    if ∃ p ∈ S, InFibre ξ p q then ⨅ p ∈ S, ⨅ _ : InFibre ξ p q, Lp p q else L₀ q

theorem Lat.patch_empty (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) : Lat.patch ∅ L₀ Lp = L₀ := by
  funext q; simp [Lat.patch]

theorem Lat.patch_of_not (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) {q : Cpt ξ}
    (hq : ∀ p ∈ S, ¬ InFibre ξ p q) : Lat.patch S L₀ Lp q = L₀ q := by
  simp only [Lat.patch]; rw [if_neg]; rintro ⟨p, hp, h⟩; exact hq p hp h

theorem Lat.patch_of_unique (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) {q : Cpt ξ} {p : ℕ} (hp : p ∈ S)
    (hq : InFibre ξ p q) (hu : ∀ p' ∈ S, InFibre ξ p' q → p' = p) : Lat.patch S L₀ Lp q = Lp p q := by
  simp only [Lat.patch]; rw [if_pos ⟨p, hp, hq⟩]
  refine le_antisymm (iInf₂_le_of_le p hp (iInf_le _ hq)) (le_iInf₂ fun p' hp' => le_iInf fun h => ?_)
  rw [hu p' hp' h]

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ProjectiveLinePlaceTrivialOnConstants
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ProjectiveLinePlaces

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

theorem centre_specializes (z : Spec (CommRingCat.of R) ⟶ X) (φ : R →+* S) :
    centre (Spec.map (CommRingCat.ofHom φ) ≫ z) ⤳ centre z :=
  (IsLocalRing.specializes_closedPoint (R := R) _).map z.continuous

theorem stalk_square {x y : X} (hs : y ⤳ x) {A B : CommRingCat.{0}} (g : X.presheaf.stalk x ⟶ A)
    (g' : X.presheaf.stalk y ⟶ B) (φ : A ⟶ B)
    (h : Spec.map g' ≫ X.fromSpecStalk y = Spec.map φ ≫ Spec.map g ≫ X.fromSpecStalk x) :
    X.presheaf.stalkSpecializes hs ≫ g' = g ≫ φ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk x), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, h]

theorem genMap_specializes {x y : X} (hs : y ⤳ x) (h0 : genPt ξ ⤳ y) (h1 : genPt ξ ⤳ x)
    (s : X.presheaf.stalk x) :
    genMap ξ ⟨y, h0⟩ ((X.presheaf.stalkSpecializes hs).hom s) = genMap ξ ⟨x, h1⟩ s := by
  have h := X.presheaf.stalkSpecializes_comp h0 hs
  have h2 : X.presheaf.stalkSpecializes hs ≫ (X.presheaf.stalkSpecializes h0 ≫ Scheme.stalkClosedPointTo ξ) =
      X.presheaf.stalkSpecializes h1 ≫ Scheme.stalkClosedPointTo ξ :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Scheme.stalkClosedPointTo ξ) h)
  exact congrArg (fun g => g.hom s) h2

theorem valAt_restrict {z : Spec (CommRingCat.of R) ⟶ X} (φ : R →+* S) {y : Spec (CommRingCat.of S) ⟶ X}
    (hy : Spec.map (CommRingCat.ofHom φ) ≫ z = y) (h0 : genPt ξ ⤳ centre y) {a : Ω} {r : R}
    (h : ValAt ξ z a r) : ValAt ξ y a (φ r) := by
  obtain ⟨hz, s, rfl, rfl⟩ := h
  have hs : centre y ⤳ centre z := hy ▸ centre_specializes z φ
  refine ⟨h0, (X.presheaf.stalkSpecializes hs).hom s, genMap_specializes hs h0 hz s, ?_⟩
  have key := stalk_square hs (Scheme.stalkClosedPointTo z) (Scheme.stalkClosedPointTo y)
    (CommRingCat.ofHom φ) ((Scheme.Spec_stalkClosedPointTo_fromSpecStalk y).trans (hy.symm.trans
      (congrArg (Spec.map (CommRingCat.ofHom φ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z)).symm))
  exact congrArg (fun g => g.hom s) key

theorem valAt_of_unit {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω}
    (ha : unitAt ξ ⟨centre z, h⟩ a) : ∃ r : Rˣ, ValAt ξ z a r := by
  obtain ⟨s, hs, rfl⟩ := (CptModel.unitAt_iff ξ _ a).1 ha
  obtain ⟨r, hr⟩ := hs.map (Scheme.stalkClosedPointTo z).hom
  exact ⟨r, h, s, rfl, hr.symm⟩

theorem unitAt_div {L : Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : L.IsGenAt p s) (ht : L.IsGenAt p t) :
    unitAt ξ p (s / t) := by
  have key : ∀ s t : Ω, L.IsGenAt p s → L.IsGenAt p t → s / t ∈ regAt ξ p := by
    intro s t hs ht
    have : s ∈ Submodule.span (regAt ξ p) {t} := ht.2 ▸ hs.2 ▸ Submodule.mem_span_singleton_self s
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 this
    rw [show c • t = (c : Ω) * t from rfl, mul_div_cancel_right₀ _ ht.1]
    exact c.2
  exact ⟨div_ne_zero hs.1 ht.1, key s t hs ht, by rw [inv_div]; exact key t s ht hs⟩

end General

section Line

open IsDedekindDomain Polynomial Crv.Inhab
open scoped Classical

variable (k : Type) [Field k]

end Line

section Proj

open MvPolynomial HomogeneousLocalization ProjCoord

attribute [local instance] MvPolynomial.gradedAlgebra

variable {o κ Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem valAt_pow {Y : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ Y} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ Y} {a : Ω} {r : R} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  exact ⟨hz, t ^ n, map_pow _ _ _, map_pow _ _ _⟩

end Proj

end GlobalTheory.CompanionTheory.Ar.Flat.ProjectiveLinePlaces
end
end

