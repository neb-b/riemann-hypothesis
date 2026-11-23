module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

def Lat (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] : Type :=
  (p : Cpt ξ) → Submodule (regAt ξ p) E

namespace Lat

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def IsFrameAt (L : Lat ξ E) {r : ℕ} (b : Fin r → E) (p : Cpt ξ) : Prop :=
  LinearIndependent Ω b ∧ L p = Submodule.span (regAt ξ p) (Set.range b)

def IsVBOn (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω E) : Prop :=
  ∀ p ∈ T, ∃ U : X.Opens, p.1 ∈ U ∧ ∃ b : Fin r → E, Submodule.span Ω (Set.range b) = V ∧
    ∀ q ∈ T, q.1 ∈ U → L.IsFrameAt b q

def IsVB (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E) : Prop := L.IsVBOn Set.univ r V

def inter (L : Lat ξ E) (V : Submodule Ω E) : Lat ξ E := fun p => L p ⊓ V.restrictScalars (regAt ξ p)

def map (L : Lat ξ E) (f : E →ₗ[Ω] E') : Lat ξ E' := fun p => (L p).map (f.restrictScalars (regAt ξ p))

def comap (L : Lat ξ E') (f : E →ₗ[Ω] E') : Lat ξ E := fun p => (L p).comap (f.restrictScalars (regAt ξ p))

def scale (L : Lat ξ E) (a : Ω) : Lat ξ E := L.map (a • LinearMap.id)

def dual (L : Lat ξ E) : Lat ξ (Module.Dual Ω E) := fun p =>
  { carrier := {w | ∀ e ∈ L p, w e ∈ regAt ξ p}
    add_mem' := fun ha hb e he => by simpa using add_mem (ha e he) (hb e he)
    zero_mem' := fun e _ => by simp
    smul_mem' := fun c w hw e he => by
      show (c : Ω) * w e ∈ regAt ξ p
      exact mul_mem c.2 (hw e he) }

def wedge (L : Lat ξ E) (r : ℕ) : Lat ξ (⋀[Ω]^r E) := fun p =>
  Submodule.span (regAt ξ p) {w | ∃ b : Fin r → E, (∀ i, b i ∈ L p) ∧ w = exteriorPower.ιMulti Ω r b}

def IsChartOf (L : Lat ξ E) {κ : Type} (x : κ → Ω) (lat : κ → AddSubgroup E) : Prop :=
  ∀ c, x c ≠ 0 → ∀ e, e ∈ lat c ↔ ∀ p : Cpt ξ, InChart ξ x c p → e ∈ L p

def IsDegOn (L : Lat ξ E) (T : Set (Cpt ξ)) {K : Type} [Fintype K] {ι : K → Type} (y : (Σ k, ι k) → Ω)
    (a : K → ℤ) (e₀ : E) : Prop :=
  e₀ ≠ 0 ∧ ∀ p ∈ T, ∀ c : (k : K) → ι k, InChart ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c p →
    L p = Submodule.span (regAt ξ p) {(∏ k, y ⟨k, c k⟩ ^ a k) • e₀}

end Lat

def Dominates {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X')
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X' ⟶ X) (i : Ω →+* Ω') : Prop :=
  ξ' ≫ f = Spec.map (CommRingCat.ofHom i) ≫ ξ

def Lat.pull {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {F : Type} [AddCommGroup F] [Module Ω' F]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ E) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X)
    (j : E →+ F) : Lat ξ' F := fun p' =>
  Submodule.span (regAt ξ' p') {e' | ∃ (h : genPt ξ ⤳ f p'.1) (e : E), e ∈ L ⟨f p'.1, h⟩ ∧ e' = j e}

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsCoordsAtOfCoordTie
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordModel

open AlgebraicGeometry CategoryTheory

variable (A : Type) [CommRing A] (Ω : Type) [Field Ω] [Algebra A Ω]


variable [IsDomain A] [IsFractionRing A Ω]



section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsLocalRing R]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X}

theorem valAt_unique (hξ : IsCptGen ξ) {a : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨hz, s, rfl, rfl⟩ := h
  obtain ⟨_, s', e, rfl⟩ := h'
  rw [hξ.inj ⟨centre z, hz⟩ e]

theorem valAt_mul {a b : Ω} {r s : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  obtain ⟨_, t', rfl, rfl⟩ := h'
  exact ⟨hz, t * t', map_mul _ _ _, map_mul _ _ _⟩

theorem valAt_inv {a : Ω} {r : Rˣ} (h : ValAt ξ z a r) : a ≠ 0 ∧ ValAt ξ z a⁻¹ ↑r⁻¹ := by
  obtain ⟨hz, t, rfl, e⟩ := h
  have ht : IsUnit t := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit t (by have := r.isUnit; rw [← e] at this; exact this)
  obtain ⟨u, rfl⟩ := ht
  refine ⟨(u.isUnit.map (genMap ξ ⟨centre z, hz⟩)).ne_zero, hz, ↑u⁻¹, map_units_inv _ u, ?_⟩
  refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
  rw [← e]
  exact (map_mul _ _ _).symm.trans ((congrArg _ u.mul_inv).trans (map_one _))

theorem exists_coordsAt {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω) (hz : genPt ξ ⤳ centre z)
    (h : ∀ k, ∃ c, InChart ξ (fun i => y ⟨k, i⟩) c ⟨centre z, hz⟩) (hξ : IsCptGen ξ) :
    ∃ w, CoordsAt ξ y z w := by
  choose c hc using h
  have hv : ∀ j : Σ k, ι k, ∃ r, ValAt ξ z (y j / y ⟨j.1, c j.1⟩) r := by
    rintro ⟨k, i⟩
    obtain ⟨s, hs⟩ := (hc k).2 i
    exact ⟨_, hz, s, hs, rfl⟩
  choose w hw using hv
  refine ⟨w, fun k => ⟨c k, ?_⟩, fun k d hd => ?_⟩
  · have h1 : ValAt ξ z 1 1 := ⟨hz, 1, map_one _, map_one _⟩
    have h2 := hw ⟨k, c k⟩
    rw [div_self (hc k).1] at h2
    rw [valAt_unique hξ h2 h1]; exact isUnit_one
  · obtain ⟨u, hu⟩ := hd
    have h1 := hw ⟨k, d⟩
    rw [← hu] at h1
    obtain ⟨h0, h2⟩ := valAt_inv h1
    have hd0 : y ⟨k, d⟩ ≠ 0 := fun e => h0 (by simp [e])
    refine ⟨hd0, fun i => ⟨w ⟨k, i⟩ * ↑u⁻¹, ?_, by rw [← hu]; simp⟩⟩
    have h3 := valAt_mul (hw ⟨k, i⟩) h2
    have hc0 : y ⟨k, c k⟩ ≠ 0 := (hc k).1
    convert h3 using 1
    field_simp

end General

end GlobalTheory.CompanionTheory.Ar.CoordModel
end
end

