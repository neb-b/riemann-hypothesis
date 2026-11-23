module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def InChart (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ : Type} (x : κ → Ω) (c : κ) (p : Cpt ξ) : Prop :=
  x c ≠ 0 ∧ ∀ c', x c' / x c ∈ regAt ξ p

structure CoordTie (o : Type) [CommRing o] [Algebra o Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ : Type}
    (x : κ → Ω) : Prop where
  gen : IsCptGen ξ
  cover : ∀ p : Cpt ξ, ∃ c, InChart ξ x c p
  affine : ∀ c, x c ≠ 0 → ∃ U : X.Opens, IsAffineOpen U ∧
    ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩
  ring : ∀ c, x c ≠ 0 → ∀ a : Ω, a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔
    ∀ p : Cpt ξ, InChart ξ x c p → a ∈ regAt ξ p

variable {R : Type} [CommRing R] [IsLocalRing R]

def centre (z : Spec (CommRingCat.of R) ⟶ X) : X := z (IsLocalRing.closedPoint R)

def ValAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of R) ⟶ X) (a : Ω) (r : R) : Prop :=
  ∃ (h : genPt ξ ⤳ centre z) (s : X.presheaf.stalk (centre z)),
    genMap ξ ⟨centre z, h⟩ s = a ∧ (Scheme.stalkClosedPointTo z).hom s = r

def CoordsAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω)
    (z : Spec (CommRingCat.of R) ⟶ X) (w : (Σ k, ι k) → R) : Prop :=
  (∀ k, ∃ c, IsUnit (w ⟨k, c⟩)) ∧ ∀ k c, IsUnit (w ⟨k, c⟩) → y ⟨k, c⟩ ≠ 0 ∧
    ∀ i, ∃ r : R, ValAt ξ z (y ⟨k, i⟩ / y ⟨k, c⟩) r ∧ w ⟨k, i⟩ = r * w ⟨k, c⟩

def InFibre (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : ℕ) (q : Cpt ξ) : Prop := ¬ unitAt ξ q (p : Ω)

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.DefiniteFormStabilizerFiniteAwayFromP
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.Ar.Rec

section Tuple

open ReciprocityTheory.ChartRestriction.G.T0 (TVar OmS sImg)

variable (K : Type) [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  {Ω : Type} [Field Ω] [Algebra K Ω]

abbrev Gens (V : Type) : Type := Σ n : ℕ, Fin (n + 1) → V

def IsGen (W : Submodule (𝓞 K) V) (ev : V → Ω) (g : Gens V) : Prop :=
  Submodule.span (𝓞 K) (Set.range g.2) = W ∧ ev (g.2 0) ≠ 0

def xs (ev : V → Ω) (g : Gens V) (k : Fin g.1) : Ω := ev (g.2 k.succ) / ev (g.2 0)



end Tuple

end GlobalTheory.CompanionTheory.Ar.Rec
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

def QFGroup.HasValues (Γ : QFGroup R T) (s : Γ(Γ.G.left, ⊤)) (f : T → R) : Prop :=
  ∀ t, valAt (Γ.pt t).left ⊤ le_top s = algebraMap R (FractionRing R) (f t)

def QFGroup.IsHT (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
    (i : Γ.G.left ⟶ G.left) {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (N : ℕ)
    (χ : T →* Rˣ) (w : Module.Dual R L) : Prop :=
  ∃ s : Γ(Γ.G.left, ⊤), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) ∧ ∀ e : L,
    ∃ v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left,
      v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
        (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧
      v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left ∧
      valAt v ⊤ le_top s = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e))

end GlobalTheory.CompanionTheory.Ar.BT
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InjectiveOfIsCptGen
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CptModel

open AlgebraicGeometry CategoryTheory

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def self (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Cpt ξ := ⟨genPt ξ, specializes_refl _⟩

theorem genMap_self (ξ : Spec (CommRingCat.of Ω) ⟶ X) :
    genMap ξ (self ξ) = (Scheme.stalkClosedPointTo ξ).hom := by
  have h : X.presheaf.stalkSpecializes (self ξ).2 = 𝟙 _ := X.presheaf.stalkSpecializes_refl _
  unfold genMap
  rw [h]
  rfl

theorem unitAt_iff (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω) :
    unitAt ξ p a ↔ ∃ s : X.presheaf.stalk p.1, IsUnit s ∧ genMap ξ p s = a := by
  constructor
  · rintro ⟨h0, ⟨s, hs⟩, ⟨t, ht⟩⟩
    refine ⟨s, ?_, hs⟩
    have h1 : genMap ξ p (1 - s * t) = 0 := by
      rw [map_sub, map_mul, map_one, hs, ht, mul_inv_cancel₀ h0, sub_self]
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (s * t) with h | h
    · exact isUnit_of_mul_isUnit_left h
    · exact absurd (h1 ▸ h.map (genMap ξ p)) not_isUnit_zero
  · rintro ⟨s, ⟨u, rfl⟩, rfl⟩
    refine ⟨(u.isUnit.map (genMap ξ p)).ne_zero, ⟨_, rfl⟩, ⟨(u⁻¹ : _ˣ), ?_⟩⟩
    exact (map_units_inv (genMap ξ p) u)

theorem regAt_self {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) : regAt ξ (self ξ) = ⊤ := by
  rw [regAt, RingHom.range_eq_top, genMap_self]
  exact h.bij.2

end General

section Affine

variable {R K : Type} [CommRing R] [Field K]

abbrev pt (φ : R →+* K) : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom φ)

def tS (p : Spec (CommRingCat.of R)) : R →+* (Spec (CommRingCat.of R)).presheaf.stalk p :=
  (StructureSheaf.toStalk R p).hom

theorem genMap_toStalk (φ : R →+* K) (p : Cpt (pt φ)) (r : R) :
    genMap (pt φ) p (tS p.1 r) = φ r := by
  have h1 := Scheme.germ_stalkClosedPointTo_Spec (R := CommRingCat.of R) (S := CommRingCat.of K)
    (CommRingCat.ofHom φ)
  have h2 := (Spec (CommRingCat.of R)).presheaf.germ_stalkSpecializes (U := ⊤) (y := p.1) trivial p.2
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.germ ⊤ p.1 trivial ≫
      ((Spec (CommRingCat.of R)).presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo (pt φ)) =
      CommRingCat.ofHom φ := by
    have h4 : (Spec (CommRingCat.of R)).presheaf.germ ⊤ p.1 trivial ≫
      ((Spec (CommRingCat.of R)).presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo (pt φ)) =
        (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Scheme.stalkClosedPointTo (pt φ)) h2).trans h1)
    exact (congrArg ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ ·) h4).trans (Iso.inv_hom_id_assoc _ _)
  exact congrArg (fun f => f.hom r) h3

theorem exists_frac (φ : R →+* K) (p : Cpt (pt φ)) (x : (Spec (CommRingCat.of R)).presheaf.stalk p.1) :
    ∃ a s : R, s ∉ p.1.asIdeal ∧
      x * tS p.1 s = tS p.1 a := by
  have key : ∀ (q : PrimeSpectrum R) (y : (Spec.structureSheaf R).presheaf.stalk q), ∃ a s : R, s ∉ q.asIdeal ∧
      y * algebraMap R _ s = algebraMap R _ a := fun q y => by
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj q.asIdeal.primeCompl y
    exact ⟨a, s, s.2, h⟩
  exact key p.1 x

theorem isUnit_toStalk (p : PrimeSpectrum R) {s : R} (hs : s ∉ p.asIdeal) :
    IsUnit (tS p s) :=
  IsLocalization.map_units (M := p.asIdeal.primeCompl)
    ((Spec.structureSheaf R).presheaf.stalk p) ⟨s, hs⟩

theorem mem_regAt_iff (φ : R →+* K) (p : Cpt (pt φ)) (c : K) :
    c ∈ regAt (pt φ) p ↔ ∃ a s : R, s ∉ p.1.asIdeal ∧ φ s ≠ 0 ∧ c * φ s = φ a := by
  have hne : ∀ s : R, s ∉ p.1.asIdeal → φ s ≠ 0 := fun s hs => by
    rw [← genMap_toStalk φ p]
    exact ((isUnit_toStalk p.1 hs).map (genMap (pt φ) p)).ne_zero
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, s, hs, h⟩ := exists_frac φ p x
    refine ⟨a, s, hs, hne s hs, ?_⟩
    rw [← genMap_toStalk φ p, ← genMap_toStalk φ p]
    exact (map_mul (genMap (pt φ) p) _ _).symm.trans (congrArg (genMap (pt φ) p) h)
  · rintro ⟨a, s, hs, h0, h⟩
    obtain ⟨v, hv⟩ := (isUnit_toStalk p.1 hs).exists_right_inv
    refine ⟨tS p.1 a * v, ?_⟩
    have e : φ s * genMap (pt φ) p v = 1 := by
      rw [← genMap_toStalk φ p]
      exact (map_mul (genMap (pt φ) p) _ _).symm.trans
        ((congrArg (genMap (pt φ) p) hv).trans (map_one _))
    refine (map_mul (genMap (pt φ) p) _ _).trans ?_
    rw [genMap_toStalk, ← h, mul_assoc, e, mul_one]

theorem genPt_asIdeal (φ : R →+* K) : (genPt (pt φ)).asIdeal = RingHom.ker φ := by
  change Ideal.comap φ (IsLocalRing.maximalIdeal K) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

theorem genMap_injective (φ : R →+* K) (hφ : Function.Injective φ) (p : Cpt (pt φ)) :
    Function.Injective (genMap (pt φ) p) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, s, hs, h⟩ := exists_frac φ p x
  have h1 := (map_mul (genMap (pt φ) p) _ _).symm.trans (congrArg (genMap (pt φ) p) h)
  rw [hx, zero_mul, genMap_toStalk] at h1
  have ha : a = 0 := hφ (by rw [← h1, map_zero])
  rw [ha, map_zero] at h
  exact (isUnit_toStalk p.1 hs).mul_left_eq_zero.mp h

theorem isCptGen_fractionRing [IsDomain R] [Algebra R K] [IsFractionRing R K] :
    IsCptGen (pt (algebraMap R K)) := by
  have hi := IsFractionRing.injective R K
  refine ⟨?_, genMap_injective _ hi⟩
  rw [← genMap_self]
  refine ⟨genMap_injective _ hi _, fun c => ?_⟩
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) c
  have h0 : algebraMap R K s ≠ 0 := (map_ne_zero_iff _ hi).2 (nonZeroDivisors.ne_zero hs)
  refine (mem_regAt_iff _ (self _) _).2 ⟨a, s, ?_, h0, div_mul_cancel₀ _ h0⟩
  change s ∉ (genPt (pt (algebraMap R K))).asIdeal
  rw [genPt_asIdeal]
  exact h0

end Affine

section Int

theorem isCptGen_int : IsCptGen (pt (algebraMap ℤ ℚ)) := isCptGen_fractionRing

def two : Cpt (pt (algebraMap ℤ ℚ)) :=
  ⟨(⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).2 Int.prime_two⟩ : PrimeSpectrum ℤ),
    (PrimeSpectrum.le_iff_specializes _ _).1 (by
      change (genPt (pt (algebraMap ℤ ℚ))).asIdeal ≤ _
      rw [genPt_asIdeal, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective ℤ ℚ)]
      exact bot_le)⟩

theorem half_notMem : (2 : ℚ)⁻¹ ∉ regAt _ two := by
  rw [mem_regAt_iff]
  rintro ⟨a, s, hs, -, h⟩
  apply hs
  change s ∈ Ideal.span {(2 : ℤ)}
  rw [Ideal.mem_span_singleton]
  refine ⟨a, ?_⟩
  simp only [algebraMap_int_eq, eq_intCast] at h
  have : (s : ℚ) = 2 * a := by rw [← h]; ring
  exact_mod_cast this

theorem not_unitAt_two : ¬ unitAt _ two (2 : ℚ) := fun h => half_notMem h.2.2

theorem unitAt_three : unitAt _ two (3 : ℚ) := by
  have h : ∀ n : ℤ, ¬ (2 : ℤ) ∣ n → n ∉ two.1.asIdeal := fun n hn hm =>
    hn (Ideal.mem_span_singleton.1 hm)
  refine ⟨by norm_num, (mem_regAt_iff _ _ _).2 ⟨3, 1, h 1 (by decide), by simp, by simp⟩,
    (mem_regAt_iff _ _ _).2 ⟨1, 3, h 3 (by decide), by simp, by simp⟩⟩

end Int

end GlobalTheory.CompanionTheory.Ar.CptModel
end
end

