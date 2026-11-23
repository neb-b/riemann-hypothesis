module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaPowFixesOfCommutative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1427

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExponentInertiaTateModuleFiniteResidue
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InertiaTate

theorem iterate_map_mul' {M : Type} [CommGroup M] (φ : M →* M) (j : ℕ) (a b : M) :
    (⇑φ)^[j] (a * b) = (⇑φ)^[j] a * (⇑φ)^[j] b := by
  induction j generalizing a b with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, map_mul, ih]

theorem pow_fix_of_fix {M : Type} [CommGroup M] (φ : M →* M) (l : ℕ)
    (h : ∀ x : M, x ^ l = 1 → φ x = x) :
    ∀ (k : ℕ) (x : M), x ^ l ^ (k + 1) = 1 → (⇑φ)^[l ^ k] x = x := by
  intro k
  induction k with
  | zero =>
    intro x hx
    rw [pow_zero, Function.iterate_one]
    exact h x (by simpa using hx)
  | succ k ih =>
    intro x hx
    let ψ : M →* M := MonoidHom.mk' ((⇑φ)^[l ^ k]) (iterate_map_mul' φ _)
    have hψ : ∀ y, ψ y = (⇑φ)^[l ^ k] y := fun _ => rfl
    have ih' : ∀ y : M, y ^ l ^ (k + 1) = 1 → ψ y = y := fun y hy => by rw [hψ]; exact ih y hy
    have hxl : ψ (x ^ l) = x ^ l := ih' _ (by rw [← pow_mul, ← pow_succ', hx])
    obtain ⟨d, hd⟩ : ∃ d : M, d = ψ x * x⁻¹ := ⟨_, rfl⟩
    have hψx : ψ x = x * d := by rw [hd, mul_comm (ψ x), mul_inv_cancel_left]
    have hdl : d ^ l = 1 := by
      rw [hd, mul_pow, inv_pow, ← map_pow, hxl, mul_inv_cancel]
    have hdψ : ψ d = d := ih' d (by rw [pow_succ', pow_mul, hdl, one_pow])
    have hit : ∀ j : ℕ, (⇑ψ)^[j] x = x * d ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ihj =>
        rw [Function.iterate_succ_apply', ihj, map_mul, map_pow, hdψ, hψx, _root_.mul_assoc, ← pow_succ']
    have e : (⇑φ)^[l ^ (k + 1)] x = (⇑ψ)^[l] x := by
      rw [pow_succ, Function.iterate_mul]
      rfl
    rw [e, hit, hdl, _root_.mul_one]

theorem mem_of_pow_mem_of_coprime {G : Type} [Group G] (H : Subgroup G) (g : G) {m n : ℕ}
    (hmn : Nat.Coprime m n) (hm : g ^ m ∈ H) (hn : g ^ n ∈ H) : g ∈ H := by
  have e : ((Nat.gcd m n : ℕ) : ℤ) = m * Nat.gcdA m n + n * Nat.gcdB m n := Nat.gcd_eq_gcd_ab m n
  rw [hmn.gcd_eq_one, Nat.cast_one] at e
  have : g = (g ^ m) ^ Nat.gcdA m n * (g ^ n) ^ Nat.gcdB m n := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← e, zpow_one]
  rw [this]
  exact H.mul_mem (H.zpow_mem hm _) (H.zpow_mem hn _)

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]

def stab (x : ptOver K Ω ⟶ A) : Subgroup (Ω ≃ₐ[K] Ω) where
  carrier := {σ | specAut σ ≫ x = x}
  one_mem' := by
    change specAut 1 ≫ x = x
    rw [specAut_one, Category.id_comp]
  mul_mem' := by
    intro a b ha hb
    change specAut (a * b) ≫ x = x
    change specAut a ≫ x = x at ha
    change specAut b ≫ x = x at hb
    rw [specAut_mul, Category.assoc, hb, ha]
  inv_mem' := by
    intro a ha
    change specAut a ≫ x = x at ha
    change specAut a⁻¹ ≫ x = x
    conv_lhs => rw [← ha]
    rw [← Category.assoc, ← specAut_mul, inv_mul_cancel, specAut_one, Category.id_comp]

theorem mem_stab_iff (x : ptOver K Ω ⟶ A) (σ : Ω ≃ₐ[K] Ω) : σ ∈ stab A x ↔ galPts A σ x = x := Iff.rfl

theorem galPts_pow (σ : Ω ≃ₐ[K] Ω) (j : ℕ) (x : ptOver K Ω ⟶ A) :
    galPts A (σ ^ j) x = (⇑(galPts A σ))^[j] x := by
  induction j generalizing x with
  | zero =>
    change specAut (σ ^ 0) ≫ x = x
    rw [pow_zero, specAut_one, Category.id_comp]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ← ih]
    change specAut (σ ^ (j + 1)) ≫ x = specAut σ ≫ (specAut (σ ^ j) ≫ x)
    rw [pow_succ', specAut_mul, Category.assoc]

theorem exists_field_of_point [Algebra.IsAlgebraic K Ω] [LocallyOfFiniteType A.hom] (x : ptOver K Ω ⟶ A) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧ ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ stab A x ↔ σ ∈ E.fixingSubgroup := by
  obtain ⟨E, hE1, -, hE3⟩ := GlobalTheory.SS.exists_fieldOfValues A.left Ω x.left
  obtain ⟨L, hL, hLE⟩ := hE3 K A.hom inferInstance (Over.w x) inferInstance
  refine ⟨L, hL, fun σ => ?_⟩
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by
    rw [← Spec.map_id]
    congr 1
  rw [IntermediateField.mem_fixingSubgroup_iff]
  have h1 : σ ∈ stab A x ↔ spMap (σ : Ω →+* Ω) ≫ x.left = spMap (RingHom.id Ω) ≫ x.left := by
    rw [hid, Category.id_comp]
    constructor
    · intro h
      exact congrArg CommaMorphism.left h
    · intro h
      exact Over.OverMorphism.ext h
  rw [h1, hE1]
  constructor
  · intro h c hc
    exact h c (by rw [← hLE]; exact hc)
  · intro h c hc
    exact h c (by rw [← hLE] at hc; exact hc)

end GlobalTheory.InertiaTate

namespace GlobalTheory.InertiaTate

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]

theorem exists_galois_field_of_finite [IsGalois K Ω] [LocallyOfFiniteType A.hom] (S : Set (ptOver K Ω ⟶ A))
    (hS : S.Finite) (hst : ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ S, galPts A σ x ∈ S) :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ IsGalois K L ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ L.fixingSubgroup ↔ ∀ x ∈ S, σ ∈ stab A x := by
  choose E hE hEs using fun x : S => exists_field_of_point A x.1
  haveI : Finite S := hS.to_subtype
  haveI := hE
  have key : ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ (⨆ x : S, E x).fixingSubgroup ↔ ∀ x ∈ S, σ ∈ stab A x := by
    intro σ
    rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, iSup_le_iff]
    constructor
    · intro h x hx
      exact (hEs ⟨x, hx⟩ σ).2 (Subgroup.zpowers_le.1 ((IntermediateField.le_iff_le _ _).1 (h ⟨x, hx⟩)))
    · intro h x
      exact (IntermediateField.le_iff_le _ _).2 (Subgroup.zpowers_le.2 ((hEs x σ).1 (h x.1 x.2)))
  refine ⟨⨆ x : S, E x, inferInstance, ?_, key⟩
  refine (InfiniteGalois.normal_iff_isGalois _).1 ⟨fun n hn g => ?_⟩
  rw [key] at hn ⊢
  intro x hx
  have h1 := hn _ (hst g⁻¹ x hx)
  change specAut n ≫ (specAut g⁻¹ ≫ x) = specAut g⁻¹ ≫ x at h1
  change specAut (g * n * g⁻¹) ≫ x = x
  rw [specAut_mul, specAut_mul, Category.assoc, Category.assoc, h1, ← Category.assoc, ← specAut_mul,
    mul_inv_cancel, specAut_one, Category.id_comp]

theorem aut_comm_of_galTate_comm (l : ℕ) [Fact l.Prime]
    (hc : ∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ)
    (L : IntermediateField K Ω) [Normal K L] [Normal K Ω] (n : ℕ)
    (hL : ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ L.fixingSubgroup ↔
      ∀ x ∈ Set.range (fun t : Tate l (ptOver K Ω ⟶ A) => t.lev n), σ ∈ stab A x) :
    ∀ α β : L ≃ₐ[K] L, α * β = β * α := by
  intro α β
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) Ω α
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) Ω β
  rw [← map_mul, ← map_mul, MonoidHom.eq_iff, IntermediateField.restrictNormalHom_ker, hL]
  rintro _ ⟨t, rfl⟩
  have h1 : galTate A l ((τ * σ)⁻¹ * (σ * τ)) = 1 := by
    rw [map_mul, map_mul (galTate A l) σ τ, hc σ τ, ← map_mul (galTate A l) τ σ, ← map_mul, inv_mul_cancel,
      map_one]
  exact (congrArg (fun f => Tate.lev (f t) n) h1 :)

end GlobalTheory.InertiaTate


open GlobalTheory.InertiaTate in
theorem GlobalTheory.InertiaTate.exists_exponent_inertia_galTate : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → (∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ) → ∃ E : ℕ, 0 < E ∧ ∀ σ ∈ inertia K V, galTate A l σ ^ E = 1 := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA l _ hl hc
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  haveI : LocallyOfFiniteType A.hom := by
    haveI := hA.smooth
    infer_instance
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim K A hA
  have hlK : (l : K) ≠ 0 := by
    intro h0
    apply hl
    have : (l : R) = 0 := IsFractionRing.injective R K (by rw [map_natCast, h0, map_zero])
    rw [← map_natCast (residue R), this, map_zero]
  have hfin : ∀ n : ℕ, {x : ptOver K Ω ⟶ A | x ^ (l ^ n) = 1}.Finite := by
    intro n
    have h := _root_.GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K Ω A hA g hg (l ^ n) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hlK)
    have : Finite {x : ptOver K Ω ⟶ A // x ^ (l ^ n) = 1} :=
      Nat.finite_of_card_ne_zero (by
        rw [h]; exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))
    exact Set.finite_coe_iff.mp this
  have hSfin : ∀ n, (Set.range (fun t : Tate l (ptOver K Ω ⟶ A) => t.lev n)).Finite := fun n =>
    (hfin n).subset (by rintro _ ⟨t, rfl⟩; exact t.lev_pow n)
  have hSst : ∀ n, ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ Set.range (fun t : Tate l (ptOver K Ω ⟶ A) => t.lev n),
      galPts A σ x ∈ Set.range (fun t : Tate l (ptOver K Ω ⟶ A) => t.lev n) := by
    rintro n σ _ ⟨t, rfl⟩
    exact ⟨galTate A l σ t, rfl⟩
  have h1st : ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ {x : ptOver K Ω ⟶ A | x ^ l = 1},
      galPts A σ x ∈ {x : ptOver K Ω ⟶ A | x ^ l = 1} := by
    intro σ x hx
    change galPts A σ x ^ l = 1
    rw [← map_pow, show x ^ l = 1 from hx, map_one]
  obtain ⟨L₁, hL₁f, hL₁g, hL₁⟩ := exists_galois_field_of_finite A {x : ptOver K Ω ⟶ A | x ^ l = 1}
    (by simpa using hfin 1) h1st
  have hq : 1 < Nat.card (ResidueField R) := Finite.one_lt_card
  have hN : 0 < Nat.card (L₁ ≃ₐ[K] L₁) := Nat.card_pos
  refine ⟨(Nat.card (ResidueField R) - 1) * Nat.card (L₁ ≃ₐ[K] L₁), Nat.mul_pos (by omega) hN, ?_⟩
  intro σ hσ
  obtain ⟨g0, hg0⟩ : ∃ g0, g0 = (σ ^ (Nat.card (ResidueField R) - 1)) ^ Nat.card (L₁ ≃ₐ[K] L₁) := ⟨_, rfl⟩
  rw [← map_pow, pow_mul, ← hg0]
  refine LinearMap.ext fun t => Tate.ext fun n => ?_
  change galPts A g0 (t.lev n) = t.lev n
  rw [← mem_stab_iff]
  have hp : (ringChar (ResidueField R)).Prime := CharP.char_is_prime (ResidueField R) _
  have hpl : ringChar (ResidueField R) ≠ l := by
    intro h
    apply hl
    rw [← h, ringChar.Nat.cast_ringChar]
  have hA1 : ∀ y : ptOver K Ω ⟶ A, y ^ l = 1 → galPts A g0 y = y := by
    intro y hy
    have : g0 ∈ L₁.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, hg0, map_pow, pow_card_eq_one']
    exact (hL₁ g0).1 this y hy
  have hlp : g0 ^ (l ^ n) ∈ stab A (t.lev n) := by
    rw [mem_stab_iff, galPts_pow]
    exact pow_fix_of_fix (galPts A g0) l hA1 n _ (by rw [pow_succ, pow_mul, t.lev_pow, one_pow])
  obtain ⟨Ln, hLnf, hLng, hLn⟩ := exists_galois_field_of_finite A _ (hSfin n) (hSst n)
  have hcomm := aut_comm_of_galTate_comm A l hc Ln n hLn
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.TameInertia.inertia_pow_fixes_of_commutative R K Ω V hV Ln hLnf hLng hcomm σ hσ
  have hpp : g0 ^ (ringChar (ResidueField R) ^ a) ∈ stab A (t.lev n) := by
    have h2 : σ ^ ((Nat.card (ResidueField R) - 1) * ringChar (ResidueField R) ^ a) ∈ Ln.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 ha
    have h3 := (hLn _).1 h2 _ ⟨t, rfl⟩
    have e : g0 ^ (ringChar (ResidueField R) ^ a) =
        (σ ^ ((Nat.card (ResidueField R) - 1) * ringChar (ResidueField R) ^ a)) ^ Nat.card (L₁ ≃ₐ[K] L₁) := by
      rw [hg0, ← pow_mul, ← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [e]
    exact Subgroup.pow_mem _ h3 _
  exact mem_of_pow_mem_of_coprime _ g0 (Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Fact.out).2 hpl)) hpp hlp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupSchemeUnitStalkData
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

noncomputable section

namespace GlobalTheory.Nef

theorem exists_stalk_fac {X : Scheme.{0}} (x : X) {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ X)
    (h : f (IsLocalRing.closedPoint R) = x) :
    ∃ φ : X.presheaf.stalk x ⟶ R, Spec.map φ ≫ X.fromSpecStalk x = f := by
  subst h
  exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

theorem exists_stalk_map {X Y : Scheme.{0}} (x : X) (g : X ⟶ Y) (y : Y) (hy : g x = y) :
    ∃ φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x, Spec.map φ ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ g := by
  subst hy
  exact exists_stalk_fac (g x) (X.fromSpecStalk x ≫ g) (congrArg (fun z => g z) Scheme.fromSpecStalk_closedPoint)

theorem stalk_hom_eq {X : Scheme.{0}} (x : X) {R : CommRingCat.{0}} (φ ψ : X.presheaf.stalk x ⟶ R)
    (h : Spec.map φ ≫ X.fromSpecStalk x = Spec.map ψ ≫ X.fromSpecStalk x) : φ = ψ :=
  Spec.map_injective ((cancel_mono (X.fromSpecStalk x)).1 h)

section

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

theorem unitSec_sqr : unitSec G ≫ sqr G = unitSec G := by
  have h1 : (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h2 : η[G] ≫ (𝟙 G * 𝟙 G) = η[G] := by
    rw [Hom.mul_def, ← Category.assoc, comp_lift, Category.comp_id, ← Hom.mul_def, ← h1, _root_.one_mul]
  change η[G].left ≫ (𝟙 G * 𝟙 G : G ⟶ G).left = η[G].left
  rw [← Over.comp_left, h2]

theorem sqr_hom : sqr G ≫ G.hom = G.hom := Over.w _

end

theorem stalkData_exists : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ s : S, ∃ π ε m,
    StalkData G s π ε m ∧ ε.comp π = RingHom.id _ ∧ m.comp π = π ∧ ε.comp m = ε := by
  intro S G _ s
  obtain ⟨π, hπ⟩ := exists_stalk_map (unitSec G s) G.hom s (by
    rw [← Scheme.Hom.comp_apply, sec_hom]; rfl)
  obtain ⟨ε, hε⟩ := exists_stalk_map s (unitSec G) (unitSec G s) rfl
  obtain ⟨m, hm⟩ := exists_stalk_map (unitSec G s) (sqr G) (unitSec G s) (by
    rw [← Scheme.Hom.comp_apply, unitSec_sqr])
  refine ⟨π.hom, ε.hom, m.hom, ⟨hπ, hε, hm⟩, ?_, ?_, ?_⟩
  · have : π ≫ ε = 𝟙 _ := stalk_hom_eq s _ _ (by
      rw [Spec.map_comp, Category.assoc, hπ, ← Category.assoc, hε, Category.assoc, sec_hom,
        Category.comp_id, Spec.map_id, Category.id_comp])
    exact congrArg CommRingCat.Hom.hom this
  · have : π ≫ m = π := stalk_hom_eq s _ _ (by
      rw [Spec.map_comp, Category.assoc, hπ, ← Category.assoc, hm, Category.assoc, sqr_hom])
    exact congrArg CommRingCat.Hom.hom this
  · have : m ≫ ε = ε := stalk_hom_eq (unitSec G s) _ _ (by
      rw [Spec.map_comp, Category.assoc, hm, ← Category.assoc, hε, Category.assoc, unitSec_sqr])
    exact congrArg CommRingCat.Hom.hom this

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicChartsGenericPointProjective
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.GenericCharts

theorem exists_etale_coords (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp F) (D : ℕ) (hp : IsProjOver p) (hd : topologicalKrullDim X = (D : ℕ)) :
    ∃ (U : X.Opens) (x : Fin D → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧
      (MvPolynomial.eval₂Hom (algX p U) x).Etale := by
  obtain ⟨N, i, hi, hcomp⟩ := hp
  haveI : IsProper (PSpace.str F N) := isProper_str F N
  haveI : LocallyOfFiniteType p := by rw [← hcomp]; infer_instance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint X)) isOpen_univ
  have hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  let ψ := Spec.preimage (hU.fromSpec ≫ p)
  have hψ : Spec.map ψ = hU.fromSpec ≫ p := Spec.map_preimage _
  letI : Algebra F Γ(X, U) := ψ.hom.toAlgebra
  haveI hft : Algebra.FiniteType F Γ(X, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ)).mp (hψ ▸ inferInstance)
  have hA : Algebra.trdeg F Γ(X, U) = D :=
    GlobalTheory.GenFinite.trdeg_affineOpen_eq F p hU ⟨_, hxU⟩ D hd
  haveI : FaithfulSMul F Γ(X, U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F Γ(X, U)).injective
  obtain ⟨f, hf, hs⟩ := GlobalTheory.GenericEtale.exists_away F Γ(X, U) hA
  let B := Localization.Away f
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsOpenImmersion (spMap (algebraMap Γ(X, U) B)) := IsOpenImmersion.of_isLocalization f
  let i' : Sp Γ(X, U) ⟶ X := hU.fromSpec
  haveI : IsOpenImmersion i' := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hi' : i' ≫ p = spMap (algebraMap F Γ(X, U)) := hψ.symm
  let j : Sp B ⟶ X := spMap (algebraMap Γ(X, U) B) ≫ i'
  have hj : j ≫ p = spMap (algebraMap F B) := by
    rw [Category.assoc, hi', IsScalarTower.algebraMap_eq F Γ(X, U) B, ← Spec.map_comp]
    rfl
  have h₁ : SmoothOfRelativeDimension D (j ≫ p) := by
    rw [hj]
    refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension D)).mpr ?_
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap D).mpr hs)
  have h₂ : SmoothOfRelativeDimension D (j.opensRange.ι ≫ p) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc]
    have : SmoothOfRelativeDimension (0 + D) (j.isoOpensRange.inv ≫ j ≫ p) := inferInstance
    rwa [zero_add] at this
  refine ModelCharts.exists_etale_coords_of_opens p D j.opensRange ?_
  exact ⟨genericPoint _, genericPoint_eq_of_isOpenImmersion j⟩

theorem exists_generic_charts : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∃ U : X.Opens, genericPoint X ∈ U ∧ ∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source := by
  intro F _ X _ _ p σ D hp hd
  haveI : CharZero F := σ.charZero
  obtain ⟨U, x, hU, hη, hx⟩ := exists_etale_coords F X p D hp hd
  exact ⟨U, hη, fun y hy => (AlgChart.exists_of_etale hU x hx hy).imp fun c h => h.1⟩

end GlobalTheory.GenericCharts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowSectionVanishingDegreePos
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem exists_sec_lbPow_vanishing_of_degree_pos : ∀ (k : Type) [Field k] (C : Scheme.{0})
    [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ L : LB C, L.IsLB →
      0 < interNum k (GlobalTheory.structureModule C) ![L] →
      ∃ (m : ℕ) (σ : (lbPow L m).Sec) (c : C), 0 < m ∧ σ ≠ 0 ∧ c ∉ Out.nonzeroLocus σ := by
  intro k _ C _ hC L hL hpos
  have := LieSemineg.isIntegral_curve hC.1 hC.2.2
  have hd : topologicalKrullDim C = 1 := LieSemineg.dim_curve hC.1
  obtain ⟨hprop, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB (strHom k C)).1 hC.2.1
  have := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  set O := GlobalTheory.structureModule C with hO
  set d := interNum k O ![L] with hdd
  set f := chiPic k O with hf

  have hdeg : ∀ (M : LB C) (hM : M.IsLB), interNum k O ![M] = f 0 - f (-cls M hM) := by
    intro M hM
    rw [interNum_one k O hM, chi_twistZ k O hM, hf, chiPic_zero, neg_one_zsmul]

  have hchi : ∀ m : ℕ, f ((m : ℤ) • cls L hL) = f 0 + m * d := by
    intro m
    obtain ⟨N, hN, hc⟩ := cls_surj (-((m : ℤ) • cls L hL))
    have hLm := isLB_lbPow hL m
    have e : cls _ (LB.isLB_triv C) = cls N hN + cls _ hLm := by
      rw [hc, cls_lbPow hL m hLm, cls_triv, natCast_zsmul, neg_add_cancel]
    have hadd := interNum_one_of_cls_eq_add (k := k) hH hd (LB.isLB_triv C) hN hLm e
    rw [ArInt.interNum_one_lbPow_of_curve hH hd hL m, hdeg _ (LB.isLB_triv C), hdeg N hN, hc,
      cls_triv, neg_zero, neg_neg] at hadd
    have hd' : interNum k (GlobalTheory.structureModule C) ![L] = d := rfl
    linarith
  set m : ℕ := (f 0).natAbs + 1 with hm
  have hm0 : 0 < m := Nat.succ_pos _
  have hLm := isLB_lbPow hL m
  have hqc := Twist.isQuasicoherent_twist (F := O) hLm
  have hvan : ∀ n, 2 ≤ n → Subsingleton (coh (twist O (lbPow L m)) n) := by
    intro n hn
    refine hH.subsingleton_coh_of_dim_lt _ ?_
    rw [hd]
    exact_mod_cast (show (1 : ℕ) < n by omega)
  have hχ : chi k (twist O (lbPow L m)) = f 0 + m * d := by
    rw [← chiPic_cls k O hLm, cls_lbPow hL m hLm, ← natCast_zsmul, ← hf, hchi m]
  have hχpos : 0 < chi k (twist O (lbPow L m)) := by
    rw [hχ]
    have h1 : (1 : ℤ) ≤ d := hpos
    have h2 : -(f 0) ≤ ((f 0).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]; exact neg_le_abs (f 0)
    have h3 : (m : ℤ) = (f 0).natAbs + 1 := by rw [hm]; push_cast; ring
    nlinarith
  have hh0 : 0 < hdim k (twist O (lbPow L m)) 0 := by
    have := chi_eq_hdim_zero_sub_hdim_one k hvan
    omega
  have hnt : Nontrivial (coh (twist O (lbPow L m)) 0) := Module.nontrivial_of_finrank_pos hh0
  obtain ⟨σ, hσ⟩ := hasNonzeroSec_iff_nontrivial.2 hnt
  refine ⟨m, σ, ?_⟩
  by_contra! hall
  have htop : Out.nonzeroLocus σ = ⊤ := top_unique fun c _ ↦ (hall c hm0 hσ)
  have h0 : cls _ hLm = 0 := (cls_eq_zero_iff hLm).2 (exists_isGen_of_nonzeroLocus_eq_top σ htop)
  have hz := interNum_eq_zero_of_cls_eq_zero k O (isLB_vecOne hLm) 0 h0
  rw [ArInt.interNum_one_lbPow_of_curve hH hd hL m] at hz
  have : (0 : ℤ) < m * d := mul_pos (by exact_mod_cast hm0) hpos
  have hd' : interNum k (GlobalTheory.structureModule C) ![L] = d := rfl
  rw [hd'] at hz
  omega

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSmConnOfIsProperStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianScheme_of_smConn_of_isProper' : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], GlobalTheory.SS.SmConn G → IsProper G.hom → IsAbelianScheme G := by
  first | exact @GlobalTheory.SmConnProper.isAbelianScheme_of_smConn_of_isProper | exact GlobalTheory.SmConnProper.isAbelianScheme_of_smConn_of_isProper | (intros; apply GlobalTheory.SmConnProper.isAbelianScheme_of_smConn_of_isProper <;> assumption)
end

