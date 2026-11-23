module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0487
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0486
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import ReciprocityTheory.GaloisValuations.GlobalB

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionSectionEqPushedTraitPointLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorSecLocal

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem pow_comp_of_isMonHom {S : Scheme.{0}} {G G' Z : Over S} [MonObj G] [MonObj G'] (φ : G ⟶ G')
    [IsMonHom φ] (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem toric_torsion_section_overLocal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (k : ℕ)
    (s : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t.G)),
    (∀ (A : Type) [CommRing A] (a : R →+* A) τ h, s A a τ h ^ k = 1) →
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (a' : R →+* A') (f : A →+* A') τ h τ' h',
      a' = f.comp a → (∀ χ, (τ' χ : A') = f (τ χ : A)) → (s A' a' τ' h').left = spMap f ≫ (s A a τ h).left) →
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (a' : R →+* A')
      (f : A →+* A') (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t (spMap a)) τ h
      (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P.D.toPre.X),
      a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
      (s A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ) →
    ∀ (X' : Type) [AddCommGroup X'] (ρ : P.D.toPre.X →+ X')
      (V : Type) [CommRing V] [IsLocalRing V] (ψ : R →+* V) (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
      (j : splitTorus (Sp V) X' ⟶ tV.G) [IsMonHom j]
      (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
      (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ))),
      m₀'.φ = m₀.φ ≫ mV.φ →
      GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    ∀ (U : Type) [CommRing U] [IsLocalRing U] (u : V →+* U), IsLocalHom u → IsUnit (k : U) →
    ∀ (τU : Multiplicative X' →* Uˣ) (τ : Multiplicative P.D.toPre.X →* Uˣ) (h : τ ^ k = 1),
      τU ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τU (Multiplicative.ofAdd (ρ χ))) →
    ∀ (z : Over.mk (spMap u) ⟶ splitTorus (Sp V) X'),
      (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τU (Multiplicative.ofAdd χ))) →
      (s U (u.comp ψ) τ h).left = (z ≫ j).left ≫ mV.φ := by
  intro E _ _ _ H R _ _ _ t P k s hs1 hs2 hs3 X' _ ρ V _ _ ψ tV mV j _ t₀ m₀ h₀ m₀' hφ hpull
    U _ _ u hu hk τU τ h hτU hττ z hz
  have hg : spMap (u.comp ψ) = (Over.mk (spMap u)).hom ≫ spMap ψ := spMap_comp_ringHom ψ u
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv mV.cart (Over.mk (spMap u)) (spMap (u.comp ψ)) hg

  have hzk : z ^ k = 1 := by
    apply (GlobalTheory.splitTorusPointsEquiv (Sp V) X' (Over.mk (spMap u))).injective
    rw [map_pow, map_one]
    refine MonoidHom.ext fun m => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    have e1 := hz (Multiplicative.toAdd m)
    simp only [GlobalTheory.UU.chV, ofAdd_toAdd] at e1
    rw [e1]
    have e2 : τU m ^ k = 1 := by rw [← MonoidHom.pow_apply, hτU, MonoidHom.one_apply]
    simp only [unitOn, ← map_pow, e2, map_one]
  have hx : s U (u.comp ψ) τ h = e (z ≫ j) := by
    refine _root_.GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) t.G t.semi.smooth U (spMap (u.comp ψ)) k hk _ _ ?_
      (ResidueField U) (residue U) inferInstance ?_
    · rw [hs1, ← map_pow, ← pow_comp_of_isMonHom, hzk, MonObj.one_comp, map_one]
    · let cU := residue U
      let τ₀ : Multiplicative P.D.toPre.X →* (ResidueField U)ˣ :=
        (Units.map (cU : U →* ResidueField U)).comp τ
      have h' : τ₀ ^ k = 1 := by
        refine MonoidHom.ext fun m => ?_
        rw [MonoidHom.pow_apply, MonoidHom.one_apply]
        show Units.map _ (τ m) ^ k = 1
        rw [← map_pow, ← MonoidHom.pow_apply, h, MonoidHom.one_apply, map_one]
      have n1 := hs2 U (ResidueField U) (u.comp ψ) (cU.comp (u.comp ψ)) cU τ h τ₀ h' rfl (fun χ => rfl)
      let w₁ : Multiplicative X' →* Γ(Sp (ResidueField U), ⊤)ˣ :=
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField U))).inv.hom.toMonoidHom).comp
          ((Units.map (cU : U →* ResidueField U)).comp τU)
      let z₁ : Over.mk (spMap (ResidueField.map u)) ⟶ splitTorus (Sp (ResidueField V)) X' :=
        (GlobalTheory.splitTorusPointsEquiv _ X' _).symm w₁
      have hz₁ : ∀ χ, GlobalTheory.UU.chV z₁ χ = w₁ (Multiplicative.ofAdd χ) := fun χ => by
        simp only [GlobalTheory.UU.chV, z₁, MulEquiv.apply_symm_apply]
      let z₀ := z₁ ≫ GlobalTheory.SplitTorus.torusMap _ ρ
      have hz₀ : ∀ χ, GlobalTheory.UU.chV z₀ χ = unitOn (τ₀ (Multiplicative.ofAdd χ)) := fun χ => by
        apply Units.ext
        rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.SplitTorus.val_eq,
          GlobalTheory.SplitTorus.val_comp_torusMap, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val,
          ← GlobalTheory.UU.chV_val, hz₁]
        show _ = (unitOn ((Units.map (cU : U →* ResidueField U)) (τ (Multiplicative.ofAdd χ)))).val
        rw [hττ]; rfl
      have hres : cU.comp u = (ResidueField.map u).comp (residue V) := by
        ext r; simp [cU, ResidueField.map_residue]
      have hcomp : cU.comp (u.comp ψ) = (ResidueField.map u).comp ((residue V).comp ψ) := by
        rw [← RingHom.comp_assoc, hres, RingHom.comp_assoc]
      have n2 := hs3 (ResidueField V) (ResidueField U) ((residue V).comp ψ) h₀ (cU.comp (u.comp ψ))
        (ResidueField.map u) t₀ m₀' τ₀ h' z₀ hcomp hz₀
      have hzz : z₁.left ≫ GlobalTheory.SplitTorus.bcMap (spMap (residue V)) X' = spMap cU ≫ z.left := by
        refine GlobalTheory.UU.splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
        · rw [Category.assoc, GlobalTheory.SplitTorus.bcMap_hom, ← Category.assoc, Over.w z₁, Category.assoc,
            Over.w z]
          show spMap (ResidueField.map u) ≫ spMap (residue V) = spMap cU ≫ spMap u
          rw [← spMap_comp_ringHom, ← spMap_comp_ringHom, hres]
        · rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, GlobalTheory.UU.bcMap_charUnit,
            Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ← GlobalTheory.UU.chV_val,
            ← GlobalTheory.UU.chV_val, hz₁, hz]
          show (Scheme.ΓSpecIso _).inv.hom (cU (τU _).val) =
            (Spec.map (CommRingCat.ofHom cU)).appTop.hom ((Scheme.ΓSpecIso _).inv.hom (τU _).val)
          rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
      rw [he, ← n1, n2, hφ]
      have hz₀t : z₀ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' = z₁ ≫ GlobalTheory.TorusPart.pullTorus m₀.cart j := by
        rw [hpull, Category.assoc]
      rw [hz₀t, Over.comp_left, Category.assoc, ← Category.assoc (GlobalTheory.TorusPart.pullTorus m₀.cart j).left,
        GlobalTheory.TorusPart.pullTorus_left]
      have k3 := congrArg (· ≫ j.left ≫ mV.φ) hzz
      simp only [Category.assoc, Over.comp_left] at k3 ⊢
      exact k3
  rw [hx, he]

end GlobalTheory.TorSecLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

def EigFrame.Coord {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') (g : EigFrame Z φ' x')
    (A : Mat Dw.mult R') : Prop :=
  x' = spMap ψ ≫ x ∧ φ' = ψ.comp φ ∧
    ∀ τ i, IsCombAtG Z.t x' (fun k => spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ k) (A τ i) (g.v τ i)

def EigFrame.Stable {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) : Prop :=
  ∀ (R' : Type) [CommRing R'] [IsLocalRing R'] (ψ : R →+* R'),
    ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ i

theorem EigFrame.tri_iff {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') (g : EigFrame Z φ' x')
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ) :
    f.Tri ψ g t ↔ ∃ A : Mat Dw.mult R', f.Coord ψ g A ∧ (∀ τ i, A τ i i = t τ i) ∧ ∀ τ i k, i < k → A τ i k = 0 := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    choose A hA hA' hA'' using h3
    exact ⟨A, ⟨h1, h2, hA''⟩, hA, hA'⟩
  · rintro ⟨A, ⟨h1, h2, h3⟩, hA, hA'⟩
    exact ⟨h1, h2, fun τ i => ⟨A τ i, hA τ i, hA' τ i, h3 τ i⟩⟩

variable {F : Type} [Field F]

def Tied (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) (π : Y.X ⟶ gen Z)
    (f₀ : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)) {k : (E →+* ℂ) → ℕ} (S : Fr (ratOf Y) Dw.mult k)
    (A₀ : Mat Dw.mult Y.Fn) : Prop :=
  A₀ ∈ S.S (genericPoint Y.X) ∧ ∀ y : Y.X, ∀ A ∈ S.S y, ∃ (φ : c.F →+* Y.X.presheaf.stalk y)
    (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z)),
    f.Coord (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f₀ (A₀ * A⁻¹)

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationLtOneOfInvNotMem
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open Pointwise

namespace GlobalTheory.WittFracPlace

theorem valuation_intCast_lt_one_iff {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {p : ℕ} (hp : p.Prime)
    (h : A.valuation (p : Ω) < 1) (n : ℤ) : A.valuation (n : Ω) < 1 ↔ (p : ℤ) ∣ n := by
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m => (A.valuation_le_one_iff _).2 (intCast_mem A m)
  have hmul : ∀ (m : ℤ) (x : Ω), A.valuation x < 1 → A.valuation (m * x) < 1 := fun m x hx => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle m)) hx
  constructor
  · intro hn
    by_contra hd
    obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd).2 hd
    have e : (a : Ω) * p + b * n = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
    have := Valuation.map_add_lt _ (hmul a _ h) (hmul b _ hn)
    rw [e, map_one] at this
    exact lt_irrefl _ this
  · rintro ⟨m, rfl⟩
    rw [Int.cast_mul, mul_comm, Int.cast_natCast]
    exact hmul m _ h

theorem exists_smul_eq {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {p : ℕ} (hp : p.Prime)
    (A A' : ValuationSubring Ω) (h : A.valuation (p : Ω) < 1) (h' : A'.valuation (p : Ω) < 1) :
    ∃ g : Ω ≃ₐ[ℚ] Ω, g • A = A' := by
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨(Ideal.span {(p : ℤ)}).comap Rat.ringOfIntegersEquiv.toRingHom, Ideal.comap_isPrime _ _, fun hb => by
      have h1 : (p : 𝓞 ℚ) ∈ (Ideal.span {(p : ℤ)}).comap Rat.ringOfIntegersEquiv.toRingHom := by
        rw [Ideal.mem_comap, map_natCast]; exact Ideal.subset_span rfl
      rw [hb, Ideal.mem_bot] at h1
      exact hp.ne_zero (by exact_mod_cast h1)⟩
  have key : ∀ B : ValuationSubring Ω, B.valuation (p : Ω) < 1 →
      ∀ x : 𝓞 ℚ, B.valuation (algebraMap ℚ Ω (x : ℚ)) < 1 ↔ x ∈ v.asIdeal := by
    intro B hB x
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
    have e : Rat.ringOfIntegersEquiv.symm n = (n : 𝓞 ℚ) := eq_intCast Rat.ringOfIntegersEquiv.symm.toRingHom n
    have e2 : algebraMap ℚ Ω ((n : 𝓞 ℚ) : ℚ) = (n : Ω) :=
      map_intCast ((algebraMap ℚ Ω).comp (algebraMap (𝓞 ℚ) ℚ)) n
    rw [e, e2, valuation_intCast_lt_one_iff B hp hB]
    change _ ↔ (n : 𝓞 ℚ) ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_intCast, Int.cast_id, Ideal.mem_span_singleton]
  exact ReciprocityTheory.Gal.exists_smul_eq_of_over (key A h) (key A' h')

theorem valuation_lt_one_of_inv_notMem {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {x : Ω} (h : x⁻¹ ∉ A) :
    A.valuation x < 1 := by
  rw [← A.valuation_le_one_iff, map_inv₀, not_le] at h
  have h0 : A.valuation x ≠ 0 := fun e => by simp [e] at h
  exact (one_lt_inv₀ (zero_lt_iff.2 h0)).1 h

theorem exists_emb_inducing (L : Type) [Field L] [NumberField L] {p : ℕ} (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 L)) (hv : (p : 𝓞 L) ∈ v.asIdeal) (V : ValuationSubring ℂ) (hV : (p : ℂ)⁻¹ ∉ V) :
    ∃ e : L →+* ℂ, ∀ x, e x ∈ V ↔ v.valuation L x ≤ 1 := by
  let Ω := AlgebraicClosure L
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ L Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  let ι : Ω →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  obtain ⟨A', hA'⟩ := GlobalTheory.exists_valuationSubring_comap_eq (v.valuation L).valuationSubring (algebraMap L Ω)
  have hm : ∀ x : L, algebraMap L Ω x ∈ A' ↔ v.valuation L x ≤ 1 := fun x => by
    rw [← ValuationSubring.mem_comap, hA', Valuation.mem_valuationSubring_iff]
  have h1 : (V.comap ι.toRingHom).valuation (p : Ω) < 1 := valuation_lt_one_of_inv_notMem _ (by
    rwa [ValuationSubring.mem_comap, map_inv₀, map_natCast])
  have h2 : A'.valuation (p : Ω) < 1 := valuation_lt_one_of_inv_notMem _ (by
    have h3 : v.valuation L (p : L) < 1 := by
      have := (v.valuation_lt_one_iff_mem (K := L) (p : 𝓞 L)).2 hv
      rw [← map_natCast (algebraMap (𝓞 L) L) p]
      exact this
    have h4 : v.valuation L (p : L) ≠ 0 := by simpa using hp.ne_zero
    rw [← map_natCast (algebraMap L Ω), ← map_inv₀, hm, map_inv₀, not_le]
    exact (one_lt_inv₀ (zero_lt_iff.2 h4)).2 h3)
  obtain ⟨g, hg⟩ := exists_smul_eq hp _ _ h1 h2
  refine ⟨(ι.toRingHom.comp g.symm.toRingEquiv.toRingHom).comp (algebraMap L Ω), fun x => ?_⟩
  rw [← hm, ← hg, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem exists_jcPin : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (la : PlL D p), ∃ jc : DV.KW p →+* ℂ, JcPin D p la jc := by
  intro D p hp la
  obtain ⟨j⟩ := GlobalTheory.WittFracComplex.nonempty_ringHom_complex p
  obtain ⟨V, -, -, -, hV⟩ :=
    GlobalTheory.exists_valuationSubring_dominating (V := WittVector p (AlgebraicClosure (ZMod p))) j
  have hp' : (p : ℂ)⁻¹ ∉ V := by
    rw [← map_natCast j, ← map_inv₀, hV]
    rintro ⟨a, ha⟩
    have hinj := IsFractionRing.injective (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)
    have h0 : (p : DV.KW p) ≠ 0 := fun e => hp.out.ne_zero (by
      have := congrArg j e
      rw [map_natCast, map_zero] at this
      exact_mod_cast this)
    refine (WittVector.irreducible p (k := AlgebraicClosure (ZMod p))).not_isUnit
      (isUnit_iff_exists_inv.2 ⟨a, hinj ?_⟩)
    rw [map_mul, ha, map_natCast, map_one, mul_inv_cancel₀ h0]
  obtain ⟨e, he⟩ := exists_emb_inducing D.what₂.LL hp.out la.1 la.2 V hp'
  have : Countable D.what₂.LL := Cardinal.mk_le_aleph0_iff.1
    ((Algebra.IsAlgebraic.cardinalMk_le_max ℚ D.what₂.LL).trans (by simp))
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq D.what₂.LL e D.what₂.embLL
  refine ⟨τ.toRingHom.comp j, V.comap τ.symm.toRingHom, fun x => ?_, fun a => ?_⟩
  · rw [← he, ← hτ, ValuationSubring.mem_comap]
    simp
  · rw [← hV, ValuationSubring.mem_comap]
    simp

end GlobalTheory.WittFracPlace
end

