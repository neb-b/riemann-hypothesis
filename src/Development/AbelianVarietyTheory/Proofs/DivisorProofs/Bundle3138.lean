module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2961
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionKilledByIdealCharZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1982
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2780
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3109
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjCorrespondenceTargetFiniteEtal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3131

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsTypeTjPIsogeny
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.TjExists

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}} {N : ℕ}

theorem charZero_of_base (b : Base D R) (hp : IsUnit ((p : ℕ) : R)) {k : Type} [Field k] (s : Sp k ⟶ Sp R) :
    CharZero k := by
  let β : R →+* k := (Spec.preimage s).hom
  haveI := ringChar.charP k
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hl | hl
  · exfalso
    have h0 : ((ringChar k : ℕ) : k) = 0 := CharP.cast_eq_zero k _
    have hu : IsUnit ((ringChar k : ℕ) : R) := by
      by_cases h : ringChar k = p
      · rw [h]; exact hp
      · exact b.unit _ ((Nat.coprime_primes hl Fact.out).2 h)
    have := hu.map β
    rw [map_natCast, h0] at this
    exact not_isUnit_zero this
  · haveI : CharP k 0 := hl ▸ ringChar.charP k
    exact CharP.charP_to_charZero k

attribute [local instance] ptModuleWvs

def torsSub {s : S ⟶ Sp R} (o : Obj b N s) (T : Over S) (c : ℕ) : Submodule (𝓞 D.F) (Additive (T ⟶ o.A)) where
  carrier := {g | g.toMul ^ c = 1}
  zero_mem' := one_pow c
  add_mem' {g h} hg hh := by
    show (g.toMul * h.toMul) ^ c = 1
    rw [mul_pow, show g.toMul ^ c = 1 from hg, show h.toMul ^ c = 1 from hh, _root_.mul_one]
  smul_mem' a g hg := by
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
    show (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ^ c = 1
    rw [← MonObj.pow_comp, show g.toMul ^ c = 1 from hg, MonObj.one_comp]

theorem comp_act_natCast {s : S ⟶ Sp R} (o : Obj b N s) {T : Over S} (q : T ⟶ o.A) (n : ℕ) :
    q ≫ o.act.act (n : D.O) = q ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero_eq_one_wvs, pow_zero, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, o.act.add, o.act.one, MonObj.comp_mul, ih, Category.comp_id, pow_succ]

theorem exists_sub (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (hw : w.IsMaximal) (hu : uIdeal D r ≤ w) (hj : j ≤ D.n)
    (hc : ∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) (hm : D.m = 1) {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {s : Sp k ⟶ Sp R} (o : Obj b N s) :
    ∃ H : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.A), (∀ c' : D.O, ∀ h ∈ H, h ≫ o.act.act c' ∈ H) ∧ (∀ h ∈ H, h ^ c = 1) ∧
      (∀ h₁ ∈ H, ∀ h₂ ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
        (lift h₁ 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 h₂) 1) ∧
      (∀ g : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1
        (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 h) 1) → g ∈ H) ∧
      (∀ h ∈ H, (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) h) → KilledBy o w h) ∧
      Nat.card {h : 𝟙_ (Over (Sp k)) ⟶ o.A // h ∈ H ∧ KilledBy o w h} = Ideal.absNorm w ^ j := by
  obtain ⟨ex, hce, hje⟩ := hc
  have hpk : ((p : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hck : (c : k) ≠ 0 := by rw [hce, Nat.cast_pow]; exact pow_ne_zero _ hpk
  obtain ⟨e, he, hl, hr, hadj, hskew, hnd⟩ : ∃ e : (𝟙_ (Over (Sp k)) ⟶ o.A) → (𝟙_ (Over (Sp k)) ⟶ o.A) → kˣ,
      (∀ g g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g' ^ c = 1 → ∀ u : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ,
        Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 g') u ↔
          u = unitOn (e g g')) ∧
      (∀ g₁ g₂ g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g₁ ^ c = 1 → g₂ ^ c = 1 → g' ^ c = 1 →
        e (g₁ * g₂) g' = e g₁ g' * e g₂ g') ∧
      (∀ g g₁ g₂ : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g₁ ^ c = 1 → g₂ ^ c = 1 →
        e g (g₁ * g₂) = e g g₁ * e g g₂) ∧
      (∀ (a : D.O) (g g' : 𝟙_ (Over (Sp k)) ⟶ o.A), g ^ c = 1 → g' ^ c = 1 →
        e (g ≫ o.act.act a) g' = e g (g' ≫ o.act.act (D.star a).unop)) ∧
      (∀ g g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g' ^ c = 1 → e g g' * e g' g = 1) ∧
      (∀ g : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → (∀ g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g' ^ c = 1 → e g g' = 1) → g = 1) :=
    PQuot.exists_pairing o c ⟨ex, hce⟩ k hpk (𝟙 _)
  have hinj : Function.Injective (unitOn (R := k)) := by
    refine Units.map_injective (f := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) ?_
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.injective
  have hone : unitOn (1 : kˣ) = 1 := map_one (Units.map _)
  have he1 : ∀ g g' : 𝟙_ (Over (Sp k)) ⟶ o.A, g ^ c = 1 → g' ^ c = 1 →
      (Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : 𝟙_ (Over (Sp k)) ⟶ G2 o.A) (lift 1 g') 1 ↔
        e g g' = 1) := fun g g' hg hg' => by
    rw [he g g' hg hg']
    exact ⟨fun h => (hinj (hone.trans h)).symm, fun h => by rw [h]; exact hone.symm⟩
  let M := torsSub o (𝟙_ (Over (Sp k))) c
  haveI : Finite M := (GlobalTheory.T.finite_torsion_and_descent_abelianVariety_algClosed k o.A o.ab c hck).1
  have hM0 : ∀ x : M, x = 0 ↔ x.1.toMul = 1 := fun x => ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  have hkill : ∀ (v : Ideal (𝓞 D.F)) (x : M), (∀ a ∈ v, a • x = 0) ↔ KilledBy o v x.1.toMul :=
    fun v x => forall₂_congr fun a _ => hM0 (a • x)
  have hwne : w ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hw (NumberField.RingOfIntegers.not_isField D.F)
  have hq : 0 < Ideal.absNorm w := Nat.pos_of_ne_zero fun h => hwne (Ideal.absNorm_eq_zero_iff.1 h)
  have hle : Ideal.absNorm w ^ j ≤ Nat.card {x : M // ∀ a ∈ w, a • x = 0} := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [pow_zero]
      haveI : Nonempty {x : M // ∀ a ∈ w, a • x = 0} := ⟨⟨0, fun a _ => smul_zero a⟩⟩
      exact Nat.card_pos
    · have hrk : Nat.card {g : 𝟙_ (Over (Sp k)) ⟶ o.A // KilledBy o w g} = Ideal.absNorm w ^ (D.m * D.n) :=
        _root_.GlobalTheory.UPel.HT.ES.CharZeroCount.card_killedBy_charZero p D R b N (Sp k) s o w hwne k (𝟙 _)
      have htor : ∀ g : 𝟙_ (Over (Sp k)) ⟶ o.A, KilledBy o w g → g ^ c = 1 := fun g hg => by
        have h1 := hg _ (hu (p_mem_uIdeal D r))
        rw [map_natCast, comp_act_natCast] at h1
        obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (hje hj0).ne'
        rw [hce, pow_succ', pow_mul, h1, one_pow]
      let φ : {g : 𝟙_ (Over (Sp k)) ⟶ o.A // KilledBy o w g} ≃ {x : M // ∀ a ∈ w, a • x = 0} :=
        { toFun := fun g => ⟨⟨Additive.ofMul g.1, htor g.1 g.2⟩, (hkill w _).2 g.2⟩
          invFun := fun x => ⟨x.1.1.toMul, (hkill w _).1 x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [← Nat.card_congr φ, hrk, hm, Nat.one_mul]
      exact Nat.pow_le_pow_right hq hj
  obtain ⟨K, Kiso, Kmax, Ku, Kcard⟩ := GlobalTheory.T.perfect_pairing_torsion_module p D r w j c hw hu ⟨ex, hce⟩ M
    (fun x => (hM0 _).2 x.2) k (fun x y => e x.1.toMul y.1.toMul)
    (fun x x' y => hl _ _ _ x.2 x'.2 y.2) (fun x y y' => hr _ _ _ x.2 y.2 y'.2)
    (fun a x y => by
      have := hadj (algebraMap (𝓞 D.F) D.O a) _ _ x.2 y.2
      rw [D.star_F, MulOpposite.unop_op] at this
      exact this)
    (fun x y => hskew _ _ x.2 y.2)
    (fun x h => (hM0 x).2 (hnd _ x.2 fun g' hg' => h ⟨Additive.ofMul g', hg'⟩)) hle
  let H : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.A) :=
    { carrier := {g | ∃ x ∈ K, x.1.toMul = g}
      one_mem' := ⟨0, K.zero_mem, rfl⟩
      mul_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, K.add_mem hx hy, rfl⟩
      inv_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨-x, K.neg_mem hx, rfl⟩ }
  refine ⟨H, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro c' _ ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := GlobalTheory.T.integers_surjective_of_rank_one p D hm c'
    exact ⟨a • x, K.smul_mem a hx, rfl⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (he1 _ _ x.2 y.2).2 (Kiso x hx y hy)
  · intro g hg h
    exact ⟨⟨Additive.ofMul g, hg⟩, Kmax _ fun y hy => (he1 _ _ hg y.2).1 (h _ ⟨y, hy, rfl⟩), rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ ⟨i, hi⟩
    exact (hkill w x).1 (Ku x hx ⟨i, (hkill _ x).2 hi⟩)
  · rw [← Kcard]
    refine (Nat.card_eq_of_bijective (fun x : {x : M // x ∈ K ∧ ∀ a ∈ w, a • x = 0} =>
      (⟨x.1.1.toMul, ⟨x.1, x.2.1, rfl⟩, (hkill w _).1 x.2.2⟩ :
        {h : 𝟙_ (Over (Sp k)) ⟶ o.A // h ∈ H ∧ KilledBy o w h})) ⟨fun x y h => ?_, ?_⟩).symm
    · exact Subtype.ext (Subtype.ext (Subtype.mk.inj h))
    · rintro ⟨_, ⟨x, hx, rfl⟩, hk⟩
      exact ⟨⟨x, hx, (hkill w x).2 hk⟩, rfl⟩

theorem exists_isPIsog_isTj : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Sp k ⟶ Sp R) (o : Obj b N s), ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ IsTj r w j o o' ψ := by
  intro p _ D R _ _ b N _ _ hp r w j c hw hu hj hc hm k _ _ s o
  haveI := charZero_of_base b hp s
  obtain ⟨H, stab, hpow, hiso, hmax, hU, hcard⟩ := exists_sub r w j c hw hu hj hc hm o
  obtain ⟨ex, hce, -⟩ := hc
  have hck : (c : k) ≠ 0 := by
    rw [hce, Nat.cast_pow]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hfin : Finite H := by
    haveI := (GlobalTheory.T.finite_torsion_and_descent_abelianVariety_algClosed k o.A o.ab c hck).1
    exact Finite.of_injective (fun h : H => (⟨h.1, hpow h.1 h.2⟩ : {g : 𝟙_ (Over (Sp k)) ⟶ o.A // g ^ c = 1}))
      fun a a' h => Subtype.ext (Subtype.mk.inj h)
  have hinj : ∀ (κ : Type) [Field κ] (x : Sp κ ⟶ Sp k) (h h' : 𝟙_ (Over (Sp k)) ⟶ o.A),
      toUnit (Over.mk x) ≫ h = toUnit (Over.mk x) ≫ h' → h = h' := fun κ _ x h h' e => by
    haveI : Nonempty (Over.mk x).left := inferInstanceAs (Nonempty (PrimeSpectrum κ))
    haveI := GlobalTheory.PointQuot.epi_toUnit (Over.mk x)
    exact (cancel_epi _).1 e
  have hfree : ∀ (κ : Type) [Field κ] (x : Sp κ ⟶ Sp k) (h : 𝟙_ (Over (Sp k)) ⟶ o.A),
      toUnit (Over.mk x) ≫ h = 1 ↔ h = 1 := fun κ _ x h =>
    ⟨fun e => hinj κ x h 1 (by rw [e, MonObj.comp_one]), fun e => by rw [e, MonObj.comp_one]⟩
  obtain ⟨o', ψ, hψ, hker⟩ := PQuot.exists_quot o c ⟨ex, hce⟩ hp H hfin (fun κ _ _ x h _ e => (hfree κ x h).1 e)
    stab hpow hiso (fun κ _ _ x g hg ho => PQuot.max_geom o c hck H hpow hmax κ x g hg ho)
  refine ⟨o', ψ, hψ, fun κ _ _ _ x => ?_⟩
  have hkb : ∀ (v : Ideal (𝓞 D.F)) (h : 𝟙_ (Over (Sp k)) ⟶ o.A),
      KilledBy o v (toUnit (Over.mk x) ≫ h) ↔ KilledBy o v h := fun v h =>
    forall₂_congr fun a _ => by rw [Category.assoc, hfree]
  refine ⟨fun g hg ⟨i, hi⟩ => ?_, ?_⟩
  · obtain ⟨h, hh, rfl⟩ := (hker κ x g).1 hg
    exact (hkb w h).2 (hU h hh ⟨i, (hkb _ h).1 hi⟩)
  · rw [hm, Nat.one_mul, ← hcard]
    refine (Nat.card_eq_of_bijective (fun h : {h : 𝟙_ (Over (Sp k)) ⟶ o.A // h ∈ H ∧ KilledBy o w h} =>
      (⟨toUnit (Over.mk x) ≫ h.1, (hker κ x _).2 ⟨h.1, h.2.1, rfl⟩, (hkb w _).2 h.2.2⟩ :
        {g : Over.mk x ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g})) ⟨fun a a' h => ?_, ?_⟩).symm
    · exact Subtype.ext (hinj κ x _ _ (congrArg Subtype.val h))
    · rintro ⟨g, hg, hk⟩
      obtain ⟨h, hh, rfl⟩ := (hker κ x g).1 hg
      exact ⟨⟨h, hh, (hkb w h).1 hk⟩, rfl⟩

end GlobalTheory.UPel.HT.ES.TjExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesCompleteNoetherianLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SFamCompl

theorem glue : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (X : Scheme.{0}) (x : ∀ e : ℕ, Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) ⟶ X), (∀ e, Out.thickTrans R (IsLocalRing.maximalIdeal R) e ≫ x (e + 1) = x e) → ∃ f : Sp R ⟶ X, ∀ e, Out.thick R (IsLocalRing.maximalIdeal R) e ≫ f = x e :=
  _root_.GlobalTheory.LocalThickGlue.exists_glue

theorem ext_affine : ∀ (R : Type) [CommRing R] (I : Ideal R), IsHausdorff I R → ∀ (A : Type) [CommRing A]
    (f f' : Sp R ⟶ Sp A), (∀ e, Out.thick R I e ≫ f = Out.thick R I e ≫ f') → f = f' := by
  intro R _ I hI A _ f f' h
  rw [← Spec.map_preimage f, ← Spec.map_preimage f']
  congr 1
  ext a
  refine (IsHausdorff.eq_iff_smodEq (I := I)).2 fun k => ?_
  cases k with
  | zero =>
    rw [SModEq, Submodule.Quotient.eq, pow_zero, Ideal.one_eq_top, smul_eq_mul, Ideal.mul_top]
    trivial
  | succ e =>
    have he := h e
    rw [← Spec.map_preimage f, ← Spec.map_preimage f', Out.thick, ← Spec.map_comp, ← Spec.map_comp] at he
    have he' := congrArg (fun q => q.hom a) (Spec.map_injective he)
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at he'
    rw [SModEq, Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top]
    exact Ideal.Quotient.eq.1 he'

theorem srel_comp {h k : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
    {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
    {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} {c'' : SiegPre h k ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left}
    (m : SRelBy c' c 1 1 f φ) (m' : SRelBy c'' c' 1 1 f' ψ) : SRelBy c'' c 1 1 (f' ≫ f) (ψ ≫ φ) := by
  obtain ⟨hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨hψ, ⟨ψ₂, hs', hw'⟩, hl'⟩ := m'
  simp only [pow_one] at hl hl' ⊢
  refine ⟨hψ.comp hφ, ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (GlobalTheory.SiegelPullComp.iso_pull ψ₂ hw)).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _)
      (GlobalTheory.SiegelPullComp.iso_pull_pull c.isLB φ₂ ψ₂)
  · rw [pow_one, pow_one]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem tower : ∀ (g n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (R : Type) [CommRing R] (I : Ideal R) (s s' : Sp R ⟶ Sp B) (c : SiegPre g n (b.ζ : B) s) (c' : SiegPre g n (b.ζ : B) s') (t : ∀ e : ℕ, Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : ∀ e, SiegPre g n (b.ζ : B) (t e)) (φ : ∀ e, (ce e).A.left ⟶ c.A.left) (ψ : ∀ e, (ce e).A.left ⟶ c'.A.left), 3 ≤ n → Odd n → c.Principal → c'.Principal → (∀ e, SRelBy (ce e) c 1 1 (Out.thick R I e) (φ e)) → (∀ e, SRelBy (ce e) c' 1 1 (Out.thick R I e) (ψ e)) → ∃ β : ∀ e, (ce e).A.left ⟶ (ce (e + 1)).A.left, ∀ e, β e ≫ φ (e + 1) = φ e ∧ β e ≫ ψ (e + 1) = ψ e := by
  intro g n B _ b R _ I s s' c c' t ce φ ψ hn hodd hc hc' hφ hψ
  have key : ∀ e, ∃ β : (ce e).A.left ⟶ (ce (e + 1)).A.left, β ≫ φ (e + 1) = φ e ∧ β ≫ ψ (e + 1) = ψ e := by
    intro e
    have h1 : SiegPB (ce e) (ce (e + 1)) (Out.thickTrans R I e) :=
      GlobalTheory.SiegelPullComp.pb_cancel ((sRel_one_one_iff _ _ _).1 ⟨_, hφ (e + 1)⟩)
        (by rw [Out.thickTrans_comp]; exact (sRel_one_one_iff _ _ _).1 ⟨_, hφ e⟩)
    obtain ⟨β, hβ⟩ := (sRel_one_one_iff _ _ _).2 h1
    refine ⟨β, ?_, ?_⟩
    · have := srel_comp (hφ (e + 1)) hβ
      rw [Out.thickTrans_comp] at this
      exact GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 B B b (b.ζ : B) _ _ s (t e) c (ce e) _ _ _ hn hodd hc this (hφ e)
    · have := srel_comp (hψ (e + 1)) hβ
      rw [Out.thickTrans_comp] at this
      exact GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 B B b (b.ζ : B) _ _ s' (t e) c' (ce e) _ _ _ hn hodd hc' this (hψ e)
  choose β hβ using key
  exact ⟨β, hβ⟩

theorem assemble : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (s s' : Sp R ⟶ Sp B) (c : SiegPre g n ζ s) (c' : SiegPre g n ζ s') (t : ∀ e : ℕ, Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : ∀ e, SiegPre g n ζ (t e)) (φ : ∀ e, (ce e).A.left ⟶ c.A.left) (ψ : ∀ e, (ce e).A.left ⟶ c'.A.left) (β : ∀ e, (ce e).A.left ⟶ (ce (e + 1)).A.left), c.Principal → (∀ e, SRelBy (ce e) c 1 1 (Out.thick R I e) (φ e)) → (∀ e, SRelBy (ce e) c' 1 1 (Out.thick R I e) (ψ e)) → (∀ e, β e ≫ φ (e + 1) = φ e) → (∀ e, β e ≫ ψ (e + 1) = ψ e) → SiegPB c c' (𝟙 _) :=
  _root_.GlobalTheory.SiegFormalAssemble.siegPB_id_of_tower

theorem alg : ∀ (g n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (R : Type) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R), IsAdicComplete I R → 3 ≤ n → Odd n → ∀ (s s' : Sp R ⟶ Sp B) (c : SiegPre g n (b.ζ : B) s)
    (c' : SiegPre g n (b.ζ : B) s'), c.Principal → c'.Principal →
    (∀ e, ∃ (t : Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : SiegPre g n (b.ζ : B) t),
      SiegPB ce c (Out.thick R I e) ∧ SiegPB ce c' (Out.thick R I e)) → SiegPB c c' (𝟙 _) := by
  intro g n B _ b R _ _ I hI hn hodd s s' c c' hc hc' h
  choose t ce hce hce' using h
  choose φ hφ using fun e => (sRel_one_one_iff (ce e) c _).2 (hce e)
  choose ψ hψ using fun e => (sRel_one_one_iff (ce e) c' _).2 (hce' e)
  obtain ⟨β, hβ⟩ := tower g n B b R I s s' c c' t ce φ ψ hn hodd hc hc' hφ hψ
  exact assemble g n B (b.ζ : B) R I hI s s' c c' t ce φ ψ β hc hφ hψ (fun e => (hβ e).1) (fun e => (hβ e).2)

theorem quot_local (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ) :
    IsLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) :=
  have : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero e)))
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem quot_artin {R : Type} [CommRing R] [IsNoetherianRing R] (m : Ideal R) (hm : m.IsMaximal)
    (N : ℕ) : IsArtinianRing (R ⧸ m ^ (N + 1)) := by
  have : Ring.KrullDimLE 0 (R ⧸ m ^ (N + 1)) := by
    refine Ring.KrullDimLE.mk₀ fun P hP => ?_
    have h1 : m ^ (N + 1) ≤ P.comap (Ideal.Quotient.mk (m ^ (N + 1))) := by
      intro a ha
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
      exact P.zero_mem
    have hp : (P.comap (Ideal.Quotient.mk (m ^ (N + 1)))).IsPrime := Ideal.comap_isPrime _ _
    have h2 : m ≤ P.comap (Ideal.Quotient.mk (m ^ (N + 1))) := hp.le_of_pow_le h1
    have h3 := hm.eq_of_le hp.ne_top h2
    have h4 : (P.comap (Ideal.Quotient.mk (m ^ (N + 1)))).IsMaximal := h3 ▸ hm
    have h5 := Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (m ^ (N + 1)))
      Ideal.Quotient.mk_surjective h4
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h5
    exact h5.resolve_left hP.ne_top
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

theorem spMap_comp_ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id_ {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp [spMap]

end GlobalTheory.SFamCompl

namespace GlobalTheory.SFamCompl

theorem classified_of_complete : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F R _ _ _ hR β c hc
  have hn0 : n ≠ 0 := by omega
  set m := IsLocalRing.maximalIdeal R with hm
  haveI : ∀ e : ℕ, IsLocalRing (R ⧸ m ^ (e + 1)) := fun e => quot_local R e
  haveI : ∀ e : ℕ, IsArtinianRing (R ⧸ m ^ (e + 1)) := fun e => quot_artin m (IsLocalRing.maximalIdeal.isMaximal R) e
  let βe : ∀ e : ℕ, cycAway n →+* (R ⧸ m ^ (e + 1)) := fun e => (Ideal.Quotient.mk _).comp β
  have hthick : ∀ e, Out.thick R m e ≫ spMap β = spMap (βe e) ≫ spMap (RingHom.id (cycAway n)) := by
    intro e
    rw [spMap_id_, Category.comp_id]
    exact (spMap_comp_ β (Ideal.Quotient.mk (m ^ (e + 1)))).symm
  have hpull := fun e => GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n)
    (zetaAway n) (RingHom.id _) (Sp R) (Sp (R ⧸ m ^ (e + 1))) (spMap β) (spMap (βe e)) (Out.thick R m e) rfl (hthick e)
  choose ce hce using fun e => (hpull e).1 c
  have hcep : ∀ e, (ce e).Principal := fun e => (hpull e).2.1 c (ce e) (hce e) hc
  choose x hxs hxpb using fun e => _root_.GlobalTheory.SiegelArtin.main g n hg hn hodd F (R ⧸ m ^ (e + 1)) (βe e) (ce e) (hcep e)
  have hcomp : ∀ e, Out.thickTrans R m e ≫ x (e + 1) = x e := by
    intro e
    have h1 : SiegPB (ce e) (ce (e + 1)) (Out.thickTrans R m e) :=
      GlobalTheory.SiegelPullComp.pb_cancel (hce (e + 1)) (by rw [Out.thickTrans_comp]; exact hce e)
    refine _root_.GlobalTheory.SiegUniq.eq_of_siegPB g n hg hn hodd F _ (spMap (βe e)) (ce e) _ _ ?_ (hxs e)
      (GlobalTheory.SiegelPullComp.pb_comp (hxpb (e + 1)) h1) (hxpb e)
    rw [Category.assoc, hxs (e + 1)]
    exact (spMap_comp_ _ _).symm.trans (congrArg spMap (by ext a; rfl))
  obtain ⟨f, hf⟩ := glue R hR F.X x hcomp
  have hfs : f ≫ F.s = spMap β := by
    refine ext_affine R m hR.toIsHausdorff (cycAway n) _ _ fun e => ?_
    rw [← Category.assoc, hf e, hxs e, hthick e, spMap_id_, Category.comp_id]
  have hpf := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n)
    (zetaAway n) (RingHom.id _) F.X (Sp R) F.s (spMap β) f rfl (by rw [hfs, spMap_id_, Category.comp_id])
  obtain ⟨c', hc'⟩ := hpf.1 F.univ
  have hc'p : c'.Principal := hpf.2.1 F.univ c' hc' F.princ
  have key : SiegPB c c' (𝟙 _) := by
    refine alg g n (cycAway n) (cycBase hn0) R m hR hn hodd (spMap β) (spMap β) c c' hc hc'p fun e => ?_
    refine ⟨_, ce e, hce e, GlobalTheory.SiegelPullComp.pb_cancel hc' ?_⟩
    rw [hf e]
    exact hxpb e
  refine ⟨f, hfs, ?_⟩
  simpa using GlobalTheory.SiegelPullComp.pb_comp hc' key

end GlobalTheory.SFamCompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNormalOfSmooth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.ESOrdM

theorem stalk_normal_of_smooth (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f] (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  refine GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f (fun y => ?_) x
  have : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
  let _ : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y
  have h : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  have hle : y.asIdeal.primeCompl ≤ nonZeroDivisors R := y.asIdeal.primeCompl_le_nonZeroDivisors
  have hd : IsDomain ((Spec (CommRingCat.of R)).presheaf.stalk y) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  exact ⟨hd, isIntegrallyClosed_of_isLocalization _ _ hle⟩

end GlobalTheory.ESOrdM
end
end

