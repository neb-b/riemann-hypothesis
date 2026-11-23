module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1952
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0519
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticSimilitudeActionOnLevelFamily
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.UPel.HT.SympAct

theorem exists_smul_iff {h : ℕ} (M : ℕ) (w : Fin h ⊕ Fin h → ℤ) : (∃ c, w = M • c) ↔ reduceMod M w = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    funext i
    simp [reduceMod]
  · intro hw
    refine ⟨fun i => w i / M, ?_⟩
    funext i
    have hd : (M : ℤ) ∣ w i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (congrFun hw i)
    simp only [Pi.smul_apply, nsmul_eq_mul]
    rw [Int.mul_ediv_cancel' hd]

theorem lev_eq_of_reduce {h : ℕ} {T : Type*} [Monoid T] {M : ℕ} (hM : 0 < M) (lev : (Fin h ⊕ Fin h → ℤ) → T)
    (hadd : ∀ a b, lev (a + b) = lev a * lev b) (htor : ∀ a, lev a ^ M = 1) {x y : Fin h ⊕ Fin h → ℤ}
    (hxy : reduceMod M x = reduceMod M y) : lev x = lev y := by
  have hsm : ∀ (n : ℕ) c, lev ((n + 1) • c) = lev c ^ (n + 1) := by
    intro n c
    induction n with
    | zero => simp
    | succ n ih => rw [succ_nsmul, hadd, ih, ← pow_succ]
  obtain ⟨c, hc⟩ := (exists_smul_iff M (x - y)).2 (by
    funext i
    have e := congrFun hxy i
    simp only [reduceMod] at e
    simp only [reduceMod, Pi.sub_apply, Int.cast_sub, e, sub_self, Pi.zero_apply])
  have hx : x = y + M • c := by rw [← hc]; abel
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  rw [hx, hadd, hsm, htor, _root_.mul_one]

theorem omegaStd_cast {h : ℕ} (M : ℕ) (a b : Fin h ⊕ Fin h → ℤ) :
    ((omegaStd a b : ℤ) : ZMod M) = omegaMod M (reduceMod M a) (reduceMod M b) := by
  simp [omegaStd, omegaMod, reduceMod]

theorem zpow_eq_of_cast_eq {G : Type*} [Group G] {M : ℕ} (z : G) (hz : z ^ M = 1) {k l : ℤ}
    (hkl : (k : ZMod M) = l) : z ^ k = z ^ l := by
  obtain ⟨t, ht⟩ : (M : ℤ) ∣ k - l := (ZMod.intCast_eq_intCast_iff_dvd_sub l k M).1 hkl.symm
  have e : k = l + M * t := by linarith
  rw [e, zpow_add, zpow_mul, zpow_natCast, hz, one_zpow, _root_.mul_one]

theorem pow_eq_of_cast_eq {G : Type*} [Monoid G] {M : ℕ} (z : G) (hz : z ^ M = 1) {k l : ℕ}
    (hkl : (k : ZMod M) = l) : z ^ k = z ^ l := by
  rw [ZMod.natCast_eq_natCast_iff'] at hkl
  rw [← Nat.div_add_mod k M, ← Nat.div_add_mod l M, hkl, pow_add, pow_add, pow_mul, pow_mul, hz, one_pow, one_pow]

theorem mult_unique {h M : ℕ} (hh : 0 < h) (g : sympSimGrp h M) {n n' : ℕ} (hn : IsMultOf g n)
    (hn' : IsMultOf g n') : (n : ZMod M) = n' := by
  classical
  let e : Fin h ⊕ Fin h → ZMod M := Pi.single (Sum.inl ⟨0, hh⟩) 1
  let f : Fin h ⊕ Fin h → ZMod M := Pi.single (Sum.inr ⟨0, hh⟩) 1
  have hef : omegaMod M e f = 1 := by
    simp [omegaMod, e, f, Pi.single_apply]
  have := (hn e f).symm.trans (hn' e f)
  rw [hef] at this
  simpa using this

theorem isMultOf_mul {h M : ℕ} {a c : sympSimGrp h M} {n n' : ℕ} (ha : IsMultOf a n) (hc : IsMultOf c n') :
    IsMultOf (a * c) (n * n') := by
  intro x y
  change omegaMod M ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
    ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) x))
    ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
    ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) y)) = _
  rw [ha, hc]
  push_cast
  ring

theorem isMultOf_one {h M : ℕ} : IsMultOf (1 : sympSimGrp h M) 1 := by
  intro x y
  change omegaMod M x y = ((1 : ℕ) : ZMod M) * omegaMod M x y
  simp

theorem exists_mult {h M : ℕ} [NeZero M] (a : sympSimGrp h M) :
    ∃ n : ℕ, IsMultOf a n ∧ n.Coprime M ∧ (h = 0 → n = 1) := by
  by_cases hh : h = 0
  · subst hh
    exact ⟨1, fun x y => by simp [omegaMod], Nat.coprime_one_left _, fun _ => rfl⟩
  · obtain ⟨m, hm⟩ := a.2
    exact ⟨(m : ZMod M).val, fun x y => by rw [ZMod.natCast_zmod_val]; exact hm x y,
      ZMod.val_coe_unit_coprime m, fun h0 => absurd h0 hh⟩

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def idObjMap {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) : ObjMap o o (𝟙 S) :=
  { φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id o.A, sq := ⟨by simp, by simp⟩,
    act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB, eta := fun y => by simp }

theorem isSympLev_twist {b : Base D R} {N h M : ℕ} (hM : 0 < M) {X : Scheme.{0}} {s : X ⟶ Sp R}
    {s₁ : X ⟶ Sp (cycAway M)} (u : Obj b N s) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A))
    (hlev : IsSympLev u.P h M (zetaAway M) s₁ lev) (a : sympSimGrp h M) (n : ℕ) (ha : IsMultOf a n)
    (σ : cycAway M →+* cycAway M) (hσ : σ (zetaAway M) = zetaAway M ^ n) :
    IsSympLev u.P h M (zetaAway M) (s₁ ≫ spMap σ) (sympTwist a lev) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨hadd, htor, hgeo⟩ := hlev
  have hres : ∀ {x y : Fin h ⊕ Fin h → ℤ}, reduceMod M x = reduceMod M y → lev x = lev y :=
    fun hxy => lev_eq_of_reduce hM lev hadd htor hxy
  have hred_add : ∀ x y : Fin h ⊕ Fin h → ℤ, reduceMod M (x + y) = reduceMod M x + reduceMod M y := by
    intro x y; funext i; simp [reduceMod]
  refine ⟨fun x y => ?_, fun x => htor _, ?_⟩
  · simp only [sympTwist]
    rw [← hadd]
    apply hres
    simp only [hred_add, reduceMod_liftMod, map_add (f := _)]
  · intro k _ _ x β z hx hz
    obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : cycAway M →+* k, x ≫ s₁ = spMap β₀ :=
      ⟨(Spec.preimage (x ≫ s₁)).hom, by simp [spMap]⟩
    have hββ : β = β₀.comp σ := by
      have e : spMap β = spMap (β₀.comp σ) := by
        rw [← hx, ← Category.assoc, hβ₀, spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg CommRingCat.Hom.hom (Spec.map_inj.1 e)
    have hζ := isPrimitiveRoot_zetaAway hM.ne'
    let z₀ : kˣ := ((hζ.isUnit hM.ne').map β₀).unit
    have hz₀ : (z₀ : k) = β₀ (zetaAway M) := IsUnit.unit_spec _
    have hz' : z = z₀ ^ n := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hz, hββ, RingHom.comp_apply, hσ, map_pow, hz₀]
    have hz₀M : z₀ ^ M = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hz₀, ← map_pow, hζ.pow_eq_one, map_one, Units.val_one]
    obtain ⟨hker, hsurj, hweil⟩ := hgeo k x β₀ z₀ hβ₀ hz₀
    refine ⟨fun w => ?_, fun g hg => ?_, fun w v => ?_⟩
    · simp only [sympTwist]
      rw [hker, exists_smul_iff, exists_smul_iff, reduceMod_liftMod]
      exact LinearEquiv.map_eq_zero_iff _
    · obtain ⟨w, hw⟩ := hsurj g hg
      refine ⟨liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)).symm (reduceMod M w)), ?_⟩
      simp only [sympTwist]
      rw [reduceMod_liftMod, LinearEquiv.apply_symm_apply, ← hw]
      congr 1
      exact hres (reduceMod_liftMod _)
    · simp only [sympTwist]
      have key : z ^ (2 * omegaStd w v) = z₀ ^ (2 * omegaStd
          (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M w)))
          (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M v)))) := by
        rw [hz', ← zpow_natCast, ← zpow_mul]
        apply zpow_eq_of_cast_eq z₀ hz₀M
        push_cast
        rw [omegaStd_cast, omegaStd_cast, reduceMod_liftMod, reduceMod_liftMod, ha]
        ring
      rw [key]
      exact hweil _ _

theorem exists_sympActs : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev → HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
    ∃ ρ : sympSimGrp h M → (X ⟶ X), ρ 1 = 𝟙 X ∧ (∀ a c, ρ (a * c) = ρ a ≫ ρ c) ∧ SympActs s s₁ u lev ρ := by
  intro p _ D R _ b N h M hM X s s₁ u lev hlev huniv
  haveI : NeZero M := ⟨hM.ne'⟩
  have hζ := isPrimitiveRoot_zetaAway hM.ne'
  have hζM : zetaAway M ^ M = 1 := hζ.pow_eq_one
  have hadd := hlev.1
  have htor := hlev.2.1
  have hres : ∀ {x y : Fin h ⊕ Fin h → ℤ}, reduceMod M x = reduceMod M y → lev x = lev y :=
    fun hxy => lev_eq_of_reduce hM lev hadd htor hxy
  choose n hn hcop h0 using fun a : sympSimGrp h M => exists_mult a
  have hσex : ∀ a, ∃ σ : cycAway M →+* cycAway M, σ (zetaAway M) = zetaAway M ^ n a := fun a =>
    let ⟨σ, hσ⟩ := exists_cycAway_aut hM.ne' (hcop a); ⟨σ.toRingHom, hσ⟩
  choose σ hσ using hσex
  have hU : ∀ a, ∃! f : X ⟶ X, f ≫ s = s ∧ f ≫ s₁ = s₁ ≫ spMap (σ a) ∧
      ∃ m : ObjMap u u f, ∀ x, (sympTwist a lev x).left ≫ m.φ = f ≫ (lev x).left :=
    fun a => huniv X s (s₁ ≫ spMap (σ a)) u (sympTwist a lev)
      (isSympLev_twist hM u lev hlev a (n a) (hn a) (σ a) (hσ a))
  choose ρ hρ hρu using hU
  have hcons : ∀ a c, zetaAway M ^ n (a * c) = zetaAway M ^ (n a * n c) := by
    intro a c
    by_cases hh : h = 0
    · rw [h0 _ hh, h0 _ hh, h0 _ hh]
    · exact pow_eq_of_cast_eq _ hζM (mult_unique (Nat.pos_of_ne_zero hh) _ (hn _) (isMultOf_mul (hn a) (hn c)))
  have hone : zetaAway M ^ n 1 = zetaAway M := by
    by_cases hh : h = 0
    · rw [h0 _ hh, pow_one]
    · rw [pow_eq_of_cast_eq _ hζM (mult_unique (Nat.pos_of_ne_zero hh) _ (hn 1) isMultOf_one), pow_one]
  refine ⟨ρ, ?_, fun a c => ?_, fun a => ⟨(hρ a).1, ⟨n a, σ a, hn a, hσ a, (hρ a).2.1⟩, (hρ a).2.2⟩⟩
  · have hσ1 : σ 1 = RingHom.id _ := cycAway_hom_ext hM.ne' (by rw [hσ, hone]; rfl)
    refine (hρu 1 (𝟙 X) ⟨Category.id_comp _, ?_, ?_⟩).symm
    · rw [hσ1, Category.id_comp]
      simp [spMap]
    · refine ⟨idObjMap u, fun x => ?_⟩
      change (lev (liftMod (reduceMod M x))).left ≫ 𝟙 _ = 𝟙 X ≫ (lev x).left
      rw [Category.comp_id, Category.id_comp, hres (reduceMod_liftMod _)]
  · have hσmul : σ (a * c) = (σ a).comp (σ c) := cycAway_hom_ext hM.ne' (by
      rw [hσ, RingHom.comp_apply, hσ, map_pow, hσ, ← pow_mul, hcons])
    refine (hρu (a * c) (ρ a ≫ ρ c) ⟨?_, ?_, ?_⟩).symm
    · rw [Category.assoc, (hρ c).1, (hρ a).1]
    · rw [Category.assoc, (hρ c).2.1, ← Category.assoc, (hρ a).2.1, Category.assoc, hσmul, spMap, spMap, spMap,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · obtain ⟨ma, hma⟩ := (hρ a).2.2
      obtain ⟨mc, hmc⟩ := (hρ c).2.2
      refine ⟨ObjMapComp.comp ma mc, fun x => ?_⟩
      change (sympTwist (a * c) lev x).left ≫ ma.φ ≫ mc.φ = (ρ a ≫ ρ c) ≫ (lev x).left
      have e1 : sympTwist (a * c) lev x = sympTwist a lev
          (liftMod ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M x))) := by
        simp only [sympTwist, reduceMod_liftMod]
        rfl
      rw [e1, ← Category.assoc, hma, Category.assoc]
      change ρ a ≫ (sympTwist c lev x).left ≫ mc.φ = _
      rw [hmc, Category.assoc]

end GlobalTheory.UPel.HT.SympAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorOfOriginDerivation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section
namespace GlobalTheory.CoordsOrigin

variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]

def derHom (D : G.left.presheaf.stalk (origin G) → R) (hadd : ∀ x y, D (x + y) = D x + D y)
    (hmul : ∀ x y, D (x * y) = evO G x * D y + evO G y * D x) (hc : ∀ r, D (constO G r) = 0) :
    G.left.presheaf.stalk (origin G) →+* DualNumber R where
  toFun f := TrivSqZeroExt.inl (evO G f) + TrivSqZeroExt.inr (D f)
  map_one' := by
    have h1 : D 1 = 0 := by simpa using hc 1
    ext <;> simp [h1]
  map_mul' x y := by
    ext <;> simp [hmul]
    ring
  map_zero' := by
    have h0 : D 0 = 0 := by simpa using hadd 0 0
    ext <;> simp [h0]
  map_add' x y := by
    ext <;> simp [hadd]

end GlobalTheory.CoordsOrigin

namespace GlobalTheory.CoordsOrigin
theorem exists_tan_of_derivation (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] (D : G.left.presheaf.stalk (origin G) → R) (hadd : ∀ x y, D (x + y) = D x + D y)
    (hmul : ∀ x y, D (x * y) = evO G x * D y + evO G y * D x) (hc : ∀ r, D (constO G r) = 0) :
    ∃ v : TanM (𝟙 (Sp R)) G, ∀ f, tanDer G v f = D f := by
  set ψ := derHom G D hadd hmul hc with hψdef
  have hψ : ∀ f, ψ f = TrivSqZeroExt.inl (evO G f) + TrivSqZeroExt.inr (D f) := fun f => rfl
  haveI : IsLocalHom (evO G) := Scheme.isLocalHom_stalkClosedPointTo' (R := R) (η[G]).left
  haveI hloc : IsLocalHom ψ := ⟨fun a ha => by
    have h2 : IsUnit (ψ a).fst := (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha
    simp only [hψ, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero] at h2
    exact isUnit_of_map_unit (evO G) a h2⟩
  haveI hloc' : IsLocalHom (CommRingCat.ofHom ψ).hom := hloc
  let p : Sp (DualNumber R) ⟶ G.left := spMap ψ ≫ G.left.fromSpecStalk (origin G)
  have hcomp : ψ.comp (constO G) = algebraMap R (DualNumber R) := by
    ext r <;> simp [hψ, evO_constO, hc, TrivSqZeroExt.algebraMap_eq_inl]
  have hover : p ≫ G.hom = (overAt (𝟙 (Sp R)) (DualNumber R)).hom := by
    simp only [p, Category.assoc]
    rw [spMap_fromSpecStalk_origin_hom, hcomp]
    simp [overAt]
  let w : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G := Over.homMk p hover
  have hw : smT (𝟙 (Sp R)) 0 w = 1 := by
    apply Over.OverMorphism.ext
    rw [smT_left, one_left]
    have e1 : (epsMul (0 : R)).comp ψ = (algebraMap R (DualNumber R)).comp (evO G) := by
      ext f <;> simp [hψ, epsMul, TrivSqZeroExt.algebraMap_eq_inl]
    have e2 : spMap (evO G) ≫ G.left.fromSpecStalk (origin G) = (η[G]).left :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R) (η[G]).left
    change spMap (epsMul (0 : R)) ≫ spMap ψ ≫ G.left.fromSpecStalk (origin G) = _
    have e3 : spMap (epsMul (0 : R)) ≫ spMap ψ = spMap ((epsMul (0 : R)).comp ψ) := by
      simp only [spMap, ← Spec.map_comp]; rfl
    have e4 : spMap ((algebraMap R (DualNumber R)).comp (evO G)) = spMap (algebraMap R (DualNumber R)) ≫ spMap (evO G) := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [← Category.assoc, e3, e1, e4, Category.assoc, e2]
    simp [overAt]
  refine ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT w hw, fun f => ?_⟩
  rw [tanDer_eq]
  have key : (G.left.presheaf.stalkCongr (Inseparable.of_eq (tv_closedPoint G (ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT w hw)).symm)).hom ≫
      Scheme.stalkClosedPointTo (R := CommRingCat.of (DualNumber R)) (tv (ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT w hw)).left =
      CommRingCat.ofHom ψ := by
    refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
    rw [TopCat.Presheaf.stalkCongr_hom]
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc]
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (CommRingCat.ofHom ψ) U _
  rw [key]
  simp [hψ]
end GlobalTheory.CoordsOrigin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionsEmbedFunctionFieldRegular
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct

namespace GlobalTheory.Desc.BCChart

def ev {T : Scheme.{0}} {K : Type} [CommRing K] (f : Sp K ⟶ T) (O : T.Opens) (h : ⊤ ≤ f ⁻¹ᵁ O) (u : Γ(T, O)) : K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((f.appLE O ⊤ h).hom u)

theorem ev_comp {T T' : Scheme.{0}} {K : Type} [CommRing K] (s : Sp K ⟶ T') (g : T' ⟶ T) {O : T.Opens}
    {O' : T'.Opens} (e : O' ≤ g ⁻¹ᵁ O) (h : ⊤ ≤ s ⁻¹ᵁ O') {g' : Sp K ⟶ T} (hg : s ≫ g = g')
    (h' : ⊤ ≤ g' ⁻¹ᵁ O) (u : Γ(T, O)) : ev g' O h' u = ev s O' h ((g.appLE O O' e).hom u) := by
  subst hg
  unfold ev
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem appLE_top_top {A B : Scheme.{0}} (f : A ⟶ B) : f.appLE ⊤ ⊤ le_top = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  congr 1

theorem ev_spMap {T : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (θ : A →+* B) (f : Sp A ⟶ T)
    (O : T.Opens) (h : ⊤ ≤ f ⁻¹ᵁ O) (h' : ⊤ ≤ (spMap θ ≫ f) ⁻¹ᵁ O) (u : Γ(T, O)) :
    ev (spMap θ ≫ f) O h' u = θ (ev f O h u) := by
  rw [ev_comp (spMap θ) f h le_top rfl]
  unfold ev
  rw [appLE_top_top, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]
  rfl

theorem fromSpecStalk_top' {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
  intro z _
  have hz : X.fromSpecStalk x z ⤳ x := by
    have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact hz.mem_open U.2 hx

theorem fromSpecStalk_appLE' {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (fromSpecStalk_top' x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (fromSpecStalk_top' x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

theorem fnOf_eq_ev {X : Scheme.{0}} [IsIntegral X] (O : X.Opens) (hO : genericPoint X ∈ O) (u : Γ(X, O)) :
    fnOf O hO u = ev (gp X) O (fromSpecStalk_top' _ O hO) u := by
  unfold ev gp
  rw [fromSpecStalk_appLE' (genericPoint X) O hO, CommRingCat.comp_apply]
  change _ = (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).hom _
  rw [Iso.inv_hom_id_apply]
  rfl

theorem exists_tensor_fnOf : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (X Y V : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp R) (q : Y ⟶ Sp R₁) (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), IsPullback φ (i ≫ q) p (spMap ρ) → PFF i φ θ → ∀ (U : X.Opens), IsAffineOpen U → ∀ hg : genericPoint X ∈ U, letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra; letI := ρ.toAlgebra; ∃ β : Γ(X, U) ⊗[R] R₁ →+ Y.functionField, Function.Injective β ∧ (∀ b r, β (b ⊗ₜ[R] r) = θ (GlobalTheory.Cartier.fnOf U hg b) * GlobalTheory.Desc.cst q r) ∧ Set.range β = {v | ∀ z : V, φ z ∈ U → GlobalTheory.Cartier.RegAt (i z) v} := by
  intro R R₁ _ _ ρ X Y V _ _ p q i _ φ θ H hP U hU hg
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra
  letI := ρ.toAlgebra
  obtain ⟨l, hl1, hl2⟩ := hP
  let W : V.Opens := φ ⁻¹ᵁ U ⊓ (i ≫ q) ⁻¹ᵁ ⊤
  let O : Y.Opens := i ''ᵁ W
  have hmemW : ∀ z : V, z ∈ W ↔ φ z ∈ U := fun z => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩
  have hmemO : ∀ y : Y, y ∈ O ↔ ∃ z : V, φ z ∈ U ∧ i z = y := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz.1, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, (hmemW z).2 hz, rfl⟩
  let pt : Sp Y.functionField := IsLocalRing.closedPoint Y.functionField
  have hz1 : i (l pt) = genericPoint Y := by
    rw [← Scheme.Hom.comp_apply, hl1]
    exact Scheme.fromSpecStalk_closedPoint
  have hz2 : φ (l pt) = genericPoint X := by
    rw [← Scheme.Hom.comp_apply, hl2, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecStalk_closedPoint (x := genericPoint X) ▸ congrArg _ (Subsingleton.elim _ _)
  have hO : genericPoint Y ∈ O := (hmemO _).2 ⟨l pt, hz2 ▸ hg, hz1⟩
  let e := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens p (i ≫ q) φ H U hU
  let j : Γ(V, W) →+* Γ(Y, O) := (i.appIso W).inv.hom
  have hj : ∀ s, j ((i.appIso W).hom.hom s) = s := fun s => Iso.hom_inv_id_apply _ _
  have hj' : ∀ s, (i.appIso W).hom.hom (j s) = s := fun s => Iso.inv_hom_id_apply _ _
  refine ⟨((fnOf O hO).comp (j.comp e.toRingHom)).toAddMonoidHom, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 := congrArg (i.appIso W).hom.hom (fnOf_injective O hO hab)
    simp only [RingHom.comp_apply, hj'] at h1
    exact e.injective h1
  · intro b r
    have hlW : ⊤ ≤ l ⁻¹ᵁ W := by
      intro z _
      have hz : z = pt := Subsingleton.elim _ _
      subst hz
      exact (hmemW _).2 (hz2 ▸ hg)
    have hC : ∀ y : Γ(V, W), fnOf O hO (j y) = ev l W hlW y := by
      intro y
      rw [fnOf_eq_ev]
      refine (ev_comp l i (O := O) (O' := W) (i.preimage_image_eq W).ge hlW hl1 _ _).trans ?_
      congr 1
      rw [← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
      have : (homOfLE (le_refl W)).op = 𝟙 (Opposite.op W) := rfl
      erw [this, CategoryTheory.Functor.map_id]
      rfl
    have hX : ⊤ ≤ (spMap θ ≫ gp X) ⁻¹ᵁ U := fun z _ => fromSpecStalk_top' (genericPoint X) U hg (Set.mem_univ (spMap θ z))
    have hYq : ⊤ ≤ (gp Y ≫ q) ⁻¹ᵁ ⊤ := fun _ _ => trivial
    show fnOf O hO (j (e (b ⊗ₜ[R] r))) = _
    rw [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_tmul, map_mul, map_mul, hC, hC]
    congr 1
    · rw [← ev_comp l φ inf_le_left hlW hl2 hX, ev_spMap θ (gp X) U (fromSpecStalk_top' _ U hg), ← fnOf_eq_ev]
    · unfold ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX cst
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, fnOf_eq_ev ⊤ trivial, ← appLE_top_top,
        ← ev_comp l (i ≫ q) le_top hlW (by rw [← Category.assoc, hl1]) hYq,
        ← ev_comp (gp Y) q le_top (fromSpecStalk_top' _ ⊤ trivial) rfl hYq]
  · ext v
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, rfl⟩ z hz
      exact regAt_fnOf ((hmemO _).2 ⟨z, hz, rfl⟩) hO _
    · intro hv
      obtain ⟨s, hs⟩ := exists_fnOf_eq hO fun y hy => by
        obtain ⟨z, hz, rfl⟩ := (hmemO y).1 hy
        exact hv z hz
      refine ⟨e.symm ((i.appIso W).hom.hom s), ?_⟩
      show fnOf O hO (j (e (e.symm ((i.appIso W).hom.hom s)))) = v
      rw [RingEquiv.apply_symm_apply, hj, hs]

end GlobalTheory.Desc.BCChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSquareEquivFibreSquareSections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBDescent

theorem exists_tensorSquare_equiv_sections {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (V₀ : Y.Opens)
    (hV₀ : IsAffineOpen V₀)
    (h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀) :
    letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
    ∃ e : Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀) ≃+* Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀),
      ∀ a b : Γ(X, f ⁻¹ᵁ V₀), e (a ⊗ₜ b) =
        ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a * ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom b := by
  letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
  have hV' : IsAffineOpen (f ⁻¹ᵁ V₀) := hV₀.preimage f
  have P := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE (IsPullback.of_hasPullback f f).flip
    inferInstance hV₀ hV' le_rfl h
  rw [Scheme.Hom.appLE_eq_app] at P
  have T := CommRingCat.isPushout_tensorProduct Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) Γ(X, f ⁻¹ᵁ V₀)
  let I := IsPushout.isoIsPushout _ _ T P.flip
  refine ⟨I.commRingCatIsoToRingEquiv, fun a b => ?_⟩
  have h1 : I.hom.hom (a ⊗ₜ 1) = ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a :=
    congrArg (fun t => t.hom a) (IsPushout.inl_isoIsPushout_hom _ _ T P.flip)
  have h2 : I.hom.hom (1 ⊗ₜ b) = ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom b :=
    congrArg (fun t => t.hom b) (IsPushout.inr_isoIsPushout_hom _ _ T P.flip)
  have hab : (a ⊗ₜ[Γ(Y, V₀)] b : Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) = (a ⊗ₜ 1) * (1 ⊗ₜ b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
  change I.hom.hom (a ⊗ₜ b) = _
  rw [hab, map_mul, h1, h2]

end GlobalTheory.LBDescent
end
end

