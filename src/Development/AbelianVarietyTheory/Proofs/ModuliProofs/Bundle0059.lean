module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothModelsIsoOverFgSubalgebra
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.Spread

section

variable {k V : Type} [CommRing k] [CommRing V] [Algebra k V] {P Q T : Scheme.{0}}
  {p : P ⟶ Sp k} {q : Q ⟶ Sp k} {t : T ⟶ Sp V} {τ : T ⟶ P} {τ' : T ⟶ Q}

theorem eq_isoPullback_hom_comp_bcMap (hτ : IsPullback τ t p (spMap (algebraMap k V)))
    (R : Subalgebra k V) (σ : T ⟶ pullback p (spMap (algebraMap k R)))
    (h₁ : σ ≫ pullback.fst _ _ = τ) (h₂ : σ ≫ pullback.snd _ _ = t ≫ spMap R.val.toRingHom) :
    σ = hτ.isoPullback.hom ≫ bcMap p R.val := by
  apply pullback.hom_ext
  · rw [h₁, Category.assoc, bcMap_fst, IsPullback.isoPullback_hom_fst]
  · rw [h₂, Category.assoc, bcMap_snd, ← Category.assoc, IsPullback.isoPullback_hom_snd]

theorem comp_eq_id_of_models [Flat p] [IsSeparated p]
    (hτ : IsPullback τ t p (spMap (algebraMap k V)))
    (hτ' : IsPullback τ' t q (spMap (algebraMap k V))) (R : Subalgebra k V)
    (f : pullback p (spMap (algebraMap k R)) ⟶ pullback q (spMap (algebraMap k R)))
    (g : pullback q (spMap (algebraMap k R)) ⟶ pullback p (spMap (algebraMap k R)))
    (hf : f ≫ pullback.snd _ _ = pullback.snd _ _) (hg : g ≫ pullback.snd _ _ = pullback.snd _ _)
    (hf' : hτ.isoPullback.hom ≫ bcMap p R.val ≫ f ≫ pullback.fst _ _ = τ')
    (hg' : hτ'.isoPullback.hom ≫ bcMap q R.val ≫ g ≫ pullback.fst _ _ = τ) :
    f ≫ g = 𝟙 _ := by

  have hu : hτ.isoPullback.hom ≫ bcMap p R.val ≫ f = hτ'.isoPullback.hom ≫ bcMap q R.val := by
    apply eq_isoPullback_hom_comp_bcMap hτ' R
    · simpa only [Category.assoc] using hf'
    · rw [Category.assoc, Category.assoc, hf, bcMap_snd, ← Category.assoc,
        IsPullback.isoPullback_hom_snd]

  have hfst : bcMap p R.val ≫ f ≫ g ≫ pullback.fst _ _ = pullback.fst _ _ := by
    rw [← cancel_epi hτ.isoPullback.hom, reassoc_of% hu, IsPullback.isoPullback_hom_fst]
    exact hg'

  refine hom_ext_bcMap p R.val Subtype.val_injective (pullback.snd p (spMap (algebraMap k R)))
    ?_ ?_
  · rw [Category.assoc, hg, hf, Category.id_comp]
  · rw [Category.comp_id]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hfst, bcMap_fst]
    · rw [Category.assoc, Category.assoc, hg, hf]

end

end GlobalTheory.Spread

namespace GlobalTheory

open Spread

theorem smooth_models_iso_over_fg_subalgebra :
    ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (P Q T : Scheme.{0}) (p : P ⟶ Sp k) (q : Q ⟶ Sp k) (t : T ⟶ Sp V) (τ : T ⟶ P) (τ' : T ⟶ Q), Smooth p → IsSeparated p → QuasiCompact p → Smooth q → IsSeparated q → QuasiCompact q → IsPullback τ t p (spMap (algebraMap k V)) → IsPullback τ' t q (spMap (algebraMap k V)) → ∃ (R : Subalgebra k V) (e : pullback p (spMap (algebraMap k R)) ≅ pullback q (spMap (algebraMap k R))), R.FG ∧ e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧ ∀ σ : T ⟶ pullback p (spMap (algebraMap k R)), σ ≫ pullback.fst _ _ = τ → σ ≫ pullback.snd _ _ = t ≫ spMap R.val.toRingHom → σ ≫ e.hom ≫ pullback.fst _ _ = τ' := by
  intro k V _ _ _ P Q T p q t τ τ' _ _ _ _ _ _ hτ hτ'

  have hΦ : (hτ.isoPullback.inv ≫ τ') ≫ q = pullback.fst _ _ ≫ p := by
    rw [← hτ.isoPullback_inv_fst]
    simp only [Category.assoc, hτ.w, hτ'.w]
  have hΨ : (hτ'.isoPullback.inv ≫ τ) ≫ p = pullback.fst _ _ ≫ q := by
    rw [← hτ'.isoPullback_inv_fst]
    simp only [Category.assoc, hτ.w, hτ'.w]

  obtain ⟨R₁, ψ₁, hR₁, hψ₁, hψ₁'⟩ := exists_fg_comp_eq p q _ hΦ
  obtain ⟨R, ψ₂, hR, hle, hψ₂⟩ :=
    exists_fg_forall_comp_eq q p (fun _ : Unit ↦ hτ'.isoPullback.inv ≫ τ) (fun _ ↦ hΨ) R₁ hR₁

  have ha : (bcMap p (Subalgebra.inclusion hle) ≫ ψ₁) ≫ q =
      pullback.snd _ _ ≫ spMap (algebraMap k R) := by
    rw [Category.assoc, hψ₁, bcMap_fst_assoc, pullback.condition]
  have hb : ψ₂ () ≫ p = pullback.snd _ _ ≫ spMap (algebraMap k R) := by
    rw [(hψ₂ ()).1, pullback.condition]
  obtain ⟨f, hf₁, hf₂⟩ : ∃ f : pullback p (spMap (algebraMap k R)) ⟶
      pullback q (spMap (algebraMap k R)),
      f ≫ pullback.fst _ _ = bcMap p (Subalgebra.inclusion hle) ≫ ψ₁ ∧
        f ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift _ _ ha, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨g, hg₁, hg₂⟩ : ∃ g : pullback q (spMap (algebraMap k R)) ⟶
      pullback p (spMap (algebraMap k R)),
      g ≫ pullback.fst _ _ = ψ₂ () ∧ g ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift _ _ hb, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

  have hf' : hτ.isoPullback.hom ≫ bcMap p R.val ≫ f ≫ pullback.fst _ _ = τ' := by
    rw [hf₁, bcMap_comp_of_eq_assoc p (Subalgebra.inclusion hle) R.val R₁.val (fun _ ↦ rfl), hψ₁',
      Iso.hom_inv_id_assoc]
  have hg' : hτ'.isoPullback.hom ≫ bcMap q R.val ≫ g ≫ pullback.fst _ _ = τ := by
    rw [hg₁, (hψ₂ ()).2, Iso.hom_inv_id_assoc]
  refine ⟨R, ⟨f, g, comp_eq_id_of_models hτ hτ' R f g hf₂ hg₂ hf' hg',
    comp_eq_id_of_models hτ' hτ R g f hg₂ hf₂ hg' hf'⟩, hR, hf₂, ?_⟩
  intro σ h₁ h₂
  rw [eq_isoPullback_hom_comp_bcMap hτ R σ h₁ h₂, Category.assoc]
  exact hf'

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapComp
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (g : Sp A ⟶ Sp B) : ∃ β : B →+* A, g = spMap β :=
  ⟨(Spec.preimage g).hom, (Spec.map_preimage g).symm⟩

theorem spMap_inj' {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

def fnOn {L : Type} [CommRing L] {T : Scheme.{0}} (g : T ⟶ Sp L) : L →+* Γ(T, ⊤) :=
  g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom

theorem map_fnOn {L k : Type} [CommRing L] [CommRing k] {T : Scheme.{0}} (g : T ⟶ Sp L) (h : Sp k ⟶ T)
    (β : L →+* k) (e : h ≫ g = spMap β) (c : Lˣ) :
    Units.map h.appTop.hom.toMonoidHom (Units.map (fnOn g).toMonoidHom c) = unitOn (Units.map β.toMonoidHom c) := by
  apply Units.ext
  show h.appTop.hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom c)) =
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (β c)
  have h1 : (h ≫ g).appTop = g.appTop ≫ h.appTop := Scheme.Hom.comp_appTop _ _
  have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β)
  have h3 := congrArg (fun φ => φ.hom (c : L)) h2
  rw [e] at h1
  have h4 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom c)) h1
  exact h4.symm.trans h3.symm

abbrev TateAt (D : Datum H) (t : SAB H S) {k : Type} [Field k] (x : Sp k ⟶ S) : Type :=
  TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
    (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))

theorem datum_free (D : Datum H) : Module.Free ℤ D.La ∧ Module.Finite ℤ D.La := by
  have := D.fin
  have := D.proj
  have h : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  exact ⟨inferInstance, h⟩

theorem act_nsmul (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) (c : 𝓞 E) :
    x ≫ t.act.act (n • c) = (x ^ n) ≫ t.act.act c := by
  have := t.act.hom c
  rw [add_map_nsmul t.act.add, MonObj.comp_pow, MonObj.pow_comp]

theorem exists_full (t : SAB H S) {B L : Type} [Field B] [CharZero B] [Field L] [Algebra B L] [FiniteDimensional B L]
    (s : S ⟶ Sp B) {N : ℕ} (hN : 0 < N) {ξ : Lˣ} (hξ : ξ ^ N = 1)
    {Z : Over S} {et : D.La → (Z ⟶ t.G)} (R : RepTors t.G N D.La Z et)
    (hW : ∀ (T : Over S) (x y : T ⟶ t.G) (c : Γ(T.left, ⊤)ˣ), IsUnit (N : Γ(T.left, ⊤)) → x ^ N = 1 → y ^ N = 1 →
      c ^ N = 1 → ClopenCond T fun _ h =>
        Out.WeilIs t.G t.PP.L N (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c)) :
    ∃ (W : Over S) (α : D.La → (W ⟶ t.G)), IsFinite W.hom ∧ Etale W.hom ∧ (∀ a c, α (a + c) = α a * α c) ∧
      (∀ a, α a ^ N = 1) ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (β : B →+* k), x ≫ s = spMap β →
        ∀ α' : D.La → (Over.mk x ⟶ t.G), (∀ a c, α' (a + c) = α' a * α' c) → (∀ a, α' a ^ N = 1) →
          ((∃ w : Over.mk x ⟶ W, ∀ a, w ≫ α a = α' a) ↔ ∃ β' : L →+* k, β'.comp (algebraMap B L) = β ∧
            (∀ (c : 𝓞 E) a, α' (c • a) = α' a ≫ t.act.act c) ∧
            ∀ a b, Out.WeilIs t.G t.PP.L N (α' a) (α' b) (unitOn (Units.map β'.toMonoidHom ξ ^ D.EF a b))) := by
  obtain ⟨hfree, hfin⟩ := datum_free D
  have hLf : IsFinite (spMap (algebraMap B L)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hLe : Etale (spMap (algebraMap B L)) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FormallyEtale B L := Algebra.FormallyEtale.of_isSeparable B L
    have : Algebra.FinitePresentation B L := Algebra.FinitePresentation.of_finiteType.1 inferInstance
    exact RingHom.etale_algebraMap.mpr ⟨inferInstance, inferInstance⟩
  let C : Over S := Over.mk (pullback.fst s (spMap (algebraMap B L)))
  have hC1 : IsFinite C.hom := inferInstanceAs (IsFinite (pullback.fst s (spMap (algebraMap B L))))
  have hC2 : Etale C.hom := inferInstanceAs (Etale (pullback.fst s (spMap (algebraMap B L))))
  have := R.1
  have := R.2.1
  obtain ⟨hY1, hY2⟩ := finiteEtale_tensor Z C
  let g : (Z ⊗ C).left ⟶ Sp L := (snd Z C).left ≫ pullback.snd s (spMap (algebraMap B L))
  have hg : g ≫ spMap (algebraMap B L) = (Z ⊗ C).hom ≫ s := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ s) (Over.w (snd Z C))
  let y : D.La → (Z ⊗ C ⟶ t.G) := fun a => fst Z C ≫ et a
  have yadd : ∀ a c, y (a + c) = y a * y c := fun a c => by simp only [y, R.2.2.1, MonObj.comp_mul]
  have ypow : ∀ a, y a ^ N = 1 := fun a => by simp only [y]; rw [← MonObj.comp_pow, R.2.2.2.1, MonObj.comp_one]
  have ymod : ∀ a c, y (a + N • c) = y a := fun a c => by rw [yadd, add_map_nsmul yadd, ypow, _root_.mul_one]
  have hchar : CharZero L := charZero_of_injective_algebraMap (algebraMap B L).injective
  have hu : IsUnit (N : Γ((Z ⊗ C).left, ⊤)) := by
    have := (IsUnit.mk0 (N : L) (Nat.cast_ne_zero.2 hN.ne')).map (fnOn g)
    rwa [map_natCast] at this
  obtain ⟨κ, _, q, hq⟩ := exists_finite_mod D.La hN
  obtain ⟨κ', _, q', hq'⟩ := exists_finite_mod (𝓞 E) hN
  have c1 : ClopenCond (Z ⊗ C) fun _ h => ∀ (c : 𝓞 E) a, h ≫ y (c • a) = h ≫ y a ≫ t.act.act c := by
    refine ClopenCond.forall_of_finite q' (fun c => ?_) fun c c' e T' h Hc a => ?_
    · have := t.act.hom c
      refine R.clopenCond (fun a => y (c • a)) (fun a => y a ≫ t.act.act c) (fun a a' => by rw [smul_add, yadd])
        (fun a => ypow _) (fun a a' => by rw [yadd, MonObj.mul_comp]) fun a => by
          rw [← MonObj.pow_comp, ypow, MonObj.one_comp]
    · obtain ⟨d, rfl⟩ := hq' c c' e
      have := t.act.hom d
      rw [add_smul, smul_assoc, ymod, Hc, t.act.add, MonObj.comp_mul, act_nsmul, ypow, MonObj.one_comp,
        _root_.mul_one]
  have c2 : ClopenCond (Z ⊗ C) fun _ h => ∀ p : D.La × D.La, Out.WeilIs t.G t.PP.L N (h ≫ y p.1) (h ≫ y p.2)
      (Units.map (h.left.appTop).hom.toMonoidHom (Units.map (fnOn g).toMonoidHom (ξ ^ D.EF p.1 p.2))) := by
    refine ClopenCond.forall_of_finite (Prod.map q q) (fun p => hW _ _ _ _ hu (ypow _) (ypow _) ?_)
      fun p p' e T' h Hc => ?_
    · rw [← map_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hξ, one_zpow, map_one]
    · obtain ⟨a, b⟩ := p
      obtain ⟨a', b'⟩ := p'
      obtain ⟨c, rfl⟩ := hq a a' (congrArg Prod.fst e)
      obtain ⟨d, rfl⟩ := hq b b' (congrArg Prod.snd e)
      have : ξ ^ D.EF (a + N • c) (b + N • d) = ξ ^ D.EF a b := by
        have : D.EF (a + N • c) (b + N • d) = D.EF a b + N * (D.EF a d + D.EF c (b + N • d)) := by
          simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
          ring
        rw [this, zpow_add, zpow_mul, zpow_natCast, hξ, one_zpow, _root_.mul_one]
      dsimp only at Hc ⊢
      rwa [ymod, ymod, this]
  obtain ⟨U, hU, HU⟩ := c1.and c2
  obtain ⟨W, i, hW1, hW2, -, Hi⟩ := exists_sub U hU
  refine ⟨W, fun a => i ≫ y a, hW1, hW2, fun a c => by beta_reduce; rw [yadd, MonObj.comp_mul],
    fun a => by beta_reduce; rw [← MonObj.comp_pow, ypow, MonObj.comp_one], fun k _ x β hx α' hadd hpow => ⟨?_, ?_⟩⟩
  · rintro ⟨w, hw⟩
    obtain ⟨h1, h2⟩ := (HU _ (w ≫ i)).2 ((Hi _ _).2 ⟨w, rfl⟩)
    obtain ⟨β', hβ'⟩ := exists_spMap (A := k) ((w ≫ i).left ≫ g)
    refine ⟨β', spMap_inj' ?_, fun c a => ?_, fun a b => ?_⟩
    · rw [← spMap_comp'', ← hβ', ← hx, Category.assoc, hg, ← Category.assoc]
      exact congrArg (· ≫ s) (Over.w (w ≫ i))
    · rw [← hw, ← hw, ← Category.assoc, h1]
      simp only [Category.assoc]
    · have := h2 (a, b)
      rw [map_fnOn g _ β' hβ', map_zpow, Category.assoc, Category.assoc, hw, hw] at this
      exact this
  · rintro ⟨β', hβ', h1, h2⟩
    obtain ⟨z, hz, -⟩ := R.2.2.2.2 _ α' hadd hpow
    let c : Over.mk x ⟶ C := Over.homMk (pullback.lift x (spMap β') (by rw [hx, spMap_comp'', hβ']))
      (pullback.lift_fst _ _ _)
    have hy : ∀ a, lift z c ≫ y a = α' a := fun a => by simp only [y]; rw [lift_fst_assoc, hz]
    have hg' : (lift z c).left ≫ g = spMap β' := by
      simp only [g]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      exact pullback.lift_snd _ _ _
    obtain ⟨w, hw⟩ := (Hi _ (lift z c)).1 ((HU _ _).1 ⟨fun c a => by rw [hy, ← Category.assoc, hy, h1], fun p => by
      rw [map_fnOn g _ β' hg', map_zpow, hy, hy]
      exact h2 _ _⟩)
    exact ⟨w, fun a => by rw [← Category.assoc, hw, hy]⟩

end GlobalTheory.LevCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointsVanishingIdealRadicalHomogeneous
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.ThIdeal

theorem hasTh_unit_mul {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {S : Scheme.{0}} {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {R : Type} [CommRing R]
    {x : Sp R ⟶ S} {v : Ix g (N' ^ 2) → R} (h : t.HasTh x v) (c : R) (hc : IsUnit c) :
    t.HasTh x (fun a => c * v a) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, k1, k2, k3, k4, k5, k6, k7, k8⟩ := h3 p
  have hu : IsUnit (V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) :=
    (hc.map _).map _
  obtain ⟨u', hu'⟩ : ∃ u' : Γ((Out.overRes (T := Over.mk x) V).left, ⊤)ˣ,
      u'.val = V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := hu
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, u' * u, k1, k2, k3, k4, k5, k6, k7, fun i => ?_⟩
  have e := k8 i
  have e1 : V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c * v i)) =
      V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) *
        V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) := by
    rw [map_mul]
    exact map_mul _ _ _
  refine e1.trans ?_
  rw [Units.val_mul, _root_.mul_assoc, hu']
  exact congrArg (fun y => V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * y) e

theorem coeff_scale {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R') (w : σ → R')
    (F : MvPolynomial σ R) (e : ℕ) :
    (MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F).coeff e =
      MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial d c =>
    have hm : MvPolynomial.monomial d c ∈ MvPolynomial.homogeneousSubmodule σ R d.degree :=
      MvPolynomial.isHomogeneous_monomial c rfl
    rw [MvPolynomial.homogeneousComponent_of_mem hm]
    have : MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) (MvPolynomial.monomial d c) =
        Polynomial.C (MvPolynomial.eval₂Hom β w (MvPolynomial.monomial d c)) * Polynomial.X ^ d.degree := by
      simp only [MvPolynomial.eval₂Hom_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, RingHom.comp_apply, Finsupp.degree_apply]
      ring
    rw [this, Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add (f := _), Polynomial.coeff_add, hp, hq]

theorem component_eq_zero {R σ : Type} [CommRing R] (β : R →+* ℂ) (w : σ → ℂ)
    (F : MvPolynomial σ R) (e : ℕ)
    (h : ∀ c : ℂ, c ≠ 0 → MvPolynomial.eval₂Hom β (fun i => c * w i) F = 0) :
    MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) = 0 := by
  rw [← coeff_scale]
  have : MvPolynomial.eval₂Hom ((Polynomial.C : ℂ →+* Polynomial ℂ).comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := {0}ᶜ) (fun c hc => ?_) (Set.finite_singleton (0 : ℂ)).infinite_compl
    have h1 := MvPolynomial.map_eval₂Hom ((Polynomial.C : ℂ →+* Polynomial ℂ).comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) (Polynomial.evalRingHom c) F
    rw [Set.mem_ofPred_eq, Polynomial.IsRoot.def, ← Polynomial.coe_evalRingHom, h1, ← h c hc]
    congr 2
    · ext r; simp
    · ext i; simp [_root_.mul_comm c]
  rw [this, Polynomial.coeff_zero]

theorem mem_thIdeal {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} (em : o →+* ℂ)
    (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (F : MvPolynomial (Ix g (N' ^ 2)) o) :
    F ∈ thIdeal em C ↔ ∀ t v, C t → t.HasTh (𝟙 _) v → MvPolynomial.eval₂Hom em v F = 0 := by
  simp only [thIdeal, Ideal.mem_iInf, RingHom.mem_ker, and_imp]

theorem thIdeal_radical_homogeneous_torsionFree :
    ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop), Function.Injective em → (thIdeal em C).IsRadical ∧ (∀ F ∈ thIdeal em C, ∀ e, MvPolynomial.homogeneousComponent e F ∈ thIdeal em C) ∧ ∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ thIdeal em C → F ∈ thIdeal em C := by
  intro o _ g N' J b em C hem
  refine ⟨fun F hF => ?_, fun F hF e => ?_, fun c F hc hF => ?_⟩
  · obtain ⟨n, hn⟩ := hF
    rw [mem_thIdeal] at hn ⊢
    intro t v ht hv
    have := hn t v ht hv
    rw [map_pow] at this
    exact pow_eq_zero_iff'.mp this |>.1
  · rw [mem_thIdeal] at hF ⊢
    intro t v ht hv
    exact component_eq_zero em v F e fun c hc => hF t _ ht (hasTh_unit_mul hv c hc.isUnit)
  · rw [mem_thIdeal] at hF ⊢
    intro t v ht hv
    have := hF t v ht hv
    rw [map_mul, MvPolynomial.eval₂Hom_C] at this
    exact (mul_eq_zero.mp this).resolve_left ((map_ne_zero_iff em hem).mpr hc)

end GlobalTheory.ZM.ThIdeal
end

