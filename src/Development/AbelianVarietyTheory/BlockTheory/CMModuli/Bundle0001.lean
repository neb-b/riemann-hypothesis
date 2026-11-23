module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.HeckeIsogenyKernels
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def conjIdeal (H : Host E) (P : Ideal (𝓞 E)) : Ideal (𝓞 E) := P.map (H.bar : 𝓞 E →+* 𝓞 E)

def IsSplitPrimeOff (l : Level H) (p : ℕ) (P : Ideal (𝓞 E)) : Prop :=
  p.Prime ∧ P.IsMaximal ∧ (p : 𝓞 E) ∈ P ∧ conjIdeal H P ≠ P ∧ ¬ p ∣ l.M'

section Fibre

variable {k : Type} [Field k]

abbrev Pts (t : SAB H (Sp k)) : Type := 𝟙_ (Over (Sp k)) ⟶ t.G

def KilledBy (t : SAB H (Sp k)) (I : Ideal (𝓞 E)) (x : Pts t) : Prop :=
  ∀ a ∈ I, x ≫ t.act.act a = 1

def KilledByPow (t : SAB H (Sp k)) (I : Ideal (𝓞 E)) (x : Pts t) : Prop :=
  ∃ n : ℕ, KilledBy t (I ^ n) x

def IsHeckeDatum (t : SAB H (Sp k)) (P : Ideal (𝓞 E)) (i : ℕ) (C₀ : Subgroup (Pts t)) : Prop :=
  (∀ a, ∀ x ∈ C₀, x ≫ t.act.act a ∈ C₀) ∧ (∀ x ∈ C₀, KilledBy t (conjIdeal H P) x) ∧
    Finite C₀ ∧ Nat.card C₀ = Ideal.absNorm P ^ i

def heckeKernel (t : SAB H (Sp k)) (p : ℕ) (P : Ideal (𝓞 E)) (C₀ : Subgroup (Pts t)) : Set (Pts t) :=
  {x | ∃ x₁ x₂ x₃ : Pts t, x = x₁ * x₂ * x₃ ∧
    (x₁ ^ p = 1 ∧ ∃ a : 𝓞 E, a ∉ P ∧ a ∉ conjIdeal H P ∧ x₁ ≫ t.act.act a = 1) ∧
    (KilledByPow t (conjIdeal H P) x₂ ∧ x₂ ^ p ∈ C₀) ∧
    (x₃ ^ p = 1 ∧ KilledByPow t P x₃ ∧ ∀ c ∈ C₀, Out.WeilIs t.G t.PP.L (p : ℤ) x₃ c 1)}

end Fibre

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.RelativeGroupHatForm
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

def zhatSubring : Subring (∀ n : ℕ+, ZMod n) where
  carrier := {f | ∀ (m n : ℕ+) (h : (m : ℕ) ∣ n), ZMod.castHom h (ZMod m) (f n) = f m}
  mul_mem' {a b} ha hb m n h := by rw [Pi.mul_apply, map_mul, ha m n h, hb m n h, Pi.mul_apply]
  one_mem' m n h := by rw [Pi.one_apply, map_one, Pi.one_apply]
  add_mem' {a b} ha hb m n h := by rw [Pi.add_apply, map_add (f := _), ha m n h, hb m n h, Pi.add_apply]
  zero_mem' m n h := by rw [Pi.zero_apply, map_zero, Pi.zero_apply]
  neg_mem' {a} ha m n h := by rw [Pi.neg_apply, map_neg, ha m n h, Pi.neg_apply]

abbrev Zhat : Type := zhatSubring

def Zhat.red (n : ℕ+) : Zhat →+* ZMod n := (Pi.evalRingHom (fun m : ℕ+ => ZMod m) n).comp zhatSubring.subtype

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev Lhat (D : Datum H) : Type := Zhat ⊗[ℤ] D.La

def hatMul (D : Datum H) (c : 𝓞 E) : Lhat D →ₗ[Zhat] Lhat D :=
  (DistribSMul.toLinearMap ℤ D.La c).baseChange Zhat

def hatForm (D : Datum H) : LinearMap.BilinForm Zhat (Lhat D) := D.EF.baseChange Zhat

def hatSub (D : Datum H) (𝔞 : Ideal (𝓞 E)) : Submodule Zhat (Lhat D) :=
  Submodule.span Zhat ((fun a : D.La => (1 : Zhat) ⊗ₜ[ℤ] a) '' (𝔞 • (⊤ : Submodule (𝓞 E) D.La) : Submodule (𝓞 E) D.La))

def simGroup (D : Datum H) (l : Level H) : Subgroup (Lhat D ≃ₗ[Zhat] Lhat D) where
  carrier := {g | (∀ c x, g (hatMul D c x) = hatMul D c (g x)) ∧
    ∃ ν : Zhatˣ, Zhat.red ⟨l.A, l.A_pos⟩ ν = 1 ∧ ∀ x y, hatForm D (g x) (g y) = ν * hatForm D x y}
  mul_mem' := by
    rintro g h ⟨hg, ν, hν, eg⟩ ⟨hh, ν', hν', eh⟩
    refine ⟨fun c x => ?_, ν * ν', by rw [Units.val_mul, map_mul, hν, hν', _root_.mul_one], fun x y => ?_⟩
    · show g (h _) = hatMul D c (g (h x))
      rw [hh, hg]
    · show hatForm D (g (h x)) (g (h y)) = _
      rw [eg, eh, Units.val_mul, _root_.mul_assoc]
  one_mem' := ⟨fun _ _ => rfl, 1, map_one _, fun x y => by simp⟩
  inv_mem' := by
    rintro g ⟨hg, ν, hν, eg⟩
    refine ⟨fun c x => ?_, ν⁻¹, ?_, fun x y => ?_⟩
    · apply g.injective
      show g (g.symm _) = g (hatMul D c (g.symm x))
      rw [hg, g.apply_symm_apply, g.apply_symm_apply]
    · have := congrArg (Zhat.red ⟨l.A, l.A_pos⟩) ν.inv_mul
      rwa [map_mul, hν, _root_.mul_one, map_one] at this
    · have := eg (g.symm x) (g.symm y)
      rw [g.apply_symm_apply, g.apply_symm_apply] at this
      show hatForm D (g.symm x) (g.symm y) = _
      rw [this, Units.inv_mul_cancel_left]

def congSub (D : Datum H) (𝔞 : Ideal (𝓞 E)) : Subgroup (Lhat D ≃ₗ[Zhat] Lhat D) where
  carrier := {g | ∀ x, g x - x ∈ hatSub D 𝔞}
  mul_mem' {g h} hg hh x := by
    have := (hatSub D 𝔞).add_mem (hg (h x)) (hh x)
    rwa [sub_add_sub_cancel] at this
  one_mem' x := by simp
  inv_mem' {g} hg x := by
    have := (hatSub D 𝔞).neg_mem (hg (g.symm x))
    rwa [g.apply_symm_apply, neg_sub] at this

def trivAt (D : Datum H) (l : Level H) : Subgroup (Lhat D ≃ₗ[Zhat] Lhat D) :=
  congSub D l.Mb ⊓ congSub D (Ideal.span {(l.A : 𝓞 E)})

def relGroup (D : Datum H) (l l₂ : Level H) : Subgroup (Lhat D ≃ₗ[Zhat] Lhat D) := simGroup D l₂ ⊓ trivAt D l

theorem zeta_pow_div {m n : ℕ} (hn : 0 < n) (h : m ∣ n) : zeta n ^ (n / m) = zeta m := by
  obtain ⟨k, rfl⟩ := h
  have hm : 0 < m := Nat.pos_of_mul_pos_right hn
  have hk : 0 < k := Nat.pos_of_mul_pos_left hn
  rw [Nat.mul_div_cancel_left k hm]
  unfold zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  push_cast
  field_simp

theorem KA_le {l l₂ : Level H} (h : l.Dvd l₂) : KA l ≤ KA l₂ := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  rintro x (rfl | rfl)
  · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  · have hz : zeta l₂.A ∈ IntermediateField.adjoin ℚ ({H.rt0, zeta l₂.A} : Set ℂ) :=
      IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rw [SetLike.mem_coe, ← zeta_pow_div l₂.A_pos h.2.2]
    exact pow_mem hz _

def lowerCoeff {l l₂ : Level H} (h : l.Dvd l₂) (c : Coeff l₂) : Coeff l where
  F := c.F
  fin := c.fin
  conj := c.conj
  zeta_mem := by
    have hp : 0 < l₂.M' := Nat.lcm_pos (by have := l₂.three_le; omega) l₂.A_pos
    have hd : l.M' ∣ l₂.M' := Nat.lcm_dvd (h.1.trans (Nat.dvd_lcm_left _ _)) (h.2.2.trans (Nat.dvd_lcm_right _ _))
    rw [← zeta_pow_div hp hd]
    exact pow_mem c.zeta_mem _
  le := (KA_le h).trans c.le

variable {D : Datum H} {l l₂ : Level H}

def IsOver (h : l.Dvd l₂) (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (π : Xo₂.X ⟶ Xo.X) : Prop :=
  π ≫ Xo.s = Xo₂.s ≫ spMap (IntermediateField.inclusion (KA_le h)).toRingHom

def PullsBack (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (π : Xo₂.X ⟶ Xo.X) : Prop :=
  ∃ m : SABMap Xo₂.univ.t Xo.univ.t π,
    (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (Xo.univ.eta a).left) ∧
    (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (Xo.univ.etaA a).left)

def ChangesLevelBy (Xo : Moduli D l) (g : Lhat D ≃ₗ[Zhat] Lhat D) (r : Xo.X ⟶ Xo.X) : Prop :=
  ∃ m : SABMap Xo.univ.t Xo.univ.t r,
    (∀ a b : D.La, g (1 ⊗ₜ a) - 1 ⊗ₜ b ∈ hatSub D l.Mb →
      (Xo.univ.eta b).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧
    (∀ a b : D.La, g (1 ⊗ₜ a) - 1 ⊗ₜ b ∈ hatSub D (Ideal.span {(l.A : 𝓞 E)}) →
      (Xo.univ.etaA b).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)

theorem spMap_inclusion_comp {A B C : IntermediateField ℚ ℂ} (h₁ : A ≤ B) (h₂ : B ≤ C) :
    spMap (IntermediateField.inclusion h₂).toRingHom ≫ spMap (IntermediateField.inclusion h₁).toRingHom =
      spMap (IntermediateField.inclusion (h₁.trans h₂)).toRingHom := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

def levelMapF (h : l.Dvd l₂) {Xo : Moduli D l} {Xo₂ : Moduli D l₂} {π : Xo₂.X ⟶ Xo.X} (hπ : IsOver h Xo Xo₂ π)
    (c : Coeff l₂) : Xo₂.XF c ⟶ Xo.XF (lowerCoeff h c) :=
  pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by
    rw [Category.assoc, hπ, ← Category.assoc, pullback.condition, Category.assoc, spMap_inclusion_comp]
    rfl)

def endF {Xo : Moduli D l} (r : Xo.X ⟶ Xo.X) (hr : r ≫ Xo.s = Xo.s) (c : Coeff l) : Xo.XF c ⟶ Xo.XF c :=
  pullback.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by rw [Category.assoc, hr, pullback.condition])

def IsLevelCovering (h : l.Dvd l₂) {Xo : Moduli D l} {Xo₂ : Moduli D l₂} {π : Xo₂.X ⟶ Xo.X}
    (hπ : IsOver h Xo Xo₂ π) : Prop :=
  ∃ (ρ : relGroup D l l₂ → (Xo₂.X ≅ Xo₂.X)) (hρ : ∀ g, (ρ g).hom ≫ Xo₂.s = Xo₂.s),
    ρ 1 = Iso.refl _ ∧ (∀ g g', ρ (g * g') = ρ g ≪≫ ρ g') ∧
    (∀ g, ChangesLevelBy Xo₂ g.1 (ρ g).hom) ∧
    (∀ g, (ρ g).hom ≫ π = π) ∧
    ∀ c : Coeff l₂,
      IsFinite (levelMapF h hπ c) ∧ Etale (levelMapF h hπ c) ∧ Surjective (levelMapF h hπ c) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Xo₂.XF c),
        (∀ y : Sp k ⟶ Xo₂.XF c, y ≫ levelMapF h hπ c = x ≫ levelMapF h hπ c →
          ∃ g, x ≫ endF (ρ g).hom (hρ g) c = y) ∧
        ∀ g, x ≫ endF (ρ g).hom (hρ g) c = x ↔ g.1 ∈ trivAt D l₂

end GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.CMModuli.SiegelFamilyZetaUnit
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Triple

variable {S : Scheme.{0}}

def IsTrivial {X : Scheme.{0}} (L : LB X) : Prop := ∃ t : LB.Gen L, t.IsGen

def diagPull (A : Over S) (P : LB (A ⊗ A).left) : LB A.left := P.pull (lift (𝟙 A) (𝟙 A)).left

def IsSymmetricPair (h : ℕ) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) : Prop :=
  IsAbelianScheme A ∧ SmoothOfRelativeDimension h A.hom ∧ P.IsLB ∧
    IsTrivial (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) ∧
    IsTrivial (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) ∧
    LBIso P (P.pull (lift (snd A A) (fst A A)).left)

def slice (A : Over S) (P : LB (A ⊗ A).left) {T : Over S} (x : T ⟶ A) : LB (T ⊗ A).left :=
  P.pull (lift (fst T A ≫ x) (snd T A)).left

def IsPrincipal (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) : Prop :=
  Out.RelAmple A (diagPull A P) ∧ ∀ (T : Over S) (x : T ⟶ A), IsTrivial (slice A P x) → x = 1

abbrev Std (h M : ℕ) : Type := (Fin h → ZMod M) × (Fin h → ZMod M)

def stdForm {h M : ℕ} (a b : Std h M) : ZMod M := ∑ i, (a.1 i * b.2 i - a.2 i * b.1 i)

def IsLevel {h M : ℕ} (A : Over S) [GrpObj A] (lv : Std h M → (𝟙_ (Over S) ⟶ A)) : Prop :=
  (∀ a b, lv (a + b) = lv a * lv b) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      (Function.Injective fun a => toUnit (Over.mk x) ≫ lv a) ∧
      ∀ g : Over.mk x ⟶ A, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk x) ≫ lv a = g

def IsSymplectic {h M : ℕ} {R : Type} [CommRing R] (ζ : Rˣ) (s : S ⟶ Sp R) (A : Over S) [GrpObj A]
    (P : LB (A ⊗ A).left) (lv : Std h M → (𝟙_ (Over S) ⟶ A)) : Prop :=
  ∀ a b, Out.WeilIs A (diagPull A P) (M : ℤ) (lv a) (lv b)
    (Units.map ((𝟙_ (Over S)).hom ≫ s).appTop.hom.toMonoidHom (unitOn (ζ ^ (2 * stdForm a b).val)))

def IsPullbackTriple {h M : ℕ} {S' : Scheme.{0}} (A' : Over S') [GrpObj A'] (P' : LB (A' ⊗ A').left)
    (lv' : Std h M → (𝟙_ (Over S') ⟶ A')) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left)
    (lv : Std h M → (𝟙_ (Over S) ⟶ A)) (f : S' ⟶ S) : Prop :=
  ∃ (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left),
    IsGrpPullback A' A f φ ∧
    φ₂ ≫ (fst A A).left = (fst A' A').left ≫ φ ∧ φ₂ ≫ (snd A A).left = (snd A' A').left ≫ φ ∧
    LBIso P' (P.pull φ₂) ∧
    ∀ a, (lv' a).left ≫ φ = f ≫ (lv a).left

end Triple

end GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit
end
end

