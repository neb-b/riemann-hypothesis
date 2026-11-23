module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommRingCatIsPullbackFlatBaseChangeSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.MilFlat

open TensorProduct

theorem isPullback_iff_elem {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (i : C ⟶ D)
    (w : f ≫ h = g ≫ i) :
    IsPullback f g h i ↔ (∀ x y, f.hom x = f.hom y → g.hom x = g.hom y → x = y) ∧
      ∀ b c, h.hom b = i.hom c → ∃ a, f.hom a = b ∧ g.hom a = c := by
  constructor
  · intro H
    have H' := (Types.isPullback_iff _ _ _ _).1 (H.map (forget CommRingCat))
    exact ⟨fun x y hx hy ↦ H'.2.1 x y ⟨hx, hy⟩, fun b c hbc ↦ H'.2.2 b c hbc⟩
  · rintro ⟨h₁, h₂⟩
    refine IsPullback.of_map (forget CommRingCat) w ((Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩)
    · ext x
      simpa using congrArg (fun φ : A ⟶ D ↦ φ.hom x) w
    · exact fun x y hxy ↦ h₁ x y hxy.1 hxy.2
    · exact fun b c hbc ↦ h₂ b c hbc

theorem isoIsPushout_tmul {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    {X : CommRingCat.{0}} {f : CommRingCat.of A ⟶ X} {f' : CommRingCat.of B ⟶ X}
    (h : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R B)) f f') (a : A) (b : B) :
    ((CommRingCat.isPushout_tensorProduct R A B).isoIsPushout _ _ h).hom.hom (a ⊗ₜ b) = f.hom a * f'.hom b := by
  have e₁ := congrArg (fun φ ↦ φ.hom a)
    (IsPushout.inl_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct R A B) h)
  have e₂ := congrArg (fun φ ↦ φ.hom b)
    (IsPushout.inr_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct R A B) h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e₁ e₂
  have : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by simp
  rw [this, map_mul]
  simp only [Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply] at e₁ e₂
  exact congrArg₂ (· * ·) e₁ e₂

theorem isPullback_of_flat (P C₁ C₂ C₀ E E₁ E₂ E₀ : CommRingCat.{0}) (p₁ : P ⟶ C₁) (p₂ : P ⟶ C₂) (q₁ : C₁ ⟶ C₀)
    (q₂ : C₂ ⟶ C₀) (hP : IsPullback p₁ p₂ q₁ q₂) (hq : Function.Surjective q₂.hom) (g : P ⟶ E) (g₁ : C₁ ⟶ E₁)
    (g₂ : C₂ ⟶ E₂) (g₀ : C₀ ⟶ E₀) (i₁ : E ⟶ E₁) (i₂ : E ⟶ E₂) (r₁ : E₁ ⟶ E₀) (r₂ : E₂ ⟶ E₀) (hg : g.hom.Flat)
    (h₁ : IsPushout g p₁ i₁ g₁) (h₂ : IsPushout g p₂ i₂ g₂) (h₀ : IsPushout g₂ q₂ r₂ g₀)
    (w₁ : i₁ ≫ r₁ = i₂ ≫ r₂) (w₂ : g₁ ≫ r₁ = q₁ ≫ g₀) : IsPullback i₁ i₂ r₁ r₂ := by
  letI : Algebra P E := g.hom.toAlgebra
  letI : Algebra P C₁ := p₁.hom.toAlgebra
  letI : Algebra P C₂ := p₂.hom.toAlgebra
  letI : Algebra P C₀ := (p₂ ≫ q₂).hom.toAlgebra
  haveI : Module.Flat P E := hg
  have hw : ∀ a, q₁.hom (p₁.hom a) = q₂.hom (p₂.hom a) := fun a ↦ by
    simpa using congrArg (fun φ ↦ φ.hom a) hP.w
  have hw₁ : ∀ x, r₁.hom (i₁.hom x) = r₂.hom (i₂.hom x) := fun x ↦ by
    simpa using congrArg (fun φ ↦ φ.hom x) w₁
  have hw₂ : ∀ c, r₁.hom (g₁.hom c) = g₀.hom (q₁.hom c) := fun c ↦ by
    simpa using congrArg (fun φ ↦ φ.hom c) w₂
  have hw₀ : ∀ c, r₂.hom (g₂.hom c) = g₀.hom (q₂.hom c) := fun c ↦ by
    simpa using congrArg (fun φ ↦ φ.hom c) h₀.w
  obtain ⟨hinj, hex⟩ := (isPullback_iff_elem p₁ p₂ q₁ q₂ hP.w).1 hP

  let f : P →ₗ[P] C₁ × C₂ := (Algebra.linearMap P C₁).prod (Algebra.linearMap P C₂)
  let Q₁ : C₁ →ₗ[P] C₀ :=
    { toFun := q₁.hom, map_add' := map_add _
      map_smul' := fun a c ↦ by
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, hw] }
  let Q₂ : C₂ →ₗ[P] C₀ :=
    { toFun := q₂.hom, map_add' := map_add _
      map_smul' := fun a c ↦ by
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra] }
  let h : C₁ × C₂ →ₗ[P] C₀ := Q₁ ∘ₗ LinearMap.fst P C₁ C₂ - Q₂ ∘ₗ LinearMap.snd P C₁ C₂
  have hh : ∀ x y, h (x, y) = q₁.hom x - q₂.hom y := fun _ _ ↦ rfl
  have hf : ∀ a, f a = (p₁.hom a, p₂.hom a) := fun _ ↦ rfl
  have hfinj : Function.Injective f := fun a b hab ↦ by
    rw [hf, hf, Prod.ext_iff] at hab
    exact hinj a b hab.1 hab.2
  have hexact : Function.Exact f h := by
    rintro ⟨x, y⟩
    rw [hh, sub_eq_zero]
    constructor
    · intro hxy
      obtain ⟨a, ha₁, ha₂⟩ := hex x y hxy
      exact ⟨a, by rw [hf, ha₁, ha₂]⟩
    · rintro ⟨a, ha⟩
      rw [hf, Prod.mk.injEq] at ha
      rw [← ha.1, ← ha.2]
      exact hw a
  have hsurj : Function.Surjective h := fun z ↦ by
    obtain ⟨y, hy⟩ := hq (-z)
    exact ⟨(0, y), by rw [hh, hy]; simp⟩
  have hex' := lTensor_exact E hexact hsurj
  have hinj' := Module.Flat.lTensor_preserves_injective_linearMap (M := E) f hfinj

  have h₀' : IsPushout g (p₂ ≫ q₂) (i₂ ≫ r₂) g₀ := (h₂.flip.paste_horiz h₀.flip).flip
  let k₁ := (CommRingCat.isPushout_tensorProduct P E C₁).isoIsPushout _ _ h₁
  let k₂ := (CommRingCat.isPushout_tensorProduct P E C₂).isoIsPushout _ _ h₂
  let k₀ := (CommRingCat.isPushout_tensorProduct P E C₀).isoIsPushout _ _ h₀'
  have k₁t : ∀ (e : E) (c : C₁), k₁.hom.hom (e ⊗ₜ c) = i₁.hom e * g₁.hom c := isoIsPushout_tmul h₁
  have k₂t : ∀ (e : E) (c : C₂), k₂.hom.hom (e ⊗ₜ c) = i₂.hom e * g₂.hom c := isoIsPushout_tmul h₂
  have k₀t : ∀ (e : E) (c : C₀), k₀.hom.hom (e ⊗ₜ c) = r₂.hom (i₂.hom e) * g₀.hom c := isoIsPushout_tmul h₀'
  have kinv : ∀ {X Y : CommRingCat.{0}} (k : X ≅ Y) (y : Y), k.hom.hom (k.inv.hom y) = y := fun k y ↦ by simp
  have kinj : ∀ {X Y : CommRingCat.{0}} (k : X ≅ Y), Function.Injective k.hom.hom := fun k x y hxy ↦ by
    simpa using congrArg k.inv.hom hxy
  let pr := TensorProduct.prodRight P P E C₁ C₂
  have key : ∀ x, k₀.hom.hom (h.lTensor E x) =
      r₁.hom (k₁.hom.hom (pr x).1) - r₂.hom (k₂.hom.hom (pr x).2) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul e c =>
      obtain ⟨c₁, c₂⟩ := c
      rw [LinearMap.lTensor_tmul, hh, TensorProduct.prodRight_tmul, k₀t, k₁t, k₂t, map_mul, map_mul, hw₁, hw₂,
        hw₀, map_sub]
      ring
    | add x y hx hy =>
      simp only [map_add (f := _), Prod.fst_add, Prod.snd_add, hx, hy]
      ring
  have keyone : ∀ e : E, pr (f.lTensor E (e ⊗ₜ 1)) = (e ⊗ₜ 1, e ⊗ₜ 1) := fun e ↦ by
    rw [LinearMap.lTensor_tmul, hf, map_one, map_one, TensorProduct.prodRight_tmul]
  have k₁one : ∀ e, k₁.hom.hom (e ⊗ₜ 1) = i₁.hom e := fun e ↦ by rw [k₁t, map_one, _root_.mul_one]
  have k₂one : ∀ e, k₂.hom.hom (e ⊗ₜ 1) = i₂.hom e := fun e ↦ by rw [k₂t, map_one, _root_.mul_one]
  refine (isPullback_iff_elem i₁ i₂ r₁ r₂ w₁).2 ⟨fun x y hx hy ↦ ?_, fun a b hab ↦ ?_⟩
  · have : f.lTensor E (x ⊗ₜ 1) = f.lTensor E (y ⊗ₜ 1) := by
      apply pr.injective
      rw [keyone, keyone, Prod.mk.injEq]
      exact ⟨kinj k₁ (by rw [k₁one, k₁one, hx]), kinj k₂ (by rw [k₂one, k₂one, hy])⟩
    simpa using congrArg (TensorProduct.rid P E) (hinj' this)
  · obtain ⟨x, hxd⟩ : ∃ x, pr x = (k₁.inv.hom a, k₂.inv.hom b) := ⟨pr.symm _, pr.apply_symm_apply _⟩
    have hx0 : h.lTensor E x = 0 := by
      apply kinj k₀
      rw [key, map_zero, hxd, kinv, kinv, hab, sub_self]
    obtain ⟨y, hy⟩ := (hex' x).1 hx0
    have hy' : y = (TensorProduct.rid P E y) ⊗ₜ 1 := by
      rw [← TensorProduct.rid_symm_apply, LinearEquiv.symm_apply_apply]
    rw [hy'] at hy
    have e₁ := congrArg (fun z ↦ k₁.hom.hom (pr z).1) hy
    have e₂ := congrArg (fun z ↦ k₂.hom.hom (pr z).2) hy
    simp only [keyone, k₁one, k₂one, hxd, kinv] at e₁ e₂
    exact ⟨_, e₁, e₂⟩

end GlobalTheory.MilFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingHeckePointsPowEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

theorem eta_nsmul {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {M : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b M s) (y : D.La) (m : ℕ) : o.eta (m • y) = o.eta y ^ m := by
  induction m with
  | zero => rw [zero_smul, pow_zero, eta_zero]
  | succ m ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem weilIs_heckeSub_pow_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ u : Γ((𝟙_ (Over S)).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) u → u ^ k = 1 := by
  intro p _ D R _ b g c k N _ _ _ _ _ _ _ S s o h₁ hh₁ h₂ _ u hu
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hA : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have hL : (lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  obtain ⟨x, rfl⟩ := hh₁
  have hk1 : o.eta (N • g x) ^ k = 1 := by
    rw [← eta_nsmul, smul_smul, Nat.mul_comm k N]; exact o.eta_ker _
  have hxk : (lift (o.eta (N • g x)) 1 : 𝟙_ (Over S) ⟶ G2 o.A) ^ k = 1 := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [MonObj.pow_comp]; simp [hk1]
    · rw [MonObj.pow_comp]; simp
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk, pow_zero]
  have pw : ∀ m : ℕ, Out.WeilIs (G2 o.A) (lbPow o.P (k ^ 2 / c)) 1
      ((lift (o.eta (N • g x)) 1 : 𝟙_ (Over S) ⟶ G2 o.A) ^ (m + 1)) (lift 1 h₂) (u ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hu
    | succ m ih =>
      rw [pow_succ _ (m + 1), pow_succ u (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL ih hu
  have hp := pw (k - 1)
  rw [Nat.sub_add_cancel hk, hxk] at hp
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL hp hp
  rw [_root_.mul_one] at h11
  exact mul_eq_left.1 (GlobalTheory.CommutatorPairing.weilIs_unique hG hA hL h11 hp)

end GlobalTheory.UPel.HT.Hecke
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingHeckeTranslateEqZeta
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.HeckeWeilValue

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem lbIso_mulA_diag (hA : IsAbelianScheme A) {P : LB (G2 A).left} (hP : P.IsLB)
    (hamp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left))
    (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) (k : ℕ) :
    LBIso (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) (k ^ 2))
      ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull (Out.mulA A k).left) := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A), DiagPairing.pc hP (x * x') y =
      DiagPairing.pc hP x y + DiagPairing.pc hP x' y := fun T x x' y => by
    obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP h₁ h₂ T x x' y).1
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    unfold DiagPairing.pc
    rw [← sub_eq_zero, ← e]
    abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A), DiagPairing.pc hP x (y * y') =
      DiagPairing.pc hP x y + DiagPairing.pc hP x y' := fun T x y y' => by
    obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP h₁ h₂ T y y' x).2
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    unfold DiagPairing.pc
    rw [← sub_eq_zero, ← e]
    abel
  refine (cls_eq_iff (LB.isLB_linComb hD _ _) (pull_isLB hD _)).1 ?_
  rw [cls_lbPow hD, cls_pull hD, cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
  have e1 : pull (lift (Out.mulA A k) (Out.mulA A k)).left (cls P hP) =
      DiagPairing.pc hP (Out.mulA A k) (Out.mulA A k) := rfl
  have e2 : pull (lift (𝟙 A) (𝟙 A)).left (cls P hP) = DiagPairing.pc hP (𝟙 A) (𝟙 A) := rfl
  rw [e1, e2, Out.mulA, DiagPairing.pc_pow_left hP hB, DiagPairing.pc_pow_right hP hB', smul_smul, sq]

end GlobalTheory.HeckeWeilValue


open GlobalTheory.HeckeWeilValue in
theorem GlobalTheory.UPel.HT.Hecke.weil_value_translate : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k M : ℕ), c.Coprime p → k.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∀ (I : TateIsoO D κ (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))) (n : ℕ), 0 < n → n.Coprime p → ∀ (u v : D.La) (e : (Γ((Over.mk x).left, ⊤))ˣ), Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) ((n * (k ^ 2 / c) : ℕ) : ℤ) (I.ev (n * k) (g u)) (I.ev (n * k) (g v)) e → e = unitOn (I.ζ n ^ (2 * D.EF u v)) := by
  intro p _ D R _ b g c k M hc hk hEF _ hck S s o κ _ _ x β _ I n hn hnp u v e he
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hk0 : 0 < k := levelPos_of_coprime hk
  have hc0 : 0 < c := levelPos_of_coprime hc
  have hmc : k ^ 2 / c * c = k ^ 2 := Nat.div_mul_cancel hck
  have hm0 : 0 < k ^ 2 / c := Nat.div_pos (Nat.le_of_dvd (by positivity) hck) hc0
  have hmp : (k ^ 2 / c).Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro c hmc) (Nat.Coprime.pow_left 2 hk)
  set m := k ^ 2 / c with hm
  have hN : 0 < n * (m * k ^ 2) := by positivity
  have hNp : (n * (m * k ^ 2)).Coprime p :=
    Nat.Coprime.mul_left hnp (Nat.Coprime.mul_left hmp (Nat.Coprime.pow_left 2 hk))
  have eN : n * (m * k ^ 2) = n * k * (m * k) := by ring
  have hev : ∀ w : D.La, I.ev (n * k) (g w) = I.ev (n * (m * k ^ 2)) (m • g w) ≫ Out.mulA o.A k := fun w => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id, ← TateIsoO.ev_nsmul, smul_smul, mul_comm k m,
      TateIsoO.ev_nsmul, eN, I.tower (n * k) (m * k) (by positivity) (by positivity) (by rw [← eN]; exact hNp)]
  letI : IsCommMonObj o.A := o.ab.comm
  haveI : IsMonHom (Out.mulA o.A k) := by
    change IsMonHom ((𝟙 o.A) ^ k)
    constructor
    · rw [MonObj.comp_pow, Category.comp_id, MonObj.one_eq_one, one_pow]
    · rw [MonObj.comp_pow, Category.comp_id, MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst,
        tensorHom_snd, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, mul_pow]
  have hw := lbIso_mulA_diag o.ab o.isLB o.ample o.rig₁ o.rig₂ k
  rw [hev u, hev v] at he
  have h1 := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG o.ab hL hL (Out.mulA o.A k) hw he
  have h2 := I.isom (n * (m * k ^ 2)) hN hNp (m • g u) (m • g v)
  have eZ : ((n * m : ℕ) : ℤ) * ((k ^ 2 : ℕ) : ℤ) = ((n * (m * k ^ 2) : ℕ) : ℤ) := by push_cast; ring
  rw [eZ] at h1
  rw [GlobalTheory.CommutatorPairing.weilIs_unique hG o.ab hL h1 h2]
  congr 1
  have eF : D.EF (m • g u) (m • g v) = ((m * k ^ 2 : ℕ) : ℤ) * D.EF u v := by
    simp only [map_nsmul, LinearMap.smul_apply, hEF, nsmul_eq_mul]
    rw [← hmc]
    push_cast
    ring
  rw [eF, show (2 : ℤ) * (((m * k ^ 2 : ℕ) : ℤ) * D.EF u v) = ((m * k ^ 2 : ℕ) : ℤ) * (2 * D.EF u v) by ring,
    zpow_mul, zpow_natCast, I.ζ_pow n (m * k ^ 2) hn (by positivity) hNp]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingPullbackPowerMapLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HeckePullLevel

open GlobalTheory.CechPic

theorem isMonHom_id_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    IsMonHom ((𝟙 G) ^ n : G ⟶ G) := by
  induction n with
  | zero => rw [pow_zero, Hom.one_def]; infer_instance
  | succ n ih => rw [pow_succ, Hom.mul_def]; infer_instance

theorem weilIs_powPull : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (H₀ : LB A.left) (P : LB (G2 A).left), IsAbelianScheme A → H₀.IsLB → Out.RelAmple A H₀ → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (m a b : ℕ) (n : ℤ) (T : Over S) (x₁ x₂ y₁ y₂ : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) (GlobalTheory.UPel.HT.Hecke.lbPow P m) n (lift (x₁ ^ a) (x₂ ^ b)) (lift (y₁ ^ a) (y₂ ^ b)) c → Out.WeilIs (G2 A) P (n * ((m * a * b : ℕ) : ℤ)) (lift x₁ x₂) (lift y₁ y₂) c := by
  intro S A _ _ H₀ P hA hH hamp hP h₁ h₂ m a b n T x₁ x₂ y₁ y₂ c h
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A),
      DiagPairing.pc hP (x * x') y = DiagPairing.pc hP x y + DiagPairing.pc hP x' y := fun T x x' y => by
    obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A H₀ hA hH hamp P hP h₁ h₂ T x x' y).1
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    unfold DiagPairing.pc
    rw [← sub_eq_zero, ← e]
    abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A),
      DiagPairing.pc hP x (y * y') = DiagPairing.pc hP x y + DiagPairing.pc hP x y' := fun T x y y' => by
    obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A H₀ hA hH hamp P hP h₁ h₂ T y y' x).2
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    unfold DiagPairing.pc
    rw [← sub_eq_zero, ← e]
    abel
  haveI := isMonHom_id_pow A a
  haveI := isMonHom_id_pow A b
  let ψ : G2 A ⟶ G2 A := lift (fst A A ≫ (𝟙 A) ^ a) (snd A A ≫ (𝟙 A) ^ b)
  have e : ∀ {T : Over S} (u v : T ⟶ A), lift u v ≫ ψ = lift (u ^ a) (v ^ b) := fun u v => by
    simp only [ψ, comp_lift, ← Category.assoc, MonObj.comp_pow, Category.comp_id, lift_fst, lift_snd]
  have hM : (GlobalTheory.UPel.HT.Hecke.lbPow P m).IsLB := LB.isLB_linComb hP _ _
  have hψ : pull ψ.left (cls P hP) = (a * b) • cls P hP := by
    have e₀ : ψ = lift (fst A A ^ a) (snd A A ^ b) := by
      rw [← e (fst A A) (snd A A), lift_fst_snd, Category.id_comp]
    rw [e₀]
    change DiagPairing.pc hP (fst A A ^ a) (snd A A ^ b) = _
    rw [DiagPairing.pc_pow_left hP hB, DiagPairing.pc_pow_right hP hB', DiagPairing.pc, lift_fst_snd,
      Over.id_left, pull_id, smul_smul, mul_comm]
  have hw : LBIso (lbPow P (m * a * b)) ((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull ψ.left) := by
    refine (cls_eq_iff (LB.isLB_linComb hP _ _) (pull_isLB hM _)).1 ?_
    have hc : cls _ hM = m • cls P hP := by
      refine (cls_linComb hP (K := Fin m) (fun _ => 𝟙 (G2 A).left) (fun _ => 1) hM).trans ?_
      simp only [pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [cls_lbPow hP, cls_pull hM, hc, map_nsmul, hψ, smul_smul]
    congr 1
    ring
  have h' : Out.WeilIs (G2 A) (GlobalTheory.UPel.HT.Hecke.lbPow P m) n (lift x₁ x₂ ≫ ψ) (lift y₁ y₂ ≫ ψ) c := by
    rw [e, e]; exact h
  exact WeilIsogeny.weilIs_pull_hom hG hAA hP hM ψ hw h'

end GlobalTheory.HeckePullLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateDividesOnNonzeroLocusSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.ThetaDiv

theorem resG_top_injective {X : Scheme.{0}} {W : X.Opens} (hW : ⊤ ≤ W) :
    Function.Injective (resG X (le_top : W ≤ ⊤)) := by
  obtain rfl : W = ⊤ := top_le_iff.1 hW
  intro x y h
  have e : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (Opposite.op (⊤ : X.Opens)) := rfl
  simpa only [resG, e, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply] using h

theorem div_of_mem_nonzeroLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : ZH.RatModel o Ω) (δ : LB M.Z) {I : Type} (t : I → δ.Sec) (th : I → Ω), δ.IsLB → ZM.SecCoord δ t M.pt th → ∀ (a : I) (z : M.Z), z ∈ nonzeroLocus (t a) → M.Div th a z := by
  intro o Ω _ _ _ M δ I t th _ hsc a z hz
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have hDU : M.Z.basicOpen ((t a).f k) ≤ δ.U k := M.Z.basicOpen_le _
  have hD : ((M.Z.basicOpen ((t a).f k) : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hk⟩
  have hptD := M.top_le_preimage_pt hD
  have hptU : ⊤ ≤ M.pt ⁻¹ᵁ δ.U k := fun x hx => hDU (hptD hx)
  obtain ⟨τ, -, hτ⟩ := hsc
  let j : PUnit → δ.ι := fun _ => k
  have hj : (δ.pull M.pt).U j ≤ M.pt ⁻¹ᵁ δ.U (j PUnit.unit) := LB.wchart_le δ _ j PUnit.unit
  have hW : ⊤ ≤ (δ.pull M.pt).U j := fun x _ => Set.mem_iInter.2 fun _ => hptU (x := x) trivial
  have inj := resG_top_injective hW
  let e := Scheme.ΓSpecIso (CommRingCat.of Ω)
  have hc : ∀ b, resG (Sp Ω) (le_top : (δ.pull M.pt).U j ≤ ⊤) ((M.pt.appLE (δ.U k) ⊤ hptU).hom ((t b).f k)) =
      resG (Sp Ω) le_top (e.inv.hom (th b)) * (τ.s j).val := by
    intro b
    rw [← hτ b j hj]
    show (M.pt.appLE _ ⊤ hptU ≫ (Sp Ω).presheaf.map (homOfLE le_top).op).hom _ = _
    rw [Scheme.Hom.appLE_map]
  have hv : ∀ b, valF M.pt (δ.U k) ((t b).f k) = e.hom.hom ((M.pt.appLE (δ.U k) ⊤ hptU).hom ((t b).f k)) :=
    fun b => dif_pos hptU
  have hei : ∀ x : Ω, e.hom.hom (e.inv.hom x) = x := fun x => by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  have key : ∀ b, valF M.pt (δ.U k) ((t b).f k) * th a = valF M.pt (δ.U k) ((t a).f k) * th b := by
    intro b
    have h1 : (M.pt.appLE (δ.U k) ⊤ hptU).hom ((t b).f k) * e.inv.hom (th a) =
        (M.pt.appLE (δ.U k) ⊤ hptU).hom ((t a).f k) * e.inv.hom (th b) := by
      apply inj
      rw [map_mul, map_mul, hc b, hc a]
      ring
    have h2 := congrArg e.hom.hom h1
    rwa [map_mul, map_mul, hei, hei, ← hv, ← hv] at h2
  have hua : valF M.pt (δ.U k) ((t a).f k) ≠ 0 :=
    ((GlobalTheory.Points.le_preimage_basicOpen_iff M.pt hptU ((t a).f k)).1 hptD).ne_zero
  have hth : th a ≠ 0 := by
    intro h0
    apply hua
    rw [hv]
    have h1 := hc a
    rw [h0, map_zero, map_zero, zero_mul] at h1
    rw [inj (h1.trans (map_zero _).symm), map_zero]
  refine ⟨hth, fun b => ?_⟩
  have hu : IsUnit (resG M.Z hDU ((t a).f k)) :=
    RingedSpace.isUnit_res_basicOpen M.Z.toLocallyRingedSpace.toRingedSpace ((t a).f k)
  have hval : valF M.pt _ (resG M.Z hDU ((t b).f k) * ((hu.unit⁻¹ : (Γ(M.Z, M.Z.basicOpen ((t a).f k)))ˣ) : Γ(M.Z, M.Z.basicOpen ((t a).f k)))) = th b / th a := by
    rw [← ZH.RatModel.res_apply M _ hD, map_mul, map_units_inv, IsUnit.unit_spec, ZH.RatModel.res_resG,
      ZH.RatModel.res_resG, ZH.RatModel.res_apply, ZH.RatModel.res_apply]
    field_simp
    linear_combination key b
  exact hval ▸ ZH.RatModel.valF_mem_O hk _

end GlobalTheory.ThetaDiv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalIdentityStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_scaling_local_identity : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∃ cd : GlobalTheory.DblScal.UD σ W.J → ℂ, GlobalTheory.DblScal.IsShapeD omd t c ιd cd := by
  first | exact @GlobalTheory.DblShape.shape_dbl | exact GlobalTheory.DblShape.shape_dbl | (intros; apply GlobalTheory.DblShape.shape_dbl <;> assumption)
end

