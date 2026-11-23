module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0544
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitCoordsBalancedSymmetricRoots
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitForm

theorem exists_coords {O : Type} [CommRing O] [StarRing O] [IsDedekindDomain O]
    [Module.Finite ℤ O] [Module.Free ℤ O] {w : O} (hw : w + star w = 1)
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite ℤ X] [Module.Free ℤ X]
    {J : Type} [Fintype J] (ε : Module.Basis J ℤ (PolFan.balForms (star : O → O) X))
    {B : Type} [AddCommGroup B] (τ : Forms.balForms ℤ O X B) :
    ∃ c : J → B, ∀ a b, (τ : Forms.Bil X B) a b = ∑ k, (ε k : LinearMap.BilinForm ℤ X) a b • c k := by
  classical
  have := Forms.projective_of_int O X
  have := Forms.finite_balTensor (O := O) (X := X)
  have := Forms.free_balTensor (X := X) hw
  let e := Module.Free.chooseBasis ℤ ((TensorProduct ℤ X X) ⧸ Forms.balTensorRel (O := O) (X := X))
  have hm := Forms.balTensorMk_mem_balForms O X
  let β : _ → PolFan.balForms (star : O → O) X := fun j =>
    ⟨(Forms.balTensorMk O).compr₂ (e.coord j),
      fun y x => congrArg (e.coord j) (hm.1 y x), fun a y x => congrArg (e.coord j) (hm.2 a y x)⟩
  refine ⟨fun k => ∑ j, ε.repr (β j) k • Forms.balTensorLift τ (e j), fun a b => ?_⟩
  have h1 (j) : e.repr (Forms.balTensorMk O a b) j =
      ∑ k, ε.repr (β j) k * (ε k : LinearMap.BilinForm ℤ X) a b := by
    have h := congrArg (fun g : PolFan.balForms (star : O → O) X =>
      (g : LinearMap.BilinForm ℤ X) a b) (ε.sum_repr (β j))
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul] at h
    exact h.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Forms.balTensorLift_mk, ← e.sum_repr (Forms.balTensorMk O a b), map_sum]
  simp only [map_zsmul]
  simp only [h1, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [_root_.mul_comm]

theorem exists_root {V : Type} [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V]
    [IsAlgClosed (ResidueField V)] {n : ℕ} (hn : IsUnit (n : V)) (u : Vˣ) :
    ∃ v : Vˣ, v ^ n = u := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (residue V u) (Nat.pos_of_ne_zero hn0)
  obtain ⟨a, rfl⟩ := residue_surjective z
  have ha : IsUnit a := by
    rw [← residue_ne_zero_iff_isUnit]
    intro h
    rw [h, zero_pow hn0] at hz
    exact (residue_ne_zero_iff_isUnit _).2 u.isUnit hz.symm
  obtain ⟨y, hy, -⟩ := HenselianRing.is_henselian (R := V) (I := maximalIdeal V)
    (Polynomial.X ^ n - Polynomial.C (u : V)) (Polynomial.monic_X_pow_sub_C _ hn0) a
    (by
      rw [← residue_eq_zero_iff]
      simp [hz])
    (by
      refine IsUnit.map _ ?_
      simpa [Polynomial.derivative_X_pow] using ⟨hn, ha.pow _⟩)
  have hy' : y ^ n = u := by
    simpa [sub_eq_zero] using hy
  have hyu : IsUnit y := (isUnit_pow_iff hn0).1 (hy' ▸ u.isUnit)
  exact ⟨hyu.unit, Units.ext (by simpa using hy')⟩

theorem mem_of_diag {O : Type} [CommRing O] (bar : O → O) {w : O} (hw : w + bar w = 1)
    {X : Type} [AddCommGroup X] [Module O X] {G : Type} [CommGroup G] (U : Subgroup G)
    (q : X → X → G) (hs : ∀ a b, q a b = q b a) (ha : ∀ a a' b, q (a + a') b = q a b * q a' b)
    (hb : ∀ (x : O) a b, q (x • a) b = q a (bar x • b)) (hd : ∀ y, q y (w • y) ∈ U) (a b : X) :
    q a b ∈ U := by
  have hr (a b b') : q a (b + b') = q a b * q a b' := by rw [hs, ha, hs b, hs b']
  have h1 : q a (w • b) * q b (w • a) = q a b := by
    rw [hs b, hb, ← hr, ← add_smul, hw, one_smul]
  have h2 : q a b = q (a + b) (w • (a + b)) / (q a (w • a) * q b (w • b)) := by
    rw [smul_add, ha, hr, hr, ← h1, eq_div_iff_mul_eq']
    simp only [mul_comm, mul_left_comm, mul_assoc]
  rw [h2]
  exact U.div_mem (hd _) (U.mul_mem (hd _) (hd _))

theorem exists_unit_coords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → IsAlgClosed (ResidueField V) → ∀ n : ℕ, IsUnit (n : V) → ∀ (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms H.bar X)) (t : Fin m → V), (∀ i, t i ≠ 0) → ∀ q : X → X → (FractionRing V)ˣ, (∀ a b, q a b = q b a) → (∀ a a' b, q (a + a') b = q a b * q a' b) → (∀ (x : 𝓞 E) a b, q (x • a) b = q a (H.bar x • b)) → (∀ y, ∃ u : Vˣ, (q y (H.w0 • y) : FractionRing V) = algebraMap V _ u * ∏ i, algebraMap V (FractionRing V) (t i) ^ ((n : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ X) y (H.w0 • y))) → ∃ s : Fin m ⊕ Fin N → V, (∀ i, Associated (s (.inl i)) (t i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ ∀ a b, (q a b : FractionRing V) = ∏ k, algebraMap V (FractionRing V) (s k) ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ X) a b) := by
  intro E _ _ _ H X _ _ _ _ V _ _ _ hV hk n hn m N ε t ht q hs ha hb hd
  letI : StarRing (𝓞 E) :=
    { star := H.bar
      star_involutive := fun a => by
        apply Subtype.ext
        change ((H.bar (H.bar a) : 𝓞 E) : E) = a
        rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
      star_mul := fun a b => by rw [map_mul, _root_.mul_comm]
      star_add := fun a b => map_add H.bar a b }
  have hw : H.w0 + H.bar H.w0 = 1 := PullbackSections.CVA.cmHostUnit_add_conj_eq_one H
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective _ _
  let φ : Vˣ →* (FractionRing V)ˣ := Units.map (algebraMap V (FractionRing V) : V →* FractionRing V)
  have hφ : Function.Injective φ := Units.map_injective hinj
  let τ : Fin m → (FractionRing V)ˣ := fun i =>
    Units.mk0 (algebraMap V (FractionRing V) (t i)) (fun h => ht i (hinj (by rw [h, map_zero])))
  let M : X → X → (FractionRing V)ˣ := fun a b =>
    ∏ i, τ i ^ ((n : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ X) a b)
  have Ms (a b) : M a b = M b a := Finset.prod_congr rfl fun i _ => by rw [(ε (.inl i)).2.1 a b]
  have Ma (a a' b) : M (a + a') b = M a b * M a' b := by
    simp only [M, map_add (f := _), LinearMap.add_apply, mul_add, zpow_add, Finset.prod_mul_distrib]
  have Mb (x : 𝓞 E) (a b) : M (x • a) b = M a (H.bar x • b) :=
    Finset.prod_congr rfl fun i _ => by rw [(ε (.inl i)).2.2 x a b]
  have hmem := mem_of_diag H.bar hw φ.range (fun a b => q a b / M a b)
    (fun a b => by rw [hs, Ms]) (fun a a' b => by rw [ha, Ma, mul_div_mul_comm])
    (fun x a b => by rw [hb, Mb]) (fun y => by
      obtain ⟨u, hu⟩ := hd y
      refine ⟨u, ?_⟩
      rw [eq_div_iff_mul_eq']
      apply Units.ext
      rw [hu]
      simp [M, τ, φ])
  choose u hu using hmem
  have us (a b) : u a b = u b a := hφ (by rw [hu, hu, hs, Ms])
  have ua (a a' b) : u (a + a') b = u a b * u a' b :=
    hφ (by rw [map_mul, hu, hu, hu, ha, Ma, mul_div_mul_comm])
  have ub (x : 𝓞 E) (a b) : u (x • a) b = u a (H.bar x • b) := hφ (by rw [hu, hu, hb, Mb])
  have ur (a b b') : u a (b + b') = u a b * u a b' := by rw [us, ua, us b, us b']
  obtain ⟨c, hc⟩ := exists_coords (O := 𝓞 E) hw ε ⟨Forms.bilOfMul u ua ur, us, ub⟩
  choose v hv using fun k => exists_root hn (c k).toMul
  refine ⟨Sum.elim (fun i => t i * v (.inl i)) (fun j => v (.inr j)),
    fun i => ⟨(v (.inl i))⁻¹, by simp⟩, fun j => Units.isUnit _, fun a b => ?_⟩
  have h1 : u a b = ∏ k, v k ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ X) a b) := by
    have h := congrArg Additive.toMul (hc a b)
    simp only [toMul_sum, toMul_zsmul, ← hv] at h
    simp only [zpow_mul, zpow_natCast]
    exact h
  have h2 : q a b = M a b * φ (u a b) := by rw [hu, mul_div_cancel]
  rw [h2, h1]
  simp [M, τ, φ, Fintype.prod_sum_type, mul_zpow, Finset.prod_mul_distrib, _root_.mul_assoc]

end GlobalTheory.UnitForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitCentredClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UTraitCen

theorem exists_uTrait_cen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C)
    (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ →
    ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∃ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z),
      (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) ∧
        ξ (IsLocalRing.closedPoint T.V) = x := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hA x _
  have hU : (U₀ : Set M.Z).Nonempty := hA.1.ne
  obtain ⟨W, _, _, _, _, hc, a, ha, hg⟩ := GlobalTheory.Poinc.TraitCen.exists_cdvr M U₀ hU x
  have hr : Set.range (jK W ≫ a) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact hg t
  let ξ₀' : Sp (FractionRing W) ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (jK W ≫ a) hr
  have hξ₀' : ξ₀' ≫ U₀.ι = jK W ≫ a := IsOpenImmersion.lift_fac _ _ _
  have hB : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, inferInstance⟩
  obtain ⟨y, ⟨x', hx', hy'⟩, -⟩ := X₁.existsUnique_lies (ξ₀' ≫ out.u₀)
  obtain ⟨T, f, fK, -, hloc, -, hcomp, hy⟩ := GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c W hB inferInstance y
  refine ⟨T, spMap f ≫ a, ⟨spMap fK ≫ ξ₀', ?_, spMap fK ≫ x', ?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hξ₀', ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact hcomp r
  · rw [Category.assoc, hx', Category.assoc]
  · rw [hy, Category.assoc, hy']
  · have h : (spMap f) (closedPoint T.V) = closedPoint W := IsLocalRing.comap_closedPoint f
    show a ((spMap f) (closedPoint T.V)) = x
    rw [h, ha]

end GlobalTheory.UTraitCen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitFiniteExtensionClassicalPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.UTraitExtLab

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (p : ℕ) [Fact p.Prime] (y₁ : ratHull S.R →+* PadicAlgCl p) (T : UTrait Xo cf) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₁ ≫ u' = spMap ι ≫ T.y → ∃ (T' : UTrait Xo cf) (ι' : FractionRing T'.V →+* PadicAlgCl p) (yK : ratHull S.R →+* FractionRing T'.V) (e : T'.P.D.toPre.X ≃ₗ[𝓞 E] T.P.D.toPre.X) (k : ℕ), (∀ x, ‖ι' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T'.V (FractionRing T'.V))) ∧ ι'.comp yK = y₁ ∧ spMap yK ≫ u' = T'.y ∧ ‖ι (algebraMap T.V _ T.ϖ)‖ = ‖ι' (algebraMap T'.V _ T'.ϖ)‖ ^ k ∧ ∀ a b, T'.be a b = (k : ℤ) * T.be (e a) (e b) := by
  intro E _ _ _ H Dw l Xo cf o Ω _ _ _ _ S u' p _ y₁ T ι hι hy
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft (o := o) (Ω := Ω)
  haveI : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  haveI : Algebra.FiniteType ℤ S.R := Algebra.FiniteType.trans (S := o) inferInstance inferInstance
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  haveI hTc : IsAdicComplete (maximalIdeal T.V) T.V := T.cdvr.2.1
  haveI : CharZero T.V := T.cdvr.2.2
  have hQ := GlobalTheory.PadicUnitBall.padic_mem_range p T.V hTc ι hι
  obtain ⟨W, _, _, _, hWc, _, fV, fK, κ, hfV, hfVl, -, hfK, hκι, hκ, hy₀⟩ :=
    GlobalTheory.DvrFinExt.exists_finite_extension p T.V hTc ι hι hQ S.R (y₁.comp (toRat S.R))
  have hy₁ : ∀ a, y₁ a ∈ κ.range := fun a => by
    obtain ⟨n, hn, ha⟩ := mem_ratHull.1 a.2
    obtain ⟨x, hx⟩ := hy₀ ⟨_, ha⟩
    have h0 : (n : PadicAlgCl p) ≠ 0 := Int.cast_ne_zero.2 hn
    have h1 : toRat S.R ⟨_, ha⟩ = (n : ratHull S.R) * a := Subtype.ext rfl
    rw [RingHom.comp_apply, h1, map_mul, map_intCast] at hx
    refine ⟨(n : FractionRing W)⁻¹ * x, ?_⟩
    rw [map_mul, map_inv₀, map_intCast, hx, inv_mul_cancel_left₀ h0]
  have hbase : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hWc⟩, inferInstance⟩
  obtain ⟨T', f, gK, hf, hfl, hff, hgK, hTy⟩ :=
    GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo cf W hbase inferInstance (spMap fK ≫ T.y)
  haveI : IsDiscreteValuationRing T'.V := T'.cdvr.1
  haveI hTc' : IsAdicComplete (maximalIdeal T'.V) T'.V := T'.cdvr.2.1
  haveI : CharZero T'.V := T'.cdvr.2.2
  letI : Algebra (FractionRing W) (FractionRing T'.V) := gK.toAlgebra
  letI : Algebra W T'.V := f.toAlgebra
  haveI : Module.Finite W T'.V := hff
  haveI : Algebra.IsIntegral W T'.V := Algebra.IsIntegral.of_finite W T'.V
  haveI : IsLocalHom (algebraMap W T'.V) := hfl
  have hcomp : (algebraMap (FractionRing W) (FractionRing T'.V)).comp (algebraMap W (FractionRing W)) =
      (algebraMap T'.V (FractionRing T'.V)).comp (algebraMap W T'.V) := RingHom.ext hgK
  have hI : ∀ a : T'.V, _root_.IsIntegral (FractionRing W) (algebraMap T'.V (FractionRing T'.V) a) := fun a =>
    IsIntegral.map_of_comp_eq (algebraMap W (FractionRing W)) (algebraMap T'.V (FractionRing T'.V)) hcomp
      (Algebra.IsIntegral.isIntegral a)
  haveI : Algebra.IsAlgebraic (FractionRing W) (FractionRing T'.V) := ⟨fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := T'.V) x
    rw [div_eq_mul_inv]
    exact (hI a).isAlgebraic.mul (hI b).isAlgebraic.inv⟩
  letI : Algebra (FractionRing W) (PadicAlgCl p) := κ.toAlgebra
  let ιA : FractionRing T'.V →ₐ[FractionRing W] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let ι' : FractionRing T'.V →+* PadicAlgCl p := ιA
  have hι'κ : ι'.comp gK = κ := ιA.comp_algebraMap
  have hint := GlobalTheory.unitBall_eq_of_integral_dvr p W T'.V hf κ ι' (fun v => by
    show ι' (algebraMap T'.V (FractionRing T'.V) (f v)) = _
    rw [← hgK]
    exact congrArg (fun h : FractionRing W →+* PadicAlgCl p => h (algebraMap W (FractionRing W) v)) hι'κ) hκ
  have hιc : ι'.comp (gK.comp fK) = ι := by rw [← RingHom.comp_assoc, hι'κ, hκι]

  have hr : ∀ a, y₁ a ∈ ι'.range := fun a => by
    obtain ⟨x, hx⟩ := hy₁ a
    exact ⟨gK x, by rw [← hx, ← hι'κ]; rfl⟩
  let eι : FractionRing T'.V ≃+* ι'.range := RingEquiv.ofBijective ι'.rangeRestrict
    ⟨fun a b hab => ι'.injective (congrArg Subtype.val hab), ι'.rangeRestrict_surjective⟩
  let yK : ratHull S.R →+* FractionRing T'.V := eι.symm.toRingHom.comp (y₁.codRestrict ι'.range hr)
  have hyK : ι'.comp yK = y₁ := RingHom.ext fun a =>
    congrArg Subtype.val (eι.apply_symm_apply (y₁.codRestrict ι'.range hr a))

  have hne : f (fV T.ϖ) ≠ 0 := fun h => T.irr.ne_zero (hfV (hf (by rw [h, map_zero, map_zero])))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne T'.irr
  have hbase' : GlobalTheory.Mum.Base T'.V := ⟨⟨inferInstance, inferInstance, inferInstance, hTc'⟩, inferInstance⟩
  haveI : IsLocalHom (f.comp fV) := by
    haveI : IsLocalHom f := hfl
    haveI : IsLocalHom fV := hfVl
    exact RingHom.isLocalHom_comp f fV
  obtain ⟨e₀, he₀⟩ := GlobalTheory.UPoinc.uTraitUniqSt_holds E H Dw l Xo cf T T' T'.V (f.comp fV) (RingHom.id _) (gK.comp fK)
    (RingHom.id _) hbase' inferInstance (hf.comp hfV) Function.injective_id inferInstance inferInstance
    (fun a => by simp only [RingHom.comp_apply, hfK, hgK]) (fun a => rfl)
    (by
      rw [hTy, spMap_comp_ringHom, Category.assoc]
      rw [show spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _ from Spec.map_id _, Category.id_comp])
    T'.ϖ m 1 T'.irr hm (by rw [pow_one, RingHom.id_apply])
  refine ⟨T', ι', yK, e₀.symm, m, hint, hyK, ?_, ?_, ?_⟩
  · haveI : Epi (spMap ι') := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (spMap ι'), ← Category.assoc, ← spMap_comp_ringHom, hyK, hy, hTy, ← hιc, spMap_comp_ringHom,
      spMap_comp_ringHom, Category.assoc, Category.assoc]
  · obtain ⟨u, hu⟩ := hm
    have hunit : ∀ w : T'.Vˣ, ‖ι' (algebraMap T'.V _ (w : T'.V))‖ = 1 := fun w => by
      have h1 := (hint _).2 ⟨(w : T'.V), rfl⟩
      have h2 := (hint _).2 ⟨((w⁻¹ : T'.Vˣ) : T'.V), rfl⟩
      have h3 : ‖ι' (algebraMap T'.V _ (w : T'.V))‖ * ‖ι' (algebraMap T'.V _ ((w⁻¹ : T'.Vˣ) : T'.V))‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
      nlinarith [norm_nonneg (ι' (algebraMap T'.V _ (w : T'.V))),
        norm_nonneg (ι' (algebraMap T'.V _ ((w⁻¹ : T'.Vˣ) : T'.V)))]
    have e1 : ι (algebraMap T.V _ T.ϖ) = ι' (algebraMap T'.V _ (f (fV T.ϖ))) := by
      rw [← hιc, RingHom.comp_apply, RingHom.comp_apply, hfK, hgK]
    have e2 : f (fV T.ϖ) = T'.ϖ ^ m * ((u⁻¹ : T'.Vˣ) : T'.V) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [e1, e2, map_mul, map_mul, norm_mul, hunit, mul_one, map_pow, map_pow, norm_pow]
  · intro a b
    have h := he₀ (e₀.symm a) (e₀.symm b)
    simp only [LinearEquiv.apply_symm_apply, Nat.cast_one, one_mul] at h
    exact h.symm

end GlobalTheory.UTraitExtLab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitRamifiedExtensionFormMultiple
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.UPoinc

theorem mumBase_of_cdvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] : GlobalTheory.Mum.Base V :=
  ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩

theorem uTrait_ramExt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (T : GlobalTheory.UPoinc.UTrait Xo c) (n : ℕ), 0 < n →
    ∃ (T₂ : GlobalTheory.UPoinc.UTrait Xo c) (g : T.V →+* T₂.V) (gK : FractionRing T.V →+* FractionRing T₂.V)
      (e : T.P.D.toPre.X ≃ₗ[𝓞 E] T₂.P.D.toPre.X) (q : ℕ), Function.Injective g ∧ IsLocalHom g ∧
      (∀ a, gK (algebraMap T.V _ a) = algebraMap T₂.V _ (g a)) ∧ T₂.y = spMap gK ≫ T.y ∧ 0 < q ∧
      ∀ a b, T₂.be (e a) (e b) = ((n * q : ℕ) : ℤ) * T.be a b := by
  intro E _ _ _ H Dw l Xo c T n hn
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  haveI : IsAdicComplete (maximalIdeal T.V) T.V := T.cdvr.2.1
  haveI : CharZero T.V := T.cdvr.2.2
  let T0 : Formalism.L2.Pj.CDVR := { V := T.V }
  obtain ⟨T₁, g₁, κ, e₁, ϖ₁, hg₁, hl₁, hϖ₁, hκ, hne₁, hass₁⟩ :=
    GlobalTheory.ArcExt.exists_ramified_ext T0 (Ω := AlgebraicClosure T0.Fr) ⊥ n hn T.ϖ T.irr
  let gK₁ : FractionRing T.V →+* FractionRing T₁.V :=
    κ.comp (algebraMap T0.Fr (⊥ : IntermediateField T0.Fr (AlgebraicClosure T0.Fr)))
  have hgK₁ : ∀ a, gK₁ (algebraMap T.V _ a) = algebraMap T₁.V _ (g₁ a) := hκ
  haveI : IsAdicComplete (maximalIdeal T₁.V) T₁.V := T₁.cpl
  have hB₁ : GlobalTheory.Mum.Base T₁.V := mumBase_of_cdvr T₁.V
  obtain ⟨T₂, f, fK, hf, hfl, -, hfK, hy⟩ :=
    _root_.GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c T₁.V hB₁ inferInstance (spMap gK₁ ≫ T.y)
  haveI : IsDiscreteValuationRing T₂.V := T₂.cdvr.1
  haveI : IsAdicComplete (maximalIdeal T₂.V) T₂.V := T₂.cdvr.2.1
  haveI : CharZero T₂.V := T₂.cdvr.2.2

  have hfϖ0 : f ϖ₁ ≠ 0 := fun h => hϖ₁.ne_zero (hf (by rw [h, map_zero]))
  obtain ⟨e₂, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfϖ0 T₂.irr
  have he₂ : 0 < e₂ := by
    rcases Nat.eq_zero_or_pos e₂ with h | h
    · exfalso
      rw [h, pow_zero, mul_one] at hu
      exact hϖ₁.not_isUnit ((isUnit_map_iff f ϖ₁).1 (hu ▸ u.isUnit))
    · exact h
  have he₁ : 0 < e₁ := by
    rcases Nat.eq_zero_or_pos e₁ with h | h
    · exfalso
      rw [h, pow_zero] at hass₁
      exact T.irr.not_isUnit ((isUnit_map_iff g₁ T.ϖ).1 (associated_one_iff_isUnit.1 hass₁))
    · exact h
  have hassf : Associated (f ϖ₁) (T₂.ϖ ^ e₂) := ⟨u⁻¹, by rw [hu, mul_comm (u : T₂.V), mul_assoc, Units.mul_inv, mul_one]⟩
  have hass : Associated ((f.comp g₁) T.ϖ) (T₂.ϖ ^ (e₁ * e₂)) := by
    have h1 : Associated (f (g₁ T.ϖ)) (f ϖ₁ ^ e₁) := by
      rw [← map_pow]; exact hass₁.map f
    rw [mul_comm, pow_mul]
    exact h1.trans (hassf.pow_pow)
  have hyc : spMap (fK.comp gK₁) ≫ T.y = spMap (RingHom.id (FractionRing T₂.V)) ≫ T₂.y := by
    have hid : spMap (RingHom.id (FractionRing T₂.V)) = 𝟙 _ := by
      show Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [hy, hid, Category.id_comp, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp]; rfl
  have hcomp : ∀ a, (fK.comp gK₁) (algebraMap T.V _ a) = algebraMap T₂.V _ ((f.comp g₁) a) := fun a => by
    simp only [RingHom.comp_apply]
    rw [hgK₁, hfK]
  obtain ⟨e, he⟩ := _root_.GlobalTheory.UPoinc.uTraitUniqSt_holds E H Dw l Xo c T T₂ T₂.V (f.comp g₁) (RingHom.id T₂.V) (fK.comp gK₁)
    (RingHom.id _) (mumBase_of_cdvr T₂.V) inferInstance (hf.comp hg₁) Function.injective_id inferInstance
    inferInstance hcomp (fun _ => rfl) hyc T₂.ϖ (e₁ * e₂) 1 T₂.irr hass (by rw [pow_one]; rfl)
  obtain ⟨k, hk⟩ := hne₁
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk; omega
    · exact h
  refine ⟨T₂, f.comp g₁, fK.comp gK₁, e, k * e₂, hf.comp hg₁, inferInstance, hcomp, ?_, Nat.mul_pos hk0 he₂,
    fun a b => ?_⟩
  · rw [hy, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp]; rfl
  · have h := he a b
    rw [Nat.cast_one, one_mul] at h
    rw [← h, hk, mul_assoc]

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeMin
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart.Fam

open Classical

theorem finrank_le_min : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R,
    Module.finrank (𝓞 E) C.P.D.toPre.X ≤ min Dw.p Dw.q := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hB C
  obtain ⟨hadm, hch⟩ := hB
  haveI : IsNoetherianRing R := hadm.1
  haveI : CharZero R := hch
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := C.gen
  let K := AlgebraicClosure (FractionRing R)
  let g : FractionRing R →+* K := algebraMap (FractionRing R) K
  let f : R →+* K := g.comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Xo.X := spMap g ≫ C.y ≫ pullback.fst _ _
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective (x' ≫ Xo.s)
  have hβ : x' ≫ Xo.s = spMap β₀.hom := hβ₀.symm
  have hdet := (Xo.univ.geom K x' β₀.hom hβ).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hjK : spMap g ≫ jK R = spMap f := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Xo.univ.t.act x' τ N →
      Module.finrank (𝓞 E) C.P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₂.cart tK.act Xo.univ.t.act m₂.act (spMap g) τ N).2 hN
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₁.cart tK.act C.t.act m₁.act (spMap g) τ N).1 h₅
    rw [hjK] at h₆
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H R C.t C.P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

end GlobalTheory.UChart.Fam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GrpPullAb

theorem isAbelianScheme_of_grpPullback :
    ∀ {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
      (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → IsAbelianScheme G → IsAbelianScheme G' :=
  fun _ h hG => GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG h

end GlobalTheory.GrpPullAb
end

