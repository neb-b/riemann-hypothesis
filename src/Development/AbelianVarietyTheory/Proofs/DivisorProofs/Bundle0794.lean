module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
public import Formalism.PolynomialDimension.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDescentSymmetricLinearisedBundle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0784
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOrbitProjectorEigen
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory

theorem freeOrbit_projector_eigen : ∀ (K V G C : Type) [Field K] [AddCommGroup V] [Module K V] [Group G] [Fintype G] [Fintype C] [MulAction G C] (e : C → V →ₗ[K] V) (ρ : Representation K G V) (χ : G →* Kˣ), (∀ (g : G) (Z : C), g • Z = Z → g = 1) → (∀ Z v, e Z (e Z v) = e Z v) → (∀ Z Z' v, Z ≠ Z' → e Z (e Z' v) = 0) → (∀ v, ∑ Z, e Z v = v) → (∀ g Z v, ρ g (e Z v) = e (g • Z) (ρ g v)) → ∃ O : Finset C, (∀ Z, ∃ g : G, ∃ o ∈ O, Z = g • o) ∧ (∀ F, (∀ g, ρ g F = (χ g : K) • F) → F = ∑ o ∈ O, ∑ g, ((χ g)⁻¹ : Kˣ) • ρ g (e o F)) ∧ ∀ f : C → V, (∀ o, e o (f o) = f o) → (∀ h, ρ h (∑ o ∈ O, ∑ g, ((χ g)⁻¹ : Kˣ) • ρ g (f o)) = (χ h : K) • ∑ o ∈ O, ∑ g, ((χ g)⁻¹ : Kˣ) • ρ g (f o)) ∧ ∀ g, ∀ o ∈ O, e (g • o) (∑ o' ∈ O, ∑ g', ((χ g')⁻¹ : Kˣ) • ρ g' (f o')) = ((χ g)⁻¹ : Kˣ) • ρ g (f o) := by
  intro K V G C _ _ _ _ _ _ _ e ρ χ hfree hidem horth hsum1 hequi
  classical
  let O : Finset C := Finset.univ.image (fun Z : C => (Quotient.mk (MulAction.orbitRel G C) Z).out)
  have hq : ∀ (g : G) (x : C), Quotient.mk (MulAction.orbitRel G C) (g • x) = Quotient.mk (MulAction.orbitRel G C) x :=
    fun g x => Quotient.sound (MulAction.mem_orbit x g)
  have hinj : ∀ (g : G) (o : C) (g' : G) (o' : C), o ∈ O → o' ∈ O → g • o = g' • o' → g = g' ∧ o = o' := by
    intro g o g' o' ho ho' h
    obtain ⟨Z1, -, rfl⟩ := Finset.mem_image.1 ho
    obtain ⟨Z2, -, rfl⟩ := Finset.mem_image.1 ho'
    have hZ : Quotient.mk (MulAction.orbitRel G C) Z1 = Quotient.mk (MulAction.orbitRel G C) Z2 := by
      calc Quotient.mk (MulAction.orbitRel G C) Z1
          = Quotient.mk (MulAction.orbitRel G C) (Quotient.mk (MulAction.orbitRel G C) Z1).out := (Quotient.out_eq _).symm
        _ = Quotient.mk (MulAction.orbitRel G C) (g • (Quotient.mk (MulAction.orbitRel G C) Z1).out) := (hq g _).symm
        _ = Quotient.mk (MulAction.orbitRel G C) (g' • (Quotient.mk (MulAction.orbitRel G C) Z2).out) := by rw [h]
        _ = Quotient.mk (MulAction.orbitRel G C) (Quotient.mk (MulAction.orbitRel G C) Z2).out := hq g' _
        _ = Quotient.mk (MulAction.orbitRel G C) Z2 := Quotient.out_eq _
    rw [hZ] at h ⊢
    refine ⟨?_, rfl⟩
    have h2 : (g'⁻¹ * g) • (Quotient.mk (MulAction.orbitRel G C) Z2).out = (Quotient.mk (MulAction.orbitRel G C) Z2).out := by
      rw [mul_smul, h, inv_smul_smul]
    have := hfree _ _ h2
    rw [inv_mul_eq_one] at this
    exact this.symm
  have hsurj : ∀ Z, ∃ g : G, ∃ o ∈ O, Z = g • o := by
    intro Z
    have hm : (Quotient.mk (MulAction.orbitRel G C) Z).out ∈ MulAction.orbit G Z := @Quotient.mk_out _ (MulAction.orbitRel G C) Z
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hm
    exact ⟨g⁻¹, _, Finset.mem_image_of_mem _ (Finset.mem_univ Z), by rw [← hg, inv_smul_smul]⟩
  have hsum : ∀ φ : C → V, ∑ Z, φ Z = ∑ o ∈ O, ∑ g : G, φ (g • o) := by
    intro φ
    rw [← Finset.sum_product (s := O) (t := Finset.univ) (f := fun x : C × G => φ (x.2 • x.1))]
    symm
    refine Finset.sum_bij (fun x _ => x.2 • x.1) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
    · rintro ⟨o, g⟩ h ⟨o', g'⟩ h' he
      simp only [Finset.mem_product] at h h'
      obtain ⟨h1, h2⟩ := hinj g o g' o' h.1 h'.1 he
      simp [h1, h2]
    · intro Z _
      obtain ⟨g, o, ho, rfl⟩ := hsurj Z
      exact ⟨(o, g), Finset.mem_product.2 ⟨ho, Finset.mem_univ _⟩, rfl⟩
  refine ⟨O, hsurj, ?_, ?_⟩
  · intro F hF
    conv_lhs => rw [← hsum1 F, hsum (fun Z => e Z F)]
    refine Finset.sum_congr rfl (fun o _ => Finset.sum_congr rfl (fun g _ => ?_))
    rw [hequi, hF, LinearMap.map_smul, ← Units.smul_def, inv_smul_smul]
  · intro f hf
    refine ⟨?_, ?_⟩
    · intro h
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun o _ => ?_)
      refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => ?_)
      simp only [Equiv.coe_mulLeft]
      rw [Units.smul_def, Units.smul_def, LinearMap.map_smul, map_mul, map_mul, Module.End.mul_apply, smul_smul]
      congr 1
      rw [← Units.val_mul]
      congr 1
      rw [mul_inv_rev, mul_comm, mul_assoc, inv_mul_cancel, mul_one]
    · intro g o ho
      have key : ∀ o' ∈ O, ∀ g', e (g • o) (((χ g')⁻¹ : Kˣ) • ρ g' (f o')) =
          if g' = g ∧ o' = o then ((χ g)⁻¹ : Kˣ) • ρ g (f o) else 0 := by
        intro o' ho' g'
        have hw : ρ g' (f o') = e (g' • o') (ρ g' (f o')) := by rw [← hequi g' o' (f o'), hf o']
        split_ifs with hc
        · obtain ⟨rfl, rfl⟩ := hc
          rw [Units.smul_def, LinearMap.map_smul]
          congr 1
          rw [hw, hidem]
        · rw [Units.smul_def, LinearMap.map_smul, hw, horth, smul_zero]
          intro hZ
          obtain ⟨h1, h2⟩ := hinj g o g' o' ho ho' hZ
          exact hc ⟨h1.symm, h2.symm⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single_of_mem o ho]
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Fintype.sum_eq_single g]
        · rw [key o ho g, if_pos ⟨rfl, rfl⟩]
        · intro g' hg'
          rw [key o ho g', if_neg (fun h => hg' h.1)]
      · intro o' ho' hne
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_eq_zero (fun g' _ => ?_)
        rw [key o' ho' g', if_neg (fun h => hne h.2)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpSchemeMonHomSquareLiftOneRight
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke.PullInj

variable {X Y Z : Scheme.{0}}

theorem gen_germ {L : LB X} {w : LB.Gen L} (hw : w.IsGen) (r : Z ⟶ X) (z : Z) {k l : L.ι}
    (hk : r z ∈ L.U k) (hl : r z ∈ L.U l) :
    gm r z _ (w.s k) = gm r z (L.U k ⊓ L.U l) (L.g k l) * gm r z _ (w.s l) := by
  have hm : r z ∈ L.U k ⊓ L.U l := ⟨hk, hl⟩
  exact (gm_res r z inf_le_left hm _).symm.trans ((congrArg (gm r z _) (hw k l)).trans
    ((map_mul _ _ _).trans (congrArg _ (gm_res r z inf_le_right hm _))))

theorem gm_pull_g (Q : LB Y) (F : X ⟶ Y) (r : Z ⟶ X) (z : Z) {j j' : PUnit → Q.ι}
    (hj : F (r z) ∈ Q.U (j PUnit.unit)) (hj' : F (r z) ∈ Q.U (j' PUnit.unit)) :
    gm r z ((Q.pull F).U j ⊓ (Q.pull F).U j') ((Q.pull F).g j j') =
      gm (r ≫ F) z (Q.U (j PUnit.unit) ⊓ Q.U (j' PUnit.unit)) (Q.g (j PUnit.unit) (j' PUnit.unit)) := by
  have hp : r z ∈ (Q.pull F).U j ⊓ (Q.pull F).U j' := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm r z _ (∏ _k : PUnit, (res _ (pullU F _ (Q.g _ _))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res r z _ hp _).trans (gm_pull r F z (Q.U (j PUnit.unit) ⊓ Q.U (j' PUnit.unit)) ⟨hj, hj'⟩ _)

theorem germ_div_g (M L : LB X) (r : Z ⟶ X) (z : Z) {p q : M.ι × L.ι}
    (hp : r z ∈ (LB.div M L).U p) (hq : r z ∈ (LB.div M L).U q) :
    gm r z _ ((LB.div M L).g p q) =
      gm r z (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) * (gm r z (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ := by
  have hm : r z ∈ (LB.div M L).U p ⊓ (LB.div M L).U q := ⟨hp, hq⟩
  show gm r z _ (res _ (M.g _ _) * (res _ (L.g _ _))⁻¹) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _) ((map_inv _ _).trans (congrArg _ (gm_res r z _ hm _))))

theorem mem_divPull {Q₁ Q₂ : LB Y} {F : X ⟶ Y} {x : X} {k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)} :
    x ∈ (LB.div (Q₂.pull F) (Q₁.pull F)).U k ↔ F x ∈ Q₂.U (k.1 PUnit.unit) ∧ F x ∈ Q₁.U (k.2 PUnit.unit) :=
  ⟨fun h => ⟨mem_pull.1 h.1, mem_pull.1 h.2⟩, fun h => ⟨mem_pull.2 h.1, mem_pull.2 h.2⟩⟩

theorem gm_top_eq {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (g : Γ(A.left, ⊤)ˣ)
    (r r' : Z ⟶ A.left) (e : r ≫ A.hom = r' ≫ A.hom) (z : Z) : gm r z ⊤ g = gm r' z ⊤ g := by
  obtain ⟨c, hc⟩ := (GlobalTheory.globalFns_holds S A hA).2 g.val
  have h1 : ∀ r₀ : Z ⟶ A.left, gs r₀ z ⊤ g.val = gs (r₀ ≫ A.hom) z ⊤ c := fun r₀ => by
    rw [← hc]; exact gs_pull r₀ A.hom z ⊤ trivial c
  apply Units.ext
  rw [← gs_unit r z ⊤ trivial, ← gs_unit r' z ⊤ trivial, h1, h1, e]

end GlobalTheory.UPel.HT.Hecke.PullInj

namespace GlobalTheory.UPel.HT.Hecke.PullInj

variable {S : Scheme.{0}}

theorem transl_axis₁ (A : Over S) [GrpObj A] [IsCommMonObj A] (h : 𝟙_ (Over S) ⟶ A) :
    lift (1 : A ⟶ A) (𝟙 A) ≫ transl (lift (1 : 𝟙_ (Over S) ⟶ A) h : 𝟙_ (Over S) ⟶ G2 A) =
      transl h ≫ lift (1 : A ⟶ A) (𝟙 A) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]

theorem transl_axis₂ (A : Over S) [GrpObj A] [IsCommMonObj A] (h : 𝟙_ (Over S) ⟶ A) :
    lift (𝟙 A) (1 : A ⟶ A) ≫ transl (lift h (1 : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S) ⟶ G2 A) =
      transl h ≫ lift (𝟙 A) (1 : A ⟶ A) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]
  · simp [transl, MonObj.mul_comp, MonObj.comp_mul]

theorem grpScheme_monHom_square_lift_one_left {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A')
    [IsMonHom ψ] : lift (1 : A ⟶ A) (𝟙 A) ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) = ψ ≫ lift (1 : A' ⟶ A') (𝟙 A') := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp

theorem grpScheme_monHom_square_lift_one_right {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A')
    [IsMonHom ψ] : lift (𝟙 A) (1 : A ⟶ A) ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) = ψ ≫ lift (𝟙 A') (1 : A' ⟶ A') := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp

end GlobalTheory.UPel.HT.Hecke.PullInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionAtIffKottwitzModuleCondi
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

noncomputable section

namespace GlobalTheory.UPel.HT.LieLin

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {S : Scheme.{0}}
  {A : Over S} [GrpObj A] [IsCommMonObj A] {R' : Type} [CommRing R'] (x : Sp R' ⟶ S)

theorem spMap_comp_spMap_lieAt {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₂ →+* R₃)
    (g : R₁ →+* R₂) : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem tanScal_iff_lieAt (act : OActN D.O A) (c : 𝓞 D.F) (r : R') (v : epsPtR x ⟶ A) :
    IsTanScal act x (algebraMap (𝓞 D.F) D.O c) r v ↔
      (smT x 0 v = 1 ∧ v ≫ (act.toF D).act c = smT x r v) := by
  have e0 : epsMul (0 : R') = (algebraMap R' (DualNumber R')).comp (TrivSqZeroExt.fstHom R' R' R').toRingHom := by
    ext r <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  have e1 : ((1 : epsPtR x ⟶ A).left) = spMap (algebraMap R' (DualNumber R')) ≫ (1 : Over.mk x ⟶ A).left := by
    rw [Hom.one_def, Hom.one_def]; rfl
  have e2 : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    rw [spMap_comp_spMap_lieAt]
    have : (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (algebraMap R' (DualNumber R')) = RingHom.id R' := by
      ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]
    exact Spec.map_id _
  have t1 : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left ↔
      smT x 0 v = 1 := by
    constructor
    · intro hp
      apply Over.OverMorphism.ext
      rw [smT_left, e1, e0, ← spMap_comp_spMap_lieAt, Category.assoc, hp]
    · intro hp
      have := congrArg (fun V => spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ V.left) hp
      rw [e1, ← Category.assoc, e2, Category.id_comp, smT_left, e0, ← spMap_comp_spMap_lieAt,
        ← Category.assoc, ← Category.assoc, e2, Category.id_comp] at this
      exact this
  have t2 : (v ≫ act.act (algebraMap (𝓞 D.F) D.O c)).left = spMap (epsScaleR r) ≫ v.left ↔
      v ≫ (act.toF D).act c = smT x r v := by
    constructor
    · intro h
      apply Over.OverMorphism.ext
      rw [smT_left]
      exact h
    · intro h
      have := congrArg (fun V => V.left) h
      rw [smT_left] at this
      exact this
  unfold IsTanScal
  rw [t1, t2]

theorem tv_sum_lieAt {κ : Type} (s : Finset κ) (f : κ → TanM x A) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tv_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, tv_add, ih]

theorem eig_iff_lieAt (act : OActN D.O A) (c : 𝓞 D.F) (r : R') (u : TanM x A) :
    ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := x) (S := R') (act.toF D) c u = r • u ↔
      tv u ≫ (act.toF D).act c = smT x r (tv u) := by
  constructor
  · intro h
    have := congrArg tv h
    rw [tv_actR, tv_smul] at this
    exact this
  · intro h
    apply tanM_ext
    rw [tv_actR, tv_smul]
    exact h

end

theorem lieAt_iff_lieMod : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0})
  (A : Over S) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (R' : Type) [CommRing R'] (β : R →+* R')
  (x : Sp R' ⟶ S),
    LieAt b act β x ↔
      LieMod (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := x) (S := R') (act.toF D)) D.ω (β b.ρ) (fun i => β.comp (b.t i)) := by
  intro p _ D R _ b S A _ _ act R' _ β x
  constructor
  · intro h v hv
    have hv' := (eig_iff_lieAt x act D.ω (β b.ρ) v).1 hv
    obtain ⟨w, hw, hsum⟩ := h (tv v) ((tanScal_iff_lieAt x act D.ω (β b.ρ) (tv v)).2 ⟨tv_mem v, hv'⟩)
    have h0 : ∀ i, smT x 0 (w i) = 1 := fun i => ((tanScal_iff_lieAt x act 0 _ (w i)).1 (hw i 0)).1
    refine ⟨fun i => mkT (w i) (h0 i), fun i => ?_, ?_⟩
    · rw [mem_eigSub]
      intro c
      exact (eig_iff_lieAt x act c _ _).2 ((tanScal_iff_lieAt x act c _ (w i)).1 (hw i c)).2
    · apply tanM_ext
      rw [hsum, tv_sum_lieAt, List.prod_ofFn]
      rfl
  · intro h v hv
    obtain ⟨h0, hω⟩ := (tanScal_iff_lieAt x act D.ω (β b.ρ) v).1 hv
    obtain ⟨w, hw, hsum⟩ := h (mkT v h0) ((eig_iff_lieAt x act D.ω (β b.ρ) (mkT v h0)).2 hω)
    refine ⟨fun i => tv (w i), fun i c => ?_, ?_⟩
    · exact (tanScal_iff_lieAt x act c _ (tv (w i))).2 ⟨tv_mem _, (eig_iff_lieAt x act c _ (w i)).1 ((mem_eigSub.1 (hw i)) c)⟩
    · have := congrArg tv hsum
      rw [tv_mkT, tv_sum_lieAt] at this
      rw [List.prod_ofFn]
      exact this

end GlobalTheory.UPel.HT.LieLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtInverseThetaTransformHeisenbergOnePara
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

theorem continuous_heisV_snd {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (u : VA F N) (g : VA F N → ℂ) (hg : Continuous g)
    (x : Fin N → AF F) : Continuous fun y : Fin N → AF F => heisV ψ u g (x, y) := by
  unfold heisV symV
  have h1 : Continuous fun y : Fin N → AF F => (x, y).1 ⬝ᵥ u.2 - u.1 ⬝ᵥ (x, y).2 := by
    simp only [dotProduct]
    fun_prop
  refine (hψ.comp (continuous_const.mul h1)).mul (hg.comp ?_)
  fun_prop

theorem heisV_zero {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ) (g : VA F N → ℂ) : heisV ψ 0 g = g := by
  funext w
  simp [heisV, symV, AddChar.map_zero_eq_one]

open GlobalTheory.GaugeEx in
theorem hasDerivAt_invV_heisV : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ (f f' : VA F N → ℂ) (C : ℝ), Continuous f → Continuous f' → (∀ w, ‖f w‖ ≤ C) → (∀ w, ‖f' w‖ ≤ C) → ∀ M : ℝ →+ VA F N, Continuous M → (∀ w s, HasDerivAt (fun t : ℝ => heisV ψ (M t) f w) (heisV ψ (M s) f' w) s) → ∀ x, HasDerivAt (fun t : ℝ => invV ψ ν 𝓓 (heisV ψ (M t) f) x) (invV ψ ν 𝓓 f' x) 0 := by
  intro F _ _ N _ ψ lam ν hC 𝓓 _ h1 f f' C hf hf' hfC hf'C M _ hM x
  have hψ := hC.2.1
  haveI : IsFiniteMeasure ((muV N ν).restrict 𝓓) := isFiniteMeasure_restrict.2 (by rw [h1]; simp)
  have hcont : ∀ (u : VA F N) (g : VA F N → ℂ), Continuous g →
      Continuous fun y : Fin N → AF F => heisV ψ u g (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) := by
    intro u g hg
    refine (continuous_heisV_snd ψ hψ.1 u g hg x).mul (hψ.1.comp ?_)
    simp only [dotProduct]
    fun_prop
  have hnorm : ∀ (u : VA F N) (g : VA F N → ℂ), (∀ w, ‖g w‖ ≤ C) → ∀ y : Fin N → AF F,
      ‖heisV ψ u g (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y)))‖ ≤ C := by
    intro u g hg y
    simp only [heisV, norm_mul, hψ.2.1, one_mul, mul_one]
    exact hg _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (muV N ν).restrict 𝓓)
    (F := fun t y => heisV ψ (M t) f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))))
    (F' := fun t y => heisV ψ (M t) f' (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))))
    (x₀ := (0 : ℝ)) (bound := fun _ => C) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hcont _ f hf).aestronglyMeasurable)
    (Integrable.of_bound (hcont _ f hf).aestronglyMeasurable C (Filter.Eventually.of_forall (hnorm _ f hfC)))
    (hcont _ f' hf').aestronglyMeasurable
    (ae_of_all _ fun y t _ => hnorm _ f' hf'C y)
    (integrable_const C)
    (ae_of_all _ fun y t _ => (hM (x, y) t).mul_const _)
  have e : (fun y => heisV ψ (M 0) f' (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y)))) =
      fun y => f' (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) := by
    rw [map_zero, heisV_zero]
  have k2 := key.2
  simp only [e] at k2
  exact k2

end GlobalTheory.ThetaTransform
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrandPeriodic
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.GaugeEx
open scoped Matrix Pointwise

namespace GlobalTheory.ThetaTransform

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}

theorem integrand_periodic {f : VA F N → ℂ} (hf : QuasiV ψ f) (x y : Fin N → AF F) (b : Fin N → F) :
    f (x, rat b + y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ (rat b + y)))) = f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) := by
  have h0 : (rat (0 : Fin N → F) : Fin N → AF F) = 0 := by funext l; simp [rat]
  have h := hf 0 b (x, y)
  rw [h0, Prod.mk_add_mk, zero_add] at h
  rw [h, mul_right_comm, ← AddChar.map_add_eq_mul, mul_comm]
  congr 2
  simp only [symV, dotProduct_add, zero_dotProduct]
  ring

theorem invV_heisV_fst (ν : Measure (AF F)) (𝓓 : Set (Fin N → AF F)) (f : VA F N → ℂ) (u x : Fin N → AF F) :
    invV ψ ν 𝓓 (heisV ψ (u, 0) f) x = invV ψ ν 𝓓 f (x + u) := by
  unfold invV
  congr 1
  funext y
  rw [heisV, mul_right_comm, ← AddChar.map_add_eq_mul, mul_comm, Prod.mk_add_mk, add_zero]
  congr 2
  simp only [symV, add_dotProduct, dotProduct_zero]
  ring

theorem invV_heisV_snd {ν : Measure (AF F)} (hν : IsCov1 ν) {𝓓 : Set (Fin N → AF F)}
    (hD : IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν)) {f : VA F N → ℂ} (hf : QuasiV ψ f) (u x : Fin N → AF F) :
    invV ψ ν 𝓓 (heisV ψ (0, u) f) x = ψ (x ⬝ᵥ u) * invV ψ ν 𝓓 f x := by
  obtain ⟨hH, hmem, -, -, -⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hν
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable (ratSub F N) := by
    refine Set.Countable.to_subtype ((Set.countable_range (rat : (Fin N → F) → (Fin N → AF F))).mono fun v hv => ?_)
    obtain ⟨ξ, h⟩ := (hmem v).1 hv
    exact ⟨ξ, h.symm⟩
  let P : (Fin N → AF F) → ℂ := fun y => f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y)))
  have hP : ∀ (g : ratSub F N) (y : Fin N → AF F), P (g +ᵥ y) = P y := by
    rintro ⟨g, hg⟩ y
    obtain ⟨ξ, rfl⟩ := (hmem g).1 hg
    exact integrand_periodic hf x y ξ
  have e1 : invV ψ ν 𝓓 (heisV ψ (0, u) f) x = ψ (x ⬝ᵥ u) * ∫ y in 𝓓, P (y + u) ∂(muV N ν) := by
    unfold invV
    rw [← integral_const_mul]
    congr 1
    funext y
    simp only [heisV, P, Prod.mk_add_mk, add_zero]
    rw [mul_right_comm, ← AddChar.map_add_eq_mul, mul_left_comm, ← AddChar.map_add_eq_mul, mul_comm]
    congr 2
    simp only [symV, dotProduct_add, zero_dotProduct]
    linear_combination two_mul_invOf (x ⬝ᵥ u)
  rw [e1]
  congr 1
  have hmp : MeasurePreserving (fun y : Fin N → AF F => y + u) (muV N ν) (muV N ν) := measurePreserving_add_right _ u
  have hemb : MeasurableEmbedding (fun y : Fin N → AF F => y + u) := measurableEmbedding_addRight u
  have hD' : IsAddFundamentalDomain (ratSub F N) (u +ᵥ 𝓓) (muV N ν) := hD.vadd_of_comm u
  have e2 : 𝓓 = (fun y : Fin N → AF F => y + u) ⁻¹' (u +ᵥ 𝓓) := by
    ext y
    rw [Set.mem_preimage, add_comm]
    exact Set.vadd_mem_vadd_set_iff.symm
  conv_lhs => rw [e2]
  rw [hmp.setIntegral_preimage_emb hemb P]
  exact hD'.setIntegral_eq hD hP

end GlobalTheory.ThetaTransform

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KronIdentity
section
namespace GlobalTheory.KroneckerIdentity

theorem kron_identity {T : Type} [Fintype T] [DecidableEq T] {J : T → Type}
    [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)] {R : Type} [CommRing R] :
    (GlobalTheory.DefPt.kron fun (t : T) ↦ (1 : Matrix (J t) (J t) R))
      = (1 : Matrix ((t : T) → J t) ((t : T) → J t) R) := by
  ext I I'
  simp only [GlobalTheory.DefPt.kron, Matrix.of_apply, Matrix.one_apply]
  by_cases h : I = I'
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨t, ht⟩ : ∃ t, I t ≠ I' t := not_forall.mp fun hc => h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)

end GlobalTheory.KroneckerIdentity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresPowEightMulStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prodDerivWeierstrassPOverSquares_pow_eight_mul : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ^ 8 * (p : ℂ) ^ 6 = (latticeCurve L).Δ ^ (p - 1) := by
  first | exact @GlobalTheory.CMModel.sqProd_pow_eight_mul | exact GlobalTheory.CMModel.sqProd_pow_eight_mul | (intros; apply GlobalTheory.CMModel.sqProd_pow_eight_mul <;> assumption)
end

