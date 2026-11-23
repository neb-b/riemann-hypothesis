module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointAddSqZeroEqProdMulTangent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueCoord
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilChart

open SqZero

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B]

def augAlg (R : Type) [CommRing R] {B : Type} [CommRing B] [Algebra R B] (I : Ideal B) : Subalgebra R (R × B) :=
  AlgHom.equalizer ((Ideal.Quotient.mkₐ R I).comp (AlgHom.snd R R B))
    ((Ideal.Quotient.mkₐ R I).comp ((Algebra.ofId R B).comp (AlgHom.fst R R B)))

theorem mem_augAlg {I : Ideal B} {b : R × B} : b ∈ augAlg R I ↔ b.2 - algebraMap R B b.1 ∈ I :=
  Ideal.Quotient.eq

theorem mk_comp_eq {κ : Type} {m : ℕ} {I : Ideal B} (ψ : JetR R κ m →ₐ[R] B) (h : ∀ j, ψ (zR m j) ∈ I) :
    (Ideal.Quotient.mkₐ R I).comp ψ = (Algebra.ofId R _).comp (jetAug R κ m) :=
  jet_ext fun j => by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, jetAug_zR, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h j)

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) {d : ℕ}
  {v : Fin d → (epsR R ⟶ G)} (hv : IsLieBasis v) {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G}
  (hx₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
  (hx₂ : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
  (hx₃ : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)

include hG hv hx₁ hx₂ hx₃

theorem move {I J : Ideal B} (hJ : J * I = ⊥) (hle : J ≤ I) {m : ℕ} (ψ ψ' : JetR R (Fin d) m →ₐ[R] B)
    (hψ : ∀ j, ψ (zR m j) ∈ I) (c : Fin d → B) (hcJ : ∀ j, c j ∈ J) (hc : ∀ j, c j * c j = 0)
    (h : ∀ j, ψ' (zR m j) = ψ (zR m j) + c j) : spMap ψ' ≫ x m = lieExp v c hc * (spMap ψ ≫ x m) := by
  have hψ' : ∀ j, ψ' (zR m j) ∈ I := fun j => by rw [h]; exact add_mem (hψ j) (hle (hcJ j))
  let aug : augAlg R I →ₐ[R] R := (AlgHom.fst R R B).comp (augAlg R I).val
  let p : augAlg R I →ₐ[R] B := (AlgHom.snd R R B).comp (augAlg R I).val
  let up : ∀ φ : JetR R (Fin d) m →ₐ[R] B, (∀ j, φ (zR m j) ∈ I) → (JetR R (Fin d) m →ₐ[R] augAlg R I) :=
    fun φ hφ => ((jetAug R (Fin d) m).prod φ).codRestrict _ fun a => by
      have := AlgHom.congr_fun (mk_comp_eq φ hφ) a
      exact this
  let J' : Ideal (augAlg R I) := J.comap p ⊓ RingHom.ker aug
  have hker : ∀ a : augAlg R I, a ∈ RingHom.ker aug → p a ∈ I := fun a ha => by
    have h1 : a.1.1 = 0 := ha
    have h2 := mem_augAlg.1 a.2
    rw [h1, map_zero, sub_zero] at h2
    exact h2
  have hJ' : J' * RingHom.ker aug = ⊥ := by
    rw [← le_bot_iff, Ideal.mul_le]
    intro a ha b hb
    have h1 : a.1.1 = 0 := ha.2
    have h2 : p a * p b ∈ J * I := Ideal.mul_mem_mul ha.1 (hker b hb)
    rw [hJ] at h2
    exact Subtype.ext (Prod.ext (show a.1.1 * b.1.1 = 0 by rw [h1, zero_mul]) h2)
  let c' : Fin d → augAlg R I := fun j => ⟨(0, c j), mem_augAlg.2 (by simpa using hle (hcJ j))⟩
  have hc' : ∀ j, c' j * c' j = 0 := fun j => Subtype.ext (Prod.ext (mul_zero _) (hc j))
  have he : ∀ j, epsTo R (c' j) (hc' j) (TrivSqZeroExt.inr 1) = c' j := fun j => epsTo_eps _ _
  have key := jet_add_sqZero_eq_prod_mul R G hG d v hv x hx₁ hx₂ hx₃ _ aug J' hJ' inf_le_right m
    (up ψ hψ) (up ψ' hψ') rfl rfl (fun j => epsTo R (c' j) (hc' j))
    (fun j => by rw [he]; exact ⟨hcJ j, rfl⟩)
    (fun j => by
      rw [he]
      exact Subtype.ext (Prod.ext (add_zero _).symm (h j)))
  have fin := congrArg (spMap p ≫ ·) key
  change spMap p ≫ spMap _ ≫ x m = spMap p ≫ (lieExp v c' hc' * (spMap _ ≫ x m)) at fin
  rw [MonObj.comp_mul, comp_lieExp, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp] at fin
  exact fin

theorem eq_of_sub_mem {I J : Ideal B} (hJ : J * I = ⊥) (hle : J ≤ I) {m : ℕ} (ψ ψ' : JetR R (Fin d) m →ₐ[R] B)
    (hψ : ∀ j, ψ (zR m j) ∈ I) (hδ : ∀ j, ψ' (zR m j) - ψ (zR m j) ∈ J)
    (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  have hJ2 : J ^ 2 = ⊥ := by
    rw [← le_bot_iff, pow_two, ← hJ]
    exact Ideal.mul_mono_right hle
  let c : Fin d → J := fun j => ⟨_, hδ j⟩
  have hc : ∀ j, (c j : B) * (c j : B) = 0 := fun j => mul_eq_zero_of_sq hJ2 (c j).2 (c j).2
  have key := move hG hv hx₁ hx₂ hx₃ hJ hle ψ ψ' hψ (fun j => c j) (fun j => (c j).2) hc
    (fun j => (add_sub_cancel _ _).symm)
  rw [← h] at key
  have h1 : lieExp v (fun j => (c j : B)) hc = 1 := mul_eq_right.1 key.symm
  have h0 : c = 0 := by
    apply (expHom_bijective hv hJ2).1
    rw [map_zero]
    exact congrArg Additive.ofMul (Subtype.ext h1)
  refine jet_ext fun j => ?_
  have : ψ' (zR m j) - ψ (zR m j) = 0 := congrArg Subtype.val (congrFun h0 j)
  exact (sub_eq_zero.1 this).symm

theorem eq_of_nil {N : Ideal B} (hN : IsNilpotent N) {m : ℕ} (ψ ψ' : JetR R (Fin d) m →ₐ[R] B)
    (hψ : ∀ j, ψ (zR m j) ∈ N) (hψ' : ∀ j, ψ' (zR m j) ∈ N)
    (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  have main : ∀ k j, ψ' (zR m j) - ψ (zR m j) ∈ N ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro j
      rw [zero_add, pow_one]
      exact sub_mem (hψ' j) (hψ j)
    | succ k ih =>
      let q : B →ₐ[R] B ⧸ N ^ (k + 1 + 1) := Ideal.Quotient.mkₐ R _
      have e := eq_of_sub_mem hG hv hx₁ hx₂ hx₃ (I := N.map q) (J := (N ^ (k + 1)).map q)
        (by rw [← Ideal.map_mul, ← pow_succ]; exact Ideal.map_quotient_self _)
        (Ideal.map_mono (Ideal.pow_le_self (by omega)))
        (q.comp ψ) (q.comp ψ') (fun j => Ideal.mem_map_of_mem _ (hψ j))
        (fun j => by
          rw [AlgHom.comp_apply, AlgHom.comp_apply, ← map_sub]
          exact Ideal.mem_map_of_mem _ (ih j))
        (by rw [← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc, h])
      intro j
      exact Ideal.Quotient.eq.1 (AlgHom.congr_fun e (zR m j)).symm
  obtain ⟨n, hn⟩ := hN
  refine jet_ext fun j => ?_
  have := main n j
  rw [pow_succ, hn, zero_mul, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  exact (sub_eq_zero.1 this).symm

theorem coord_unique {m : ℕ} (ψ ψ' : JetR R (Fin d) m →ₐ[R] B) (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  have nil : ∀ φ : JetR R (Fin d) m →ₐ[R] B, IsNilpotent ((RingHom.ker (jetAug R (Fin d) m)).map φ) := fun φ =>
    ⟨m + 1, by rw [← Ideal.map_pow, ker_jetAug_pow, Ideal.map_bot, Ideal.zero_eq_bot]⟩
  refine eq_of_nil hG hv hx₁ hx₂ hx₃ (N := (RingHom.ker (jetAug R (Fin d) m)).map ψ +
    (RingHom.ker (jetAug R (Fin d) m)).map ψ') ((Commute.all _ _).isNilpotent_add (nil ψ) (nil ψ')) ψ ψ'
    (fun j => Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (zR_mem_ker m j)))
    (fun j => Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (zR_mem_ker m j))) h

theorem coord_exists {m : ℕ} {N : Ideal B} (hN : N ^ (m + 1) = ⊥) (y : sp (R₀ := R) B ⟶ G)
    (hy : spMap (Ideal.Quotient.mkₐ R N) ≫ y = 1) : ∃ ψ : JetR R (Fin d) m →ₐ[R] B, spMap ψ ≫ x m = y := by
  have haug : spMap (jetAug R (Fin d) m) ≫ x m = 1 := by
    have e : jetAug R (Fin d) m = (jetAug R (Fin d) 0).comp (jetZeroR R (Fin d) m) :=
      (jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR]; exact (jetAug_zR (R := R) 0 j).symm)
    rw [e, ← spMap_comp, Category.assoc, hx₂ m, comp_one']
  have fac : ∀ {A₁ A₂ : Type} [CommRing A₁] [Algebra R A₁] [CommRing A₂] [Algebra R A₂] (p : B →ₐ[R] A₁)
      (q : A₁ →ₐ[R] A₂) {y y' : sp (R₀ := R) B ⟶ G}, spMap p ≫ y = spMap p ≫ y' →
      spMap (q.comp p) ≫ y = spMap (q.comp p) ≫ y' := fun p q y y' h => by
    rw [← spMap_comp, Category.assoc, Category.assoc, h]
  have key : ∀ k : ℕ, ∃ (b : Fin d → B) (hb : ∀ j, b j ∈ N),
      spMap (Ideal.Quotient.mkₐ R (N ^ (k + 1))) ≫ y =
        spMap (Ideal.Quotient.mkₐ R (N ^ (k + 1))) ≫ spMap (jetLift R _ hN b hb) ≫ x m := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun _ => 0, fun _ => zero_mem _, ?_⟩
      have e : Ideal.Quotient.mkₐ R (N ^ (0 + 1)) =
          (Ideal.Quotient.factorₐ R (show N ≤ N ^ (0 + 1) by rw [zero_add, pow_one])).comp
            (Ideal.Quotient.mkₐ R N) := by
        ext a; rfl
      rw [e]
      refine fac _ _ ?_
      rw [hy, ← Category.assoc, spMap_comp, mk_comp_eq _ (fun j => by rw [jetLift_zR]; exact zero_mem _),
        ← spMap_comp, Category.assoc, haug, comp_one']
    | succ k ih =>
      obtain ⟨b, hb, ih⟩ := ih
      let B' := B ⧸ N ^ (k + 1 + 1)
      let π : B →ₐ[R] B' := Ideal.Quotient.mkₐ R (N ^ (k + 1 + 1))
      have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
      let J : Ideal B' := (N ^ (k + 1)).map π
      have hJN : J * N.map π = ⊥ := by
        rw [← Ideal.map_mul, ← pow_succ]
        exact Ideal.map_quotient_self _
      have hJle : J ≤ N.map π := Ideal.map_mono (Ideal.pow_le_self (by omega))
      have hJ : J ^ 2 = ⊥ := by
        rw [← le_bot_iff, pow_two, ← hJN]
        exact Ideal.mul_mono_right hJle
      let q : (B ⧸ N ^ (k + 1)) →ₐ[R] B' ⧸ J := Ideal.Quotient.liftₐ _
        ((Ideal.Quotient.mkₐ R J).comp π)
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha))
      have hq : q.comp (Ideal.Quotient.mkₐ R (N ^ (k + 1))) = (Ideal.Quotient.mkₐ R J).comp π := by
        ext a; rfl
      have h2 := fac _ q ih
      rw [hq, ← spMap_comp, Category.assoc, Category.assoc] at h2
      haveI := hG
      obtain ⟨c, hc, -⟩ := SqZero.existsUnique_eq_lieExp_mul hv hJ h2.symm
      choose δ hδ hδc using fun j => (Ideal.mem_map_iff_of_surjective π hπ).1 (c j).2
      have hb' : ∀ j, b j + δ j ∈ N := fun j =>
        add_mem (hb j) (Ideal.pow_le_self (by omega) (hδ j))
      refine ⟨fun j => b j + δ j, hb', ?_⟩
      have h3 := move hG hv hx₁ hx₂ hx₃ hJN hJle
        (π.comp (jetLift R _ hN b hb)) (π.comp (jetLift R _ hN (fun j => b j + δ j) hb'))
        (fun j => by rw [AlgHom.comp_apply, jetLift_zR]; exact Ideal.mem_map_of_mem _ (hb j))
        (fun j => (c j : B')) (fun j => (c j).2) (fun j => SqZero.mul_eq_zero_of_sq hJ (c j).2 (c j).2)
        (fun j => by
          rw [AlgHom.comp_apply, AlgHom.comp_apply, jetLift_zR, jetLift_zR, map_add (f := _), hδc])
      change spMap π ≫ y = spMap π ≫ _
      rw [hc, ← Category.assoc, spMap_comp, ← Category.assoc, spMap_comp, h3]
  obtain ⟨b, hb, h⟩ := key m
  refine ⟨jetLift R _ hN b hb, ?_⟩
  let q : (B ⧸ N ^ (m + 1)) →ₐ[R] B := Ideal.Quotient.liftₐ _ (AlgHom.id R B)
    (fun a ha => by rw [hN] at ha; exact ha)
  have hq : q.comp (Ideal.Quotient.mkₐ R (N ^ (m + 1))) = AlgHom.id R B := by
    ext a; rfl
  have h2 := fac _ q h
  rw [hq, spMap_id, Category.id_comp, Category.id_comp] at h2
  exact h2.symm

theorem existsUnique_coord {m : ℕ} {N : Ideal B} (hN : N ^ (m + 1) = ⊥) (y : sp (R₀ := R) B ⟶ G)
    (hy : spMap (Ideal.Quotient.mkₐ R N) ≫ y = 1) : ∃! ψ : JetR R (Fin d) m →ₐ[R] B, spMap ψ ≫ x m = y := by
  obtain ⟨ψ, h⟩ := coord_exists hG hv hx₁ hx₂ hx₃ hN y hy
  exact ⟨ψ, h, fun ψ' h' => coord_unique hG hv hx₁ hx₂ hx₃ _ _ (h'.trans h.symm)⟩

end GlobalTheory.NilChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueLinearLiftUniformisedFibres
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology

namespace GlobalTheory

namespace UniformLift

def toAddHom {V A : Type*} [AddGroup V] [Group A] (e : V → A) (he : ∀ z w, e (z + w) = e z * e w) :
    V →+ Additive A :=
  AddMonoidHom.mk' (fun z => Additive.ofMul (e z)) fun z w => by rw [he, ofMul_mul]

theorem map_zero_eq_one {V A : Type*} [AddGroup V] [Group A] (e : V → A) (he : ∀ z w, e (z + w) = e z * e w) :
    e 0 = 1 :=
  (toAddHom e he).map_zero

theorem addMonoidHom_eq_of_eventuallyEq_addGroup {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [AddGroup A]
    {e e' : V →+ A} (h : e =ᶠ[𝓝 0] e') : e = e' := by
  ext v
  have ht : Tendsto (fun j : ℕ => (2⁻¹ : ℝ) ^ j • v) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num)
      (by norm_num)).smul_const v
  obtain ⟨j, hj⟩ := (ht.eventually h).exists
  have hv : v = (2 ^ j : ℕ) • (2⁻¹ : ℝ) ^ j • v := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp
  rw [hv, map_nsmul, map_nsmul, hj]

theorem existsUnique_linearMap_lift_of_germ {V W A : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [AddGroup A] {ex : V →+ A} {ex' : W →+ A}
    (hker : IsDiscrete (ex'.ker : Set W)) {k : V → W} (hd : DifferentiableAt ℂ k 0) (h0 : k 0 = 0)
    (hk : ∀ᶠ z in 𝓝 0, ex' (k z) = ex z) : ∃! L : V →ₗ[ℂ] W, ∀ z, ex' (L z) = ex z := by
  have hadd : Tendsto (fun p : V × V ↦ p.1 + p.2) (𝓝 0) (𝓝 0) := by
    simpa using continuous_add.tendsto (0 : V × V)
  have hL := eventuallyEq_fderiv_of_eventually_add_mod_discrete hker hd h0 <| by
    filter_upwards [hadd.eventually hk, (continuous_fst.tendsto (0 : V × V)).eventually hk,
      (continuous_snd.tendsto (0 : V × V)).eventually hk] with p h1 h2 h3
    rw [AddMonoidHom.mem_ker, sub_sub, map_sub, map_add (f := _), h1, h2, h3, map_add (f := _), sub_self]
  have hL' : ex'.comp (fderiv ℂ k 0 : V →+ W) = ex := addMonoidHom_eq_of_eventuallyEq_addGroup <| by
    filter_upwards [hL, hk] with z h1 h2
    change ex' (fderiv ℂ k 0 z) = ex z
    rw [← h1, h2]
  have hL'' : ∀ z, ex' (fderiv ℂ k 0 z) = ex z := fun z => DFunLike.congr_fun hL' z
  refine ⟨(fderiv ℂ k 0 : V →ₗ[ℂ] W), hL'', fun L h => ?_⟩
  have := realLinear_eq_of_sub_mem_discrete hker (L := L.restrictScalars ℝ)
    (L' := (fderiv ℂ k 0 : V →ₗ[ℂ] W).restrictScalars ℝ) fun x => by
      rw [AddMonoidHom.mem_ker, map_sub]
      exact sub_eq_zero.2 ((h x).trans (hL'' x).symm)
  exact LinearMap.ext fun z => DFunLike.congr_fun this z

theorem fibPt_fst {X : Scheme.{0}} (G : Over X) {y : Sp ℂ ⟶ X} (x : Over.mk y ⟶ G) :
    fibPt G x ≫ pullback.fst _ _ = x.left := pullback.lift_fst _ _ _

theorem fibPt_snd {X : Scheme.{0}} (G : Over X) {y : Sp ℂ ⟶ X} (x : Over.mk y ⟶ G) :
    fibPt G x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _

theorem fibPt_injective {X : Scheme.{0}} (G : Over X) {y : Sp ℂ ⟶ X} {x x' : Over.mk y ⟶ G}
    (h : fibPt G x = fibPt G x') : x = x' :=
  Over.OverMorphism.ext (by rw [← fibPt_fst, h, fibPt_fst])

end UniformLift


open UniformLift in
theorem existsUnique_linear_lift_fibre :
    ∀ (X X' : Scheme.{0}) (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (y : Sp ℂ ⟶ X) (y' : Sp ℂ ⟶ X') (g g' : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (e' : (Fin g' → ℂ) → (Over.mk y' ⟶ G')) (ψ : pullback G.hom y ⟶ pullback G'.hom y') (ψp : (Over.mk y ⟶ G) →* (Over.mk y' ⟶ G')), Smooth G'.hom → (∀ z w, e (z + w) = e z * e w) → (∀ z w, e' (z + w) = e' z * e' w) → IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => (e' z).left) → ((∀ w, ∃! v : epsPt y' ⟶ G', IsDerivAt0 (fun z => (e' z).left) w v.left) ∧ ∀ v : epsPt y' ⟶ G', spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left → ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) → DiscreteTopology {z // e' z = 1} → ψ ≫ pullback.snd _ _ = pullback.snd _ _ → (∀ x, fibPt G x ≫ ψ = fibPt G' (ψp x)) → ∃! h : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), ∀ z, e' (h z) = ψp (e z) := by
  intro X X' G G' _ _ y y' g g' e e' ψ ψp hsm he he' hol hol' hder hdisc hψ hψp
  have hsm' : Smooth (pullback.snd G'.hom y') := inferInstance
  have hd := isDerivAt0_fibre X' G' y' g' e' _ _ _ (fun z => fibPt G' (e' z)) (IsPullback.of_hasPullback G'.hom y')
    (fun z => ⟨fibPt_fst _ _, fibPt_snd _ _⟩) hol' hder
  obtain ⟨k, k0, hka, hk⟩ := LocalLift.exists_local_lift _ (pullback.snd G'.hom y') g g'
    (fun z => fibPt G (e z) ≫ ψ) (fun z => fibPt G' (e' z)) hsm'
    (fun z => by rw [Category.assoc, hψ, fibPt_snd]) (fun z => fibPt_snd _ _)
    ((_root_.GlobalTheory.HolFibre.isHolTo_fibPt_and_comp X G y g e hol).2 _ ψ) (_root_.GlobalTheory.HolFibre.isHolTo_fibPt_and_comp X' G' y' g' e' hol').1 hd
    (by simp only [hψp, map_zero_eq_one e he, map_zero_eq_one e' he', map_one])
  exact existsUnique_linearMap_lift_of_germ
    (ex := toAddHom (fun z => ψp (e z)) fun z w => by rw [he, map_mul]) (ex' := toAddHom e' he')
    ⟨hdisc⟩ hka.differentiableAt k0 (hk.mono fun z hz => fibPt_injective G' (hz.trans (hψp _)))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameEqOfBaseChangeInjective
section
namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem frPt_eq_of_frMap_injective : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (z z' : FrPt Xo c S) (w : FrPt Xo c T), Function.Injective φ → z'.x = z.x → FrMap φ z w → FrMap φ z' w → z = z' := by
  intro _ E _ _ _ H Dw l Xo c S _ _ T _ _ φ z z' w hφ hx hz hz'
  obtain ⟨g, a, -, hga⟩ := (_root_.GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c S z z').1 hx
  have h1 := (_root_.GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c S T φ z z' w w g (a : S) hga hz).1 hz'
  have h2 := (_root_.GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c T w w w).1
  obtain ⟨hg, ha⟩ := (_root_.GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c T w w).2 _ _ _ _ h1 h2
  have ha1 : (a : S) = ((1 : Sˣ) : S) := hφ (by rw [ha]; simp)
  have hg1 : g = fun _ => 1 := by
    funext τ
    have h := congrFun hg τ
    ext i j
    apply hφ
    have hij := congrFun (congrFun h i) j
    simp only [Matrix.map_apply] at hij
    rw [hij]
    by_cases e : i = j
    · subst e; simp
    · simp [Matrix.one_apply_ne e]
  rw [ha1, hg1] at hga
  have h3 : FrChg (fun _ => 1) ((1 : Sˣ) : S) z z := (_root_.GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S z z z).1
  exact (GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c S z (fun _ => 1) 1 (fun _ => by simp)).unique h3 hga

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToOfComponents
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.HolPullback

theorem isHolTo_of_components :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (Y Y' S S' : Scheme.{0}) (φ : Y' ⟶ Y) (p' : Y' ⟶ S') (p : Y ⟶ S) (f : S' ⟶ S) (a : V → (Sp ℂ ⟶ Y')), IsPullback φ p' p f → IsOpen B → IsHolTo B (fun b => a b ≫ φ) → IsHolTo B (fun b => a b ≫ p') → IsHolTo B a :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ H _ h₁ h₂ => GlobalTheory.HolFibre.isHolTo_of_isPullback H h₁ h₂

end GlobalTheory.HolPullback
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieBasisIffTangentBasisPullbackUniversal
section
noncomputable section

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem spMap_epsScaleR_comp {S : Type} [CommRing S] (c : S) :
    spMap (epsScaleR c) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S)) := by
  have e : (epsScaleR c).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) := by
    ext s <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  conv_rhs => rw [← e]
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem lieBasis_iff_tanBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (G' : Over (Sp S)) [GrpObj G'] (φ : G'.left ⟶ Xo.univ.t.G.left), IsGrpPullback G' Xo.univ.t.G x φ → (∀ w : (Sp (DualNumber S) ⟶ Xo.univ.t.G.left), IsTanAt x w → ∃ v : epsR S ⟶ G', v.left ≫ φ = w) ∧ ∀ (n : ℕ) (v : Fin n → (epsR S ⟶ G')), IsLieBasis v ↔ TanBasis x (fun i => (v i).left ≫ φ) := by
  intro E _ _ _ H Dw l Xo S _ x G' _ φ hp
  let up : ∀ w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left,
      w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x → (epsR S ⟶ G') :=
    fun w h => Over.homMk (hp.1.lift w _ h) (hp.1.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => hp.1.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp S)} {u v : T ⟶ G'}, u.left ≫ φ = v.left ≫ φ → u = v := fun h =>
    Over.OverMorphism.ext (hp.1.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp S), (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ x) ⟶ Xo.univ.t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have e : η[G'].left ≫ φ = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
    have e₁ : (1 : 𝟙_ (Over (Sp S)) ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [← e₁, one]
    exact congrArg (· ≫ (η[Xo.univ.t.G]).left) (Category.id_comp x)
  have zs : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext s; simp
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have tan : ∀ w : epsR S ⟶ G', IsTangent w ↔ IsTanAt x (w.left ≫ φ) := fun w => by
    refine ⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => hp.1.hom_ext ?_ ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ φ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
    · refine (Category.assoc _ _ _).trans ?_
      rw [Over.w w, Over.w η[G']]
      exact zs
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ G')), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEps x ⟶ Xo.univ.t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ G')) w,
      IsLieComb c v w ↔ IsCombAt x (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := fun c v w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => up (u i).left (Over.w _), fun i => hp.1.hom_ext ?_ ?_,
        inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (spMap_epsScaleR_comp (c i)).symm
      · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEps x ⟶ Xo.univ.t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEps x ⟶ Xo.univ.t.G) => (List.ofFn q).prod.left) this
  refine ⟨fun w hw => ⟨up w hw.1, hup _ _⟩, fun n v => ⟨fun hB => ⟨fun i => (tan _).1 (hB.1 i), fun w hw => ?_⟩,
    fun hB => ⟨fun i => (tan _).2 (hB.1 i), fun w hw => ?_⟩⟩⟩
  · have h := hB.2 (up w hw.1) ((tan _).2 (by rw [hup]; exact hw))
    simp only [comb, hup] at h
    exact h
  · have h := hB.2 _ ((tan _).1 hw)
    simp only [comb]
    exact h

end GlobalTheory.Frames
end
end

