module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyInjectiveOfIsoOnFiniteTypeRings
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FiniteTypeApprox

theorem nat_apply {N M : CommRingCat.{0} ⥤ AbCx} (ε : N ⟶ M) {A B : CommRingCat.{0}} (g : A ⟶ B) (n : ℤ)
    (x : (N.obj A).X n) : (ε.app B).f n ((N.map g).f n x) = (M.map g).f n ((ε.app A).f n x) := by
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ε.naturality, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply]

theorem comm_apply {K L : AbCx} (φ : K ⟶ L) (i j : ℤ) (x : K.X i) :
    φ.f j (K.d i j x) = L.d i j (φ.f i x) := by
  rw [← ConcreteCategory.comp_apply, ← φ.comm, ConcreteCategory.comp_apply]

theorem map_comp_apply (N : CommRingCat.{0} ⥤ AbCx) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ)
    (x : (N.obj A).X n) : (N.map (f ≫ g)).f n x = (N.map g).f n ((N.map f).f n x) := by
  rw [Functor.map_comp, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]

theorem map_id_apply (N : CommRingCat.{0} ⥤ AbCx) (A : CommRingCat.{0}) (n : ℤ) (x : (N.obj A).X n) :
    (N.map (𝟙 A)).f n x = x := by
  simp

theorem inj_of_iso {X Y : AddCommGrpCat.{1}} (f : X ⟶ Y) [IsIso f] {x y : X} (h : f x = f y) : x = y :=
  (ConcreteCategory.bijective_of_isIso f).1 h

theorem inv_apply_eq {X Y : AddCommGrpCat.{1}} (f : X ⟶ Y) [IsIso f] (y : Y) : f (inv f y) = y := by
  rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]

theorem eq_zero_of_isZero {X : AddCommGrpCat.{1}} (h : IsZero X) (x : X) : x = 0 := by
  have := (AddCommGrpCat.isZero_iff_subsingleton.1 h)
  exact Subsingleton.elim _ _

theorem isIso_f {K L : AbCx} (φ : K ⟶ L) [IsIso φ] (n : ℤ) : IsIso (φ.f n) :=
  (inferInstance : IsIso ((HomologicalComplex.eval _ _ n).map φ))

theorem locInj_of_finiteType : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → LocInj EtFF ε := by
  intro N M ε F0 ι hF0 hι hMneg hMpos hN hε
  intro n A c hc hy
  obtain ⟨y, hy⟩ := hy
  obtain ⟨J, _, _, D, ιD, ⟨hcol⟩, hft⟩ := GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType A
  obtain ⟨-, hN2⟩ := GlobalTheory.T.complexCohomology_commutes_with_filteredColimits N hN
  obtain ⟨⟨hmul, hcob, -⟩, -, hftB⟩ := GlobalTheory.T.etaleFaithfullyFlatRingHom_basic_properties
  obtain ⟨j, w, y', hw, hwc⟩ := (hN2 J D (Cocone.mk A ιD) hcol n).1 c hc
  change (N.map (ιD.app j)).f n w = c + (N.obj A).d (n - 1) n y' at hwc
  have hwv : (M.obj (D.obj j)).d n (n + 1) ((ε.app (D.obj j)).f n w) = 0 := by
    rw [← comm_apply, hw, map_zero]

  have fin : (N.map (ιD.app j)).f n w = 0 → ∃ (V : CommRingCat.{0}) (g : A ⟶ V), EtFF g ∧
      ∃ b : (N.obj V).X (n - 1), (N.obj V).d (n - 1) n b = (N.map g).f n c := by
    intro h0
    refine ⟨A, 𝟙 A, MorphismProperty.id_mem EtFF A, -y', ?_⟩
    rw [map_id_apply, map_neg]
    rw [h0] at hwc
    exact (eq_neg_of_add_eq_zero_left hwc.symm).symm
  rcases lt_trichotomy n 0 with hn | hn | hn
  ·
    apply fin
    haveI := hε _ (hft j)
    haveI := isIso_f (ε.app (D.obj j)) n
    have : w = 0 := inj_of_iso ((ε.app (D.obj j)).f n)
      ((eq_zero_of_isZero (hMneg n hn _) _).trans (map_zero _).symm)
    rw [this, map_zero]
  ·
    subst hn
    apply fin
    have hy0 : y = 0 := eq_zero_of_isZero (hMneg _ (by norm_num) _) y
    rw [hy0, map_zero] at hy
    obtain ⟨x0, hx0⟩ := ((hι (D.obj j)).2 _).1 hwv
    have hιnat : ∀ {B C : CommRingCat.{0}} (g : B ⟶ C) (x : F0.obj B),
        ι.app C (F0.map g x) = (M.map g).f 0 (ι.app B x) := by
      intro B C g x
      rw [← ConcreteCategory.comp_apply, ι.naturality, ConcreteCategory.comp_apply]
      rfl
    have hdie : F0.map (ιD.app j) x0 = 0 := by
      apply (hι A).1
      rw [hιnat, hx0, ← nat_apply, hwc, map_add (f := _), hy, comm_apply,
        eq_zero_of_isZero (hMneg _ (by norm_num) _) ((ε.app A).f (0 - 1) y'), map_zero, add_zero]
      exact (map_zero _).symm
    obtain ⟨-, hF0inj⟩ := (GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} F0).1 hF0 J D (Cocone.mk A ιD) hcol
    obtain ⟨k, f, hk⟩ := hF0inj j x0 hdie
    haveI := hε _ (hft k)
    haveI := isIso_f (ε.app (D.obj k)) 0
    have hwk : (N.map (D.map f)).f 0 w = 0 := by
      apply inj_of_iso ((ε.app (D.obj k)).f 0)
      rw [nat_apply, ← hx0, ← hιnat, hk, map_zero, map_zero]
    have hcw : ιD.app j = D.map f ≫ ιD.app k := by
      have := ιD.naturality f
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
      exact this.symm
    rw [hcw, map_comp_apply, hwk, map_zero]
  ·
    obtain ⟨B0, g0, hg0, y0, hy0⟩ := hMpos n hn _ _ hwv
    have hB0 := hftB _ _ g0 hg0 (hft j)
    haveI := hε _ hB0
    haveI := isIso_f (ε.app B0) n
    haveI := isIso_f (ε.app B0) (n - 1)
    set b0 := inv ((ε.app B0).f (n - 1)) y0 with hb0
    have hdb0 : (N.obj B0).d (n - 1) n b0 = (N.map g0).f n w := by
      apply inj_of_iso ((ε.app B0).f n)
      rw [comm_apply, hb0, inv_apply_eq, hy0, nat_apply]
    haveI := hcob
    have hg : EtFF (pushout.inr g0 (ιD.app j)) := MorphismProperty.pushout_inr _ _ hg0
    refine ⟨pushout g0 (ιD.app j), pushout.inr g0 (ιD.app j), hg,
      (N.map (pushout.inl g0 (ιD.app j))).f (n - 1) b0 - (N.map (pushout.inr g0 (ιD.app j))).f (n - 1) y', ?_⟩
    rw [map_sub, ← comm_apply, ← comm_apply, hdb0, ← map_comp_apply, pushout.condition, map_comp_apply, hwc,
      map_add]
    exact add_sub_cancel_right _ _
end GlobalTheory.EtC.FiniteTypeApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSymmetricCocyclesOfPullbackMulP
section
set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDivGroup

theorem mem_symCocycles_of_pullTwo_mulP {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ)
    (c : G.A n ⊗[R] G.A n) (h : pullbackTwo (G.mulP n) c ∈ symCocycles R (G.A (n + 1))) :
    c ∈ symCocycles R (G.A n) := by
  rw [mem_symCocycles] at h ⊢
  have h3 : Function.Injective
      (TensorProduct.map (G.mulP n : G.A n →ₗ[R] G.A (n + 1)) (pullbackTwo (G.mulP n))) :=
    TensorProduct.map_injective_of_flat_flat _ _ (Test.mulP_injective G n)
      (G.pullbackTwo_mulP_injective n)
  refine ⟨h3 ?_, G.pullbackTwo_mulP_injective n ?_⟩
  · rw [← cobTwo_pullTwo, h.1, map_zero]
  · rw [← h.2]
    exact TensorProduct.map_comm _ _ c

end PDivGroup

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastSmulMemAugIdealSqSupMapMulP
section
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra

namespace GlobalTheory

open PDiv

theorem PDivGroup.natCast_smul_mem_augSq_sup_map : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ),
    ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))),
      (p : R) • a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 ⊔
        (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map
          ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  intro p R _ G n a ha
  have ha0 : counit (R := R) a = 0 := ha
  have hb : G.res n a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A n)) := by
    change counit (R := R) (G.res n a) = 0
    rw [CoalgHomClass.counit_comp_apply, ha0]
  have h1 : PDiv.mulBy (R := R) (A := G.A (n + 1)) p a ∈ (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map
      ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
    rw [← G.mulP_res n a]
    exact Ideal.mem_map_of_mem _ hb
  have h2 : dUnit (R := R) (PDiv.mulBy (R := R) (A := G.A (n + 1)) p a - (p : R) • a) = 0 := by
    have e1 : dUnit (R := R) (PDiv.mulBy (R := R) (A := G.A (n + 1)) p a - (p : R) • a) =
        dUnit (R := R) (PDiv.mulBy (R := R) (A := G.A (n + 1)) p a) - dUnit (R := R) ((p : R) • a) :=
      map_sub (AugCot.d (Bialgebra.counitAlgHom R (G.A (n + 1)))) _ _
    have e2 : dUnit (R := R) ((p : R) • a) = (p : R) • dUnit (R := R) a :=
      map_smul (AugCot.d (Bialgebra.counitAlgHom R (G.A (n + 1)))) _ _
    rw [e1, e2, ← cotMap_d, cotMap_mulBy, sub_self]
  have h3 : PDiv.mulBy (R := R) (A := G.A (n + 1)) p a - (p : R) • a ∈
      RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 := by
    have h := (AugCot.d_eq_zero_iff _ _).1 h2
    have he : Bialgebra.counitAlgHom R (G.A (n + 1)) (PDiv.mulBy (R := R) (A := G.A (n + 1)) p a - (p : R) • a) = 0 := by
      change counit (R := R) (PDiv.mulBy (R := R) (A := G.A (n + 1)) p a - (p : R) • a) = 0
      rw [map_sub, map_smul, CoalgHomClass.counit_comp_apply, ha0, smul_zero, sub_zero]
    rwa [he, map_zero, sub_zero] at h
  have : (p : R) • a = PDiv.mulBy (R := R) (A := G.A (n + 1)) p a - (PDiv.mulBy (R := R) (A := G.A (n + 1)) p a - (p : R) • a) := by abel
  rw [this]
  exact Submodule.sub_mem _ (Submodule.mem_sup_right h1) (Submodule.mem_sup_left h3)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeBijectiveOfPEqZero
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDiv

theorem liftSemi_toBaseChange_cot_bijective (R R' A : Type) [CommRing R] [CommRing R'] [Algebra R R']
    [CommRing A] [Bialgebra R A] : Function.Bijective (liftSemi (toBaseChange R R' A).cot) := by
  have heq : (counitAlgHom R' (R' ⊗[R] A)).comp
      ((AlgEquiv.refl : (R' ⊗[R] A) ≃ₐ[R'] (R' ⊗[R] A)) : (R' ⊗[R] A) →ₐ[R'] (R' ⊗[R] A)) =
      AugCot.baseChangeAug R' (counitAlgHom R A) := by
    apply Algebra.TensorProduct.ext'
    intro r a
    simp [AugCot.baseChangeAug_tmul, Algebra.smul_def, mul_comm]
  let E : R' ⊗[R] Cot R A ≃ₗ[R'] Cot R' (R' ⊗[R] A) :=
    (AugCot.baseChangeEquiv R' (counitAlgHom R A)).trans (AugCot.congr AlgEquiv.refl heq)
  have hmap : liftSemi (toBaseChange R R' A).cot = E.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r m
    obtain ⟨a, rfl⟩ := AugCot.d_surjective (counitAlgHom R A) m
    simp only [liftSemi_tmul, LinearEquiv.coe_coe, E, LinearEquiv.trans_apply,
      AugCot.baseChangeEquiv_tmul_d, map_smul, AugCot.congr_d]
    exact congrArg (r • ·) ((toBaseChange R R' A).cot_d a)
  rw [hmap]
  exact E.bijective

end PDiv

namespace PDivGroup

theorem omega_baseChange_bijective {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (R' : Type)
    [CommRing R'] [Algebra R R'] (hp : (p : R) = 0) :
    Function.Bijective (liftSemi (G.toBase R').omega) := by
  have hp' : (p : R') = 0 := by rw [← map_natCast (algebraMap R R'), hp, map_zero]
  have hL := G.omegaLevel_one_bijective hp
  have hL' := (G.baseChange R').omegaLevel_one_bijective hp'
  have hg := liftSemi_toBaseChange_cot_bijective R R' (G.A 1)
  let e : R' ⊗[R] G.omega ≃ₗ[R'] R' ⊗[R] Cot R (G.A 1) :=
    LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofBijective (G.omegaLevel 1) hL)
  have hcomp : ((G.baseChange R').omegaLevel 1).comp (liftSemi (G.toBase R').omega) =
      (liftSemi (toBaseChange R R' (G.A 1)).cot).comp e.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, liftSemi_tmul, map_smul, e,
      LinearEquiv.baseChange_tmul, LinearEquiv.ofBijective_apply]
    rfl
  refine Function.Bijective.of_comp_left ?_ hL'.injective
  change Function.Bijective (((G.baseChange R').omegaLevel 1).comp (liftSemi (G.toBase R').omega))
  rw [hcomp]
  exact hg.comp e.bijective

end PDivGroup

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupMulPUnitFibreEqLevelOne
section
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra GlobalTheory.PDiv

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

open scoped TensorProduct in
set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
theorem _root_.GlobalTheory.PDivGroup.ker_resOne (n : ℕ) :
    RingHom.ker (G.resOne n :
      G.A (n + 1) →ₐ[R] G.A 1) =
      _root_.GlobalTheory.PDiv.torsionIdeal (R := R) (A := G.A (n + 1)) p := by
  induction n with
  | zero =>
    have hid : (G.resOne 0 :
        G.A 1 →ₐ[R] G.A 1) = AlgHom.id R _ := by
      ext a; exact G.resOne_zero a
    rw [hid]
    refine le_antisymm ?_ ?_
    · intro a ha
      have : a = 0 := ha
      simp [this]
    · refine (_root_.GlobalTheory.PDiv.torsionIdeal_le_ker_iff p
        (AlgHom.id R (G.A (0 + 1)))).2 ?_
      simpa using G.pts_pow_self 1 (WithConv.toConv (AlgHom.id R (G.A 1)))
  | succ n ih =>
    have hcomp : (G.resOne (n + 1) :
        G.A (n + 2) →ₐ[R] G.A 1) =
        (G.resOne n :
          G.A (n + 1) →ₐ[R] G.A 1).comp
          (G.res (n + 1) :
            G.A (n + 2) →ₐ[R] G.A (n + 1)) := by
      ext a; exact G.resOne_succ n a
    have hsurj : Function.Surjective (G.res (n + 1) :
        G.A (n + 2) →ₐ[R] G.A (n + 1)) :=
      G.res_surjective (n + 1)
    have hker : RingHom.ker ((G.resOne n :
        G.A (n + 1) →ₐ[R] G.A 1).comp
          (G.res (n + 1) :
            G.A (n + 2) →ₐ[R] G.A (n + 1))) =
        Ideal.comap (G.res (n + 1) :
          G.A (n + 2) →ₐ[R] G.A (n + 1))
          (RingHom.ker (G.resOne n :
            G.A (n + 1) →ₐ[R] G.A 1)) := by
      ext a; exact Iff.rfl
    rw [hcomp, hker, ih, ← _root_.GlobalTheory.PDiv.map_torsionIdeal
      (G.res_surjective (n + 1)) p]
    erw [Ideal.comap_map_of_surjective _ hsurj]
    refine sup_eq_left.mpr ?_
    have h0 : Ideal.comap (G.res (n + 1) :
        G.A (n + 2) →ₐ[R] G.A (n + 1)) ⊥ =
        _root_.GlobalTheory.PDiv.torsionIdeal (R := R) (A := G.A (n + 2)) (p ^ (n + 1)) := by
      rw [← G.ker_res (n + 1)]
      ext a; exact Iff.rfl
    rw [h0]
    exact _root_.GlobalTheory.PDiv.torsionIdeal_le_of_dvd (dvd_pow_self p (Nat.succ_ne_zero n))

open scoped TensorProduct in
set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra in
variable {p : ℕ} {R : Type} [CommRing R] (G : _root_.GlobalTheory.PDivGroup p R) in
theorem _root_.GlobalTheory.PDivGroup.kerIdeal_mulP (n : ℕ) :
    _root_.GlobalTheory.PDiv.kerIdeal (G.mulP n) =
      _root_.GlobalTheory.PDiv.torsionIdeal (R := R) (A := G.A (n + 1)) p := by
  unfold _root_.GlobalTheory.PDiv.torsionIdeal
  rw [← G.mulP_comp_res n,
    _root_.GlobalTheory.PDiv.kerIdeal_comp_of_surjective _ (G.res_surjective n)]

end PDivGroup

section TensorQuot

variable {R k M : Type} [CommRing R] [CommRing k] [Algebra R k] [AddCommGroup M] [Module R M]

end TensorQuot

namespace PDivGroup

end PDivGroup

open scoped TensorProduct in
set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra in
private theorem mem_ker_smul_univ_of_one_tmul_eq_zero {R k M : Type} [CommRing R] [CommRing k]
    [Algebra R k] [AddCommGroup M] [Module R M] (hk : Function.Surjective (algebraMap R k))
    {m : M} (hm : (1 : k) ⊗ₜ[R] m = 0) :
    m ∈ RingHom.ker (algebraMap R k) • (⊤ : Submodule R M) := by
  set f : R →ₐ[R] k := Algebra.ofId R k
  have hf : Function.Surjective f := hk
  let e : (R ⧸ RingHom.ker f) ≃ₐ[R] k := Ideal.quotientKerAlgEquivOfSurjective hf
  have hker : RingHom.ker f = RingHom.ker (algebraMap R k) := rfl
  let g : k ⊗[R] M ≃ₗ[R] M ⧸ (RingHom.ker f • (⊤ : Submodule R M)) :=
    (LinearEquiv.rTensor M e.symm.toLinearEquiv).trans
      (quotTensorEquivQuotSMul M (RingHom.ker f))
  have h1 : e.symm 1 = Ideal.Quotient.mk (RingHom.ker f) 1 := by simp
  have h2 : g ((1 : k) ⊗ₜ[R] m) = Submodule.Quotient.mk m := by
    simp only [g, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
      AlgEquiv.toLinearEquiv_apply, h1, quotTensorEquivQuotSMul_mk_tmul, one_smul]
  rw [hm, map_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at h2
  exact hker ▸ h2

open scoped TensorProduct in
set_option autoImplicit false in
open TensorProduct Coalgebra Bialgebra in
theorem _root_.GlobalTheory.fibre_statement : ∀ (p : ℕ) (R k : Type) [CommRing R] [CommRing k]
    [Algebra R k], Function.Surjective (algebraMap R k) → ∀ (G : _root_.GlobalTheory.PDivGroup p R) (n : ℕ),
      Function.Surjective (fun a : G.A (n + 1) =>
        ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1)) ∧
      ∀ a : G.A (n + 1),
        ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1) = 0 ↔
          a ∈ (RingHom.ker ((algebraMap R k).comp
            (Bialgebra.counitAlgHom R (G.A n) :
              G.A n →+* R))).map
            ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) :
              G.A n →+* G.A (n + 1)) := by
  intro p R k _ _ _ hk G n
  set ρ := G.resOne n
  set μ := G.mulP n
  set J := RingHom.ker ((algebraMap R k).comp
    (Bialgebra.counitAlgHom R (G.A n) : G.A n →+* R))
  set L := J.map ((μ : G.A n →ₐ[R] G.A (n + 1)) :
    G.A n →+* G.A (n + 1))
  have hρ : Function.Surjective ρ := G.resOne_surjective n
  have hJ : ∀ x : G.A n, x ∈ J ↔
      algebraMap R k (Bialgebra.counitAlgHom R (G.A n) x) = 0 :=
    fun x => Iff.rfl
  refine ⟨?_, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c x =>
      obtain ⟨r, rfl⟩ := hk c
      obtain ⟨y, rfl⟩ := hρ x
      refine ⟨r • y, ?_⟩
      show (1 : k) ⊗ₜ[R] ρ (r • y) = _
      rw [map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.algebraMap_eq_smul_one]
    | add s t hs ht =>
      obtain ⟨a, rfl⟩ := hs
      obtain ⟨b, rfl⟩ := ht
      exact ⟨a + b, by simp [TensorProduct.tmul_add]⟩
  · have hmem := mem_ker_smul_univ_of_one_tmul_eq_zero hk ha
    have hle : RingHom.ker (algebraMap R k) • (⊤ : Submodule R (G.A 1)) ≤
        (L.restrictScalars R).map
          (ρ : G.A (n + 1) →ₐ[R] G.A 1).toLinearMap := by
      refine Submodule.smul_le.mpr fun r hr x _ => ?_
      obtain ⟨y, rfl⟩ := hρ x
      refine ⟨r • y, ?_, map_smul _ r y⟩
      show r • y ∈ L
      rw [Algebra.smul_def]
      refine Ideal.mul_mem_right _ _ ?_
      have h1 : algebraMap R (G.A (n + 1)) r =
          (μ : G.A n →ₐ[R] G.A (n + 1))
            (algebraMap R (G.A n) r) := (AlgHom.commutes _ r).symm
      rw [h1]
      refine Ideal.mem_map_of_mem _ ((hJ _).mpr ?_)
      rw [AlgHom.commutes]
      exact hr
    obtain ⟨b, hb, hab⟩ := hle hmem
    have hker : a - b ∈ RingHom.ker
        (ρ : G.A (n + 1) →ₐ[R] G.A 1) := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      exact hab.symm
    rw [_root_.GlobalTheory.PDivGroup.ker_resOne,
      ← _root_.GlobalTheory.PDivGroup.kerIdeal_mulP] at hker
    have haug : _root_.GlobalTheory.PDiv.kerIdeal μ ≤ L := by
      unfold _root_.GlobalTheory.PDiv.kerIdeal
      refine Ideal.map_mono fun x hx => (hJ x).mpr ?_
      rw [show Bialgebra.counitAlgHom R (G.A n) x = 0 from hx, map_zero]
    have := L.add_mem (haug hker) hb
    rwa [sub_add_cancel] at this
  · let ψ : G.A (n + 1) →+* k ⊗[R] G.A 1 :=
      (Algebra.TensorProduct.includeRight :
        G.A 1 →ₐ[R] k ⊗[R] G.A 1).toRingHom.comp
        (ρ : G.A (n + 1) →ₐ[R] G.A 1).toRingHom
    have hL : L ≤ RingHom.ker ψ := by
      refine Ideal.map_le_iff_le_comap.mpr fun j hj => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      show (1 : k) ⊗ₜ[R] ρ (μ j) = 0
      rw [G.resOne_mulP, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]
      have := (hJ j).mp hj
      rw [Bialgebra.counitAlgHom_apply] at this
      rw [this, TensorProduct.zero_tmul]
    exact hL ha

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaNoPTorsionOfCotangentInjective
section
open scoped TensorProduct

namespace GlobalTheory

open PDiv

theorem omega_eq_zero_of_p_smul_eq_zero :
    ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R),
      (∀ n, Function.Injective (GlobalTheory.PDiv.cotMap (G.mulP n))) →
        ∀ w : G.omega, (p : R) • w = 0 → w = 0 := by
  intro p R _ G hinj w hw
  refine Subtype.ext (funext fun n => ?_)
  have hp : (p : R) • w.1 (n + 1) = 0 := congrArg (fun v : G.omega => v.1 (n + 1)) hw
  apply hinj n
  change cotMap (G.mulP n) (w.1 n) = cotMap (G.mulP n) 0
  rw [map_zero, ← w.2 n, ← LinearMap.comp_apply, ← cotMap_comp, G.mulP_comp_res,
    cotMap_mulBy, hp]

end GlobalTheory
end

