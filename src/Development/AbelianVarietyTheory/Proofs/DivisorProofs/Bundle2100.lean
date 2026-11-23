module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCompleteOfFinite
section
open IsLocalRing

namespace GlobalTheory.FiniteLocalCompleteness

theorem precomplete_of_finite {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (M : Type) [AddCommGroup M]
    [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r x =>
    obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective I R r
    refine ⟨a • x, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    have : AdicCompletion.of I R a = algebraMap R (AdicCompletion I R) a := rfl
    rw [this, algebraMap_smul]
  | add s t hs ht =>
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩

theorem precomplete_of_pow_le {S : Type} [CommRing S] (I J : Ideal S) [hI : IsPrecomplete I S] (hIJ : I ≤ J) (k : ℕ)
    (hk : J ^ (k + 1) ≤ I) : IsPrecomplete J S := by
  refine ⟨fun f hf => ?_⟩
  have h1 : ∀ n, (J ^ ((k + 1) * n) • ⊤ : Submodule S S) ≤ I ^ n • ⊤ := fun n => by
    refine Submodule.smul_mono_left ?_
    rw [pow_mul]
    exact Ideal.pow_right_mono hk n
  obtain ⟨L, hL⟩ := hI.prec (f := fun n => f ((k + 1) * n))
    (fun {m n} h => (hf (Nat.mul_le_mul_left _ h)).mono (h1 m))
  refine ⟨L, fun n => ?_⟩
  refine (hf (show n ≤ (k + 1) * n by nlinarith)).trans ((hL n).mono ?_)
  exact Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)

theorem isLocalRing_of_complete {S : Type} [CommRing S] [IsDomain S] (I : Ideal S) [IsAdicComplete I S]
    [IsArtinianRing (S ⧸ I)] : IsLocalRing S := by
  have hjac := IsAdicComplete.le_jacobson_bot I
  have hu : ∀ z ∈ I, IsUnit (1 - z) := fun z hz => by
    have := Ideal.mem_jacobson_bot.1 (hjac (I.neg_mem hz)) 1
    simpa [sub_eq_add_neg, add_comm] using this
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨n, y', hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (Ideal.Quotient.mk I x) (1 : S ⧸ I)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
  simp only [smul_eq_mul, mul_one] at hy
  set X := Ideal.Quotient.mk I x with hX
  set Y := Ideal.Quotient.mk I y with hY
  have hk : ∀ k : ℕ, X ^ n * (X * Y) ^ k = X ^ n := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      calc X ^ n * (X * Y) ^ (k + 1) = (X ^ (n + 1) * Y) * (X * Y) ^ k := by ring
        _ = X ^ n := by rw [Nat.succ_eq_add_one] at hy; rw [hy, ih]
  have he : ((X * Y) ^ n) ^ 2 = (X * Y) ^ n := by
    calc ((X * Y) ^ n) ^ 2 = (X ^ n * (X * Y) ^ n) * Y ^ n := by ring
      _ = (X * Y) ^ n := by rw [hk]; ring
  have hE : Ideal.Quotient.mk I ((x * y) ^ n) = (X * Y) ^ n := by simp [hX, hY]
  obtain ⟨a, ha, hae⟩ := HenselianRing.is_henselian (I := I) (Polynomial.X ^ 2 - Polynomial.X : Polynomial S)
    (by monicity!) ((x * y) ^ n)
    (by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, map_sub]
      rw [map_pow, hE, he, sub_self])
    (by
      have : Ideal.Quotient.mk I (Polynomial.eval ((x * y) ^ n)
          (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.X : Polynomial S))) = 2 * (X * Y) ^ n - 1 := by
        rw [← hE]
        simp [one_add_one_eq_two, map_ofNat]
      rw [this]
      exact IsUnit.of_mul_eq_one (2 * (X * Y) ^ n - 1) (by linear_combination 4 * he))
  have ha' : a * (a - 1) = 0 := by
    have : a ^ 2 - a = 0 := by simpa using ha
    linear_combination this
  rcases mul_eq_zero.1 ha' with h0 | h0
  · right
    subst h0
    have h2 : (X * Y) ^ n = 0 := by
      rw [← hE, Ideal.Quotient.eq_zero_iff_mem]
      simpa using hae
    have h3 : x ^ n ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, ← hX, ← hk n, h2, mul_zero]
    exact isUnit_of_dvd_unit (one_sub_dvd_one_sub_pow x n) (hu _ h3)
  · obtain rfl : a = 1 := sub_eq_zero.1 h0
    have h2 := hu _ hae
    rw [sub_sub_cancel] at h2
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h3 := hk 1
      left
      have h4 : 1 - x * y ∈ I := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        simp only [pow_zero, pow_one, one_mul] at h3
        rw [map_sub, map_one, map_mul, ← hX, ← hY, h3, sub_self]
      have h5 := hu _ h4
      rw [sub_sub_cancel] at h5
      exact isUnit_of_mul_isUnit_left h5
    · left
      exact isUnit_of_mul_isUnit_left ((isUnit_pow_iff hn.ne').1 h2)

theorem local_complete_of_finite (R S : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] :
    ∃ _ : IsLocalRing S, IsAdicComplete (maximalIdeal S) S := by
  haveI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  haveI : IsPrecomplete (maximalIdeal R) S := precomplete_of_finite _ S
  haveI : IsAdicComplete (maximalIdeal R) S := ⟨⟩
  set I := (maximalIdeal R).map (algebraMap R S) with hI
  haveI : IsAdicComplete I S := (IsAdicComplete.map_algebraMap_iff _ _).2 inferInstance
  haveI : IsArtinianRing (S ⧸ I) := by
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    haveI : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ I) := Module.Finite.of_restrictScalars_finite R _ _
    exact IsArtinianRing.of_finite (R ⧸ maximalIdeal R) _
  haveI hl : IsLocalRing S := isLocalRing_of_complete I
  refine ⟨hl, ?_⟩
  have hne : I ≠ ⊤ := by
    intro h
    have := IsAdicComplete.le_jacobson_bot I
    rw [h, IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at this
    exact (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 this)
  have hrad : maximalIdeal S ≤ I.radical := by
    intro x hx
    obtain ⟨n, y', hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (Ideal.Quotient.mk I x) (1 : S ⧸ I)
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
    simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
    have hu : IsUnit (1 - x * y) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (Ideal.mul_mem_right y (maximalIdeal S) hx)
    refine ⟨n, (Ideal.mul_unit_mem_iff_mem I hu).1 ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_mul, map_pow, map_sub, map_one]
    linear_combination -hy
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  haveI : IsPrecomplete (maximalIdeal S) S :=
    precomplete_of_pow_le I _ (le_maximalIdeal hne) k ((Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk)
  exact ⟨⟩

theorem exists_normal (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : Type) [CommRing D] [IsDomain D]
    [Algebra R D] [Module.Finite R D] [FaithfulSMul R D] (hR : GlobalTheory.TorRef.IsCN R) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (σ : D →+* R'),
      GlobalTheory.TorRef.IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ σ.comp (algebraMap R D) = ρ := by
  obtain ⟨h1, h2, h3, h4⟩ := hR
  letI : Algebra (FractionRing R) (FractionRing D) := FractionRing.liftAlgebra R (FractionRing D)
  haveI : IsScalarTower R (FractionRing R) (FractionRing D) := FractionRing.isScalarTower_liftAlgebra R _
  haveI : FiniteDimensional (FractionRing R) (FractionRing D) :=
    Module.Finite.of_isLocalization R D (nonZeroDivisors R) (Rₚ := FractionRing R) (Sₚ := FractionRing D)
  haveI : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  haveI : Algebra.IsIntegral (FractionRing R) (FractionRing D) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable (FractionRing R) (FractionRing D) := Algebra.IsSeparable.of_integral _ _
  let S := integralClosure R (FractionRing D)
  haveI : Module.Finite R S := IsIntegralClosure.finite R (FractionRing R) (FractionRing D) S
  haveI : IsIntegrallyClosed S := integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)
  have hL : Function.Injective (algebraMap R (FractionRing D)) := FaithfulSMul.algebraMap_injective R _
  have hS : Function.Injective (algebraMap R S) := fun a b h => hL (congrArg Subtype.val h)
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).2 hS
  obtain ⟨hl, hc⟩ := local_complete_of_finite R S
  let ψ : D →ₐ[R] FractionRing D := IsScalarTower.toAlgHom R D _
  let σ : D →ₐ[R] S := ψ.codRestrict S fun c => (Algebra.IsIntegral.isIntegral c).map ψ
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite _ _
  refine ⟨S, inferInstance, inferInstance, hl, algebraMap R S, σ.toRingHom,
    ⟨IsNoetherianRing.of_finite R S, inferInstance, hc, charZero_of_injective_algebraMap hS⟩, hS,
    RingHom.finite_algebraMap.2 inferInstance, Algebra.IsIntegral.isLocalHom R S, σ.comp_algebraMap⟩

theorem main (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : Type) [CommRing C] (φ : R →+* C)
    (hR : GlobalTheory.TorRef.IsCN R) (hφ : Function.Injective φ) (hfin : φ.Finite) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (σ : C →+* R'),
      GlobalTheory.TorRef.IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ σ.comp φ = ρ := by
  letI : Algebra R C := φ.toAlgebra
  haveI : Module.Finite R C := hfin
  obtain ⟨P, -, hP, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (R := R) (S := C) (⊥ : Ideal R) ⊥
    (by rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot]; exact ((RingHom.injective_iff_ker_eq_bot _).1 hφ).le)
  have hD : Function.Injective (algebraMap R (C ⧸ P)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ P.comap (algebraMap R C) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      exact ha
    change a ∈ Ideal.under R P at this
    rwa [hPc] at this
  haveI : FaithfulSMul R (C ⧸ P) := (faithfulSMul_iff_algebraMap_injective _ _).2 hD
  obtain ⟨R', i1, i2, i3, ρ, σ, h1, h2, h3, h4, h5⟩ := exists_normal R (C ⧸ P) hR
  exact ⟨R', i1, i2, i3, ρ, σ.comp (Ideal.Quotient.mk P), h1, h2, h3, h4, h5⟩

end GlobalTheory.FiniteLocalCompleteness
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFormsTensorSectionGenericFibreTransitionGer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeySecRel

theorem appLE_map' {X Y : Scheme.{0}} (p : Y ⟶ X) {U V : X.Opens} (hVU : V ≤ U) {W : Y.Opens} (h : W ≤ p ⁻¹ᵁ V)
    (h' : W ≤ p ⁻¹ᵁ U) (a : Γ(X, U)) :
    (p.appLE V W h).hom ((X.presheaf.map (homOfLE hVU).op).hom a) = (p.appLE U W h').hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem appLE_app' {X Y S : Scheme.{0}} (p : Y ⟶ X) (π : X ⟶ S) {U : S.Opens} {W : Y.Opens}
    (h : W ≤ p ⁻¹ᵁ (π ⁻¹ᵁ U)) (h' : W ≤ (p ≫ π) ⁻¹ᵁ U) (a : Γ(S, U)) :
    (p.appLE _ W h).hom ((π.app U).hom a) = ((p ≫ π).appLE U W h').hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.comp_appLE]

theorem appLE_sec_tens {X Y S : Scheme.{0}} (p : Y ⟶ X) (π : X ⟶ S) (A : LB X) (hA : A.IsLB) (δ : LB S)
    (σ : (CechPic.tens A (δ.pull π)).Sec) (l : A.ι) (i i' : δ.ι) (W : Y.Opens)
    (h : W ≤ p ⁻¹ᵁ (CechPic.tens A (δ.pull π)).U (l, fun _ => i))
    (h' : W ≤ p ⁻¹ᵁ (CechPic.tens A (δ.pull π)).U (l, fun _ => i'))
    (hW : W ≤ (p ≫ π) ⁻¹ᵁ (δ.U i ⊓ δ.U i')) :
    (p.appLE _ W h).hom (σ.f (l, fun _ => i)) =
      ((p ≫ π).appLE _ W hW).hom (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) * (p.appLE _ W h').hom (σ.f (l, fun _ => i')) := by
  have hh : W ≤ p ⁻¹ᵁ ((CechPic.tens A (δ.pull π)).U (l, fun _ => i) ⊓ (CechPic.tens A (δ.pull π)).U (l, fun _ => i')) :=
    fun y hy => ⟨h hy, h' hy⟩
  have e := congrArg (p.appLE _ W hh).hom (σ.compat (l, fun _ => i) (l, fun _ => i'))
  rw [map_mul, appLE_map' p _ hh h, appLE_map' p _ hh h'] at e
  rw [e]
  congr 1
  have h1 : W ≤ p ⁻¹ᵁ (A.U l) := fun y hy => (h hy).1
  have h11 : W ≤ p ⁻¹ᵁ (A.U l ⊓ A.U l) := fun y hy => ⟨h1 hy, h1 hy⟩
  have hg : (p.appLE _ W h11).hom (A.g l l : Γ(X, A.U l ⊓ A.U l)) = 1 := by
    have := congrArg (fun u : Γ(X, A.U l)ˣ => (p.appLE _ W h1).hom (u : Γ(X, A.U l))) (hA.g_self l)
    simp only [Units.val_one, map_one] at this
    rw [← this]
    exact (appLE_map' p _ h1 h11 _).symm
  have h2 : W ≤ p ⁻¹ᵁ ((δ.pull π).U (fun _ => i) ⊓ (δ.pull π).U (fun _ => i')) := fun y hy => ⟨(h hy).2, (h' hy).2⟩
  have hd : ((δ.pull π).g (fun _ => i) (fun _ => i') : Γ(X, (δ.pull π).U (fun _ => i) ⊓ (δ.pull π).U (fun _ => i'))) =
      (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le δ (fun _ : PUnit => π) (fun _ => i) PUnit.unit))
        (inf_le_right.trans (LB.wchart_le δ (fun _ : PUnit => π) (fun _ => i') PUnit.unit)) :
        (δ.pull π).U (fun _ => i) ⊓ (δ.pull π).U (fun _ => i') ≤ π ⁻¹ᵁ (δ.U i ⊓ δ.U i'))).op).hom
        ((π.app _).hom (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i'))) := by
    unfold LB.pull LB.LinComb
    dsimp only
    erw [Fintype.prod_unique, zpow_one]
    rfl
  refine (map_mul _ _ _).trans ?_
  refine (congrArg₂ (· * ·) ((appLE_map' p _ hh h11 _).trans hg) (appLE_map' p _ hh h2 _)).trans ?_
  rw [_root_.one_mul]
  refine (congrArg (p.appLE _ W h2).hom hd).trans ?_
  have hW' : W ≤ p ⁻¹ᵁ (π ⁻¹ᵁ (δ.U i ⊓ δ.U i')) := hW
  exact (appLE_map' p _ h2 hW' _).trans (appLE_app' p π hW' hW _)

theorem genPt_appLE {S : Scheme.{0}} [IsIntegral S] (U : S.Opens) (hU : genericPoint S ∈ U) (a : Γ(S, U)) :
    ((KeyVals.genPt S).appLE U ⊤ (KeyVals.genPt_le U hU)).hom a =
      (Scheme.ΓSpecIso (CommRingCat.of (KeyVals.FF S))).inv.hom (S.presheaf.germ U (genericPoint S) hU a) := by
  have e := Scheme.fromSpecStalk_app (X := S) (x := genericPoint S) hU
  have : (KeyVals.genPt S).appLE U ⊤ (KeyVals.genPt_le U hU) =
      S.presheaf.germ U (genericPoint S) hU ≫ (Scheme.ΓSpecIso (S.presheaf.stalk (genericPoint S))).inv := by
    unfold KeyVals.genPt Scheme.Hom.appLE
    erw [e]
    simp only [Category.assoc]
    erw [← Functor.map_comp]
    refine congrArg (fun z => _ ≫ z) ?_
    refine (congrArg (fun z => _ ≫ (Spec (S.presheaf.stalk (genericPoint S))).presheaf.map z)
      (Subsingleton.elim _ (𝟙 _))).trans ?_
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [this]
  rfl

theorem locSec_eq_germ_mul : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), δ.IsLB → ∀ (i i' : δ.ι) (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i')
    (t t' : (KeyVals.bL L (KeyVals.genPt S)).L.Sec), KeyVals.IsLocSec σ i (KeyVals.genPt S) t →
    KeyVals.IsLocSec σ i' (KeyVals.genPt S) t' → ∀ j, t.f j =
      constFn (KeyVals.bG G (KeyVals.genPt S)).hom _ (S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i'))) * t'.f j := by
  intro S _ G _ _ L δ σ _ i i' h2 t t' ht ht' j
  have hc : pullback.fst G.hom (KeyVals.genPt S) ≫ G.hom =
      (KeyVals.bG G (KeyVals.genPt S)).hom ≫ KeyVals.genPt S := pullback.condition
  have hW : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤
      (pullback.fst G.hom (KeyVals.genPt S) ≫ G.hom) ⁻¹ᵁ (δ.U i ⊓ δ.U i') := by
    rw [hc]
    exact fun y _ => KeyVals.genPt_le _ h2 (Set.mem_univ _)
  have hl : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤
      pullback.fst G.hom (KeyVals.genPt S) ⁻¹ᵁ L.L.U (j PUnit.unit) :=
    LB.wchart_le L.L (fun _ : PUnit => pullback.fst G.hom (KeyVals.genPt S)) j PUnit.unit
  have h : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤ pullback.fst G.hom (KeyVals.genPt S) ⁻¹ᵁ
      (CechPic.tens L.L (δ.pull G.hom)).U (j PUnit.unit, fun _ => i) :=
    fun y hy => ⟨hl hy, Set.mem_iInter.2 fun _ => (hW hy).1⟩
  have h' : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤ pullback.fst G.hom (KeyVals.genPt S) ⁻¹ᵁ
      (CechPic.tens L.L (δ.pull G.hom)).U (j PUnit.unit, fun _ => i') :=
    fun y hy => ⟨hl hy, Set.mem_iInter.2 fun _ => (hW hy).2⟩
  rw [ht j h, ht' j h']
  refine (appLE_sec_tens _ G.hom L.L L.isLB δ σ _ i i' _ h h' hW).trans ?_
  congr 1
  unfold constFn
  rw [← genPt_appLE, ← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_comp_appLE]
  have key : ∀ {Y : Scheme.{0}} (f f' : Y ⟶ S) (_ : f = f') (U : S.Opens) (W : Y.Opens) (a : W ≤ f ⁻¹ᵁ U)
      (a' : W ≤ f' ⁻¹ᵁ U) (x : Γ(S, U)), (f.appLE U W a).hom x = (f'.appLE U W a').hom x := by
    intro Y f f' e; subst e; intros; rfl
  exact key _ _ hc _ _ _ _ _

end GlobalTheory.KeySecRel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyTrivialUnitCocycleScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CharKer

theorem appLE_eq_of_eq' {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem app_map_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.app U).hom x) = (f.appLE U V h).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]

theorem appLE_map_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V V' : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ V) (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h').op).hom ((f.appLE U V h).hom x) = (f.appLE U V' (h'.trans h)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem map_app_map_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} (hU : U' ≤ U)
    (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U') (h' : V ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.app U').hom ((Y.presheaf.map (homOfLE hU).op).hom x)) =
      (f.appLE U V h').hom x := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
    ← Category.assoc, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem appLE_map_top {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
    (x : Γ(Y, ⊤)) :
    (f.appLE U V e).hom ((Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom x) =
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (f.appTop.hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 2
  simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
  rw [Scheme.Hom.naturality_assoc, ← Functor.map_comp]
  rfl

theorem map_map_apply {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (h₃ : W ≤ U)
    (x : Γ(X, U)) : (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom x) =
      (X.presheaf.map (homOfLE h₃).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.CharKer

namespace GlobalTheory.CharKer

theorem exists_local_charUnit : ∀ (X Y Z W : Scheme.{0}) (p : X ⟶ Y) (a b : Z ⟶ X) (m₁₂ m₂₃ m₁₃ : W ⟶ Z) (χ : Γ(Z, ⊤)ˣ), IsAffineHom p → Flat p → Surjective p → IsPullback b a p p → IsPullback m₁₂ m₂₃ a b → m₁₃ ≫ b = m₁₂ ≫ b → m₁₃ ≫ a = m₂₃ ≫ a → pullTop m₁₃ χ = pullTop m₁₂ χ * pullTop m₂₃ χ → ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ e : Γ(X, p ⁻¹ᵁ V)ˣ, ∀ (W' : Z.Opens) (h₁ : W' ≤ a ⁻¹ᵁ (p ⁻¹ᵁ V)) (h₂ : W' ≤ b ⁻¹ᵁ (p ⁻¹ᵁ V)), res h₁ (pullU a _ e) = res le_top χ * res h₂ (pullU b _ e) := by
  intro X Y Z W p a b m₁₂ m₂₃ m₁₃ χ hpA hpF hpS sq₁ sq₂ e₁₃b e₁₃a hχ y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
  have ha : IsAffineHom a := MorphismProperty.of_isPullback (P := @IsAffineHom) sq₁ hpA
  have hab : a ⁻¹ᵁ (p ⁻¹ᵁ V) = b ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq₁.w]
  have h12 : m₂₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) ≤ m₁₂ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) := by
    rw [← Scheme.Hom.comp_preimage m₁₂ a, sq₂.w, Scheme.Hom.comp_preimage, ← hab]
  have h13 : m₂₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) ≤ m₁₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) := by
    rw [← Scheme.Hom.comp_preimage m₁₃ a, e₁₃a, Scheme.Hom.comp_preimage]
  have hV₀ : IsAffineOpen (p ⁻¹ᵁ V) := hV.preimage p
  have hV₁ : IsAffineOpen (a ⁻¹ᵁ (p ⁻¹ᵁ V)) := hV₀.preimage a
  have P₁ := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq₁ hpA hV hV₀ le_rfl hab.le
  rw [Scheme.Hom.appLE_eq_app] at P₁
  have P₂ := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq₂ ha hV₀ hV₁ hab.le h12
  have E₁ : b.appLE (p ⁻¹ᵁ V) (a ⁻¹ᵁ (p ⁻¹ᵁ V)) hab.le ≫ m₁₃.appLE _ _ h13 =
      b.appLE (p ⁻¹ᵁ V) (a ⁻¹ᵁ (p ⁻¹ᵁ V)) hab.le ≫ m₁₂.appLE _ _ h12 := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_of_eq' e₁₃b _ _ _ _
  have E₂ : a.app (p ⁻¹ᵁ V) ≫ m₁₃.appLE _ _ h13 = a.app (p ⁻¹ᵁ V) ≫ m₂₃.app _ := by
    rw [Scheme.Hom.app_eq_appLE a, Scheme.Hom.app_eq_appLE m₂₃, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_of_eq' e₁₃a _ _ _ _
  have FF := _root_.GlobalTheory.faithfullyFlat_app_of_isAffineHom_flat_surjective X Y p V hpA hpF hpS hV
  let c : Γ(Z, a ⁻¹ᵁ (p ⁻¹ᵁ V))ˣ := res le_top χ
  have hc : (m₁₃.appLE _ _ h13).hom (c : Γ(Z, a ⁻¹ᵁ (p ⁻¹ᵁ V))) =
      (m₁₂.appLE _ _ h12).hom (c : Γ(Z, a ⁻¹ᵁ (p ⁻¹ᵁ V))) * (m₂₃.app _).hom (c : Γ(Z, a ⁻¹ᵁ (p ⁻¹ᵁ V))) := by
    have := congrArg (fun u => ((res (le_top : m₂₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) ≤ ⊤) u : Γ(W, _)ˣ) :
      Γ(W, m₂₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V))))) hχ
    simp only [map_mul, Units.val_mul, res, pullTop, Units.coe_map, MonoidHom.coe_coe] at this
    rw [Scheme.Hom.app_eq_appLE m₂₃]
    simp only [c, res, Units.coe_map, MonoidHom.coe_coe]
    rw [appLE_map_top, appLE_map_top, appLE_map_top]
    exact this
  obtain ⟨s, hs, x, x', hxx', hx⟩ := GlobalTheory.T.locally_trivial_unit_cocycle_faithfully_flat _ _ _ _ (p.app V) _ _ _ _ _ P₁ P₂ E₁ E₂ FF c hc
    (hV.primeIdealOf ⟨y, hyV⟩).asIdeal inferInstance
  have hyS : y ∈ Y.basicOpen s := by
    have h0 : hV.primeIdealOf ⟨y, hyV⟩ ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen s := by
      rw [hV.fromSpec_preimage_basicOpen]; exact hs
    have h1 := hV.fromSpec_primeIdealOf ⟨y, hyV⟩
    have h0' : hV.fromSpec (hV.primeIdealOf ⟨y, hyV⟩) ∈ Y.basicOpen s := h0
    rwa [h1] at h0'
  refine ⟨Y.basicOpen s, hyS, ?_⟩
  have hle : p ⁻¹ᵁ Y.basicOpen s ≤ p ⁻¹ᵁ V := fun z hz => Y.basicOpen_le s hz
  have hpre := Scheme.preimage_basicOpen p s
  have hu : IsUnit ((X.presheaf.map (homOfLE hle).op).hom x) := by
    apply isUnit_of_mul_isUnit_left (y := (X.presheaf.map (homOfLE hle).op).hom x')
    rw [← map_mul, hxx']
    have h2 := RingedSpace.isUnit_res_basicOpen X.toRingedSpace ((p.app V).hom s)
    have h3 := h2.map (X.presheaf.map (homOfLE hpre.le).op).hom
    rw [← map_map_apply (X.basicOpen_le ((p.app V).hom s)) hpre.le hle]
    exact h3
  refine ⟨hu.unit, fun W' h₁ h₂ => ?_⟩
  have hW : W' ≤ a ⁻¹ᵁ (p ⁻¹ᵁ V) := fun z hz => hle (h₁ hz)
  have hWb : W' ≤ b ⁻¹ᵁ (p ⁻¹ᵁ V) := hW.trans hab.le
  apply Units.ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, IsUnit.unit_spec, Units.val_mul]
  rw [map_app_map_eq_appLE a hle W' h₁ hW, map_app_map_eq_appLE b hle W' h₂ hWb]
  have := congrArg (Z.presheaf.map (homOfLE hW).op).hom hx
  rw [map_mul, app_map_eq_appLE, appLE_map_eq_appLE] at this
  rw [this]
  congr 1
  simp only [c, res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.CharKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCartierMultipleChartIffRegularCodimOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.ChartHartogs

theorem stalk_normal (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (p : PrimeSpectrum R) :
    IsDomain ((Spec.structureSheaf R).presheaf.stalk p) ∧ IsIntegrallyClosed ((Spec.structureSheaf R).presheaf.stalk p) :=
  ⟨IsLocalization.isDomain_of_le_nonZeroDivisors (R := R) (M := p.asIdeal.primeCompl) (S := (Spec.structureSheaf R).presheaf.stalk p) (hM := p.asIdeal.primeCompl_le_nonZeroDivisors),
    isIntegrallyClosed_of_isLocalization _ p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors⟩

theorem chart_normal (σ : Setup) (x : Sp σ.R) :
    IsLocallyNoetherian (σ.C x).G.left ∧ ∀ z : (σ.C x).G.left, IsIntegrallyClosed ((σ.C x).G.left.presheaf.stalk z) := by
  have hs : Smooth (σ.C x).G.hom := (σ.C x).semi.smooth
  obtain ⟨h1, h2⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (σ.C x).R
  refine ⟨LocallyOfFiniteType.isLocallyNoetherian (σ.C x).G.hom, fun z => ?_⟩
  have := (stalk_normal (σ.C x).R ((σ.C x).G.hom z)).1
  have := (stalk_normal (σ.C x).R ((σ.C x).G.hom z)).2
  exact (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_of_smooth (σ.C x).G.hom z).2

theorem mem_sec_iff : ∀ (σ : Setup) (x : Sp σ.R) (k : ℕ) (v : (σ.C x).G.left.functionField), v ∈ Sec (σ.D₁ x) k ↔ (∀ z : (σ.V x).toScheme, (k • σ.D₁ x).RegularAt ((σ.V x).ι z) v) ∧ ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → RegAt z v := by
  intro σ x k v
  have hV1 : ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → (k • σ.D₁ x).IsEqn z 1 := fun z hz => by
    simpa using (σ.noVert x z hz).nsmul k
  constructor
  · intro h
    refine ⟨fun z => h _, fun z hz => ?_⟩
    have := (hV1 z hz).regularAt_iff.1 (h z)
    simpa using this
  · rintro ⟨h1, h2⟩ y
    obtain ⟨hLN, hN⟩ := chart_normal σ x
    obtain ⟨g, hg⟩ := (k • σ.D₁ x).exists_isEqn y
    obtain ⟨U, hyU, hU⟩ := hg.exists_nhds
    refine hg.regularAt_iff.2 (GlobalTheory.Hartogs.regAt_of_forall_dvr _ hN _ y fun z hzy hdvr => ?_)
    have hgz := hU z (hzy.mem_open U.isOpen hyU)
    by_cases hzV : z ∈ σ.V x
    · have := h1 ⟨z, hzV⟩
      rw [Scheme.Opens.ι_apply] at this
      exact hgz.regularAt_iff.1 this
    · have hv : Vert (σ.C x).G.hom (σ.ρ x σ.f) z :=
        ⟨IsDiscreteValuationRing.ringKrullDim_eq_one _, not_not.1 fun h => hzV ((σ.hV x z).2 h)⟩
      exact hgz.regularAt_iff.1 ((hV1 z hv).regularAt_iff.2 (by simpa using h2 z hv))

end GlobalTheory.Desc.ChartHartogs
end
end

