module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2143
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0486
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTorsionBundleAbelianSchemeSqZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CechPic

theorem pow_add_sqZero {A : Type*} [CommRing A] (v M : A) (hM : M * M = 0) (k : ℕ) :
    (v + M) ^ (k + 1) = v ^ (k + 1) + (k + 1) * M * v ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]; push_cast
    linear_combination ((k : A) + 1) * v ^ k * hM

theorem sqZero_root_correction_mul_pow_eq_zero {A : Type*} [CommRing A] {G Sa Sb Na Nb H M : A} (k : ℕ)
    (hS : Sa = G ^ (k + 1) * Sb) (hNa : Na = Sa - 1) (hNb : Nb = Sb - 1) (hNa2 : Na * Na = 0)
    (hNb2 : Nb * Nb = 0) (hH : ((k + 1 : ℕ) : A) * H = 1) (hM : M = (1 + Na * H) - G * (1 + Nb * H))
    (hM2 : M * M = 0) : M * (G * (1 + Nb * H)) ^ k = 0 := by
  push_cast at hH
  have r1 : ∀ N : A, N * N = 0 → (1 + N * H) ^ (k + 1) = 1 + N := fun N hN => by
    rw [pow_add_sqZero 1 (N * H) (by linear_combination H ^ 2 * hN) k, one_pow, one_pow]
    linear_combination N * hH
  have e1 : (1 + Na * H) ^ (k + 1) = Sa := by rw [r1 Na hNa2]; linear_combination hNa
  have e2 : (G * (1 + Nb * H)) ^ (k + 1) = G ^ (k + 1) * Sb := by
    rw [mul_pow, r1 Nb hNb2]; linear_combination G ^ (k + 1) * hNb
  have e3 := pow_add_sqZero (G * (1 + Nb * H)) M hM2 k
  have hu : G * (1 + Nb * H) + M = 1 + Na * H := by linear_combination hM
  rw [hu] at e3
  linear_combination H * (e1 - e2 + hS - e3) - M * (G * (1 + Nb * H)) ^ k * hH

end GlobalTheory.CechPic

namespace GlobalTheory.CechPic

open scoped CategoryTheory.Obj
open IsLocalRing

theorem eq_zero_of_sqZero_baseChange_nsmul : ∀ (k : ℕ) (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → IsUnit ((k + 1 : ℕ) : R) →
    ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s₀ : X₀ ⟶ Sp R₀) (i : X₀ ⟶ X), IsPullback i s₀ s (spMap π) →
    Function.Surjective i.appTop.hom → ∀ m : GlobalTheory.CechPic.Pic X, GlobalTheory.CechPic.pull i m = 0 →
    (k + 1) • m = 0 → m = 0 := by
  intro k R R₀ _ _ π hπ hk h2 X X₀ s s₀ i hP hsurj m hm hm2
  haveI : IsClosedImmersion (spMap π) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom π) hπ
  haveI : IsClosedImmersion i :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hP.flip inferInstance
  haveI : Surjective i := GlobalTheory.LiftSys.surjective_of_isPullback_sqZero (I := RingHom.ker π)
    (by rw [hk]; rfl) hπ rfl hP
  have hsq : ∀ (W : X.Opens) (x y : Γ(X, W)), (i.app W).hom x = 0 → (i.app W).hom y = 0 → x * y = 0 :=
    GlobalTheory.SquareZero.mul_eq_zero_of_app_eq_zero R R₀ π hπ hk X X₀ s s₀ i hP
  obtain ⟨D, hD, rfl, hD1⟩ := exists_cocycle_one_on_thickening X X₀ i m hm
  have h2X : IsUnit ((k + 1 : ℕ) : Γ(X, ⊤)) := by
    have := h2.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
    rwa [map_natCast] at this
  rw [← cls_lbPow hD (k + 1) (LB.isLB_linComb hD _ _), cls_eq_zero_iff] at hm2
  obtain ⟨σ₂, hσ₂⟩ := hm2
  have hle : ∀ a, D.U a ≤ (lbPow D (k + 1)).U (fun _ => a) := fun a y hy =>
    Set.mem_iInter.2 fun _ => hy
  let σ : ∀ a, Γ(X, D.U a)ˣ := fun a => res (hle a) (σ₂.s (fun _ => a))
  have hσ : ∀ a b, res (inf_le_left : D.U a ⊓ D.U b ≤ D.U a) (σ a) =
      D.g a b ^ (k + 1) * res inf_le_right (σ b) := by
    intro a b
    refine unit_ext fun y hy => ?_
    have e := (isGen_iff_germ σ₂).1 hσ₂ y (fun _ => a) (fun _ => b) (hle a hy.1) (hle b hy.2)
    have hg := gm_linComb D (fun _ : PUnit => 𝟙 X) (fun _ => ((k + 1 : ℕ) : ℤ)) (𝟙 X) y
      (fun _ => a) (fun _ => b) (hle a hy.1) (hle b hy.2)
    rw [Fintype.prod_unique, Category.id_comp, zpow_natCast] at hg
    erw [hg] at e
    rw [map_mul, map_pow, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy]
    dsimp only [σ]
    erw [gm_res (𝟙 X) y (hle a) hy.1, gm_res (𝟙 X) y (hle b) hy.2]
    exact e
  have hg1 : ∀ a b (y : X₀) (hy : i y ∈ D.U a ⊓ D.U b), gm i y _ (D.g a b) = 1 := by
    intro a b y hy
    have e := gm_pull (𝟙 X₀) i y (D.U a ⊓ D.U b) hy (D.g a b)
    rw [Category.id_comp, hD1 a b, map_one] at e
    exact e.symm
  have hσi : ∀ a b (y : X₀) (ha : i y ∈ D.U a) (hb : i y ∈ D.U b), gm i y _ (σ a) = gm i y _ (σ b) := by
    intro a b y ha hb
    have hab : i y ∈ D.U a ⊓ D.U b := ⟨ha, hb⟩
    rw [← gm_res i y (inf_le_left : D.U a ⊓ D.U b ≤ D.U a) hab, hσ a b, map_mul, map_pow,
      hg1 a b y hab, gm_res i y inf_le_right hab, one_pow, _root_.one_mul]
  have hpi : ∀ a (y : X₀) (ha : i y ∈ D.U a), gm (𝟙 X₀) y (i ⁻¹ᵁ D.U a) (pullU i _ (σ a)) = gm i y _ (σ a) := by
    intro a y ha
    rw [gm_pull (𝟙 X₀) i y _ ha, Category.id_comp]
  obtain ⟨U₀, hU₀⟩ := glue_unit (X := X₀) (i ⁻¹ᵁ ⊤) (fun a => i ⁻¹ᵁ D.U a) (fun a _ _ => trivial)
    (fun y _ => TopologicalSpace.Opens.mem_iSup.2 (exists_chart hD (i y))) (fun a => pullU i _ (σ a))
    (fun a b y hy => by rw [hpi a y hy.1, hpi b y hy.2]; exact hσi a b y hy.1 hy.2)
  obtain ⟨v, hv⟩ := hsurj (show Γ(X₀, ⊤) from U₀.val)
  have hvu : IsUnit v := X.toRingedSpace.isUnit_of_isUnit_germ ⊤ v fun x hx => by
    obtain ⟨y, rfl⟩ := Surjective.surj (f := i) x
    have h1 : IsUnit ((i.stalkMap y).hom ((X.presheaf.germ ⊤ (i y) hx).hom v)) := by
      rw [Scheme.Hom.germ_stalkMap_apply]
      erw [hv]
      exact U₀.isUnit.map _
    exact isUnit_of_map_unit _ _ h1
  let Vu : Γ(X, ⊤)ˣ := hvu.unit
  have hVu : ∀ (y : X₀), gm i y ⊤ Vu = gm (𝟙 X₀) y (i ⁻¹ᵁ ⊤) U₀ := by
    intro y
    have e := gm_pull (𝟙 X₀) i y ⊤ trivial Vu
    rw [Category.id_comp] at e
    rw [← e]
    congr 1
    exact Units.ext hv
  let σ' : ∀ a, Γ(X, D.U a)ˣ := fun a => σ a * res (le_top : D.U a ≤ ⊤) Vu⁻¹
  have hσ'1 : ∀ a, (i.app (D.U a)).hom (σ' a).val = 1 := by
    intro a
    have e : pullU i (D.U a) (σ' a) = 1 := unit_ext fun y hy => by
      rw [map_one, gm_pull (𝟙 X₀) i y _ hy, Category.id_comp]
      dsimp only [σ']
      rw [map_mul, gm_res i y le_top hy, map_inv, hVu y, ← hpi a y hy, ← hU₀ a]
      erw [gm_res (𝟙 X₀) y (fun _ _ => trivial : i ⁻¹ᵁ D.U a ≤ i ⁻¹ᵁ ⊤) hy]
      exact mul_inv_cancel _
    exact congrArg Units.val e
  have hσ' : ∀ a b, res (inf_le_left : D.U a ⊓ D.U b ≤ D.U a) (σ' a) =
      D.g a b ^ (k + 1) * res inf_le_right (σ' b) := by
    intro a b
    dsimp only [σ']
    rw [map_mul, map_mul, hσ a b]
    simp only [res_res, _root_.mul_assoc]
  let n : ∀ a, Γ(X, D.U a) := fun a => (σ' a).val - 1
  have hn0 : ∀ a, (i.app (D.U a)).hom (n a) = 0 := fun a => by
    simp only [n, map_sub, map_one, hσ'1 a, sub_self]
  have hn2 : ∀ a, n a * n a = 0 := fun a => hsq _ _ _ (hn0 a) (hn0 a)
  let Hh : ∀ a, Γ(X, D.U a) := fun a => (res (le_top : D.U a ≤ ⊤) h2X.unit⁻¹).val
  let t : ∀ a, Γ(X, D.U a) := fun a => 1 + n a * Hh a
  have ht : ∀ a, IsUnit (t a) := fun a =>
    IsUnit.of_mul_eq_one (1 - n a * Hh a) (by linear_combination (-(Hh a * Hh a)) * hn2 a)
  have hti : ∀ a, (i.app (D.U a)).hom (t a) = 1 := fun a => by
    simp only [t, map_add (f := _), map_one, map_mul, hn0 a, zero_mul, add_zero]
  refine (cls_eq_zero_iff hD).2 ⟨⟨fun a => (ht a).unit⟩, fun a b => ?_⟩
  apply Units.ext
  let ρa := (X.presheaf.map (homOfLE (inf_le_left : D.U a ⊓ D.U b ≤ D.U a)).op).hom
  let ρb := (X.presheaf.map (homOfLE (inf_le_right : D.U a ⊓ D.U b ≤ D.U b)).op).hom
  let ρt := (X.presheaf.map (homOfLE (le_top : D.U a ⊓ D.U b ≤ ⊤)).op).hom
  show ρa (t a) = (D.g a b).val * ρb (t b)
  let Hc : Γ(X, D.U a ⊓ D.U b) := (res (le_top : D.U a ⊓ D.U b ≤ ⊤) h2X.unit⁻¹).val
  have hHa : ρa (Hh a) = Hc := congrArg Units.val (res_res inf_le_left le_top h2X.unit⁻¹)
  have hHb : ρb (Hh b) = Hc := congrArg Units.val (res_res inf_le_right le_top h2X.unit⁻¹)
  have hH : ((k + 1 : ℕ) : Γ(X, D.U a ⊓ D.U b)) * Hc = 1 := by
    show ((k + 1 : ℕ) : Γ(X, D.U a ⊓ D.U b)) * ρt h2X.unit⁻¹.val = 1
    rw [show ((k + 1 : ℕ) : Γ(X, D.U a ⊓ D.U b)) = ρt ((k + 1 : ℕ) : Γ(X, ⊤)) from (map_natCast ρt _).symm,
      ← map_mul, h2X.mul_val_inv, map_one]
  have hS : ρa (σ' a).val = (D.g a b).val ^ (k + 1) * ρb (σ' b).val := by
    have := congrArg Units.val (hσ' a b)
    rw [Units.val_mul, Units.val_pow_eq_pow_val] at this
    exact this
  have hNa : ρa (n a) = ρa (σ' a).val - 1 := by simp only [n, map_sub, map_one]
  have hNb : ρb (n b) = ρb (σ' b).val - 1 := by simp only [n, map_sub, map_one]
  have hNa2 : ρa (n a) * ρa (n a) = 0 := by rw [← map_mul, hn2 a, map_zero]
  have hNb2 : ρb (n b) * ρb (n b) = 0 := by rw [← map_mul, hn2 b, map_zero]
  have hTa : ρa (t a) = 1 + ρa (n a) * Hc := by simp only [t, map_add (f := _), map_one, map_mul, hHa]
  have hTb : ρb (t b) = 1 + ρb (n b) * Hc := by simp only [t, map_add (f := _), map_one, map_mul, hHb]
  have hG1 : (i.app (D.U a ⊓ D.U b)).hom (D.g a b).val = 1 := congrArg Units.val (hD1 a b)
  have hM0 : (i.app (D.U a ⊓ D.U b)).hom (ρa (t a) - (D.g a b).val * ρb (t b)) = 0 := by
    rw [map_sub, map_mul, app_restrict, app_restrict, hti a, hti b, hG1, map_one, map_one,
      _root_.one_mul, sub_self]
  have key := sqZero_root_correction_mul_pow_eq_zero k hS hNa hNb hNa2 hNb2 hH (by rw [hTa, hTb]) (hsq _ _ _ hM0 hM0)
  have hu : IsUnit (((D.g a b).val * (1 + ρb (n b) * Hc)) ^ k) :=
    ((D.g a b).isUnit.mul (hTb ▸ (ht b).map ρb)).pow k
  exact sub_eq_zero.1 (hu.mul_left_eq_zero.1 key)

end GlobalTheory.CechPic

namespace GlobalTheory.CechPic

theorem exists_isGen_of_lbPow_of_sqZero_abelianScheme : ∀ (T : Type) [CommRing T] [IsLocalRing T] (e : T),
    (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) → e ∈ IsLocalRing.maximalIdeal T →
    ∀ (A : Over (Sp T)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ k : ℕ,
    IsUnit (k : T) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) →
    ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (f' : X' ⟶ Sp (T ⧸ Ideal.span {e})),
    IsPullback π f' A.hom (spMap (Ideal.Quotient.mk (Ideal.span {e}))) →
    (∃ t : (M.pull π).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen := by
  intro T _ _ e hme hem A _ hA M hM k hk hpow X' π f' hP hπ
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := by
    cases k with
    | zero => exact absurd hk (by rw [Nat.cast_zero]; exact not_isUnit_zero)
    | succ k => exact ⟨k, rfl⟩
  set q := Ideal.Quotient.mk (Ideal.span {e})
  have hee : e * e = 0 := hme e hem
  have hker : RingHom.ker q ^ 2 = ⊥ := by
    rw [Ideal.mk_ker, Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot, pow_two, hee]
  haveI : IsClosedImmersion (spMap q) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom q) Ideal.Quotient.mk_surjective
  have hq : Function.Surjective (spMap q).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (spMap q)).2
  have hf' : Function.Bijective f'.appTop.hom :=
    GlobalTheory.AbLaw.CubeOpen.bijective_appTop GlobalTheory.globalFns_holds A hA hP
  have hsurj : Function.Surjective π.appTop.hom := by
    intro w
    obtain ⟨c, rfl⟩ := hf'.2 w
    obtain ⟨d, rfl⟩ := hq c
    refine ⟨A.hom.appTop d, ?_⟩
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, hP.w]
  have hpull : pull π (cls M hM) = 0 := by
    rw [← cls_pull hM π (pull_isLB hM π), cls_eq_zero_iff]
    exact hπ
  have hnsmul : (k + 1) • cls M hM = 0 := by
    have h := cls_linComb hM (fun _ : Fin (k + 1) => 𝟙 A.left) (fun _ => 1) (LB.isLB_linComb hM _ _)
    have h0 : cls (LB.LinComb M (fun _ : Fin (k + 1) => 𝟙 A.left) (fun _ => 1)) (LB.isLB_linComb hM _ _) = 0 :=
      (cls_eq_zero_iff _).2 hpow
    rw [h0] at h
    simpa [pull_id] using h.symm
  exact (cls_eq_zero_iff hM).1 (eq_zero_of_sqZero_baseChange_nsmul k T (T ⧸ Ideal.span {e}) q
    Ideal.Quotient.mk_surjective hker hk A.left X' A.hom f' π hP hsurj _ hpull hnsmul)

end GlobalTheory.CechPic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibresCommonPullDegToField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GenericPull

open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull GlobalTheory.FieldPull

theorem nonempty_isPullDeg_cancel {R K₁ K : Type} [CommRing R] [IsDomain R] [Field K₁] [Field K] {α : R →+* K₁}
    (hα : Function.Injective α) (β : K₁ →+* K) {D₀ : DegPre R} {D₁ : DegPre K₁} {D : DegPre K}
    (h₁ : IsPullDeg α D₀ D₁) (h : IsPullDeg (β.comp α) D₀ D) : Nonempty (IsPullDeg β D₁ D) := by
  have p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w ((isGen_iff _).1 h₁.w_gen)
    ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (pmaps_rig h₁) (pmaps_rig h)
  let xe : D.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨hD, -, -, -⟩ := exists_isPullDeg_of_val β D₁ D gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have sβ : jK K ≫ spMap β = genMap β.injective ≫ jK K₁ :=
      (Category.id_comp _).symm.trans (fracMap_sq β.injective)
    have sα : jK K₁ ≫ spMap α = genMap hα ≫ jK R :=
      (Category.id_comp _).symm.trans (fracMap_sq hα)
    have q₁ : genMap β.injective ≫ jK K₁ ≫ spMap α = (genMap β.injective ≫ genMap hα) ≫ jK R :=
      (congrArg (_ ≫ ·) sα).trans (Category.assoc _ _ _).symm
    have q : 𝟙 (TK K).left ≫ jK K ≫ spMap (β.comp α) = (genMap β.injective ≫ genMap hα) ≫ jK R :=
      (Category.id_comp _).trans ((congrArg (_ ≫ ·) sc.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) sβ).trans ((Category.assoc _ _ _).trans q₁))))
    have v := psi_val h _ _ q hJ₀ hJ x
    have v₁ := psi_val h₁ _ _ q₁ hJ₀ hJ₁ (xe x)
    have hx : D.xK x ≫ Φ = genMap β.injective ≫ D₁.xK (xe x) := by
      show (jK K ≫ (D.c x).left) ≫ Φ = genMap β.injective ≫ jK K₁ ≫ (D₁.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    rw [hxe, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD⟩

theorem exists_generic_fibre {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) :
    ∃ E : DegPre (FractionRing R), Nonempty (IsPullDeg (algebraMap R (FractionRing R)) D E) := by
  obtain ⟨U, hU, hψ⟩ := PsiSpread.exists_psiOn D hB
  obtain ⟨E, p, -⟩ := DegPull.exists_isPullDeg polBaseChange_holds R (FractionRing R) (algebraMap R (FractionRing R))
    D U hψ (TauPull.jK_mem (R := R) (genericPoint (Spec (CommRingCat.of (FractionRing R)))) U ⟨_, hU⟩)
  exact ⟨E, ⟨p⟩⟩

end GlobalTheory.GenericPull

namespace GlobalTheory.Mum

open GlobalTheory.GenericPull

theorem exists_generic_common_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ D₂ : DegData R (maximalIdeal R)) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ D' : DegPre W, IsPullDeg φ D₁.toPre D' → IsPullDeg φ D₂.toPre D' → ∃ (E₁ E₂ : DegPre (FractionRing R)) (L : Type) (_ : Field L) (β : FractionRing R →+* L) (E' : DegPre L), Nonempty (IsPullDeg (algebraMap R (FractionRing R)) D₁.toPre E₁) ∧ Nonempty (IsPullDeg (algebraMap R (FractionRing R)) D₂.toPre E₂) ∧ Nonempty (IsPullDeg β E₁ E') ∧ Nonempty (IsPullDeg β E₂ E') := by
  intro R _ _ _ _ D₁ D₂ W _ _ φ hφ D' p₁ p₂
  obtain ⟨E₁, ⟨q₁⟩⟩ := exists_generic_fibre D₁.toPre D₁.tau_bimult
  obtain ⟨E₂, ⟨q₂⟩⟩ := exists_generic_fibre D₂.toPre D₂.tau_bimult
  obtain ⟨E', ⟨q⟩⟩ := exists_generic_fibre D' (TauPull.tauBimult_pull globalFns_holds p₁ D₁.tau_bimult)
  have e : (algebraMap W (FractionRing W)).comp φ = (ArcPull.fracMap hφ).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun x => (ArcPull.fracMap_algebraMap hφ x).symm
  have hR := IsFractionRing.injective R (FractionRing R)
  have hW := IsFractionRing.injective W (FractionRing W)
  obtain ⟨r₁⟩ := e ▸ PullDegComp.nonempty_isPullDeg_comp hφ hW p₁ q
  obtain ⟨r₂⟩ := e ▸ PullDegComp.nonempty_isPullDeg_comp hφ hW p₂ q
  exact ⟨E₁, E₂, FractionRing W, inferInstance, ArcPull.fracMap hφ, E', ⟨q₁⟩, ⟨q₂⟩,
    nonempty_isPullDeg_cancel hR _ q₁ r₁, nonempty_isPullDeg_cancel hR _ q₂ r₂⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointsEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

namespace GlobalTheory.GenRestrict

theorem unifPre_generic {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) :
    IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ∧
      LBIso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R))) := by
  have := U.gen_hom
  refine ⟨?_, ?_⟩
  · have : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  · have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    have hext : LBIso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R))) := U.ext
    have h1 : LBIso (A.L.pull (U.gen.inv.left ≫ U.gen.hom.left))
        (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R))) :=
      LBIso.chartPull (chartPullSame A.L _ (fun _ => U.gen.hom.left) _ U.gen.inv.left fun _ => rfl)
        (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ U.gen.inv.left fun _ => rfl) hext
    exact LBIso.chartPull (chartPullUnpull A.L _ hgi)
      (chartPullSame U.LG.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : B →+* C) (b : A →+* B) :
    spMap (a.comp b) = spMap a ≫ spMap b := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem weilIs_congr_base {S X : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (k : ℤ) {a b : X ⟶ S}
    (hab : a = b) (x y : Over.mk a ⟶ G) (x' y' : Over.mk b ⟶ G) (hx : x.left = x'.left) (hy : y.left = y'.left)
    (c : Γ(X, ⊤)ˣ) : WeilIs G L k x y c ↔ WeilIs G L k x' y' c := by
  subst hab
  obtain rfl : x = x' := Over.OverMorphism.ext hx
  obtain rfl : y = y' := Over.OverMorphism.ext hy
  exact Iff.rfl

end GlobalTheory.GenRestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodLabRankOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Recog

variable {R : Type} [CommRing R] [IsDomain R]

structure GoodLab (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (f : ∀ k : ℕ, QkPt D F k → (TFK (R := R) F ⟶ A.A)) : Prop where
  pow : ∀ k, 1 ≤ k → ∀ p, f k p ^ k = 1
  onto : ∀ k, 1 ≤ k → ∀ x : TFK (R := R) F ⟶ A.A, x ^ k = 1 → ∃ p, f k p = x
  eqv : ∀ k, 1 ≤ k → ∀ p p', f k p = f k p' ↔ QkPt.Equiv D F p p'
  add : ∀ k, 1 ≤ k → ∀ p p' p'', QkAdd p p' p'' → f k p'' = f k p * f k p'
  weil : ∀ k, 1 ≤ k → ∀ p p' (z : Fˣ), WeilQkIs D F k p p' z → WeilIs A.A A.L k (f k p) (f k p') (unitOn z)
  level : ∀ k m N, 1 ≤ k → 1 ≤ m → N = k * m → ∀ (p : QkPt D F k) (q : QkPt D F N), q.y = m • p.y → q.g = p.g →
    f N q = f k p

def Lies {W : Type} [CommRing W] [IsDomain W] (φ : R →+* W) {D : DegPre R} {D' : DegPre W} (hD : IsPullDeg φ D D')
    {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F']
    [Algebra (FractionRing W) F'] (em : F →+* F') {k : ℕ} (p : QkPt D F k) (p' : QkPt D' F' k) : Prop :=
  ∃ p₁ : QkPt D F' k, QkExt em p p₁ ∧ p'.y = hD.xe.symm p₁.y ∧ IsPullGtF φ hD F' p₁.g p'.g

theorem exists_goodLab [CharZero R] {I : Ideal R} (hR : AdmBase R I) {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) (F : Type) [Field F]
    [IsAlgClosed F] [Algebra (FractionRing R) F] :
    ∃ f, GoodLab D.toPre A F f ∧ ∀ k, 1 ≤ k → ∀ p x, QkToAkU U.toUnifPre F k p x ↔ x = f k p := by
  have H : ∀ k : ℕ, ∃ f : QkPt D.toPre F k → (TFK (R := R) F ⟶ A.A), 1 ≤ k →
      GlobalTheory.UT.Tors U.toUnifPre F k f ∧ ∀ p, f p ^ k = 1 := fun k => by
    by_cases hk : 1 ≤ k
    · obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_clause R _ hR D A G hG U F k hk
      exact ⟨f, fun _ => hf⟩
    · exact ⟨fun _ => 1, fun h => absurd h hk⟩
  choose f hf using H
  refine ⟨f, ⟨fun k hk => (hf k hk).2, fun k hk => (hf k hk).1.2.1, fun k hk => (hf k hk).1.2.2.1,
    fun k hk => (hf k hk).1.2.2.2.1, fun k hk p p' z => ((hf k hk).1.2.2.2.2 p p' z).1, ?_⟩, fun k hk => (hf k hk).1.1⟩
  intro k m N hk hm hN p q hy hg
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hm
  exact (((hf N hN1).1.1 q _).1 (((GlobalTheory.LevelCompat.qkToAkU_level GlobalTheory.firstFiveLaws R _ hR D A G hG U F k m N hk hm hN p q
    (f k p)).1 hy hg).1 (((hf k hk).1.1 p _).2 rfl))).symm

end GlobalTheory.Mum.Recog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorPreObjectOfSiegelPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorPreObject_of_siegelPullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ o : PreEta b N (πX ≫ t), ∀ (k : Type) [Field k] (x : Sp k ⟶ X), (o.GeomAt k x ↔ GeomAt D N actX (c.P.pull φ₂X) ηX k x) := by
  first | (exact @GlobalTheory.UPel.HT.exists_preEta_of_siegPull) | (exact GlobalTheory.UPel.HT.exists_preEta_of_siegPull) | (intros; apply GlobalTheory.UPel.HT.exists_preEta_of_siegPull  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHost
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_host : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E), Nonempty (Host E) :=
  ⟨GlobalTheory.HostModel.E21, inferInstance, inferInstance, inferInstance, ⟨GlobalTheory.HostModel.host⟩⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroClassicalPointOfLocalHomAvoidingStatement
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_classicalPoint_of_localHom_avoiding : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ x : M.Z, ∃ s : M.O x, s ≠ 0 ∧ ∀ (p : ℕ) [Fact p.Prime] (χ : M.O x →+* OO p), IsLocalHom χ → χ s ≠ 0 → ∃ y : Sp (OO p) ⟶ M.Z, M.Cen U x y ∧ ∀ a : M.O x, M.val (gPt p ≫ y) a = ((χ a : OO p) : PadicAlgCl p) := by
  first | exact @GlobalTheory.Izumi.exists_ne_zero_forall_exists_cen | exact GlobalTheory.Izumi.exists_ne_zero_forall_exists_cen | (intros; apply GlobalTheory.Izumi.exists_ne_zero_forall_exists_cen <;> assumption)
end

