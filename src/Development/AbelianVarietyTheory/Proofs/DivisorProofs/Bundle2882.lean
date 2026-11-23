module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstOfRegularOnCoverAbelianVariety
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.HeatConst

theorem const_of_regular_on_cover : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (I : Type) (W : I → P₀.A.left.Opens), ⨆ i, W i = ⊤ → (∀ i, ⊤ ≤ ξ ⁻¹ᵁ W i) → ∀ y : F, (∀ i, ∃ h : Γ(P₀.A.left, W i), valR ξ (W i) h = y) → ∃ r : K, ψ r = y := by
  intro K _ P₀ F _ ψ ξ hξ hinj I W hW hWξ y hy
  choose h hh using hy
  have hagree : ∀ i j, rsT (h i) (W i ⊓ W j) = rsT (h j) (W i ⊓ W j) := by
    intro i j
    have hij : ⊤ ≤ ξ ⁻¹ᵁ (W i ⊓ W j) := fun p hp => ⟨hWξ i hp, hWξ j hp⟩
    refine sub_eq_zero.1 (hinj _ _ hij ?_)
    rw [GlobalTheory.LogKSBal.valR_eq ξ hij, map_sub, ← GlobalTheory.LogKSBal.valR_eq ξ hij, ← GlobalTheory.LogKSBal.valR_eq ξ hij,
      GlobalTheory.LogKSBal.valR_rsT ξ inf_le_left hij, GlobalTheory.LogKSBal.valR_rsT ξ inf_le_right hij, hh, hh, sub_self]
  obtain ⟨t, ht⟩ := GlobalTheory.KS.exists_rsT_eq W (O := ⊤) (fun _ => le_top) hW.ge h hagree
  obtain ⟨u, hu⟩ := (GlobalTheory.globalFns_holds (Sp K) P₀.A P₀.isAb).2 t
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom u, ?_⟩
  obtain ⟨i, -⟩ : ∃ i, ξ.base (IsLocalRing.closedPoint F) ∈ W i := by
    have : ξ.base (IsLocalRing.closedPoint F) ∈ (⨆ i, W i) := by rw [hW]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have htop : ⊤ ≤ ξ ⁻¹ᵁ (⊤ : P₀.A.left.Opens) := fun _ _ => trivial
  have hc : t = constFn P₀.A.hom ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom u) := by
    rw [← hu]
    simp [constFn, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rw [← hh i, ← ht i, GlobalTheory.LogKSBal.valR_rsT ξ le_top (hWξ i), hc, GlobalTheory.LogKSBal.valR_constFn P₀.A.hom ξ htop hξ]

end GlobalTheory.HeatConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverMemberContainingFractionFieldPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem genPt_mem_cover : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (c : R), φ c ≠ 0 → ∀ (J : Type) (W : J → G.left.Opens), ⨆ i, W i = G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → ∃ i, ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ⁻¹ᵁ W i := by
  intro R _ G Ω _ _ φ x' hx c hc J W hW
  set K := FractionRing Ω
  have hK : (⊤ : (Sp K).Opens) ≤ (spMap (algebraMap Ω K) ≫ x') ⁻¹ᵁ (⨆ i, W i) := by
    rw [hW, ← Scheme.Hom.comp_preimage]
    rw [Category.assoc, hx]
    simp only [GlobalTheory.HeatV.bo, Scheme.affineBasicOpen_coe, Scheme.preimage_basicOpen_top]
    rw [Scheme.basicOpen_of_isUnit]
    have e : spMap (algebraMap Ω K) ≫ spMap φ = Spec.map (CommRingCat.ofHom ((algebraMap Ω K).comp φ)) := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [e]
    have h1 := congrArg (fun f => f.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ((algebraMap Ω K).comp φ)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    rw [← h1]
    refine IsUnit.map _ ?_
    refine isUnit_iff_ne_zero.mpr ?_
    intro h0
    exact hc ((IsFractionRing.injective Ω K) (by simpa using h0))
  obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
  have hp := hK (Set.mem_univ p)
  obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).mp hp
  refine ⟨i, fun q _ => ?_⟩
  have : q = p := Subsingleton.elim _ _
  subst this
  exact hi

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationAway
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocReg

theorem exists_derivation_away {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (f : A)
    (hloc : letI := φ.toAlgebra; IsLocalization.Away f B) (d : A → A)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = x * d y + y * d x) :
    ∃ D : Derivation ℤ B B, ∀ a, D (φ a) = φ (d a) := by
  letI := φ.toAlgebra
  have h0 : d 0 = 0 := by
    have e := hadd 0 0
    rw [add_zero] at e
    linear_combination -e
  have h1 : d 1 = 0 := by
    have e := hmul 1 1
    rw [_root_.mul_one, _root_.one_mul] at e
    linear_combination -e
  let ψ : A →+* TrivSqZeroExt B B :=
    { toFun := fun a => TrivSqZeroExt.inl (φ a) + TrivSqZeroExt.inr (φ (d a))
      map_one' := by ext <;> simp [h1]
      map_mul' := fun x y => by
        ext
        · simp
        · simp [hmul]
          ring
      map_zero' := by ext <;> simp [h0]
      map_add' := fun x y => by ext <;> simp [hadd] }
  have hu : IsUnit (ψ f) := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
    simpa [ψ, RingHom.algebraMap_toAlgebra] using IsLocalization.Away.algebraMap_isUnit (S := B) f)
  let Λ : B →+* TrivSqZeroExt B B := IsLocalization.Away.lift f hu
  have hΛ : ∀ a, Λ (φ a) = ψ a := fun a => IsLocalization.lift_eq (M := Submonoid.powers f) (S := B) _ a
  have hfst : ∀ x, (Λ x).fst = x := by
    have : (TrivSqZeroExt.fstHom ℤ B B).toRingHom.comp Λ = RingHom.id B := by
      refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun r => ?_)
      simp [RingHom.algebraMap_toAlgebra, hΛ, ψ]
    intro x
    exact congr($this x)
  let L : B →+ B :=
    { toFun := fun x => (Λ x).snd
      map_zero' := by simp
      map_add' := fun x y => by simp }
  refine ⟨Derivation.mk' L.toIntLinearMap (fun x y => ?_), fun a => ?_⟩
  · show (Λ (x * y)).snd = x • (Λ y).snd + y • (Λ x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [mul_comm]
  · show (Λ (φ a)).snd = φ (d a)
    rw [hΛ]
    simp [ψ]

theorem deriv_ext_basicOpen : ∀ (X : Scheme.{0}) (U W : X.affineOpens) (hWU : W.1 ≤ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (DW : Derivation ℤ Γ(X, W.1) Γ(X, W.1)), (∀ r, DW ((X.presheaf.map (homOfLE hWU).op).hom r) = (X.presheaf.map (homOfLE hWU).op).hom (D r)) → ∀ (h : Γ(X, U.1)), X.basicOpen h ≤ W.1 → ∀ (R : Type) [CommRing R] [Algebra ℤ R] (g : Sp R ⟶ X) (hg : ⊤ ≤ g ⁻¹ᵁ U.1) (D' : Derivation ℤ R R), (∀ r, D' ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((g.appLE U.1 ⊤ hg).hom r)) = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((g.appLE U.1 ⊤ hg).hom (D r))) → ∃ (hUW : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1 ≤ g ⁻¹ᵁ W.1) (D'' : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1)), (∀ r, D'' (((Sp R).presheaf.map (homOfLE (le_top : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1 ≤ ⊤)).op).hom r) = ((Sp R).presheaf.map (homOfLE (le_top : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1 ≤ ⊤)).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D' ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r)))) ∧ (∀ θ, D'' ((g.appLE W.1 _ hUW).hom θ) = (g.appLE W.1 _ hUW).hom (DW θ)) := by

  intro X U W hWU D DW hDW h hhW R _ _ g hg D' hD'
  set e := Scheme.ΓSpecIso (CommRingCat.of R) with he
  set f := (g.appLE U.1 ⊤ hg).hom h with hf
  have hUW : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) f).1 ≤ g ⁻¹ᵁ W.1 := by
    show (Sp R).basicOpen f ≤ _
    rw [hf, Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact fun x hx => hhW hx.2
  refine ⟨hUW, ?_⟩
  set U' := ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) f) with hU'
  let φ := ((Sp R).presheaf.map (homOfLE (le_top : U'.1 ≤ ⊤)).op).hom
  have hloc : letI := φ.toAlgebra; IsLocalization.Away f Γ(Sp R, U'.1) :=
    (isAffineOpen_top (Sp R)).isLocalization_basicOpen f
  obtain ⟨D'', hD''⟩ := exists_derivation_away φ f hloc (fun r => e.inv.hom (D' (e.hom.hom r)))
    (fun x y => by simp only [map_add (f := _)]) (fun x y => by
      simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _)]
      simp)
  refine ⟨D'', hD'', ?_⟩

  set resUW := (X.presheaf.map (homOfLE hWU).op).hom with hresUW
  set ψW := (g.appLE W.1 U'.1 hUW).hom with hψW
  have hUU : U'.1 ≤ g ⁻¹ᵁ U.1 := hUW.trans (fun x hx => hWU hx)
  set ψU := (g.appLE U.1 U'.1 hUU).hom with hψU
  have hψ : ∀ y, ψW (resUW y) = ψU y := fun y => by
    rw [hψW, hresUW, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have hψU' : ∀ y, ψU y = φ ((g.appLE U.1 ⊤ hg).hom y) := fun y => by
    rw [hψU, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have hDU : ∀ y, D'' (ψU y) = ψU (D y) := fun y => by
    rw [hψU', hD'', hψU', hD']
    simp
  have hres : ∀ y, D'' (ψW (resUW y)) = ψW (DW (resUW y)) := fun y => by
    rw [hψ, hDU, hDW, hψ]
  have hunit : IsUnit (ψU h) := by
    rw [hψU']
    letI := φ.toAlgebra
    exact IsLocalization.Away.algebraMap_isUnit (S := Γ(Sp R, U'.1)) f
  have key : ∀ θ : Γ(X, W.1), ∃ (a : Γ(X, U.1)) (M : ℕ), resUW (h ^ M) * θ = resUW a := by
    intro θ
    set V := X.basicOpen (resUW h) with hVdef
    have hV : V = X.basicOpen h := by
      rw [hVdef, hresUW, Scheme.basicOpen_res]
      exact inf_eq_right.2 hhW
    have hVW : V ≤ W.1 := X.basicOpen_le _
    have hVU : V ≤ U.1 := hVW.trans hWU
    let resUV := (X.presheaf.map (homOfLE hVU).op).hom
    let resWV := (X.presheaf.map (homOfLE hVW).op).hom
    have hcomp : ∀ y, resWV (resUW y) = resUV y := fun y => by
      rw [hresUW, ← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    have hlocU : letI := resUV.toAlgebra; IsLocalization.Away h Γ(X, V) :=
      U.2.isLocalization_of_eq_basicOpen h (homOfLE hVU) hV
    have hlocW : letI := resWV.toAlgebra; IsLocalization.Away (resUW h) Γ(X, V) :=
      W.2.isLocalization_basicOpen (resUW h)
    obtain ⟨⟨a, _, N, rfl⟩, hN⟩ := (letI := resUV.toAlgebra; IsLocalization.surj (Submonoid.powers h) (resWV θ))
    simp only [RingHom.algebraMap_toAlgebra] at hN
    rw [← hcomp, ← hcomp, ← map_mul] at hN
    letI := resWV.toAlgebra
    obtain ⟨⟨c, k, rfl⟩, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (resUW h)) (S := Γ(X, V))
      (x := θ * resUW (h ^ N)) (y := resUW a) (by simpa only [RingHom.algebraMap_toAlgebra] using hN)
    refine ⟨h ^ k * a, k + N, ?_⟩
    simp only [map_mul, map_pow] at hc ⊢
    linear_combination hc
  intro θ
  obtain ⟨a, M, hM⟩ := key θ
  have e2 := congrArg (fun x => D'' (ψW x)) hM
  have e3 := congrArg (fun x => ψW (DW x)) hM
  simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _)] at e2 e3
  rw [hres, hres] at e2
  have hu : IsUnit (ψW (resUW (h ^ M))) := by rw [hψ, map_pow]; exact hunit.pow M
  exact hu.mul_left_cancel (by linear_combination e2 - e3)

end GlobalTheory.LocReg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivSec
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatRatio

theorem exists_div_sec {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s a b : LB.Sec (LB.LinComb L φ ε)) (U : Y.Opens) (f : Γ(Y, U))
    (hs : ∀ z ∈ U, ∀ J, Good L z J → IsUnit (sval s (𝟙 Y) z J)) :
    ∃ g : Γ(Y, U), ∀ z ∈ U, ∀ J, Good L z J →
      sval a (𝟙 Y) z J = gs (𝟙 Y) z U f * sval b (𝟙 Y) z J + gs (𝟙 Y) z U g * sval s (𝟙 Y) z J := by
  have hun : ∀ (j : K → L.ι) (y : Y), y ∈ U → y ∈ LB.wchart L φ j →
      IsUnit (gs (𝟙 Y) y (LB.wchart L φ j) (s.f j)) := fun j y hU hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
    rw [e]
    exact (Units.isUnit _).mul (hs y hU J hJ)
  let W : (K → L.ι) → Y.Opens := fun j => U ⊓ LB.wchart L φ j
  have hloc : ∀ j, ∃ u : Γ(Y, W j), ∀ y ∈ W j,
      gs (𝟙 Y) y (LB.wchart L φ j) (a.f j) = gs (𝟙 Y) y U f * gs (𝟙 Y) y (LB.wchart L φ j) (b.f j) +
        gs (𝟙 Y) y (W j) u * gs (𝟙 Y) y (LB.wchart L φ j) (s.f j) := by
    intro j
    have l₁ : W j ≤ U := inf_le_left
    have l₂ : W j ≤ LB.wchart L φ j := inf_le_right
    have hu : IsUnit ((Y.presheaf.map (homOfLE l₂).op).hom (s.f j)) :=
      Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
        (congrArg IsUnit ((gs_eq (𝟙 Y) y (W j) hy _).symm.trans (gs_res (𝟙 Y) y l₂ hy (s.f j)))).mpr
          (hun j y hy.1 hy.2)
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have key : (Y.presheaf.map (homOfLE l₂).op).hom (a.f j) =
        (Y.presheaf.map (homOfLE l₁).op).hom f * (Y.presheaf.map (homOfLE l₂).op).hom (b.f j) +
        (((Y.presheaf.map (homOfLE l₂).op).hom (a.f j) -
          (Y.presheaf.map (homOfLE l₁).op).hom f * (Y.presheaf.map (homOfLE l₂).op).hom (b.f j)) * v) *
          (Y.presheaf.map (homOfLE l₂).op).hom (s.f j) := by
      rw [_root_.mul_assoc, hv]; ring
    refine ⟨((Y.presheaf.map (homOfLE l₂).op).hom (a.f j) -
          (Y.presheaf.map (homOfLE l₁).op).hom f * (Y.presheaf.map (homOfLE l₂).op).hom (b.f j)) * v, fun y hy => ?_⟩
    refine (gs_res (𝟙 Y) y l₂ hy _).symm.trans ((congrArg (gs (𝟙 Y) y (W j)) key).trans ?_)
    refine (gs_add (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· + ·) ?_ ?_)
    · exact (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 Y) y l₁ hy _) (gs_res (𝟙 Y) y l₂ hy _))
    · exact (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg _ (gs_res (𝟙 Y) y l₂ hy _))
  choose u hu using hloc
  obtain ⟨g, hg, -⟩ := Y.sheaf.existsUnique_gluing' W U (fun j => homOfLE inf_le_left) (fun y hy => by
      choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun k => I (φ k), hy, Set.mem_iInter.2 fun k => hI _⟩) u
    (fun j j' => fn_ext (V := W j ⊓ W j') fun y hy => by
      refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
      have e₁ := hu j y hy.1
      have e₂ := hu j' y hy.2
      rw [sec_trans a (𝟙 Y) y hy.1.2 hy.2.2, sec_trans b (𝟙 Y) y hy.1.2 hy.2.2,
        sec_trans s (𝟙 Y) y hy.1.2 hy.2.2] at e₁
      have hc := (Units.isUnit (trF φ ε (𝟙 Y) y j j')).mul (hun j' y hy.1.1 hy.2.2)
      refine hc.mul_right_cancel ?_
      linear_combination (trF φ ε (𝟙 Y) y j j').val * e₂ - e₁)
  refine ⟨g, fun z hz J hJ => ?_⟩
  have hm : z ∈ W (fun k => J (𝟙 Y ≫ φ k)) := ⟨hz, hJ.mem φ (𝟙 Y)⟩
  have e : gs (𝟙 Y) z U g = gs (𝟙 Y) z (W _) (u (fun k => J (𝟙 Y ≫ φ k))) :=
    (gs_res (𝟙 Y) z inf_le_left hm g).symm.trans (congrArg (gs (𝟙 Y) z (W _)) (hg _))
  rw [e]
  exact hu _ z hm

theorem exists_isRem : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (N : ℕ) (α : Q.X) (σ σ' σp σp' : Q.SecB N α) (U : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, U)), GlobalTheory.HeatRatio.IsRatio Q σ σ' U f → ∃ g : Γ(Q.P.A.left, U), GlobalTheory.HeatRatio.IsRem Q σ' σp σp' U f g := by
  intro R _ _ Q N α σ σ' σp σp' U f h
  exact exists_div_sec Q.P.isLB σ' σp σp' U f fun z hz J hJ => (h z hz J hJ).1

end GlobalTheory.HeatRatio
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivalentIdempotentImageFixedTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.EFix

theorem exists_equiv_act_of_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (n : ℕ), 1 ≤ n → IsUnit (n : R) → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), IsSemiAbelian G' → U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A'.A), a ^ n = 1 → a ≫ oA.act F.e = a → ∀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n, QkToAkU U'.toUnifPre (AlgebraicClosure (FractionRing R)) n p a → ∃ p₁ : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n, p₁.y = F.e • p.y ∧ GtPtAct F.o F.e p.g p₁.g ∧ QkPt.Equiv D'.toPre (AlgebraicClosure (FractionRing R)) p₁ p := by
  intro R _ _ _ hR n hn _ Q D' F A' G' _ _ U' oA oG hS hl a _ hae p hp
  have hAdm : AdmBase R (maximalIdeal R) := ⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩
  haveI : CharZero R := hR.2.2.2
  have hL := GlobalTheory.firstFiveLaws
  obtain ⟨q, hqy, hqg⟩ := exists_gtPtAct (F := AlgebraicClosure (FractionRing R)) hL.1.globalFns F.o F.e p
  obtain ⟨E, eG, eA, -, -, eact⟩ := endU_of_oLinear hL R (maximalIdeal R) hAdm D' A' G' hS U' F.O F.o oA oG hl F.e
  obtain ⟨E', eG', -, -, eh', -⟩ := endU_of_oLinear hL R (maximalIdeal R) hAdm D' A' G' hS U' F.O F.o oA oG hl (star F.e)
  have hcube := GlobalTheory.Mum.EFixCube.cube_adj_of_oLinear R hAdm D' A' G' U'.toUnifPre hS F.O F.o oA oG hl F.e
  have hfun := GlobalTheory.UT.functorial_of_unif R (maximalIdeal R) hAdm D' A' G' hS U'
  have h2 := (hfun.2 E E' (by rw [eG, eG']; exact hcube)).2 (AlgebraicClosure (FractionRing R))
  have hq := h2.2.2 n hn p q a (by rw [eh', star_star]; exact hqy)
    ((eact (AlgebraicClosure (FractionRing R)) _ _).2 hqg) hp
  rw [eA, hae] at hq
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hAdm D' A' G' hS U'
    (AlgebraicClosure (FractionRing R)) n hn
  exact ⟨q, hqy, hqg, (hf.2.2.1 q p).1 (((hf.1 q a).1 hq).symm.trans ((hf.1 p a).1 hp))⟩

end GlobalTheory.Mum.EFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionFieldMapBasicOpenFormalPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatV

theorem fracIotaBasicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (t : SAB H (Sp R)) (c : R), c ≠ 0 → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left), x' ≫ t.G.hom = spMap φ → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∃ iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* (FractionRing Ω), ∀ r, iota (GlobalTheory.HeatV.resV R c r) = (algebraMap Ω (FractionRing Ω)) (φ r) := by
  intro E _ _ _ H R _ _ t c hc Ω _ _ φ x' hx hinj
  have e1 : ∀ y : Γ(Sp R, ⊤), (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom
      ((x'.appTop).hom ((t.G.hom.appTop).hom y)) = φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y) := by
    intro y
    have n := congrArg (fun k => k.hom y) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
    rw [← n, show Spec.map (CommRingCat.ofHom φ) = x' ≫ t.G.hom from hx.symm, Scheme.Hom.comp_appTop]
    rfl
  have e2 : ∀ y : Γ(Sp R, ⊤), ((η[t.G]).left.appTop).hom ((t.G.hom.appTop).hom y) = y := by
    intro y
    have w : (η[t.G]).left ≫ t.G.hom = 𝟙 (Sp R) := by simpa using Over.w η[t.G]
    have := congrArg (fun k => (Scheme.Hom.appTop k).hom y) w
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    simp
  have ht : ⊤ ≤ x' ⁻¹ᵁ (⊤ : t.G.left.Opens) := by simp
  have inj : ∀ r : R, φ r = 0 → r = 0 := by
    intro r hr
    set y := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r with hy
    have hv : valR x' ⊤ ((t.G.hom.appTop).hom y) = 0 := by
      unfold valR
      rw [dite_eq_left ht]
      have : x'.appLE ⊤ ⊤ ht = x'.appTop := Scheme.Hom.appLE_eq_app _
      rw [this, e1, hy]
      simpa using hr
    have h0 := hinj ⊤ _ ht hv
    have h1 := e2 y
    rw [h0, map_zero] at h1
    have : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y = r := by simp [hy]
    rw [← this, ← h1, map_zero]
  let s : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c
  let gg : Γ(Sp R, ⊤) →+* FractionRing Ω :=
    (algebraMap Ω (FractionRing Ω)).comp (φ.comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom)
  have hu : IsUnit (gg s) := by
    rw [isUnit_iff_ne_zero]
    simp only [gg, s, RingHom.comp_apply]
    have hs : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) = c := by simp
    rw [hs]
    intro h0
    exact hc (inj c ((IsFractionRing.injective Ω (FractionRing Ω)) (by simpa using h0)))
  refine ⟨IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu, fun r => ?_⟩
  show IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu
    (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _
  rw [IsLocalization.Away.lift, IsLocalization.lift_eq]
  simp [gg]

end GlobalTheory.HeatV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntLogOfIsLiePSmul
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem GlobalTheory.QLog.exists_int_log_of_isLie_p_smul : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), QL c.μ ⊤ f → c.IsLie f ((p : O) • l) → ∃ (s : MvPowerSeries (Fin d) O) (g : MvPowerSeries (Fin d) E), cob1 (up E c.μ) g = 0 ∧ QL c.μ (Ideal.span {(p : O)}) (f - map (algebraMap O E) s - g) := by
  intro p _ O E _ _ _ hF G d c f l hf hl
  obtain ⟨s₁, hs₁, hl₁⟩ := (c.isLie_iff hF.inj f _).1 hl 1
  rw [pow_one] at hs₁
  have hdiv : ∀ (w : G.dual.omega) (φ : CartierDual O (G.A 1)), dUnit (R := O) φ = w.1 1 →
      (p : O) ∣ φ (c.ev 1 s₁) := by
    intro w φ hφ
    have h1 := hl₁ w φ hφ
    rw [pow_one, LinearMap.smul_apply, smul_eq_mul] at h1
    exact (dvd_sub_right (dvd_mul_right _ _)).1 h1
  obtain ⟨⟨z, hz⟩, -⟩ := GlobalTheory.T.dvd_of_forall_invariantDifferential_dvd p O G 1 (p : O) (c.ev 1 s₁) hdiv
  obtain ⟨t, ht0, ht⟩ := _root_.GlobalTheory.QLog.exists_int_cob_dvd_of_defect_ev p O E hF G d c f s₁ z hf hs₁ hz
  obtain ⟨hf0, hflin, -⟩ := hf
  choose b _ hb using hflin
  obtain ⟨g, hg0, hglin, hgcob⟩ := _root_.GlobalTheory.QLog.exists_log_of_lin p O E hF d c.μ c.isLaw (fun i => b i - lin t i)
  have hμ : ∀ i, constantCoeff (up E c.μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      c.isLaw.const i, map_zero]
  refine ⟨t, g, hgcob, ?_, ?_, ?_⟩
  · rw [map_sub, map_sub, hf0, hg0, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
      coeff_zero_eq_constantCoeff_apply, ht0, map_zero]
    simp
  · intro i
    refine ⟨0, Ideal.zero_mem _, ?_⟩
    have : lin (f - map (algebraMap O E) t - g) i = lin f i - algebraMap O E (lin t i) - lin g i := by
      simp [lin, coeff_map]
    rw [this, hb i, hglin i, map_sub, map_zero]
    simp
  · have hsub : f - map (algebraMap O E) t - g = (f - map (algebraMap O E) t) + (-1 : E) • g := by
      rw [neg_one_smul, ← sub_eq_add_neg]
    rw [hsub, formalCoboundary_add hμ, formalCoboundary_smul hμ, hgcob, smul_zero, add_zero]
    exact ht
end

