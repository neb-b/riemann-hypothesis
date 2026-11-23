module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegResidueFieldOfIsOpenImmersion
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0002
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2894
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNsmulEqOfEqClosedPointDualNumbers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem eq_of_pow_eq_of_eq_at_closed : ∀ (k : Type) [Field k] (B : Over (Sp (DualNumber k))) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : k) ≠ 0 → ∀ x x' : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B, x ^ n = x' ^ n → spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x.left = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x'.left → x = x' := by
  intro k _ B _ hB n hn x x' hpow h0
  haveI : IsCommMonObj B := hB.comm
  haveI hloc : IsLocalRing (DualNumber k) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one, isUnit_iff_ne_zero]
    by_cases ha : a.fst = 0
    · right; rw [ha, sub_zero]; exact one_ne_zero
    · left; exact ha
  have hnD : IsUnit (n : DualNumber k) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_natCast]
    exact hn.isUnit
  have hnΓ : IsUnit (n : Γ(Sp (DualNumber k), ⊤)) := by
    simpa using hnD.map (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom
  haveI : PreconnectedSpace (Sp (DualNumber k)) := by
    have : PreconnectedSpace (PrimeSpectrum (DualNumber k)) := by
      refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint (DualNumber k)) fun y _ =>
        ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩
      exact (IsLocalRing.specializes_closedPoint y).mem_closure
    exact this
  haveI : PreconnectedSpace (𝟙_ (Over (Sp (DualNumber k)))).left := ‹PreconnectedSpace (Sp (DualNumber k))›
  let T : Over (Sp (DualNumber k)) := Over.mk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
  haveI : Nonempty T.left := inferInstanceAs (Nonempty (Sp k))
  have hw : (x * x'⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, hpow, mul_inv_cancel]
  obtain ⟨C, hC, hz⟩ := GlobalTheory.TorsionCover.exists_clopen_eq_one B hB hnΓ (x * x'⁻¹) hw
  have hT : toUnit T ≫ x = toUnit T ≫ x' := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, GlobalTheory.ObjPull.toUnit_left']
    exact h0
  have h1 : toUnit T ≫ (x * x'⁻¹) = 1 := by
    show (preHom (toUnit T)) (x * x'⁻¹) = 1
    rw [map_mul, map_inv]
    show (toUnit T ≫ x) * (toUnit T ≫ x')⁻¹ = 1
    rw [hT, mul_inv_cancel]
  have hsub := (hz T (toUnit T)).1 h1
  obtain ⟨p⟩ := ‹Nonempty T.left›
  have hne : C.Nonempty := ⟨_, hsub ⟨p, rfl⟩⟩
  have huniv : C = Set.univ := hC.eq_univ hne
  have h2 : 𝟙 _ ≫ (x * x'⁻¹) = 1 := (hz _ (𝟙 _)).2 (by rw [huniv]; exact Set.subset_univ _)
  rw [Category.id_comp] at h2
  exact mul_inv_eq_one.1 h2

end GlobalTheory.UCanon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProdZpowEqBalancedFormsBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BalMono

theorem coords_eq_zero {O : Type} [CommRing O] [StarRing O] [IsDedekindDomain O]
    [Module.Finite ℤ O] [Module.Free ℤ O] {w : O} (hw : w + star w = 1)
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite ℤ X] [Module.Free ℤ X]
    {J : Type} [Fintype J] (ε : Module.Basis J ℤ (PolFan.balForms (star : O → O) X))
    {B : Type} [AddCommGroup B] (c : J → B)
    (hc : ∀ a b, ∑ k, (ε k : LinearMap.BilinForm ℤ X) a b • c k = 0) (k : J) : c k = 0 := by
  classical
  have := Forms.projective_of_int O X
  have := Forms.finite_balTensor (O := O) (X := X)
  have := Forms.free_balTensor (X := X) hw
  let e := Module.Free.chooseBasis ℤ ((TensorProduct ℤ X X) ⧸ Forms.balTensorRel (O := O) (X := X))
  have hm := Forms.balTensorMk_mem_balForms O X
  let β : _ → PolFan.balForms (star : O → O) X := fun j =>
    ⟨(Forms.balTensorMk O).compr₂ (e.coord j),
      fun y x => congrArg (e.coord j) (hm.1 y x), fun a y x => congrArg (e.coord j) (hm.2 a y x)⟩
  let L : J → ((TensorProduct ℤ X X) ⧸ Forms.balTensorRel (O := O) (X := X)) →+ ℤ := fun i =>
    Forms.balTensorLift (O := O) ⟨(ε i : LinearMap.BilinForm ℤ X), (ε i).2.1, (ε i).2.2⟩
  have hL (i a b) : L i (Forms.balTensorMk O a b) = (ε i : LinearMap.BilinForm ℤ X) a b := rfl
  let Φ : ((TensorProduct ℤ X X) ⧸ Forms.balTensorRel (O := O) (X := X)) →+ B :=
    ∑ i, (zmultiplesHom B (c i)).comp (L i)
  have hΦa (t) : Φ t = ∑ i, L i t • c i := by
    simp [Φ, AddMonoidHom.finsetSum_apply]
  have hΦ : Φ = 0 := Forms.balTensor_hom_ext fun a b => by
    rw [hΦa]
    exact hc a b
  have hε (i) : ε i = ∑ j, L i (e j) • β j := by
    apply Subtype.ext
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hL, ← e.sum_repr (Forms.balTensorMk O a b), map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_eq_mul, _root_.mul_comm]
    rfl
  have hδ (i) : L i (∑ j, ε.repr (β j) k • e j) = ε.repr (ε i) k := by
    have h1 := congrArg (ε.coord k) (hε i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← ε.coord_apply, h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul, _root_.mul_comm, ε.coord_apply]
  have h := hΦa (∑ j, ε.repr (β j) k • e j)
  simp only [hδ, hΦ, AddMonoidHom.zero_apply] at h
  simpa [Finsupp.single_apply] using h.symm

theorem eq_of_prod_zpow_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : Type) [Field F] (I : Type) [Fintype I] (ε : Module.Basis I ℤ (balForms H.bar X)) (x y : I → F), (∀ i, x i ≠ 0) → (∀ i, y i ≠ 0) → (∀ a b, ∏ i, x i ^ (ε i : LinearMap.BilinForm ℤ X) a b = ∏ i, y i ^ (ε i : LinearMap.BilinForm ℤ X) a b) → x = y := by
  intro E _ _ _ H X _ _ _ _ F _ I _ ε x y hx hy h
  letI : StarRing (𝓞 E) :=
    { star := H.bar
      star_involutive := fun a => by
        apply Subtype.ext
        change ((H.bar (H.bar a) : 𝓞 E) : E) = a
        rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
      star_mul := fun a b => by rw [map_mul, _root_.mul_comm]
      star_add := fun a b => map_add H.bar a b }
  have hw : H.w0 + H.bar H.w0 = 1 := PullbackSections.CVA.cmHostUnit_add_conj_eq_one H
  let u : I → Fˣ := fun i => Units.mk0 (x i) (hx i)
  let v : I → Fˣ := fun i => Units.mk0 (y i) (hy i)
  have huv : ∀ a b, ∏ i, (u i / v i) ^ ((ε i : LinearMap.BilinForm ℤ X) a b) = 1 := by
    intro a b
    rw [Finset.prod_congr rfl (fun i _ => div_zpow _ _ _), Finset.prod_div_distrib, div_eq_one]
    apply Units.ext
    simpa [u, v, Units.coe_prod] using h a b
  funext k
  have hk := coords_eq_zero (O := 𝓞 E) hw ε (fun i => Additive.ofMul (u i / v i))
    (fun a b => by
      apply Additive.toMul.injective
      simp only [toMul_sum, toMul_zsmul, toMul_ofMul, toMul_zero]
      exact huv a b) k
  have hk' : u k / v k = 1 := hk
  simpa [u, v] using congrArg Units.val (div_eq_one.1 hk')

end GlobalTheory.BalMono
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSameFibreIsIntegralHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory

theorem eq_of_specializes_of_isIntegralHom : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] {x x' : X}, x ⤳ x' → f x = f x' → x = x' := by
  intro X Y f _ x x' hxx' hf
  obtain ⟨_, ⟨V, hV0, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x')) isOpen_univ
  have hV : IsAffineOpen V := hV0
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have hx' : x' ∈ f ⁻¹ᵁ V := hxV
  have hx : x ∈ f ⁻¹ᵁ V := hxx'.mem_open (f ⁻¹ᵁ V).isOpen hx'
  set P := hU.primeIdealOf ⟨x, hx⟩ with hPdef
  set P' := hU.primeIdealOf ⟨x', hx'⟩ with hP'def
  have eP : hU.fromSpec P = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have eP' : hU.fromSpec P' = x' := hU.fromSpec_primeIdealOf ⟨x', hx'⟩
  have hsp : P ⤳ P' := by
    exact hU.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.1 (by rw [eP, eP']; exact hxx')
  have hle : P.asIdeal ≤ P'.asIdeal := (PrimeSpectrum.le_iff_specializes P P').mpr hsp
  have sq : Spec.map (f.app V) ≫ hV.fromSpec = hU.fromSpec ≫ f := by
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f hV hU le_rfl
  have img : ∀ Q : Spec Γ(X, f ⁻¹ᵁ V), hV.fromSpec (Spec.map (f.app V) Q) = f (hU.fromSpec Q) :=
    fun Q => (Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun m : Spec Γ(X, f ⁻¹ᵁ V) ⟶ Y => m Q) sq).trans (Scheme.Hom.comp_apply _ _ _))
  have hc : Spec.map (f.app V) P = Spec.map (f.app V) P' := by
    apply hV.fromSpec.isOpenEmbedding.injective
    exact (img P).trans ((congrArg f eP).trans (hf.trans ((congrArg f eP').symm.trans (img P').symm)))
  have hc' : P.asIdeal.comap (f.app V).hom = P'.asIdeal.comap (f.app V).hom :=
    congrArg PrimeSpectrum.asIdeal hc
  letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  haveI : Algebra.IsIntegral Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := ⟨f.isIntegral_app V hV⟩
  have heq : P.asIdeal = P'.asIdeal := by
    by_contra hne
    have hlt := Ideal.IsIntegral.comap_lt_comap (R := Γ(Y, V)) (lt_of_le_of_ne hle hne)
    exact (ne_of_lt hlt) hc'
  have : P = P' := PrimeSpectrum.ext heq
  rw [← eP, ← eP', this]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfIsometryApply
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {Z Z' : Submodule (𝓞 E) D.La}

theorem IsOpp.proj_unique (h : IsOpp D Z Z') {a b b' : D.La} (hb : b ∈ Z') (hb' : b' ∈ Z')
    (h1 : a - b ∈ perp D Z) (h2 : a - b' ∈ perp D Z) : b = b' := by
  have := h.eq_zero (sub_mem hb hb') (by
    have := sub_mem h2 h1
    rwa [sub_sub_sub_cancel_left] at this)
  exact sub_eq_zero.1 this

def IsOpp.proj (h : IsOpp D Z Z') : D.La →ₗ[𝓞 E] Z' where
  toFun a := ⟨(h.exists_sub_mem_perp a).choose, (h.exists_sub_mem_perp a).choose_spec.1⟩
  map_add' a b := by
    have ha := (h.exists_sub_mem_perp a).choose_spec
    have hb := (h.exists_sub_mem_perp b).choose_spec
    have hab := (h.exists_sub_mem_perp (a + b)).choose_spec
    apply Subtype.ext
    refine h.proj_unique hab.1 (add_mem ha.1 hb.1) hab.2 ?_
    have := add_mem ha.2 hb.2
    simpa [sub_add_sub_comm] using this
  map_smul' c a := by
    have ha := (h.exists_sub_mem_perp a).choose_spec
    have hca := (h.exists_sub_mem_perp (c • a)).choose_spec
    apply Subtype.ext
    refine h.proj_unique hca.1 (Z'.smul_mem c ha.1) hca.2 ?_
    have := (perp D Z).smul_mem c ha.2
    simpa [smul_sub] using this

theorem IsOpp.sub_proj_mem (h : IsOpp D Z Z') (a : D.La) : a - h.proj a ∈ perp D Z :=
  (h.exists_sub_mem_perp a).choose_spec.2

theorem IsOpp.proj_eq (h : IsOpp D Z Z') {a b : D.La} (hb : b ∈ Z') (hab : a - b ∈ perp D Z) : (h.proj a : D.La) = b :=
  h.proj_unique (h.proj a).2 hb (h.sub_proj_mem a) hab

theorem IsOpp.proj_of_mem (h : IsOpp D Z Z') {b : D.La} (hb : b ∈ Z') : (h.proj b : D.La) = b :=
  h.proj_eq hb (by simp)

theorem IsOpp.proj_of_perp (h : IsOpp D Z Z') {a : D.La} (ha : a ∈ perp D Z) : (h.proj a : D.La) = 0 :=
  h.proj_eq Z'.zero_mem (by simpa using ha)

variable (D)

theorem exists_adjoint (σ : D.La →ₗ[𝓞 E] D.La) : ∃ w : D.La →ₗ[𝓞 E] D.La, ∀ a b, D.EF (w a) b = D.EF a (σ b) := by
  choose w hw using fun a => D.unimod.2 ((D.EF a).comp (σ.restrictScalars ℤ))
  refine ⟨{ toFun := w, map_add' := fun a b => D.unimod.1 ?_, map_smul' := fun c a => D.unimod.1 ?_ }, fun a b => ?_⟩
  · ext x; simp [hw]
  · ext x
    simp only [hw, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, RingHom.id_apply, D.adj]
    rw [← σ.map_smul]
  · exact congrArg (fun f => f b) (hw a)

theorem bijective_of_isometry (g : D.La →ₗ[𝓞 E] D.La) (hg : ∀ a b, D.EF (g a) (g b) = D.EF a b) :
    Function.Bijective g := by
  obtain ⟨w, hw⟩ := exists_adjoint D g
  have hwg : ∀ a, w (g a) = a := fun a => D.unimod.1 (LinearMap.ext fun b => by rw [hw, hg])
  have hws : Function.Surjective w := fun a => ⟨g a, hwg a⟩
  haveI := D.fin
  have hwi : Function.Injective w := OrzechProperty.injective_of_surjective_endomorphism w hws
  refine ⟨fun a b hab => by rw [← hwg a, ← hwg b, hab], fun a => ⟨w a, hwi (by rw [hwg])⟩⟩

def equivOfIsometry (g : D.La →ₗ[𝓞 E] D.La) (hg : ∀ a b, D.EF (g a) (g b) = D.EF a b) : D.La ≃ₗ[𝓞 E] D.La :=
  LinearEquiv.ofBijective g (bijective_of_isometry D g hg)

@[simp] theorem equivOfIsometry_apply (g : D.La →ₗ[𝓞 E] D.La) (hg : ∀ a b, D.EF (g a) (g b) = D.EF a b) (a : D.La) :
    equivOfIsometry D g hg a = g a := rfl

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypePreimageFromSpecStalk
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothStalk

theorem essFiniteType_preimage_fromSpecStalk (F : Type) [CommRing F] (X : Scheme.{0})
    (g : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType g] (z : X) :
    (Spec.preimage (X.fromSpecStalk z ≫ g)).hom.EssFiniteType := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (show z ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ g)
  have hft : φ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have he : Spec.preimage (X.fromSpecStalk z ≫ g) = φ ≫ X.presheaf.germ U z hx := by
    rw [← Spec.map_inj, Spec.map_preimage, Spec.map_comp, hφ, ← hU.fromSpecStalk_eq_fromSpecStalk hx,
      IsAffineOpen.fromSpecStalk, Category.assoc]
  rw [he, CommRingCat.hom_comp]
  refine RingHom.EssFiniteType.comp hft.essFiniteType ?_
  let _ := X.presheaf.algebra_section_stalk ⟨z, hx⟩
  have := hU.isLocalization_stalk ⟨z, hx⟩
  exact Algebra.EssFiniteType.of_isLocalization (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hx⟩).asIdeal.primeCompl

theorem stalk_regular_essFiniteType_dim : ∀ (F : Type) [Field F] (Cs : Scheme.{0}) (g : Cs ⟶ Sp F) (n : ℕ), SmoothOfRelativeDimension n g → ∀ z : Cs, IsRegularLocalRing (Cs.presheaf.stalk z) ∧ ∃ b : F →+* Cs.presheaf.stalk z, Cs.fromSpecStalk z ≫ g = spMap b ∧ b.EssFiniteType ∧ (letI := ((residue (Cs.presheaf.stalk z)).comp b).toAlgebra; ∃ a t : ℕ, ringKrullDim (Cs.presheaf.stalk z) = a ∧ Algebra.trdeg F (ResidueField (Cs.presheaf.stalk z)) = t ∧ a + t = n) := by
  intro F _ Cs g n hsm z
  haveI := hsm
  haveI : Smooth g := SmoothOfRelativeDimension.smooth n g
  haveI : IsRegularRing (CommRingCat.of F) := inferInstanceAs (IsRegularRing F)
  have hreg : ∀ x : Cs, IsRegularLocalRing (Cs.presheaf.stalk x) := fun x =>
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth g x
  refine ⟨hreg z, (Spec.preimage (Cs.fromSpecStalk z ≫ g)).hom, ?_, essFiniteType_preimage_fromSpecStalk F Cs g z, ?_⟩
  · exact (Spec.map_preimage _).symm
  · have h := GlobalTheory.StalkDim.stalk_dim_add_trdeg F g (𝟙 Cs) n (by simp) (by simpa using hsm)
      (fun x => haveI := hreg x; ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing) z
    have he : Spec.preimage (Cs.fromSpecResidueField z ≫ g) =
        Spec.preimage (Cs.fromSpecStalk z ≫ g) ≫ Cs.residue z := by
      rw [← Spec.map_inj, Spec.map_preimage, Spec.map_comp, Spec.map_preimage, Scheme.fromSpecResidueField,
        Category.assoc]
    rw [he] at h
    exact h

end GlobalTheory.SmoothStalk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyIndEtaleBaseChange
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC TensorProduct

noncomputable section

namespace GlobalTheory.EtC.LineAcyc

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  dsimp only [spMap]
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (sp A) := by
  dsimp only [spMap]
  rw [CommRingCat.ofHom_id, Spec.map_id]
  exact sch.map_id _

theorem pull_bijective_of_ringEquiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (R : Type) [CommRing R] (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R (spMap (e : A →+* B)) F n) := by
  have h1 : ∀ x, pull R (spMap (e.symm : B →+* A)) F n (pull R (spMap (e : A →+* B)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp', show ((e.symm : B →+* A).comp (e : A →+* B)) = RingHom.id A by
      ext; simp, spMap_id', pull_id]
  have h2 : ∀ x, pull R (spMap (e : A →+* B)) F n (pull R (spMap (e.symm : B →+* A)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp', show ((e : A →+* B).comp (e.symm : B →+* A)) = RingHom.id B by
      ext; simp, spMap_id', pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem eqv_of_square {X Y X' Y' : Type} [CommRing X] [CommRing Y] [CommRing X'] [CommRing Y']
    (g : X →+* Y) (g' : X' →+* Y') (eX : X ≃+* X') (eY : Y ≃+* Y')
    (h : (eY : Y →+* Y').comp g = g'.comp (eX : X →+* X')) {R : Type} [CommRing R] (F : Shv R) :
    Eqv R (spMap g') F → Eqv R (spMap g) F := by
  intro hg' n
  have hc : spMap (eY : Y →+* Y') ≫ spMap g = spMap g' ≫ spMap (eX : X →+* X') := by
    rw [← spMap_comp', ← spMap_comp', h]
  have key : (pull R (spMap (eY : Y →+* Y')) F n) ∘ (pull R (spMap g) F n) =
      (pull R (spMap g') F n) ∘ (pull R (spMap (eX : X →+* X')) F n) := by
    funext x
    simp only [Function.comp_apply]
    rw [← pull_comp, ← pull_comp, hc]
  have hY := pull_bijective_of_ringEquiv eY R F n
  have hX := pull_bijective_of_ringEquiv eX R F n
  refine (Function.Bijective.of_comp_iff' hY _).mp ?_
  rw [key]
  exact (hg' n).comp hX

end GlobalTheory.EtC.LineAcyc

namespace GlobalTheory.EtC.LineAcyc

theorem affineLine_localAcyclicity_of_strictHenselian_points (core : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
    ∀ (O : Type) [CommRing O] [Algebra (Polynomial T) O] [Algebra T O] [IsScalarTower T (Polynomial T) O],
    SH O → IndEt (Polynomial T) O → ∀ i : ℤ,
    Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := O)).toRingHom) (tw q i)) : C3 := by
  intro q _ T _ _ _ hT hq B _ _ _ _ _ i

  have hB := GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) B B (B ⊗[T] FractionRing T)
    (Algebra.ofId B (B ⊗[T] FractionRing T))

  refine eqv_of_square _ (Algebra.ofId B (B ⊗[T] FractionRing T)).toRingHom (RingEquiv.refl B)
    (Algebra.TensorProduct.comm T (FractionRing T) B).toRingEquiv ?_ _ (hB ?_)
  · ext b
    simp [Algebra.TensorProduct.algebraMap_apply]
  intro O _ _ hO hOi
  letI : Algebra (Polynomial T) O := ((algebraMap B O).comp (algebraMap (Polynomial T) B)).toAlgebra
  letI : Algebra T O := ((algebraMap B O).comp (algebraMap T B)).toAlgebra
  haveI : IsScalarTower T (Polynomial T) O := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap B O (algebraMap T B x) = algebraMap B O (algebraMap (Polynomial T) B (algebraMap T (Polynomial T) x))
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) B x]
  haveI : IsScalarTower T B O := IsScalarTower.of_algebraMap_eq fun x => rfl
  have hOi' : IndEt (Polynomial T) O :=
    isIndEtale_comp_etale (algebraMap (Polynomial T) B) (RingHom.etale_algebraMap.2 inferInstance)
      (algebraMap B O) hOi
  have hc := core q T hT hq O hO hOi' i
  refine eqv_of_square _ _ (Algebra.TensorProduct.rid B B O).toRingEquiv
    ((Algebra.TensorProduct.cancelBaseChange T B B O (FractionRing T)).toRingEquiv.trans
      (Algebra.TensorProduct.comm T O (FractionRing T)).toRingEquiv) ?_ _ hc
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o b => simp [Algebra.smul_def]
  | add x y hx hy => simp only [map_add (f := _)] at hx hy ⊢; rw [hx, hy]

end GlobalTheory.EtC.LineAcyc

namespace GlobalTheory.EtC.LineAcyc

theorem c3 : C3 := affineLine_localAcyclicity_of_strictHenselian_points GlobalTheory.T.etaleCohomology_equiv_strictHenselian_line_point

end GlobalTheory.EtC.LineAcyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrAlgClosedResidueInjectiveLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompleteClosedDvr

theorem exists_complete_dvr_isAlgClosed : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], ¬ IsField V → Nonempty (ℚ →+* V) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ρ : V →+* W), IsAdicComplete (maximalIdeal W) W ∧ IsAlgClosed (ResidueField W) ∧ Function.Injective ρ ∧ IsLocalHom ρ := by
  intro V _ _ _ _ _ _
  obtain ⟨D, _, _, _, φ, hac, hinj, hc⟩ := GlobalTheory.UnifProperChar.exists_dvr_centre V (maximalIdeal V)
  have : IsLocalHom φ := ((IsLocalRing.local_hom_tfae φ).out 1 5).mpr hc
  have hb := AdicCompletion.residueField_map_bijective_of_fg (R := D)
    (maximalIdeal D).fg_of_isNoetherianRing
  refine ⟨AdicCompletion (maximalIdeal D) D, inferInstance, inferInstance, inferInstance,
    (algebraMap D _).comp φ, inferInstance, ?_,
    (GlobalTheory.injective_and_isLocalHom_adicCompletion_comp φ hinj).1,
    (GlobalTheory.injective_and_isLocalHom_adicCompletion_comp φ hinj).2⟩
  exact IsAlgClosed.of_ringEquiv (ResidueField D) _ (RingEquiv.ofBijective _ hb)

end GlobalTheory.CompleteClosedDvr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSabMapOfGrpPullbackRespectingActionBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.TriplePull

theorem exists_sabMap_of_isProper : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (π : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G f π → (∀ a, (t'.act.act a).left ≫ π = π ≫ (t.act.act a).left) → LBIso t'.PP.L (t.PP.L.pull π) → ∃ m : SABMap t' t f, m.φ = π := by
  intro E _ _ _ H S S' t' t f π hp gp hact h
  have hp' : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) gp.1 hp
  exact GlobalTheory.CartTriple.exists_tripleMap GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 E H S S' f t' t π
    ⟨t'.semi.comm, t'.semi.smooth, hp', t'.semi.geomConnected⟩ gp hact h

end GlobalTheory.UCanon.TriplePull
end

