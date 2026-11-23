module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0048
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericChartFunctionsFractionsSmooth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.Mum

theorem injective_gp_app {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (U : M.S.Opens) :
    Function.Injective (M.gp.app U).hom := by
  haveI := M.integral
  haveI := M.dominant
  by_cases hU : (U : Set M.S).Nonempty
  · obtain ⟨x, hx⟩ := M.gp.denseRange.exists_mem_open U.isOpen hU
    have h1 := germ_injective_of_isIntegral (X := M.S) (M.gp x) hx
    have h2 := M.gp.germ_stalkMap U x hx
    have hcl : closure {M.gp x} = (Set.univ : Set M.S) := by
      have hd := M.gp.denseRange
      have hr : Set.range M.gp = {M.gp x} := by
        ext y; constructor
        · rintro ⟨z, rfl⟩
          haveI : Subsingleton (Sp (FractionRing R)) := inferInstanceAs (Subsingleton (PrimeSpectrum _))
          rw [Subsingleton.elim z x]; rfl
        · rintro rfl; exact ⟨x, rfl⟩
      rw [← hr]; exact hd.closure_range
    have hF := isField_stalk_of_closure_mem_irreducibleComponents M.S (M.gp x)
      (by rw [hcl]; simp [irreducibleComponents_eq_singleton])
    letI := hF.toField
    have h3 : Function.Injective (M.gp.stalkMap x).hom := RingHom.injective _
    intro a b h
    apply h1
    apply h3
    have ea := congrArg (fun φ => φ.hom a) h2
    have eb := congrArg (fun φ => φ.hom b) h2
    simp only [CommRingCat.comp_apply] at ea eb
    rw [ea, eb, h]
  · have : U = ⊥ := by
      ext y; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hy => hU ⟨y, hy⟩
    subst this
    intro a b _; exact Subsingleton.elim a b

def fracRes (R : Type) [CommRing R] [IsDomain R] (V : (Sp (FractionRing R)).Opens) : R →+* Γ(Sp (FractionRing R), V) :=
  ((Sp (FractionRing R)).presheaf.map (homOfLE le_top).op).hom.comp
    (((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom).comp (algebraMap R (FractionRing R)))

theorem isUnit_fracRes {R : Type} [CommRing R] [IsDomain R] (V : (Sp (FractionRing R)).Opens) {r : R} (hr : r ≠ 0) :
    IsUnit (fracRes R V r) := by
  have : IsUnit (algebraMap R (FractionRing R) r) :=
    Ne.isUnit ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
  exact this.map (((Sp (FractionRing R)).presheaf.map (homOfLE le_top).op).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)

theorem exists_mul_fracRes {R : Type} [CommRing R] [IsDomain R] (V : (Sp (FractionRing R)).Opens)
    (k : Γ(Sp (FractionRing R), V)) : ∃ a r : R, r ≠ 0 ∧ k * fracRes R V r = fracRes R V a := by
  haveI : Subsingleton (Sp (FractionRing R)) := inferInstanceAs (Subsingleton (PrimeSpectrum _))
  by_cases h : (V : Set (Sp (FractionRing R))).Nonempty
  · obtain ⟨x, hx⟩ := h
    have hV : V = ⊤ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      exact Subsingleton.elim x y ▸ hx
    subst hV
    obtain ⟨⟨a, r⟩, hr⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R)
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom k)
    refine ⟨a, r, nonZeroDivisors.ne_zero r.2, ?_⟩
    have hmap : ((Sp (FractionRing R)).presheaf.map (homOfLE (le_top : (⊤ : (Sp (FractionRing R)).Opens) ≤ ⊤)).op) = 𝟙 _ := by
      rw [show (homOfLE (le_top : (⊤ : (Sp (FractionRing R)).Opens) ≤ ⊤)) = 𝟙 _ from Subsingleton.elim _ _]
      simp
    simp only [fracRes, RingHom.coe_comp, Function.comp_apply, hmap, CommRingCat.hom_id, RingHom.id_apply]
    have hk : k = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom k) := by
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
    rw [hk, ← map_mul, ← hr, IsLocalization.mk'_spec]
  · have hV : V = ⊥ := by
      ext y; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hy => h ⟨y, hy⟩
    subst hV
    exact ⟨0, 1, one_ne_zero, Subsingleton.elim _ _⟩

theorem appLE_jK_eq_fracRes {R : Type} [CommRing R] [IsDomain R] (f : Sp (FractionRing R) ⟶ Sp R) (hf : f = jK R)
    (V : (Sp (FractionRing R)).Opens) (e : V ≤ f ⁻¹ᵁ ⊤) (x : R) :
    (f.appLE ⊤ V e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) = fracRes R V x := by
  subst hf
  have h := congrArg (fun φ => φ.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  simp only [fracRes, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.appLE, CommRingCat.comp_apply]
  rw [h]
  rfl

theorem gp_app_fracRes {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (U : M.S.Opens) (e : U ≤ M.π ⁻¹ᵁ ⊤) (r : R) :
    (M.gp.app U).hom ((M.π.appLE ⊤ U e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      fracRes R (M.gp ⁻¹ᵁ U) r := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_jK_eq_fracRes _ M.gp_π _ _ r

theorem injective_and_exists_frac_genericChart : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (W : G.left.Opens) (U : M.S.Opens), W ≤ G.hom ⁻¹ᵁ U → IsAffineOpen W → IsAffineOpen U → Function.Injective (α.app W).hom ∧ ∀ b : Γ(Y, α ⁻¹ᵁ W), ∃ c s : Γ(G.left, W), IsUnit ((α.app W).hom s) ∧ b * (α.app W).hom s = (α.app W).hom c := by
  intro R _ _ M G hG Y α t hpb W U hWU hW hU
  have hV : IsAffineOpen (M.gp ⁻¹ᵁ U) := isAffineOpen_Sp_field _ _
  have hle := locInt_le_gen G.hom α t M.gp hpb.w W U hWU
  have hUY : α ⁻¹ᵁ W = α ⁻¹ᵁ W ⊓ t ⁻¹ᵁ (M.gp ⁻¹ᵁ U) := (inf_eq_left.2 hle).symm
  have po := (isIso_pushoutSection_iff hpb (US := U) (UT := M.gp ⁻¹ᵁ U) (UX := W) le_rfl hWU hUY).mp
    (isIso_pushoutSection_of_isAffineOpen hpb le_rfl hWU hUY hU hV hW)
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at po
  letI : Algebra Γ(M.S, U) Γ(G.left, W) := (G.hom.appLE U W hWU).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) := (M.gp.app U).hom.toAlgebra
  letI : Algebra Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom.toAlgebra
  letI : Algebra Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) hle).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Y, α ⁻¹ᵁ W) := (G.hom.appLE U W hWU ≫ α.app W).hom.toAlgebra
  haveI : IsScalarTower Γ(M.S, U) Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom po.w)
  haveI : Algebra.IsPushout Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    CommRingCat.isPushout_iff_isPushout.mp po
  haveI : Algebra.Smooth Γ(M.S, U) Γ(G.left, W) :=
    HasRingHomProperty.appLE @AlgebraicGeometry.Smooth G.hom hG ⟨U, hU⟩ ⟨W, hW⟩ hWU
  haveI : Module.Flat Γ(M.S, U) Γ(G.left, W) := inferInstance
  let e := Algebra.IsPushout.equiv Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W)
  have he1 : ∀ c : Γ(G.left, W), e (c ⊗ₜ 1) = (α.app W).hom c := fun c => by
    rw [Algebra.IsPushout.equiv_tmul, map_one, _root_.mul_one]; rfl
  have hinc := Algebra.TensorProduct.includeLeft_injective (S := Γ(M.S, U)) (R := Γ(M.S, U))
    (A := Γ(G.left, W)) (B := Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)) (injective_gp_app M U)
  refine ⟨fun a b h => hinc (e.injective ?_), fun b => ?_⟩
  · change e (a ⊗ₜ 1) = e (b ⊗ₜ 1)
    rw [he1, he1, h]

  have eU : U ≤ M.π ⁻¹ᵁ ⊤ := fun x _ => trivial
  let σ : R →+* Γ(G.left, W) := (algebraMap Γ(M.S, U) Γ(G.left, W)).comp
    ((M.π.appLE ⊤ U eU).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  have hσ : ∀ r : R, (α.app W).hom (σ r) =
      algebraMap Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) (fracRes R (M.gp ⁻¹ᵁ U) r) := fun r => by
    rw [← gp_app_fracRes M U eU r]
    change algebraMap Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) (algebraMap Γ(M.S, U) Γ(G.left, W) _) =
      algebraMap Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) (algebraMap Γ(M.S, U) _ _)
    exact (IsScalarTower.algebraMap_apply Γ(M.S, U) Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) _).symm.trans
      (IsScalarTower.algebraMap_apply Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) _)
  have key : ∀ y : Γ(G.left, W) ⊗[Γ(M.S, U)] Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U),
      ∃ (c : Γ(G.left, W)) (r : R), r ≠ 0 ∧ e y * (α.app W).hom (σ r) = (α.app W).hom c := by
    intro y
    induction y with
    | tmul c k =>
      obtain ⟨a, r, hr, hk⟩ := exists_mul_fracRes (M.gp ⁻¹ᵁ U) k
      refine ⟨c * σ a, r, hr, ?_⟩
      rw [Algebra.IsPushout.equiv_tmul, hσ, map_mul, hσ, _root_.mul_assoc, ← map_mul, hk]
      rfl
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨c₁, r₁, hr₁, e₁⟩ := h₁
      obtain ⟨c₂, r₂, hr₂, e₂⟩ := h₂
      refine ⟨c₁ * σ r₂ + c₂ * σ r₁, r₁ * r₂, mul_ne_zero hr₁ hr₂, ?_⟩
      rw [map_add (f := _), add_mul, map_mul σ, map_mul, map_add (f := _), map_mul, map_mul, ← e₁, ← e₂]
      ring
  obtain ⟨c, r, hr, hc⟩ := key (e.symm b)
  refine ⟨c, σ r, ?_, ?_⟩
  · rw [hσ]; exact (isUnit_fracRes _ hr).map _
  · rw [← hc, e.apply_symm_apply]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFiberArithmeticVarietyIntegralProjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem genericFibre_facts : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (D : ℕ), IsArithVar p D → ∃ (_ : IsIntegral G) (_ : IsLocallyNoetherian G), IsProjOver q ∧ topologicalKrullDim G = D ∧ j (genericPoint G) = genericPoint X ∧ Function.Injective j ∧ (∀ x, IsIso (j.stalkMap x)) ∧ (∀ x, Order.coheight (j x) = Order.coheight x) ∧ ∀ z : X, z ∉ Set.range j → ∀ σ : k →+* ℂ, IsEmpty (CxPts (closι z ≫ p) σ) := by
  intro k K _ _ _ _ X G _ p q j hp D h
  obtain ⟨hG, hd, hη⟩ := GenSmoothCover.genericFibre h hp
  have hq : IsProjOver q := ProjSpace.isProjOver_of_isPullback_spMap _ hp h.isProjOver
  have : IsProper q := CommonModel.isProper_of_isProjOver hq
  have := h.isDomain
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion j := MorphismProperty.of_isPullback hp.flip this
  have := flat_specMap_localization (nonZeroDivisors k) K
  have : Flat j := MorphismProperty.of_isPullback hp.flip this
  have hs (x : G) : IsIso (j.stalkMap x) := GenSpread.isIso_stalkMap_of_flat j x
  refine ⟨hG, LocallyOfFiniteType.isLocallyNoetherian q, hq, hd, hη, j.isEmbedding.injective, hs,
    fun x => ?_, fun z hz σ => ⟨fun y => hz ?_⟩⟩
  · have := hs x
    have e := ringKrullDim_eq_of_ringEquiv (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at e
    exact_mod_cast e
  · have hr : Set.range j = p ⁻¹' Set.range (spMap (algebraMap k K)) := by
      rw [← Scheme.Pullback.range_fst, ← hp.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
        Function.Surjective.range_comp hp.isoPullback.hom.surjective]
    let c : Sp ℂ := IsLocalRing.closedPoint ℂ
    have hw : closι z (y.1 c) ∈ closure {z} := by
      have : closι z (y.1 c) ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subschemeι :=
        ⟨_, rfl⟩
      rw [Scheme.IdealSheafData.range_subschemeι] at this
      simpa using this
    have h₁ : p z ⤳ p (closι z (y.1 c)) := (specializes_iff_mem_closure.2 hw).map p.continuous
    have h₂ : p (closι z (y.1 c)) = spMap σ c := by
      have := y.2
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun f : Sp ℂ ⟶ Sp k => f c) this
    have h₃ : (spMap σ c).asIdeal = ⊥ := by
      change Ideal.comap σ (IsLocalRing.maximalIdeal ℂ) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective _ (ChernNull.injective_of_arithVar h σ)
    rw [h₂] at h₁
    have h₄ : (p z).asIdeal ≤ (spMap σ c).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 h₁
    rw [h₃, le_bot_iff] at h₄
    rw [hr]
    refine ⟨(⟨⊥, inferInstance⟩ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
    rw [h₄]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective k K)

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIsoSpecialisesToFieldPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.Spread

theorem spread_fibre : ∀ (o Ω : Type) [CommRing o] [IsNoetherianRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (G : Over M.Z) [GrpObj G], IsSemiAbelian G → ∀ (R' : Subalgebra o Ω) (B : Over (Sp R')) [GrpObj B], IsSemiAbelian B → ∀ (A₀ : Over (Sp Ω)) [GrpObj A₀] (a' : A₀.left ⟶ B.left) (ψ : A₀.left ⟶ G.left), IsGrpPullback A₀ B (spMap R'.val.toRingHom) a' → IsGrpPullback A₀ G M.pt ψ → ∀ (K : Type) [Field K] (s : Sp K ⟶ M.Z), R' ≤ M.O (s (closedPoint K)) → ∀ (yK : R' →+* K), (∀ x : R', yK x = M.val s x) → ∀ (AK : Over (Sp K)) [GrpObj AK] (φK : AK.left ⟶ B.left), IsGrpPullback AK B (spMap yK) φK → ∃ Ψ : AK.left ⟶ G.left, IsGrpPullback AK G s Ψ ∧ (∀ (e : B ⟶ B) (F : G ⟶ G) (e₀ : A₀ ⟶ A₀), e₀.left ≫ a' = a' ≫ e.left → e₀.left ≫ ψ = ψ ≫ F.left → ∀ eK : AK ⟶ AK, eK.left ≫ φK = φK ≫ e.left → eK.left ≫ Ψ = Ψ ≫ F.left) ∧ ∀ (b : Sp R' ⟶ B.left) (gγ : Over.mk M.pt ⟶ G) (w : Sp Ω ⟶ A₀.left), b ≫ B.hom = 𝟙 _ → w ≫ A₀.hom = 𝟙 _ → w ≫ a' = spMap R'.val.toRingHom ≫ b → w ≫ ψ = gγ.left → ∀ (T : Scheme.{0}) (x : T ⟶ AK.left) (v : T ⟶ G.left), x ≫ φK = x ≫ AK.hom ≫ spMap yK ≫ b → ValAt gγ (x ≫ AK.hom ≫ s) v → x ≫ Ψ = v := by
  intro o Ω _ _ _ _ M hN G _ hG R' B _ hB A₀ _ a' ψ ha' hψ K _ s hR' yK hyK AK _ φK hφK
  set z := s (closedPoint K) with hz
  haveI : IsNoetherianRing (M.O z) := M.isNoetherianRing_O z
  haveI : IsIntegrallyClosed (M.O z) := RatModel.isIntegrallyClosed_O hN z

  let ιO : Sp (M.O z) ⟶ M.Z :=
    Spec.map (CommRingCat.ofHom (M.stalkEquiv z).toRingHom : M.Z.presheaf.stalk z ⟶ CommRingCat.of (M.O z)) ≫
      M.Z.fromSpecStalk z
  have key : ∀ {C : Type} [CommRing C] [IsLocalRing C] (y : Sp C ⟶ M.Z) (hy : y (closedPoint C) ⤳ z)
      (r : M.O z →+* C), r.comp (M.stalkEquiv z).toRingHom =
        (M.Z.presheaf.stalkSpecializes hy ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of C) y).hom →
      spMap r ≫ ιO = y := by
    intro C _ _ y hy r hr
    have e : (CommRingCat.ofHom (M.stalkEquiv z).toRingHom : M.Z.presheaf.stalk z ⟶ CommRingCat.of (M.O z)) ≫
        CommRingCat.ofHom r = M.Z.presheaf.stalkSpecializes hy ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of C) y := by
      ext a
      exact congrArg (fun f : M.Z.presheaf.stalk z →+* C => f a) hr
    have e2 : spMap r ≫ Spec.map (CommRingCat.ofHom (M.stalkEquiv z).toRingHom : M.Z.presheaf.stalk z ⟶ CommRingCat.of (M.O z)) =
        Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of C) y) ≫ Spec.map (M.Z.presheaf.stalkSpecializes hy) :=
      (Spec.map_comp _ _).symm.trans ((congrArg Spec.map e).trans (Spec.map_comp _ _))
    change spMap r ≫ Spec.map (CommRingCat.ofHom (M.stalkEquiv z).toRingHom : M.Z.presheaf.stalk z ⟶ CommRingCat.of (M.O z)) ≫
      M.Z.fromSpecStalk z = y
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ M.Z.fromSpecStalk z) e2).trans
      ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of C) y) ≫ ·)
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hy)).trans ?_
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk y
  have hpt : spMap (algebraMap (M.O z) Ω) ≫ ιO = M.pt :=
    key M.pt (M.pt_specializes _ z) _ (by ext a; rfl)
  let v : M.O z →+* K := RatModel.valLoc s z specializes_rfl
  have hs : spMap v ≫ ιO = s := key s specializes_rfl v (by ext a; simp [v, RatModel.valLoc])

  let ι' : R' →+* M.O z := (Subalgebra.inclusion hR').toRingHom
  have hyv : yK = v.comp ι' := by
    ext x
    rw [hyK x, RingHom.comp_apply]
    exact (RatModel.valLoc_eq_val s specializes_rfl (ι' x)).symm
  have spc : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hyK' : spMap yK = spMap v ≫ spMap ι' := by rw [hyv, spc]
  have hval : spMap R'.val.toRingHom = spMap (algebraMap (M.O z) Ω) ≫ spMap ι' := by
    rw [← spc]; rfl

  let BO := (Over.pullback (spMap ι')).obj B
  let GO := (Over.pullback ιO).obj G
  have hBO : IsGrpPullback BO B (spMap ι') (pullback.fst _ _) := isGrpPullback_pullback B _
  have hGO : IsGrpPullback GO G ιO (pullback.fst _ _) := isGrpPullback_pullback G _
  have hBOs : IsSemiAbelian BO := IsSemiAbelian.pullback _ B hB
  have hGOs : IsSemiAbelian GO := IsSemiAbelian.pullback _ G hG
  let j := spMap (algebraMap (M.O z) Ω)
  let a₀ : A₀.left ⟶ BO.left := pullback.lift a' (A₀.hom ≫ j) (by
    rw [ha'.1.w, hval, Category.assoc])
  have ha₀ : a₀ ≫ pullback.fst _ _ = a' := pullback.lift_fst _ _ _
  have ha₀' : a₀ ≫ BO.hom = A₀.hom ≫ j := pullback.lift_snd _ _ _
  have hA₀B : IsGrpPullback A₀ BO j a₀ :=
    hBO.cancel (ha'.congr hval ha₀.symm) ha₀'
  let ψ₀ : A₀.left ⟶ GO.left := pullback.lift ψ (A₀.hom ≫ j) (by
    rw [hψ.1.w, ← hpt, Category.assoc])
  have hψ₀ : ψ₀ ≫ pullback.fst _ _ = ψ := pullback.lift_fst _ _ _
  have hψ₀' : ψ₀ ≫ GO.hom = A₀.hom ≫ j := pullback.lift_snd _ _ _
  have hA₀G : IsGrpPullback A₀ GO j ψ₀ :=
    hGO.cancel (hψ.congr hpt.symm hψ₀.symm) hψ₀'
  have hj : GlobalTheory.IsGenericPointHom j := GlobalTheory.IsGenericPointHom.fractionField (M.O z) Ω
  obtain ⟨E, ⟨hEm, hE⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.generic_existsUnique_iso_of_extensions
    GlobalTheory.semiAbelianHomExtension_holds (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec (M.O z)) hj
    hBOs hGOs hA₀B hA₀G

  let φO : AK.left ⟶ BO.left := pullback.lift φK (AK.hom ≫ spMap v) (by
    rw [hφK.1.w, hyK', Category.assoc])
  have hφO : φO ≫ pullback.fst _ _ = φK := pullback.lift_fst _ _ _
  have hφO' : φO ≫ BO.hom = AK.hom ≫ spMap v := pullback.lift_snd _ _ _
  have hAKB : IsGrpPullback AK BO (spMap v) φO := hBO.cancel (hφK.congr hyK' hφO.symm) hφO'

  obtain ⟨-, hGsep⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨hBOf, -⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian BO hBOs
  obtain ⟨-, hGOsep⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian GO hGOs
  obtain ⟨hjq, hjd⟩ := hj.quasiCompact_and_dominant
  have hEw : E.hom.left ≫ GO.hom = BO.hom := Over.w E.hom
  refine ⟨φO ≫ E.hom.left ≫ pullback.fst _ _, ?_, ?_, ?_⟩
  · refine ((hAKB.comp (isGrpPullback_of_iso E)).comp hGO).congr ?_ ?_
    · rw [Category.comp_id, hs]
    · simp only [Category.assoc]
  · intro e F e₀ he₀a he₀ψ eK heK
    let eO := (Over.pullback (spMap ι')).map e
    let FO := (Over.pullback ιO).map F
    have heO : eO.left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ e.left := pullback.lift_fst _ _ _
    have heO' : eO.left ≫ BO.hom = BO.hom := Over.w eO
    have hFO : FO.left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ F.left := pullback.lift_fst _ _ _
    have hFO' : FO.left ≫ GO.hom = GO.hom := Over.w FO
    have h1 : e₀.left ≫ a₀ = a₀ ≫ eO.left := by
      apply pullback.hom_ext
      · rw [Category.assoc, ha₀, Category.assoc, heO, ← Category.assoc, ha₀, he₀a]
      · change e₀.left ≫ a₀ ≫ BO.hom = a₀ ≫ eO.left ≫ BO.hom
        rw [heO', ha₀', ← Category.assoc, Over.w e₀]
    have h2 : e₀.left ≫ ψ₀ = ψ₀ ≫ FO.left := by
      apply pullback.hom_ext
      · rw [Category.assoc, hψ₀, Category.assoc, hFO, ← Category.assoc, hψ₀, he₀ψ]
      · change e₀.left ≫ ψ₀ ≫ GO.hom = ψ₀ ≫ FO.left ≫ GO.hom
        rw [hFO', hψ₀', ← Category.assoc, Over.w e₀]
    have h3 : eO ≫ E.hom = E.hom ≫ FO := by
      refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback hA₀B.1 ?_
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← h1, Category.assoc, hE, ← Category.assoc, hE, h2]
    have h4 : eK.left ≫ φO = φO ≫ eO.left := by
      apply pullback.hom_ext
      · rw [Category.assoc, hφO, Category.assoc, heO, ← Category.assoc, hφO, heK]
      · change eK.left ≫ φO ≫ BO.hom = φO ≫ eO.left ≫ BO.hom
        rw [heO', hφO', ← Category.assoc, Over.w eK]
    have h5 := congrArg (fun f => f.left ≫ pullback.fst G.hom ιO) h3
    simp only [Over.comp_left, Category.assoc, hFO] at h5
    rw [← Category.assoc, h4, Category.assoc, h5]
    simp only [Category.assoc]
  · intro b gγ w hb hw hwa hwψ T x vv hx hv
    by_cases hT : IsEmpty T
    · exact (isInitialOfIsEmpty (X := T)).hom_ext _ _
    obtain ⟨t₀⟩ := not_isEmpty_iff.1 hT
    obtain ⟨W, h, s', ⟨h1, h2⟩, hs', rfl⟩ := id hv
    have hzpt : (x ≫ AK.hom ≫ s) t₀ = z := by
      simp only [Scheme.Hom.comp_apply]
      exact congrArg s (Subsingleton.elim _ _)
    have hzW : z ∈ W := by rw [← hzpt, ← hs']; exact (s' t₀).2
    have hr : Set.range ιO ⊆ Set.range W.ι := by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hp : ιO p ∈ Set.range (M.Z.fromSpecStalk z) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rw [Scheme.range_fromSpecStalk] at hp
      exact Specializes.mem_open hp W.isOpen hzW
    let ℓ := IsOpenImmersion.lift W.ι ιO hr
    have hℓ : ℓ ≫ W.ι = ιO := IsOpenImmersion.lift_fac _ _ _
    let bO : Sp (M.O z) ⟶ BO.left := pullback.lift (spMap ι' ≫ b) (𝟙 _) (by
      rw [Category.assoc, hb, Category.comp_id, Category.id_comp])
    have hbO : bO ≫ pullback.fst _ _ = spMap ι' ≫ b := pullback.lift_fst _ _ _
    have hbO' : bO ≫ BO.hom = 𝟙 _ := pullback.lift_snd _ _ _
    have hEG : E.hom.left ≫ pullback.fst G.hom ιO ≫ G.hom = BO.hom ≫ ιO := by
      rw [pullback.condition, ← Category.assoc, ← hEw]; rfl
    have hσ : bO ≫ E.hom.left ≫ pullback.fst G.hom ιO = ℓ ≫ h := by
      refine ext_of_isDominant_of_isSeparated G.hom ?_ j ?_
      · rw [Category.assoc, Category.assoc, hEG, ← Category.assoc, hbO', Category.id_comp, Category.assoc, h1, hℓ]
      · have hjb : j ≫ bO = w ≫ a₀ := by
          apply pullback.hom_ext
          · rw [Category.assoc, hbO, Category.assoc, ha₀, hwa, hval, Category.assoc]
          · change j ≫ bO ≫ BO.hom = w ≫ a₀ ≫ BO.hom
            rw [hbO', ha₀', ← Category.assoc, hw, Category.comp_id, Category.id_comp]
        rw [← Category.assoc, hjb, Category.assoc, ← Category.assoc a₀, hE, hψ₀, hwψ, ← Category.assoc]
        exact (h2 _ (by rw [Category.assoc, hℓ]; exact hpt)).symm
    have hxb : x ≫ φO = (x ≫ AK.hom ≫ spMap v) ≫ bO := by
      apply pullback.hom_ext
      · rw [Category.assoc, hφO, hx, Category.assoc, hbO, hyK']
        simp only [Category.assoc]
      · change x ≫ φO ≫ BO.hom = (x ≫ AK.hom ≫ spMap v) ≫ bO ≫ BO.hom
        rw [hφO', hbO', Category.comp_id]
    refine ValAt.unique ?_ hv
    refine ⟨W, h, (x ≫ AK.hom ≫ spMap v) ≫ ℓ, ⟨h1, h2⟩, ?_, ?_⟩
    · rw [Category.assoc, hℓ]
      simp only [Category.assoc, hs]
    · have hxb' : x ≫ φO ≫ E.hom.left ≫ pullback.fst G.hom ιO = ((x ≫ AK.hom ≫ spMap v) ≫ ℓ) ≫ h := by
        rw [← Category.assoc x φO, hxb, Category.assoc, hσ]
        simp only [Category.assoc]
      simpa only [Category.assoc] using hxb'.symm

end GlobalTheory.Poinc.Spread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointGenericFibreMemberHasLabel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

theorem torsion_has_label : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), xb ^ (X₁.S.r * X₁.S.N) = 1 → ∃ a : X₁.S.Gam, xb.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt a).left := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 xb hxb
  let T := TFK (R := V) (AlgebraicClosure (FractionRing V))
  obtain ⟨a, ha, -⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) (T.hom ≫ spMap 𝔪.yK) (pushHom 𝔪.cart T xb)
    (by rw [← map_pow, hxb, map_one])
  refine ⟨a, ?_⟩
  have h1 : (T.hom ≫ spMap 𝔪.yK) ≫ (X₁.ρ.pt a).left = xb.left ≫ 𝔪.φ := congrArg (fun z => z.left) ha
  rw [← h1]
  congr 1
  exact (Spec.map_comp (CommRingCat.ofHom 𝔪.yK)
    (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))))).symm

end GlobalTheory.Poinc.IntTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o' : Obj b N s') (o : Obj b N s) (f : S' ⟶ S) (m m' : ObjMap o' o f), m.φ = m'.φ := by
  first | exact @GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique | exact GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique | (intros; apply GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique <;> assumption)
end

