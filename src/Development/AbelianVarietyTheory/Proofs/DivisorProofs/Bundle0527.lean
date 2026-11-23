module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyDerivativeRelationSemilinearPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory


set_option maxHeartbeats 600000 in
theorem dRel_pull : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (x : HO1 s) (n : ℕ) (y : Fin n → HO1 s) (w : Fin n → GlobForm s), DRel (OAff s) x y w → DRel (OAff s') (pullHO1 h x) (fun k ↦ pullHO1 h (y k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (w k)) := by
  intro R R' _ _ X X' s s' σ φ h x n y w hx
  obtain ⟨f, g, ω, hf, hg, hD⟩ := hx
  obtain ⟨f', hf'⟩ := H1.mk_surjective (OAff s') (pullHO1 h x)
  choose g' hg' using fun k ↦ H1.mk_surjective (OAff s') (pullHO1 h (y k))
  have ef := (isPullO_pullHO1 h x).symm
  rw [← hf', ← hf, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at ef
  obtain ⟨A, hA⟩ := ef
  have eg : ∀ k, ∃ B : C0 (OPair φ s'), d0 (OPair φ s') B =
      ((pairRes φ s').pullbackOneCocycle (g' k)).1 - ((pairPull h).pullbackOneCocycle (g k)).1 := by
    intro k
    have e := (isPullO_pullHO1 h (y k)).symm
    rw [← hg' k, ← hg k, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at e
    exact e
  choose B hB using eg
  have hA' : ∀ ⦃t t' : (Pair φ)ᵒᵖ⦄ (a : t ⟶ t'), ((pairRes φ s').pullbackOneCocycle f').1 t t' a =
      ((pairPull h).pullbackOneCocycle f).1 t t' a + (A t' - mp (OPair φ s') a (A t)) := by
    intro t t' a
    have e := congrFun (congrFun (congrFun hA t) t') a
    rw [amitsur_d0_apply, Pi.sub_apply, Pi.sub_apply] at e
    exact sub_eq_iff_eq_add'.1 e.symm
  have hB' : ∀ k ⦃t t' : (Pair φ)ᵒᵖ⦄ (a : t ⟶ t'), ((pairRes φ s').pullbackOneCocycle (g' k)).1 t t' a =
      ((pairPull h).pullbackOneCocycle (g k)).1 t t' a + (B k t' - mp (OPair φ s') a (B k t)) := by
    intro k t t' a
    have e := congrFun (congrFun (congrFun (hB k) t) t') a
    rw [amitsur_d0_apply, Pi.sub_apply, Pi.sub_apply] at e
    exact sub_eq_iff_eq_add'.1 e.symm
  set w' : Fin n → GlobForm s' := fun k ↦ pullForm h (w k) with hw'def
  let Wm : Fin n → Glob1 (OPair φ s') := fun k ↦ pullGlob1 (pairPull h) (w k)
  have hWm : ∀ k t, (Wm k).1 t = (w' k).1 ((pairFst φ).obj t) := fun k t ↦
    (congrArg (fun z : Glob1 (OPair φ s') ↦ z.1 t) (isPullForm_pullForm h (w k))).trans
      (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff s') (pairFst φ) t _)
  let κ : A1 (OAff s') := fun T T' a ↦ D R' _ (f'.1 T T' a) - ∑ k, (g' k).1 T T' a • (w' k).1 T'
  have hκ : ∀ ⦃T T' T'' : AffOp X'⦄ (a : T ⟶ T') (b : T' ⟶ T''),
      κ T T'' (a ≫ b) = p1 (OAff s') b (κ T T' a) + κ T' T'' b := by
    intro T T' T'' a b
    have e1 : D R' _ (f'.1 T T'' (a ≫ b)) =
        p1 (OAff s') b (D R' _ (f'.1 T T' a)) + D R' _ (f'.1 T' T'' b) := by
      rw [Z1.comp, Derivation.map_add (D := _), p1_D]
    have e2 : ∀ k, (g' k).1 T T'' (a ≫ b) • (w' k).1 T'' =
        p1 (OAff s') b ((g' k).1 T T' a • (w' k).1 T') + (g' k).1 T' T'' b • (w' k).1 T'' := by
      intro k; rw [Z1.comp, add_smul, oneFormsMapOfFunctorMorphism_smul, ← (w' k).2 b]
    simp only [κ]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, Finset.sum_congr rfl fun k _ ↦ e2 k, Finset.sum_add_distrib, map_sub, map_sum]
    abel
  let θP : A0 (OPair φ s') := fun t ↦
    q1 (pairPull h) t (ω ((pairPull h).G.obj t)) + D R' _ (A t) - ∑ k, B k t • (Wm k).1 t
  have key : ∀ ⦃t t' : (Pair φ)ᵒᵖ⦄ (a : t ⟶ t'),
      D R' _ (((pairRes φ s').pullbackOneCocycle f').1 t t' a) - ∑ k, ((pairRes φ s').pullbackOneCocycle (g' k)).1 t t' a • (Wm k).1 t' =
        θP t' - p1 (OPair φ s') a (θP t) := by
    intro t t' a
    have hW : ∀ k, (Wm k).1 t' = p1 (OPair φ s') a ((Wm k).1 t) := fun k ↦ (Wm k).2 a
    have e1 : D R' _ (((pairPull h).pullbackOneCocycle f).1 t t' a) =
        ∑ k, ((pairPull h).pullbackOneCocycle (g k)).1 t t' a • (Wm k).1 t' +
          (q1 (pairPull h) t' (ω ((pairPull h).G.obj t')) -
            p1 (OPair φ s') a (q1 (pairPull h) t (ω ((pairPull h).G.obj t)))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [CoefMap.pullCocycleOne_apply, ← cechDeRhamCoefMapOneForms_D, hD, map_add (f := _), map_sum, map_sub, cechDeRhamCoefMapOneForms_naturality]
      congr 1
      exact Finset.sum_congr rfl fun k _ ↦ prodFirstProjection_smul _ _ _
    have e2 : ∀ k, ((pairRes φ s').pullbackOneCocycle (g' k)).1 t t' a • (Wm k).1 t' =
        ((pairPull h).pullbackOneCocycle (g k)).1 t t' a • (Wm k).1 t' + B k t' • (Wm k).1 t' -
          p1 (OPair φ s') a (B k t • (Wm k).1 t) := by
      intro k
      rw [hB', oneFormsMapOfFunctorMorphism_smul, ← hW k, add_smul, sub_smul]
      abel
    simp only [θP]
    rw [hA', Derivation.map_add (D := _), Derivation.map_sub, ← p1_D, e1, Finset.sum_congr rfl fun k _ ↦ e2 k]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, map_sub, map_add (f := _), map_sum]
    abel
  let θ' : ∀ t : (Pair φ)ᵒᵖ, Ω[(OAff s').obj ((pairFst φ).obj t)⁄R'] := θP
  have hθ' : ∀ ⦃t t' : (Pair φ)ᵒᵖ⦄ (a : t ⟶ t'), κ _ _ ((pairFst φ).map a) =
      θ' t' - p1 (OAff s') ((pairFst φ).map a) (θ' t) := by
    intro t t' a
    have k := key a
    simp only [hWm] at k
    exact k
  obtain ⟨θ, hθ⟩ := GlobalTheory.cocycle_one_forms_coboundary_of_restrict (OAff s') (pairFst φ)
    (_root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' (pairFst φ) (_root_.GlobalTheory.CechDR.pair_cover_affine φ s'))
    (_root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' (pairFst φ) (_root_.GlobalTheory.CechDR.pair_cover_affine φ s')
      (_root_.GlobalTheory.CechDR.exists_pair_below_two φ s')) κ hκ θ' hθ'
  refine ⟨f', g', θ, hf', hg', fun T T' a ↦ ?_⟩
  exact sub_eq_iff_eq_add'.1 (hθ a)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommAlgFunctorCohomologyTwoEqZeroOfIsInitial
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.Vanish

theorem commAlgFunctorCohomologyTwo_eq_zero_of_isInitial {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) {T₀ : C} (h : IsInitial T₀) (c : CatCoh.H2 F) : c = 0 := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  refine H2.mk_eq_zero.2 ⟨fun T T' φ ↦ z.1 T₀ T T' (h.to T) φ, ?_⟩
  funext T T' T'' φ ψ
  have := z.2 (h.to T) φ ψ
  rw [h.to_comp φ] at this
  rw [d1_apply]
  linear_combination this

theorem glob_sub {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {T₀ : C}
    (h : IsInitial T₀) [Subsingleton Ω[F.obj T₀⁄R]] : Subsingleton (Glob1 F) :=
  subsingleton_of_forall_eq 0 fun ω ↦ Subtype.ext (funext fun T ↦ by
    rw [ω.2 (h.to T), Subsingleton.elim (ω.1 T₀) 0, map_zero]; rfl)

def topInit {X : Scheme.{0}} (hX : IsAffineOpen (⊤ : X.Opens)) : IsInitial (op ⟨⊤, hX⟩ : AffOp X) :=
  IsInitial.ofUniqueHom (fun U ↦ (homOfLE (show U.unop ≤ ⟨⊤, hX⟩ from le_top (a := U.unop.1))).op)
    fun _ _ ↦ rfl

theorem omega_sub {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsIso s] :
    Subsingleton Ω[Sec s ⊤⁄R] := by
  refine KaehlerDifferential.subsingleton_of_surjective R _ ?_
  have : IsIso (secMap s ⊤) := by
    unfold secMap
    haveI h1 : IsIso s.appTop := inferInstanceAs (IsIso (s.app ⊤))
    haveI h2 : IsIso (X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op) := by
      rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ from rfl]
      infer_instance
    exact IsIso.comp_isIso' (f := (Scheme.ΓSpecIso (CommRingCat.of R)).inv) inferInstance
      (IsIso.comp_isIso' h1 h2)
  exact (ConcreteCategory.bijective_of_isIso (secMap s ⊤)).2

theorem main :
    (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsAffine X → Subsingleton (HO1 s) ∧ Subsingleton (HO2 s)) ∧
      ∀ (R : Type) [CommRing R], Subsingleton (GlobForm (𝟙_ (Over (Sp R))).hom) ∧
        Subsingleton (HH1 (𝟙_ (Over (Sp R))).hom) := by
  refine ⟨fun R _ X s hX ↦ ?_, fun R _ ↦ ?_⟩
  · have h := topInit (isAffineOpen_top X)
    exact ⟨subsingleton_of_forall_eq 0 (H1.eq_zero_of_isInitial _ h),
      subsingleton_of_forall_eq 0 (commAlgFunctorCohomologyTwo_eq_zero_of_isInitial _ h)⟩
  · haveI : IsIso (𝟙_ (Over (Sp R))).hom := inferInstanceAs (IsIso (𝟙 (Sp R)))
    have h := topInit (isAffineOpen_top (Sp R))
    haveI : Subsingleton Ω[(OAff (𝟙_ (Over (Sp R))).hom).obj (op ⟨⊤, isAffineOpen_top (Sp R)⟩)⁄R] :=
      omega_sub (𝟙_ (Over (Sp R))).hom
    haveI hg : Subsingleton (GlobForm (𝟙_ (Over (Sp R))).hom) := glob_sub _ h
    refine ⟨hg, subsingleton_of_forall_eq 0 fun c ↦ ?_⟩
    have hc : c ∈ Fil1 (OAff (𝟙_ (Over (Sp R))).hom) := H1.eq_zero_of_isInitial _ h _
    rw [Fil1_eq_range] at hc
    obtain ⟨ω, rfl⟩ := hc
    have : ω = 0 := Subtype.ext (Subsingleton.elim (α := GlobForm (𝟙_ (Over (Sp R))).hom) _ _)
    rw [this, map_zero]

end GlobalTheory.AbCoh.Vanish
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionCurvatureSumWedgeSemilinearPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

section Helpers

variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type} [Category.{0} C] [Category.{0} C']

theorem pOm_wsum (F : C ⥤ CommAlgCat.{0} R) {n : ℕ} (u v : Fin n → Glob1 F) {T T' : C} (w : T ⟶ T') :
    pOm F 2 w (wsum F u v T) = wsum F u v T' := by
  unfold wsum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [pOm_wedge, ← (u k).2 w, ← (v k).2 w]

theorem qOm_wsum {σ : R →+* R'} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'} (m : CoefMap σ F F')
    {n : ℕ} (u v : Fin n → Glob1 F) (T : C') :
    qOm m 2 T (wsum F u v (m.G.obj T)) =
      wsum F' (fun k ↦ pullGlob1 m (u k)) (fun k ↦ pullGlob1 m (v k)) T := by
  unfold wsum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ qOm_wedge m _ _

end Helpers

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem obRel_pullHO1 : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (x : HO1 s) (n : ℕ) (u v : Fin n → GlobForm s), ObRel (OAff s) x u v → ObRel (OAff s') (pullHO1 h x) (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) := by
  intro R R' _ _ X X' s s' σ φ h x n u v hx
  obtain ⟨f, ω, hfx, hconn, hcurv⟩ := hx
  obtain ⟨f', hf'⟩ := H1.mk_surjective (OAff s') (pullHO1 h x)
  have e1 := isPullO_pullHO1 h x
  rw [IsPullO, ← hf', ← hfx, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at e1
  obtain ⟨b, hb⟩ := e1
  have hb' : ∀ (t t' : (Pair φ)ᵒᵖ) (a : t ⟶ t'), ((pairRes φ s').pullbackOneCocycle f').1 t t' a =
      ((pairPull h).pullbackOneCocycle f).1 t t' a - (b t' - mp (OPair φ s') a (b t)) := by
    intro t t' a
    have e := congrFun (congrFun (congrFun hb t) t') a
    simp only [Pi.sub_apply, amitsur_d0_apply] at e
    linear_combination e
  let ω'' : ∀ t : (Pair φ)ᵒᵖ, Ω[(OAff s').obj ((pairFst φ).obj t)⁄R'] :=
    fun t ↦ q1 (pairPull h) t (ω _) - D R' _ (b t)
  let κ : A1 (OAff s') := fun T T' ψ ↦ D R' _ (f'.1 T T' ψ)
  have hκ : ∀ ⦃T T' T'' : AffOp X'⦄ (a : T ⟶ T') (c : T' ⟶ T''),
      κ T T'' (a ≫ c) = p1 (OAff s') c (κ T T' a) + κ T' T'' c := by
    intro T T' T'' a c
    simp only [κ]
    rw [Z1.comp f', map_add (f := _), p1_D]
  have hθ' : ∀ ⦃t t' : (Pair φ)ᵒᵖ⦄ (a : t ⟶ t'),
      κ _ _ ((pairFst φ).map a) = ω'' t' - p1 (OAff s') ((pairFst φ).map a) (ω'' t) := by
    intro t t' a
    have e0 := hconn ((pairSnd φ).map a)
    have e : q1 (pairPull h) t' (ω _) = p1 (OPair φ s') a (q1 (pairPull h) t (ω _)) +
        D R' _ ((pairPull h).α t' (f.1 _ _ ((pairSnd φ).map a))) := by
      rw [← cechDeRhamCoefMapOneForms_naturality, ← cechDeRhamCoefMapOneForms_D, ← map_add (f := _)]; exact congrArg _ e0
    have k1 : κ _ _ ((pairFst φ).map a) = D R' _ (((pairPull h).pullbackOneCocycle f).1 t t' a) -
        (D R' _ (b t') - D R' _ (mp (OPair φ s') a (b t))) := by
      simp only [κ]
      rw [show f'.1 _ _ ((pairFst φ).map a) = ((pairRes φ s').pullbackOneCocycle f').1 t t' a from rfl, hb' t t' a,
        map_sub, map_sub] <;> rfl
    have k3 : p1 (OPair φ s') a (D R' _ (b t)) = D R' _ (mp (OPair φ s') a (b t)) :=
      p1_D _ _ _
    have key : ∀ {M : Type} [AddCommGroup M] (df da db dm q' q pq pd : M), df = da - (db - dm) →
        q' = pq + da → pd = dm → df = (q' - db) - (pq - pd) := by
      intros; subst_vars; abel
    rw [show ω'' t' - p1 (OAff s') ((pairFst φ).map a) (ω'' t) = (q1 (pairPull h) t' (ω _) - D R' _ (b t')) -
      (p1 (OPair φ s') a (q1 (pairPull h) t (ω _)) -
        p1 (OPair φ s') a (D R' _ (b t))) from by simp only [ω'', map_sub] <;> rfl]
    exact key _ _ _ _ _ (0 : Ω[(OAff s').obj ((pairFst φ).obj t')⁄R']) _ _ k1 e k3
  have hcov := _root_.GlobalTheory.CechDR.pair_cover_affine φ s'
  have hdir := _root_.GlobalTheory.CechDR.exists_pair_below_two φ s'
  have hs1 := _root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' (pairFst φ) hcov
  have hg1 := _root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' (pairFst φ) hcov hdir
  have hs2 := _root_.GlobalTheory.CechDR.twoForm_sep_of_basis s' (pairFst φ) hcov
  obtain ⟨θ, hθ⟩ := _root_.GlobalTheory.cocycle_one_forms_coboundary_of_restrict (OAff s') (pairFst φ) hs1 hg1
    κ hκ ω'' hθ'
  have key2 : ∀ {M : Type} [AddCommGroup M] (k A PA C PC PAC : M), k = A - PA → k = C - PC →
      PAC = PA - PC → A - C = PAC := by
    intro M _ k A PA C PC PAC h1 h2 h3
    subst h3
    exact sub_eq_sub_iff_sub_eq_sub.1 (h1.symm.trans h2)
  let δ : Glob1 (OPair φ s') := ⟨fun t ↦ θ ((pairFst φ).obj t) - ω'' t, fun t t' a ↦
    key2 _ _ _ _ _ _ (hθ ((pairFst φ).map a)) (hθ' a) (map_sub _ _ _)⟩
  obtain ⟨β, hβ⟩ := (pairRes_bijective φ s').2.1.2 δ
  have hβt : ∀ t, β.1 ((pairFst φ).obj t) = θ ((pairFst φ).obj t) - ω'' t := fun t ↦
    (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff s') (pairFst φ) t _).symm.trans (congrArg (fun z : Glob1 (OPair φ s') ↦ z.1 t) hβ)
  refine ⟨f', fun T ↦ θ T - β.1 T, hf', fun T T' ψ ↦ ?_, fun T ↦ ?_⟩
  · have key3 : ∀ {M : Type} [AddCommGroup M] (k A PA B PB : M), k = A - PA → B = PB →
        A - B = (PA - PB) + k := by
      intros; subst_vars; abel
    rw [map_sub]
    exact key3 _ _ _ _ _ (hθ ψ) (β.2 ψ)
  · refine sub_eq_zero.1 (hs2 T _ fun t w ↦ ?_)
    have key4 : ∀ {M : Type} [AddCommGroup M] (k A PA B PB O : M), k = A - PA → B = PB → B = A - O →
        PA - PB = O - k := by
      intros; subst_vars; abel
    have key5 : ∀ (B : Type) [CommRing B] [Algebra R' B] (y : Ω[B⁄R']) (c : B),
        dOne R' B (y - D R' B c) = dOne R' B y := fun B _ _ y c ↦ by rw [map_sub, dOne_D, sub_zero]
    have c1 : p1 (OAff s') w (θ T - β.1 T) = ω'' t - D R' _ (f'.1 _ _ w) := by
      rw [map_sub]; exact key4 _ _ _ _ _ _ (hθ w) (β.2 w) (hβt t)
    have e1 : ∀ (z : Fin n → GlobForm s) k, pullGlob1 (pairPull h) (z k) =
        pullGlob1 (pairRes φ s') (GlobalTheory.CechDR.pullForm h (z k)) := fun z k ↦ isPullForm_pullForm h (z k)
    have c2 : dOne R' ((OAff s').obj ((pairFst φ).obj t)) (ω'' t) = wsum (OAff s')
        (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) ((pairFst φ).obj t) := by
      calc dOne R' ((OAff s').obj ((pairFst φ).obj t)) (ω'' t)
          = dOne R' ((OPair φ s').obj t) (q1 (pairPull h) t (ω ((pairSnd φ).obj t))) := key5 _ _ _
        _ = qOm (pairPull h) 2 t (dOne R ((OAff s).obj ((pairSnd φ).obj t)) (ω ((pairSnd φ).obj t))) :=
          (qOm_dOne _ _).symm
        _ = qOm (pairPull h) 2 t (wsum (OAff s) u v ((pairSnd φ).obj t)) := by rw [hcurv]
        _ = wsum (OPair φ s') (fun k ↦ pullGlob1 (pairPull h) (u k)) (fun k ↦ pullGlob1 (pairPull h) (v k)) t :=
          qOm_wsum _ _ _ _
        _ = wsum (OPair φ s') (fun k ↦ pullGlob1 (pairRes φ s') (GlobalTheory.CechDR.pullForm h (u k)))
            (fun k ↦ pullGlob1 (pairRes φ s') (GlobalTheory.CechDR.pullForm h (v k))) t := by
          simp only [e1 u, e1 v]
        _ = qOm (pairRes φ s') 2 t (wsum (OAff s') (fun k ↦ GlobalTheory.CechDR.pullForm h (u k))
            (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) ((pairFst φ).obj t)) := (qOm_wsum _ _ _ _).symm
        _ = _ := qOm_restrict _ _ _ _
    have c3 := pOm_wsum (OAff s') (fun k ↦ GlobalTheory.CechDR.pullForm h (u k))
      (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) w
    rw [map_sub, pOm_dOne, c1, c3, key5, c2, sub_self]

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousConeDescendsEtaleSurjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contCone_of_etale_surjective : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G) (W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W), Etale f → Surjective f → ∀ (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative], P f → (∀ (Z : Scheme.{0}) (π : Z ⟶ V), P π → ContCone R F ((bc (sch.map (π ≫ f ≫ r))).mapCone c)) → ContCone R F ((bc (sch.map r)).mapCone c) := by
  intro R _ F S I _ _ G c W V r f hE hS P _ _ hf hZ
  have hstep : ContCone R F ((bc (cechAug f ≫ sch.map r)).mapCone c) := by
    refine GlobalTheory.T.cohomologyContinuous_base_change_of_levels R F S (cech f) (cechAug f ≫ sch.map r) I G c (fun k => ?_)
    obtain ⟨Z, π, e, hP, he⟩ := GlobalTheory.EtC.cech_level_representable P V W f hf k
    refine ⟨Z, π ≫ f ≫ r, e, ?_, hZ Z π hP⟩
    rw [NatTrans.comp_app, ← Category.assoc, he]
    change yoneda.map (π ≫ f) ≫ yoneda.map r = _
    rw [← yoneda.map_comp, Category.assoc]
  refine (ContCone.iff_of_eqv R F I _ _ ((bc (cechAug f ≫ sch.map r)).mapCone c) ((bc (sch.map r)).mapCone c)
    (Functor.whiskerLeft G (bcMap (cechAug f) (sch.map r))) ((bcMap (cechAug f) (sch.map r)).app c.pt) (fun i => ?_)
    (fun i => GlobalTheory.T.etaleCohomologyEquivalence_baseChange_cechAugmentation R F S W V r f hE hS (G.obj i)) (GlobalTheory.T.etaleCohomologyEquivalence_baseChange_cechAugmentation R F S W V r f hE hS c.pt)).mp hstep
  exact ((bcMap (cechAug f) (sch.map r)).naturality (c.π.app i))

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSumClosedGlobalOneFormsEqZeroIffSumWedge
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem cupSum_eq_zero_iff_wsum_eq_zero (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (hc : Closed1 F = ⊤) (hs : Function.Surjective (toO F)) (n : ℕ)
    (u v : Fin n → Glob1 F) :
    ∑ k, cupHyp F (clAll F hc (u k)) (clAll F hc (v k)) = 0 ↔ wsum F u v = 0 := by
  have hcl : ∀ w : Glob1 F, clAll F hc w = Hyp1.mk F (formZZ F ⟨w, hc ▸ Submodule.mem_top⟩) :=
    fun w ↦ rfl
  have hsum : ∑ k, cupHyp F (clAll F hc (u k)) (clAll F hc (v k)) =
      Hyp2.mk F (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩)
        (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hcl, cupHyp_mk, map_sum]
  have hval : ∀ T, (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩)
        (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)).1.2.2 T = wsum F u v T := by
    intro T
    simp only [Submodule.coe_sum, Prod.snd_sum, Finset.sum_apply, coe_cupZZ, cupTot_η, wsum]
    rfl
  have h1 : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩)
        (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)).1.1 T T' T'' φ ψ = 0 := by
    intro T T' T'' φ ψ
    simp only [Submodule.coe_sum, Prod.fst_sum, Finset.sum_apply, coe_cupZZ, cupTot_apply]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    change mp F ψ 0 * 0 = 0
    simp
  have h2 : ∀ T T' (φ : T ⟶ T'), (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩)
        (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)).1.2.1 T T' φ = 0 := by
    intro T T' φ
    simp only [Submodule.coe_sum, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, coe_cupZZ, cupTot_a]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    change (0 : F.obj T') • _ - (0 : F.obj T') • _ = 0
    simp
  rw [hsum, Hyp2.mk_eq_zero]
  constructor
  · rintro ⟨e, he⟩
    have hz : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), (dTot1 F e).1 T T' T'' φ ψ = 0 := fun T T' T'' φ ψ ↦ by
      rw [he]; exact h1 T T' T'' φ ψ
    have ha : ∀ T T' (φ : T ⟶ T'), e.2 T' = p1 F φ (e.2 T) + D R _ (e.1 T T' φ) := fun T T' φ ↦ by
      have := (congrArg (fun x : Tot2 F ↦ x.2.1 T T' φ) he).trans (h2 T T' φ)
      rw [dTot1_a] at this
      rw [sub_sub, sub_eq_zero] at this
      exact this
    have hη : ∀ T, dOne R _ (e.2 T) = wsum F u v T := fun T ↦ by
      have := congrArg (fun x : Tot2 F ↦ x.2.2 T) he
      rw [dTot1_η] at this
      rw [this, hval]
    have hf : e.1 ∈ Z1 F := by
      rw [commAlgFunctorCocyclesOne_eq_ker]
      funext T T' T'' φ ψ
      exact hz T T' T'' φ ψ
    obtain ⟨c, hcz⟩ := hs (CatCoh.H1.mk F ⟨e.1, hf⟩)
    obtain ⟨cz, rfl⟩ := Hyp1.mk_surjective F c
    rw [toO_mk, CatCoh.H1.mk_eq_mk] at hcz
    obtain ⟨g, hg⟩ := hcz
    have hg' : ∀ T T' (φ : T ⟶ T'), g T' - mp F φ (g T) = cz.1.1 T T' φ - e.1 T T' φ := fun T T' φ ↦
      congrFun (congrFun (congrFun hg T) T') φ
    let θ : A0 F := fun T ↦ e.2 T - (cz.1.2 T - D R _ (g T))
    have hθ : θ ∈ Glob1 F := by
      intro T T' φ
      simp only [θ, map_sub, p1_D]
      have hgT : g T' = mp F φ (g T) + (cz.1.1 T T' φ - e.1 T T' φ) := by rw [← hg' T T' φ]; abel
      rw [ha T T' φ, cechDeRhamTotalCocyclesOne.conn cz φ, hgT]
      simp only [map_add (f := _), map_sub]
      abel
    have hθc : (⟨θ, hθ⟩ : Glob1 F) ∈ Closed1 F := hc ▸ Submodule.mem_top
    funext T
    have hθ0 : dOne R _ (e.2 T - (cz.1.2 T - D R _ (g T))) = 0 := hθc T
    rw [map_sub, map_sub, cechDeRhamTotalCocyclesOne.closed cz T, dOne_D, sub_zero, sub_zero] at hθ0
    rw [← hη T, hθ0]; rfl
  · intro hw
    refine ⟨0, ?_⟩
    rw [map_zero]
    refine Tot2.ext (fun T T' T'' φ ψ ↦ (h1 T T' T'' φ ψ).symm) (fun T T' φ ↦ (h2 T T' φ).symm)
      fun T ↦ ?_
    rw [hval, hw]; rfl

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureSumWedgeWellDefinedAndDeRhamLift
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem curvature_wellDefined_and_lift : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), (Closed1 F = ⊤ → ∀ (x : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F), ObRel F x u v → ObRel F x u' v' → wsum F u v = wsum F u' v') ∧ ∀ (x : GlobalTheory.CatCoh.H1 F) (n : ℕ) (u v : Fin n → Glob1 F), ObRel F x u v → wsum F u v = 0 → ∃ c, toO F c = x := by
  intro R _ C _ F
  refine ⟨fun hcl x n n' u v u' v' ⟨f, ω, hf, hω, hd⟩ ⟨f', ω', hf', hω', hd'⟩ ↦ ?_,
    fun x n u v ⟨f, ω, hf, hω, hd⟩ h0 ↦ ?_⟩
  · obtain ⟨b, hb⟩ := H1.mk_eq_mk.1 (hf.trans hf'.symm)
    let e0 : Glob1 F := ⟨fun T ↦ ω T - ω' T - D R _ (b T), fun T T' φ ↦ by
      have hb' : f.1 T T' φ - f'.1 T T' φ = b T' - mp F φ (b T) :=
        (congrFun (congrFun (congrFun hb T) T') φ).symm
      have h2 : D R _ (b T') = D R _ (f.1 T T' φ) - D R _ (f'.1 T T' φ) + D R _ (mp F φ (b T)) := by
        rw [← map_sub, hb', map_sub]; abel
      show ω T' - ω' T' - D R _ (b T') = p1 F φ (ω T - ω' T - D R _ (b T))
      rw [hω φ, hω' φ, map_sub, map_sub, p1_D, h2]
      abel⟩
    have he0 : e0 ∈ Closed1 F := by rw [hcl]; exact Submodule.mem_top
    funext T
    rw [← hd T, ← hd' T]
    have h := he0 T
    change dOne R _ (ω T - ω' T - D R _ (b T)) = 0 at h
    rw [map_sub, map_sub, dOne_D, sub_zero, sub_eq_zero] at h
    exact h
  · refine ⟨Hyp1.mk F ⟨(f.1, ω), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨f.2, hω, fun T ↦ (hd T).trans (congrFun h0 T)⟩⟩, ?_⟩
    rw [toO_mk]
    exact hf

end GlobalTheory.AbCoh
end

