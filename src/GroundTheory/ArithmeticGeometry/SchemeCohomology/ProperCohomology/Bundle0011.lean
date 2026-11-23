module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0010
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0001
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CohFinite
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesSheaf

@[expose] public section

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalTower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe c236Ext c236Scheme

private noncomputable def H.linearMapV436 {X : Scheme.{c236Scheme}}
    [HasExt.{c236Ext} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{c236Scheme})]
    (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]
    {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) :
    Sheaf.H.{c236Ext} (modulesAb F) n →ₗ[A] Sheaf.H.{c236Ext} (modulesAb G) n where
  toFun := Sheaf.H.map.{c236Ext} (modulesAbMap φ) n
  map_add' := map_add _
  map_smul' a x := by
    change Sheaf.H.map.{c236Ext} (modulesAbMap φ) n (a • x) =
      a • Sheaf.H.map.{c236Ext} (modulesAbMap φ) n x
    rw [H.smul_def, H.smul_def, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
      ← modulesAbMap_comp, ← modulesAbMap_comp, smulHom_comp]

private lemma H.linearMapV436_apply {X : Scheme.{c236Scheme}}
    [HasExt.{c236Ext} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{c236Scheme})]
    (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]
    {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) (x : Sheaf.H.{c236Ext} (modulesAb F) n) :
    H.linearMapV436 A φ n x = Sheaf.H.map.{c236Ext} (modulesAbMap φ) n x := rfl

end

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] (F : X.Modules) (q : ℕ)

abbrev formalα (n : ℕ) : Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) q →ₗ[A]
    Sheaf.H.{u} (modulesAb F) q :=
  H.linearMap A (idealPowι I F (n + 1)) q

def formalK (n : ℕ) : Submodule A (Sheaf.H.{u} (modulesAb F) q) :=
  LinearMap.range (formalα I F q n)

lemma formalK_antitone : Antitone (formalK I F q) := by
  refine antitone_nat_of_succ_le fun n => ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨H.linearMapV436 A (idealPowSucc I F (n + 1)) q x, ?_⟩
  change Sheaf.H.map.{u} (modulesAbMap (idealPowι I F (n + 1))) q
      (Sheaf.H.map.{u} (modulesAbMap (idealPowSucc I F (n + 1))) q x) =
    Sheaf.H.map.{u} (modulesAbMap (idealPowι I F (n + 1 + 1))) q x
  rw [← Sheaf.H.map_comp_apply, ← modulesAbMap_comp, idealPowSucc_ι]

abbrev formalβ (n : ℕ) : Sheaf.H.{u} (modulesAb F) q →ₗ[A]
    Sheaf.H.{u} (modulesAb (quotPow I F n)) q :=
  H.linearMap A (quotPowπ I F n) q

abbrev formalτE (n : ℕ) : Sheaf.H.{u} (modulesAb (quotPow I F (n + 1))) q →ₗ[A]
    Sheaf.H.{u} (modulesAb (quotPow I F n)) q :=
  H.linearMap A (quotPowMap I F n) q

lemma shortExact_abSC_quotPow (n : ℕ) : (abSC (quotPowSC I F n)).ShortExact :=
  shortExact_abSC (quotPowSC_shortExact I F n)

lemma ker_formalβ (n : ℕ) : LinearMap.ker (formalβ I F q n) = formalK I F q n := by
  ext h
  constructor
  · intro hh
    exact H.exact₂ (shortExact_abSC_quotPow I F n) h hh
  · rintro ⟨x, rfl⟩
    exact H.map_g_map_f (S := abSC (quotPowSC I F n)) x

abbrev formalδ (n : ℕ) : Sheaf.H.{u} (modulesAb (quotPow I F n)) q →ₗ[A]
    Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) (q + 1) :=
  H.δLinear A (shortExact_abSC_quotPow I F n) q

def formalQ (n : ℕ) : Submodule A (Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) (q + 1)) :=
  LinearMap.range (formalδ I F q n)

def formalι (n : ℕ) : (Sheaf.H.{u} (modulesAb F) q ⧸ formalK I F q n) →ₗ[A]
    Sheaf.H.{u} (modulesAb (quotPow I F n)) q :=
  (formalK I F q n).liftQ (formalβ I F q n) (ker_formalβ I F q n).ge

lemma formalι_injective (n : ℕ) : Function.Injective (formalι I F q n) := by
  rw [← LinearMap.ker_eq_bot, formalι, Submodule.ker_liftQ, ker_formalβ, Submodule.mkQ_map_self]

def formalπ (n : ℕ) : Sheaf.H.{u} (modulesAb (quotPow I F n)) q →ₗ[A] formalQ I F q n :=
  (formalδ I F q n).rangeRestrict

lemma range_formalι (n : ℕ) :
    LinearMap.range (formalι I F q n) = LinearMap.ker (formalπ I F q n) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    apply Subtype.ext
    exact H.δ_map_g (shortExact_abSC_quotPow I F n) rfl h
  · intro hy
    have hy' : formalδ I F q n y = 0 := congrArg Subtype.val hy
    obtain ⟨h, rfl⟩ := H.exact₃ (shortExact_abSC_quotPow I F n) rfl y hy'
    exact ⟨Submodule.Quotient.mk h, rfl⟩

def abSCHom {S S' : ShortComplex X.Modules} (φ : S ⟶ S') : abSC S ⟶ abSC S' where
  τ₁ := modulesAbMap φ.τ₁
  τ₂ := modulesAbMap φ.τ₂
  τ₃ := modulesAbMap φ.τ₃
  comm₁₂ := by
    change modulesAbMap φ.τ₁ ≫ modulesAbMap S'.f = modulesAbMap S.f ≫ modulesAbMap φ.τ₂
    rw [← modulesAbMap_comp, ← modulesAbMap_comp, φ.comm₁₂]
  comm₂₃ := by
    change modulesAbMap φ.τ₂ ≫ modulesAbMap S'.g = modulesAbMap S.g ≫ modulesAbMap φ.τ₃
    rw [← modulesAbMap_comp, ← modulesAbMap_comp, φ.comm₂₃]

def quotPowSCMap (n : ℕ) : quotPowSC I F (n + 1) ⟶ quotPowSC I F n where
  τ₁ := idealPowSucc I F (n + 1)
  τ₂ := 𝟙 F
  τ₃ := quotPowMap I F n
  comm₁₂ := by
    change idealPowSucc I F (n + 1) ≫ idealPowι I F (n + 1) = idealPowι I F (n + 2) ≫ 𝟙 F
    rw [idealPowSucc_ι, Category.comp_id]
  comm₂₃ := by
    change 𝟙 F ≫ quotPowπ I F n = quotPowπ I F (n + 1) ≫ quotPowMap I F n
    rw [quotPowπ_map, Category.id_comp]

lemma formalδ_naturality (n : ℕ) (x : Sheaf.H.{u} (modulesAb (quotPow I F (n + 1))) q) :
    formalδ I F q n (formalτE I F q n x) =
      H.linearMap A (idealPowSucc I F (n + 1)) (q + 1) (formalδ I F q (n + 1) x) := by
  simp only [formalδ, formalτE, H.δLinear_apply, H.linearMap_apply]
  exact H.δ_naturality (shortExact_abSC_quotPow I F (n + 1)) (shortExact_abSC_quotPow I F n)
    (abSCHom (quotPowSCMap I F n)) q (q + 1) rfl x

end

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesNatural
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} [X.Over (Spec (.of A))]
  {F : X.Modules} {V V' : X.Opens} (hle : V' ≤ V)

lemma algV_res (a : A) : resO hle (algV X V a) = algV X V' a := by
  have := Scheme.Hom.appLE_map (X ↘ Spec (.of A)) (U := ⊤) (le_top : V ≤ _) (homOfLE hle).op
  exact congrArg (fun f : Γ(Spec (.of A), ⊤) ⟶ Γ(X, V') => f.hom ((Scheme.ΓSpecIso (.of A)).inv a))
    this


variable (I) in
abbrev resS : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) →+* Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V') :=
  resO (Scheme.Hom.preimage_mono _ hle)

lemma resS_reesInr (r : reesAlgebra I) : resS I hle (reesInr I V r) = reesInr I V' r := by
  have := Scheme.Hom.appLE_map (reesSnd I X) (U := ⊤) (le_top : reesPr I X ⁻¹ᵁ V ≤ _)
    (homOfLE (Scheme.Hom.preimage_mono _ hle)).op
  exact congrArg (fun f : Γ(Spec (.of (reesAlgebra I)), ⊤) ⟶ Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V') =>
    f.hom ((Scheme.ΓSpecIso (.of (reesAlgebra I))).inv r)) this

lemma resS_prApp (c : Γ(X, V)) :
    resS I hle ((reesPr I X).app V c) = (reesPr I X).app V' (resO hle c) := by
  have := (reesPr I X).naturality (homOfLE hle).op
  exact (congrArg (fun f : Γ(X, V) ⟶ Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V') => f.hom c) this).symm

lemma reesRingHom_res (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (s : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)) :
    reesRingHom hV' (resS I hle s) = (reesRingHom hV s).map (resO hle) := by
  have h := (isPushout_rees (I := I) hV).hom_ext
    (k := CommRingCat.ofHom ((reesRingHom hV').comp (resS I hle)))
    (l := CommRingCat.ofHom ((Polynomial.mapRingHom (resO hle)).comp (reesRingHom hV)))
    (by
      refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
      change reesRingHom hV' (resS I hle ((reesPr I X).app V c)) =
        (reesRingHom hV ((reesPr I X).app V c)).map (resO hle)
      rw [resS_prApp, reesRingHom_inl, reesRingHom_inl, Polynomial.map_C])
    (by
      refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
      change reesRingHom hV' (resS I hle (reesInr I V r)) =
        (reesRingHom hV (reesInr I V r)).map (resO hle)
      rw [resS_reesInr, reesRingHom_inr, reesRingHom_inr, Polynomial.map_map]
      congr 1
      exact RingHom.ext fun a => (algV_res hle a).symm)
  exact congrArg (fun f : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) ⟶
    CommRingCat.of (Polynomial Γ(X, V')) => f.hom s) h


variable (F) in
def resFA : Γ(F, V) →ₗ[A] Γ(F, V') where
  toFun := resF F hle
  map_add' := map_add _
  map_smul' a m := by
    change resF F hle (algV X V a • m) = algV X V' a • resF F hle m
    rw [resF_smul, algV_res]

lemma resFA_apply (m : Γ(F, V)) : resFA (A := A) F hle m = resF F hle m := rfl

lemma app_resF {M N : X.Modules} (φ : M ⟶ N) {U U' : X.Opens} (h : U' ≤ U) (y : Γ(M, U)) :
    φ.app U' (resF M h y) = resF N h (φ.app U y) := by
  have := φ.mapPresheaf.naturality (homOfLE h).op
  exact congrArg (fun f => f.hom y) this

variable (hF : IsCoherent F) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')

lemma theta₁_res_coeff
    (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) (n : ℕ) :
    (theta₁ hF hV' (resF _ (Scheme.Hom.preimage_mono _ hle) y)).coeff n =
      resF F hle ((theta₁ hF hV y).coeff n) := by
  have hy : y ∈ Submodule.span Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)
      (Set.range (unitPr I F V)) := by
    rw [(isBaseChangeAt_reesPr (I := I) hF hV).span_range]
    trivial
  induction hy using Submodule.span_induction generalizing n with
  | mem z hz =>
    obtain ⟨m, rfl⟩ := hz
    have hres : resF _ (Scheme.Hom.preimage_mono _ hle) (unitPr I F V m) =
        unitPr I F V' (resF F hle m) :=
      (Etale.pullbackUnitApp_res (reesPr I X) F (homOfLE hle) m).symm
    rw [hres, theta₁_unitPr, theta₁_unitPr, PolynomialModule.coeff_single,
      PolynomialModule.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs
    · rfl
    · exact (map_zero _).symm
  | zero => simp
  | add z z' _ _ hz hz' =>
    simp only [map_add (f := _), PolynomialModule.coeff_add, Finsupp.add_apply, hz, hz']
  | smul s z _ hz =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Scheme.Modules.map_smul, theta₁_smul, theta₁_smul, reesRingHom_res hle hV hV',
      PolynomialModule.smul_apply, PolynomialModule.smul_apply, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Polynomial.coeff_map, hz, resF_smul]

theorem reesSectionsEquiv_res (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    (reesSectionsEquiv I hF hV' (resF _ (Scheme.Hom.preimage_mono _ hle) x) :
      PolynomialModule A Γ(F, V')) =
      PolynomialModule.map A (resFA F hle) (reesSectionsEquiv I hF hV x : PolynomialModule A Γ(F, V)) := by
  obtain ⟨y, rfl⟩ := surjective_reesSheafπ_app hF (hV.preimage (reesPr I X)) x
  rw [← app_resF, reesSectionsEquiv_apply, reesSectionsEquiv_apply, reesSectionsMap_π,
    reesSectionsMap_π]
  apply PolynomialModule.coeff_injective
  ext n
  exact theta₁_res_coeff hle hF hV hV' y n

end

section Base

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Scheme.{u}) [X.Over (Spec (.of A))]

variable {I X}

end Base

end GroundTheory.Arith.SchemeCoh
end

