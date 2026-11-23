module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorComponentsTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2473
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2421

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldLinearIndependentClosedFibreGenericP
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.ResInj

theorem cst_eq_fnOf {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) (V : X.Opens)
    (hV : genericPoint X ∈ V) (r : R) : GlobalTheory.Desc.cst p r = fnOf V hV (GlobalTheory.AbLaw.cst p V r) := by
  simp only [GlobalTheory.Desc.cst, GlobalTheory.AbLaw.cst, fnOf, RingHom.comp_apply, Scheme.Hom.appLE, CommRingCat.hom_comp]
  rw [TopCat.Presheaf.germ_res_apply]

theorem zeroAt_fnOf_iff {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} {x : X} (hx : x ∈ U) (b : Γ(X, U)) :
    ZeroAt x (fnOf U (gen_mem hx) b) ↔ (X.presheaf.germ U x hx).hom b ∈ maximalIdeal (X.presheaf.stalk x) := by
  refine ⟨fun ⟨a, ha, e⟩ => ?_, fun h => ⟨_, h, algebraMap_germ hx b⟩⟩
  rwa [IsFractionRing.injective (X.presheaf.stalk x) X.functionField (e.trans (algebraMap_germ hx b).symm)] at ha

theorem cst_zeroAt (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp R) (x : X)
    (hx : p x = closedPoint R) (r : R) (hr : r ∈ maximalIdeal R) : ZeroAt x (GlobalTheory.Desc.cst p r) := by
  have hreg : RegAt x (GlobalTheory.Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _
  refine zeroAt_iff.2 ⟨hreg, fun hu => ?_⟩
  have h1 := (unitAt_fnOf_iff (U := ⊤) trivial trivial _).1 hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact h1
  have h3 : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h3 hr

end GlobalTheory.Desc.ResInj

theorem GlobalTheory.Desc.ResInj.exists_affine_fnOf : ∀ (X : Scheme.{0}) [IsIntegral X] (x : X) (n : ℕ) (u : Fin n → X.functionField), (∀ i, GlobalTheory.Cartier.RegAt x (u i)) → ∃ (U : X.Opens) (hx : x ∈ U), IsAffineOpen U ∧ ∃ s : Fin n → Γ(X, U), ∀ i, GlobalTheory.Cartier.fnOf U (GlobalTheory.Cartier.gen_mem hx) (s i) = u i := by
  intro X _ x n u hu
  choose W hxW s hs using fun i => (hu i).exists_fnOf
  let W₀ : X.Opens := ⟨⋂ i, (W i : Set X), isOpen_iInter_of_finite fun i => (W i).isOpen⟩
  have hx₀ : x ∈ W₀ := Set.mem_iInter.2 hxW
  obtain ⟨U, hU, hxU, hUW⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)) hx₀
  have hle : ∀ i, U ≤ W i := fun i z hz => Set.mem_iInter.1 (hUW hz) i
  refine ⟨U, hxU, hU, fun i => resG X (hle i) (s i), fun i => ?_⟩
  rw [fnOf_resG, hs]

theorem GlobalTheory.Desc.ResInj.mem_map_of_germ_mem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (G : Over (Sp R)) [IsIntegral G.left], Smooth G.hom → GeometricallyConnected G.hom → ∀ y : G.left, G.hom y = closedPoint R → ringKrullDim (G.left.presheaf.stalk y) = 1 → ∀ (U : G.left.Opens) (hy : y ∈ U), IsAffineOpen U → ∀ b : Γ(G.left, U), (G.left.presheaf.germ U y hy).hom b ∈ maximalIdeal (G.left.presheaf.stalk y) → b ∈ (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U) := by
  intro R _ _ _ G _ hsm hgc y hy hdim U hyU hU b hb
  haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
  letI : Algebra R Γ(G.left, U) := (GlobalTheory.AbLaw.cst G.hom U).toAlgebra
  haveI : Module.Flat R Γ(G.left, U) := GlobalTheory.AbLaw.flat_cst G.hom hU
  let p := hU.primeIdealOf ⟨y, hyU⟩
  letI : Algebra Γ(G.left, U) (G.left.presheaf.stalk y) := G.left.presheaf.algebra_section_stalk ⟨y, hyU⟩
  haveI hloc := hU.isLocalization_stalk ⟨y, hyU⟩
  have hmem : ∀ c : Γ(G.left, U), (G.left.presheaf.germ U y hyU).hom c ∈ maximalIdeal (G.left.presheaf.stalk y) ↔ c ∈ p.asIdeal := by
    intro c
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff (G.left.presheaf.stalk y) p.asIdeal c
  have hle : (maximalIdeal R).map (algebraMap R Γ(G.left, U)) ≤ p.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro t ht
    rw [Ideal.mem_comap, ← hmem, ← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hyU]
    have := GlobalTheory.Desc.ResInj.cst_zeroAt R G.left G.hom y hy t ht
    rwa [GlobalTheory.Desc.ResInj.cst_eq_fnOf G.hom U (gen_mem hyU)] at this
  have hd : ringKrullDim (Localization.AtPrime p.asIdeal) = 1 := by
    rw [← hdim]
    exact ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal) (G.left.presheaf.stalk y)).toRingEquiv
  have e := _root_.GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one R Γ(G.left, U) p.asIdeal hle hd (_root_.GlobalTheory.isDomain_quot_maximalIdeal_of_smooth R G hsm hgc U hU y hyU hy)
  have : b ∈ p.asIdeal := (hmem b).1 hb
  rw [e] at this
  exact this

theorem GlobalTheory.Desc.ResInj.residue_linearIndependent : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → ∀ (n : ℕ) (u : Fin n → H.left.functionField), (∀ i, GlobalTheory.Cartier.RegAt y (u i)) → (∀ c : Fin n → T, GlobalTheory.Cartier.ZeroAt y (∑ i, GlobalTheory.Desc.cst H.hom (c i) * u i) → ∀ i, c i ∈ maximalIdeal T) → ∀ d : Fin n → D, GlobalTheory.Cartier.ZeroAt y' (∑ i, GlobalTheory.Desc.cst H'.hom (d i) * θ (u i)) → ∀ i, d i ∈ maximalIdeal D := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hH hpb hpff y y' hy hy' hdy hdy' n u hu hind d hz
  have hπy : π y' = y := _root_.GlobalTheory.Desc.GaussBC.apply_eq_of_closedFibre_dim_one T D a ha hm H H' π θ hH hpb hpff y y' hy hy' hdy hdy'
  obtain ⟨U, hyU, hUa, x, hx⟩ := GlobalTheory.Desc.ResInj.exists_affine_fnOf H.left y n u hu
  set V : H'.left.Opens := π ⁻¹ᵁ U with hVdef
  have hy'V : y' ∈ V := by show π y' ∈ U; rw [hπy]; exact hyU
  have hgU : genericPoint H.left ∈ U := gen_mem hyU
  have hgV : genericPoint H'.left ∈ V := gen_mem hy'V
  letI : Algebra T D := a.toAlgebra
  letI : Algebra T Γ(H.left, U) := (GlobalTheory.AbLaw.cst H.hom U).toAlgebra
  letI : Algebra D Γ(H'.left, V) := (GlobalTheory.AbLaw.cst H'.hom V).toAlgebra
  letI : Algebra Γ(H.left, U) Γ(H'.left, V) := (π.app U).hom.toAlgebra
  letI : Algebra T Γ(H'.left, V) := ((GlobalTheory.AbLaw.cst H'.hom V).comp a).toAlgebra
  haveI : IsScalarTower T D Γ(H'.left, V) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower T Γ(H.left, U) Γ(H'.left, V) := .of_algebraMap_eq fun r => by
    have e := GlobalTheory.AbLaw.appLE_cst hpb.w (V := U) (V' := V) le_rfl r
    rw [Scheme.Hom.appLE_eq_app] at e
    exact e.symm
  haveI : Algebra.IsPushout T D Γ(H.left, U) Γ(H'.left, V) := by
    have po := GlobalTheory.AbLaw.isPushout_cst hpb hUa (V' := V) rfl
    rw [Scheme.Hom.appLE_eq_app] at po
    exact CommRingCat.isPushout_iff_isPushout.mp po
  have hsm : Smooth H'.hom := MorphismProperty.of_isPullback hpb hH.smooth
  have hgc : GeometricallyConnected H'.hom := MorphismProperty.of_isPullback hpb hH.geomConnected

  have hindA : ∀ c : Fin n → T, ∑ i, c i • x i ∈ (maximalIdeal T).map (algebraMap T Γ(H.left, U)) →
      ∀ i, c i ∈ maximalIdeal T := by
    intro c hc
    apply hind c
    have hle : (maximalIdeal T).map (algebraMap T Γ(H.left, U)) ≤
        Ideal.comap (H.left.presheaf.germ U y hyU).hom (maximalIdeal _) := by
      rw [Ideal.map_le_iff_le_comap]
      intro t ht
      rw [Ideal.mem_comap, Ideal.mem_comap, ← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hyU]
      have := GlobalTheory.Desc.ResInj.cst_zeroAt T H.left H.hom y hy t ht
      rwa [GlobalTheory.Desc.ResInj.cst_eq_fnOf H.hom U hgU] at this
    have h1 := hle hc
    rw [Ideal.mem_comap, ← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hyU] at h1
    convert h1 using 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Algebra.smul_def, map_mul, hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GlobalTheory.Desc.ResInj.cst_eq_fnOf H.hom U hgU]
    rfl

  have hd := _root_.GlobalTheory.pushout_residue_linearIndependent T D Γ(H.left, U) Γ(H'.left, V) hm n x hindA d
  apply hd
  apply GlobalTheory.Desc.ResInj.mem_map_of_germ_mem D H' hsm hgc y' hy' hdy' V hy'V (GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback hpb hUa)
  rw [← GlobalTheory.Desc.ResInj.zeroAt_fnOf_iff hy'V]
  convert hz using 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Algebra.smul_def, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hx i, ← GlobalTheory.Desc.fnOf_app_of_pff H.left H'.left π θ hpff U hgU hgV, GlobalTheory.Desc.ResInj.cst_eq_fnOf H'.hom V hgV]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedGaloisLinearisationCarriesRigidificati
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RigCubCarry

theorem pmaps_of_pullGen {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {a : LB.Gen (LB.LinComb L' φ' ε)}
    {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y} (hc : ∀ k, φ' k ≫ F = h ≫ φ k)
    (H : PMaps w φ' (fun k => h ≫ φ k) ε a (LB.pullGen L φ ε t h) (𝟙 Y')) : PMaps w φ' φ ε a t h := by
  intro Z r z p q hp hq
  have e := H Z r z p q hp hq
  rw [Category.comp_id] at e
  have hm' : ∀ k, (h ≫ φ k) (r z) ∈ L.U (p k) := fun k => by
    rw [← hc k]; exact hp k
  have hm : r z ∈ LB.wchart L (fun k => h ≫ φ k) p := Set.mem_iInter.2 hm'
  have hm2 : h (r z) ∈ LB.wchart L φ p := Set.mem_iInter.2 hm'
  refine Eq.trans ?_ e
  exact ((gm_res r z _ hm _).trans (gm_pull r h z _ hm2 _)).symm


open RigidIsoCube in
theorem surjective_appTop_tripleProduct_uniformisedGroup (R : Type) [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) :
    Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom := by
  have hG : GlobalFnsSt := GlobalTheory.globalFns_holds
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  exact surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _)
      (surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _) s₁)

theorem cubeMap_tripleProduct_unit_eq {S : Scheme.{0}} {G' : Over S} [GrpObj G'] [IsCommMonObj G'] (m : CubeMap G' G') :
    (lift (1 : 𝟙_ (Over S) ⟶ G') (lift 1 1)).left ≫ m.F3 =
      (lift (1 : Over.mk (m.e ≫ (𝟙_ (Over S)).hom) ⟶ G') (lift 1 1)).left := by
  have ht : (toUnit (Over.mk (m.e ≫ (𝟙_ (Over S)).hom))).left = m.e := by
    have w := Over.w (toUnit (Over.mk (m.e ≫ (𝟙_ (Over S)).hom)))
    simpa using w
  apply hom_ext_triple
  intro i
  rw [Category.assoc, cubeMap_comp_proj_three m i, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
  have h1 : ∀ {T : Over S}, lift (1 : T ⟶ G') (lift 1 1) ≫ x3 G' i = 1 := by
    intro T; fin_cases i <;> simp [x3]
  rw [h1, h1, Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, ht]
  have e₁ : (toUnit (𝟙_ (Over S))).left = 𝟙 _ := by simp
  rw [e₁, Category.id_comp]
  exact m.e_comm

end GlobalTheory.Mum.RigCubCarry

namespace GlobalTheory.Mum


set_option maxHeartbeats 2000000 in
open RigidIsoCube RigCubCarry in
theorem rigidified_galois_lin_carries_rig_and_cube : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PMaps (Classical.choose hP.lg) (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) U'.LG.rig U'.LG.rig (specOf (Gal.hom σ)) ∧ ∀ hc : IsGrpPullback G' G' (specOf (Gal.hom σ)) (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))), PMaps (Classical.choose hP.lg) (thφ G' (x3 G')) (thφ G' (x3 G')) thε U'.cubG.t U'.cubG.t (cubeMapOf hc).F3 := by
  intro R _ _ _ hB R' _ _ _ ρ hF hGal D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact σ h bc hbc hP
  obtain ⟨hw, he, hrig, -⟩ := Classical.choose_spec hP.lg
  refine ⟨(maps_iff _ _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig (specOf (Gal.hom σ)) _
    (rigPull_le _ _ he U'.LG.L) (fun _ => rfl)).1 hrig, fun hc => ?_⟩
  have sj := surjective_appTop_tripleProduct_uniformisedGroup R' G' U'.toUnifPre
  let e : 𝟙_ (Over (Sp R')) ⟶ G3 G' := lift 1 (lift 1 1)
  have he3 : e.left ≫ (snd G' (G' ⊗ G')).left ≫ (snd G' G').left ≫ G'.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have pg := (isGen_iff _).1 hw
  have hψ : ∀ k : thK.{0}, thφ G' (x3 G') k ≫ (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) =
      (cubeMapOf hc).F3 ≫ thφ G' (x3 G') k := fun k => (cubeMapOf hc).psum_comm k.down
  have eF := cubeMap_tripleProduct_unit_eq (cubeMapOf hc)
  refine pmaps_of_pullGen hψ (pmaps_of_section pg U'.LG.isLB U'.LG.isLB U'.cubG.t U'.cubG.isGen
    (LB.pullGen _ _ _ U'.cubG.t (cubeMapOf hc).F3) (DVR.pullGen_isGen _ _ _ _ U'.cubG.isGen _) hψ _ e.left he3 sj
    fun y J J' hJ hJ' => ?_)
  refine ((val_pull hJ _ _ _).trans (congrArg (fun r => val U'.cubG.t r y J) eF)).trans ?_
  have face {T : Over (Sp R')} {z : T.left} {I : (T.left ⟶ G'.left) → U'.LG.L.ι}
      (hI : Good U'.LG.L z I) (x y : T ⟶ G') :
      val U'.cubG.t (lift 1 (lift x y)).left z I = 1 := by
    have hv := val_corr hI (U'.cubG.face 0) (lift x y).left
    rw [val_one] at hv
    refine (Eq.trans ?_ (val_pull hI _ _ _).symm).trans hv
    congr 1
    rw [← Over.comp_left]
    simp [faceMap, x2, pzero, Hom.one_def]
  have f1 := face (T := Over.mk ((cubeMapOf hc).e ≫ (𝟙_ (Over (Sp R'))).hom)) hJ 1 1
  have p := prod_cub (1 : 𝟙_ (Over (Sp R')) ⟶ G') 1 1
    (fun q => gw (Classical.choose hP.lg) q y (J (q ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)))) (J' q))
  rw [_root_.mul_one, _root_.mul_one] at p
  refine f1.trans (Eq.trans ?_ (congrArg₂ (· * ·) p (face hJ' 1 1)).symm)
  simp

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedValueAtOriginPullbackDegeneration
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.OrigValPull

theorem gs_comp {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)) :
    gs (f ≫ g) z U a = (f.stalkMap z).hom (gs g (f z) U a) := by
  rw [← gs_pull f g z U h, gs_eq f z (g ⁻¹ᵁ U) h, gs_eq g (f z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f (g ⁻¹ᵁ U) z h _).symm

theorem gm_comp {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)ˣ) :
    (gm (f ≫ g) z U a).val = (f.stalkMap z).hom (gm g (f z) U a).val := by
  rw [← gs_unit (f ≫ g) z U h, ← gs_unit g (f z) U h, gs_comp f g z U h]

theorem stalkMap_stalkOf {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (z : Sp R') (v : R) :
    ((spMap φ).stalkMap z).hom (stalkOf (spMap φ z) v) = stalkOf z (φ v) := by
  have h := congrArg (fun q => q.hom v) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  refine (Scheme.Hom.germ_stalkMap_apply (spMap φ) ⊤ z trivial _).trans ?_
  exact congrArg ((Sp R').presheaf.germ ⊤ z trivial).hom h.symm

theorem unit_fam {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (α : D.X) (κ : Fin 4) :
    unitW D.P.A ≫ D.famφB α κ = ![unitW D.P.A, (D.c α).left, (D.c α).left, unitW D.P.A] κ := by
  have u : η[D.P.A] ≫ toUnit D.P.A = 𝟙 _ := Subsingleton.elim _ _
  fin_cases κ
  · exact Category.comp_id _
  · show (η[D.P.A] ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left = (D.c α).left
    congr 1
    show η[D.P.A] ≫ (lift (𝟙 D.P.A) (toUnit _ ≫ D.c α) ≫ μ[D.P.A]) = _
    rw [← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, u, Category.id_comp]
    have := MonObj.lift_comp_one_left (𝟙 (𝟙_ (Over (Sp R)))) (D.c α)
    simpa using this
  · show (η[D.P.A] ≫ toUnit _ ≫ D.c α).left = (D.c α).left
    rw [← Category.assoc, u, Category.id_comp]
  · show (η[D.P.A] ≫ toUnit _ ≫ η[D.P.A]).left = η[D.P.A].left
    rw [← Category.assoc, u, Category.id_comp]

theorem origVal_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (k : ℕ) (x : D'.X) (b : D.SecB k (hD.xe x)) (b' : D'.SecB k x) (v : R), PullB hD x b b' → OrigVal D b v → OrigVal D' b' (φ v) := by
  intro R R' _ _ _ _ φ D D' hD k x b b' v hP hO z J' hJ'
  choose J hJ using fun χ : Sp R ⟶ D.P.A.left => exists_chart D.P.isLB (χ (spMap φ z))
  have hJ : Good D.P.L (spMap φ z) J := hJ
  have he : unitW D'.P.A ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = spMap φ ≫ unitW D.P.A := hD.he
  have hc : ∀ κ, (unitW D'.P.A ≫ D'.famφB x κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
      spMap φ ≫ unitW D.P.A ≫ D.famφB (hD.xe x) κ := fun κ => by
    rw [unit_fam, unit_fam]
    fin_cases κ
    exacts [he, hD.c_pr x, hD.c_pr x, he]
  have h₁ := hP (Sp R') (unitW D'.P.A) z (fun κ => J (unitW D.P.A ≫ D.famφB (hD.xe x) κ))
    (fun κ => J' (unitW D'.P.A ≫ D'.famφB x κ))
    (fun κ => (congrArg (fun q : Sp R' ⟶ D.P.A.left => q z ∈ D.P.L.U (J (unitW D.P.A ≫ D.famφB (hD.xe x) κ))) (hc κ)).mpr
      (hJ _)) (fun κ => hJ' _)
  have hprod : (∏ κ, gw hD.w (unitW D'.P.A ≫ D'.famφB x κ) z (J (unitW D.P.A ≫ D.famφB (hD.xe x) κ))
      (J' (unitW D'.P.A ≫ D'.famφB x κ)) ^ (DegPre.famε k) κ) =
      gw hD.w (unitW D'.P.A) z (J (unitW D.P.A)) (J' (unitW D'.P.A)) ^ k := by
    simp only [unit_fam, Fin.prod_univ_four, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [_root_.mul_assoc (_ ^ _), ← zpow_add, add_neg_cancel, zpow_zero, _root_.mul_one, ← zpow_add, sub_add_cancel,
      zpow_natCast]
  have h₂ := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
    (rigPull_le _ _ hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig (Sp R') (idW R') z
    (fun _ => J (idW R ≫ eSec D.P.A)) (fun _ => J' (idW R' ≫ eSec D'.P.A))
    (fun _ => (congrArg (fun q : Sp R' ⟶ D.P.A.left => q z ∈ D.P.L.U (J (idW R ≫ eSec D.P.A))) he).mpr
      (hJ _)) (fun _ => hJ' _)
  have h₃ : ((spMap φ).stalkMap z).hom (val D.rig (idW R) (spMap φ z) J).val =
      (gw hD.w (unitW D'.P.A) z (J (unitW D.P.A)) (J' (unitW D'.P.A))).val * (val D'.rig (idW R') z J').val := by
    have i : idW R ≫ eSec D.P.A = unitW D.P.A := Category.id_comp _
    have i' : idW R' ≫ eSec D'.P.A = unitW D'.P.A := Category.id_comp _
    have c : spMap φ ≫ idW R = idW R' ≫ specOf φ := (Category.comp_id _).trans (Category.id_comp _).symm
    refine (gm_comp (spMap φ) (idW R) z _ (hJ.mem (fun _ : PUnit => eSec D.P.A) (idW R)) _).symm.trans ?_
    rw [c, ← Units.val_mul]
    refine congrArg Units.val (h₂.trans (congrArg₂ (· * ·) ?_ rfl))
    rw [Fintype.prod_unique, zpow_one, i, i']
  have h₄ := congrArg ((spMap φ).stalkMap z).hom (hO (spMap φ z) J hJ)
  rw [map_mul, map_pow, stalkMap_stalkOf, h₃] at h₄
  have h₅ := (gs_comp (spMap φ) (unitW D.P.A) z _ (hJ.mem (D.famφB (hD.xe x)) (unitW D.P.A)) _).trans h₄
  rw [he, hprod] at h₁
  have h₆ := h₁.symm.trans h₅
  rw [mul_pow, _root_.mul_left_comm, ← Units.val_pow_eq_pow_val] at h₆
  exact (Units.mul_right_inj _).1 h₆

end GlobalTheory.Mum.OrigValPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfUnityFractionFieldMemberEqZetaPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep

theorem eq_yK_zeta_pow_of_pow_eq_one : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ u : FractionRing V, u ^ ((X₁.S.r * X₁.S.N) ^ 2) = 1 → ∃ e : ℕ, u = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 u hu
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI : CharZero (FractionRing V) := IsFractionRing.charZero V
  set k := (X₁.S.r * X₁.S.N) ^ 2 with hk
  have hkpos : 0 < k := by
    have h1 := X₁.S.r_pos; have h2 := X₁.S.N_ge
    positivity
  have hinj : Function.Injective (algebraMap X₁.o₁ X₁.S.R) := by
    intro a b hab
    apply X₁.ar.inj
    have := congrArg (fun x : X₁.S.R => (x : X₁.Ω₁)) hab
    simpa using this
  have hR : IsPrimitiveRoot (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) k := X₁.S.prim.map_of_injective hinj
  have hroot : (Polynomial.cyclotomic k (FractionRing V)).IsRoot (𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ)) := by
    have h := (hR.isRoot_cyclotomic hkpos).map (f := 𝔪.yK)
    rwa [Polynomial.map_cyclotomic] at h
  haveI : NeZero (k : FractionRing V) := ⟨by exact_mod_cast hkpos.ne'⟩
  have hK : IsPrimitiveRoot (𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ)) k :=
    (Polynomial.isRoot_cyclotomic_iff).1 hroot
  obtain ⟨e, -, he⟩ := hK.eq_pow_of_pow_eq_one hu
  exact ⟨e, by rw [map_pow, map_pow, he]⟩

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorComponentsTorusExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiGenerator_components_torusExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (x : 𝓞 E) (ρ'' : N'.A → N'.A → F), (letI := H.starRing; GlobalTheory.Mum.TensRos.RosVT T ν ν' (o.onB.act (star x)) (o.onB.act x) ρ'') → ∀ (χ : N'.X) (b : N'.A) (gs : Fin r → N.Gt), (∀ j, GlobalTheory.Mum.TensTor.cmp T ν ν' b j = (gs j).b) → (letI := H.starRing; ρ'' (N'.c χ) b * GlobalTheory.Mum.TensRos.PV W (GlobalTheory.Mum.TensTor.chi T ν ν') (ν'.eX.symm (star x • ν'.eX χ)) gs = GlobalTheory.Mum.TensRos.PV W (GlobalTheory.Mum.TensTor.chi T ν ν') χ (fun i => ∏ j, gs j ^ ρ x i j)) := by
  first | exact @GlobalTheory.Mum.TensRos.rosVT_components | exact GlobalTheory.Mum.TensRos.rosVT_components | (intros; apply GlobalTheory.Mum.TensRos.rosVT_components <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SFamCharZeroAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegelTor

theorem sFam_charZero_affineOpen : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (U : F.X.affineOpens),
    Nontrivial Γ(F.X, U) → CharZero Γ(F.X, U) := by
  intro g n F U hU
  have hW : IsAffineOpen (U : F.X.Opens) := U.2
  have : SmoothOfRelativeDimension (g * (g + 1) / 2) F.s := F.smooth
  have : Smooth F.s := by first | exact SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s | exact F.smooth.smooth | infer_instance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hW.fromSpec ≫ F.s)
  have h₁ : φ.hom.Flat := by rw [← Flat.SpecMap_iff, hφ]; infer_instance
  letI : Algebra (cycAway n) Γ(F.X, U) := φ.hom.toAlgebra
  have : Module.Flat (cycAway n) Γ(F.X, U) := h₁
  refine charZero_of_inj_zero fun k hk => by_contra fun h0 => ?_
  have hk' : ((k : cycAway n) : ℂ) ≠ 0 := by simpa using h0
  have hne : (k : cycAway n) ≠ 0 := fun h => hk' (by rw [h]; rfl)
  have := (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(F.X, U)) (r := (k : cycAway n))
    (mem_nonZeroDivisors_of_ne_zero hne)).right_eq_zero_of_smul (x := 1) (by rw [Algebra.smul_def, _root_.mul_one, map_natCast]; exact hk)
  exact one_ne_zero this

end GlobalTheory.SiegelTor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValuesIdentityDescendsToFibreProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionValues_identity_descends_to_fibreProduct : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (w : W), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s p' z J := by
  first | exact @GlobalTheory.Mum.ValDescent.desc | exact GlobalTheory.Mum.ValDescent.desc | (intros; apply GlobalTheory.Mum.ValDescent.desc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpOverOfPolarizedPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc

theorem sharpOver_baseChange : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left), SharpOver F W P u → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → SharpOver F W P' (f ≫ u) := by
  intro g n F W T T' P P' u f φ hS hφ hL
  obtain ⟨c, hc, pr, hpr, huniv, hbun⟩ := hS
  obtain ⟨c', hc', pr', hpr', huniv', hbun', -⟩ :=
    sharpOver_pullback_end g n _ _ F W T T' P P' u f φ c hc pr hpr huniv hbun hφ hL
  exact ⟨c', hc', pr', hpr', huniv', hbun'⟩

end GlobalTheory.Poinc
end
end

