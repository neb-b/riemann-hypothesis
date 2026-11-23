module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Rosati
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2528
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3105
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleProdIsoOfPowIsoBirigidifiedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_prod_iso_of_pow_iso_birigidified : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ) (P₁ P₂ : LB (G2 A).left), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → P₁.IsLB → (∃ t : (P₁.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P₁.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → P₂.IsLB → (∃ t : (P₂.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P₂.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso (lbPow P₁ k) (lbPow P₂ k) → LBIso P₁ P₂ := by
  first | (exact @GlobalTheory.BirigidRoot.iso_of_lbPow_iso) | (exact GlobalTheory.BirigidRoot.iso_of_lbPow_iso) | (intros; apply GlobalTheory.BirigidRoot.iso_of_lbPow_iso  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffDualNumberGraphReductionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_hodgeFiltration_iff_dualNumberGraph_reduction : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (f : HdR A₀ →ₗ[k] HdR A₀) (y : HdR A₀), y ∈ Fil A₀ ↔ ∃ d ∈ GlobalTheory.HTRealise.graphFil A₀ f, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀).Corr d y := by
  first | (exact @GlobalTheory.HTRealise.mem_Fil_iff_exists_graphFil_corr) | (exact GlobalTheory.HTRealise.mem_Fil_iff_exists_graphFil_corr) | (intros; apply GlobalTheory.HTRealise.mem_Fil_iff_exists_graphFil_corr  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffReductionGluedFiltrationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_hodgeFiltration_iff_reduction_gluedFiltration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (tk : R →+* k) (s : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s), s = spMap tk → ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ GlobalTheory.HTGlue.glueFil o₀.A f, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) rfl o₀.A).Corr e y := by
  first | (exact @GlobalTheory.HTGlue.mem_fil_iff_exists_glueFil) | (exact GlobalTheory.HTGlue.mem_fil_iff_exists_glueFil) | (intros; apply GlobalTheory.HTGlue.mem_fil_iff_exists_glueFil  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedBlowupAmpleDivisorCompactification
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.PoincTop

theorem poinSt : PoinSt := by
  intro g hg n hn hodd F Z z i hth OZ hOZ hamp φ hφ
  obtain ⟨hproj, hnorm, hoi, hiz, hdense, W8, hW8, hthi⟩ := hth
  obtain ⟨d, J, hd, hJ, hval⟩ :=
    _root_.GlobalTheory.Poinc.idealSt_holds g hg n hn hodd F Z z i ⟨hproj, hnorm, hoi, hiz, hdense, W8, hW8, hthi⟩ φ hφ
  haveI := hoi
  let W : Z.Opens := i.opensRange
  have hWset : (W : Set Z) = Set.range i := by simp [W]
  obtain ⟨S, π, BD, hbl, hpS, hBD, hiso, hdS⟩ :=
    _root_.GlobalTheory.NormBlowupInt.exists_normBl n Z z hproj (GlobalTheory.IsNormalScheme.pred Z) J W (by rw [hWset]; exact hdense)
      (fun x hx hxW => hJ x hx (by have h : x ∈ (W : Set Z) := hxW; rwa [hWset] at h))
  haveI := hiso
  let A : F.X ⟶ (π ⁻¹ᵁ W).toScheme := i.isoOpensRange.hom ≫ inv (π ∣_ W)
  let j : F.X ⟶ S := A ≫ (π ⁻¹ᵁ W).ι
  have hjπ : j ≫ π = i := by
    simp only [j, A, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    simp [W]
  have hrj : Set.range j = π ⁻¹' Set.range i := by
    have hA : Function.Surjective A := A.surjective
    change Set.range ((π ⁻¹ᵁ W).ι ∘ A) = _
    rw [Set.range_comp, hA.range_eq, Set.image_univ, Scheme.Opens.range_ι, ← hWset]
    rfl
  refine ⟨d, J, S, π, j, BD, hd, hJ, hval, hbl, hpS, inferInstance, ?_, hjπ, hrj.symm, hBD, ?_, ?_⟩
  · rw [hrj, ← hWset]; exact hdS
  · intro T ξ hξ
    obtain ⟨a, ha, hid⟩ := hval T (ξ ≫ π) (by rw [← Category.assoc, hξ, Category.assoc, hjπ])
    refine ⟨a, ha, ?_⟩
    rw [hBD, GlobalTheory.PullAlong.idlAlong_comap_eq]
    exact hid
  · obtain ⟨S₀, π₀, ν, U, hb, hνπ, hfin, -⟩ := hbl.2
    haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
    haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
    obtain ⟨T₀, hT⟩ := _root_.GlobalTheory.BlowAmpleNoeth.ample_twist_of_blowup (cycAway n) Z S₀ S z J π₀ ν BD hproj hb hfin
      (by rw [hνπ]; exact hBD) OZ hamp
    refine ⟨T₀, fun k hk => ?_⟩
    have h := hT k hk
    rwa [hνπ] at h

end GlobalTheory.PoincTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedPullConstMorVPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlueLie

theorem ext_of_liftSemi_surj {K C : Type} [Field K] [CommRing C] [Algebra K C] {M M' : Type*} [AddCommGroup M]
    [Module K M] [AddCommGroup M'] [Module C M'] (P : M →ₛₗ[algebraMap K C] M')
    (hP : Function.Surjective (liftSemi P)) {e e' : M' →ₗ[C] C} (h : ∀ c, e (P c) = e' (P c)) : e = e' := by
  refine LinearMap.ext fun c' ↦ ?_
  obtain ⟨u, rfl⟩ := hP c'
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add (f := _), map_add (f := _), map_add (f := _), hu, hv]
  | tmul r c => rw [liftSemi_tmul, map_smul, map_smul, h c]

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
  (A₀ : Over (Sp k)) [GrpObj A₀]

def fstC : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀ →+ HdR A₀ where
  toFun e :=
    { toFun c := (e ((GlobalTheory.FODef.constMorV k V A₀).pull c)).fst
      map_add' c c' := by rw [map_add (f := _), map_add (f := _), TrivSqZeroExt.fst_add]
      map_smul' r c := by
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, TrivSqZeroExt.algebraMap_eq_inl,
          TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, smul_eq_mul] }
  map_zero' := by ext c; rfl
  map_add' e e' := by ext c; rfl

def sndC : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀ →+
    (primDR A₀ →ₗ[k] V) where
  toFun e :=
    { toFun c := (e ((GlobalTheory.FODef.constMorV k V A₀).pull c)).snd
      map_add' c c' := by rw [map_add (f := _), map_add (f := _), TrivSqZeroExt.snd_add]
      map_smul' r c := by
        rw [LinearMap.map_smulₛₗ, map_smul, algebraMap_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply] }
  map_zero' := by ext c; rfl
  map_add' e e' := by ext c; rfl

variable {A₀}

theorem fstC_apply (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀)
    (c : primDR A₀) : fstC A₀ e c = (e ((GlobalTheory.FODef.constMorV k V A₀).pull c)).fst := rfl

theorem sndC_apply (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀)
    (c : primDR A₀) : sndC A₀ e c = (e ((GlobalTheory.FODef.constMorV k V A₀).pull c)).snd := rfl

theorem eval_eq (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀)
    (c : primDR A₀) : e ((GlobalTheory.FODef.constMorV k V A₀).pull c) =
      TrivSqZeroExt.inl (fstC A₀ e c) + TrivSqZeroExt.inr (sndC A₀ e c) := by
  ext
  · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]; rfl
  · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]; rfl

theorem fstC_smul (r : k) (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) :
    fstC A₀ (algebraMap k (TrivSqZeroExt k V) r • e) = r • fstC A₀ e := by
  ext c
  rw [LinearMap.smul_apply, fstC_apply, fstC_apply, LinearMap.smul_apply, smul_eq_mul,
    TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, smul_eq_mul]

theorem sndC_smul (r : k) (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) :
    sndC A₀ (algebraMap k (TrivSqZeroExt k V) r • e) = r • sndC A₀ e := by
  ext c
  rw [LinearMap.smul_apply, sndC_apply, sndC_apply, LinearMap.smul_apply, algebraMap_smul, TrivSqZeroExt.snd_smul]

theorem fstC_push (g : A₀ ⟶ A₀) [IsMonHom g]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) :
    fstC A₀ (push (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g e) =
      push (dp0 k) (𝟙 _) g (fstC A₀ e) := by
  ext c; rw [fstC_apply, push_apply, GlobalTheory.HTGlue.primPull_constMorV_pull, push_apply, fstC_apply]

theorem sndC_push (g : A₀ ⟶ A₀) [IsMonHom g]
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) :
    sndC A₀ (push (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) g e) =
      sndC A₀ e ∘ₗ primPull (dp0 k) (𝟙 _) g := by
  ext c; rw [sndC_apply, push_apply, GlobalTheory.HTGlue.primPull_constMorV_pull, LinearMap.comp_apply, sndC_apply]

theorem ext_coords (hA : IsAbelianScheme A₀)
    {e e' : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀}
    (h1 : fstC A₀ e = fstC A₀ e') (h2 : sndC A₀ e = sndC A₀ e') : e = e' := by
  refine ext_of_liftSemi_surj _ (GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V)
    (GlobalTheory.FODef.constMorV k V A₀)).2 fun c ↦ ?_
  rw [eval_eq, eval_eq, h1, h2]

theorem exists_of_coords (hA : IsAbelianScheme A₀) (x : HdR A₀) (y : primDR A₀ →ₗ[k] V) :
    ∃ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀,
      fstC A₀ e = x ∧ sndC A₀ e = y := by
  obtain ⟨e, he⟩ := GlobalTheory.HTGlue.exists_coords V A₀ hA
    ((Algebra.linearMap k (TrivSqZeroExt k V)) ∘ₗ x + (TrivSqZeroExt.inrHom k V) ∘ₗ y)
  refine ⟨e, ?_, ?_⟩ <;> ext c
  · rw [fstC_apply, he c]; simp [TrivSqZeroExt.algebraMap_eq_inl]
  · rw [sndC_apply, he c]; simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem red_pull_constMorV_pull (c : prim (dp0 k) (𝟙 _) A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).pull
      ((GlobalTheory.FODef.constMorV k V A₀).pull c) = c := by
  rw [GrpMor.pull_pull _ _ (homMor (dp0 k) (𝟙 _) (𝟙 A₀)) (fun r => rfl) (by simp)]
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)

theorem corr_iff_fstC (hA : IsAbelianScheme A₀)
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀) (y : HdR A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k V)) rfl A₀).Corr e y ↔
      fstC A₀ e = y := by
  constructor
  · intro h
    ext c
    have h1 := h ((GlobalTheory.FODef.constMorV k V A₀).pull c)
    rw [red_pull_constMorV_pull] at h1
    rw [h1, fstC_apply]
    rfl
  · rintro rfl
    exact GlobalTheory.HTGlue.eq_of_liftSemi_surj _ (GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V)
      (GlobalTheory.FODef.constMorV k V A₀)).2 _ _ e (fstC A₀ e) red_pull_constMorV_pull (fun c ↦ rfl)

theorem mem_glueFil_iff {d : ℕ} (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀))
    (e : Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) :
    e ∈ GlobalTheory.HTGlue.glueFil A₀ f ↔ fstC A₀ e ∈ Fil A₀ ∧
      ∀ j, LinearMap.proj j ∘ₗ sndC A₀ e - f j (fstC A₀ e) ∈ Fil A₀ := by
  constructor
  · rintro ⟨x, hx, z, hz, he⟩
    have h1 : fstC A₀ e = x := by ext c; rw [fstC_apply, he c]; simp
    refine ⟨h1 ▸ hx, fun j ↦ ?_⟩
    have h2 : LinearMap.proj j ∘ₗ sndC A₀ e = f j x + z j := by
      ext c; rw [LinearMap.comp_apply, sndC_apply, he c]; simp
    rw [h1, h2, add_sub_cancel_left]; exact hz j
  · rintro ⟨h1, h2⟩
    refine ⟨fstC A₀ e, h1, fun j ↦ LinearMap.proj j ∘ₗ sndC A₀ e - f j (fstC A₀ e), h2, fun c ↦ ?_⟩
    rw [eval_eq]
    congr 2
    funext j
    simp [sndC_apply]

end GlobalTheory.HTGlueLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagRootPullbackQuasiInverse
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES

open GlobalTheory.CechPic

theorem relAmple_diag_root_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) [IsLocallyNoetherian Y] (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → Out.RelAmple B (P'.pull (lift (𝟙 B) (𝟙 B)).left) := by
  intro p _ D R _ b N c Y _ s o B _ _ ψ ψ' hp hc hB hq P' hP' hiso _
  obtain ⟨e, rfl⟩ := hc
  have hu : IsUnit (((p ^ e : ℕ)) : Γ(Y, ⊤)) := by
    have h := hp.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [map_natCast] at h
    rw [Nat.cast_pow]
    exact h.pow e
  have hq' : IsQuasiInv (p ^ e) ψ' ψ := ⟨hq.2.1, hq.1, hq.2.2.2, hq.2.2.1⟩
  have hfin := (isFinite_etale_surjective_of_isQuasiInv Y B o.A (p ^ e) ψ' ψ hB o.ab hu hq').1
  have := hB.proper
  have := o.ab.proper
  have hL := hP'.1
  have hD := pull_isLB o.isLB (lift (𝟙 o.A) (𝟙 o.A)).left
  have a₁ := GlobalTheory.RootDiagAmple.relAmple_pull_of_isFinite ψ' hD o.ample
  have relAmple_of_pow {A : Over Y} [IsProper A.hom] {L M : LB A.left} (hL : L.IsLB)
      (hM : M.IsLB) {d : ℕ} (hd : 1 ≤ d) (eq : cls M hM = d • cls L hL)
      (h : Out.RelAmple A M) : Out.RelAmple A L := by
    rw [relAmple_iff_isAmpleLB A hM] at h
    refine relAmple_of_isAmpleLB A hL fun U hU => (isAmpleLB_pow_iff (pull_isLB hL _) hd).1 ?_
    refine (isAmpleLB_congr (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)
      ((cls_eq_iff (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)).1 ?_)).2 (h U hU)
    rw [cls_lbPow (pull_isLB hL _), cls_pull hL, cls_pull hM, eq, map_nsmul]
  refine relAmple_of_pow (pull_isLB hL _) (pull_isLB hD _)
    (d := p ^ e) (Nat.one_le_pow e p ((Fact.out : p.Prime).pos)) ?_ a₁
  have hpow : (Hecke.lbPow P' (p ^ e)).IsLB := LB.isLB_linComb hL _ _
  have ec := (cls_eq_iff (pull_isLB o.isLB _) hpow).2 hiso
  have ep : cls _ hpow = (p ^ e) • cls P' hL := by
    refine (cls_linComb hL (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 1) hpow).trans ?_
    simp [pull_id]
  rw [cls_pull hL, cls_pull hD, cls_pull o.isLB, ← pull_comp]
  have m : ψ'.left ≫ (lift (𝟙 o.A) (𝟙 o.A)).left = (lift (𝟙 B) (𝟙 B)).left ≫ Hecke.sq2 ψ' := by
    rw [Hecke.sq2, ← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [m, pull_comp, ← cls_pull o.isLB _ (pull_isLB o.isLB _), ec, ep, map_nsmul]

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianUniformizationLinearActionTransfer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorTrait

theorem exists_trait_of_unif (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀] (hR : Base R₀)
    (D₀ : DegData R₀ (maximalIdeal R₀)) (A₀ : PolAV (Sp (FractionRing R₀))) (G₀ : Over (Sp R₀)) [GrpObj G₀]
    [IsCommMonObj G₀] (hG : IsSemiAbelian G₀) (U₀ : Unif (maximalIdeal R₀) D₀ A₀ G₀) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₀ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW)
      (_ : IsCommMonObj GW) (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W)))
      (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧
      IsGrpPullback GW G₀ (spMap φ) β ∧ LBIso UW.LG.L (U₀.LG.L.pull β) ∧ Nonempty (IsPullDeg φ D₀.toPre DW.toPre) := by
  have := hR.2
  have := hR.1.1
  obtain ⟨W, _, _, _, φ, hW, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R₀ (maximalIdeal R₀)
  haveI hloc : IsLocalHom φ := ((IsLocalRing.local_hom_tfae φ).out 1 5).mpr hc
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨DW, hD, AW, UW, hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hR.1 hW' φ hφ (map_maximalIdeal_le φ) hG U₀
  have hb : (Iso.refl ((Over.pullback (specOf φ)).obj G₀)).hom.left ≫ pullback.fst G₀.hom (specOf φ) =
      pullback.fst G₀.hom (specOf φ) := Category.id_comp _
  refine ⟨W, _, inferInstance, inferInstance, φ, (Over.pullback (specOf φ)).obj G₀, inferInstance, inferInstance,
    (Iso.refl ((Over.pullback (specOf φ)).obj G₀)).hom.left ≫ pullback.fst G₀.hom (specOf φ), DW, AW, UW, hW, hφ, hloc,
    ?_, ⟨hP.lg.choose, hP.lg.choose_spec.1⟩, ⟨hD⟩⟩
  exact (isGrpPullback_pullback G₀ (spMap φ)).congr rfl hb.symm

theorem factor_unif_at_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (D₀ : DegData R₀ (maximalIdeal R₀)) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₀ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), FinExt ρ₀ ∧ Nonempty (IsPullDeg ρ₀ D.toPre D₀.toPre) ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₀ (spMap φ) β ∧ LBIso UW.LG.L (P.L.L.pull β) ∧ Nonempty (IsPullDeg φ D₀.toPre DW.toPre) ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) := by
  intro R _ _ _ hR D D' F hA A' G' _ _ hG' U' oA oG hO G _ _ hG inc pr hinc hpr h1 h2
  obtain ⟨R₉, _, _, _, ρ₉, G₉, _, _, β₉, β₉₂, P₉, A₉, gen₉, a1, a2, a3, a4, a5, a6, a7, a8⟩ :=
    GlobalTheory.T.exists_finExt_cubicalSymmetric_even_factor R hR D D' F hA A' G' hG' U' oA oG hO G hG inc pr hinc hpr h1 h2
  obtain ⟨R₀, _, _, _, ρ₀, D₀, G₀, _, _, β₀, β₀₂, P, A₀, gen₀, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ :=
    _root_.GlobalTheory.Mum.TraitTwist.exists_bundle_data_at_traits R hR D D' F A' G' hG' U' oA oG hO G hG inc pr hinc hpr h1 h2 R₉ ρ₉ G₉ β₉ β₉₂ P₉ A₉ gen₉ a1 a2 a3 a4 a5 a6 a7 a8
  haveI := hR.2
  have hR₀ : Base R₀ := ⟨c1.1, charZero_of_injective_ringHom c1.2.1⟩
  obtain ⟨D'', U'', hLG, -⟩ := _root_.GlobalTheory.Mum.exists_unif_even R₀ hR₀ G₀ P c5 c7 A₀ gen₀ c8 c9
  obtain ⟨W, _, _, _, φ, GW, _, _, β, DW, AW, UW, w1, w2, w3, w4, w5, -⟩ := exists_trait_of_unif R₀ hR₀ D'' A₀ G₀ c5 U''
  rw [hLG] at w5
  exact ⟨R₀, _, _, _, ρ₀, D₀, G₀, _, _, β₀, β₀₂, P, W, _, _, _, φ, GW, _, _, β, DW, AW, UW, c1, c2, c3, c4, c5, w1, w2, w3,
    w4, w5, c10 W w1 φ w2 w3 GW β DW AW UW w4 w5, c6⟩

end GlobalTheory.Mum.FactorTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfDualHomomorphismKernelKilled
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
open ReciprocityTheory.ChartRestriction.G
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.DualHomSurj

theorem surjective_of_ker_killed : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Surjective la.left := by
  intro S A B _ _ Q la d hA hB hd _ hla hd0 hk
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  have : LocallyOfFiniteType (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType la.left := locallyOfFiniteType_of_comp _ B.hom
  have : QuasiCompact (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact la.left := QuasiCompact.of_comp _ B.hom
  have hSA := GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA
  have hLQF : LocallyQuasiFinite la.left :=
    GlobalTheory.locallyQuasiFinite_of_finite_geometric_ker _ A B la hla inferInstance inferInstance
      fun Ω _ _ t => by
        have := GlobalTheory.HomExt.finite_torsion_points hSA t hd0
        exact Finite.of_injective (β := {x : Over.mk t ⟶ A // x ^ d = 1})
          (fun x => ⟨x.1, hk _ x.1 x.2⟩) fun a b e =>
            Subtype.ext (congrArg (fun z : {x : Over.mk t ⟶ A // x ^ d = 1} => z.1) e)
  haveI : IsMonHom la := hla
  refine GlobalTheory.AbLaw.MulN.surjective_of_geomFibres la fun K _ _ s => ?_
  have hA' := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  have hB' := GlobalTheory.isAbelianScheme_pullback_obj s B hB
  obtain ⟨gA, hgA⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj A) hA'
  obtain ⟨gB, hgB⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj B) hB'
  let Ak : GlobalTheory.AV.AbVar K := { X := (Over.pullback s).obj A, ab := hA', dim := gA, smooth := hgA }
  let Bk : GlobalTheory.AV.AbVar K := { X := (Over.pullback s).obj B, ab := hB', dim := gB, smooth := hgB }
  have key : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback s).map a).left ≫ pullback.fst Y.hom s = pullback.fst X.hom s ≫ a.left :=
    fun a ↦ pullback.lift_fst _ _ _
  let h : ((Over.pullback s).obj A ⊗ (Over.pullback s).obj B).left ⟶ (A ⊗ B).left :=
    (Functor.LaxMonoidal.μ (Over.pullback s) A B).left ≫ pullback.fst (A ⊗ B).hom s
  have h₁ : h ≫ (fst A B).left = (fst ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst A.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (fst A B) = fst _ _ by simp]
  have h₂ : h ≫ (snd A B).left = (snd ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst B.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (snd A B) = snd _ _ by simp]
  have hP' : (Q.pull h).IsLB := pull_isLB hd.isLB _
  have hd' : IsDual Ak.X Bk.X (Q.pull h) := IsDual.baseChange (isGrpPullback_pullback A s)
    (isGrpPullback_pullback B s) h₁ h₂ hP' ((cls_eq_iff hP' hP').1 rfl) hd
  have hdim : gB = gA := GlobalTheory.DualTower.dim_eq_of_isDual Ak Bk (Q.pull h) hd'
  have : LocallyQuasiFinite ((Over.pullback s).map la).left :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange s la)
      inferInstance
  exact (GlobalTheory.IsogenyQuasiInverse.flat_surjective_of_field _ _ gA hA' hB' hgA (hdim ▸ hgB) _).2

end GlobalTheory.DualHomSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPointInductionStepLogCanonicalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoPoint_induction_step_logCanonical : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (d ε : ℚ) (h : ℕ → ℚ) (x x' : X) (j : ℕ), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsClosed ({x} : Set X) → IsClosed ({x'} : Set X) → x ≠ x' → (∀ e, 0 < h e) → (∀ (z : X) (e : ℕ), z ⤳ x ∨ z ⤳ x' → 1 ≤ e → topologicalKrullDim (closure ({z} : Set X)) = e → 2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin e => N : ℤ)) → 0 < ε → QNum p N d D → 0 ≤ d → LcCut p n (Δ + D) x j → ¬ KltAt p n (Δ + D) x' → LcCut p n (Δ + D) x 0 ∨ ∃ (i : ℕ) (D' : X → ℚ) (d' : ℚ), i < j ∧ 0 ≤ d' ∧ d' ≤ d + (h (i + 1) + ε) ∧ QNum p N d' D' ∧ ((LcCut p n (Δ + D') x i ∧ ¬ KltAt p n (Δ + D') x') ∨ (LcCut p n (Δ + D') x' i ∧ ¬ KltAt p n (Δ + D') x)) := by
  first | exact @GlobalTheory.PairStep.twoPoint_step | exact GlobalTheory.PairStep.twoPoint_step | (intros; apply GlobalTheory.PairStep.twoPoint_step <;> assumption)
end

