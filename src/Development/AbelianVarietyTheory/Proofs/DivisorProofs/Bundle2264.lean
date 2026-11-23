module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0100
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiser
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2163
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionOfFiniteFreeBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FlatGenDescent

variable {X X' : Scheme.{0}}

theorem isUnit_gs_iff {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (h : f z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs f z U a) ↔ f z ∈ X.basicOpen a := by
  rw [gs_eq f z U h, ← Scheme.mem_basicOpen Z _ z h, ← Scheme.preimage_basicOpen]
  rfl

theorem exists_mul {M : LB X} (hM : M.IsLB) (u : LB.Sec M) (v : LB.Sec (AbLaw.pw M (-1))) :
    ∃ a : Γ(X, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (k : M.ι), r z ∈ M.U k →
      gs r z ⊤ a = gs r z (M.U k) (u.f k) * gs r z (M.U k) (v.f k) := by
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' M.U ⊤ (fun k => homOfLE le_top) hM.cover.ge
    (fun k => (show Γ(X, M.U k) from u.f k) * (show Γ(X, M.U k) from v.f k))
    (fun k l => fn_ext (V := M.U k ⊓ M.U l) fun y hy => by
      refine (gs_res (𝟙 X) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X) y inf_le_right hy _).symm)
      refine (gs_mul (𝟙 X) y _ hy.1 _ _).trans (Eq.trans ?_ (gs_mul (𝟙 X) y _ hy.2 _ _).symm)
      have h₁ := FlatSec.gs_sec_trans u (𝟙 X) y hy.1 hy.2
      have h₂ : gs (𝟙 X) y (M.U k) (v.f k) = (gm (𝟙 X) y (M.U k ⊓ M.U l) (M.g k l ^ (-1 : ℤ))).val *
          gs (𝟙 X) y (M.U l) (v.f l) := FlatSec.gs_sec_trans v (𝟙 X) y (k := k) (l := l) hy.1 hy.2
      rw [h₁, h₂, map_zpow, zpow_neg_one, _root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul])
  refine ⟨a, fun Z r z k hk => ?_⟩
  exact (gs_res r z le_top hk a).symm.trans ((congrArg (gs r z (M.U k)) (ha k)).trans (gs_mul r z _ hk _ _))

def invSec (M : LB X) (π : X' ⟶ X) (t : LB.Gen (M.pull π)) (ht : t.IsGen) : LB.Sec ((AbLaw.pw M (-1)).pull π) :=
  genSec (M := (AbLaw.pw M (-1)).pull π) ⟨fun j => (t.s j)⁻¹⟩ fun i j => by
    have h := congrArg (·⁻¹) (ht i j)
    simp only [mul_inv, ← map_inv] at h
    refine h.trans (congrArg₂ (· * ·) ?_ rfl)
    show (∏ _k : PUnit, (res _ (pullU π _ (M.g _ _))) ^ (1 : ℤ))⁻¹ =
      ∏ _k : PUnit, (res _ (pullU π _ (M.g _ _ ^ (-1 : ℤ)))) ^ (1 : ℤ)
    rw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one, map_zpow, map_zpow, zpow_neg_one]

theorem exists_sec_of_flat {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (hg : g.Flat) [CompactSpace X]
    [QuasiSeparatedSpace X] (f : X ⟶ Sp R) (π : X' ⟶ X) (f' : X' ⟶ Sp R') (H : IsPullback π f' f (spMap g))
    (M : LB X) (hM : M.IsLB) (t : LB.Gen (M.pull π)) (ht : t.IsGen) (m : Ideal Γ(X, ⊤)) (hm : m.IsMaximal) :
    ∃ u : LB.Sec M, ∀ z : X', (∀ a ∈ m, π z ∉ X.basicOpen a) → π z ∈ nonzeroLocus u := by
  classical
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H M hM (genSec t ht)
  obtain ⟨n', c', v, hv⟩ := FlatSec.exists_comb_of_flat R R' g hg X f X' π f' H _ (AbLaw.isLB_pw hM (-1))
    (invSec M π t ht)
  choose a ha using fun i j => exists_mul hM (u i) (v j)
  by_cases hne : ∃ i j, a i j ∉ m
  · obtain ⟨i, j, hij⟩ := hne
    refine ⟨u i, fun z hz => ?_⟩
    obtain ⟨k, hk⟩ := exists_chart hM (π z)
    obtain ⟨y, x, hx, e⟩ := hm.exists_inv hij
    have e' := congrArg (gs π z ⊤) e
    rw [gs_add π z ⊤ trivial, gs_mul π z ⊤ trivial, gs_eq π z ⊤ trivial 1, map_one, map_one] at e'
    have hxu : ¬ IsUnit (gs π z ⊤ x) := fun h => hz x hx ((isUnit_gs_iff π z ⊤ trivial x).1 h)
    have hu1 : IsUnit (gs π z ⊤ y * gs π z ⊤ (a i j)) :=
      (IsLocalRing.isUnit_or_isUnit_of_add_one e').resolve_right hxu
    have hu2 := isUnit_of_mul_isUnit_right hu1
    rw [ha i j X' π z k hk] at hu2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (isUnit_gs_iff π z _ hk _).1 (isUnit_of_mul_isUnit_left hu2)⟩
  · push_neg at hne
    refine ⟨⟨fun _ => 0, fun _ _ => by simp⟩, fun z hz => False.elim ?_⟩
    obtain ⟨k, hk⟩ := exists_chart hM (π z)
    have hz' : z ∈ (M.pull π).U (fun _ => k) := mem_pull.2 hk
    have h₁ : (gm (𝟙 X') z ((M.pull π).U (fun _ => k)) (t.s fun _ => k)).val = _ :=
      (gs_unit (𝟙 X') z _ hz' _).symm.trans (hu z k hk)
    have h₂ : (gm (𝟙 X') z ((M.pull π).U (fun _ => k)) (t.s fun _ => k)⁻¹).val = _ :=
      (gs_unit (𝟙 X') z _ hz' _).symm.trans (hv z k hk)
    have h₃ := congrArg₂ (· * ·) h₁ h₂
    rw [map_inv, Units.mul_inv, Finset.sum_mul_sum] at h₃
    apply (IsLocalRing.maximalIdeal.isMaximal (X'.presheaf.stalk z)).ne_top
    rw [Ideal.eq_top_iff_one, h₃]
    refine Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun j _ => ?_
    rw [_root_.mul_mul_mul_comm]
    refine Ideal.mul_mem_left _ _ ?_
    have h₄ : ¬ IsUnit (gs π z ⊤ (a i j)) := fun h => hz _ (hne i j) ((isUnit_gs_iff π z ⊤ trivial _).1 h)
    rw [ha i j X' π z k hk] at h₄
    exact h₄

theorem flat_of_basis {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (d : ℕ) (b : Fin d → R')
    (h : ∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, g (c l) * b l) : g.Flat := by
  let _ : Algebra R R' := g.toAlgebra
  have hb : Function.Bijective (Fintype.linearCombination R b) := by
    rw [Function.bijective_iff_existsUnique]
    intro r'
    refine (existsUnique_congr fun c => ?_).1 (h r')
    rw [Fintype.linearCombination_apply, eq_comm]
    rfl
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective _ hb).symm

theorem exists_sec_of_free : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (d : ℕ) (b : Fin d → R'), (∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, g (c l) * b l) → ∀ (Z Z' : Scheme.{0}) (k' : Z' ⟶ Z) (f : Z ⟶ Sp R) (f' : Z' ⟶ Sp R'), IsPullback k' f' f (spMap g) → ∀ (O : Z.Opens), IsCompact (O : Set Z) → IsQuasiSeparated (O : Set Z) → ∀ (L : LB Z), L.IsLB → ∀ σ : LB.Gen ((L.pull k').pull (k' ⁻¹ᵁ O).ι), σ.IsGen → ∀ m : Ideal Γ(Z, O), m.IsMaximal → ∃ u : LB.Sec (L.pull O.ι), ∀ z : (k' ⁻¹ᵁ O).toScheme, (∀ a ∈ m, k' ((k' ⁻¹ᵁ O).ι z) ∉ Z.basicOpen a) → ∀ z₀ : O.toScheme, O.ι z₀ = k' ((k' ⁻¹ᵁ O).ι z) → z₀ ∈ nonzeroLocus u := by
  intro R R' _ _ g d b hb Z Z' k' f f' H O hO hO' L hL σ hσ m hm
  haveI : CompactSpace O.toScheme := isCompact_iff_compactSpace.mp hO
  haveI : QuasiSeparatedSpace O.toScheme := (isQuasiSeparated_iff_quasiSeparatedSpace _ O.isOpen).mp hO'
  have H' : IsPullback (k' ∣_ O) ((k' ⁻¹ᵁ O).ι ≫ f') (O.ι ≫ f) (spMap g) :=
    (isPullback_morphismRestrict k' O).paste_vert H
  obtain ⟨t₁, h₁⟩ := gen_chartPull (chartPullIn L (fun _ : PUnit => k') (fun _ => 1) (k' ⁻¹ᵁ O).ι) σ hσ
  obtain ⟨t, ht⟩ := gen_chartPull (chartPullOut L (fun _ : PUnit => O.ι) (fun _ => 1) (k' ∣_ O) _
    fun _ => (morphismRestrict_ι k' O).symm) t₁ h₁
  let e : Γ(O.toScheme, ⊤) ≃+* Γ(Z, O) := O.topIso.commRingCatIsoToRingEquiv
  haveI := hm
  obtain ⟨u, hu⟩ := exists_sec_of_flat g (flat_of_basis g d b hb) (O.ι ≫ f) (k' ∣_ O) _ H' (L.pull O.ι)
    (LB.isLB_pull hL _) t ht (m.comap e) (Ideal.comap_isMaximal_of_surjective e e.surjective)
  refine ⟨u, fun z hz z₀ hz₀ => ?_⟩
  have hc : O.ι ((k' ∣_ O) z) = k' ((k' ⁻¹ᵁ O).ι z) := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  obtain rfl : z₀ = (k' ∣_ O) z := O.ι.injective (hz₀.trans hc.symm)
  refine hu z fun a ha h => hz (e a) ha ?_
  rw [← hc]
  have := O.ι_image_basicOpen_topIso_inv (e a)
  rw [← this]
  exact ⟨_, (show _ ∈ O.toScheme.basicOpen (O.topIso.inv.hom (e a)) from (e.symm_apply_apply a).symm ▸ h), rfl⟩

end GlobalTheory.FlatGenDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalArithmeticVarietyModelProjectiveSpac
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormalModel

open TopologicalSpace

theorem exists_normal_model : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D m : ℕ) (y : Fin (m + 1) → Ω) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ : Ω →+* X.functionField),
    (g ≫ PSpace.str (𝓞 K) m = p ∧ IsArithVar p D ∧ Function.Bijective ψ ∧
      (∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i)) →
    ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (p' : X' ⟶ Sp (𝓞 K)) (g' : X' ⟶ PSpace (𝓞 K) m) (ψ' : Ω →+* X'.functionField),
      g' ≫ PSpace.str (𝓞 K) m = p' ∧ IsArithVar p' D ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' ∧ Function.Bijective ψ' ∧
      (∀ a : 𝓞 K, ψ' (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p' ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g').ι) (h : genericPoint X' ∈ ((ProjSpace.O1 (𝓞 K) m).pull g').U i),
        ψ' (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g').f i) =
          ψ' (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g').f i) := by
  intro K Ω _ _ _ _ D m y X _ p g ψ ⟨hgp, hX, hψ, hK, hy⟩
  obtain ⟨W, hne, hn⟩ := _root_.GlobalTheory.NormalOpen.exists_normal_opens (𝓞 K) X p D hX
  have := hX.finite
  have : IsFinite (spMap (Int.castRingHom (𝓞 K))) :=
    (IsFinite.SpecMap_iff _).2 (by
      have : (Int.castRingHom (𝓞 K)) = algebraMap ℤ (𝓞 K) := RingHom.ext_int _ _
      change (Int.castRingHom (𝓞 K)).Finite
      rw [this]
      exact RingHom.finite_algebraMap.2 hX.finite)
  have hs : IsProjOver (p ≫ spMap (Int.castRingHom (𝓞 K))) := by
    obtain ⟨h₁, h₂⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hX.isProjOver
    exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨inferInstance, h₂⟩
  have := hX.flat
  obtain ⟨Y, ν, e, hν, hnY, -, hfl, hpb, hd⟩ :=
    GraphClosure.exists_normalisation_of_locallyClosed ℤ X W.toScheme
      (p ≫ spMap (Int.castRingHom (𝓞 K))) W (𝟙 _) hs inferInstance hn inferInstance
  have he : IsOpenImmersion e := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : Nonempty W.toScheme := hne.to_subtype
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  have : IsIntegral Y := by
    have := GlobalTheory.IsNormalScheme.of_pred hnY
    have h := ((IrreducibleSpace.isIrreducible_univ W.toScheme).image _
      e.continuous.continuousOn).closure
    rw [Set.image_univ, hd.closure_eq] at h
    have : IrreducibleSpace Y := (irreducibleSpace_def _).2 h
    exact isIntegral_of_irreducibleSpace_of_isReduced Y
  have hfac : e ≫ ν = W.ι := by rw [hpb.w, Category.id_comp]
  have hoi : IsOpenImmersion (e ≫ ν) := by rw [hfac]; infer_instance
  have hg : e (genericPoint _) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have hgen : ν (genericPoint Y) = genericPoint X := by
    rw [← hg, ← Scheme.Hom.comp_apply]
    exact genericPoint_eq_of_isOpenImmersion _
  have hdeg : ν.residueDegree (genericPoint Y) ≠ 0 := by
    intro h0
    have h1 := CurveDegreesCompare.residueDegree_comp e ν (genericPoint _)
    rw [CurveDegreesCompare.residueDegree_of_isOpenImmersion, hg, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hproj : IsProjOver (ν ≫ p) := isProjOver_comp_of_isFinite ν hX.isProjOver
  have hflat : Flat ((ν ≫ p) ≫ spMap (Int.castRingHom (𝓞 K))) := by rwa [Category.assoc]
  have har : IsArithVar (ν ≫ p) D := ⟨hX.isDomain, hX.finite, ‹_›, hproj, hflat,
    DimCover.topologicalKrullDim_eq (𝓞 K) X Y p (ν ≫ p) D hX hproj hflat ν rfl hgen hdeg⟩

  have hη : ν (genericPoint Y) ⤳ genericPoint X := specializes_of_eq hgen
  have hWη : W.ι (genericPoint W.toScheme) ⤳ genericPoint X :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion _)
  have heη : e (genericPoint W.toScheme) ⤳ genericPoint Y := specializes_of_eq hg
  have hbij : Function.Bijective (SmallSec.fnMap ν hη) := by
    refine ⟨(SmallSec.fnMap ν hη).injective, fun u => ?_⟩
    obtain ⟨t, ht⟩ := SmallSec.fnMap_surjective W.ι hWη (SmallSec.fnMap e heη u)
    refine ⟨t, (SmallSec.fnMap e heη).injective ?_⟩
    rw [← ht, ← ProjSpace.fnMap_comp e ν heη hη (ProjSpace.comp_genericPoint_specializes _ _ heη hη)]
    exact ProjSpace.fnMap_congr hfac _ _ t
  refine ⟨Y, ‹_›, ν ≫ p, ν ≫ g, (SmallSec.fnMap ν hη).comp ψ, by rw [Category.assoc, hgp], har, hnY,
    hbij.comp hψ, fun a => ?_, fun k l i h => ?_⟩
  · have e₁ : ν.app ⊤ (algX p ⊤ a) = algX (ν ≫ p) ⊤ a := by
      simp only [algX, RingHom.comp_apply]
      rw [← Scheme.Hom.appLE_comp_appLE ν p ⊤ ⊤ ⊤ (by simp) (by simp)]
      rw [Scheme.Hom.app_eq_appLE ν]
      rfl
    rw [RingHom.comp_apply, hK, SmallSec.fnMap_fnOf ν hη _ (Opens.mem_top _), e₁]
    rfl
  · have hX' : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i := (pull_U _ g i).ge (by
      have h' : ν (genericPoint Y) ∈ g ⁻¹ᵁ (ProjSpace.O1 (𝓞 K) m).U (i PUnit.unit) :=
        (pull_U _ (ν ≫ g) i).le h
      rw [hgen] at h'
      exact h')
    have key (a : Fin (m + 1)) : fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) (ν ≫ g)).f i) =
        SmallSec.fnMap ν hη (fnOf _ hX' ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) g).f i)) := by
      have h₁ : genericPoint Y ∈ (ν ≫ g) ⁻¹ᵁ (ProjSpace.O1 (𝓞 K) m).U (i PUnit.unit) :=
        (pull_U _ (ν ≫ g) i).le h
      have h₂ : genericPoint X ∈ g ⁻¹ᵁ (ProjSpace.O1 (𝓞 K) m).U (i PUnit.unit) :=
        (pull_U _ g i).le hX'
      change fnOf _ h (resG Y _ _) = SmallSec.fnMap ν hη (fnOf _ hX' (resG X _ _))
      rw [fnOf_resG, fnOf_resG, SmallSec.fnMap_fnOf ν hη h₂ h₁, Scheme.Hom.comp_app]
      rfl
    rw [RingHom.comp_apply, RingHom.comp_apply, key, key, ← map_mul, ← map_mul, hy k l i hX']

end GlobalTheory.NormalModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenMulPointOnPullbackContainingClosedFibr
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem Near.exists_mul_pt {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G]
    (N : Near π G) {Z : Scheme.{0}} (q : Z ⟶ S) (a b : Z ⟶ N.U.left) (ha : a ≫ N.U.hom = q ≫ π)
    (hb : b ≫ N.U.hom = q ≫ π) :
    ∃ (O : Z.Opens) (h : O.toScheme ⟶ N.U.left), (∀ z : Z, π (q z) = closedPoint R → z ∈ O) ∧
      h ≫ N.U.hom = O.ι ≫ q ≫ π ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (s : T ⟶ S) (x y : Over.mk s ⟶ G), t ≫ O.ι ≫ q = s →
        N.Pt s (t ≫ O.ι ≫ a) x.left → N.Pt s (t ≫ O.ι ≫ b) y.left → N.Pt s (t ≫ h) (x * y).left := by
  haveI := N.isOpen
  let X₁ : Over.mk q ⟶ G := Over.homMk (pullback.lift a q ha ≫ N.u) (by
    change (pullback.lift a q ha ≫ N.u) ≫ G.hom = q
    rw [Category.assoc, N.u_over, pullback.lift_snd])
  let X₂ : Over.mk q ⟶ G := Over.homMk (pullback.lift b q hb ≫ N.u) (by
    change (pullback.lift b q hb ≫ N.u) ≫ G.hom = q
    rw [Category.assoc, N.u_over, pullback.lift_snd])
  let m : Z ⟶ G.left := (X₁ * X₂).left
  have hm : m ≫ G.hom = q := Over.w (X₁ * X₂)
  let O : Z.Opens := m ⁻¹ᵁ N.u.opensRange
  have hO : Set.range (O.ι ≫ m) ⊆ Set.range N.u := by
    rintro _ ⟨z, rfl⟩
    have hz : O.ι z ∈ O := z.2
    rw [Scheme.Hom.comp_apply]
    exact hz
  let h' : O.toScheme ⟶ pullback N.U.hom π := IsOpenImmersion.lift N.u (O.ι ≫ m) hO
  have hh : h' ≫ N.u = O.ι ≫ m := IsOpenImmersion.lift_fac _ _ _
  have hs : h' ≫ pullback.snd N.U.hom π = O.ι ≫ q := by
    rw [← N.u_over, ← Category.assoc, hh, Category.assoc, hm]
  refine ⟨O, h' ≫ pullback.fst _ _, fun z hz => ?_, ?_, ?_⟩
  · refine N.all (m z) ?_
    rw [← Scheme.Hom.comp_apply m G.hom, hm]
    exact hz
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.assoc]
  · rintro T t s x y hts ⟨x₀, hx₁, hx₂, hx₃⟩ ⟨y₀, hy₁, hy₂, hy₃⟩
    let τ : Over.mk s ⟶ Over.mk q := Over.homMk (t ≫ O.ι) (by
      change (t ≫ O.ι) ≫ q = s
      rw [Category.assoc, hts])
    have ex : x = τ ≫ X₁ := by
      ext1
      change x.left = (t ≫ O.ι) ≫ pullback.lift a q ha ≫ N.u
      rw [← hx₃, ← Category.assoc]
      congr 1
      apply pullback.hom_ext
      · rw [hx₁, Category.assoc, pullback.lift_fst, Category.assoc]
      · rw [hx₂, Category.assoc, pullback.lift_snd, Category.assoc, hts]
    have ey : y = τ ≫ X₂ := by
      ext1
      change y.left = (t ≫ O.ι) ≫ pullback.lift b q hb ≫ N.u
      rw [← hy₃, ← Category.assoc]
      congr 1
      apply pullback.hom_ext
      · rw [hy₁, Category.assoc, pullback.lift_fst, Category.assoc]
      · rw [hy₂, Category.assoc, pullback.lift_snd, Category.assoc, hts]
    refine ⟨t ≫ h', Category.assoc _ _ _, ?_, ?_⟩
    · rw [Category.assoc, hs, hts]
    · rw [ex, ey, ← MonObj.comp_mul, Category.assoc, hh]
      exact (Category.assoc _ _ _).symm

theorem Near.exists_mul_pt_pullback (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S)
    [GrpObj G'] (N : Near M.π G') :
    ∃ (O : (pullback (N.U ⊗ N.U).hom M.π).Opens) (h : O.toScheme ⟶ N.U.left),
      (∀ z : ↥(pullback (N.U ⊗ N.U).hom M.π),
        (N.U ⊗ N.U).hom (pullback.fst (N.U ⊗ N.U).hom M.π z) = closedPoint R → z ∈ O) ∧
      h ≫ N.U.hom = O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (N.U ⊗ N.U).hom ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (s : T ⟶ M.S) (x y : Over.mk s ⟶ G'),
        t ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π = s →
        N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (fst N.U N.U).left) x.left →
        N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (snd N.U N.U).left) y.left →
        N.Pt s (t ≫ h) (x * y).left := by
  obtain ⟨O, h, h₁, h₂, h₃⟩ := N.exists_mul_pt (pullback.snd (N.U ⊗ N.U).hom M.π)
    (pullback.fst (N.U ⊗ N.U).hom M.π ≫ (fst N.U N.U).left)
    (pullback.fst (N.U ⊗ N.U).hom M.π ≫ (snd N.U N.U).left)
    (by rw [Category.assoc, Over.w (fst N.U N.U), pullback.condition])
    (by rw [Category.assoc, Over.w (snd N.U N.U), pullback.condition])
  refine ⟨O, h, fun z hz => h₁ z ?_, ?_, h₃⟩
  · rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact hz
  · rw [h₂, pullback.condition]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenRangeEqInterPreimageEtaleUnivOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isOpen_range_of_etale_of_universallyOpen_comp {Y Z T : Scheme.{0}} (i' : Z ⟶ Y) (h : Y ⟶ T)
    [Etale h] (hu : UniversallyOpen (i' ≫ h)) : IsOpen (Set.range i') := by
  have s_open : IsOpenImmersion (pullback.lift (𝟙 Z) i' (by simp) : Z ⟶ pullback (i' ≫ h) h) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (pullback_lift_diagonal_isPullback i' h) inferInstance
  have e : Set.range i' = (pullback.snd (i' ≫ h) h) '' Set.range (pullback.lift (𝟙 Z) i' (by simp) : Z ⟶ pullback (i' ≫ h) h) := by
    rw [← Set.range_comp]
    congr 1
    ext z
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd]
  rw [e]
  exact (pullback.snd (i' ≫ h) h).isOpenMap _ (pullback.lift (𝟙 Z) i' _).isOpenEmbedding.isOpen_range

theorem exists_opens_range_eq_of_etale {X B T Z : Scheme.{0}} (c : X ⟶ B) (j : T ⟶ B) (i : Z ⟶ X) (φ : Z ⟶ T)
    (hc : Etale c) (hj : IsPreimmersion j) (hφ : UniversallyOpen φ) (w : i ≫ c = φ ≫ j) :
    ∃ W : X.Opens, Set.range i = (W : Set X) ∩ c ⁻¹' Set.range j := by
  let i' : Z ⟶ pullback c j := pullback.lift i φ w
  have hi' : i' ≫ pullback.snd c j = φ := pullback.lift_snd _ _ _
  have ho : IsOpen (Set.range i') :=
    isOpen_range_of_etale_of_universallyOpen_comp i' (pullback.snd c j) (by rw [hi']; exact hφ)
  have hemb := IsPreimmersion.isEmbedding (pullback.fst c j)
  obtain ⟨U, hU, hpre⟩ := hemb.isInducing.isOpen_iff.1 ho
  refine ⟨⟨U, hU⟩, ?_⟩
  have hr : Set.range i = (pullback.fst c j) '' Set.range i' := by
    rw [← Set.range_comp]
    congr 1
    ext z
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
  rw [hr, ← hpre, Set.image_preimage_eq_inter_range, Scheme.Pullback.range_fst]
  rfl

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointArcDataAtUniformiserCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_point_hasArcData_uniformiser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (Xo : Moduli Dm l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Y.N4 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (b : O →+* V) (ϖ : V) (a : ArcIn Dm l β V b), Irreducible ϖ → ∃ y : Sp V ⟶ Y.X, Y.HasArcData a (maximalIdeal V) (RingHom.id V) ϖ y := by
  intro E _ _ _ H Dm l Xo c O _ β Y hN V _ _ _ hV b ϖ a hϖ
  obtain ⟨hdvr, hc, hcz⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  obtain ⟨h1, h2, -, h4, h5⟩ := GlobalTheory.lawsAndExpansions.1
  have hT := GlobalTheory.twistBaseChange
  have hm : maximalIdeal V = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  obtain ⟨χ, hχ, -⟩ := hN V b ϖ a (Or.inr ⟨hdvr, hϖ, hm ▸ hc⟩)
  obtain ⟨hs, -, hj, hd⟩ := (hχ χ).1 rfl
  obtain ⟨-, -, ev, hC, hX, -⟩ := GlobalTheory.UniformiserEval.dvr_admissibleBase_and_powerSeries_evalUniformiser V ϖ hϖ hc
  have hr : Set.range (jK V ≫ spMap ev ≫ χ) ⊆ Set.range Y.j := by
    rintro _ ⟨x, rfl⟩
    have e : (jK V ≫ spMap ev ≫ χ) x = χ (spMap ev (jK V x)) := by
      simp only [Scheme.Hom.comp_apply]
    rw [e]
    apply hj
    intro hx
    have hx' : algebraMap V (FractionRing V) (ev (PowerSeries.C ϖ * PowerSeries.X)) ∈ x.asIdeal := hx
    have hu : IsUnit (algebraMap V (FractionRing V) (ev (PowerSeries.C ϖ * PowerSeries.X))) := by
      rw [map_mul, hC, hX]
      refine IsUnit.mk0 _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact mul_ne_zero hϖ.ne_zero hϖ.ne_zero
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx' hu)
  refine ⟨spMap ev ≫ χ, ?_⟩
  rw [hm]
  exact GlobalTheory.hasArcData_specialise h1 h2 hT h4.unifBaseChange h5 E H Dm l Xo c O β Y V b ϖ a hϖ hc ev hC hX χ hs hr hd

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneBirigidifiedSymmetricNoetherianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_eq_one_birigidifiedSymmetric_noetherian : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (A : Over (Sp B)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∃ M : ℕ, 0 < M ∧ ∀ (T : Over (Sp B)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ M = 1 := by
  first | (exact @GlobalTheory.AbDual.exists_pow_eq_one_of_triv_ev_noeth) | (exact GlobalTheory.AbDual.exists_pow_eq_one_of_triv_ev_noeth) | (intros; apply GlobalTheory.AbDual.exists_pow_eq_one_of_triv_ev_noeth  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqOfLogDerivationExtendEqStatement
section
open GlobalTheory.LogDerProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_eq_of_logDerivation_extend_eq : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ (J : Ideal R) (D₁ D₂ : logSub φ J), res (S := S) f φ J D₁ = res (S := S) f φ J D₂ → ∃ c : Submonoid.powers f, c • D₁ = c • D₂ := by
  first | exact @GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq | exact GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq | (intros; apply GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackGroupOLinearTorsionLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_group_oLinear_torsion_level : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] [IsCommMonObj AH] (actH : OActN D.O AH) (Y : Over H) (u : D.La → (Y ⟶ AH)), (∀ x y, u (x + y) = u x * u y) → (∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c) → (∀ x, u (N • x) = 1) → ∃ (AE : Over Y.left) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ AH.left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE)), IsGrpPullback AE AH Y.hom φE ∧ (∀ a : D.O, (actE.act a).left ≫ φE = φE ≫ (actH.act a).left) ∧ EtaOK D N actE ηE ∧ ∀ y, (ηE y).left ≫ φE = (u y).left := by
  first | (exact @GlobalTheory.UPel.HT.LevPull.exists_pull_level) | (exact GlobalTheory.UPel.HT.LevPull.exists_pull_level) | (intros; apply GlobalTheory.UPel.HT.LevPull.exists_pull_level  <;> assumption)
end

