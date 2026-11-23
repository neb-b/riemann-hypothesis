module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2227
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleGenericFibreDescent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory

namespace GenericBundleDescent

variable {X X' Y Z : Scheme.{0}}

theorem pull_both {M : LB X} {N : LB X'} {a : Y ⟶ X} {b : Y ⟶ X'} (H : LBIso (M.pull a) (N.pull b)) (h : Z ⟶ Y)
    {a' : Z ⟶ X} {b' : Z ⟶ X'} (ea : a' = h ≫ a) (eb : b' = h ≫ b) : LBIso (M.pull a') (N.pull b') :=
  LBIso.chartPull (chartPullSame M _ _ _ h fun _ => ea) (chartPullSame N _ _ _ h fun _ => eb) H

theorem pull_right {M : LB Y} {N : LB X'} {b : Y ⟶ X'} (H : LBIso M (N.pull b)) (h : Z ⟶ Y)
    {b' : Z ⟶ X'} (eb : b' = h ≫ b) : LBIso (M.pull h) (N.pull b') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M h h rfl) (chartPullSame N _ _ _ h fun _ => eb) H

theorem pull_pull {M : LB X} {N : LB Z} {a : Y ⟶ X} {h : Z ⟶ Y} (H : LBIso (M.pull (h ≫ a)) N) :
    LBIso ((M.pull a).pull h) N :=
  LBIso.chartPull (chartPullLinComb M a (fun _ : PUnit => h) (fun _ => h ≫ a) (fun _ => 1) (𝟙 Z)
    fun _ => (Category.id_comp _).symm) (chartPullId N) H

theorem mono_jK (R : Type) [CommRing R] : Mono (jK R) := by
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  infer_instance

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

end GenericBundleDescent


open GenericBundleDescent in
theorem unif_bundle_generic_descent : ∀ (R W R₂ W₂ K' Ω' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] [CommRing W₂] [IsDomain W₂] [IsLocalRing W₂] [Field K'] [Field Ω'] (φ : R →+* W) (ρ : R →+* R₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂) (io : FractionRing R →+* K') (j : FractionRing W →+* Ω') (l : K' →+* Ω') (i : K' ≃+* FractionRing R₂) (j₂ : FractionRing W₂ →+* Ω'), Function.Injective φ → Function.Injective ρ → Function.Injective σ → Function.Injective φ₂ → φ₂.comp ρ = σ.comp φ → (∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r))) → (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) → (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) → (∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = l (i.symm (algebraMap R₂ _ r))) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (α : AW.A.left ⟶ A.A.left), IsGrpPullback GW G (spMap φ) βW → UW.gen.inv.left ≫ pullback.fst GW.hom (jK W) ≫ βW = α ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) → ∀ (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (p : pullback AW.A.hom (spMap j) ⟶ A₁.A.left), IsGrpPullback A₁.A A.A (spMap io) α₁ → p ≫ α₁ = pullback.fst _ _ ≫ α → p ≫ A₁.A.hom = pullback.snd _ _ ≫ spMap l → LBIso (AW.L.pull (pullback.fst AW.A.hom (spMap j))) (A₁.L.pull p) → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (q : A₂.A.left ⟶ A₁.A.left), IsGrpPullback G₂ G (spMap ρ) β → IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q → LBIso A₂.L (A₁.L.pull q) → gen₂.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) → ∀ (GW' : Over (Sp W₂)) [GrpObj GW'] [IsCommMonObj GW'] (βW' : GW'.left ⟶ G₂.left) (τ : GW'.left ⟶ GW.left) (DW' : DegData W₂ (maximalIdeal W₂)) (AW' : PolAV (Sp (FractionRing W₂))) (UW' : Unif (maximalIdeal W₂) DW' AW' GW') (κ : pullback GW'.hom (jK W₂) ⟶ pullback G₂.hom (jK R₂)), IsGrpPullback GW' G₂ (spMap φ₂) βW' → IsGrpPullback GW' GW (spMap σ) τ → βW' ≫ β = τ ≫ βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW' → LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) (UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)) → LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  intro R W R₂ W₂ K' Ω' _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ ρ σ φ₂ io j l i j₂ _ _ _ _ _ _ _ hj₂σ hj₂φ G _ _ A gen GW _ _ βW DW
    AW UW α _ hα A₁ α₁ p hA₁ hp₁ hp₂ hLp G₂ _ _ β A₂ gen₂ q _ hq hLq hgq GW' _ _ βW' τ DW' AW' UW' κ hβW' hτ hsq hκ hL
  have := mono_jK R
  have := mono_jK R₂
  let π := pullback.fst (pullback.snd GW'.hom (jK W₂)) (spMap j₂)
  let s := pullback.snd (pullback.snd GW'.hom (jK W₂)) (spMap j₂)
  have hπ : π ≫ pullback.fst GW'.hom (jK W₂) ≫ GW'.hom = s ≫ spMap j₂ ≫ jK W₂ := by
    rw [pullback.condition, pullback.condition_assoc]
  have e₁ : spMap j₂ ≫ jK W₂ ≫ spMap σ = spMap j ≫ jK W := by
    rw [sp_comp, sp_comp, sp_comp]
    exact congrArg spMap (RingHom.ext hj₂σ)
  have e₂ : spMap j₂ ≫ jK W₂ ≫ spMap φ₂ = spMap (l.comp i.symm.toRingHom) ≫ jK R₂ := by
    rw [sp_comp, sp_comp, sp_comp]
    exact congrArg spMap (RingHom.ext hj₂φ)
  have e₃ : spMap (l.comp i.symm.toRingHom) ≫ spMap i.toRingHom = spMap l := by
    rw [sp_comp]
    exact congrArg spMap (RingHom.ext fun x => by simp)
  obtain ⟨ℓ, hℓ₁, hℓ₂⟩ : ∃ ℓ : _ ⟶ pullback GW.hom (jK W),
      ℓ ≫ pullback.fst _ _ = π ≫ pullback.fst GW'.hom (jK W₂) ≫ τ ∧ ℓ ≫ pullback.snd _ _ = s ≫ spMap j :=
    ⟨pullback.lift _ _ (by
      rw [Category.assoc, Category.assoc, hτ.1.w, reassoc_of% hπ, e₁, Category.assoc]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have wW : UW.gen.hom.left ≫ AW.A.hom = pullback.snd GW.hom (jK W) := Over.w UW.gen.hom
  have w₂ : gen₂.hom.left ≫ A₂.A.hom = pullback.snd G₂.hom (jK R₂) := Over.w gen₂.hom
  let gW : pullback GW.hom (jK W) ⟶ AW.A.left := UW.gen.hom.left
  let g₂ : pullback G₂.hom (jK R₂) ⟶ A₂.A.left := gen₂.hom.left
  let gi : A.A.left ⟶ pullback G.hom (jK R) := gen.inv.left
  have wW' : gW ≫ AW.A.hom = pullback.snd GW.hom (jK W) := wW
  have w₂' : g₂ ≫ A₂.A.hom = pullback.snd G₂.hom (jK R₂) := w₂
  have hα' : gW ≫ α ≫ gi ≫ pullback.fst G.hom (jK R) = pullback.fst GW.hom (jK W) ≫ βW := by
    have c : UW.gen.hom.left ≫ UW.gen.inv.left = 𝟙 _ := congrArg Over.Hom.left UW.gen.hom_inv_id
    exact (congrArg (UW.gen.hom.left ≫ ·) hα.symm).trans (by rw [reassoc_of% c])
  have hgq' : g₂ ≫ q ≫ α₁ ≫ gi ≫ pullback.fst G.hom (jK R) = pullback.fst G₂.hom (jK R₂) ≫ β := by
    have c : gen₂.hom.left ≫ gen₂.inv.left = 𝟙 _ := congrArg Over.Hom.left gen₂.hom_inv_id
    exact (congrArg (gen₂.hom.left ≫ ·) hgq.symm).trans (by rw [reassoc_of% c])
  obtain ⟨n, hn₁, hn₂⟩ : ∃ n : _ ⟶ pullback AW.A.hom (spMap j),
      n ≫ pullback.fst _ _ = ℓ ≫ gW ∧ n ≫ pullback.snd _ _ = s :=
    ⟨pullback.lift _ _ (by rw [Category.assoc, wW', hℓ₂]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have : IsIso gi := inferInstanceAs (IsIso ((Over.forget _).map gen.inv))
  have hm : n ≫ p = π ≫ κ ≫ g₂ ≫ q := by
    refine hA₁.1.hom_ext ?_ ?_
    · rw [← cancel_mono gi, ← cancel_mono (pullback.fst G.hom (jK R))]
      simp only [Category.assoc]
      rw [reassoc_of% hp₁, reassoc_of% hn₁, hα', reassoc_of% hℓ₁, hgq', reassoc_of% hκ, hsq]
    · have k : π ≫ κ ≫ pullback.snd G₂.hom (jK R₂) = s ≫ spMap (l.comp i.symm.toRingHom) := by
        rw [← cancel_mono (jK R₂)]
        simp only [Category.assoc]
        rw [← pullback.condition, reassoc_of% hκ, hβW'.1.w, reassoc_of% hπ, e₂]
      simp only [Category.assoc]
      rw [hp₂, reassoc_of% hn₂, hq.1.w, reassoc_of% w₂', reassoc_of% k, e₃]
  have H₁ : LBIso (AW.L.pull (ℓ ≫ gW)) (UW.LG.L.pull (π ≫ pullback.fst GW'.hom (jK W₂) ≫ τ)) :=
    pull_both (a := gW) UW.ext ℓ rfl hℓ₁.symm
  have H₂ : LBIso (AW.L.pull (ℓ ≫ gW)) (A₁.L.pull (n ≫ p)) := pull_both hLp n hn₁.symm rfl
  have H₃ : LBIso (A₂.L.pull ((π ≫ κ) ≫ g₂)) (A₁.L.pull (n ≫ p)) :=
    pull_right hLq _ (by simp only [hm, Category.assoc])
  have hG := UW.LG.isLB
  have H : LBIso ((UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)).pull π) (((A₂.L.pull g₂).pull κ).pull π) :=
    pull_pull (pull_pull (pull_pull (LBIso.trans (pull_isLB A₂.isLB _) (pull_isLB A₁.isLB _) (pull_isLB hG _) H₃
      (LBIso.trans (pull_isLB A₁.isLB _) (pull_isLB AW.isLB _) (pull_isLB hG _) H₂.symm H₁)))).symm
  let g' : pullback GW'.hom (jK W₂) ⟶ AW'.A.left := UW'.gen.hom.left
  have : IsIso g' := inferInstanceAs (IsIso ((Over.forget _).map UW'.gen.hom))
  have w' : g' ≫ AW'.A.hom = pullback.snd GW'.hom (jK W₂) := Over.w UW'.gen.hom
  have := AW'.isAb.smooth
  have := AW'.isAb.proper
  have hc := AW'.isAb.geomConnected
  have hD := (lb_gen_iso_descend_field (FractionRing W₂) Ω' j₂ _ _ (pullback.snd GW'.hom (jK W₂)) s π
    (by rw [← w']; infer_instance) (by rw [← w']; infer_instance)
    (by rw [← w']; exact (MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso ⟨(Category.comp_id (g' ≫ AW'.A.hom)).symm⟩) hc))
    (IsPullback.of_hasPullback _ _)).2 _ _ (pull_isLB hG _) (pull_isLB (pull_isLB A₂.isLB _) _) H
  exact LBIso.trans (pull_isLB UW'.LG.isLB _) (pull_isLB hG _) (pull_isLB (pull_isLB A₂.isLB _) _) hL hD

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationCompleteTraitBaseChangeFiniteExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem unif_trait_baseChange : ∀ (R R₂ W W₂ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing W₂] [IsDomain W₂] [IsLocalRing W₂] (ρ : R →+* R₂) (φ : R →+* W) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂), Base R → GlobalTheory.LN.CDvr W → GlobalTheory.LN.CDvr W₂ → FinExt σ → IsLocalHom σ → φ₂.comp ρ = σ.comp φ → Function.Injective φ₂ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left), IsGrpPullback G₂ G (spMap ρ) β → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left), IsGrpPullback GW G (spMap φ) βW → ∀ (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), ∃ (GW' : Over (Sp W₂)) (_ : GrpObj GW') (_ : IsCommMonObj GW') (βW' : GW'.left ⟶ G₂.left) (τ : GW'.left ⟶ GW.left) (DW' : DegData W₂ (maximalIdeal W₂)) (AW' : PolAV (Sp (FractionRing W₂))) (UW' : Unif (maximalIdeal W₂) DW' AW' GW') (κ : pullback GW'.hom (jK W₂) ⟶ pullback G₂.hom (jK R₂)), IsGrpPullback GW' G₂ (spMap φ₂) βW' ∧ IsGrpPullback GW' GW (spMap σ) τ ∧ βW' ≫ β = τ ≫ βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW' ∧ LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) (UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)) := by
  intro R R₂ W W₂ _ _ _ _ _ _ _ _ _ _ _ _ ρ φ σ φ₂ _ hW hW₂ hσ hloc hc hφ₂ G _ _ hG G₂ _ _ β hβ GW _ _ βW hβW DW AW UW
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have := hW.1
  have hWa : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hGW : IsSemiAbelian GW := by
    obtain ⟨e, he, -⟩ := grpPullback_iso hβW (isGrpPullback_pullback G (spMap φ))
    exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback _ G hG)
  obtain ⟨D₁, hX, A₁, U₁, hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hWa hσ.1 σ hσ.2.1 (map_maximalIdeal_le σ) hGW UW
  have hτ : IsGrpPullback ((Over.pullback (specOf σ)).obj GW) GW (spMap σ) (pullback.fst GW.hom (specOf σ)) :=
    isGrpPullback_pullback GW (specOf σ)
  have hb : spMap σ ≫ spMap φ = spMap φ₂ ≫ spMap ρ := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  have hn := (hτ.comp hβW).congr hb rfl
  have hw : (pullback.fst GW.hom (specOf σ) ≫ βW) ≫ G.hom =
      (((Over.pullback (specOf σ)).obj GW).hom ≫ spMap φ₂) ≫ spMap ρ := by
    rw [hn.1.w]; exact (Category.assoc _ _ _).symm
  have h₁ := hβ.1.lift_fst _ _ hw
  have h₂ := hβ.1.lift_snd _ _ hw
  have hβ' : IsGrpPullback ((Over.pullback (specOf σ)).obj GW) G₂ (spMap φ₂) (hβ.1.lift _ _ hw) :=
    hβ.cancel (hn.congr rfl h₁.symm) h₂
  have hsq : jK W₂ ≫ spMap φ₂ =
      spMap (IsFractionRing.map (K := FractionRing R₂) (L := FractionRing W₂) hφ₂) ≫ jK R₂ := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [IsFractionRing.map, IsLocalization.map_eq]
  have cond : (pullback.fst ((Over.pullback (specOf σ)).obj GW).hom (jK W₂) ≫ hβ.1.lift _ _ hw) ≫ G₂.hom =
      (pullback.snd ((Over.pullback (specOf σ)).obj GW).hom (jK W₂) ≫
        spMap (IsFractionRing.map (K := FractionRing R₂) (L := FractionRing W₂) hφ₂)) ≫ jK R₂ := by
    rw [Category.assoc, h₂, ← Category.assoc, pullback.condition, Category.assoc, hsq, Category.assoc]
  refine ⟨(Over.pullback (specOf σ)).obj GW, inferInstance, inferInstance, hβ.1.lift _ _ hw,
    pullback.fst GW.hom (specOf σ), D₁, A₁, U₁, pullback.lift _ _ cond, hβ', hτ, h₁, pullback.lift_fst _ _ _, ?_⟩
  obtain ⟨wL, hwL, -⟩ := hP.lg
  exact LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull U₁.LG.L _ _ rfl)
    (chartPullSame UW.LG.L _ (fun _ => (Iso.refl ((Over.pullback (specOf σ)).obj GW)).hom.left ≫
      pullback.fst GW.hom (specOf σ)) _ _ fun _ => by
        exact congrArg (_ ≫ ·) (Category.id_comp _).symm) ⟨wL, hwL⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelBaseChangeCompleteDvrExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedModel_baseChange_complete_dvr_extension : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsDiscreteValuationRing V₂] [Algebra (FractionRing V₂) (PadicAlgCl p)], IsAdicComplete (IsLocalRing.maximalIdeal V₂) V₂ → (∀ x : FractionRing V₂, ‖algebraMap (FractionRing V₂) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V₂ (FractionRing V₂))) → ∀ σ : FractionRing u.V →+* FractionRing V₂, (algebraMap (FractionRing V₂) (PadicAlgCl p)).comp σ = algebraMap (FractionRing u.V) (PadicAlgCl p) →
  ∃ (u' : ρ.UTest p y₀) (τ : FractionRing V₂ →+* FractionRing u'.V) (e : u'.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)),
    (algebraMap (FractionRing u'.V) (PadicAlgCl p)).comp τ = algebraMap (FractionRing V₂) (PadicAlgCl p) ∧
    (∀ χ r, u.PsiNorm (e χ) r → u'.PsiNorm χ r) ∧
    (∀ x, (T x).left ≫ u.φ = x.left ≫ u'.φ) ∧
    (∀ (m : ℕ) (pk' : QkPt u'.D.toPre (PadicAlgCl p) m) x', 1 ≤ m → QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk'.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x')) ∧
    (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk' : QkPt u'.D.toPre (PadicAlgCl p) m, e pk'.y = pk.y ∧ QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' (T.symm x)) := by
  first | exact @GlobalTheory.Poinc.UTestBaseChange.baseChange | exact GlobalTheory.Poinc.UTestBaseChange.baseChange | (intros; apply GlobalTheory.Poinc.UTestBaseChange.baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedSemiAbelianSplitModMaximalIdeal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SplitRed

theorem splitOver_of_unif : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))), Unif (maximalIdeal V₁) D₀ A₀ G₀ → IsSemiAbelian G₀ → GlobalTheory.LN.SplitOver G₀ (maximalIdeal V₁) := by
  intro V₁ _ _ _ _ D₀ G₀ _ _ A₀ U _
  obtain ⟨E, -, -, -, -, hE⟩ := GlobalTheory.gtCoord_isGt V₁ (IsLocalRing.maximalIdeal V₁) D₀.toPre 0 G₀ ⟨U.gt 0⟩
  have key : ∀ J : Ideal V₁, J = IsLocalRing.maximalIdeal V₁ →
      ∀ S : SplitExt (Spec (CommRingCat.of (V₁ ⧸ J))),
        S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G₀) →
        GlobalTheory.LN.SplitOver G₀ (IsLocalRing.maximalIdeal V₁) := by
    rintro J rfl S hS
    exact ⟨S, hS⟩
  exact key _ (pow_one _) E hE

end GlobalTheory.SplitRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformiserZpowMulUnitExponentUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformiser_zpow_mul_unit_exponent_unique : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}, Irreducible ϖ → ∀ (a b : ℤ) (w w' : Vˣ), algebraMap V (FractionRing V) ϖ ^ a * algebraMap V (FractionRing V) (w : V) = algebraMap V (FractionRing V) ϖ ^ b * algebraMap V (FractionRing V) (w' : V) → a = b := by
  first | exact @GlobalTheory.exponent_uniformiser_unique | exact GlobalTheory.exponent_uniformiser_unique | (intros; apply GlobalTheory.exponent_uniformiser_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValSectionUnit
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.UnitValuedLeadingSection

variable (R : Type) [CommRing R] [IsDomain R]

def thK (z : (TK R).left) : FractionRing R →+* (TK R).left.presheaf.stalk z :=
  ((TK R).left.presheaf.germ ⊤ z trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom

def uK (z : (TK R).left) : Rˣ →* ((TK R).left.presheaf.stalk z)ˣ :=
  Units.map ((thK R z).comp (algebraMap R (FractionRing R))).toMonoidHom

variable {R}

def TopGood (P : PolAV (Spec (CommRingCat.of R))) (z : (TK R).left) (J : ((TK R).left ⟶ P.A.left) → P.L.ι) : Prop :=
  Good P.L z J ∧ ∀ x : Spec (CommRingCat.of R) ⟶ P.A.left, x ≫ P.A.hom = 𝟙 _ → x ⁻¹ᵁ P.L.U (J (jK R ≫ x)) = ⊤

theorem gm_top_unit {R : Type} [CommRing R] [IsDomain R] (V : (Spec (CommRingCat.of R)).Opens) (hV : V = ⊤)
    (v : Γ(Spec (CommRingCat.of R), V)ˣ) (z : (TK R).left) : ∃ u : Rˣ, gm (jK R) z V v = uK R z u := by
  subst hV
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom v, Units.ext ?_⟩
  have hz : jK R z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) := trivial
  simp only [gm, dif_pos hz]
  have e := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (v : Γ(Spec (CommRingCat.of R), ⊤))))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  simp [uK, thK, pullU]
  rw [CommRingCat.hom_ofHom] at e
  have hv : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (v : Γ(Spec (CommRingCat.of R), ⊤))) = v := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  rw [e, hv]
  rfl

theorem val_section_unit {R : Type} [CommRing R] [IsDomain R] (P : PolAV (Spec (CommRingCat.of R)))
    (z : (TK R).left) (J : ((TK R).left ⟶ P.A.left) → P.L.ι) (hJ : TopGood P z J) {Y : Scheme.{0}} {K : Type}
    [Fintype K] {φ : K → (Y ⟶ P.A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb P.L φ ε))
    (q : Spec (CommRingCat.of R) ⟶ Y) (hq : ∀ k, (q ≫ φ k) ≫ P.A.hom = 𝟙 _) :
    ∃ u : Rˣ, val t (jK R ≫ q) z J = uK R z u := by
  have htop : q ⁻¹ᵁ LB.wchart P.L φ (fun k => J ((jK R ≫ q) ≫ φ k)) = ⊤ := by
    refine eq_top_iff.2 fun p _ => Set.mem_iInter.2 fun k => ?_
    have h := hJ.2 (q ≫ φ k) (hq k)
    have : p ∈ (q ≫ φ k) ⁻¹ᵁ P.L.U (J (jK R ≫ q ≫ φ k)) := by rw [h]; trivial
    show q p ∈ (φ k) ⁻¹ᵁ P.L.U (J ((jK R ≫ q) ≫ φ k))
    rw [Category.assoc]
    exact this
  have hz : q (jK R z) ∈ LB.wchart P.L φ (fun k => J ((jK R ≫ q) ≫ φ k)) := by
    have : jK R z ∈ q ⁻¹ᵁ LB.wchart P.L φ (fun k => J ((jK R ≫ q) ≫ φ k)) := by rw [htop]; trivial
    exact this
  obtain ⟨u, hu⟩ := gm_top_unit _ htop (pullU q _ (t.s (fun k => J ((jK R ≫ q) ≫ φ k)))) z
  exact ⟨u, (gm_pull (jK R) q z _ hz _).symm.trans hu⟩

theorem exists_topGood (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (P : PolAV (Spec (CommRingCat.of R)))
    (z : (TK R).left) : ∃ J, TopGood P z J := by
  classical
  haveI : IsProper P.A.hom := P.isAb.proper
  haveI : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
    (algebraMap R (FractionRing R))).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
      exact bot_le)⟩
  have hext : ∀ x x' : Spec (CommRingCat.of R) ⟶ P.A.left, x ≫ P.A.hom = 𝟙 _ → x' ≫ P.A.hom = 𝟙 _ →
      jK R ≫ x = jK R ≫ x' → x = x' := fun x x' hx hx' h =>
    ext_of_isDominant_of_isSeparated P.A.hom (hx.trans hx'.symm) (jK R) h
  choose top htop using fun x : Spec (CommRingCat.of R) ⟶ P.A.left =>
    ReciprocityTheory.ChartRestriction.G.DVR.GC.exists_chart_top P.L P.isLB x
  choose d hd using fun φ : (TK R).left ⟶ P.A.left => exists_chart P.isLB (φ z)
  refine ⟨fun φ => if h : ∃ x, x ≫ P.A.hom = 𝟙 _ ∧ jK R ≫ x = φ then top h.choose else d φ,
    fun φ => ?_, fun x hx => ?_⟩
  · by_cases h : ∃ x, x ≫ P.A.hom = 𝟙 _ ∧ jK R ≫ x = φ
    · simp only [dif_pos h]
      have m : jK R z ∈ h.choose ⁻¹ᵁ P.L.U (top h.choose) := by rw [htop]; trivial
      have m' : (jK R ≫ h.choose) z ∈ P.L.U (top h.choose) := m
      rwa [h.choose_spec.2] at m'
    · simp only [dif_neg h]; exact hd φ
  · have h : ∃ x', x' ≫ P.A.hom = 𝟙 _ ∧ jK R ≫ x' = jK R ≫ x := ⟨x, hx, rfl⟩
    simp only [dif_pos h]
    rw [hext _ _ h.choose_spec.1 hx h.choose_spec.2]
    exact htop x

end GlobalTheory.Mum.UnitValuedLeadingSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartDependsOnLabelMod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSum


set_option maxHeartbeats 1000000 in
theorem part_eq_of_congMod : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → ∀ a a' ν ν' κ, yy a = QuotientAddGroup.mk ν → yy a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → GSum.part D z₁ z₂ a κ = GSum.part D z₁ z₂ a' κ := by
  intro g n F W Z i X₁ hg hn hodd hi hE hT hP ε₁ hd D z₁ z₂ hq p _ c y h hy yy hl a a' ν ν' κ ha ha' hc
  subst hy
  obtain ⟨hon, hker⟩ := GlobalTheory.Poinc.isLab_onto_and_ker g n F W Z i D.X hg hn hodd hi hE hT D.proj D.ε D.diag p
    (y (cPt p)) (D.lift c y h) yy hl
  obtain ⟨w, hw⟩ := hc
  obtain ⟨b, hb⟩ := hon (QuotientAddGroup.mk w)
  have hk : a - a' - D.m • b ∈ D.X.S.HH D.X.M (y (cPt p)) := by
    rw [← hker, AddMonoidHom.mem_ker]
    have e1 : yy (a - a' - D.m • b) = yy a - yy a' - D.m • yy b := by
      rw [map_sub, map_sub, map_nsmul]
    rw [e1, ha, ha', hb, hw]
    show ((QuotientAddGroup.mk (ν' + D.m • w) - QuotientAddGroup.mk ν' - D.m • QuotientAddGroup.mk w :
      ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X))) = 0
    rw [← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_sub, ← QuotientAddGroup.mk_sub]
    simp
  have hw' : wtChar D (D.X.S.TT D.X.M (y (cPt p))) a = wtChar D (D.X.S.TT D.X.M (y (cPt p))) a' := by
    ext t
    have ht : eStdBilin D.X.S.g _ (t : D.X.S.Gam) (a - a' - D.m • b) = 0 := t.2 _ hk
    have hsplit : D.m • a = D.m • a' + (D.m * D.m) • b + D.m • (a - a' - D.m • b) := by
      rw [mul_nsmul', ← smul_add, ← smul_add]
      congr 1
      abel
    have key : eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a) =
        eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a') + (D.m * D.m) • eStd D.X.S.g _ (t : D.X.S.Gam) b := by
      rw [hsplit]
      simp only [← eStdBilin_apply, map_add (f := _), map_nsmul, ht, smul_zero, add_zero]
    have hN : ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N)
        ((D.m * D.m) • eStd D.X.S.g _ (t : D.X.S.Gam) b) = 0 := by
      rw [map_nsmul, ← sq, ← D.sq, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    show ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N) (eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a)) =
      ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N) (eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a'))
    rw [key, map_add (f := _), hN, add_zero]
  simp only [part, hw']

end GlobalTheory.Poinc.GSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveRegularStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_eigen_bijective_regular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) →
    ∀ d' d₁' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = M.co.e x) → (∀ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d₁'.e xᵀ = M₁.co.e x) →
      HasDbl (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) d' d₁' T := by
  first | exact @GlobalTheory.DblTransp.main | exact GlobalTheory.DblTransp.main | (intros; apply GlobalTheory.DblTransp.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingConditionLocusIsClopenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_condition_locus_isClopen : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Z : Over S) (t₁ : Z.left ⟶ Sp (cycAway M)) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ (β : cycAway M →+* k) (z : kˣ), x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) → ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e c) (unitOn (z ^ (2 * omegaStd a c)))) := by
  first | (exact @GlobalTheory.HTWeilLocus.weil_locus_clopen) | (exact GlobalTheory.HTWeilLocus.weil_locus_clopen) | (intros; apply GlobalTheory.HTWeilLocus.weil_locus_clopen  <;> assumption)
end

