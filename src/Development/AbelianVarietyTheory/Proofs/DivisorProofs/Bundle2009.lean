module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatTransverseLagrangia
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalGoodPlaceEquivariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalUnramifiedVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalLocalUniqueness
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1949
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0540
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoConstOfGenericIsoDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenericIsoConst

theorem lbIso_of_generic : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (P M : LB G.left), P.IsLB → M.IsLB → LBIso (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) → LBIso P M := by
  intro W K' _ _ _ _ _ _ G _ hG P M hP hM h
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  haveI : GeometricallyIntegral G.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ G.hom inferInstance inferInstance
  let ψ : K' ≃ₐ[W] FractionRing W := IsLocalization.algEquiv (nonZeroDivisors W) K' (FractionRing W)
  have e₂ : Out.jK W ≫ 𝟙 _ = spMap (ψ : K' →+* FractionRing W) ≫ spMap (algebraMap W K') := by
    have hr : (ψ : K' →+* FractionRing W).comp (algebraMap W K') = algebraMap W (FractionRing W) := by
      ext x; simp
    rw [Category.comp_id, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hr]
  have h' : LBIso (P.pull (pullback.fst G.hom (Out.jK W))) (M.pull (pullback.fst G.hom (Out.jK W))) :=
    GlobalTheory.GenericSpread.lbIso_pull_of_comp
      (pullback.map G.hom (Out.jK W) G.hom (spMap (algebraMap W K')) (𝟙 _) (spMap (ψ : K' →+* FractionRing W)) (𝟙 _)
        (by simp) e₂) ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm h
  exact GlobalTheory.lbIso_of_generic_normal_local W inferInstance inferInstance G.left G.hom (eSec G) inferInstance inferInstance
    inferInstance (Over.w η[G]) P M hP hM h'


open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh TopologicalSpace Opposite in
theorem globalFn_eq_cst : ∀ (W K' : Type) [CommRing W] [Field K'] [Algebra W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ f : Γ(pullback G.hom (spMap (algebraMap W K')), ⊤), ∃ c : K', f = GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ c := by
  intro W K' _ _ _ G _ hG f
  have hU := GlobalTheory.AbCoh.uConst_of_isAbelianScheme W G hG K' (pullback G.hom (spMap (algebraMap W K')))
    (pullback.snd G.hom (spMap (algebraMap W K'))) (pullback.fst G.hom (spMap (algebraMap W K')))
    (IsPullback.of_hasPullback _ _)
  let g : C0 (OAff (pullback.snd G.hom (spMap (algebraMap W K')))) := fun T =>
    ((pullback G.hom (spMap (algebraMap W K'))).presheaf.map (homOfLE le_top).op).hom f
  have hg : d0 _ g = 0 := by
    funext T T' φ
    rw [amitsur_d0_apply]
    rw [Pi.zero_apply, Pi.zero_apply, Pi.zero_apply, sub_eq_zero]
    exact Sec.res_res (pullback.snd G.hom (spMap (algebraMap W K'))) le_top (leOfHom φ.unop) f
  obtain ⟨r, hr, -⟩ := hU g hg
  refine ⟨r, TopCat.Presheaf.section_ext (pullback G.hom (spMap (algebraMap W K'))).sheaf ⊤ _ _ fun x hx => ?_⟩
  obtain ⟨U, hUa, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp (pullback G.hom (spMap (algebraMap W K'))).isBasis_affineOpens hx
  have e1 : ((pullback G.hom (spMap (algebraMap W K'))).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom f =
      ((pullback G.hom (spMap (algebraMap W K'))).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
        (GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ r) := by
    refine (hr (op ⟨U, hUa⟩)).trans ?_
    show _ = GlobalTheory.AbLaw.rs _ (le_top : U ≤ ⊤) (GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ r)
    rw [GlobalTheory.AbLaw.rs_cst]
    rfl
  have h1 := TopCat.Presheaf.germ_res_apply (pullback G.hom (spMap (algebraMap W K'))).presheaf (homOfLE (le_top : U ≤ ⊤)) x hxU f
  have h2 := TopCat.Presheaf.germ_res_apply (pullback G.hom (spMap (algebraMap W K'))).presheaf (homOfLE (le_top : U ≤ ⊤)) x hxU
    (GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ r)
  exact h1.symm.trans ((congrArg _ e1).trans h2)

theorem exists_iso_const_of_generic : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (P M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), w.IsGen → w₁.IsGen → ∃ (v : LB.Iso P M) (c : K'), v.IsGen ∧ ∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ pullback.fst G.hom (spMap (algebraMap W K')) ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) _ c * ((pullback.fst G.hom (spMap (algebraMap W K'))).appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m)) (w.s (n, fun _ => m)).val := by
  intro W K' _ _ _ _ _ _ G _ hG P M N hP hM hN w w₁ hw hw₁
  have hP' := pull_isLB hP (pullback.fst G.hom (spMap (algebraMap W K')))
  have hM' := pull_isLB hM (pullback.fst G.hom (spMap (algebraMap W K')))
  obtain ⟨v, hv⟩ := lbIso_of_generic W K' G hG P M hP hM (LBIso.trans hP' hN hM' ⟨w₁, hw₁⟩ (LBIso.symm ⟨w, hw⟩))
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.GenIsoRatio.ratio _ _ _ P M N hP hM hN w w₁ v hw hw₁ hv
  obtain ⟨c, hc⟩ := globalFn_eq_cst W K' G hG u.val
  refine ⟨v, c, hv, fun n i m hle => ?_⟩
  rw [hu n i m hle, hc, GlobalTheory.AbLaw.rs_cst]

end GlobalTheory.GenericIsoConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearModelIntertwinerGoodSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LinBarExist

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem locCo_form {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x u : W) :
    (GlobalTheory.LatVac.locCo co v x).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v u).2 -
      (GlobalTheory.LatVac.locCo co v u).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v x).2 = evFin F v (B x u) := by
  rw [co.form]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul, map_sub]

theorem locCo_surj {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (w : (κ → Fv F v) × (κ → Fv F v)) : ∃ u : W, At (evFin F v) u ∧ GlobalTheory.LatVac.locCo co v u = w := by
  refine ⟨co.e.symm (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)), ?_, ?_⟩
  · intro a ha
    rw [← LinearEquiv.map_smul, ← co.e.symm.map_zero]
    congr 1
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
  · refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
      simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]

theorem at_symp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (AE F E)) (JB : Matrix (Fin d) (Fin d) (AE F E)) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)}
    (x u : Matrix (Fin n) (Fin d) (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) (symp (R := AF F) (cA σ) (-1) JA JB x u) := by
  intro a ha
  have h := GlobalTheory.LatVac.symp_smul_smul σ JA JB (-1) a 1 x u
  rw [hx a ha, one_smul, mul_one, GlobalTheory.VacIndic.symp_zero_left] at h
  rw [smul_eq_mul]
  exact h.symm

theorem exists_isLinBar : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om'),
    ∃ ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ), Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι := by
  intro D a a' Bs Γ X om om' hTr
  obtain ⟨uT, uM, hT, hM, hspan, hsymp⟩ := GlobalTheory.T.exists_unipotent_maps_for_theta_triple Bs Γ X om om' hTr
  have hψc : Continuous (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) := GlobalTheory.VacAny.continuous_psiV hTr.base.std.1 Bs.v₁
  have hunr : PsiUnr Bs.ψ Bs.v₁ := GlobalTheory.BaseGoodPlace.psiUnr_of_not_le
    (GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hTr.base.std) Bs.v₁
    (GlobalTheory.SplitFullyUnr.not_le_differentIdeal Bs.v₁ hTr.chars.good.2)
  have hunr' : ∀ x : Fv D.host.F Bs.v₁, (∀ y ∈ 𝒪[Fv D.host.F Bs.v₁], GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (x * y) = 1) ↔
      x ∈ 𝒪[Fv D.host.F Bs.v₁] := by
    intro x
    simp only [GlobalTheory.FinPl.SplitPoint.mem_integer_iff]
    exact hunr x
  have hcoM : ∀ z, GlobalTheory.VacShape.coBar Bs Γ (uM z) = 0 := fun z => by
    unfold GlobalTheory.VacShape.coBar
    rw [(hM z).2.1]
    simp
  haveI : CharZero (Fv D.host.F Bs.v₁) := charZero_of_injective_algebraMap (algebraMap D.host.F _).injective
  obtain ⟨ι, hbij, htr, hmu⟩ := _root_.GlobalTheory.StoneVN.intertwiner_matrix (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) hψc hunr'
    ((GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁).comp uT) ((GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁).comp uM)
    (fun Y Y' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hT Y).1 (hT Y').1, (hT Y).2.1, (hT Y').2.1]
      simp)
    (fun z z' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hM z).1 (hM z').1, hcoM, hcoM]
      simp)
    (fun Y z => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hT Y).1 (hM z).1, (hT Y).2.1, (hT Y).2.2, (hM z).2.2, hcoM]
      simp)
    (fun w => by
      obtain ⟨u, hu, rfl⟩ := locCo_surj Γ.M'.co Bs.v₁ w
      obtain ⟨Y, z, rfl⟩ := hspan u hu
      exact ⟨Y, z, by simp only [AddMonoidHom.comp_apply, map_add (f := _)]⟩)
  have hφ₁ : ∀ (u : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E)), At (evFin D.host.F Bs.v₁) u →
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁, Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ u) φ φ₁ →
        φ₁ = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ u) φ :=
    fun u hu φ hφ φ₁ hact => GlobalTheory.TensUniq.eq_of_tens_eq Bs.v₁ φ φ₁ _ hφ fun r hr =>
      (hact r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo Γ.M'.co Bs.ψ Bs.v₁ u hu φ r hr)
  refine ⟨ι, hbij, ?_, ?_⟩
  · intro u hu hu0 φ hφ φ₁ _ hact Y
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hz : z = 0 := by
      have h := hu0
      rw [Matrix.map_add _ (map_add _), (hT Y₀).2.1, (hM z).2.2, zero_add, neg_eq_zero] at h
      exact h
    subst hz
    rw [map_zero, add_zero] at e1 ⊢
    show ι φ₁ Y = ι φ (Y + GlobalTheory.VacShape.coBar Bs Γ (uT Y₀))
    rw [(hT Y₀).2.2, e1]
    exact congrFun (htr Y₀ φ hφ) Y
  · intro u hu hu1 φ hφ φ₁ _ hact x hx hx0
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hY : Y₀ = 0 := by
      have h := hu1
      rw [Matrix.map_add _ (map_add _), (hM z).2.1, add_zero] at h
      rw [← (hT Y₀).2.2]
      unfold GlobalTheory.VacShape.coBar
      rw [h]
      simp
    subst hY
    rw [map_zero, zero_add] at e1 ⊢
    show ι φ₁ (GlobalTheory.VacShape.coBar Bs Γ x) = _ * ι φ (GlobalTheory.VacShape.coBar Bs Γ x)
    rw [e1, GlobalTheory.VacIndic.psi_of_at Bs.ψ (at_symp _ _ _ x (uM z) hx), hsymp x (uM z) hx (hM z).1, hx0, hcoM,
      (hM z).2.2]
    have h2 := congrFun (hmu z φ hφ) (GlobalTheory.VacShape.coBar Bs Γ x)
    simp only [AddMonoidHom.comp_apply] at h2
    rw [h2, ← GlobalTheory.LatVac.psiAt_apply]
    congr 2
    simp [Finset.sum_neg_distrib]

end GlobalTheory.LinBarExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalCharactersLinearBar
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.WeilLinA

theorem omA_h_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D : Type}
    [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν β : kˣ →* ℂˣ) (g : GL A k) (Φ : Matrix A D k → ℂ) :
    GlobalTheory.SplitFlip.omA ν β g 1 Φ = GlobalTheory.SplitFlip.omA ν 1 g 1 Φ := by
  funext X; simp [GlobalTheory.SplitFlip.omA]

theorem omA_g_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D : Type}
    [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν β : kˣ →* ℂˣ) (h : GL D k) (Φ : Matrix A D k → ℂ) :
    GlobalTheory.SplitFlip.omA ν β 1 h Φ = GlobalTheory.SplitFlip.omA 1 β 1 h Φ := by
  funext X; simp [GlobalTheory.SplitFlip.omA]

theorem one_mem_UAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (Y : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev := by
  intro u _
  simp [mat]

theorem isSmoothChar_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ : kˣ →* ℂˣ) (h : GlobalTheory.SmGL.IsSmoothChar χ) : GlobalTheory.SmGL.IsSmoothChar χ⁻¹ := by
  have e : (χ⁻¹).ker = χ.ker := by ext x; simp [MonoidHom.mem_ker]
  unfold GlobalTheory.SmGL.IsSmoothChar at h ⊢
  rw [e]; exact h

theorem isUnitaryChar_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ : kˣ →* ℂˣ) (h : GlobalTheory.SmGL.IsUnitaryChar χ) : GlobalTheory.SmGL.IsUnitaryChar χ⁻¹ := by
  intro x
  have := h x
  simp [this]

theorem localOps_eq_omA : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∃ (ν₀ β₀ : (Fv F v)ˣ →* ℂˣ) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)),
      (∃ t : E →ₐ[F] Fv F v, ν₀ = chrW X.ν t ∨ ν₀ = (chrW X.ν t)⁻¹) ∧
      GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧ GlobalTheory.SmGL.IsSmoothChar β₀ ∧ GlobalTheory.SmGL.IsUnitaryChar β₀ ∧
      Set.BijOn ι (SB (Fin a × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) : Set _) ∧
      (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ →
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ g' 1 (ι φ)) ∧
      (∀ g' : GL (Fin a) (Fv F v), ∃ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ g' 1 (ι φ)) ∧
      (∀ h' : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ β₀ 1 h' (ι φ)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hv
  obtain ⟨t, ι, hι⟩ := _root_.GlobalTheory.LinWAt.exists_isLinW hP F E σ B a a' G X om om' hTr v hv
  obtain ⟨ν₀, hV⟩ := _root_.GlobalTheory.SchurCharV.exists_char_of_schur hP F E σ B a a' G X om om' hTr v hv t ι hι (_root_.GlobalTheory.ShapeUV.shapeV hP F E σ B a a' G X om om' hTr v hv t ι hι)
  obtain ⟨t', ht'⟩ := _root_.GlobalTheory.MixedForm.char_eq_local hP F E σ B a a' G X om om' hTr v hv t ι hι ν₀ hV
  obtain ⟨β₀, hW⟩ := _root_.GlobalTheory.LocalUnitSubgroupClosure.linear_weil_functional_character_weight_zero hP F E σ B a a' G X om om' hTr v hv t ι hι (_root_.GlobalTheory.UnitWShape.shape hP F E σ B a a' G X om om' hTr v hv t ι hι)
  obtain ⟨hβs, hβu⟩ := _root_.GlobalTheory.WeilLinW.charW_smooth_unitary hP F E σ B a a' G X om om' hTr v hv t ι hι β₀ hW
  obtain ⟨hs, hu⟩ := _root_.GlobalTheory.ChrWSmooth.chrW_nu_smooth_unitary hP F E σ B a a' G X om om' hTr v hv t'
  have hνs : GlobalTheory.SmGL.IsSmoothChar ν₀ := by
    rcases ht' with h | h
    · rw [h]; exact hs
    · rw [h]; exact isSmoothChar_inv _ hs
  have hνu : GlobalTheory.SmGL.IsUnitaryChar ν₀ := by
    rcases ht' with h | h
    · rw [h]; exact hu
    · rw [h]; exact isUnitaryChar_inv _ hu
  have hloc := ((GlobalTheory.T.theta_action_exists hP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hTr).1 v).1
  refine ⟨ν₀, β₀, ι, ⟨t', ht'⟩, hνs, hνu, hβs, hβu, hι.bij, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', -, hg'⟩ := hV g hg
    exact ⟨g', fun φ hφ φ₁ hφ₁ hA => by rw [hg' φ hφ φ₁ hφ₁ hA, omA_h_one ν₀ β₀]⟩
  · intro g'
    obtain ⟨g, hg, hgt⟩ := _root_.GlobalTheory.SurjAtPlaceV.surj_at_place hP F E σ B a a' G X om om' hTr v hv t g'
    refine ⟨g, hg, fun φ hφ => ?_⟩
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc g hg 1 (one_mem_UAt σ G.W _) φ hφ
    obtain ⟨g'', hg'', hgeq⟩ := hV g hg
    have : g'' = g' := Units.ext (hg''.symm.trans hgt)
    subst this
    exact ⟨φ₁, hφ₁, hA, by rw [hgeq φ hφ φ₁ hφ₁ hA, omA_h_one ν₀ β₀]⟩
  · intro h'
    obtain ⟨h, hh, hht⟩ := _root_.GlobalTheory.SkewLevi.surj_at_place hP F E σ B a a' G X om om' hTr v hv t h'
    refine ⟨h, hh, fun φ hφ => ?_⟩
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc 1 (one_mem_UAt σ G.V _) h hh φ hφ
    obtain ⟨h'', hh'', hheq⟩ := hW h hh
    have : h'' = h' := Units.ext (hh''.symm.trans hht)
    subst this
    exact ⟨φ₁, hφ₁, hA, by rw [hheq φ hφ φ₁ hφ₁ hA, omA_g_one ν₀ β₀]⟩

end GlobalTheory.WeilLinA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivationExtensionBasicOpen
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogDerLoc

def dualHom {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (D : Derivation ℤ A A) :
    A →+* TrivSqZeroExt B B where
  toFun r := TrivSqZeroExt.inl (φ r) + TrivSqZeroExt.inr (φ (D r))
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · simp
    · simp [D.leibniz, mul_comm, -DualNumber.inr_eq_smul_eps]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [-DualNumber.inr_eq_smul_eps]

theorem exists_extension {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (f : A) [IsLocalization.Away f B]
    (D : Derivation ℤ A A) : ∃ E : Derivation ℤ B B, ∀ r, E (algebraMap A B r) = algebraMap A B (D r) := by
  have hu : IsUnit (dualHom (algebraMap A B) D f) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
      simpa [dualHom] using IsLocalization.Away.algebraMap_isUnit (S := B) f)
  let L : B →+* TrivSqZeroExt B B := IsLocalization.Away.lift f hu
  have hfst : ∀ x, (L x).fst = x := fun x => by
    have : (TrivSqZeroExt.fstHom B _ _).toRingHom.comp L = RingHom.id _ := by
      refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun r => ?_)
      simp [L, dualHom]
    exact congr($this x)
  let e : B →+ B :=
    { toFun := fun x => (L x).snd
      map_zero' := by rw [map_zero, TrivSqZeroExt.snd_zero]
      map_add' := fun x y => by rw [map_add (f := _), TrivSqZeroExt.snd_add] }
  refine ⟨Derivation.mk' e.toIntLinearMap fun x y => ?_, fun r => ?_⟩
  · change (L (x * y)).snd = x • (L y).snd + y • (L x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [mul_comm]
  · change (L (algebraMap A B r)).snd = _
    simp [L, dualHom, -DualNumber.inr_eq_smul_eps]

theorem map_mem_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (D : Derivation ℤ A A)
    (E : Derivation ℤ B B) (h : ∀ r, E (φ r) = φ (D r)) (J : Ideal A) (hJ : ∀ g ∈ J, D g ∈ J) :
    ∀ x ∈ J.map φ, E x ∈ J.map φ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [h]
    exact Ideal.mem_map_of_mem φ (hJ g hg)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x hx hE =>
    rw [smul_eq_mul, E.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ a hE) (Ideal.mul_mem_right _ _ hx)

theorem exists_logDer_basicOpen : ∀ (X : Scheme.{0}) (K : Type) [CommRing K] (s : X ⟶ Sp K) (I : X.IdealSheafData) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ Dl ∈ GlobalTheory.LogKS.logDer s I U, ∃ DlW ∈ GlobalTheory.LogKS.logDer s I W, ∀ r, DlW ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (Dl r) := by
  intro X K _ s I U W hW f hf Dl hD
  obtain rfl : W = X.affineBasicOpen f := Subtype.ext hf
  haveI : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  obtain ⟨E, hE⟩ := exists_extension (B := Γ(X, X.basicOpen f)) f Dl
  have hE' : ∀ r, E ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (Dl r) := hE
  refine ⟨E, ⟨fun a => ?_, ?_⟩, hE'⟩
  · have hc : (X.presheaf.map (homOfLE hW).op).hom (constFn s U.1 a) = constFn s (X.affineBasicOpen f).1 a := by
      exact congr(($(Scheme.Hom.appLE_map s (U := ⊤) (V := U.1) (fun _ _ => trivial) (homOfLE hW).op)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    have := hE' (constFn s U.1 a)
    rw [hc, hD.1 a, map_zero] at this
    exact this
  · rw [← I.map_ideal_basicOpen U f]
    exact map_mem_map _ Dl E hE' _ hD.2

end GlobalTheory.LogDerLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModificationExtendingMapFromOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

noncomputable section

theorem GlobalTheory.CompHS.exists_modif_map_of_open : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (Y T : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (d : ℕ) (t : T ⟶ Sp F) (U : Y.Opens) (r₀ : U.toScheme ⟶ T), SmoothOfRelativeDimension d p → IsProjOver p → IsProjOver t → (U : Set Y).Nonempty → r₀ ≫ t = U.ι ≫ p → ∃ (M : Modif p U d) (r : M.X ⟶ T), IsIntegral M.X ∧ r ≫ t = M.str ∧ M.opn.ι ≫ r = (M.σ ∣_ U) ≫ r₀ := by
  intro hPr F _ _ Y T _ p d t U r₀ hs hpY hpT hU hr
  obtain ⟨N, i, hi, hit⟩ := hpT
  have hφ : (r₀ ≫ i) ≫ PSpace.str F N = U.ι ≫ p := by rw [Category.assoc, hit, hr]
  obtain ⟨w, i₀, hw₀, hwU, hext⟩ := _root_.GlobalTheory.ProjSpace.exists_ratCoords_extend F Y p N U (r₀ ≫ i) hφ hU
  obtain ⟨I, hI0, hIU, hC⟩ := GlobalTheory.T.exists_denominatorIdealSheaf_principalising_family Y N w i₀ U hw₀ hwU
  obtain ⟨Y', s, hY', hs', hp', -, hiso, hEC, -⟩ := hPr F d Y p inferInstance hs hpY I hI0
  have hUle : U ≤ I.support.compl := fun y hy => hIU y hy
  have hisoU : IsIso (s ∣_ U) := ReciprocityTheory.AnForm.R.isIso_morphismRestrict_of_le s hUle
  have : Nonempty U := hU.to_subtype
  let c : U.toScheme ⟶ Y' := inv (s ∣_ U) ≫ (s ⁻¹ᵁ U).ι
  have hc : c ≫ s = U.ι := by simp [c, morphismRestrict_ι]
  have hcη : c (genericPoint U) = genericPoint Y' := genericPoint_eq_of_isOpenImmersion c
  have hη : s (genericPoint Y') = genericPoint Y := by
    rw [← hcη, ← Scheme.Hom.comp_apply, hc]
    exact genericPoint_eq_of_isOpenImmersion U.ι
  have hne : ((s ⁻¹ᵁ U : Y'.Opens) : Set Y').Nonempty :=
    ⟨genericPoint Y', show s (genericPoint Y') ∈ U from hη ▸ GlobalTheory.Cartier.gen_mem hU.some_mem⟩
  have hdense : Dense ((s ⁻¹ᵁ U : Y'.Opens) : Set Y') := (s ⁻¹ᵁ U).isOpen.dense hne
  let M : Modif p U d := ⟨Y', s, hs', hp', hisoU, hdense⟩
  obtain ⟨g, hg1, hg2⟩ := hext Y' s hη (hC Y' s hη hEC)
  obtain ⟨r, hr'⟩ := GlobalTheory.exists_lift_closedImmersion_of_dense i g _ hdense fun x hx => by
    refine ⟨(s ∣_ U ≫ r₀) ⟨x, hx⟩, ?_⟩
    have e := congrArg (fun f : (s ⁻¹ᵁ U).toScheme ⟶ PSpace F N => f ⟨x, hx⟩) hg2
    exact e.symm
  refine ⟨M, r, hY', ?_, ?_⟩
  · show r ≫ t = s ≫ p
    rw [← hit, ← Category.assoc, hr', hg1]
  · show (s ⁻¹ᵁ U).ι ≫ r = (s ∣_ U) ≫ r₀
    rw [← cancel_mono i, Category.assoc, hr', hg2, Category.assoc]
end
end

