module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0654
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPlacesThetaFunctionFixedVectorShape
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0752
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLocalGenerationSplitPlaceOffLevels
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGenerationThetaFunAtTypePrime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGenerationThetaFunctionsTwistPlace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaPrimeIsAuxiliarySplitSquarefreeLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatTwistOfIsRatScalar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliarySquarefreeLevelTwistPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2521
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedFiniteDatumFourierExpansionChainless

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLevelTypeMemSpanTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section
namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem transl_mem_span_gen (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (g : GA D (Wc D i))
    {φ : WO (Vc D i) (Wc D i) → ℂ} (hφ : φ ∈ Submodule.span ℂ (Gen R i t)) :
    R.ωP i t (1, g) φ ∈ Submodule.span ℂ (Gen R i t) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g', f', hf', rfl⟩ := hx
    refine Submodule.subset_span ⟨g * g', f', hf', ?_⟩
    have hm : ((1, g) : GA D (Vc D i) × GA D (Wc D i)) * (1, g') = (1, g * g') := by
      rw [Prod.mk_mul_mk, mul_one]
    rw [← hm, map_mul, Module.End.mul_apply]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem finLike_of_likeOff_empty (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {f : WO (Vc D i) (Wc D i) → ℂ}
    (hf : LikeOff R i t ∅ f) : FinLike R i t f :=
  ⟨hf.1, fun c hc h0 => hf.2 c (fun u hu => ⟨hc u hu, fun v hv => absurd hv (Finset.notMem_empty v)⟩) h0⟩

theorem mem_span_gen_of_step (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (hst : ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb →
      ∀ f, TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → f ∈ Submodule.span ℂ (StepGen R i t (dropPl Sb v)))
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∀ f, TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → f ∈ Submodule.span ℂ (Gen R i t) := by
  classical
  induction Sb using Finset.induction_on with
  | empty =>
    intro f _ _ hL
    refine Submodule.subset_span ⟨1, f, finLike_of_likeOff_empty R i t hL, ?_⟩
    have h1 : ((1, 1) : GA D (Vc D i) × GA D (Wc D i)) = 1 := rfl
    rw [h1, map_one, Module.End.one_apply]
  | insert v s hv ih =>
    intro f hT hC hL
    have h := hst (insert v s) v (Finset.mem_insert_self v s) f hT hC hL
    rw [dropPl_insert hv] at h
    refine (Submodule.span_le.2 ?_) h
    rintro φ ⟨g, f', hT', hC', hL', rfl⟩
    exact transl_mem_span_gen R i t g (ih f' hT' hC' hL')

end GlobalTheory.DownLift.GenFinite

namespace GlobalTheory.DownLift.GenFinite

theorem gen_of_type_clean : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeVec R i t f → GlobalTheory.DownLift.GenFinite.Clean R i t f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.Gen R i t) := by
  intro hH D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t f hT hC
  obtain ⟨Sb, hL⟩ := _root_.GlobalTheory.DownLift.ShapeOff.exists_likeOff D G Pl0 T A Ks R F hG hP i t f hT.1
  refine mem_span_gen_of_step R i t ?_ Sb f ⟨hT.1, fun κ hκ _ => hT.2 κ hκ⟩
    (fun PP a ha tr ε hε _ κ hκ _ => hC PP a ha tr ε hε κ hκ) hL
  intro Sb v hv f hT hC hL
  by_cases hpg : ∃ PP ∈ R.Pg, Over PP v
  · exact _root_.GlobalTheory.DownLift.GenSplit.gen_at_type_prime D G Pl0 T A Ks R F hG hP i t Sb v hv hpg f hT hC hL
  by_cases hq : ∃ PP ∈ R.Q t, Over PP v
  · exact _root_.GlobalTheory.DownLift.GenTwist.step_twist D G Pl0 T A Ks R F hG hP i t Sb v hv (fun PP h ho => hpg ⟨PP, h, ho⟩) hq f hT hC hL
  have hoff : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ¬ Over PP v := by
    rintro PP (h | h) ho
    · exact hpg ⟨PP, h, ho⟩
    · exact hq ⟨PP, h, ho⟩
  by_cases hs : ∃ ε e, IsPlaceIdem D v ε ∧ IsSplitIdem D e ∧ e * algebraMap (AF D.host.F) (AE D) ε ≠ 0
  · exact _root_.GlobalTheory.DownLift.SplitGen.gen_split D G Pl0 T A Ks R F hG hP i t Sb v hv hs hoff f hT hC hL
  · refine GlobalTheory.T.thetaFunction_local_generation_inertPlace_offLevel hH D G Pl0 T A Ks R F hG hP i t Sb v hv ?_ hoff f hT hC hL
    intro ε hε e he
    by_contra hne
    exact hs ⟨ε, e, hε, he, hne⟩

end GlobalTheory.DownLift.GenFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesBaseTwistedUniversalRational
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.SeriesTie GlobalTheory.BigOn.Exp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.SeriesTie.RatAll

section Zero

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem evW_eq_zero (fw : FWTie T Rl.toRealDat κ v₀) {j : Fin D.R.m}
    (h : T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n = ⊥) (f : NX.FmK S ((j : ℕ) + 1)) :
    evW YS v₀ j (Subtype.val f) = 0 := by
  have hm : (YS.fi j).e (Subtype.val f) ∈ (Rl.FW j).WK := ((YS.fi j).wk _).1 f.2
  obtain ⟨c, hc⟩ := (fw.e j).surjective ⟨_, hm⟩
  have hc0 : c = 0 := Subtype.ext (by
    have h2 := c.2
    simp only [h, Submodule.mem_bot] at h2
    exact h2)
  rw [hc0, map_zero] at hc
  have h3 : (YS.fi j).e (Subtype.val f) = 0 := (congrArg Subtype.val hc).symm
  have h4 : Subtype.val f = 0 := (YS.fi j).e.injective (h3.trans (map_zero _).symm)
  rw [h4, map_zero]

theorem realRd_eq_zero (fw : FWTie T Rl.toRealDat κ v₀) {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) {j : Fin D.R.m} (b : Bool)
    (h : T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n = ⊥) (ν : ℂ) (f : D.nexp.Fm i ((j : ℕ) + 1) b) :
    realRd YS v₀ hρ i j b ν f = 0 := by
  change ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f) = 0
  have key : ∀ x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1), evK YS v₀ hρ i j b x = 0 := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact map_zero _
    | add x y hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | tmul a g => rw [evK_tmul, evW_eq_zero YS fw h, smul_zero]
  exact (congrArg (fun x => ν⁻¹ • x) (key _)).trans (smul_zero _)

end Zero

theorem ratRow : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), RealPin Rl cG ρ → ρ.LevelOf D.nexp → D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK → RatHyp T Rl F κ v₀ O i j hV → RatRow YS v₀ hρ i j b := by
  intro hA hRF row D Γ _ _ Pl0 I0 T0 A3 T _ Rl cG S YS F κ v₀ O ρ hρ i j b hV hpin hL hsp H
  have hrat : ∀ ν, IsRatScalar T Rl κ v₀ hV (ρ.B i j b) ν → Rat hρ (realRd YS v₀ hρ i j b ν) := fun ν hν => by
    refine ⟨?_, GlobalTheory.SeriesTie.TwistRat.ratTwist hA hRF row D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O ρ hρ i j b hV hpin hL hsp H ν hν,
      GlobalTheory.SeriesTie.UnivRat.ratUniv_of_ratHyp hA hRF row D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O ρ hρ i j b hV hpin hL hsp H ν hν⟩
    apply GlobalTheory.SeriesTie.BaseRat.ratBase_of_ratHyp hA hRF row D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O ρ hρ i j b hV <;> assumption
  by_cases hc : T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n = ⊥
  · obtain ⟨fw⟩ := H.fw
    have hcore := H.core
    have hti := H.tieIn
    have hrow0 : OneMapRow0 T Rl.toRealDat κ v₀ O j :=
      GlobalTheory.OneMapTies.oneMapRow0_of_ties_base_clauses GlobalTheory.chartIndependence_unconditional D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀
        hcore.lev hcore.grp hcore.fam hcore.models hcore.thP hti H.io O j H.pins
    have hph1 : ‖cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j)‖ = 1 := (H.phase hrow0).2.1.2.2.2.2.1
    have hph0 : cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j) ≠ 0 := fun e => by
      rw [e, norm_zero] at hph1; exact zero_ne_one hph1
    obtain ⟨c, hc0, hsc⟩ := exists_isScale Rl cG v₀ hρ hpin hcore.lev hcore.fam.tie hcore.models.cV hcore.thP H.io i j b
      (hti.hv₀ j _)
    have hsc' := hsc
    obtain ⟨gramR, c0R, c0L, hft, u, hu, hs⟩ := hsc'
    obtain ⟨ph, h1, h2⟩ := row D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ H.laws hcore.lev hcore.grp hcore.fam hcore.models hcore.thP hti
      j hV H.frame H.std gramR c0R c0L hft u hu
    have hR := hrat _ (IsRatScalar.intro (B := ρ.B i j b) hft hu hc0 h1 hs fun C hC _ => h2 C hC)
    have e : realRd YS v₀ hρ i j b (ph * c) = realRd YS v₀ hρ i j b (cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j) * c) :=
      LinearMap.ext fun f => (realRd_eq_zero YS fw hρ i b hc _ f).trans (realRd_eq_zero YS fw hρ i b hc _ f).symm
    exact ⟨_, ⟨mul_ne_zero hph0 hc0, c, hsc, 1, one_ne_zero, rfl⟩, e ▸ hR⟩
  · obtain ⟨ν, hn, hν⟩ := GlobalTheory.SeriesTie.NormRatStd.exists_isNorm_isRatScalar_std hA hRF row D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O ρ hρ i j b hV hpin H hc
    exact ⟨ν, hn, hrat ν hν⟩

end GlobalTheory.SeriesTie.RatAll

end
end

