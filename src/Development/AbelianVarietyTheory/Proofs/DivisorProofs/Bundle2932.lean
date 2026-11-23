module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0478
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2915
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1101
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2897

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamGlobalFormsBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem exact_clAll_toHO1 {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hc : Closed1 (OAff s) = ⊤) :
    Function.Exact (clAll (OAff s) hc) (toHO1 s) := by
  rw [LinearMap.exact_iff]
  change Fil1 (OAff s) = _
  rw [Fil1_eq_range, clAll, LinearMap.range_comp_of_range_eq_top]
  exact LinearEquiv.range _

theorem surjective_of_section {X Y : Scheme.{0}} (f : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ f = 𝟙 Y) : Surjective f := by
  have : Surjective (e ≫ f) := by rw [he]; infer_instance
  exact Surjective.of_comp e f

theorem baseChange_HH1_globForm : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))), (∃ e : R' ⊗[R] HH1 A.hom ≃ₗ[R'] HH1 s', ∀ c, e (1 ⊗ₜ c) = pullHH1 h.w c) ∧ ∃ e : R' ⊗[R] GlobForm A.hom ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  intro R _ A _ g hab hsm R' _ _ X' s' φ h
  obtain ⟨inst', hab', hsm'⟩ := _root_.GlobalTheory.exists_grpObj_isAbelianScheme_of_isPullback_spMap R A g hab hsm R' (algebraMap R R') X' s' φ h
  obtain ⟨hfr, h0, -, -⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R A g hab hsm
  obtain ⟨hfr', h0', -, -⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R' (Over.mk s') g hab' hsm'
  have hc := _root_.GlobalTheory.AbCoh.closed1_eq_top_of_abelian R A g hab hsm
  have hc' := _root_.GlobalTheory.AbCoh.closed1_eq_top_of_abelian R' (Over.mk s') g hab' hsm'
  have hflat : Flat s' := by
    haveI := hsm'
    haveI : Smooth s' := SmoothOfRelativeDimension.smooth g s'
    infer_instance
  have hsurj : Surjective s' := by
    refine surjective_of_section s' (η[Over.mk s']).left ?_
    have := Over.w (η[Over.mk s'])
    simpa using this
  have hW := _root_.GlobalTheory.AbCoh.exists_equiv_globForm_baseChange R R' A.left X' A.hom s' φ h hfr h0 hfr' h0' hflat hsurj
  refine ⟨?_, hW⟩
  have hH := (_root_.GlobalTheory.AbCoh.oStr R A g hab hsm).2.2.1 R' X' s' φ h
  refine _root_.GlobalTheory.AbCoh.baseChange_middle_equiv_of_exact R R' (GlobForm A.hom) (HH1 A.hom) (HO1 A.hom) (GlobForm s') (HH1 s') (HO1 s')
    (clAll (OAff A.hom) hc) (toHO1 A.hom) (clAll (OAff s') hc') (toHO1 s')
    (pullForm h.w) (pullHH1 h.w) (pullHO1 h.w)
    (_root_.GlobalTheory.AbCoh.toHO1_surjective R A g hab hsm) (exact_clAll_toHO1 A.hom hc) ?_ (exact_clAll_toHO1 s' hc') ?_ ?_ hW hH
  · exact (ofForm_injective_of_H0Const R' _ (OAff s') h0').comp (LinearEquiv.injective _)
  · intro x
    exact _root_.GlobalTheory.AbCoh.pullHH1_clAll R R' A.left X' A.hom s' (algebraMap R R') φ h.w hc hc' x
  · intro x
    exact toHO1_pullHH1 h.w x

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamH1RankPrimitive
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem fp_HH1 (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hs : SmoothOfRelativeDimension g A.hom) : FP R (HH1 A.hom) (2 * g) := by
  have hcl := _root_.GlobalTheory.AbCoh.closed1_eq_top_of_abelian R A g hA hs
  have h0 := (_root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R A g hA hs).2.1
  have hinj : Function.Injective (clAll (OAff A.hom) hcl) := by
    unfold clAll
    exact (ofForm_injective_of_H0Const R _ _ h0).comp (LinearEquiv.ofTop _ hcl).symm.injective
  have hex : Function.Exact (clAll (OAff A.hom) hcl) (toHO1 A.hom) := by
    rw [LinearMap.exact_iff]
    change Fil1 (OAff A.hom) = _
    rw [Fil1_eq_range]
    unfold clAll
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  have := (_root_.GlobalTheory.AbCoh.fp_ext_prod).1 R _ _ _ g g _ _ hinj (_root_.GlobalTheory.AbCoh.toHO1_surjective R A g hA hs) hex
    (_root_.GlobalTheory.AbCoh.globForm_FP R A g hA hs) (_root_.GlobalTheory.AbCoh.oStr R A g hA hs).1
  rwa [two_mul]

theorem rank_prim_HH1 : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → FP R (HH1 A.hom) (2 * g) ∧ DeRhamH1Primitive A := by
  intro R _ A _ g hA hs
  refine ⟨fp_HH1 R A g hA hs, fun x ↦ ?_⟩
  obtain ⟨-, -, hAA, hsAA⟩ := _root_.GlobalTheory.AbCoh.basic_of_isAbelianScheme R A g hA hs
  have ax := (_root_.GlobalTheory.AbCoh.AxesPull.main R A).2.2
  set i₁ : A ⟶ A ⊗ A := lift (𝟙 A) (toUnit A ≫ η[A])
  set i₂ : A ⟶ A ⊗ A := lift (toUnit A ≫ η[A]) (𝟙 A)
  let f : HH1 A.hom × HH1 A.hom →ₗ[R] HH1 (A ⊗ A).hom :=
    (deRhamH1Pullback (fst A A)).coprod (deRhamH1Pullback (snd A A))
  let r : HH1 (A ⊗ A).hom →ₗ[R] HH1 A.hom × HH1 A.hom := (deRhamH1Pullback i₁).prod (deRhamH1Pullback i₂)
  have hrf : ∀ p, r (f p) = p := by
    rintro ⟨a, b⟩
    show (deRhamH1Pullback i₁ (deRhamH1Pullback (fst A A) a + deRhamH1Pullback (snd A A) b), deRhamH1Pullback i₂ (deRhamH1Pullback (fst A A) a + deRhamH1Pullback (snd A A) b)) = (a, b)
    rw [map_add (f := _), map_add (f := _), (ax a).1, (ax b).2.1, (ax a).2.2.2.1, (ax b).2.2.2.2.1, add_zero, zero_add]
  have hM : FP R (HH1 A.hom × HH1 A.hom) (2 * (g + g)) := by
    have := (_root_.GlobalTheory.AbCoh.fp_ext_prod).2 R _ _ _ _ (fp_HH1 R A g hA hs) (fp_HH1 R A g hA hs)
    rwa [← mul_add] at this
  have hbij := _root_.GlobalTheory.AbCoh.bijective_of_split_of_FP R _ _ _ hM (fp_HH1 R (A ⊗ A) (g + g) hAA hsAA) f r hrf
  obtain ⟨p, hp⟩ := hbij.2 (deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x)
  have hry : r (deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x) = 0 := by
    show (deRhamH1Pullback i₁ (deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x),
      deRhamH1Pullback i₂ (deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x)) = (0, 0)
    rw [map_sub, map_sub, map_sub, map_sub, (ax x).1, (ax x).2.1, (ax x).2.2.1,
      (ax x).2.2.2.1, (ax x).2.2.2.2.1, (ax x).2.2.2.2.2, sub_self, sub_zero, sub_zero, sub_self]
  have hp0 : p = 0 := by rw [← hrf p, hp, hry]
  have h0 : deRhamH1Pullback μ[A] x - deRhamH1Pullback (fst A A) x - deRhamH1Pullback (snd A A) x = 0 := by rw [← hp, hp0, map_zero]
  rw [sub_sub, sub_eq_zero] at h0
  exact h0

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescSt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc GlobalTheory.SiegJoin

namespace GlobalTheory.SiegDescent

theorem exists_chart {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {s : S ⟶ Sp o}
    {j : F.X ⟶ S} [IsOpenImmersion j] {φ : InvFun ℤ} {BD : EffCartierData S} {d : ℕ} {x : S}
    (h : GlobalTheory.PolDeg.PreChart F s j φ BD d x) :
    ∃ C : Chart j F.univ.A x, ∀ p : Sp C.R, p ∈ abLocus C.G ↔ C.ξ p ∈ Set.range j := by
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, G₁, _, y, α₁, ⟨hc, h0, -, hx, het, hun⟩, ⟨-, -, hr⟩, ⟨hs, hab, hy, hgen⟩, -⟩ := h
  exact ⟨{ R := R, complete := hc, charZero := h0, ξ := ξ, centre := hx, etc := het, unr := hun, G := G₁, semi := hs,
           y := y, hy := hy, α := α₁, gen := hgen }, fun p => (hab p).trans (hr p).symm⟩

end GlobalTheory.SiegDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalRestrictionRelAmpleLocusOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.FibreAmple

noncomputable section

namespace GlobalTheory.DiagAmpleLocus

theorem diag_relAmple_locus : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → Set.range g.base ⊆ (U : Set S') := by
  intro S' _ G _ _ P hG hP
  have := hG.proper
  have : Flat G.hom := by have := hG.smooth; infer_instance
  have hD : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  let good : Set S' := {s | ∃ (Y X : Scheme.{0}) (j : Y ⟶ S') (_ : IsOpenImmersion j) (π : X ⟶ G.left)
      (f : X ⟶ Y), IsPullback π f G.hom j ∧ s ∈ Set.range j.base ∧
        RelAmple (Over.mk f) ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull π)}
  have hopen : IsOpen good := by
    rw [isOpen_iff_forall_mem_open]
    rintro s ⟨Y, X, j, hj, π, f, h, hs, hA⟩
    exact ⟨Set.range j.base, fun x hx => ⟨Y, X, j, hj, π, f, h, hx, hA⟩,
      j.isOpenEmbedding.isOpen_range, hs⟩
  refine ⟨⟨good, hopen⟩, fun V hV => ?_, ?_⟩
  · let AV := (Over.pullback V.ι).obj G
    have : IsProper AV.hom := inferInstanceAs (IsProper (pullback.snd G.hom V.ι))
    have key : RelAmple AV ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull (pullback.fst G.hom V.ι)) := by
      refine GlobalTheory.AmpleLocal.relAmple_of_locally V AV _ (pull_isLB hD _) inferInstance inferInstance
        fun v => ?_
      obtain ⟨Y, X, j, hj, π, f, h, ⟨y, hy⟩, hA⟩ := hV v.2
      let V' : V.toScheme.Opens := V.ι ⁻¹ᵁ j.opensRange
      have hv : v ∈ V' := ⟨y, hy⟩
      have hrange : Set.range (V'.ι ≫ V.ι).base ⊆ Set.range j.base := by
        rintro _ ⟨w, rfl⟩
        exact w.2
      have sq : IsPullback ((AV.hom ⁻¹ᵁ V').ι ≫ pullback.fst G.hom V.ι) (AV.hom ∣_ V') G.hom (V'.ι ≫ V.ι) :=
        (isPullback_morphismRestrict AV.hom V').flip.paste_horiz (IsPullback.of_hasPullback G.hom V.ι)
      have h₁ := relAmple_of_factor hD h sq (IsOpenImmersion.lift j _ hrange)
        (IsOpenImmersion.lift_fac _ _ _) (pull_isLB hD π) (GlobalTheory.lbIso_refl (pull_isLB hD π)) hA
      have : IsProper (Over.mk (AV.hom ∣_ V')).hom := inferInstanceAs (IsProper (AV.hom ∣_ V'))
      exact ⟨V', hv, GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hD _)
        (pull_isLB (pull_isLB hD _) _) (lbIso_pull_pull hD _ _) h₁⟩
    have e₁ : LBIso ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 AV) (𝟙 AV)).left)
        (P.pull ((lift (𝟙 AV) (𝟙 AV)).left ≫ Pdiv.PullbackComparison.pφ₂ V.ι G)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
    rw [GlobalTheory.DiagAmpleBC.diag_comp G AV _ _ (Pdiv.PullbackComparison.isSquare V.ι G)] at e₁
    have e₂ : LBIso ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull (Pdiv.PullbackComparison.pφ V.ι G))
        (P.pull (Pdiv.PullbackComparison.pφ V.ι G ≫ (lift (𝟙 G) (𝟙 G)).left)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
    exact GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hD _) (pull_isLB (pull_isLB hP _) _)
      (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB hD _) e₁ e₂.symm) key
  · rintro T g A' _ φ φ₂ P' hpb hsq hP' e hA _ ⟨t, rfl⟩
    have h₀ : IsPullback φ A'.hom G.hom g := hpb.1
    have : IsProper A'.hom := MorphismProperty.of_isPullback (P := @IsProper) h₀ ‹_›
    have e₁ : LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) (P.pull ((lift (𝟙 A') (𝟙 A')).left ≫ φ₂)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp e _
    rw [GlobalTheory.DiagAmpleBC.diag_comp G A' φ φ₂ hsq] at e₁
    have e₂ : LBIso ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull φ) (P.pull (φ ≫ (lift (𝟙 G) (𝟙 G)).left)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
    have hA' : RelAmple A' ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull φ) :=
      GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hP' _) (pull_isLB hD _)
        (LBIso.trans (pull_isLB hD _) (pull_isLB hP _) (pull_isLB hP' _) e₂ e₁.symm) hA
    obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S') (U := ⊤) (x := g.base t) trivial
    have : IsNoetherianRing Γ(S', V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    obtain ⟨VT, hVT, ht, hle⟩ := exists_isAffineOpen_mem_and_subset (X := T) (U := g ⁻¹ᵁ V) (x := t) hs
    obtain ⟨q, hq⟩ : t ∈ Set.range hVT.fromSpec.base := by rw [hVT.range_fromSpec]; exact ht
    let tV : Sp Γ(S', V) ⟶ S' := hV.fromSpec
    let φR := g.appLE V VT hle
    have sqR : Spec.map φR ≫ hV.fromSpec = hVT.fromSpec ≫ g := IsAffineOpen.SpecMap_appLE_fromSpec g hV hVT hle
    let p : PrimeSpectrum Γ(S', V) := (Spec.map φR).base q
    have hp : tV.base p = g.base t := by
      have := congrArg (fun f : Spec Γ(T, VT) ⟶ S' => f.base q) sqR
      simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at this
      rw [← hq]
      exact this
    have : q.asIdeal.IsPrime := PrimeSpectrum.isPrime (q : PrimeSpectrum Γ(T, VT))
    have : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
    let k := p.asIdeal.ResidueField
    let kq := q.asIdeal.ResidueField
    let gR := algebraMap Γ(S', V) k
    let i : k →+* kq := Ideal.ResidueField.map p.asIdeal q.asIdeal φR.hom rfl
    have hi : spMap (algebraMap Γ(T, VT) kq) ≫ Spec.map φR = spMap i ≫ spMap gR := by
      show Spec.map (CommRingCat.ofHom _) ≫ Spec.map φR = Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom gR)
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext x
      exact (Ideal.ResidueField.map_algebraMap _ _ _ _ x).symm
    let y : Sp kq ⟶ S' := spMap i ≫ spMap gR ≫ tV
    have hu : (spMap (algebraMap Γ(T, VT) kq) ≫ hVT.fromSpec) ≫ g = y := by
      rw [Category.assoc, ← sqR, ← Category.assoc, hi, Category.assoc]
    have hfib := relAmple_of_factor hD h₀ (IsPullback.of_hasPullback G.hom y) _ hu (pull_isLB hD φ)
      (GlobalTheory.lbIso_refl (pull_isLB hD φ)) hA'
    let B : Over (Sp Γ(S', V)) := Over.mk (pullback.snd G.hom tV)
    have : IsProper B.hom := inferInstanceAs (IsProper (pullback.snd G.hom tV))
    have : Flat B.hom := inferInstanceAs (Flat (pullback.snd G.hom tV))
    have hB := IsPullback.of_hasPullback G.hom tV
    have hL := pull_isLB hD (pullback.fst G.hom tV)
    obtain ⟨r, hr, hAr⟩ := GlobalTheory.ProperFinite.relAmple_near_fibre B hL gR (residueField_fraction p.asIdeal)
      (relAmple_of_fieldExtension hD i ((IsPullback.of_hasPullback B.hom (spMap gR)).paste_horiz hB)
        (IsPullback.of_hasPullback G.hom _) (pull_isLB hL _) (lbIso_pull_pull hD _ _) hfib)
    let Dr : (Sp Γ(S', V)).Opens := PrimeSpectrum.basicOpen r
    have hpD : p ∈ Dr := fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)
    have : IsProper (Over.mk (pullback.snd B.hom Dr.ι)).hom := inferInstanceAs (IsProper (pullback.snd B.hom Dr.ι))
    exact ⟨Dr.toScheme, _, Dr.ι ≫ tV, inferInstance, pullback.fst B.hom Dr.ι ≫ pullback.fst G.hom tV,
      pullback.snd B.hom Dr.ι, (IsPullback.of_hasPullback B.hom Dr.ι).paste_horiz hB, ⟨⟨p, hpD⟩, hp⟩,
      GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hL _) (pull_isLB hD _) (lbIso_pull_pull hD _ _).symm hAr⟩

end GlobalTheory.DiagAmpleLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivStrictHenselianLinePoint
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC TensorProduct

namespace GlobalTheory.EtC.LineLocal

open Polynomial

theorem bijective_of_subsingleton {X Y : Type*} [Subsingleton X] [Subsingleton Y] (f : X → Y) (x : X) :
    Function.Bijective f :=
  ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨x, Subsingleton.elim _ _⟩⟩

theorem idem_of_domain {A : Type} [CommRing A] [IsDomain A] (e : A) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have h : e * (e - 1) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem isDomain_tensor_fractionRing (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [IsDomain O]
    [Algebra T O] (hinj : Function.Injective (algebraMap T O)) : IsDomain (O ⊗[T] FractionRing T) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
      (O ⊗[T] FractionRing T) := by
    rw [Algebra.isLocalization_iff_isPushout (nonZeroDivisors T) (FractionRing T)]
    infer_instance
  exact IsLocalization.isDomain_of_le_nonZeroDivisors (M := Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
    (O ⊗[T] FractionRing T) (by
      rintro _ ⟨a, ha, rfl⟩
      exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha)))

theorem eqv_local : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T →
    IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra (Polynomial T) O] [Algebra T O]
    [IsScalarTower T (Polynomial T) O], SH O → IndEt (Polynomial T) O → ∀ i : ℤ,
    Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := O)).toRingHom)
      (tw q i) := by
  intro q _ T _ _ _ hT hq O _ _ _ _ hSH hInd i
  unfold Eqv
  intro n
  have hfac : ∀ a : O, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E)
      (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] O), a ∈ φ.range := by
    intro a
    obtain ⟨C, _, _, _, ψ, χ, h⟩ := exists_etale_factor_of_indEt (Polynomial T) O hInd
      (Polynomial (Polynomial T)) (Polynomial.aeval a)
    refine ⟨C, ‹_›, ‹_›, ‹_›, χ, ⟨ψ Polynomial.X, ?_⟩⟩
    have := DFunLike.congr_fun h Polynomial.X
    simpa using this
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have h1 : ∀ E : Spc, ∀ n : ℤ, n < 0 → Subsingleton (H (ZMod q) E (tw q i) n) := by
      intro E n hn
      have hz : ∀ α : CochainComplex.HomComplex.Cochain ((chains (ZMod q)).obj E)
          (res (ZMod q) (tw q i)) n, α = 0 := by
        intro α
        apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 α 0
        intro p s h U x
        have hs : s < 0 := by omega
        haveI := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness
          (ZMod q) (tw q i) U).2.2.2 s hs)
        exact Subsingleton.elim _ _
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := a.mk_surjective
      obtain ⟨b, rfl⟩ := b.mk_surjective
      have : a = b := CochainComplex.HomComplex.Cocycle.ext (by rw [hz a.1, hz b.1])
      rw [this]
    haveI := h1 (sp O) n hn
    haveI := h1 (sp (TensorProduct T (FractionRing T) O)) n hn
    exact bijective_of_subsingleton _ 0
  · haveI : IsIntegrallyClosed T := GlobalTheory.AICStalk.isIntegrallyClosed_of_aic hT
    obtain ⟨hH, -⟩ := hSH
    haveI : IsLocalRing O := hH.toIsLocalRing
    haveI : IsDomain O := GlobalTheory.AICStalk.isDomain_of_indEt hInd
    have hinjX : Function.Injective (algebraMap (Polynomial T) O) :=
      GlobalTheory.AICStalk.algebraMap_injective_of_indEt hInd
    have hinj : Function.Injective (algebraMap T O) := by
      rw [IsScalarTower.algebraMap_eq T (Polynomial T) O]
      exact hinjX.comp (Polynomial.C_injective)
    haveI : IsDomain (O ⊗[T] FractionRing T) := isDomain_tensor_fractionRing T O hinj
    haveI : IsDomain (TensorProduct T (FractionRing T) O) :=
      MulEquiv.isDomain _ (Algebra.TensorProduct.comm T (FractionRing T) O).toRingEquiv.toMulEquiv
    have hqO : IsUnit (q : O) := by
      have := hq.map (algebraMap T O)
      rwa [map_natCast] at this
    obtain ⟨z, hz⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T) (by
      rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q))
    have hζ : Polynomial.aeval (algebraMap T O z) (Polynomial.cyclotomic q ℤ) = 0 := by
      rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
        Polynomial.map_cyclotomic, hz, map_zero]
    exact GlobalTheory.T.h_zero_pullback_twist_bijective q O (TensorProduct T (FractionRing T) O)
      (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := O)).toRingHom hqO
      ⟨_, hζ⟩ inferInstance (idem_of_domain) (idem_of_domain) i
  · haveI : Subsingleton (H (ZMod q) (sp O) (tw q i) n) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) O hSH (tw q i) n hn
    haveI : Subsingleton (H (ZMod q) (sp (TensorProduct T (FractionRing T) O)) (tw q i) n) := by
      rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
      · exact GlobalTheory.T.subsingleton_ht_one_genericFibre_of_sh_etale_cover q T hT hq O hSH hfac i
      · exact GlobalTheory.T.subsingleton_etaleCohomology_genericFibre_henselianLine q T hT hq O hSH hInd n i h2
    exact bijective_of_subsingleton _ 0

end GlobalTheory.EtC.LineLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalDeRhamRigidExtensionFamily
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DeRhamExt

def canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (hA : IsAbelianScheme A)
    {G : PDivGroup p R} (t : G.TorsionTower A) : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))) :=
  Classical.choose (GlobalTheory.T.exists_linear_canonical_map_primitiveDeRham_rigExt R A p G t hA)

theorem isCan_iff_canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
    (hA : IsAbelianScheme A) {G : PDivGroup p R} (t : G.TorsionTower A) (c : primDR A)
    (x : ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) : IsCan t c x ↔ canMap p hA t c = x :=
  Classical.choose_spec (GlobalTheory.T.exists_linear_canonical_map_primitiveDeRham_rigExt R A p G t hA) c x

theorem isCan_canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
    (hA : IsAbelianScheme A) {G : PDivGroup p R} (t : G.TorsionTower A) (c : primDR A) :
    IsCan t c (canMap p hA t c) :=
  (isCan_iff_canMap p hA t c _).2 rfl

theorem canMap_bijective (hP : GlobalTheory.Published.AbelianHodgeDeRham) (p : ℕ) [Fact p.Prime] {R : Type}
    [CommRing R] (hR : IsNilpotent (p : R)) {A : Over (Sp R)} [GrpObj A] (hA : IsAbelianScheme A)
    {G : PDivGroup p R} (t : G.TorsionTower A) : Function.Bijective (canMap p hA t) := by
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.TowerDim.exists_smoothOfRelativeDimension_of_hodgeDeRham hP p R hR A hA G t
  exact _root_.GlobalTheory.PtExt.bijective_of_isCan_of_isNilpotent_of_hodgeDeRham hP p R hR A g hA hg G t _ (isCan_canMap p hA t)

def canFamily (hP : GlobalTheory.Published.AbelianHodgeDeRham) (p : ℕ) [Fact p.Prime] :
    GlobalTheory.Published.DeRhamVectorExtension.Family p :=
  fun _ _ hR _ _ hA _ t => LinearEquiv.ofBijective (canMap p hA t) (canMap_bijective hP p hR hA t)

theorem exists_canonical_family : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime],
    ∃ e : GlobalTheory.Published.DeRhamVectorExtension.Family p, e.Natural ∧ e.Filtered ∧ e.Tangent ∧
      ∀ ⦃R : Type⦄ [CommRing R] (hR : IsNilpotent (p : R)) ⦃A : Over (Sp R)⦄ [GrpObj A]
        (hA : IsAbelianScheme A) ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A) (c : primDR A),
        IsCan t c (e hR hA t c) := by
  intro hP p _
  refine ⟨canFamily hP p, ?_, ?_, ?_, ?_⟩
  · intro R R' _ _ hR hR' A _ A' _ hA hA' G G' t t' σ φ m c
    exact ((isCan_iff_canMap p hA' t' _ _).1
      (GlobalTheory.T.canonicalRigidifiedExtension_pullback_naturality p R R' A A' G G' t t' σ φ m c _ (isCan_canMap p hA t c)))
  · intro R _ hR A _ hA G t
    obtain ⟨N, hN⟩ := hR
    exact GlobalTheory.T.canonical_iso_hodge_filtration_eq_range_invariant_forms p R N hN A hA G t (canMap p hA t)
      (canMap_bijective hP p ⟨N, hN⟩ hA t).2 (isCan_canMap p hA t)
  · intro R _ hR A _ hA G t h v
    obtain ⟨g, hg⟩ := _root_.GlobalTheory.TowerDim.exists_smoothOfRelativeDimension_of_hodgeDeRham hP p R hR A hA G t
    exact _root_.GlobalTheory.PtExt.isLieImage_iff_lieCorr hP p R hR A g hA hg G t (canFamily hP p hR hA t)
      (isCan_canMap p hA t) h v
  · intro R _ hR A _ hA G t c
    exact isCan_canMap p hA t c

end GlobalTheory.DeRhamExt
end
end

