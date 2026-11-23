module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2735
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2706
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionMapWelldefinedAdditiveCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2732
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelOpenAbelianEighthPowerWithBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.SharpOnV

theorem lAb : ∀ {X : Scheme.{0}} (G : Over X) (V : X.Opens), (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ V.toScheme), IsProper (pullback.snd G.hom (t ≫ V.ι))) → (V : Set X) ⊆ abLocus G := by
  intro X G V h s hs K _ _ t ⟨p, hp⟩
  have hr : Set.range t.base ⊆ (V : Set X) := by
    rintro _ ⟨q, rfl⟩
    have : q = p := Subsingleton.elim _ _
    subst this
    rw [hp]; exact hs
  let t' := IsOpenImmersion.lift V.ι t (by rwa [Scheme.Opens.range_ι])
  have ht : t' ≫ V.ι = t := IsOpenImmersion.lift_fac _ _ _
  have := h K t'
  rwa [ht] at this

theorem lGen : ∀ {X : Scheme.{0}} {G : Over X} [GrpObj G] {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ X) (gm : G'.left ⟶ G.left), IsGrpPullback G' G ξ gm → IsGrpPullback A'.A G (jK R ≫ ξ) (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) := by
  intro X G _ R _ _ _ G' _ _ D' A' U' ξ gm hgm
  exact ((GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (jK R) G' U'.gen U'.gen_hom).comp hgm).congr rfl (Category.assoc _ _ _)

theorem lLB : ∀ {X : Scheme.{0}} (L : LB X) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (gm : G'.left ⟶ X), L.IsLB → LBIso U'.LG.L (L.pull gm) → LBIso A'.L (L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm)) := by
  intro X L R _ _ _ G' _ _ D' A' U' gm hL hLB
  have hA := A'.isLB
  have ext : LBIso (A'.L.pull U'.gen.hom.left) (U'.LG.L.pull (pullback.fst G'.hom (jK R))) := U'.ext
  have H1 := GlobalTheory.ThetaAffineGlue.lbIso_comp (pull_isLB hA _) U'.LG.isLB hL ext hLB
  have H2 := GlobalTheory.ThetaAffineGlue.lbIso_pull H1 U'.gen.inv.left
  have hP : (A'.L.pull U'.gen.hom.left).IsLB := pull_isLB hA _
  have refl : LBIso (A'.L.pull U'.gen.hom.left) (A'.L.pull U'.gen.hom.left) :=
    LBIso.trans hP (pull_isLB hP _) hP (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hP) (LBIso.symm (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hP))
  have H4 := GlobalTheory.ThetaAffineGlue.lbIso_pull refl U'.gen.inv.left
  have e : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  rw [e] at H4
  have H3 : LBIso A'.L ((A'.L.pull U'.gen.hom.left).pull U'.gen.inv.left) :=
    LBIso.trans hA (pull_isLB hA _) (pull_isLB hP _) (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hA) (LBIso.symm H4)
  exact LBIso.trans hA (pull_isLB hP _) (pull_isLB hL _) H3 H2

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → (V : Set M.Z) ⊆ abLocus FinalForm.G ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → ∀ ξ₀ : Sp (FractionRing R) ⟶ V.toScheme, ξ₀ ≫ V.ι = jK R ≫ ξ → ∃ c' pr', SharpBy F W A' (ξ₀ ≫ v) c' pr' ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (f' : G' ⟶ G'), MatOn FinalForm pr a b f → f'.left ≫ gm = gm ≫ f.left → ∃ f₁ : A'.A ⟶ A'.A, MatEnd pr' a b f₁ ∧ (Over.pullback (jK R)).map f' ≫ U'.gen.hom = U'.gen.hom ≫ f₁ := by
  intro g n o _ ζ F W o' Ω _ _ _ _ S ρ u c pr hS M U₀ EE FinalForm hO V v hv
  have hK := GlobalTheory.T.semiAbelian_fieldPoint_eq_eighthPower_universal_pullback g n o ζ F W o' Ω S ρ u c pr hS M U₀ EE FinalForm hO V v hv
  refine ⟨lAb FinalForm.G V fun K _ _ t => ?_, ?_⟩
  · obtain ⟨c', pr', -, -, huniv, -, -⟩ := hK K t ((Over.pullback (t ≫ V.ι)).obj FinalForm.G) (pullback.fst _ _)
      (isGrpPullback_pullback _ _)
    exact _root_.GlobalTheory.FibrePowerProper.isProper_eighth_fibre_power pr' huniv c'.ab.proper
  · intro R _ _ _ hB G' _ _ hsemi D' A' U' ξ gm hgm hLB ξ₀ hξ₀
    have hpb : IsGrpPullback A'.A FinalForm.G (ξ₀ ≫ V.ι) (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) :=
      (lGen U' ξ gm hgm).congr hξ₀.symm rfl
    have hL := lLB FinalForm.L.L U' gm FinalForm.L.isLB hLB
    obtain ⟨c', pr', hSP, hmon, huniv, hlb, hmat⟩ := hK (FractionRing R) ξ₀ A'.A _ hpb
    refine ⟨c', pr', ⟨hSP, hmon, huniv, hlb A'.L A'.isLB hL⟩, fun a b f f' hf hff' => ?_⟩
    have hgi : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    have hmapf : ((Over.pullback (jK R)).map f').left ≫ pullback.fst G'.hom (jK R) = pullback.fst G'.hom (jK R) ≫ f'.left :=
      pullback.lift_fst _ _ _
    refine ⟨U'.gen.inv ≫ (Over.pullback (jK R)).map f' ≫ U'.gen.hom, hmat a b f _ hf ?_, by simp⟩
    simp only [Over.comp_left, Category.assoc]
    rw [reassoc_of% hgi, reassoc_of% hmapf, hff']

end GlobalTheory.Poinc.Eq8.SharpOnV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceShortSeriesEqMulAdelicSeries
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.OneMapExact.splitOff_of_dvd {D : D7} {V : HSp D} {b b' : ℕ} (hd : b ∣ b') {g : GA D V} (H : SplitOffBad V b' g) :
    SplitOffBad V b g := by
  obtain ⟨h1, e, P, h2, h3, h4⟩ := H
  refine ⟨h1, e, P, h2, fun PP hP hb => h3 PP hP ?_, h4⟩
  obtain ⟨c, rfl⟩ := hd
  rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hb

theorem GlobalTheory.OneMapExact.trace_of_terms {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (S : GA D (Wc D i) → ℂ) (c : D.what₂.LL) (X : U → Fin (R.nW i) → D.what₂.LL)
    (w : ∀ τ, (R.MW i (sg0 D A)).sm τ)
    (H : ∀ u : U, adForm R i (X u) w =
      D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) S) :
    adForm R i (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • X u) w = D.what₂.embLL c • levelTrace R i U ψ S := by
  classical
  have h0 : adForm R i 0 = 0 := by
    have := adForm_smul (R := R) (i := i) 0 0
    rw [zero_smul, map_zero, zero_smul] at this
    exact this
  have hadd : ∀ (s : Finset U) (Y : U → Fin (R.nW i) → D.what₂.LL),
      adForm R i (∑ u ∈ s, Y u) = ∑ u ∈ s, adForm R i (Y u) := by
    intro s Y
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, adForm_add, ih]
  rw [finsum_eq_sum_of_fintype, hadd]
  simp only [adForm_smul]
  unfold levelTrace gaL
  rw [LinearMap.sum_apply]
  ext1 g
  simp only [MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, LinearMap.smul_apply,
    H, smul_eq_mul]
  set Fn : G → ℂ := fun d => (if hg : d ∈ U then D.what₂.embLL ((ψ ⟨d, hg⟩)⁻¹ : D.what₂.LLˣ) else 0) *
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG d) S g with hFn
  have e1 : ∑ d : G, Fn d = ∑ u : U, D.what₂.embLL ((ψ u)⁻¹ : D.what₂.LLˣ) *
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (u : G)) S g := by
    calc ∑ d : G, Fn d = ∑ d ∈ Finset.univ.filter (· ∈ U), Fn d :=
          (Finset.sum_filter_of_ne fun d _ h => by
            by_contra hd
            exact h (by simp only [hFn, dif_neg hd, zero_mul])).symm
      _ = ∑ u : U, Fn u := Finset.sum_subtype _ (by simp) Fn
      _ = _ := Finset.sum_congr rfl fun u _ => by simp only [hFn, dif_pos u.2]
  have e2 : ∑ u : U, D.what₂.embLL ((ψ u)⁻¹ : D.what₂.LLˣ) *
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (u : G)) S g =
      ∑ u : U, D.what₂.embLL ((ψ u⁻¹)⁻¹ : D.what₂.LLˣ) *
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u⁻¹ : U) : G)) S g :=
    (Equiv.sum_comp (Equiv.inv U) (fun u : U => D.what₂.embLL ((ψ u)⁻¹ : D.what₂.LLˣ) *
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (u : G)) S g)).symm
  rw [e2] at e1
  calc _ = D.what₂.embLL c * ∑ d : G, Fn d := by
        rw [e1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [map_inv, inv_inv, Subgroup.coe_inv]
        ring
    _ = _ := by
        congr 1


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.OneMapExact.one_term : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, ∀ u : U, adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i h01 hβ h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16
    U hU χ ξR ω φ h17 Λ h h18 h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27
  have hterm := GlobalTheory.T.shortSeries_trace_term_at_evaluationVector D G Pl0 T0 A T R F κ v₀ fw O hT hC i h01 hβ h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16 U hU χ ξR ω φ h17 Λ h h18 h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27
  obtain ⟨y₀, c, hr, hc, H⟩ := hterm
  exact ⟨y₀, c, hr, hc, fun φ' hφ' w u =>
    GlobalTheory.T.lowestTypeEquality_of_evaluationVector D G Pl0 T0 A T R F κ v₀ fw O hT hC i h01 h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16 U χ ξR ω φ h17 Λ h (GlobalTheory.OneMapExact.splitOff_of_dvd (dvd_mul_right _ _) h18) h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27 y₀ c hr φ' hφ' u (fun w₀ hw₀ => H φ' hφ' w₀ hw₀ u) w⟩


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.OneMapExact.trace_short_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (ψ : U →* D.what₂.LLˣ) χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • levelTrace R i U ψ (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i h01 hβ h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16
    U hU ψ χ ξR ω φ h17 Λ h h18 h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27
  obtain ⟨y₀, c, hr, hc, H⟩ := GlobalTheory.OneMapExact.one_term D G Pl0 T0 A T R F κ v₀ fw O hT hC i h01 hβ h02 h03 h04 h05 h06 v h07 h08 h09 h10 h11 h12 h13 h14 ℓ h15 h16 U hU χ ξR ω φ h17 Λ h h18 h19 N x₀ P x f y h20 h21 h22 h23 h24 h25 h26 h27
  exact ⟨y₀, c, hr, hc, fun φ' hφ' w => GlobalTheory.OneMapExact.trace_of_terms R i U ψ _ c _ _ (H φ' hφ' w)⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitEquivariantBijectionTransportCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trait_equivariant_bijection_transport_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α) → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), Eqv T.D'.toPre T.A F (C.n ^ j) lab' E' → ∃ (lab : QkPt D.toPre F (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A)) (E : Fam D.toPre F (C.n ^ j) → SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)) (Φ : Fam D.toPre F (C.n ^ j) → Fam T.D'.toPre F (C.n ^ j)), LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ (∀ (s : Fam D.toPre F (C.n ^ j)) (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)), F₀.Over s → (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((Φ s).s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1)) ∧ ∀ (s : Fam D.toPre F (C.n ^ j)) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' (Φ s)) q z Jt := by
  first | exact @GlobalTheory.Mum.trait_transport | exact GlobalTheory.Mum.trait_transport | (intros; apply GlobalTheory.Mum.trait_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopChernFormGoodPatch
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem hasInt_patch_transgression : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → ∃ a b : ℝ, HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) a ∧ HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H₀ c y) (ptsIn X.str σ ⊤) b ∧ HasInt (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) (a - b) := by
  intro F _ σ X m E O H H₀ hH hH₀ e S A W c hP ρ hρ hsupp
  obtain ⟨hUo, hUoff, hcpt⟩ := _root_.GlobalTheory.GoodTop.goodPatch_image E O H hP
  have h1 := _root_.GlobalTheory.GoodTop.hasInt_mul_topDens_goodPatch E O H H₀ hH hH₀ hP hρ hsupp
  have h0 := _root_.GlobalTheory.GoodTop.hasInt_cut_topDens_patch E O H H₀ hH hH₀ hP hρ hsupp
  have hc := _root_.GlobalTheory.GoodTop.hasInt_corrDens_of_goodPatch E O H H₀ hH hH₀ hP hρ hsupp
  refine ⟨_, _, h1, h0, ?_⟩
  have hloc := _root_.GlobalTheory.GoodTop.integral_cutTop_sub S (e '' W) (e '' tsupport ρ) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ())
    (fun v => ρ (e.symm v)) c hUo (hcpt _ (isClosed_tsupport ρ) hsupp) (Set.image_mono hsupp)
    (by
      rintro v ⟨z, hz, rfl⟩ a ha
      exact hP.small z hz a ha)
    (by
      rintro v ⟨z, hz, rfl⟩
      exact _root_.GlobalTheory.GoodTop.gram_smooth_isUnit_holoChart E ⊤ H₀ hH₀ hP.holo mem_ptsIn_top (hP.sub hz) (hP.frame z hz))
    (by
      intro v hv
      rw [← hUoff] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact _root_.GlobalTheory.GoodTop.gram_smooth_isUnit_holoChart E O H hH hP.holo hzO (hP.sub hz) (hP.frame z hz))
    (by
      intro v hv a i j
      rw [← hUoff] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.form z hz hzO a i j)
    (by
      intro v hv a b i j
      rw [← hUoff] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.dbar z hz hzO a b i j)
    (by
      rintro v ⟨z, hz, rfl⟩
      exact (_root_.GlobalTheory.GoodTop.contDiffAt_holoChart hP.holo (hP.sub hz) (hρ z)).contDiffWithinAt)
    (by
      rintro v ⟨z, hz, rfl⟩ hv
      rw [e.left_inv (hP.sub hz)]
      by_contra h
      exact hv ⟨z, subset_tsupport _ h, rfl⟩)
  convert hc using 1
  rw [← mul_sub, ← Complex.sub_re, hloc]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoTraitUniformisationsMatchingData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

noncomputable section

namespace GlobalTheory.TInj

theorem lbIso_cube_of_lam {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (f : G ⟶ G')
    (H : LBIso (abelian₂ G L) ((abelian₂ G' L').pull (lift (fst G G ≫ f) (snd G G ≫ f) : G2 G ⟶ G2 G').left)) :
    LBIso (cubeLB G' ![fst G G ≫ f, snd G G ≫ f] L') (cubeLB G ![fst G G ≫ 𝟙 G, snd G G ≫ 𝟙 G] L) := by
  have hΛ' : (abelian₂ G' L').IsLB := LB.isLB_linComb hL' _ _
  have e₁ : cubeCls G (x2 G) (cls L hL) = CechPic.pull (lift (fst G G ≫ f) (snd G G ≫ f) : G2 G ⟶ G2 G').left
      (cubeCls G' (x2 G') (cls L' hL')) :=
    (cls_cubeLB G _ hL).symm.trans (((cls_eq_iff _ (pull_isLB hΛ' _)).2 H).trans
      ((cls_pull hΛ' _ _).trans (congrArg _ (cls_cubeLB G' _ hL'))))
  rw [pull_cubeCls G' _ ![fst G G ≫ f, snd G G ≫ f] _ (fun i => by fin_cases i <;> simp [x2])] at e₁
  refine (cls_eq_iff (LB.isLB_linComb hL' _ _) (LB.isLB_linComb hL _ _)).1
    ((cls_cubeLB G' _ hL').trans (Eq.trans ?_ (cls_cubeLB G _ hL).symm))
  rw [← e₁]
  simp only [Category.comp_id]
  rfl


set_option maxHeartbeats 1000000 in
theorem two_unif_match : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (D₁ : DegData V (maximalIdeal V)) (A₁ : PolAV (Sp (FractionRing V))) (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal V) D₁ A₁ G₁) (D₂ : DegData V (maximalIdeal V)) (A₂ : PolAV (Sp (FractionRing V))) (G₂ : Over (Sp V)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal V) D₂ A₂ G₂), IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (y : Sp (FractionRing V) ⟶ X) (α₁ : A₁.A.left ⟶ c.A.left) (α₂ : A₂.A.left ⟶ c.A.left), OverPt c A₁ y α₁ → OverPt c A₂ y α₂ → ∃ (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Match D₁.toPre D₂.toPre b φ (AlgebraicClosure (FractionRing V)) ∧ ∀ k : ℕ, 1 ≤ k → ∀ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) k) (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) k) (x₁ : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A₁.A) (x₂ : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A₂.A), QkToAkU U₁.toUnifPre (AlgebraicClosure (FractionRing V)) k p₁ x₁ → QkToAkU U₂.toUnifPre (AlgebraicClosure (FractionRing V)) k p₂ x₂ → x₁.left ≫ α₁ = x₂.left ≫ α₂ → QImg b φ p₁ p₂ := by
  intro X g n B _ ζ sX c V _ _ _ _ hc D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ hG₁ hG₂ y α₁ α₂ hO₁ hO₂
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨a, cA, ha, hcA, gen, hα, hlbA⟩ := _root_.GlobalTheory.TInj.exists_iso_of_overPt c V (maximalIdeal V) hA D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂
    U₂.toUnifPre hG₁ hG₂ y α₁ α₂ hO₁ hO₂
  obtain ⟨b, h, hbi, lin, coord⟩ := _root_.GlobalTheory.TInj.iso_lin_coord V (maximalIdeal V) hA D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre a ha
  have hb : IsMonHom b := lin.2.1
  have hov : Over₀ U₁.toUnifPre U₂.toUnifPre a.hom b := lin.2.2.1
  have hlbG := _root_.GlobalTheory.TInj.lbIso_lam_of_generic V (maximalIdeal V) hA D₁ A₁ G₁ U₁.toUnifPre D₂ A₂ G₂ U₂.toUnifPre hG₁ a.hom cA.hom ha hcA
    gen hlbA
  have hlbB := _root_.GlobalTheory.HomMum.lbIso_descends V hA D₁ D₂ A₁ A₂ G₁ G₂ hG₁ hG₂ U₁ U₂ a.hom a.hom b b ha ha hb hb hov hov hlbG
  have hnrm : ∀ χ, ∃ u : LB.Gen (CmpLB D₁.toPre D₂.toPre b (h.toAddMonoidHom χ) χ), Nrm u :=
    fun χ => (coord χ).imp fun _ => And.left
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨v, hv⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 V ϖ hϖ
  have key := GlobalTheory.Mum.Two.KeyDvr.main V hc ϖ hϖ (AlgebraicClosure (FractionRing V)) v hv D₁ D₂ A₁ A₂ G₁ G₂ hG₁ hG₂
    U₁ U₂ a.hom cA.hom b h.toAddMonoidHom hcA gen lin coord h.injective
  obtain ⟨E, eG, eA, -, eh, -⟩ :=
    (GlobalTheory.IntEnd.exists_nsmul_and_neg GlobalTheory.firstFiveLaws V (maximalIdeal V) hA D₁ A₁ G₁ hG₁ U₁).1 1
  have H₁ : LBIso (cubeLB G₁ ![fst G₁ G₁ ≫ E.aG, snd G₁ G₁] U₁.LG.L)
      (cubeLB G₁ ![fst G₁ G₁, snd G₁ G₁ ≫ E.aG] U₁.LG.L) := by
    rw [eG, pow_one, Category.comp_id, Category.comp_id]
    exact GlobalTheory.PolBaseChange.lbIso_refl (LB.isLB_linComb U₁.LG.isLB _ _)
  have H₂ : LBIso (cubeLB A₂.A ![fst A₁.A A₁.A ≫ cA.hom, snd A₁.A A₁.A ≫ cA.hom] A₂.L)
      (cubeLB A₁.A ![fst A₁.A A₁.A ≫ E.aA, snd A₁.A A₁.A ≫ 𝟙 A₁.A] A₁.L) := by
    rw [eA, pow_one]
    exact lbIso_cube_of_lam A₁.isLB A₂.isLB cA.hom hlbA
  obtain ⟨φ', hφ', hhφ'⟩ := GlobalTheory.Mum.Two.periods_of_key V (maximalIdeal V) hA D₁ D₂ A₁ A₂ G₁ G₂ hG₁ hG₂ U₁ U₂ a.hom
    cA.hom b h.toAddMonoidHom hcA gen lin coord E E H₁ H₂ _ key
  have hφe : ∀ y₀, φ' y₀ = h.symm y₀ := fun y₀ => h.injective (by
    show h (φ' y₀) = h (h.symm y₀)
    rw [h.apply_symm_apply]
    exact (hhφ' y₀).trans (by rw [eh, one_smul]))
  have hM : Match D₁.toPre D₂.toPre b h.symm (AlgebraicClosure (FractionRing V)) := by
    refine ⟨hb, hbi, hlbB, hnrm, fun y₀ g₀ hy => ?_⟩
    obtain ⟨g', h1, h2⟩ := hφ' y₀ g₀ hy
    exact ⟨g', h1, hφe y₀ ▸ h2⟩
  refine ⟨b, h.symm, hM, fun k hk p₁ p₂ x₁ x₂ hq₁ hq₂ hx => ?_⟩
  obtain ⟨g', hg', -⟩ :=
    (GlobalTheory.Mum.Two.act_two_hom V D₁.toPre D₂.toPre b h.toAddMonoidHom hb hnrm (AlgebraicClosure (FractionRing V))).1 p₁.g
  obtain ⟨p', rfl, hp'⟩ := key k hk p₁ x₁ hq₁ g' hg'
  have hxx : x₁ ≫ cA.hom = x₂ := by
    apply Over.OverMorphism.ext
    apply hO₂.1.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hα, hx]
    · rw [Over.comp_left, Category.assoc, Over.w, Over.w, Over.w]
  refine ⟨p', _root_.GlobalTheory.TInj.qImg_lattice V (maximalIdeal V) hA D₁ D₂ b h.symm _ hM k p₁ p' hg', hg',
    (GlobalTheory.T.torsionPointOfPair_exists_torsion_injective_upToEquiv V (maximalIdeal V) hA D₂ A₂ G₂ U₂ hG₂ _ k hk).2 p' p₂ x₂ (hxx ▸ hp') hq₂⟩

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeOfKernelInGeneratingOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem unif_baseChange_of_psiUnitOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ φ : R →+* R', IsLocalHom φ → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → spMap φ (genericPoint (Sp R')) ∈ W → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∃ (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif (maximalIdeal R') D' A' G'), IsPullUnif φ hD bc U U' := by
  intro R _ _ _ hR D A G _ _ hG U R' _ _ _ hR' φ hφl W hψ hgen G' _ _ bc mbc
  obtain ⟨hL, -, -, h4, -⟩ := GlobalTheory.firstFiveLaws
  have aR := hR.1
  have hI : (maximalIdeal R).map φ ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff φ a).2 ha
  let x : Sp (FractionRing R') ⟶ Sp R := jK R' ≫ specOf φ
  have hxW : Set.range x ⊆ (W : Set (Sp R)) := by
    rintro _ ⟨z, rfl⟩
    have hz : (jK R').base z = genericPoint (Sp R') := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap R' (FractionRing R')) z.asIdeal = ⊥
      haveI := z.isPrime
      rw [Ideal.eq_bot_of_prime z.asIdeal]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R' (FractionRing R'))
    show (specOf φ).base ((jK R').base z) ∈ W
    rw [hz]
    exact hgen
  obtain ⟨hamp, hkt⟩ := _root_.GlobalTheory.Mum.PolFibre.relAmple_kTriv_fibre R hR D A G hG U W hψ (FractionRing R') x hxW
  have hBs := IsSemiAbelian.pullback x G hG
  have hab : IsAbelianScheme ((Over.pullback x).obj G) :=
    ⟨hBs.comm, hBs.smooth, GlobalTheory.ZH.isProper_hom_of_relAmple hamp, hBs.geomConnected⟩
  have hpbG := isGrpPullback_pullback G x
  haveI := mbc
  have hbc : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  have hgK := (isGrpPullback_pullback G' (jK R')).comp hbc
  obtain ⟨eA, meA, heA⟩ := grpPullback_iso hgK hpbG

  have := hG.smooth
  have := hG.geomConnected
  have : ConnectedSpace (Sp R) := inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have hgA := GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
  have dA : d = A.g := H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgA.1 hd)
    A.smoothDim (eSec A.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R)))
  have hdB : SmoothOfRelativeDimension A.g ((Over.pullback x).obj G).hom :=
    dA ▸ (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hpbG.1 hd
  let A' : PolAV (Sp (FractionRing R')) :=
    { A := (Over.pullback x).obj G
      isAb := hab
      g := A.g
      smoothDim := hdB
      L := U.LG.L.pull (pullback.fst G.hom x)
      isLB := pull_isLB U.LG.isLB _
      rigid := GlobalTheory.PolBaseChange.rigidified_pull hpbG ⟨U.LG.rig, U.LG.rigGen⟩
      sym := GlobalTheory.PolBaseChange.sym_pull hpbG (GlobalTheory.WtPoint.sym_of_cp (GlobalTheory.ValueForm.modelCP U.toUnifPre hL.globalFns))
      ample := hamp
      ktriv := hkt }
  have wA : ∃ wA : LB.Iso (A'.L.pull eA.hom.left)
      (U.LG.L.pull (pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ))), wA.IsGen := by
    rw [← heA]
    exact ⟨GlobalTheory.Proof.TautologicalModel.taut U.LG.L _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen U.LG.isLB _ _⟩
  have he := GlobalTheory.PolBaseChange.eSec_comm hbc
  let L' : RigLB G' := ⟨U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)),
    rigPullOf (G' := G') (G := G) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig,
    pull_isLB U.LG.isLB _,
    GlobalTheory.Proof.TautologicalModel.rigPullOf_isGen (G' := G') (G := G) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he
      U.LG.L U.LG.rig U.LG.rigGen⟩
  obtain ⟨wL, gL, rL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (specOf φ) G G' _ he U.LG L'
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB U.LG.isLB _))
  have hWne : (W : Set (Sp R)).Nonempty := ⟨_, hgen⟩
  obtain ⟨D', hD, U', -, -, hP⟩ := h4.unifBaseChange R R' _ _ aR hR' φ hI D A G hG U W
    (GlobalTheory.PelCoordPull.nonempty_psiOn D.toPre W hWne hψ) hgen G' bc mbc A' rfl eA meA wA L' wL he gL rL
  exact ⟨D', A', hD, U', hP⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_convergence_of_kernel : GlobalTheory.ThK.KP → GlobalTheory.ThK.WeilConv := by
  first | exact @GlobalTheory.ThKWeil.weilConv | exact GlobalTheory.ThKWeil.weilConv | (intros; apply GlobalTheory.ThKWeil.weilConv <;> assumption)
end

