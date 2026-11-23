module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2482
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0173
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbackAlongIdLiesOverDataIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two.PullLin

open GlobalTheory.Mum.Two.HomConst

theorem map_fstG {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Sp R)) (ψ : G ⟶ G) :
    ((Over.pullback (thick R I e)).map ψ).left ≫ (fstG I e G).left = (fstG I e G).left ≫ ψ.left := by
  simp [fstG, pullback.lift_fst]

end GlobalTheory.Mum.Two.PullLin


open GlobalTheory.Mum.Two.PullLin GlobalTheory.Mum.Two.HomConst in
theorem GlobalTheory.Mum.Two.isPullUnif_id_over₀_onTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (ψ : G ⟶ G) (bc : G ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (b : D'.toPre.P.A ⟶ D.toPre.P.A), IsMonHom ψ → bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.left → hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = b.left → IsPullUnif (RingHom.id R) hD bc U U' → Over₀ U'.toUnifPre U.toUnifPre ψ b ∧ OnTorus U'.toUnifPre U.toUnifPre ψ hD.xe.symm := by
  intro R _ _ _ hB D A G _ _ hG U D' A' U' hD ψ bc b hψ hbc hb hP
  obtain ⟨hR, -⟩ := hB
  obtain ⟨wL, -, he, -, hlev⟩ := hP.lg

  have lev : ∀ e, ∃ h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left,
      h = ((Over.pullback (thick R (maximalIdeal R) e)).map ψ).left ∧
      (U'.gt e).pG.left ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
        h ≫ (U.gt e).pG.left ∧
      (∀ x : D'.toPre.X, ∃ hψ : ∀ k : Fin 4,
          D'.toPre.Oφ ((U'.gt e).pG) x k ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
            h ≫ D.toPre.Oφ ((U.gt e).pG) (hD.xe x) k,
        LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) ((U'.gt e).t x)
          (GeneratorPullback.pullAlong D.toPre.P.L (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) h _
            Oinvε _ hψ ((U.gt e).t (hD.xe x)))) := by
    intro e
    obtain ⟨h, h1, h2, h3, -⟩ := hlev e
    have : Mono (fstG (maximalIdeal R) e G).left :=
      inferInstanceAs (Mono (pullback.fst G.hom (thick R (maximalIdeal R) e)))
    refine ⟨h, (cancel_mono (fstG (maximalIdeal R) e G).left).1 ?_, h2, h3⟩
    rw [h1, hbc, map_fstG]
  refine ⟨fun e => ?_, ?_⟩
  · obtain ⟨h, rfl, h2, -⟩ := lev e
    have : Mono (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) := inferInstance
    refine Over.OverMorphism.ext ((cancel_mono (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e))).1 ?_)
    rw [hb] at h2
    clear lev hlev hP wL he
    simp only [Over.comp_left, Category.assoc]
    refine Eq.trans ?_ (h2.symm.trans ?_)
    · rfl
    · show (U'.gt e).q.left ≫ pullback.fst D'.toPre.P.A.hom (thick R (maximalIdeal R) e) ≫ b.left = _
      congr 1
      exact (pullback.lift_fst _ _ _).symm
  · obtain ⟨-, -, -, hC⟩ := id hR
    obtain ⟨h₀, hT⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R (maximalIdeal R) hR D' D A' A G G U'.toUnifPre
      U.toUnifPre ψ hψ
    have key : (h₀ : D.toPre.X → D'.toPre.X) = hD.xe.symm := by
      haveI := hC
      obtain ⟨t, ht, hi⟩ := hT 0
      refine acts_unique (U'.gt 0) (U.gt 0) (acts_of_torusHomOf _ _ _ ht hi) ?_
      obtain ⟨h, rfl, -, h3⟩ := lev 0
      clear lev hlev hP wL he hT ht hi
      intro Z r z J₁ J₂ hJ₁ hJ₂ c χ
      obtain ⟨x, rfl⟩ := hD.xe.surjective χ
      rw [AddEquiv.symm_apply_apply]
      obtain ⟨hψk, M⟩ := h3 x
      have P := (maps_iff hD.w _ _ Oinvε _ _ _ _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψk ·) (fun _ => rfl)).1 M
      have e := P Z r z
        (fun k => J₂ ((r ≫ D'.toPre.Oφ (U'.gt 0).pG x k) ≫ hD.e.hom.left ≫
          pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))))
        (fun k => J₁ (r ≫ D'.toPre.Oφ (U'.gt 0).pG x k)) (fun k => hJ₂ _) (fun k => hJ₁ _)
      have h1 := GlobalTheory.ArcLieCompare.prod_Oφ_zero (D := D'.toPre) (U'.gt 0).pG r
        (r ≫ (fstG (maximalIdeal R) 0 G).left ≫ G.hom) (c.trans (by simp only [Category.assoc])) x
        (fun f => gw hD.w f z (J₂ (f ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)))) (J₁ f))
      rw [h1, _root_.one_mul] at e
      rw [val_of _ _ z J₂
          (fun k => J₂ ((r ≫ D'.toPre.Oφ (U'.gt 0).pG x k) ≫ hD.e.hom.left ≫
            pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))))
          (fun k => by simp only [Category.assoc, hψk k]),
        val_of _ r z J₁ (fun k => J₁ (r ≫ D'.toPre.Oφ (U'.gt 0).pG x k)) (fun k => rfl)]
      exact e
    rw [key] at hT
    exact hT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedEighthPowerBundleClassEqSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.SharpBundle

open GlobalTheory.ZH.EndoExtend GlobalTheory.SquareOfGeneric

theorem prod_left_ext {S : Scheme.{0}} {X Y : Over S} {Z : Scheme.{0}} (f g : Z ⟶ (X ⊗ Y).left)
    (h₁ : f ≫ (fst X Y).left = g ≫ (fst X Y).left) (h₂ : f ≫ (snd X Y).left = g ≫ (snd X Y).left) : f = g := by
  apply pullback.hom_ext
  · simpa using h₁
  · simpa using h₂

theorem cls_eq_sum_lam : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : GlobalTheory.ZM.SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀) (y : Sp (FractionRing R) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → ∀ pr : Fin 8 → (A.A ⟶ c.A), LBIso A.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ q : Fin 8 → (G ⟶ G₀), (∀ u, IsMonHom (q u)) → (∀ u, ((Over.pullback (jK R)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → cls U.LG.L U.LG.isLB = ∑ a, ∑ b, W a b • lam (cls U₀.LG.L U₀.LG.isLB) (q a) (q b) := by
  intro g n o _ ζ F W R _ _ _ hR D D₀ A A₀ G G₀ _ _ _ _ hG U U₀ y α α₂ hα hαs hαL c φc φ₂ hφ hφs hφL pr hP q hq hqg
  obtain ⟨hno, -, hic, -⟩ := hR.1
  have hS : IsSemiAbelian G := hG
  have := hS.smooth
  have := hS.geomConnected
  have := geometricallyIntegral_of_smooth G.hom
  have := U₀.gen_hom
  have hL := U.LG.isLB
  have hL₀ := U₀.LG.isLB
  have hA := A.isLB
  have hA₀ := A₀.isLB
  have hcP := c.isLB
  have hUP := F.univ.isLB
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have h₃ : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have hn : Geo.Tor.IsNormalScheme (Sp R) := (GlobalTheory.isNormalScheme_iff_pred _).1 inferInstance

  have key : ∀ a b, CechPic.pull U.gen.hom.left (CechPic.pull (lift (pr a) (pr b)).left (cls c.P hcP)) =
      CechPic.pull (pullback.fst G.hom (jK R)) (lam (cls U₀.LG.L hL₀) (q a) (q b)) := by
    intro a b
    have eP : cls c.P hcP = CechPic.pull φ₂ (cls F.univ.P hUP) := (cls_eq_iff hcP (pull_isLB hUP _)).2 hφL
    have eΛ : CechPic.pull α₂ (cls F.univ.P hUP) = lam (cls A₀.L hA₀) (fst A₀.A A₀.A) (snd A₀.A A₀.A) :=
      ((cls_eq_iff (LB.isLB_linComb hA₀ _ _) (pull_isLB hUP _)).2 hαL).symm.trans (cls_cube_two hA₀ _ _ _)
    have eK : (U.gen.hom ≫ lift (pr a) (pr b)).left ≫ φ₂ =
        (lift ((Over.pullback (jK R)).map (q a) ≫ U₀.gen.hom) ((Over.pullback (jK R)).map (q b) ≫ U₀.gen.hom)).left ≫ α₂ := by
      apply GlobalTheory.SharpBundle.prod_left_ext
      · rw [Category.assoc, hφs.1, Category.assoc, hαs.1, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
          ← Over.comp_left, Category.assoc, lift_fst, lift_fst]
        exact (hqg a).symm
      · rw [Category.assoc, hφs.2, Category.assoc, hαs.2, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
          ← Over.comp_left, Category.assoc, lift_snd, lift_snd]
        exact (hqg b).symm
    have hext₀ : CechPic.pull U₀.gen.hom.left (cls A₀.L hA₀) =
        CechPic.pull (pullback.fst G₀.hom (jK R)) (cls U₀.LG.L hL₀) := by
      obtain ⟨w, hw⟩ := U₀.ext
      rw [← cls_pull hL₀ _ (pull_isLB hL₀ _), ← cls_pull hA₀ _ (pull_isLB hA₀ _)]
      exact (cls_eq_iff _ _).2 ⟨w, hw⟩
    rw [← pull_comp, ← Over.comp_left, eP, ← pull_comp, eK, pull_comp, eΛ, pull_lam, lift_fst, lift_snd, ← lam_pull,
      hext₀, lam_pull_fst]
    let hh : Over.mk (((Over.pullback (jK R)).obj G).hom ≫ jK R) ⟶ G :=
      Over.homMk (pullback.fst G.hom (jK R)) pullback.condition
    show _ = CechPic.pull hh.left _
    rw [pull_lam]
    congr 1 <;> ext1 <;> exact pullback.lift_fst _ _ _
  refine pic_ext (jK R) hn G (eSec G) (Over.w η[G]) ?_ ?_
  · have h0 : CechPic.pull (eSec G) (cls U.LG.L hL) = 0 :=
      (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨U.LG.rig, U.LG.rigGen⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h0, map_sum]
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    have := hq a
    have := hq b
    have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ G₀) = η[G₀] := by rw [Hom.one_def]; simp
    rw [map_zsmul]
    show _ • CechPic.pull η[G].left _ = 0
    rw [pull_lam, IsMonHom.one_hom, IsMonHom.one_hom, ← e₁, lam_one_left, smul_zero]
  · have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
        CechPic.pull U.gen.hom.left (cls A.L hA) := by
      obtain ⟨w, hw⟩ := U.ext
      rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
      exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc', (cls_eq_iff hA (LB.isLB_linComb hcP _ _)).2 hP, cls_linComb hcP, map_sum, map_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_zsmul, map_zsmul, key]

end GlobalTheory.SharpBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedFrameRatioIntegralFrameChartIndepende
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.Poinc.FrameIndep

theorem ratio_indep {X H Y Z B B' : Scheme.{0}} {L : LB X} {M : LB H} {f : Y ⟶ H} {ψ : Y ⟶ X}
    (w : LB.Iso (L.pull ψ) (M.pull f)) (hw : w.IsGen) {e : B ⟶ X} {e' : B' ⟶ H}
    {a : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => e) (fun _ => 1))}
    {a' : LB.Gen (LB.LinComb M (K := Fin 1) (fun _ => e') (fun _ => 1))} (ha : a.IsGen)
    (ha' : a'.IsGen) (r : Z ⟶ Y) (t : Z ⟶ B) (t' : Z ⟶ B') (p : Z ⟶ X) (p' : Z ⟶ H)
    (h : r ≫ ψ = p) (h' : r ≫ f = p') (k : t ≫ e = p) (k' : t' ≫ e' = p') (z : Z)
    {J J' I I'} (hJ : Good L z J) (hJ' : Good M z J') (hI : Good L z I) (hI' : Good M z I') :
    Geo.Tor.gw w r z (J' p') (fun _ => J p) * val a t z J * (val a' t' z J')⁻¹ =
      Geo.Tor.gw w r z (I' p') (fun _ => I p) * val a t z I * (val a' t' z I')⁻¹ := by
  subst h h'
  have e₁ : val a t z J = _ * val a t z I := gen_trans ha t z (hJ.mem _ t) (hI.mem _ t)
  have e₂ : val a' t' z J' = _ * val a' t' z I' := gen_trans ha' t' z (hJ'.mem _ t') (hI'.mem _ t')
  have e₃ : Geo.Tor.gw w r z (J' (r ≫ f)) (fun _ => J (r ≫ ψ)) =
      _ * Geo.Tor.gw w r z (I' (r ≫ f)) (fun _ => I (r ≫ ψ)) :=
    (Geo.Tor.isGen_iff w).1 hw Z r z _ _ _ _ (hJ' (r ≫ f)) (hI' (r ≫ f))
      (mem_pull.2 (hJ (r ≫ ψ))) (mem_pull.2 (hI (r ≫ ψ)))
  rw [Geo.Tor.gm_pull_g L ψ r z _ _ (mem_pull.2 (hJ (r ≫ ψ))) (mem_pull.2 (hI (r ≫ ψ)))] at e₃
  rw [Geo.Tor.trF, Fintype.prod_unique, zpow_one] at e₁ e₂
  rw [k] at e₁
  rw [k'] at e₂
  rw [e₁, e₂, e₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem frame_ratio_indep : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x), e.IsGen → ∀ (h : 𝟙_ (Over (Sp V)) ⟶ G) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))), f.IsGen → GlobalTheory.Poinc.IntTerm.Ext U x h → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA JA' : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG JG' : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → Good A.L z JA' → Good U.LG.L z JG' → Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA x.left) * val (Z := (TF (R := V) (FractionRing V)).left) e (𝟙 _) z JA * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG)⁻¹ = Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG' (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA' x.left) * val (Z := (TF (R := V) (FractionRing V)).left) e (𝟙 _) z JA' * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG')⁻¹ := by
  intro V _ _ I D A G _ _ U w₀ hw₀ x e he h f hf hx z JA JA' JG JG' hJA hJG hJA' hJG'
  refine ratio_indep w₀ hw₀ he hf (x.left ≫ U.gen.inv.left) (𝟙 _) (toUnit (TF (R := V) (FractionRing V))).left
    x.left (toUnit (TF (R := V) (FractionRing V)) ≫ h).left ?_ ?_ (Category.id_comp _) rfl z hJA hJG hJA' hJG'
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (x.left ≫ ·) (congrArg (·.left) U.gen.inv_hom_id)).trans (Category.comp_id _)
  · exact (Category.assoc _ _ _).trans hx

end GlobalTheory.Poinc.FrameIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupIsoAbelianPartCharacterIsos
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.TInj

theorem torusHomOf_comp' {S : Scheme.{0}} {X₁ X₂ X₃ : Type} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    {h : X₂ → X₁} {k : X₃ → X₂} {t : splitTorus S X₁ ⟶ splitTorus S X₂} {s : splitTorus S X₂ ⟶ splitTorus S X₃}
    (ht : TorusHomOf h t) (hs : TorusHomOf k s) : TorusHomOf (fun χ => h (k χ)) (t ≫ s) := fun χ => by
  rw [← ht (k χ), ← hs χ]
  refine unit_ext fun z _ => ?_
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_
  refine Eq.symm (((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_)
  refine ((gm_res _ z (V := ⊤) _ trivial _).trans (gm_pull _ _ z ⊤ trivial _)).trans ?_
  rfl

theorem torusHomOf_id' {S : Scheme.{0}} (X : Type) [AddCommGroup X] : TorusHomOf (fun χ : X => χ) (𝟙 (splitTorus S X)) :=
  fun χ => unit_ext fun z _ =>
    ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans rfl

theorem iso_lin_coord : ∀ (R : Type) [CommRing R] [IsDomain R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂) (a : G₁ ≅ G₂), IsMonHom a.hom → ∃ (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X ≃+ D₁.toPre.X), IsIso b ∧ Lin U₁ U₂ a.hom b h.toAddMonoidHom ∧ Coord U₁ U₂ a.hom b h.toAddMonoidHom := by
  intro R _ _ J hR D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ a ha
  have ha' : IsMonHom a.inv := inferInstance
  obtain ⟨b, hb, hbO⟩ := exists_abelian_hom R J hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a.hom ha
  obtain ⟨b', hb', hb'O⟩ := exists_abelian_hom R J hR D₂ D₁ A₂ A₁ G₂ G₁ U₂ U₁ a.inv ha'
  obtain ⟨h, hh⟩ := unifPre_hom_character_const R J hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a.hom ha
  obtain ⟨h', hh'⟩ := unifPre_hom_character_const R J hR D₂ D₁ A₂ A₁ G₂ G₁ U₂ U₁ a.inv ha'
  have oComp : ∀ {Da Db : DegData R J} {Aa Ab : PolAV (Sp (FractionRing R))} {Ga Gb : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] [GrpObj Gb] [IsCommMonObj Gb]
      (Ua : UnifPre J Da Aa Ga) (Ub : UnifPre J Db Ab Gb) (f : Ga ⟶ Gb) (g : Gb ⟶ Ga) c c',
      Over₀ Ua Ub f c → Over₀ Ub Ua g c' → Over₀ Ua Ua (f ≫ g) (c ≫ c') := by
    intro Da Db Aa Ab Ga Gb _ _ _ _ Ua Ub f g c c' hf hg e
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hg e, ← Category.assoc, hf e, Category.assoc]
  have tComp : ∀ {Da Db : DegData R J} {Aa Ab : PolAV (Sp (FractionRing R))} {Ga Gb : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] [GrpObj Gb] [IsCommMonObj Gb]
      (Ua : UnifPre J Da Aa Ga) (Ub : UnifPre J Db Ab Gb) (f : Ga ⟶ Gb) (g : Gb ⟶ Ga) k k',
      OnTorus Ua Ub f k → OnTorus Ub Ua g k' → OnTorus Ua Ua (f ≫ g) (fun χ => k (k' χ)) := by
    intro Da Db Aa Ab Ga Gb _ _ _ _ Ua Ub f g k k' hf hg e
    obtain ⟨t, ht, hi⟩ := hf e
    obtain ⟨s, hs, hj⟩ := hg e
    refine ⟨t ≫ s, torusHomOf_comp' ht hs, ?_⟩
    rw [Functor.map_comp, ← Category.assoc, hi, Category.assoc, hj, Category.assoc]
  have oId : ∀ {Da : DegData R J} {Aa : PolAV (Sp (FractionRing R))} {Ga : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] (Ua : UnifPre J Da Aa Ga), Over₀ Ua Ua (𝟙 Ga) (𝟙 _) := by
    intro Da Aa Ga _ _ Ua e
    simp
  have tId : ∀ {Da : DegData R J} {Aa : PolAV (Sp (FractionRing R))} {Ga : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] (Ua : UnifPre J Da Aa Ga), OnTorus Ua Ua (𝟙 Ga) (fun χ => χ) := by
    intro Da Aa Ga _ _ Ua e
    exact ⟨𝟙 _, torusHomOf_id' _, by simp⟩
  have u₁ := over₀_onTorus_unique R J hR D₁ D₁ A₁ A₁ G₁ G₁ U₁ U₁ (𝟙 G₁)
  have u₂ := over₀_onTorus_unique R J hR D₂ D₂ A₂ A₂ G₂ G₂ U₂ U₂ (𝟙 G₂)
  have bb : b ≫ b' = 𝟙 _ := u₁.1 _ _ (a.hom_inv_id ▸ oComp U₁ U₂ a.hom a.inv b b' hbO hb'O) (oId U₁)
  have bb' : b' ≫ b = 𝟙 _ := u₂.1 _ _ (a.inv_hom_id ▸ oComp U₂ U₁ a.inv a.hom b' b hb'O hbO) (oId U₂)
  have hh₁ : (fun χ => h (h' χ)) = fun χ => χ :=
    u₁.2 _ _ (a.hom_inv_id ▸ tComp U₁ U₂ a.hom a.inv h h' hh hh') (tId U₁)
  have hh₂ : (fun χ => h' (h χ)) = fun χ => χ :=
    u₂.2 _ _ (a.inv_hom_id ▸ tComp U₂ U₁ a.inv a.hom h' h hh' hh) (tId U₂)
  let hE : D₂.toPre.X ≃+ D₁.toPre.X :=
    { toFun := h, invFun := h', left_inv := fun χ => congrFun hh₂ χ, right_inv := fun χ => congrFun hh₁ χ,
      map_add' := h.map_add }
  have hL : Lin U₁ U₂ a.hom b hE.toAddMonoidHom := ⟨ha, hb, hbO, hh⟩
  exact ⟨b, hE, ⟨b', bb, bb'⟩, hL, coord_of_lin R J hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a.hom b _ hL⟩

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupProdZpowCharacterMap
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

theorem torusHomOf_iff_charUnit {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem charUnit_eq_pointsEquiv {S : Scheme.{0}} {X : Type} [AddCommGroup X] (χ : X) :
    charUnit S X χ = GlobalTheory.splitTorusPointsEquiv S X _ (𝟙 _) (Multiplicative.ofAdd χ) :=
  Units.ext ((GlobalTheory.splitTorusPointsEquiv_val S X _ (𝟙 _) χ).trans (GlobalTheory.SplitTorusHom.appTop_id _)).symm

theorem torusHomOf_prod_zpow {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {K : Type}
    [Fintype K] (n : K → ℤ) (h : K → X' → X) (t : K → (splitTorus S X ⟶ splitTorus S X'))
    (ht : ∀ i, TorusHomOf (h i) (t i)) : TorusHomOf (fun χ => ∑ i, n i • h i χ) (∏ i, t i ^ n i) := by
  simp only [torusHomOf_iff_charUnit] at ht
  rw [torusHomOf_iff_charUnit]
  intro χ
  have e₁ : ∀ i, GlobalTheory.splitTorusPointsEquiv S X' _ (t i) (Multiplicative.ofAdd χ) = charUnit S X (h i χ) := fun i =>
    Units.ext ((GlobalTheory.splitTorusPointsEquiv_val S X' _ (t i) χ).trans (ht i χ))
  rw [← GlobalTheory.splitTorusPointsEquiv_val, map_prod]
  simp only [map_zpow]
  rw [charUnit_eq_pointsEquiv, ofAdd_sum, map_prod]
  simp only [ofAdd_zsmul, map_zpow, ← charUnit_eq_pointsEquiv]
  congr 1
  change (MonoidHom.eval (Multiplicative.ofAdd χ)) (∏ x, GlobalTheory.splitTorusPointsEquiv S X' _ (t x) ^ n x) = _
  rw [map_prod]
  simp only [map_zpow, MonoidHom.eval, MonoidHom.flip_apply, MonoidHom.id_apply, e₁]

end GlobalTheory.Mum.PowData

theorem GlobalTheory.Mum.PowData.onTorus_prod_zpow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), ∀ (D D₀ : DegData R I) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], ∀ (U : UnifPre I D A G) (U₀ : UnifPre I D₀ A₀ G₀) (K : Type) [Fintype K] (n : K → ℤ) (a : K → (G ⟶ G₀)) (h : K → D₀.toPre.X → D.toPre.X), (∀ i, OnTorus U U₀ (a i) (h i)) → OnTorus U U₀ (∏ i, a i ^ n i) (fun χ => ∑ i, n i • h i χ) := by
  intro R _ _ I D D₀ A A₀ G G₀ _ _ _ _ U U₀ K _ n a h H e
  choose t ht et using fun i => H i e
  refine ⟨∏ i, t i ^ n i, torusHomOf_prod_zpow n h t ht, ?_⟩
  have := (U₀.gt e).i_hom
  have hm : (Over.pullback (thick R I e)).map (∏ i, a i ^ n i) = ∏ i, (Over.pullback (thick R I e)).map (a i) ^ n i :=
    (map_prod ((Over.pullback (thick R I e)).homMonoidHom (X := G) (M := G₀)) _ _).trans
      (Finset.prod_congr rfl fun i _ => map_zpow ((Over.pullback (thick R I e)).homMonoidHom (X := G) (M := G₀)) _ _)
  rw [hm, comp_prod_zpow, prod_zpow_comp]
  exact Finset.prod_congr rfl fun i _ => by rw [et i]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMemberDividingThetaConstantNeZero
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

theorem UMem.yK_th_ne_zero : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x₀ hd h0
  obtain ⟨c, -, h⟩ := GlobalTheory.ZH.GoodOut.exists_th_notMem GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 X₁.ρ
    ⟨RingHom.ker 𝔪.yK, RingHom.ker_isPrime 𝔪.yK⟩ 0
  refine h (RingHom.mem_ker.2 ?_)
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hd' := hd.of_specializes
    (ξ := (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) (sp _)
  have hs : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have e := RatModel.val_mul hs (hd'.2 (0 + c)) (𝔪.reg _ (X₁.S.th_mem x₀))
  rw [div_mul_cancel₀ _ hd.1] at e
  rw [𝔪.yK_eq] at h0 ⊢
  exact e.trans ((congrArg (_ * ·) h0).trans (mul_zero _))

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VarietyComplexPointsMapIsHolomorphic
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem ptMap_isHolo : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str),
    (atlas X σ).IsHolo (atlas Y σ) (ptMap σ f hf) := fun _ _ _ _ _ f _ =>
  ⟨CxPts.continuous_of_comp (f := f) fun _ => rfl, fun j i => AlgChart.holo_map (f := f) (fun _ => rfl) j i⟩

end GlobalTheory.ChernCalc
end

