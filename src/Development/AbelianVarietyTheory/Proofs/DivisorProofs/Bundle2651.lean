module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2415
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2594
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2601
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2482

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaWitnessesBaseChangeMember
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.TermsMove

theorem tors_mul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {g : GtPtF D F} {n : ℕ} (d : ℕ) (h : ∃ o, GtPtF.IsNsmul n g o ∧ o.IsZero) :
    ∃ o, GtPtF.IsNsmul (n * d) g o ∧ o.IsZero := by
  letI := @TorusExt.gtGroup
  obtain ⟨o, o₁, o₂⟩ := h
  rw [TorusExt.isNsmul_iff_eq] at o₁
  rw [TorusExt.isZero_iff_eq] at o₂
  refine ⟨0, (TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (TorusExt.isZero_iff_eq _).2 rfl⟩
  rw [mul_nsmul, ← o₁, o₂, nsmul_zero]

theorem frExt_isGen {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {E : Type} (F : Type) [Field F] [Algebra (FractionRing R) F] [Field E] [Algebra (FractionRing R) E] [Algebra E F]
    [IsScalarTower (FractionRing R) E F] {x : TFK (R := R) E ⟶ A.A} {e : FrAt x} (he : e.IsGen) : (frExt F e).IsGen :=
  pullGen_isGen A.L _ _ e he (TorsionExt.fieldMap (R := R) E F).left


open GlobalTheory.FieldBaseChange GlobalTheory.TorsionExt GlobalTheory.ArcPull in
set_option maxHeartbeats 800000 in
theorem exists_witnesses : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z)
    (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type)
      (lab : C → X₁.S.Gam)
      (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
      (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : C → GtPtF 𝔪.D.toPre (FractionRing V))
      (w : ∀ c, GlobalTheory.UT.Frm 𝔪.D.toPre (FractionRing V) 1 (g' c).b),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
      (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
      𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
      (∀ c, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero) ∧ (w c).IsGen ∧
        𝔪.Over' w₀ (g' c) (w c) (x (lab c)) (fr (lab c))) →
    ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ)
      (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre)
      (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → ∀ (wψ : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), wψ.IsGen →
      𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U →
      (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) →
      𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
        pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∀ ρ : X₁.S.Gam → (FractionRing V')ˣ, (∀ b, FrPull wψ f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b) (ρ b)) →
    ∃ (th₂ : SecA 𝔪₂.A (FractionRing V') 1) (w₀₂ : W0 𝔪₂.U.toUnifPre) (s₂ : Fam 𝔪₂.D.toPre (FractionRing V') 1)
      (g'₂ : C → GtPtF 𝔪₂.D.toPre (FractionRing V')) (w₂ : ∀ c, GlobalTheory.UT.Frm 𝔪₂.D.toPre (FractionRing V') 1 (g'₂ c).b)
      (K : FractionRing V'),
      (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩)) ∧ w₀₂.IsGen ∧
      𝔪₂.U.ExpandsF (FractionRing V') 1 w₀₂ th₂ s₂ ∧
      (∀ c, (∃ o, GtPtF.IsNsmul (𝔗.X₂.S.r * 𝔗.X₂.S.N) (g'₂ c) o ∧ o.IsZero) ∧ (w₂ c).IsGen ∧
        𝔪₂.Over' w₀₂ (g'₂ c) (w₂ c) (x₂ (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c)))) ∧
      (∀ mu c, coef s₂ (g'₂ c) (w₂ c) (𝔪₂.e₈ mu) * (ρ (lab c) : FractionRing V') = K * f (coef s (g' c) (w c) (𝔪.e₈ mu))) ∧
      ∀ b, 𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam b), 𝔗.X₂.S.th_mem _⟩ * (ρ b : FractionRing V') = K * f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) := by
  intro g n F W Z i X₁ act 𝔗 z₁ z₂ hp x₀ hdiv V _ _ _ ev X _ m t δ 𝔪 C lab x fr th w₀ s g' w h1 h2 h3 h4 h5 h6
    V' _ _ _ io f hf hinj hfin ev₂ 𝔪₂ ψ hD bc hExt hyK hcart wψ hwψ hφ hmon hU he₈ hgen x₂ fr₂ h1' h2' ρ hρ
  have hG := GlobalTheory.globalFns_holds
  letI : Algebra (FractionRing V) (FractionRing V') := f.toAlgebra
  haveI : IsScalarTower (FractionRing V) (FractionRing V) (FractionRing V') := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hF : Compat io (FractionRing V') := hf
  haveI : IsLocalHom io := RingHom.IsIntegral.isLocalHom hfin.to_isIntegral hinj
  have hI : (maximalIdeal V).map io ≤ maximalIdeal V' := map_maximalIdeal_le io
  have hg₂ : jFK (R := V') (FractionRing V') ≫ spMap f = jFK (R := V) (FractionRing V') := (Spec.map_comp _ _).symm
  obtain ⟨κ, κ', hκ⟩ := exists_isFibreIso hD hF
  obtain ⟨w₀₂, hw₀₂, Ω, hΩ₁, hΩ₂, hE⟩ := exists_expand hG hmon hU hF hg₂ hcart.1 hwψ hgen h4 hκ
  obtain ⟨t', s', E', ht', hs'⟩ := (hE 1 le_rfl).1 _ _ (expandsF_pull (F := FractionRing V') 𝔪.U.toUnifPre hG h5)
  have hx : ∀ b, (x₂ (𝔗.lam b)).left ≫ ψ = (fieldMap (R := V) (FractionRing V) (FractionRing V') ≫ x b).left := fun b => by
    refine 𝔪.cart.1.hom_ext ?_ ?_
    · show _ = (spMap f ≫ (x b).left) ≫ 𝔪.φ
      rw [Category.assoc, ← hφ, ← Category.assoc, h1', Category.assoc, 𝔗.lam_pt, Category.assoc, h1, ← Category.assoc,
        ← Category.assoc, ← spMap_comp, ← spMap_comp, hyK]
    · rw [Category.assoc, hcart.1.w, ← Category.assoc, Over.w, Over.w]
      exact hg₂
  have hfr : ∀ b, FrUp wψ (fr₂ (𝔗.lam b)) (frExt (FractionRing V') (fr b)) (ρ b : FractionRing V') := fun b z J J' hJ hJ' => by
    have e : vS (frExt (FractionRing V') (fr b)) z J = val (fr b) (spMap f) z J :=
      (val_frExt (fr b) (𝟙 _) hJ).trans (congrArg (fun q => val (fr b) q z J) (Category.id_comp _))
    rw [e]
    exact hρ b z J J' hJ hJ'
  have hv : ∀ b, ValAt t' (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b))
      (f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) * ((ρ b)⁻¹ ^ 1).val) := fun b =>
    valAt_pull hΩ₁ hΩ₂ ht' (hx b) (hfr b) (valAt_ext (h3 b))
  have t0 : (show AbSec 𝔪₂.A (FractionRing V') 1 from t') ≠ 0 := fun e => by
    have h₀ := hv x₀
    rw [show t' = (0 : AbSec 𝔪₂.A (FractionRing V') 1) from e] at h₀
    exact mul_ne_zero ((map_ne_zero f).2 (UMem.yK_th_ne_zero _ _ F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hdiv))
      (Units.ne_zero _) (valAt_unique h₀ (valAt_zero _ _))
  obtain ⟨x', fr', Θ, -, k1, k2, k3, -⟩ := IntTerm.exists_points_frames_theta _ _ F W Z i 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X m _ δ 𝔪₂
  obtain rfl : x' = x₂ := funext fun a => Over.OverMorphism.ext (𝔪₂.cart.1.hom_ext ((k1 a).trans (h1' a).symm)
    ((Over.w _).trans (Over.w _).symm))
  have hΘ : ∀ a, ValAt Θ (x' a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩) := fun a z J' hJ' => by
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' 𝔗.X₂.ρ.P.isLB z
    have e := mul_left_cancel (((k2 a).2 z J J' hJ hJ').trans ((h2' a).2 z J J' hJ hJ').symm)
    have b := k3 a z J' hJ'
    rw [FrameMove.val_powFrame] at b ⊢
    rwa [← e]
  obtain ⟨K, hK⟩ := exists_eq_smul t0 Θ
  obtain ⟨e', he'⟩ := exists_linearEquiv_expandsF hG 𝔪₂.U (FractionRing V') le_rfl w₀₂ hw₀₂
  choose g₁ w₁ a₁ a₂ a₃ a₄ using fun c => exists_ext (F := FractionRing V') hG 𝔪.U h4 (g' c) (h6 c).2.1
  choose g₂ w₂ b₁ b₂ b₃ b₄ using fun c => exists_point hG hI hF hκ hΩ₁ hΩ₂ (fun k hk => (hE k hk).2) (g₁ c) (a₁ c) (ρ (lab c))
  refine ⟨Θ, w₀₂, K • s', g₂, w₂, K, hΘ, hw₀₂, (he' _ _).2 ?_, fun c => ⟨?_, b₁ c, ?_⟩, fun mu c => ?_, fun b => ?_⟩
  · exact (congrArg e' hK).trans ((map_smul e' K _).trans (congrArg (K • ·) ((he' _ _).1 E')))
  · rw [𝔗.lev]
    exact tors_mul _ (b₂ c _ (a₂ c _ (h6 c).1))
  · exact b₄ c (x' (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c))) _ (frExt (FractionRing V') (fr (lab c)))
      (frExt_isGen _ (h2 (lab c)).1) (hx (lab c)) (hfr (lab c)) (a₄ c (x (lab c)) (fr (lab c)) (h2 (lab c)).1 (h6 c).2.2)
  · rw [coef_smul (b₁ c), _root_.mul_assoc, b₃ c _ _ hs', a₃, he₈]
    rfl
  · have h₀ := valAt_lin (hv b) (valAt_zero _ _) K
    rw [add_zero, add_zero, ← hK] at h₀
    rw [valAt_unique (hΘ _) h₀, pow_one, _root_.mul_assoc, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

end GlobalTheory.TermsMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToroidalCanonicalBundleWeightLine
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
namespace GlobalTheory.LogCanon

theorem exOf_kapBase {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) :
    (fun ix : Ix Dw => Option.elim ix 0 fun x =>
      (fun τ : E →+* ℂ => if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p) x.1) =
      AllWt.exOf Dw (kapBase Dw) 0 := by
  funext ix
  rcases ix with _ | ⟨τ, i⟩
  · rfl
  · by_cases h' : τ (H.rt : E) = H.rt0
    · have hi : (i : ℕ) < Dw.p := by
        have := i.2; simp only [Datum.mult, if_pos h'] at this; exact this
      simp only [Option.elim, AllWt.exOf, exZ, AllWt.wtOf, if_pos h', dif_pos h', dif_pos hi, kapBase, sub_zero,
        if_pos hi]
    · have hi : (i : ℕ) < Dw.q := by
        have := i.2; simp only [Datum.mult, if_neg h'] at this; exact this
      have hc : conjEmb τ (H.rt : E) = H.rt0 := by
        have := (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or H τ).resolve_left h'
        unfold InPsi at this
        rw [ComplexEmbedding.conjugate_coe_eq] at this
        exact this
      have hn : ¬ (Dw.p + (Dw.q - 1 - (i : ℕ)) < Dw.p) := by omega
      simp only [Option.elim, AllWt.exOf, exZ, AllWt.wtOf, if_neg h', dif_neg h', dif_pos hc, dif_pos hi, kapBase,
        if_neg hn, neg_neg, sub_zero]

theorem exists_kap_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (K : CanonLB (s₀ TF.Y Z) Dw.dim), ∃ (κ : LB (X₀ TF.Y Z)) (hκ : κ.IsLB), CechPic.pull (π₀ TF.X Z) (cls κ hκ) = cls (L₀ TF.X Z (kapBase Dw)) (isLB_L₀ TF.X Z _) ∧ ∃ θ : (LB.div κ K.bundle).Sec, nonzeroLocus θ = (j₀ TF.Y Z).opensRange := by
  intro E hE hNumber hCM H Dw l Xo c TF Z hpq hF hSmooth K
  obtain ⟨hI, -⟩ := GlobalTheory.BaseVar.isVariety_barComp E H Dw l Xo c TF Z hF
  letI : IsIntegral (X₀ TF.Y Z) := hI
  obtain ⟨φ₀, f₀, hgen, hdiv⟩ := _root_.GlobalTheory.EigDiv.exists_detDiv E H Dw l Xo c TF Z
  obtain ⟨D, hpull, hD⟩ := hdiv fun τ => if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p
  refine ⟨toLB D, isLB_toLB D, ?_, ?_⟩
  · rw [exOf_kapBase Dw] at hpull
    exact hpull
  · obtain ⟨i₀, hi₀⟩ := exists_chart K.isLB (genericPoint (X₀ TF.Y Z))
    have hP := presents_ofLB K.isLB i₀ hi₀
    have hKS := @GlobalTheory.T.exists_logKodairaSpencer_divisor_toroidalComponent
      E hE hNumber hCM H Dw l Xo c TF Z hpq hF hI hSmooth K
      (ofLB K.isLB i₀ hi₀) (frameRat K.bundle i₀ hi₀) hP φ₀ f₀ hgen D hD
    obtain ⟨h, hh⟩ := hKS
    exact GlobalTheory.Cartier.exists_sec_div_nonzeroLocus_eq D _ K.bundle _ hP _ h hh
end GlobalTheory.LogCanon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitPeriodFormValuationSumRefinedChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.Poinc.ChartTraitForm


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear in
theorem exists_pull {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g) (hI : I.map g ≤ I')
    {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) :
    ∃ (D' : DegData R' I') (_ : IsPullDeg g D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R')))
      (_ : Unif I' D' A' ((Over.pullback (spMap g)).obj G)) (gA : A'.A.left ⟶ A.A.left),
      IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA ∧ LBIso A'.L (A.L.pull gA) := by
  have hP : PolBaseChangeSt := polBaseChange_holds
  have hU : UnifBaseChangeSt := GlobalTheory.UnifPullGuards.unifBaseChange_holds
  have hψ : PsiOnExistsSt := psiOnExists
  have sq : spMap (fracMap hg) ≫ jK R = jK R' ≫ spMap g := (fracMap_sq hg).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap (fracMap hg)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap (fracMap hg) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) =
      pullback.fst G.hom (spMap g) := Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫
      pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec ((Over.pullback (specOf g)).obj G)) (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) :=
    ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
      rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig,
      pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := hψ R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨D', hD, A', U', gA, gpA, LBIso.symm tA⟩

theorem isMonomial_pull {R W : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] [IsLocalRing W] {κ : R →+* W}
    {D : DegPre R} {D' : DegPre W} (hD : IsPullDeg κ D D') {m : ℕ} {r : Fin m → R}
    {B : Fin m → LinearMap.BilinForm ℤ D.X} (h : IsMonomial D r B) {ϖ : W} {a : Fin m → ℕ}
    (ha : ∀ k, Associated (κ (r k)) (ϖ ^ a k)) (β : LinearMap.BilinForm ℤ D'.X)
    (hβ : ∀ y, β y y = ∑ k, (a k : ℤ) * B k (hD.xe y) (hD.xe y)) : IsMonomial D' ![ϖ] ![β] := by
  intro y
  obtain ⟨u, n, hn, hc⟩ := h (hD.xe y)
  obtain ⟨u', hc'⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD y _ hc
  have h₁ : Associated (ϖ ^ ∑ k, a k * n k) (u' * κ (u * ∏ i, r i ^ n i)) := by
    refine Associated.symm ((associated_unit_mul_left _ _ u'.isUnit).trans ?_)
    rw [map_mul, map_prod, ← Finset.prod_pow_eq_pow_sum]
    refine (associated_unit_mul_left _ _ (u.isUnit.map κ)).trans (Associated.prod _ _ _ fun i _ => ?_)
    rw [map_pow, pow_mul]
    exact (ha i).pow_pow
  obtain ⟨v, hv⟩ := h₁
  refine ⟨v, ![∑ k, a k * n k], fun i => ?_, ?_⟩
  · fin_cases i
    simp only [Fin.zero_eta, Matrix.cons_val_zero, hβ, hn]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · rw [Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_zero, mul_comm, hv]
    exact hc'

theorem exists_trait : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (S : Scheme.{0}) (j : F.X ⟶ S)
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (ξ : Sp V ⟶ S), UnifOver F j ξ Q →
    ∀ (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X) (R' : Type) [CommRing R'] [IsDomain R']
      [IsLocalRing R'] (ρ : V →+* R') (r : Fin m → R') (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X),
      IsCN R' → Function.Injective ρ → ρ.Finite → IsLocalHom ρ → (∀ k, r k ^ 2 = ρ (t k)) → (∀ k, t k ≠ 0) →
      (∀ k a b, δ k a b = δ k b a) → Refines Q ρ D.toPre e →
      IsMonomial D.toPre r (fun k => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ k)) →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W], IsAdicComplete (maximalIdeal W) W →
    ∀ κ : R' →+* W, Function.Injective κ → IsLocalHom κ →
      ∃ (T : Trait F) (σ : W →+* T.V) (c : Fin m → ℕ) (e' : T.D.toPre.X ≃+ Q.X), Function.Bijective σ ∧
        jK T.V ≫ spMap σ ≫ spMap κ ≫ spMap ρ ≫ ξ = T.y ≫ j ∧ (∀ k, Associated (σ (κ (ρ (t k)))) (T.ϖ ^ c k)) ∧
        ∀ a b, T.β a b = ∑ k, (c k : ℤ) * δ k (e' a) (e' b) := by
  intro o _ ζ g n F S j V _ _ _ Q ξ hUO m t δ R' _ _ _ ρ r D e hR' hρ hρf _ hr ht hδ hRef hmon W _ _ _ hW κ hκ hκl
  obtain ⟨G', _, _, A, U, y', α, α₂, hG, hy, hα, hsq, hL⟩ := hUO.2 R' ρ hR' hρ hρf D e hRef
  have h0 : CharZero R' := hR'.2.2.2
  have hW0 : CharZero W := charZero_of_injective_ringHom hκ
  obtain ⟨D', hD, A', U', gA, gpA, tA⟩ := exists_pull (I := maximalIdeal R') (I' := maximalIdeal W)
    ⟨hR'.1, inferInstance, hR'.2.1, hR'.2.2.1⟩ ⟨inferInstance, inferInstance, inferInstance, hW⟩ κ hκ
    (Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit κ a ha) hG U
  obtain ⟨β₂, hβ₂, hΛ⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ A.A A'.A gA gpA
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hr0 : ∀ k, κ (r k) ≠ 0 := fun k h => ht k (hρ (hκ (by rw [← hr, map_pow, h]; simp)))
  choose a u hu using fun k => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hr0 k) hϖ
  have ha : ∀ k, Associated (κ (r k)) (ϖ ^ a k) := fun k => by
    rw [hu]; exact associated_unit_mul_left _ _ (u k).isUnit
  let e' : D'.toPre.X ≃+ Q.X := hD.xe.trans e
  let β : LinearMap.BilinForm ℤ D'.toPre.X := ∑ k, ((2 * a k : ℕ) : ℤ) • pull e'.toIntLinearEquiv.toLinearMap (δ k)
  have hβ : ∀ x y, β x y = ∑ k, ((2 * a k : ℕ) : ℤ) * δ k (e' x) (e' y) := fun x y => by
    simp only [β, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rfl
  have sq : spMap (GlobalTheory.ArcPull.fracMap hκ) ≫ jK R' = jK W ≫ spMap κ :=
    (GlobalTheory.ArcPull.fracMap_sq hκ).symm.trans (Category.id_comp _)
  let T : Trait F :=
    { V := W, complete := hW, ϖ := ϖ, irr := hϖ, y := spMap (GlobalTheory.ArcPull.fracMap hκ) ≫ y'
      G := (Over.pullback (spMap κ)).obj G', semi := IsSemiAbelian.pullback _ G' hG, D := D', A := A', U := U'
      α := gA ≫ α, α₂ := β₂ ≫ α₂, cart := gpA.comp hα
      sq := ⟨by rw [Category.assoc, hsq.1, ← Category.assoc, hβ₂.1, Category.assoc],
        by rw [Category.assoc, hsq.2, ← Category.assoc, hβ₂.2, Category.assoc]⟩
      lb := hΛ A.L A'.L _ F.univ.P α₂ A.isLB A'.isLB F.univ.isLB tA hL
      β := β
      symm := fun x y => by
        rw [hβ, hβ]
        exact Finset.sum_congr rfl fun k _ => by rw [hδ]
      mono := isMonomial_pull hD hmon ha β fun y => by
        rw [hβ]
        refine Finset.sum_congr rfl fun k _ => ?_
        have : ((2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ k)) (hD.xe y) (hD.xe y) = 2 * δ k (e' y) (e' y) := rfl
        rw [this]
        push_cast
        ring }
  refine ⟨T, RingHom.id W, fun k => 2 * a k, e', Function.bijective_id, ?_, fun k => ?_, hβ⟩
  · show jK W ≫ spMap (RingHom.id W) ≫ spMap κ ≫ spMap ρ ≫ ξ = (spMap (GlobalTheory.ArcPull.fracMap hκ) ≫ y') ≫ j
    have : spMap (RingHom.id W) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp, Category.assoc, hy, ← Category.assoc (spMap (GlobalTheory.ArcPull.fracMap hκ)), sq, Category.assoc]
  · show Associated (κ (ρ (t k))) (ϖ ^ (2 * a k))
    rw [← hr, map_pow, mul_comm, pow_mul]
    exact (ha k).pow_pow

end GlobalTheory.Poinc.ChartTraitForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilCommutatorPairingTorsionGeometricPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.WeilGeomPt

theorem exists_weilIs_geomPt : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (n : ℕ), 0 < n → (n : κ) ≠ 0 → ∀ y y' : Over.mk x ⟶ B, y ^ n = 1 → y' ^ n = 1 → ∃ e : (Γ((Over.mk x).left, ⊤))ˣ, Out.WeilIs B M n y y' e := by
  intro S B _ _ M hA hM κ _ _ x n _ _ y y' hy hy'
  obtain ⟨e, -, he⟩ := GlobalTheory.HolTorsionAny.exists_weilIs_pow_eq_one hA hM hy hy'
  exact ⟨e, he⟩

end GlobalTheory.WeilGeomPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpBijOfBasisCard
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

theorem expBij_of_basis_card : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), AdmBase R I → 1 ≤ k → ∀ (Λ : Type) [Fintype Λ] (b : Module.Basis Λ (FractionRing R) (Fam D.toPre (FractionRing R) k)) (σ : Λ → U.SecK k), Fintype.card Λ = k ^ A.g → (∀ l, U.Expands k (σ l) (b l)) → U.ExpBij k := by
  intro R _ _ I D A G _ _ U k hR hk Λ _ b σ hcard hσ
  classical
  obtain ⟨β, -, hβ⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis
    GlobalTheory.abelianSchemeLaws_all.1.secBaseChange R I D A G U k hk
  choose C hC using fun l => (hβ (σ l)).exists
  have hCc : ∀ l, GlobalTheory.UnifPowAdm.IsComb (pullback.snd G.hom (jK R)) (σ l) (C l) β := fun l jj => hC l jj
  let Φ : (Λ → FractionRing R) →ₗ[FractionRing R] (Fin (k ^ A.g) → FractionRing R) :=
    { toFun := fun c a => ∑ l, c l * C l a
      map_add' := fun c d => by funext a; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        funext a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _ }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    obtain ⟨s, hs⟩ := GlobalTheory.UnifPowAdm.exists_isComb (pullback.snd G.hom (jK R)) c σ
    have h1 := hs.trans hCc
    have hz : ∀ a, ∑ l, c l * C l a = 0 := fun a => congrFun hc a
    have h0 : ∀ jj, s.f jj = 0 := fun jj => by
      rw [h1 jj]
      simp [hz]
    have hE := GlobalTheory.UnifPowAdm.expands_comb U k hσ hs
    have h2 := GlobalTheory.ExpZero.main R I D A G U k hR s _ h0 hE
    exact funext fun l => Fintype.linearIndependent_iff.1 b.linearIndependent c h2 l
  have hsurj : Function.Surjective Φ := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    simp [hcard]
  refine GlobalTheory.UnifPowAdm.expBij_of_basis U k hR b σ hσ fun s => ?_
  obtain ⟨d, hd, -⟩ := hβ s
  obtain ⟨c, rfl⟩ := hsurj d
  obtain ⟨s', hs'⟩ := GlobalTheory.UnifPowAdm.exists_isComb (pullback.snd G.hom (jK R)) c σ
  have e : s' = s := (hs'.trans hCc).unique fun jj => hd jj
  exact ⟨c, e ▸ hs'⟩

end GlobalTheory.ProdUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMumfordClassEqZeroAmpleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_mumfordClass_eq_zero_ample : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left), IsAmpleCls c → Finite {x : A.Pt // AbVar.lam c (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0} := by
  first | (exact @GlobalTheory.AV.AbVar.finite_lam_eq_zero) | (exact GlobalTheory.AV.AbVar.finite_lam_eq_zero) | (intros; apply GlobalTheory.AV.AbVar.finite_lam_eq_zero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantPointDescendsToSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_invariant_point_descends_to_section : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V], IsIntegrallyClosed V → ∀ (N : Over (Sp V)), IsFinite N.hom → ∀ (nb : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ N), (∀ σ : AlgebraicClosure (FractionRing V) ≃ₐ[FractionRing V] AlgebraicClosure (FractionRing V), spMap σ.toAlgHom.toRingHom ≫ nb.left = nb.left) → ∃ s : 𝟙_ (Over (Sp V)) ⟶ N, nb = toUnit _ ≫ s := by
  first | exact @GlobalTheory.FinDescent.galoisFixed_point_of_finite | exact GlobalTheory.FinDescent.galoisFixed_point_of_finite | (intros; apply GlobalTheory.FinDescent.galoisFixed_point_of_finite <;> assumption)
end

