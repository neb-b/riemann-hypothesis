module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2706
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2671
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2646
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3083
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartEqOfSameGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section
namespace GlobalTheory.TInj

theorem tautChart_eq_of_genPt : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left), C.IsFam F G₁ y α₁ → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (θ₁ θ₂ : C.R →+* R'), IsCN R' → Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ (κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing C.R)), κ₁ ≫ jK C.R = jK R' ≫ spMap θ₁ → κ₂ ≫ jK C.R = jK R' ≫ spMap θ₂ → κ₁ ≫ y = κ₂ ≫ y → spMap (θ₁.comp C.iw) ≫ C.u = spMap (θ₂.comp C.iw) ≫ C.u ∧ (θ₁.comp C.iw = θ₂.comp C.iw → ∀ k, θ₁ (C.s k) = θ₂ (C.s k)) := by
  intro g n φ hn F C G₁ _ _ y α₁ hC R' _ _ _ θ₁ θ₂ hR' hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨hsa, -, -, hM, hys⟩ := hC
  have hn1 : 1 ≤ n := by omega
  have hCN : IsCN C.R := hM.isCN
  obtain ⟨R₁, _, _, _, ρ, D, e', hR₁, hρ, hρf, hρl, href⟩ := _root_.GlobalTheory.TInj.taut_refine hn1 C hCN
  obtain ⟨β, ββ, w, hFrom⟩ := _root_.GlobalTheory.TInj.FromRefine.from_of_refines C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n C.R R₁ ρ C.iw C.s C.Q C.e D.toPre e' hρ C.data href
  obtain ⟨G₀, _, _, π, A₀, U₀, hU⟩ := hM.unif R₁ ρ hR₁ hρ hρf D e' href
  obtain ⟨hπ, κρ, πK, α₀, α₂, hκρ, -, hA, hsq, hL, -⟩ := hU
  have hsa₀ : IsSemiAbelian G₀ := GlobalTheory.Mum.EvenDesc.isSemiAbelian_of_isGrpPullback hπ hsa
  obtain ⟨V, _, _, _, _, η', f₁, f₂, hVc, hη', hf₁, hf₂, hlf₁, hlf₂, hc₁, hc₂⟩ :=
    exists_cDvr_two_embeddings C.R R₁ R' ρ hρ hρf hR' θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂
  obtain ⟨κf₁, hκf₁⟩ := exists_genericMap hf₁
  obtain ⟨κf₂, hκf₂⟩ := exists_genericMap hf₂
  obtain ⟨κη, hκη⟩ := exists_genericMap hη'
  have e₁ : κf₁ ≫ κρ = κη ≫ κ₁ := GlobalTheory.T.genericPointMap_over_ringHom_unique (f₁.comp ρ) _ _
    (by rw [Category.assoc, hκρ, ← Category.assoc, hκf₁, Category.assoc, ← spMap_comp])
    (by rw [Category.assoc, hκ₁, ← Category.assoc, hκη, Category.assoc, ← spMap_comp, hc₁])
  have e₂ : κf₂ ≫ κρ = κη ≫ κ₂ := GlobalTheory.T.genericPointMap_over_ringHom_unique (f₂.comp ρ) _ _
    (by rw [Category.assoc, hκρ, ← Category.assoc, hκf₂, Category.assoc, ← spMap_comp])
    (by rw [Category.assoc, hκ₂, ← Category.assoc, hκη, Category.assoc, ← spMap_comp, hc₂])
  have hy₀ : κf₁ ≫ (κρ ≫ y) = κf₂ ≫ (κρ ≫ y) := by
    rw [← Category.assoc, e₁, Category.assoc, hy, ← Category.assoc, ← e₂, Category.assoc]
  have hmap : ∀ f : R₁ →+* V, IsLocalHom f → (maximalIdeal R₁).map f ≤ maximalIdeal V := fun f hf =>
    Ideal.map_le_iff_le_comap.mpr fun x hx => (mem_maximalIdeal _).2 (map_nonunit f x ((mem_maximalIdeal _).1 hx))
  haveI : CharZero R₁ := hR₁.2.2.2
  obtain ⟨D₁, D₂, hD₁, hD₂, j₁, j₂, b, φ', hE₁, hE₂, hMatch, hpairs⟩ :=
    _root_.GlobalTheory.TInj.pull_pair_match F.univ (GlobalTheory.LowChart.isUnit_zetaAway n hn) hn1 R₁ (maximalIdeal R₁)
      ⟨hR₁.1, inferInstance, hR₁.2.1, hR₁.2.2.1⟩ D A₀ G₀ U₀ hsa₀ (κρ ≫ y) α₀ ⟨hA, α₂, hsq, hL⟩ V hVc f₁ f₂ hf₁ hf₂
      (hmap f₁ hlf₁) (hmap f₂ hlf₂) κf₁ κf₂ hκf₁ hκf₂ hy₀
  obtain ⟨ββ₁, w₁, hFrom₁⟩ := _root_.GlobalTheory.TInj.from_pull C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n R₁ V
    (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₁ D₁.toPre hD₁ hf₁ hFrom
  obtain ⟨ββ₂, w₂, hFrom₂⟩ := _root_.GlobalTheory.TInj.from_pull C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n R₁ V
    (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₂ D₂.toPre hD₂ hf₂ hFrom
  have hne₀ : ∀ k, ρ (C.s k) ≠ 0 := fun k => (map_ne_zero_iff ρ hρ).2 (C.s_ne_zero k)
  have htaut : ∀ a : Fin C.T.r → ℤ, ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) n)
      (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) n),
      p₁.y = (hD₁.xe.trans (e'.trans C.e)).symm a ∧
      TautPt C.T (f₁.comp (ρ.comp C.iw)) (fun k => f₁ (ρ (C.s k))) (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n
        D₁.toPre (hD₁.xe.trans (e'.trans C.e)) ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
        (AlgebraicClosure (FractionRing V)) a p₁.g ∧
      p₂.y = (hD₂.xe.trans (e'.trans C.e)).symm a ∧
      TautPt C.T (f₂.comp (ρ.comp C.iw)) (fun k => f₂ (ρ (C.s k))) (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n
        D₂.toPre (hD₂.xe.trans (e'.trans C.e)) ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂
        (AlgebraicClosure (FractionRing V)) a p₂.g ∧ QImg b φ' p₁ p₂ := by
    intro a
    obtain ⟨p₀, hp₀y, hp₀⟩ := _root_.GlobalTheory.TInj.exists_qkPt_tautPt C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n R₁ D.toPre
      (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w D.tau_bimult hFrom hne₀
      (AlgebraicClosure (FractionRing R₁)) a
    obtain ⟨p₁, p₂, hp₁y, hTr₁, hp₂y, hTr₂, hQ⟩ := hpairs p₀
    refine ⟨p₁, p₂, ?_, ?_, ?_, ?_, hQ⟩
    · rw [hp₁y, hp₀y]; rfl
    · exact _root_.GlobalTheory.TautTransport.tautPt_tr C.T _ n R₁ V (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₁
        D₁.toPre hD₁ ββ₁ w₁ hf₁ D₁.tau_bimult hFrom hFrom₁ _ _ j₁ hE₁ a p₀.g p₁.g hp₀ hTr₁
    · rw [hp₂y, hp₀y]; rfl
    · exact _root_.GlobalTheory.TautTransport.tautPt_tr C.T _ n R₁ V (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₂
        D₂.toPre hD₂ ββ₂ w₂ hf₂ D₂.tau_bimult hFrom hFrom₂ _ _ j₂ hE₂ a p₀.g p₂.g hp₀ hTr₂
  have hlev := GlobalTheory.T.exists_level_point_pairs_lower_base C.toLowBase hn1 R₁ V (maximalIdeal R₁) (maximalIdeal V) D D₁ D₂ (ρ.comp C.iw) β hFrom.1
    f₁ f₂ hD₁ hD₂ (AlgebraicClosure (FractionRing R₁)) (AlgebraicClosure (FractionRing V)) j₁ j₂ b φ' hE₁ hE₂ hpairs
  have hloc : ∀ f : R₁ →+* V, IsLocalHom f → ∀ x, x ∈ maximalIdeal C.R → f (ρ x) ∈ maximalIdeal V := fun f hf x hx =>
    (mem_maximalIdeal _).2 (map_nonunit f _ (map_nonunit ρ x ((mem_maximalIdeal _).1 hx)))
  have hbd₁ : ∀ k, f₁ (ρ (C.s (.inl k))) ∈ maximalIdeal V ∧ f₁ (ρ (C.s (.inl k))) ≠ 0 := fun k =>
    ⟨hloc f₁ hlf₁ _ (C.bd k), (map_ne_zero_iff f₁ hf₁).2 (hne₀ _)⟩
  have hbd₂ : ∀ k, f₂ (ρ (C.s (.inl k))) ∈ maximalIdeal V ∧ f₂ (ρ (C.s (.inl k))) ≠ 0 := fun k =>
    ⟨hloc f₂ hlf₂ _ (C.bd k), (map_ne_zero_iff f₂ hf₂).2 (hne₀ _)⟩
  have hu₁ : ∀ k, IsUnit (f₁ (ρ (C.s (.inr k)))) := fun k => ((C.tor k).map ρ).map f₁
  have hu₂ : ∀ k, IsUnit (f₂ (ρ (C.s (.inr k)))) := fun k => ((C.tor k).map ρ).map f₂
  have hfin1 := _root_.GlobalTheory.TInj.lattice_iso_eq_of_tautPts C.T φ C.m C.N n (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) hn C.cone C.defin V
    D₁.toPre D₂.toPre (f₁.comp (ρ.comp C.iw)) (fun k => f₁ (ρ (C.s k))) (hD₁.xe.trans (e'.trans C.e))
    ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
    (f₂.comp (ρ.comp C.iw)) (fun k => f₂ (ρ (C.s k))) (hD₂.xe.trans (e'.trans C.e))
    ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂ b φ' (AlgebraicClosure (FractionRing V))
    D₁.tau_bimult D₂.tau_bimult hFrom₁ hFrom₂ hbd₁ hu₁ hbd₂ hu₂ hMatch htaut
  have hb := _root_.GlobalTheory.TInj.baseEq_of_sameImage F.s y C.b hys θ₁ θ₂ κ₁ κ₂ hκ₁ hκ₂ hy
  have k₁ : f₁.comp (ρ.comp C.iw) = η'.comp (θ₁.comp C.iw) := by
    rw [← RingHom.comp_assoc, hc₁, RingHom.comp_assoc]
  have k₂ : f₂.comp (ρ.comp C.iw) = η'.comp (θ₂.comp C.iw) := by
    rw [← RingHom.comp_assoc, hc₂, RingHom.comp_assoc]
  have hbase : (f₁.comp (ρ.comp C.iw)).comp C.toLowBase.T.b = (f₂.comp (ρ.comp C.iw)).comp C.toLowBase.T.b := by
    rw [k₁, k₂]
    change η'.comp (θ₁.comp C.b) = η'.comp (θ₂.comp C.b)
    rw [hb]
  obtain ⟨hU', hβeq⟩ := GlobalTheory.T.siegelFibrePower_point_eq_of_matching_lower_data C.toLowBase hn (GlobalTheory.LowChart.isUnit_zetaAway n hn) (isUnit_natCast (by omega))
    (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) V
    D₁.toPre D₂.toPre (f₁.comp (ρ.comp C.iw)) (fun k => f₁ (ρ (C.s k))) (hD₁.xe.trans (e'.trans C.e))
    ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
    (f₂.comp (ρ.comp C.iw)) (fun k => f₂ (ρ (C.s k))) (hD₂.xe.trans (e'.trans C.e))
    ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂ b φ' (AlgebraicClosure (FractionRing V))
    D₁.tau_bimult D₂.tau_bimult hFrom₁ hFrom₂ hbase hMatch hfin1 htaut hlev
  refine ⟨GlobalTheory.T.specMap_comp_eq_of_comp_injective_localScheme C.u (θ₁.comp C.iw) (θ₂.comp C.iw) η' hη' (by rw [← k₁, ← k₂]; exact hU'), fun heq k => ?_⟩
  have hω : f₁.comp (ρ.comp C.iw) = f₂.comp (ρ.comp C.iw) := by rw [k₁, k₂, heq]
  have hβ₂ := hβeq hω
  rw [← hω] at hFrom₂ htaut
  have hs := _root_.GlobalTheory.TInj.coords_eq_of_match C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n V (f₁.comp (ρ.comp C.iw))
    D₁.toPre D₂.toPre (fun k => f₁ (ρ (C.s k))) (hD₁.xe.trans (e'.trans C.e))
    ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
    (fun k => f₂ (ρ (C.s k))) (hD₂.xe.trans (e'.trans C.e))
    ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂ b φ' (AlgebraicClosure (FractionRing V))
    hn1 ⟨C.ε, fun _ => rfl⟩ D₁.tau_bimult D₂.tau_bimult hFrom₁ hFrom₂ (fun k => (map_ne_zero_iff f₁ hf₁).2 (hne₀ k))
    (fun k => (map_ne_zero_iff f₂ hf₂).2 (hne₀ k)) hMatch hfin1 hβ₂ htaut
  have h1 := congrFun hs k
  have h2 := DFunLike.congr_fun hc₁ (C.s k)
  have h3 := DFunLike.congr_fun hc₂ (C.s k)
  simp only [RingHom.comp_apply] at h1 h2 h3
  exact hη' (by rw [← h2, ← h3]; exact h1)

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationExponentOfFrameExponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic
open GlobalTheory.GSep GlobalTheory.GSep.TransTerms

namespace GlobalTheory.GSep.TransTerms

theorem transExp_of_frExp : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ), ∀ a ∈ X₁.S.HH X₁.M z₁, ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ e : ℕ, GlobalTheory.GSep.TransTerms.FrExp 𝔪 a τ e → GlobalTheory.GSep.TransTerms.TransExp 𝔪 x₀ a τ e := by
  have huniq := GlobalTheory.T.thetaMember_terms_coefficients_unique
  intro I X₁ z₁ act x₀ hdiv V _ _ _ ev Y _ t δ 𝔪 a _ τ _ e hF
  obtain ⟨-, x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, htor, hw, hov, htr⟩ := hF
  intro χ hχ C lab T hT c hc C' lab' T' hT' c' hc' mu
  letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (FractionRing V)
  set g₀ := GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ) with hg₀def
  have hg₀ : IsTor χ g₀ := (GlobalTheory.UT.isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ)
  have hadd : g'.IsAdd g₀ (g' + g₀) := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl
  have hb : (g' + g₀).b = g'.b := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  set c₀ : FractionRing V := 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) with hc₀def
  have hc₀ : c₀ ≠ 0 :=
    ((((X₁.S.prim.isUnit (by have := X₁.S.r_pos; have := X₁.S.N_ge; positivity)).pow e).map
      (algebraMap X₁.o₁ X₁.S.R)).map 𝔪.yK).ne_zero
  obtain ⟨w₁, hw₁, hv₁⟩ := GlobalTheory.UT.TorsionValue.exists_frm_scale w hw (inv_ne_zero hc₀)
  obtain ⟨w'', hw'', hv''⟩ : ∃ w'' : Frm 𝔪.D.toPre (FractionRing V) 1 (g' + g₀).b, w''.IsGen ∧
      ∀ z J, val w'' (𝟙 _) z J = val w₁ (𝟙 _) z J := by
    rw [hb]; exact ⟨w₁, hw₁, fun _ _ => rfl⟩
  have hvs : ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w'' (𝟙 _) z J).val = cstH z c₀⁻¹ * (val w (𝟙 _) z J).val :=
    fun z J hJ => by rw [hv'' z J, hv₁ z J hJ, GlobalTheory.UT.CoefBasic.cst_eq]
  have hvw : ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w (𝟙 _) z J).val = cstH (R := V) z c₀ * (val w'' (𝟙 _) z J).val :=
    fun z J hJ => by rw [hvs z J hJ, ← _root_.mul_assoc, ← map_mul, mul_inv_cancel₀ hc₀, map_one, _root_.one_mul]
  have hov'' := htr χ hχ g₀ hg₀ (g' + g₀) hadd w'' hw'' hvw
  have htor'' : ∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' + g₀) o ∧ o.IsZero := by
    obtain ⟨o, ho, hoz⟩ := htor
    refine ⟨0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (GlobalTheory.TorusExt.isZero_iff_eq _).2 rfl⟩
    rw [smul_add, ← (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho, (GlobalTheory.TorusExt.isZero_iff_eq _).1 hoz, zero_add, hg₀def,
      ← map_nsmul, ← ofMul_pow, hχ.1, ofMul_one, map_zero]
  obtain ⟨x₁, fr₁, th₁, w₀₁, s₁, G₁, W₁, hx₁, hfr₁, hth₁, hw₀₁, hs₁, hc₁, hT₁⟩ := hT
  obtain ⟨x₂, fr₂, th₂, w₀₂, s₂, G₂, W₂, hx₂, hfr₂, hth₂, hw₀₂, hs₂, hc₂, hT₂⟩ := hT'
  obtain ⟨ht₁, hW₁, ho₁⟩ := hc₁ c
  obtain ⟨ht₂, hW₂, ho₂⟩ := hc₂ c'
  rw [hc] at ho₁
  rw [hc'] at ho₂
  have u₁ := huniq I X₁ z₁ act V ev Y t δ 𝔪 a x x₁ fr fr₁ th th₁ w₀ w₀₁ s s₁ g' (G₁ c) w (W₁ c)
    hx hfr hth hw₀ hs htor hw hov hx₁ hfr₁ hth₁ hw₀₁ hs₁ ht₁ hW₁ ho₁ (𝔪.e₈ mu)
  have u₂ := huniq I X₁ z₁ act V ev Y t δ 𝔪 (a + τ) x x₂ fr fr₂ th th₂ w₀ w₀₂ s s₂ (g' + g₀) (G₂ c') w'' (W₂ c')
    hx hfr hth hw₀ hs htor'' hw'' hov'' hx₂ hfr₂ hth₂ hw₀₂ hs₂ ht₂ hW₂ ho₂ (𝔪.e₈ mu)
  have co := GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd hw hvs s (𝔪.e₈ mu)
  have hθ := GlobalTheory.GSep.GMem.yK_th_ne_zero I X₁ z₁ act V ev Y t δ 𝔪 x₀ hdiv
  apply mul_right_cancel₀ hθ
  rw [_root_.mul_assoc, _root_.mul_assoc, hT₁ mu c, hT₂ mu c', ← u₁, ← u₂, co]
  field_simp

end GlobalTheory.GSep.TransTerms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndependentMemberStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedThetaSum_zeta_exponent_independent_member : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (Y₁ : Type) [AddCommGroup Y₁] (m₁ : ℕ) (t₁ : Fin m₁ → V₁) (δ₁ : Fin m₁ → LinearMap.BilinForm ℤ Y₁) (𝔪₁ : UMem X₁ z₁ act V₁ ev₁ Y₁ t₁ δ₁) (C₁ : Type) (lab₁ : C₁ → X₁.S.Gam), (∀ c, lab₁ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₁ : (Fin 8 → Y₁) → C₁ → V₁, 𝔪₁.Terms x₀ lab₁ T₁ → ∀ c₁ : C₁, ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (Y₂ : Type) [AddCommGroup Y₂] (m₂ : ℕ) (t₂ : Fin m₂ → V₂) (δ₂ : Fin m₂ → LinearMap.BilinForm ℤ Y₂) (𝔪₂ : UMem X₁ z₁ act V₂ ev₂ Y₂ t₂ δ₂) (C₂ : Type) (lab₂ : C₂ → X₁.S.Gam), (∀ c, lab₂ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₂ : (Fin 8 → Y₂) → C₂ → V₂, 𝔪₂.Terms x₀ lab₂ T₂ → ∀ c₂ : C₂, lab₁ c₁ = lab₂ c₂ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ e₁ e₂ : ℕ, TwistSum X₁ z₁ act x₀ 𝔪₁ lab₁ T₁ sg c₁ τ e₁ → TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₂ → (∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab₁ c₁ + τ) / X₁.S.th x₀ ∧ ev₁ r ≠ 0) → TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₁ := by
  first | exact @GlobalTheory.Poinc.Sep.twistSum_indep | exact GlobalTheory.Poinc.Sep.twistSum_indep | (intros; apply GlobalTheory.Poinc.Sep.twistSum_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedSemiAbelianGaloisDescent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem has_of_galois_action : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), GalAct ρ hD U' → Has D := by
  intro R R' _ _ _ _ _ _ ρ hB hF hG D D' hD A' G' _ _ hG' U' a
  obtain ⟨N, hL, hinv⟩ := exists_near_galois_quotient R hB R' ρ hF hG D D' hD A' G' hG' U' a
  have hP : IsProper (spMap ρ) := by
    have : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hF.2.2
    infer_instance
  have hS : Surjective (spMap ρ) := ⟨hF.2.2.to_isIntegral.comap_surjective hF.2.1⟩
  obtain ⟨G, _, _, β, i, hGs, hpb, -, hu⟩ :=
    descend_of_near R hB.1 (Sp R') (spMap ρ) hP hS inferInstance G' hG' N hL
  exact has_of_galAct R hB R' ρ hF hG D D' hD A' G' hG' U' a G β hGs hpb fun σ =>
    comp_eq_of_near ρ hF.2.2 G' hG' N G hGs.separated β hpb.1.w i hu σ (a.act σ) (a.cart σ).1.w (hinv σ)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassSumsDeeperLevelGeometricCoreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_classSums_deeper_level_geometric_core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_ : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k : ∀ y, Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y) (Q : Type) (F : (Fin 1 → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearEquiv.refl (𝓞 E) (Φ.X y₀) ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → F c κ = F c' κ) ∧ (∀ y c κ (μ : Fin 1 → Φ.X y), (∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → qW !![(1 : ℤ)] (Φ.β y) μ ≤ qW !![(1 : ℤ)] (Φ.β y) μ') → ‖ev' y (F c κ)‖ ≤ Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ (∀ y (μ : Fin 1 → Φ.X y), (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → μ' ≠ μ → qW !![(1 : ℤ)] (Φ.β y) μ < qW !![(1 : ℤ)] (Φ.β y) μ') → ∃ c κ, (∀ u, CongMod N (μ u) (k y (c u))) ∧ ‖ev' y (F c κ)‖ = Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y₀, (N : ℤ) ∣ LinearMap.det (γ.toLinearMap.restrictScalars ℤ) - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (F c κ) = F (fun u => γ (c u)) κ := by
  first | exact @GlobalTheory.UPoinc.UCore.classSums_core | exact GlobalTheory.UPoinc.UCore.classSums_core | (intros; apply GlobalTheory.UPoinc.UCore.classSums_core <;> assumption)
end

