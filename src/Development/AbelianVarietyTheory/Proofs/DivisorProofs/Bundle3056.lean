module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3043
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2722
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationCombIntegrableThetaKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ZConv

theorem zconv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∃ z : GA D (G.V (.grid i j)) →₀ ℂ, zdeg z ≠ 0 ∧
    (∀ g, IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd (.grid i j)) (M.ν (.grid i j))) ∧
    Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) => F p.1 * translates z (kerSmall W Θ' p.1 g₁) p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid i j)).restrict (M.fd (.grid i j)))) := by
  intro D T L sc G hK hP μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hB g₁
  obtain ⟨e, Bs, Γ, X, om, om', h, hTr, hv⟩ := hT M hM
  obtain ⟨z, Φ, a, C₀, hz, hΦ, hid⟩ := _root_.GlobalTheory.ZConvIdent.translates_kerSmall_le_theta hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  have dec := (hK.1 D.host.F D.host.E D.sp.cm.sig Bs _ _ Γ X om om' hTr).1
  obtain ⟨C, k, hC⟩ := (dec.2 Φ hΦ).1 0
  have hbd : ∀ g u, ‖translates z (kerSmall W Θ' g g₁) u‖ ≤
      |C₀| * |C| * (2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁) ^ k := by
    intro g u
    obtain ⟨γ, hγ, hle⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight _ g
    have e1 : translates z (kerSmall W Θ' g g₁) u = translates z (kerSmall W Θ' (γ * g) g₁) u := by
      simp only [translates, _root_.GlobalTheory.ZConvLeft.kerSmall_rat_left hL W B ρ t i j Θ Θ' hΘ g₁ γ hγ]
    rw [e1]
    have h1 := hC (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))
    rw [pow_zero, mul_one] at h1
    have h2 := _root_.GlobalTheory.BlockHeight.ht_blkU_le _ _ e h.JWW (γ * g) g₁
    have h3 : (0 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) := NNReal.coe_nonneg _
    have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ≤
        2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁ :=
      h2.trans (mul_le_mul_of_nonneg_right hle (GlobalTheory.Grow.height_pos _ _).le)
    calc _ ≤ C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ := hid _ _
      _ ≤ |C₀| * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self C₀) (norm_nonneg _)
      _ ≤ |C₀| * (|C| * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h3 k)))
            (abs_nonneg C₀)
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h4 k) (mul_nonneg (abs_nonneg C₀) (abs_nonneg C))

  have hWl := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  have hVl := (hM.vtx (.grid i (j + 1)) ⟨i.2.le, j.2⟩).haar_fund
  haveI : IsFiniteMeasure ((M.ν (.grid i j)).restrict (M.fd (.grid i j))) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hWl.1 hWl.2).ne
  haveI : IsFiniteMeasure ((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hVl.1 hVl.2).ne
  have hcont := _root_.GlobalTheory.SmallRoute.continuous_translates_kerSmall hL W B ρ t i j Θ Θ' hΘ g₁ z
  have hRD := GlobalTheory.Grow.rapidDec_of_cuspForm (GlobalTheory.Grow.cuspRapidDecay_of_bound hP) W.θ_is hF hFc
  obtain ⟨Bd, hBd⟩ := hRD.decay k
  refine ⟨z, hz, fun g => ?_, ?_⟩
  · exact Integrable.of_bound ((hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable) _
      (.of_forall fun u => hbd g u)
  · have h0 : (0 : ℝ) ≤ |C₀| * |C| * (2 * GlobalTheory.Grow.height _ g₁) ^ k :=
      mul_nonneg (mul_nonneg (abs_nonneg C₀) (abs_nonneg C)) (pow_nonneg (by have := GlobalTheory.Grow.height_pos _ g₁; positivity) k)
    refine Integrable.of_bound ((hRD.continuous.comp continuous_fst).mul hcont).aestronglyMeasurable
      (|C₀| * |C| * (2 * GlobalTheory.Grow.height _ g₁) ^ k * Bd) (.of_forall fun p => ?_)
    rw [norm_mul]
    calc ‖F p.1‖ * ‖translates z (kerSmall W Θ' p.1 g₁) p.2‖ ≤
          ‖F p.1‖ * (|C₀| * |C| * (2 * GlobalTheory.Grow.quotHeight _ p.1 * GlobalTheory.Grow.height _ g₁) ^ k) :=
          mul_le_mul_of_nonneg_left (hbd _ _) (norm_nonneg _)
      _ = |C₀| * |C| * (2 * GlobalTheory.Grow.height _ g₁) ^ k * (‖F p.1‖ * GlobalTheory.Grow.quotHeight _ p.1 ^ k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hBd _) h0
end GlobalTheory.ZConv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreEighthPowerThetaObjectSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem sharp_fibre_theta_object : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ), ∃ (J : Type) (_ : Finite J)
    (Mat : J → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ) (κ : ℕ) (w w' : J),
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁),
  (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (v : Ix (8 * gQ) ((l ^ j) ^ 2) → k₀) (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    t.Shape Mat κ ∧ t.Prim w w' ∧ t.HasTh (𝟙 _) (fun a => k₀.subtype (v a)) ∧
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) ∧
    ∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ a, q ≫ ψ = (t.lab a).left := by
  intro W hW gQ
  obtain ⟨J, hJ, Mat, κ, w, w', hA⟩ := _root_.GlobalTheory.Poinc.Sep.E8Fibration.eighthPowerFibre_thetaObj W hW gQ
  refine ⟨J, hJ, Mat, κ, w, w', ?_⟩
  intro l hl ho j hj V V₁ _ _ _ _ _ hCN hu Q hQ ρ hρ D e hS C u mo hmo hT K _ _ ev k₀ hk₀ hr
  obtain ⟨bT, t, ψ, h1, h2, h3, h4, h5⟩ := hA l hl ho j hj V V₁ hCN hu Q hQ ρ hρ D e hS K ev k₀ hk₀
  obtain ⟨v, hv⟩ := _root_.GlobalTheory.Poinc.Sep.fibre_theta_consts_in_subfield W hW gQ J l hl ho j hj V V₁ hCN hu Q hQ ρ hρ D e hS C u mo hmo hT K ev k₀ hk₀ hr bT t ψ h3 h4
  exact ⟨bT, t, v, ψ, h1, h2, hv, h3, h4, h5⟩

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrExp
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

namespace GlobalTheory.GSep.TransTerms

variable {I : Type}

def FrExp {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
    (𝔪 : GMem X₁ z₁ act V ev X t δ) (a τ : X₁.S.Gam) (e : ℕ) : Prop :=
  (∃ χ, TorChar 𝔪 τ χ) ∧
  ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
    (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : GtPtF 𝔪.D.toPre (FractionRing V))
    (w : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b),
    (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧
    (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) ∧
    (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) ∧ w₀.IsGen ∧
    𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s ∧
    (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g' o ∧ o.IsZero) ∧ w.IsGen ∧ 𝔪.Over' w₀ g' w (x a) (fr a) ∧
    ∀ χ, TorChar 𝔪 τ χ → ∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∀ g'' : GtPtF 𝔪.D.toPre (FractionRing V),
      g'.IsAdd g₀ g'' → ∀ w'' : Frm 𝔪.D.toPre (FractionRing V) 1 g''.b, w''.IsGen →
      (∀ z J, Good 𝔪.D.toPre.P.L z J → (val w (𝟙 _) z J).val =
        cstH (R := V) z (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e))) * (val w'' (𝟙 _) z J).val) →
      𝔪.Over' w₀ g'' w'' (x (a + τ)) (fr (a + τ))

end GlobalTheory.GSep.TransTerms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTowerDividingLabelStaysDividing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.DeepDivG

variable {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {x₀ : X₁.S.Gam}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}

end GlobalTheory.GSep.DeepDivG

namespace GlobalTheory.GSep.DeepDivG

theorem tower_same {I : Type} {X₁ : GlobalTheory.GSep.GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : GlobalTheory.GSep.Tower X₁ act) :
    GlobalTheory.Poinc.Same X₁.ρ (fun _ => 𝟙 _) 𝔗.X₂.ρ (fun _ => 𝟙 _) 𝔗.lam (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁) := by
  let f₂ : Sp 𝔗.X₂.Ω₁ ⟶ Sp 𝔗.X₂.S.R := spMap 𝔗.X₂.S.R.val.toRingHom
  let polPull {S S' : Scheme.{0}} (P : PolAV S) (f : S' ⟶ S) : PolAV S' := by
    exact {
      A := (Over.pullback f).obj P.A,
      isAb := TLinPf.isAb_pullback f P.A P.isAb,
      g := P.g,
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (isGrpPullback_pullback P.A f).1 P.smoothDim,
      L := P.L.pull (pullback.fst P.A.hom f),
      isLB := LB.isLB_pull P.isLB _,
      rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A f) P.rigid,
      sym := PolBaseChange.sym_pull (isGrpPullback_pullback P.A f) P.sym,
      ample := by
        haveI := P.isAb.proper
        exact AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom f)
      ktriv := by
        obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (LB.isLB_pull P.isLB (pullback.fst P.A.hom f))
        exact kTriv_pull (isGrpPullback_pullback P.A f) P.isLB (LB.isLB_pull P.isLB _) ((isGen_iff w).1 hw) P.ktriv } 
  let P₀ := polPull 𝔗.X₂.ρ.P f₂
  let a' : P₀.A.left ⟶ 𝔗.X₂.ρ.P.A.left := pullback.fst 𝔗.X₂.ρ.P.A.hom f₂
  have hring : (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom = 𝔗.X₂.S.R.val.toRingHom.comp 𝔗.om := by
    ext x; exact (𝔗.om_eq x).symm
  have hsp : spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) = f₂ ≫ spMap 𝔗.om := by
    rw [hring]; exact Spec.map_comp (CommRingCat.ofHom 𝔗.om) (CommRingCat.ofHom 𝔗.X₂.S.R.val.toRingHom)
  have ha' : IsGrpPullback P₀.A 𝔗.X₂.ρ.P.A f₂ a' := isGrpPullback_pullback _ _
  have hr : LBIso P₀.L (𝔗.X₂.ρ.P.L.pull a') := ⟨idIso _, idIso_isGen P₀.isLB⟩
  refine ⟨P₀, a' ≫ 𝔗.φ, a', fun _ => 𝟙 _, ?_, ha', ?_, hr, ?_, ?_⟩
  · exact (ha'.comp 𝔗.cart).congr hsp.symm rfl
  · exact LBIso.trans P₀.isLB (pull_isLB 𝔗.X₂.ρ.P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hr (lbIso_pull_comp 𝔗.lb a')
  · intro E
    exact ⟨by simp, by simp⟩
  · intro x
    have hc : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.X₂.ρ.P.A.hom = 𝟙 _ ≫ f₂ := by
      rw [Category.assoc, Over.w (𝔗.X₂.ρ.pt (𝔗.lam x))]
      simp [baseOver]
    refine ⟨pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc, ?_, ?_⟩
    · have hw : pullback.lift (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) (𝟙 _) hc ≫ a' = f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left :=
        pullback.lift_fst _ _ _
      have h3 : (f₂ ≫ (𝔗.X₂.ρ.pt (𝔗.lam x)).left) ≫ 𝔗.φ =
          spMap ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp X₁.S.R.val.toRingHom) ≫ (X₁.ρ.pt x).left := by
        rw [Category.assoc, 𝔗.lam_pt, hsp, Category.assoc]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝔗.φ) hw).trans h3)
    · exact pullback.lift_fst _ _ _

end GlobalTheory.GSep.DeepDivG


open GlobalTheory.GSep.DeepDivG in
theorem GlobalTheory.GSep.DeepDivG.div_lam : (∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → (∀ m : ℕ, m ≠ 0 → IsUnit (m : X₁.M.Z.presheaf.stalk z₁)) → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂) := by
  intro I X₁ z₁ act hact hunit 𝔗 z₂ hz₂ x₀ hx V _ _ _ ev X _ t δ _
  have hk : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  have hdvd : X₁.S.r * X₁.S.N ∣ 𝔗.X₂.S.r * 𝔗.X₂.S.N := ⟨𝔗.d, 𝔗.lev⟩
  obtain ⟨a, ha, hdv⟩ := GlobalTheory.GSep.exists_div_torsion 𝔗.X₂ z₂ _ (X₁.S.N_ge.trans (Nat.le_mul_of_pos_left _ X₁.S.r_pos)) hdvd
  have hL : 0 < 𝔗.X₂.S.r * 𝔗.X₂.S.N := Nat.mul_pos 𝔗.X₂.S.r_pos (by have := 𝔗.X₂.S.N_ge; omega)
  choose x hxa using fun s => DivDeep.exists_eq_smul_of_smul_eq_zero hL hdvd (a s) (congrFun ha s)
  have hd : 𝔗.X₂.S.r * 𝔗.X₂.S.N / (X₁.S.r * X₁.S.N) = 𝔗.d := by
    rw [𝔗.lev]; exact Nat.mul_div_cancel_left _ hk
  rw [hd] at hxa
  obtain ⟨b, hb⟩ := 𝔗.lam_range x
  obtain rfl : 𝔗.lam b = a := hb.trans (funext hxa)
  obtain ⟨k, hk, e⟩ := DivDeep.same_ratio (GlobalTheory.GSep.DeepDivG.tower_same 𝔗) x₀ b
  set φ := algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁
  have h₁ : φ (X₁.S.th x₀) ≠ 0 := (map_ne_zero φ).2 hx.1
  have h₂ := hdv.1
  have h₃ : 𝔗.X₂.S.th (𝔗.lam x₀) * φ (X₁.S.th b) ≠ 0 := fun h => by
    rw [h, zero_pow hk.ne'] at e
    exact pow_ne_zero k (mul_ne_zero h₂ h₁) e.symm
  have h₄ := left_ne_zero_of_mul h₃
  have h₅ := right_ne_zero_of_mul h₃
  have hN : IsIntegrallyClosed (𝔗.X₂.M.O z₂) := RatModel.isIntegrallyClosed_O (fun z => by
    haveI := 𝔗.X₂.normal
    exact ⟨𝔗.X₂.normal.isDomain_stalk z, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z⟩) z₂
  have m₁ : 𝔗.X₂.S.th (𝔗.lam b) * φ (X₁.S.th x₀) / (𝔗.X₂.S.th (𝔗.lam x₀) * φ (X₁.S.th b)) ∈ 𝔗.X₂.M.O z₂ :=
    DivDeep.root_mem_O hN hk (by rw [div_pow, e, div_self (pow_ne_zero k (mul_ne_zero h₂ h₁))])
  have m₂ : φ (X₁.S.th b / X₁.S.th x₀) ∈ 𝔗.X₂.M.O z₂ := by
    obtain ⟨U, f, hU, hf⟩ := hx.2 b
    refine ⟨𝔗.p ⁻¹ᵁ U, 𝔗.p.app U f, show 𝔗.p z₂ ∈ U from hz₂ ▸ hU, ?_⟩
    refine (GlobalTheory.Points.valR_comp 𝔗.X₂.M.pt 𝔗.p U f).symm.trans ?_
    rw [𝔗.p_pt, ← hf]
    exact GlobalTheory.Points.valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt ⟨_, hU⟩) f
  refine ⟨h₄, fun j => ?_⟩
  have := mul_mem (hdv.2 j) (mul_mem m₁ m₂)
  convert this using 1
  rw [map_div₀]
  field_simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsIsotropicCommutatorPairingPower
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd

open GlobalTheory.CechPic GlobalTheory.DiagPairing GlobalTheory.HeckeWeilLift

theorem exists_weilIs_heckeA : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g₁ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ g₂ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∃ v : Γ((𝟙_ (Over S)).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 g₂) v := by
  intro p _ D R _ b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₁ hg₁ g₂ hg₂
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ o.A), pc o.isLB (x * x') y = pc o.isLB x y + pc o.isLB x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ o.A), pc o.isLB x (y * y') = pc o.isLB x y + pc o.isLB x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  have hcls : cls _ hQ = (k ^ 2 / c) • cls o.P o.isLB := by
    refine (cls_linComb o.isLB (K := Fin (k ^ 2 / c)) (fun _ => 𝟙 _) (fun _ => 1) hQ).trans ?_
    simp [pull_id]
  have hQB : ∀ (T : Over S) (x x' y : T ⟶ o.A), qc hQ (x * x') y = qc hQ x y + qc hQ x' y :=
    fun T x x' y => by
      unfold qc
      rw [hcls, map_nsmul, map_nsmul, map_nsmul]
      exact (congrArg _ (hB T x x' y)).trans (smul_add _ _ _)
  have hQB' : ∀ (T : Over S) (x y y' : T ⟶ o.A), qc hQ x (y * y') = qc hQ x y + qc hQ x y' :=
    fun T x y y' => by
      unfold qc
      rw [hcls, map_nsmul, map_nsmul, map_nsmul]
      exact (congrArg _ (hB' T x y y')).trans (smul_add _ _ _)
  obtain ⟨t₁, -⟩ := GlobalTheory.T.hecke_coefficients_congruence p D R b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₁ hg₁
  obtain ⟨-, t₂⟩ := GlobalTheory.T.hecke_coefficients_congruence p D R b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₂ hg₂
  have hA2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  exact CommutatorPairing.exists_weilIs hG hA2 hQ
    (fun _ => ⟨⊤, trivial, exists_theta_left hQB (Out.overResι ⊤) g₁ t₁⟩)
    (fun _ => ⟨⊤, trivial, exists_theta_right hQB' (Out.overResι ⊤) g₂ t₂⟩)

theorem weilIs_heckeA_pow_eq_one {S : Scheme.{0}} {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]
    {b : Base D R} {s : S ⟶ Sp R} (f : D.La →+ D.La) (c k N : ℕ) (o : Obj b (N * k) s)
    (g₁ : 𝟙_ (Over S) ⟶ o.A) (hg₁ : g₁ ∈ heckeSubA o f N) (g₂ : 𝟙_ (Over S) ⟶ o.A)
    (v : Γ((𝟙_ (Over S)).left, ⊤)ˣ)
    (hv : Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A)
      (lift 1 g₂) v) : v ^ k = 1 := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hA : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have hL : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  have hk1 : g₁ ^ k = 1 := pow_eq_one_of_mem o f g₁ hg₁
  have hxk : (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) ^ k = 1 := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [MonObj.pow_comp]; simp [hk1]
    · rw [MonObj.pow_comp]; simp
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk, pow_zero]
  have pw : ∀ m : ℕ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1
      ((lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) ^ (m + 1)) (lift 1 g₂) (v ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hv
    | succ m ih =>
      rw [pow_succ _ (m + 1), pow_succ v (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL ih hv
  have hp := pw (k - 1)
  rw [Nat.sub_add_cancel hk, hxk] at hp
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL hp hp
  rw [_root_.mul_one] at h11
  exact mul_eq_left.1 (GlobalTheory.CommutatorPairing.weilIs_unique hG hA hL h11 hp)

theorem weilIs_heckeSubA_one : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g₁ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ g₂ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 g₂) 1 := by
  intro p _ D R _ b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₁ hg₁ g₂ hg₂
  obtain ⟨v, hv⟩ := exists_weilIs_heckeA p D R b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₁ hg₁
    g₂ hg₂
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  have hA2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have h1 : v = 1 := by
    refine GlobalTheory.rootOfUnity_eq_one_of_geom R S s k v (b.unit k hk)
      (weilIs_heckeA_pow_eq_one (h (N * k)) c k N o g₁ hg₁ g₂ v hv) ?_
    intro K _ _ x β hx
    have hp := GlobalTheory.CommPairing.weilIs_pull (A := G2 o.A) GlobalTheory.globalFns_holds hA2 hQ (toUnit (Over.mk x)) hv
    exact GlobalTheory.T.hecke_coefficients_congruence_scaled p D R b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₁ hg₁ g₂ hg₂ K x β hx _ hp
  subst h1
  exact hv

end GlobalTheory.UPel.HT.HeckeAd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdeleUnitCongruenceSequence
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_adele_unit_congruence_sequence : ∀ (p : ℕ) [Fact p.Prime] (ε ε' : AfP p), IsIntAf ε → IsIntAf ε' → ε * ε' = 1 → ∃ u : ℕ → ℤ, (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ u (n * m) - u n) ∧ ∀ n : ℕ, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∃ β : AfP p, IsIntAf β ∧ ε = (u n : AfP p) + (n : AfP p) * β := by
  first | (exact @GlobalTheory.UnitApprox.exists_int_approx) | (exact GlobalTheory.UnitApprox.exists_int_approx) | (intros; apply GlobalTheory.UnitApprox.exists_int_approx  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEndomorphismIntegralApproximation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_endomorphism_integral_approximation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) → ∃ h : ℕ → D.La →+ D.La, ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (h n x) + n • w := by
  first | (exact @GlobalTheory.LKGeo.LiftSys.exists_lift_sys) | (exact GlobalTheory.LKGeo.LiftSys.exists_lift_sys) | (intros; apply GlobalTheory.LKGeo.LiftSys.exists_lift_sys  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickLevelSymplecticGeometricPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinTrick_level_symplectic_geometricPoints : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : cycAway M →+* k) (z : kˣ), x ≫ t = spMap β → (z : k) = β (zetaAway M) → (∀ a, (toUnit (Over.mk x) ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a = 1 ↔ ∃ b, a = M • b)) ∧ (∀ g : Over.mk x ⟶ (GlobalTheory.ZarhinFam.Zob c.A B), g ^ M = 1 → ∃ a, toUnit _ ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a = g) ∧ ∀ a b, Out.WeilIs (GlobalTheory.ZarhinFam.Zob c.A B) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left) M (toUnit (Over.mk x) ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a) (toUnit _ ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) b) (unitOn (z ^ (2 * omegaStd a b))) := by
  first | (exact @GlobalTheory.ZarhinFam.geom_levZ) | (exact GlobalTheory.ZarhinFam.geom_levZ) | (intros; apply GlobalTheory.ZarhinFam.geom_levZ  <;> assumption)
end

