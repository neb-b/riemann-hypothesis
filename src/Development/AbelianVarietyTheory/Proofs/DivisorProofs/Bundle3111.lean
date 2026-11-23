module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotTwistSumZeroFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxOrbitSumsOfGaloisClassSums
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2971
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumExponentsDifferAffineTwoMembers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.GSep.TransTerms

theorem sum_terms {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {x₀ : X₁.S.Gam}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X} (𝔪 : GMem X₁ z₁ act V ev X t δ)
    {C : Type} (lab : C → X₁.S.Gam) (T : X → C → V) (hT : 𝔪.Terms x₀ lab T) (c : C) :
    SumF (maximalIdeal V) (FractionRing V) (fun mu : X => algebraMap V (FractionRing V) (T mu c) *
      𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) (𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem (lab c)⟩) := by
  obtain ⟨x, fr, th, w₀, s, g', w, -, -, hth, -, hexp, hg', hTe⟩ := hT
  have hO := (hg' c).2.2 1 le_rfl (w c) (fun z J _ => (pow_one _).symm) (hg' c).2.1 th s _ hexp (hth (lab c))
  have := sumF_comp_equiv 𝔪.e₈.toEquiv hO
  convert this using 1
  funext mu
  exact hTe mu c

theorem twistSum_of_transExp {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {x₀ : X₁.S.Gam} (hd : X₁.M.Div X₁.S.th x₀ z₁) (sg : ℤˣ)
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X} (𝔪 : GMem X₁ z₁ act V ev X t δ)
    (hW : ∀ (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), TorChar 𝔪 τ χ →
      ∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) =
        𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))
    {C : Type} (lab : C → X₁.S.Gam) (hlab : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁) (T : X → C → V)
    (hT : 𝔪.Terms x₀ lab T) (c : C) (τ : X₁.S.Gam) (hτ : τ ∈ X₁.S.TT X₁.M z₁) (e : ℕ)
    (hE : TransExp 𝔪 x₀ (lab c) τ e) : TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e := by
  obtain ⟨χ, hχ1, hχ2⟩ := GlobalTheory.T.exists_level_killed_char_of_torus_label I X₁ z₁ act V ev X t δ 𝔪 τ hτ
  obtain ⟨T', hT'⟩ := _root_.GlobalTheory.GSep.TermsExt.exists_terms_translate I X₁ z₁ act x₀ hd V ev X t δ 𝔪 C lab hlab T hT c τ hτ
  have hprop := hE χ ⟨hχ1, hχ2⟩ C lab T hT c rfl Unit _ T' hT' () rfl
  have hsum := sumF_const_mul (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)))
    (sum_terms 𝔪 (fun _ : Unit => lab c + τ) T' hT' ())
  refine _root_.GlobalTheory.GSep.TwistSum₂.twistSum_of_sumF I X₁ z₁ act V ev X t δ 𝔪 x₀ C lab T sg c τ χ e
    (GlobalTheory.GSep.TwistModel.yK_th_ne_zero 𝔪 hd) (GlobalTheory.GSep.TwistModel.exists_yy 𝔪) (hW τ χ ⟨hχ1, hχ2⟩) ?_
  convert hsum using 1
  funext mu
  rw [← _root_.mul_assoc, hprop mu, _root_.mul_assoc]

end GlobalTheory.GSep.TransTerms

namespace GlobalTheory.GSep
open GlobalTheory.GSep.TransTerms

theorem twistSum_exp_affine : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∃ ε1 ε2 : X₁.S.Gam → X₁.S.Gam → ℕ, (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ (ε1 (lab c) τ)) ∧ (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y2 → C → V2, 𝔪2.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪2 lab T sg c τ (ε2 (lab c) τ)) ∧ ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((ε1 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((ε2 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  intro I X₁ z₁ act x₀ hd sg _ hW V1 _ _ _ ev1 Y1 _ t1 δ1 𝔪1 V2 _ _ _ ev2 Y2 _ t2 δ2 𝔪2
  classical
  have hA := _root_.GlobalTheory.GSep.TransTerms.trans_exp_affine I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 V2 ev2 Y2 t2 δ2 𝔪2
  choose! F1 F2 hF1 hF2 hAff using hA
  refine ⟨fun a τ => F1 τ a, fun a τ => F2 τ a, ?_, ?_, fun τ hτ => hAff τ hτ⟩
  · intro C lab hlab T hT c τ hτ
    exact twistSum_of_transExp hd sg 𝔪1 (fun τ χ hχ => hW V1 ev1 Y1 t1 δ1 𝔪1 τ χ hχ.1 hχ.2) lab hlab T hT c τ hτ _
      (hF1 τ hτ (lab c) (hlab c))
  · intro C lab hlab T hT c τ hτ
    exact twistSum_of_transExp hd sg 𝔪2 (fun τ χ hχ => hW V2 ev2 Y2 t2 δ2 𝔪2 τ χ hχ.1 hχ.2) lab hlab T hT c τ hτ _
      (hF2 τ hτ (lab c) (hlab c))

end GlobalTheory.GSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassicalTraitsFourierTermsAllLevels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem USetup.isNoetherianRing_stalk {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {C : UCompact Xo c} (X₁ : USetup C) (z₁ : X₁.M.Z) :
    IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  have : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  have := X₁.M.lft
  have : IsLocallyNoetherian (Sp X₁.o₁) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.o₁)))
  have : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  infer_instance

theorem posW_one_one : PosW (!![1] : Matrix (Fin 1) (Fin 1) ℤ) := by
  unfold PosW
  have : ((!![1] + (!![1] : Matrix (Fin 1) (Fin 1) ℤ).transpose).map (Int.cast : ℤ → ℝ)) = Matrix.diagonal fun _ => 2 := by
    ext i j
    fin_cases i; fin_cases j; simp [Matrix.vecHead, Function.swap]
  rw [this, Matrix.posDef_diagonal_iff]
  intro _; norm_num

theorem four_of_classical : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → Φ.Four !![(1 : ℤ)] (X₁.S.r * X₁.S.N) := by
  intro E _ _ _ H Dw hpq l Xo c C X₁ p _ z₁ Φ h y₀ N₀
  obtain ⟨N, hN, hd, k, Q, t, B, _, _, _, _, _, 𝔷, hinj, hfix, hmax, hk, hu, ht, hc⟩ :=
    _root_.GlobalTheory.UPoinc.uclassSums_deeper E H Dw hpq l Xo c C X₁ p z₁ Φ h y₀ (N₀ + 1)
  have := X₁.normal.isDomain_stalk z₁
  have := X₁.normal.isIntegrallyClosed_stalk z₁
  have := X₁.isNoetherianRing_stalk z₁
  exact ⟨N, by omega, hd, k, Q, t, hk, hu, ht,
    _root_.GlobalTheory.Poinc.OrbTrace.orbitSums_of_classSums (𝓞 E) H.bar (min Dw.p Dw.q) p _ Φ 1 !![(1 : ℤ)] _ N y₀ k Q t B hinj hfix 𝔷 hmax (by omega) posW_one_one hu hc⟩

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickPrincipalObjectsIsoUnique
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

theorem actPB_of_zRel : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∀ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P (GlobalTheory.ZarhinFam.bar d) act₁ → Adj z₂.A z₂.P (GlobalTheory.ZarhinFam.bar d) act₂ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₁ act₁ → ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z₂ act₂ → ActPB z₁ act₁ z₂ act₂ (𝟙 S) := by
  intro h M d _ _ _ hd _ jl n o κ S t c z₁ z₂ act₁ act₂ hdS hK hP₁ hP₂ hA₁ hA₂ hJ₁ hJ₂ hZ₁ hZ₂
  obtain ⟨inc₁, pr₁, hi₁, hp₁, hip₁, hpi₁, hL₁, -, hz₁⟩ := hZ₁
  obtain ⟨inc₂, pr₂, hi₂, hp₂, hip₂, hpi₂, hL₂, -, hz₂⟩ := hZ₂
  have hker : ∀ (T : Over S) (x : T ⟶ c.A), x ≫ inc₁ ≫ act₁ (GlobalTheory.ZarhinFam.polUnit d) = 1 ↔
      x ≫ inc₂ ≫ act₂ (GlobalTheory.ZarhinFam.polUnit d) = 1 := fun T x =>
    ⟨fun hx => GlobalTheory.T.zarhin_polarisation_kernel_le_unit_kernel h M d hd S t c z₂ act₂ inc₂ pr₂ hdS hK hP₂ hA₂ hJ₂ hi₂ hp₂ hip₂ hpi₂ hL₂ T x
        (GlobalTheory.T.zarhin_polarisation_unit_kernel_le_kernel h M d hd S t c z₁ act₁ inc₁ pr₁ hdS hK hP₁ hA₁ hJ₁ hi₁ hp₁ hip₁ hpi₁ hL₁ T x hx),
     fun hx => GlobalTheory.T.zarhin_polarisation_kernel_le_unit_kernel h M d hd S t c z₁ act₁ inc₁ pr₁ hdS hK hP₁ hA₁ hJ₁ hi₁ hp₁ hip₁ hpi₁ hL₁ T x
        (GlobalTheory.T.zarhin_polarisation_unit_kernel_le_kernel h M d hd S t c z₂ act₂ inc₂ pr₂ hdS hK hP₂ hA₂ hJ₂ hi₂ hp₂ hip₂ hpi₂ hL₂ T x hx)⟩
  obtain ⟨e, he, hinc, hact⟩ := GlobalTheory.T.zarhinTrick_actions_isomorphic h M d hd S t c z₁ z₂ act₁ act₂ inc₁ pr₁ inc₂ pr₂ hdS hA₁ hA₂
    hi₁ hp₁ hip₁ hpi₁ hi₂ hp₂ hip₂ hpi₂ hker
  have hLB := GlobalTheory.T.zarhinTrick_bundle_unique_of_order_linear_iso h M d hd S t c z₁ z₂ act₁ act₂ inc₁ pr₁ inc₂ e hdS hK hP₁ hP₂ hA₁ hA₂ hJ₁ hJ₂
    hi₁ hp₁ hip₁ hpi₁ hL₁ hL₂ he hinc hact
  haveI := he
  refine ⟨e.hom.left, (e.hom ⊗ₘ e.hom).left, isGrpPullback_of_iso e, ⟨?_, ?_⟩, hLB, fun a => ?_, fun o => ?_⟩
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_fst]
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_snd]
  · rw [Category.id_comp, ← Over.comp_left, hz₁ a, hz₂ a]
    congr 1
    have key := map_list_prod (IsMonHom.monoidHom e.hom (𝟙_ (Over S)))
      (List.ofFn fun k => c.lev (κ k a) ≫ inc₁ ≫ act₁ (o k))
    refine key.trans ?_
    rw [List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    show (c.lev (κ k a) ≫ inc₁ ≫ act₁ (o k)) ≫ e.hom = _
    rw [Category.assoc, Category.assoc, hact, ← Category.assoc inc₁, hinc]
  · rw [← Over.comp_left, ← Over.comp_left, hact o]

end GlobalTheory.ZarhinFam
end
end

