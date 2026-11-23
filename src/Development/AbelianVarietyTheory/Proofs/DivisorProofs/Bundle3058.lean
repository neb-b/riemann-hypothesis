module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallThetaKernelTranslateIntegrable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallConv

theorem splitBound_ge : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ _ => 11 ≤ D.host.splitBound := by
  exact ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS _ _ _ => hS.size.2.1.eleven_le⟩⟩

theorem standing : Big fun ch => ∀ t, SquareStanding ch.G t := by
  obtain ⟨CF0, hH⟩ := splitBound_ge.and _root_.GlobalTheory.PlacesPrime.places_prime_to_level
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc t => ?_⟩
  obtain ⟨h11, hW⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc
  refine ⟨h11, fun w hw => ?_⟩
  classical
  unfold locPl at hw
  rcases Finset.mem_union.1 hw with hw | hw
  · exact hW w hw
  · intro hmem
    have h1 := (hS.core.lev.Q_off t w hw).1
    have h2 := hS.guard.2 t w hw
    push_cast at hmem h1 h2
    rcases w.isPrime.mem_or_mem hmem with h | h
    · exact h1 (Ideal.mul_mem_right _ _ h)
    · exact h2 (Ideal.mul_mem_left _ _ h)

end GlobalTheory.SmallConv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermsWitnessesBaseChangeAlongTowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.termsWitnesses_baseChange_along_tower : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₁ : X₁.M.Z)
    (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type)
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
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ)
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
  first | exact @GlobalTheory.GSep.TermsTrans.terms_witnesses_baseChange | exact GlobalTheory.GSep.TermsTrans.terms_witnesses_baseChange | (intros; apply GlobalTheory.GSep.TermsTrans.terms_witnesses_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGeneratorTorsionFrameValueEqScalarMulRootStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGenerator_torsionFrame_value_eq_scalar_mul_root : ∀ (m : ℕ), Odd m → 3 ≤ m → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ k : ℕ, k ≠ 0 → IsUnit (k : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (x : Over.mk (spMap ev) ⟶ D.P.A) (τ : LB.Gen (LB.LinComb D.P.L (Y := (Over.mk (spMap ev)).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (c : K), IsTorsFrame D.P ρ₀ (m ^ 2) x τ → IsValueAt D.P.A D.P.L ((1 : ℕ) : ℤ) th x (powFrame D.P.A D.P.L x τ ((1 : ℕ) : ℤ)) (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  first | exact @GlobalTheory.USep.FrameInt.frameValue_eq_lam_root_mul | exact GlobalTheory.USep.FrameInt.frameValue_eq_lam_root_mul | (intros; apply GlobalTheory.USep.FrameInt.frameValue_eq_lam_root_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberDividingLabelClassZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.DivInt

variable {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}

theorem t_mem (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) {mu : X} (h : mu ≠ 0) : t mu ∈ maximalIdeal V := by
  haveI := 𝔪.cn.2.2.2
  obtain ⟨u, hu⟩ := 𝔪.psi mu
  obtain ⟨r, hr, -, hm, -⟩ := (PsiCoordLocal.main V 𝔪.D 𝔪.cn.2.1 (𝔪.e₈ mu)).1
  obtain ⟨v, hv⟩ := PsiCoordLocal.exists_unit_of_coord hr hu
  have : (u : V) * t mu ∈ maximalIdeal V := hv ▸ Ideal.mul_mem_left _ _ (hm (𝔪.e₈.map_ne_zero_iff.2 h))
  exact (Ideal.unit_mul_mem_iff_mem _ u.isUnit).1 this

theorem ratio (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) {a : X₁.S.Gam} (ha : X₁.M.Div X₁.S.th a z₁) (b : X₁.S.Gam) :
    ∃ v : V, 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ = algebraMap V (FractionRing V) v * 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ := by
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  set yC : Sp V ⟶ X₁.M.Z := spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hyC
  have hC : yC (closedPoint V) ⤳ z₁ := sp _
  set y : Sp (FractionRing V) ⟶ X₁.M.Z := jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy
  set ξ := y (closedPoint (FractionRing V)) with hξ
  have hyξ : ∀ w, y w ⤳ ξ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hξz : ξ ⤳ z₁ := sp _
  have hr : X₁.S.th b / X₁.S.th a ∈ X₁.M.O z₁ := ha.2 b
  have hrξ : X₁.S.th b / X₁.S.th a ∈ X₁.M.O ξ := RatModel.O_le_of_specializes hξz hr
  have haξ : X₁.S.th a ∈ X₁.M.O ξ := 𝔪.reg _ (X₁.S.th_mem a)
  refine ⟨RatModel.valLoc yC z₁ hC ⟨_, hr⟩, ?_⟩
  have e1 : X₁.S.th b = X₁.S.th b / X₁.S.th a * X₁.S.th a := (div_mul_cancel₀ _ ha.1).symm
  have e2 : X₁.M.val y (X₁.S.th b / X₁.S.th a) = algebraMap V (FractionRing V) (RatModel.valLoc yC z₁ hC ⟨_, hr⟩) :=
    RatModel.val_spMap_comp (algebraMap V (FractionRing V)) yC hC ⟨_, hr⟩
  rw [𝔪.yK_eq, 𝔪.yK_eq]
  show X₁.M.val y (X₁.S.th b) = _ * X₁.M.val y (X₁.S.th a)
  rw [← e2, ← RatModel.val_mul hyξ hrξ haξ, ← e1]

theorem label_zero_of_mem_supI : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → 𝔪.YY a 0 := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 a ha
  have ha' : X₁.M.Div X₁.S.th a z₁ := ha
  obtain ⟨b₀, hb₀⟩ := _root_.GlobalTheory.GSep.GMem.exists_th_ne_zero I X₁ z₁ act V ev X t δ 𝔪
  have hane : 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := ratio 𝔪 ha' b₀
    rw [h0, mul_zero] at hv
    exact hb₀ hv
  obtain ⟨ν, hν1, hνm⟩ := GlobalTheory.T.exists_discreteValuation_centred_completeNormal V 𝔪.cn
  have hmax : ∀ b, ν (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) ≤ ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) := fun b => by
    obtain ⟨v, hv⟩ := ratio 𝔪 ha' b
    rw [hv, map_mul]
    exact mul_le_of_le_one_left' (hν1 v)
  obtain ⟨w, hw, hle⟩ := _root_.GlobalTheory.GSep.DivBound.theta_pow_le I X₁ z₁ act V ev X t δ 𝔪 ν hν1 hνm _ hmax a
  have h0 : ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2) ≠ 0 :=
    pow_ne_zero _ ((Valuation.ne_zero_iff ν).2 hane)
  have h1 : 1 ≤ ν (algebraMap V (FractionRing V) (t w)) := by
    have := mul_le_mul_of_nonneg_left hle
      (zero_le' : (0 : WithZero (Multiplicative ℤ)) ≤ (ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2))⁻¹)
    rwa [← _root_.mul_assoc, inv_mul_cancel₀ h0, _root_.one_mul] at this
  by_cases hw0 : w = 0
  · exact hw0 ▸ hw
  · exact absurd h1 (not_le.2 (hνm _ (t_mem 𝔪 hw0)))

end GlobalTheory.GSep.DivInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberOfUnitaryMonomialUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.USep

theorem member_of_monomial_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (z₁ : X₁.M.Z) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (y : Sp (FractionRing V) ⟶ Xo.XF c) (P : PELUnif (maximalIdeal V) t), GenOf Xo c y t → ∀ (m : ℕ) (s : Fin m → V) (β : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre s β → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁) (fK : FractionRing V →+* FractionRing V₁) (r : Fin m → V₁), IsCN V₁ → Function.Injective ρ → IsLocalHom ρ → (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (ρ a)) → (∀ k, r k ^ 2 = ρ (s k)) → ∀ ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁, IsLocalHom ev → GlobalTheory.GSep.RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ π = spMap fK ≫ y ≫ C.i → ∃ (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V₁ ev (Fin 1 → P.D.toPre.X) (mono !![(1 : ℤ)] r β) (fun a mu => a • mu)) (p : IsPullDeg ρ P.D.toPre 𝔪.D.toPre), ∀ mu, p.xe (𝔪.e₈ mu) = mu 0 := by
  intro E _ _ _ H Dw hpq l Xo c C X₁ act u π hL z₁ V _ _ _ hV t y P hG m s β hmono V₁ _ _ _ ρ fK r hV₁ hinj hloc hfK hr ev hev hreg hpt
  obtain ⟨t₁, P₁, p, hG₁, hlin, hpsi⟩ := _root_.GlobalTheory.USepBC.exists_pelUnif_baseChange_of_injective E H Dw l Xo c V hV t y P hG V₁ ρ fK hV₁ hinj hloc hfK
  obtain ⟨yK, x', hyK, hx', hx'u⟩ := GlobalTheory.GSep.valPt_lies_over_unitary E H Dw hpq l Xo c C X₁ act u π hL z₁ V₁ ev (spMap fK ≫ y) hreg
    (hpt.trans (Category.assoc _ _ _).symm)
  obtain ⟨φ, hcart, hwl, hact⟩ := GlobalTheory.T.unitaryUniformisation_genericFibre_isPullback E H Dw hpq l Xo c C X₁ act u π hL V₁ hV₁ t₁ P₁ yK x' hx'
    (by rw [hx'u]; exact hG₁)
  obtain ⟨wl, hwl⟩ := hwl
  let e₈ : (Fin 1 → P.D.toPre.X) ≃+ P₁.D.toPre.X := (AddEquiv.piUnique fun _ : Fin 1 => P.D.toPre.X).trans p.xe.symm
  have he₈ : ∀ mu, p.xe (e₈ mu) = mu 0 := fun mu => by simp [e₈]
  refine ⟨{
    cn := hV₁
    loc := hev
    reg := hreg
    yK := yK
    yK_eq := hyK
    D := P₁.D
    e₈ := e₈
    G := t₁.G
    semi := t₁.semi
    A := P₁.A
    U := P₁.U
    φ := φ
    cart := hcart
    wl := wl
    wl_gen := hwl
    equiv := fun a => ?_
    psi := fun mu => ?_ }, p, he₈⟩
  · obtain ⟨En, hEn, hh⟩ := GlobalTheory.USep.conjAct_endU_chars E H V₁ hV₁ t₁ P₁ a
    refine ⟨En, by rw [hEn]; exact hact a, fun mu => ?_⟩
    rw [hh]
    apply p.xe.injective
    rw [hlin, he₈, he₈]
    rfl
  · obtain ⟨u₀, n, hn, hc⟩ := hmono (mu 0)
    rw [← he₈ mu] at hc
    obtain ⟨w, hw⟩ := hpsi _ _ hc
    refine ⟨w * Units.map ρ.toMonoidHom u₀, ?_⟩
    have hmo : mono !![(1 : ℤ)] r β mu = ρ (∏ i, s i ^ n i) := by
      simp only [mono, qW, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.empty_val', _root_.one_mul, map_prod, map_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hn i, ← hr i, ← pow_mul]
      congr 1
    rw [hmo]
    have hu : (↑(w * Units.map ρ.toMonoidHom u₀) : V₁) * ρ (∏ i, s i ^ n i) = ↑w * ρ (↑u₀ * ∏ i, s i ^ n i) := by
      rw [map_mul, Units.val_mul, Units.coe_map, _root_.mul_assoc]; rfl
    rw [hu]
    exact hw

end GlobalTheory.USep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupTowerMemberTermsBaseChange
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

namespace GlobalTheory.Poinc.Sep.BaseTerms

theorem terms_baseChange : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∃ eps : X₁.S.Gam → ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V), 𝔪.Terms x₀ lab T → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite → ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ) (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre) (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK → IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → (∃ w : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ), w.IsGen) → 𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U → (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) → 𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) = pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) → ∀ zt : 𝔗.X₂.M.Z.presheaf.stalk z₂, 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ → 𝔪₂.Terms (𝔗.lam x₀) (fun c => 𝔗.lam (lab c)) (fun mu c => ev₂ zt ^ eps (lab c) * io (T mu c)) := by
  intro g n F W Z i X₁ act 𝔗 z₁ z₂ hp x₀ hdiv
  obtain ⟨k, hk⟩ := GlobalTheory.T.frames_along_theta_tower_root_of_unity_power X₁ act 𝔗
  set M := (𝔗.X₂.S.r * 𝔗.X₂.S.N) ^ 2 with hM
  refine ⟨fun b => k x₀ + (M - 1) * k b, ?_⟩
  intro V _ _ _ ev X _ m t δ 𝔪 C lab T hT V' _ _ _ io f hf hinj hfin ev₂ 𝔪₂ ψ hD bc hExt hyK hcart hw hφ hmon hU he₈ hgen zt hzt
  obtain ⟨x, fr, th, w₀, s, g', w, h1, h2, h3, h4, h5, h6, h7⟩ := hT
  obtain ⟨wψ, hwψ⟩ := hw
  obtain ⟨j₂, hj₂⟩ := 𝔗.X₂.div z₂
  obtain ⟨u, ⟨x₂, fr₂, -, -, -, -, -, h1', h2', -⟩, -, -⟩ := _root_.GlobalTheory.Poinc.IntTerm.exists_terms _ _ F W Z i 𝔗.X₂ z₂ 𝔗.act₂ j₂ hj₂ V' ev₂ X m
    (fun k => io (t k)) δ 𝔪₂ (𝔗.X₂.S.HH 𝔗.X₂.M z₂) Subtype.val Subtype.range_coe
  obtain ⟨c₀, hc₀⟩ := hk z₁ z₂ hp V ev X m t δ 𝔪 V' io f hf ev₂ X m (fun k => io (t k)) δ 𝔪₂ ψ wψ hwψ hExt hyK hcart hφ
    x fr h1 h2 x₂ fr₂ h1' h2'
  set ζ' : FractionRing V' := 𝔪₂.yK ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ with hζ'
  have hζM : ζ' ^ M = 1 := by
    rw [hζ', ← map_pow]
    have : (⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ : 𝔗.X₂.S.R) ^ M = 1 := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [← map_pow, hM, 𝔗.X₂.S.prim.pow_eq_one, map_one]
    rw [this, map_one]
  have hζ0 : ζ' ≠ 0 := by
    intro h0
    have hMpos : M ≠ 0 := by
      rw [hM]; exact pow_ne_zero _ (Nat.mul_ne_zero (by have := 𝔗.X₂.S.r_pos; omega) (by have := 𝔗.X₂.S.N_ge; omega))
    rw [h0, zero_pow hMpos] at hζM
    exact zero_ne_one hζM
  let ρ : X₁.S.Gam → (FractionRing V')ˣ := fun b => c₀ * (Units.mk0 ζ' hζ0) ^ k b
  have hρ : ∀ b, FrPull wψ f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b) (ρ b) := by
    intro b
    simpa [ρ] using hc₀ b
  obtain ⟨th₂, w₀₂, s₂, g'₂, w₂, K, h3', h4', h5', h6', hcoef, hval⟩ := GlobalTheory.T.exists_theta_witnesses_baseChange_member X₁ act 𝔗 z₁ z₂ hp x₀ hdiv V ev X m t δ 𝔪 C lab
    x fr th w₀ s g' w h1 h2 h3 h4 h5 h6 V' io f hf hinj hfin ev₂ 𝔪₂ ψ hD bc hExt hyK hcart wψ hwψ hφ hmon hU he₈ hgen
    x₂ fr₂ h1' h2' ρ hρ
  refine ⟨x₂, fr₂, th₂, w₀₂, s₂, g'₂, w₂, h1', h2', h3', h4', h5', h6', ?_⟩
  intro mu c
  have hz := _root_.GlobalTheory.Poinc.Sep.MemberZeta.algebraMap_ev_eq_yK 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X m (fun k => io (t k)) δ 𝔪₂ zt hzt
  have hF0 : f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) ≠ 0 :=
    (map_ne_zero_iff f f.injective).2 (UMem.yK_th_ne_zero _ _ F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hdiv)
  have hρc : (ρ (lab c) : FractionRing V') ≠ 0 := (ρ (lab c)).ne_zero
  have e1 := hcoef mu c
  have e2 := hval x₀
  have e3 := h7 mu c
  have eρ : (ρ x₀ : FractionRing V') = ρ (lab c) * ζ' ^ (k x₀ + (M - 1) * k (lab c)) := by
    simp only [ρ, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [_root_.mul_assoc, ← pow_add]
    have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 (by
      rw [hM]; exact pow_ne_zero _ (Nat.mul_ne_zero (by have := 𝔗.X₂.S.r_pos; omega) (by have := 𝔗.X₂.S.N_ge; omega)))
    have hsum : (M - 1) * k (lab c) + k (lab c) = M * k (lab c) := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hM1]
    rw [show k (lab c) + (k x₀ + (M - 1) * k (lab c)) = k x₀ + ((M - 1) * k (lab c) + k (lab c)) by ring, hsum,
      pow_add, pow_mul, hζM, one_pow, _root_.mul_one]
  have e3' : f (coef s (g' c) (w c) (𝔪.e₈ mu)) =
      algebraMap V' (FractionRing V') (io (T mu c)) * f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) := by
    rw [← e3, map_mul, hf]
  show algebraMap V' (FractionRing V') (ev₂ zt ^ (k x₀ + (M - 1) * k (lab c)) * io (T mu c)) *
    𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam x₀), 𝔗.X₂.S.th_mem _⟩ = coef s₂ (g'₂ c) (w₂ c) (𝔪₂.e₈ mu)
  rw [map_mul, map_pow, hz]
  apply mul_right_cancel₀ (mul_ne_zero hρc hF0)
  linear_combination (-(algebraMap V' (FractionRing V') (io (T mu c))) * f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) *
      𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam x₀), 𝔗.X₂.S.th_mem _⟩) * eρ +
    (algebraMap V' (FractionRing V') (io (T mu c)) * f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) * e2 -
    f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) * e1 - K * f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) * e3'

end GlobalTheory.Poinc.Sep.BaseTerms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEighthPowerDataEquivariantStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_eighthPower_data_equivariant : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)), SiegPB c F.univ y → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G), ∃ e : (Fin 8 → Q.X) ≃+ D.toPre.X, SharpRef W Q ρ D.toPre e ∧ ∀ a a' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ aA : P.A ⟶ P.A, (∀ u, aA ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∃ E : EndU U.toUnifPre, E.aA = aA ∧ ∀ mu, E.h (e mu) = e fun u => ∑ v, a' u v • mu v := by
  first | exact @GlobalTheory.Poinc.Sep.unif_pow_equivariant | exact GlobalTheory.Poinc.Sep.unif_pow_equivariant | (intros; apply GlobalTheory.Poinc.Sep.unif_pow_equivariant <;> assumption)
end

