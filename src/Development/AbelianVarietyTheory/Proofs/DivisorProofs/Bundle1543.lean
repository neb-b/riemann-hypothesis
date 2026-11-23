module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftDarbouxAdelicSymplectic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0258
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0992
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0993
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0997
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
section
noncomputable section

namespace GlobalTheory.RatWeilOp

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def act {R κ : Type} [CommRing R] [Fintype κ] (a : Matrix (κ ⊕ κ) (κ ⊕ κ) R) (w : (κ → R) × (κ → R)) : (κ → R) × (κ → R) :=
  ((a *ᵥ Sum.elim w.1 w.2) ∘ Sum.inl, (a *ᵥ Sum.elim w.1 w.2) ∘ Sum.inr)

theorem act_mul {R κ : Type} [CommRing R] [Fintype κ] (a b : Matrix (κ ⊕ κ) (κ ⊕ κ) R) (w : (κ → R) × (κ → R)) :
    act (a * b) w = act a (act b w) := by
  simp only [act, Matrix.mulVec_mulVec, Sum.elim_comp_inl_inr]

theorem act_fromBlocks {R κ : Type} [CommRing R] [Fintype κ] (A B C D : Matrix κ κ R) (w : (κ → R) × (κ → R)) :
    act (Matrix.fromBlocks A B C D) w = (A *ᵥ w.1 + B *ᵥ w.2, C *ᵥ w.1 + D *ᵥ w.2) := by
  simp only [act, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]

variable {F : Type} [Field F] [NumberField F]

def ind (κ : Type) (v : Pl F) : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

def IsFam {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : Prop :=
  (∀ v, φ v ∈ SB (κ → Fv F v)) ∧ ∀ᶠ v in cofinite, φ v = ind κ v

def IsOp {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (a : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (c : ℂ) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ) : Prop :=
  c ≠ 0 ∧ Function.Surjective ei ∧
  (∀ v, Set.BijOn (ev v) (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _)) ∧
  (∀ v (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v), ev v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) =
    schr (GlobalTheory.LatVac.psiAt ψ v) (act (a.map (algebraMap F (Fv F v))) w) (ev v φ)) ∧
  (∀ᶠ v in cofinite, ev v (ind κ v) = ind κ v) ∧
  ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), IsFam φ →
    e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) (fun v => ev v (φ v)) ∧
    (∀ w : (κ → AF F) × (κ → AF F), e (schr ψ w (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) =
      schr ψ (act (a.map (algebraMap F (AF F))) w) (e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))) ∧
    thetaSum F (e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) = c * thetaSum F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)

def HasOp {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (a : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ e c ei ev, IsOp ψ a e c ei ev

theorem IsOp.isFam {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} {a : Matrix (κ ⊕ κ) (κ ⊕ κ) F} {e c ei ev}
    (h : IsOp ψ a e c ei ev) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) : IsFam fun v => ev v (φ v) := by
  obtain ⟨-, -, hbij, -, hind, -⟩ := h
  refine ⟨fun v => (hbij v).mapsTo (hφ.1 v), ?_⟩
  filter_upwards [hφ.2, hind] with v h1 h2
  rw [h1, h2]

theorem HasOp.mul {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} {a b : Matrix (κ ⊕ κ) (κ ⊕ κ) F}
    (ha : HasOp ψ a) (hb : HasOp ψ b) : HasOp ψ (a * b) := by
  obtain ⟨e₁, c₁, ei₁, ev₁, h₁⟩ := ha
  obtain ⟨e₂, c₂, ei₂, ev₂, h₂⟩ := hb
  have h₂' := h₂
  obtain ⟨hc₁, hs₁, hb₁, hw₁, hi₁, hp₁⟩ := h₁
  obtain ⟨hc₂, hs₂, hb₂, hw₂, hi₂, hp₂⟩ := h₂
  refine ⟨e₁ ∘ₗ e₂, c₁ * c₂, ei₁.comp ei₂, fun v => ev₁ v ∘ₗ ev₂ v, mul_ne_zero hc₁ hc₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs₁.comp hs₂
  · intro v
    exact (hb₁ v).comp (hb₂ v)
  · intro v w φ hφ
    simp only [LinearMap.comp_apply]
    rw [hw₂ v w φ hφ, hw₁ v _ _ ((hb₂ v).mapsTo hφ), Matrix.map_mul, act_mul]
  · filter_upwards [hi₁, hi₂] with v h1 h2
    simp only [LinearMap.comp_apply, h2, h1]
  · intro f φ hφ
    have hφ' : IsFam fun v => ev₂ v (φ v) := IsOp.isFam h₂' hφ
    obtain ⟨hq₂, hw₂', ht₂⟩ := hp₂ f φ hφ
    obtain ⟨hq₁, hw₁', ht₁⟩ := hp₁ (ei₂ f) (fun v => ev₂ v (φ v)) hφ'
    refine ⟨?_, ?_, ?_⟩
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply, hq₂, hq₁]
    · intro w
      simp only [LinearMap.comp_apply]
      rw [hw₂' w, hq₂, hw₁' _, Matrix.map_mul, act_mul]
    · simp only [LinearMap.comp_apply]
      rw [hq₂, ht₁, ← hq₂, ht₂, mul_assoc]

end GlobalTheory.RatWeilOp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAtStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchrodinger_tensor_eq_local_of_supportedAt : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.1 i)) →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.2 i)) → ∀ (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ),
    (∀ x z : κ → AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z → r (x + z) = r x) →
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) φ r) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v)
        (GlobalTheory.WeilM.schr (GlobalTheory.VacAny.psiV ψ v) (fun i => GlobalTheory.AdelicU.evFin F v (w.1 i), fun i => GlobalTheory.AdelicU.evFin F v (w.2 i)) φ) r := by
  first | exact @GlobalTheory.SchrLoc.schr_tens_of_at | exact GlobalTheory.SchrLoc.schr_tens_of_at | (intros; apply GlobalTheory.SchrLoc.schr_tens_of_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AestronglyMeasurableKernelRouteBigVertex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.BigRoute

theorem theta_of_matched_big : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)} (_ : IsMatched B t ρ i j Θ Θ')
    {d : PureT G (routeBig t i j)} (_ : d ∈ Θ.support),
    IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) d.2 := by
  intro D T L sc G W B ρ t i j Θ Θ' hΘ d hd
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, -, ⟨φ₁, φ₂, hloc, -⟩⟩, rfl, -⟩ := hΘ
  obtain ⟨d₀, hd₀, P, rfl⟩ := GlobalTheory.SmallRoute.mem_support_tensT W hd
  obtain ⟨h1, h2⟩ := hloc d₀ hd₀
  have v1 := ρ.vX_is i (j + 1) i.2 j.2
  have v2 := ρ.vT_is t (i + 1) j i.2 j.2
  have t1 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h1.2 v1.2.theta
  have t2 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h2.2 v2.2.theta
  exact ⟨GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _,
    GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _⟩

theorem continuous_kerBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (_ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    Continuous (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
      kerBig W Θ p.1 g₁ p.2) := by
  intro D T L sc G W B ρ t i j Θ Θ' hΘ g₁
  have hc := W.om_is (.chi (i : ℕ) (j + 1)) ⟨i.2, j.2⟩
  have hm := W.om_is (.mu t ((i : ℕ) + 1) j) ⟨i.2, j.2⟩
  have hK : ∀ d ∈ Θ.support, Continuous (fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
      W.kerA (.right i (j + 1)) d.1.2 q.1 q.2 * W.kerA (.down t (i + 1) j) d.2 q.2 g₁) := by
    intro d hd
    obtain ⟨h1, h2⟩ := theta_of_matched_big hΘ hd
    refine Continuous.mul ?_ ?_
    · show Continuous fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
        thetaKO (W.om (.chi (i : ℕ) (j + 1))) (negGA _ q.2) q.1 d.1.2
      exact (hc.om_cont _ h1 0).comp (((continuous_negGA _).comp continuous_snd).prodMk continuous_fst)
    · show Continuous fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
        thetaKO (W.om (.mu t ((i : ℕ) + 1) j)) g₁ q.2 d.2
      exact (hm.om_cont _ h2 0).comp (continuous_const.prodMk continuous_snd)
  unfold kerBig
  simp only [Finsupp.sum]
  exact continuous_finsetSum _ fun d hd => continuous_const.mul (hK d hd)

theorem aestronglyMeasurable_kerBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) => kerBig W Θ p.1 g₁ p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁
  exact (continuous_kerBig W B ρ t i j Θ Θ' hΘ g₁).aestronglyMeasurable

end GlobalTheory.BigRoute
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedAtLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_div_beta_ramified_at_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.E)), P ∈ L.Q t →
      P.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  first | exact @GlobalTheory.TwistRam.not_unrAt_alpha_div_beta | exact GlobalTheory.TwistRam.not_unrAt_alpha_div_beta | (intros; apply GlobalTheory.TwistRam.not_unrAt_alpha_div_beta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedFirstStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_div_beta_ramified_first : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∈ S1 D →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  first | exact @GlobalTheory.FunObj.SqNum.not_unrAt_alpha_div_beta_over_S₁ | exact GlobalTheory.FunObj.SqNum.not_unrAt_alpha_div_beta_over_S₁ | (intros; apply GlobalTheory.FunObj.SqNum.not_unrAt_alpha_div_beta_over_S₁ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaUnramifiedOutsideStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_unramified_outside : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      (∀ P ∈ L.Q t, P.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) → GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j) w := by
  first | exact @GlobalTheory.FunObj.alpha_unrAt | exact GlobalTheory.FunObj.alpha_unrAt | (intros; apply GlobalTheory.FunObj.alpha_unrAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzGenuineUnitaryRepSignatures
section
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD GlobalTheory.RealWeil GlobalTheory.ArchUniq GlobalTheory.ArchRep

namespace GlobalTheory.ArchRepD

theorem archRepD :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    ∃ (ρ : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f f₁ : SInf F κ,
          (∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h) →
            ∀ h : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F (ρ g f) h) = pureA F (ρ g f₁) h) ∧
        ∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
          ∫ x, star (ρ g f₁ x) * ρ g f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) ∧
      (∀ (L : SInf F κ →L[ℂ] ℂ) (f : SInf F κ),
        ContinuousOn (fun g => L (ρ g f)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ∀ γ ∈ RLines (σ := σ) JB, ∀ Y, IsGenD τ C γ Y → ∀ (T : TensD F P Q R S) (L : SInf F κ →L[ℂ] ℂ),
        HasDerivAt (fun t : ℝ => L (ρ (γ (Multiplicative.ofAdd t)) (Φ T)))
          (L (Φ (sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) + (c₀ w * (Y w).trace) • 1) T))) 0 := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨n, θ, φ, φ₀, hp, hq, hφ, hφu⟩ := GlobalTheory.T.exists_archimedean_phaseSpace_coordinates_placeSignatures F E σ α β κ P Q R S τ JA JB d a b A C hCM hFr
  obtain ⟨k, hkc, hkC, hkJ, hcan⟩ := GlobalTheory.T.exists_continuous_hom_unitary_realPlaces_placewise_signature F E σ β R S τ JB b C hCM hFr.2.2
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨ω, hωc, hωi⟩ := _root_.GlobalTheory.HoweD.exists_osc _ _ P Q R S φ hφ (_root_.GlobalTheory.RealWeil.continuous_rho _) (UG (cA σ) JB) k hkc hkJ
  obtain ⟨s, hsc, hsφ⟩ := _root_.GlobalTheory.ColActionD.exists_symplectic_hom_of_unitary_dep _ _ P Q R S φ hφ (UG (cA σ) JB) k hkc hkJ
  obtain ⟨ρ, η, hη1, hη2, hη3, hρi, hρu, hρc, hρd⟩ :=
    realRep GlobalTheory.Published.realMetaplecticRepresentation_holds s hsc ω hωc fun g w v => by
      obtain ⟨c, rfl⟩ := φ.surjective w
      rw [hsφ, hωi]
  obtain ⟨kk, hkk⟩ := GlobalTheory.T.deriv_continuous_character_real_unitary_one_parameter F E σ β R S τ JB b C hCM hFr.2.2 η (fun g h _ _ => hη1 g h) hη2.continuousOn
    fun g _ => hη3 g
  let toE : SInf F κ →L[ℂ] Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) θ.symm
  let toV : Sch (Fin n) →L[ℂ] SInf F κ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) θ
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑θ.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑θ := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  have hEV : ∀ h, toE (toV h) = h := fun h => by ext x; simp [htoE, htoV]
  clear_value toE toV
  have hS := SchrTransport.schr_coords (trP F κ) θ φ₀ hp hq
  let ρ' : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ) :=
    { toFun := fun g => toV ∘L ρ g ∘L toE
      map_one' := ContinuousLinearMap.ext fun f => by
        rw [map_one]
        exact hVE f
      map_mul' := fun g h => ContinuousLinearMap.ext fun f => by
        simp only [map_mul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, hEV] }
  have hρ' : ∀ g f, ρ' g f = toV (ρ g (toE f)) := fun _ _ => rfl
  clear_value ρ'
  refine ⟨ρ', fun w => kk w / 2, fun g _ => ⟨fun u hu f f₁ hf h => ?_, fun ν hν f₁ f₂ => ?_⟩, fun L f => ?_,
    fun γ hγ Y hY T L => ?_⟩
  · choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    obtain ⟨c, hc⟩ : ∃ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
        ∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ :=
      ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, fun w => by
        have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
        simp only [Matrix.mul_assoc]
        rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    have hu' : At (evI F) (actB (cA σ) g u) := fun t ht => by
      rw [actB, ← Matrix.smul_mul, hu t ht, Matrix.zero_mul]
    have hc' : ∀ w, (actB (cA σ) g u).map (piInf (τ w)) = A w * (c w * (k g w)ᵀ) * (C w)ᵀ := fun w => by
      rw [actB, Matrix.map_mul, hc, Matrix.transpose_map, Matrix.mul_assoc, ← Matrix.transpose_mul, hkC,
        Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    have e1 : ⇑f₁ = schrF (trP F κ) (locV (d.e u).1, locV (d.e u).2) ⇑f := by
      funext y
      have := congrFun ((GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace F E σ α β κ ψ JA JB d hψ u hu f fun _ => 1).symm.trans (hf fun _ => 1)) (liftV y)
      simp only [pureA, liftV, Prod.fst, RingEquiv.apply_symm_apply, mul_one] at this
      exact this.symm
    have e2 : ⇑(toE f₁) = rhoFun (φ c) ⇑(toE f) := by
      have := hS (locV (d.e u).1, locV (d.e u).2) ⇑(toE f)
      rw [← htoV, hVE, ← e1, ← hφu u c hu hc] at this
      rw [htoE, this]
      funext x
      simp
    have e3 := hρi g _ _ _ e2
    rw [hsφ, hφu _ _ hu' hc'] at e3
    rw [GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace F E σ α β κ ψ JA JB d hψ _ hu', hρ', hρ', htoV, htoV, hS, e3]
  · haveI : BorelSpace ({w : InfinitePlace F // w.IsReal} → ℝ) := Pi.borelSpace
    haveI : BorelSpace ({w : InfinitePlace F // w.IsComplex} → ℂ) := Pi.borelSpace
    haveI : BorelSpace (mixedEmbedding.mixedSpace F) := Prod.borelSpace
    haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := Pi.borelSpace
    obtain ⟨r, hr⟩ := haar_coords ν θ
    rw [hr, hr]
    congr 1
    simp only [hρ', htoV, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    rw [hρu]
    simp only [htoE, Function.comp_apply]
  · simp only [hρ']
    exact (hρc (L ∘L toV) (toE f)).continuousOn
  · have hkY : ∀ (t : ℝ) w, k (γ (Multiplicative.ofAdd t)) w = NormedSpace.exp (t • Y w) := fun t w =>
      hcan w _ _ ((hkC _ w).symm.trans (hY t w))
    have hYu : ∀ w, Y w ∈ upq (R w) (S w) := fun w => GlobalTheory.RealLiftGen.mem_upq_of (Y w) fun t => by
      have := congrArg (fun X => X.map star) (hkJ (γ (Multiplicative.ofAdd t)) w)
      simp only [GlobalTheory.RealLiftGen.map_star_mul, GlobalTheory.RealLiftGen.Jm_map_star, hkY] at this
      refine Eq.trans ?_ this
      congr 2
      ext i j
      simp
    obtain ⟨Z, hZ, hZφ, hZe⟩ := _root_.GlobalTheory.HoweD.SpLieD.exists_sp_rightActD _ _ P Q R S φ hφ Y hYu
    have hsZ : ∀ t : ℝ, (s (γ (Multiplicative.ofAdd t)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) =
        NormedSpace.exp (t • Z) := fun t => Matrix.toLin'.injective (LinearMap.ext fun v => by
      obtain ⟨c, rfl⟩ := φ.surjective v
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
      calc
        _ = φ (fun w => c w * (k (γ (Multiplicative.ofAdd t)) w)ᵀ) := hsφ _ _
        _ = _ := by simp only [hkY, ← hZe])
    have hd := hρd (fun t => γ (Multiplicative.ofAdd t)) (hγ.1.comp continuous_ofAdd) (by change γ 1 = 1; exact map_one γ) Z hZ hsZ _
      (hkk γ hγ Y hY) (L ∘L toV) (toE (Φ T))
    obtain ⟨D, hD⟩ := _root_.GlobalTheory.HeisDer.derEx F E σ α β κ ψ JA JB d hψ
    have hΨ : ∀ c T, (toE.toLinearMap ∘ₗ Φ) (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) ((toE.toLinearMap ∘ₗ Φ) T) := by
      intro c T
      obtain ⟨u, ⟨hu, hc⟩, -⟩ := GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM fun w => A w * c w * (C w)ᵀ
      have e1 := (GlobalTheory.RealLift.actsLaws F κ (Φ T) _ _).2.2.2.2 _ (hΦ.2 u hu c hc T) (hD u hu (Φ T)).1
      ext x
      obtain ⟨y, rfl⟩ := θ.surjective x
      have e2 := SchrTransport.dRho_coords (trP F κ) θ φ₀ hp hq (locV (d.e u).1, locV (d.e u).2) (Φ T) (toE (Φ T))
        (by rw [← htoV, hVE]) y
      rw [← hφu u c hu hc] at e2
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [← e2, e1, htoE, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
      exact (hD u hu (Φ T)).2 y
    have e3 := _root_.GlobalTheory.HoweD.quad_fockD _ _ P Q R S φ hφ _ hΨ Y hYu Z hZφ T
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at e3
    have hf : (fun t : ℝ => L (ρ' (γ (Multiplicative.ofAdd t)) (Φ T))) =
        (fun t : ℝ => L (toV (ρ (γ (Multiplicative.ofAdd t)) (toE (Φ T))))) := by
      funext t
      exact congrArg L (hρ' (γ (Multiplicative.ofAdd t)) (Φ T))
    rw [hf]
    refine hd.congr_deriv ?_
    rw [e3, sumPl_add_smul]
    simp only [ContinuousLinearMap.comp_apply, hVE, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_add, map_smul, smul_eq_mul, Finset.sum_div]
    congr 2
    exact Finset.sum_congr rfl fun w _ => by ring

end GlobalTheory.ArchRepD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelBoundOfQuotedTheoremsStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmeticHilbertSamuelBound : Quoted → GeoBound := by
  first | exact @GlobalTheory.HSShort.geoBound_of_quoted' | exact GlobalTheory.HSShort.geoBound_of_quoted' | (intros; apply GlobalTheory.HSShort.geoBound_of_quoted' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaUnramifiedOutsideStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.beta_unramified_outside : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (beta G i j) w := by
  first | exact @GlobalTheory.FunObj.beta_unrAt_off | exact GlobalTheory.FunObj.beta_unrAt_off | (intros; apply GlobalTheory.FunObj.beta_unrAt_off <;> assumption)
end

