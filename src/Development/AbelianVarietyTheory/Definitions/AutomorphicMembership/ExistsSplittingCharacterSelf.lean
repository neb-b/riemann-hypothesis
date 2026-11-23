module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyBesselPeriodPositionOneData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Th

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def AdmE (V W : HSp D) (χ χ' : IdC D) : Prop :=
  V.rank = W.rank ∧ IsHC D χ ∧ IsHC D χ' ∧ ResEta D χ V.rank ∧ ResEta D χ' W.rank

theorem IsHC.mul {χ ν : IdC D} (h : IsHC D χ) (k : IsHC D ν) : IsHC D (χ * ν) :=
  ⟨⟨h.1.1.mul k.1.1, fun x => by rw [MonoidHom.mul_apply, h.1.2, k.1.2, mul_one]⟩, fun τ =>
    (h.2 τ).elim fun _ ha => (k.2 τ).elim fun _ hb => ⟨_, GlobalTheory.Chain.StepVac.hasInfExp_mul ha hb⟩⟩

structure WeilFun.EqRank {ψ : AddChar (AF D.host.F) ℂ} (Wf : WeilFun D ψ) : Prop where
  weil : ∀ (V W : HSp D) χ χ', AdmE V W χ χ' → IsWeilOn ψ V W χ χ' (Wf.om V W χ χ')
  twW : ∀ (V W : HSp D) χ χ' ν, AdmE V W χ χ' → IsHC D ν → ResEta D ν 0 → ∀ g h x, IsDetRoot V g x →
    Wf.om V W χ (χ' * ν) (g, h) = (((ν x)⁻¹ : Circle) : ℂ) • Wf.om V W χ χ' (g, h)
  twV : ∀ (V W : HSp D) χ χ' ν, AdmE V W χ χ' → IsHC D ν → ResEta D ν 0 → ∀ g h x, IsDetRoot W h x →
    Wf.om V W (χ * ν) χ' (g, h) = ((ν x : Circle) : ℂ) • Wf.om V W χ χ' (g, h)

def WeilOnEqEx (D : D7) : Prop := ∀ ψ, IsStdChar D ψ (-1) → ∀ (V W : HSp D) χ χ', AdmE V W χ χ' → ∃ om, IsWeilOn ψ V W χ χ' om

def WeilTwEq (D : D7) : Prop := ∀ ψ, IsStdChar D ψ (-1) → ∀ (V W : HSp D) χ χ' ν, AdmE V W χ χ' → IsHC D ν → ResEta D ν 0 →
  ∀ om, IsWeilOn ψ V W χ χ' om →
    (∀ om', IsWeilOn ψ V W χ (χ' * ν) om' → ∀ g h x, IsDetRoot V g x → om' (g, h) = (((ν x)⁻¹ : Circle) : ℂ) • om (g, h)) ∧
    ∀ om', IsWeilOn ψ V W (χ * ν) χ' om' → ∀ g h x, IsDetRoot W h x → om' (g, h) = ((ν x : Circle) : ℂ) • om (g, h)


def LiftAutEq (D : D7) : Prop := ∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ (V W : HSp D) χ χ', AdmE V W χ χ' →
  ∀ om, IsWeilOn ψ V W χ χ' om → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ (Φ : ThS ψ V W) F, IsCuspForm θ V F →
    (∀ h, IntegrableOn (fun g => (om (g, h) Φ).1 0 * F g) 𝓕 μ) ∧
    IsAutFunSm θ W fun h => ∫ g in 𝓕, (om (g, h) Φ).1 0 * F g ∂μ

structure RealisesE {θ : InfF D} {X : ThetaX D} {T : ThetaTied D X} {W : WeilTied D X T} (B : BesselTied D X T W)
    (Wf : WeilFun D W.ψ) (Tw : Tow D) (Rc : RecFun D θ W.ψ) : Prop where
  inf : IsInfFam θ

  eqRank : Wf.EqRank := by assumption

  forms : ∀ V, Set.range (T.ev V) = {φ | IsAutFunSm θ V φ}
  typ : ∀ V P F, F ∈ X.typ V P ↔ T.ev V F ∈ TypS θ V P

  sch : ∀ V V', Set.range (W.evS V V') = {f | IsThetaFun W.ψ V V' f}
  chr : ∀ μ j, T.eChr (X.chrOf μ j) = Rc.chr μ j
  eta : T.eChr X.etaT = Rc.eta
  col : ∀ u μ j φ, T.ev _ (X.colAF u μ j φ).1 = (Rc.col u μ j φ).1
  row : ∀ μ j F, T.ev _ (X.rowAF μ j F).1 = (Rc.row μ j F).1
  phi : ∀ μ j, W.evS _ _ (X.PhiY μ j) = (Rc.Phi μ j).1
  phiUp : PhiYupTied W
  mY : X.mY = Rc.mY
  petF : T.petF = Rc.petF
  petR : T.petR = Rc.meas.petR
  xs : X.Xs = Tw.Xs
  ys : X.Ys = Tw.Ys
  ysLow : X.YsLow = Tw.YsLow
  iXYs : ∀ t j, HEq (X.iXYs t j) (Tw.iXYs t j)
  iYXm : ∀ t, HEq (X.iYXm t) (Tw.iYXm t)
  om : ∀ V V' χ χ' p (Φ : X.Sch V V') (f : ThS W.ψ V V'), W.evS V V' Φ = f.1 →
    W.evS V V' (W.om V V' χ χ' p Φ) = (Wf.om V V' (T.eChr χ) (T.eChr χ') p f).1

  thOff : ∀ (V V' : HSp D) χ χ', ¬ ((admitted V V' (T.eChr χ) (T.eChr χ') ∨ AdmE V V' (T.eChr χ) (T.eChr χ')) ∧ V.SigOK) →
    X.th V V' χ χ' = 0

  thEq : ∀ (V V' : HSp D) χ χ', AdmE V V' (T.eChr χ) (T.eChr χ') → V.SigOK → ∀ μ 𝓕, IsVolPair D V μ 𝓕 →
    ∀ (Φ : X.Sch V V') (F : X.cusp V) (h : GA D V'), T.ev V' (X.th V V' χ χ' Φ F) h =
      (T.petC V : ℂ) * ∫ g in 𝓕, W.evS V V' (W.om V V' χ χ' (g, h) Φ) 0 * T.ev V (F : X.AF V) g ∂μ

  fact : ∀ V V' Φ, Φ ∈ X.fact V V' ↔ IsPureFun W.ψ V V' (W.evS V V' Φ)

  kfin : ∃ K : KfinTied W, K.cpt = Rc.dec.cpt ∧ K.bas = Rc.dec.bas

  posDat : ∀ u ho, B.dat _ _ _ ho (X.posSym u) = Rc.posSym u ∧ B.dat _ _ _ ho (X.pos1 u) = Rc.pos1 u

  pos1Val : ∀ u σ μ 𝓕, IsVolPair D (D.sp.X 0) μ 𝓕 → ∀ ν 𝓝, (Rc.per1.dat u).bes.IsUnitPair ν 𝓝 →
    ∀ s : GA D (D.sp.X 0) → GA D (D.sp.Y 0), (∀ h, EmbRel (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (s h) h) →
    ∀ (φ : X.AF (D.sp.X 0)) (F : X.cusp (D.sp.Y 0)), X.Bper _ _ _ (X.pos1 u) σ φ F = (T.petC (D.sp.X 0) : ℂ) *
      (Rc.per1.dat u).period W.ψ μ 𝓕 ν 𝓝 s (fun g => star (T.ev _ φ g)) (T.ev _ (F : X.AF (D.sp.Y 0)))

  besAll : ∀ (A A' : HSp D) (ι : A.V →ₗ[D.host.E] A'.V) ho, A.SigOK → HSpace.IsIsomEmb A A' ι →
    ∀ d : BesDat A A' ι, (d.y : GA D A') = 1 → ∃ p, B.dat A A' ι ho p = d ∧ BesGlob T W.ψ d p

  besOnly : ∀ (A A' : HSp D) (ι : A.V →ₗ[D.host.E] A'.V) ho, A.SigOK → HSpace.IsIsomEmb A A' ι →
    ∀ p, BesGlob T W.ψ (B.dat A A' ι ho p) p ∨ ∃ u,
      (⟨A, A', ι, p⟩ : Σ (A A' : HSp D) (ι : A.V →ₗ[D.host.E] A'.V), X.Pos A A' ι) = ⟨_, _, _, X.pos1 u⟩

def RealisedExE (D : D7) : Prop := ∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) →
  ∀ Wf : WeilFun D ψ, Wf.EqRank → ∀ (Tw : Tow D) (Rc : RecFun D θ ψ),
    ∃ (X : ThetaX D) (T : ThetaTied D X) (W : WeilTied D X T) (B : BesselTied D X T W) (h : W.ψ = ψ),
      RealisesE (θ := θ) B (h ▸ Wf) Tw (h ▸ Rc)

section Lift

variable {θ : InfF D} {X : ThetaX D} {T : ThetaTied D X} {W : WeilTied D X T} {B : BesselTied D X T W}
  {Wf : WeilFun D W.ψ} {Tw : Tow D} {Rc : RecFun D θ W.ψ}


end Lift

structure WeilThetaCompatibility {X : ThetaX D} {T : ThetaTied D X} (W : WeilTied D X T) : Prop where
  range : ∀ V V' : HSp D, V.rank = V'.rank → Set.range (W.evS V V') = {f | IsThetaFun W.ψ V V' f}
  Heisenberg₂ : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ∀ g h w₀ Φ Φ', W.evS V V' Φ' = Heisenberg₂ W.ψ V V' w₀ (W.evS V V' Φ) →
      W.evS V V' (W.om V V' χ χ' (g, h) Φ') =
        Formalism.L2.Theta.Heisenberg₂ W.ψ V V' (actHom V V' g h w₀) (W.evS V V' (W.om V V' χ χ' (g, h) Φ))
  aut : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ∀ γ ∈ GQ V, ∀ γ' ∈ GQ V', ∀ Φ, W.evS V V' (W.om V V' χ χ' (γ, γ') Φ) 0 = W.evS V V' Φ 0
  cont : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ∀ Φ w, Continuous fun p : GA D V × GA D V' => W.evS V V' (W.om V V' χ χ' p Φ) w
  unit : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ∀ (μ : Measure (WA V V')) (𝓕 : Set (WA V V')), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V V') 𝓕 μ →
    ∀ p Φ, ∫ w in 𝓕, ‖W.evS V V' (W.om V V' χ χ' p Φ) w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖W.evS V V' Φ w‖ ^ 2 ∂μ
  split : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ∀ e, IsSplitIdem D e → ∀ g h, SuppAt e V g → SuppAt e V' h → ∀ x y, IsDetAt e V g x → IsDetAt e V' h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : X.Sch V V' →ₗ[ℂ] ℂ,
      (∀ u : WA V V', (∀ i j, cA D e * u i j = u i j) → ∀ Φ Φ',
        W.evS V V' Φ' = Formalism.L2.Theta.Heisenberg₂ W.ψ V V' u (W.evS V V' Φ) → ℓ Φ' = ℓ Φ) →
      ∀ Φ, ℓ (W.om V V' χ χ' (g, h) Φ) = (r : ℂ) * (splitFac V V' (T.eChr χ) (T.eChr χ') x y : ℂ) * ℓ Φ
  twW : ∀ (V V' : HSp D) χ χ' ν, V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ResEta D (T.eChr ν) 0 → ∀ g h x, IsDetRoot V g x →
      W.om V V' χ (χ' * ν) (g, h) = (((T.eChr ν x)⁻¹ : Circle) : ℂ) • W.om V V' χ χ' (g, h)
  twV : ∀ (V V' : HSp D) χ χ' ν, V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
    ResEta D (T.eChr ν) 0 → ∀ g h x, IsDetRoot V' h x →
      W.om V V' (χ * ν) χ' (g, h) = ((T.eChr ν x : Circle) : ℂ) • W.om V V' χ χ' (g, h)
  th : ∀ (V V' : HSp D) χ χ', V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank → V.SigOK →
    ∀ μ 𝓕, IsVolPair D V μ 𝓕 → ∀ (Φ : X.Sch V V') (F : X.cusp V) (h : GA D V'),
      T.ev V' (X.th V V' χ χ' Φ F) h =
        (T.petC V : ℂ) * ∫ g in 𝓕, W.evS V V' (W.om V V' χ χ' (g, h) Φ) 0 * T.ev V (F : X.AF V) g ∂μ

namespace RealisesE

variable {θ : InfF D} {X : ThetaX D} {T : ThetaTied D X} {W : WeilTied D X T} {B : BesselTied D X T W}
  {Wf : WeilFun D W.ψ} {Tw : Tow D} {Rc : RecFun D θ W.ψ} (h : RealisesE B Wf Tw Rc)

include h

theorem eq_of_isInfFam {θ' : InfF D} (h' : IsInfFam θ') : θ' = θ :=
  ((GlobalTheory.AutFunCompare.isInfFam_iff θ').1 h').trans ((GlobalTheory.AutFunCompare.isInfFam_iff θ).1 h.inf).symm

theorem afTiedSm : ThetaSmoothnessCondition T := ⟨⟨θ, h.inf⟩, fun _ h' V _ => by rw [h.eq_of_isInfFam h']; exact h.forms V⟩

theorem formSub : FormSub D := fun θ' h' V φ => by
  rw [h.eq_of_isInfFam h']
  refine ⟨fun hφ => ?_, fun hφ => Submodule.subset_span hφ⟩
  have : AFs θ V ≤ LinearMap.range (T.ev V) := Submodule.span_le.2 (by rw [LinearMap.coe_range, h.forms V])
  have h2 : φ ∈ Set.range (T.ev V) := this hφ
  rwa [h.forms V] at h2

theorem typTied (ht : TypAdd D) : TypTied T := ⟨⟨θ, h.inf⟩, fun _ h' V hV P hP => by
  intros
  rename_i F
  rw [h.eq_of_isInfFam h', h.typ, mem_TypS h.formSub ht h.inf hV hP]
  have : T.ev V F ∈ Set.range (T.ev V) := ⟨F, rfl⟩
  rw [h.forms V] at this
  exact ⟨fun k => k.2, fun k => ⟨this, k⟩⟩⟩

theorem weilUnrTied : WeilUnramifiedCondition W := fun V V' χ χ' hr h1 h2 S u1 u2 k hk k' hk' Φ hΦ => by
  have hc : ∀ χ, IsHC D (T.eChr χ) := fun χ => by
    have : T.eChr χ ∈ Set.range T.eChr := ⟨χ, rfl⟩
    rwa [T.eChr_range] at this
  have hf : W.evS V V' Φ ∈ Set.range (W.evS V V') := ⟨Φ, rfl⟩
  rw [h.sch] at hf
  refine W.evS_inj V V' ?_
  rw [h.om V V' χ χ' (k, k') Φ ⟨_, mem_ThS.2 hf⟩ rfl,
    Wf.om_unr V V' _ _ ⟨hr, hc χ, hc χ', h1, h2⟩ S u1 u2 k hk k' hk' _ hΦ]

def schEquiv (V V' : HSp D) : X.Sch V V' ≃ₗ[ℂ] ThS W.ψ V V' :=
  LinearEquiv.ofBijective ((W.evS V V').codRestrict _ fun Φ => mem_ThS.2 (by
      have hf : W.evS V V' Φ ∈ Set.range (W.evS V V') := ⟨Φ, rfl⟩
      rwa [h.sch] at hf))
    ⟨fun _ _ e => W.evS_inj V V' (congrArg Subtype.val e), fun f => by
      have hf : f.1 ∈ Set.range (W.evS V V') := by rw [h.sch]; exact mem_ThS.1 f.2
      exact hf.imp fun _ e => Subtype.ext e⟩

theorem schEquiv_om (V V' : HSp D) (χ χ') (p) (Φ : X.Sch V V') :
    h.schEquiv V V' (W.om V V' χ χ' p Φ) = Wf.om V V' (T.eChr χ) (T.eChr χ') p (h.schEquiv V V' Φ) :=
  Subtype.ext (h.om V V' χ χ' p Φ _ rfl)

theorem eqTied : WeilThetaCompatibility W := by
  have hc : ∀ χ, IsHC D (T.eChr χ) := fun χ => by
    have : T.eChr χ ∈ Set.range T.eChr := ⟨χ, rfl⟩
    rwa [T.eChr_range] at this
  have ha : ∀ {V V' : HSp D} {χ χ'}, V.rank = V'.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') V'.rank →
      AdmE V V' (T.eChr χ) (T.eChr χ') := fun hr h1 h2 => ⟨hr, hc _, hc _, h1, h2⟩
  have ho := fun V V' χ χ' p Φ => h.om V V' χ χ' p Φ (h.schEquiv V V' Φ) rfl
  refine ⟨fun V V' _ => h.sch V V', fun V V' χ χ' hr h1 h2 g x w₀ Φ Φ' e => ?_, fun V V' χ χ' hr h1 h2 γ hγ γ' hγ' Φ => ?_,
    fun V V' χ χ' hr h1 h2 Φ w => ?_, fun V V' χ χ' hr h1 h2 μ 𝓕 hμ h𝓕 p Φ => ?_,
    fun V V' χ χ' hr h1 h2 e he g x hg hx a b k1 k2 => ?_, fun V V' χ χ' ν hr h1 h2 h3 g x a k => ?_,
    fun V V' χ χ' ν hr h1 h2 h3 g x a k => ?_, fun V V' χ χ' hr h1 h2 => h.thEq V V' χ χ' (ha hr h1 h2)⟩
  · rw [ho, ho]; exact (h.eqRank.weil _ _ _ _ (ha hr h1 h2)).Heisenberg₂ g x w₀ _ _ e
  · rw [ho]; exact (h.eqRank.weil _ _ _ _ (ha hr h1 h2)).aut γ hγ γ' hγ' _
  · simp only [ho]; exact (h.eqRank.weil _ _ _ _ (ha hr h1 h2)).cont _ w
  · rw [ho]; exact (h.eqRank.weil _ _ _ _ (ha hr h1 h2)).unit μ 𝓕 hμ h𝓕 p _
  · obtain ⟨r, hr0, k⟩ := (h.eqRank.weil _ _ _ _ (ha hr h1 h2)).split e he g x hg hx a b k1 k2
    refine ⟨r, hr0, fun ℓ hℓ Φ => ?_⟩
    have := k (ℓ ∘ₗ (h.schEquiv V V').symm.toLinearMap) (fun u hu f f' e' => by
      obtain ⟨Ψ, rfl⟩ := (h.schEquiv V V').surjective f
      obtain ⟨Ψ', rfl⟩ := (h.schEquiv V V').surjective f'
      simpa using hℓ u hu Ψ Ψ' e') (h.schEquiv V V' Φ)
    rw [← h.schEquiv_om] at this
    simpa using this
  · refine LinearMap.ext fun Φ => (h.schEquiv V V').injective ?_
    rw [LinearMap.smul_apply, map_smul, h.schEquiv_om, h.schEquiv_om, map_mul,
      h.eqRank.twW _ _ _ _ _ (ha hr h1 h2) (hc ν) h3 g x a k, LinearMap.smul_apply]
  · refine LinearMap.ext fun Φ => (h.schEquiv V V').injective ?_
    rw [LinearMap.smul_apply, map_smul, h.schEquiv_om, h.schEquiv_om, map_mul,
      h.eqRank.twV _ _ _ _ _ (ha hr h1 h2) (hc ν) h3 g x a k, LinearMap.smul_apply]

theorem petC_eq (V : HSp D) : T.petC V = Rc.petC V := by
  unfold ThetaTied.petC RecFun.petC; rw [h.petF, h.petR]

theorem carY_eq (μ s i) : T.eChr (X.carY μ s i) = Rc.carY μ s i := by
  unfold ThetaX.carY RecFun.carY
  split_ifs
  · rw [map_mul, map_inv, h.chr, h.eta]
  · exact h.chr _ _

theorem tieIo (hi : Rc.IoTie Wf) : X.TieIo := fun μ j hj y x => by
  obtain ⟨L, hL, hx⟩ := hi μ j hj y
  obtain ⟨⟨m, hm⟩, h2⟩ := hx x
  have e : T.ev _ (X.dnY μ j (X.rowAF μ (j + 1) y)) = L := by
    funext g
    obtain ⟨⟨n, hn⟩, h3⟩ := hL g
    have k := W.th _ _ _ _ (rank_Y_ne X j hj) (row_lift_ok T μ (j + 1) (by omega) hj (j + 1) hj)
      (row_lift_ok T μ (j + 1) (by omega) hj j hj.le) (D.sp.Y_sig _) n.1 n.2 hn (X.PhiY μ j) (X.rowAF μ (j + 1) y) g
    unfold ThetaX.dnY
    rw [LinearMap.smul_apply, map_smul, Pi.smul_apply, k, (h3 n hn).2]
    simp only [h.om _ _ _ _ _ _ _ (h.phi μ j), h.carY_eq, h.row, h.mY, ← h.petC_eq, WeilFun.ker, Complex.ofReal_mul,
      mul_assoc, smul_eq_mul]
  unfold ThetaX.petY
  rw [T.pet _ (D.sp.Y_sig j) m.1 m.2 hm, (h2 m hm).2, e, h.row, h.mY, ← h.petC_eq]
  simp only [ThetaTied.petC, Complex.ofReal_mul, mul_assoc]

end RealisesE

structure ChrRead {X : ThetaX D} (T : ThetaTied D X) (C : Formalism.L2.Host.CharFrame D)
    (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) : Prop where
  chr : ∀ μ (j : Fin D.R.m), Formalism.IndefR.Links.ChrEq (T.eChr (X.chrOf μ (j.1 + 1))) (C.mu0 j * xi μ)
  eta : Formalism.IndefR.Links.ChrEq (T.eChr X.etaT) C.eta

structure RecFun.ChrIs {θ : InfF D} {ψ : AddChar (AF D.host.F) ℂ} (Rc : RecFun D θ ψ) (C : Formalism.L2.Host.CharFrame D)
    (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) : Prop where
  chr : ∀ μ (j : Fin D.R.m), Formalism.IndefR.Links.ChrEq (Rc.chr μ (j.1 + 1)) (C.mu0 j * xi μ)
  eta : Formalism.IndefR.Links.ChrEq Rc.eta C.eta


open Formalism.IndefR.Links in
theorem RecFun.exists_chrIs (C : Formalism.L2.Host.CharFrame D) (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E)
    (hf : ∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n) (ht : ∀ μ, (xi μ).TrivOn D.host.F) (θ : InfF D)
    (ψ : AddChar (AF D.host.F) ℂ) : ∃ Rc : RecFun D θ ψ, Rc.ChrIs C xi := by
  choose n hn ho using hf
  choose m hm using fun j => GlobalTheory.CharTransport.exists_chrEq D (C.mu0 j) (C.isMu0 j).unitary
  choose x hx using fun μ => GlobalTheory.CharTransport.exists_chrEq D (xi μ) (Formalism.L2.Host.HChar.isUnitary_of_order (hn μ) (ho μ))
  obtain ⟨η, hη⟩ := GlobalTheory.CharTransport.exists_chrEq D C.eta C.isEta.unitary
  obtain ⟨θ₀, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D η C.eta hη C.isEta
  obtain ⟨P⟩ := GlobalTheory.PosOneData.nonempty_besselPeriodPositionOneData D
  obtain ⟨Dc⟩ := GlobalTheory.Mem.ThModel.nonempty_orthDec D
  obtain ⟨R⟩ := nonempty_recFun θ ψ (GlobalTheory.Mem.AntiChar.exists_char D) (GlobalTheory.Mem.EtaTilde.exists_etaTilde D)
    (GlobalTheory.Mem.ThetaNonzero.exists_thetaFun_ne_zero D ψ) Dc P
  have h2 := D.R.two_le_m
  have hexp : ∀ μ (j : Fin D.R.m) τ, HasInfExp D (m j * x μ) τ (-(D.hc τ).e j) := fun μ j τ => by
    have := GlobalTheory.Chain.StepVac.hasInfExp_mul (GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hm j)
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (C.isMu0 j).inf) τ)
      (GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hx μ) (hn μ) (ho μ) τ)
    rwa [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this
  have heq : ∀ μ j, ChrEq (m j * x μ) (C.mu0 j * xi μ) := fun μ j =>
    ⟨⟨(hm j).1.1.mul (hx μ).1.1, fun y => by rw [MonoidHom.mul_apply, (hm j).1.2, (hx μ).1.2, mul_one]⟩,
      fun P e he k y hy => by
        rw [MonoidHom.mul_apply, Circle.coe_mul, (hm j).2 P e he k y hy, (hx μ).2 P e he k y hy, ← Units.val_mul]; rfl⟩
  have e : ∀ j : Fin D.R.m, (⟨(j.1 + 1 - 1) % D.R.m, Nat.mod_lt _ (by omega)⟩ : Fin D.R.m) = j := fun j =>
    Fin.ext (by simp [Nat.mod_eq_of_lt j.2])
  refine ⟨{ R with
    chr := fun μ j => m ⟨(j - 1) % D.R.m, Nat.mod_lt _ (by omega)⟩ * x μ
    chr_hc := fun μ _ => ⟨(heq μ _).1, fun τ => ⟨_, hexp μ _ τ⟩⟩
    chr_inf := fun μ j τ => by rw [e]; exact hexp μ j τ
    chr_res := fun μ _ _ _ => ⟨⟨_, hres⟩, fun η' _ a => by
      rw [pow_zero, MonoidHom.mul_apply, GlobalTheory.GridWeil.triv_base (hm _) (C.isMu0 _).triv a,
        GlobalTheory.GridWeil.triv_base (hx μ) (ht μ) a, mul_one]⟩
    eta := η, eta_hc := hη.1
    eta_inf := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hη
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, C.isEta.inf⟩)
    eta_res := ⟨⟨_, hres⟩, fun η' hη' a => by
      rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique hη' hres, pow_one, MonoidHom.comp_apply]⟩
    eta_unr := GlobalTheory.EtaConjExist.unram_of_chrEq hη C.isEta.unr }, fun μ j => ?_, hη⟩
  show ChrEq (m _ * x μ) _
  rw [e]; exact heq μ j

theorem RealisesE.chrRead {θ : InfF D} {X : ThetaX D} {T : ThetaTied D X} {W : WeilTied D X T} {B : BesselTied D X T W}
    {Wf : WeilFun D W.ψ} {Tw : Tow D} {Rc : RecFun D θ W.ψ} (h : RealisesE B Wf Tw Rc) {C : Formalism.L2.Host.CharFrame D}
    {xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E} (k : Rc.ChrIs C xi) : ChrRead T C xi :=
  ⟨fun μ j => by rw [h.chr]; exact k.chr μ j, by rw [h.eta]; exact k.eta⟩

end GlobalTheory.Mem.Th

end
