module

public import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.IsProbabilityMeasureAutQuotientNormalized
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.BetaAddRight
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def N3AtPoints (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C), Nonempty (DatAt Y P)

def BetaAdd (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C) (A : DatAt Y P) (a a' b : A.Ylat),
    A.beta (a + a') b = A.beta a b + A.beta a' b

def BetaBal (Y : Model Xo c β) (p : ℕ) (cj : E → E) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C) (A : DatAt Y P) (x x' : 𝓞 E), (x' : E) = cj (x : E) →
    ∀ a b : A.Ylat, A.beta (x • a) b = A.beta a (x' • b)

def BetaPosDef (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C) (A : DatAt Y P),
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ A.Ylat),
      ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * A.beta (b i) (b k)

namespace DatAt

variable {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

theorem beta_add_right (hA : BetaAdd Y p) (A : DatAt Y P) (a b b' : A.Ylat) :
    A.beta a (b + b') = A.beta a b + A.beta a b' := by
  rw [A.beta_symm, hA C P A, A.beta_symm b, A.beta_symm b']

def beLin (hA : BetaAdd Y p) (A : DatAt Y P) : A.Ylat →ₗ[ℤ] A.Ylat →ₗ[ℤ] ℝ :=
  (AddMonoidHom.mk' (fun a => (AddMonoidHom.mk' (fun b => A.beta a b)
      (fun b b' => A.beta_add_right hA a b b')).toIntLinearMap)
    (fun a a' => by
      ext b
      simp [hA C P A a a' b])).toIntLinearMap

theorem beLin_apply (hA : BetaAdd Y p) (A : DatAt Y P) (a b : A.Ylat) : A.beLin hA a b = A.beta a b := rfl

end DatAt

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.EquivariantFiniteGroup
section
noncomputable section

open scoped TensorProduct
open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.Pj

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

abbrev FDSec (X : Comp → Data E r) : Type := ∀ c, Frame (X c).Ψ r → ℂ

abbrev FPt (X : Comp → Data E r) : Type := Σ c, ((X c).dom : Set (Frame (X c).Ψ r))

def IsHolCusp (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : Prop :=
  ∀ c, P c ∈ (X c).SS (la c)

def supE (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : ENNReal :=
  ⨆ p : FPt X, ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)

def supN (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : ℝ := (supE X la P).toReal

theorem pnorm_fac_nonneg (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) :
    0 ≤ ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _

theorem pnorm_add_le (X : Data E r) (la : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (P + Q) x ≤ X.pnorm la P x + X.pnorm la Q x := by
  simp only [Data.pnorm, Pi.add_apply]
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (pnorm_fac_nonneg X la x)

theorem pnorm_smul (X : Data E r) (la : Wt X.Ψ r) (a : ℂ) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (a • P) x = ‖a‖ * X.pnorm la P x := by
  simp only [Data.pnorm, Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

theorem pnorm_zero (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) : X.pnorm la 0 x = 0 := by
  simp [Data.pnorm]

def holSub (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) : Submodule ℂ (FDSec X) :=
  Submodule.span ℂ {P | IsHolCusp X la P}

theorem holCusp_mem_holSub (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) {P : FDSec X}
    (h : IsHolCusp X la P) : P ∈ holSub X la := Submodule.subset_span h

def dmet (n f r : ℕ) : ℝ := Real.exp ((n : ℝ) * f * r * (-(1 / 2) * Real.log (2 * Real.pi)) / 2)

theorem supN_nonneg (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : 0 ≤ supN X la P := ENNReal.toReal_nonneg

variable (V : HSp D)

def adel {X : Comp → Data E r} (dict : GA D V → Σ c, Frame (X c).Ψ r) (mu : GA D V → ℂ) :
    FDSec X →ₗ[ℂ] (GA D V → ℂ) where
  toFun P := fun g => mu g * P (dict g).1 (dict g).2
  map_add' P Q := by funext g; simp [mul_add]
  map_smul' a P := by funext g; simp [mul_left_comm]

def onQ : (GA D V → ℂ) →ₗ[ℂ] (AutQ V → ℂ) where
  toFun φ := fun q => φ q.out
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def SS {X : Comp → Data E r} (la : ∀ c, Wt (X c).Ψ r) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) : Submodule ℂ (Lp ℂ 2 (muQ1 V)) :=
  Submodule.span ℂ {F | ∃ P : FDSec X, IsHolCusp X la P ∧
    ∃ h : MemLp (onQ V (adel V dict mu P)) 2 (muQ1 V), F = h.toLp _}

variable {K : Type} [Field K] {C : Type} [AddCommGroup C] [Module K C] (σ : K →+* ℂ)

def jFn {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) : C →ₛₗ[σ] (AutQ V → ℂ) :=
  (onQ V ∘ₗ adel V dict mu).comp rd

def RdHolCusp {X : Comp → Data E r} (la : ∀ c, Wt (X c).Ψ r) (rd : C →ₛₗ[σ] FDSec X) : Prop :=
  ∀ f, IsHolCusp X la (rd f)

def JMemL2 {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) : Prop :=
  ∀ f, MemLp (jFn V σ rd dict mu f) 2 (muQ1 V)

def uniformisationL2 {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) : C →ₛₗ[σ] Lp ℂ 2 (muQ1 V) where
  toFun f := (h f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    congr 1
    exact map_add _ f g
  map_smul' a f := by
    rw [← MemLp.toLp_const_smul]
    congr 1
    exact map_smulₛₗ _ a f

def l2NormAlt {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) (f : C) : ℝ :=
  ‖uniformisationL2 V σ rd dict mu h f‖

theorem l2Norm_nonneg_bis {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) (f : C) : 0 ≤ l2NormAlt V σ rd dict mu h f := norm_nonneg _

theorem l2Norm_smul_alt {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) (a : K) (f : C) :
    l2NormAlt V σ rd dict mu h (a • f) = ‖σ a‖ * l2NormAlt V σ rd dict mu h f := by
  simp only [l2NormAlt, map_smulₛₗ, norm_smul]

theorem L2Norm_add_le {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) (f g : C) :
    l2NormAlt V σ rd dict mu h (f + g) ≤ l2NormAlt V σ rd dict mu h f + l2NormAlt V σ rd dict mu h g := by
  simp only [l2NormAlt, map_add (f := _)]
  exact norm_add_le _ _

def JInj {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) : Prop :=
  ∀ (n : ℕ) (b : Fin n → C), LinearIndependent K b → LinearIndependent ℂ (fun i => uniformisationL2 V σ rd dict mu h (b i))

def L2Definite {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu) : Prop :=
  ∀ f, l2NormAlt V σ rd dict mu h f = 0 → f = 0

def FinVol : Prop := muQ V Set.univ ≠ 0 ∧ muQ V Set.univ ≠ ⊤

def archM (th' : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (h : GA D V) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  (infHom V h).1.map th'

def archMat {X : Comp → Data E r} (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r)
    (x0 : ∀ c, Frame (X c).Ψ r) (h : GA D V) (c : Comp) : Frame (X c).Ψ r :=
  fun τ => ((mat (x0 c) τ)⁻¹ * Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th c τ) h) * mat (x0 c) τ :
    Matrix (Fin r) (Fin r) ℂ)

def DictIsUnif {X : Comp → Data E r} (dict : GA D V → Σ c, Frame (X c).Ψ r) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r) : Prop :=
  (∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧
    (∀ k ∈ Kf, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (g * k) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧
    (∃ x0 : ∀ c, Frame (X c).Ψ r, (∀ c, x0 c ∈ (X c).dom ∧ ∃ g, dict g = ⟨c, x0 c⟩) ∧
      ∀ g, ∀ h ∈ GinfC V, ∃ γ' ∈ (X (dict g).1).Γ,
        dict (g * h) = ⟨(dict g).1, lact γ' (rmul (dict g).2 (archMat V th hr x0 h (dict g).1))⟩) ∧
    (∀ g, (dict g).2 ∈ (X (dict g).1).dom) ∧
    (∀ c, ∀ x ∈ (X c).dom, ∃ g, ∃ γ ∈ (X c).Γ, ∃ b ∈ Bor (X c).Ψ r, dict g = ⟨c, rmul (lact γ x) b⟩) ∧
    ∀ g g', (∃ γ' ∈ (X (dict g).1).Γ, dict g' = ⟨(dict g).1, lact γ' (dict g).2⟩) →
      ∃ γ ∈ GQ V, ∃ k ∈ Kf, g' = γ * g * k

def repOf {X : Comp → Data E r} (dict : GA D V → Σ c, Frame (X c).Ψ r) (c : Comp) : GA D V :=
  Classical.epsilon fun g => (dict g).1 = c

def MuUnit {X : Comp → Data E r} (dict : GA D V → Σ c, Frame (X c).Ψ r) (mu : GA D V → ℂ) : Prop :=
  (∀ g g', mu (g * g') = mu g * mu g') ∧ (∀ g, ‖mu g‖ = 1) ∧ (∀ γ ∈ GQ V, mu γ = 1) ∧
    ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1

theorem pnorm_eq_of_unit (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    (h : ∀ τ i, ‖dmin X.Gm x τ i‖ = 1) : X.pnorm la P x = ‖P x‖ := by
  simp [Data.pnorm, norm_div, h]

theorem L2Norm_le_sup_norm {X : Comp → Data E r} (la : ∀ c, Wt (X c).Ψ r) (rd : C →ₛₗ[σ] FDSec X)
    (dict : GA D V → Σ c, Frame (X c).Ψ r) (mu : GA D V → ℂ) (h : JMemL2 V σ rd dict mu)
    (hd : ∀ g, (dict g).2 ∈ (X (dict g).1).dom) (hm : MuUnit V dict mu) (f : C)
    (hfin : supE X la (rd f) ≠ ⊤) : l2NormAlt V σ rd dict mu h f ≤ supN X la (rd f) := by
  haveI : IsProbabilityMeasure (muQ1 V) := by
    unfold muQ1
    split_ifs with hh
    · constructor
      rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hh.1 hh.2]
    · infer_instance
  have hC : 0 ≤ supN X la (rd f) := supN_nonneg X la (rd f)
  have hb : ∀ᵐ q ∂(muQ1 V), ‖(uniformisationL2 V σ rd dict mu h f : AutQ V → ℂ) q‖ ≤ supN X la (rd f) := by
    filter_upwards [(h f).coeFn_toLp] with q hq
    have hq' : (uniformisationL2 V σ rd dict mu h f : AutQ V → ℂ) q = jFn V σ rd dict mu f q := hq
    rw [hq']
    show ‖mu q.out * rd f (dict q.out).1 (dict q.out).2‖ ≤ _
    rw [norm_mul, hm.2.1, one_mul,
      ← pnorm_eq_of_unit (X (dict q.out).1) (la (dict q.out).1) (rd f (dict q.out).1) (dict q.out).2 (hm.2.2.2 q.out)]
    have h1 : ENNReal.ofReal ((X (dict q.out).1).pnorm (la (dict q.out).1) (rd f (dict q.out).1) (dict q.out).2)
        ≤ supE X la (rd f) :=
      le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (rd f p.1) p.2))
        ⟨(dict q.out).1, ⟨(dict q.out).2, hd q.out⟩⟩
    have h0 : 0 ≤ (X (dict q.out).1).pnorm (la (dict q.out).1) (rd f (dict q.out).1) (dict q.out).2 := by
      unfold Data.pnorm
      exact mul_nonneg (norm_nonneg _) (pnorm_fac_nonneg _ _ _)
    have h2 := ENNReal.toReal_mono hfin h1
    rwa [ENNReal.toReal_ofReal h0] at h2
  have := Lp.norm_le_of_ae_bound hC hb
  simpa [l2NormAlt, measureUnivNNReal] using this

def EquivariantFiniteGroup {X : Comp → Data E r} (rd : C →ₛₗ[σ] FDSec X) (dict : GA D V → Σ c, Frame (X c).Ψ r)
    (mu : GA D V → ℂ) {G0 : Type} [Group G0] (ρ : G0 →* (C →ₗ[K] C)) (chi : G0 →* Kˣ) (ℓ : G0 → GA D V) :
    Prop :=
  ∀ g f x, adel V dict mu (rd (ρ g f)) x = σ ((chi g : Kˣ) : K) * adel V dict mu (rd f) (x * ℓ g)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ExtendedPointBaseChange
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

structure PtExt (X : PJ D B P j) where
  Pt' : HeightOneSpectrum (𝓞 B.KO) → Type
  extendedPointBaseChange : ∀ la, Pt' la → (P.loc X.dat (resCh la)).Pt (P.loc X.dat (resCh la)).YY
  vAt' : ∀ la, Pt' la → X.Forms → EReal
  vAt'_zero : ∀ la y, vAt' la y 0 = ⊤
  vAt'_ne_bot : ∀ la y F, vAt' la y F ≠ ⊥
  vAt'_add : ∀ la y F G, min (vAt' la y F) (vAt' la y G) ≤ vAt' la y (F + G)
  vAt'_smul : ∀ la y (a : B.KO) F, a ≠ 0 →
    vAt' la y (a • F) = (((vAdd la a : ℤ) : ℝ) : EReal) + vAt' la y F
  vAt'_mul : ∀ la y w w' (F : B.Cusp j w) (G : B.Cusp j w'),
    vAt' la y (X.inc w F * X.inc w' G) = vAt' la y (X.inc w F) + vAt' la y (X.inc w' G)

def IntAtExt (X : PJ D B P j) (E : PtExt X) : Prop :=
  ∀ w (F : B.Cusp j w), F ∈ B.Mlat j w → ∀ la (y : E.Pt' la), 0 ≤ E.vAt' la y (X.inc w F)

def xplus (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) : PJ D B P j where
  Forms := X.Forms
  rF := X.rF
  aF := X.aF
  aFO := X.aFO
  stF := X.stF
  inc := X.inc
  inc_inj := X.inc_inj
  inc_indep := X.inc_indep
  inc_mul := X.inc_mul
  dat := X.dat
  dat_rk := X.dat_rk
  dat_jj := X.dat_jj
  Pt la := X.Pt la ⊕ E.Pt' la
  pt66 la := Sum.elim (X.pt66 la) (E.extendedPointBaseChange la)
  vAt la := Sum.elim (X.vAt la) (E.vAt' la)
  vAt_zero la
    | .inl y => X.vAt_zero la y
    | .inr y => E.vAt'_zero la y
  vAt_ne_bot la
    | .inl y => X.vAt_ne_bot la y
    | .inr y => E.vAt'_ne_bot la y
  vAt_add la
    | .inl y => X.vAt_add la y
    | .inr y => E.vAt'_add la y
  vAt_smul la
    | .inl y => X.vAt_smul la y
    | .inr y => E.vAt'_smul la y
  vAt_mul la
    | .inl y => X.vAt_mul la y
    | .inr y => E.vAt'_mul la y
  Mlat_eq w F :=
    ⟨fun h la y => match y with
      | .inl y => (X.Mlat_eq w F).1 h la y
      | .inr y => hM w F h la y,
     fun h => (X.Mlat_eq w F).2 fun la y => h la (.inl y)⟩
  thAll := X.thAll
  shortTh := X.shortTh

section xplus

variable (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E)

end xplus

abbrev withNorm (B : WeightFamilies.Prov D) (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)
    (h0 : ∀ j ka σ F, 0 ≤ N j ka σ F) (h1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0)
    (h2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F)
    (h3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G)
    (h4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F) : WeightFamilies.Prov D :=
  { B with l2NormAlt := N, l2Norm_nonneg_bis := h0, l2Norm_eq_zero_iff := h1, l2Norm_smul_alt := h2, l2Norm_add_le' := h3, l2Norm_le_supNorm_alt := h4 }

section tol2NormAlt

variable (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)
    (h0 : ∀ j ka σ F, 0 ≤ N j ka σ F) (h1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0)
    (h2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F)
    (h3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G)
    (h4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F)

def PJ.tol2NormAlt (X : PJ D B P j) : PJ D (withNorm B N h0 h1 h2 h3 h4) P j where
  Forms := X.Forms
  rF := X.rF
  aF := X.aF
  aFO := X.aFO
  stF := X.stF
  inc := X.inc
  inc_inj := X.inc_inj
  inc_indep := X.inc_indep
  inc_mul := X.inc_mul
  dat := X.dat
  dat_rk := X.dat_rk
  dat_jj := X.dat_jj
  Pt := X.Pt
  pt66 := X.pt66
  vAt := X.vAt
  vAt_zero := X.vAt_zero
  vAt_ne_bot := X.vAt_ne_bot
  vAt_add := X.vAt_add
  vAt_smul := X.vAt_smul
  vAt_mul := X.vAt_mul
  Mlat_eq := X.Mlat_eq
  thAll := X.thAll
  shortTh := X.shortTh

def scalarsWithNorm (S : Scal B) : Scal (withNorm B N h0 h1 h2 h3 h4) := ⟨S.sW, S.sF, S.s0, S.sK⟩

def xplusN (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) : PJ D (withNorm B N h0 h1 h2 h3 h4) P j :=
  PJ.tol2NormAlt N h0 h1 h2 h3 h4 (xplus X E hM)

end tol2NormAlt

section Transfer

variable (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)
    (h0 : ∀ j ka σ F, 0 ≤ N j ka σ F) (h1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0)
    (h2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F)
    (h3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G)
    (h4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F)


theorem concl_xplus (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (T : ℕ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ) :
    Concl (xplus X E hM) S ka wL wF T nus β ↔ Concl X S ka wL wF T nus β := Iff.rfl

end Transfer

section On

variable (cov : ∀ j, WeightFamilies.Wt D j → Prop) (Nn : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)


open Classical in
def l2nOn : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ :=
  fun j ka σ F => if cov j ka then Nn j ka σ F else B.supN j ka σ F

variable {cov Nn}
variable (h0 : ∀ j ka, cov j ka → ∀ σ F, 0 ≤ Nn j ka σ F)
    (h1 : ∀ j ka, cov j ka → ∀ σ F, Nn j ka σ F = 0 ↔ F = 0)
    (h2 : ∀ j ka, cov j ka → ∀ σ (a : B.KO) F, Nn j ka σ (a • F) = ‖σ a‖ * Nn j ka σ F)
    (h3 : ∀ j ka, cov j ka → ∀ σ F G, Nn j ka σ (F + G) ≤ Nn j ka σ F + Nn j ka σ G)
    (h4 : ∀ j ka, cov j ka → ∀ σ F, Nn j ka σ F ≤ B.supN j ka σ F)

include h0 in
theorem l2nOn_nonneg : ∀ j ka σ F, 0 ≤ l2nOn cov Nn j ka σ F := fun j ka σ F => by
  unfold l2nOn; split_ifs with h
  · exact h0 j ka h σ F
  · exact B.supN_nonneg j ka σ F

include h1 in
theorem l2nOn_eq_zero : ∀ j ka σ F, l2nOn cov Nn j ka σ F = 0 ↔ F = 0 := fun j ka σ F => by
  unfold l2nOn; split_ifs with h
  · exact h1 j ka h σ F
  · exact B.supN_eq_zero j ka σ F

include h2 in
theorem l2nOn_smul : ∀ j ka σ (a : B.KO) F, l2nOn cov Nn j ka σ (a • F) = ‖σ a‖ * l2nOn cov Nn j ka σ F :=
  fun j ka σ a F => by
  unfold l2nOn; split_ifs with h
  · exact h2 j ka h σ a F
  · exact B.supN_smul j ka σ a F

include h3 in
theorem l2nOn_add : ∀ j ka σ F G, l2nOn cov Nn j ka σ (F + G) ≤ l2nOn cov Nn j ka σ F + l2nOn cov Nn j ka σ G :=
  fun j ka σ F G => by
  unfold l2nOn; split_ifs with h
  · exact h3 j ka h σ F G
  · exact B.supN_add j ka σ F G

include h4 in
theorem l2nOn_le : ∀ j ka σ F, l2nOn cov Nn j ka σ F ≤ B.supN j ka σ F := fun j ka σ F => by
  unfold l2nOn; split_ifs with h
  · exact h4 j ka h σ F
  · exact le_rfl

abbrev withNormOnWeights : WeightFamilies.Prov D :=
  withNorm B (l2nOn cov Nn) (l2nOn_nonneg h0) (l2nOn_eq_zero h1) (l2nOn_smul h2) (l2nOn_add h3) (l2nOn_le h4)

end On

end Formalism.L2.Pj
end
end

