module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

section Sup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  (X : Comp → Data E r) (la : ∀ c, ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r)

theorem supE_add_le (P Q : FDSec X) : supE X la (P + Q) ≤ supE X la P + supE X la Q := by
  unfold supE
  refine iSup_le fun p => ?_
  have h1 : (X p.1).pnorm (la p.1) ((P + Q) p.1) p.2 ≤
      (X p.1).pnorm (la p.1) (P p.1) p.2 + (X p.1).pnorm (la p.1) (Q p.1) p.2 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
  calc ENNReal.ofReal ((X p.1).pnorm (la p.1) ((P + Q) p.1) p.2)
      ≤ ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2) +
          ENNReal.ofReal ((X p.1).pnorm (la p.1) (Q p.1) p.2) :=
        (ENNReal.ofReal_le_ofReal h1).trans ENNReal.ofReal_add_le
    _ ≤ (⨆ p : FPt X, ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) +
          ⨆ p : FPt X, ENNReal.ofReal ((X p.1).pnorm (la p.1) (Q p.1) p.2) :=
        add_le_add (le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) p)
          (le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (Q p.1) p.2)) p)

theorem supE_smul (a : ℂ) (P : FDSec X) : supE X la (a • P) = ENNReal.ofReal ‖a‖ * supE X la P := by
  unfold supE
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun p => ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  show ‖a * P p.1 p.2‖ * _ = ‖a‖ * (‖P p.1 p.2‖ * _)
  rw [norm_mul]
  ring

theorem supE_ne_top [Fintype Comp] {P : FDSec X} (h : P ∈ holSub X la) : supE X la P ≠ ⊤ := by
  unfold holSub at h
  induction h using Submodule.span_induction with
  | mem P hP =>
    have hb : ∀ c, ∃ C : ℝ, ∀ x ∈ (X c).dom, (X c).pnorm (la c) (P c) x ≤ C := fun c => (hP c).1.2
    choose C hC using hb
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑ c, |C c|))
      (iSup_le fun p => ENNReal.ofReal_le_ofReal ?_)
    calc (X p.1).pnorm (la p.1) (P p.1) p.2 ≤ C p.1 := hC p.1 p.2 p.2.2
      _ ≤ |C p.1| := le_abs_self _
      _ ≤ ∑ c, |C c| := Finset.single_le_sum (fun c _ => abs_nonneg (C c)) (Finset.mem_univ _)
  | zero =>
    refine ne_top_of_le_ne_top ENNReal.zero_ne_top (iSup_le fun p => ?_)
    simp [ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm]
  | add P Q _ _ hP hQ =>
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hP, hQ⟩) (supE_add_le X la P Q)
  | smul a P _ hP =>
    rw [supE_smul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP

end Sup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)


open Classical in
def goodOf (σ : c.F →+* ℂ) : c.F →+* ℂ := if GoodEmb c σ then σ else (starRingEnd ℂ).comp σ

theorem norm_goodOf (σ : c.F →+* ℂ) (x : c.F) : ‖goodOf c σ x‖ = ‖σ x‖ := by
  unfold goodOf
  split_ifs <;> simp

theorem goodEmb_goodOf (σ : c.F →+* ℂ) : GoodEmb c (goodOf c σ) := by
  unfold goodOf
  split_ifs with h
  · exact h
  · unfold GoodEmb at h ⊢
    set β := (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ with hβ
    have hβsq : β ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq, hβ, ← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
    have hneg : β = -H.rt0 := by
      have hm : (β - H.rt0) * (β + H.rt0) = 0 := by
        rw [show (β - H.rt0) * (β + H.rt0) = β ^ 2 - H.rt0 ^ 2 by ring, hβsq, sub_self]
      rcases mul_eq_zero.mp hm with h1 | h1
      · exact absurd (sub_eq_zero.mp h1) h
      · exact eq_neg_of_add_eq_zero_left h1
    have hd : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
    have h3 := congrArg Complex.im H.sqrt_neg_disc_sq
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero] at h2 h3
    have hre : H.rt0.re = 0 := by
      rcases mul_eq_zero.mp (show H.rt0.re * H.rt0.im = 0 by nlinarith) with h4 | h4
      · exact h4
      · rw [h4] at h2
        exfalso
        nlinarith [mul_self_nonneg H.rt0.re]
    show starRingEnd ℂ β = H.rt0
    rw [hneg, map_neg]
    apply Complex.ext <;> simp [hre]

theorem IsNormOn.of_goodOf {C : Submodule c.F (Rul Xo c)} {σ : c.F →+* ℂ} {N : Rul Xo c → ℝ}
    (h : IsNormOn C (goodOf c σ) N) : IsNormOn C σ N := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by simpa only [norm_goodOf] using h1, by simpa only [norm_goodOf] using h2,
    by simpa only [norm_goodOf] using h3, by simpa only [norm_goodOf] using h4⟩

def lieFac (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

theorem lieFac_pos (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : 0 < lieFac Dw x a := Real.exp_pos _

def supC (x : ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ℝ :=
  lieFac Dw x a * supN (U σ).X (laU (U σ) a n) (rdU (U σ) f)

def SupDef : Prop :=
  ∀ a n, Dom a n → ∀ σ, GoodEmb c σ → ∀ f ∈ cusp Xo c U a n, supN (U σ).X (laU (U σ) a n) (rdU (U σ) f) = 0 → f = 0

variable {Xo c U}

theorem supE_cusp_ne_top {a n} {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n) :
    supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) ≠ ⊤ := by
  have h1 := (Submodule.mem_inf.mp hf).2
  have h2 := Submodule.mem_iInf _ |>.mp h1 σ
  have h3 := Submodule.mem_iInf _ |>.mp h2 hσ
  exact supE_ne_top (U σ).X (laU (U σ) a n) (Submodule.mem_comap.mp h3)

theorem isNormOn_supC (x : ℝ) (h : SupDef Xo c U) {a n} (hd : Dom a n) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) :
    IsNormOn (cusp Xo c U a n) σ (supC Xo c U x σ a n) := by
  constructor
  · intro f _
    exact mul_nonneg (lieFac_pos _ _ _).le (supN_nonneg _ _ _)
  · intro f hf h0
    exact h a n hd σ hσ f hf ((mul_eq_zero.mp h0).resolve_left (lieFac_pos _ _ _).ne')
  · intro y f _
    unfold supC supN
    rw [map_smulₛₗ, supE_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
    ring
  · intro f hf g hg
    unfold supC supN
    rw [← mul_add, map_add (f := _), ← ENNReal.toReal_add (supE_cusp_ne_top hσ hf) (supE_cusp_ne_top hσ hg)]
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono ?_ (supE_add_le _ _ _ _)) (lieFac_pos _ _ _).le
    exact ENNReal.add_ne_top.mpr ⟨supE_cusp_ne_top hσ hf, supE_cusp_ne_top hσ hg⟩

variable (U)

-- Prefer the same-scalar submodule instance when elaborating the L² constructions.
attribute [local instance 2000] Submodule.module

def rdC (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : cusp Xo c U a n →ₛₗ[σ] FDSec (U σ).X :=
  (rdU (U σ)).comp (cusp Xo c U a n).subtype

variable {D : D7} (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ)

def CuspL2 : Prop := ∀ a n, Dom a n → JMemL2 V σ (rdC U σ a n) dict mu


open Classical in
def l2C (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : JMemL2 V σ (rdC U σ a n) dict mu) (f : Rul Xo c) : ℝ :=
  if hf : f ∈ cusp Xo c U a n then
    lieFac Dw x a * l2NormAlt V σ (rdC U σ a n) dict mu h ⟨f, hf⟩ else 0

def L2DefiniteCuspForms (h : CuspL2 U σ V dict mu) : Prop :=
  ∀ a n (hd : Dom a n), L2Definite V σ (rdC U σ a n) dict mu (h a n hd)

variable {U σ V dict mu}

theorem isNormOn_l2C (x₀ : ℝ) {h : CuspL2 U σ V dict mu} (h1 : L2DefiniteCuspForms U σ V dict mu h) {a n} (hd : Dom a n) :
    IsNormOn (cusp Xo c U a n) σ (l2C U σ V dict mu x₀ a n (h a n hd)) := by
  constructor
  · intro f hf
    rw [l2C, dite_eq_left hf]; exact mul_nonneg (lieFac_pos _ _ _).le (l2Norm_nonneg_bis _ _ _ _ _ _ _)
  · intro f hf h0
    rw [l2C, dite_eq_left hf] at h0
    exact congrArg Subtype.val (h1 a n hd ⟨f, hf⟩ ((mul_eq_zero.mp h0).resolve_left (lieFac_pos _ _ _).ne'))
  · intro x f hf
    rw [l2C, l2C, dite_eq_left hf, dite_eq_left (Submodule.smul_mem _ x hf)]
    have := l2Norm_smul_alt V σ (rdC U σ a n) dict mu (h a n hd) x ⟨f, hf⟩
    exact (congrArg (lieFac Dw x₀ a * ·) this).trans (by ring)
  · intro f hf g hg
    rw [l2C, l2C, l2C, dite_eq_left hf, dite_eq_left hg, dite_eq_left (Submodule.add_mem _ hf hg), ← mul_add]
    exact mul_le_mul_of_nonneg_left (L2Norm_add_le V σ (rdC U σ a n) dict mu (h a n hd) ⟨f, hf⟩ ⟨g, hg⟩)
      (lieFac_pos _ _ _).le

theorem l2C_le_supC (x : ℝ) (hσ : GoodEmb c σ) {a n} (h : JMemL2 V σ (rdC U σ a n) dict mu)
    (hd : ∀ g, (dict g).2 ∈ ((U σ).X (dict g).1).dom) (hm : MuUnit V dict mu) :
    ∀ f ∈ cusp Xo c U a n, l2C U σ V dict mu x a n h f ≤ supC Xo c U x σ a n f := by
  intro f hf
  unfold l2C supC
  rw [dite_eq_left hf]
  refine mul_le_mul_of_nonneg_left ?_ (lieFac_pos Dw x a).le
  exact L2Norm_le_sup_norm (V := V) (la := laU (U σ) a n) (rd := rdC U σ a n) (dict := dict) (mu := mu) (h := h)
    (hd := hd) (hm := hm) (f := ⟨f, hf⟩) (hfin := supE_cusp_ne_top hσ hf)

theorem rdC_continuousOn (hU : IsUnf (U σ)) {a n} (hd : Dom a n) (f : cusp Xo c U a n) (k : (U σ).Comp) :
    ContinuousOn (rdC U σ a n f k) ((U σ).X k).dom := by
  obtain ⟨-, -, -, -, hsec, -⟩ := hU
  have hf : (f : Rul Xo c) ∈ sec Xo c a n := (Submodule.mem_inf.mp f.2).1
  exact (hsec a n hd f hf k).1.continuousOn

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.RegularityR2Quotient
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def trivCls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop :=
  fun T ι _ => ∀ a : c.F, a ≠ 0 → ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = ι a

structure QPt where
  T : CDVR
  ι : c.F →+* T.Fr
  y : IntFr Xo c T ι
  triv : trivCls Xo c T ι y

def ordQ (q : QPt Xo c) (f : Rul Xo c) : EReal := nval q.T.V 1 (evI q.y f)

def RegularityR1Quotient (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n,
    (∃ la : HeightOneSpectrum (𝓞 c.F), ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) →
      ∀ q : QPt Xo c, 0 ≤ ordQ Xo c q f

def RegularityR2Quotient (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (aL : (E →+* ℂ) × ℕ → ℕ) (nL : ℕ) (aE : (E →+* ℂ) × ℕ → ℕ) (nE k : ℕ) (ws : Fin k → Rul Xo c)
    (et : Rul Xo c) (c' : ℝ), 0 ≤ c' → (∀ i, ws i ∈ C aL nL) → et ∈ C aE nE →
    (∃ (la : HeightOneSpectrum (𝓞 c.F)) (nu : ℝ), ∀ v ∈ valSet Xo c (algCls Xo c) la,
      0 ≤ v et ∧ (∃ i, v (ws i) ≠ ⊤) ∧ (v et ≠ ⊤ → (⨅ i, v (ws i)) ≤ (nu : EReal) + (c' : EReal) * v et)) →
    ∀ q : QPt Xo c, 0 ≤ ordQ Xo c q et ∧
      (ordQ Xo c q et ≠ ⊤ → (⨅ i, ordQ Xo c q (ws i)) ≤ (c' : EReal) * ordQ Xo c q et)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ResChPrime
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} (Q : Par D)

structure In66 : Type 1 where
  P : ModuliIntegralCharts.Prov D
  dat : ℕ → P.Dat
  Tw : ∀ j p, PointsOfFlagModel.Tower p (Q.Xo j) Q.c
  rel : ∀ j p, (P.loc (dat j) p).Pt (P.loc (dat j) p).YY → PointsOfFlagModel.Pt (Tw j p) .yy → Prop

namespace In66

variable {Q} (G : In66 Q)

abbrev PY (j p : ℕ) : Type := (G.P.loc (G.dat j) p).Pt (G.P.loc (G.dat j) p).YY

def PinDat : Prop := ∀ j, 1 ≤ j → j < D.R.m → G.P.rk (G.dat j) = D.R.r ∧ G.P.jj (G.dat j) = (D.R.sigW j).1

def PinTower : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ p, p.Prime → PointsOfFlagModel.TowerAt (G.Tw j p)

def IsAlgPt (j : ℕ) (la : HeightOneSpectrum (𝓞 Q.c.F)) (z : PointsOfFlagModel.Pt (G.Tw j (WeightAlgebra.resCh la)) .yy) : Prop :=
  ∃ (T : CDVR) (io : Q.c.F →+* T.Fr) (e : ℕ) (y : IntFr (Q.Xo j) Q.c T io), OverLa la T.V io e ∧
    algCls (Q.Xo j) Q.c T io y ∧ LiesOverBaseChange la (G.Tw j (WeightAlgebra.resCh la)) T io y z

def HasData : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ la z, G.IsAlgPt j la z →
  Nonempty (DatAt ((G.Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1)

def PinPts : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ la z, G.IsAlgPt j la z →
  (∃ η, G.rel j _ η z) ∧ ∀ η, G.rel j _ η z → (G.P.loc (G.dat j) _).fld η = PointsOfFlagModel.fld z

def PinLat : Prop := ∀ j, 1 ≤ j → j < D.R.m → ∀ la z, G.IsAlgPt j la z → ∀ η, G.rel j _ η z →
  ∀ A : DatAt ((G.Tw j (WeightAlgebra.resCh la)).Y z.1) z.2.2.1,
    ∃ e : (G.P.loc (G.dat j) _).Ylat η ≃ₗ[𝓞 D.host.E] A.Ylat,
      ∀ a b, A.beta (e a) (e b) = (G.P.loc (G.dat j) _).be η a b

def BaseChange : Prop := ∀ j, 1 ≤ j → j < D.R.m →
  ∀ (la : HeightOneSpectrum (𝓞 Q.c.F)) (T : CDVR) (io : Q.c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    ∀ y : IntFr (Q.Xo j) Q.c T io, algCls (Q.Xo j) Q.c T io y →
      ∃ z, LiesOverBaseChange la (G.Tw j (WeightAlgebra.resCh la)) T io y z

def lies (j : ℕ) (la : HeightOneSpectrum (𝓞 Q.c.F)) (T : CDVR) (io : Q.c.F →+* T.Fr)
    (y : IntFr (Q.Xo j) Q.c T io) (η : G.PY j (WeightAlgebra.resCh la)) : Prop :=
  j < D.R.m → ∃ z, G.rel j (WeightAlgebra.resCh la) η z ∧ LiesOverBaseChange la (G.Tw j (WeightAlgebra.resCh la)) T io y z

end In66

theorem resCh_prime {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : (WeightAlgebra.resCh la).Prime := by
  unfold WeightAlgebra.resCh
  haveI := la.isPrime
  haveI : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot la.asIdeal la.ne_bot
  first
  | exact CharP.char_is_prime (𝓞 K ⧸ la.asIdeal) _
  | exact (CharP.char_is_prime_or_zero (𝓞 K ⧸ la.asIdeal) _).resolve_right
      (ringChar.char_ne_zero_of_finite _)

variable {Q}

theorem In66.liesTotal (G : In66 Q) (h1 : G.PinPts) (h2 : G.BaseChange) {j : ℕ} (hj : InR D j) :
    LiesTotal (Q.Xo j) Q.c (algCls (Q.Xo j) Q.c) (fun la => G.PY j (WeightAlgebra.resCh la)) (G.lies j) := by
  intro la T io e ho y hy
  by_cases hm : j < D.R.m
  · obtain ⟨z, hz⟩ := h2 j hj.1 hm la T io e ho y hy
    obtain ⟨η, hη⟩ := (h1 j hj.1 hm la z ⟨T, io, e, y, ho, hy, hz⟩).1
    exact ⟨η, fun _ => ⟨z, hη, hz⟩⟩
  · exact ⟨(G.P.ex (G.dat j) (WeightAlgebra.resCh la)).yEta
      (Classical.choice ((G.P.ex (G.dat j) (WeightAlgebra.resCh la)).genNe _)), fun h => absurd h hm⟩

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def trivialClassCondition (T : CDVR) (io : c.F →+* T.Fr) (_y : IntFr Xo c T io) : Prop := True

theorem valSet_alg_subset (la : HeightOneSpectrum (𝓞 c.F)) :
    valSet Xo c (algCls Xo c) la ⊆ valSet Xo c (trivialClassCondition Xo c) la := by

  unfold valSet
  rintro v ⟨⟨x, hx⟩, rfl⟩
  refine ⟨⟨x, ?_⟩, rfl⟩
  obtain ⟨T, io, e, h1, y, -, h2⟩ := hx
  exact ⟨T, io, e, h1, y, trivial, h2⟩

def trivSet : Set (Rul Xo c → EReal) :=
  {q | ∃ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io),
    (∀ a : c.F, a ≠ 0 → vV T.V (io a) = 0) ∧ q = fun f => nval T.V 1 (evI y f)}

def NoCommonZero {n : ℕ} (ws : Fin n → Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), ∃ i, evR Xo c (ws i) y ≠ 0

abbrev DomWt (E : Type) [Field E] : Type := {x : ((E →+* ℂ) × ℕ → ℕ) × ℕ // Dom x.1 x.2}

def regular₂ {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ReciprocityTheory.ChartRestriction.G.T0.RegLaw (Λ := HeightOneSpectrum (𝓞 c.F)) (Wt := DomWt E)
    (fun w => cusp Xo c U w.1.1 w.1.2)
    (fun la => valSet Xo c (algCls Xo c) la) (fun la => valSet Xo c (trivialClassCondition Xo c) la)
    (fun la v => ⟨v.1, valSet_alg_subset Xo c la v.2⟩) (fun _ v _ F => v.1 F.1)
    (trivSet Xo c) (fun q _ F => q.1 F.1) (fun ws => NoCommonZero Xo c fun i => (ws i).1) ∧
  ∀ a n, Dom a n → ∀ (m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ cusp Xo c U a n) → NoCommonZero Xo c ws →
    ∀ nu : HeightOneSpectrum (𝓞 c.F) → ℝ,
      (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, (⨅ i, v (ws i)) ≤ (nu la : EReal)) →
        ∀ la, ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, (⨅ i, v (ws i)) ≤ (nu la : EReal)

variable {Xo c}

theorem regular₂.int {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (h : regular₂ Xo c U) {a n} (hd : Dom a n)
    {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n)
    (h0 : ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) :
    ∀ la, ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, 0 ≤ v f := by
  intro la v hv
  have h1 := h.1
  unfold ReciprocityTheory.ChartRestriction.G.T0.RegLaw at h1
  exact (h1.1 ⟨(a, n), hd⟩ ⟨f, hf⟩ (fun la' y => h0 la' y.1 y.2)).1 la ⟨v, hv⟩

end Formalism.L2.Pj
end
end

