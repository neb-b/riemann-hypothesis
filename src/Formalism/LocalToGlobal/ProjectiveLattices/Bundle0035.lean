module

public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtMain
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.KapTrdegPf
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import ReciprocityTheory.SemistableReduction.Bundle0029
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftCurveSt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftSec
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftLoc
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftRG
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

theorem htConcl_dataOf (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    (hne : CompNe Xo c) (hfg : FnFG Xo c) (htr : FnTrdeg Xo c Dd) (hac : FnAlgClosed (Xo := Xo) (c := c))
    (hwb : ∀ Z, evC h Z (wR (jc Z)) ≠ 0) (het : NZAt h etR) (hta1 : NZAt h ta1R) (hta2 : NZAt h ta2R)
    (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2)
    (huta1 : wtZ uta1.1 uta1.2 = (2 : ℕ) • (wtZ uL.1 uL.2 - wtZ ude.1 ude.2))
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2)
    (hfn : FnNe Xo c fn) (hconj : FnConj Xo c fn yP)
    (hbdd : LawBdd (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha1 : A1Bigness (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha2 : A2RegularityOrders (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha3' : LawA3' (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (sel : Fin (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).del → Fin np)
    (ha4 : A4Selection (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) sel)
    (hnum : NumOK (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha13 : A13Measurable (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (hH1 : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).FinitePlaceHyp) (hF1d : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).TrivialPlaceHyp)
    (hLAM : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HtLAM) (hSup : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HtSup)
    (hI2et : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HeightIntegralEstimateTrivialPlace) (hI2be : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HeightIntegralBoundEstimate) :
    Formalism.MainNotions.Gaps.HeightData.HtConcl ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).htOf (axHOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne hfg htr hac hwb het hta1 hta2 huet huta1 huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13)
      ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).genericSection_of_axioms (axHOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne hfg htr hac hwb het hta1 hta2 huet huta1 huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13))) :=
  (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).heights (axHOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne hfg htr hac hwb het hta1 hta2 huet huta1 huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13)
    ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).genericSection_of_axioms (axHOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne hfg htr hac hwb het hta1 hta2 huet huta1 huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13)) hH1 hF1d hLAM hSup hI2et hI2be

section Of

open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj.abelian₂ Formalism.L2.LamCM ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {Tc : Core D}

end Of

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CoreAt
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (l : Level (hostOfRecord D))
  (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1)

def parAt : Par D where
  H := hostOfRecord D
  l := l
  c :=
    { F := FO D
      fin := inferInstance
      conj := fun τ a => conj_mem_FO D τ a
      zeta_mem := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).zeta_mem
        have h1 : (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))).M' = l.M' := by
          simp [Level.M', levelG, levelOfPs, hl.1, hl.2]
        rw [h1] at h
        exact h
      le := by
        have h := (coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz).le
        have h1 : KA l = KA (levelG D (hU := unramBridge D.host.E (cmUnram_conj D))) := by
          unfold KA
          rw [hl.2]
          rfl
        rw [h1]
        exact h }
  Dw := datumAtLift D _ (datHolds D)
  Xo := fun j => Classical.choice (hN D.host.E _ (datumAtLift D _ (datHolds D) j) l (datumAtLift_pq_pos D _ (datHolds D) j))
  eO := eOf D hF

def LevelPb (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  ∃ l : Level (hostOfRecord D), (l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) ∧
    l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CurveInstSt
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7}

def SpanW {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) {wL : WeightFamilies.Wt D j} {N : ℕ}
    (w : Fin N → B.Cusp j wL) (S : Scal B) : Prop :=
  Submodule.span (𝓞 B.KO) (Set.range w) = X.WWc S.sW wL

variable {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

def wNorm (σ : T.Q.c.F →+* ℂ) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (p : FPt (T.U j σ).X) : ℝ :=
  Real.sqrt (∑ k, (((T.U j σ).X p.1).pnorm (laU (T.U j σ) (wtA wL) wL.n p.1)
    (rdU (T.U j σ) ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) p.1) p.2) ^ 2)

def BigAt (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF) : Prop :=
  NoCommonZero (Xo := T.Q.Xo j) (c := T.Q.c) (fun k => ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j)) ∧
  (∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j) ≠ 0 ∧
    Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k =>
      evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) /
        evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j))) = WeightFamilies.dimY D j)

def ThAt (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (g0 : (recB h.toLawsCore).Cusp j wF) : Prop :=
  ∃ (e : ℕ) (w' : WeightFamilies.Wt D j) (θ : (recB h.toLawsCore).Cusp j w'),
    wadd wF w' = wsmul e wL ∧
    ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((θ : (recB h.toLawsCore).Cusp j w') : T.R j) ≠ 0

def CurveInstSt : Prop :=
  ∀ (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (S : Scal (recB h.toLawsCore))
    (g0 : (recB h.toLawsCore).Cusp j wF),
    SpanW (recPlus h j hj) G.w S → BigAt h j hj hG G → ThAt h j hj hG G g0 → (recPlus h j hj).NonZeroComp wF g0 →
    Nonempty (CurveModel G la g0)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.EtArch
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Top D} (h : LawsP T)

def EtArch (th tableLineDegreeTwo : ℝ) : ∀ j i, (recB h.toLawsCore).Cusp j (wEt D j i) → Prop :=
  fun j i η => ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp)
    (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom →
      lieFac (T.Q.Dw j) (xiR D) (wtA (wEt D j i)) *
          ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA (wEt D j i)) (wEt D j i).n k)
            (rdU (T.U j σ) η.1 k) x ≤
        Real.exp (-(i : ℝ) * (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x - tableLineDegreeTwo))

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FullXi
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def cjFin (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* (Af D.host.F ⊗[D.host.F] D.host.E)ˣ :=
  Units.map (Algebra.TensorProduct.map (AlgHom.id D.host.F (Af D.host.F)) D.conjF).toRingHom.toMonoidHom

def XiTilde (xi δ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) : Prop := ∀ x, xi (x / cjFin D x) = δ x

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.LiftModelPf
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain Finset

lemma nval_alg_nonneg {T : CDVR} (x : T.V) : 0 ≤ nval T.V 1 (algebraMap T.V T.Fr x) := by
  by_cases hx : x = 0
  · rw [hx, map_zero, nval_zero]; exact le_top
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (mt (IsDiscreteValuationRing.addVal_eq_top_iff).1 hx)
    have h0 : algebraMap T.V T.Fr x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hx
    rw [nval_of_ne h0, vV_alg_of_addVal hk.symm]
    exact EReal.coe_nonneg.2 (by positivity)

lemma toE_nonneg' {w : WithTop ℤ} (h : 0 ≤ w) : 0 ≤ toE w := by
  cases w with
  | top => simp [toE]
  | coe n =>
    simp only [toE]
    have : (0 : ℤ) ≤ n := by exact_mod_cast h
    exact_mod_cast this

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
  {y : PtsG G la → E.Pt' la} (hw : ∀ ζ, FromW ζ (y ζ))

abbrev hsW : ∀ ζ, SecPt ζ (y ζ) := fun ζ => (hw ζ).toSecPt

def IW : Ideal (LamL (hsW hw)) := Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
  ιW (hsW hw) (sfr (xplus X E hM) la G.w i.succ : Lw (xplus X E hM) la G.w))

def RGW : Subring (LamL (hsW hw)) :=
  stabSub (hdL_zero (hsW hw)) (hdW_mul (hsW hw)) (intSub (fun ζ => (hsW hw ζ).T) (evL (hsW hw))) ⊓
    appSub (ιW (hsW hw)) (Frac0 (xplus X E hM) la G.w).toSubring (IW hw)

theorem ιW_Jid {z : ↥(Frac0 (xplus X E hM) la G.w)} (hz : z ∈ Jid (xplus X E hM) la G.w) :
    ιW (hsW hw) (z : Lw (xplus X E hM) la G.w) ∈ IW hw := by
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Ideal.subset_span ⟨i, rfl⟩
  | zero => rw [ZeroMemClass.coe_zero, map_zero]; exact Ideal.zero_mem _
  | add x z _ _ hx hz => rw [Subalgebra.coe_add, map_add (f := _)]; exact Ideal.add_mem _ hx hz
  | smul a x _ hx => rw [smul_eq_mul, Subalgebra.coe_mul, map_mul]; exact Ideal.mul_mem_left _ _ hx

theorem RGW_hd (β : Idx D j G.N →₀ ℕ) (r : LamL (hsW hw)) (hr : r ∈ RGW hw) : hdL (hsW hw) β r ∈ RGW hw :=
  ⟨stabSub_hd _ _ _ β hr.1, appSub_hd (hdL_zero (hsW hw)) (hdW_mul (hsW hw)) (ιW (hsW hw)) _ _
    (fun β x => hasse (xplus X E hM) la G.w β x) (hdW_ι (hsW hw))
    (fun β f hf => (mem_Frac0 _ _ _).2 (hasse_mem_Hfr _ _ _ ((mem_Frac0 _ _ _).1 hf) β)) β hr.2⟩

theorem RGW_int (ζ : PtsG G la) (r : LamL (hsW hw)) (hr : r ∈ RGW hw) :
    0 ≤ nval (hsW hw ζ).T.V 1 (evL (hsW hw) ζ r) :=
  stabSub_le _ _ _ hr.1 ζ

theorem app_of_mem (f : ↥(Frac0 (xplus X E hM) la G.w)) :
    ιW (hsW hw) (f : Lw (xplus X E hM) la G.w) ∈
      appSub (ιW (hsW hw)) (Frac0 (xplus X E hM) la G.w).toSubring (IW hw) :=
  fun n => ⟨f, f.2, by rw [sub_self]; exact Ideal.zero_mem _⟩

theorem evL_inv (ζ : PtsG G la) {u : LamL (hsW hw)} (hu : IsUnit u) :
    evL (hsW hw) ζ ↑hu.unit⁻¹ = (evL (hsW hw) ζ u)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_mul, hu.val_inv_mul, map_one]

theorem inv_app {g0 : B.Cusp j wF} (C : CurveModel G la g0) (d : ↥(Frac0 (xplus X E hM) la G.w))
    (hd : ∀ ζ, (hsW hw ζ).lift (d : Lw (xplus X E hM) la G.w) ≠ 0) :
    (↑(isUnit_of_lift_ne (hsW hw) hd).unit⁻¹ : LamL (hsW hw)) ∈
      appSub (ιW (hsW hw)) (Frac0 (xplus X E hM) la G.w).toSubring (IW hw) := by
  obtain ⟨b, hb⟩ := (isUnit_toOsK_of_lift hw C d hd).exists_right_inv
  obtain ⟨v, rfl⟩ := toOsK_surjective (xplus X E hM) la G.w b
  have hz : (1 - d * v : ↥(Frac0 (xplus X E hM) la G.w)) ∈ Jid (xplus X E hM) la G.w := by
    rw [← toOsK_eq_zero_iff, map_sub, map_one, map_mul, hb, sub_self]
  have h := ιW_Jid hw hz
  push_cast at h
  exact appSub_inv _ _ _ d.2 v.2 h _

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ReadLeaves
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Test

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem wtC_of (hB : BorChartF Xo c) (hA : AllTest Xo c) (σ : c.F →+* ℂ) : WtC Xo c σ := by
  intro a n _ f hf t y y' hb
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  exact wtField_of_borChart hB a n f hf (CAt σ) t y y' (hA _ y) (hA _ y') hb

end Test

section Inv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Inv

section Cont

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

def DictLoc (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r) : Prop :=
  ∀ g₀ : GA D V, ∃ N ∈ 𝓝 g₀, ∃ (k : Comp) (x : GA D V → Frame (X k).Ψ r), ContinuousOn x N ∧
    ∀ g ∈ N, x g ∈ (X k).dom ∧ ∃ γ ∈ (X k).Γ, dict g = ⟨k, lact γ (x g)⟩

end Cont

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)


include h hj in
theorem pt_realise (la : HeightOneSpectrum (𝓞 T.Q.c.F))
    (y : PtV (T.Q.Xo j) T.Q.c (algCls _ _) Unit (fun _ _ _ _ => True) la) :
    ∃ y' : T.PtA j la, ∀ f, vAtV y' f = vAtV y f := by
  rcases y with ⟨q, S, io, e, ho, z, hz, η, hη, rfl⟩
  obtain ⟨η', hη'⟩ := T.G.liesTotal h.points_condition h.bc66 hj la S io e ho z hz
  exact ⟨PtV.mk la ho z hz η' hη', fun _ => rfl⟩

theorem ereal_lin (a c : ℝ) (v : EReal) (h0 : 0 ≤ v) (ht : v ≠ ⊤) :
    (((a + c * v.toReal : ℝ)) : EReal) = (a : EReal) + (c : EReal) * v := by
  have hb : v ≠ ⊥ := fun hb => by simp [hb] at h0
  conv_rhs => rw [← EReal.coe_toReal ht hb]
  push_cast
  rfl

theorem regularity_R2_extended_points :
    RegularityR2 (recPJ h j hj) (extAll h j hj)
      (fun {wL} {n} gens => NoCommonZero (T.Q.Xo j) T.Q.c fun i => (gens i).1) := by
  have hv : ∀ la (y : (recPJ h j hj).Pt la) w (F : (recB h.toLawsCore).Cusp j w),
      (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y F.1 :=
    fun la y w F => recPJ_vAt_inc h j hj la y w F
  have ev : ∀ la (y : (extAll h j hj).Pt' la) w (F : (recB h.toLawsCore).Cusp j w),
      (extAll h j hj).vAt' la y ((recPJ h j hj).inc w F) = y.1 F.1 :=
    fun la y w F => extAll_vAt_inc h j hj la y w F
  constructor
  · intro wL wE n gens et nus c hc hNZ hX la y'
    have hR := (h.reg j hj).1.2 ⟨(wtA wL, wL.n), dom_wtA wL⟩ ⟨(wtA wE, wE.n), dom_wtA wE⟩ n
      (fun k => ⟨(gens k).1, cutR_le T.C j wL (gens k).2⟩) ⟨et.1, cutR_le T.C j wE et.2⟩ nus c hc hNZ
      (by
        rintro la' ⟨_, ⟨y, rfl⟩⟩
        obtain ⟨y0, hy0⟩ := pt_realise h j hj la' y
        have hx := hX la' y0
        have eet : (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wE et) = vAtV y et.1 :=
          (hv la' y0 wE et).trans (hy0 _)
        have egs : (⨅ k, (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wL (gens k))) =
            ⨅ k, vAtV y (gens k).1 := iInf_congr fun k => (hv la' y0 wL (gens k)).trans (hy0 _)
        have h0 : 0 ≤ vAtV y et.1 := le_of_le_of_eq hx.1 eet
        show 0 ≤ vAtV y et.1 ∧ (vAtV y et.1 ≠ ⊤ →
          (⨅ k, vAtV y (gens k).1) ≤ (nus la' : EReal) + (c : EReal) * vAtV y et.1)
        refine ⟨h0, fun hne => ?_⟩
        have hne' : (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wE et) ≠ ⊤ := by rw [eet]; exact hne
        calc (⨅ k, vAtV y (gens k).1)
            = ⨅ k, (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wL (gens k)) := egs.symm
          _ ≤ (((nus la' : ℝ) + c * ((recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wE et)).toReal : ℝ) :
                EReal) := hx.2 hne'
          _ = (nus la' : EReal) + (c : EReal) * vAtV y et.1 := by
              rw [eet]; exact ereal_lin _ _ _ h0 hne)
    obtain ⟨h1, h2⟩ := hR.1 la ⟨y'.1, y'.2⟩
    have eet : (extAll h j hj).vAt' la y' ((recPJ h j hj).inc wE et) = y'.1 et.1 := ev la y' wE et
    have egs : (⨅ k, (extAll h j hj).vAt' la y' ((recPJ h j hj).inc wL (gens k))) =
        ⨅ k, y'.1 (gens k).1 := iInf_congr fun k => ev la y' wL (gens k)
    have h1' : 0 ≤ y'.1 et.1 := h1
    refine ⟨le_of_le_of_eq h1' eet.symm, fun hne => ?_⟩
    have hne' : y'.1 et.1 ≠ ⊤ := by rw [← eet]; exact hne
    calc (⨅ k, (extAll h j hj).vAt' la y' ((recPJ h j hj).inc wL (gens k)))
        = ⨅ k, y'.1 (gens k).1 := egs
      _ ≤ (nus la : EReal) + (c : EReal) * y'.1 et.1 := h2 hne'
      _ = (((nus la : ℝ) + c * ((extAll h j hj).vAt' la y' ((recPJ h j hj).inc wE et)).toReal : ℝ) :
            EReal) := by rw [eet]; exact (ereal_lin _ _ _ h1' hne').symm
  · intro wL n gens nus hNZ hX la y'
    have hR := (h.reg j hj).2 (wtA wL) wL.n (dom_wtA wL) n (fun k => (gens k).1)
      (fun k => cutR_le T.C j wL (gens k).2) hNZ nus
      (by
        rintro la' _ ⟨y, rfl⟩
        obtain ⟨y0, hy0⟩ := pt_realise h j hj la' y
        have egs : (⨅ k, (recPJ h j hj).vAt la' y0 ((recPJ h j hj).inc wL (gens k))) =
            ⨅ k, vAtV y (gens k).1 := iInf_congr fun k => (hv la' y0 wL (gens k)).trans (hy0 _)
        exact le_of_eq_of_le egs.symm (hX la' y0)) la y'.1 y'.2
    calc (⨅ k, (extAll h j hj).vAt' la y' ((recPJ h j hj).inc wL (gens k)))
        = ⨅ k, y'.1 (gens k).1 := iInf_congr fun k => ev la y' wL (gens k)
      _ ≤ _ := hR

end Formalism.L2.Pj
end
end

