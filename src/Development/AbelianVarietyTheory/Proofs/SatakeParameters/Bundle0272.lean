module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.SharpRestriction.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0263
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0056
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0140
public import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.NumbersP
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0251
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Formalism.LocalToGlobal.GroupLattices.Joint0

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodRelationsTrueColumnsAtTuple
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

open Formalism.L2.Col GlobalTheory.ColPeriodCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound GlobalTheory.Mem GlobalTheory.Mem.Col2
namespace GlobalTheory.TiesTrue

def baseCast {D : D7} {cc cc' : Ideal (𝓞 D.host.K)} (e : cc = cc') {δ : ℂ} (Bs : Formalism.L2.Ker.Base D cc δ) :
    Formalism.L2.Ker.Base D cc' δ := e ▸ Bs

theorem ambOf_baseCast {D : D7} {X : Fields} (s : Seam D X) {cc cc' : Ideal (𝓞 D.host.K)} (e : cc = cc') {δ : ℂ}
    (Bs : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) :
    ambOf s (baseCast e Bs) χ cD = ambOf s Bs χ cD := by
  subst e; rfl

def exOf {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws}
    {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} (EX : ErrX (I.rec7 l Z)) (h1 : EX.piG = X.piG) (h2 : EX.piT = X.piT) :
    ErrX (I.rec7 l Z) :=
  ⟨X.piG, h1 ▸ EX.piG_K, h1 ▸ EX.piG_norm, X.piT, h2 ▸ EX.piT_K, h2 ▸ EX.piT_norm, h2 ▸ EX.piT_cong, EX.vPl, EX.vPl_inj,
    EX.norm_mem_place_ideal⟩

theorem exOf_eq {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} {l : I.Laws}
    {Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)} (EX : ErrX (I.rec7 l Z)) (h1 : EX.piG = X.piG) (h2 : EX.piT = X.piT) :
    exOf EX h1 h2 = EX := by
  obtain ⟨piG, _, _, piT, _, _, _, _, _, _⟩ := EX
  obtain rfl : piG = X.piG := h1
  obtain rfl : piT = X.piT := h2
  rfl

theorem badS_subset {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : GlobalTheory.Mem.Col2.TC B X} (h : I.Ok) (l : I.Laws)
    (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) : badS (I.rec7 l Z) ⊆ I.S := by
  rintro p (hp | ⟨u, rfl⟩ | hp)
  · rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact h.two_q_d_mem.1
    · exact h.two_q_d_mem.2.1
    · exact h.two_q_d_mem.2.2
    · exact h.g_mem 0
    · exact h.g_mem 1
  · exact h.T_mem u
  · exact h.small_mem (Finset.mem_coe.1 hp)

theorem mem_tupGrp_of_subset {F E L : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field L]
    {S S' : Set ℕ} (hS : S' ⊆ S) {x : Chr F E L} (hx : x ∈ tupGrp F E L S) : x ∈ tupGrp F E L S' := by
  obtain ⟨h1, h4⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_⟩
  exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v) fun hg => hv ⟨hg.1, hg.2.1, fun hm => hg.2.2 (hS hm)⟩

section Gen

variable {D : D7} {EX : ErrX D} (Ch : Chars (recFields D) (recPrimes EX) D.R.m)
  (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))

def TwistTieS {S : Set ℕ} (Dx : DivX D) (μ : D.what₂.Tup) (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S) : Prop :=
  ((Dx.Qp μ : Set ℕ) = QprimeN (ξ : Chr (recFields D).F (recFields D).E (recFields D).K)) ∧
    (μ = D.what₂.mu0 → (ξ : Chr (recFields D).F (recFields D).E (recFields D).K) = 1)

def FieldTieS (A : Amb (recFields D)) {S : Set ℕ} (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S)
    (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel ξ)) (u : D.what₂.Word) : Prop :=
  ∀ i < D.R.m, JetsRatDeg A (D.R.N i) (D.R.N (i + 1)) (Sall (Pr := recPrimes EX) sel ξ u)
    (cAof sel ξ cst * cBof sel ξ cst u) (fun τ => ∑ a, ((recWts EX).nuW u (i + 1) τ).w a)

def RowTieS (μ : D.what₂.Tup) {S : Set ℕ} (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S)
    (jA : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) : Prop :=
  (∀ s : Finset (MtildeV (recWts EX) Ch sel ξ (rPsymF Ch)),
      LinearIndependent D.what₂.LL (fun x : s => (x : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch))) →
      LinearIndependent ℂ (fun x : s => jA x)) ∧
    Submodule.span ℂ (Set.range jA) = ⊤ ∧
    (∀ v ∈ (D.what₂.Mtilde μ).gen, v ∈ Set.range jA) ∧
    ∀ x, x ∈ MtildeL (recWts EX) Ch sel ξ (rPsymF Ch) ↔ ∃ c : D.what₂.Amb μ → 𝓞 D.what₂.LL,
      jA x = ∑ v ∈ (D.what₂.Mtilde μ).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v

def PerTieS (u : D.what₂.Word) (μ : D.what₂.Tup) {S : Set ℕ} (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S)
    (hP : (mtildeGSD (recWts EX) Ch sel ξ (rPsymF Ch)).Ok)
    (col : MfV (recWts EX) Ch u →ₗ[D.what₂.LL] (evGSD (recWts EX) Ch sel ξ (rPsymF Ch) u).EqFun)
    (eM : (D.div.Nu u).V ≃ₗ[D.what₂.LL] MramV (recWts EX) Ch u)
    (jA : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) : Prop :=
  ∀ φ x, D.what₂.perCol u μ (D.jN u φ) (jA x) =
    D.what₂.embLL (PtilE (recWts EX) Ch sel ξ (rPsymF Ch) hP u (col (eM φ : MfV (recWts EX) Ch u)) x)

def ChainTieS (Dx : DivX D) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (A : Amb (recFields D))
    (u : D.what₂.Word) (μ : D.what₂.Tup) {S : Set ℕ} (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S) : Prop :=
  ∃ (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel ξ))
    (I : ChIdx (recFields D) (recPrimes EX) D.R (QE sel (ξ : Chr (recFields D).F (recFields D).E (recFields D).K)))
    (hI : I.Ok Ch sel ξ cst (recGlob D mu0) (D.R.m - 2))
    (b : I.β (D.R.m - 2 + 1)) (hY : YbHyp (R := D.R) sel ξ cst I u (D.R.m - 2) b)
    (hK : KerEquivC (recWts EX) Ch sel ξ cst I A u (D.R.m - 2) b hY (rPsymF Ch))
    (hF : ∀ j, (chF (recWts EX) sel ξ I u j).Ok)
    (hP : (mtildeGSD (recWts EX) Ch sel ξ (rPsymF Ch)).Ok)
    (eM : (D.div.Nu u).V ≃ₗ[D.what₂.LL] MramV (recWts EX) Ch u)
    (jA : MtildeV (recWts EX) Ch sel ξ (rPsymF Ch) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ),
    cst.sharp = true ∧ TwistTieS Dx μ ξ ∧ FieldTieS sel A ξ cst u ∧ ColTie Ch u eM ∧ RowTieS Ch sel μ ξ jA ∧
      PerTieS Ch sel u μ ξ hP (colMu (recWts EX) Ch sel ξ cst I A u (D.R.m - 2) b hY (rPsymF Ch) hK hF hI) eM jA

theorem chainPeriodRelation_read_for_character_avoiding_primes (Dx : DivX D) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (A : Amb (recFields D))
    (u : D.what₂.Word) (μ : D.what₂.Tup) {S : Set ℕ} (χ : Chr (recFields D).F (recFields D).E (recFields D).K)
    (h : IsTwist (recFields D).F (recFields D).E (recFields D).K S χ)
    (h' : IsTwist (recFields D).F (recFields D).E (recFields D).K (badS D) χ)
    (H : ChainTieS Ch sel Dx mu0 A u μ (@Subtype.mk _ (IsTwist _ _ _ S) χ h)) : ChainTie Ch sel Dx mu0 A u μ := by
  obtain ⟨cst, I, hI, b, hY, hK, hF, hP, eM, jA, h1, h2, h3, h4, h5, h6⟩ := H
  exact ⟨@Subtype.mk _ (IsTwist _ _ _ (badS D)) χ h', cst, I, { hI with }, b, ⟨hY.fin⟩, hK, hF, hP, eM, jA, h1,
    ⟨h2.1, fun e => Subtype.ext (h2.2 e)⟩, h3, h4, h5, h6⟩

theorem chainTie_of (Dx : DivX D) (mu0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (A : Amb (recFields D))
    (u : D.what₂.Word) (μ : D.what₂.Tup) {S : Set ℕ} (ξ : Tup (recFields D).F (recFields D).E (recFields D).K S)
    (hξ : (ξ : Chr (recFields D).F (recFields D).E (recFields D).K) ∈
      tupGrp (recFields D).F (recFields D).E (recFields D).K (badS D))
    (H : ChainTieS Ch sel Dx mu0 A u μ ξ) : ChainTie Ch sel Dx mu0 A u μ := by
  obtain ⟨χ, h⟩ := ξ
  exact chainPeriodRelation_read_for_character_avoiding_primes Ch sel Dx mu0 A u μ χ h hξ H

end Gen

theorem colTie_of_addEquiv {D : D7} {EX : ErrX D} (Ch : Chars (recFields D) (recPrimes EX) D.R.m) (u : D.what₂.Word)
    (eM : (D.div.Nu u).V ≃+ MramV (recWts EX) Ch u) (hs : ∀ (r : D.what₂.LL) x, eM (r • x) = r • eM x)
    (h : ∀ x, x ∈ DV.MramL D u ↔ eM x ∈ MramL (recWts EX) Ch u) : ColTie Ch u (eM.toLinearEquiv hs) := h

theorem span_range_comp_eq_top {K V W U : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {σ : K →+* ℂ} (f : V →ₛₗ[σ] W) (e : W ≃ₗ[ℂ] U)
    (h : Submodule.span ℂ (Set.range f) = ⊤) : Submodule.span ℂ (Set.range (e.toLinearMap.comp f)) = ⊤ := by
  rw [LinearMap.coe_comp, Set.range_comp, Submodule.span_image, h, Submodule.map_top, LinearEquiv.range]

theorem perCol_eq {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws)
    (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) (u : B.Word) (a : (I.rec7 l Z).what₂.Tup)
    (eM : ((I.rec7 l Z).div.Nu u).V ≃+ MramV (Pr := B.primes X) B.wts I.Ch u)
    (heM3 : ∀ x, (I.rec7 l Z).nuIn u x = KerRat.colForm I l h u I.mu0 (eM x).1)
    (heM4 : ∀ a φ, (I.fm l u a).emb 0 (KerRat.colForm I l h u a φ) =
      (I.cols l).e0Tw u a ((I.fm l u I.mu0).emb 0 (KerRat.colForm I l h u I.mu0 φ)))
    (e : (I.per l u a).Mt ≃ₗ[ℂ] (I.rec7 l Z).what₂.Amb a)
    (he1 : a = (I.rec7 l Z).what₂.mu0 → HEq e ((I.rec7 l Z).eMt u))
    (he2 : a ≠ (I.rec7 l Z).what₂.mu0 → e = (I.rec7 l Z).eMtTw u a) (φ : ((I.rec7 l Z).div.Nu u).V)
    (z : MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps) :
    (I.rec7 l Z).what₂.perCol u a ((I.rec7 l Z).jN u φ) (e (KerRat.rowForm I l h u a z)) =
      (I.per l u a).PtilCol ((I.fm l u a).emb 0 (KerRat.colForm I l h u a (eM φ).1)) (KerRat.rowForm I l h u a z) := by
  have hj := (I.rec7 l Z).nuIn_jN u φ
  rw [heM3 φ] at hj
  by_cases ha : a = (I.rec7 l Z).what₂.mu0
  · subst ha
    have e1 : e = (I.rec7 l Z).eMt u := eq_of_heq (he1 rfl)
    rw [(I.rec7 l Z).perCol_base_eq_PtilCol u, hj, e1]
    erw [LinearEquiv.symm_apply_apply]
    rfl
  · rw [(I.rec7 l Z).perCol_tie u a ha, hj, he2 ha]
    erw [LinearEquiv.symm_apply_apply]
    exact congrArg (fun w => (I.per l u a).PtilCol w (KerRat.rowForm I l h u a z)) (heM4 a (eM φ).1).symm


set_option maxHeartbeats 40000000 in
theorem tiesAt_true : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (Z : GlobalTheory.Mem.Col2.TC.Later B (I.cols l)) (l0 : I.Law0 l), GlobalTheory.Mem.Col2.ColIn.JetsIn I → ∀ (EX : ErrX (I.rec7 l Z)) (Dx : DivX (I.rec7 l Z)) (a : I.ι), EX.piG = X.piG → EX.piT = X.piT → I.QpIs Dx.Qp → RowPin I h l Z a → TiesAt (I.rec7 l Z) EX Dx a := by
  intro B X I h l Z l0 hJ EX Dx a h1 h2 hQ hR
  change (I.rec7 l Z).what₂.Tup at a
  rw [← exOf_eq EX h1 h2]
  have hA : ambOf (recSeam (I.rec7 l Z)) (baseCast B.ccK_top.symm (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G)) I.chi I.J.cD = I.A :=
    (ambOf_baseCast _ _ _ _ _).trans (AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J I.chi).symm
  have hX := base_fields_primes_ok B X
  have hcc : TaylorLogMetric.IsCurveIdeal (I.rec7 l Z) ⊤ := ⟨top_ne_bot, by simp⟩
  have hδ := (I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 h.amb_ok
  have hχ : TaylorLogMetric.IsChi (I.rec7 l Z) I.chi := GlobalTheory.Mem.ChiIdeal.isChi_chiId _ _ I.C.isChi
  have hFL : KerRat.FamilyLaws I l Z := ⟨GlobalTheory.Mem.NatEqui.eqP _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ.1 hχ,
    (GlobalTheory.NatFamily.family _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ.1 hχ).1⟩
  have hFam := KerRat.kernels_rational I l Z h hJ (Or.inr (hFL))
  refine ⟨I.Ch, I.C.mu0, I.C.eta, I.sel, I.J.δ, baseCast B.ccK_top.symm (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G), I.chi, I.J.cD, ?_, ?_, ?_, fun u => ?_⟩
  · obtain ⟨c1, c2, c3, c4, -, -, c7, -⟩ := GlobalTheory.Core.Ht2.host_fields_primes_ties I h hX.1 l Z
    exact ⟨c1, c2, c3, c4, c7⟩
  · exact ⟨h.ch_ok, h.ch_tied, h.weil, h.sel_ok⟩
  · exact ⟨by rw [show (I.rec7 l Z).host.ccK = ⊤ from B.ccK_top]; exact hδ.1, hχ, hδ.2⟩
  · have hC : ∀ A : Amb B.fields, A = I.A → ChainTie (D := I.rec7 l Z) (EX := exOf EX h1 h2) I.Ch I.sel Dx I.C.mu0 A u a := by
      rintro A rfl
      obtain ⟨hne, hb⟩ := (hFam.1 u a).period
      obtain ⟨hY, hK, hF, hM, hper⟩ := hb hne.some
      obtain ⟨eM, heM1, heM2, heM3, heM4⟩ := GlobalTheory.T.ramifiedColumns_trueColumns_eq_concrete I h l Z l0 u
      obtain ⟨e, he1, he2, he3, he4⟩ := hR u
      let rE := GlobalTheory.PeriodOnStep.rowEmb (Pr := B.primes X) (I := I.chIn u a) B.wts I.Ch I.sel (I.tup a) I.Ps (I.perIn u a).b0
        (I.perIn u a).til (I.perIn u a).ext (I.perIn u a).tz (I.perIn u a).H (KerRat.tilOk I h u a).2.2 B.embLL
      have hrf : ⇑rE = KerRat.rowForm I l h u a := rfl
      refine chainTie_of (D := I.rec7 l Z) (EX := exOf EX h1 h2) I.Ch I.sel Dx I.C.mu0 I.A u a (I.tup a) (mem_tupGrp_of_subset (badS_subset h l Z) (I.tup a).2) ?_
      refine ⟨I.cst a, I.idx a, h.idx_ok a, hne.some, hY, hK, hF, hM, (show ((I.rec7 l Z).div.Nu u).V ≃+ MramV (recWts (exOf EX h1 h2)) I.Ch u from eM).toLinearEquiv heM1, LinearMap.comp (σ₁₃ := B.embLL) e.toLinearMap rE, h.sharp a, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨?_, fun e0 => by rw [e0]; exact congrArg Subtype.val I.trueColumn_tuple_trivial_eq_one⟩
        have hfin : (Qprime (I.tup a : Chr B.fields.F B.fields.E B.fields.K)).Finite :=
          GlobalTheory.OpenChrRam.qprime_finite _ _ _ _ (I.tup a).2.1.1.1.1.2
        ext p
        rw [Finset.mem_coe, hQ a p]
        constructor
        · rintro ⟨hp, P, hP, hpP⟩
          obtain ⟨v, hv, rfl, -⟩ := I.exists_of_mem_Q hP
          refine ⟨v, hv, ?_⟩
          have := (GlobalTheory.Mem.ReadTwist.plc_under_eq_iff (F := B.host.F) (I.sel v) hp).2 hpP
          rwa [GlobalTheory.Mem.LevTwist.under_sel h v] at this
        · rintro ⟨v, hv, rfl⟩
          have hmem : I.sel v ∈ I.Q a := by
            classical
            unfold ColIn.Q QE
            rw [dite_eq_left hfin]
            convert Finset.mem_image_of_mem I.sel (hfin.mem_toFinset.2 hv)
          have hu := (GlobalTheory.Mem.ReadTwist.plc_under_eq_iff (F := B.host.F) (I.sel v) (Formalism.L2.DIV.plc_prime' v)).1
          rw [GlobalTheory.Mem.LevTwist.under_sel h v] at hu
          exact ⟨Formalism.L2.DIV.plc_prime' v, I.sel v, hmem, hu rfl⟩
      · exact fun i hi => hJ a u i hi
      · exact colTie_of_addEquiv (EX := exOf EX h1 h2) I.Ch u eM heM1 heM2
      · obtain ⟨r1, r2⟩ := GlobalTheory.T.rowForms_coefficientField_form_complexPeriodRows I h l u a
        refine ⟨fun s hs => (r1 s hs).map' e.toLinearMap e.ker, span_range_comp_eq_top rE e r2, fun v hv => ?_, he4⟩
        obtain ⟨z, hz⟩ := he3 v hv
        exact ⟨z, hz⟩
      · intro φ x
        exact (perCol_eq I h l Z u a eM heM3 heM4 e he1 he2 φ x).trans (hper (eM φ).1 x)
    exact hC _ hA

end GlobalTheory.TiesTrue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceSubgroupMemLevelTwistPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.TwistCong

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem sclLat_zero (q N : ℕ) : LocE.sclLat P q N (fun _ => 0) = stdAt E N P := by
  ext x
  rw [CongLevel.mem_sclLat, mem_stdAt]
  simp

theorem lamY_zero (q n c : ℕ) : LocE.lamY P q n c 0 = stdAt E (n + c) P := by
  have e : LocE.scE n 0 = fun _ => (0 : ℤ) := by
    funext l
    unfold LocE.scE
    split_ifs <;> simp
  unfold LocE.lamY
  rw [e, sclLat_zero]

theorem inX_mem_std {n : ℕ} (c : ℕ) {x : Sp E n} (hx : x ∈ stdAt E n P) : Loc.inX E n c x ∈ stdAt E (n + c) P := by
  refine mem_stdAt.2 fun l => ?_
  rw [CongLevel.inX_apply]
  split_ifs
  · exact mem_stdAt.1 hx _
  · exact intAt_zero

theorem resX_mem_std {n : ℕ} (c : ℕ) {v : Sp E (n + c)} (hv : v ∈ stdAt E (n + c) P) :
    CongLevel.resX c v ∈ stdAt E n P :=
  mem_stdAt.2 fun i => mem_stdAt.1 hv (Fin.castAdd c i)

theorem stab_of_cong {N : ℕ} (g : Sp E N ≃ₗ[E] Sp E N)
    (hg : ∀ x ∈ stdAt E N P, ((qOf P : ℕ) : E)⁻¹ • (g x - x) ∈ stdAt E N P)
    (hg' : ∀ x ∈ stdAt E N P, ((qOf P : ℕ) : E)⁻¹ • (g⁻¹ x - x) ∈ stdAt E N P) : g ∈ stabL E N (stdAt E N P) := by
  have hq := qOf_ne_zero (P := P)
  have maps : ∀ f : Sp E N ≃ₗ[E] Sp E N, (∀ x ∈ stdAt E N P, ((qOf P : ℕ) : E)⁻¹ • (f x - x) ∈ stdAt E N P) →
      ∀ x ∈ stdAt E N P, f x ∈ stdAt E N P := by
    intro f hf x hx
    have e : f x = x + ((qOf P : ℕ) : E) • (((qOf P : ℕ) : E)⁻¹ • (f x - x)) := by
      rw [smul_smul, mul_inv_cancel₀ hq, one_smul, add_sub_cancel]
    rw [e]
    exact add_mem hx (smul_mem_locP (intAt_nat _) (hf x hx))
  intro x
  refine ⟨fun hx => ?_, maps g hg x⟩
  have := maps g⁻¹ hg' _ hx
  rwa [show g⁻¹ (g x) = x from LinearEquiv.symm_apply_apply _ x] at this

theorem conj_extE_cong {n c : ℕ} (j D : ℕ) (hjD : j + 1 ≤ D) (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c))
    (hb : ∀ x ∈ stdAt E (n + c) P, h⁻¹ x ∈ stdAt E (n + c) P ∧ (((qOf P : ℕ) : E) ^ j) • h x ∈ stdAt E (n + c) P)
    (κ : Sp E n ≃ₗ[E] Sp E n) (hκ : ∀ y ∈ stdAt E n P, (((qOf P : ℕ) : E) ^ D)⁻¹ • (κ y - y) ∈ stdAt E n P) :
    ∀ x ∈ stdAt E (n + c) P, ((qOf P : ℕ) : E)⁻¹ • ((h⁻¹ * CongLevel.extE c κ * h) x - x) ∈ stdAt E (n + c) P := by
  intro x hx
  have hq := qOf_ne_zero (P := P)
  set q : E := ((qOf P : ℕ) : E) with hqdef
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjD
  have hy := (hb x hx).2
  set y := q ^ j • h x with hydef
  have hhx : h x = (q ^ j)⁻¹ • y := by
    rw [hydef, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hq), one_smul]
  have hres := resX_mem_std c hy
  have hk := hκ _ hres
  have e1 : (h⁻¹ * CongLevel.extE c κ * h) x - x = h⁻¹ (CongLevel.extE c κ (h x) - h x) := by
    rw [map_sub]
    show h.symm (CongLevel.extE c κ (h x)) - x = h.symm (CongLevel.extE c κ (h x)) - h.symm (h x)
    rw [LinearEquiv.symm_apply_apply]
  have e2 : CongLevel.extE c κ (h x) - h x =
      Loc.inX E n c ((q ^ j)⁻¹ • (κ (CongLevel.resX c y) - CongLevel.resX c y)) := by
    rw [CongLevel.extE_apply, add_sub_cancel_left, hhx, map_smul, map_smul, smul_sub]
  have e3 : q⁻¹ • (q ^ j)⁻¹ • (κ (CongLevel.resX c y) - CongLevel.resX c y) =
      q ^ d • ((q ^ (j + 1 + d))⁻¹ • (κ (CongLevel.resX c y) - CongLevel.resX c y)) := by
    rw [smul_smul, smul_smul]
    congr 1
    field_simp
    ring
  rw [e1, e2, ← map_smul, ← map_smul, e3]
  refine (hb _ (inX_mem_std c ?_)).1
  exact smul_mem_locP (intAt_pow (intAt_nat _) d) hk

theorem entry_cong {N : ℕ} (g : Sp E N ≃ₗ[E] Sp E N)
    (hg : ∀ x ∈ stdAt E N P, ((qOf P : ℕ) : E)⁻¹ • (g x - x) ∈ stdAt E N P) (l i : ℕ) (hl : l < N) (hi : i < N) :
    IntAt P (Loc.atN (g (Loc.eN E N l)) i) ∧ redP P (Loc.atN (g (Loc.eN E N l)) i) = if i = l then 1 else 0 := by
  have hq := qOf_ne_zero (P := P)
  have he : Loc.eN E N l ∈ stdAt E N P := mem_stdAt.2 fun m => by
    unfold Loc.eN
    split_ifs
    · exact intAt_one
    · exact intAt_zero
  have hy := mem_stdAt.1 (hg _ he) ⟨i, hi⟩
  have e : g (Loc.eN E N l) = Loc.eN E N l + ((qOf P : ℕ) : E) • (((qOf P : ℕ) : E)⁻¹ • (g (Loc.eN E N l) - Loc.eN E N l)) := by
    rw [smul_smul, mul_inv_cancel₀ hq, one_smul, add_sub_cancel]
  have ee : Loc.atN (g (Loc.eN E N l)) i = (if i = l then (1 : E) else 0) +
      ((qOf P : ℕ) : E) * (((qOf P : ℕ) : E)⁻¹ • (g (Loc.eN E N l) - Loc.eN E N l)) ⟨i, hi⟩ := by
    conv_lhs => rw [e]
    unfold Loc.atN
    rw [dite_eq_left hi]
    simp [Loc.eN]
  have h1 : IntAt P (if i = l then (1 : E) else 0) := by
    split_ifs
    · exact intAt_one
    · exact intAt_zero
  have h2 := (intAt_nat (P := P) (qOf P)).mul hy
  rw [ee]
  refine ⟨h1.add h2, ?_⟩
  rw [reduction_add h1 h2, reduction_mul (intAt_nat _) hy, reduction_absNorm_eq_zero, zero_mul, add_zero]
  split_ifs
  · exact reduction_one₂
  · exact reduction_zero

end Lat


open GlobalTheory.TopStep in
theorem cong_mem_prCat_twist : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ},
    X.Ok → Pr.Ok → L.Ok Ch sel mu cst G m2 → ∀ {j : ℕ}, j ≤ m2 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
    ∀ C : GLint X.E (R.N j) P.1, C ∈ GlobalTheory.TopStep.prinCong (R.N j) P.1 (cst.D P) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (C.1 x)) ∧
        chiInv Ch sel mu cst j P (L.h j b P) r = 1 := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hL j hj b P hP C hC
  have hq := qOf_ne_zero (P := P.1)
  have hstd : lamYat (Pr := Pr) (R := R) j P.1 = stdAt X.E (R.N j + cOf R j) P.1 := by
    unfold lamYat
    rw [if_neg hP]
    exact lamY_zero _ _ _
  have hD : j + 1 ≤ cst.D P := by
    have h1 := hL.depthQ' P hP
    have h2 := hL.hm
    omega
  have hb : ∀ x ∈ stdAt X.E (R.N j + cOf R j) P.1, (L.h j b P)⁻¹ x ∈ stdAt X.E (R.N j + cOf R j) P.1 ∧
      (((qOf P.1 : ℕ) : X.E) ^ j) • (L.h j b P) x ∈ stdAt X.E (R.N j + cOf R j) P.1 := by
    intro x hx
    rw [← hstd] at hx ⊢
    exact hL.boundQ j b P hP x hx
  have hκ : ∀ y ∈ stdAt X.E (R.N j) P.1, (((qOf P.1 : ℕ) : X.E) ^ cst.D P)⁻¹ • (C.1 y - y) ∈ stdAt X.E (R.N j) P.1 :=
    mem_prinCong.1 hC
  have hκ' : ∀ y ∈ stdAt X.E (R.N j) P.1, (((qOf P.1 : ℕ) : X.E) ^ cst.D P)⁻¹ • (C.1⁻¹ y - y) ∈ stdAt X.E (R.N j) P.1 := by
    intro y hy
    have h0 := mem_prinCong.1 (inv_mem hC) y hy
    rwa [Subgroup.coe_inv] at h0
  have hg := conj_extE_cong j (cst.D P) hD (L.h j b P) hb C.1 hκ
  have hg' : ∀ x ∈ stdAt X.E (R.N j + cOf R j) P.1, ((qOf P.1 : ℕ) : X.E)⁻¹ •
      (((L.h j b P)⁻¹ * CongLevel.extE (cOf R j) C.1 * L.h j b P)⁻¹ x - x) ∈ stdAt X.E (R.N j + cOf R j) P.1 := by
    have e : ((L.h j b P)⁻¹ * CongLevel.extE (cOf R j) C.1 * L.h j b P)⁻¹ =
        (L.h j b P)⁻¹ * CongLevel.extE (cOf R j) C.1⁻¹ * L.h j b P := by
      rw [← CongLevel.extE_inv]
      group
    rw [e]
    exact conj_extE_cong j (cst.D P) hD (L.h j b P) hb C.1⁻¹ hκ'
  have hs := stab_of_cong _ hg hg'
  refine ⟨CongLevel.extE (cOf R j) C.1, ⟨CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ C.1, ?_⟩, CongLevel.extE_inX _ C.1, ?_⟩
  · have e : (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (CongLevel.extE (cOf R j) C.1) =
        (L.h j b P)⁻¹ * CongLevel.extE (cOf R j) C.1 * L.h j b P := by simp
    show (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (CongLevel.extE (cOf R j) C.1) ∈ Jat (Pr := Pr) cst.sharp j P.1
    rw [e]
    unfold Jat
    rw [if_neg hP]
    refine ⟨hs, ?_⟩
    have ep : LocE.parL P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j) =
        LocE.sclLat P.1 (qOf P.1) (R.N j + cOf R j)
          (fun l => (fun _ => (0 : ℤ)) l + if R.k + j ≤ l ∧ l < R.N j then 1 else 0) := by
      simp only [LocE.parL, zero_add]
    have hM : ∀ _s : ℕ, LocE.parL P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j) ≤ stdAt X.E (R.N j + cOf R j) P.1 := by
      intro _
      rw [ep, ← sclLat_zero (P := P.1) (qOf P.1)]
      exact CongLevel.sclLat_le P.1 (qOf P.1) hq _ (fun _ => 0) (fun l => R.k + j ≤ l ∧ l < R.N j)
    have hM' : ∀ (_s : ℕ) (x : Sp X.E (R.N j + cOf R j)), ((qOf P.1 : ℕ) : X.E)⁻¹ • x ∈ stdAt X.E (R.N j + cOf R j) P.1 →
        x ∈ LocE.parL P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j) := by
      intro _ x hx
      rw [ep]
      rw [← sclLat_zero (P := P.1) (qOf P.1)] at hx
      exact CongLevel.smul_mem_sclLat P.1 (qOf P.1) hq _ (fun _ => 0) (fun l => R.k + j ≤ l ∧ l < R.N j) x hx
    exact (CongLevel.mem_flagU (qOf P.1) (stdAt X.E (R.N j + cOf R j) P.1)
      (fun _ => LocE.parL P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j)) (fun _ => 0) 0 Set.univ hM hM'
      (fun _ => zero_mem _) _ hs hg).1 0 trivial
  · unfold chiInv
    have hn : Loc.n1Arg (CongLevel.extE (cOf R j) C.1) = 0 := by
      unfold Loc.n1Arg
      refine Finset.sum_eq_zero fun i _ => ?_
      have e : CongLevel.extE (cOf R j) C.1 (Loc.eN X.E (R.N j + cOf R j) (R.N j + i + 1)) =
          Loc.eN X.E (R.N j + cOf R j) (R.N j + i + 1) := by
        rw [show R.N j + i + 1 = R.N j + (i + 1) by ring, CongLevel.extE_apply, CongLevel.resX_eN]
        simp
      rw [e]
      unfold Loc.atN
      split_ifs with h1
      · simp [Loc.eN]
      · rfl
    rw [hn, hL.cst_ok.psi_int P 0 intAt_zero, inv_one, one_mul]
    unfold lamRow
    rw [if_neg hP]
    unfold LocE.lamQB
    rw [GlobalTheory.LamRowCong.unitV_det_eq_one, inv_one]
    · intro s t
      have := s.2
      have := t.2
      exact (entry_cong _ hg (R.k + j + t.1) (R.k + j + s.1) (by omega) (by omega)).1
    · ext s t
      have := s.2
      have := t.2
      rw [Matrix.map_apply, Matrix.one_apply]
      show redP P.1 (Loc.atN (((L.h j b P)⁻¹ * CongLevel.extE (cOf R j) C.1 * L.h j b P)
        (Loc.eN X.E (R.N j + cOf R j) (R.k + j + t.1))) (R.k + j + s.1)) = _
      rw [(entry_cong _ hg (R.k + j + t.1) (R.k + j + s.1) (by omega) (by omega)).2]
      by_cases hst : s = t
      · subst hst
        simp
      · rw [if_neg (fun e => hst (Fin.ext (by omega))), if_neg hst]

end GlobalTheory.TwistCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowPinSetDivZ
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Col2 NumberField

set_option maxHeartbeats 1000000

namespace GlobalTheory.AtG

theorem rowPin_setDivZ : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (ht : B.Word → ℝ) (a : (I.rec7 l Z).what₂.Tup), GlobalTheory.AtG.RowPin I h l Z a → GlobalTheory.AtG.RowPin I h l (GlobalTheory.Mem.Db.setDivZ Z N ht) a := by
  intro B X I h l Z N ht a hp
  exact hp

end GlobalTheory.AtG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroChartOfMemberLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroChart_of_memberLevel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClsTied (D := (I.rec7 l Z)) u 0 (Nat.zero_le _)) (κ : (I.stp u I.mu0 0).Cl → K.lev.U), (∀ c s, (K.stabI c s).1 = (I.stp u I.mu0 0).gam c.1 s.1) → ∃ K0 : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), (K0 ()).lev.Lb = K.lev.Lb ∧ (K0 ()).lev.Uloc = K.lev.Uloc ∧ (K0 ()).lev.U = K.lev.U ∧ (∀ (x : (K0 ()).lev.U) (x' : K.lev.U), x.1 = x'.1 → (K0 ()).lev.chi x = K.lev.chi x') ∧ (∀ c, ((K0 ()).y ⟨I.eCls0 l u a c, rfl⟩).1 = (K.y c).1 * (κ c).1) ∧ ∀ c s, ((K0 ()).stabI c s).1 = (I.stp u a 0).gam c.1.1 s.1 := by
  first | exact @GlobalTheory.TwU.AtTrue.ZeroChart.chart_of_member | exact GlobalTheory.TwU.AtTrue.ZeroChart.chart_of_member | (intros; apply GlobalTheory.TwU.AtTrue.ZeroChart.chart_of_member <;> assumption)
end

