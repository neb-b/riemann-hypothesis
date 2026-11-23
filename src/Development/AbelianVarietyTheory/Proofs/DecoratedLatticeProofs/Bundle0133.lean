module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.LocalOrderMatrix
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
public import Formalism.LocalToGlobal.Columns.ChainOneOk
public import Formalism.LocalToGlobal.Columns.RowFormsLemmas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0126
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralBasisOfLatticeAtPlaceStable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdditiveCharacterOneNe
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.MatchCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
open GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix

theorem isOrd_ordX (R : Ranks) (j : ℕ) : IsOrd xPos (ordX R j) := by
  rintro ((i | i) | ⟨i, l⟩)
  · rfl
  · rfl
  · rw [ordX_d]; simp only [xPos]; ring

section Concl
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ι : X.E →+* k) {s : ℕ} (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

end Concl

section Arith
variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Arith

section Hyp
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (ι : X.E →+* k) {s : ℕ} (S : SymData k s R.k)

end Hyp

section Trunc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

end Trunc

section Ext
variable {E K K' : Type} [Field E] [NumberField E] [StarRing E] [Field K] [Field K'] (φ : K →+* K')
  {P : HeightOneSpectrum (𝓞 E)}

end Ext

section Reparam
variable (X : Fields) (K' : Type) [Field K'] [NumberField K']

abbrev extFields : Fields where
  F := X.F
  E := X.E
  K := K'
  starK := starRingOfComm
  Tau := Empty
  emb := Empty.elim

def onePrimes (π : 𝓞 X.E) : Primes (extFields X K') where
  cond := 0
  g := 0
  piG := fun _ => X.conjO π
  Word := Empty
  T := Empty.elim
  piT := Empty.elim

variable {X K'} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (φ : X.K →+* K') (π : 𝓞 X.E)

variable {π} {P : HeightOneSpectrum (𝓞 X.E)}

variable (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Tup X.F X.E X.K S₀)
  (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (z : K')

variable {P} (hP : P.1 ∈ Pr.vGs) (hs : cst.sharp = true) (hq : (qOf P.1 : X.E) ≠ 0) (hP' : P.1 ∈ (onePrimes X K' π).vGs)

end Reparam

end GlobalTheory.MatchCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryEveryPointHasCuspScaleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitary_every_point_has_cusp_scale : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ V : HSp D, Near θ V := by
  first | exact @GlobalTheory.CuspGeo.near | exact GlobalTheory.CuspGeo.near | (intros; apply GlobalTheory.CuspGeo.near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLevelStepFourierJacobiPeriodLink
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.UnfLink

theorem star_psi {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem heisO_at_zero' {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  have h : hO S T 0 w = 0 := by simp [hO]
  simp [heisO, symplOH, symplO, h]

theorem link : ∀ D : D7, LinkLaw D := by
  intro D ψ ρ B J s L' ζ' hz l φ Ξ hφ hΞ
  refine ⟨_root_.GlobalTheory.HandFam.handBF_isQuasiFam D ψ ρ B J s L' ζ' hz l φ Ξ hφ hΞ, fun G' => ?_⟩
  unfold JacLev.perAll JacLev.per fjAll fjSrcKer
  congr 1; funext h; congr 1; funext n
  have hk := _root_.GlobalTheory.Unf.fjKer_eq_om_apply D ψ J.W J.W₀ B.V₀ B.A B.L ρ J.d B.o B.ζ _ _ s.om₀ s.weil₀ Ξ hΞ
  obtain ⟨hp, hc⟩ := GlobalTheory.T.jacobiActions_match_through_linkMap D ρ ρ B L' ζ' hz l J.W J.W₀ J.d n.1 n.2
  simp only [fjAllFun, fjSrcKerFun, JacLev.ker, jacS, handBF, hk, Pi.smul_apply, smul_eq_mul, heisO_at_zero', hp, hc]
  rw [star_mul', star_star, star_psi s.weil₀.std]
  simp_rw [mul_left_comm (φ _) (ψ _)]
  rw [integral_const_mul]
  ring

end GlobalTheory.UnfLink
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjBesselCharacterIsUnfoldingThetaFunctionOfGra
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.CutChar

theorem exists_psiE_ne_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ s : AE D, psiE ψ s ≠ 1 := by
  intro D ψ hψ
  obtain ⟨x₀, hx₀⟩ := hψ.1.2.2.2
  set q : D.host.F := Algebra.trace D.host.F D.host.E 1 with hq
  have hq0 : q ≠ 0 := by
    rw [hq, ← map_one (algebraMap D.host.F D.host.E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
    exact_mod_cast (Module.finrank_pos (R := D.host.F) (M := D.host.E)).ne'
  refine ⟨(x₀ * algebraMap D.host.F (AF D.host.F) q⁻¹) • incA D 1, ?_⟩
  rw [psiE, map_smul, GlobalTheory.BesselChar.trace_incA, ← hq, smul_eq_mul, mul_assoc, ← map_mul,
    inv_mul_cancel₀ hq0, map_one, mul_one]
  exact hx₀

theorem vecB_norm_ne : ∀ (D : D7) (V₀ A L : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → star (vecB o ζ) ⬝ᵥ V₀.gram *ᵥ vecB o ζ ≠ 0 := by
  intro D V₀ A L o ζ hζ
  rw [vecB, Matrix.star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.isoB]
  exact hζ.2

theorem psi_qS_eq_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (W : HSp D) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), gramQ W x₀ = 0 → ∀ c : skewA D ρ, ψ (d.qS W c (rat x₀)) = 1 := by
  intro D ψ hψ V V₀ ρ d W x₀ hx₀ c
  have hg : adj (rat x₀) * (gA W * rat x₀) = 0 := by
    have h : x₀ᴴ * HSpace.gram W * x₀ = 0 := by rw [Matrix.mul_assoc]; exact hx₀
    rw [gram_rat W h, rat_zero]
  have hq := ((_root_.GlobalTheory.CentralGram.central D).1 V V₀ W ρ d).2.1 c (rat x₀)
  have h0 : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat x₀) = 0 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, hg, Matrix.transpose_zero, smul_zero]
  rw [HypDec.qS, hq, h0]
  simp

theorem conjBessel_isTh : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (W : HSp D) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), gramQ W x₀ = 0 → IsTh ψ B.d W x₀ fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) := by
  intro D ψ hψ ρ B W x₀ hx₀
  have hC := _root_.GlobalTheory.MixPer.charLaws D ψ hψ.1 B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  set z := vecB B.o B.ζ with hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact continuous_star.comp ((hC.1 z).comp continuous_subtype_val)
  · intro γ hγ hγN n hn
    rw [psiBes_mul B.d ψ 1 z hγN hn, hC.2.1 z γ hγ, one_mul]
  · intro c n hn
    rw [psiBes_mul B.d ψ 1 z (B.d.nC_mem_NFlag c) hn, psiBes_nC, one_mul,
      psi_qS_eq_one D ψ hψ B.V B.V₀ ρ B.d W x₀ hx₀ c, star_one, one_mul]
  · intro j a haj hai _
    obtain ⟨s, hs⟩ := exists_psiE_ne_one D ψ hψ
    have key : ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA B.V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D B.V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer B.V (B.d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum B.d z u = s := by
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt j.2) with h | h
      · exact _root_.GlobalTheory.TransvMid.exists_mid D B.V B.V₀ ρ B.d z j a haj hai h s
      · exact _root_.GlobalTheory.TransvLast.exists_transv_simpleSum_last D B.V B.V₀ ρ B.d z (vecB_norm_ne D B.V₀ B.A B.L B.o B.ζ B.line) j a haj hai h s
    obtain ⟨v, hv0, hvT, hv⟩ := key
    obtain ⟨u, hu⟩ := _root_.GlobalTheory.TransvAdelic.transv_unitary D B.V B.V₀ ρ B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a) v hv0
    obtain ⟨hfix, hus⟩ := hv u hu
    have huN : u ∈ Nfix B.d j :=
      ⟨_root_.GlobalTheory.TransvFlag.transv_mem_flagN D B.V B.V₀ ρ B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a) v hvT u hu, Subgroup.mem_iInf.2 hfix⟩
    have hval : psiBes ψ B.d 1 z u = psiE ψ s := by
      rw [psiBes, hus, map_one, one_mul]
    refine ⟨v, u, star (psiE ψ s), hv0, hu, huN, ?_, ?_⟩
    · intro h1
      apply hs
      have := congrArg star h1
      rwa [star_star, star_one] at this
    · intro n hn n' hn'
      have huF : u ∈ flagN B.d := huN.1
      rw [psiBes_mul B.d ψ 1 z (mul_mem hn huF) hn', psiBes_mul B.d ψ 1 z hn huF, hval,
        psiBes_mul B.d ψ 1 z hn hn']
      simp only [star_mul']
      ring

end GlobalTheory.Unf.CutChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ConjAdjWeil

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.PairLift

variable {D : D7}

theorem dagger_eq (S T : HSp D) (x : WO S T) : dagger S T x = adjO T S x := by
  simp only [dagger, adjO, giA, gA, adj, Matrix.mul_assoc]
  rfl

theorem cj_dagger (S T : HSp D) (f : WO S T → ℂ) : cj (dagger T S) f = dag S T f := by
  funext y; simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dag, dagger_eq]

theorem conjAdjoint_apply {S T : HSp D} (om : Rep S T) (g : GA D T) (h : GA D S) (f : WO T S → ℂ) :
    conjAdjoint om (g, h) f = dag S T (om (h, g) (dag T S f)) := by
  show cj (dagger T S) (om (h, g) (cj (dagger S T) f)) = _
  rw [cj_dagger, cj_dagger]

theorem chi_conj {χ : (AE D)ˣ →* Circle} {n : ℕ} (hR : ResEta D χ n) (y : (AE D)ˣ) :
    χ (Units.map (cA D).toMonoidHom y) = (χ y)⁻¹ := by
  obtain ⟨⟨η, hη⟩, hall⟩ := hR
  have hprod : y * Units.map (cA D).toMonoidHom y =
      idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) y) := by
    apply Units.ext
    rw [GlobalTheory.Mem.EtaTilde.idF_norm]
    rfl
  have h1 : χ y * χ (Units.map (cA D).toMonoidHom y) = 1 := by
    rw [← map_mul, hprod, hall η hη, hη.2.2.1, one_pow]
  exact eq_inv_of_mul_eq_one_right h1

theorem isSplitIdem_conj {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hε, by rw [cA_cA, add_comm, h3]⟩

theorem suppAt_conj {e : AE D} {V : HSp D} {g : GA D V} (h : SuppAt e V g) : SuppAt (cA D e) V g := by
  intro i j
  rw [cA_cA, add_comm]
  exact h i j

theorem det_inv_eq (V : HSp D) (g : GA D V) : (mt V g⁻¹).det = cA D (mt V g).det := by
  have h1 : (giA V).det * (gA V).det = 1 := by rw [← Matrix.det_mul, giA_mul_gA, Matrix.det_one]
  rw [mt_inv, Matrix.det_mul, Matrix.det_mul, adj, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
  linear_combination ((mt V g).map (cA D)).det * h1

theorem isDetAt_conj {e : AE D} (he : e * e = e) {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (hx : IsDetAt e V g x) :
    IsDetAt (cA D e) V g (Units.map (cA D).toMonoidHom x⁻¹) := by
  have hd : (mt V g⁻¹).det * (mt V g).det = 1 := by rw [← Matrix.det_mul, mt_inv_mul, Matrix.det_one]
  have hz : ((x⁻¹ : (AE D)ˣ) : AE D) = e * (mt V g⁻¹).det + (1 - e) := by
    apply Units.inv_eq_of_mul_eq_one_left
    rw [hx]
    linear_combination e * hd + ((mt V g⁻¹).det * (mt V g).det - (mt V g⁻¹).det - (mt V g).det + 1) * he
  show cA D ((x⁻¹ : (AE D)ˣ) : AE D) = cA D e * (mt V g).det + (1 - cA D e)
  rw [hz, map_add (f := _), map_mul, map_sub, map_one, det_inv_eq, cA_cA]

end GlobalTheory.ConjAdjWeil

namespace GlobalTheory.ConjAdjWeil

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.PairLift

theorem isWeilDatumO_conjAdjoint : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ T S χT χS (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint om) := by
  intro D ψ S T χS χT om hw
  have hS : AdjLaw ψ S T := GlobalTheory.AdjLawPf.adjLaw D ψ hw.std S T
  have hT : AdjLaw ψ T S := GlobalTheory.AdjLawPf.adjLaw D ψ hw.std T S
  have thB : ∀ f : WO T S → ℂ, IsThetaFunO ψ T S f → IsThetaFunO ψ S T (dag T S f) := hT.theta
  have thA : ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ T S (dag S T f) := hS.theta
  have key : ∀ (g : GA D T) (h : GA D S) (f : WO T S → ℂ),
      conjAdjoint om (g, h) f = dag S T (om (h, g) (dag T S f)) := fun g h f => conjAdjoint_apply om g h f
  have dd : ∀ f : WO T S → ℂ, dag S T (dag T S f) = f := fun f => by
    funext y; simp only [dag, hT.invol, Complex.conj_conj]
  have d0 : adjO S T 0 = 0 := by
    have := hS.add 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  have d0' : adjO T S 0 = 0 := by
    have := hT.add 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  refine ⟨hw.std, hw.hecT, hw.hecS, hw.resT, hw.resS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨g, h⟩ f hf
    rw [key]
    exact thA _ (hw.om_pres _ _ (thB f hf))
  · intro g h w₀ f hf
    have e1 : dag T S (heisO ψ T S w₀ f) = heisO ψ S T (adjO S T w₀) (dag T S f) := by
      rw [hT.Heisenberg₂, hT.invol]
    rw [key, key, e1, hw.om_heis _ _ _ _ (thB f hf), ← hS.act, ← hS.Heisenberg₂]
  · intro γ hγ γ' hγ' f hf
    rw [key]
    have := hw.om_aut γ' hγ' γ hγ (dag T S f) (thB f hf)
    simp only [dag] at this ⊢
    rw [d0, this, d0', Complex.conj_conj]
  · intro f hf w
    have e : (fun p : GA D T × GA D S => conjAdjoint om p f w) =
        fun p => starRingEnd ℂ (om (Prod.swap p) (dag T S f) (adjO S T w)) := by
      funext p
      obtain ⟨g, h⟩ := p
      rw [key]
      rfl
    rw [e]
    exact Complex.continuous_conj.comp ((hw.om_cont _ (thB f hf) _).comp continuous_swap)
  · intro μ 𝓕 hμ h𝓕 p f hf
    obtain ⟨g, h⟩ := p
    haveI : BorelSpace (WO S T) := ⟨rfl⟩
    haveI : BorelSpace (WO T S) := ⟨rfl⟩
    let dE : WO T S ≃+ WO S T :=
      { toFun := adjO S T, invFun := adjO T S, left_inv := hT.invol, right_inv := hS.invol, map_add' := hS.add }
    let hE : WO S T ≃ₜ WO T S :=
      { toFun := adjO T S, invFun := adjO S T, left_inv := hS.invol, right_inv := hT.invol,
        continuous_toFun := hT.cont, continuous_invFun := hS.cont }
    set ν : Measure (WO S T) := μ.map dE with hν
    have hνH : ν.IsAddHaarMeasure := dE.isAddHaarMeasure_map μ hS.cont hT.cont
    have hfm : Measurable (adjO T S) := hT.cont.measurable
    have hdm : Measurable (adjO S T) := hS.cont.measurable
    have hmp : MeasurePreserving (adjO T S) ν μ := by
      refine ⟨hfm, ?_⟩
      rw [hν, Measure.map_map hfm (show Measurable dE from hdm)]
      have : adjO T S ∘ dE = id := funext fun w => hT.invol w
      rw [this, Measure.map_id]
    have hemb : MeasurableEmbedding (adjO T S) := hE.measurableEmbedding
    have hfd : IsAddFundamentalDomain (ratL T S) (adjO T S ⁻¹' 𝓕) ν := by
      refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving
        (e := fun γ : ratL S T => (⟨adjO S T γ, (hS.rat γ).2 γ.2⟩ : ratL T S)) ⟨?_, ?_⟩ ?_
      · intro a b hab
        have := congrArg (fun z : ratL T S => adjO T S (z : WO S T)) hab
        simp only [hT.invol] at this
        exact Subtype.ext this
      · intro b
        refine ⟨⟨adjO T S b, (hT.rat b).2 b.2⟩, Subtype.ext ?_⟩
        exact hS.invol b
      · intro γ x
        show adjO T S (adjO S T (γ : WO T S) + x) = (γ : WO T S) + adjO T S x
        rw [hT.add, hT.invol]
    calc ∫⁻ w in 𝓕, ‖conjAdjoint om (g, h) f w‖ₑ ^ 2 ∂μ
        = ∫⁻ w in 𝓕, (fun z => ‖om (h, g) (dag T S f) z‖ₑ ^ 2) (adjO S T w) ∂μ := by
          congr 1
          funext w
          rw [key]
          simp [dag]
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, (fun z => ‖om (h, g) (dag T S f) z‖ₑ ^ 2) (adjO S T (adjO T S z)) ∂ν :=
          (hmp.setLIntegral_comp_preimage_emb hemb (fun w => (fun z => ‖om (h, g) (dag T S f) z‖ₑ ^ 2) (adjO S T w)) 𝓕).symm
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, ‖om (h, g) (dag T S f) z‖ₑ ^ 2 ∂ν := by simp only [hS.invol]
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, ‖dag T S f z‖ₑ ^ 2 ∂ν := hw.om_unit ν _ hνH hfd (h, g) _ (thB f hf)
      _ = ∫⁻ z in adjO T S ⁻¹' 𝓕, (fun w => ‖f w‖ₑ ^ 2) (adjO T S z) ∂ν := by
          congr 1
          funext z
          simp [dag]
      _ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := hmp.setLIntegral_comp_preimage_emb hemb (fun w => ‖f w‖ₑ ^ 2) 𝓕
  · intro e he g h hsg hsh x y hx hy
    obtain ⟨r, hr, hℓ⟩ := hw.om_split (cA D e) (isSplitIdem_conj he) h g (suppAt_conj hsh) (suppAt_conj hsg) _ _
      (isDetAt_conj he.1 hy) (isDetAt_conj he.1 hx)
    refine ⟨r, hr, fun ℓ hinv f hf => ?_⟩
    have dadd : ∀ a b : WO S T → ℂ, dag S T (a + b) = dag S T a + dag S T b := fun a b => by
      funext z; simp [dag]
    have dsmul : ∀ (c : ℂ) (a : WO S T → ℂ), dag S T (c • a) = starRingEnd ℂ c • dag S T a := fun c a => by
      funext z; simp [dag]
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun F => starRingEnd ℂ (ℓ (dag S T F))
        map_add' := fun a b => by simp only [dadd, map_add (f := _)]
        map_smul' := fun c a => by
          simp only [dsmul, map_smul, smul_eq_mul, map_mul, RingHom.id_apply, Complex.conj_conj] }
    have hinv' : ∀ u : WO S T, (∀ i j, cA D (cA D e) * u i j = u i j) → ∀ F, IsThetaFunO ψ S T F →
        ℓ' (heisO ψ S T u F) = ℓ' F := by
      intro u hu F hF
      have hu' : IsHalf e u := fun i j => by have := hu i j; rwa [cA_cA] at this
      have e2 : dag S T (heisO ψ S T u F) = heisO ψ T S (adjO T S u) (dag S T F) := by rw [hS.Heisenberg₂, hS.invol]
      show starRingEnd ℂ (ℓ (dag S T (heisO ψ S T u F))) = starRingEnd ℂ (ℓ (dag S T F))
      rw [e2, hinv _ (hT.half e u hu') _ (thA F hF)]
    have main := hℓ ℓ' hinv' (dag T S f) (thB f hf)
    have m2 : starRingEnd ℂ (ℓ (dag S T (om (h, g) (dag T S f)))) =
        (r : ℂ) * (splitFacO χS χT (Units.map (cA D).toMonoidHom y⁻¹) (Units.map (cA D).toMonoidHom x⁻¹) : ℂ) *
          starRingEnd ℂ (ℓ f) := by
      have := main
      simp only [ℓ', LinearMap.coe_mk, AddHom.coe_mk, dd] at this
      exact this
    have hconj := congrArg (starRingEnd ℂ) m2
    rw [Complex.conj_conj] at hconj
    have hfac : (splitFacO χS χT (Units.map (cA D).toMonoidHom y⁻¹) (Units.map (cA D).toMonoidHom x⁻¹))⁻¹ =
        splitFacO χT χS x y := by
      unfold splitFacO
      rw [chi_conj hw.resT, chi_conj hw.resS, map_inv, map_inv, inv_inv, inv_inv, _root_.mul_inv_rev, inv_inv]
    rw [key, hconj, map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal, ← Circle.coe_inv_eq_conj, hfac]

end GlobalTheory.ConjAdjWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnimodularBasisSelfDualLatticeAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.SDBasis

theorem exists_basis_unimodular : ∀ (D : D7) (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → IsSDAt S v Λ → ∃ β β' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, β i j ∈ idAt D (· = v)) ∧ (∀ i j, β' i j ∈ idAt D (· = v)) ∧ β * β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧ β' * β = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ∧ (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ intAt D (· = v))) ∧ (∀ i j, (adj β * (gA S * β)) i j ∈ intAt D (· = v)) ∧ (∀ i j, cA D ((adj β * (gA S * β)) i j) = (adj β * (gA S * β)) j i) ∧ ∃ H' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ adj β * (gA S * β) * H' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  intro D S v ε Λ hT hεε hcε hεO hε hΛ
  obtain ⟨β, β', hβ, hβ', h1, h2, h3⟩ :=
    _root_.GlobalTheory.IwaPlace.FreeAt.exists_basis D S.rank v ε Λ hT hεε hcε hεO hε hΛ.1 (_root_.GlobalTheory.IwaPlace.SDStable.smul_mem D S v Λ hΛ) hΛ.2.1 (_root_.GlobalTheory.IwaPlace.SDBound.exists_mul_mem_intAt D S v Λ hΛ)
  exact ⟨β, β', hβ, hβ', h1, h2, h3, _root_.GlobalTheory.IwaPlace.GramBasis.gram_basis D S v ε Λ β β' hεε hcε hεO hε hΛ hβ hβ' h1 h2 h3⟩

end GlobalTheory.IwaPlace.SDBasis
end

