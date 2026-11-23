module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0140
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParametersSpacingAndGap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleIdempotentMulIntegralOfUnitFactor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.UnitAtPl

open GlobalTheory.FinPlLoc (idem ePl evalV_ePl ePl_int idem_mem_idAt idem_mul_self finPart_pair)

variable {D : D7}

theorem evalV_inv_mem (x : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) (hc : c ∉ x.asIdeal) :
    evalV D.host.F x (algebraMap D.host.F (Af D.host.F) ((c : D.host.F))⁻¹) ∈ x.adicCompletionIntegers D.host.F := by
  rw [AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : x.intValuation c = 1 := HeightOneSpectrum.intValuation_eq_one_iff.2 hc
  have h2 := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) x c
  rw [h1] at h2
  show Valued.v ((((c : D.host.F))⁻¹ : D.host.F) : x.adicCompletion D.host.F) ≤ 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
  have : HeightOneSpectrum.valuation D.host.F x (c : D.host.F) = 1 := h2
  rw [this, inv_one]

theorem inv_ePl_int (x : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) (hc : c ∉ x.asIdeal) :
    ((c : D.host.F))⁻¹ • ePl D (· = x) ∈ intAf D.host.F := by
  intro w
  rw [Algebra.smul_def, map_mul, evalV_ePl]
  split_ifs with h
  · subst h; rw [mul_one]; exact evalV_inv_mem w c hc
  · rw [mul_zero]; exact zero_mem _

theorem tmul_one_mul_mem {γ : Af D.host.F} (hγ : γ ∈ intAf D.host.F) {w : Af D.host.F ⊗[D.host.F] D.host.E}
    (hw : w ∈ intAE D) : (γ ⊗ₜ[D.host.F] (1 : D.host.E)) * w ∈ intAE D := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    refine AddSubgroup.subset_closure ⟨γ * α, fun v => ?_, o, rfl⟩
    rw [map_mul]
    exact mul_mem (hγ v) (hα v)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem finPart_idem_inv (x : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) :
    finPart D (idem D (· = x) * incA D ((c : D.host.F) : D.host.E)⁻¹) =
      (((c : D.host.F))⁻¹ • ePl D (· = x)) ⊗ₜ[D.host.F] (1 : D.host.E) := by
  have h0 : idem D (· = x) * incA D ((c : D.host.F) : D.host.E)⁻¹ =
      pairA D.host.F 0 (ePl D (· = x)) ⊗ₜ[D.host.F] ((c : D.host.F) : D.host.E)⁻¹ := by
    change (pairA D.host.F 0 (ePl D (· = x)) ⊗ₜ[D.host.F] (1 : D.host.E)) *
      ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((c : D.host.F) : D.host.E)⁻¹) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h1 : ((c : D.host.F) : D.host.E)⁻¹ = ((c : D.host.F))⁻¹ • (1 : D.host.E) := by
    rw [Algebra.smul_def, map_inv₀, mul_one]; rfl
  rw [h0, finPart_pair, h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul']

theorem idem_mul_mem_of_unit : ∀ (D : D7) (v : GlobalTheory.FinPl.Pl D) (u : 𝓞 D.host.F), u ∉ v.asIdeal → ∀ z : AE D, GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((u : D.host.F) : D.host.E) * z ∈ intAt D (· = v) → GlobalTheory.FinPlLoc.idem D (· = v) * z ∈ intAt D (· = v) := by
  intro D v u hu z hz
  have hu0 : ((u : D.host.F) : D.host.E) ≠ 0 := by
    intro h
    apply hu
    have h' : (u : D.host.F) = 0 := by exact_mod_cast h
    have h'' : u = 0 := by exact_mod_cast h'
    rw [h'']; exact zero_mem _
  have hinc : incA D ((u : D.host.F) : D.host.E)⁻¹ * incA D ((u : D.host.F) : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hu0, map_one]
  have key : idem D (· = v) * z = (idem D (· = v) * incA D ((u : D.host.F) : D.host.E)⁻¹) *
      (idem D (· = v) * incA D ((u : D.host.F) : D.host.E) * z) := by
    calc idem D (· = v) * z = (idem D (· = v) * idem D (· = v)) *
        (incA D ((u : D.host.F) : D.host.E)⁻¹ * incA D ((u : D.host.F) : D.host.E)) * z := by
          rw [idem_mul_self, hinc, mul_one]
      _ = _ := by ring
  refine ⟨Ideal.mul_mem_right _ _ (idem_mem_idAt _), ?_⟩
  rw [key, (finPart D).map_mul, finPart_idem_inv]
  exact tmul_one_mul_mem (inv_ePl_int v u hu) hz.2

end GlobalTheory.UnitAtPl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleIdempotentSmulMemLatticeCompletionAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPlLoc

theorem idem_smul_mem_latMul_at : ∀ (D : D7) (S : HSp D) (𝔞 : Set D.host.E) (L : GlobalTheory.FinPl.Lat S) (v : GlobalTheory.FinPl.Pl D) (z : Fin S.rank → AE D), z ∈ GlobalTheory.FinPl.latMul S 𝔞 L (fun _ => True) → GlobalTheory.FinPlLoc.idem D (· = v) • z ∈ GlobalTheory.FinPl.latMul S 𝔞 L (· = v) := by
  intro D S 𝔞 L v z hz
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hαi, -, a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨ePl D (· = v) * α, fun w => ?_, fun w hw => ?_, a, ha, x, hx, ?_⟩
    · rw [map_mul]
      exact mul_mem (ePl_int _ w) (hαi w)
    · rw [map_mul, evalV_ePl, if_neg hw, zero_mul]
    · funext i
      rw [Pi.smul_apply, smul_eq_mul]
      unfold idem
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← pairA_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

end GlobalTheory.FinPlLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryWittIsotropicCoordinateEqPairing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.AscFin

theorem coeff_monic_poly_sum {K R : Type} [CommRing K] [CommRing R] (φ : K →+* R) {n : ℕ} (u s : K) (h : s * u = 1)
    (b : Fin n → K) (G : Matrix (Fin n) (Fin n) K) (x : Fin n → R) :
    φ u * ∑ l, φ (∑ k, (s * b k) * G k l) * x l = ∑ k, ∑ l, φ (b k) * φ (G k l) * x l := by
  have hus : φ u * φ s = 1 := by rw [← map_mul, mul_comm, h, map_one]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  linear_combination (φ (b k) * φ (G k l) * x l) * hus

private theorem cT_sig_eq_conjTranspose' {D : D7} {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M = Mᴴ := rfl

private theorem cA_incA_apply_eq_incA_star {D : D7} (e : D.host.E) : cA D (incA D e) = incA D (star e) := rfl

theorem incA_neg_xi0_pow_mul_pX_mulVec_eq_sum : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), c = 2 * ρ → IsAuxiliaryVectorWittDec a d → ∀ (i : Fin ρ) (hi : 2 * ρ - 1 - i.1 < c) (x : Fin B.rank → AE D), incA D ((-D.host.xi0) ^ (i.1 + 1)) * (d.pX *ᵥ x) i = ∑ k, ∑ l, cA D (incA D (a.a k ⟨2 * ρ - 1 - i.1, hi⟩)) * incA D (B.gram k l) * x l := by
  intro D A B B₀ c ρ a d hc hA i hi x
  obtain ⟨h2, he, s, he'⟩ := hA
  have hle : ρ ≤ c := by omega
  have hj : ∀ hle : ρ ≤ c, (Fin.castLE hle i).rev = (⟨2 * ρ - 1 - i.1, hi⟩ : Fin c) := fun hle => by
    ext
    simp only [Fin.val_rev, Fin.coe_castLE]
    omega
  have g1 := congrFun (congrFun a.gram ⟨2 * ρ - 1 - i.1, hi⟩) (Fin.castLE hle i)
  have g2 := congrFun (congrFun d.e'e i) i
  rw [he, he'] at g2
  simp only [antiDiagonalSignGramMatrix, cT_sig_eq_conjTranspose', Matrix.mul_apply, Matrix.conjTranspose_apply, colsOf, star_mul', Matrix.one_apply_eq, hj,
    Fin.coe_castLE] at g1 g2
  rw [if_pos (by omega), if_neg (fun h => by have := congrArg Fin.val h; simp only [Fin.coe_castLE] at this; omega)] at g1
  have g3 : ∑ l, (∑ k, star (s i) * star (a.a k ⟨2 * ρ - 1 - i.1, hi⟩) * HSpace.gram B k l) *
      ((-D.host.xi0) ^ (i.1 + 1) * a.a l (Fin.castLE hle i)) =
      star (s i) * (-D.host.xi0) ^ (i.1 + 1) *
        ∑ l, (∑ k, star (a.a k ⟨2 * ρ - 1 - i.1, hi⟩) * HSpace.gram B k l) * a.a l (Fin.castLE hle i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [mul_assoc (star (s i)), ← Finset.mul_sum]
    ring
  have key : star (s i) * (-D.host.xi0) ^ (i.1 + 1) = 1 := by
    linear_combination g2 - g3 - (star (s i) * (-D.host.xi0) ^ (i.1 + 1)) * g1
  simp only [HypDec.pX, HypDec.qX, GlobalTheory.MixModel.rat, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, he', colsOf, star_mul', hj, cA_incA_apply_eq_incA_star]
  exact coeff_monic_poly_sum (incA D) _ _ key (fun k => star (a.a k ⟨2 * ρ - 1 - i.1, hi⟩)) (HSpace.gram B) x

end GlobalTheory.AscFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLevelUnfoldingCharacterAndFlatMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc.FromBes

theorem conjBessel_isTh (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (ρ : ℕ) (B : BesL D ρ) (W : HSp D)
    (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (hx₀ : gramQ W x₀ = 0) :
    IsTh ψ B.d W x₀ fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) := by
  have hC := _root_.GlobalTheory.MixPer.charLaws D ψ hψ.1 B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  set z := vecB B.o B.ζ with hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact continuous_star.comp ((hC.1 z).comp continuous_subtype_val)
  · intro γ hγ hγN n hn
    rw [psiBes_mul B.d ψ 1 z hγN hn, hC.2.1 z γ hγ, one_mul]
  · intro c n hn
    rw [psiBes_mul B.d ψ 1 z (B.d.nC_mem_NFlag c) hn, psiBes_nC, one_mul,
      GlobalTheory.Unf.CutChar.psi_qS_eq_one D ψ hψ B.V B.V₀ ρ B.d W x₀ hx₀ c, star_one, one_mul]
  · intro j a haj hai _
    obtain ⟨s, hs⟩ := GlobalTheory.Unf.CutChar.exists_psiE_ne_one D ψ hψ
    have key : ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA B.V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D B.V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer B.V (B.d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum B.d z u = s := by
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt j.2) with h | h
      · exact _root_.GlobalTheory.TransvMid.exists_mid D B.V B.V₀ ρ B.d z j a haj hai h s
      · exact _root_.GlobalTheory.TransvLast.exists_transv_simpleSum_last D B.V B.V₀ ρ B.d z (GlobalTheory.Unf.CutChar.vecB_norm_ne D B.V₀ B.A B.L B.o B.ζ B.line) j a haj hai h s
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

theorem fl_eq_flBF (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J)
    (Ψ : WO B.V J.W → ℂ) (hΨ : IsThetaFunO ψ B.V J.W Ψ) :
    fl ψ B.d J.W s.vS s.vT s.vU (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d) Ψ = flBF s Ψ 0 := by
  have hψ : IsStdChar D ψ (-1) := s.weil.std
  have hf : ∀ x, IsThetaFunO ψ B.V₀ J.W (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ x) := fun x =>
    (_root_.GlobalTheory.MixValues.mixed_values D ψ hψ).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  unfold fl flBF flatS flatAt
  congr 1
  funext u
  have hu : ∀ b, star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b * B.d.levi u.1)) =
      star (psiUni ψ u.1) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b)) := by
    intro b
    rw [psiBes_mul B.d ψ 1 _ (B.d.nB_mem_NFlag b) (B.d.levi_mem_NFlag (mem_UX.1 u.2)), psiBes_levi, star_mul',
      mul_comm]
  unfold flFun flatFun evalAt
  simp_rw [hu, mul_assoc]
  rw [integral_const_mul]
  congr 1
  congr 1
  funext b
  exact GlobalTheory.Unf.StepFour.integrand_eq hψ B.d J.d _ _ (hf _) b

theorem isTh_and_fl : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), IsTh ψ B.d J.W J.d.e (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) ∧ ∀ Ψ, IsThetaFunO ψ B.V J.W Ψ → fl ψ B.d J.W s.vS s.vT s.vU (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d) Ψ = flBF s Ψ 0 := by
  intro D ψ ρ B J s
  exact ⟨conjBessel_isTh D ψ s.weil.std ρ B J.W J.d.e (gramQ_e J.d), fun Ψ hΨ => fl_eq_flBF D ψ ρ B J s Ψ hΨ⟩

end GlobalTheory.Asc.FromBes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodAscentOfTowerRungs
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc

theorem ascent_of_rungs : TowerEx → Rung0 → RungB → RungJ → Ascent := by
  intro hT h0 hB hJ D hq T L μ0 hL sc G W M hM v Ψ hΨ u hu hper
  obtain ⟨F, hE, ΓL, hG⟩ := hT D hq T L μ0 hL sc G W M hM v
  have key : ∀ k (h : 2 * k + 2 ≤ D.R.m), NZB W M v F Ψ u k h := by
    intro k
    induction k with
    | zero =>
      intro h
      exact hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu 0 h
        (h0 D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hper h)
    | succ k ih =>
      intro h
      have h' : 2 * k + 2 ≤ D.R.m := by omega
      exact hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu (k + 1) h
        (hJ D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu k h h' (ih h'))
  obtain ⟨r, hr⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  have hk : 2 * (r - 1) + 2 ≤ D.R.m := by omega
  have hk' : 2 * (r - 1) + 2 = D.R.m := by omega
  obtain ⟨ρ, Φ, hne⟩ := key (r - 1) hk
  refine ⟨ρ, Φ, ?_⟩
  let f : ∀ i, Fn G (.grid i 0) := fun i => if hi : i ≤ D.R.m then part W M ρ Φ u i hi else 0
  have hf : f D.R.m = thetaChi W M ρ Φ u := by
    simp only [f, dif_pos le_rfl]; rfl
  have := hE.top (r - 1) hk hk' Ψ f (hΨ.1 _ le_rfl) (by rw [hf, ← part_m]; exact hu ρ Φ _ le_rfl) (by
    simp only [f, dif_pos hk]; exact hne)
  rwa [hf] at this

end GlobalTheory.Asc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingHypothesesGridParametersLargeScale
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

private theorem dualPar_dualPar' (S : SPar) : dualPar (dualPar S) = S := by
  unfold dualPar
  rw [Finset.image_image]
  simp [Function.comp_def]

private theorem shift_zero_lemma_2 (S : SPar) : GlobalTheory.SignedHC.shift 0 S = S := by
  unfold GlobalTheory.SignedHC.shift
  simp

private theorem exists_par_of_gridData_bounds {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {ε : Fin (n + 1) → Bool}
    {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ} {B : ℝ}
    (hke : Even G.k) (hme : Even G.m) (hm2 : 2 ≤ G.m) (hn : n + 1 = G.k + G.m) (h3 : 3 ≤ n)
    (hv : ∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) (hvk : 2 ≤ G.v G.k + G.b 1)
    (hb : ∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + 1000 * ((n : ℝ) + 1) ^ 3 ≤ G.b (l + 1))
    (hga : 1000 * ((n : ℝ) + 1) ^ 3 ≤ G.ga) (hvk0 : 0 ≤ G.v G.k) (hb1 : 0 < G.b 1)
    (ha0 : ((G.a 0 : ℚ) : ℝ) ≤ B) (hbm : (G.b G.m : ℝ) ≤ B)
    (hl : IsEnum (G.parPi 0) lam ε) (hm : IsEnum G.parD0 mu ε') :
    ∃ e, GlobalTheory.SepReal.Par e ε lam ε' mu B := by
  have hga0 : 0 < G.ga := by
    have h0 : (0 : ℝ) < 1000 * ((n : ℝ) + 1) ^ 3 := by positivity
    exact_mod_cast h0.trans_le hga
  have hH : (2 : ℝ) ≤ 1000 * ((n : ℝ) + 1) ^ 3 := by
    have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    linarith
  have hvk1 : 1 ≤ G.v G.k + G.b 1 := by omega
  obtain ⟨hc, hc'⟩ := GlobalTheory.T.card_minus_signs_half_of_even hme hga0 hl hm
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_signsMatchBranchingCoordinate_equiv ε ε' (hc.trans hc'.symm)
  obtain ⟨hHl, hHm⟩ := _root_.GlobalTheory.HCEnum.isHCParam_parPi_zero_parD0 hke hme hn hl hm
  have hw := _root_.GlobalTheory.SignedHC.GridData.interlaced_pi_zero_and_D0 hga0 hvk1 hl hm
  obtain ⟨hs1, hs2⟩ := _root_.GlobalTheory.WordSep.word_sep hga0 hv (by omega) hl hm
  obtain ⟨hwl, hwm, hgl, hgm⟩ := _root_.GlobalTheory.SignedHC.GridData.pi_zero_and_D0_spacing hH hga hv hvk hb hl hm
  have habs : ∀ a c, a ≠ c → 2 ≤ |lam a - lam c| := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h | h
    · exact (hwl a c h).trans (le_abs_self _)
    · rw [abs_sub_comm]
      exact (hwl c a h).trans (le_abs_self _)
  have hB := _root_.GlobalTheory.Twist.parPi_parD0_entries_bounded hvk0 hb1 ha0 hbm hl hm
  have hk2 := G.two_le_k
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => ε' i = false)
  have hneg : ∃ i, ε' i = false := by
    have hpos : 0 < (Finset.univ.filter fun i => ε' i = false).card := by
      rw [hc']
      omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  have hpos : (Finset.univ.filter fun i => ε' i = false).card ≤ (Finset.univ.filter fun i => ε' i = true).card := by
    have heq : (Finset.univ.filter fun i => ¬ ε' i = false) = Finset.univ.filter fun i => ε' i = true := by
      ext i
      simp
    rw [heq, Finset.card_univ, Fintype.card_fin] at hsum
    omega
  exact ⟨e, he, h3, hHl, hHm, hw, _root_.GlobalTheory.SepReal.interlaced_sub_single hw habs hs1 hs2, hwl, hwm, hgl, hgm, hneg, hpos, hB⟩

theorem realInputPar : Ev fun {D} _ _ {sc} _ _ _ => ∀ (τ : D.what₂.Tau) (ε : Fin (D.R.r + 1) → Bool) (lam : Fin (D.R.r + 1) → ℝ)
    (ε' : Fin D.R.r → Bool) (mu : Fin D.R.r → ℝ), IsEnum (Node.par D sc.cGap (.core 0) τ) lam ε →
    IsEnum (dualPar (parB (Ptw D) 0 τ)) mu ε' → (∃ e, GlobalTheory.SepReal.Par e ε lam ε' mu (sc.b ^ 2)) ∧
      Real.log (8 * ((D.R.r : ℝ) + 1) * sc.b ^ 2) ≤ 6 * Real.log sc.b ∧ 0 ≤ Real.log sc.b := by
  intro _ _ _
  refine ⟨0, fun D large₂ _ _ hS T L μ0 _ Gr W M _ => ?_⟩
  intro τ ε lam ε' mu hlam hmu
  obtain ⟨hv, hvk, hb, hga, hvk0, hb1, ha0, hbm, hb1', hb4⟩ := _root_.GlobalTheory.GridReal.num_real_bounds D large₂ hS τ
  have hl : IsEnum ((GlobalTheory.ChiGrid.num D 1 τ).parPi 0) lam ε := hlam
  have hD : dualPar (parB (Ptw D) 0 τ) = (GlobalTheory.ChiGrid.num D 1 τ).parD0 := by
    rw [← GlobalTheory.SignedHC.GridData.parD_zero_zero, parB, ← parV_zero D 1 (Nat.zero_le _) τ, dualPar_dualPar']
    show GlobalTheory.SignedHC.shift (if Odd (0 + 0) then -(1 / 2) else 0) _ = _
    rw [if_neg (by decide), shift_zero_lemma_2]
  have hm' : IsEnum (GlobalTheory.ChiGrid.num D 1 τ).parD0 mu ε' := hD ▸ hmu
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have h2m := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  refine ⟨exists_par_of_gridData_bounds (n := D.R.r) D.R.k_even D.R.m_even h2m
    (by show D.R.r + 1 = D.R.k + D.R.m; omega) (by omega) hv hvk hb hga hvk0 hb1 ha0 hbm hl hm', ?_,
    Real.log_nonneg hb1'⟩
  have hbpos : 0 < large₂.sc.b := by linarith
  show Real.log (8 * ((D.R.r : ℝ) + 1) * large₂.sc.b ^ 2) ≤ 6 * Real.log large₂.sc.b
  have h6 := Real.log_pow large₂.sc.b 6
  push_cast at h6
  rw [← h6]
  apply Real.log_le_log (by positivity)
  calc 8 * ((D.R.r : ℝ) + 1) * large₂.sc.b ^ 2 ≤ large₂.sc.b ^ 4 * large₂.sc.b ^ 2 := by gcongr
    _ = large₂.sc.b ^ 6 := by ring

end GlobalTheory.SepPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffHeisenbergArchimedeanDiffOperatorFamilyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_heisenbergArchimedeanDiffOperator_family : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (G : ℝ → SInf F κ) (P Q : ℝ → (κ → mixedEmbedding.mixedSpace F)),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => GlobalTheory.HeisOrbit.dOp (P p.1) (Q p.1) (G p.1) p.2) := by
  first | exact @GlobalTheory.HeisOrbit.dOp_contDiff_family | exact GlobalTheory.HeisOrbit.dOp_contDiff_family | (intros; apply GlobalTheory.HeisOrbit.dOp_contDiff_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumNormSphericalZetaKernelGLTrivialRepStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_norm_sphericalZetaKernelGL_trivialRep : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r t : ℕ), r ≤ t → ∀ (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → KerGL w (r + t) z φ → ∃ B : Multiset ℂˣ, B.card = r ∧ (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧ HasSum (fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) => ((‖φ a.out‖ : ℝ) : ℂ)) (eulerFac B (npow w (-((1 + (t : ℂ)) / 2))) * eulerFac (B.map fun β => β⁻¹) (npow w (-((1 + (t : ℂ)) / 2))) * ∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹)) := by
  first | exact @GlobalTheory.FinZeta.AbsZeta.hasSum_norm_kerGL | exact GlobalTheory.FinZeta.AbsZeta.hasSum_norm_kerGL | (intros; apply GlobalTheory.FinZeta.AbsZeta.hasSum_norm_kerGL <;> assumption)
end

