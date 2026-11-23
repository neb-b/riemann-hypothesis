module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointDetOnCompactTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilQDivisorAvoidsPointCartierIffNotMemSupp
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.PairStep

open CategoryTheory AlgebraicGeometry TopologicalSpace in
set_option autoImplicit false in
private lemma exists_coheight_one_generalization_not_unitAt {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {z : X} {f : X.functionField} (hf : f ≠ 0)
    (hreg : _root_.GlobalTheory.Cartier.RegAt z f) (hnu : ¬ _root_.GlobalTheory.Cartier.UnitAt z f) :
    ∃ w : X, w ⤳ z ∧ Order.coheight w = 1 ∧ ¬ _root_.GlobalTheory.Cartier.UnitAt w f := by
  obtain ⟨U, hzU, a, rfl⟩ := hreg.exists_fnOf
  obtain ⟨V, hV, hzV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hzU
  have hV' : IsAffineOpen V := hV
  have hgV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨z, trivial, hzV⟩
  rw [← _root_.GlobalTheory.Cartier.fnOf_resG hVU hgV a] at hf hnu ⊢
  generalize _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hVU a = b at hf hnu ⊢
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : Nonempty V := ⟨⟨z, hzV⟩⟩
  have hmem : ∀ q : PrimeSpectrum Γ(X, V), hV'.fromSpec q ∈ V := fun q => by
    have : hV'.fromSpec q ∈ Set.range hV'.fromSpec := Set.mem_range_self q
    rwa [hV'.range_fromSpec] at this
  have key : ∀ q : PrimeSpectrum Γ(X, V),
      _root_.GlobalTheory.Cartier.UnitAt (hV'.fromSpec q) (_root_.GlobalTheory.Cartier.fnOf V hgV b) ↔
        b ∉ q.asIdeal := by
    intro q
    rw [_root_.GlobalTheory.Cartier.unitAt_fnOf_iff (hmem q) hgV b]
    have : hV'.fromSpec q ∈ X.basicOpen b ↔ q ∈ PrimeSpectrum.basicOpen b := by
      rw [← hV'.fromSpec_preimage_basicOpen]; rfl
    rw [this, PrimeSpectrum.mem_basicOpen]
  set p := hV'.primeIdealOf ⟨z, hzV⟩
  have hpz : hV'.fromSpec p = z := hV'.fromSpec_primeIdealOf ⟨z, hzV⟩
  have hbp : b ∈ p.asIdeal := by
    by_contra h
    exact hnu (hpz ▸ (key p).mpr h)
  obtain ⟨P, hPmin, hPp⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem _).mpr hbp)
  haveI hPprime : P.IsPrime := hPmin.1.1
  set q : PrimeSpectrum Γ(X, V) := ⟨P, hPprime⟩
  have hbP : b ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hPmin.1.2
  refine ⟨hV'.fromSpec q, ?_, ?_, fun h => (key q).mp h hbP⟩
  · rw [← hpz]
    exact ((PrimeSpectrum.le_iff_specializes q p).mp hPp).map hV'.fromSpec.continuous
  · letI := X.presheaf.algebra_section_stalk ⟨hV'.fromSpec q, hmem q⟩
    haveI hloc := hV'.isLocalization_stalk' q (hmem q)
    have hdim : ringKrullDim (X.presheaf.stalk (hV'.fromSpec q)) = (P.height : WithBot ℕ∞) :=
      @IsLocalization.AtPrime.ringKrullDim_eq_height _ _ q.asIdeal q.2 _ _ _ hloc
    rw [ringKrullDim_stalk_eq_coheight] at hdim
    haveI : (Ideal.span {b}).IsPrincipal := ⟨⟨b, rfl⟩⟩
    have hle : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hPmin
    have hne : P.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff]
      intro hmin
      have hbot : P ≤ ⊥ := hmin.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
      have hb0 : b = 0 := (Submodule.eq_bot_iff _).mp (le_bot_iff.mp hbot) b hbP
      exact hf (by rw [hb0, map_zero])
    have h1 : P.height = 1 := le_antisymm hle (ENat.one_le_iff_ne_zero.mpr hne)
    rw [h1] at hdim
    exact_mod_cast hdim


open CategoryTheory AlgebraicGeometry TopologicalSpace in
set_option autoImplicit false in
theorem _root_.GlobalTheory.PairStep.off_qWeil_iff_notMem_supp : ∀ (X : Scheme.{0}) [IsIntegral X]
    [IsLocallyNoetherian X] (D₀ : _root_.GlobalTheory.Cartier.CartierDiv X) (m : ℕ) (z : X),
    D₀.Eff → 0 < m →
      (_root_.GlobalTheory.PairStep.Off (_root_.GlobalTheory.Discrepancy.qWeil D₀ m) z ↔
        z ∉ D₀.supp) := by
  intro X _ _ D m z hD hm
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  obtain ⟨g, hg⟩ := D.exists_isEqn z
  obtain ⟨U, hzU, hU⟩ := hg.exists_nhds
  have hgen : ∀ w : X, w ⤳ z → D.IsEqn w g := fun w hwz =>
    hU w (hwz.mem_open U.isOpen hzU)
  unfold _root_.GlobalTheory.PairStep.Off _root_.GlobalTheory.Discrepancy.qWeil
  simp only [div_eq_zero_iff, hm', or_false, Int.cast_eq_zero]
  rw [hg.mem_supp_iff, not_not]
  constructor
  · intro h
    by_contra hnu
    have hreg := (_root_.GlobalTheory.Cartier.CartierDiv.eff_iff.mp hD) z g hg
    obtain ⟨w, hwz, hw1, hwnu⟩ := exists_coheight_one_generalization_not_unitAt (Units.ne_zero g) hreg hnu
    have hmult := h w hwz
    rw [(hgen w hwz).mult_eq] at hmult
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.Discrepancy.regAt_of_specializes hwz hreg
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact Units.ne_zero g (by rw [← ha, map_zero])
    rw [← ha, _root_.GlobalTheory.Cartier.ord_algebraMap hw1 ha0] at hmult
    have hdim : ringKrullDim (X.presheaf.stalk w) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight, hw1]; rfl
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk w) := by
      rw [Ring.krullDimLE_iff, hdim]
      exact_mod_cast le_rfl
    have hfin := isFiniteLength_quotient_span_singleton (X.presheaf.stalk w)
      (mem_nonZeroDivisors_of_ne_zero ha0)
    have htop := Module.length_ne_top_iff.mpr hfin
    have hzero : Module.length (X.presheaf.stalk w) (X.presheaf.stalk w ⧸ Ideal.span {a}) ≠ 0 := by
      rw [Ne, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
        Ideal.span_singleton_eq_top]
      exact fun hunit => hwnu ⟨a, hunit, ha⟩
    have : (Module.length (X.presheaf.stalk w) (X.presheaf.stalk w ⧸ Ideal.span {a})).toNat ≠ 0 := by
      rw [Ne, ENat.toNat_eq_zero]
      tauto
    exact this (by exact_mod_cast hmult)
  · intro hunit w hwz
    rw [(hgen w hwz).mult_eq]
    obtain ⟨V, hzV, hV⟩ := hunit.exists_nhds
    exact (hV w (hwz.mem_open V.isOpen hzV)).ord_eq_zero

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylFormulaCompactTorusIdentityOfIngredients
section
section
open GlobalTheory.PsCo.PcEG

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open GlobalTheory.HCChar (dsChar)

namespace GlobalTheory.PsCo.PcEF

namespace WeylCompactTorusIdentity

theorem alg {W S C M s p x : ℂ} (hs : s * s = 1) (hp : p * p = 1) (hW : W ≠ 0) (hM : M ≠ 0) (hs0 : s ≠ 0)
    (hx : W * x = S * C) : s * x = p * S / (W * (s * M)) * (p * M * C) := by
  have hden : W * (s * M) ≠ 0 := mul_ne_zero hW (mul_ne_zero hs0 hM)
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination (M * s * s) * hx + (M * S * C) * hs - (M * S * C) * hp

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

end WeylCompactTorusIdentity


open WeylCompactTorusIdentity in
theorem weylFormulaCompactTorusIdentity_of_ingredients : VdmSplit → PhysTor → NumShift → TorusId := by
  intro hV hP hN n ε lam Λ m hm hΛ θ hinj x hx
  have ht0 : ∀ a, tor θ a ≠ 0 := fun a => Complex.exp_ne_zero _
  obtain ⟨hPD, -⟩ := hP n ε θ
  have hVd := hV n ε (tor θ)
  have hx' : ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε (tor θ) * x =
      (∑ w ∈ GlobalTheory.HCChar.compactWeyl ε,
        ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, tor θ a ^ m (w.symm a)) *
        ∏ a, tor θ a ^ (-(if ε a then 0 else (pOf ε : ℤ))) := by
    rw [hx]
    exact (congrArg (fun μ => ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε μ (tor θ)) (funext hΛ)).trans
      (hN n ε m (fun b : Bool => if b then (0 : ℤ) else (pOf ε : ℤ)) (tor θ) ht0)
  have hV0 : (∏ a, ∏ b ∈ Finset.Ioi a, (tor θ a - tor θ b)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun a _ => Finset.prod_ne_zero_iff.mpr (fun b hb => ?_))
    exact sub_ne_zero.mpr (fun h => (Finset.mem_Ioi.mp hb).ne (hinj h))
  rw [hVd] at hV0
  rw [GlobalTheory.HCChar.dsChar_eq ε hm θ, hPD, hVd]
  exact alg (neg_one_pow_mul_self _) (neg_one_pow_mul_self _)
    (left_ne_zero_of_mul hV0) (right_ne_zero_of_mul (right_ne_zero_of_mul hV0))
    (pow_ne_zero _ (by norm_num)) hx'

end GlobalTheory.PsCo.PcEF

end
end

namespace GlobalTheory.PsCo.PcEF
open GlobalTheory.PsCo.PcEG

theorem torusId_full : TorusId := weylFormulaCompactTorusIdentity_of_ingredients vandermonde_splits_compactNoncompact adjointDet_onCompactTorus numShift_holds

end GlobalTheory.PsCo.PcEF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameConjugateGramInv
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WittFrame

theorem yx_eq_one : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) * X = 1 := by
  intro D V r X Y hW
  have hσ : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := fun _ => rfl
  have hJ : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram = V.gram := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hσ, Formalism.BasicNotions.HSpace.gram]
    exact V.herm.eq (V.frame j) (V.frame i)
  have hX : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X) = X := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hσ, star_star]
  have h := congrArg (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)) hW.xy
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hX, hJ, Formalism.UG.cT_one] at h
  rwa [Matrix.mul_assoc]

end GlobalTheory.WittFrame
end

