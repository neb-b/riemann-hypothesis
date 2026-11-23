module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal
public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Formalism.LocalToGlobal.Columns.RowFormsAdelic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeIdempotentProjectorVanishingBaseChangeTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem transfer_aeval (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (F : Module.End D.what₂.LL (S.WL j)) (G : Module.End (FractionRing (T.O i)) (FmT D T S i j b))
    (hFG : ∀ x, Φ (F x) = G (Φ x)) (p : Polynomial ↥D.LL0) (x : S.WL j) :
    Φ (aeval F (p.map (algebraMap ↥D.LL0 D.what₂.LL)) x) = aeval G (p.map (readT D T i b)) (Φ x) := by
  have hpow : ∀ (n : ℕ) (y : S.WL j), Φ ((F ^ n) y) = (G ^ n) (Φ y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih => intro y; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hFG]
  induction p using Polynomial.induction_on' generalizing x with
  | add p q hp hq => rw [Polynomial.map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply,
      map_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, IntermediateField.algebraMap_apply,
      hc, hpow]

theorem transfer_piLop (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (ha : ∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x))
    (x : S.WL j) : Φ (piLop D S In.θ j x) = piKop D T S In i j b (Φ x) := by
  haveI : Fintype (Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _
  unfold piLop piKop
  set_option synthInstance.maxHeartbeats 100000 in
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hc, ha, LinearEquiv.coe_coe]

theorem phiKop_eGT_piKop_eq_zero : ∀ (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ)
    (b : Bool) (k : ℕ) (P : PlE D.host),
    1 ≤ j → j ≤ D.R.m → phiLop D S In j k P * eLop D S j * piLop D S In.θ j = 0 →
    phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b = 0 := by
  intro D T S In i j b k P h1 h2 h0
  obtain ⟨Φ, hc, hf, hw⟩ := descend_exists D T S In i j b h1 h2
  have ha := descend_actL D T S In i j b h1 h2 Φ hc hf
  have he : ∀ x, Φ (eLop D S j x) = eGT D T S In.rho In.chi i j b (Φ x) := descend_eSum D T S In i j b Φ hc ha
  have hpi := transfer_piLop D T S In i j b Φ hc ha
  have hr : ∀ w : ↥(WKr D S j), (hLr D S In j k P w : S.WL j) = In.hL j k P w := by
    intro w
    unfold hLr
    split_ifs with h
    · rfl
    · exact absurd ⟨h1, h2⟩ h
  have hh : ∀ x, Φ (In.hL j k P x) = hLT D T S In i j b k P (Φ x) := fun x => hf _ _ hr x
  have hphi : ∀ x, Φ (phiLop D S In j k P x) = phiKop D T S In i j b k P (Φ x) :=
    transfer_aeval D T S i j b Φ hc _ _ hh (evPol D S In j k P)
  have key : ∀ w : ↥(WKr D S j),
      (phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b)
        ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) = 0 := by
    intro w
    rw [← hw, Module.End.mul_apply, Module.End.mul_apply, ← hpi, ← he, ← hphi]
    have h3 := LinearMap.congr_fun h0 (w : S.WL j)
    rw [Module.End.mul_apply, Module.End.mul_apply] at h3
    rw [h3, LinearMap.zero_apply, map_zero]
  set f := phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b with hfdef
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.zero_apply]
  change KT D T i b ⊗[S.Ks] ↥(WKr D S j) at y
  induction y using TensorProduct.induction_on with
  | zero => exact f.map_zero
  | tmul c w =>
    have hcw : (c ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) =
        (c : FractionRing (T.O i)) • ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hcw]
    exact (f.map_smul (c : FractionRing (T.O i))
      (show FmT D T S i j b from ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)))).trans
      (by rw [key]; exact smul_zero _)
  | add y z hy hz =>
    exact (f.map_add (show FmT D T S i j b from y) (show FmT D T S i j b from z)).trans (by rw [hy, hz, add_zero])

end GlobalTheory.HeightCounting.FormsStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualCoefficientSpaceUnique
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.AlgWtF.DDHw

theorem dd_hw_unique : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → ∀ (τ₀ : ι) (mu : Fin n → ℤ),
      NX.HWAtF (IsCMField.complexConj L : L →+* L) (GlobalTheory.AlgWtF.wtRepF emb lam).dual (emb τ₀) mu → mu = (lam τ₀).w := by
  intro L _ _ _ n ι _ K _ _ emb lam hd τ₀ mu h
  classical
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  obtain ⟨w, hwV, hw0, hB⟩ := _root_.GlobalTheory.AlgWtF.DDHwT.hw_eigvec_transport L n ι K emb lam hd τ₀ mu h
  obtain ⟨φ, hφ0, hφV, hφA⟩ := _root_.GlobalTheory.specialise_factor K n ι lam τ₀ w hwV hw0
  refine _root_.GlobalTheory.HwEigen.mu_eq_of_upper_eigen K n (lam τ₀) mu (φ w) (hφV w hwV) hφ0 fun B hBt => ?_
  have hc0 : detPow K n B (lam τ₀).detShift ≠ 0 := by
    rw [detPow]; exact Units.ne_zero _
  rw [sqAct, ← hφA, hB B hBt, map_smul, smul_smul, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

end GlobalTheory.AlgWtF.DDHw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfOfLamLdefEqParamV
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WtPar

lemma univ_map_eq_range {α : Type} (n : ℕ) (f : ℕ → α) :
    (Finset.univ : Finset (Fin n)).val.map (fun i : Fin n => f (i : ℕ)) = (Multiset.range n).map f := by
  rw [Fin.univ_val_map, List.ofFn_eq_map, Multiset.range, Multiset.map_coe, ← List.map_coe_finRange_eq_range,
    List.map_map]
  rfl

lemma transport {D : D7} {j : ℕ} {τ : D.what₂.Tau} {n n' : ℕ} (h : n = n')
    (hx : ∃ lam : DomWeight n, Bridge.IsLamPrime (D := D) lam j τ) :
    ∃ lam : DomWeight n', Bridge.IsLamPrime (D := D) lam j τ := by
  subst h; exact hx

lemma lamPrime_add_rho (W : Formalism.IndefR.IndefiniteWeightData.WeightData) (hk : 1 ≤ W.k) (hj : 1 ≤ W.j) (hjm : W.j ≤ W.m)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ W.nV) :
    W.lamPrime i + W.rhoNV i = W.uSideTarget i - 1 / 2 := by
  have hN : W.nV = W.p + W.q + W.t := by
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.nV, Formalism.IndefR.IndefiniteWeightData.WeightData.r,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q]; omega
  have hNq : (W.nV : ℚ) = W.p + W.q + W.t := by exact_mod_cast hN
  simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt,
    Formalism.IndefR.IndefiniteWeightData.WeightData.dTau, Formalism.IndefR.IndefiniteWeightData.WeightData.rhoNV,
    Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus,
    Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus]
  split_ifs with h1 h2
  · ring
  · rw [hNq]; ring
  · have hc : W.q + 1 - (W.q + 1 - (i - W.p - W.t)) = i - W.p - W.t := by omega
    rw [hc]
    have hc' : ((i - W.p - W.t : ℕ) : ℚ) = i - W.p - W.t := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    rw [hc', hNq]; ring

end GlobalTheory.Mem.WtPar

namespace GlobalTheory.Mem.WtPar

theorem infOf_lamLdef_eq_paramV : ∀ (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau),
    NG.infOf (Bridge.lamLdef (D := D) D.R.nV ((j : ℕ) + 1) τ).w = NG.paramV D.R (D.hc τ) j (1 / 2) := by
  intro D j τ
  have hk := D.R.m_add_three_le_k
  have hjm := j.2
  have hex : ∃ lam : DomWeight D.R.nV, Bridge.IsLamPrime (D := D) lam ((j : ℕ) + 1) τ := by
    have h0 := GlobalTheory.ForcedWeights.lamLForced D ((j : ℕ) + 1) (by omega) (by omega) τ
    have hr : (D.sp.V ((j : ℕ) + 1)).rank = D.R.nV := D.sp.V_rank _ (by omega) (by omega)
    exact transport hr ⟨_, h0⟩
  have hl : Bridge.IsLamPrime (D := D) (Bridge.lamLdef (D := D) D.R.nV ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ := by
    unfold Bridge.lamLdef; rw [dite_eq_left hex]; exact hex.choose_spec
  set lam := Bridge.lamLdef (D := D) D.R.nV ((j : ℕ) + 1) τ
  obtain ⟨hj, W, hWk, hWm, hWt, hWj, hWe, hWv, hWb, hw⟩ := hl
  have hWn : W.nV = D.R.nV := by
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.nV, Formalism.IndefR.IndefiniteWeightData.WeightData.r, Ranks.nV, Ranks.r, hWk, hWm, hWt]
  have hWp : W.p = D.R.k + (j : ℕ) := by
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.p, hWk, hWj]; omega
  let g : ℕ → ℚ := fun i => W.uSideTarget (i + 1) - 1 / 2

  have hL : NG.infOf lam.w = (Multiset.range D.R.nV).map (fun i => ((g i : ℚ) : ℂ)) := by
    unfold NG.infOf
    rw [← univ_map_eq_range]
    refine Multiset.map_congr rfl fun i _ => ?_
    have h1 := lamPrime_add_rho W (by omega) (by omega) (by omega) ((i : ℕ) + 1) (by omega)
      (by have := i.2; omega)
    have h2 := hw i
    have key : ((lam.w i : ℤ) : ℚ) + ((D.R.nV : ℚ) - 1) / 2 - ((i : ℕ) : ℚ) = g i := by
      simp only [g]
      rw [h2, ← h1]
      simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.rhoNV, hWn]
      push_cast; ring
    have := congrArg (fun x : ℚ => (x : ℂ)) key
    push_cast at this ⊢
    exact this

  let gv : ℕ → ℚ := fun n => (W.v (n + 2) : ℚ) - 1 / 2
  let gb : ℕ → ℚ := fun n => -(W.b (n + 1) : ℚ) - 1 / 2
  let ge : ℕ → ℚ := fun c => -(W.e : ℚ) - 1 / 2 + ((D.R.t : ℚ) - 1 - 2 * c) / 2
  have hR : NG.paramV D.R (D.hc τ) j (1 / 2) =
      ((Multiset.range (D.R.k - 1)).map gv + (Multiset.range D.R.m).map gb
        + (Multiset.range D.R.t).map ge).map (fun x : ℚ => (x : ℂ)) := by
    simp only [Multiset.map_add (f := _), Multiset.map_map]
    unfold NG.paramV
    congr 1
    · congr 1
      · rw [← univ_map_eq_range]
        refine Multiset.map_congr rfl fun i _ => ?_
        simp only [Function.comp, gv, hWv i]
        push_cast; ring
      · rw [← univ_map_eq_range]
        refine Multiset.map_congr rfl fun i _ => ?_
        simp only [Function.comp, gb, hWb i]
        push_cast; ring
    · refine Multiset.map_congr rfl fun c _ => ?_
      have he : (D.hc τ).e j = (W.e : ℚ) := by
        rw [hWe]; congr 1; try (ext; simp)
      simp only [Function.comp, ge, he]
      push_cast; ring
  rw [hL, hR, show (fun i => ((g i : ℚ) : ℂ)) = (fun x : ℚ => (x : ℂ)) ∘ g from rfl, ← Multiset.map_map]
  congr 1

  have hsplit : D.R.nV = ((D.R.k - 1) + ((j : ℕ) + 1)) + D.R.t + (D.R.m - ((j : ℕ) + 1)) := by
    simp only [Ranks.nV, Ranks.r]; omega
  have hmsplit : D.R.m = ((j : ℕ) + 1) + (D.R.m - ((j : ℕ) + 1)) := by omega
  rw [hsplit, Multiset.range_add, Multiset.range_add, Multiset.range_add]
  conv_rhs => rw [hmsplit, Multiset.range_add]
  simp only [Multiset.map_add (f := _), Multiset.map_map]
  have e1 : (Multiset.range (D.R.k - 1)).map g = (Multiset.range (D.R.k - 1)).map gv := by
    refine Multiset.map_congr rfl fun n hn => ?_
    rw [Multiset.mem_range] at hn
    simp only [g, gv, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, Formalism.IndefR.IndefiniteWeightData.WeightData.lam, hWp, hWk]
    rw [if_pos (by omega), if_pos (by omega)]
  have e2 : (Multiset.range ((j : ℕ) + 1)).map (g ∘ fun x => D.R.k - 1 + x) =
      (Multiset.range ((j : ℕ) + 1)).map gb := by
    refine Multiset.map_congr rfl fun n hn => ?_
    rw [Multiset.mem_range] at hn
    simp only [Function.comp, g, gb, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      hWp, hWk]
    rw [if_pos (by omega), if_neg (by omega)]
    have hh : D.R.k - 1 + n + 1 - (D.R.k - 1) = n + 1 := by omega
    rw [hh]; push_cast; ring
  have e3 : (Multiset.range D.R.t).map (g ∘ fun x => D.R.k - 1 + ((j : ℕ) + 1) + x) =
      (Multiset.range D.R.t).map ge := by
    refine Multiset.map_congr rfl fun c hc => ?_
    rw [Multiset.mem_range] at hc
    simp only [Function.comp, g, ge, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, hWp, hWt]
    rw [if_neg (by omega), if_pos (by omega)]
    have : ((D.R.k - 1 + ((j : ℕ) + 1) + c + 1 : ℕ) : ℚ) - ((D.R.k + (j : ℕ) : ℕ) : ℚ) = c + 1 := by
      rw [show D.R.k - 1 + ((j : ℕ) + 1) + c + 1 = (D.R.k + (j : ℕ)) + (c + 1) by omega]
      push_cast; ring
    rw [this]; ring
  have e4 : (Multiset.range (D.R.m - ((j : ℕ) + 1))).map (g ∘ fun x => D.R.k - 1 + ((j : ℕ) + 1) + D.R.t + x) =
      (Multiset.range (D.R.m - ((j : ℕ) + 1))).map (gb ∘ fun x => (j : ℕ) + 1 + x) := by
    refine Multiset.map_congr rfl fun c hc => ?_
    rw [Multiset.mem_range] at hc
    simp only [Function.comp, g, gb, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, hWp, hWt, hWj]
    rw [if_neg (by omega), if_neg (by omega)]
    have hh : (j : ℕ) + 1 + (D.R.k - 1 + ((j : ℕ) + 1) + D.R.t + c + 1 - (D.R.k + (j : ℕ)) - D.R.t) = (j : ℕ) + 1 + c + 1 := by omega
    rw [hh]
  rw [e1, e2, e3, e4]
  abel

end GlobalTheory.Mem.WtPar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIsCompactParahoricGLCompletion
section
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.ParahoricTopo

theorem isClopen_OP {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) :
    IsClopen ((OP P : Subring (P.adicCompletion L)) : Set (P.adicCompletion L)) :=
  Valued.isClopen_valuationSubring (P.adicCompletion L)

theorem isClopen_mulSet {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))
    (ϖ : P.adicCompletion L) (hϖ : ϖ ≠ 0) :
    IsClopen {y : P.adicCompletion L | ∃ o ∈ OP P, y = ϖ * o} := by
  have e : {y : P.adicCompletion L | ∃ o ∈ OP P, y = ϖ * o} =
      (fun y => ϖ⁻¹ * y) ⁻¹' ((OP P : Subring (P.adicCompletion L)) : Set (P.adicCompletion L)) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨o, ho, rfl⟩
      rwa [← mul_assoc, inv_mul_cancel₀ hϖ, one_mul]
    · intro h
      exact ⟨_, h, by rw [← mul_assoc, mul_inv_cancel₀ hϖ, one_mul]⟩
  rw [e]
  exact (isClopen_OP P).preimage (continuous_const.mul continuous_id)

theorem isOpen_isCompact_parJ : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (r c : ℕ), IsOpen (parJ (OP P) (piP P : P.adicCompletion L) r c) ∧ IsCompact (parJ (OP P) (piP P : P.adicCompletion L) r c) := by
  intro L _ _ P r c
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  haveI : (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (P.adicCompletion L))
    (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ)))
  have hK : GlobalTheory.SplitWeil.KO (P.adicCompletion L) (Fin (r + c)) = GLint (OP P) (r + c) := by
    ext g
    rw [GlobalTheory.SplitFlip.mem_KO_iff]
    simp only [he.le_one_iff_le_one, Valuation.mem_integer_iff]
    exact Iff.rfl
  have hS := isClopen_mulSet P (piP P : P.adicCompletion L) (Units.ne_zero _)
  set B : Set (GL (Fin (r + c)) (P.adicCompletion L)) :=
    {k | bDA (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) ∈
      IIset (t := c) (a := r) (OP P) (piP P : P.adicCompletion L)} with hB
  have hBe : B = ⋂ i : Fin c, ⋂ j : Fin r,
      (fun k : GL (Fin (r + c)) (P.adicCompletion L) =>
        (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) (Fin.natAdd r i) (Fin.castAdd c j)) ⁻¹'
        {y : P.adicCompletion L | ∃ o ∈ OP P, y = (piP P : P.adicCompletion L) * o} := by
    ext k
    simp only [hB, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, IIset, bDA, Matrix.submatrix_apply]
  have hcont : ∀ (i : Fin (r + c)) (j : Fin (r + c)), Continuous fun k : GL (Fin (r + c)) (P.adicCompletion L) =>
      (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) i j := fun i j =>
    (Units.continuous_val (M := Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).matrix_elem i j
  have hBc : IsClopen B := by
    rw [hBe]
    exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j => hS.preimage (hcont _ _)
  have hP : parJ (OP P) (piP P : P.adicCompletion L) r c =
      (GlobalTheory.SplitWeil.KO (P.adicCompletion L) (Fin (r + c)) : Set _) ∩ B := by
    rw [hK]; rfl
  rw [hP]
  exact ⟨GlobalTheory.SplitFlip.isOpen_KO.inter hBc.isOpen, GlobalTheory.SplitFlip.isCompact_KO.inter_right hBc.isClosed⟩

end GlobalTheory.ParahoricTopo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonzeroLiftPartTypeGivesNonzeroTypeVectorStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_liftPart_type_gives_nonzero_typeVector : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (π : Formalism.L2.NG.FinTyp D.host.E D.R.r) (i : Fin D.R.m), principalLevelFrame.isotL R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) (R.toRealDat.eWf i (sg0 D A3.A)) π ≠ ⊥ → ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec ((Y.PW i).ψ ⁻¹' (levS _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))) (fun κ => (levChi _ (R.βW i) (R.datWp i (R.toRealDat.levL F.lv2 false (sg0 D A3.A)))) ((Y.PW i).ψ κ)) x := by
  first | exact @GlobalTheory.IsotPartVec.main | exact GlobalTheory.IsotPartVec.main | (intros; apply GlobalTheory.IsotPartVec.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsRowOfEigensystemIndexGoodCharactersStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partsRow_of_eigensystemIndex_goodCharacters : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D), Pins R F cG → Holds R F → HostHyp D → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → (∀ (i : Fin D.R.m) π (c : A3.fam3.base3.Ix) (e : D.what₂.LL →+* ℂ), D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) → Xd.logLam ((i : ℕ) + 1) π e = Real.log (R.lam3 i A3.A.μ0 c (InfinitePlace.mk e))) → ∃ (E : EigIdx D Xd) (labPi : E.Pi → A3.A.fam.base.Ix) (piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), PartsRec R.toRealDat F.lv2 Y.tupT Y.hm Y.PY Y.PW Y.eFT E labPi piOf Y.Ish.prt Y.IL.prtW := by
  first | exact @GlobalTheory.Mem.R3.partsRec_of_eig | exact GlobalTheory.Mem.R3.partsRec_of_eig | (intros; apply GlobalTheory.Mem.R3.partsRec_of_eig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayFieldTopMaximalUnramified
section
noncomputable section

open Formalism.L2.Host GlobalTheory.Published GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain

namespace GlobalTheory.HilbertInClosure

theorem rayField_top_maximal_unramified : GlobalArtinReciprocity → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (j : E →ₐ[ℚ] Qb) (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ),
    IsRayFieldIn (ι.comp j.toRingHom) ⊤ M →
    ∃ _ : NumberField (qb ι M),
      (j.fieldRange ≤ qb ι M ∧
        (∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → ∀ y ∈ qb ι M, σ y ∈ qb ι M) ∧
        ∀ σ τ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → (∀ x ∈ j.fieldRange, τ x = x) →
          ∀ y ∈ qb ι M, σ (τ y) = τ (σ y)) ∧
      (discr (qb ι M)).natAbs = (discr E).natAbs ^ (Module.finrank ℚ (qb ι M) / Module.finrank ℚ E) ∧
      ∀ (L : Fld) [NumberField L],
        (j.fieldRange ≤ L ∧ (∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → ∀ y ∈ L, σ y ∈ L) ∧
          ∀ σ τ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → (∀ x ∈ j.fieldRange, τ x = x) →
            ∀ y ∈ L, σ (τ y) = τ (σ y)) →
        (discr L).natAbs = (discr E).natAbs ^ (Module.finrank ℚ L / Module.finrank ℚ E) → L ≤ qb ι M := by
  intro H E _ _ _ j ι M hM
  obtain ⟨hN, h, hst, hc, hd, hmax⟩ := hilbert_qb_aut H E j ι M hM
  have hm : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ GalOf j.fieldRange ↔ ∀ x ∈ j.fieldRange, σ x = x := fun σ =>
    IntermediateField.mem_fixingSubgroup_iff _ _
  exact ⟨hN, ⟨h, fun σ hσ => hst σ ((hm σ).2 hσ), fun σ τ hσ hτ => hc σ ((hm σ).2 hσ) τ ((hm τ).2 hτ)⟩, hd,
    fun L _ hL => hmax L hL.1 fun σ hσ τ hτ => hL.2.2 σ τ ((hm σ).1 hσ) ((hm τ).1 hτ)⟩

end GlobalTheory.HilbertInClosure

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsDeco
section
noncomputable section

open scoped TensorProduct

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowAd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (X : Stages)

theorem rank_X' : X.toD7.sp.X'.rank = X.B.R.N X.B.R.m - 1 := by
  rw [X.toD7.sp.X'_rank, Formalism.L2.Col.rank_X'_eq]
  rfl

def ptE (h : Bridge.Gf X.toD7.sp.X') :
    GL (Fin (X.B.R.N X.B.R.m - 1)) (X.B.fields.E ⊗[X.B.fields.F] Formalism.L2.Herm.Af X.B.fields.F) :=
  Units.map (Matrix.reindexAlgEquiv (Formalism.IndefR.Lev.EAf X.toD7) (Formalism.IndefR.Lev.EAf X.toD7) (finCongr (rank_X' X))).toMonoidHom
    (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE X.toD7) h.1)

variable {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) {U : Set I.ι}

def decoAd (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X') : (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).D :=
  Formalism.L2.Col.decoOf (F := X.B.fields.F) (E := X.B.fields.E) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) (ptE X h)

def ReadsDeco (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (cX : CoefA X.toD7.sp.X') {J : Subgroup (Bridge.Gf X.toD7.sp.X')}
    {χ : J →* ℂˣ} (t : TupU I U)
    (P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ J χ) : Prop :=
  ∃ m : ((famR X I hX U Xg tr).A.MtildeCSD t).V →ₛₗ[X.toD7.what₂.embLL] cX.W,
    ∀ (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) (h : Bridge.Gf X.toD7.sp.X'),
      P.ext (f : _ → _) h = m ((((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1
        (decoAd X I t h))

end GlobalTheory.Mem.R3.RowAd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameInertiaRepresentativeResidueStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameInertia_representative_residue : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime], IsPlaceOver (F := E) A P → normV P = g → ((g : ℕ) : 𝓞 E) ∈ P.asIdeal → ((g : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (σ : G E Ω) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g), σ ∈ Ine (F := E) A → IsGenSys ζ → TameCoupled A κ σ ζ → (∀ A' : ValuationSubring Ω, IsPlaceOver (F := E) A' P → σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A) → ∀ u : 𝓞 E, NX.TameRep P 1 σ u → ∃ a : ℕ, a.Coprime g ∧ u - (a : 𝓞 E) ∈ P.asIdeal ∧ algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (a : ZMod g) = ζ 1 := by
  first | exact @GlobalTheory.tameRep_residue | exact GlobalTheory.tameRep_residue | (intros; apply GlobalTheory.tameRep_residue <;> assumption)
end

