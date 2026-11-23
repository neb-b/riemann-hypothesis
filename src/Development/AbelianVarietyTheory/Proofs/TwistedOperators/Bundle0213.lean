module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKtypeCoefficientExplicitPowerDecay
section
noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.SepReal.PowDec

theorem hsn_sq_le {m : ℕ} (g : Mat m) : hsn g ^ 2 ≤ m * Real.exp (2 * GlobalTheory.Count.dHS g) := by
  have hA := Matrix.isHermitian_conjTranspose_mul_self g
  have h1 : hsn g ^ 2 = ∑ j, hA.eigenvalues j := by
    have e0 : hsn g = Real.sqrt (Formalism.REAL.hs g) := rfl
    rw [e0, Real.sq_sqrt (by unfold Formalism.REAL.hs; positivity), GlobalTheory.Count.Cartan.hs_eq_trace,
      hA.trace_eq_sum_eigenvalues]
    simp [Complex.re_sum]
  rw [h1]
  have hle : ∀ j, hA.eigenvalues j ≤ Real.exp (2 * GlobalTheory.Count.dHS g) := by
    intro j
    have hx : |Real.log (hA.eigenvalues j) / 2| ≤ GlobalTheory.Count.dHS g := by
      unfold GlobalTheory.Count.dHS
      apply Real.abs_le_sqrt
      exact Finset.single_le_sum (f := fun i => (Real.log (hA.eigenvalues i) / 2) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    rcases le_or_gt (hA.eigenvalues j) 0 with h0 | h0
    · exact h0.trans (Real.exp_pos _).le
    · calc hA.eigenvalues j = Real.exp (2 * (Real.log (hA.eigenvalues j) / 2)) := by
            rw [show 2 * (Real.log (hA.eigenvalues j) / 2) = Real.log (hA.eigenvalues j) by ring,
              Real.exp_log h0]
        _ ≤ Real.exp (2 * GlobalTheory.Count.dHS g) := by
            apply Real.exp_le_exp.2
            linarith [le_abs_self (Real.log (hA.eigenvalues j) / 2)]
  calc ∑ j, hA.eigenvalues j ≤ ∑ _j : Fin m, Real.exp (2 * GlobalTheory.Count.dHS g) :=
        Finset.sum_le_sum fun j _ => hle j
    _ = m * Real.exp (2 * GlobalTheory.Count.dHS g) := by simp

theorem hsn_pos {m : ℕ} (hm : 1 ≤ m) {ε : Fin m → Bool} {g : Mat m} (hg : g ∈ UJset ε) : 0 < hsn g := by
  unfold hsn
  apply Real.sqrt_pos.2
  by_contra hle
  push_neg at hle
  have hsum : ∑ a, ∑ b, ‖g a b‖ ^ 2 = 0 := le_antisymm hle (by positivity)
  have hg0 : g = 0 := by
    ext a b
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at hsum
    have h2 := hsum a (Finset.mem_univ _)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at h2
    simpa using h2 b (Finset.mem_univ _)
  have hJ : gᴴ * Jm ε * g = Jm ε := hg
  rw [hg0] at hJ
  have := congrFun (congrFun hJ ⟨0, hm⟩) ⟨0, hm⟩
  simp [Jm] at this
  split_ifs at this <;> simp at this

theorem hsn_sq_definite {m : ℕ} {ε : Fin m → Bool} (hq : GlobalTheory.Count.rkR ε = 0) {g : Mat m} (hg : g ∈ UJset ε) :
    hsn g ^ 2 = m := by
  have hJ : gᴴ * Jm ε * g = Jm ε := hg
  have hJc : Jm ε = 1 ∨ Jm ε = -1 := by
    unfold GlobalTheory.Count.rkR at hq
    rcases Nat.min_eq_zero_iff.1 hq with h | h
    · right
      have hf : ∀ a, ε a = false := fun a => by
        by_contra ha
        have : a ∈ univ.filter fun a => ε a = true := by simpa using ha
        rw [Finset.card_eq_zero.1 h] at this
        simp at this
      ext a b
      by_cases hab : a = b <;> simp [Jm, Matrix.diagonal_apply, hab, hf, Matrix.one_apply]
    · left
      have hf : ∀ a, ε a = true := fun a => by
        by_contra ha
        have : a ∈ univ.filter fun a => ε a = false := by simpa using ha
        rw [Finset.card_eq_zero.1 h] at this
        simp at this
      ext a b
      by_cases hab : a = b <;> simp [Jm, Matrix.diagonal_apply, hab, hf, Matrix.one_apply]
  have hu : gᴴ * g = 1 := by
    rcases hJc with h | h
    · rw [h, Matrix.mul_one] at hJ; exact hJ
    · rw [h] at hJ
      have : -(gᴴ * g) = -1 := by simpa [Matrix.mul_neg, Matrix.neg_mul] using hJ
      exact neg_inj.1 this
  have e0 : hsn g = Real.sqrt (Formalism.REAL.hs g) := rfl
  rw [e0, Real.sq_sqrt (by unfold Formalism.REAL.hs; positivity), GlobalTheory.Count.Cartan.hs_eq_trace, hu]
  simp

end GlobalTheory.SepReal.PowDec

namespace GlobalTheory.SepReal.PowDec

theorem rkR_le {m : ℕ} (ε : Fin m → Bool) : GlobalTheory.Count.rkR ε ≤ m := by
  unfold GlobalTheory.Count.rkR
  exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))

theorem gap_ok {m : ℕ} (hm : 1 ≤ m) (ε : Fin m → Bool) :
    120 * (m : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 1000 * (m : ℝ) ^ 3 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ≤ m := by exact_mod_cast rkR_le ε
  have h1 : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) hq (by norm_num)
  have h2 : (m : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  rw [Real.rpow_two] at h2
  have h3 : 0 ≤ (m : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity : (0 : ℝ) ≤ 120 * m)]

end GlobalTheory.SepReal.PowDec

namespace GlobalTheory.SepReal


open GlobalTheory.SepReal.PowDec in
theorem decPow : DecPow := by
  intro m ε lam B hm hlam hgap _ H _ _ π hπ v₀ hv₀ g hg
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hdec := (GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap m ε lam H π hlam hπ
    (1000 * (m : ℝ) ^ 3) hgap (gap_ok (by omega) ε) g hg v₀ hv₀.2 v₀ hv₀.2).1
  rw [hv₀.1, mul_one, mul_one] at hdec
  unfold GlobalTheory.Dec.decHS at hdec
  set t := GlobalTheory.Count.dHS g with ht
  set q := GlobalTheory.Count.rkR ε with hqdef
  have hx := hsn_pos (by omega) hg
  set A : ℝ := 40 * (m : ℝ) ^ 2 with hA
  have hpow : hsn g ^ (-A) = Real.exp (Real.log (hsn g) * (-A)) := Real.rpow_def_of_pos hx _
  rw [hpow, ← Real.exp_add]
  refine hdec.trans (Real.exp_le_exp.2 ?_)
  have hlogm : Real.log m ≤ m := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hm0 : (0 : ℝ) ≤ m := by positivity
  rcases Nat.eq_zero_or_pos q with hq | hq
  ·
    have hs2 := hsn_sq_definite hq hg
    have hL : 2 * Real.log (hsn g) = Real.log m := by
      rw [← Real.log_rpow hx, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hs2]
    have hM : min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) = 0 := by
      rw [hq]; simp; positivity
    rw [hM]
    nlinarith [mul_le_mul_of_nonneg_left hlogm (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2)]
  · have hs2 := hsn_sq_le g
    have hL : 2 * Real.log (hsn g) ≤ Real.log m + 2 * t := by
      have h1 : Real.log (hsn g ^ 2) ≤ Real.log (m * Real.exp (2 * t)) := Real.log_le_log (by positivity) hs2
      rw [Real.log_pow, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at h1
      push_cast at h1; linarith
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hqm : (q : ℝ) ≤ m := by exact_mod_cast rkR_le ε
    have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hsq : Real.sqrt (2 * (q : ℝ)) ≤ m := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    have hsq0 : 0 < Real.sqrt (2 * (q : ℝ)) := Real.sqrt_pos.2 (by positivity)

    have hkey : t - 1 ≤ (m : ℝ) * min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) := by
      rcases le_total t 1 with h1 | h1
      · have : 0 ≤ min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) := le_min (by positivity) (by positivity)
        nlinarith
      · have a1 : t ≤ (m : ℝ) * t ^ 2 := by nlinarith
        have a2 : t ≤ (m : ℝ) * (t / Real.sqrt (2 * (q : ℝ))) := by
          rw [mul_div_assoc', le_div_iff₀ hsq0]; nlinarith
        rcases min_choice (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) with e | e <;> rw [e] <;> linarith
    have hL' : Real.log (hsn g) * A ≤ 20 * (m : ℝ) ^ 3 + 40 * (m : ℝ) ^ 2 * t := by
      rw [hA]
      nlinarith [mul_le_mul_of_nonneg_left hlogm (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2),
        mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 20 * (m : ℝ) ^ 2)]
    have hk2 := mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ 125 * (m : ℝ) ^ 2)
    nlinarith

end GlobalTheory.SepReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemUnipotentRadicalIffIotaMemAdelicRadical
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeOntoCusp

theorem mem_NI_iff_iota : ∀ (D : D7) {r : ℕ} (C : Matrix (Fin (D.sp.Y 0).rank) (Fin r) D.host.E), IsIsoFrame (D.sp.Y 0) C → ∀ g : GA D (D.sp.Y 0), g ∈ NI (D.sp.Y 0) C ↔ Formalism.IndefR.RationalEmbedding.iota D g ∈ (Formalism.IndefR.RationalEmbedding.inst D).NA (Submodule.span (Formalism.IndefR.RationalEmbedding.inst D).E (Set.range C.col)) := by
  intro D r C hC g
  let I := Formalism.IndefR.RationalEmbedding.inst D
  let T := (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv
  obtain ⟨L, R, hL, hR⟩ :=
    GlobalTheory.CuspCompare.exists_inverses (starRingEnd D.host.E) (J := (D.sp.Y 0).gram) I.J_det hC.2.1
  have key : ∀ h : GA D (D.sp.Y 0),
      T h ∈ I.NA (Submodule.span I.E (Set.range (C : Matrix (Fin I.n) (Fin r) I.E).col)) ↔
      GlobalTheory.CuspCompare.UnipEq (incA D) C R (Formalism.UG.cT (starRingEnd D.host.E) C * (D.sp.Y 0).gram) L
        ((matHom (D.sp.Y 0) h).1 - 1) := fun h => by
    have hs : (Formalism.IndefR.RationalEmbedding.iota D).symm (T h) = h := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply h
    refine GlobalTheory.CuspCompare.mem_NA_iff I (fun v => Formalism.IndefR.Eqv.thetaC D ((Formalism.L2.Host.tauPl D).symm v))
      (fun v => Formalism.IndefR.Eqv.isInfFam_thetaC D ((Formalism.L2.Host.tauPl D).symm v)) h (T h) ?_ (fun v => ?_) hL hR
    · have hb := (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (T h)).2
      have h2 := hb.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin I) hs)
      unfold Formalism.L2.SG.AdBridge.ofHAFin at h2
      rw [Formalism.L2.SG.EvalTIota.tauF_eq_i] at h2
      exact h2
    · obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
      have hb := Formalism.L2.SG.EvalTIota.infMat_brg_i (T h) ρ
      rw [hs] at hb
      simp only [Equiv.symm_apply_apply]
      exact hb.symm
  have hW : I.IsIsot (Submodule.span I.E (Set.range (C : Matrix (Fin I.n) (Fin r) I.E).col)) :=
    (GlobalTheory.CuspCompare.isIsot_iff I _).2 ⟨r, C, hC, rfl⟩
  refine GlobalTheory.CuspCompare.mem_closure_iff_of_equiv T (_root_.GlobalTheory.UnipApprox.strong_approximation I _ hW).1 (fun g => ?_) g
  rw [key]
  exact and_congr Iff.rfl (and_congr Iff.rfl (GlobalTheory.CuspCompare.perp_cond (incA D) hL hR _).2)

end GlobalTheory.SeeOntoCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModerateGrowthSobolevSizeRightTranslatePolyBound
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.Grow GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.Size
open scoped ENNReal NNReal

namespace GlobalTheory.Size.Translate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem wordSum_succ {ι X : Type} [Fintype ι] (A : ι → X → X) (p : X → ℝ≥0∞) (d : ℕ) (x : X) :
    wordSum A p (d + 1) x = p x + ∑ i, wordSum A p d (A i x) := by
  classical
  unfold wordSum
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · simp [wordAct_nil]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Fintype.sum_prod_type']
    symm
    refine Fintype.sum_equiv (Fin.snocEquiv fun _ => ι) _ _ fun q => ?_
    change _ = p (wordAct A (List.ofFn (fun i => (Fin.snoc (α := fun _ => ι) q.2 q.1 i : ι))) x)
    rw [List.ofFn_succ']
    simp [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, wordAct_append, wordAct_cons, wordAct_nil]

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem growthSob_sum_le {α : Type} (s : Finset α) (f : α → GA D V → ℂ) (hf : ∀ a, f a ∈ SmFun θ V) (d N : ℕ) :
    growthSob θ V d N (∑ a ∈ s, f a) ≤ ∑ a ∈ s, growthSob θ V d N (f a) := by
  classical
  induction s using Finset.induction_on
  · simpa using growthSob_smul (θ := θ) (φ := (0 : GA D V → ℂ)) (0 : ℂ) d N
  · rename_i a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (growthSob_add_le (hf a) (Submodule.sum_mem _ fun b _ => hf b) d N).trans (add_le_add le_rfl ih)

theorem growthSob_RderC_le (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hs : φ ∈ SmFun θ V) (τ : D.what₂.Tau)
    {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ} {B : ℝ≥0∞} (hB : ∀ a b, ‖Z a b‖ₑ ≤ B) (d N : ℕ) :
    growthSob θ V d N (RderC θ V τ Z φ) ≤
      (Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0∞) * (B * growthSob θ V (d + 1) N φ) := by
  rw [RderC_eq_sum_glDer hθ hs τ Z]
  have hmem : ∀ a : Fin V.rank × Fin V.rank, Z a.1 a.2 • glDer θ V (τ, a) φ ∈ SmFun θ V := fun a =>
    (SmFun θ V).smul_mem _ ((linOnSm_RderC (θ := θ) τ (Matrix.single a.1 a.2 1)).mem φ hs)
  refine (growthSob_sum_le Finset.univ _ hmem d N).trans ?_
  calc ∑ a : Fin V.rank × Fin V.rank, growthSob θ V d N (Z a.1 a.2 • glDer θ V (τ, a) φ)
      ≤ ∑ _a : Fin V.rank × Fin V.rank, B * growthSob θ V (d + 1) N φ := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [growthSob_smul]
        exact mul_le_mul' (hB a.1 a.2)
          (wordSum_letter_le (A := glDer θ V) (p := growthSize V N) d (τ, a) φ)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem growthSize_rTr_le (h : GA D V) (N : ℕ) (φ : GA D V → ℂ) :
    growthSize V N (rTr V h φ) ≤ ENNReal.ofReal (height V h) ^ N * growthSize V N φ := by
  obtain ⟨h1, -, -, hmul, -⟩ := height_laws V
  unfold growthSize
  refine iSup_le fun g => ?_
  have hgpos : 0 < height V g := lt_of_lt_of_le one_pos (h1 g)
  have hhpos : 0 < height V h := lt_of_lt_of_le one_pos (h1 h)
  have hghpos : 0 < height V (g * h) := lt_of_lt_of_le one_pos (h1 (g * h))
  have hq : 0 ≤ ‖φ (g * h)‖ / height V (g * h) ^ N := div_nonneg (norm_nonneg _) (pow_pos hghpos N).le
  have key : ‖rTr V h φ g‖ / height V g ^ N ≤ height V h ^ N * (‖φ (g * h)‖ / height V (g * h) ^ N) := by
    change ‖φ (g * h)‖ / height V g ^ N ≤ _
    rw [div_le_iff₀ (pow_pos hgpos N)]
    have hp : height V (g * h) ^ N ≤ (height V g * height V h) ^ N := pow_le_pow_left₀ hghpos.le (hmul g h) N
    calc ‖φ (g * h)‖ = ‖φ (g * h)‖ / height V (g * h) ^ N * height V (g * h) ^ N :=
          (div_mul_cancel₀ _ (pow_pos hghpos N).ne').symm
      _ ≤ ‖φ (g * h)‖ / height V (g * h) ^ N * (height V g * height V h) ^ N := mul_le_mul_of_nonneg_left hp hq
      _ = height V h ^ N * (‖φ (g * h)‖ / height V (g * h) ^ N) * height V g ^ N := by ring
  calc ENNReal.ofReal (‖rTr V h φ g‖ / height V g ^ N)
      ≤ ENNReal.ofReal (height V h ^ N * (‖φ (g * h)‖ / height V (g * h) ^ N)) := ENNReal.ofReal_le_ofReal key
    _ = ENNReal.ofReal (height V h) ^ N * ENNReal.ofReal (‖φ (g * h)‖ / height V (g * h) ^ N) := by
        rw [ENNReal.ofReal_mul (pow_pos hhpos N).le, ENNReal.ofReal_pow hhpos.le]
    _ ≤ ENNReal.ofReal (height V h) ^ N * ⨆ g', ENNReal.ofReal (‖φ g'‖ / height V g' ^ N) :=
        by gcongr; exact le_iSup (fun g' => ENNReal.ofReal (‖φ g'‖ / height V g' ^ N)) (g * h)

theorem exists_adAt_le (hθ : IsInfFam θ) (V : HSp D) : ∃ C : ℝ≥0, ∀ (h : GA D V) τ a b c d,
    ‖adAt θ h τ (Matrix.single a b 1) c d‖ₑ ≤ C * ENNReal.ofReal (height V h) ^ 2 := by
  obtain ⟨C, hC⟩ := normInf_le_height V hθ
  refine ⟨Real.toNNReal (C ^ 2), fun h τ a b c d => ?_⟩
  have hent : ∀ i j, ‖infMat D.sp.cm.sig V.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j‖ ≤
      C * height V h := by
    intro i j
    refine le_trans ?_ (hC h)
    calc ‖infMat D.sp.cm.sig V.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j‖
        ≤ ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ) h i j'‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j'‖) :=
          Finset.single_le_sum (f := fun j' => ‖infMat D.sp.cm.sig V.gram (θ τ) h i j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j'‖) (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ) h i' j'‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i' j'‖) :=
          Finset.single_le_sum (f := fun i' => ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ) h i' j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i' j'‖)) (fun _ _ => by positivity) (Finset.mem_univ i)
      _ ≤ ∑ τ', ∑ i', ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ') h i' j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ') h⁻¹ i' j'‖) :=
          Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ') h i' j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ') h⁻¹ i' j'‖)) (fun _ _ => by positivity) (Finset.mem_univ τ)
      _ = _ := rfl
  have hcomp : adAt θ h τ (Matrix.single a b 1) c d =
      infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a * infMat D.sp.cm.sig V.gram (θ τ) h b d := by
    simp [adAt, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have hx := hent c a
  have hy := hent b d
  have hx' : ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a‖ ≤ C * height V h := by
    linarith [norm_nonneg (infMat D.sp.cm.sig V.gram (θ τ) h c a)]
  have hy' : ‖infMat D.sp.cm.sig V.gram (θ τ) h b d‖ ≤ C * height V h := by
    linarith [norm_nonneg (infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ b d)]
  have hht : 0 ≤ height V h := le_trans zero_le_one ((height_laws V).1 h)
  have hreal : ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a‖ * ‖infMat D.sp.cm.sig V.gram (θ τ) h b d‖ ≤
      C ^ 2 * height V h ^ 2 := by
    calc _ ≤ (C * height V h) * (C * height V h) :=
          mul_le_mul hx' hy' (norm_nonneg _) ((norm_nonneg _).trans hx')
      _ = C ^ 2 * height V h ^ 2 := by ring
  rw [hcomp, ← ofReal_norm_eq_enorm, norm_mul]
  calc ENNReal.ofReal (‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a‖ * ‖infMat D.sp.cm.sig V.gram (θ τ) h b d‖)
      ≤ ENNReal.ofReal (C ^ 2 * height V h ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by rw [ENNReal.ofReal_mul (sq_nonneg C), ENNReal.ofReal_pow hht]; rfl

private theorem rderC_rTr' (hθ : IsInfFam θ) (h : GA D V) {φ : GA D V → ℂ} (hs : φ ∈ SmFun θ V)
    (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ Z (rTr V h φ) = rTr V h (RderC θ V τ (adAt θ h τ Z) φ) := by
  obtain ⟨hX, hY⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  have hZ := (GlobalTheory.SmoothAutCheck.parts_sum V τ Z).symm
  set X := (1 / 2 : ℂ) • (Z + conjAt V τ Z) with hXdef
  set Y := (1 / (2 * Complex.I)) • (Z - conjAt V τ Z) with hYdef
  have hsum : adAt θ h τ Z = adAt θ h τ X + Complex.I • adAt θ h τ Y := by
    conv_lhs => rw [hZ]
    simp only [adAt, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hsum, RderC_add hθ hs, RderC_smul hθ hs,
    GlobalTheory.SmoothAutCheck.RderC_eq θ V τ (adAt_mem_lieAt hθ h hX),
    GlobalTheory.SmoothAutCheck.RderC_eq θ V τ (adAt_mem_lieAt hθ h hY)]
  change Rder θ V τ X (rTr V h φ) + Complex.I • Rder θ V τ Y (rTr V h φ) = _
  rw [Rder_rTr_adelic hθ h hX, Rder_rTr_adelic hθ h hY]
  rfl

theorem exists_growthSob_rTr_le (hθ : IsInfFam θ) (V : HSp D) (N d : ℕ) : ∃ C : ℝ≥0, ∀ h ∈ GinfC V, ∀ φ ∈ SmFun θ V,
    growthSob θ V d N (rTr V h φ) ≤ C * ENNReal.ofReal (height V h) ^ (N + 2 * d) * growthSob θ V d N φ := by
  obtain ⟨C₁, hC₁⟩ := exists_adAt_le hθ V
  induction d with
  | zero =>
    refine ⟨1, fun h _ φ _ => ?_⟩
    simpa [growthSob, wordSum_zero] using growthSize_rTr_le h N φ
  | succ d ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨1 + (Fintype.card (D.what₂.Tau × Fin V.rank × Fin V.rank) : ℝ≥0) * C *
      (Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0) * C₁, fun h hh φ hs => ?_⟩
    have hT : 1 ≤ ENNReal.ofReal (height V h) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal ((height_laws V).1 h)
    have hS0 : growthSize V N φ ≤ growthSob θ V (d + 1) N φ :=
      le_wordSum (A := glDer θ V) (p := growthSize V N) (l := []) (Nat.zero_le _) φ
    have hterm : ∀ a : D.what₂.Tau × Fin V.rank × Fin V.rank,
        growthSob θ V d N (glDer θ V a (rTr V h φ)) ≤
          C * ENNReal.ofReal (height V h) ^ (N + 2 * d) *
            ((Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0∞) *
              ((C₁ * ENNReal.ofReal (height V h) ^ 2) * growthSob θ V (d + 1) N φ)) := by
      intro a
      have e : glDer θ V a (rTr V h φ) =
          rTr V h (RderC θ V a.1 (adAt θ h a.1 (Matrix.single a.2.1 a.2.2 1)) φ) :=
        rderC_rTr' hθ h hs a.1 _
      rw [e]
      refine (hC h hh _ ((linOnSm_RderC (θ := θ) a.1 _).mem φ hs)).trans ?_
      gcongr
      exact growthSob_RderC_le hθ hs a.1 (fun b c => hC₁ h a.1 a.2.1 a.2.2 b c) d N
    have hpow : ENNReal.ofReal (height V h) ^ N ≤ ENNReal.ofReal (height V h) ^ (N + 2 * (d + 1)) :=
      pow_le_pow_right₀ hT (by omega)
    have e0 : growthSob θ V (d + 1) N (rTr V h φ) =
        growthSize V N (rTr V h φ) + ∑ a, growthSob θ V d N (glDer θ V a (rTr V h φ)) :=
      wordSum_succ _ _ _ _
    rw [e0]
    calc growthSize V N (rTr V h φ) + ∑ a, growthSob θ V d N (glDer θ V a (rTr V h φ))
        ≤ ENNReal.ofReal (height V h) ^ (N + 2 * (d + 1)) * growthSob θ V (d + 1) N φ +
          ∑ _a : D.what₂.Tau × Fin V.rank × Fin V.rank, C * ENNReal.ofReal (height V h) ^ (N + 2 * d) *
            ((Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0∞) *
              ((C₁ * ENNReal.ofReal (height V h) ^ 2) * growthSob θ V (d + 1) N φ)) :=
          add_le_add ((growthSize_rTr_le h N φ).trans (mul_le_mul' hpow hS0))
            (Finset.sum_le_sum fun a _ => hterm a)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          push_cast
          ring

theorem growthSob_rTr_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (d N : ℕ), ∃ (C : NNReal) (m : ℕ),
    ∀ h ∈ GinfC V, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V d N (rTr V h φ) ≤
      (C : ENNReal) * ENNReal.ofReal (GlobalTheory.Grow.height V h ^ m) * GlobalTheory.Size.growthSob θ V d N φ := by
  intro D θ hθ V d N
  obtain ⟨C, hC⟩ := exists_growthSob_rTr_le hθ V N d
  refine ⟨C, N + 2 * d, fun h hh φ hφ => ?_⟩
  rw [ENNReal.ofReal_pow (le_trans zero_le_one ((height_laws V).1 h))]
  exact hC h hh φ hφ

end GlobalTheory.Size.Translate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceCoverProd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeProductCover

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  have := D.host.isCMField_hostE
  exact (IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x).trans
    (D.host.conjE_apply D.host.φ₀ x).symm

theorem lev_of_isConjPl (D : D7) {P P' : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.BasicNotions.IsConjPl D.host P P') :
    Formalism.IndefR.Lev.IsConjPl P P' := fun c hc =>
  ⟨RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) c,
    (h c _ rfl).1 hc, by
      show D.host.conj (c : D.host.E) = star (c : D.host.E)
      rw [star_eq_conj]⟩

theorem place_cover_prod : ∀ (D : D7) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg),
    (∀ kv, ((plg kv : ↥Pg) : Formalism.L2.DIV.Pl D.host.E) = D.naut.plGw kv.1 kv.2) →
    ∀ PP : Formalism.L2.DIV.Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal →
      PP ∈ Pg ∨ ∃ PP' ∈ Pg, IsConjPl PP' PP := by
  intro D Pg plg hplg PP hPP
  have hmul : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rw [← Nat.cast_mul]; exact hPP
  have hk : ∃ k : Fin 2, PP ∈ placesOver D.host.E (D.host.g k) := by
    rcases PP.isPrime.mem_or_mem hmul with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨k, hk⟩ := hk
  obtain ⟨v, hv | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k PP hk
  · left
    rw [hv, ← hplg ⟨k, v⟩]
    exact (plg ⟨k, v⟩).2
  · right
    refine ⟨(plg ⟨k, v⟩ : Formalism.L2.DIV.Pl D.host.E), (plg ⟨k, v⟩).2, ?_⟩
    rw [hplg ⟨k, v⟩]
    exact lev_of_isConjPl D hv

end GlobalTheory.TypeProductCover
end
end

