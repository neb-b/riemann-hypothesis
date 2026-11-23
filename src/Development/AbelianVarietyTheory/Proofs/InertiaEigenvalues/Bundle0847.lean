module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0820
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0835
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0825
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0836
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarisedThetaIntegralUnfoldWhittaker
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

theorem lastRow_uGL_mul (X : GroundTheory.Automorphic.FourierWhittaker.Pos (m + 1) → Ad E) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow (GroundTheory.Automorphic.FourierWhittaker.uGL X * g) = GlobalTheory.ZEul.lastRow g := by
  funext j
  simp only [GlobalTheory.ZEul.lastRow, Units.val_mul, GroundTheory.Automorphic.FourierWhittaker.coe_uGL, Matrix.mul_apply,
    GroundTheory.Automorphic.FourierWhittaker.uMat_apply]
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp
  · intro c _ hc
    rw [if_neg (Ne.symm hc), dite_eq_right (not_lt.2 (Fin.le_last c)), zero_mul]
  · simp

theorem jswWhit_fT (φ : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (g : GA E (m + 1)) :
    GlobalTheory.JSW.whit (fT φ Φ) g = sqrtC Φ (yInf g) * GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv (yInf g))) := by
  simp only [GlobalTheory.JSW.whit, GroundTheory.Automorphic.FourierWhittaker.whittaker]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only
  rw [fT_of_lastRow (lastRow_uGL_mul X g), mul_assoc (GroundTheory.Automorphic.FourierWhittaker.uGL X) g]
  ring

end GlobalTheory.ZUnf

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

theorem indN_eq_re (N : ℕ) (y : Fin (m + 1) → Af E) : indN N y = ((indN N y).re : ℂ) := by
  unfold indN; split_ifs <;> simp

theorem indN_re_nonneg (N : ℕ) (y : Fin (m + 1) → Af E) : 0 ≤ (indN N y).re := by
  unfold indN; split_ifs <;> simp

theorem wt_coe (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    (((wt N x g : ℝ≥0) : ℝ) : ℂ) = indN N (yFin g) * (detPow E (m + 1) x g : ℂ) := by
  have h0 : 0 ≤ detPow E (m + 1) x g := norm_nonneg _
  rw [wt, Real.coe_toNNReal _ (mul_nonneg (indN_re_nonneg N _) h0), Complex.ofReal_mul, ← indN_eq_re]

theorem sqrtC_mul_conj {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) (u : Fin (m + 1) → Cinf E) :
    sqrtC Φ u * conj (sqrtC Φ u) = Φ u := by
  rw [sqrtC, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hΦ u).1]
  exact Complex.ext (by simp) (by simp [(hΦ u).2])

theorem psi_lastRow_eq {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (φ φ' : GA E (m + 1) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ) =
      fT φ Φ g * conj (fT φ' Φ g) * (((wt N x g : ℝ≥0) : ℝ) : ℂ) := by
  rw [wt_coe, fT, fT, map_mul]
  have h := sqrtC_mul_conj hΦ (yInf g)
  change φ (g * (infGL E (m + 1)) (secInv (yInf g))) * conj (φ' (g * (infGL E (m + 1)) (secInv (yInf g)))) *
    Φ (yInf g) * indN N (yFin g) * (detPow E (m + 1) x g : ℂ) = _
  rw [← h]
  ring

end GlobalTheory.ZUnf

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

theorem uInt_eq {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (φ φ' : GA E (m + 1) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.uInt φ φ' Φ N x g =
      GlobalTheory.JSW.whit (fT φ Φ) g * conj (GlobalTheory.JSW.whit (fT φ' Φ) g) * (((wt N x g : ℝ≥0) : ℝ) : ℂ) := by
  rw [wt_coe, jswWhit_fT, jswWhit_fT, map_mul]
  have h := sqrtC_mul_conj hΦ (yInf g)
  change GlobalTheory.JSW.whit φ (g * (infGL E (m + 1)) (secInv (yInf g))) *
    conj (GlobalTheory.JSW.whit φ' (g * (infGL E (m + 1)) (secInv (yInf g)))) *
    Φ (yInf g) * indN N (yFin g) * (detPow E (m + 1) x g : ℂ) = _
  rw [← h]
  ring


omit [_root_.NumberField.IsTotallyComplex E] in
theorem NE_eq_ratMirU_zero : GlobalTheory.CellDec.NE E (m + 1) = ratMirU E (m + 1) 0 := by
  have h : GlobalTheory.SmGL.unipB E (Fin (m + 1)) = mirU E (m + 1) 0 := by
    ext γ
    rw [GlobalTheory.SmGL.mem_unipB, mem_mirU_zero]
  rw [GlobalTheory.CellDec.NE, ratMirU, h]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem isMir_of_mem_mirU_zero {γ : GL (Fin (m + 1)) E} (hγ : γ ∈ mirU E (m + 1) 0) : IsMir m γ := by
  intro i k h
  refine hγ i k (Nat.zero_le _) ?_
  rcases h with h | h
  · have := k.2; change (k : ℕ) ≤ i; omega
  · have := k.2; omega

end GlobalTheory.ZUnf

namespace GlobalTheory.ZUnf
open GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host

theorem enorm_uInt_self {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}
    {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (φ : GA E (m + 1) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) :
    ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ = ‖GlobalTheory.JSW.whit (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) := by
  rw [uInt_eq hΦ, enorm_mul, enorm_mul, RCLike.enorm_conj, pow_two]
  congr 1
  have h0 : (((wt N x g : ℝ≥0) : ℝ) : ℂ) = ((wt N x g : ℝ≥0) : ℂ) := rfl
  rw [h0, enorm_eq_nnnorm]
  congr 1
  ext
  simp

set_option synthInstance.maxHeartbeats 400000 in
theorem zint_unfold : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure],
  ∃ c : ℝ, 0 < c ∧ ∀ (π π' : CuspSub E (m + 1)) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω →
    π'.HasCentChar ω' → ∀ φ φ' : GA E (m + 1) → ℂ, φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
    ∀ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N → ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (𝓕 𝓕₀ : Set (GA E (m + 1))), IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ →
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∀ x : ℝ, 1 < x → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ ∂μ ≠ ⊤ → ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ ∂μ ≠ ⊤ →
      IntegrableOn (GlobalTheory.ZEul.uInt φ φ' Φ N x) 𝓕₀ μ ∧
        GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = (c : ℂ) * ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ φ' Φ N x g ∂μ := by
  intro E _ _ _ m μ _
  refine ⟨1, one_pos, ?_⟩
  intro π π' ω ω' hω hω' hπ hπ' φ φ' hφ hφ' N Φ _hN hΦs _hΦc hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x _hx h1 h2
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E (m + 1)
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E (m + 1)
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E (m + 1)
  obtain ⟨𝓕P, h𝓕P⟩ : ∃ 𝓕P, IsFundamentalDomain (ratMirU E (m + 1) m) 𝓕P μ := by
    haveI : DiscreteTopology (ratMirU E (m + 1) m) := discrete_of_le_range (Subgroup.map_le_range _ _)
    exact GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain _ μ
  have h𝓕₀' : IsFundamentalDomain (ratMirU E (m + 1) 0) 𝓕₀ μ := NE_eq_ratMirU_zero (E := E) (m := m) ▸ h𝓕₀
  obtain ⟨hc, hl, hv⟩ := _root_.GlobalTheory.JSW.mspanR_cont_left_avg E m π ω hω hπ φ hφ
  obtain ⟨hc', hl', hv'⟩ := _root_.GlobalTheory.JSW.mspanR_cont_left_avg E m π' ω' hω' hπ' φ' hφ'
  have hΦcont : Continuous Φ := hΦs.continuous
  have hG := _root_.GlobalTheory.ZUnf.good_fT E m φ hc hl hv Φ hΦcont hΦr (GlobalTheory.StdCharConductor.psi E)
  have hG' := _root_.GlobalTheory.ZUnf.good_fT E m φ' hc' hl' hv' Φ hΦcont hΦr (GlobalTheory.StdCharConductor.psi E)
  obtain ⟨hwm, hwΓ, hwU⟩ := GlobalTheory.T.lastRowCongruenceDetWeight_measurable_invariant E m N x
  have hU := GlobalTheory.MirTower.unfold_mirabolic E (m + 1) μ (GlobalTheory.StdCharConductor.psi E) (GlobalTheory.StdCharConductor.stdPsi_psi E)
    𝓕P 𝓕₀ h𝓕P h𝓕₀' (wt N x) hwm hwΓ hwU
  have hW : ∀ f : GA E (m + 1) → ℂ, Good (GlobalTheory.StdCharConductor.psi E) m f → ∀ g,
      GlobalTheory.JSW.whit f g = GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f g := fun f hf g =>
    _root_.GlobalTheory.WhitCols.whit_eq_colWhit E m f hf.cont (fun γ hγ g => hf.left γ (isMir_of_mem_mirU_zero hγ) g) g
  have hd : ∫⁻ g in 𝓕P, ‖fT φ Φ g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG]
    show ∫⁻ g in 𝓕₀, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤
    have e : ∀ g, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) =
        ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ := fun g => by rw [enorm_uInt_self hΦp, hW _ hG]
    simp only [e]
    exact h1
  have hd' : ∫⁻ g in 𝓕P, ‖fT φ' Φ g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤ := by
    rw [hU.1 _ hG']
    show ∫⁻ g in 𝓕₀, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) ∂μ ≠ ⊤
    have e : ∀ g, ‖GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g‖ₑ ^ 2 * (wt N x g : ℝ≥0∞) =
        ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ := fun g => by rw [enorm_uInt_self hΦp, hW _ hG']
    simp only [e]
    exact h2
  obtain ⟨hI1, hI2, hEq⟩ := hU.2 _ _ hG hG' hd hd'
  have e1 : GlobalTheory.ZEul.uInt φ φ' Φ N x = fun g => GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ Φ) g *
      conj (GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m (fT φ' Φ) g) * ((wt N x g : ℝ) : ℂ) := by
    funext g
    rw [uInt_eq hΦp, hW _ hG, hW _ hG']
  have e2 : (fun g => Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)) =
      fun g => fT φ Φ g * conj (fT φ' Φ g) * ((wt N x g : ℝ) : ℂ) := funext fun g => psi_lastRow_eq hΦp φ φ' N x g
  have hfin : ∫⁻ g in 𝓕P, ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ ∂μ ≠ ⊤ := by
    rw [show (fun g => ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ) =
      fun g => ‖fT φ Φ g * conj (fT φ' Φ g) * ((wt N x g : ℝ) : ℂ)‖ₑ from funext fun g => by rw [psi_lastRow_eq hΦp]]
    exact hI1.2.ne
  refine ⟨by rw [e1]; exact hI2, ?_⟩
  have hUnfold := GlobalTheory.ZUnfTheta.zint_eq_mirabolic E m μ 𝓕 𝓕P h𝓕 h𝓕P
    φ φ' hc.measurable hc'.measurable hl hl' N Φ hΦcont x hfin
  rw [hUnfold, e2, Complex.ofReal_one, one_mul, e1]
  exact hEq

end GlobalTheory.ZUnf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergLocalTermEqSphericalWhittakerProduc
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.ZEulLocal

theorem wtS_eq_sum (n : ℕ) (a : Fin n → ℤ) :
    GlobalTheory.CellDec.wtS n a = ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * a i := by
  have h1 : ∀ i : Fin n, (∑ j : Fin n, if i < j then a i - a j else 0) =
      (∑ j : Fin n, if i < j then a i else 0) - ∑ j : Fin n, if i < j then a j else 0 := by
    intro i
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [GlobalTheory.CellDec.wtS, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib,
    Finset.sum_comm (f := fun i j => if i < j then a j else 0)]
  simp only [← Finset.sum_filter, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Finset.sum_const,
    Fin.card_Ioi, Fin.card_Iio, nsmul_eq_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring


open GlobalTheory.JSW in
theorem localTerm_eq : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ), (∀ i, 0 ≤ v i) → Antitone v →
    (((q : ℝ) ^ GlobalTheory.CellDec.wtS n v : ℝ) : ℂ) *
      (GlobalTheory.JSW.sphW q α (fun i => (v i).toNat) * conj (GlobalTheory.JSW.sphW q β (fun i => (v i).toNat))) *
      (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = GlobalTheory.ZEul.rsTerm q α β x v := by
  intro q hq n α β x v h0 hv
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hl : Antitone (fun i => (v i).toNat) := fun i j hij => Int.toNat_le_toNat (hv hij)
  have hcast : ∀ i, (((v i).toNat : ℕ) : ℂ) = ((v i : ℝ) : ℂ) := by
    intro i
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (h0 i)]
    simp
  set cR : ℝ := ∑ i : Fin n, ((n : ℝ) - 1 - 2 * (i : ℕ)) * (v i : ℝ) with hcR
  have hc : (∑ i : Fin n, (((n : ℂ) - 1 - 2 * (i : ℕ)) * (((v i).toNat : ℕ) : ℂ))) = (cR : ℂ) := by
    rw [hcR]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcast i, Complex.ofReal_intCast]
  set A : ℝ := (q : ℝ) ^ (-cR / 2) with hA'
  have hA : (q : ℂ) ^ (-(cR : ℂ) / 2) = (A : ℂ) := by
    rw [hA', Complex.ofReal_cpow hqR.le]
    push_cast
    rfl
  have hW : (GlobalTheory.CellDec.wtS n v : ℝ) = cR := by
    rw [GlobalTheory.ZEulLocal.wtS_eq_sum, hcR]
    push_cast
    rfl
  have key : (q : ℝ) ^ GlobalTheory.CellDec.wtS n v * (A * A) = 1 := by
    rw [hA', ← Real.rpow_add hqR, ← Real.rpow_intCast, ← Real.rpow_add hqR, hW]
    rw [show cR + (-cR / 2 + -cR / 2) = 0 by ring, Real.rpow_zero]
  have key2 : (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat) := by
    have e : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hqR.le]
      push_cast
      rfl
    rw [e, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul hqR.le]
    congr 3
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    exact_mod_cast (Int.toNat_of_nonneg (h0 i)).symm
  rw [sphW, sphW, if_pos hl, if_pos hl, hc, hA, GlobalTheory.ZEul.rsTerm, if_pos ⟨h0, hv⟩, key2, map_mul,
    Complex.conj_ofReal]
  calc _ = (((q : ℝ) ^ GlobalTheory.CellDec.wtS n v * (A * A) : ℝ) : ℂ) *
        (schurAt (fun i => (v i).toNat) α * conj (schurAt (fun i => (v i).toNat) β) *
          ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat)) := by push_cast; ring
    _ = _ := by rw [key]; simp

end GlobalTheory.ZEulLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatCopyIff
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.Move.RatUp

variable {D : D7} (r : Rest D)

theorem placeMap_up {S T : HSp D} (B : Base S T) (a : AE D) :
    HEq ((baseUp r B).F.placeMap ((a))) (B.F.placeMap a) := by
  have h : (fun Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) =>
      (IsPlaceModel (baseUp r B).F.ψ (symplO _ _) (heisO (baseUp r B).F.ψ _ _) ((by with_unfolding_all exact (a :))) (baseUp r B).F.lat 1 (baseUp r B).F.f₀
        ((by with_unfolding_all exact (Tm :))))) = IsPlaceModel B.F.ψ (symplO S T) (heisO B.F.ψ S T) a B.F.lat 1 B.F.f₀ :=
    funext fun Tm => propext ⟨fun g => ⟨(by with_unfolding_all exact (g.1 :)), (by with_unfolding_all exact (g.2 :)), (by with_unfolding_all exact (g.3 :))⟩, fun g => ⟨(by with_unfolding_all exact (g.1 :)), (by with_unfolding_all exact (g.2 :)), (by with_unfolding_all exact (g.3 :))⟩⟩
  exact (by with_unfolding_all exact ((heq_of_eq (congrArg Classical.epsilon h)) :))

open Classical in
theorem vecAt_up {S T : HSp D} (B : Base S T) : (baseUp r B).vecAt = (B.vecAt) := by
  delta ExportSeries.Base.vecAt Frame.vec
  rewrite [show (baseUp r B).F.placeMap = ((by with_unfolding_all exact (B.F.placeMap :))) from (by with_unfolding_all exact ((funext fun a => eq_of_heq (placeMap_up r B a)) :))]
  exact (by with_unfolding_all exact ((Eq.refl B.vecAt) :))

theorem theta_up {S T : HSp D} (B : Base S T) : (baseUp r B).theta = (B.theta) := by
  delta ExportSeries.Base.theta ExportSeries.Base.vecBase
  rewrite [vecAt_up r B]
  exact (by with_unfolding_all exact ((Eq.refl B.theta) :))

theorem genSet_up {S T : HSp D} (B : Base S T) (ω) (t : Twist D Circle) :
    (baseUp r B).genSet (((ω : PairRep S T))) (twistUp r t) = ((B.genSet ω t : GA (overD D r) S → PolF (overD D r) T.rank S.rank → Set (GA (overD D r) T → ℂ))) := by
  delta ExportSeries.Base.genSet ExportSeries.Base.gen ExportSeries.Base.vecFlat
  rewrite [vecAt_up r B]
  exact (by with_unfolding_all exact ((Eq.refl (B.genSet ω t)) :))

def univUp {A : Type} [AddCommGroup A] (t : UnivTwist D A) : UnivTwist (overD D r) A := ⟨(by with_unfolding_all exact (t.del :)), (by with_unfolding_all exact (t.kap :))⟩

theorem xiCoef_up {S T : HSp D} {A : Type} [AddCommGroup A] [Fintype A] (B : Base S T) (ω) (u : UnivTwist D A) :
    (baseUp r B).xiCoef (((ω : PairRep S T))) (univUp r u) = ((B.xiCoef ω u : (Q : Finset (Pl (overD D r).host.E)) → ((PP : Pl (overD D r).host.E) → A → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ) → GA (overD D r) S → PolF (overD D r) T.rank S.rank → (↥Q → A) → GA (overD D r) T → ℂ)) := by
  delta ExportSeries.Base.xiCoef ExportSeries.Base.xi ExportSeries.Base.vecFam
  rewrite [vecAt_up r B]
  exact (by with_unfolding_all exact ((Eq.refl (B.xiCoef ω u)) :))

section Lat

variable {r} {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0} (h : CopyTw D (overD D r) ι e)
include h

theorem embLL0_up : embLL0 (overD D r) = (embLL0 D).comp e.toRingHom := RingHom.ext fun x => (h.embLL0_eq x).symm

theorem labLL0_up (τ : D.what₂.Tau) : e.toRingHom.comp (labLL0 (overD D r) ((τ))) = (labLL0 D τ) := by
  refine RingHom.ext fun x => (embLL0 D).injective ((h.embLL0_eq _).trans ?_)
  have a := DFunLike.congr_fun (embLL0_labLL0 (D := overD D r) ((by with_unfolding_all exact (τ :)))) x
  have c := DFunLike.congr_fun (embLL0_labLL0 (D := D) τ) ((by with_unfolding_all exact (x :)))
  refine Eq.trans a ?_
  exact (by with_unfolding_all exact (c.symm :))

theorem coefLat_up {S T : HSp D} (B : Base S T) (O : Subring ℂ) (g : Bridge.Gf S) :
    (baseUp r B).coefLat (embLL0 (overD D r)) (labLL0 (overD D r)) O ((g)) = (B.coefLat (embLL0 D) (labLL0 D) O g) := by
  have a := GlobalTheory.CoefLatIso.coefLatFn_ringEquiv D S.rank _ _ e (embLL0 D) ((by with_unfolding_all exact ((labLL0 (overD D r)) :))) O B.w.lam (B.latAt g)
  have c : (fun τ : D.what₂.Tau => e.toRingHom.comp (((by with_unfolding_all exact ((labLL0 (overD D r)) :)) : D.what₂.Tau → (D.host.E →+* ↥(overD D r).LL0)) τ)) =
      labLL0 D := funext fun τ => (by with_unfolding_all exact ((labLL0_up h τ) :))
  rw [← embLL0_up h, c] at a
  exact (by with_unfolding_all exact ((congrArg (fun L : Submodule O (GLR D S.rank → ℂ) => (harm T.rank B.w B.F.BS).restrictScalars O ⊓
    L.comap ((harmFn T.rank B.w B.F.BS).restrictScalars O)) a) :))

end Lat

section Setup

variable (ρ : Setup D.ntw) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

theorem se_theta : (setupUp r ρ).theta ((i)) ((j)) b = (ρ.theta i j b) := by
  funext h P
  have e : @Eq (type_of% (ρ.B i j b).theta) ((by with_unfolding_all exact ((baseUp r (ρ.B i j b)).theta :))) (ρ.B i j b).theta :=
    (by with_unfolding_all exact ((theta_up r (ρ.B i j b)) :))
  exact (by with_unfolding_all exact ((congrArg (fun t : type_of% (ρ.B i j b).theta => t (ρ.om i j b 1) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (P :)))) e) :))

theorem se_gens : (setupUp r ρ).gens ((i)) ((j)) b = (ρ.gens i j b) := by
  funext k Q ψ
  exact (by with_unfolding_all exact ((genSet_up r (ρ.B i j b) (ρ.om i j b 1) (ρ.tw i b k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (ψ :))))) :))

theorem se_xi : (setupUp r ρ).xi ((i)) ((j)) b (overD D r).nexp = (ρ.xi i j b D.nexp) := by
  funext Q M
  exact (by with_unfolding_all exact ((congrFun (congrFun (xiCoef_up r (ρ.B i j b) (ρ.om i j b 1) (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i ((by with_unfolding_all exact (Q :))) M) M ρ.rc))
    ((by with_unfolding_all exact ((half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i ((Q)) M)) : _))))
    ((by with_unfolding_all exact ((ExportSeries.Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i ((Q)) M) M ρ.rc) (ρ.β j)) : _)))) :))

variable {r ρ i j b} {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0} (h : CopyTw D (overD D r) ι e)
include h

theorem se_lat (O : Subring ℂ) (g : GA D (Vc D j)) : (setupUp r ρ).lat ((i)) ((j)) b O ((g)) = (ρ.lat i j b O g) :=
  (by with_unfolding_all exact ((coefLat_up h (ρ.B i j b) O (finPt _ g)) :))

theorem datum_up {s g P} (d : ρ.IsDatum i j b s g P) : (setupUp r ρ).IsDatum ((i)) ((j)) b ((s)) ((g)) ((P)) :=
  ⟨(by with_unfolding_all exact (d.split :)), (by with_unfolding_all exact (d.off :)), (by with_unfolding_all exact (d.fin :)), (by with_unfolding_all exact (d.supp :)), by
    have a := se_lat (ρ := ρ) (i := i) (j := j) (b := b) h (ρ.eO i b).range g
    have c := (le_of_eq a.symm) ((by with_unfolding_all exact (d.mem :)) : ((by with_unfolding_all exact (P :))) ∈ _)
    exact (by with_unfolding_all exact (c :))⟩

theorem datum_dn {s g P} (d : (setupUp r ρ).IsDatum ((i)) ((j)) b s g P) : ρ.IsDatum i j b ((s)) ((g)) ((P)) :=
  ⟨(by with_unfolding_all exact (d.split :)), (by with_unfolding_all exact (d.off :)), (by with_unfolding_all exact (d.fin :)), (by with_unfolding_all exact (d.supp :)), by
    have a := se_lat (ρ := ρ) (i := i) (j := j) (b := b) h (ρ.eO i b).range ((by with_unfolding_all exact (g :)))
    have c := (le_of_eq a) ((by with_unfolding_all exact (d.mem :)) : ((by with_unfolding_all exact (P :))) ∈ _)
    exact (by with_unfolding_all exact (c :))⟩


omit h in
variable (r) in
def rdUp (rd : Rd ρ D.nexp i j b) : Rd (setupUp r ρ) (overD D r).nexp ((i)) ((j)) b := (rd)

theorem rat_up {hρ : ρ.Good} {hρ' : (setupUp r ρ).Good} {rd : Rd ρ D.nexp i j b} (g : SeriesTie.Rat hρ rd) :
    SeriesTie.Rat hρ' (rdUp r rd) := by
  refine ⟨fun s x P d => ?_, fun k Q ψ h1 h2 s x P d => ?_, fun Q M h1 s x P d h2 a => ?_⟩
  · rewrite [se_theta r ρ i j b]
    exact (by with_unfolding_all exact ((g.1 _ _ _ (datum_dn h d)) :))
  · rewrite [se_gens r ρ i j b]
    exact (by with_unfolding_all exact ((g.2.1 k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (h1 :))) ((by with_unfolding_all exact (h2 :))) _ _ _ (datum_dn h d)) :))
  · rewrite [se_xi r ρ i j b]
    exact (by with_unfolding_all exact ((g.2.2 ((by with_unfolding_all exact (Q :))) M ((by with_unfolding_all exact (h1 :))) _ _ _ (datum_dn h d) ((by with_unfolding_all exact (h2 :))) ((by with_unfolding_all exact (a :)))) :))

theorem rat_dn {hρ : ρ.Good} {hρ' : (setupUp r ρ).Good} {rd : Rd ρ D.nexp i j b} (g : SeriesTie.Rat hρ' (rdUp r rd)) :
    SeriesTie.Rat hρ rd := by
  refine ⟨fun s x P d => ?_, fun k Q ψ h1 h2 s x P d => ?_, fun Q M h1 s x P d h2 a => ?_⟩
  · have c := g.1 _ _ _ (datum_up h d)
    rewrite [se_theta r ρ i j b] at c
    exact (by with_unfolding_all exact (c :))
  · have c := g.2.1 k ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (h1 :))) ((by with_unfolding_all exact (h2 :))) _ _ _ (datum_up h d)
    rewrite [se_gens r ρ i j b] at c
    exact (by with_unfolding_all exact (c :))
  · have c := g.2.2 ((by with_unfolding_all exact (Q :))) M ((by with_unfolding_all exact (h1 :))) _ _ _ (datum_up h d) ((by with_unfolding_all exact (h2 :))) ((by with_unfolding_all exact (a :)))
    rewrite [se_xi r ρ i j b] at c
    exact (by with_unfolding_all exact (c :))

end Setup

theorem rat_copy_iff {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e) {ρ : Setup D.ntw}
    {ρ' : Setup D'.ntw} (hs : SameSetup ρ ρ') (hρ : ρ.Good) (hρ' : ρ'.Good) (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ')
    (hrd : RdRel h rd rd') (i : D.ntw.Tw) (i' : D'.ntw.Tw) (hi : HEq i i') (j : Fin D.R.m) (b : Bool) :
    SeriesTie.Rat hρ (rd i j b) ↔ SeriesTie.Rat hρ' (rd' i' (h.cm j) b) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  obtain rfl := SameData.eq_up r hs
  have e0 : @Eq D.ntw.Tw ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (i' :))) := (by with_unfolding_all exact ((@eq_of_heq D.ntw.Tw i ((by with_unfolding_all exact (i' :))) ((by with_unfolding_all exact (hi :)))) :))
  have e1 : ∀ (i' : (overD D r).ntw.Tw) (hi : HEq ((by with_unfolding_all exact (i' :)) : D.ntw.Tw) i') (j' : Fin (overD D r).R.m),
      rd' i' j' b = (by with_unfolding_all exact ((rdUp r (rd ((by with_unfolding_all exact (i' :))) ((by with_unfolding_all exact (j' :))) b)) :)) := fun i' hi j' => by
    refine LinearMap.ext fun f => ?_
    have a := hrd _ i' hi ((by with_unfolding_all exact (j' :))) b ((by with_unfolding_all exact (f :)))
    have c : h.fmCast hi ((j' : ℕ) + 1) b ((by with_unfolding_all exact (f :))) = (by with_unfolding_all exact (f :)) := (by with_unfolding_all exact ((eq_of_heq (h.fmCast_heq hi ((j' : ℕ) + 1) b ((by with_unfolding_all exact (f :))))) :))
    have a' : HEq (rd' i' j' b (h.fmCast hi ((j' : ℕ) + 1) b ((by with_unfolding_all exact (f :))))) (rd ((by with_unfolding_all exact (i' :))) ((by with_unfolding_all exact (j' :))) b ((by with_unfolding_all exact (f :)))) := (by with_unfolding_all exact (a :))
    rewrite [c] at a'
    exact (by with_unfolding_all exact ((@eq_of_heq (GA (overD D r) (Wc (overD D r) j') → ℂ) (rd' i' j' b f) ((by with_unfolding_all exact ((rd ((i')) ((j')) b ((f))) : _))) ((by with_unfolding_all exact (a' :)))) :))
  subst e0
  rewrite [e1 _ hi (h.cm j)]
  exact ⟨fun g => (by with_unfolding_all exact ((rat_up h (hρ' := hρ') g) :)), fun g => rat_dn h (hρ' := hρ') ((by with_unfolding_all exact (g :)))⟩

end GlobalTheory.TwInputs.Move.RatUp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexSplitPlaceEqMulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLatticeIndex_splitPlace_eq_mul : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (h' : w'.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → w ≠ w' → ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = GlobalTheory.LocKerMod.idxAt T w h g * GlobalTheory.LocKerMod.idxAt T w' h' g := by
  first | exact @GlobalTheory.SplitLatIdx.latIndex_split | exact GlobalTheory.SplitLatIdx.latIndex_split | (intros; apply GlobalTheory.SplitLatIdx.latIndex_split <;> assumption)
end

