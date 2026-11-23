module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDenseFin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsMain
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0049
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdelicHermitianHyperbolicEAnisotropicEqZero
section
noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB PIW.AdelClassFin

attribute [local instance] starRA

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem mulVec_cols' {m p : Type*} [Fintype p] [DecidableEq p] (M : Matrix m p (RA X)) (c : p → RA X) :
    M *ᵥ c = ∑ k, c k • (M *ᵥ Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single c]
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (Pi.single k (c k) : p → RA X) = c k • Pi.single k 1 by ext j; simp [Pi.single_apply],
    Matrix.mulVec_smul]

theorem Bf_col (k : Kap X) : Bf X *ᵥ Pi.single k 1 = incl X.B.I (bv X k) := by
  rw [mulVec_single_one]
  rfl

theorem Bf'_incl (k : Kap X) : Bf' X *ᵥ incl X.B.I (bv X k) = Pi.single k 1 := by
  rw [← Bf_col, Matrix.mulVec_mulVec, Bf'_mul_Bf, Matrix.one_mulVec]

theorem hA_sum' (x : VA X.B.I) (s : Finset (Kap X)) (c : Kap X → RA X) (v : Kap X → VA X.B.I) :
    hA X.B.I x (∑ k ∈ s, c k • v k) = ∑ k ∈ s, c k * hA X.B.I x (v k) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact DictLat.hhat_zero_right X.B.I x
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rw [show hA X.B.I x (c a • v a + ∑ k ∈ s, c k • v k) =
        hA X.B.I x (c a • v a) + hA X.B.I x (∑ k ∈ s, c k • v k) from DictLat.hhat_add_right X.B.I _ _ _]
    rw [show hA X.B.I x (c a • v a) = c a * hA X.B.I x (v a) from DictLat.hhat_smul_right X.B.I _ _ _]

theorem hA_incl (v w : Fin X.B.I.n → X.B.I.E) :
    hA X.B.I (incl X.B.I v) (incl X.B.I w) = ic X (Formalism.L2.SG.Pf.UnipB.hE X v w) := DictLat.hhat_iv X.B.I v w

theorem hA_e_Bf (a : Fin D.R.rS) (c : Kap X → RA X) :
    hA X.B.I (incl X.B.I (X.eR a)) (Bf X *ᵥ c) = c (Sum.inr (Sum.inr a)) := by
  rw [mulVec_cols', hA_sum']
  have e : ∀ k, hA X.B.I (incl X.B.I (X.eR a)) (Bf X *ᵥ Pi.single k 1) = ic X (JB X (Sum.inl a) k) := by
    intro k
    rw [Bf_col]
    exact hA_incl X (X.eR a) (bv X k)
  simp only [e, JB_e_row]
  simp

theorem hA_e_w (a : Fin D.R.rS) (i : Fin (mW X)) :
    hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (bv X (Sum.inr (Sum.inl i)))) = 0 := by
  rw [hA_incl]
  have := (wb_mem X i a).1
  simp only [bv, Sum.elim_inr, Sum.elim_inl]
  rw [this, map_zero]

theorem adelicHermitian_hyperbolicE_anisotropic_eq_zero (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.zR u)) = 0 := by
  rw [hA_incl, hE_ez X u a, map_zero]

theorem Bf_mulVec_mem (S : Set (Fin D.R.rS)) (c : Kap X → RA X) (hc : ∀ k, k ∉ Sum.inl '' S → c k = 0) :
    Bf X *ᵥ c ∈ Submodule.span (RA X) ((fun b => incl X.B.I (X.eR b)) '' S) := by
  rw [mulVec_cols']
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : k ∈ Sum.inl '' S
  · obtain ⟨b, hb, rfl⟩ := hk
    rw [Bf_col]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · rw [hc k hk, zero_smul]
    exact Submodule.zero_mem _

theorem Bf'_mulVec_supp (S : Set (Fin D.R.rS)) {y : VA X.B.I}
    (hy : y ∈ Submodule.span (RA X) ((fun b => incl X.B.I (X.eR b)) '' S)) :
    ∀ k, k ∉ Sum.inl '' S → (Bf' X *ᵥ y) k = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    intro k hk
    show (Bf' X *ᵥ incl X.B.I (bv X (Sum.inl b))) k = 0
    rw [Bf'_incl, Pi.single_apply, if_neg]
    rintro rfl
    exact hk ⟨b, hb, rfl⟩
  | zero => intro k _; simp
  | add x y _ _ hx hy => intro k hk; rw [Matrix.mulVec_add, Pi.add_apply, hx k hk, hy k hk, add_zero]
  | smul c x _ hx => intro k hk; rw [Matrix.mulVec_smul, Pi.smul_apply, hx k hk, smul_zero]

theorem nf_of_pat (x : X.B.I.Gf) (hpat : InPat (lvk X) 1 (Mf X x - 1)) : x ∈ X.NfinU u := by
  set M := Mf X x with hM
  have hg : X.B.I.fmat x - 1 = Bf X * (M - 1) * Bf' X := by
    rw [hM, Mf, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bf_mul_Bf']
    simp only [← Matrix.mul_assoc, Bf_mul_Bf', Matrix.one_mul]
    rw [Matrix.mul_assoc, Bf_mul_Bf', Matrix.mul_one]
  have hgv : ∀ y, (X.B.I.fmat x - 1) *ᵥ y = Bf X *ᵥ ((M - 1) *ᵥ (Bf' X *ᵥ y)) := by
    intro y
    rw [hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hperp : ∀ y : VA X.B.I, (∀ a, hA X.B.I (incl X.B.I (X.eR a)) y = 0) →
      (X.B.I.fmat x - 1) *ᵥ y ∈ Submodule.span (RA X) (Set.range fun b => incl X.B.I (X.eR b)) := by
    intro y hy
    set c := Bf' X *ᵥ y with hc
    have hyc : y = Bf X *ᵥ c := by rw [hc, Matrix.mulVec_mulVec, Bf_mul_Bf', Matrix.one_mulVec]
    have hcf : ∀ a, c (Sum.inr (Sum.inr a)) = 0 := by
      intro a
      have := hA_e_Bf X a c
      rw [← hyc, hy a] at this
      exact this.symm
    rw [hgv, ← hc, ← Set.image_univ]
    refine Bf_mulVec_mem X Set.univ _ fun k hk => ?_
    have hk' : ∀ b, k ≠ Sum.inl b := by
      rintro b rfl
      exact hk ⟨b, Set.mem_univ _, rfl⟩
    rw [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hlk := lvk_notinl X k hk'
    rcases j with b | i | b
    · rw [hpat k _ (by rw [lvk_inl]; have := b.2; omega), zero_mul]
    · rw [hpat k _ (by rw [lvk_w]; omega), zero_mul]
    · rw [hcf b, mul_zero]
  show _ ∧ _ ∧ _
  refine ⟨fun a => ?_, hperp _ fun a => adelicHermitian_hyperbolicE_anisotropic_eq_zero X u a, hperp⟩
  rw [hgv]
  rw [show incl X.B.I (X.eR a) = incl X.B.I (bv X (Sum.inl a)) from rfl, Bf'_incl]
  refine Bf_mulVec_mem X {b | b.1 < a.1} _ fun k hk => ?_
  rw [mulVec_single_one]
  refine hpat k _ ?_
  rcases k with b | i | b
  · have : ¬ b.1 < a.1 := fun h => hk ⟨b, h, rfl⟩
    simp only [lvk, Sum.elim_inl]; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; have := b.2; omega

theorem half_fin {y : X.B.I.Gf} (hy : y ∈ X.NfinU u) :
    ∀ i j, lvk X j ≤ D.R.rS + 1 → lvk X j < lvk X i + 1 → (Mf X y - 1) i j = 0 := by
  intro i j hj hij
  have hM : Mf X y - 1 = Bf' X * (X.B.I.fmat y - 1) * Bf X := by
    unfold Mf
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bf'_mul_Bf]
  have hcol : (Mf X y - 1) i j = (Bf' X *ᵥ ((X.B.I.fmat y - 1) *ᵥ incl X.B.I (bv X j))) i := by
    rw [hM, ← Bf_col, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mulVec_single_one]
    rfl
  rw [hcol]
  rcases j with a | w | a
  · refine Bf'_mulVec_supp X {b | b.1 < a.1} (hy.1 a) i ?_
    rintro ⟨b, hb, rfl⟩
    simp only [lvk, Sum.elim_inl, Set.mem_setOf_eq] at hij hb
    omega
  · have h := hy.2.2 _ fun a => hA_e_w X a w
    rw [← Set.image_univ] at h
    refine Bf'_mulVec_supp X Set.univ h i ?_
    rintro ⟨b, -, rfl⟩
    simp only [lvk, Sum.elim_inl, Sum.elim_inr] at hij
    have := b.2
    omega
  · simp only [lvk, Sum.elim_inr] at hj
    have := a.2
    omega

theorem pat_of_nf {x : X.B.I.Gf} (hx : x ∈ X.NfinU u) : InPat (lvk X) 1 (Mf X x - 1) := by
  have hx' : x⁻¹ ∈ X.NfinU u := (Formalism.L2.SG.Pf.NfinSub X.eR (X.zR u)).inv_mem hx
  have hMN : Mf X x = sharp (JBf X) (JBf' X) (Mf X x⁻¹) := by
    have := Mf_inv X x⁻¹
    rwa [inv_inv] at this
  exact half_to_full (JBf_graded X) (JBf'_graded X) (JBf'_mul X) (h₀ := D.R.rS + 1) (by omega) hMN
    (half_fin X u hx') (half_fin X u hx)

theorem pattern_of_nilradical : NfPat := fun _ X u _ hx => pat_of_nf X u hx

theorem nilradical_of_pattern : NfOfPat := fun _ X u x h => nf_of_pat X u x h

theorem cay_inv_R (x : X.B.I.Gf) (hT : InPat (lvk X) 1 (Mf X x - 1)) :
    ∃ Z : Matrix (Kap X) (Kap X) (RA X), InPat (lvk X) 1 Z ∧
      Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) Z * JBf X = -(JBf X * Z) ∧
        cay (2 * D.R.rS + 2) Z = Mf X x := by
  set N := 2 * D.R.rS + 2 with hN
  have hZpat : InPat (lvk X) 1 (icay N (Mf X x)) :=
    inPat_mul hT (inPat_geo (inPat_neg (inPat_smul _ hT)) N)
  have hP : sharp (JBf X) (JBf' X) (Mf X x) = Mf X x⁻¹ := (Mf_inv X x).symm
  have hPM : Mf X x⁻¹ * Mf X x = 1 := by rw [← Mf_mul, inv_mul_cancel, Mf_one]
  have hT' : InPat (lvk X) 1 (Mf X x⁻¹ - 1) := by
    have e : Mf X x⁻¹ - 1 = sharp (JBf X) (JBf' X) (Mf X x - 1) := by
      rw [sharp_sub, hP, sharp_one (JBf'_mul X)]
    rw [e]
    exact inPat_sharp (JBf_graded X) (JBf'_graded X) hT
  have hs := icay_skew (JBf_mul X) (JBf'_mul X) hP hPM (nil_of_pat X le_rfl hT _) (nil_of_pat X le_rfl hT' _)
  refine ⟨icay N (Mf X x), hZpat, ?_, cay_icay (nil_of_pat X le_rfl hT _) (nil_of_pat X le_rfl hZpat _)⟩
  rw [cT_eqR]
  calc (icay N (Mf X x))ᴴ * JBf X = JBf X * sharp (JBf X) (JBf' X) (icay N (Mf X x)) := by
        unfold sharp
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, JBf_mul, Matrix.one_mul]
    _ = -(JBf X * icay N (Mf X x)) := by rw [hs, Matrix.mul_neg]

theorem cayley_inverse_right : CayInvR := fun _ X x h => cay_inv_R X x h

end Formalism.L2.SG.Pf.SlabNDensePf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAt
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.RealObj.EnergyInst

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.EnergyAbs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StepIntAt (D : D7) : Prop :=
  ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ →
      TermOp.OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Set.univ (X.Wu u) (X.Wu u') γ

def StepConvAt (D : D7) : Prop :=
  ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    (∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ →
      ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪X.B.σs z (X.B.tens X.B.w),
          X.B.σs (s * γ * s'⁻¹) (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ * ‖X.Wu u z‖ₑ * ‖X.Wu u' z'‖ₑ
        ∂(muS X u') ∂(muS X u) ∂(X.nuQ u') ∂(X.nuQ u) < ⊤) ∧
    ∀ w : D.what₂.Word,
      ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪X.B.σs z (X.B.tens X.B.w), X.B.σs s (X.B.σs z' (X.B.tens X.B.w))⟫_ℂ‖ₑ *
        ‖X.Wu w z‖ₑ * ‖X.Wu w z'‖ₑ ∂(muS X w) ∂(X.nuQ w) ∂(X.nuQ w) < ⊤

def StepEnergyAt (D : D7) : Prop :=
  ∀ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    DisintegrationConstantPositive X u u' sc → CoordOK X u u' sc → intOOe X u u' sc ≤ ENNReal.ofReal (1 / degX X)

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem stepEnergyAt_of_inst (D : D7) (hE : EnergyAbs) (hS : StepSchurG) (hG : StepSubG) (hSec : StepSection)
    (hC : StepConvAt D) (hI : StepIntAt D) : StepEnergyAt D := by
  classical
  intro X u u' sc hsc h27 _
  obtain ⟨hUR, hSch, hw, -⟩ := hS D X
  obtain ⟨hHu, hFu, -, -, hSFu⟩ := hG D X u
  obtain ⟨hHu', hFu', -, -, hSFu'⟩ := hG D X u'
  obtain ⟨hh, hhm, hhd⟩ := hSec D X u u' sc hsc
  have hGood : MeasurableSet (Good X u u') := by
    rw [Formalism.L2.SG.RealObj.EnergyCut.good_eq_pi X u u']
    exact MeasurableSet.univ_pi fun _ => Formalism.L2.SG.RealObj.EnergyCut.goodV_meas u u'
  by_cases hne : (Good X u u').Nonempty
  swap
  · have h0 : Good X u u' = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [intOOe, nuM, h0]
  obtain ⟨c₀, hc₀⟩ := hne
  let g : Cinf X → X.B.I.Ginf := (Good X u u').piecewise hh (fun _ => hh c₀)
  have hgm : Measurable g := Measurable.piecewise hGood hhm measurable_const
  have hgG : ∀ c ∈ Good X u u', g c = hh c := fun c hc => Set.piecewise_eq_of_mem _ _ _ hc
  have hgd : ∀ c, ∃ c' ∈ Good X u u', HasDiag X u u' sc c' (g c) := by
    intro c
    by_cases hc : c ∈ Good X u u'
    · exact ⟨c, hc, by rw [hgG c hc]; exact hhd c hc⟩
    · refine ⟨c₀, hc₀, ?_⟩
      have : g c = hh c₀ := Set.piecewise_eq_of_notMem _ _ _ hc
      rw [this]; exact hhd c₀ hc₀
  have hgD : ∀ c ∈ Good X u u', HasDiag X u u' sc c (g c) := fun c hc => by
    rw [hgG c hc]; exact hhd c hc
  have hOfD : ∀ c ∈ Good X u u', HasDiag X u u' sc c (hOf X u u' sc c) := by
    intro c hc
    have hex : ∃ γ, HasDiag X u u' sc c γ := ⟨hh c, hhd c hc⟩
    have e : hOf X u u' sc c = hex.choose := dif_pos hex
    rw [e]
    exact hex.choose_spec
  have hD : Disint X u u' sc (DisintegrationConstant X u u' sc) := by
    have e : DisintegrationConstant X u u' sc = h27.choose := dif_pos h27
    rw [e]
    exact h27.choose_spec.2
  have hm : Measurable fun c => ENNReal.ofReal (DisintegrationConstant X u u' sc * wt X u u' c) :=
    ENNReal.measurable_ofReal.comp ((Formalism.L2.SG.RealObj.InfCut.wt_cont X u u').measurable.const_mul _)
  have hDis : Formalism.L2.SG.Pf.EnergyAbs.IsDisint (Formalism.L2.SG.ProjRows.muInf X.B.I) (muS X u) (muS X u')
      (nuM X u u' sc) g := by
    intro φ hφ
    rw [hD φ hφ, nuM, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine lintegral_congr_ae (ae_restrict_of_forall_mem hGood fun c hc => ?_)
    simp only [Pi.mul_apply]
    congr 1
    obtain ⟨a, ha, b, hb, hab⟩ :=
      InfCut.UnitaryIsometries.StepDiagDC_holds D X u u' sc c hc _ _ (hOfD c hc) (hgD c hc)
    exact (inner_transfer X hG u u' φ hφ _ _ a ha b hb hab).symm
  have key := hE X.B.I.Ginf (Formalism.L2.SG.ProjRows.muInf X.B.I) _ X.B.σs (degX X) (X.B.tens X.B.w)
    (X.Vpi u) (X.Vpi u') (X.SinfU u) (X.SinfU u') (muS X u) (muS X u') (X.nuQ u) (X.nuQ u')
    (tauU X u) (tauU X u') (X.Wu u) (X.Wu u') (Cinf X) inferInstance (nuM X u u' sc) g
    hUR hSch hw hHu hHu' hFu hFu' hSFu hSFu' (fun f hf => X.nuQ_weil u f hf)
    (fun f hf => X.nuQ_weil u' f hf) (isWAbs_of X hS hG u) (isWAbs_of X hS hG u') hDis hgm
    (fun c => by
      obtain ⟨c', hc', hd⟩ := hgd c
      exact integrableOn_univ.mp (hI X u u' sc hsc c' hc' (g c) hd))
    (fun c => by
      obtain ⟨c', hc', hd⟩ := hgd c
      exact (hC X u u' sc hsc).1 c' hc' (g c) hd)
    ((hC X u u' sc hsc).2 u) ((hC X u u' sc hsc).2 u')
  refine le_trans (le_of_eq ?_) key
  have hae : ∀ᵐ c ∂(nuM X u u' sc), c ∈ Good X u u' := by
    rw [nuM]
    exact withDensity_absolutelyContinuous _ _ (ae_restrict_mem hGood)
  have hIndep : OOIndep X u u' sc := InfCut.ooIndep_of_step X InfCut.UnitaryIsometries.StepDiagDC_holds u u' sc
  unfold intOOe
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with c hc
  rw [hilbertSchmidtSqGram, hIndep c hc _ _ (hOfD c hc) (hgD c hc)]
  simp only [OOinf, TermOp.OO, Measure.restrict_univ]
  rfl

theorem inInfinityXAt (hI : StepIntAt D) (hC : StepConvAt D) (u u' : D.what₂.Word) (sc : ℝ) (hsc : 0 < sc) :
    InInfinityX X u u' sc := by
  have h27 : DisintegrationConstantPositive X u u' sc := InfCut.ProductExactness.haar_disintegration_real_holds D X u u' sc hsc
  have hR := InfCut.ProductExactness.StepReal_holds D X u u' sc hsc
  have hco : CoordOK X u u' sc := by
    refine ⟨hR, fun c hc => ?_⟩
    have hex := hR c hc
    refine hI X u u' sc hsc c hc _ ?_
    have e : hOf X u u' sc c = hex.choose := dif_pos hex
    rw [e]
    exact hex.choose_spec
  exact ⟨h27, hco, stepEnergyAt_of_inst D S.Pv.EnergyAbs.energyAbs_holds S.Pv.SchurTens.stepSchurG_holds
    S.Pv.HaarSubS.stepSubG_holds S.Pv.SecW.stepSection_holds hC hI X u u' sc hsc h27 hco⟩

end Formalism.L2.SG.RealObj.EnergyInst
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMemConj
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

section MemConj

variable {D : D7} (X : HidaSetting D)

theorem mc_gr_mul_inv (M : GL (Fin X.B.I.n) X.B.I.E) :
    Gr X (M : Matrix _ _ _) * Gr X (↑M⁻¹ : Matrix _ _ _) = 1 := by
  unfold Gr
  have h1 := Bm_mul_Bm' X
  have h2 : Bm' X * Bm X = 1 := Bm'_mul_Bm X
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Bm X) (Bm' X), h1, Matrix.one_mul]
  have h3 : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *
      (((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * Bm X) = Bm X := by
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  rw [h3, h2]

theorem mc_gr_unitary (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    (Gr X (M : Matrix _ _ _))ᴴ * JB X * Gr X (M : Matrix _ _ _) = JB X := by
  have hc : Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) =
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ := by
    ext i j
    unfold Formalism.UG.cT
    simp [Matrix.conjTranspose_apply, starRingEnd_apply]
  have hMJ : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ * X.B.I.J *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J := by
    rw [← hc]
    exact hM
  have hJB : JB X = (Bm X)ᴴ * X.B.I.J * Bm X := by
    ext k k'
    unfold JB hE Formalism.UG.hform Bm
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, starRingEnd_apply]
    rw [Finset.sum_comm]
  have h1 := Bm_mul_Bm' X
  have h5 : ∀ Z : Matrix (Fin X.B.I.n) (Kap X) X.B.I.E, (Bm' X)ᴴ * ((Bm X)ᴴ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one, Matrix.one_mul]
  rw [hJB]
  unfold Gr
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Bm X) (Bm' X), h1, Matrix.one_mul, h5]
  have h4 : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ * (X.B.I.J *
      ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * Bm X)) = X.B.I.J * Bm X := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMJ]
  rw [h4]

theorem memConjOf_holds : MemConjOf := by
  intro D X M hM
  letI : Invertible (2 : X.B.I.E) := invertibleOfNonzero two_ne_zero
  have h1 : Gr X (M : Matrix _ _ _) * Gr X (↑M⁻¹ : Matrix _ _ _) = 1 := mc_gr_mul_inv X M
  have h2 : Gr X (↑M⁻¹ : Matrix _ _ _) * Gr X (M : Matrix _ _ _) = 1 := by
    have := mc_gr_mul_inv X M⁻¹
    rwa [inv_inv] at this
  have hU := mc_gr_unitary X M hM
  refine ⟨fun Z => ?_, fun Z hZ => ?_, ?_⟩
  ·
    have hBB : ∀ Y : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E, Bm X * (Bm' X * Y) = Y := by
      intro Y
      rw [← Matrix.mul_assoc, Bm_mul_Bm', Matrix.one_mul]
    unfold Formalism.L2.SG.Pf.UnipB.gE
    rw [← conj_cay h1]
    unfold Gr
    simp only [Matrix.mul_assoc, hBB, Bm_mul_Bm', Matrix.mul_one]
  ·
    set G := Gr X (M : Matrix _ _ _) with hG
    set G' := Gr X (↑M⁻¹ : Matrix _ _ _) with hG'
    have hA : Gᴴ * JB X = JB X * G' := by
      calc Gᴴ * JB X = Gᴴ * JB X * (G * G') := by rw [h1, Matrix.mul_one]
        _ = Gᴴ * JB X * G * G' := by simp only [Matrix.mul_assoc]
        _ = JB X * G' := by rw [hU]
    have hB : G'ᴴ * JB X = JB X * G := by
      calc G'ᴴ * JB X = G'ᴴ * (Gᴴ * JB X * G) := by rw [hU]
        _ = (G * G')ᴴ * JB X * G := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = JB X * G := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul]
    calc (G' * Z * G)ᴴ * JB X = Gᴴ * Zᴴ * (G'ᴴ * JB X) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Gᴴ * (Zᴴ * JB X) * G := by rw [hB]; simp only [Matrix.mul_assoc]
      _ = Gᴴ * (-(JB X * Z)) * G := by rw [hZ]
      _ = -(Gᴴ * JB X * Z * G) := by simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(JB X * (G' * Z * G)) := by rw [hA]; simp only [Matrix.mul_assoc]
  ·
    obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
      ((Finset.univ.image fun ij : Kap X × Kap X => Gr X (↑M⁻¹ : Matrix _ _ _) ij.1 ij.2) ∪
        (Finset.univ.image fun ij : Kap X × Kap X => Gr X (M : Matrix _ _ _) ij.1 ij.2))
    have hint : ∀ z ∈ ((Finset.univ.image fun ij : Kap X × Kap X => Gr X (↑M⁻¹ : Matrix _ _ _) ij.1 ij.2) ∪
        (Finset.univ.image fun ij : Kap X × Kap X => Gr X (M : Matrix _ _ _) ij.1 ij.2)),
        (y.natAbs : X.B.I.E) * z ∈ integralClosure ℤ X.B.I.E := by
      intro z hz
      rw [mem_integralClosure_iff]
      have h := hy z hz
      rw [zsmul_eq_mul] at h
      rcases Int.natAbs_eq y with e | e
      · rw [e] at h
        simpa using h
      · rw [e] at h
        have h' := h.neg
        simpa [neg_mul] using h'
    have hP : ∀ i j, (y.natAbs : X.B.I.E) * Gr X (↑M⁻¹ : Matrix _ _ _) i j ∈ integralClosure ℤ X.B.I.E :=
      fun i j => hint _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
    have hQ : ∀ i j, (y.natAbs : X.B.I.E) * Gr X (M : Matrix _ _ _) i j ∈ integralClosure ℤ X.B.I.E :=
      fun i j => hint _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
    let P1 : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E) := Matrix.of fun i j => ⟨_, hP i j⟩
    let Q1 : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E) := Matrix.of fun i j => ⟨_, hQ i j⟩
    have hP1 : P1.map (fun a => (a : X.B.I.E)) = (y.natAbs : X.B.I.E) • Gr X (↑M⁻¹ : Matrix _ _ _) := by
      ext i j
      rfl
    have hQ1 : Q1.map (fun a => (a : X.B.I.E)) = (y.natAbs : X.B.I.E) • Gr X (M : Matrix _ _ _) := by
      ext i j
      rfl
    have hmap : ∀ U V : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E),
        (U * V).map (fun a => (a : X.B.I.E)) =
          U.map (fun a => (a : X.B.I.E)) * V.map (fun a => (a : X.B.I.E)) :=
      fun U V => Matrix.map_mul (f := algebraMap (𝓞 X.B.I.E) X.B.I.E)
    refine ⟨y.natAbs * y.natAbs, Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (Int.natAbs_ne_zero.mpr hy0) (Int.natAbs_ne_zero.mpr hy0)), fun d A => ⟨P1 * A * Q1, ?_⟩⟩
    rw [hmap, hmap, hP1, hQ1]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Nat.cast_mul]
    congr 1
    ring

end MemConj

end Formalism.L2.SG.TermOp.Vanish
end
end

