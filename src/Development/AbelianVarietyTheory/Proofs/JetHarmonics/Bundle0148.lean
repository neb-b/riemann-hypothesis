module

public import Mathlib
public import Formalism.HermitianCurvature.Bundle0010
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0188
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0193
public import Formalism.HermitianCurvature.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0147

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CutoffCompactApproximantsConvergeDecayClass
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem cutF_approximants_ccle :
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A₀ ε A : ℝ) (mm : ℕ), C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV k r) f → (∀ m : ℕ, B.InCC A₀ m f) → A + 1 + 2 * ((r : ℝ) + 1) * (mm : ℝ) ≤ A₀ → ∃ K : ℝ, 0 ≤ K ∧ B.CCle A mm (D.cutF Bs χ f ε) K ∧ ∀ n : ℕ, B.CCle A mm ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε g)) K ∧ B.CCle A mm ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε g) - (D.cutF Bs χ f ε)) (K / ((n : ℝ) + 1)) := by
  intro k r Wp Wq _ _ _ _ _ _ Bs χ f A₀ ε A mm hχ hε _ hfA hA
  obtain ⟨b, hb⟩ := Formalism.FourierDecayAlt.P.PBE.cutF_inCC Bs hχ hfA hε (A + 1) mm hA
  generalize D.cutF Bs χ f ε = H at hb ⊢
  have hb0 : 0 ≤ b := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hb
  have hb' : B.CCle A mm H b := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) hb
  obtain ⟨Kp, hKp0, hKp⟩ := Formalism.FourierDecayAlt.P.JCx2.pd_cut_ccle (k := k) (r := r) (E := Wq →L[ℂ] Wp) mm
  have hψ : ∀ n : ℕ, B.CCle A mm (fun g => Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • H g)
      (Kp * b / ((n : ℝ) + 1)) := fun n => by
    have h := hKp ((n : ℝ) + 1) (by positivity) (A + 1) H b hb
    rwa [add_sub_cancel_right] at h
  have hc : ∀ (n : ℕ) (g : B.Mat k r), ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)
        = 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := fun n g =>
    Formalism.FourierDecayAlt.P.PBE.cut_eq (fun (n : ℕ) (g : B.Mat k r) => ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) (fun _ _ => rfl) n g
  have hKb : 0 ≤ Kp * b := mul_nonneg hKp0 hb0
  refine ⟨b + Kp * b, by positivity, Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c hb' (by linarith), fun n => ⟨?_, ?_⟩⟩
  · have e : (fun g : B.Mat k r => ((Real.smoothTransition
        ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H g)
          = fun g => H g + (-1 : ℂ) • (Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • H g) := by
      funext g
      rw [hc n g, sub_smul, one_smul, neg_one_smul, sub_eq_add_neg]
    rw [e]
    refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hb' (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1) (hψ n))) ?_
    have h1 : Kp * b / ((n : ℝ) + 1) ≤ Kp * b := div_le_self hKb (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simp only [norm_neg, norm_one, one_mul]
    linarith
  · have e : ((fun g : B.Mat k r => ((Real.smoothTransition
        ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H g) - H)
          = fun g => (-1 : ℂ) • (Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • H g) := by
      funext g
      rw [Pi.sub_apply, hc n g, sub_smul, one_smul, neg_one_smul, sub_sub_cancel_left]
    rw [e]
    refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1) (hψ n)) ?_
    simp only [norm_neg, norm_one, one_mul]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundedRadialOpsClosureAndFunctions
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.PtBBasic

open Formalism.FourierDecayAlt.P.TLB

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem nv_of_mulAt {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {s : ℂ} (h : MulAt x T s)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : nv (T Φ) x = ‖s‖ * nv Φ x := by
  unfold nv
  rw [h Φ, ← norm_smul]
  rfl

theorem nv_nonneg {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) : 0 ≤ nv Φ x := norm_nonneg _

theorem ptB_of_mulAt {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (b : RA P Bs) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', ∃ s : ℂ, MulAt x b.1 s ∧ ‖s‖ ≤ C) : PtB P Bs b := by
  refine ⟨C, hC, fun Φ x hx => ?_⟩
  obtain ⟨s, hs, hle⟩ := h x hx
  rw [nv_of_mulAt hs]
  exact mul_le_mul_of_nonneg_right hle (nv_nonneg Φ x)

theorem ptB_mul {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} (a b : RA P Bs) (ha : PtB P Bs a) (hb : PtB P Bs b) :
    PtB P Bs (a * b) := by
  obtain ⟨C, hC, ha⟩ := ha
  obtain ⟨C', hC', hb⟩ := hb
  refine ⟨C * C', mul_nonneg hC hC', fun Φ x hx => ?_⟩
  rw [pr_mul_fst, Module.End.mul_apply, mul_assoc]
  exact (ha _ x hx).trans (mul_le_mul_of_nonneg_left (hb Φ x hx) hC)

theorem norm_ratio_le (a b : ℂ) (h : ‖a‖ = ‖b‖) : ‖a * b⁻¹‖ ≤ 1 := by
  rw [norm_mul, norm_inv, h]
  exact mul_inv_le_one

theorem sqrt_lt_zeta {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') :
    Real.sqrt (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z') < ‖Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2‖ := by
  have h := hx.2.2
  unfold Q.GGl at h
  rw [Complex.normSq_eq_norm_sq] at h
  have hn := norm_nonneg (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2)
  rw [← Real.sqrt_sq hn]
  exact Real.sqrt_lt_sqrt (mul_pos Bs.T_pos Bs.T'_pos).le (by linarith)

end GlobalTheory.HatNF.PtBBasic

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt.P.TLB PtBBasic

theorem ptB_basic : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → (PtB P Bs 1 ∧ (∀ a b, PtB P Bs a → PtB P Bs b → PtB P Bs (a * b))) ∧ PtB P Bs d.L.ζi ∧ PtB P Bs d.L.ζbi ∧ PtB P Bs (d.L.D * d.L.Dbi) ∧ PtB P Bs (d.L.Db * d.L.Di) ∧ PtB P Bs (d.L.Drb * d.L.Dri) ∧ PtB P Bs (d.L.Dr * d.L.Drbi) ∧ ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', 0 < dR P Bs x.1 x.2 ∧ 0 < gR P Bs x.1 x.2 ∧ nv (d.L.Di.1 Φ) x = (dR P Bs x.1 x.2)⁻¹ * nv Φ x ∧ nv ((TL.gI d.L).1 Φ) x = (gR P Bs x.1 x.2)⁻¹ * nv Φ x := by
  intro Wp Wq _ _ _ _ _ _ Pa Bs X μ L0 st l0 d _ hd
  have hL := hd.1
  set L := d.L with hLdef
  have hDr : ∀ x, MulAt x L.Dr.1 (∏ a, x.1 a) := fun x =>
    mulAt_ofFn L.c _ fun l => act_c X L hL x l
  have hDri : ∀ x, MulAt x L.Dri.1 (∏ a, x.1 a)⁻¹ := fun x => by
    rw [← Finset.prod_inv_distrib]
    exact mulAt_ofFn L.ci _ fun l => act_ci X L hL x l
  have hDrb : ∀ x, MulAt x L.Drb.1 (star (∏ a, x.1 a)) := fun x => by
    rw [star_prod]
    exact mulAt_ofFn L.cb _ fun l => act_cb X L hL x l
  have hDrbi : ∀ x, MulAt x L.Drbi.1 (star (∏ a, x.1 a))⁻¹ := fun x => by
    rw [star_prod, ← Finset.prod_inv_distrib]
    exact mulAt_ofFn L.cbi _ fun l => act_cbi X L hL x l
  have hz : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z', MulAt x L.ζ.1 (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2) := by
    intro x hx; rw [hL.2.2.2.2.2.2.1]; exact act_fn X x hx 0
  have hzi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζi.1 (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.1]; exact act_fn X x hx 1
  have hzb : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζb.1 (star (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)) := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 2
  have hzbi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.ζbi.1 (star (Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2))⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 3
  have hGGi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.GGi.1 ((Q.GGl Pa.k Pa.r Bs.z Bs.z' x.2 : ℂ))⁻¹ := by
    intro x hx; rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; exact act_fn X x hx 5
  have hD : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.D.1 ((∏ a, x.1 a) * Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2) :=
    fun x hx => mulAt_mul (hDr x) (hz x hx)
  have hDb : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.Db.1 (star ((∏ a, x.1 a) * Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)) := by
    intro x hx
    rw [star_mul']
    exact mulAt_mul (hDrb x) (hzb x hx)
  have hDi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.Di.1 ((∏ a, x.1 a) * Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2)⁻¹ := by
    intro x hx
    rw [mul_inv, mul_comm]
    exact mulAt_mul (hzi x hx) (hDri x)
  have hDbi : ∀ x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z',
      MulAt x L.Dbi.1 (star ((∏ a, x.1 a) * Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2))⁻¹ := by
    intro x hx
    rw [star_mul', mul_inv, mul_comm]
    exact mulAt_mul (hzbi x hx) (hDrbi x)
  have hsq : 0 < Real.sqrt (Tz Pa.k Pa.r Bs.z * Tz Pa.k Pa.r Bs.z') :=
    Real.sqrt_pos.2 (mul_pos Bs.T_pos Bs.T'_pos)
  refine ⟨⟨?_, ptB_mul⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ptB_of_mulAt _ 1 zero_le_one fun x _ => ⟨1, mulAt_one x, by simp⟩
  · refine ptB_of_mulAt _ _ (inv_pos.2 hsq).le fun x hx => ⟨_, hzi x hx, ?_⟩
    rw [norm_inv]
    exact inv_anti₀ hsq (sqrt_lt_zeta Bs hx).le
  · refine ptB_of_mulAt _ _ (inv_pos.2 hsq).le fun x hx => ⟨_, hzbi x hx, ?_⟩
    rw [norm_inv, norm_star]
    exact inv_anti₀ hsq (sqrt_lt_zeta Bs hx).le
  · exact ptB_of_mulAt _ 1 zero_le_one fun x hx =>
      ⟨_, mulAt_mul (hD x hx) (hDbi x hx), norm_ratio_le _ _ (norm_star _).symm⟩
  · exact ptB_of_mulAt _ 1 zero_le_one fun x hx =>
      ⟨_, mulAt_mul (hDb x hx) (hDi x hx), norm_ratio_le _ _ (norm_star _)⟩
  · exact ptB_of_mulAt _ 1 zero_le_one fun x _ =>
      ⟨_, mulAt_mul (hDrb x) (hDri x), norm_ratio_le _ _ (norm_star _)⟩
  · exact ptB_of_mulAt _ 1 zero_le_one fun x _ =>
      ⟨_, mulAt_mul (hDr x) (hDrbi x), norm_ratio_le _ _ (norm_star _).symm⟩
  · intro Φ x hx
    have hc : (∏ a, x.1 a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a
    have hζ : Q.zetaL Pa.k Pa.r Bs.z Bs.z' (Fin.last Pa.r) x.2 ≠ 0 :=
      norm_pos_iff.1 (hsq.trans (sqrt_lt_zeta Bs hx))
    have hG := hx.2.2
    refine ⟨norm_pos_iff.2 (mul_ne_zero hc hζ), mul_pos (Complex.normSq_pos.2 hc) hG, ?_, ?_⟩
    · rw [nv_of_mulAt (hDi x hx), norm_inv]
      rfl
    · have h : MulAt x (TL.gI L).1 _ := mulAt_mul (mulAt_mul (hDri x) (hDrbi x)) (hGGi x hx)
      rw [nv_of_mulAt h]
      congr 1
      unfold gR
      rw [norm_mul, norm_mul, norm_inv, norm_inv, norm_inv, norm_star, Complex.norm_real, Real.norm_of_nonneg hG.le,
        Complex.normSq_eq_norm_sq, sq, mul_inv, mul_inv]

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorCutoffEqAndVanish
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace GlobalTheory.TopVec

open Filter Topology MeasureTheory in
open scoped Matrix.Norms.Elementwise in
private lemma vecV_cutoff_lemma {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (B : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : _root_.Formalism.FourierDecayAlt.B.Mat k r)
    (H : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (q : _root_.Formalism.FourierDecayAlt.C.LPt) (ψ : ℝ → ℝ) (t : ℝ) :
    _root_.Formalism.FourierDecayAlt.D.vecV B ν' m₀ (_root_.Formalism.FourierDecayAlt.D.cutF B ψ H t) q =
      ((ψ (_root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz k r B.z * _root_.Formalism.QuantumDeterminants.Tz k r B.z') r q / t) : ℝ) : ℂ) •
        _root_.Formalism.FourierDecayAlt.D.vecV B ν' m₀ H q := by
  unfold _root_.Formalism.FourierDecayAlt.D.vecV
  split_ifs with h h'
  · rw [_root_.Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_cutF, _root_.Formalism.FourierDecayAlt.P.TBBx2.Gf_of_Zhat _ _ _ _ h'.choose_spec.2.1]
  · simp
  · simp

open Filter Topology MeasureTheory in
open scoped Matrix.Norms.Elementwise in
private lemma foldr_RdV_zero {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (w : List (_root_.Formalism.FourierDecayAlt.B.Mat k r)) : List.foldr _root_.Formalism.REAL.RdV (fun _ => (0 : E)) w = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    rw [List.foldr_cons, ih]
    funext g
    unfold _root_.Formalism.REAL.RdV
    simp

open Filter Topology MeasureTheory in
open scoped Matrix.Norms.Elementwise in
private lemma opApply_zero {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] (D : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.B.opApply D (fun _ => 0) g = 0 := by
  unfold _root_.Formalism.FourierDecayAlt.B.opApply
  apply List.sum_eq_zero
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨T, -, rfl⟩ := hx
  unfold _root_.Formalism.FourierDecayAlt.B.Rw
  rw [foldr_RdV_zero]
  simp

open Filter Topology MeasureTheory in
open scoped Matrix.Norms.Elementwise in
theorem _root_.GlobalTheory.TopVec.tv_cutF (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq)
    (Cb : ℝ) (χ : ℝ → ℝ) (δ ε : ℝ) (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List _root_.Formalism.FourierDecayAlt.C.Letter)
    (c : Fin (P.r + 1) → ℂ) (hD : _root_.Formalism.FourierDecayAlt.KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hw : _root_.Formalism.FourierDecayAlt.KB.CutWord P p.l0 w)
    (hχ : _root_.Formalism.FourierDecayAlt.C6.IsCut0 χ) (hδ : ∀ x, x < δ → χ x = 0) (hε : 0 < ε)
    (hF : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) F) :
    (ε < _root_.Formalism.FourierDecayAlt.TBB.Gp p (_root_.Formalism.FourierDecayAlt.TBB.bigPt P.r c) →
      _root_.GlobalTheory.TopVec.tv p (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε) w c = _root_.GlobalTheory.TopVec.tv p F w c) ∧
    (_root_.Formalism.FourierDecayAlt.TBB.Gp p (_root_.Formalism.FourierDecayAlt.TBB.bigPt P.r c) < δ * ε →
      _root_.GlobalTheory.TopVec.tv p (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε) w c = 0) ∧
    (_root_.Formalism.FourierDecayAlt.TBB.Gp p (_root_.Formalism.FourierDecayAlt.TBB.bigPt P.r c) ≤ 0 → _root_.GlobalTheory.TopVec.tv p F w c = 0) := by
  set q := _root_.Formalism.FourierDecayAlt.TBB.bigPt P.r c with hq
  set G := _root_.Formalism.FourierDecayAlt.TBB.Gp p q with hGdef
  have hG : G = _root_.Formalism.FourierDecayAlt.D.ptG (_root_.Formalism.QuantumDeterminants.Tz P.k P.r p.T.base.z * _root_.Formalism.QuantumDeterminants.Tz P.k P.r p.T.base.z') P.r q := rfl
  have hV : ∀ H, p.V H q = _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ H q := fun H => rfl
  have hcut : ∀ (ψ : ℝ → ℝ) (H : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp) (t : ℝ) (g : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r),
      _root_.Formalism.FourierDecayAlt.D.cutF p.T.base ψ H t g =
        ((ψ (_root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g / t) : ℝ) : ℂ) • H g := fun _ _ _ _ => rfl
  have hcont : Continuous (_root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z') := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Gf_cont _ _
  have hzero : ∀ F' : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp,
      (∀ e, p.V (p.Θ.Θ w e F') q = 0) → _root_.GlobalTheory.TopVec.tv p F' w c = 0 := by
    intro F' h
    unfold _root_.GlobalTheory.TopVec.tv
    simp [← hq, h, _root_.Formalism.FourierDecayAlt.B.hsVec]
    funext x
    try simp only [Pi.zero_apply]
    rw [← Pi.zero_def, WithLp.toLp_zero, smul_zero]
  have htv : ∀ F₁ F₂ : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp,
      (∀ e, p.V (p.Θ.Θ w e F₁) q = p.V (p.Θ.Θ w e F₂) q) →
        _root_.GlobalTheory.TopVec.tv p F₁ w c = _root_.GlobalTheory.TopVec.tv p F₂ w c := by
    intro F₁ F₂ h
    unfold _root_.GlobalTheory.TopVec.tv
    simp only [← hq, h]
  have hV0 : G ≤ 0 → ∀ H, p.V H q = 0 := by
    intro h H
    rw [hV]
    unfold _root_.Formalism.FourierDecayAlt.D.vecV
    rw [dite_eq_right]
    rintro ⟨-, h'⟩
    rw [← hG] at h'
    linarith
  refine ⟨?_, ?_, fun h => hzero F fun e => hV0 h _⟩
  · intro hlt
    have hGpos : 0 < G := hε.trans hlt
    apply htv
    intro e
    obtain ⟨nf, fib, o, κ, Dop, -, -, -, -, hDop⟩ := hD w hw e
    rw [hV, hV]
    have h1 : ∀ H, _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ H q = _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀
        (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base (fun x => if ε / G < x then 1 else 0) H G) q := by
      intro H
      rw [vecV_cutoff_lemma, ← hG, div_self hGpos.ne', if_pos ((div_lt_one hGpos).mpr hlt)]
      simp
    rw [h1, h1 (p.Θ.Θ w e F)]
    apply _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos
    intro g hg
    rw [hcut, hcut]
    by_cases hgε : ε < _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g
    · have hOQ : g ∈ _root_.Formalism.FourierDecayAlt.C6.domL p.T.base ∅ := ⟨hg.1, hg.2, by simp⟩
      have hloc : _root_.Formalism.FourierDecayAlt.B.opApply Dop (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε) g = _root_.Formalism.FourierDecayAlt.B.opApply Dop F g := by
        apply _root_.Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Dop (isOpen_lt continuous_const hcont) _ g hgε
        intro x hx
        have hx' : ε < _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' x := hx
        rw [hcut, hχ.2.2 _ ((le_div_iff₀ hε).mpr (by linarith))]
        simp
      rw [hDop _ g hOQ, hDop _ g hOQ, hloc]
    · have : ¬ (ε / G < _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g / G) := by
        rw [div_lt_div_iff_of_pos_right hGpos]; exact hgε
      simp [this]
  · intro hlt
    rcases le_or_gt G 0 with hG0 | hGpos
    · exact hzero _ fun e => hV0 hG0 _
    apply hzero
    intro e
    obtain ⟨nf, fib, o, κ, Dop, -, -, -, -, hDop⟩ := hD w hw e
    rw [hV]
    have h1 : ∀ H, _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ H q = _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀
        (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base (fun x => if x < δ * ε / G then 1 else 0) H G) q := by
      intro H
      rw [vecV_cutoff_lemma, ← hG, div_self hGpos.ne', if_pos ((one_lt_div hGpos).mpr hlt)]
      simp
    rw [h1]
    have h2 : _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base
          (fun x => if x < δ * ε / G then 1 else 0) (p.Θ.Θ w e (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε)) G) q =
        _root_.Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base
          (fun x => if x < δ * ε / G then 1 else 0) (fun _ => 0) G) q := by
      apply _root_.Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos
      intro g hg
      rw [hcut, hcut]
      by_cases hgd : _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g < δ * ε
      · have hOQ : g ∈ _root_.Formalism.FourierDecayAlt.C6.domL p.T.base ∅ := ⟨hg.1, hg.2, by simp⟩
        have hloc : _root_.Formalism.FourierDecayAlt.B.opApply Dop (_root_.Formalism.FourierDecayAlt.D.cutF p.T.base χ F ε) g = _root_.Formalism.FourierDecayAlt.B.opApply Dop (fun _ => 0) g := by
          apply _root_.Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Dop (isOpen_lt hcont continuous_const) _ g hgd
          intro x hx
          have hx' : _root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' x < δ * ε := hx
          rw [hcut, hδ _ ((div_lt_iff₀ hε).mpr hx')]
          simp
        rw [hDop _ g hOQ, hloc, opApply_zero]
      · have : ¬ (_root_.Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g / G < δ * ε / G) := by
          rw [div_lt_div_iff_of_pos_right hGpos]; exact hgd
        simp [this]
    have h3 : _root_.Formalism.FourierDecayAlt.D.cutF p.T.base (fun x => if x < δ * ε / G then 1 else 0)
        (fun _ => (0 : Wq →L[ℂ] Wp)) G = _root_.Formalism.FourierDecayAlt.D.cutF p.T.base (fun _ => 0) (fun _ => 0) G := by
      funext g
      rw [hcut, hcut]
      simp
    rw [h2, h3, vecV_cutoff_lemma]
    simp

end GlobalTheory.TopVec
end

