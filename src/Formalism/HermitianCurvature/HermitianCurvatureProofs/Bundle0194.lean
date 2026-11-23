module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0182
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSquareIntegrableHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0155
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0184
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGSlice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
public import Formalism.HermitianCurvature.StatementHeads
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0137
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0187
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0112

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalSquareIntegrableTransfer
section
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem local_square_integrable_transfer : LocalSquareIntegrableTransfer := by
  refine ⟨3, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Bg A ε J e hFr hBg hε hA hJ π
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Db := (T v).base with hDb
  have hT : Tz S.G.k S.G.r Db.z = S.T := hPl.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hPl.2.2.2.2.1
  have hTT : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' = (D.parOf S v).TT := by rw [hT, hT']; rfl
  have hQm : MeasurableSet (MA.Qset (D.parOf S v).r (D.parOf S v).TT) := (MA.Qset_open _ _).measurableSet

  obtain ⟨F, -, hCC, hFJ⟩ := hJ.2 ε hε
  set A' := A - 5 * Bg with hA'
  have hC5 : ∀ m, m ≤ 5 → B.InCC A' m F := by
    intro m hm
    refine inCC_antiA ?_ (hCC m)
    have : (m : ℝ) ≤ 5 := by exact_mod_cast hm
    rw [hA']; nlinarith

  have hAB : B.AB S.G.k S.G.r ≤ A' := by
    have := jd_AB_le S.G.k S.G.r
    rw [hA']; linarith
  obtain ⟨c0, -, -, hB1, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db A' hAB
  obtain ⟨C, hC⟩ := hB1
  obtain ⟨c4, hc4⟩ := hC5 4 (by norm_num)
  have hN : B.normSq Db F ≠ ⊤ := (hC F F c4 c4 (hC5 5 le_rfl) (hC5 5 le_rfl) hc4 hc4).1
  unfold B.normSq jNormSq at hN

  have hsm := Formalism.FourierDecayAlt.P.CutMP.En.trace_smoothness E Wp Wq S T v hPl e hFr J hJ.1 π
  have hval := Formalism.FourierDecayAlt.P.CutMP.En.toSm_val_of_mem (D.parOf S v) hsm
  have hGm : Measurable (fun q : MA.Qp (D.parOf S v).r (D.parOf S v).TT => MA.Gq (D.parOf S v) q) := by
    unfold MA.Gq; fun_prop
  have hs : MeasurableSet {q : MA.Qp (D.parOf S v).r (D.parOf S v).TT | ε ≤ MA.Gq (D.parOf S v) q} :=
    measurableSet_le measurable_const hGm
  refine ⟨(((jd_evQ_meas _ _).norm).pow 2).restrict, ?_⟩
  refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun q => by positivity)).2 ?_
  set H : MA.E S.G.r → ENNReal := fun x =>
    ENNReal.ofReal (MA.wq S.G.k x (D.parOf S v).TT * ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) with hH
  have p1 : ∀ q ∈ {q : MA.Qp (D.parOf S v).r (D.parOf S v).TT | ε ≤ MA.Gq (D.parOf S v) q},
      ENNReal.ofReal (‖MA.evQ (D.parOf S v) (trJ S T v e J π) q‖ ^ 2) ≤ H q.1 := by
    intro q hqs
    refine ENNReal.ofReal_le_ofReal ?_
    have hGg : ε ≤ GfP S T v (B.gq (T v).base q.1) := by
      have h1 := Formalism.FourierDecayAlt.P.CutMP.cutTr_Gf_gq (T v).base q.2.1 (by rw [hTT]; exact q.2.2)
      have h2 : GfP S T v (B.gq (T v).base q.1) = MA.Gq (D.parOf S v) q := by
        unfold GfP MA.Gq; rw [h1, hTT]
      rw [h2]; exact hqs
    have hJF : J (B.gq Db q.1) = B.JF Db F (B.gq Db q.1) := hFJ q.1 q.2 hGg
    have hq : MA.evQ (D.parOf S v) (trJ S T v e J π) q =
        ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
          inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1))) := by
      rw [← hJF]; exact congrFun hval q
    rw [hq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hw := Formalism.FourierDecayAlt.P.CutMP.En.wq_pos (k := S.G.k) q.2
    rw [Real.sq_sqrt hw.le]
    refine mul_le_mul_of_nonneg_left ?_ hw.le
    have he1 : ‖B.hsVec (e π q.1.2)‖ ≤ 1 := by
      have h1 : inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (e π q.1.2)) = (1 : ℂ) := by
        simpa using (hFr.2 q.1.2 q.2.2).2.1 π π
      rw [inner_self_eq_norm_sq_to_K] at h1
      have h2' : ((‖B.hsVec (e π q.1.2)‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
        rw [Complex.ofReal_pow, Complex.ofReal_one]; exact h1
      have h2 : ‖B.hsVec (e π q.1.2)‖ ^ 2 = 1 := Complex.ofReal_injective h2'
      nlinarith [norm_nonneg (B.hsVec (e π q.1.2))]
    have hi : ‖inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1)))‖ ≤
        ‖B.hsVec (B.JF Db F (B.gq Db q.1))‖ :=
      (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (B.hsVec (B.JF Db F (B.gq Db q.1)))])
    exact pow_le_pow_left₀ (norm_nonneg _) hi 2
  have p2 : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.dens0 x * H x ≤
      ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
        ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := by
    intro x hx
    have hd : MA.dens0 x = ENNReal.ofReal (Formalism.FourierDecayAlt.P.MAx2.Adj.dR x) := by
      unfold MA.dens0 Formalism.FourierDecayAlt.P.MAx2.Adj.dR
      rw [ENNReal.ofReal_prod_of_nonneg (fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _))]
    have hd0 : 0 ≤ Formalism.FourierDecayAlt.P.MAx2.Adj.dR x :=
      Finset.prod_nonneg fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _)
    have hW : bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x =
        Formalism.FourierDecayAlt.P.MAx2.Adj.dR x * MA.wq S.G.k x (D.parOf S v).TT := by
      have hle : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' ≤ Complex.normSq x.2 := by
        rw [hTT]; exact le_of_lt hx.2
      unfold bcWeight
      rw [if_pos hle]
      unfold Formalism.FourierDecayAlt.P.MAx2.Adj.dR MA.wq
      rw [hTT, ← mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun l _ => ?_
      have hM : 2 ≤ MA.Mdim S.G.k S.G.r l := by
        have := l.isLt
        simp only [MA.Mdim]; omega
      have hn : Complex.normSq (x.1 l) ≠ 0 := (Complex.normSq_pos.2 (hx.1 l)).ne'
      have e1 : Formalism.QuantumDeterminants.Mdim S.G.k S.G.r l = MA.Mdim S.G.k S.G.r l := rfl
      rw [e1, pow_mul, Complex.sq_norm, show MA.Mdim S.G.k S.G.r l - 1 = (MA.Mdim S.G.k S.G.r l - 2) + 1 by omega,
        pow_succ]
      field_simp
    rw [hd, hH, ← ENNReal.ofReal_mul hd0, hW, mul_assoc]
  calc ∫⁻ q, ENNReal.ofReal (‖MA.evQ (D.parOf S v) (trJ S T v e J π) q‖ ^ 2)
          ∂(MA.mu0 (D.parOf S v).r (D.parOf S v).TT).restrict
            {q | ε ≤ MA.Gq (D.parOf S v) q}
        ≤ ∫⁻ q in {q : MA.Qp (D.parOf S v).r (D.parOf S v).TT | ε ≤ MA.Gq (D.parOf S v) q}, H q.1
            ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT := setLIntegral_mono' hs p1
      _ ≤ ∫⁻ q : MA.Qp (D.parOf S v).r (D.parOf S v).TT, H q.1 ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT :=
          setLIntegral_le_lintegral _ _
      _ ≤ ∫⁻ x in MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.dens0 x * H x := lintegral_base_measure_le H
      _ ≤ ∫⁻ x in MA.Qset (D.parOf S v).r (D.parOf S v).TT,
            ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
              ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := setLIntegral_mono' hQm p2
      _ ≤ ∫⁻ x, ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
              ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := setLIntegral_le_lintegral _ _
      _ < ⊤ := lt_top_iff_ne_top.2 hN

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NilpotentDerivative
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem nd_deriv_smul_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : ℝ → ℂ) (v : E) :
    deriv (fun t => φ t • v) 0 = deriv φ 0 • v := by
  by_cases hφ : DifferentiableAt ℝ φ 0
  · exact deriv_smul_const hφ v
  by_cases hv : v = 0
  · simp [hv]
  rw [deriv_zero_of_not_differentiableAt hφ, zero_smul]
  apply deriv_zero_of_not_differentiableAt
  intro hd
  apply hφ
  obtain ⟨ℓ, -, hℓv⟩ := exists_dual_vector ℂ v (norm_ne_zero_iff.mpr hv)
  have h1 : DifferentiableAt ℝ (fun t => ℓ (φ t • v)) 0 :=
    (ℓ.restrictScalars ℝ).differentiableAt.comp 0 hd
  have hn : ℓ v ≠ 0 := by
    rw [hℓv]; exact RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)
  have h2 : φ = fun t => ℓ (φ t • v) * (ℓ v)⁻¹ := by
    funext t
    rw [map_smul, smul_eq_mul, mul_assoc, mul_inv_cancel₀ hn, mul_one]
  rw [h2]
  exact h1.mul_const _

theorem nd_exp_mem {k r : ℕ} {X : B.Mat k r} (hX : X ∈ JfS.lieOf (Nset k r)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Q.Nlev k r 0 :=
  ⟨hX t, (hX t).1, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩

theorem nd_om_mem {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    g ∈ Q.Glev k r 0 ∩ Q.OmPlus k r z z' :=
  ⟨⟨hg.1, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩, hg.2⟩

theorem nilpotent_derivative : NDiff := by
  intro k r Wp Wq _ _ _ _ D m J hJ
  obtain ⟨_, hL, hR, _⟩ := hJ
  constructor
  · intro X hX
    refine ⟨deriv (fun t : ℝ => psi k r D.z' cStd (NormedSpace.exp ((t : ℂ) • X))) 0, fun g hg => ?_⟩
    show deriv (fun t : ℝ => J (g * NormedSpace.exp ((t : ℂ) • X))) 0 = _
    have e : (fun t : ℝ => J (g * NormedSpace.exp ((t : ℂ) • X))) =
        fun t : ℝ => psi k r D.z' cStd (NormedSpace.exp ((t : ℂ) • X)) • J g :=
      funext fun t => hR g (nd_om_mem hg) _ (nd_exp_mem hX t)
    rw [e, nd_deriv_smul_const]
  · intro X hX
    refine ⟨deriv (fun t : ℝ => psi k r D.z cStd (NormedSpace.exp ((t : ℂ) • X))) 0, fun g hg => ?_⟩
    show deriv (fun t : ℝ => J (NormedSpace.exp ((t : ℂ) • X) * g)) 0 = _
    have e : (fun t : ℝ => J (NormedSpace.exp ((t : ℂ) • X) * g)) =
        fun t : ℝ => psi k r D.z cStd (NormedSpace.exp ((t : ℂ) • X)) • J g :=
      funext fun t => hL g (nd_om_mem hg) _ (nd_exp_mem hX t)
    rw [e, nd_deriv_smul_const]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWaveMain
section
open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem letter_level_zero_eq {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (hj : 0 ≤ r) (l : C.Letter) (e : Fin 2) (G : B.Mat k r → E) :
    D.vLet k r z z' 0 hj l e G = if e = 0 then G else fun _ => 0 := by
  funext g
  by_cases he : e = 0
  · subst he
    have hD0 : Dmin k r z z' g 0 = 1 := by simp [Dmin]
    rcases l with ⟨b, Y⟩
    cases b <;>
      simp [D.vLet, C3.AAop, C3.AAvop, qminorOp, Matrix.det_isEmpty, Finset.univ_unique] <;>
      rw [if_pos (show StrictMono _ from fun a => a.elim0)] <;> simp [hD0]
  · have he1 : e = 1 := by omega
    subst he1
    simp [D.vLet]

theorem slicePolyAll : SlicePolyAll := by
  intro Wp Wq _ _ _ _ _ _ P p F hF j hj h hh w' b δ e
  by_cases hj0 : j = 0
  · subst hj0
    refine ⟨fun _ => if e = 0 then KB.slv p.T F 0 hj w' h hh.2 else 0, rfl, fun l => ?_, fun t => ?_⟩
    · by_cases he : e = 0
      · simp only [he, if_true]
        exact nice_vec_of_cpt (p.T.bs 0) (fun a => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F 0 hj w' h hh hF a)
      · simp only [he, if_false]
        exact ⟨0, fun a => Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero⟩
    · intro a g hg
      show D.castF _ (D.sliceAt P.k P.r p.T.base.z p.T.base.z'
        (D.vLet P.k P.r p.T.base.z p.T.base.z' 0 hj (b, t + δ) e
          (D.uwG P.k P.r p.T.base.z p.T.base.z' F 0 hj w' a)) h) g = _
      rw [letter_level_zero_eq]
      by_cases he : e = 0
      · simp [he, Finset.sum_apply, Fin.sum_univ_succ, KB.slv]
      · simp [he, sliceAt_zero, Finset.sum_apply, D.castF]
  · refine slicePoly_of_pt p.T F hF j hj (by omega) h hh w' b δ e (fun a g hg hD => ?_)
    obtain ⟨c, hcl, hc⟩ := uwG_letter_poly p.T.base.z p.T.base.z' j hj hF.1 w' a g hg hD b e
    obtain ⟨c', hc'l, hsh⟩ := poly_shift j c (δ : ℂ)
    refine ⟨c', hc'l.trans hcl, fun t => ?_⟩
    show D.vLet P.k P.r p.T.base.z p.T.base.z' j hj (b, t + δ) e (D.uwG P.k P.r p.T.base.z p.T.base.z' F j hj w' a) g = _
    rw [hc (t + δ), ← hsh (t : ℂ)]
    push_cast
    rfl

theorem _root_.Formalism.FourierDecayAlt.P.degree_of_plane_wave : KB.DegWave := degWave_of slicePolyAll

end Formalism.FourierDecayAlt.P.PBG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PbRadHeadOf
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

section smul

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem act_smul' (M : Wd.SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (x : Wd.Ix S → RadSp k r z z' π π') (a : ℂ) :
    P5.act M (fun e => a • x e) = fun e => a • P5.act M x e := by
  funext e
  simp only [P5.act, map_smul, Finset.smul_sum]

theorem rrform_smul (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (μ : Measure (Mt k r)) (i : Fin (r + 1)) (w : List (Wd.Letter ℂ S)) (x y : Wd.Ix S → RadSp k r z z' π π')
    (c : Fin r → ℂ) (a : ℂ) :
    P5.RRform L st μ i w (fun e => a • x e) (fun e => a • y e) c = a * conj a * P5.RRform L st μ i w x y c := by
  unfold P5.RRform
  rw [act_smul']
  unfold P5.form
  rw [← integral_const_mul]
  congr 1
  funext c'
  simp only [HerA.pairAt_smul_left, HerA.pairAt_smul_right, ← Finset.mul_sum]
  ring

end smul

theorem isLocPt_snoc {h : C.LPt} {j : ℕ} (hh : D.IsLocPt h j) {t : ℂ} (ht : t ≠ 0) :
    D.IsLocPt (h ++ [(1, t)]) (j + 1) := by
  obtain ⟨h1, h2⟩ := hh
  refine ⟨fun b hb => ?_, ?_⟩
  · rcases List.mem_append.1 hb with hb | hb
    · exact h1 b hb
    · rw [List.mem_singleton] at hb
      subst hb
      exact ⟨le_rfl, ht⟩
  · unfold D.ptSize at h2 ⊢
    rw [List.map_append, List.sum_append, h2]
    simp

theorem levW_below (P : M.Par) (j : ℕ) (hj : j + 1 ≤ P.r) {t : ℂ} (ht : t ≠ 0) :
    ‖t‖ ^ (-2 : ℤ) * (‖t‖ ^ (2 * (P.r - j) + P.k)) ^ 2 = KB.levW P (j + 1) t := by
  have hj' : j + 1 ≠ P.r + 1 := by omega
  unfold KB.levW
  rw [if_neg hj']
  have ht' : ‖t‖ ≠ 0 := norm_ne_zero_iff.2 ht
  rw [← pow_mul, ← zpow_natCast, ← zpow_add₀ ht']
  congr 1
  unfold C.Mlev
  push_cast [Nat.cast_sub (show j ≤ P.r by omega)]
  ring

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBP

theorem pb_radHead_of (hOne : PBO.FormOne) (hZN : PBO.ZetaNormExists) (hHP : HeadPic) : KB.RadHead := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h h' hh hh' X μ L st Φ Φ' hD hZ hF hw hΦ hΦ' t ht
  let jF : Fin (P.r + 1) := ⟨j + 1, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨Xs⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨Ls, sts, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl Xs p.l0
  obtain ⟨μs, hμs⟩ := hZN P.k (P.r - (j + 1)) Wp Wq (p.T.bs (j + 1))
  have hDs : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' Xs μs Ls sts p.l0 :=
    ⟨hPl, hμs.1, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨T, hT, hph⟩ :=
    Formalism.FourierDecayAlt.P.radial_transport_plus Wp Wq P p j hj X μ L st Xs μs Ls sts hD hZ hDs hμs t ht
  refine (hph (Fin w.length) (D.positionted w) Φ Φ' (fun _ => 1) 0).trans ?_
  have hl := isLocPt_snoc hh ht
  have hl' := isLocPt_snoc hh' ht

  set x2 := KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) hl.2 with hx2def
  set x2' := KB.slv p.T F (j + 1) hj w (h' ++ [(1, t)]) hl'.2 with hx2'def
  have hc2 : ∀ e, KB.CptCoef (p.T.bs (j + 1)) (x2 e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F (j + 1) hj w _ hl hF e
  have hc2' : ∀ e, KB.CptCoef (p.T.bs (j + 1)) (x2' e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F (j + 1) hj w _ hl' hF e
  obtain ⟨ε₁, hε₁, hx⟩ := PBO.nice_common (p.T.bs (j + 1)) hc2
  obtain ⟨ε₂, hε₂, hx'⟩ := PBO.nice_common (p.T.bs (j + 1)) hc2'
  have hε : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have mono : ∀ {ε' : ℝ} {G : B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)}, min ε₁ ε₂ ≤ ε' →
      JC.NiceCoef (p.T.bs (j + 1)) ε' G → JC.NiceCoef (p.T.bs (j + 1)) (min ε₁ ε₂) G :=
    fun hle hG => ⟨hG.1, hG.2.1, fun g hg h0 => le_trans hle (hG.2.2 g hg h0)⟩
  have hxn : ∀ e, JC.NiceCoef (p.T.bs (j + 1)) (min ε₁ ε₂) (x2 e) := fun e => mono (min_le_left _ _) (hx e)
  have hxn' : ∀ e, JC.NiceCoef (p.T.bs (j + 1)) (min ε₁ ε₂) (x2' e) := fun e => mono (min_le_right _ _) (hx' e)

  set lam : ℝ := ‖t‖ ^ (2 * (P.r - j) + P.k) with hlam
  have hlam0 : lam ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 ht)
  have hlamC : ((lam : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlam0
  let b0 : Fin (JC.parLev P j).r := ⟨0, by change 0 < P.r - j; omega⟩
  let Φ2 := fun e => (((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Φ e)
  let Φ2' := fun e => (((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Φ' e)
  have hpic : ∀ (hh₀ : C.LPt) (hhh : D.IsLocPt hh₀ j) (Ψ : Wd.Ix (Fin w.length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
      (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Ψ e) (KB.slv p.T F j (by omega) w hh₀ hhh.2 e)) →
      ∀ e, ∀ y ∈ Q.DomR (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z',
        Subtype.val ((((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Ψ e)) y.1 y.2 =
          Q.resG (JC.parLev P jF).k (JC.parLev P jF).r (Fin.last _)
            (B.JF (p.T.bs jF) (KB.slv p.T F (j + 1) hj w (hh₀ ++ [(1, t)]) (isLocPt_snoc hhh ht).2 e)) y.1 y.2 := by
    intro hh₀ hhh Ψ hΨ e y hy
    have e1 := hT (P5.act (P5.bTl L b0 (D.positionted w)) Ψ e) y.1 y.2
    have e2 := hHP Wp Wq P p F j hj w hh₀ hhh X μ L st Ψ hD hF hw hΨ t (isLocPt_snoc hhh ht) e y hy
    have hcl : ∀ v : Wq →L[ℂ] Wp, ((lam⁻¹ : ℝ) : ℂ) • (((lam : ℝ) : ℂ) • v) = v := fun v => by
      rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0, Complex.ofReal_one, one_smul]
    exact (congrArg (fun v => ((lam⁻¹ : ℝ) : ℂ) • v) (e1.trans e2)).trans (hcl _)
  have hΦ2 := hpic h hh Φ hΦ
  have hΦ2' := hpic h' hh' Φ' hΦ'
  have hOne' := hOne Wp Wq P p.T jF Xs μs Ls sts p.l0 hDs hμs w x2 x2' Φ2 Φ2' (min ε₁ ε₂) hε hxn hxn' hΦ2 hΦ2'
  have hTΦ : (fun a => T (P5.act (P5.bTl L b0 (D.positionted w)) Φ a)) = fun a => ((lam : ℝ) : ℂ) • Φ2 a := by
    funext a
    simp only [Φ2, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hlam0, Complex.ofReal_one, one_smul]
  have hTΦ' : (fun a => T (P5.act (P5.bTl L b0 (D.positionted w)) Φ' a)) = fun a => ((lam : ℝ) : ℂ) • Φ2' a := by
    funext a
    simp only [Φ2', smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hlam0, Complex.ofReal_one, one_smul]
  rw [hTΦ, hTΦ']
  have hRR : p.RR F (j + 1) w (h ++ [(1, t)]) (h' ++ [(1, t)]) = D.formLev p.T (M.sgn P p.l0) jF w x2 x2' := by
    unfold KB.Pl.RR D.RRplace
    rw [dite_eq_left ⟨hl, hl'⟩, dite_eq_left hj]
    rfl
  have key : P5.RRform Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0 = D.formLev p.T (M.sgn P p.l0) jF w x2 x2' := hOne'.symm
  calc _ = ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ((lam : ℂ) * conj (lam : ℂ) * P5.RRform Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0) :=
        congrArg _ (rrform_smul Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0 (lam : ℂ))
    _ = ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ((lam : ℂ) * conj (lam : ℂ) * D.formLev p.T (M.sgn P p.l0) jF w x2 x2') := by
        rw [key]
    _ = _ := by
        rw [hRR, ← levW_below P j hj ht, Complex.conj_ofReal, hlam]
        push_cast
        ring

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothOfCoefficientsHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smooth_of_coefficients_holds : SmoothOfCoeffs := by
  intro k r E _ _ _ Dm J h g₀ hg₀
  let b := Module.finBasis ℂ E
  let ℓ : Fin (Module.finrank ℂ E) → E →L[ℂ] ℂ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  choose U F hU hgU hF hJF using fun i => h (ℓ i) g₀ hg₀
  refine ⟨⋂ i, U i, fun g => ∑ i, F i g • b i, isOpen_iInter_of_finite hU, Set.mem_iInter.2 hgU, ?_, ?_⟩
  · refine ContDiffOn.sum fun i _ => ?_
    exact ((hF i).mono (Set.iInter_subset _ i)).smul contDiffOn_const
  · intro g hg hgG
    have hg' := Set.mem_iInter.1 hg
    conv_lhs => rw [← b.sum_repr (J g)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hJF i g (hg' i) hgG]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopUnipotentIntegralPositive
section
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

theorem top_unipotent_integral_positive (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (h : C.LPt) (ζ : ℂ) (hh : D.IsLocPt h P.r)
    (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r))
    (hF : KB.CptCoef p.T.base F) (hζ : ζ ≠ 0)
    (hν : D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν')
    (hm : D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀) (hR : 1 ≤ P.r) :
    p.V F (h ++ [(1, ζ)]) =
      D.vecV (p.T.bs P.r) ν'r m₀r
        (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h)) [(1, ζ)] := by
  have h0 := p.hT 0 (Nat.zero_le _)
  have hr := p.hT P.r le_rfl
  exact vecV_append_singleton_eq_vecV_sliceAt P.k P.r (P.r - P.r) (Nat.sub_self _) (by omega) p.T.base (p.T.bs P.r)
    (p.T.z_lev P.r le_rfl) (p.T.z'_lev P.r le_rfl) (p.T.π_lev P.r le_rfl) (p.T.π'_lev P.r le_rfl)
    h0.2.2 h0.1 h0.2.1 hr.1 hr.2.1 hr.2.2 p.ν' p.m₀ ν'r m₀r hν hm p.hF
    (CompactCoefficientAppend.baseFrame_last p ν'r m₀r hν hm) h hh ζ hζ F hF hR _

theorem highestUnipotentIntegral : PBI.HighestUnipotentIntegral := by
  intro Wp Wq _ _ _ _ _ _ P p F h ζ hh ν'r m₀r hF hζ hν hm
  by_cases hR : P.r = 0
  · exact CompactCoefficientAppend.top_unipotent_integral_zero Wp Wq P p F h ζ hh ν'r m₀r hR hF hζ hν hm
  · exact top_unipotent_integral_positive Wp Wq P p F h ζ hh ν'r m₀r hF hζ hν hm (by omega)

end Formalism.FourierDecayAlt.P.PBM

namespace Formalism.FourierDecayAlt.P

theorem top_unipotent_integral : PBI.HighestUnipotentIntegral := PBM.highestUnipotentIntegral

end Formalism.FourierDecayAlt.P
end
end

