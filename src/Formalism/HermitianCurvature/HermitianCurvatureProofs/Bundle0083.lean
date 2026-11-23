module

public import Formalism.HermitianCurvature.StatementTop
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0071
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0030
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0078
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CvRhoOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0032
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
public import Formalism.HermitianCurvature.StatementTL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SingleMulVecOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0057
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0080
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorRepresentations

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseCutoffIsTruncation
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P.Topx2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


section helpers

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def chi0 (x : ℝ) : ℝ := Real.smoothTransition (2 * x - 1)

theorem base_cutoff_is_truncation : C6.IsCut0 chi0 := by
  unfold C6.IsCut0
  refine ⟨?_, ⟨1 / 2, by norm_num, fun x hx => ?_⟩, fun x hx => ?_⟩
  · exact Real.smoothTransition.contDiff.comp (f := fun x : ℝ => 2 * x - 1) (by fun_prop)
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · exact Real.smoothTransition.one_of_one_le (by linarith)

end helpers

section diff

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end diff

end Formalism.FourierDecayAlt.P.Topx2
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliDetAdInvariant
section
theorem Formalism.FourierDecayAlt.P.capelli_rho_commute : Formalism.FourierDecayAlt.JF.CVRho := by
  exact Formalism.FourierDecayAlt.P.JFxE.cVRho
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliVectorFrame
section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.TL

namespace TLC

variable {k r : ℕ}

theorem cap_econj {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : IsRepW k r z π) {Bs Bs' : Fin k → Fin (2 * r + k + 1) → ℂ} (hB : IsFrameOf k r [z] Bs)
    (hB' : IsFrameOf k r [z] Bs') :
    (Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b)) * (Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c)) = 1 ∧
    (Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c)) * (Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b)) = 1 ∧
    EB π Bs = Econj (EB π Bs') (Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c))
      (Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b)) := by
  set P : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c) with hP
  set Q : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b) with hQ
  have hexp : ∀ a, Bs a = ∑ c, P c a • Bs' c := by
    intro a
    exact HermitianFormSums.complete0 hz (HermitianFormSums.hzz hT) hB' (hB.1 a) (hB.2.2 a z (by simp))
  have hQP : Q * P = 1 := by
    ext b a
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h1 : herm (Hpk k r) (Bs a) (Bs b) = herm (Hpk k r) (∑ c, P c a • Bs' c) (Bs b) := by
      rw [← hexp a]
    rw [HermitianFormSums.herm_lsum, hB.2.1] at h1
    rw [show (if b = a then (1 : ℂ) else 0) = if a = b then 1 else 0 by simp only [eq_comm], h1]
    apply Finset.sum_congr rfl
    intro c _
    simp only [hQ, Matrix.of_apply]
    ring
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have hunit : ∀ a b, unitB (Hpk k r) Bs a b =
      ∑ x ∈ (Finset.univ : Finset (Fin k)) ×ˢ (Finset.univ : Finset (Fin k)),
        (P x.1 a * Q b x.2) • unitB (Hpk k r) Bs' x.1 x.2 := by
    intro a b
    rw [Finset.sum_product]
    ext p q
    have h1 : Bs a p = ∑ c, P c a * Bs' c p := by
      have := congrFun (hexp a) p
      rw [Finset.sum_apply] at this
      exact this
    have h2 : herm (Hpk k r) (bvec q) (Bs b) = ∑ d, Q b d * herm (Hpk k r) (bvec q) (Bs' d) := by
      have h3 : herm (Hpk k r) (bvec q) (Bs b) = herm (Hpk k r) (bvec q) (∑ d, P d b • Bs' d) := by
        rw [← hexp b]
      rw [h3, HermitianFormSums.herm_rsum]
      apply Finset.sum_congr rfl
      intro d _
      simp only [hP, hQ, Matrix.of_apply, Qx2.herm_star]
    simp only [Matrix.sum_apply, Matrix.smul_apply, unitB, Matrix.of_apply, smul_eq_mul]
    rw [h1, h2, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring
  refine ⟨hQP, hPQ, ?_⟩
  funext a b
  unfold EB Econj
  rw [hunit a b, (HermitianFormSums.ec_sum elementary_lie_elements hπ _ _ (fun x : Fin k × Fin k => unitB (Hpk k r) Bs' x.1 x.2)
    (fun x => QrD.frame_lie hB' x.1 x.2) _ (QrD.frame_lie hB' a a)).2, Finset.sum_product]
  ext v
  simp

theorem cap_vec {B0 : Fin k → Fin (2 * r + k + 1) → ℂ} {z' : Fin (2 * r + k + 1) → ℂ}
    (hB0 : IsFrameOf k r [z'] B0) {ν : Fin k → ℂ} (hν : C6.sq2 ν = 1) :
    inWb k r (∑ j, ν j • B0 j) ∧ herm (Hpk k r) (∑ j, ν j • B0 j) z' = 0 ∧
      herm (Hpk k r) (∑ j, ν j • B0 j) (∑ j, ν j • B0 j) = 1 := by
  refine ⟨HermitianFormSums.inWb_sum _ _ _ hB0.1, ?_, ?_⟩
  · rw [HermitianFormSums.herm_lsum]
    exact Finset.sum_eq_zero fun j _ => by rw [hB0.2.2 j z' (by simp), mul_zero]
  · rw [HermitianFormSums.herm_comb hB0]
    have : ∀ a, ν a * star (ν a) = ((Complex.normSq (ν a) : ℝ) : ℂ) := fun a => Complex.mul_conj (ν a)
    simp only [this]
    rw [← Complex.ofReal_sum]
    unfold C6.sq2 at hν
    rw [hν, Complex.ofReal_one]

end TLC

open TLC in
theorem capelli_vector_frame : TL.CapVFrame := by
  intro Wq _ _ _ k r z' π' B0 Bs ν hk hz hT hπ hB0 hν hBs w v
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨he, hez, hee⟩ := cap_vec hB0 hν
  set e := ∑ j, ν j • B0 j with hedef
  have hBs1 := HermitianFormSums.frame_sub hBs
  set C : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs e with hCdef
  have hCc : ∀ a : Fin n, C a.castSucc = Bs a := fun a => by rw [hCdef, Fin.snoc_castSucc]
  have hCl : C (Fin.last n) = e := by rw [hCdef, Fin.snoc_last]
  have hBe : ∀ a, herm (Hpk (n + 1) r) (Bs a) e = 0 := fun a => hBs.2.2 a e (by simp)
  have heB : ∀ a, herm (Hpk (n + 1) r) e (Bs a) = 0 := fun a => by
    rw [← Qx2.herm_star, hBe, star_zero]
  have hC : IsFrameOf (n + 1) r [z'] C := by
    refine ⟨fun a => ?_, fun a b => ?_, fun a v hv => ?_⟩
    · refine Fin.lastCases ?_ (fun a => ?_) a
      · rw [hCl]; exact he
      · rw [hCc]; exact hBs.1 a
    · refine Fin.lastCases ?_ (fun a => ?_) a
      · refine Fin.lastCases ?_ (fun b => ?_) b
        · rw [hCl, hee, if_pos rfl]
        · rw [hCl, hCc, heB, if_neg (Fin.castSucc_lt_last b).ne']
      · refine Fin.lastCases ?_ (fun b => ?_) b
        · rw [hCl, hCc, hBe, if_neg (Fin.castSucc_lt_last a).ne]
        · rw [hCc, hCc, hBs.2.1]
          simp only [Fin.castSucc_inj]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      subst hv
      refine Fin.lastCases ?_ (fun a => ?_) a
      · rw [hCl]; exact hez
      · rw [hCc]; exact hBs.2.2 a v (by simp)
  obtain ⟨hQP, hPQ, hEB⟩ := cap_econj hz hT hπ hC hB0
  set P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun c a => herm (Hpk (n + 1) r) (C a) (B0 c) with hP
  set Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun b d => herm (Hpk (n + 1) r) (B0 d) (C b) with hQ
  have hcol : (fun p => P p (Fin.last n)) = ν := by
    funext p
    simp only [hP, Matrix.of_apply, hCl, hedef, HermitianFormSums.herm_lsum, hB0.2.1, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hβ : ∀ j, (star ν ᵥ* P) j = if j = Fin.last n then 1 else 0 := by
    intro j
    have h1 : (star ν ᵥ* P) j = herm (Hpk (n + 1) r) (C j) e := by
      rw [hedef, HermitianFormSums.herm_rsum]
      simp only [Matrix.vecMul, dotProduct, hP, Matrix.of_apply, Pi.star_apply]
    rw [h1, ← hCl, hC.2.1, eq_comm]
  have hGl := (frame_general_linear Wq (n + 1) r (n + 1) z' π' B0 hπ hB0).1
  have key := AnisotropicColumnSums.chat_gen (n + 1) n rfl (Module.End ℂ Wq) (EB π' B0) P Q (Fin.last n) (by simp) Fin.castSucc
    (fun a => rfl) hGl hQP hPQ w (star ν) (fun j hj => by rw [hβ j, if_neg hj])
  rw [hcol, hβ, if_pos rfl, one_smul, ← hEB, ← BorderedDeterminants.qdet_sub] at key
  have hsub : subA (EB π' C) = EB π' Bs := by
    funext a b
    simp only [subA, EB, unitB, hCc]
  rw [hsub] at key
  have hcap := (frame_general_linear Wq (n + 1) r n z' π' Bs hπ hBs1).2 w v
  rw [hcap, ← key]
  rfl

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnTrSmooth
section
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hsVec_contDiff {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] :
    ContDiff ℝ ∞ (fun A : W →L[ℂ] V => B.hsVec A) := by
  let L : (W →L[ℂ] V) →ₗ[ℝ] PiLp 2 (fun _ : Fin (Module.finrank ℂ W) => V) :=
    { toFun := fun A => B.hsVec A
      map_add' := fun A A' => by ext i; simp [B.hsVec]
      map_smul' := fun c A => by ext i; simp [B.hsVec] }
  haveI : FiniteDimensional ℝ (W →L[ℂ] V) := FiniteDimensional.complexToReal _
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem wq_contDiff (k r : ℕ) (TT : ℝ) : ContDiff ℝ ∞ (fun x : MA.E r => MA.wq k x TT) := by
  have hn : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
    simp_rw [Complex.normSq_eq_norm_sq]
    exact contDiff_norm_sq ℝ
  unfold MA.wq
  apply ContDiff.mul
  · apply contDiff_prod
    intro l _
    exact (hn.comp ((contDiff_apply ℝ (fun _ => ℂ) l).comp contDiff_fst)).pow _
  · exact ((hn.comp contDiff_snd).sub contDiff_const).pow _

theorem wq_pos {k r : ℕ} {TT : ℝ} {x : MA.E r} (hx : x ∈ MA.Qset r TT) : 0 < MA.wq k x TT := by
  obtain ⟨h1, h2⟩ := hx
  unfold MA.wq
  apply mul_pos
  · apply Finset.prod_pos
    intro l _
    exact pow_pos (Complex.normSq_pos.mpr (h1 l)) _
  · exact pow_pos (by linarith) _

theorem trace_smoothness : TrSmooth := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v hIP e he J hJ ρ
  obtain ⟨-, -, -, hTz, hTz', -, -⟩ := hIP
  have hsub : ∀ q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
      q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := by
    intro q hq
    refine ⟨hq.1, ?_⟩
    have h2 : (D.parOf S v).TT < Complex.normSq q.2 := hq.2
    have h3 : (D.parOf S v).TT = (D.parOf S v).T * (D.parOf S v).T' := rfl
    rw [h3, ← hTz, ← hTz'] at h2
    exact h2
  have hgq : ∀ q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
      B.gq (T v).base q ∈ Q.Glev S.G.k S.G.r 0 ∩ OmP S T v := fun q hq =>
    om_sub' (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base (hsub q hq))
  have hgqS : ContDiffOn ℝ ∞ (fun q => B.gq (T v).base q) (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
    (contDiffOn_infty.mpr fun n => Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn (T v).base n).mono hsub
  have hJq : ContDiffOn ℝ ∞ (fun q => B.hsVec (J (B.gq (T v).base q)))
      (MA.Qset (D.parOf S v).r (D.parOf S v).TT) := by
    intro x hx
    obtain ⟨U, F, hU, hxU, hF, hJF⟩ := hJ.1 _ (hgq x hx)
    have hFat : ContDiffAt ℝ ∞ F (B.gq (T v).base x) := hF.contDiffAt (hU.mem_nhds hxU)
    have h1 : ContDiffWithinAt ℝ ∞ (fun q => F (B.gq (T v).base q))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) x := hFat.comp_contDiffWithinAt x (hgqS x hx)
    have h2 : ContDiffWithinAt ℝ ∞ (fun q => B.hsVec (F (B.gq (T v).base q)))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) x :=
      (hsVec_contDiff (V := Wp (S.pl v)) (W := Wq (S.pl v))).contDiffAt.comp_contDiffWithinAt x h1
    refine h2.congr_of_eventuallyEq ?_ ?_
    · have hpre := (hgqS x hx).continuousWithinAt.preimage_mem_nhdsWithin (hU.mem_nhds hxU)
      filter_upwards [hpre, self_mem_nhdsWithin] with y hyU hyQ
      rw [hJF _ hyU (hgq y hyQ).1]
    · rw [hJF _ hxU (hgq x hx).1]
  have he2 : ContDiffOn ℝ ∞ (fun q : MA.E (D.parOf S v).r => B.hsVec (e ρ q.2))
      (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
    (hsVec_contDiff (V := Wp (S.pl v)) (W := Wq (S.pl v))).comp_contDiffOn
      ((he.1 ρ).comp contDiff_snd.contDiffOn (fun q hq => hq.2))
  have hw0 : ContDiffOn ℝ ∞ (fun q : MA.E (D.parOf S v).r => Real.sqrt (MA.wq S.G.k q (D.parOf S v).TT))
      (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
    (wq_contDiff _ _ _).contDiffOn.sqrt fun q hq => (wq_pos hq).ne'
  have hw : ContDiffOn ℝ ∞ (fun q : MA.E (D.parOf S v).r =>
      ((Real.sqrt (MA.wq S.G.k q (D.parOf S v).TT) : ℝ) : ℂ))
      (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hw0
  have hF := hw.mul (ContDiffOn.inner ℂ he2 hJq)
  show ContDiffOn ℝ MA.sm (MA.ext _) (MA.Qset (D.parOf S v).r (D.parOf S v).TT)
  refine hF.congr ?_
  intro x hx
  rw [MA.ext, dite_eq_left hx]

end Formalism.FourierDecayAlt.P.CutMP.En
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnFinal
section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

def GTConnOfLeaves : Prop := GTCLocal → GTCReal → GTCCurv → GTCHol → GTCAnnulus → GTConn

theorem gTConn_of_leaves : GTConnOfLeaves := fun hL hR hC hH hA =>
  gTConn_of_cut hL (gTCPhase_of_cut hR hC hH hA torus_parameter) gauge_transform_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTopActCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def QTop : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (h : ℂ),
    ∃ d : ℕ → A, (∀ Y : ℂ, qminor E id id (Y + h) = ∑ j ∈ Finset.range (n + 1), Y ^ j • d j) ∧
      (1 ≤ n → d (n - 1) = ∑ a, E a a + algebraMap ℂ A ((n : ℂ) * h - (n : ℂ) * ((n : ℂ) - 1) / 2))

theorem interp {V : Type*} [AddCommGroup V] [Module ℂ V] (N : ℕ) (W : Matrix (Fin N) (Fin N) ℂ)
    (hW : W * Matrix.vandermonde (fun i : Fin N => ((i : ℕ) : ℂ)) = 1) (p : ℂ → V) (a : ℕ → V)
    (ha : ∀ Y, p Y = ∑ j ∈ Finset.range N, Y ^ j • a j) (j : Fin N) :
    ∑ i : Fin N, W j i • p ((i : ℕ) : ℂ) = a j := by
  have key : ∀ l : Fin N, ∑ i : Fin N, W j i * ((i : ℕ) : ℂ) ^ (l : ℕ) = if j = l then 1 else 0 := by
    intro l
    have h := congrFun (congrFun hW j) l
    simpa [Matrix.mul_apply, Matrix.vandermonde_apply, Matrix.one_apply] using h
  simp_rw [ha, Finset.sum_range, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, key, ite_smul, one_smul, zero_smul]
  simp

theorem vdm_inv (N : ℕ) : ∃ W : Matrix (Fin N) (Fin N) ℂ,
    W * Matrix.vandermonde (fun i : Fin N => ((i : ℕ) : ℂ)) = 1 := by
  refine ⟨(Matrix.vandermonde (fun i : Fin N => ((i : ℕ) : ℂ)))⁻¹, Matrix.nonsing_inv_mul _ ?_⟩
  rw [isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
  intro a b h
  exact Fin.ext (Nat.cast_injective h)

theorem pt_poly (hQ : QTop) {k r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (D : Set (Mx k r)) (hD : IsOpen D) (f : Mx k r → V) (hf : SmoothLev k r (Fin.last r) D f)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) :
    ∃ a : ℕ → V, (∀ Y : ℂ, capL k r (Fin.last r) (uC k r (Fin.last r) Y) f g =
        ∑ j ∈ Finset.range (mdim k r (Fin.last r) + 1), Y ^ j • a j) ∧
      a (mdim k r (Fin.last r) - 1) = ∑ b : Fin (mdim k r (Fin.last r)),
        EH k r (posL k r (Fin.last r) b) (posL k r (Fin.last r) b) f g := by
  obtain ⟨d, hd, htop⟩ := hQ (Module.End ℂ (SV k r (Fin.last r) D V)) (mdim k r (Fin.last r))
    (EV k r (Fin.last r) D V) (((mdim k r (Fin.last r) : ℂ) - 1) / 2)
  refine ⟨fun j => (d j (mkV hD f hf)).1 g, fun Y => ?_, ?_⟩
  · have h1 := (OperatorRepresentations.rep_qminor (E := V) hD (id : Fin (mdim k r (Fin.last r)) → Fin (mdim k r (Fin.last r))) id
      (uC k r (Fin.last r) Y)).mkV hD hf hg
    simp only [Function.comp_id] at h1
    have e : uC k r (Fin.last r) Y = Y + ((mdim k r (Fin.last r) : ℂ) - 1) / 2 := rfl
    unfold capL
    rw [← h1, e, hd Y, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
  · have hn1 : 1 ≤ mdim k r (Fin.last r) := by simp [mdim]
    show (d (mdim k r (Fin.last r) - 1) (mkV hD f hf)).1 g = _
    rw [htop hn1]
    have e0 : ((mdim k r (Fin.last r) : ℂ) * (((mdim k r (Fin.last r) : ℂ) - 1) / 2) -
        (mdim k r (Fin.last r) : ℂ) * ((mdim k r (Fin.last r) : ℂ) - 1) / 2) = 0 := by ring
    rw [e0, map_zero, add_zero, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun b _ => (OperatorRepresentations.rep_EV (E := V) hD b b).mkV hD hf hg

theorem mdim_last (k r : ℕ) : mdim k r (Fin.last r) = k + 1 := by
  simp [Q.mdim]

theorem gTRTopAct_of_cut (hQ : QTop) : GTRTopAct := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' hpl hk X
  obtain ⟨W, hW⟩ := vdm_inv (P.k + 2)

  have hpt : ∀ (Φ : RadSp P.k P.r z z' π π'), ∀ x ∈ DomR P.k P.r z z',
      ∃ a : ℕ → (Wq →L[ℂ] Wp), (∀ Y : ℂ, ((X.t Y 0 0 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          ∑ j ∈ Finset.range (P.k + 2), Y ^ j • a j) ∧
        a P.k = ∑ b : Fin (mdim P.k P.r (Fin.last P.r)),
          EH P.k P.r (posL P.k P.r (Fin.last P.r) b) (posL P.k P.r (Fin.last P.r) b)
            ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2 := by
    intro Φ x hx
    have hmem := Φ.2
    obtain ⟨_, hs, _⟩ := hmem
    obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs x hx
    set D : Set (Mx P.k P.r) := {g | (x.1, g) ∈ U} with hDdef
    have hc : ContDiff ℝ ∞ (fun g : Mx P.k P.r => (x.1, g)) := contDiff_prodMk_right x.1
    have hD : IsOpen D := hU.preimage hc.continuous
    have hf : SmoothLev P.k P.r (Fin.last P.r) D ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) := by
      intro g₀ hg₀
      refine ⟨D, fun g => F (x.1, g), hD, hg₀.2, ?_, fun g hgD hgG => hΦ (x.1, g) hgD hgG⟩
      exact hF.comp hc.contDiffOn (fun g hg => hg)
    have hg : x.2 ∈ Glev P.k P.r (Fin.last P.r) ∩ D := ⟨hx.2.1, by simpa [hDdef] using hxU⟩
    obtain ⟨a, ha, htop⟩ := pt_poly hQ D hD _ hf hg
    have hm : mdim P.k P.r (Fin.last P.r) + 1 = P.k + 2 := by rw [mdim_last]
    have hm1 : mdim P.k P.r (Fin.last P.r) - 1 = P.k := by rw [mdim_last]; rfl
    refine ⟨a, fun Y => ?_, ?_⟩
    · rw [X.t_apply Y 0 0 Φ x hx, ← hm]
      exact ha Y
    · rw [← htop, hm1]

  let c : ℕ → Module.End ℂ (RadSp P.k P.r z z' π π') := fun j =>
    if h : j < P.k + 2 then ∑ i : Fin (P.k + 2), W ⟨j, h⟩ i • X.t ((i : ℕ) : ℂ) 0 0 else 0
  have hval : ∀ (T : Module.End ℂ (RadSp P.k P.r z z' π π')) (Φ : RadSp P.k P.r z z' π π') x,
      x ∉ DomR P.k P.r z z' → ((T Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = 0 := by
    intro T Φ x hx
    have hmem := (T Φ).2
    obtain ⟨h0, _, _⟩ := hmem
    exact h0 x hx
  have hc : ∀ (Φ : RadSp P.k P.r z z' π π'), ∀ x ∈ DomR P.k P.r z z', ∀ (a : ℕ → (Wq →L[ℂ] Wp)),
      (∀ Y : ℂ, ((X.t Y 0 0 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          ∑ j ∈ Finset.range (P.k + 2), Y ^ j • a j) →
      ∀ j ∈ Finset.range (P.k + 2), ((c j Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = a j := by
    intro Φ x hx a ha j hj
    have hj' : j < P.k + 2 := Finset.mem_range.1 hj
    have e1 : c j = ∑ i : Fin (P.k + 2), W ⟨j, hj'⟩ i • X.t ((i : ℕ) : ℂ) 0 0 := dif_pos hj'
    rw [e1, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
    simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    exact interp (P.k + 2) W hW (fun Y => ((X.t Y 0 0 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)
      a ha ⟨j, hj'⟩
  refine ⟨c, fun Y => ?_, 0, fun Φ x hx => ?_⟩
  · apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    funext c0 g
    by_cases hx : (c0, g) ∈ DomR P.k P.r z z'
    · obtain ⟨a, ha, -⟩ := hpt Φ (c0, g) hx
      have hL := ha Y
      simp only at hL
      rw [hL, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply]
      congr 1
      exact (hc Φ (c0, g) hx a ha j hj).symm
    · have h1 := hval (X.t Y 0 0) Φ (c0, g) hx
      have h2 := hval (∑ j ∈ Finset.range (P.k + 2), Y ^ j • c j) Φ (c0, g) hx
      simp only at h1 h2
      rw [h1, h2]
  · obtain ⟨a, ha, htop⟩ := hpt Φ x hx
    rw [hc Φ x hx a ha P.k (Finset.mem_range.2 (by omega)), htop]
    simp

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct
end

