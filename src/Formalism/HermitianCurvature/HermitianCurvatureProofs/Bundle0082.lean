module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0077
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0029
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0044
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbConvDDOfDecDD
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem ag_nonneg (k r : ℕ) : 0 ≤ AG k r := by unfold AG; positivity

theorem gap4 {k r : ℕ} {h : ℝ} (hG : GapOK k r h) :
    9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 3 ≤ aOf r h := hG.2.2.2

theorem thr_of_gapOK {k r : ℕ} {h : ℝ} (hG : GapOK k r h) : JF.TransportedAlt k r (aOf r h) 0 := by
  have h4' := gap4 hG
  have h4 : 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < aOf r h := by
    linarith [ag_nonneg k r]
  unfold JF.TransportedAlt
  have hpos : (0 : ℝ) < 9 * ((r : ℝ) + 1) := by positivity
  rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hpos]
  calc ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * (9 * ((r : ℝ) + 1))
      = 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by ring
    _ < aOf r h := h4

theorem aOf_pos_of_gapOK {k r : ℕ} {h : ℝ} (hG : GapOK k r h) : 0 < aOf r h := by
  have h4 := gap4 hG
  have h5 := ag_nonneg k r
  have : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  linarith

theorem rho_triv {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r)
    (F : B.Mat k r → (ℂ →L[ℂ] ℂ)) (g : B.Mat k r) : B.rho (triv D) p F g = F (B.sgs p g) := by
  ext
  simp [B.rho, triv]

theorem rpow_bound (t C a : ℝ) (ht : 0 ≤ t) (ha : a ≠ 0) : t ^ a * (C * t ^ (-a)) ≤ |C| := by
  rcases ht.lt_or_eq with h | h
  · rw [mul_left_comm, ← Real.rpow_add h, add_neg_cancel, Real.rpow_zero, mul_one]
    exact le_abs_self C
  · subst h
    rw [Real.zero_rpow ha, zero_mul]
    exact abs_nonneg C

theorem orbConvDD_of_decDD (hD : DecDD) : OrbConvDD := by
  intro hIn k r Wp Wq _ _ _ _ _ _ _ _ D ε lam h H _ _ _ σ w0 u u' νq νq' hS hS' x hx y hy
  obtain ⟨C, hC⟩ :=
    hD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS y hy x hx
  have hG : GapOK k r h := hS.2.2.2.1
  have hσ : PI.UpqRep.IsDSHpk k r ε lam σ := hS.2.1
  have hThr : JF.TransportedAlt k r (aOf r h) 0 := thr_of_gapOK hG
  have ha : aOf r h ≠ 0 := (aOf_pos_of_gapOK hG).ne'
  let f : Mx k r → ℂ := fun g => ⟪x, σ g y⟫_ℂ
  have hfc : ContinuousOn f (B.GV k r) :=
    ContinuousOn.inner continuousOn_const (sigma_contOn hσ y)
  let F : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun g => f g • (1 : ℂ →L[ℂ] ℂ)
  have hCC : B.InCC (aOf r h) 0 F := by
    refine ⟨|C|, ckOn_zero_of_contOn f hfc, ?_⟩
    intro uu vv _ _ hlen g hg
    have hu : uu = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hv : vv = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu; subst hv
    show B.gN g ^ aOf r h * ‖F g‖ ≤ |C|
    have hF : ‖F g‖ = ‖f g‖ := by simp [F]
    rw [hF]
    have hgN : 0 ≤ B.gN g := Real.sqrt_nonneg _
    calc B.gN g ^ aOf r h * ‖f g‖ ≤ B.gN g ^ aOf r h * (C * B.gN g ^ (-aOf r h)) :=
          mul_le_mul_of_nonneg_left (hC g hg) (Real.rpow_nonneg hgN _)
      _ ≤ |C| := rpow_bound _ _ _ hgN ha
  have hJC := Formalism.FourierDecayAlt.P.bessel_integral_converges k r ℂ ℂ (triv D) (aOf r h) F hThr hCC
  have hJD := Formalism.FourierDecayAlt.P.bessel_integral_domain k r ℂ ℂ (triv D) (aOf r h) 0 F hThr hCC
  have hnorm : ∀ p γ, ‖⟪x, σ (B.sgs p γ) y⟫_ℂ‖ = ‖B.rho (triv D) p F γ‖ := by
    intro p γ
    rw [rho_triv]
    simp [F, f]
  have happ : ∀ p γ, ⟪x, σ (B.sgs p γ) y⟫_ℂ = (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) (B.rho (triv D) p F γ) := by
    intro p γ
    rw [rho_triv]
    simp [F, f]
  refine ⟨fun γ hγ => ?_, fun K hK hKO => ?_⟩
  · obtain ⟨b, hb, hbd⟩ := hJC.2 {γ} isCompact_singleton (Set.singleton_subset_iff.mpr hγ)
    have hmeas : AEStronglyMeasurable (fun p => B.rho (triv D) p F γ) D.μSS :=
      hJD.1 [] [] (by simp) (by simp) (by simp) γ hγ
    have hmeas' : AEStronglyMeasurable (fun p => ⟪x, σ (B.sgs p γ) y⟫_ℂ) D.μSS := by
      have := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).continuous.comp_aestronglyMeasurable hmeas
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      exact (happ p γ).symm
    refine Integrable.mono' hb hmeas' ?_
    filter_upwards [hbd γ rfl] with p hp
    rw [hnorm]
    exact hp
  · obtain ⟨b, hb, hbd⟩ := hJC.2 K hK hKO
    refine ⟨b, hb, fun γ hγ => ?_⟩
    filter_upwards [hbd γ hγ] with p hp
    rw [hnorm]
    exact hp

end Formalism.FourierDecayAlt.P.S3dx4
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.StrictMonoSnoc
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem det_row_sum {n : ℕ} {ι : Type} (s : Finset ι) (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (c : ι → ℂ)
    (v : ι → Fin n → ℂ) :
    (M.updateRow i (∑ w ∈ s, c w • v w)).det = ∑ w ∈ s, c w * (M.updateRow i (v w)).det := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp [Matrix.updateRow_self])
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.det_updateRow_add,
      Matrix.det_updateRow_smul, ih]

theorem det_row_lin {n : ℕ} {ι : Type} [Fintype ι] (X : Fin n → Fin n → ℂ) (i : Fin n) (η : ι → ℂ)
    (v : ι → Fin n → ℂ) (hrow : ∀ l, X i l = ∑ w, η w * v w l) :
    (Matrix.of X).det = ∑ w, η w * (Matrix.of fun a l => if a = i then v w l else X a l).det := by
  have h1 : Matrix.of X = (Matrix.of X).updateRow i (∑ w, η w • v w) := by
    ext a l
    by_cases h : a = i
    · subst h
      simp [Matrix.updateRow_self, hrow, Finset.sum_apply]
    · simp [Matrix.updateRow_ne h]
  have h2 : ∀ w, (Matrix.of fun a l => if a = i then v w l else X a l) =
      (Matrix.of X).updateRow i (v w) := by
    intro w
    ext a l
    by_cases h : a = i
    · subst h
      simp
    · simp [h, Matrix.updateRow_ne h]
  calc (Matrix.of X).det = ((Matrix.of X).updateRow i (∑ w ∈ Finset.univ, η w • v w)).det :=
        congrArg Matrix.det h1
    _ = ∑ w ∈ Finset.univ, η w * ((Matrix.of X).updateRow i (v w)).det := det_row_sum _ _ _ _ _
    _ = ∑ w, η w * (Matrix.of fun a l => if a = i then v w l else X a l).det :=
        Finset.sum_congr rfl (fun w _ => by rw [h2 w])

theorem sum_lin {M : Type*} [AddCommGroup M] [Module ℂ M] {m N : ℕ} {ι : Type} [Fintype ι]
    (P : (Fin m → Fin N) → Prop) [DecidablePred P] (X : Fin m → Fin N → ℂ) (i : Fin m) (η : ι → ℂ)
    (v : ι → Fin N → ℂ) (hrow : ∀ p, X i p = ∑ w, η w * v w p) (F : (Fin m → Fin N) → M) :
    (∑ c : Fin m → Fin N, if P c then (Matrix.of fun a l => X a (c l)).det • F c else 0) =
      ∑ w, η w • ∑ c : Fin m → Fin N,
        if P c then (Matrix.of fun a l => (if a = i then v w (c l) else X a (c l))).det • F c else 0 := by
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  split_ifs with hP
  · rw [det_row_lin (fun a l => X a (c l)) i η (fun w l => v w (c l)) (fun l => hrow (c l)),
      Finset.sum_smul]
    exact Finset.sum_congr rfl (fun w _ => mul_smul _ _ _)
  · simp

theorem strictMono_snoc {α : Type} [Preorder α] {m : ℕ} (f : Fin m → α) (hf : StrictMono f) (x : α)
    (hx : ∀ l, f l < x) : StrictMono (Fin.snoc (α := fun _ => α) f x : Fin (m + 1) → α) := by
  intro a b hab
  induction b using Fin.lastCases with
  | last =>
    induction a using Fin.lastCases with
    | last => exact absurd hab (lt_irrefl _)
    | cast a =>
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact hx a
  | cast b =>
    induction a using Fin.lastCases with
    | last => exact absurd hab (not_lt.2 (Fin.castSucc_lt_last b).le)
    | cast a =>
      simp only [Fin.snoc_castSucc]
      exact hf (Fin.castSucc_lt_castSucc_iff.1 hab)

theorem hpk_zero_alt (k r : ℕ) (p q : Fin (2 * r + k + 1)) (hq : r ≤ q.val ∧ q.val ≤ r + k)
    (hp : ¬ (r ≤ p.val ∧ p.val ≤ r + k)) : Hpk k r q p = 0 := by
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem herm_bvec_sum (k r : ℕ) (yb : Fin (2 * r + k + 1) → ℂ) (hyb : inWb k r yb) (p : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec p) yb =
      ∑ w : Fin (k + 1), herm (Hpk k r) (bvec (wI k r w)) yb * (if p = wI k r w then 1 else 0) := by
  unfold inWb at hyb
  unfold herm bvec wI
  by_cases hp : r ≤ (p : ℕ) ∧ (p : ℕ) ≤ r + k
  · rw [Finset.sum_eq_single (⟨(p : ℕ) - r, by omega⟩ : Fin (k + 1))]
    · split_ifs with h
      · rw [mul_one, ← h]
      · exact absurd (Fin.ext (by simp only [Fin.val_mk]; omega)) h
    · intro b _ hb
      split_ifs with h
      · exact absurd (Fin.ext (by simp only [Fin.ext_iff, Fin.val_mk] at h ⊢; omega)) hb
      · exact mul_zero _
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hL : star yb ⬝ᵥ Hpk k r *ᵥ Pi.single p 1 = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k
      · have h0 : (Hpk k r *ᵥ Pi.single p 1) i = 0 := by
          simp [Matrix.mulVec, hpk_zero_alt k r p i hi hp]
        rw [h0, mul_zero]
      · have h0 : yb i = 0 := hyb i (by omega)
        simp [h0]
    rw [hL]
    symm
    apply Finset.sum_eq_zero
    intro w _
    split_ifs with h
    · have hw := w.isLt
      rw [Fin.ext_iff] at h
      simp only [Fin.val_mk] at h
      exact absurd ⟨by omega, by omega⟩ hp
    · exact mul_zero _

theorem hpk_real (k r : ℕ) (p q : Fin (2 * r + k + 1)) : star (Hpk k r p q) = Hpk k r p q := by
  unfold Hpk
  split_ifs <;> simp

theorem hpk_symm (k r : ℕ) (p q : Fin (2 * r + k + 1)) : Hpk k r p q = Hpk k r q p := by
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_star (k r : ℕ) (p q : Fin (2 * r + k + 1)) : star (Hpk k r p q) = Hpk k r q p := by
  rw [hpk_real, hpk_symm]

theorem herm_swap (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  unfold herm
  have hH : (Hpk k r)ᴴ = Hpk k r := by
    ext p q
    rw [conjTranspose_apply, hpk_star]
  rw [star_dotProduct v (Hpk k r *ᵥ w), star_star, star_mulVec, hH, dotProduct_mulVec]

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SupportPhiZeroSubset
section
namespace Formalism.FourierDecayAlt.P.PBI

open Finset Filter Topology MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

open Classical

def gPoly {r : ℕ} (TT : ℝ) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : ℝ :=
  Complex.normSq M.det - TT * Complex.normSq (M.submatrix Fin.castSucc Fin.castSucc).det

theorem gf_eq_gPoly (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    Gf k r z z' g = gPoly (Tz k r z * Tz k r z') (Zhat k r z z' g) := by
  first
    | rfl
    | (unfold Gf gPoly Dmin; rfl)
    | (simp only [Gf, gPoly, Dmin]; rfl)

theorem continuous_gPoly (r : ℕ) (TT : ℝ) : Continuous fun Z : G.Mat (r + 1) => gPoly TT (Matrix.of Z) := by
  have hc : Continuous fun Z : G.Mat (r + 1) =>
      (Matrix.of Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) := continuous_id
  unfold gPoly
  exact (Complex.continuous_normSq.comp hc.matrix_det).sub
    (continuous_const.mul (Complex.continuous_normSq.comp (hc.matrix_submatrix _ _).matrix_det))

section fibre

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def fibInt (Bs : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : Wq →L[ℂ] Wp :=
  ∫ p, B.rho Bs p F g ∂((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0'))

def phi0 (Bs : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (sec : G.Mat (r + 1) → Mt k r)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) : G.Mat (r + 1) → (Wq →L[ℂ] Wp) := fun Z =>
  if 0 < gPoly (Tz k r Bs.z * Tz k r Bs.z') (Matrix.of Z) then fibInt Bs μ0 μ0' F (Matrix.of (sec Z)) else 0

def IsSec (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (sec : G.Mat (r + 1) → Mt k r) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sec {Z | 0 < gPoly (Tz k r Bs.z * Tz k r Bs.z') (Matrix.of Z)} ∧
    ∀ Z, 0 < gPoly (Tz k r Bs.z * Tz k r Bs.z') (Matrix.of Z) →
      Matrix.of (sec Z) ∈ B.GV k r ∧ Zhat k r Bs.z Bs.z' (Matrix.of (sec Z)) = Matrix.of Z ∧
        D.IsDFrame Bs ν' m₀ (Matrix.of (sec Z))

theorem cpt_of_fibre {E : Type*} [NormedAddCommGroup E] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef Bs F) (Ψ : G.Mat (r + 1) → E)
    (hΨ : ∀ Z, Ψ Z ≠ 0 → ∃ g ∈ B.GV k r, F g ≠ 0 ∧ Zhat k r Bs.z Bs.z' g = Matrix.of Z) :
    HasCompactSupport Ψ ∧ ∀ Z ∈ tsupport Ψ, G.detM Z ≠ 0 := by
  obtain ⟨_, ⟨R, hR⟩, ε, hε, hεG⟩ := hF
  obtain ⟨C, hC⟩ := zhat_norm_bound k r Bs.z Bs.z'
  set TT : ℝ := Tz k r Bs.z * Tz k r Bs.z' with hTT
  set K : Set (G.Mat (r + 1)) :=
    Metric.closedBall 0 (max C 0 * R) ∩ {Z | ε ≤ gPoly TT (Matrix.of Z)} with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 _).inter_right (isClosed_le continuous_const (continuous_gPoly r TT))
  have hsub : Function.support Ψ ⊆ K := by
    intro Z hZ
    obtain ⟨g, hg, hFg, hZg⟩ := hΨ Z hZ
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : C2.mx (Zhat k r Bs.z Bs.z' g) ≤ C * B.gN g := hC g
      rw [hZg] at h1
      have h2 : C2.mx (Matrix.of Z) = ‖Z‖ := rfl
      rw [h2] at h1
      have hgN : 0 ≤ B.gN g := Real.sqrt_nonneg _
      have hRg : B.gN g ≤ R := hR g hg hFg
      calc ‖Z‖ ≤ C * B.gN g := h1
        _ ≤ max C 0 * B.gN g := mul_le_mul_of_nonneg_right (le_max_left _ _) hgN
        _ ≤ max C 0 * R := mul_le_mul_of_nonneg_left hRg (le_max_right _ _)
    · show ε ≤ gPoly TT (Matrix.of Z)
      have := hεG g hg hFg
      rw [gf_eq_gPoly, hZg] at this
      exact this
  have hts : tsupport Ψ ⊆ K := closure_minimal hsub hKc.isClosed
  refine ⟨hKc.of_isClosed_subset (isClosed_tsupport Ψ) hts, fun Z hZ => ?_⟩
  have hZK := (hts hZ).2
  simp only [Set.mem_ofPred_eq, gPoly] at hZK
  have hTT0 : 0 ≤ TT := mul_nonneg Bs.T_pos.le Bs.T'_pos.le
  have hpos : 0 < Complex.normSq (Matrix.of Z).det := by
    have := mul_nonneg hTT0 (Complex.normSq_nonneg ((Matrix.of Z).submatrix Fin.castSucc Fin.castSucc).det)
    linarith
  intro h0
  unfold G.detM at h0
  rw [h0, map_zero] at hpos
  exact lt_irrefl _ hpos

theorem support_phi_zero_subset (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (μ0 μ0' : Measure (Mt k r)) (hμ0 : B.IsHaarOn (C2.N0set k r Bs.z) μ0)
    (hμ0' : B.IsHaarOn (C2.N0set k r Bs.z') μ0') (sec : G.Mat (r + 1) → Mt k r) (hsec : IsSec Bs ν' m₀ sec)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (Z : G.Mat (r + 1)) (hZ : phi0 Bs μ0 μ0' sec F Z ≠ 0) :
    ∃ g ∈ B.GV k r, F g ≠ 0 ∧ Zhat k r Bs.z Bs.z' g = Matrix.of Z := by
  unfold phi0 at hZ
  split_ifs at hZ with hG
  · obtain ⟨hg0, hZg0, -⟩ := hsec.2 Z hG
    set g0 : B.Mat k r := Matrix.of (sec Z) with hg0def
    by_contra hno
    push Not at hno
    apply hZ
    unfold fibInt
    have hW := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF Bs.haarW
    have hW' := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF Bs.haarW'
    have hN := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hμ0
    have hN' := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hμ0'
    have b1 : ∀ᵐ q ∂(Bs.μW.prod μ0), Matrix.of q.1 ∈ UWset k r Bs.z :=
      (Measure.quasiMeasurePreserving_fst (μ := Bs.μW) (ν := μ0)).ae
        (Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem Bs.haarW)
    have b2 : ∀ᵐ q ∂(Bs.μW.prod μ0), Matrix.of q.2 ∈ C2.N0set k r Bs.z :=
      (Measure.quasiMeasurePreserving_snd (μ := Bs.μW) (ν := μ0)).ae (Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem hμ0)
    have c1 : ∀ᵐ q ∂(Bs.μW'.prod μ0'), Matrix.of q.1 ∈ UWset k r Bs.z' :=
      (Measure.quasiMeasurePreserving_fst (μ := Bs.μW') (ν := μ0')).ae
        (Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem Bs.haarW')
    have c2 : ∀ᵐ q ∂(Bs.μW'.prod μ0'), Matrix.of q.2 ∈ C2.N0set k r Bs.z' :=
      (Measure.quasiMeasurePreserving_snd (μ := Bs.μW') (ν := μ0')).ae (Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem hμ0')
    have d1 : ∀ᵐ p ∂((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0')),
        Matrix.of p.1.1 ∈ UWset k r Bs.z ∧ Matrix.of p.1.2 ∈ C2.N0set k r Bs.z :=
      (Measure.quasiMeasurePreserving_fst (μ := Bs.μW.prod μ0) (ν := Bs.μW'.prod μ0')).ae (b1.and b2)
    have d2 : ∀ᵐ p ∂((Bs.μW.prod μ0).prod (Bs.μW'.prod μ0')),
        Matrix.of p.2.1 ∈ UWset k r Bs.z' ∧ Matrix.of p.2.2 ∈ C2.N0set k r Bs.z' :=
      (Measure.quasiMeasurePreserving_snd (μ := Bs.μW.prod μ0) (ν := Bs.μW'.prod μ0')).ae (c1.and c2)
    apply integral_eq_zero_of_ae
    filter_upwards [d1, d2] with p h1 h2
    have hGG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
    have hNN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
    have hz : C2.StdZ k r Bs.z := ⟨Bs.z_mem, Bs.T_pos⟩
    have hz' : C2.StdZ k r Bs.z' := ⟨Bs.z'_mem, Bs.T'_pos⟩
    set h := (Matrix.of p.1.1 : B.Mat k r)
    set n := (Matrix.of p.1.2 : B.Mat k r)
    set h' := (Matrix.of p.2.1 : B.Mat k r)
    set n' := (Matrix.of p.2.2 : B.Mat k r)
    have hhG : h ∈ B.GV k r := h1.1.1
    have hnG : n ∈ B.GV k r := h1.2.1.1
    have hh'G : h' ∈ B.GV k r := h2.1.1
    have hn'G : n' ∈ B.GV k r := h2.2.1.1
    have hsgs : B.sgs p g0 = h⁻¹ * (n⁻¹ * g0 * n') * h' := by
      simp only [B.sgs, Matrix.mul_assoc]; rfl
    have hmem : B.sgs p g0 ∈ B.GV k r := by
      rw [hsgs]
      exact hGG.mul_mem _ (hGG.mul_mem _ (hGG.inv_mem _ hhG)
        _ (hGG.mul_mem _ (hGG.mul_mem _ (hGG.inv_mem _ hnG) _ hg0) _ hn'G)) _ hh'G
    have hS_h : h ∈ Sset k r Bs.z := ⟨h, h1.1, 1, hNN.one_mem, (Matrix.mul_one h).symm⟩
    have hS_h' : h' ∈ Sset k r Bs.z' := ⟨h', h2.1, 1, hNN.one_mem, (Matrix.mul_one h').symm⟩
    have hS_n : n ∈ Sset k r Bs.z :=
      ⟨1, (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs.z).one_mem, n, h1.2.1, (Matrix.one_mul n).symm⟩
    have hS_n' : n' ∈ Sset k r Bs.z' :=
      ⟨1, (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r Bs.z').one_mem, n', h2.2.1, (Matrix.one_mul n').symm⟩
    have e1 := Formalism.FourierDecayAlt.P.zhat_equivalence k r Bs.z Bs.z' hz hz' h hS_h h' hS_h' (n⁻¹ * g0 * n')
    have e2 := Formalism.FourierDecayAlt.P.zhat_equivalence k r Bs.z Bs.z' hz hz' n hS_n n' hS_n' g0
    have u1 : C2.uMap k r Bs.z h = 1 := (Formalism.FourierDecayAlt.P.unipotent_map_frame k r Bs.z hz).2 h h1.1
    have u1' : C2.uMap k r Bs.z' h' = 1 := (Formalism.FourierDecayAlt.P.unipotent_map_frame k r Bs.z' hz').2 h' h2.1
    rw [u1, u1', Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at e1
    rw [h1.2.2, h2.2.2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at e2
    have hZs : Zhat k r Bs.z Bs.z' (B.sgs p g0) = Matrix.of Z := by rw [hsgs, e1, e2, hZg0]
    have hF0 : F (B.sgs p g0) = 0 := by
      by_contra hne
      exact hno _ hmem hne hZs
    simp [B.rho, hF0]
  · exact absurd rfl hZ

end fibre

def SectionExists : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r),
    D.IsBaseFrame Bs ν' m₀ → ∃ sec : G.Mat (r + 1) → Mt k r, IsSec Bs ν' m₀ sec

def FibIntSmooth : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (μ0 μ0' : Measure (Mt k r)) (sec : G.Mat (r + 1) → Mt k r)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    D.IsBaseFrame Bs ν' m₀ → B.IsHaarOn (C2.N0set k r Bs.z) μ0 → B.IsHaarOn (C2.N0set k r Bs.z') μ0' →
    IsSec Bs ν' m₀ sec → KB.CptCoef Bs F → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (phi0 Bs μ0 μ0' sec F)

def FibIntCells : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    ∃ (μ0 μ0' : Measure (Mt P.k P.r)) (c : ℂ), B.IsHaarOn (C2.N0set P.k P.r p.T.base.z) μ0 ∧
      B.IsHaarOn (C2.N0set P.k P.r p.T.base.z') μ0' ∧
      ∀ sec : G.Mat (P.r + 1) → Mt P.k P.r, IsSec p.T.base p.ν' p.m₀ sec →
      ∀ F, KB.CptCoef p.T.base F →
      ∀ (a : C.LPt) (σ : Equiv.Perm (Fin (P.r + 1))) (d : Fin (P.r + 1) → ℂ), D.IsLocPt a (P.r + 1) →
        U.hMat σ d = D.ptMatN a (P.r + 1) →
        p.V F a = U.PhiTop (p := P.r + 1) (s := 0) U.betaU σ d (c • phi0 p.T.base μ0 μ0' sec F)
          fun x => x.elim0

def Phi0Support : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (μ0 μ0' : Measure (Mt k r)) (sec : G.Mat (r + 1) → Mt k r) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    B.IsHaarOn (C2.N0set k r Bs.z) μ0 → B.IsHaarOn (C2.N0set k r Bs.z') μ0' → IsSec Bs ν' m₀ sec →
    KB.CptCoef Bs F → HasCompactSupport (phi0 Bs μ0 μ0' sec F) ∧
      ∀ Z ∈ tsupport (phi0 Bs μ0 μ0' sec F), G.detM Z ≠ 0

def PhiZeroOfParts : Prop := SectionExists → FibIntSmooth → FibIntCells → KB.PhiZero

end

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Formalism.FourierDecayAlt

theorem phi_zero_support : PBI.Phi0Support := by
  intro k r Wp Wq _ _ _ _ Bs ν' m₀ μ0 μ0' sec F hμ0 hμ0' hsec hF
  exact PBI.cpt_of_fibre Bs F hF (PBI.phi0 Bs μ0 μ0' sec F)
    (fun Z hZ => PBI.support_phi_zero_subset Bs ν' m₀ μ0 μ0' hμ0 hμ0' sec hsec F Z hZ)

theorem phi_zero_of_parts : PBI.PhiZeroOfParts := by
  intro hSec hSm hCells Wp Wq _ _ _ _ _ _ P p F hF
  obtain ⟨μ0, μ0', c, hμ0, hμ0', hV⟩ := hCells Wp Wq P p
  obtain ⟨sec, hsec⟩ := hSec P.k P.r Wp Wq p.T.base p.ν' p.m₀ p.hF
  have hsupp := phi_zero_support P.k P.r Wp Wq p.T.base p.ν' p.m₀ μ0 μ0' sec F hμ0 hμ0' hsec hF
  refine ⟨c • PBI.phi0 p.T.base μ0 μ0' sec F, ?_, ?_, ?_, ?_⟩
  · exact (hSm P.k P.r Wp Wq p.T.base p.ν' p.m₀ μ0 μ0' sec F p.hF hμ0 hμ0' hsec hF).const_smul c
  · exact hsupp.1.mono (Function.support_const_smul_subset c _)
  · intro Z hZ
    exact hsupp.2 Z (closure_mono (Function.support_const_smul_subset c _) hZ)
  · intro a σ d ha hd
    exact hV sec hsec F hF a σ d ha hd

end Formalism.FourierDecayAlt.P
end

