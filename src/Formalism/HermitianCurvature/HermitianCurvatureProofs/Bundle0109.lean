module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0102
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0084
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0063
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0106
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0103
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftDerivativeCurves

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLocalFrameB
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section frame

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem gcl_hsVec_add (A A' : Wq →L[ℂ] Wp) : B.hsVec (A + A') = B.hsVec A + B.hsVec A' := by
  ext i
  simp [B.hsVec]

theorem gcl_hsVec_sum {ι : Type} (s : Finset ι) (A : ι → (Wq →L[ℂ] Wp)) :
    B.hsVec (∑ i ∈ s, A i) = ∑ i ∈ s, B.hsVec (A i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · ext i
    simp [B.hsVec]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, gcl_hsVec_add, ih]

theorem gcl_hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  ext i
  simp [B.hsVec]

theorem gcl_wRc_smooth (P : M.Par) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => ((wR P.k P.TT ζ : ℝ) : ℂ)) (Ann P) := by
  have hre : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => ζ.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => ζ.im) := Complex.imCLM.contDiff
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => Complex.normSq ζ - P.TT) := by
    simp_rw [Complex.normSq_apply]
    exact ((hre.mul hre).add (him.mul him)).sub contDiff_const
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => wR P.k P.TT ζ) (Ann P) := by
    simp only [wR]
    exact ((h1.pow _).contDiffOn).sqrt (fun ζ hζ => (pow_pos (sub_pos.2 hζ) _).ne')
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h2

theorem gcl_wR_ne (P : M.Par) {ζ : ℂ} (hζ : ζ ∈ Ann P) : ((wR P.k P.TT ζ : ℝ) : ℂ) ≠ 0 := by
  have h : 0 < Complex.normSq ζ - P.TT := sub_pos.2 hζ
  have hw : 0 < wR P.k P.TT ζ := by
    unfold wR
    exact Real.sqrt_pos.2 (pow_pos h _)
  exact Complex.ofReal_ne_zero.2 hw.ne'

theorem gcl_dZ_smooth {g : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g s) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (NF.dZ g) s ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (NF.dZb g) s := by
  have hd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ g y) s :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hs).1 hg).2
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ g y 1) s :=
    hd.clm_apply contDiffOn_const
  have hI : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ g y Complex.I) s :=
    hd.clm_apply contDiffOn_const
  refine ⟨?_, ?_⟩
  · exact contDiffOn_const.mul (h1.sub (contDiffOn_const.mul hI))
  · exact contDiffOn_const.mul (h1.add (contDiffOn_const.mul hI))

theorem gcl_wirt_slice {r : ℕ} (F : MA.E r → ℂ) (x : MA.E r) (hF : DifferentiableAt ℝ F x) :
    MA.wirt M.vz F x = NF.dZ (fun ζ => F (x.1, ζ)) x.2 ∧
      MA.wirt M.vzb F x = NF.dZb (fun ζ => F (x.1, ζ)) x.2 := by
  have hmap : HasFDerivAt (fun ζ : ℂ => (x.1, ζ))
      ((0 : ℂ →L[ℝ] (Fin r → ℂ)).prod (ContinuousLinearMap.id ℝ ℂ)) x.2 :=
    (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
  have hF' : HasFDerivAt F (fderiv ℝ F x) (x.1, x.2) := by
    simpa using hF.hasFDerivAt
  have hcomp : HasFDerivAt (fun ζ => F (x.1, ζ))
      ((fderiv ℝ F x).comp ((0 : ℂ →L[ℝ] (Fin r → ℂ)).prod (ContinuousLinearMap.id ℝ ℂ))) x.2 :=
    hF'.comp x.2 hmap
  have hd : ∀ v : ℂ, fderiv ℝ (fun ζ => F (x.1, ζ)) x.2 v = fderiv ℝ F x (0, v) := by
    intro v
    rw [hcomp.fderiv]
    simp
  have e1 : MA.dirE (r := r) M.vz = ((0 : Fin r → ℂ), (1 : ℂ)) := by
    simp [MA.dirE, M.vz]
  have e2 : MA.dirE (r := r) M.vzb = ((0 : Fin r → ℂ), (1 : ℂ)) := by
    simp [MA.dirE, M.vzb]
  refine ⟨?_, ?_⟩
  · simp only [MA.wirt, NF.dZ, e1, hd]
    simp [M.vz] <;> ring
  · simp only [MA.wirt, NF.dZb, e2, hd]
    simp [M.vzb] <;> ring

theorem gcl_radR_sum {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type} (s : Finset ι) (F : ι → Q.Fn k r E)
    (x : (Fin r → ℂ) × ℂ) :
    NF.radR k r z z' μsec (∑ i ∈ s, F i) x = ∑ i ∈ s, NF.radR k r z z' μsec (F i) x := by
  by_cases hx : x ∈ NF.QR k r z z'
  · simp [NF.radR, Set.indicator, hx, Finset.sum_apply]
  · simp [NF.radR, Set.indicator, hx]

theorem gcl_trR_val (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
      ((wR P.k P.TT q.1.2 : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1)) := by
  have hmem := radial_space_smoothness Wp Wq P Bs hpl hk e he Φ ρ
  have hq : q.1 ∈ NF.QR P.k P.r Bs.z Bs.z' := by
    obtain ⟨h1, h2⟩ := q.2
    refine ⟨h1, ?_⟩
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
    exact h2
  have h1 : ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) =
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ := by
    simp only [trR, MA.toSm, dif_pos hmem]
  rw [h1]
  simp [rawR, NF.radR, Set.indicator_of_mem hq]

end frame

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLEig
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

namespace KLEigPf

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

theorem alg {ι : Type} [Fintype ι] [DecidableEq ι] (Qs : ι → (Wq →L[ℂ] Wq)) (x : ι → ℂ → ℂ)
    (C : ℂ → (Wq →L[ℂ] Wq)) (E : Wq →L[ℂ] Wp)
    (hQQ : ∀ ρ σ, (Qs ρ).comp (Qs σ) = if ρ = σ then Qs ρ else 0) (hsum : ∑ ρ, Qs ρ = 1)
    (hsep : ∀ ρ σ, ρ ≠ σ → ∃ Y, x ρ Y ≠ x σ Y)
    (hid : ∀ Y, E.comp (∑ σ, x σ Y • Qs σ) = E.comp (C Y)) (ρ : ι) :
    E.comp (Qs ρ) = E ↔ ∀ (Y : ℂ) (v : Wq), E (C Y v) = x ρ Y • E v := by
  have hQv : ∀ ρ σ v, Qs ρ (Qs σ v) = if ρ = σ then Qs ρ v else 0 := by
    intro ρ σ v
    have h := congrArg (fun T : Wq →L[ℂ] Wq => T v) (hQQ ρ σ)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h]
    split_ifs <;> simp
  have hEC : ∀ Y v, E (C Y v) = ∑ σ, x σ Y • E (Qs σ v) := by
    intro Y v
    have h := congrArg (fun T : Wq →L[ℂ] Wp => T v) (hid Y)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [← h]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have hEv : ∀ v, E v = ∑ σ, E (Qs σ v) := by
    intro v
    have h : (∑ σ, Qs σ) v = v := by rw [hsum, ContinuousLinearMap.one_apply]
    conv_lhs => rw [← h]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ContinuousLinearMap.sum_apply, map_sum]
  constructor
  · intro h Y v
    have hE : ∀ w, E (Qs ρ w) = E w := fun w => congrArg (fun T : Wq →L[ℂ] Wp => T w) h
    have hσ : ∀ σ, E (Qs σ v) = if ρ = σ then E v else 0 := by
      intro σ
      rw [← hE (Qs σ v), hQv]
      split_ifs
      · exact hE v
      · exact map_zero E
    rw [hEC]
    simp [hσ, Finset.sum_ite_eq]
  · intro h
    have h0 : ∀ σ, σ ≠ ρ → ∀ v, E (Qs σ v) = 0 := by
      intro σ hσ v
      obtain ⟨Y, hY⟩ := hsep ρ σ (Ne.symm hσ)
      have h1 := h Y (Qs σ v)
      rw [hEC] at h1
      have h2 : ∑ τ, x τ Y • E (Qs τ (Qs σ v)) = x σ Y • E (Qs σ v) := by
        simp only [hQv]
        rw [Finset.sum_eq_single σ]
        · simp
        · intro τ _ hτ
          simp [hτ]
        · simp
      rw [h2] at h1
      have h3 : (x σ Y - x ρ Y) • E (Qs σ v) = 0 := by rw [sub_smul, h1, sub_self]
      exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hY))
    ext v
    rw [ContinuousLinearMap.comp_apply, hEv v, Finset.sum_eq_single ρ]
    · intro σ _ hσ
      exact h0 σ hσ v
    · simp

end KLEigPf

open KLEigPf in
theorem lie_eigenvalue_holds : KLEig := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH Qρ hK ζ hζ Fr hFr ρ E hE
  obtain ⟨hpl, hk, hcs, hL, -, -, hQ⟩ := id hH
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hT : 0 < Tz P.k P.r Bs.z := by rw [hTz]; exact hOK.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := by rw [hTz']; exact hOK.T'_pos
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  set c0 : Fin P.r → ℂ := fun _ => 1 with hc0def
  have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  set φ : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := (NF.QR P.k P.r Bs.z Bs.z').indicator (fun _ => E) with hφdef
  have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨?_, ?_, ?_⟩
    · exact contDiffOn_const.congr (fun q hq' => Set.indicator_of_mem hq' _)
    · intro q hq'
      rw [hφdef, Set.indicator_of_mem hq']
      have hst := hcs.2 q.2 ζ hq'.2 hζ'
      intro p hp
      exact hE p (hst ▸ hp)
    · intro q hq'
      exact Set.indicator_of_notMem hq' _
  have hbase : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨by omega, hz, hz', hT, hT', hcs.1, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩
  obtain ⟨Φ, hΦ, hΦr⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hbase φ hφ
  set g := NF.muZ P.k P.r Bs.μsec ζ with hgdef
  have hval : Φ c0 g = E := by
    have h1 := congrFun hΦr (c0, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq, hφdef] at h1
    exact h1
  have hx : (c0, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hcs.1 hq
  set Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ⟨Φ, hΦ⟩ with hΦ'def
  let qq : MA.Qp P.r P.TT := ⟨(c0, ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have hx1 : ∀ Y : ℂ, (d.x Y).1 = X.fn 5 * X.t Y 1 1 := by
    intro Y
    have h : d.x Y = d.L.GGi * X.QQ Y 1 1 := by
      rw [hQ]
      simp only [Q.NFData.QQ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val_zero]
      rw [← mul_assoc, d.L.GGi_GG, one_mul]
    show Formalism.FourierDecayAlt.P5.Kfp.fstAlg _ (d.x Y) = _
    rw [h, hL.2.2.2.2.2.2.2.2.2.2.2.1]
    rfl
  let C : ℂ → (Wq →L[ℂ] Wq) := fun Y =>
    LinearMap.toContinuousLinearMap (qdet (Qr.EB Bs.π' Fr) (Y + ((P.k : ℂ) - 2) / 2))
  have hid : ∀ Y, E.comp (∑ σ, M.xC P σ Y • Qρ σ) = E.comp (C Y) := by
    intro Y
    ext v
    have hk1 := hK.2.2.2 (fun σ => M.xC P σ Y) Φ' qq
    have hk2 := congrArg (fun L : Wq →L[ℂ] Wp => L v) hk1
    have hact := Formalism.FourierDecayAlt.P5.Kfp.diagonal_transfer_action X hz hz' Bs.π'_rep Bs.π'_cont hx Fr hFr Y Φ' v
    have hκx : (d.κ fun σ => M.xC P σ Y) = d.x Y := rfl
    rw [hκx, hx1 Y] at hk2
    change (((X.fn 5 * X.t Y 1 1) Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 g v =
      (Φ c0 g) ((∑ σ, M.xC P σ Y • Qρ σ) v) at hk2
    rw [hact, hval] at hk2
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hk2]
    show (Φ c0 g) _ = _
    rw [hval]
    rfl
  obtain ⟨Y₀, hY₀⟩ := Formalism.FourierDecayAlt.P5.Kfp.sep_real hOK
  have hsep : ∀ ρ σ : M.Ty P, ρ ≠ σ → ∃ Y, M.xC P ρ Y ≠ M.xC P σ Y :=
    fun ρ σ h => ⟨(Y₀ : ℂ), fun he => h (hY₀ he)⟩
  classical
  exact alg Qρ (fun σ Y => M.xC P σ Y) C E hK.1 hK.2.1 hsep hid ρ

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGTrChain
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem tc_hsVec_smul (a : ℂ) (X : Wq →L[ℂ] Wp) : B.hsVec (a • X) = a • B.hsVec X := by
  simp only [B.hsVec, ContinuousLinearMap.smul_apply]
  rw [← WithLp.toLp_smul]
  rfl

theorem tc_hsVec_sum {ι : Type} (s : Finset ι) (X : ι → (Wq →L[ℂ] Wp)) :
    B.hsVec (∑ i ∈ s, X i) = ∑ i ∈ s, B.hsVec (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    simp only [B.hsVec, ContinuousLinearMap.zero_apply]
    exact WithLp.toLp_zero 2
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [B.hsVec, ContinuousLinearMap.add_apply]
    exact WithLp.toLp_add 2 _ _

theorem tc_gq (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (x : (Fin P.r → ℂ) × ℂ) :
    B.gq Bs x = Q.wCell P.k P.r (Fin.last P.r) x.1 * NF.muZ P.k P.r Bs.μsec x.2 := by
  show bigCell P.k P.r x.1 (Bs.μsec x.2) = _
  rw [(Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization P.k P.r x.1 (Bs.μsec x.2)).1, Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq]
  rfl

theorem tc_sqrt_wq (k r : ℕ) (TT : ℝ) (x : MA.E r) :
    Real.sqrt (MA.wq k x TT) =
      (∏ a : Fin r, (if a.val < (Fin.last r).val then ‖x.1 a‖ ^ (Formalism.QuantumDeterminants.Mdim k r a - 1) else 1)) *
        wR k TT x.2 := by
  unfold MA.wq wR
  rw [Real.sqrt_mul (Finset.prod_nonneg fun l _ => pow_nonneg (Complex.normSq_nonneg _) _)]
  congr 1
  have h : ∏ l : Fin r, Complex.normSq (x.1 l) ^ (MA.Mdim k r l - 1) =
      (∏ a : Fin r, (if a.val < (Fin.last r).val then ‖x.1 a‖ ^ (Formalism.QuantumDeterminants.Mdim k r a - 1) else 1)) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun a _ => ?_
    have hM : MA.Mdim k r a = Formalism.QuantumDeterminants.Mdim k r a := rfl
    rw [if_pos (by simp), Complex.normSq_eq_norm_sq, hM, ← pow_mul, ← pow_mul, mul_comm]
  rw [h, Real.sqrt_sq (Finset.prod_nonneg fun a _ => by split_ifs <;> positivity)]

theorem tc_rawJ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) :
    rawJ P Bs e J ρ = rawR P Bs.μsec e (Q.resG P.k P.r (Fin.last P.r) J) ρ := by
  funext q
  simp only [rawJ, rawR, Q.resG, tc_gq, tc_sqrt_wq]
  rw [tc_hsVec_smul, inner_smul_right]
  push_cast
  ring

theorem tc_mu (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (q : MA.Qp P.r P.TT) :
    NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) ∧
      Q.wCell P.k P.r (Fin.last P.r) q.1.1 * NF.muZ P.k P.r Bs.μsec q.1.2 ∈ OmB Bs := by
  have hTT : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl
  have hζ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2 := by
    rw [hTT]; exact q.2.2
  have hc : q.1.1 ∈ OmX P.r := q.2.1
  have hG : NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) :=
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb Bs.sec hζ)
  have hGG : 0 < Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) := by
    unfold Q.GGl
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ Bs.z_mem Bs.z'_mem Bs.sec hζ]
    linarith
  have h := Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hc hG hGG
  exact ⟨hG, h.2, fun a => h.1 ⟨(a : ℕ) + 1, by omega⟩ (by show (a : ℕ) + 1 ≤ P.r; omega)⟩

theorem tc_famR (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hJ : J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (OmB Bs)) :
    FamR P Bs (fun c => {g | Q.wCell P.k P.r (Fin.last P.r) c * g ∈ OmB Bs})
      (Q.resG P.k P.r (Fin.last P.r) J) := by
  have hD : Q.IsDom P.k P.r Bs.z Bs.z' 0 (OmB Bs) := isDom_omP Bs.z_mem Bs.z'_mem
  refine ⟨?_, ?_, fun q => (tc_mu P Bs hpl q).2, ?_⟩
  · have hw : ContDiffOn ℝ ∞ (fun c : Fin P.r → ℂ => Q.wCell P.k P.r (Fin.last P.r) c) (OmX P.r) :=
      Formalism.FourierDecayAlt.P.Qx3.wlist_smooth _
    have hm : ContDiffOn ℝ ∞ (fun x : (Fin P.r → ℂ) × Q.Mx P.k P.r => Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2)
        {x | x.1 ∈ OmX P.r} :=
      Formalism.FourierDecayAlt.P.Qx3.cdo_mul (hw.comp contDiff_fst.contDiffOn (fun _ h => h)) contDiff_snd.contDiffOn
    exact hm.continuousOn.isOpen_inter_preimage Formalism.FourierDecayAlt.P.Qx3.isOpen_OmXX hD.1
  · intro c hc
    refine ⟨hD.1.preimage (continuous_const.matrix_mul continuous_id), ?_⟩
    rintro g ⟨hgG, hgD⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hhm : h * m ∈ Q.Glev P.k P.r (Fin.last P.r) :=
      Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.uw_glev _ hh) hm.2
    have hcomm : Q.wCell P.k P.r (Fin.last P.r) c * (h * m) = (h * m) * Q.wCell P.k P.r (Fin.last P.r) c :=
      Formalism.FourierDecayAlt.P.Qx3.wlist_comm (Fin.last P.r) c _ (fun a _ => a.isLt) hhm
    have hwg : Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Q.Glev P.k P.r 0 :=
      Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _)
        (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hgG)
    have e : Q.wCell P.k P.r (Fin.last P.r) c * (h * m * g * (h' * m')) =
        h * m * (Q.wCell P.k P.r (Fin.last P.r) c * g) * (h' * m') := by
      rw [← Matrix.mul_assoc (Q.wCell P.k P.r (Fin.last P.r) c), ← Matrix.mul_assoc (Q.wCell P.k P.r (Fin.last P.r) c),
        hcomm, Matrix.mul_assoc (h * m)]
    show Q.wCell P.k P.r (Fin.last P.r) c * (h * m * g * (h' * m')) ∈ OmB Bs
    rw [e]
    exact hD.2 _ ⟨hwg, hgD⟩ _ ⟨h, hh, m, ⟨hm.1, Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hm.2⟩, rfl⟩ _
      ⟨h', hh', m', ⟨hm'.1, Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hm'.2⟩, rfl⟩
  · exact Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (OmB Bs) Bs.z_mem Bs.z'_mem hD J hJ
      (Fin.last P.r)

end

theorem gauge_transition_chain_holds : GTrChain := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl _ J hJ
  refine ⟨tc_famR P Bs hpl J hJ, fun e ρ => tc_rawJ P Bs e J ρ, fun e ρ Y => ?_⟩
  rw [tc_rawJ]
  funext q
  have hmu := tc_mu P Bs hpl q
  have hcv := Formalism.FourierDecayAlt.P.capelli_vector_valued_all_levels Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Fin.last P.r) (OmB Bs) (Y : ℂ)
    Bs.z_mem Bs.z'_mem (isDom_omP Bs.z_mem Bs.z'_mem) J hJ q.1.1 q.2.1 _ hmu.1 hmu.2
  simp only [rawR, Finset.sum_apply]
  rw [hcv]
  simp only [Finset.sum_apply, tc_hsVec_sum, inner_sum, Finset.mul_sum, Fin.val_last]

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPLeftCov
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

theorem rdV_leftCov {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z))
    {D : Set (Q.Mx k r)} {F : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hF : ∀ h ∈ UWset k r z, ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, F (h * g) = (π h).comp (F g))
    {μ : Q.Mx k r} (hμ : μ ∈ Q.Glev k r (Fin.last r) ∩ D) {X : Q.Mx k r} (hX : P.QrD.InLieW k r z X) :
    RdV (μ⁻¹ * X * μ) F μ = (P.QrD.dOp π X).comp (F μ) := by
  have hU : μᴴ * Hpk k r * μ = Hpk k r := hμ.1.1
  have hdet : IsUnit μ.det := by
    apply Matrix.isUnit_det_of_left_inverse (B := Hpk k r * μᴴ * Hpk k r)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc μᴴ, hU, Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  have hμu : IsUnit μ := (Matrix.isUnit_iff_isUnit_det μ).mpr hdet
  have key : ∀ t : ℝ, F (μ * NormedSpace.exp ((t : ℂ) • (μ⁻¹ * X * μ))) =
      (π (NormedSpace.exp ((t : ℂ) • X))).comp (F μ) := by
    intro t
    rw [show (t : ℂ) • (μ⁻¹ * X * μ) = μ⁻¹ * ((t : ℂ) • X) * μ by rw [Matrix.mul_smul, Matrix.smul_mul],
      Matrix.exp_conj' μ _ hμu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
    exact hF _ (Formalism.FourierDecayAlt.P.QrD.exp_uw hX t) μ hμ
  unfold Formalism.REAL.RdV
  simp only [key]
  let L : (Wp →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
    ((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip (F μ)).restrictScalars ℝ
  have hL : ∀ A, L A = A.comp (F μ) := fun A => rfl
  have hd : HasDerivAt (fun t : ℝ => L (π (NormedSpace.exp ((t : ℂ) • X)))) (L (P.QrD.dOp π X)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 (Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv hπ hc hX)
  simp only [hL] at hd
  exact hd.deriv

theorem left_covariance_holds : LeftCov := by
  intro k r z Wp Wq _ _ _ _ _ _ π hπ hc _ D F _ _ _ hF μ hμ B hB
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [P.LeftDerivativeCurves.hpart1_conj hμ.1.1]
    exact P.LeftDerivativeCurves.lie_conj hμ.1 hB.1.1
  · rw [P.LeftDerivativeCurves.hpart2_conj hμ.1.1]
    exact P.LeftDerivativeCurves.lie_conj hμ.1 hB.2.1
  · unfold Rc P.QrD.ecOp
    rw [P.LeftDerivativeCurves.hpart1_conj hμ.1.1, P.LeftDerivativeCurves.hpart2_conj hμ.1.1, rdV_leftCov hπ hc hF hμ hB.1,
      rdV_leftCov hπ hc hF hμ hB.2]
    ext v
    simp

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

