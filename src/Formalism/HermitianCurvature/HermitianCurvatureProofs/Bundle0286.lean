module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0283
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFHatProdKBStmt
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

section kb

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def OmKB (p : KB.Pl P Wp Wq) : Set (B.Mat P.k P.r) :=
  {g | 0 < Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g ∧
    ∀ a : Fin P.r, Formalism.QuantumDeterminants.Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0}

def FFKB (p : KB.Pl P Wp Wq) : Set (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) :=
  Q.FFl P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' 0 (OmKB p)

def IsGaugeQQKB (p : KB.Pl P Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
    CutMP.Gauge.FamR P p.T.base Dc Φ →
    ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
      MA.toSm P (CutMP.Gauge.rawR P p.T.base.μsec e
          (Q.QL P.k P.r p.T.base.z p.T.base.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
        MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b)
          (fun ρ' => MA.toSm P (CutMP.Gauge.rawR P p.T.base.μsec e Φ ρ')) ρ

end kb

def NFHatProdKBS : Prop :=
  ∃ C₁ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (L : R.LevelData (MA.A P (MA.DQ P)) P.r),
    IsFrameKB p e → IsGaugeQQKB p e → MA.IsModelLevel P (MA.DQ P) L → ∀ (N : ℕ) (u : List (MA.A P (MA.DQ P))),
      u.length ≤ N → (∀ a ∈ u, a ∈ MA.hatSet P L) →
      ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (Th : Fin m → B.DiffOp P.k P.r Wp Wq),
        (∀ k, b k ∈ Submonoid.closure (MA.bddSet P L)) ∧ (∀ k, NFOpOK C₁ p N (Th k)) ∧
        ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
          Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
          B.JF p.T.base F ∈ FFKB p →
          MA.actA P u.prod (trJKB p e (B.JF p.T.base F)) =
            ∑ k, MA.actA P (b k) (trJKB p e (B.JF p.T.base (B.opApply (Th k) F)))

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibAsm
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem nfLeib_thChain_rpow (s : ℝ) : ThChain (fun n x => s ^ n * x ^ s) := by
  intro n x hx
  have h := (Real.hasDerivAt_rpow_const (p := s) (Or.inl hx.ne')).const_mul (s ^ n)
  have e : s ^ (n + 1) * x ^ s / x = s ^ n * (s * x ^ (s - 1)) := by
    rw [Real.rpow_sub_one hx.ne', pow_succ]
    ring
  show HasDerivAt (fun y => s ^ n * y ^ s) (s ^ (n + 1) * x ^ s / x) x
  rw [e]
  exact h

theorem nfLeib_xD_contDiff (φ : ℝ → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    ∀ n : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xD^[n] φ) := by
  intro n
  induction n with
  | zero => simpa using hφ
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    unfold xD
    exact contDiff_id.mul (contDiff_infty_iff_deriv.1 ih).2

theorem nfLeib_thChain_xD (φ : ℝ → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    ThChain (fun n => xD^[n] φ) := by
  intro n x hx
  have h := nfLeib_xD_contDiff φ hφ n
  have hd := ((contDiff_infty_iff_deriv.1 h).1 x).hasDerivAt
  have hx0 : x ≠ 0 := hx.ne'
  have e : xD^[n + 1] φ x / x = deriv (xD^[n] φ) x := by
    rw [Function.iterate_succ_apply']
    show x * deriv (xD^[n] φ) x / x = _
    field_simp
  show HasDerivAt (xD^[n] φ) (xD^[n + 1] φ x / x) x
  rw [e]
  exact hd

section cont

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem nfLeib_ckOn_contOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {UU : Set (B.Mat k r)}
    (hUU : UU ⊆ B.GV k r) {f : B.Mat k r → E} (h : B.CkOn m UU f) : ContinuousOn f UU := by
  unfold B.CkOn at h
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, he⟩ := h g₀ hg₀
  have hcont : ContinuousAt f' g₀ := hc.continuousOn.continuousAt (hU.mem_nhds hgU)
  have heq : f =ᶠ[𝓝[UU] g₀] f' := by
    filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g hgU' hgUU
    exact he g hgU' (hUU hgUU)
  exact hcont.continuousWithinAt.congr_of_eventuallyEq heq (he g₀ hgU (hUU hg₀))

theorem nfLeib_domL_eq (Bs : B.RealPlaceData k r Wp Wq) : C6.domL Bs ∅ = B.GPos Bs := by
  unfold C6.domL B.GPos
  ext g
  simp

theorem nfLeib_opApply_contOn (Bs : B.RealPlaceData k r Wp Wq) (L : B.DiffOp k r Wp Wq)
    (hL : B.SmoothCoef (C6.domL Bs ∅) L) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : B.CkOn ⊤ (B.GV k r) F) :
    ContinuousOn (B.opApply L F) (B.GPos Bs) := by
  induction L with
  | nil =>
    have e : B.opApply ([] : B.DiffOp k r Wp Wq) F = fun _ => 0 := by funext g; simp [B.opApply]
    rw [e]; exact continuousOn_const
  | cons T L ih =>
    have e : B.opApply (T :: L) F = fun g => T.coef g (B.Rw T.word F g) + B.opApply L F g := by
      funext g; simp [B.opApply]
    rw [e]
    refine ContinuousOn.add ?_ (ih fun T' hT' => hL T' (List.mem_cons_of_mem _ hT'))
    have h1 : ContinuousOn T.coef (B.GPos Bs) := by
      rw [← nfLeib_domL_eq Bs]
      exact nfLeib_ckOn_contOn (fun g (hg : g ∈ C6.domL Bs ∅) => hg.1) (hL T List.mem_cons_self).1
    have h2 : ContinuousOn (B.Rw T.word F) (B.GPos Bs) :=
      (nfLeib_ckOn_contOn le_rfl (JFxI.ckOn_Rw_top' hF T.word T.word_lie)).mono fun g hg => hg.1
    exact h1.clm_apply h2

end cont

theorem nfLeib_thr (Cb c₃ R Kk W o κ A : ℝ) (hR : 0 ≤ R) (hK : 0 ≤ Kk) (hW : 0 ≤ W) (ho0 : 0 ≤ o) (hκ0 : 0 ≤ κ)
    (ho : o ≤ Cb * W * (2 * R + Kk + 1)) (hκ : κ ≤ Cb * (R + 1) * o)
    (hA : (max Cb 0 ^ 2 + 5 * max Cb 0 + max c₃ 0) * (R + 1) ^ 4 *
      (W * (2 * R + Kk + 1) ^ 2 + (2 * R + Kk + 1) ^ 3) ≤ A) :
    c₃ * (R + 1) ^ 2 * (R * (2 * R + Kk + 1) + 1) ≤ A - (κ + 3 * (R + 1) * o + (2 * R + 2) * o) := by
  have hM : Cb ≤ max Cb 0 := le_max_left _ _
  have hM0 : 0 ≤ max Cb 0 := le_max_right _ _
  have hc : c₃ ≤ max c₃ 0 := le_max_left _ _
  have hc0 : 0 ≤ max c₃ 0 := le_max_right _ _
  set M := max Cb 0 with hMd
  set c := max c₃ 0 with hcd
  set T := 2 * R + Kk + 1 with hTd
  clear_value M c T
  have hTR : R + 1 ≤ T := by rw [hTd]; linarith
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hR1 : 1 ≤ R + 1 := by linarith
  have hR0 : 0 ≤ R + 1 := by linarith
  have ho' : o ≤ M * W * T := by
    have : Cb * W * T ≤ M * W * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hW) hT0
    linarith
  have hκ' : κ ≤ M * (R + 1) * o :=
    hκ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM hR0) ho0)
  have hR2 : R + 1 ≤ (R + 1) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hR1 hR0
    linarith
  have hR4 : (R + 1) ^ 2 ≤ (R + 1) ^ 4 := by
    have h1 : 1 ≤ (R + 1) ^ 2 := by linarith
    have := mul_le_mul_of_nonneg_left h1 (sq_nonneg (R + 1))
    linarith
  have hR14 : R + 1 ≤ (R + 1) ^ 4 := hR2.trans hR4
  have hT2 : T ≤ T ^ 2 := by
    have := mul_le_mul_of_nonneg_left hT1 hT0
    linarith
  have hT3 : T ^ 2 ≤ T ^ 3 := by
    have := mul_le_mul_of_nonneg_left hT1 (sq_nonneg T)
    linarith
  have hRT : R * T + 1 ≤ T ^ 2 := by
    have := mul_le_mul_of_nonneg_right hTR hT0
    linarith
  have hRT0 : 0 ≤ R * T + 1 := by
    have := mul_nonneg hR hT0
    linarith
  have hX0 : 0 ≤ (R + 1) ^ 2 * (R * T + 1) := mul_nonneg (sq_nonneg _) hRT0
  have hXY : (R + 1) ^ 2 * (R * T + 1) ≤ (R + 1) ^ 4 * T ^ 3 :=
    mul_le_mul hR4 (hRT.trans hT3) hRT0 (by positivity)
  have h1 : c₃ * (R + 1) ^ 2 * (R * T + 1) ≤ c * ((R + 1) ^ 4 * T ^ 3) := by
    have e1 := mul_le_mul_of_nonneg_right hc hX0
    have e2 := mul_le_mul_of_nonneg_left hXY hc0
    calc c₃ * (R + 1) ^ 2 * (R * T + 1) = c₃ * ((R + 1) ^ 2 * (R * T + 1)) := by ring
      _ ≤ c * ((R + 1) ^ 4 * T ^ 3) := e1.trans e2
  have hMR : 0 ≤ (M + 5) * (R + 1) := mul_nonneg (by linarith) hR0
  have h3 := mul_le_mul_of_nonneg_left ho' hMR
  have hS : 0 ≤ M ^ 2 + 5 * M := add_nonneg (sq_nonneg M) (by linarith)
  have hZ : 0 ≤ (M ^ 2 + 5 * M) * W := mul_nonneg hS hW
  have hRT4 : (R + 1) * T ≤ (R + 1) ^ 4 * T ^ 2 := mul_le_mul hR14 hT2 hT0 (by positivity)
  have h4 := mul_le_mul_of_nonneg_left hRT4 hZ
  have h5 : 0 ≤ (M ^ 2 + 5 * M) * ((R + 1) ^ 4 * T ^ 3) :=
    mul_nonneg hS (mul_nonneg (by positivity) (pow_nonneg hT0 3))
  have h6 : 0 ≤ c * ((R + 1) ^ 4 * (W * T ^ 2)) :=
    mul_nonneg hc0 (mul_nonneg (by positivity) (mul_nonneg hW (sq_nonneg T)))
  linarith [h1, h3, h4, h5, h6, hA, hκ']

theorem nfLeibV_of (hO : NFLeibOps) (hB : NFLeibBd) (hV : NFVLin) : NFLeibV := by
  obtain ⟨c₃, hc₃⟩ := hV
  intro Cb
  refine ⟨max Cb 0 ^ 2 + 5 * max Cb 0 + max c₃ 0, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p hInD w hw e
  obtain ⟨nf, fib, o, κ, Dop, hfib, hIn, ho, hκ, hΘ⟩ := hInD w hw e
  obtain ⟨Q, L, hsm, hterm, hexp⟩ := hO P.k P.r Wp Wq p.T.base Dop hIn.1
  refine ⟨Q, L, hsm, ?_, ?_⟩
  · intro s F hF g hg
    have hG : 0 < Gf P.k P.r p.T.base.z p.T.base.z' g := hg.2.1
    have e1 : (fun g' => ((Gf P.k P.r p.T.base.z p.T.base.z' g' ^ s : ℝ) : ℂ) • F g') =
        fun y => (((fun (n : ℕ) (x : ℝ) => s ^ n * x ^ s) 0 (Gf P.k P.r p.T.base.z p.T.base.z' y) : ℝ) : ℂ) •
          F y := by
      funext y; simp
    rw [hΘ _ g hg, e1, hexp _ (nfLeib_thChain_rpow s) F hF g hg, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_smul]
    congr 1
    rw [← Complex.ofReal_mul]
    congr 1
    have hp : 0 < Gf P.k P.r p.T.base.z p.T.base.z' g ^ s := Real.rpow_pos_of_pos hG s
    rw [Real.rpow_neg hG.le]
    field_simp
  · intro φ hφ F A hF hdec hA γ hγ hGγ
    obtain ⟨b, hb⟩ := hdec o
    set m : ℝ := (κ : ℝ) + 3 * ((P.r : ℝ) + 1) * o + (2 * (P.r : ℝ) + 2) * o with hm
    have hdecq : ∀ q : Fin (Q + 1), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ g ∈ B.GV P.k P.r,
        ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g → ‖B.opApply (L q) F g‖ ≤ C * B.gN g ^ (-(A - m)) := by
      intro q ε hε
      obtain ⟨K, -, hK⟩ := hB P.k P.r Wp Wq p.T.base nf fib o κ Dop hfib hIn (L q) (hterm q) ε hε
      refine ⟨K * b, fun g hg hgε => ?_⟩
      have := hK F A b hb g hg hgε
      have ee : (κ : ℝ) + 3 * ((P.r : ℝ) + 1) * o + (2 * (P.r : ℝ) + 2) * o - A = -(A - m) := by rw [hm]; ring
      rwa [ee] at this
    have hthr : c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A - m := by
      have h0 := nfLeib_thr Cb c₃ P.r P.k w.length o κ A (by positivity) (by positivity) (by positivity)
        (by positivity) (by positivity) (by push_cast at ho; linarith) hκ (by linarith)
      push_cast
      rw [hm]
      linarith
    have hsplit : ∀ g ∈ B.GPos p.T.base, p.Θ.Θ w e
        (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g) g =
        ∑ q : Fin (Q + 1), (fun (q : Fin (Q + 1)) (x : ℝ) => ((xD^[(q : ℕ)] φ x : ℝ) : ℂ)) q
          (Gf P.k P.r p.T.base.z p.T.base.z' g) • B.opApply (L q) F g := by
      intro g hg
      have hgd : g ∈ C6.domL p.T.base ∅ := by rw [nfLeib_domL_eq]; exact hg
      rw [hΘ _ g hgd]
      exact hexp (fun n => xD^[n] φ) (nfLeib_thChain_xD φ hφ) F hF g hgd
    exact hc₃ P.k P.r Wp Wq p.T.base p.ν' p.m₀ Q (fun q x => ((xD^[(q : ℕ)] φ x : ℝ) : ℂ)) _
      (fun q => B.opApply (L q) F) (A - m) hthr
      (fun q => nfLeib_opApply_contOn p.T.base (L q) (hsm q) F hF) hdecq hsplit γ hγ hGγ

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibBd
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section bd

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem nfLeibBd_term (Bs : B.RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound Bs (fib j)) {o κ : ℕ} {Dop : B.DiffOp k r Wp Wq} (hIn : C6.InDDPlus Bs fib ∅ o κ Dop)
    (T' : B.DTerm k r Wp Wq) (hT' : LeibTerm Bs Dop T') {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (A b : ℝ), B.CCle A o F b →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r Bs.z Bs.z' g →
        ‖T'.coef g (B.Rw T'.word F g)‖ ≤
          K * b * B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o + (2 * (r : ℝ) + 2) * o - A) := by
  obtain ⟨T, hT, Pc, j, hPc, hsub, hco'⟩ := hT'
  obtain ⟨Pp, a, bb, c, es, hP, hab, hlen, hlie, hco⟩ := hIn.2.2 T hT
  set S : Set (B.Mat k r) := {g | g ∈ B.GV k r ∧ ε ≤ Gf k r Bs.z Bs.z' g} with hSdef
  set c₀ : ℝ := min ε (ε ^ 2) with hc₀
  have hc₀p : 0 < c₀ := lt_min hε (by positivity)
  have hSD : ∀ g ∈ S, ∀ l, (l ∈ (∅ : Finset (Fin (r + 2))) ∨ l = Fin.last (r + 1)) →
      c₀ ≤ Complex.normSq (Dmin k r Bs.z Bs.z' g l) := by
    intro g hg l hl
    rcases hl with hl | rfl
    · simp at hl
    · have := Formalism.FourierDecayAlt.P.gram_function_last_minor k r Bs.z Bs.z' Bs.T_pos.le Bs.T'_pos.le g ε hg.2
      exact (min_le_left _ _).trans this
  have hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ) := by
    intro g hg
    rw [Complex.normSq_ofReal]
    have h1 := hg.2
    have : ε ^ 2 ≤ Gf k r Bs.z Bs.z' g * Gf k r Bs.z Bs.z' g := by nlinarith
    exact (min_le_right _ _).trans this
  have hcU := P.AdmissibleLieWords.ubl_coefP Bs fib hfib ∅ Pp a bb c es hP hab hlie hε (fun g hg => hg) hc₀p hSD hSGf 0
  obtain ⟨⟨Cc, hCc0, hUB⟩, -⟩ := hcU
  set fo := (es.map fun e => e.2.length).sum with hfo
  obtain ⟨CP, hCP0, hCP⟩ := hPc.2 [] (fun x hx => by simp at hx)
  set D : ℕ := (2 * r + 2) * T.word.length with hD
  set cw : ℝ := (T'.word.map P.BetaSesquilinearity.nz).prod with hcw
  have hcw0 : 0 ≤ cw := List.prod_nonneg fun x hx => by
    obtain ⟨X, _, rfl⟩ := List.mem_map.1 hx; exact (P.BetaSesquilinearity.nz_pos X).le
  have hεj : 0 ≤ (ε⁻¹) ^ j := by positivity
  refine ⟨CP * ε⁻¹ ^ j * Cc * cw, by positivity, fun F A b hF g hg hgε => ?_⟩
  have hgS : g ∈ S := ⟨hg, hgε⟩
  have hgp := P.BetaSesquilinearity.gN_pos hg
  have hg1 := P.BetaSesquilinearity.gN_ge_one hg
  have hGpos : 0 < Gf k r Bs.z Bs.z' g := lt_of_lt_of_le hε hgε
  have hgd : g ∈ C6.domL Bs ∅ := ⟨hg, hGpos, fun l hl => by simp at hl⟩
  have hAdm0 : PI.UnitaryCorollaryDerivatives.CRH.admitted (k := k) (r := r) 0 [] := ⟨[], [], by simp, by simp, by simp, by simp [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR]⟩
  have hc1 : ‖T.coef g‖ ≤ Cc * B.gN g ^ (κ + 3 * (r + 1) * fo + 3 * (r + 1) * 0) := by
    have h := hUB [] hAdm0 g hgS
    have e : P.BetaSesquilinearity.Dw [] (fun g => (Pp g * C6.monoM Bs a bb c g) • C6.Epart fib es g) g =
        (Pp g * C6.monoM Bs a bb c g) • C6.Epart fib es g := rfl
    rw [e] at h
    rw [hco g hgd]
    simpa using h
  have hb0 : 0 ≤ b := by
    have h := hF.2 [] [] (by simp) (by simp) (by simp) g hg
    exact le_trans (by positivity) h
  have hc2 : ‖B.Rw T'.word F g‖ ≤ cw * (b * B.gN g ^ (-A)) := by
    rw [P.BetaSesquilinearity.Rw_scale]
    simp only
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcw0]
    apply mul_le_mul_of_nonneg_left _ hcw0
    have hunit : ∀ X ∈ T'.word.map P.BetaSesquilinearity.nrm, B.unitLie k r X := fun X hX => by
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX; exact P.BetaSesquilinearity.nrm_unit (T'.word_lie Y hY)
    have hl' : T'.word.length ≤ T.word.length := hsub.length_le
    have h := hF.2 [] (T'.word.map P.BetaSesquilinearity.nrm) (by simp) hunit (by simp; omega) g hg
    have e : B.dLR [] (T'.word.map P.BetaSesquilinearity.nrm) F g = B.Rw (T'.word.map P.BetaSesquilinearity.nrm) F g := rfl
    rw [e] at h
    have hpw : 0 < B.gN g ^ A := Real.rpow_pos_of_pos hgp _
    rw [Real.rpow_neg hgp.le, ← div_eq_mul_inv, le_div_iff₀ hpw, mul_comm]
    exact h
  have hc3 : ‖Pc g‖ ≤ CP * B.gN g ^ D := by
    have := hCP g hg
    simpa [P.B4.W_nil] using this
  have hc4 : ‖(((Gf k r Bs.z Bs.z' g : ℝ) : ℂ))⁻¹ ^ j‖ ≤ ε⁻¹ ^ j := by
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hGpos]
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hε hgε) j
  have hfo' : fo ≤ o := by omega
  have hwo : T.word.length ≤ o := by omega
  rw [hco' g hgd, ContinuousLinearMap.smul_apply, norm_smul, norm_mul]
  have hX : 0 ≤ B.gN g := hgp.le
  calc ‖Pc g‖ * ‖(((Gf k r Bs.z Bs.z' g : ℝ) : ℂ))⁻¹ ^ j‖ * ‖T.coef g (B.Rw T'.word F g)‖
      ≤ (CP * B.gN g ^ D) * ε⁻¹ ^ j * (‖T.coef g‖ * ‖B.Rw T'.word F g‖) := by
        gcongr
        exact (T.coef g).le_opNorm _
    _ ≤ (CP * B.gN g ^ D) * ε⁻¹ ^ j *
          ((Cc * B.gN g ^ (κ + 3 * (r + 1) * fo + 3 * (r + 1) * 0)) * (cw * (b * B.gN g ^ (-A)))) := by
        gcongr
    _ = CP * ε⁻¹ ^ j * Cc * cw * b *
          (B.gN g ^ (((D + (κ + 3 * (r + 1) * fo) : ℕ) : ℝ)) * B.gN g ^ (-A)) := by
        rw [Real.rpow_natCast]; ring_nf
    _ = CP * ε⁻¹ ^ j * Cc * cw * b * B.gN g ^ (((D + (κ + 3 * (r + 1) * fo) : ℕ) : ℝ) - A) := by
        rw [← Real.rpow_add hgp, sub_eq_add_neg]
    _ ≤ CP * ε⁻¹ ^ j * Cc * cw * b *
          B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o + (2 * (r : ℝ) + 2) * o - A) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le hg1
        have h3 : (3 * (r + 1) * fo : ℕ) ≤ 3 * (r + 1) * o := Nat.mul_le_mul_left _ hfo'
        have h4 : ((3 * (r + 1) * fo : ℕ) : ℝ) ≤ ((3 * (r + 1) * o : ℕ) : ℝ) := by exact_mod_cast h3
        have h5 : (D : ℝ) ≤ ((2 * r + 2) * o : ℕ) := by
          rw [hD]; exact_mod_cast Nat.mul_le_mul_left _ hwo
        push_cast at h4 h5 ⊢
        linarith

theorem leibniz_bound_holds : NFLeibBd := by
  unfold NFLeibBd
  intro k r Wp Wq _ _ _ _ _ Bs nf fib o κ Dop hfib hIn L hL ε hε
  induction L with
  | nil =>
    refine ⟨0, le_refl _, ?_⟩
    intro F A b hF g hg hεg
    simp [B.opApply]
  | cons T L ih =>
    obtain ⟨K₁, hK₁, h₁⟩ := nfLeibBd_term Bs fib hfib hIn T (hL T (by simp)) hε
    obtain ⟨K₂, hK₂, h₂⟩ := ih (fun T' hT' => hL T' (by simp [hT']))
    refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩
    intro F A b hF g hg hεg
    have e1 := h₁ F A b hF g hg hεg
    have e2 := h₂ F A b hF g hg hεg
    have hs : B.opApply (T :: L) F g = T.coef g (B.Rw T.word F g) + B.opApply L F g := by
      simp [B.opApply]
    rw [hs]
    calc _ ≤ ‖T.coef g (B.Rw T.word F g)‖ + ‖B.opApply L F g‖ := norm_add_le _ _
      _ ≤ _ := add_le_add e1 e2
      _ = _ := by ring

end bd

end Formalism.FourierDecayAlt.P.CutBP
end
end

