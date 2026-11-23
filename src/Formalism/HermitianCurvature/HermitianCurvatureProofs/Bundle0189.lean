module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0184
public import Mathlib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0181
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0182
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0096
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0185

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ClassicalToWeakSolution
section
open scoped ContDiff
open MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

section ctw

variable {d : ℕ}

theorem ctw_pdc_append (l₁ l₂ : List (Fin d)) (f : (Fin d → ℝ) → ℂ) :
    pdc (l₁ ++ l₂) f = pdc l₁ (pdc l₂ f) := by
  induction l₁ with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, pdc, ih]

theorem ctw_contDiffOn_pdc {U : Set (Fin d → ℝ)} (hU : IsOpen U) :
    ∀ (l : List (Fin d)) (m n : ℕ) (f : (Fin d → ℝ) → ℂ), ContDiffOn ℝ n f U → l.length + m ≤ n →
      ContDiffOn ℝ m (pdc l f) U
  | [], m, n, f, hf, hl => hf.of_le (by simp only [List.length_nil, zero_add] at hl; exact_mod_cast hl)
  | i :: l, m, n, f, hf, hl => by
      have ih := ctw_contDiffOn_pdc hU l (m + 1) n f hf (by simp only [List.length_cons] at hl; omega)
      simp only [pdc]
      exact (ih.fderiv_of_isOpen hU (by push_cast; exact le_rfl)).clm_apply contDiffOn_const

theorem ctw_pdc_congr {U : Set (Fin d → ℝ)} (hU : IsOpen U) :
    ∀ (l : List (Fin d)) (f g : (Fin d → ℝ) → ℂ), Set.EqOn f g U → Set.EqOn (pdc l f) (pdc l g) U
  | [], _, _, h => h
  | i :: l, f, g, h => by
      intro x hx
      have ih := ctw_pdc_congr hU l f g h
      simp only [pdc]
      rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) ih)]

theorem ctw_swap {U : Set (Fin d → ℝ)} (hU : IsOpen U) {g : (Fin d → ℝ) → ℂ} (hg : ContDiffOn ℝ 2 g U)
    {x : Fin d → ℝ} (hx : x ∈ U) (v w : Fin d → ℝ) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x w = fderiv ℝ (fun y => fderiv ℝ g y w) x v := by
  have hga : ContDiffAt ℝ 2 g x := hg.contDiffAt (hU.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hga.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hs := hga.isSymmSndFDerivAt (by simp)
  rw [fderiv_clm_apply hd (differentiableAt_const v), fderiv_clm_apply hd (differentiableAt_const w)]
  simp [hs w v]

theorem ctw_pdc_perm {U : Set (Fin d → ℝ)} (hU : IsOpen U) {l₁ l₂ : List (Fin d)} (hp : l₁.Perm l₂) :
    ∀ (n : ℕ) (f : (Fin d → ℝ) → ℂ), ContDiffOn ℝ n f U → l₁.length ≤ n →
      Set.EqOn (pdc l₁ f) (pdc l₂ f) U := by
  induction hp with
  | nil => intro n f _ _; exact Set.eqOn_refl _ _
  | @cons a m₁ m₂ hp ih =>
      intro n f hf hl
      have h := ih n f hf (by simp only [List.length_cons] at hl; omega)
      have e1 := ctw_pdc_append [a] m₁ f
      have e2 := ctw_pdc_append [a] m₂ f
      simp only [List.singleton_append] at e1 e2
      rw [e1, e2]
      exact ctw_pdc_congr hU [a] _ _ h
  | swap a b l =>
      intro n f hf hl x hx
      have hg : ContDiffOn ℝ 2 (pdc l f) U :=
        ctw_contDiffOn_pdc hU l 2 n f hf (by simp only [List.length_cons] at hl; omega)
      simp only [pdc]
      exact ctw_swap hU hg hx _ _
  | trans h₁ _ ih₁ ih₂ =>
      intro n f hf hl
      exact (ih₁ n f hf hl).trans (ih₂ n f hf (h₁.length_eq ▸ hl))

theorem ctw_integrable {U : Set (Fin d → ℝ)} (hU : IsOpen U) {F G : (Fin d → ℝ) → ℂ}
    (hF : ContinuousOn F U) (hG : Continuous G) (hGc : HasCompactSupport G) (hGU : tsupport G ⊆ U) :
    Integrable (fun x => F x * G x) := by
  have hc : Continuous (fun x => F x * G x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hF.continuousAt (hU.mem_nhds hx)).mul hG.continuousAt
    · have h0 : G =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 (fun h => hx (hGU h))
      have h1 : (fun x => F x * G x) =ᶠ[nhds x] fun _ => 0 := h0.mono fun y hy => by simp [hy]
      exact continuousAt_const.congr h1.symm
  have hcs : HasCompactSupport (F * G) := hGc.mul_left
  exact hc.integrable_of_hasCompactSupport hcs

theorem ctw_tsupport_pdc (l : List (Fin d)) (ψ : (Fin d → ℝ) → ℂ) : tsupport (pdc l ψ) ⊆ tsupport ψ := by
  induction l with
  | nil => exact subset_rfl
  | cons i l ih =>
      refine subset_trans ?_ ((tsupport_fderiv_subset ℝ).trans ih)
      refine closure_mono ?_
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h
      apply hx
      simp only [pdc, h, zero_apply]

theorem ctw_contDiff_pdc (l : List (Fin d)) {ψ : (Fin d → ℝ) → ℂ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (pdc l ψ) := by
  induction l with
  | nil => exact hψ
  | cons i l ih =>
      simp only [pdc]
      exact contDiff_infty.2 fun n =>
        ((contDiff_infty.1 ih (n + 1)).fderiv_right (by push_cast; exact le_rfl)).clm_apply contDiff_const

theorem ctw_ibp {U : Set (Fin d → ℝ)} (hU : IsOpen U) (l : List (Fin d)) :
    ∀ (n : ℕ) (f ψ : (Fin d → ℝ) → ℂ), ContDiffOn ℝ n f U → l.length ≤ n → ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, f x * pdc l ψ x = (-1 : ℂ) ^ l.length * ∫ x, pdc l.reverse f x * ψ x := by
  induction l with
  | nil => intro n f ψ _ _ _ _ _; simp [pdc]
  | cons i l ih =>
      intro n f ψ hf hl hψ hψc hψU
      have hl' : l.length + 1 ≤ n := by simpa using hl
      have hgs : ContDiff ℝ ∞ (pdc l ψ) := ctw_contDiff_pdc l hψ
      have hgt : tsupport (pdc l ψ) ⊆ tsupport ψ := ctw_tsupport_pdc l ψ
      have hgc : HasCompactSupport (pdc l ψ) := hψc.mono' ((subset_tsupport _).trans hgt)
      have hg's : ContDiff ℝ ∞ (pdc (i :: l) ψ) := ctw_contDiff_pdc (i :: l) hψ
      have hg't : tsupport (pdc (i :: l) ψ) ⊆ tsupport ψ := ctw_tsupport_pdc (i :: l) ψ
      have hg'c : HasCompactSupport (pdc (i :: l) ψ) := hψc.mono' ((subset_tsupport _).trans hg't)
      have hf1 : ContDiffOn ℝ ((n - 1 : ℕ)) (pdc [i] f) U :=
        ctw_contDiffOn_pdc hU [i] (n - 1) n f hf (by simp only [List.length_cons, List.length_nil]; omega)
      have hf0 : ContinuousOn (pdc [i] f) U :=
        (ctw_contDiffOn_pdc hU [i] 0 n f hf (by simp only [List.length_cons, List.length_nil]; omega)).continuousOn
      have hstep : ∫ x, f x * pdc (i :: l) ψ x = -∫ x, pdc [i] f x * pdc l ψ x := by
        have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
          (f := f) (g := pdc l ψ) (v := (Pi.single i 1 : Fin d → ℝ))
          (ctw_integrable hU hf0 hgs.continuous hgc (hgt.trans hψU))
          (ctw_integrable hU hf.continuousOn hg's.continuous hg'c (hg't.trans hψU))
          (ctw_integrable hU hf.continuousOn hgs.continuous hgc (hgt.trans hψU))
          (fun x hx => (hf.contDiffAt (hU.mem_nhds (hψU (hgt hx)))).differentiableAt
            (by exact_mod_cast (show n ≠ 0 by omega)))
          (fun x _ => hgs.differentiable (by simp) x)
        exact h
      rw [hstep, ih (n - 1) (pdc [i] f) ψ hf1 (by omega) hψ hψc hψU, List.reverse_cons, ctw_pdc_append,
        List.length_cons, pow_succ]
      ring

theorem ctw_smooth_mul {U : Set (Fin d → ℝ)} (hU : IsOpen U) {a φ : (Fin d → ℝ) → ℂ}
    (ha : ContDiffOn ℝ ∞ a U) (hφ : ContDiff ℝ ∞ φ) (hφU : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun y => a y * φ y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (ha.contDiffAt (hU.mem_nhds hx)).mul hφ.contDiffAt
  · have h0 : φ =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 (fun h => hx (hφU h))
    have h1 : (fun y => a y * φ y) =ᶠ[nhds x] fun _ => 0 := h0.mono fun y hy => by simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h1

end ctw

theorem classical_to_weak_solution : ClassToWeak := by
  intro d N P U u hU ha hord hu hPu φ hφ hφc hφU
  have hφ0 : ∀ x, x ∉ U → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hφU h))
  have hψ : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d),
      ContDiff ℝ ∞ (fun y => P.a k w y * φ y) ∧ HasCompactSupport (fun y => P.a k w y * φ y) ∧
        tsupport (fun y => P.a k w y * φ y) ⊆ U := fun k w =>
    ⟨ctw_smooth_mul hU (ha k w) hφ hφU, hφc.mul_left, tsupport_mul_subset_right.trans hφU⟩
  have hk : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d), (List.ofFn w).length ≤ N := fun k w => by
    rw [List.length_ofFn]; have := k.isLt; omega
  have hint : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d),
      Integrable (fun x => u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x)) :=
    fun k w => by
      obtain ⟨h1, h2, h3⟩ := hψ k w
      refine ctw_integrable hU hu.continuousOn (continuous_const.mul (ctw_contDiff_pdc _ h1).continuous)
        ((h2.mono' ((subset_tsupport _).trans (ctw_tsupport_pdc _ _))).mul_left)
        (tsupport_mul_subset_right.trans ((ctw_tsupport_pdc _ _).trans h3))
  have hint2 : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d),
      Integrable (fun x => P.a k w x * pdc (List.ofFn w) u x * φ x) := fun k w =>
    ctw_integrable hU (((ha k w).continuousOn).mul
      (ctw_contDiffOn_pdc hU (List.ofFn w) 0 N u hu (by simpa using hk k w)).continuousOn) hφ.continuous hφc hφU
  have hterm : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d),
      ∫ x, u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x) =
        ∫ x, P.a k w x * pdc (List.ofFn w) u x * φ x := by
    intro k w
    obtain ⟨h1, h2, h3⟩ := hψ k w
    have hI := ctw_ibp hU (List.ofFn w) N u _ hu (hk k w) h1 h2 h3
    have hperm := ctw_pdc_perm hU (List.reverse_perm (List.ofFn w)) N u hu
      (by rw [List.length_reverse]; exact hk k w)
    calc ∫ x, u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x)
        = (-1 : ℂ) ^ (k : ℕ) * ∫ x, u x * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x := by
          rw [← integral_const_mul]; congr 1; funext x; ring
      _ = ∫ x, pdc (List.ofFn w).reverse u x * (P.a k w x * φ x) := by
          rw [hI, List.length_ofFn, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]
      _ = ∫ x, P.a k w x * pdc (List.ofFn w) u x * φ x := by
          congr 1; funext x
          by_cases hx : x ∈ U
          · rw [hperm hx]; ring
          · simp [hφ0 x hx]
  have hsplit : (fun x => u x * P.tr φ x) = fun x => ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d,
      u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x) := by
    funext x; simp only [SOp.tr, Finset.mul_sum]
  have hinner : ∀ k : Fin (P.ord + 1),
      ∫ x, ∑ w : Fin k → Fin d, u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x) =
        ∫ x, ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x * φ x := fun k => by
    rw [integral_finsetSum _ (fun w _ => hint k w), integral_finsetSum _ (fun w _ => hint2 k w)]
    exact Finset.sum_congr rfl (fun w _ => hterm k w)
  rw [hsplit, integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun w _ => hint k w)),
    Finset.sum_congr rfl (fun k _ => hinner k),
    ← integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun w _ => hint2 k w))]
  have h0 : (fun x => ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x * φ x) =
      fun _ => (0 : ℂ) := by
    funext x
    have e : ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x * φ x =
        P.app u x * φ x := by simp only [SOp.app, Finset.sum_mul]
    rw [e]
    by_cases hx : x ∈ U
    · rw [hPu x hx, zero_mul]
    · rw [hφ0 x hx, mul_zero]
  rw [h0, integral_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjAsm
section
namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section clm

variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E']

theorem contDiff_clm_comp (Λ : E →L[ℂ] E') {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (fun g => Λ (ψ g)) :=
  (Λ.restrictScalars ℝ).contDiff.comp hψ

theorem rdV_clm (Λ : E →L[ℂ] E') {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) (X : B.Mat k r) :
    RdV X (fun g => Λ (ψ g)) = fun g => Λ (RdV X ψ g) := by
  rw [rdV_global (contDiff_clm_comp Λ hψ) X, rdV_global hψ X]
  funext g
  have hd : HasFDerivAt ψ (fderiv ℝ ψ g) g := ((hψ.differentiable (by simp)) g).hasFDerivAt
  have h := (Λ.restrictScalars ℝ).hasFDerivAt.comp g hd
  exact (DFunLike.congr_fun h.fderiv (g * X)).trans rfl

theorem rw_clm' (Λ : E →L[ℂ] E') {ψ : B.Mat k r → E} (hψ : ContDiff ℝ ∞ ψ) :
    ∀ w : List (B.Mat k r), B.Rw w (fun g => Λ (ψ g)) = fun g => Λ (B.Rw w ψ g)
  | [] => rfl
  | X :: w => by
    show RdV X (B.Rw w (fun g => Λ (ψ g))) = fun g => Λ (RdV X (B.Rw w ψ) g)
    rw [rw_clm' Λ hψ w, rdV_clm Λ (rw_contDiff hψ w) X]

end clm

section comps

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def lam (i : Fin (Module.finrank ℂ Wq)) (j : Fin (Module.finrank ℂ Wp)) : (Wq →L[ℂ] Wp) →L[ℂ] ℂ :=
  (innerSL ℂ (stdOrthonormalBasis ℂ Wp j)).comp (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i))

theorem lam_apply (i j) (A : Wq →L[ℂ] Wp) :
    lam i j A = inner ℂ (stdOrthonormalBasis ℂ Wp j) (A (stdOrthonormalBasis ℂ Wq i)) := rfl

theorem hsInner_eq_sum (A C : Wq →L[ℂ] Wp) :
    B.hsInner A C = ∑ i, ∑ j, lam i j A * star (lam i j C) := by
  unfold B.hsInner B.hsVec
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.toLp_apply]
  rw [← (stdOrthonormalBasis ℂ Wp).sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lam_apply, lam_apply, mul_comm]
  congr 1
  rw [← inner_conj_symm]
  rfl

end comps

section terms

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem lam_opAdj_tail (i j) (s : ℂ) {ψ : B.Mat k r → (Wq →L[ℂ] Wp)} (hψ : ContDiff ℝ ∞ ψ) :
    ∀ (L : List (ℂ × List (B.Mat k r))), (∀ cw ∈ L, ∀ X ∈ cw.2, B.inLie k r X) → ∀ g,
    lam i j (((L.map fun cw => TLB.cTerm (Wp := Wp) (Wq := Wq) (s * cw.1) cw.2).map
        (fun T => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (ψ x)) g)).sum) =
      conj s * (L.map fun cw => conj cw.1 * (-1 : ℂ) ^ cw.2.length *
        B.Rw cw.2.reverse (fun x => lam i j (ψ x)) g).sum
  | [], _, g => by simp
  | cw :: L, hL, g => by
    simp only [List.map_cons, List.sum_cons, map_add (f := _), mul_add]
    rw [lam_opAdj_tail i j s hψ L (fun cw' h => hL cw' (List.mem_cons_of_mem _ h)) g]
    congr 1
    rw [TLB.cTerm_word (hL cw List.mem_cons_self)]
    have e : (fun x => (TLB.cTerm (Wp := Wp) (Wq := Wq) (s * cw.1) cw.2).coefAdj x (ψ x)) =
        conj (s * cw.1) • ψ := by
      funext x; simp [TLB.cTerm]
    rw [e, Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rw_smul, map_smul, Pi.smul_apply, map_smul]
    have e2 := congrFun (rw_clm' (lam i j) hψ cw.2.reverse) g
    rw [← e2, smul_eq_mul, smul_eq_mul, map_mul]
    ring

theorem lam_wordSum (i j) {ψ : B.Mat k r → (Wq →L[ℂ] Wp)} (hψ : ContDiff ℝ ∞ ψ) :
    ∀ (L : List (ℂ × List (B.Mat k r))) (g : B.Mat k r),
    lam i j ((L.map fun cw => cw.1 • B.Rw cw.2 ψ g).sum) =
      (L.map fun cw => cw.1 • B.Rw cw.2 (fun x => lam i j (ψ x)) g).sum
  | [], _ => by simp
  | cw :: L, g => by
    simp only [List.map_cons, List.sum_cons, map_add (f := _), map_smul]
    rw [lam_wordSum i j hψ L g, congrFun (rw_clm' (lam i j) hψ cw.2) g]

theorem wsAdj_contDiff (L : List (ℂ × List (B.Mat k r))) {b : B.Mat k r → ℂ} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (wsAdj L b) := by
  unfold wsAdj
  exact contDiff_listSum (fun (cw : ℂ × List (B.Mat k r)) x => conj cw.1 * (-1 : ℂ) ^ cw.2.length * B.Rw cw.2.reverse b x) L
    fun cw _ => contDiff_const.mul (rw_contDiff hb _)

end terms

theorem capacity_adjoint_integral_scalar : CapAdjIntOfScalar := by
  intro hS k r Wp Wq _ _ _ _ _ _ s Y μ hμ φ ψ hφ hφc hψ hψc
  haveI : IsFiniteMeasureOnCompacts μ := ⟨hμ.finite_compact⟩
  have hLw := (Classical.choose_spec (Formalism.FourierDecayAlt.P.capelli_word_sum k r Y)).1
  obtain ⟨L', hL', hCV'⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum k r (conj Y)
  set a : Fin (Module.finrank ℂ Wq) → Fin (Module.finrank ℂ Wp) → B.Mat k r → ℂ :=
    fun i j g => lam i j (φ g) with ha
  set b : Fin (Module.finrank ℂ Wq) → Fin (Module.finrank ℂ Wp) → B.Mat k r → ℂ :=
    fun i j g => lam i j (ψ g) with hb
  have ha_s : ∀ i j, ContDiff ℝ ∞ (a i j) := fun i j => contDiff_clm_comp (lam i j) hφ
  have hb_s : ∀ i j, ContDiff ℝ ∞ (b i j) := fun i j => contDiff_clm_comp (lam i j) hψ
  have ha_c : ∀ i j, HasCompactSupport (a i j) := fun i j => hφc.comp_left (map_zero (lam i j))
  have hb_c : ∀ i j, HasCompactSupport (b i j) := fun i j => hψc.comp_left (map_zero (lam i j))

  have hAdj : ∀ i j g, lam i j (B.opAdj (capTh k r Wp Wq s Y) ψ g) = conj s * wsAdj (capLw k r Y) (b i j) g := by
    intro i j g
    unfold B.opAdj
    rw [capTh, TLB.capOp, List.map_cons, List.sum_cons, map_add (f := _)]
    have h0 : (fun x => (TLB.cTerm (Wp := Wp) (Wq := Wq) 0
        (List.replicate (2 * r + k + 1) (0 : B.Mat k r))).coefAdj x (ψ x)) = (0 : ℂ) • ψ := by
      funext x; simp [TLB.cTerm]
    rw [h0, Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rw_smul, zero_smul]
    rw [lam_opAdj_tail i j s hψ (capLw k r Y) (fun cw h X hX => ((hLw cw h).1 X hX).1) g]
    simp [wsAdj, b]

  have hCVc : ∀ i j, ∀ g ∈ B.GV k r, lam i j (Q.CV k r (conj Y) ψ g) = Q.CV k r (conj Y) (b i j) g := by
    intro i j g hg
    rw [hCV' _ (B.GV k r) ψ (ckOn_of_contDiff hψ _ _) g hg hg,
      hCV' _ (B.GV k r) (b i j) (ckOn_of_contDiff (hb_s i j) _ _) g hg hg]
    exact lam_wordSum i j hψ L' g

  have hP1 : ∀ x : Mt k r, B.hsInner (φ (Matrix.of x)) (B.opAdj (capTh k r Wp Wq s Y) ψ (Matrix.of x)) =
      ∑ i, ∑ j, s * (a i j (Matrix.of x) * star (wsAdj (capLw k r Y) (b i j) (Matrix.of x))) := by
    intro x
    rw [hsInner_eq_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hAdj, star_mul', Complex.star_def, Complex.conj_conj]
    simp only [ha]; ring
  have hP2 : ∀ᵐ x ∂μ, B.hsInner (φ (Matrix.of x)) (conj s • Q.CV k r (conj Y) ψ (Matrix.of x)) =
      ∑ i, ∑ j, s * (a i j (Matrix.of x) * star (Q.CV k r (conj Y) (b i j) (Matrix.of x))) := by
    filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hx
    rw [hsInner_eq_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hCVc i j _ hx, smul_eq_mul, star_mul', Complex.star_def, Complex.conj_conj]
    simp only [ha]; ring

  have hI1 : ∀ i j, Integrable (fun x : Mt k r => s * (a i j (Matrix.of x) *
      star (wsAdj (capLw k r Y) (b i j) (Matrix.of x)))) μ := by
    intro i j
    have hc : Continuous (fun x : Mt k r => a i j (Matrix.of x) * star (wsAdj (capLw k r Y) (b i j) (Matrix.of x))) :=
      (ha_s i j).continuous.mul (continuous_star.comp (wsAdj_contDiff _ (hb_s i j)).continuous)
    have hcs : HasCompactSupport
        (fun x : Mt k r => a i j (Matrix.of x) * star (wsAdj (capLw k r Y) (b i j) (Matrix.of x))) :=
      (ha_c i j).mul_right
    exact (hc.integrable_of_hasCompactSupport (μ := μ) hcs).const_mul s
  have hI2 : ∀ i j, Integrable (fun x : Mt k r => s * (a i j (Matrix.of x) *
      star (Q.CV k r (conj Y) (b i j) (Matrix.of x)))) μ := by
    intro i j
    have hS' : ContDiff ℝ ∞ (fun g => (L'.map fun cw => cw.1 • B.Rw cw.2 (b i j) g).sum) :=
      contDiff_listSum (fun cw g => cw.1 • B.Rw cw.2 (b i j) g) L' fun cw _ =>
        (rw_contDiff (hb_s i j) _).const_smul _
    have hc : Continuous (fun x : Mt k r => a i j (Matrix.of x) *
        star ((L'.map fun cw => cw.1 • B.Rw cw.2 (b i j) (Matrix.of x)).sum)) :=
      (ha_s i j).continuous.mul (continuous_star.comp hS'.continuous)
    have hcs : HasCompactSupport (fun x : Mt k r => a i j (Matrix.of x) *
        star ((L'.map fun cw => cw.1 • B.Rw cw.2 (b i j) (Matrix.of x)).sum)) :=
      (ha_c i j).mul_right
    refine ((hc.integrable_of_hasCompactSupport (μ := μ) hcs).const_mul s).congr ?_
    filter_upwards [Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.ae_mem hμ] with x hx
    rw [hCV' _ (B.GV k r) (b i j) (ckOn_of_contDiff (hb_s i j) _ _) _ hx hx]
  rw [integral_congr_ae (Eventually.of_forall hP1), integral_congr_ae hP2,
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hI1 i j),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hI2 i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hI1 i j), integral_finsetSum _ (fun j _ => hI2 i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_const_mul,
    hS k r Y μ hμ (a i j) (b i j) (ha_s i j) (ha_c i j) (hb_s i j) (hb_c i j)]

theorem capAdjInt_of_scalar (hS : CapAdjScalar) : CapAdjInt := capacity_adjoint_integral_scalar hS

end

end Formalism.FourierDecayAlt.P.CutMP.ER
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocAdd
section
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem locAdd_thr (k r : ℕ) {A : ℝ} (hA : 10 * ((r : ℝ) + 1) * nDim k r ^ 2 ≤ A) : JF.TransportedAlt k r A 0 := by
  unfold JF.TransportedAlt
  have hn : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hA' : 10 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ A := by simpa [nDim] using hA
  have hn2 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  rw [lt_div_iff₀ (by positivity)]
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  nlinarith [mul_pos hr (lt_of_lt_of_le one_pos hn2)]

theorem local_additivity_transfer : JALocAdd := by
  refine ⟨10, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Bg A J J' hBg hA hJ hJ'
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hThr := locAdd_thr S.G.k S.G.r hA
  refine ⟨Formalism.FourierDecayAlt.P.Qx8.FFl_add hJ.1 hJ'.1, fun δ hδ => ?_⟩
  obtain ⟨F, hF1, hF2, hF3⟩ := hJ.2 δ hδ
  obtain ⟨F', hF1', hF2', hF3'⟩ := hJ'.2 δ hδ
  refine ⟨F + F', Formalism.FourierDecayAlt.P.JCx2.ckOn_add' hF1 hF1', fun m => ?_, fun x hx hG => ?_⟩
  · obtain ⟨c, hc⟩ := hF2 m
    obtain ⟨c', hc'⟩ := hF2' m
    exact ⟨c + c', Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc hc'⟩
  · have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, hTT ▸ hx.2⟩
    have hg := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
    have h0 : B.InCC A 0 F := by simpa using hF2 0
    have h0' : B.InCC A 0 F' := by simpa using hF2' 0
    have i1 := (Formalism.FourierDecayAlt.P.bessel_integral_converges S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A F hThr h0).1 _ hg
    have i2 := (Formalism.FourierDecayAlt.P.bessel_integral_converges S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A F' hThr h0').1 _ hg
    have e : ∀ G : GFn S v, B.JF (T v).base G (B.gq (T v).base x) =
        ∫ p, JF.integrand (T v).base G (B.gq (T v).base x) p ∂(T v).base.μSS := fun G => rfl
    rw [Pi.add_apply, hF3 x hx hG, hF3' x hx hG, e, e, e, ← integral_add i1 i2]
    congr 1
    funext p
    simp [JF.integrand, B.rho, smul_add]

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceInductionLevel
section
namespace Formalism.FourierDecayAlt.P

theorem slice_induction_level : Formalism.FourierDecayAlt.KB.SliceStep :=
  Formalism.FourierDecayAlt.P.PBH.sliceStep_of Formalism.FourierDecayAlt.P.PBH.jfStep (Formalism.FourierDecayAlt.P.PBH.asm_pointStepT Formalism.FourierDecayAlt.P.PBH.pointStep)

end Formalism.FourierDecayAlt.P
end

