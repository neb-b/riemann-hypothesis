module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle0001
public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBLink
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def hermL (n : ℕ) : (Fin n → Fin n → ℝ) →L[ℝ] Mc n :=
  LinearMap.toContinuousLinearMap
    { toFun := herm
      map_add' := fun x y => by
        ext i j; simp only [herm, Pi.add_apply, Matrix.add_apply]; push_cast; ring
      map_smul' := fun c x => by
        ext i j; simp only [herm, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, RingHom.id_apply]
        rw [Complex.real_smul]; push_cast; ring }

theorem hermL_apply (x : Fin n → Fin n → ℝ) : hermL n x = herm x := rfl

theorem vkl_re (k l a b : Fin n) :
    (vkl k l a b).re = (if a = k ∧ b = l then 1 / 2 else 0) + (if a = l ∧ b = k then 1 / 2 else 0) := by
  unfold vkl; split_ifs <;> simp

theorem vkl_im (k l a b : Fin n) :
    (vkl k l a b).im = (if a = k ∧ b = l then 1 / 2 else 0) + (if a = l ∧ b = k then -1 / 2 else 0) := by
  unfold vkl; split_ifs <;> simp

theorem herm_re_im_vkl (k l : Fin n) :
    herm (fun a b => (vkl k l a b).re) + Complex.I • herm (fun a b => (vkl k l a b).im) =
      Matrix.single l k (1 : ℂ) := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
  unfold herm
  dsimp only
  rw [vkl_re, vkl_re, vkl_im, vkl_im]
  have e1 : (if j = k ∧ i = l then (1 / 2 : ℝ) else 0) = 1 / 2 * (if i = l ∧ j = k then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e2 : (if j = l ∧ i = k then (1 / 2 : ℝ) else 0) = 1 / 2 * (if i = k ∧ j = l then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e3 : (if i = k ∧ j = l then (1 / 2 : ℝ) else 0) = 1 / 2 * (if i = k ∧ j = l then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e4 : (if i = l ∧ j = k then (1 / 2 : ℝ) else 0) = 1 / 2 * (if i = l ∧ j = k then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e5 : (if i = l ∧ j = k then (-1 / 2 : ℝ) else 0) = -1 / 2 * (if i = l ∧ j = k then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e6 : (if j = l ∧ i = k then (-1 / 2 : ℝ) else 0) = -1 / 2 * (if i = k ∧ j = l then 1 else 0) := by
    split_ifs <;> first | (exfalso; tauto) | norm_num
  have e7 : (if l = i ∧ k = j then (1 : ℂ) else 0) = (((if i = l ∧ j = k then (1 : ℝ) else 0) : ℝ) : ℂ) := by
    by_cases h : i = l ∧ j = k
    · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]; simp
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]; simp
  rw [e1, e2, e3, e4, e5, e6, e7]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

variable {F G : Mc n → ℂ} {U : Set (Mc n)}

theorem dkl_comp_herm (k l : Fin n) (y : Fin n → Fin n → ℝ) (hd : DifferentiableAt ℂ G (herm y)) :
    Dkl k l (fun y => G (herm y)) y = cpart l k G (herm y) := by
  have hG : HasFDerivAt G ((fderiv ℂ G (herm y)).restrictScalars ℝ) (herm y) :=
    hd.hasFDerivAt.restrictScalars ℝ
  have hc : HasFDerivAt (fun y => G (herm y)) (((fderiv ℂ G (herm y)).restrictScalars ℝ).comp (hermL n)) y :=
    hG.comp y (hermL n).hasFDerivAt
  unfold Dkl dirC cpart
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', hermL_apply]
  rw [← herm_re_im_vkl k l, map_add (f := _), map_smul, smul_eq_mul]

theorem cpart_contDiffOn (i j : Fin n) (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ContDiffOn ℂ (⊤ : ℕ∞) (cpart i j F) U := by
  have h := hF.fderiv_of_isOpen hU (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by norm_cast)
  exact h.clm_apply contDiffOn_const

theorem differentiableAt_of_cdo (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) {b : Mc n} (hb : b ∈ U) :
    DifferentiableAt ℂ F b :=
  ((hF.contDiffAt (hU.mem_nhds hb)).differentiableAt (by norm_cast))

theorem foldr_herm (τ : Fin n → Fin n) (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (hh : ∀ y, herm y ∈ U)
    (L : List (Fin n)) :
    L.foldr (fun k g => Dkl k (τ k) g) (fun y => F (herm y)) =
        (fun y => (L.foldr (fun k g => cpart (τ k) k g) F) (herm y)) ∧
      ContDiffOn ℂ (⊤ : ℕ∞) (L.foldr (fun k g => cpart (τ k) k g) F) U := by
  induction L with
  | nil => exact ⟨rfl, hF⟩
  | cons a L ih =>
    refine ⟨?_, cpart_contDiffOn _ _ hU ih.2⟩
    simp only [List.foldr_cons]
    rw [ih.1]
    funext y
    exact dkl_comp_herm a (τ a) y (differentiableAt_of_cdo hU ih.2 (hh y))

theorem deltaC_contDiffOn (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ContDiffOn ℂ (⊤ : ℕ∞) (DeltaC F) U := by
  have : DeltaC F = fun b => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (List.finRange n).foldr (fun k g => cpart (σ k) k g) F b := by
    funext b; simp [DeltaC, Finset.sum_apply]
  rw [this]
  refine ContDiffOn.sum fun σ _ => ContDiffOn.const_smul _ ?_
  have key : ∀ L : List (Fin n), ContDiffOn ℂ (⊤ : ℕ∞) (L.foldr (fun k g => cpart (σ k) k g) F) U := by
    intro L; induction L with
    | nil => exact hF
    | cons a L ih => exact cpart_contDiffOn _ _ hU ih
  exact key _

theorem delta_herm (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (hh : ∀ y, herm y ∈ U) :
    Delta (fun y => F (herm y)) = fun y => DeltaC F (herm y) := by
  funext y
  simp only [Delta, DeltaC, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [(foldr_herm σ hU hF hh _).1]

theorem iterate_herm (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (hh : ∀ y, herm y ∈ U) (N : ℕ) :
    (Delta^[N] (fun y => F (herm y))) = (fun y => (DeltaC^[N] F) (herm y)) ∧
      ContDiffOn ℂ (⊤ : ℕ∞) (DeltaC^[N] F) U := by
  induction N with
  | zero => exact ⟨rfl, hF⟩
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.1]
    exact ⟨delta_herm hU ih.2 hh, deltaC_contDiffOn hU ih.2⟩

theorem eqOn_cpart (i j : Fin n) (hU : IsOpen U) {H H' : Mc n → ℂ} (h : Set.EqOn H H' U) :
    Set.EqOn (cpart i j H) (cpart i j H') U := fun b hb => by
  have : H =ᶠ[nhds b] H' := Filter.eventuallyEq_of_mem (hU.mem_nhds hb) h
  simp only [cpart, this.fderiv_eq]

theorem eqOn_word (L : List (Fin n × Fin n)) (hU : IsOpen U) {H H' : Mc n → ℂ} (h : Set.EqOn H H' U) :
    Set.EqOn (word L H) (word L H') U := by
  induction L with
  | nil => exact h
  | cons a L ih => exact eqOn_cpart a.1 a.2 hU ih

theorem word_contDiffOn (L : List (Fin n × Fin n)) (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ContDiffOn ℂ (⊤ : ℕ∞) (word L F) U := by
  induction L with
  | nil => exact hF
  | cons a L ih => exact cpart_contDiffOn _ _ hU ih

theorem cpart_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → Mc n → ℂ) (i j : Fin n) (hU : IsOpen U)
    (hf : ∀ t, ContDiffOn ℂ (⊤ : ℕ∞) (f t) U) :
    Set.EqOn (cpart i j (fun x => ∑ t ∈ s, c t * f t x)) (fun x => ∑ t ∈ s, c t * cpart i j (f t) x) U := by
  intro b hb
  have hd : ∀ t ∈ s, DifferentiableAt ℂ (fun x => c t * f t x) b := fun t _ =>
    (differentiableAt_of_cdo hU (hf t) hb).const_mul (c t)
  simp only [cpart]
  have hs : HasFDerivAt (fun x => ∑ t ∈ s, c t * f t x) (∑ t ∈ s, fderiv ℂ (fun x => c t * f t x) b) b :=
    HasFDerivAt.fun_sum (fun t ht => (hd t ht).hasFDerivAt)
  rw [hs.fderiv, _root_.sum_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : HasFDerivAt (fun x => c t * f t x) (c t • fderiv ℂ (f t) b) b :=
    (differentiableAt_of_cdo hU (hf t) hb).hasFDerivAt.const_mul (c t)
  rw [h1.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem word_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → Mc n → ℂ) (L : List (Fin n × Fin n))
    (hU : IsOpen U) (hf : ∀ t, ContDiffOn ℂ (⊤ : ℕ∞) (f t) U) :
    Set.EqOn (word L (fun x => ∑ t ∈ s, c t * f t x)) (fun x => ∑ t ∈ s, c t * word L (f t) x) U := by
  induction L with
  | nil => intro b _; rfl
  | cons a L ih =>
    intro b hb
    have h1 := eqOn_cpart a.1 a.2 hU ih hb
    simp only [word, List.foldr_cons] at h1 ⊢
    rw [h1]
    exact cpart_sum s c (fun t => word L (f t)) a.1 a.2 hU (fun t => word_contDiffOn L hU (hf t)) hb

theorem word_append (L₁ L₂ : List (Fin n × Fin n)) (H : Mc n → ℂ) :
    word (L₁ ++ L₂) H = word L₁ (word L₂ H) := by
  simp [word, List.foldr_append]

def blk (σ : Equiv.Perm (Fin n)) : List (Fin n × Fin n) := (List.finRange n).map fun k => (σ k, k)

theorem deltaC_eq_word (H : Mc n → ℂ) :
    DeltaC H = fun b => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * word (blk σ) H b := by
  funext b
  simp only [DeltaC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, word, blk, List.foldr_map]

theorem flat_succ {N : ℕ} (τ : Fin (N + 1) → Equiv.Perm (Fin n)) :
    (List.finRange (N + 1)).flatMap (fun j => blk (τ j)) =
      blk (τ 0) ++ (List.finRange N).flatMap (fun j => blk (τ j.succ)) := by
  rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]

theorem deltaC_iter_word (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (N : ℕ) :
    Set.EqOn (DeltaC^[N] F) (fun b => ∑ τ : Fin N → Equiv.Perm (Fin n),
      ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ) *
        word ((List.finRange N).flatMap fun j => blk (τ j)) F b) U := by
  induction N with
  | zero => intro b _; simp [word]
  | succ N ih =>
    intro b hb
    rw [Function.iterate_succ_apply', deltaC_eq_word]
    dsimp only
    have step : ∀ σ : Equiv.Perm (Fin n), word (blk σ) (DeltaC^[N] F) b =
        ∑ τ : Fin N → Equiv.Perm (Fin n), ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ) *
          word (blk σ ++ (List.finRange N).flatMap fun j => blk (τ j)) F b := by
      intro σ
      rw [eqOn_word (blk σ) hU ih hb]
      have hw := word_sum (Finset.univ : Finset (Fin N → Equiv.Perm (Fin n)))
        (fun τ => ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ))
        (fun τ => word ((List.finRange N).flatMap fun j => blk (τ j)) F) (blk σ) hU
        (fun τ => word_contDiffOn _ hU hF) hb
      rw [hw]
      simp only [word_append]
    simp only [step, Finset.mul_sum]
    rw [← (Fin.consEquiv fun _ => Equiv.Perm (Fin n)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    simp only [Fin.consEquiv_apply, flat_succ, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ]
    push_cast
    ring

theorem link : Link := by
  intro n F U hU hF hh
  exact ⟨fun N y => by rw [(iterate_herm hU hF hh N).1],
    fun N b hb => (deltaC_iter_word hU hF N hb).trans (by simp only [blk])⟩

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Lagr
section
noncomputable section

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

def Twist : Prop :=
  ∀ (n : ℕ) (H : E n → ℂ), ContDiff ℝ (⊤ : ℕ∞) H → ∀ N : ℕ, ∃ G : ℕ → E n → ℂ,
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (G j)) ∧ ∀ (z : ℂ) (y : E n),
      (Delta^[N] (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * H y)) y =
        ((dP y : ℝ) : ℂ) ^ (-z) * ∑ j ∈ Finset.range (n * N + 1), z ^ j * G j y

def Lagr : Prop :=
  ∀ D : ℕ, ∃ C : ℝ, ∀ (c : ℕ → ℂ) (B : ℝ), (∀ i ≤ D, ‖∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * c j‖ ≤ B) →
    ∀ j ≤ D, ‖c j‖ ≤ C * B

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.MollIdA
section
noncomputable section

open MeasureTheory

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ}

def gK (v : E n) : ℝ := ∏ a, ∏ b, (Real.sqrt Real.pi)⁻¹ * Real.exp (-(v a b) ^ 2)

theorem gK_nonneg (v : E n) : 0 ≤ gK v := by
  unfold gK
  exact Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b _ =>
    mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_pos _).le

theorem integrable_gK : Integrable (gK (n := n)) := by
  have h1 : Integrable (fun s : ℝ => (Real.sqrt Real.pi)⁻¹ * Real.exp (-s ^ 2)) := by
    have := (integrable_exp_neg_mul_sq (b := 1) one_pos).const_mul (Real.sqrt Real.pi)⁻¹
    simpa using this
  have h2 : Integrable (fun w : Fin n → ℝ => ∏ b, (Real.sqrt Real.pi)⁻¹ * Real.exp (-(w b) ^ 2)) :=
    Integrable.fintype_prod (f := fun _ (s : ℝ) => (Real.sqrt Real.pi)⁻¹ * Real.exp (-s ^ 2)) (fun _ => h1)
  exact Integrable.fintype_prod (f := fun _ (w : Fin n → ℝ) => ∏ b, (Real.sqrt Real.pi)⁻¹ * Real.exp (-(w b) ^ 2))
    (fun _ => h2)

theorem integral_gK : ∫ v, gK (n := n) v = 1 := by
  have h1 : ∫ s : ℝ, (Real.sqrt Real.pi)⁻¹ * Real.exp (-s ^ 2) = 1 := by
    rw [integral_const_mul]
    have := integral_gaussian 1
    simp only [neg_mul, one_mul, div_one] at this
    rw [this]
    exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  unfold gK
  rw [integral_fintype_prod_volume_eq_prod (f := fun _ (w : Fin n → ℝ) =>
    ∏ b, (Real.sqrt Real.pi)⁻¹ * Real.exp (-(w b) ^ 2))]
  simp_rw [integral_fintype_prod_volume_eq_prod (f := fun _ (s : ℝ) => (Real.sqrt Real.pi)⁻¹ * Real.exp (-s ^ 2)), h1,
    Finset.prod_const_one]

theorem gauss_prod (ε : ℝ) (y : E n) :
    Complex.exp (-((ε * ip y y : ℝ) : ℂ)) = ∏ a, ∏ b, Complex.exp (-(ε : ℂ) * ((y a b : ℝ) : ℂ) ^ 2) := by
  simp_rw [← Complex.exp_sum]
  congr 1
  unfold ip
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem integrable_gauss (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun y : E n => Complex.exp (-((ε * ip y y : ℝ) : ℂ))) := by
  simp_rw [gauss_prod]
  have h1 : Integrable (fun s : ℝ => Complex.exp (-(ε : ℂ) * (s : ℂ) ^ 2)) :=
    integrable_cexp_neg_mul_sq (by simpa using hε)
  have h2 : Integrable (fun w : Fin n → ℝ => ∏ b, Complex.exp (-(ε : ℂ) * ((w b : ℝ) : ℂ) ^ 2)) :=
    Integrable.fintype_prod (f := fun _ (s : ℝ) => Complex.exp (-(ε : ℂ) * (s : ℂ) ^ 2)) (fun _ => h1)
  exact Integrable.fintype_prod (f := fun _ (w : Fin n → ℝ) => ∏ b, Complex.exp (-(ε : ℂ) * ((w b : ℝ) : ℂ) ^ 2))
    (fun _ => h2)

theorem norm_gauss_le (ε : ℝ) (hε : 0 < ε) (y : E n) : ‖Complex.exp (-((ε * ip y y : ℝ) : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have h : 0 ≤ ip y y := by
    unfold ip
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => mul_self_nonneg _
  have : (-((ε * ip y y : ℝ) : ℂ)).re = -(ε * ip y y) := by simp
  rw [this, Real.exp_le_one_iff]
  nlinarith

theorem kraw_eq (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : t ≠ 0) (u : E n) :
    (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) *
        ∫ y : E n, Complex.exp (-((ε * ip y y : ℝ) : ℂ)) * Complex.exp (Complex.I * t * ip y u) =
      (((|t| / (2 * Real.sqrt ε)) ^ (n ^ 2) * gK ((|t| / (2 * Real.sqrt ε)) • u) : ℝ) : ℂ) := by
  set lam : ℝ := |t| / (2 * Real.sqrt ε) with hlam
  have hε' : 0 < (ε : ℂ).re := by simpa using hε

  have hprod : ∀ y : E n, Complex.exp (-((ε * ip y y : ℝ) : ℂ)) * Complex.exp (Complex.I * t * ip y u) =
      ∏ a, ∏ b, (Complex.exp (Complex.I * ((t * u a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ)) *
        Complex.exp (-(ε : ℂ) * ((y a b : ℝ) : ℂ) ^ 2)) := by
    intro y
    simp_rw [Finset.prod_mul_distrib, ← gauss_prod, ← Complex.exp_sum]
    rw [mul_comm]
    congr 2
    unfold ip
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hint : ∫ y : E n, Complex.exp (-((ε * ip y y : ℝ) : ℂ)) * Complex.exp (Complex.I * t * ip y u) =
      ∏ a, ∏ b, ((Real.pi : ℂ) / ε) ^ (1 / 2 : ℂ) * Complex.exp (-((t * u a b : ℝ) : ℂ) ^ 2 / (4 * ε)) := by
    simp_rw [hprod]
    rw [integral_fintype_prod_volume_eq_prod (f := fun a (w : Fin n → ℝ) =>
      ∏ b, (Complex.exp (Complex.I * ((t * u a b : ℝ) : ℂ) * ((w b : ℝ) : ℂ)) *
        Complex.exp (-(ε : ℂ) * ((w b : ℝ) : ℂ) ^ 2)))]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [integral_fintype_prod_volume_eq_prod (f := fun b (s : ℝ) =>
      Complex.exp (Complex.I * ((t * u a b : ℝ) : ℂ) * (s : ℂ)) * Complex.exp (-(ε : ℂ) * (s : ℂ) ^ 2))]
    refine Finset.prod_congr rfl fun b _ => ?_
    exact fourierIntegral_gaussian hε' _

  have hsq : ((Real.pi : ℂ) / ε) ^ (1 / 2 : ℂ) = ((Real.sqrt Real.pi / Real.sqrt ε : ℝ) : ℂ) := by
    rw [← Real.sqrt_div' _ hε.le, Real.sqrt_eq_rpow, Complex.ofReal_cpow (div_nonneg Real.pi_pos.le hε.le)]
    push_cast
    ring_nf
  have hcoord : ∀ s : ℝ, (((|t| / (2 * Real.pi)) : ℝ) : ℂ) * (((Real.pi : ℂ) / ε) ^ (1 / 2 : ℂ) *
      Complex.exp (-((t * s : ℝ) : ℂ) ^ 2 / (4 * ε))) =
      ((lam * ((Real.sqrt Real.pi)⁻¹ * Real.exp (-(lam * s) ^ 2)) : ℝ) : ℂ) := by
    intro s
    have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hse : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have hee : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
    have hpp : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
    rw [hsq]
    have hexp : (-((t * s : ℝ) : ℂ) ^ 2 / (4 * ε)) = ((-(lam * s) ^ 2 : ℝ) : ℂ) := by
      rw [hlam]
      push_cast
      have : ((|t| : ℝ) : ℂ) ^ 2 = (t : ℂ) ^ 2 := by
        rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
      have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
      have hs0 : ((Real.sqrt ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hse.ne'
      have hee' : ((Real.sqrt ε : ℝ) : ℂ) ^ 2 = (ε : ℂ) := by exact_mod_cast hee
      field_simp
      rw [this, hee']
      ring
    rw [hexp, ← Complex.ofReal_exp]
    push_cast
    rw [hlam]
    have hpi0 : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    have hs0 : ((Real.sqrt ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hse.ne'
    have hpp' : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by exact_mod_cast hpp
    have hpi1 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    push_cast
    field_simp
    rw [← hpp']
  rw [hint]
  have hC : (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) = ∏ _a : Fin n, ∏ _b : Fin n, (((|t| / (2 * Real.pi)) : ℝ) : ℂ) := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    rw [← pow_mul, sq]
  rw [hC, ← Finset.prod_mul_distrib]
  simp_rw [← Finset.prod_mul_distrib, hcoord]
  push_cast
  unfold gK
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [show ((lam : ℂ)) ^ (n ^ 2) = ∏ _a : Fin n, ∏ _b : Fin n, (lam : ℂ) by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, sq]]
  rw [← Finset.prod_mul_distrib]
  simp_rw [← Finset.prod_mul_distrib]

end PositivityTheory.Rg.Sw.WR.D.Moll
end
end

