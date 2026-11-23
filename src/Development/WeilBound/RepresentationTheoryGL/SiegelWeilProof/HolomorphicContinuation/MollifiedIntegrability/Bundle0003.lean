module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBaseB

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DerivFA
section
noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

variable {m n : ℕ}

theorem continuous_evXD (P : PX m n) : Continuous (evX P) := by
  unfold evX
  have h : Continuous fun x : Fin m → Fin n → ℂ =>
      (fun k : Fin m × Fin n × Bool => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1) := by
    refine continuous_pi fun k => ?_
    rcases k with ⟨a, i, b⟩
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (continuous_apply i).comp (continuous_apply a)
    · simp only [↓reduceIte]
      exact continuous_star.comp ((continuous_apply i).comp (continuous_apply a))
  exact (MvPolynomial.continuous_eval P).comp h

theorem continuous_gsD (c : ℝ) : Continuous (gs (m := m) (n := n) c) := by
  have h : Continuous fun x : Fin m → Fin n → ℂ => (c * ∑ a, ∑ i, ‖x a i‖ ^ 2 : ℝ) := by fun_prop
  exact Complex.continuous_exp.comp (Complex.continuous_ofReal.comp h).neg

theorem continuous_ip_right (y : E n) : Continuous (fun q : E n => ip y q) := by
  unfold ip; fun_prop

theorem norm_exp_I_mul (t r : ℝ) : ‖Complex.exp (Complex.I * t * r)‖ = 1 := by
  have : Complex.I * (t : ℂ) * (r : ℂ) = ((t * r : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this]; exact Complex.norm_exp_ofReal_mul_I _

def pr (a b : Fin n) : E n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) a)

theorem pr_apply (a b : Fin n) (w : E n) : pr a b w = w a b := rfl

def Lc (q : E n) : E n →L[ℝ] ℂ := ∑ a, ∑ b, q a b • (Complex.ofRealCLM.comp (pr a b))

theorem Lc_apply (q w : E n) : Lc q w = ((ip w q : ℝ) : ℂ) := by
  simp only [Lc, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, pr_apply, ip, Complex.ofReal_sum, Complex.ofReal_mul, Complex.real_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem norm_Lc_le (q : E n) : ‖Lc q‖ ≤ ∑ a, ∑ b, |q a b| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [Lc_apply, Complex.norm_real, Real.norm_eq_abs, ip, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 : ‖w a b‖ ≤ ‖w a‖ := norm_le_pi_norm (w a) b
  have h2 : ‖w a‖ ≤ ‖w‖ := norm_le_pi_norm w a
  rw [← Real.norm_eq_abs]; exact h1.trans h2

theorem continuous_Lc_comp {X : Type*} [TopologicalSpace X] {f : X → E n} (hf : Continuous f) :
    Continuous fun x => Lc (f x) := by
  unfold Lc
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact (((continuous_apply b).comp (continuous_apply a)).comp hf).smul
    (continuous_const : Continuous fun _ : X => Complex.ofRealCLM.comp (pr a b))

theorem abs_qX_le (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (a b : Fin n) :
    |qX ε x a b| ≤ 2 * ‖evX (Qp ε a b) x‖ := by
  have h : qX ε x a b = (gramX ε x a b).re + (gramX ε x a b).im := rfl
  rw [h]
  have h1 := Complex.abs_re_le_norm (gramX ε x a b)
  have h2 := Complex.abs_im_le_norm (gramX ε x a b)
  have : gramX ε x a b = evX (Qp ε a b) x := rfl
  rw [← this]
  linarith [abs_add_le (gramX ε x a b).re (gramX ε x a b).im]

variable (ε : Fin m → Bool) (c t : ℝ)

def Fi (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : ℂ :=
  evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x))

def Fd (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : E n →L[ℝ] ℂ :=
  (evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x)) * (Complex.I * t)) • Lc (qX ε x)

variable {ε c t}

theorem continuous_Fi (hq : Continuous (qX (n := n) ε)) (P : PX m n) (y : E n) : Continuous (Fi ε c t P y) := by
  unfold Fi
  refine ((continuous_evXD P).mul (continuous_gsD c)).mul (Complex.continuous_exp.comp ?_)
  exact continuous_const.mul (Complex.continuous_ofReal.comp ((continuous_ip_right y).comp hq))

theorem continuous_Fd (hq : Continuous (qX (n := n) ε)) (P : PX m n) (y : E n) : Continuous (Fd ε c t P y) := by
  unfold Fd
  have h1 : Continuous fun x => evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x)) * (Complex.I * t) :=
    (continuous_Fi hq P y).mul continuous_const
  exact h1.smul (continuous_Lc_comp hq)

theorem norm_Fi (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : ‖Fi ε c t P y x‖ = ‖evX P x * gs c x‖ := by
  unfold Fi; rw [norm_mul, norm_exp_I_mul, mul_one]

theorem integrable_Fi (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y : E n) :
    Integrable (Fi ε c t P y) :=
  (hI m n c hc P).mono (continuous_Fi hq P y).aestronglyMeasurable
    (ae_of_all _ fun x => (norm_Fi P y x).le)

def bnd (ε : Fin m → Bool) (c t : ℝ) (P : PX m n) (x : Fin m → Fin n → ℂ) : ℝ :=
  |t| * ∑ a, ∑ b, 2 * ‖evX (Qp ε a b * P) x * gs c x‖

theorem integrable_bnd (hI : IntG) (hc : 0 < c) (P : PX m n) : Integrable (bnd ε c t P) := by
  unfold bnd
  refine Integrable.const_mul ?_ _
  refine integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_
  exact ((hI m n c hc (Qp ε a b * P)).norm).const_mul 2

theorem norm_Fd_le (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : ‖Fd ε c t P y x‖ ≤ bnd ε c t P x := by
  have e0 : ‖Fd ε c t P y x‖ = ‖evX P x * gs c x‖ * |t| * ‖Lc (qX ε x)‖ := by
    simp only [Fd, norm_smul, norm_mul, norm_exp_I_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      one_mul, mul_one]
  rw [e0]
  unfold bnd
  calc ‖evX P x * gs c x‖ * |t| * ‖Lc (qX ε x)‖
      ≤ ‖evX P x * gs c x‖ * |t| * ∑ a, ∑ b, |qX ε x a b| :=
        mul_le_mul_of_nonneg_left (norm_Lc_le _) (by positivity)
    _ = |t| * ∑ a, ∑ b, ‖evX P x * gs c x‖ * |qX ε x a b| := by
        simp only [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_; ring
    _ ≤ |t| * ∑ a, ∑ b, 2 * ‖evX (Qp ε a b * P) x * gs c x‖ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_) (abs_nonneg _)
        have h := abs_qX_le ε x a b
        have e : evX (Qp ε a b * P) x * gs c x = evX (Qp ε a b) x * (evX P x * gs c x) := by
          simp only [evX, map_mul]; ring
        rw [e]
        simp only [norm_mul]
        have hn : 0 ≤ ‖evX P x‖ * ‖gs c x‖ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h hn]

theorem hasFDerivAt_Fi (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) :
    HasFDerivAt (fun y => Fi ε c t P y x) (Fd ε c t P y x) y := by
  have h1 : HasFDerivAt (fun y : E n => ((ip y (qX ε x) : ℝ) : ℂ)) (Lc (qX ε x)) y := by
    have : (fun y : E n => ((ip y (qX ε x) : ℝ) : ℂ)) = fun y => Lc (qX ε x) y :=
      funext fun y => (Lc_apply _ y).symm
    rw [this]; exact (Lc (qX ε x)).hasFDerivAt
  have h2 := (h1.const_mul (Complex.I * t)).cexp.const_mul (evX P x * gs c x)
  have e : (evX P x * gs c x) • Complex.exp (Complex.I * t * ((ip y (qX ε x) : ℝ) : ℂ)) • (Complex.I * t) • Lc (qX ε x)
      = Fd ε c t P y x := by
    rw [Fd, smul_smul, smul_smul, mul_assoc (evX P x * gs c x)]
  exact h2.congr_fderiv e

theorem hasFDerivAt_FP (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y : E n) :
    HasFDerivAt (FP ε c t P) (∫ x, Fd ε c t P y x) y := by
  have := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (F := fun y x => Fi ε c t P y x)
    (F' := fun y x => Fd ε c t P y x) (x₀ := y) (bound := bnd ε c t P) (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall fun y' => (continuous_Fi hq P y').aestronglyMeasurable) (integrable_Fi hI hq hc P y)
    (continuous_Fd hq P y).aestronglyMeasurable (ae_of_all _ fun x y' _ => norm_Fd_le P y' x)
    (integrable_bnd hI hc P) (ae_of_all _ fun x y' _ => hasFDerivAt_Fi P y' x)
  exact this

theorem integrable_Fd (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y : E n) :
    Integrable (Fd ε c t P y) :=
  (integrable_bnd hI hc P).mono' (continuous_Fd hq P y).aestronglyMeasurable (ae_of_all _ fun x => norm_Fd_le P y x)

end PositivityTheory.Rg.Sw.WR.D
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GBCauchy
section
noncomputable section

open Matrix Metric

namespace PositivityTheory.Rg.Sw.WR.K.GB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiffOn_cpart {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U)
    (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (i j : Fin n) : ContDiffOn ℂ (⊤ : ℕ∞) (cpart i j F) U := by
  letI : NormedAddCommGroup (Mc n →L[ℂ] ℂ) := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℂ (Mc n →L[ℂ] ℂ) := ContinuousLinearMap.toNormedSpace
  have hle : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [← WithTop.coe_one, ← WithTop.coe_add, top_add]
  have h1 : ContDiffOn ℂ (⊤ : ℕ∞) (fun b => fderiv ℂ F b) U :=
    hF.fderiv_of_isOpen (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hU hle
  exact h1.clm_apply contDiffOn_const

theorem contDiffOn_word {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U)
    (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) : ∀ L : List (Fin n × Fin n), ContDiffOn ℂ (⊤ : ℕ∞) (word L F) U
  | [] => hF
  | ij :: L => contDiffOn_cpart hU (contDiffOn_word hU hF L) ij.1 ij.2

theorem mem_pdisc_self (b : Mc n) {r : Fin n → Fin n → ℝ} (hr : ∀ i j, 0 < r i j) : b ∈ pdisc b r := by
  intro i j
  simp only [sub_self, norm_zero]
  exact (hr i j).le

theorem shift_apply (b : Mc n) (w : ℂ) (i j a c : Fin n) :
    (b + w • Matrix.single i j (1 : ℂ)) a c - b a c = if i = a ∧ j = c then w else 0 := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_cancel_left]
  by_cases h : i = a ∧ j = c
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [Matrix.single_apply_of_ne _ _ _ _ _ h, if_neg h, mul_zero]

theorem shift_mem (b : Mc n) {r : Fin n → Fin n → ℝ} (hr : ∀ i j, 0 < r i j) (i j : Fin n) {w : ℂ}
    (hw : ‖w‖ ≤ r i j) : b + w • Matrix.single i j (1 : ℂ) ∈ pdisc b r := by
  intro a c
  rw [shift_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact hw
  · simpa using (hr a c).le

theorem shift_sub (b : Mc n) {r : Fin n → Fin n → ℝ} (hr : ∀ i j, 0 < r i j) (i j : Fin n) {w : ℂ}
    {K l : ℝ} (hK : 0 < K) (hl : 0 ≤ l) (hlK : l + 1 = K) (hw : ‖w‖ = r i j / K) :
    pdisc (b + w • Matrix.single i j (1 : ℂ)) (fun a c => r a c * (l / K)) ⊆ pdisc b r := by
  intro x hx a c
  have h1 := hx a c
  have h2 : ‖x a c - b a c‖ ≤ ‖x a c - (b + w • Matrix.single i j (1 : ℂ)) a c‖ +
      ‖(b + w • Matrix.single i j (1 : ℂ)) a c - b a c‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [shift_apply] at h2
  have hlK' : l / K ≤ 1 := by rw [div_le_one hK]; linarith
  split_ifs at h2 with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [hw] at h2
    have : r i j * (l / K) + r i j / K = r i j := by
      field_simp
      rw [← hlK]
    linarith
  · simp only [norm_zero, add_zero] at h2
    have := mul_le_of_le_one_right (hr a c).le hlK'
    linarith

theorem cauchy_gen {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U)
    (M : ℝ) : ∀ (L : List (Fin n × Fin n)) (b : Mc n) (r : Fin n → Fin n → ℝ), (∀ i j, 0 < r i j) →
      pdisc b r ⊆ U → (∀ x ∈ pdisc b r, ‖F x‖ ≤ M) →
      ‖word L F b‖ ≤ (L.map fun ij => (L.length : ℝ) / r ij.1 ij.2).prod * M := by
  intro L
  induction L with
  | nil =>
    intro b r hr _ hM
    simp only [word, List.foldr_nil, List.map_nil, List.prod_nil, one_mul]
    exact hM b (mem_pdisc_self b hr)
  | cons ij L ih =>
    intro b r hr hsub hM
    set K : ℝ := (L.length : ℝ) + 1 with hKdef
    have hK : 0 < K := by positivity
    set δ : ℝ := r ij.1 ij.2 / K with hδdef
    have hδ : 0 < δ := div_pos (hr _ _) hK
    have hδr : δ ≤ r ij.1 ij.2 := div_le_self (hr _ _).le (by simp [hKdef])
    set E : Mc n := Matrix.single ij.1 ij.2 (1 : ℂ) with hE
    set G : Mc n → ℂ := word L F with hG
    have hGd : ContDiffOn ℂ (⊤ : ℕ∞) G U := contDiffOn_word hU hF L
    set f : ℂ → ℂ := fun w => G (b + w • E) with hf
    have hφ : ∀ w : ℂ, HasDerivAt (fun w : ℂ => b + w • E) E w := by
      intro w
      have h := ((hasDerivAt_id w).smul_const E).const_add b
      rw [one_smul] at h
      exact h
    have hin : ∀ w : ℂ, ‖w‖ ≤ δ → b + w • E ∈ U := fun w hw =>
      hsub (shift_mem b hr ij.1 ij.2 (hw.trans hδr))
    have hdiffG : ∀ x ∈ U, DifferentiableAt ℂ G x := fun x hx =>
      ((hGd.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    have hfd : DifferentiableOn ℂ f (closedBall 0 δ) := by
      intro w hw
      have hw' : ‖w‖ ≤ δ := by simpa using hw
      exact ((hdiffG _ (hin w hw')).hasFDerivAt.comp_hasDerivAt w (hφ w)).differentiableAt.differentiableWithinAt
    have hderiv : deriv f 0 = word (ij :: L) F b := by
      have h0 : b + (0 : ℂ) • E = b := by simp
      have hb : DifferentiableAt ℂ G (b + (0 : ℂ) • E) := by
        rw [h0]; exact hdiffG b (hsub (mem_pdisc_self b hr))
      have h3 : HasDerivAt f (fderiv ℂ G (b + (0 : ℂ) • E) E) 0 := hb.hasFDerivAt.comp_hasDerivAt (0 : ℂ) (hφ 0)
      rw [h3.deriv, h0]
      rfl
    set B : ℝ := (L.map fun ij => K / r ij.1 ij.2).prod * M with hB
    have hsphere : ∀ w ∈ sphere (0 : ℂ) δ, ‖f w‖ ≤ B := by
      intro w hw
      have hw' : ‖w‖ = δ := by simpa using hw
      rcases Nat.eq_zero_or_pos L.length with hL | hL
      · have hLnil : L = [] := List.length_eq_zero_iff.mp hL
        subst hLnil
        show ‖F (b + w • E)‖ ≤ B
        simp only [hB, List.map_nil, List.prod_nil, one_mul]
        exact hM _ (shift_mem b hr ij.1 ij.2 (hw'.le.trans hδr))
      · have hl : (0 : ℝ) < L.length := by exact_mod_cast hL
        set r' : Fin n → Fin n → ℝ := fun a c => r a c * ((L.length : ℝ) / K) with hr'
        have hr'pos : ∀ a c, 0 < r' a c := fun a c => mul_pos (hr a c) (div_pos hl hK)
        have hs := shift_sub b hr ij.1 ij.2 (w := w) hK hl.le (by simp [hKdef]) hw'
        have := ih (b + w • E) r' hr'pos (hs.trans hsub) (fun x hx => hM x (hs hx))
        have heq : (L.map fun ij => (L.length : ℝ) / r' ij.1 ij.2) = (L.map fun ij => K / r ij.1 ij.2) := by
          apply List.map_congr_left
          intro x _
          simp only [hr']
          field_simp
        rw [heq] at this
        exact this
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ
      (hfd.diffContOnCl_ball subset_rfl) hsphere
    rw [hderiv] at hc
    calc ‖word (ij :: L) F b‖ ≤ B / δ := hc
      _ = ((ij :: L).map fun ij' => ((ij :: L).length : ℝ) / r ij'.1 ij'.2).prod * M := by
        simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        rw [hB, hδdef, ← hKdef]
        field_simp

theorem cauchyW : CauchyW := by
  intro n F U hU hF b₀ ρ hρ hP M hM L
  exact cauchy_gen hU hF M L b₀ ρ hρ hP hM

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GWickA
section
noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def ent (a : Fin m) (i : Fin n) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a)

def crd (k : Fin m × Fin n × Bool) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  if k.2.2 then (Complex.conjCLE.toContinuousLinearMap).comp (ent k.1 k.2.1) else ent k.1 k.2.1

theorem ent_apply (a : Fin m) (i : Fin n) (v : Fin m → Fin n → ℂ) : ent a i v = v a i := rfl

theorem crd_apply (k : Fin m × Fin n × Bool) (v : Fin m → Fin n → ℂ) :
    crd k v = if k.2.2 then star (v k.1 k.2.1) else v k.1 k.2.1 := by
  unfold crd; split_ifs <;> simp [ent_apply, Complex.conjCLE_apply]

theorem evX_eq (P : PX m n) (x : Fin m → Fin n → ℂ) : evX P x = MvPolynomial.eval (fun k => crd k x) P := by
  simp only [evX, crd_apply]

theorem evX_pderiv_mul_X (p : PX m n) (k b : Fin m × Fin n × Bool) (x : Fin m → Fin n → ℂ) :
    evX (pderiv b (p * X k)) x = evX (pderiv b p) x * crd k x + evX p x * (if k = b then 1 else 0) := by
  rw [pderiv_mul, pderiv_X]
  by_cases h : k = b
  · subst h; simp [evX_eq]
  · simp [evX_eq, Pi.single_apply, h]

def dEv (P : PX m n) (x : Fin m → Fin n → ℂ) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  ∑ k, evX (pderiv k P) x • crd k

theorem hasFDerivAt_evX (P : PX m n) (x : Fin m → Fin n → ℂ) : HasFDerivAt (evX P) (dEv P x) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : evX (C a : PX m n) = fun _ => a := by funext y; simp [evX]
    rw [h]; refine (hasFDerivAt_const a x).congr_fderiv ?_
    simp [dEv, evX]
  | add p q hp hq =>
    have h : evX (p + q) = fun y => evX p y + evX q y := by funext y; simp [evX]
    rw [h]; refine (hp.add hq).congr_fderiv ?_
    unfold dEv; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_smul]; congr 1; simp [evX]
  | mul_X p k hp =>
    have h : evX (p * X k) = fun y => evX p y * crd k y := by funext y; simp [evX_eq]
    rw [h]; refine (hp.mul (crd k).hasFDerivAt).congr_fderiv ?_
    ext v
    simp only [dEv, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul, evX_pderiv_mul_X, add_mul,
      Finset.sum_add_distrib]
    have e1 : ∑ b, evX (pderiv b p) x * crd k x * crd b v = crd k x * ∑ b, evX (pderiv b p) x * crd b v := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; ring
    have e2 : ∑ b, (evX p x * if k = b then 1 else 0) * crd b v = evX p x * crd k v := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    rw [e1, e2]; ring

end PositivityTheory.Rg.Sw.WR.G
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.HermTranspose
section
noncomputable section

open MeasureTheory Complex Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

namespace GB

def sgnR (ε : Fin m → Bool) (a : Fin m) : ℝ := if ε a then 1 else -1

theorem sgn_eq (ε : Fin m → Bool) (a : Fin m) : sgn ε a = ((sgnR ε a : ℝ) : ℂ) := by
  unfold sgn sgnR; split_ifs <;> simp

theorem evX_Qb (ε : Fin m → Bool) (bb : Bool) (i j : Fin n) (x : Fin m → Fin n → ℂ) :
    evX (Qb ε bb i j) x = ∑ a ∈ Finset.univ.filter (fun a => ε a = bb), star (x a i) * x a j := by
  simp [evX, Qb]

theorem gramX_apply (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramX ε x i j = ∑ a, ((sgnR ε a : ℝ) : ℂ) * (star (x a i) * x a j) := by
  unfold gramX
  rw [Qp, evX, map_sub, ← evX, ← evX, evX_Qb, evX_Qb, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold sgnR
  cases h : ε a <;> simp

theorem trace_gram (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    (b * gramX ε x).trace = ∑ a, ((sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (x a i) * bᵀ i j * x a j := by
  have L : (b * gramX ε x).trace =
      ∑ a, ∑ i, ∑ j, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX_apply, Finset.mul_sum]
    calc (∑ i, ∑ j, ∑ a, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)))
        = ∑ i, ∑ a, ∑ j, b i j * (((sgnR ε a : ℝ) : ℂ) * (star (x a j) * x a i)) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [L]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.transpose_apply]
  ring

theorem herm_transpose (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) : bᵀ.IsHermitian := by
  ext i j
  have := congrFun (congrFun hb j) i
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at this ⊢
  rw [← this]

end GB

open GB in
theorem base : Base := by
  intro m n ε c t hc b hb
  unfold secN
  have hpt : ∀ x : Fin m → Fin n → ℂ, evX 1 x * gs c x * cexp (Complex.I * t * (b * gramX ε x).trace) =
      ∏ a, cexp (-(((c * ∑ k, ‖x a k‖ ^ 2 : ℝ)) : ℂ) +
        Complex.I * ((t * sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (x a i) * bᵀ i j * x a j) := by
    intro x
    have h1 : evX (1 : PX m n) x = 1 := by simp [evX]
    rw [h1, one_mul, gs, ← Complex.exp_add, ← Complex.exp_sum, trace_gram]
    congr 1
    rw [Finset.sum_add_distrib]
    congr 1
    · push_cast
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      push_cast
      ring
  simp_rw [hpt]
  rw [integral_fintype_prod_volume_eq_prod (fun a (r : Fin n → ℂ) => cexp (-(((c * ∑ k, ‖r k‖ ^ 2 : ℝ)) : ℂ) +
        Complex.I * ((t * sgnR ε a : ℝ) : ℂ) * ∑ i, ∑ j, star (r i) * bᵀ i j * r j))]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [GB.gauss_row c (t * sgnR ε a) hc bᵀ (herm_transpose b hb)]
  have e : Complex.I * ((t * sgnR ε a : ℝ) : ℂ) = Complex.I * t * sgn ε a := by
    rw [sgn_eq]; push_cast; ring
  rw [e]
  rfl

end PositivityTheory.Rg.Sw.WR.G
end
end

