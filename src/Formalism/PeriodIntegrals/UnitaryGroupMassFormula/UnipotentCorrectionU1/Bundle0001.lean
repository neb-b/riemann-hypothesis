module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CADwlSmooth
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cAsec

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cA_hasDeriv (x : Bool × B.Mat k r) {F : B.Mat k r → E} {g : B.Mat k r} (hd : DifferentiableAt ℝ F g) :
    HasDerivAt (fun t : ℝ => F (crv x g t)) (fderiv ℝ F g (dirv x g)) 0 :=
  hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (crv_hasDerivAt x g) (crv_zero x g).symm

theorem cA_Dx_eq (x : Bool × B.Mat k r) {F : B.Mat k r → E} (hd : Differentiable ℝ F) :
    Dx x F = fun g => fderiv ℝ F g (dirL x g) := by
  funext g
  rw [Dx_eq, dirL_apply]
  exact (cA_hasDeriv x (hd g)).deriv

theorem cA_Dx_smooth (x : Bool × B.Mat k r) {F : B.Mat k r → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Dx x F) := by
  rw [cA_Dx_eq x (hF.differentiable (by simp))]
  exact (hF.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by exact_mod_cast le_rfl)).clm_apply (dirL x).contDiff

theorem cA_Dx_lin (x : Bool × B.Mat k r) {F₁ F₂ : B.Mat k r → E} (h₁ : Differentiable ℝ F₁)
    (h₂ : Differentiable ℝ F₂) (c : ℂ) :
    Dx x (fun g => F₁ g + c • F₂ g) = fun g => Dx x F₁ g + c • Dx x F₂ g := by
  funext g
  rw [Dx_eq, Dx_eq, Dx_eq, (cA_hasDeriv x (h₁ g)).deriv, (cA_hasDeriv x (h₂ g)).deriv]
  exact ((cA_hasDeriv x (h₁ g)).add ((cA_hasDeriv x (h₂ g)).const_smul c)).deriv

def Dwl (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) (F : B.Mat k r → E) : B.Mat k r → E :=
  w.foldr (fun x G => fun g => Dx x G g + lam x • G g) F

theorem cA_Dwl_smooth (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) {F : B.Mat k r → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Dwl lam w F) := by
  induction w with
  | nil => exact hF
  | cons x w ih => exact (cA_Dx_smooth x ih).add (ih.const_smul (lam x))

theorem cA_Dwl_lin (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) {F₁ F₂ : B.Mat k r → E}
    (h₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁) (h₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₂) (c : ℂ) :
    Dwl lam w (fun g => F₁ g + c • F₂ g) = fun g => Dwl lam w F₁ g + c • Dwl lam w F₂ g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    have d₁ := (cA_Dwl_smooth lam w h₁).differentiable (by simp)
    have d₂ := (cA_Dwl_smooth lam w h₂).differentiable (by simp)
    show (fun g => Dx x (Dwl lam w _) g + lam x • Dwl lam w _ g) = _
    rw [ih, cA_Dx_lin x d₁ d₂ c]
    funext g
    show _ = (Dx x (Dwl lam w F₁) g + lam x • Dwl lam w F₁ g) + c • (Dx x (Dwl lam w F₂) g + lam x • Dwl lam w F₂ g)
    rw [smul_add, smul_add, smul_comm c (lam x)]
    exact add_add_add_comm _ _ _ _

theorem cA_Dwl_append (lam : Bool × B.Mat k r → ℂ) (w : List (Bool × B.Mat k r)) (x : Bool × B.Mat k r)
    (F : B.Mat k r → E) : Dwl lam (w ++ [x]) F = Dwl lam w (fun g => Dx x F g + lam x • F g) := by
  simp [Dwl, List.foldr_append]

theorem cA_Dwl_bound (lam : Bool × B.Mat k r → ℂ) {Λ : ℝ} (hΛ : 0 ≤ Λ) (g : B.Mat k r) (M : ℝ) :
    ∀ (w : List (Bool × B.Mat k r)) (F : B.Mat k r → E), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
      (∀ x ∈ w, ‖lam x‖ ≤ Λ) → (∀ s : List (Bool × B.Mat k r), s.Sublist w → ‖Dw s F g‖ ≤ M) →
      ‖Dwl lam w F g‖ ≤ (1 + Λ) ^ w.length * M := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro F _ _ hM
    simpa [Dwl, Dw] using hM [] (List.Sublist.refl _)
  | append_singleton w x ih =>
    intro F hF hl hM
    have hl' : ∀ y ∈ w, ‖lam y‖ ≤ Λ := fun y hy => hl y (by simp [hy])
    have hx : ‖lam x‖ ≤ Λ := hl x (by simp)
    rw [cA_Dwl_append, cA_Dwl_lin lam w (cA_Dx_smooth x hF) hF]
    have b1 := ih (Dx x F) (cA_Dx_smooth x hF) hl' (by
      intro s hs
      have := hM (s ++ [x]) (hs.append (List.Sublist.refl _))
      rwa [Dw_append] at this)
    have b2 := ih F hF hl' (fun s hs => hM s (hs.trans (List.sublist_append_left _ _)))
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM [] (List.nil_sublist _))
    calc ‖Dwl lam w (Dx x F) g + lam x • Dwl lam w F g‖
        ≤ (1 + Λ) ^ w.length * M + Λ * ((1 + Λ) ^ w.length * M) := by
          refine (norm_add_le _ _).trans (add_le_add b1 ?_)
          rw [norm_smul]
          exact mul_le_mul hx b2 (norm_nonneg _) hΛ
      _ = (1 + Λ) ^ (w ++ [x]).length * M := by simp [pow_succ]; ring

theorem cA_Dw_expmul (lam : Bool × B.Mat k r → ℂ) (h : B.Mat k r → ℂ) :
    ∀ (w : List (Bool × B.Mat k r)) (F : B.Mat k r → E), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
      (∀ x ∈ w, ∀ g (t : ℝ), h (crv x g t) = Complex.exp ((t : ℂ) * lam x) * h g) →
      Dw w (fun g => h g • F g) = fun g => h g • Dwl lam w F g := by
  intro w
  induction w with
  | nil => intro F _ _; rfl
  | cons x w ih =>
    intro F hF hh
    have hh' : ∀ y ∈ w, ∀ g (t : ℝ), h (crv y g t) = Complex.exp ((t : ℂ) * lam y) * h g :=
      fun y hy => hh y (by simp [hy])
    show Dx x (Dw w _) = _
    rw [ih F hF hh']
    funext g
    have hG := cA_Dwl_smooth lam w hF
    have d := cA_hasDeriv x ((hG.differentiable (by simp)) g)
    have he : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * lam x) * h g) (lam x * h g) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * lam x) (1 * lam x) 0 :=
        (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (lam x)
      have h2 := (h1.cexp).mul_const (h g)
      simpa using h2
    have hs : HasDerivAt (fun t : ℝ => (Complex.exp ((t : ℂ) * lam x) * h g) • Dwl lam w F (crv x g t))
        ((Complex.exp (((0 : ℝ) : ℂ) * lam x) * h g) • fderiv ℝ (Dwl lam w F) g (dirv x g) +
          (lam x * h g) • Dwl lam w F (crv x g 0)) 0 := he.smul d
    rw [Dx_eq]
    have e : (fun t : ℝ => h (crv x g t) • Dwl lam w F (crv x g t)) =
        fun t : ℝ => (Complex.exp ((t : ℂ) * lam x) * h g) • Dwl lam w F (crv x g t) := by
      funext t; rw [hh x (by simp) g t]
    rw [e, hs.deriv, crv_zero, ← dirL_apply, ← congrFun (cA_Dx_eq x (hG.differentiable (by simp))) g]
    show _ = h g • (Dx x (Dwl lam w F) g + lam x • Dwl lam w F g)
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, smul_add, smul_smul]
    rw [mul_comm (lam x)]

theorem cA_Dw_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℂ] E')
    {U : Set (B.Mat k r)} (hU : IsOpen U) (w : List (Bool × B.Mat k r)) (hw : ∀ x ∈ w, B.inLie k r x.2)
    {f : B.Mat k r → E} (hf : B.CkOn (w.length : ℕ∞) U f) :
    ∀ g ∈ B.GV k r, g ∈ U → Dw w (fun h => L (f h)) g = L (Dw w f g) := by
  induction w with
  | nil => intro g _ _; rfl
  | cons x w ih =>
    intro g hg hgU
    have hw' : ∀ y ∈ w, B.inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hx : B.inLie k r x.2 := hw x (by simp)
    have hle : ((w.length : ℕ) : ℕ∞) ≤ ((x :: w).length : ℕ) := by exact_mod_cast Nat.le_succ _
    show Dx x (Dw w (fun h => L (f h))) g = L (Dx x (Dw w f) g)
    rw [Dx_congr_loc hx hU (f₂ := fun h => L (Dw w f h)) (ih hw' (sCkOn_mono hle hf)) g hg hgU]
    have hc : B.CkOn 1 U (Dw w f) := by
      apply CkOn_Dw hw'
      have : (1 : ℕ∞) + (w.length : ℕ∞) = ((x :: w).length : ℕ) := by simp; ring
      rw [this]; exact hf
    have h1 := CkOn_diff hx hc hgU hg
    have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    rw [Dx_eq]
    exact h2.deriv

end cAsec

end PI.UnitaryCorollaryDerivatives
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CompCA
section
open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace PI.UnitaryCorollaryDerivatives.CCA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma hasDx (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) (g : Mat k r) :
    HasDerivAt (fun t : ℝ => f (crv x g t)) (Dx x f g) 0 := by
  have h1 : HasFDerivAt f (fderiv ℝ f g) (crv x g 0) := by rw [crv_zero]; exact (hf g).hasFDerivAt
  have h2 := h1.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)
  have e : Dx x f g = fderiv ℝ f g (dirv x g) := by rw [Dx_eq]; exact h2.deriv
  rw [e]; exact h2

lemma Dx_fd (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) :
    Dx x f = fun g => fderiv ℝ f g (dirL x g) := by
  funext g
  rw [dirL_apply, Dx_eq]
  have h1 : HasFDerivAt f (fderiv ℝ f g) (crv x g 0) := by rw [crv_zero]; exact (hf g).hasFDerivAt
  exact (h1.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)).deriv

lemma sm_diff {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f := by
  first
  | exact hf.differentiable (by simp)
  | exact hf.differentiable le_top
  | exact hf.differentiable (by norm_num)

lemma sm_Dx (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dx x f) := by
  rw [Dx_fd x (sm_diff hf)]
  first
  | exact (hf.fderiv_right (m := ∞) le_rfl).clm_apply (dirL x).contDiff
  | exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply (dirL x).contDiff
  | exact (hf.fderiv_right (m := ∞) (by norm_num)).clm_apply (dirL x).contDiff

lemma sm_Dw (w : List (Bool × Mat k r)) {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dw w f) := by
  induction w with
  | nil => exact hf
  | cons x w ih => exact sm_Dx x ih

lemma Dx_add' (x : Bool × Mat k r) {f₁ f₂ : Mat k r → ℂ} (h₁ : Differentiable ℝ f₁)
    (h₂ : Differentiable ℝ f₂) : Dx x (fun g => f₁ g + f₂ g) = fun g => Dx x f₁ g + Dx x f₂ g := by
  funext g
  exact (hasDx x (h₁.add h₂) g).unique ((hasDx x h₁ g).add (hasDx x h₂ g))

lemma Dw_add' (w : List (Bool × Mat k r)) {f₁ f₂ : Mat k r → ℂ} (h₁ : ContDiff ℝ ∞ f₁)
    (h₂ : ContDiff ℝ ∞ f₂) : Dw w (fun g => f₁ g + f₂ g) = fun g => Dw w f₁ g + Dw w f₂ g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => f₁ g + f₂ g) = _
    rw [ih]
    exact Dx_add' x (sm_diff (sm_Dw w h₁)) (sm_diff (sm_Dw w h₂))

lemma Dx_mul' (x : Bool × Mat k r) {a b : Mat k r → ℂ} (ha : Differentiable ℝ a)
    (hb : Differentiable ℝ b) : Dx x (fun g => a g * b g) = fun g => Dx x a g * b g + a g * Dx x b g := by
  funext g
  have h0 : crv x g 0 = g := by simp [crv]
  have h := (hasDx x ha g).mul (hasDx x hb g)
  rw [h0] at h
  exact (hasDx x (ha.mul hb) g).unique h

lemma Dx_clm (x : Bool × Mat k r) (L : ℂ →L[ℝ] ℂ) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) :
    Dx x (fun g => L (f g)) = fun g => L (Dx x f g) := by
  funext g
  exact (hasDx x (L.differentiable.comp hf) g).unique (L.hasFDerivAt.comp_hasDerivAt _ (hasDx x hf g))

lemma Dw_clm (w : List (Bool × Mat k r)) (L : ℂ →L[ℝ] ℂ) {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) :
    Dw w (fun g => L (f g)) = fun g => L (Dw w f g) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => L (f g)) = _
    rw [ih]
    exact Dx_clm x L (sm_diff (sm_Dw w hf))

lemma Dw_snoc (w : List (Bool × Mat k r)) (x : Bool × Mat k r) (f : Mat k r → ℂ) :
    Dw (w ++ [x]) f = Dw w (Dx x f) := by
  unfold Dw
  rw [List.foldr_append]
  rfl

lemma leibC (g : Mat k r) (w : List (Bool × Mat k r)) :
    ∀ (a b : Mat k r → ℂ), ContDiff ℝ ∞ a → ContDiff ℝ ∞ b → ∀ M : ℝ,
      (∀ w₁ w₂ : List (Bool × Mat k r), w₁.Sublist w → w₂.Sublist w → (w₁ ++ w₂).Perm w →
        ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) →
      ‖Dw w (fun g => a g * b g) g‖ ≤ 2 ^ w.length * M := by
  induction w using List.reverseRecOn with
  | nil =>
    intro a b ha hb M hM
    simpa [Dw, norm_mul] using hM [] [] (by simp) (by simp) (by simp)
  | append_singleton w x ih =>
    intro a b ha hb M hM
    rw [Dw_snoc, Dx_mul' x (sm_diff ha) (sm_diff hb),
      Dw_add' w ((sm_Dx x ha).mul hb) (ha.mul (sm_Dx x hb))]
    have h1 := ih (Dx x a) b (sm_Dx x ha) hb M (fun w₁ w₂ s1 s2 p => by
      have e : w₁ ++ [x] ++ w₂ = w₁ ++ x :: w₂ := by simp
      have hp : (w₁ ++ [x] ++ w₂).Perm (w ++ [x]) := by
        rw [e]
        exact List.perm_middle.trans ((p.cons x).trans (List.perm_append_singleton x w).symm)
      have := hM (w₁ ++ [x]) w₂ (s1.append (List.Sublist.refl _))
        (s2.trans (List.sublist_append_left _ _)) hp
      rwa [Dw_snoc] at this)
    have h2 := ih a (Dx x b) ha (sm_Dx x hb) M (fun w₁ w₂ s1 s2 p => by
      have hp : (w₁ ++ (w₂ ++ [x])).Perm (w ++ [x]) := by
        rw [← List.append_assoc]
        exact p.append_right [x]
      have := hM w₁ (w₂ ++ [x]) (s1.trans (List.sublist_append_left _ _))
        (s2.append (List.Sublist.refl _)) hp
      rwa [Dw_snoc] at this)
    calc _ ≤ ‖Dw w (fun g => Dx x a g * b g) g‖ + ‖Dw w (fun g => a g * Dx x b g) g‖ := norm_add_le _ _
      _ ≤ 2 ^ w.length * M + 2 ^ w.length * M := add_le_add h1 h2
      _ = 2 ^ (w ++ [x]).length * M := by
        rw [List.length_append, List.length_singleton, pow_succ]
        ring

def reC : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

def imC : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM

lemma reC_apply (z : ℂ) : reC z = (z.re : ℂ) := rfl

lemma imC_apply (z : ℂ) : imC z = (z.im : ℂ) := rfl

lemma norm_reC (z : ℂ) : ‖reC z‖ ≤ ‖z‖ := by
  rw [reC_apply, Complex.norm_real, Real.norm_eq_abs]
  first
  | exact Complex.abs_re_le_norm z
  | exact Complex.abs_re_le_abs z

lemma norm_imC (z : ℂ) : ‖imC z‖ ≤ ‖z‖ := by
  rw [imC_apply, Complex.norm_real, Real.norm_eq_abs]
  first
  | exact Complex.abs_im_le_norm z
  | exact Complex.abs_im_le_abs z

lemma clm_split (L : ℂ →L[ℝ] ℂ) (d : ℂ) : L d = L 1 * reC d + L Complex.I * imC d := by
  have h : d = (d.re : ℝ) • (1 : ℂ) + (d.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [h]
  rw [map_add (f := _), map_smul, map_smul, reC_apply, imC_apply, Complex.real_smul, Complex.real_smul]
  ring

lemma Dx_comp (x : Bool × Mat k r) {χ : ℂ → ℂ} {ψ : Mat k r → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hψ : ContDiff ℝ ∞ ψ) :
    Dx x (fun g => χ (ψ g)) = fun g => (fun z => fderiv ℝ χ z 1) (ψ g) * reC (Dx x ψ g)
      + (fun z => fderiv ℝ χ z Complex.I) (ψ g) * imC (Dx x ψ g) := by
  funext g
  have h0 : crv x g 0 = g := by simp [crv]
  have hχd : Differentiable ℝ χ := by
    first
    | exact hχ.differentiable (by simp)
    | exact hχ.differentiable le_top
    | exact hχ.differentiable (by norm_num)
  have h1 := hasDx x (sm_diff hψ) g
  have h2 : HasFDerivAt χ (fderiv ℝ χ (ψ g)) (ψ (crv x g 0)) := by
    rw [h0]; exact (hχd (ψ g)).hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  have h4 := hasDx x (sm_diff (hχ.comp hψ)) g
  have h5 : Dx x (fun g => χ (ψ g)) g = fderiv ℝ χ (ψ g) (Dx x ψ g) := h4.unique h3
  rw [h5, clm_split]

lemma sm_fd {χ : ℂ → ℂ} (hχ : ContDiff ℝ ∞ χ) (v : ℂ) : ContDiff ℝ ∞ (fun z => fderiv ℝ χ z v) := by
  first
  | exact (hχ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  | exact (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  | exact (hχ.fderiv_right (m := ∞) (by norm_num)).clm_apply contDiff_const

end PI.UnitaryCorollaryDerivatives.CCA
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CompRA
section
open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace PI.UnitaryCorollaryDerivatives.CRH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma dif {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f := by
  first
  | exact hf.differentiable (by simp)
  | exact hf.differentiable le_top
  | exact hf.differentiable (by norm_num)

lemma hd_Dx (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) (g : Mat k r) :
    HasDerivAt (fun t : ℝ => f (crv x g t)) (Dx x f g) 0 := by
  rw [Dx_eq]
  exact ((hf _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)).differentiableAt.hasDerivAt

lemma Dx_fd (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : Differentiable ℝ f) :
    Dx x f = fun g => fderiv ℝ f g (dirL x g) := by
  funext g
  have h := (hf (crv x g 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)
  rw [crv_zero] at h
  rw [dirL_apply]
  exact (hd_Dx x hf g).unique h

lemma cd_Dx (x : Bool × Mat k r) {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dx x f) := by
  rw [Dx_fd x (dif hf)]
  first
  | exact (hf.fderiv_right (m := ∞) le_rfl).clm_apply (dirL x).contDiff
  | exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply (dirL x).contDiff
  | exact (hf.fderiv_right (m := ∞) (by norm_num)).clm_apply (dirL x).contDiff

lemma cd_Dw (w : List (Bool × Mat k r)) {f : Mat k r → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Dw w f) := by
  induction w with
  | nil => exact hf
  | cons x w ih => exact cd_Dx x ih

lemma Dx_add' (x : Bool × Mat k r) {a b : Mat k r → ℂ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    Dx x (fun g => a g + b g) = fun g => Dx x a g + Dx x b g := by
  funext g
  exact (hd_Dx x (ha.add hb) g).unique ((hd_Dx x ha g).add (hd_Dx x hb g))

lemma Dw_add' (w : List (Bool × Mat k r)) {a b : Mat k r → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    Dw w (fun g => a g + b g) = fun g => Dw w a g + Dw w b g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => a g + b g) = _
    rw [ih]
    exact Dx_add' x (dif (cd_Dw w ha)) (dif (cd_Dw w hb))

lemma Dx_mul' (x : Bool × Mat k r) {a b : Mat k r → ℂ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    Dx x (fun g => a g * b g) = fun g => Dx x a g * b g + a g * Dx x b g := by
  funext g
  have h0 : crv x g 0 = g := by simp [crv]
  have h := (hd_Dx x ha g).mul (hd_Dx x hb g)
  rw [h0] at h
  exact (hd_Dx x (ha.mul hb) g).unique h

def Spl (w w₁ w₂ : List (Bool × Mat k r)) : Prop := w₁.Sublist w ∧ w₂.Sublist w ∧ (w₁ ++ w₂).Perm w

private lemma Dw_append_singleton (w : List (Bool × Mat k r)) (x : Bool × Mat k r) (f : Mat k r → ℂ) :
    Dw (w ++ [x]) f = Dw w (Dx x f) := by
  unfold Dw
  rw [List.foldr_append]
  rfl

lemma leibB (g : Mat k r) (M : ℝ) (w : List (Bool × Mat k r)) :
    ∀ a b : Mat k r → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      (∀ w₁ w₂, Spl w w₁ w₂ → ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) →
      ‖Dw w (fun g => a g * b g) g‖ ≤ 2 ^ w.length * M := by
  induction w using List.reverseRecOn with
  | nil =>
    intro a b ha hb hM
    simpa [Dw, norm_mul] using hM [] [] (by unfold Spl; simp)
  | append_singleton w x ih =>
    intro a b ha hb hM
    rw [Dw_append_singleton, Dx_mul' x (dif ha) (dif hb),
      Dw_add' w ((cd_Dx x ha).mul hb) (ha.mul (cd_Dx x hb))]
    have h1 := ih (Dx x a) b (cd_Dx x ha) hb (fun w₁ w₂ hs => by
      obtain ⟨s1, s2, p⟩ := hs
      have e : w₁ ++ [x] ++ w₂ = w₁ ++ x :: w₂ := by simp
      have hp : (w₁ ++ [x] ++ w₂).Perm (w ++ [x]) := by
        rw [e]
        exact List.perm_middle.trans ((p.cons x).trans (List.perm_append_singleton x w).symm)
      have := hM (w₁ ++ [x]) w₂ (by
        unfold Spl
        exact ⟨s1.append (List.Sublist.refl _), s2.trans (List.sublist_append_left _ _), hp⟩)
      rwa [Dw_append_singleton] at this)
    have h2 := ih a (Dx x b) ha (cd_Dx x hb) (fun w₁ w₂ hs => by
      obtain ⟨s1, s2, p⟩ := hs
      have hp : (w₁ ++ (w₂ ++ [x])).Perm (w ++ [x]) := by
        rw [← List.append_assoc]
        exact p.append_right [x]
      have := hM w₁ (w₂ ++ [x]) (by
        unfold Spl
        exact ⟨s1.trans (List.sublist_append_left _ _), s2.append (List.Sublist.refl _), hp⟩)
      rwa [Dw_append_singleton] at this)
    calc _ ≤ ‖Dw w (fun g => Dx x a g * b g) g‖ + ‖Dw w (fun g => a g * Dx x b g) g‖ := norm_add_le _ _
      _ ≤ 2 ^ w.length * M + 2 ^ w.length * M := add_le_add h1 h2
      _ = 2 ^ (w ++ [x]).length * M := by
        rw [List.length_append, List.length_singleton, pow_succ]
        ring

end PI.UnitaryCorollaryDerivatives.CRH
end
end

