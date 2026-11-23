module

public import Formalism.RealPlaceAnalysis.Bundle0002
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0065

@[expose] public section

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
section
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.REAL

section F3ALinfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

lemma hasDerivAt_matrix_exp_smul_at_zero {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ))
  have h2 := h.scomp (x := (0:ℝ)) Complex.ofRealCLM.hasDerivAt
  exact h2.congr_deriv (by simp)

end F3ALinfty

lemma tendsto_slope_exp_smul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) 0) (𝓝[≠] 0) (𝓝 X) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℂ) (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedSpace (R := ℝ) (m := Fin n) (n := Fin n) (α := ℂ)
  exact (hasDerivAt_matrix_exp_smul_at_zero X).tendsto_slope

lemma tendsto_slope_mul_exp_smul {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0) (𝓝[≠] 0) (𝓝 (g * X)) := by
  have h := (tendsto_slope_exp_smul X).const_mul g
  refine h.congr (fun t => ?_)
  simp only [slope_def_module, Matrix.mul_sub, Matrix.mul_smul]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma hasDerivAt_mul_exp_smul_zero {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 :=
  hasDerivAt_iff_tendsto_slope.mpr (tendsto_slope_mul_exp_smul g X)

lemma indefinite_unitary_mul_mem {n : ℕ} (ε : Fin n → Bool) {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : inUJ ε a) (hb : inUJ ε b) : inUJ ε (a * b) := by
  unfold inUJ at *
  calc (a * b)ᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [ha, hb]

lemma lie_algebra_add_mem {n : ℕ} (ε : Fin n → Bool) {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (hY : inG ε Y) : inG ε (X + Y) := by
  unfold inG at *
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]

lemma lie_algebra_real_smul_mem {n : ℕ} (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (r : ℝ) : inG ε ((r : ℂ) • X) := by
  unfold inG at *
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem right_derivative_extends : RdExt := by
  intro n ε f F U g X hU hg hgJ hF hfF hX
  unfold Rd
  have hγ := hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (indefinite_unitary_mul_mem ε hgJ (exp_indefinite_unitary_holds n ε X hX t))
  rw [hev.deriv_eq]
  exact hcomp.deriv

theorem right_derivative_left_invariant : RdLeft := by
  intro n f X h g
  simp only [Rd, Matrix.mul_assoc]

theorem rdLin_of (h : RdExt) : RdLin := by
  intro n ε f f' X Y r c g hf hf' hX hY hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g hg
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hFd' : DifferentiableAt ℝ F' g :=
    (hF'.differentiableOn (by simp)).differentiableAt (hU'.mem_nhds hgU')
  have eX := h n ε f F U g X hU hgU hg hF hfF hX
  refine ⟨?_, ?_, ?_⟩
  · rw [h n ε f F U g (X + Y) hU hgU hg hF hfF (lie_algebra_add_mem ε hX hY), eX,
      h n ε f F U g Y hU hgU hg hF hfF hY, Matrix.mul_add, map_add]
  · rw [h n ε f F U g ((r : ℂ) • X) hU hgU hg hF hfF (lie_algebra_real_smul_mem ε hX r), eX,
      Matrix.mul_smul, Complex.coe_smul, map_smul, Complex.real_smul]
  · have hsm : ContDiffOn ℝ ∞ (fun x => F x + c * F' x) (U ∩ U') :=
      (hF.mono Set.inter_subset_left).add (contDiffOn_const.mul (hF'.mono Set.inter_subset_right))
    rw [h n ε (fun x => f x + c * f' x) (fun x => F x + c * F' x) (U ∩ U') g X (hU.inter hU')
      ⟨hgU, hgU'⟩ hg hsm (fun x hx hxJ => by rw [hfF x hx.1 hxJ, hfF' x hx.2 hxJ]) hX,
      eX, h n ε f' F' U' g X hU' hgU' hg hF' hfF' hX]
    have hD : HasFDerivAt (fun x => F x + c * F' x) (fderiv ℝ F g + c • fderiv ℝ F' g) g :=
      hFd.hasFDerivAt.add (hFd'.hasFDerivAt.const_mul c)
    rw [hD.fderiv]
    simp

theorem right_derivative_linear : RdLin := rdLin_of right_derivative_extends

lemma signature_mul_signature_mul {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (Jm ε * A) = A := by
  rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

lemma cartan_involution_conjTranspose_mul {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (Jm ε * Zᴴ * Jm ε)ᴴ * Jm ε = Jm ε * Z := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc, Jm_mul_self,
    Matrix.mul_one]

lemma signature_mul_cartan_involution {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (Jm ε * Zᴴ * Jm ε) = Zᴴ * Jm ε := by
  rw [Matrix.mul_assoc, signature_mul_signature_mul]

lemma star_one_half : star (1 / 2 : ℂ) = 1 / 2 := by simp

lemma star_one_div_two_I : star (1 / (2 * Complex.I) : ℂ) = - (1 / (2 * Complex.I)) := by
  simp [Complex.conj_I]

theorem complex_parts_mem_lie_algebra_holds : CpartMem := by
  intro n ε Z
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold inG cpart1
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.sub_mul,
      cartan_involution_conjTranspose_mul, Matrix.mul_smul, Matrix.mul_sub, signature_mul_cartan_involution, star_one_half, ← smul_add]
    simp
  · unfold inG cpart2
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.add_mul,
      cartan_involution_conjTranspose_mul, Matrix.mul_smul, Matrix.mul_add, signature_mul_cartan_involution, star_one_div_two_I, neg_smul,
      add_comm (Jm ε * Z), neg_add_cancel]
  · unfold cpart1 cpart2
    rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]
    rw [sub_add_add_cancel, ← two_smul ℂ Z, smul_smul]
    norm_num
  · intro hX
    unfold inG at hX
    have hA : Jm ε * Zᴴ * Jm ε = -Z := by
      rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left hX, Matrix.mul_neg, signature_mul_signature_mul]
    unfold cpart1 cpart2
    rw [hA, sub_neg_eq_add, add_neg_cancel, smul_zero, ← two_smul ℂ Z, smul_smul]
    norm_num

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasComm
section
open scoped TensorProduct
open Finset

noncomputable section

namespace Formalism.REAL

theorem casComm_casK_comm {A : Type} [Ring A] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → A) (hE : GlRel E) (c d : Fin n) (hcd : ε c = ε d) :
    CasK ε E * E c d = E c d * CasK ε E :=
  _root_.UpperTheory.Reformulated.B.CasimirCommutation.casComm_casK_comm ε E hE c d hcd

theorem casimir_central_holds : CasCentral := by
  intro A _ n ε E hE
  refine ⟨fun c d => ?_, fun c d h => casComm_casK_comm ε E hE c d h⟩
  have h := casComm_casK_comm (fun _ => true) E hE c d rfl
  have hC : CasK (fun _ : Fin n => true) E = Cas E := by simp [CasK, Cas]
  rwa [hC] at h

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
section
open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def mulRightRealCLM {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

lemma mulRightCLM_apply {n : ℕ} (X h : Matrix (Fin n) (Fin n) ℂ) : mulRightRealCLM X h = h * X := rfl

lemma withTop_enat_infty_add_one_le_infty : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by simp

theorem rdSmooth_of (h : RdExt) : RdSmooth := by
  intro n ε f X hf hX g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun k => fderiv ℝ F k (k * X), hU, hg₀U, ?_, ?_⟩
  · have h1 := hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
    have h2 : ContDiffOn ℝ ∞ (fun k : Matrix (Fin n) (Fin n) ℂ => k * X) U :=
      (mulRightRealCLM X).contDiff.contDiffOn
    exact h1.clm_apply h2
  · intro k hk hkJ
    exact h n ε f F U k X hU hk hkJ hF hfF hX

lemma lie_algebra_bracket_mem {n : ℕ} {ε : Fin n → Bool} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (hY : inG ε Y) : inG ε (X * Y - Y * X) := by
  unfold inG at *
  have hX' : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  have hY' : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left hY
  have e1 : Yᴴ * Xᴴ * Jm ε = Jm ε * Y * X := by
    rw [Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, hY', Matrix.neg_mul, neg_neg]
  have e2 : Xᴴ * Yᴴ * Jm ε = Jm ε * X * Y := by
    rw [Matrix.mul_assoc, hY', Matrix.mul_neg, ← Matrix.mul_assoc, hX', Matrix.neg_mul, neg_neg]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2,
    Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  abel

theorem rdBracket_of (h : RdExt) (hs : RdSmooth) : RdBracket := by
  intro n ε f X Y g hf hX hY hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hFa : ContDiffAt ℝ ∞ F g := hF.contDiffAt (hU.mem_nhds hgU)
  have ext : ∀ Z, inG ε Z → ∀ k ∈ U, inUJ ε k → Rd Z f k = fderiv ℝ F k (k * Z) :=
    fun Z hZ k hk hkJ => h n ε f F U k Z hU hk hkJ hF hfF hZ
  have hsm : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      ContDiffOn ℝ ∞ (fun k => fderiv ℝ F k (k * Z)) U := fun Z =>
    (hF.fderiv_of_isOpen hU withTop_enat_infty_add_one_le_infty).clm_apply (mulRightRealCLM Z).contDiff.contDiffOn
  have hc : DifferentiableAt ℝ (fderiv ℝ F) g :=
    (hFa.fderiv_right (m := ∞) withTop_enat_infty_add_one_le_infty).differentiableAt (by simp)
  have hd : ∀ Z W : Matrix (Fin n) (Fin n) ℂ, fderiv ℝ (fun k => fderiv ℝ F k (k * Z)) g W
      = fderiv ℝ (fderiv ℝ F) g W (g * Z) + fderiv ℝ F g (W * Z) := by
    intro Z W
    have H := (hc.hasFDerivAt.clm_apply (mulRightRealCLM Z).hasFDerivAt).fderiv
    erw [H]
    exact add_comm _ _
  have e1 : Rd X (Rd Y f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * Y)) g (g * X) :=
    h n ε (Rd Y f) _ U g X hU hgU hg (hsm Y) (ext Y hY) hX
  have e2 : Rd Y (Rd X f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * X)) g (g * Y) :=
    h n ε (Rd X f) _ U g Y hU hgU hg (hsm X) (ext X hX) hY
  have e3 := ext _ (lie_algebra_bracket_mem hX hY) g hgU hg
  have hsym : IsSymmSndFDerivAt ℝ F g := hFa.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have hs2 := hsym (g * X) (g * Y)
  rw [e1, e2, e3, hd, hd]
  simp only [Matrix.mul_sub, Matrix.mul_assoc, map_sub]
  erw [hs2]
  exact add_sub_add_left_eq_sub _ _ _

lemma lie_algebra_add_mem_matrix {n : ℕ} {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : inG ε A) (hB : inG ε B) : inG ε (A + B) := by
  unfold inG at *
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
  calc Aᴴ * Jm ε + Bᴴ * Jm ε + (Jm ε * A + Jm ε * B)
      = (Aᴴ * Jm ε + Jm ε * A) + (Bᴴ * Jm ε + Jm ε * B) := by abel
    _ = 0 := by rw [hA, hB, add_zero]

lemma lie_algebra_neg_mem {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : inG ε A) : inG ε (-A) := by
  unfold inG at *
  rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hA, neg_zero]

lemma lie_algebra_sub_mem {n : ℕ} {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : inG ε A) (hB : inG ε B) : inG ε (A - B) := by
  rw [sub_eq_add_neg]; exact lie_algebra_add_mem_matrix hA (lie_algebra_neg_mem hB)

lemma lie_algebra_signature_conj {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Jm ε * Xᴴ * Jm ε = -X := by
  have hX' : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  rw [Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

lemma complex_parts_unique {n : ℕ} {ε : Fin n → Bool} {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : inG ε P) (hQ : inG ε Q) :
    cpart1 ε (P + Complex.I • Q) = P ∧ cpart2 ε (P + Complex.I • Q) = Q := by
  have hZ : Jm ε * (P + Complex.I • Q)ᴴ * Jm ε = -P + Complex.I • Q := by
    rw [conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, lie_algebra_signature_conj hP, lie_algebra_signature_conj hQ, Complex.star_def, Complex.conj_I]
    module
  unfold cpart1 cpart2
  rw [hZ]
  constructor
  · module
  · have : P + Complex.I • Q + (-P + Complex.I • Q) = (2 * Complex.I) • Q := by module
    rw [this, smul_smul, one_div, inv_mul_cancel₀ (by simp), one_smul]

lemma real_part_sub {n : ℕ} (ε : Fin n → Bool) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε (Z - W) = cpart1 ε Z - cpart1 ε W := by
  unfold cpart1
  rw [conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  module

lemma imaginary_part_sub {n : ℕ} (ε : Fin n → Bool) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (Z - W) = cpart2 ε Z - cpart2 ε W := by
  unfold cpart2
  rw [conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  module

lemma commutator_complex_expand {n : ℕ} (X1 X2 Y1 Y2 : Matrix (Fin n) (Fin n) ℂ) :
    (X1 + Complex.I • X2) * (Y1 + Complex.I • Y2) - (Y1 + Complex.I • Y2) * (X1 + Complex.I • X2) =
      ((X1 * Y1 - Y1 * X1) - (X2 * Y2 - Y2 * X2)) +
        Complex.I • ((X1 * Y2 - Y2 * X1) + (X2 * Y1 - Y1 * X2)) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  match_scalars <;> first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq

lemma right_derivative_neg (hl : RdLin) {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hB : inG ε B) (hg : inUJ ε g) :
    Rd (-B) f g = -Rd B f g := by
  have := (hl n ε f f B B (-1) 0 g hf hf hB hB hg).2.1
  have e : (((-1 : ℝ) : ℂ) • B) = -B := by simp
  rw [e] at this
  rw [this]; simp

lemma right_derivative_add (hl : RdLin) {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {A B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hA : inG ε A) (hB : inG ε B)
    (hg : inUJ ε g) : Rd (A + B) f g = Rd A f g + Rd B f g :=
  (hl n ε f f A B 0 0 g hf hf hA hB hg).1

lemma right_derivative_sub (hl : RdLin) {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {A B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hA : inG ε A) (hB : inG ε B)
    (hg : inUJ ε g) : Rd (A - B) f g = Rd A f g - Rd B f g := by
  rw [sub_eq_add_neg, right_derivative_add hl hf hA (lie_algebra_neg_mem hB) hg, right_derivative_neg hl hf hB hg, sub_eq_add_neg]

lemma complexified_derivative_sub (hc : CpartMem) (hl : RdLin) {n : ℕ} {ε : Fin n → Bool}
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f)
    (hg : inUJ ε g) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    Ec ε (Z - W) f g = Ec ε Z f g - Ec ε W f g := by
  obtain ⟨hZ1, hZ2, -, -⟩ := hc n ε Z
  obtain ⟨hW1, hW2, -, -⟩ := hc n ε W
  unfold Ec
  rw [real_part_sub, imaginary_part_sub, right_derivative_sub hl hf hZ1 hW1 hg, right_derivative_sub hl hf hZ2 hW2 hg]
  ring

lemma complexified_derivative_zero {n : ℕ} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : Ec ε 0 f g = 0 := by
  simp [Ec, cpart1, cpart2, Rd]

lemma complexified_derivative_commutator (hc : CpartMem) (hl : RdLin) (hb : RdBracket) (hs : RdSmooth) {n : ℕ}
    (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (Z W g : Matrix (Fin n) (Fin n) ℂ)
    (hf : SmoothOnG ε f) (hg : inUJ ε g) :
    Ec ε Z (Ec ε W f) g - Ec ε W (Ec ε Z f) g = Ec ε (Z * W - W * Z) f g := by
  obtain ⟨hX1, hX2, hZ, -⟩ := hc n ε Z
  obtain ⟨hY1, hY2, hW, -⟩ := hc n ε W
  have hEc : ∀ (Z' : Matrix (Fin n) (Fin n) ℂ) (f' : Matrix (Fin n) (Fin n) ℂ → ℂ),
      Ec ε Z' f' g = Rd (cpart1 ε Z') f' g + Complex.I * Rd (cpart2 ε Z') f' g := fun _ _ => rfl
  have hE : ∀ V, inG ε V → ∀ W' : Matrix (Fin n) (Fin n) ℂ,
      Rd V (Ec ε W' f) g = Rd V (Rd (cpart1 ε W') f) g + Complex.I * Rd V (Rd (cpart2 ε W') f) g :=
    fun V hV W' => (hl n ε _ _ V V 0 Complex.I g (hs n ε f _ hf (hc n ε W').1)
      (hs n ε f _ hf (hc n ε W').2.1) hV hV hg).2.2
  have hZW := commutator_complex_expand (cpart1 ε Z) (cpart2 ε Z) (cpart1 ε W) (cpart2 ε W)
  rw [← hZ, ← hW] at hZW
  have hP := lie_algebra_sub_mem (lie_algebra_bracket_mem hX1 hY1) (lie_algebra_bracket_mem hX2 hY2)
  have hQ := lie_algebra_add_mem_matrix (lie_algebra_bracket_mem hX1 hY2) (lie_algebra_bracket_mem hX2 hY1)
  obtain ⟨h1, h2⟩ := complex_parts_unique hP hQ
  rw [hEc Z, hEc W, hE _ hX1, hE _ hX2, hE _ hY1, hE _ hY2, hZW, hEc, h1, h2,
    right_derivative_sub hl hf (lie_algebra_bracket_mem hX1 hY1) (lie_algebra_bracket_mem hX2 hY2) hg,
    right_derivative_add hl hf (lie_algebra_bracket_mem hX1 hY2) (lie_algebra_bracket_mem hX2 hY1) hg,
    ← hb n ε f _ _ g hf hX1 hY1 hg, ← hb n ε f _ _ g hf hX2 hY2 hg,
    ← hb n ε f _ _ g hf hX1 hY2 hg, ← hb n ε f _ _ g hf hX2 hY1 hg]
  linear_combination (Rd (cpart2 ε Z) (Rd (cpart2 ε W) f) g -
    Rd (cpart2 ε W) (Rd (cpart2 ε Z) f) g) * Complex.I_mul_I

theorem eabGl_of (hc : CpartMem) (hl : RdLin) (hb : RdBracket) (hs : RdSmooth) : EabGl := by
  intro n ε f a b c d g hf hg
  unfold Eab
  rw [complexified_derivative_commutator hc hl hb hs ε f _ _ g hf hg]
  have hm : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · subst h1; subst h2; simp
    · subst h1; simp [h2]
    · subst h2; simp [h1]
    · simp [h1, h2]
  rw [hm, complexified_derivative_sub hc hl hf hg]
  split_ifs <;> simp [complexified_derivative_zero]

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorPowUpperVanishHolds
section
open Finset

noncomputable section

namespace Formalism.REAL

theorem generatorPowCovariance_holds : EpowCov := by
  intro A _ n E hE k
  induction k with
  | zero =>
    intro a b c d
    simp only [epow, @eq_comm _ b c, @eq_comm _ a d]
    have hl : E c d * (if a = b then (1 : A) else 0) - (if a = b then (1 : A) else 0) * E c d = 0 := by
      split_ifs <;> simp
    rw [hl]
    by_cases h2 : d = a <;> by_cases h3 : c = b <;> simp [h2, h3]
  | succ k ih =>
    intro a b c d
    simp only [epow]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    have step : ∀ e, E c d * (epow E k a e * E e b) - epow E k a e * E e b * E c d =
        ((if d = a then epow E k c e else 0) - (if e = c then epow E k a d else 0)) * E e b +
        epow E k a e * ((if d = e then E c b else 0) - (if b = c then E e d else 0)) := by
      intro e
      rw [← ih a e c d, ← hE c d e b]
      noncomm_ring
    simp only [step]
    by_cases hda : d = a <;> by_cases hbc : b = c <;>
      simp [hda, hbc, Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_mul, mul_sub, ite_mul, mul_ite] <;> abel

theorem generatorTraceCentral_holds : EtrCentral := by
  intro A _ n E hE k c d
  have hc := generatorPowCovariance_holds A n E hE k
  unfold etr
  rw [Finset.sum_mul, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have h1 : ∀ a, epow E k a a * E c d - E c d * epow E k a a =
      -((if d = a then epow E k c a else 0) - (if a = c then epow E k a d else 0)) := by
    intro a
    rw [← hc a a c d]
    abel
  simp only [h1, Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sub_self, neg_zero]

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.RealPlaceTaylor.TrPowSumFilterZero
section
open Finset

noncomputable section

namespace Formalism.REAL

def TrPow_m {n : ℕ} (l : Fin n → ℂ) : ℕ → Fin n → ℂ
  | 0 => fun _ => 1
  | k + 1 => fun a => l a * TrPow_m l k a - ∑ b ∈ univ.filter (fun b => a < b), TrPow_m l k b

lemma TrPow_m_zero {n : ℕ} (l : Fin n → ℂ) (a : Fin n) : TrPow_m l 0 a = 1 := rfl

lemma TrPow_m_succ {n : ℕ} (l : Fin n → ℂ) (k : ℕ) (a : Fin n) :
    TrPow_m l (k + 1) a = l a * TrPow_m l k a - ∑ b ∈ univ.filter (fun b => a < b), TrPow_m l k b :=
  rfl

lemma TrPow_diag (h : HWDiag) {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (v : V) (hE : GlRel E)
    (hv : IsHW E ν v) : ∀ (k : ℕ) (a : Fin n), epow E k a a v = TrPow_m (lsh ν) k a • v := by
  intro k
  induction k with
  | zero => intro a; simp [epow, TrPow_m_zero]
  | succ k ih =>
    intro a
    rw [h V n E ν v hE hv k a, TrPow_m_succ, ih a]
    simp only [ih]
    rw [← Finset.sum_smul, sub_smul, mul_smul]

end Formalism.REAL
end
end

