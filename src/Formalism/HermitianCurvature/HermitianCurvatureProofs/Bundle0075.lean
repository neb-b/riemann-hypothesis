module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0069
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EulerZetaGammaInvIdentity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0065
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0054
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0066
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankFour
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFrameTwo
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0055
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0068
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0071
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0072
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0028
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0031
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0032
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalMeasurabilityWeakThreshold
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0002

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSPhaseA
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.M Finset

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh

def height (P : M.Par) (ρ : M.Ty P) : ℕ := ∑ i, ((ρ i : Fin _) : ℕ)

theorem sum_ind (P : M.Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    ∑ i : Fin (P.k - 1), (if (i : ℕ) + 1 = l then 1 else 0) = 1 := by
  rw [Finset.mem_Icc] at hl
  rw [Finset.sum_eq_single ⟨l - 1, by omega⟩]
  · rw [if_pos (by simp; omega)]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    ext
    simp
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem up_height (P : M.Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (ρ ρ' : M.Ty P) (hU : M.Up P l ρ ρ') :
    height P ρ' = height P ρ + 1 := by
  unfold height
  rw [Finset.sum_congr rfl (fun i _ => hU i), Finset.sum_add_distrib, sum_ind P l hl]

theorem pred_exists (P : M.Par) (ρ' : M.Ty P) (h : height P ρ' ≠ 0) :
    ∃ l ∈ Icc 1 (P.k - 1), ∃ ρ, M.Up P l ρ ρ' := by
  obtain ⟨i, hi⟩ : ∃ i, ((ρ' i : Fin _) : ℕ) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply h
    unfold height
    exact Finset.sum_eq_zero fun i _ => hall i
  refine ⟨(i : ℕ) + 1, ?_, fun j => if hj : j = i then ⟨((ρ' j : Fin _) : ℕ) - 1,
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (ρ' j).isLt⟩ else ρ' j, ?_⟩
  · rw [Finset.mem_Icc]
    have := i.isLt
    omega
  · intro j
    by_cases hj : j = i
    · subst hj
      simp
      omega
    · simp only [hj, dif_neg, not_false_eq_true]
      rw [if_neg]
      · simp
      · intro h2
        apply hj
        ext
        omega

theorem phase_exists (P : M.Par) (w : ℕ → M.Ty P → M.Ty P → ℂ)
    (hw1 : ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → ‖w l ρ ρ'‖ = 1)
    (hcoc : ∀ l ∈ Icc 1 (P.k - 1), ∀ j ∈ Icc 1 (P.k - 1), j ≠ l → ∀ ρ ρl ρj ρlj : M.Ty P,
      M.Up P l ρ ρl → M.Up P j ρ ρj → M.Up P j ρl ρlj → M.Up P l ρj ρlj →
        w j ρl ρlj * w l ρ ρl = w l ρj ρlj * w j ρ ρj) :
    ∃ u : M.Ty P → ℂ, (∀ ρ, ‖u ρ‖ = 1) ∧
      ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → u ρ' = w l ρ ρ' * u ρ := by
  classical
  have key : ∀ n : ℕ, ∃ u : M.Ty P → ℂ, (∀ ρ, ‖u ρ‖ = 1) ∧
      ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → height P ρ' ≤ n → u ρ' = w l ρ ρ' * u ρ := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ => 1, fun _ => by simp, fun l hl ρ ρ' hU hh => ?_⟩
      rw [up_height P l hl ρ ρ' hU] at hh
      omega
    | succ n ih =>
      obtain ⟨u, hu1, hu⟩ := ih
      let u' : M.Ty P → ℂ := fun ρ' =>
        if hh : height P ρ' = n + 1 then
          (let hp := pred_exists P ρ' (by omega)
           w hp.choose hp.choose_spec.2.choose ρ' * u hp.choose_spec.2.choose)
        else u ρ'
      have hu'1 : ∀ ρ, ‖u' ρ‖ = 1 := by
        intro ρ'
        simp only [u']
        split_ifs with hh
        · have hp := pred_exists P ρ' (by omega)
          rw [norm_mul, hw1 _ (pred_exists P ρ' (by omega)).choose_spec.1 _ _
            (pred_exists P ρ' (by omega)).choose_spec.2.choose_spec, hu1, one_mul]
        · exact hu1 ρ'
      refine ⟨u', hu'1, fun l hl ρ ρ' hU hh => ?_⟩
      have hhρ := up_height P l hl ρ ρ' hU
      have hρ : u' ρ = u ρ := by
        simp only [u']
        rw [dif_neg (by omega)]
      rw [hρ]
      by_cases hn : height P ρ' = n + 1
      · simp only [u']
        rw [dite_eq_left hn]
        set hp := pred_exists P ρ' (by omega) with hpdef
        set l0 := hp.choose with hl0
        have hl0m : l0 ∈ Icc 1 (P.k - 1) := hp.choose_spec.1
        set ρ0 := hp.choose_spec.2.choose with hρ0
        have hU0 : M.Up P l0 ρ0 ρ' := hp.choose_spec.2.choose_spec
        show w l0 ρ0 ρ' * u ρ0 = w l ρ ρ' * u ρ
        by_cases hll : l0 = l
        · have e : ρ0 = ρ := Formalism.FourierDecayAlt.P.Mx4.up_inj P l ρ' ρ0 ρ (hll ▸ hU0) hU
          rw [e, hll]
        · obtain ⟨σ, hσ1, hσ2⟩ := Formalism.FourierDecayAlt.P.Mx4.up_mixed1 P l0 l (Ne.symm hll) ρ ρ' ρ0 hU hU0

          have h0 := up_height P l0 hl0m ρ0 ρ' hU0
          have e1 : u ρ0 = w l σ ρ0 * u σ := hu l hl σ ρ0 hσ2 (by omega)
          have e2 : u ρ = w l0 σ ρ * u σ := hu l0 hl0m σ ρ hσ1 (by omega)
          have hc' := hcoc l0 hl0m l hl (Ne.symm hll) σ ρ ρ0 ρ' hσ1 hσ2 hU hU0
          rw [e1, e2, ← mul_assoc, ← mul_assoc, hc']
      · have hle : height P ρ' ≤ n := by omega
        simp only [u']
        rw [dif_neg hn]
        exact hu l hl ρ ρ' hU hle
  obtain ⟨u, hu1, hu⟩ := key (Finset.univ.sup (height P))
  exact ⟨u, hu1, fun l hl ρ ρ' hU => hu l hl ρ ρ' hU (Finset.le_sup (Finset.mem_univ ρ'))⟩

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem differential_operator_linear : Qr.DOpLin := qr_dOpLin_of trotter_product_formula trotter_product_matrices representation_exp

theorem differential_operator_bracket : Qr.DOpBracket := qr_dOpBracket_of representation_exp differential_operator_linear differential_operator_adjoint

theorem elementary_lie_elements : Qr.EcLie := qr_ecLie_of differential_operator_linear differential_operator_bracket

theorem frame_general_linear : Qr.FrameGl := qr_frameGl_of elementary_lie_elements

theorem lie_stabilizer : Qr.LieStab := qr_lieStab_of exp_generates representation_exp elementary_lie_elements

theorem qr_frameChange_proof : Qr.FrameChange := qr_frameChange_of elementary_lie_elements frame_general_linear

theorem branching_compact : Qr.BranchingK :=
  qr_branchingK_of branching_algebraic frame_general_linear lie_stabilizer stabilizer_lie_algebra qr_frameChange_proof
    exists_frame_two

theorem branching_proof : Branching := qr_branching_of branching_compact

theorem spectral_two_by_two : RadialDecompositionSpectral := radialDecompositionSpectral_of_branching branching_proof

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.EHcChange
section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dx_repF {X : Mat k r} (hX : inLie k r X) {φ F : Mat k r → E} {F' : Mat k r →L[ℝ] E} {U : Set (Mat k r)}
    {g : Mat k r} (hU : IsOpen U) (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : HasFDerivAt F F' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h) : Dx (false, X) φ g = F' (g * X) := by
  rw [← dx_false]
  have hc := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  have hF0 : HasFDerivAt F F' (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by simpa using hF
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) (F' (g * X)) 0 :=
    hF0.comp_hasDerivAt (0 : ℝ) hc
  have hU0 : U ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by simpa using hU.mem_nhds hgU
  have hev : (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0]
      fun t => F (g * NormedSpace.exp ((t : ℂ) • X)) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds hU0] with t ht
    exact hff _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hg hX t)
  exact (hcomp.congr_of_eventuallyEq hev).deriv

theorem EH_psi {φ F : Mat k r → E} {F' : Mat k r →L[ℝ] E} {U : Set (Mat k r)}
    {g : Mat k r} (hU : IsOpen U) (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : HasFDerivAt F F' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h) (a b : Fin (2 * r + k + 1)) :
    Q.EH k r a b φ g = Psi F' g (Matrix.single a b 1) := by
  have h1 : RdV (Xa k r a b) φ g = F' (g * Xa k r a b) := dx_repF (Xa_lie a b) hU hgU hg hF hff
  have h2 : RdV (Xb k r a b) φ g = F' (g * Xb k r a b) := dx_repF (Xb_lie a b) hU hgU hg hF hff
  show RdV (Xa k r a b) φ g + Complex.I • RdV (Xb k r a b) φ g =
    F' (g * Xa k r a b) + Complex.I • F' (g * Xb k r a b)
  rw [h1, h2]

private theorem inLie_conj_of_mem_GV' {y X : Mat k r} (hy : y ∈ GV k r) (hX : inLie k r X) :
    inLie k r (y⁻¹ * X * y) := by
  have hu : IsUnit y.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hy
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have h1 : Hpk k r * y⁻¹ = yᴴ * Hpk k r := by
    calc Hpk k r * y⁻¹ = yᴴ * Hpk k r * y * y⁻¹ := by rw [hy']
      _ = yᴴ * Hpk k r := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have h2 : (y⁻¹)ᴴ * Hpk k r = Hpk k r * y := by
    calc (y⁻¹)ᴴ * Hpk k r = (y⁻¹)ᴴ * (yᴴ * Hpk k r * y) := by rw [hy']
      _ = (y * y⁻¹)ᴴ * Hpk k r * y := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r * y := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one, Matrix.one_mul]
  unfold inLie at hX ⊢
  have e1 : (y⁻¹ * X * y)ᴴ * Hpk k r = yᴴ * (Xᴴ * Hpk k r) * y := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc, h2]
  have e2 : Hpk k r * (y⁻¹ * X * y) = yᴴ * (Hpk k r * X) * y := by
    simp only [← Matrix.mul_assoc]
    rw [h1]
  rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem EHc_psi {y : Mat k r} (hy : y ∈ GV k r) {φ F : Mat k r → E} {F' : Mat k r →L[ℝ] E} {U : Set (Mat k r)}
    {g : Mat k r} (hU : IsOpen U) (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : HasFDerivAt F F' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h) (c d : Fin (2 * r + k + 1)) :
    EHc k r y c d φ g = Psi F' g (y⁻¹ * Matrix.single c d 1 * y) := by
  rw [EHc_eq]
  beta_reduce
  rw [dx_repF (inLie_conj_of_mem_GV' hy (Xa_lie c d)) hU hgU hg hF hff,
    dx_repF (inLie_conj_of_mem_GV' hy (Xb_lie c d)) hU hgU hg hF hff]
  have hZ : y⁻¹ * Matrix.single c d 1 * y = y⁻¹ * Xa k r c d * y + Complex.I • (y⁻¹ * Xb k r c d * y) := by
    conv_lhs => rw [← hp_decomp (Matrix.single c d 1)]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    all_goals rfl
  obtain ⟨h1, h2⟩ := hp_of_parts (inLie_conj_of_mem_GV' hy (Xa_lie c d)) (inLie_conj_of_mem_GV' hy (Xb_lie c d))
  unfold Psi
  rw [hZ, h1, h2]

theorem conj_single (P Q : Mat k r) (c d : Fin (2 * r + k + 1)) :
    P * Matrix.single c d 1 * Q = ∑ a, ∑ b, (P a c * Q d b) • Matrix.single a b 1 := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and, mul_ite, ite_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

private theorem psi_add_hermitian_curvature (D : Mat k r →L[ℝ] E) (g A B : Mat k r) :
    Psi D g (A + B) = Psi D g A + Psi D g B := by
  have h1 : hpart1 (Hpk k r) (A + B) = hpart1 (Hpk k r) A + hpart1 (Hpk k r) B := by
    simp only [hpart1, Matrix.conjTranspose_add, mul_add, add_mul]
    rw [← smul_add]
    congr 1
    abel
  have h2 : hpart2 (Hpk k r) (A + B) = hpart2 (Hpk k r) A + hpart2 (Hpk k r) B := by
    simp only [hpart2, Matrix.conjTranspose_add, mul_add, add_mul]
    rw [← smul_add]
    congr 1
    abel
  simp only [Psi, h1, h2, mul_add, map_add (f := _), smul_add]
  abel

theorem Psi_sum {ι : Type*} (s : Finset ι) (D : Mat k r →L[ℝ] E) (g : Mat k r) (Z : ι → Mat k r) :
    Psi D g (∑ i ∈ s, Z i) = ∑ i ∈ s, Psi D g (Z i) := by
  exact map_sum (AddMonoidHom.mk' (Psi D g) (psi_add_hermitian_curvature D g)) Z s

theorem rep1 {φ : Mat k r → E} (hφ : CkOn 1 (GV k r) φ) {g : Mat k r} (hg : g ∈ GV k r) :
    ∃ (U : Set (Mat k r)) (F : Mat k r → E), IsOpen U ∧ g ∈ U ∧ HasFDerivAt F (fderiv ℝ F g) g ∧
      ∀ h ∈ U, h ∈ GV k r → φ h = F h := by
  obtain ⟨U, f', hU, hgU, hf', hff⟩ := hφ g hg
  have hd : DifferentiableAt ℝ f' g :=
    (hf'.differentiableOn (by first | exact le_rfl | simp)).differentiableAt (hU.mem_nhds hgU)
  exact ⟨U, f', hU, hgU, hd.hasFDerivAt, hff⟩

theorem EH_HC : HC (Q.EH (E := E) k r) := by
  intro a b m f hf
  have h := EHc_ck (Formalism.QuantumDeterminants.WeylGroupFacts.uh_one (k := k) (r := r)) a b m f hf
  rwa [EHc_one] at h

theorem EH_HL : HL (Q.EH (E := E) k r) := by
  intro a b f f₂ h
  exact EH_congr a b f f₂ h

theorem EH_HA : HA (Q.EH (E := E) k r) := by
  intro a b f f₂ hf hf₂ g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := rep1 hf hg
  obtain ⟨U₂, F₂, hU₂, hgU₂, hF₂, hff₂⟩ := rep1 hf₂ hg
  rw [EH_psi (φ := fun x => f x + f₂ x) (hU.inter hU₂) ⟨hgU, hgU₂⟩ hg (hF.add hF₂)
      (fun h hh hG => by simp only [hff h hh.1 hG, hff₂ h hh.2 hG, Pi.add_apply]) a b,
    EH_psi hU hgU hg hF hff a b, EH_psi hU₂ hgU₂ hg hF₂ hff₂ a b]
  simp only [Psi]
  show fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single a b 1)) +
      fderiv ℝ F₂ g (g * hpart1 (Hpk k r) (Matrix.single a b 1)) +
      Complex.I • (fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single a b 1)) +
        fderiv ℝ F₂ g (g * hpart2 (Hpk k r) (Matrix.single a b 1))) = _
  rw [smul_add]
  abel

theorem EH_HS : HS (Q.EH (E := E) k r) := by
  intro a b c f hf g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := rep1 hf hg
  rw [EH_psi (φ := fun x => c • f x) hU hgU hg (hF.const_smul c)
      (fun h hh hG => by simp only [hff h hh hG, Pi.smul_apply]) a b,
    EH_psi hU hgU hg hF hff a b]
  simp only [Psi]
  show c • fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single a b 1)) +
      Complex.I • c • fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single a b 1)) = _
  rw [smul_add, smul_comm Complex.I c]

theorem EHc_HL {y : Mat k r} (hy : y ∈ GV k r) : HL (EHc (E := E) k r y) := by
  intro a b f f₂ h g hg
  rw [EHc_eq, EHc_eq]
  beta_reduce
  rw [Dx_congr (x := (false, y⁻¹ * Xa k r a b * y)) (inLie_conj_of_mem_GV' hy (Xa_lie a b)) h g hg,
    Dx_congr (x := (false, y⁻¹ * Xb k r a b * y)) (inLie_conj_of_mem_GV' hy (Xb_lie a b)) h g hg]

theorem EHc_change {y : Mat k r} (hy : y ∈ GV k r) (c d : Fin (2 * r + k + 1)) (φ : Mat k r → E)
    (hφ : CkOn 1 (GV k r) φ) : ∀ g ∈ GV k r,
      EHc k r y c d φ g = ∑ a, ∑ b, (y⁻¹ a c * y d b) • Q.EH k r a b φ g := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := rep1 hφ hg
  rw [EHc_psi hy hU hgU hg hF hff c d, conj_single, Psi_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Psi_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Psi_smul, EH_psi hU hgU hg hF hff a b]

end Formalism.FourierDecayAlt.P.JFxE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.JfExhaustOfAvgCutoff
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxI

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def AvgCutoff : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (K : Set ((Fin r → ℂ) × ℂ)),
    IsCompact K → K ⊆ QDom k r D.z D.z' →
    ∃ φ : B.Mat k r → ℂ, B.CkOn ⊤ (B.GV k r) φ ∧
      (∃ C : Set (B.Mat k r), IsCompact C ∧ C ⊆ Om k r D.z D.z' ∧ ∀ g, g ∉ C → φ g = 0) ∧
      ∀ p₀, D.inSS p₀ → ∀ q ∈ K, ∫ p, φ (B.sgs p (B.sgs p₀ (B.gq D q))) ∂D.μSS = 1

def AdjLeibniz : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq),
    B.SmoothCoef (Om k r D.z D.z') Θ →
    ∃ Θ' : B.DiffOp k r Wp Wq, B.opOrder Θ' = B.opOrder Θ ∧
      ∀ f : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn (B.opOrder Θ : ℕ∞) (Om k r D.z D.z') f →
        ∀ g ∈ Om k r D.z D.z', B.opApply Θ' f g = B.opAdj Θ f g

variable {k r : ℕ}

theorem ckOn_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {U V : Set (Mat k r)}
    (hUV : U ⊆ V) {f : Mat k r → E} (h : CkOn m V f) : CkOn m U f := by
  exact fun g₀ hg => h g₀ (hUV hg)

theorem om_sub_gv (z z' : Fin (2 * r + k + 1) → ℂ) : Om k r z z' ⊆ GV k r := by
  exact Set.inter_subset_left

end Formalism.FourierDecayAlt.P.JFxI

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem thrW_of (k r o : ℕ) (A : ℝ)
    (h : 12 * ((r : ℝ) + 1) ^ 2 * ((o : ℝ) + r * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A o := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have ho : (0 : ℝ) ≤ o := Nat.cast_nonneg o
  push_cast at h
  constructor <;>
    nlinarith [mul_nonneg (mul_nonneg hr hr) (mul_nonneg hr hr), mul_nonneg (mul_nonneg hr hr) (mul_nonneg hr hk),
      mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg hr hr, mul_nonneg (mul_nonneg hr hr) hk, mul_nonneg hr hk,
      mul_nonneg (mul_nonneg hr hr) ho, mul_nonneg hr ho]

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem glev0 {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Q.Glev k r 0 := by
  refine ⟨hg, fun a ha => ?_⟩
  simp at ha

theorem psi_inv {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {n : Mat k r} (hn : n ∈ Nset k r) :
    psi k r z cStd n⁻¹ = (psi k r z cStd n)⁻¹ := by
  have h := Formalism.QuantumDeterminants.BesselUnipotentEquiv.star_psi_inv z cStd hz n hn
  rw [← h]
  unfold psi
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.conj_ofReal]

theorem xiTau_eq (D : RealPlaceData k r Wp Wq) (p : SS k r) :
    xiTau D (1, 1) p = psi k r D.z cStd (Matrix.of p.1.2) * (psi k r D.z' cStd (Matrix.of p.2.2))⁻¹ := by
  unfold xiTau lam psi
  push_cast
  rw [← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  ring

variable [FiniteDimensional ℂ Wp]

theorem jf_equiv (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) (hp : D.inSS p)
    (g : Mat k r) : rho D p (JF D F) g = (xiTau D (1, 1) p)⁻¹ • JF D F g := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have := FiniteDimensional.complete ℂ Wp
  have := FiniteDimensional.complete ℂ Wq
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have hN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have hW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r D.z
  have hW' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r D.z'
  have hU := Formalism.QuantumDeterminants.bessel_unitary_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F
    D.z_mem D.z'_mem D.haarN.conc D.haarW.conc D.haarW'.conc D.haarW.left D.haarW'.left
    (Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D) D.π_rep D.π'_rep
  have hNe := Formalism.QuantumDeterminants.bessel_unipotent_equiv_holds Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F
    D.z_mem D.z'_mem D.haarN.conc D.haarN.left
  have key : JF D F (sgs p g) =
      (psi k r D.z cStd (Matrix.of p.1.2)⁻¹ * psi k r D.z' cStd (Matrix.of p.2.2)) •
        (D.π (Matrix.of p.1.1)⁻¹).comp ((JF D F g).comp (D.π' (Matrix.of p.2.1))) := by
    unfold Formalism.FourierDecayAlt.B.JF Formalism.FourierDecayAlt.B.sgs
    rw [show (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1 =
        (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1 by
      simp only [Matrix.mul_assoc]]
    rw [hU _ _ (hW.inv_mem _ h1) _ h3, hNe _ _ (hN.inv_mem _ h2) _ h4,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  ext x
  simp only [rho, key, ContinuousLinearMap.comp_apply, _root_.smul_apply, map_smul]
  rw [Formalism.QuantumDeterminants.BesselUnitaryEquiv.rep_inv D.π'_rep h3 (hW'.inv_mem _ h3) (Matrix.mul_nonsing_inv _ (hW'.unit _ h3)) x,
    Formalism.QuantumDeterminants.BesselUnitaryEquiv.rep_inv D.π_rep h1 (hW.inv_mem _ h1) (Matrix.mul_nonsing_inv _ (hW.unit _ h1))]
  congr 1
  rw [xiTau_eq, psi_inv D.z_mem h2, mul_inv, inv_inv]

end

end Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

