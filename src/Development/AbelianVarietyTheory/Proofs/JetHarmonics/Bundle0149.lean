module

public import Mathlib
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0197
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.XiExistsOfBesselXiIntegrable
public import Formalism.HermitianCurvature.Bundle0010
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormActualOperatorsAlgebraicHypotheses
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0144
public import Formalism.HermitianCurvature.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaCapelliSymmOfXiExists
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory.BetaSym

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity MeasureTheory
open scoped ContDiff ComplexConjugate

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem clause_bdd (D : RealPlaceData k r Wp Wq) {A : ℝ} (hA : 0 ≤ A) (hCC : CCIntegrable D A)
    (Θ : DiffOp k r Wp Wq) (hS : SmoothCoef (GV k r) Θ)
    (hP : ∀ T ∈ Θ, ∃ C : ℝ, ∀ (u v : List (Mat k r)) (g : Mat k r),
      ‖dLR u v T.coef g‖ ≤ C ∧ ‖dLR u v T.coefAdj g‖ ≤ C)
    (F F' : Mat k r → (Wq →L[ℂ] Wp)) (hF0 : InCC A (opOrder Θ + 5) F) (hF0' : InCC A (opOrder Θ + 5) F') :
    InCC A 5 (opApply Θ F) ∧ InCC A 5 (opAdj Θ F') ∧ IntClause D Θ F F' := by
  have hF : InCC (A + 0) (opOrder Θ + 5) F := by rwa [add_zero]
  have hF' : InCC (A + 0) (opOrder Θ + 5) F' := by rwa [add_zero]
  have hO : IsOpen (∅ : Set (Mat k r)) := isOpen_empty
  have hcov : ∀ g ∈ GV k r, g ∈ (∅ : Set (Mat k r)) ∨ g ∈ GV k r := fun g hg => Or.inr hg
  have hAd0 : 0 ≤ A + 0 := by linarith
  have hadj : ∀ T ∈ Θ, InCC A (opOrder Θ + 5) (ap T.coefAdj F') := by
    intro T hT
    obtain ⟨C, hC⟩ := hP T hT
    obtain ⟨c', hc'⟩ := hF'
    exact ⟨_, prodBound (C := C) hO hcov (sCkOn_mono le_top (hS T hT).2)
      (fun u v _ _ _ g _ _ => by rw [Real.rpow_zero, mul_one]; exact (hC u v g).2) hc'
      (fun g _ h => absurd h (Set.notMem_empty g))⟩
  refine ⟨?_, ?_, ?_⟩
  · refine InCC_opsum Θ (fun T => ap T.coef (Rw T.word F)) ?_
    intro T hT
    have hlen := word_le_order Θ hT
    obtain ⟨C, hC⟩ := hP T hT
    obtain ⟨c, hc⟩ : InCC (A + 0) 5 (Rw T.word F) :=
      InCC_Rw T.word_lie (sInCC_mono le_rfl (by omega) hF)
    exact ⟨_, prodBound (C := C) hO hcov (sCkOn_mono le_top (hS T hT).1)
      (fun u v _ _ _ g _ _ => by rw [Real.rpow_zero, mul_one]; exact (hC u v g).1) hc
      (fun g _ h => absurd h (Set.notMem_empty g))⟩
  · refine InCC_opsum Θ
      (fun T => fun g => ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (ap T.coefAdj F') g) ?_
    intro T hT
    have hlen := word_le_order Θ hT
    obtain ⟨c, hc⟩ : InCC A 5 (Rw T.word.reverse (ap T.coefAdj F')) :=
      InCC_Rw (fun X hX => T.word_lie X (List.mem_reverse.mp hX))
        (sInCC_mono le_rfl (by simp; omega) (hadj T hT))
    exact ⟨_, CCle_smul _ hc⟩
  · intro p hp T hT i j hij hj
    have hlen := word_le_order Θ hT
    set a : Mat k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with hadef
    set b : Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hbdef
    have ha : a ∈ GV k r := gv_mul (gv_inv hp.1.1) (gv_inv hp.2.1.1)
    have hb : b ∈ GV k r := gv_mul hp.2.2.2.1 hp.2.2.1.1
    have hlie1 : ∀ X ∈ (T.word.take i).reverse, inLie k r X := fun X hX =>
      T.word_lie X (List.mem_of_mem_take (List.mem_reverse.mp hX))
    have hlie2 : ∀ X ∈ T.word.drop j, inLie k r X := fun X hX => T.word_lie X (List.mem_of_mem_drop hX)
    have hl1 : (T.word.take i).reverse.length ≤ opOrder Θ := by
      simp only [List.length_reverse, List.length_take]; omega
    have hl2 : (T.word.drop j).length ≤ opOrder Θ := by
      simp only [List.length_drop]; omega
    obtain ⟨K₁, hK₁⟩ : InCC A 0 (Rw (T.word.take i).reverse (ap T.coefAdj F')) :=
      InCC_Rw hlie1 (sInCC_mono le_rfl (by omega) (hadj T hT))
    obtain ⟨K₂, hK₂⟩ : InCC (A + 0) 0 (Rw ((T.word.drop j).map fun X => b⁻¹ * X * b) F) :=
      InCC_Rw (fun X hX => by
        obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
        exact lie_conj (hlie2 Y hY) hb) (sInCC_mono le_rfl (by simp only [List.length_map]; omega) hF)
    obtain ⟨cF, hcF⟩ := hF
    have hFk : CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) F := hcF.1
    set f₁ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.take i).reverse (ap T.coefAdj F') with hf₁
    set f₂ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.drop j) (rho D p F) with hf₂
    have hc₁ : ContinuousOn f₁ (GV k r) := CkOn_cont subset_rfl hK₁.1
    have hc₂ : ContinuousOn f₂ (GV k r) := by
      apply CkOn_cont subset_rfl
      rw [hf₂, ← Dw_wR, rho_eq_trn]
      apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) hlie2 x (by simpa [wL] using hx))
      apply CkOn_trn _ ha hb
      refine sCkOn_mono ?_ hFk
      simp only [wR, List.length_map, zero_add]
      exact_mod_cast (by omega : (T.word.drop j).length ≤ opOrder Θ + 5)
    have hb₂ : ∀ g ∈ GV k r, ‖f₂ g‖ ≤ ‖Lp D p‖ * K₂ := by
      intro g hg
      rw [hf₂, rho_eq_trn, Rw_trn _ ha hb _ hlie2
        (sCkOn_mono (by exact_mod_cast (by omega : (T.word.drop j).length ≤ opOrder Θ + 5)) hFk) g hg]
      exact ((Lp D p).le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (CC_bdd hAd0 hK₂ _ (gv_mul (gv_mul ha hg) hb)) (norm_nonneg _))
    set G : Mat k r → (Wq →L[ℂ] Wp) := fun g => ((‖f₂ g‖ : ℝ) : ℂ) • f₁ g with hG
    have hGn : ∀ g, ‖G g‖ = ‖f₁ g‖ * ‖f₂ g‖ := by
      intro g
      simp only [hG, norm_smul, Complex.norm_real, norm_norm]
      ring
    have hGc : ContinuousOn G (GV k r) := (Complex.continuous_ofReal.comp_continuousOn hc₂.norm).smul hc₁
    have hGm := aesm_of_continuousOn D hGc
    have hfin := hCC G (‖Lp D p‖ * K₂ * K₁) hGm (by
      intro g hg
      have h1 : gN g ^ A * ‖f₁ g‖ ≤ K₁ := hK₁.2 [] [] (by simp) (by simp) (by simp) g hg
      have h0 : 0 ≤ gN g ^ A * ‖f₁ g‖ := mul_nonneg (Real.rpow_nonneg (gN_pos hg).le _) (norm_nonneg _)
      calc gN g ^ A * ‖G g‖ = ‖f₂ g‖ * (gN g ^ A * ‖f₁ g‖) := by rw [hGn]; ring
        _ ≤ ‖Lp D p‖ * K₂ * K₁ := mul_le_mul (hb₂ g hg) h1 h0 ((norm_nonneg _).trans (hb₂ g hg)))
    have hint : Integrable (fun g : Mt k r => G (Matrix.of g)) D.μG := ⟨hGm, hfin⟩
    refine hint.norm.congr (Filter.Eventually.of_forall fun g => ?_)
    exact hGn _

theorem gv_stable (D : RealPlaceData k r Wp Wq) : IsStableOpen D (GV k r) :=
  ⟨⟨Set.univ, isOpen_univ, (Set.univ_inter _).symm⟩,
    fun _ hs _ hs' _ hg => gv_mul (gv_mul (Sset_sub hs) hg) (Sset_sub hs')⟩

theorem suppIn_gv (F : Mat k r → (Wq →L[ℂ] Wp)) : SuppIn (GV k r) F :=
  closure_minimal (by exact fun _ hg => hg.1) gv_closed

end GlobalTheory.BetaSym

namespace GlobalTheory

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP.ER BetaSym
open scoped ComplexConjugate

theorem beta_capelli_symm_of_xiExists (hXi : B.XiExists) : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Y A : ℝ) (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), B.AB k r ≤ A → (B.CkOn ⊤ (B.GV k r) (F) ∧ ∀ m : ℕ, B.InCC (A) m (F)) → (B.CkOn ⊤ (B.GV k r) (F') ∧ ∀ m : ℕ, B.InCC (A) m (F')) → B.beta D (Q.CV k r (Y : ℂ) F) F' = B.beta D F (Q.CV k r (Y : ℂ) F') := by
  intro k r Wp Wq _ _ _ _ _ _ D Y A F F' hAB hF hF'
  have hA : 0 ≤ A := le_trans (by unfold B.AB; positivity) hAB
  have hAdj : CapAdj := capAdj_of_int (capAdjInt_of_scalar capacity_adjoint_scalar)
  set Θ := capTh k r Wp Wq 1 (Y : ℂ) with hΘ
  obtain ⟨hord, -, -, -, hApp⟩ := capacity_theta_facts k r Wp Wq D 1 (Y : ℂ) 1 0
  obtain ⟨_, _, _, _, _, h3, _⟩ := BXiAsm.any_of hXi k r Wp Wq D A hAB
  have hS : B.SmoothCoef (B.GV k r) Θ := by
    intro T hT
    obtain ⟨c, w, rfl⟩ := mem_capOp 1 _ hT
    exact ⟨ckOn_const' _, ckOn_const' _⟩
  have hCo : B.Commutes D (B.GV k r) Θ := by
    intro p hp f hf g hgG
    rw [hΘ, hord] at hf
    have hs' := B7.sgs_mem D hp hgG
    rw [hApp _ (B5.ckOn_rho D hp hf) g hgG, capelli_rho_commute k r Wp Wq D (Y : ℂ) f p hp hf g hgG]
    simp only [B.rho]
    rw [hApp f hf _ hs', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  have hP : ∀ T ∈ Θ, ∃ C : ℝ, ∀ (u v : List (B.Mat k r)) (g : B.Mat k r),
      ‖B.dLR u v T.coef g‖ ≤ C ∧ ‖B.dLR u v T.coefAdj g‖ ≤ C := by
    intro T hT
    obtain ⟨c, w, rfl⟩ := mem_capOp 1 _ hT
    refine ⟨‖c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖ + ‖conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)‖,
      fun u v g => ?_⟩
    have h1 := norm_dLR_const_le (c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) u v g
    have h2 := norm_dLR_const_le (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) u v g
    have n1 := norm_nonneg (c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    have n2 := norm_nonneg (conj c • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    exact ⟨by simp only [TLB.cTerm]; linarith, by simp only [TLB.cTerm]; linarith⟩
  obtain ⟨c1, c2, c3⟩ := clause_bdd D hA (matrix_coefficient_integrable_all k r Wp Wq D A hAB) Θ hS hP F F' (hF.2 _) (hF'.2 _)
  have h1 := h3 (B.GV k r) Θ (gv_stable D) hS hCo F F' (B5.ckOn_mono le_top hF.1) (B5.ckOn_mono le_top hF'.1)
    (suppIn_gv F) (suppIn_gv F') (hF.2 _) (hF'.2 _) c1 c2 c3
  have h0 : B.beta D (Q.CV k r (Y : ℂ) F) F' = B.beta D (B.opApply Θ F) F' :=
    beta_form_congr_holds k r Wp Wq D _ _ _ _
      (fun g hg => by rw [hApp F (B5.ckOn_mono le_top hF.1) g hg, one_smul]) (fun _ _ => rfl)
  have h2 : B.beta D F (B.opAdj Θ F') = B.beta D F (Q.CV k r (Y : ℂ) F') :=
    beta_form_congr_holds k r Wp Wq D _ _ _ _ (fun _ _ => rfl) (fun g hg => by
      rw [hΘ, hAdj k r Wp Wq 1 (Y : ℂ) F' hF'.1 g hg, map_one, Complex.conj_ofReal, one_smul])
  rw [h0, h1, h2]

theorem beta_capelli_symm_of_bessel : GlobalTheory.HCXi.BesselXiIntegrable → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Y A : ℝ) (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), B.AB k r ≤ A → (B.CkOn ⊤ (B.GV k r) (F) ∧ ∀ m : ℕ, B.InCC (A) m (F)) → (B.CkOn ⊤ (B.GV k r) (F') ∧ ∀ m : ℕ, B.InCC (A) m (F')) → B.beta D (Q.CV k r (Y : ℂ) F) F' = B.beta D F (Q.CV k r (Y : ℂ) F') :=
  fun h => beta_capelli_symm_of_xiExists (GlobalTheory.HCXi.xiExists_of_besselXiIntegrable h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingCompactApproximantsCauchyBound
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.LevelZeroApprox

theorem ccle_sub {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ}
    {F F' : B.Mat k r → E} {c c' : ℝ} (h : B.CCle A m F c) (h' : B.CCle A m F' c') :
    B.CCle A m (F - F') (c + c') := by
  have h1 := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add h (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1 : ℂ) h')
  have e : (fun g => F g + (fun g => (-1 : ℂ) • F' g) g) = F - F' := by
    funext g; simp [sub_eq_add_neg]
  rw [e] at h1
  simpa using h1

theorem ckOn_sub {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {U : Set (B.Mat k r)}
    {F F' : B.Mat k r → E} (h : B.CkOn m U F) (h' : B.CkOn m U F') : B.CkOn m U (F - F') := by
  have h1 := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add h (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul (-1 : ℂ) h')
  have e : (fun g => F g + (fun g => (-1 : ℂ) • F' g) g) = F - F' := by
    funext g; simp [sub_eq_add_neg]
  rwa [e] at h1

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ckOn_bump_smul {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H : B.Mat k r → E} (h : B.CkOn ⊤ (B.GV k r) H) (n : ℕ) :
    B.CkOn ⊤ (B.GV k r) (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H g) := by
  have hcs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) := by
    have e : (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) = fun g => 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
      funext g
      rw [Formalism.FourierDecayAlt.P.JCx2.pdPsi, sub_sub_cancel]
      rfl
    rw [e]
    exact contDiff_const.sub (Formalism.FourierDecayAlt.P.JCx2.pd_psi_cd _)
  exact Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul hcs h
end

theorem threshold (k r N l : ℕ) (hl : l ≤ N) :
    B.AB k r + 1 + 2 * ((r : ℝ) + 1) * ((5 + l * (2 * r + k + 1) : ℕ) : ℝ) ≤
      20 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) := by
  unfold B.AB
  push_cast
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hlN : (l : ℝ) ≤ N := by exact_mod_cast hl
  set ρ : ℝ := (r : ℝ) + 1 with hρ
  set ν : ℝ := 2 * (r : ℝ) + k + 1 with hν
  have hρ1 : 1 ≤ ρ := by linarith
  have hν1 : 1 ≤ ν := by linarith
  have hkr : (k : ℝ) + r ≤ ν := by linarith
  have h4 : ρ ≤ ρ ^ 4 := le_self_pow₀ hρ1 (by norm_num)
  have h2 : ν ≤ ν ^ 2 := le_self_pow₀ hν1 (by norm_num)
  have h3 : ν ≤ ν ^ 3 := le_self_pow₀ hν1 (by norm_num)
  have hS : (l : ℝ) * ν + ν ≤ N * ν ^ 2 + ν ^ 3 :=
    add_le_add (mul_le_mul hlN h2 (by linarith) (by linarith)) h3
  have hlν : 0 ≤ (l : ℝ) * ν := by positivity
  have h5 : 20 * ρ * ((l : ℝ) * ν + ν) ≤ 20 * ρ ^ 4 * (N * ν ^ 2 + ν ^ 3) :=
    mul_le_mul (by linarith) hS (by linarith) (by positivity)
  refine le_trans ?_ h5
  have a1 : ((k : ℝ) + r) * ρ ≤ ν * ρ := mul_le_mul_of_nonneg_right hkr (by linarith)
  have a2 : ρ ≤ ν * ρ := le_mul_of_one_le_left (by linarith) hν1
  have a3 : 0 ≤ ρ * ((l : ℝ) * ν) := by positivity
  nlinarith

theorem beta_approx : ∃ Cc : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ) (N : ℕ), C6.IsCut0 χ → B.CkOn ⊤ (B.GV k r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A → w.length ≤ N → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → Tendsto (fun n : ℕ => B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g)) w) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₂ g))) atTop (𝓝 (B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((D.cutF Bs χ f ε₁)) w) (D.cutF Bs χ f ε₂))) ∧ ∃ K : ℝ, ∀ n m : ℕ, n ≤ m → ‖B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g) - (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((m : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g)) w) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g) - (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((m : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g))‖ ≤ K / ((n : ℝ) + 1) := by
  refine ⟨20, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ Bs s w χ f A N hχ hf hfA hA hw ε₁ ε₂ h₁ h₂
  have hth := (threshold k r N w.length hw).trans hA
  obtain ⟨K₁, hK₁, hH₁, hX₁⟩ := _root_.GlobalTheory.cutF_approximants_ccle k r Wp Wq Bs χ f A ε₁ (B.AB k r) _ hχ h₁ hf hfA hth
  obtain ⟨K₂, hK₂, hH₂, hX₂⟩ := _root_.GlobalTheory.cutF_approximants_ccle k r Wp Wq Bs χ f A ε₂ (B.AB k r) _ hχ h₂ hf hfA hth
  obtain ⟨C, hC, hbd⟩ := _root_.GlobalTheory.beta_capelliFold_norm_le k r Wp Wq Bs s w (B.AB k r) le_rfl
  have hsq := _root_.GlobalTheory.beta_foldCapelli_sesquilinear k r Wp Wq Bs s w (B.AB k r) le_rfl 1
  have hc₁ := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF Bs hχ hf ε₁
  have hx₁ := ckOn_bump_smul hc₁
  have lo : ∀ {F : B.Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ},
      B.CCle (B.AB k r) (5 + w.length * (2 * r + k + 1)) F c → B.CCle (B.AB k r) 5 F c :=
    fun h => Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono le_rfl (Nat.le_add_right _ _) h
  generalize D.cutF Bs χ f ε₁ = H₁ at *
  generalize D.cutF Bs χ f ε₂ = H₂ at *
  set X₁ : ℕ → B.Mat k r → (Wq →L[ℂ] Wp) := fun n g => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H₁ g with hX₁def
  set X₂ : ℕ → B.Mat k r → (Wq →L[ℂ] Wp) := fun n g => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H₂ g with hX₂def
  set b : (B.Mat k r → (Wq →L[ℂ] Wp)) → (B.Mat k r → (Wq →L[ℂ] Wp)) → ℂ := fun X Z =>
    B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) X w) Z with hb
  change ∀ n, B.CCle _ _ (X₁ n) K₁ ∧ B.CCle _ _ (X₁ n - H₁) _ at hX₁
  change ∀ n, B.CCle _ _ (X₂ n) K₂ ∧ B.CCle _ _ (X₂ n - H₂) _ at hX₂
  change ∀ n, B.CkOn _ _ (X₁ n) at hx₁
  change ∀ X Z c c', _ → _ → _ → ‖b X Z‖ ≤ _ at hbd
  change ∀ X X' Z Z', _ → _ → _ → _ → _ → _ → b (X + (1 : ℂ) • X') Z = b X Z + 1 * b X' Z ∧
    b X (Z + (1 : ℂ) • Z') = b X Z + (starRingEnd ℂ) 1 * b X Z' at hsq
  change Tendsto (fun n => b (X₁ n) (X₂ n)) atTop (𝓝 (b H₁ H₂)) ∧
    ∃ K : ℝ, ∀ n m : ℕ, n ≤ m → ‖b (X₁ n - X₁ m) (X₁ n - X₁ m)‖ ≤ K / ((n : ℝ) + 1)
  clear_value X₁ X₂ b
  constructor
  · have key : ∀ n : ℕ, ‖b (X₁ n) (X₂ n) - b H₁ H₂‖ ≤ 2 * C * K₁ * K₂ * (1 / ((n : ℝ) + 1)) := by
      intro n
      have hd := ckOn_sub (hx₁ n) hc₁
      have e1 := (hsq H₁ (X₁ n - H₁) (X₂ n) (X₂ n) hc₁ hd ⟨_, hH₁⟩ ⟨_, (hX₁ n).2⟩ ⟨_, lo (hX₂ n).1⟩
        ⟨_, lo (hX₂ n).1⟩).1
      have e2 := (hsq H₁ H₁ H₂ (X₂ n - H₂) hc₁ hc₁ ⟨_, hH₁⟩ ⟨_, hH₁⟩ ⟨_, lo hH₂⟩ ⟨_, lo (hX₂ n).2⟩).2
      simp only [one_smul, add_sub_cancel, one_mul, map_one] at e1 e2
      have b1 := hbd _ _ _ _ hd (hX₁ n).2 (lo (hX₂ n).1)
      have b2 := hbd _ _ _ _ hc₁ hH₁ (lo (hX₂ n).2)
      have e : b (X₁ n) (X₂ n) - b H₁ H₂ = b (X₁ n - H₁) (X₂ n) + b H₁ (X₂ n - H₂) := by
        rw [e1, e2]; ring
      rw [e]
      refine (norm_add_le _ _).trans ((add_le_add b1 b2).trans (le_of_eq ?_))
      ring
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) key ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * C * K₁ * K₂)
  · refine ⟨4 * C * K₁ * K₁, fun n m hnm => ?_⟩
    have hd := ckOn_sub (hx₁ n) (hx₁ m)
    have c1 := ccle_sub (hX₁ n).2 (hX₁ m).2
    rw [sub_sub_sub_cancel_right] at c1
    have hle : K₁ / ((m : ℝ) + 1) ≤ K₁ / ((n : ℝ) + 1) := by
      have : (n : ℝ) ≤ m := by exact_mod_cast hnm
      exact div_le_div_of_nonneg_left hK₁ (by positivity) (by linarith)
    have c2 := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c c1 (add_le_add_right hle (K₁ / ((n : ℝ) + 1)))
    have c3 := ccle_sub (hX₁ n).1 (hX₁ m).1
    refine (hbd _ _ _ _ hd c2 (lo c3)).trans (le_of_eq ?_)
    ring

end GlobalTheory.LevelZeroApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundedOfMemBoundedFactorsMonoid
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.BoundedFactors

theorem star_prod_ofFn {A : Type} [Ring A] [StarRing A] {r : ℕ} (f g : Fin r → A)
    (h : ∀ l, star (f l) = g l) (hc : ∀ l m, Commute (g l) (g m)) :
    star (List.ofFn f).prod = (List.ofFn g).prod := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, star_mul, h,
      ih (fun i => f i.succ) (fun i => g i.succ) (fun l => h _) (fun l m => hc _ _)]
    refine (Commute.list_prod_left _ _ ?_).eq
    intro x hx
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    exact hc _ _

theorem star_phase {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)
    (hc : ∀ l, star (L.c l) = L.cb l) (hi : ∀ l, star (L.ci l) = L.cbi l) :
    star (L.Drb * L.Dri) = L.Dr * L.Drbi := by
  have h1 : star L.Drb = L.Dr :=
    star_prod_ofFn _ _ (fun l => by rw [← hc l, star_star])
      (fun l m => L.fns_comm _ (by simp) _ (by simp))
  have h2 : star L.Dri = L.Drbi :=
    star_prod_ofFn _ _ hi (fun l m => L.fns_comm _ (by simp) _ (by simp))
  rw [star_mul, h1, h2]
  refine (Commute.list_prod_left _ _ ?_).eq
  intro x hx
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  refine Commute.list_prod_right _ _ ?_
  intro y hy
  obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hy
  exact L.fns_comm _ (by simp) _ (by simp)

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem hsInner_self_norm (A : Wq →L[ℂ] Wp) : ‖B.hsInner A A‖ = ‖B.hsVec A‖ ^ 2 := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K]
  simp

theorem hsInner_norm_le (A C : Wq →L[ℂ] Wp) : ‖B.hsInner A C‖ ≤ ‖B.hsVec A‖ * ‖B.hsVec C‖ := by
  unfold B.hsInner
  rw [mul_comm]
  exact norm_inner_le_norm _ _

theorem ptB_of_star_mul_self (b : RA P Bs) (ha : PtAdj P Bs b) (hb : PtB P Bs (star b * b)) : PtB P Bs b := by
  obtain ⟨C, hC, h⟩ := hb
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun Φ x hx => ?_⟩
  have h1 := ha Φ (b.1 Φ) x hx
  have h2 : nv ((star b).1 (b.1 Φ)) x ≤ C * nv Φ x := h Φ x hx
  have h3 : nv (b.1 Φ) x ^ 2 ≤ nv Φ x * nv ((star b).1 (b.1 Φ)) x := by
    unfold nv
    rw [← hsInner_self_norm, h1]
    exact hsInner_norm_le _ _
  have h0 : 0 ≤ nv Φ x := norm_nonneg _
  have h4 : nv (b.1 Φ) x ^ 2 ≤ (Real.sqrt C * nv Φ x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]
    nlinarith [mul_le_mul_of_nonneg_left h2 h0]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) h0) two_ne_zero).1 h4

theorem ptB_star (b : RA P Bs) (ha : PtAdj P Bs b) (hb : PtB P Bs b) : PtB P Bs (star b) := by
  obtain ⟨C, hC, h⟩ := hb
  refine ⟨C, hC, fun Ψ x hx => ?_⟩
  have h1 := ha ((star b).1 Ψ) Ψ x hx
  have h2 := h ((star b).1 Ψ) x hx
  have h3 : nv ((star b).1 Ψ) x ^ 2 ≤ nv (b.1 ((star b).1 Ψ)) x * nv Ψ x := by
    unfold nv
    rw [← hsInner_self_norm, ← h1]
    exact hsInner_norm_le _ _
  have h0 : 0 ≤ nv Ψ x := norm_nonneg _
  have h0' : 0 ≤ nv ((star b).1 Ψ) x := norm_nonneg _
  rcases h0'.eq_or_lt with he | hp
  · rw [← he]; exact mul_nonneg hC h0
  · have h4 : nv ((star b).1 Ψ) x * nv ((star b).1 Ψ) x ≤ nv ((star b).1 Ψ) x * (C * nv Ψ x) := by
      nlinarith [mul_le_mul_of_nonneg_right h2 h0]
    exact le_of_mul_le_mul_left h4 hp

end

theorem ptB_of_mem_bmon : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ b ∈ bmon d, PtB P Bs b := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN
  obtain ⟨⟨-, -, hRel, -, hc, hi, -⟩, -⟩ := _root_.GlobalTheory.HatNF.hatHyp_and_tie_of_isNF Wp Wq P Bs X μ L st l0 d hD hN
  have hκ := _root_.GlobalTheory.HatNF.kappa_ptAdj_ptB Wp Wq P Bs X μ L st l0 d hD hN
  obtain ⟨⟨h1, hmul⟩, hζi, hζbi, hD1, hD2, hD3, hD4, -⟩ := _root_.GlobalTheory.HatNF.ptB_basic Wp Wq P Bs X μ L st l0 d hD hN
  have hS := _root_.GlobalTheory.HatNF.RaiseAdj.ptAdj_SS Wp Wq P Bs X μ L st l0 d hD hN
  have hSb : ∀ l ∈ Finset.Icc 1 (P.k - 1), PtB P Bs (d.SS l) := fun l hl =>
    ptB_of_star_mul_self _ (hS l hl) (by rw [hRel.2.2.2.2.2 l hl]; exact (hκ _).2)
  have hSs : ∀ l ∈ Finset.Icc 1 (P.k - 1), PtB P Bs (star (d.SS l)) := fun l hl =>
    ptB_star _ (hS l hl) (hSb l hl)
  intro b hb
  induction hb using Submonoid.closure_induction with
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul _ _ hx hy
  | mem x hx =>
    rcases hx with ((hx | ⟨f, rfl⟩) | ⟨l, hl, rfl⟩) | ⟨l, hl, rfl⟩
    · rcases hx with rfl | rfl | rfl | rfl
      exacts [hζi, hζbi, hD1, hD2]
    · exact (hκ f).2
    · exact hmul _ _ hD3 (hSb l (by simpa using hl))
    · show PtB P Bs (star (d.L.Drb * d.L.Dri * d.SS l))
      rw [star_mul, star_phase d.L hc hi]
      exact hmul _ _ (hSs l (by simpa using hl)) hD4

end GlobalTheory.HatNF.BoundedFactors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorCutoffEqAndVanishStatement
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topVector_cutoff_eq_and_vanish : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (χ : ℝ → ℝ) (δ ε : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → C6.IsCut0 χ → (∀ x, x < δ → χ x = 0) → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) F → (ε < TBB.Gp p (TBB.bigPt P.r c) → tv p (D.cutF p.T.base χ F ε) w c = tv p F w c) ∧ (TBB.Gp p (TBB.bigPt P.r c) < δ * ε → tv p (D.cutF p.T.base χ F ε) w c = 0) ∧ (TBB.Gp p (TBB.bigPt P.r c) ≤ 0 → tv p F w c = 0) := by
  first | exact @GlobalTheory.TopVec.tv_cutF | exact GlobalTheory.TopVec.tv_cutF | (intros; apply GlobalTheory.TopVec.tv_cutF <;> assumption)
end

