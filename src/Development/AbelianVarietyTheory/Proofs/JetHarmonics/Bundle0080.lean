module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Formalism.HermitianCurvature.Bundle0008
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.KStableFiniteDimSmoothCompactRootStable
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompactStable

open PI.UpqRep

theorem deriv_mem {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    {f : ℝ → H} {f' : H} (hf : HasDerivAt f f' 0) (hS : ∀ t, f t ∈ S) : f' ∈ S := by
  have hcl : IsClosed (S : Set H) := S.closed_of_finiteDimensional
  have hsl := hasDerivAt_iff_tendsto_slope_zero.mp hf
  refine hcl.mem_of_tendsto hsl (Filter.Eventually.of_forall fun t => ?_)
  exact S.smul_of_tower_mem t⁻¹ (S.sub_mem (hS _) (hS _))

variable {k r : ℕ}

private lemma real_smul_skew_and_commute {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (hc : M * X = X * M)
    (t : ℝ) : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) ∧ M * ((t : ℂ) • X) = ((t : ℂ) • X) * M := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, hX, Complex.star_def, Complex.conj_ofReal, smul_neg]
  · rw [Matrix.mul_smul, hc, Matrix.smul_mul]

private lemma exp_real_smul_mem_UJset_of_inG {n : ℕ} (M Y : Matrix (Fin n) (Fin n) ℂ) (hY : Yᴴ = -Y) (hc : M * Y = Y * M) :
    NormedSpace.exp Y ∈ UH M ∩ (Matrix.unitaryGroup (Fin n) ℂ : Set _) := by
  have hu : (NormedSpace.exp Y)ᴴ * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_conjTranspose, hY, ← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]
  have hcm : Commute M (NormedSpace.exp Y) := Commute.exp_right hc
  refine ⟨?_, ?_⟩
  · show (NormedSpace.exp Y)ᴴ * M * NormedSpace.exp Y = M
    rw [Matrix.mul_assoc, hcm.eq, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  · rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hu

theorem dsig_mem (R : Rep k r) (S : Submodule ℂ R.H) [FiniteDimensional ℂ S]
    (hS : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S)
    {X : Mx k r} (hX : Xᴴ = -X) (hc : Hpk k r * X = X * Hpk k r) {v : R.H} (hv : v ∈ S) (hsm : v ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X v ∈ S := by
  have hmem : ∀ t : ℝ, R.σ (NormedSpace.exp ((t : ℂ) • X)) v ∈ S := fun t =>
    hS _ (exp_real_smul_mem_UJset_of_inG _ _ (real_smul_skew_and_commute _ _ hX hc t).1 (real_smul_skew_and_commute _ _ hX hc t).2) v hv
  show deriv (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) 0 ∈ S
  by_cases hd : DifferentiableAt ℝ (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) 0
  · exact deriv_mem S hd.hasDerivAt hmem
  · rw [deriv_zero_of_not_differentiableAt hd]
    exact S.zero_mem

private lemma herm_eq_sum_star_mul_mulVec {n : ℕ} (M Y : Matrix (Fin n) (Fin n) ℂ) (h1 : Mᴴ = M) (h2 : M * M = 1)
    (hc : M * Y = Y * M) : M * Yᴴ * M = Yᴴ ∧ M * Yᴴ = Yᴴ * M := by
  have hs : Yᴴ * M = M * Yᴴ := by
    have h0 := congrArg Matrix.conjTranspose hc
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, h1] at h0
  refine ⟨?_, hs.symm⟩
  rw [← hs, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem dC_mem (R : Rep k r) (S : Submodule ℂ R.H) [FiniteDimensional ℂ S]
    (hS : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S)
    (h1 : (Hpk k r)ᴴ = Hpk k r) (h2 : Hpk k r * Hpk k r = 1)
    {Y : Mx k r} (hc : Hpk k r * Y = Y * Hpk k r) {v : R.H} (hv : v ∈ S) (hsm : v ∈ R.sm) :
    R.dC Y v ∈ S := by
  have hH : Formalism.QuantumDeterminants.Hpk k r = Hpk k r := rfl
  obtain ⟨hθ, hcs⟩ := herm_eq_sum_star_mul_mulVec _ Y h1 h2 hc
  have e1 : ((1 / 2 : ℂ) • (Y + -Yᴴ))ᴴ = -((1 / 2 : ℂ) • (Y + -Yᴴ)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_conjTranspose, ← smul_neg]
    congr 1
    · simp
    · abel
  have hI : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [Complex.star_def, map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat, mul_neg, div_neg]
  have e2 : ((1 / (2 * Complex.I)) • (Y - -Yᴴ))ᴴ = -((1 / (2 * Complex.I)) • (Y - -Yᴴ)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_conjTranspose, hI, neg_smul]
    congr 2
    abel
  have c1 : Hpk k r * ((1 / 2 : ℂ) • (Y + -Yᴴ)) = ((1 / 2 : ℂ) • (Y + -Yᴴ)) * Hpk k r := by
    rw [Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul, mul_neg, neg_mul, hc, hcs]
  have c2 : Hpk k r * ((1 / (2 * Complex.I)) • (Y - -Yᴴ)) =
      ((1 / (2 * Complex.I)) • (Y - -Yᴴ)) * Hpk k r := by
    rw [Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, mul_neg, neg_mul, hc, hcs]
  unfold BranchingSupport.Rep.dC
  rw [hH, hθ]
  exact S.add_mem (dsig_mem R S hS e1 c1 hv hsm) (S.smul_mem _ (dsig_mem R S hS e2 c2 hv hsm))

theorem Jm_single {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (h : ε a = ε b) :
    Jm ε * Matrix.single a b (1 : ℂ) = Matrix.single a b 1 * Jm ε := by
  ext i j
  simp only [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  split_ifs <;> simp_all

private lemma unitary_conj_mem_and_commute_Jmat {n : ℕ} (Jmat M Q g : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hcay : Qᴴ * Jmat * Q = M)
    (hg : g ∈ UH M ∩ (Matrix.unitaryGroup (Fin n) ℂ : Set _)) :
    Q * g * Qᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ Q * g * Qᴴ * Jmat = Jmat * (Q * g * Qᴴ) ∧
      Qᴴ * (Q * g * Qᴴ) * Q = g := by
  obtain ⟨hgM, hgU⟩ := hg
  have hgM' : gᴴ * M * g = M := hgM
  have q1 : Qᴴ * Q = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff'.mp hQ
    rwa [Matrix.star_eq_conjTranspose] at h0
  have q2 : Q * Qᴴ = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff.mp hQ
    rwa [Matrix.star_eq_conjTranspose] at h0
  have g2 : g * gᴴ = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff.mp hgU
    rwa [Matrix.star_eq_conjTranspose] at h0
  have hJ : Jmat = Q * M * Qᴴ := by
    rw [← hcay]
    calc Jmat = (Q * Qᴴ) * Jmat * (Q * Qᴴ) := by rw [q2, Matrix.one_mul, Matrix.mul_one]
      _ = Q * (Qᴴ * Jmat * Q) * Qᴴ := by simp only [Matrix.mul_assoc]
  have hgc : M * g = g * M := by
    calc M * g = (g * gᴴ) * M * g := by rw [g2, Matrix.one_mul]
      _ = g * (gᴴ * M * g) := by simp only [Matrix.mul_assoc]
      _ = g * M := by rw [hgM']
  refine ⟨?_, ?_, ?_⟩
  · have hs : Qᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
      exact q1
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hQ hgU) hs
  · rw [hJ]
    calc Q * g * Qᴴ * (Q * M * Qᴴ) = Q * g * (Qᴴ * Q) * M * Qᴴ := by simp only [Matrix.mul_assoc]
      _ = Q * (M * g) * Qᴴ := by
          rw [q1, Matrix.mul_one, hgc]
          simp only [Matrix.mul_assoc]
      _ = Q * M * (Qᴴ * Q) * g * Qᴴ := by
          rw [q1, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = Q * M * Qᴴ * (Q * g * Qᴴ) := by simp only [Matrix.mul_assoc]
  · calc Qᴴ * (Q * g * Qᴴ) * Q = (Qᴴ * Q) * g * (Qᴴ * Q) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [q1, Matrix.one_mul, Matrix.mul_one]

theorem kStable_smooth_and_stable : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r), PI.UpqRep.IsCayleyU k r ε Q → ∀ S : Submodule ℂ R.H, FiniteDimensional ℂ S → PI.UpqRep.IsKStableOn ε (fun g => R.σ (Q⁻¹ * g * Q)) S → (∀ v ∈ S, R.KFin v ∧ v ∈ R.sm) ∧ ∀ a b, ε a = ε b → ∀ v ∈ S, R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v ∈ S := by
  intro hK k r ε mu R hR Q hQ S hfin hKS
  obtain ⟨⟨-, hcay⟩, hQU⟩ := hQ
  obtain ⟨-, -, -, -, hTKsm, -, hKTK, -, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR
  have q1 : Qᴴ * Q = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff'.mp hQU
    rwa [Matrix.star_eq_conjTranspose] at h0
  have q2 : Q * Qᴴ = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff.mp hQU
    rwa [Matrix.star_eq_conjTranspose] at h0
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv q1
  have hS' : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S,
      R.σ g x ∈ S := by
    intro g hg x hx
    obtain ⟨hu, hc, he⟩ := unitary_conj_mem_and_commute_Jmat _ _ Q g hQU hcay hg
    have hk : Q * g * Qᴴ ∈ Kset ε := by
      simp only [Kset, Set.mem_ofPred_eq]
      exact ⟨hu, hc⟩
    have h0 := hKS (Q * g * Qᴴ) hk x hx
    simp only [hinv, he] at h0
    exact h0
  have hsm : ∀ v ∈ S, R.KFin v ∧ v ∈ R.sm := by
    intro v hv
    have hkf : R.KFin v := by
      simp only [BranchingSupport.Rep.KFin, PI.UpqRep.IsKFinHpk]
      exact ⟨S, hfin, hv, hS'⟩
    exact ⟨hkf, hTKsm v (hKTK v hkf)⟩
  refine ⟨hsm, fun a b hab v hv => ?_⟩
  have h1 : (Hpk k r)ᴴ = Hpk k r := by
    rw [← hcay, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Jm_conjTranspose]
    simp only [Matrix.mul_assoc]
  have h2 : Hpk k r * Hpk k r = 1 := by
    rw [← hcay]
    calc Qᴴ * Jm ε * Q * (Qᴴ * Jm ε * Q) = Qᴴ * Jm ε * (Q * Qᴴ) * Jm ε * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [q2, Matrix.mul_one, Matrix.mul_assoc (Qᴴ) (Jm ε), Jm_mul_self, Matrix.mul_one, q1]
  have hc : Hpk k r * (Q⁻¹ * Matrix.single a b 1 * Q) = (Q⁻¹ * Matrix.single a b 1 * Q) * Hpk k r := by
    rw [hinv, ← hcay]
    calc Qᴴ * Jm ε * Q * (Qᴴ * Matrix.single a b 1 * Q)
        = Qᴴ * Jm ε * (Q * Qᴴ) * Matrix.single a b 1 * Q := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * (Jm ε * Matrix.single a b 1) * Q := by
          rw [q2, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = Qᴴ * (Matrix.single a b 1 * Jm ε) * Q := by rw [Jm_single ε hab]
      _ = Qᴴ * Matrix.single a b 1 * (Q * Qᴴ) * Jm ε * Q := by
          rw [q2, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = Qᴴ * Matrix.single a b 1 * Q * (Qᴴ * Jm ε * Q) := by simp only [Matrix.mul_assoc]
  exact dC_mem R S hS' h1 h2 hc hv (hsm v hv).2

end GlobalTheory.CompactStable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatrixCoefficientSmoothDerivatives
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CoeffDeriv

open GlobalTheory.DerivedAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def coefL (R : Rep k r) (x : R.H) (X : V) : R.H →L[ℝ] V :=
  ((innerSL ℂ x).smulRight X).restrictScalars ℝ

theorem coefL_apply (x w : R.H) (X : V) : coefL R x X w = ⟪x, w⟫_ℂ • X := rfl

theorem dsigW_smooth (hR : R.IsDS ε mu) {y : R.H} (hy : y ∈ R.sm) (b : List (Mx k r))
    (hb : ∀ Y ∈ b, B.inLie k r Y) : PI.UpqRep.dsigW (k := k) (r := r) R.σ b y ∈ R.sm := by
  induction b with
  | nil => exact hy
  | cons Y b ih =>
    exact dsig_smooth hR.2 (hb Y (by simp)) (ih fun Z hZ => hb Z (by simp [hZ]))

theorem right_step (hK : PI.KFinSmooth) (hR : R.IsDS ε mu) (X : V) (F : Mx k r → V) (x : R.H) {y : R.H}
    (hy : y ∈ R.sm) (hF : ∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) {Y : Mx k r} (hY : B.inLie k r Y)
    (g : Mx k r) (hg : g ∈ GG k r) :
    deriv (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • Y))) 0 =
      ⟪x, R.σ g (PI.UpqRep.dsig (k := k) (r := r) R.σ Y y)⟫_ℂ • X := by
  obtain ⟨hmul, -⟩ := rep_basic_of_isDS hK k r ε mu R hR
  have h := (coefL R x X).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_apply (σ := R.σ) hY hy (R.σ g))
  rw [← coefL_apply, ← h.deriv]
  congr 1
  funext t
  have he : NormedSpace.exp ((t : ℂ) • Y) ∈ GG k r := exp_mem hY t
  rw [hF _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hg he), hmul g hg _ he]
  rfl

theorem left_step (hK : PI.KFinSmooth) (hR : R.IsDS ε mu) (X : V) (F : Mx k r → V) {x : R.H} (y : R.H)
    (hx : x ∈ R.sm) (hF : ∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) {Y : Mx k r} (hY : B.inLie k r Y)
    (g : Mx k r) (hg : g ∈ GG k r) :
    B.LdV Y F g = ⟪PI.UpqRep.dsig (k := k) (r := r) R.σ Y x, R.σ g y⟫_ℂ • X := by
  obtain ⟨hmul, hone, hinner, -⟩ := rep_basic_of_isDS hK k r ε mu R hR
  have h1 := (hasDerivAt_dsig (σ := R.σ) hY hx).inner ℂ (hasDerivAt_const (0 : ℝ) (R.σ g y))
  simp only [inner_zero_right, zero_add] at h1
  have h := h1.smul_const X
  unfold B.LdV
  rw [← h.deriv]
  congr 1
  funext t
  have he : NormedSpace.exp ((t : ℂ) • Y) ∈ GG k r := exp_mem hY t
  have he' : NormedSpace.exp (-((t : ℂ) • Y)) ∈ GG k r := by
    have := exp_mem hY (-t)
    rwa [Complex.ofReal_neg, neg_smul] at this
  have hee : NormedSpace.exp ((t : ℂ) • Y) * NormedSpace.exp (-((t : ℂ) • Y)) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl ((t : ℂ) • Y)).neg_right, add_neg_cancel, NormedSpace.exp_zero]
  rw [hF _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul he' hg), hmul _ he' g hg, ← hinner _ he, ← hmul _ he _ he', hee, hone]

theorem coeff_dLR : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (X : V) (F : Mx k r → V), R.IsDS ε mu → ∀ x ∈ R.sm, ∀ y ∈ R.sm, (∀ g ∈ GG k r, F g = ⟪x, R.σ g y⟫_ℂ • X) → B.CkOn ⊤ (B.GV k r) F ∧ ∀ a b : List (Mx k r), (∀ Y ∈ a, B.inLie k r Y) → (∀ Y ∈ b, B.inLie k r Y) → ∀ g ∈ GG k r, B.dLR a b F g = ⟪PI.UpqRep.dsigW (k := k) (r := r) R.σ a x, R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ b y)⟫_ℂ • X := by
  intro hK k r ε mu R V _ _ X F hR x hx y hy hF
  refine ⟨fun g₀ hg₀ => ?_, fun a b ha hb => ?_⟩
  · obtain ⟨U, G, hU, hgU, hG, hfG⟩ := hy g₀ hg₀
    refine ⟨U, fun g => coefL R x X (G g), hU, hgU, (coefL R x X).contDiff.comp_contDiffOn hG, ?_⟩
    intro g hg hgG
    have e : R.σ g y = G g := hfG g hg hgG
    rw [hF g hgG, e]
    rfl
  · have hRw : ∀ g ∈ GG k r, B.Rw b F g = ⟪x, R.σ g (PI.UpqRep.dsigW (k := k) (r := r) R.σ b y)⟫_ℂ • X := by
      induction b with
      | nil => exact hF
      | cons Y b ih =>
        have hb' : ∀ Z ∈ b, B.inLie k r Z := fun Z hZ => hb Z (by simp [hZ])
        intro g hg
        exact right_step hK hR X _ x (dsigW_smooth hR hy b hb') (ih hb') (hb Y (by simp)) g hg
    induction a with
    | nil => exact hRw
    | cons Y a ih =>
      have ha' : ∀ Z ∈ a, B.inLie k r Z := fun Z hZ => ha Z (by simp [hZ])
      intro g hg
      exact left_step hK hR X _ _ (dsigW_smooth hR hx a ha') (ih ha') (ha Y (by simp)) g hg

end GlobalTheory.CoeffDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriRaisingSubmoduleGlSucc
section
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory.WigSh

theorem exists_splitCasimir_std (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) :
    ∃ Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), ∀ y b, Om y b = ∑ c, E c b (y c) := by
  refine ⟨(WithLp.linearEquiv 2 ℂ (Fin (n + 1) → V)).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun b => ∑ c, E c b ∘ₗ LinearMap.proj c) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (n + 1) → V)).toLinearMap, ?_⟩
  intro y b
  simp [LinearMap.sum_apply]

theorem pieri_step_raise : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ j, L j ≠ L l + 1) → ∃ S : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), Stab Et S ∧ S ≠ ⊥ ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' → S' = ⊥ ∨ S' = S) ∧ S ≤ CapSp Et (shf β (Function.update L l (L l + 1))) ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → S.starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by
  intro V _ _ _ n E Et β L l hyp hadj hEt hL
  obtain ⟨Om, hOm⟩ := exists_splitCasimir_std V n E
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.splitCasimir_eigenspace_irreducible_standard V n E Et Om β L l hyp hadj hEt hOm
  have h4 := _root_.GlobalTheory.starProjection_splitCasimirStd_last V n E Et Om β L l hyp hadj hEt hOm
  refine ⟨_, h1, ?_, h2, h3, h4⟩
  intro hbot
  have hbox : Box L (fun j : Fin n => L j.castSucc) := fun j =>
    ⟨hyp.anti (Fin.castSucc_lt_succ), le_rfl⟩
  have hne := (Formalism.FourierDecayAlt.P.branching_decomposition V n E β L hyp).1 _ hbox
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h5 := h4 _ v hv
  have hw := (wigner_extreme_ne_zero n L l hyp.anti).1 hL
  have hmem := Submodule.starProjection_apply_mem (Module.End.eigenspace Om (β + L l + 0))
    (PiLp.single 2 (Fin.last n) v)
  have hz : (Module.End.eigenspace Om (β + L l + 0)).starProjection
      (PiLp.single 2 (Fin.last n) v) = 0 := (Submodule.eq_bot_iff _).1 hbot _ hmem
  rw [hz] at h5
  have h6 : ((wP L (fun j : Fin n => L j.castSucc) l : ℝ) : ℂ) • v = 0 := by
    rw [← h5]; rfl
  rcases smul_eq_zero.1 h6 with h | h
  · exact hw (by exact_mod_cast h)
  · exact hv0 h

end GlobalTheory.WigSh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorBesselTransfer
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem map_sum_of_add_on_sm {k r : ℕ} (R : Rep k r) {Wp : Type} [AddCommGroup Wp] [Module ℂ Wp] (l : R.H → Wp)
    (hadd : ∀ v ∈ R.sm, ∀ w ∈ R.sm, l (v + w) = l v + l w) (hsmul : ∀ (a : ℂ), ∀ v ∈ R.sm, l (a • v) = a • l v)
    {α : Type} (s : Finset α) (f : α → R.H) (hf : ∀ i, f i ∈ R.sm) : l (∑ i ∈ s, f i) = ∑ i ∈ s, l (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (0 : R.H) ∈ R.sm := R.smSub.zero_mem
    simpa using hsmul 0 0 h0
  | insert a s ha ih =>
    have hs : ∑ i ∈ s, f i ∈ R.sm := R.smSub.sum_mem fun i _ => hf i
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd _ (hf a) _ hs, ih]

theorem herm_smul_eq_sum_of_tensRaw : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (om : ι → ℂ) (l : R.H → Wp) (lI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → TensRaw ρ R RI io pr → (∀ v ∈ R.sm, ∀ w ∈ R.sm, l (v + w) = l v + l w) → (∀ (a : ℂ), ∀ v ∈ R.sm, l (a • v) = a • l v) → (∀ I, ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = β I • lI I y) → ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a) om • l (R.σ g w) = ∑ I, β I • lI I ((RI I).σ g (∑ c, pr I c (tm R a w c))) := by
  intro hK k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI Wp _ _ _ _ om l lI β hR hRI hT hadd hsmul hl a w hw g hg
  have hσw : R.σ g w ∈ R.sm := (rep_basic_of_isDS hK k r ε mu R hR).2.2.2.1 g hg w hw
  have htm : ∀ c, tm R a w c ∈ R.sm := fun c => R.smSub.smul_mem (a c) hw
  have hact : ∀ c, act ρ R g (tm R a w) c = (ρ g *ᵥ a) c • R.σ g w := by
    intro c
    simp only [act, tm, map_smul, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  have hx : ∀ c, act ρ R g (tm R a w) c ∈ R.sm := fun c => by
    rw [hact]; exact R.smSub.smul_mem _ hσw
  set y : ∀ I, (RI I).H := fun I => (RI I).σ g (∑ c, pr I c (tm R a w c)) with hy
  have hyeq : ∀ I, ∑ c, pr I c (act ρ R g (tm R a w) c) = y I := fun I => hT.pr_eq I g hg _ htm
  have hysm : ∀ I, y I ∈ (RI I).sm := fun I => by
    rw [← hyeq]
    exact (RI I).smSub.sum_mem fun c _ => (hT.pr_sm I c).mem _ (hx c)
  have hdec : ∀ c, ∑ I, io I c (y I) = (ρ g *ᵥ a) c • R.σ g w := fun c => by
    rw [← hact, ← hT.sum_io_pr _ hx c]
    simp only [hyeq]
  have hev : ∀ I, ev Γ R om (fun c => io I c (y I)) ∈ R.sm := fun I =>
    R.smSub.sum_mem fun i _ => R.smSub.sum_mem fun j _ => R.smSub.smul_mem _ ((hT.io_sm I j).mem _ (hysm I))
  have hsum : ∑ I, ev Γ R om (fun c => io I c (y I)) = Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a) om • R.σ g w := by
    simp only [ev]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ I, ∑ j, (star (om i) * Γ i j) • io I j (y I)
        = ∑ j, (star (om i) * Γ i j * (ρ g *ᵥ a) j) • R.σ g w := fun i => by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.smul_sum, hdec, smul_smul]
    simp only [this, ← Finset.sum_smul]
    congr 1
    generalize ρ g *ᵥ a = b
    simp only [Formalism.QuantumDeterminants.herm, Matrix.mulVec, dotProduct, Finset.mul_sum, Pi.star_apply, mul_assoc]
  rw [← hsmul _ _ hσw, ← hsum, map_sum_of_add_on_sm R l hadd hsmul _ _ hev]
  exact Finset.sum_congr rfl fun I _ => hl I _ (hysm I)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WigMapComp
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem wigMap_comp : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (V₃ : Type) [NormedAddCommGroup V₃] [InnerProductSpace ℂ V₃] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π₁ : Mx k r → (V₁ →L[ℂ] V₁)) (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (π₃ : Mx k r → (V₃ →L[ℂ] V₃)) (d e : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (V₂ →L[ℂ] V₁)) (A' : (Fin (2 * r + k + 1) → ℂ) → (V₃ →L[ℂ] V₂)), GlobalTheory.WigSh.WigMap k r z π₂ π₁ d A → GlobalTheory.WigSh.WigMap k r z π₃ π₂ e A' → GlobalTheory.WigSh.WigMap k r z π₃ π₁ (d + e) (fun ω => (A ω).comp (A' ω)) := by
  intro V₁ _ _ V₂ _ _ V₃ _ _ k r z π₁ π₂ π₃ d e A A' hA hA'
  obtain ⟨⟨t, q, L, hq, hL⟩, h2, h3, h4⟩ := hA
  obtain ⟨⟨t', q', L', hq', hL'⟩, h2', h3', h4'⟩ := hA'
  refine ⟨⟨t * t', fun i => q (finProdFinEquiv.symm i).1 * q' (finProdFinEquiv.symm i).2,
    fun i => (L (finProdFinEquiv.symm i).1).comp (L' (finProdFinEquiv.symm i).2), ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i
    exact (MvPolynomial.totalDegree_mul _ _).trans (add_le_add (hq _) (hq' _))
  · intro ω
    rw [Equiv.sum_comp finProdFinEquiv.symm (fun p : Fin t × Fin t' =>
      MvPolynomial.eval (Sum.elim ω (fun j => star (ω j))) (q p.1 * q' p.2) • (L p.1).comp (L' p.2)),
      Fintype.sum_prod_type]
    show (A ω).comp (A' ω) = _
    rw [hL ω, hL' ω]
    ext x
    simp only [ContinuousLinearMap.comp_apply, sum_apply, ContinuousLinearMap.smul_apply,
      map_sum, map_smul, Finset.smul_sum, map_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_comm, smul_smul]
  · intro h hh ω
    show ((A (h *ᵥ ω)).comp (A' (h *ᵥ ω))).comp (π₃ h) = (π₁ h).comp ((A ω).comp (A' ω))
    rw [ContinuousLinearMap.comp_assoc, h2' h hh, ← ContinuousLinearMap.comp_assoc, h2 h hh,
      ContinuousLinearMap.comp_assoc]
  · intro s ω
    show (A ((s : ℂ) • ω)).comp (A' ((s : ℂ) • ω)) = ((s : ℂ) ^ (d + e)) • (A ω).comp (A' ω)
    rw [h3, h3', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul, pow_add]
  · intro ω hω hz
    show ‖(A ω).comp (A' ω)‖ ^ 2 ≤ _
    have a := h4 ω hω hz
    have b := h4' ω hω hz
    calc ‖(A ω).comp (A' ω)‖ ^ 2 ≤ (‖A ω‖ * ‖A' ω‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.opNorm_comp_le _ _) 2
      _ = ‖A ω‖ ^ 2 * ‖A' ω‖ ^ 2 := mul_pow _ _ _
      _ ≤ _ := by
          rw [pow_add]
          exact mul_le_mul a b (sq_nonneg _) ((sq_nonneg _).trans a)

end GlobalTheory.WigSh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WigMapZeroOfContraction
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh


open Matrix in
theorem _root_.GlobalTheory.WigSh.wigMap_zero_of_contraction : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π₁ : _root_.Formalism.FourierDecayAlt.Q.Mx k r → (V₁ →L[ℂ] V₁)) (π₂ : _root_.Formalism.FourierDecayAlt.Q.Mx k r → (V₂ →L[ℂ] V₂)) (φ : V₂ →L[ℂ] V₁), (∀ v, ‖φ v‖ ≤ ‖v‖) → (∀ h ∈ _root_.Formalism.QuantumDeterminants.UWset k r z, ∀ v, φ (π₂ h v) = π₁ h (φ v)) → _root_.GlobalTheory.WigSh.WigMap k r z π₂ π₁ 0 (fun _ => φ) := by
  intro V₁ _ _ V₂ _ _ k r z π₁ π₂ φ hφ heqv
  refine ⟨⟨1, fun _ => 1, fun _ => φ, fun _ => by simp, fun ω => by simp⟩,
    fun h hh ω => ?_, fun t ω => by simp, fun ω _ _ => ?_⟩
  · ext v
    exact heqv h hh v
  · have hle : ‖φ‖ ≤ 1 := φ.opNorm_le_bound zero_le_one (fun v => by simpa using hφ v)
    rw [pow_zero]
    exact pow_le_one₀ (norm_nonneg _) hle

end GlobalTheory.WigSh
end

