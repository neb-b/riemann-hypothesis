module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0165
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockExistsUniqueGaussianVector
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOperatorLowestWeightHolomorphicKType
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JointHarm.KTypeOp

theorem star_mem_K {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) :
    kᴴ ∈ Formalism.REAL.Kset ε := by
  refine ⟨Unitary.star_mem hk.1, ?_⟩
  have hJ : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a = true <;> simp [h]
  have := congrArg Matrix.conjTranspose hk.2
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ] at this
  exact this.symm

theorem mul_mem_K {n : ℕ} {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.REAL.Kset ε)
    (hb : b ∈ Formalism.REAL.Kset ε) : a * b ∈ Formalism.REAL.Kset ε := by
  refine ⟨mul_mem ha.1 hb.1, ?_⟩
  rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]

theorem exists_op_of_isTau {n : ℕ} {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : GlobalTheory.Dec.IsTau ε abelian₂ τ w)
    {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
    {π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P} (hπ : IsHolRep ε B π) :
    ∃ T : W →ₗ[ℂ] Module.End ℂ P, (∀ s, T s ∈ Submodule.span ℂ (π '' Formalism.REAL.Kset ε)) ∧
      ∀ y, IsBottom ε π (-abelian₂) y → T w y = y ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ s, T (τ k s) y = π k (T s y) := by
  obtain ⟨hτ, hbw⟩ := isHolRep_of_isTau h
  obtain ⟨-, ⟨h1, hm⟩, -, ha, hirr, hw, -, -⟩ := h
  have KC := @GlobalTheory.Dec.TauExt.mem_KC n ε
  let Φ : (Formalism.REAL.Kset ε →₀ ℂ) →ₗ[ℂ] W := Finsupp.linearCombination ℂ fun k => τ k.1 w
  let Ψ : (Formalism.REAL.Kset ε →₀ ℂ) →ₗ[ℂ] Module.End ℂ P := Finsupp.linearCombination ℂ fun k => π k.1
  have hΦ : ∀ k a, Φ (Finsupp.single k a) = a • τ k.1 w := fun k a => Finsupp.linearCombination_single _ _ _
  have hΨ : ∀ k a, Ψ (Finsupp.single k a) = a • π k.1 := fun k a => Finsupp.linearCombination_single _ _ _
  have hmul : ∀ a ∈ Formalism.REAL.Kset ε, ∀ b ∈ Formalism.REAL.Kset ε, τ a (τ b w) = τ (a * b) w := fun a ha' b hb => by
    rw [hm a (KC ha') b (KC hb)]; rfl
  have hw1 : Φ (Finsupp.single ⟨1, GlobalTheory.Dec.TauExt.one_mem_K⟩ 1) = w := by
    rw [hΦ, one_smul, h1]; rfl
  have hsurj : LinearMap.range Φ = ⊤ := by
    refine (hirr _ ?_).resolve_left fun h0 => ?_
    · rintro g hg _ ⟨c, rfl⟩
      induction c using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
      | single k a => exact ⟨Finsupp.single ⟨g * k.1, mul_mem_K hg k.2⟩ a, by rw [hΦ, hΦ, map_smul, hmul g hg _ k.2]⟩
    · have : w ∈ LinearMap.range Φ := ⟨_, hw1⟩
      rw [h0, Submodule.mem_bot] at this
      simp [this] at hw
  obtain ⟨R, hR⟩ := Φ.exists_rightInverse_of_surjective hsurj
  have hR' : ∀ s, Φ (R s) = s := fun s => LinearMap.congr_fun hR s
  refine ⟨Ψ ∘ₗ R, fun s => ?_, fun y hy => ?_⟩
  · rw [Set.image_eq_range, ← Finsupp.range_linearCombination]
    exact ⟨R s, rfl⟩
  have gram0 : ∀ k k' : Formalism.REAL.Kset ε, B (π k.1 y) (π k'.1 y) = B y y * ⟪τ k.1 w, τ k'.1 w⟫_ℂ := by
    intro k k'
    have hk := star_mem_K k.2
    have e := GlobalTheory.T.lowestWeight_matrixCoefficient_depends_on_weight n ε (-abelian₂) P B π W (innerₛₗ ℂ) (fun g => (τ g : W →ₗ[ℂ] W)) y y w w hπ hτ hy hy
      hbw hbw _ (mul_mem_K hk k'.2)
    have hww : innerₛₗ ℂ w w = 1 := by
      rw [innerₛₗ_apply_apply, inner_self_eq_norm_sq_to_K, hw]; simp
    rw [hww, mul_one] at e
    rw [hπ.2.2.2.1 _ (KC k.2), ha _ (KC k.2), hmul _ hk _ k'.2, ← Module.End.mul_apply,
      ← hπ.2.2.1 _ (KC hk) _ (KC k'.2), e]
    rfl
  have gram : ∀ c c', B (Ψ c y) (Ψ c' y) = B y y * ⟪Φ c, Φ c'⟫_ℂ := by
    intro c c'
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb, inner_add_left, mul_add]
    | single k a =>
      induction c' using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb, inner_add_right, mul_add]
      | single k' a' =>
        simp only [hΦ, hΨ, LinearMap.smul_apply, map_smul, LinearMap.map_smulₛₗ, inner_smul_left, inner_smul_right,
          gram0, smul_eq_mul]
        ring
  have key : ∀ c, Ψ (R (Φ c)) y = Ψ c y := by
    intro c
    have := gram (R (Φ c) - c) (R (Φ c) - c)
    rw [map_sub Φ, hR', sub_self, inner_zero_left, mul_zero] at this
    have := hπ.1 _ this
    rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
  refine ⟨?_, fun g hg s => ?_⟩
  · rw [LinearMap.comp_apply, ← hw1, key, hΨ, one_smul, hπ.2.1]; rfl
  · obtain ⟨c, rfl⟩ : s ∈ LinearMap.range Φ := hsurj ▸ Submodule.mem_top
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
    | single k a =>
      have e : τ g (Φ (Finsupp.single k a)) = Φ (Finsupp.single ⟨g * k.1, mul_mem_K hg k.2⟩ a) := by
        rw [hΦ, hΦ, map_smul, hmul g hg _ k.2]
      rw [e, LinearMap.comp_apply, LinearMap.comp_apply, key, key, hΨ, hΨ, hπ.2.2.1 _ (KC hg) _ (KC k.2)]
      simp

theorem exists_op : ∀ (n : ℕ) (ε : Fin n → Bool) (abelian₂ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H), IsURepOn (Formalism.REAL.Kset ε) σ → IsKTypeOf ε σ abelian₂ S → ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P), IsHolRep ε B π → ∃ (w : S) (T : S →ₗ[ℂ] Module.End ℂ P), w ≠ 0 ∧ (∀ s, T s ∈ Submodule.span ℂ (π '' Formalism.REAL.Kset ε)) ∧ ∀ y, IsBottom ε π (-abelian₂) y → T w y = y ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' y = π (k.map star) (T s y) := by
  intro n ε abelian₂ H _ _ σ S hσ hS P _ _ B π hπ
  obtain ⟨v, hvS, hv0, hv⟩ := hS.2.2.2.1
  let w : S := ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, S.smul_mem _ hvS⟩
  have hw : ‖w‖ = 1 := by
    have : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
    show ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1
    rw [norm_smul]; simp [this]
  have hwt : IsWtOn (Formalism.REAL.Kset ε) σ abelian₂ (w : H) := fun θ hθ => by
    show σ _ (_ • v) = _ • _ • v
    rw [map_smul, hv θ hθ, smul_comm]
  obtain ⟨τ, hτ, hτσ⟩ := GlobalTheory.Dec.TauExt.tauExists n ε abelian₂ H σ S w hσ hS hw hwt
  obtain ⟨T, hT1, hT2⟩ := exists_op_of_isTau hτ hπ
  refine ⟨w, T, fun h0 => by simp [h0] at hw, hT1, fun y hy => ⟨(hT2 y hy).1, fun k hk s s' hs => ?_⟩⟩
  have hk' := GlobalTheory.Dec.TauExt.conj_mem hk
  rw [← (hT2 y hy).2 _ hk' s]
  congr 2
  apply Subtype.ext
  rw [hτσ _ hk', GlobalTheory.Dec.TauExt.conj_conj, hs]

end GlobalTheory.JointHarm.KTypeOp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOscillatorRepresentationUnitaryCover
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

variable {P Q : ℕ}

def gauss (F : Fock (Ix P Q)) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef) (x : Ix P Q → ℂ) : F.H :=
  (_root_.GlobalTheory.FockGauss.existsUnique_gauss P Q F A x h).exists.choose

theorem hasCoeff_gauss (F : Fock (Ix P Q)) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef)
    (x : Ix P Q → ℂ) : HasCoeff F (gauss F h x) (expPS (gaussPoly A x)) :=
  (_root_.GlobalTheory.FockGauss.existsUnique_gauss P Q F A x h).exists.choose_spec

theorem gauss_congr (F : Fock (Ix P Q)) {A B : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef)
    (h' : (1 - Bᴴ * B).PosDef) {x y : Ix P Q → ℂ} (e : A = B) (e' : x = y) : gauss F h x = gauss F h' y := by
  subst e e'; rfl

abbrev Par (P Q : ℕ) : Type :=
  ℂ × {Y : Matrix (Ix P Q) (Fin Q) ℂ // IsNeg Y} × (Ix P Q → ℂ) × (Ix P Q → ℂ)

def vec (F : Fock (Ix P Q)) (p : Par P Q) : F.H :=
  (p.1 * scal p.2.1.1 p.2.2.1 p.2.2.2) • gauss F p.2.1.2.posDef (linX p.2.1.1 p.2.2.1 p.2.2.2)

def act (T0 : GrpData P Q) (g : T0.G) (p : Par P Q) : Par P Q :=
  ((T0.sq g : ℂˣ) * p.1, ⟨(T0.cov g : Mat P Q) * p.2.1.1, p.2.1.2.mul (T0.cov_mem g)⟩,
    (T0.cov g : Mat P Q) *ᵥ p.2.2.1, p.2.2.2 ᵥ* (T0.cov g⁻¹ : Mat P Q))

def base (c : ℂ) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef) (x : Ix P Q → ℂ) : Par P Q :=
  (c, ⟨baseY A, isNeg_baseY h⟩, baseV x, baseF x)

theorem vec_base (F : Fock (Ix P Q)) (c : ℂ) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef)
    (x : Ix P Q → ℂ) : vec F (base c h x) = c • gauss F h x := by
  simp only [vec, base, scal_base, mul_one]
  rw [gauss_congr F _ h (matA_baseY A) (linX_base A x)]

theorem inner_vec (F : Fock (Ix P Q)) (p q : Par P Q) :
    inner ℂ (vec F p) (vec F q) = star p.1 * q.1 * ker p.2.1.1 p.2.2.1 p.2.2.2 q.2.1.1 q.2.2.1 q.2.2.2 := by
  obtain ⟨c, ⟨Y, hY⟩, v, φ⟩ := p
  obtain ⟨c', ⟨Y', hY'⟩, v', φ'⟩ := q
  have h1 := GlobalTheory.T.inner_gaussianVectors_fockSpace P Q F _ _ _ _ hY.posDef hY'.posDef _ _
    (hasCoeff_gauss F hY.posDef (linX Y v φ)) (hasCoeff_gauss F hY'.posDef (linX Y' v' φ'))
  have h2 := GlobalTheory.T.gaussian_inner_eq_invariantKernel P Q Y Y' v φ v' φ' hY.isUnit hY'.isUnit (GlobalTheory.T.isUnit_det_one_sub_conjTranspose_mul_contractions P Q _ _ hY.posDef hY'.posDef)
  simp only at h1 h2 ⊢
  simp only [vec, inner_smul_left, inner_smul_right, h1, ← h2, map_mul, starRingEnd_apply]
  ring

theorem isUnit_form {Y Y' : Matrix (Ix P Q) (Fin Q) ℂ} (h : IsNeg Y) (h' : IsNeg Y') :
    IsUnit (Yᴴ * Jm P Q * Y').det := by
  have h1 : IsUnit (-(Yᴴ * Jm P Q * Y')).det := by
    rw [form_factor Y Y' h.isUnit h'.isUnit, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    exact (h.isUnit.star.mul (GlobalTheory.T.isUnit_det_one_sub_conjTranspose_mul_contractions P Q _ _ h.posDef h'.posDef)).mul h'.isUnit
  rw [Matrix.det_neg] at h1
  exact isUnit_of_mul_isUnit_right h1

theorem dense_vec (F : Fock (Ix P Q)) : Dense (Submodule.span ℂ (Set.range (vec F)) : Set F.H) := by
  have h0 : (1 - (0 : Matrix (Fin P) (Fin Q) ℂ)ᴴ * (0 : Matrix (Fin P) (Fin Q) ℂ)).PosDef := by
    simpa using Matrix.PosDef.one
  refine (_root_.GlobalTheory.dense_span_coherent P Q F (gauss F h0) (hasCoeff_gauss F h0)).mono (Submodule.span_mono ?_)
  rintro _ ⟨x, rfl⟩
  exact ⟨base 1 h0 x, by rw [vec_base, one_smul]⟩

theorem exists_rep (T0 : GrpData P Q) (F : Fock (Ix P Q)) :
    ∃ π : T0.G →* (F.H →L[ℂ] F.H), (∀ g x, ‖π g x‖ = ‖x‖) ∧ (∀ x, Continuous fun g => π g x) ∧
      ∀ g p, π g (vec F p) = vec F (act T0 g p) := by
  have hc : Continuous fun g : T0.G => (T0.cov g : Mat P Q) :=
    Units.continuous_val.comp (continuous_fst.comp T0.emb.continuous)
  refine _root_.GlobalTheory.TotalFamilyRep.exists_rep T0.G (Par P Q) F.H (act T0) (vec F) (fun p => ?_) (fun g h p => ?_) (dense_vec F)
    (fun g p q => ?_) (fun p q => ?_)
  · simp [act]
  · simp [act, mul_assoc, Matrix.mul_assoc]
  · rw [inner_vec, inner_vec]
    simp only [act]
    rw [ker_mul (T0.cov_mem g) (by rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])]
    have h : star ((T0.sq g : ℂˣ) : ℂ) * (T0.sq g : ℂˣ) = 1 := by
      rw [Complex.star_def, Complex.conj_mul', RealPar.Cover.norm_sq]; simp
    rw [star_mul']
    linear_combination (star p.1 * q.1 * ker p.2.1.1 p.2.2.1 p.2.2.2 q.2.1.1 q.2.2.1 q.2.2.2) * h
  · simp only [inner_vec]
    refine (continuous_const.mul (RealPar.Cover.continuous_sq.mul continuous_const)).mul
      (GlobalTheory.T.continuous_oscillatorGaussianKernel_right P Q T0.G _ _ _ _ _ _ ?_ ?_ ?_ fun g => isUnit_form q.2.1.2 (act T0 g p).2.1.2)
    · exact hc.matrix_mul continuous_const
    · exact hc.matrix_mulVec continuous_const
    · exact continuous_const.matrix_vecMul (hc.comp continuous_inv)

theorem hasDerivAt_exp_entry (X : Mat P Q) (a b : Ix P Q) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) a b) (X a b) 0 := by
  open scoped Matrix.Norms.Operator in
  have h2 := ((Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

theorem expt_inv (T0 : GrpData P Q) {Z : Mat P Q} (hZ : Z ∈ upq P Q) (t : ℝ) :
    (T0.expt (t • Z))⁻¹ = T0.expt (t • -Z) := by
  rw [inv_eq_iff_mul_eq_one, smul_neg, ← neg_smul, ← T0.expt_add Z hZ, add_neg_cancel, zero_smul, T0.expt_zero]

theorem neg_mem_upq {Z : Mat P Q} (hZ : Z ∈ upq P Q) : -Z ∈ upq P Q := by
  simpa using RealPar.KStabLie.smul_mem_upq hZ (-1)

theorem adjZ_neg {Z : Mat P Q} (hZ : Z ∈ upq P Q) : adjZ (-Z) = Z := by
  have h : Zᴴ * Jm P Q = -(Jm P Q * Z) := eq_neg_of_add_eq_zero_left hZ
  rw [adjZ, Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, h, Matrix.mul_neg, neg_neg,
    ← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]

theorem hasDerivAt_inner_act (T0 : GrpData P Q) (F : Fock (Ix P Q)) {Z : Mat P Q} (hZ : Z ∈ upq P Q)
    (f : MvPolynomial (Ix P Q) ℂ) (c : ℂ) {A : Matrix (Fin P) (Fin Q) ℂ} (h : (1 - Aᴴ * A).PosDef)
    (x : Ix P Q → ℂ) :
    HasDerivAt (fun t : ℝ => inner ℂ (F.ι f) (vec F (act T0 (T0.expt (t • Z)) (base c h x))))
      (inner ℂ (F.ι (omAct0 P Q (adjZ Z) f)) (vec F (base c h x))) 0 := by
  set g : ℝ → Mat P Q := fun t => (T0.cov (T0.expt (t • Z)) : Mat P Q) with hg
  set g' : ℝ → Mat P Q := fun t => (T0.cov (T0.expt (t • Z))⁻¹ : Mat P Q) with hg'
  have g0 : g 0 = 1 := by simp [hg, T0.expt_zero]
  have g0' : g' 0 = 1 := by simp [hg', T0.expt_zero]
  obtain ⟨hA, hx, hs⟩ := _root_.GlobalTheory.OscGauss.ParDer.par_deriv P Q A x Z g g' g0 g0'
    (fun a b => by
      simpa only [hg, T0.expt_cov _ (RealPar.KStabLie.smul_mem_upq hZ _)] using hasDerivAt_exp_entry Z a b)
    (fun a b => by
      simpa only [hg', expt_inv T0 hZ, T0.expt_cov _ (RealPar.KStabLie.smul_mem_upq (neg_mem_upq hZ) _), Matrix.neg_apply] using
        hasDerivAt_exp_entry (-Z) a b)
  have hn : ∀ t, IsNeg (g t * baseY A) := fun t => (isNeg_baseY h).mul (T0.cov_mem _)
  have hp := _root_.GlobalTheory.OscPairDer.hasDerivAt_inner_gauss P Q F _ _ (fun t => gauss F (hn t).posDef
    (linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t))) _ _ (fun t => hasCoeff_gauss F _ _) hA hx f
  have e0 : gauss F (hn 0).posDef (linX (g 0 * baseY A) (g 0 *ᵥ baseV x) (baseF x ᵥ* g' 0)) = gauss F h x :=
    gauss_congr F _ _ (by rw [g0, Matrix.one_mul, matA_baseY])
      (by rw [g0, g0', Matrix.one_mul, Matrix.one_mulVec, Matrix.vecMul_one, linX_base])
  obtain ⟨a1, a2⟩ := GlobalTheory.T.gaussianVector_annihilator_equations P Q F A x _ (hasCoeff_gauss F h x)
  have h5 := ((((RealPar.Cover.hasDerivAt_sq (T := T0) hZ).mul_const c).fun_mul hs).fun_mul hp)
  simp only [vec_base, inner_smul_right, GlobalTheory.T.inner_lieAction_adjoint_gaussian_polynomial P Q F A x _ a1 a2 Z f]
  simp only [vec, inner_smul_right]
  refine h5.congr_deriv ?_
  simp only [e0]
  simp only [g0, g0', Matrix.one_mul, Matrix.one_mulVec, Matrix.vecMul_one, scal_base, zero_smul, T0.expt_zero,
    map_one, Units.val_one]
  ring

theorem exists_isOsc (P Q : ℕ) (T0 : GrpData P Q) (F : Fock (Ix P Q)) :
    ∃ Om : T0.G →* (F.H →L[ℂ] F.H), IsOsc T0 F Om := by
  obtain ⟨π, h1, h2, h3⟩ := exists_rep T0 F
  refine ⟨π, h1, h2, fun Z hZ f => ?_⟩
  refine GlobalTheory.T.hasDerivAt_of_weak_deriv_on_invariant_total_set F.H (fun t => π (T0.expt (t • Z))) (Set.range (vec F)) _ _ ?_ (fun s t => ?_) (fun t => h1 _)
    (fun y => (h2 y).comp (T0.expt_cont.comp_continuous (by fun_prop)
      fun t => RealPar.KStabLie.smul_mem_upq hZ t)) (dense_vec F) ?_ ?_
  · simp [T0.expt_zero]
  · simp only [T0.expt_add Z hZ, map_mul]
  · rintro t _ ⟨p, rfl⟩
    exact ⟨_, (h3 _ p).symm⟩
  · rintro _ ⟨p, rfl⟩
    have e : vec F p = vec F (base (p.1 * scal p.2.1.1 p.2.2.1 p.2.2.2) p.2.1.2.posDef
      (linX p.2.1.1 p.2.2.1 p.2.2.2)) := by rw [vec_base, vec]
    have h4 := hasDerivAt_inner_act T0 F (neg_mem_upq hZ) f (p.1 * scal p.2.1.1 p.2.2.1 p.2.2.2) p.2.1.2.posDef
      (linX p.2.1.1 p.2.2.1 p.2.2.2)
    simp only [← h3, ← e, adjZ_neg hZ] at h4
    refine h4.congr_of_eventuallyEq (.of_forall fun t => ?_)
    have iso := (⟨(π (T0.expt (t • Z)) : F.H →ₗ[ℂ] F.H), h1 _⟩ : F.H →ₗᵢ[ℂ] F.H).inner_map_map (F.ι f)
      (π (T0.expt (t • -Z)) (vec F p))
    simp only [← iso]
    change _ = inner ℂ (π _ _) (π _ (π _ _))
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← expt_inv T0 hZ, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]

end GlobalTheory.OscGauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.QCoh

theorem exists_isIrreducible_inter_open_subset {α : Type*} [TopologicalSpace α] [NoetherianSpace α]
    {T : Set α} (hT : IsClosed T) (hne : T.Nonempty) :
    ∃ Z : Set α, IsClosed Z ∧ IsIrreducible Z ∧ Z ⊆ T ∧
      ∃ U : Set α, IsOpen U ∧ (∃ x ∈ T, x ∈ U) ∧ T ∩ U ⊆ Z := by
  classical
  obtain ⟨S, hS, hc, hi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  have hSne : S.Nonempty := by
    obtain ⟨x, t, ht, -⟩ := hne
    exact ⟨t, ht⟩
  obtain ⟨Z, hZ⟩ := hS.exists_maximal hSne
  have hfin : (S \ {Z}).Finite := hS.diff
  refine ⟨Z, hc Z hZ.1, hi Z hZ.1, Set.subset_sUnion_of_mem hZ.1, (⋃₀ (S \ {Z}))ᶜ, ?_, ?_, ?_⟩
  · rw [isOpen_compl_iff, Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion fun t ht => hc t ht.1
  · by_contra h
    have hsub : Z ⊆ ⋃₀ (hfin.toFinset : Set (Set α)) := fun x hx => by
      rw [hfin.coe_toFinset]
      by_contra hx'
      exact h ⟨x, Set.subset_sUnion_of_mem hZ.1 hx, hx'⟩
    obtain ⟨z, hz, hZz⟩ := isIrreducible_iff_sUnion_isClosed.1 (hi Z hZ.1) hfin.toFinset
      (fun z hz => hc z (hfin.mem_toFinset.1 hz).1) hsub
    have hz' := hfin.mem_toFinset.1 hz
    exact hz'.2 (le_antisymm (hZ.2 hz'.1 hZz) hZz)
  · rintro x ⟨⟨t, ht, hxt⟩, hx⟩
    by_contra hxZ
    exact hx ⟨t, ⟨ht, fun e => hxZ ((show t = Z from e) ▸ hxt)⟩, hxt⟩

variable {X : Scheme.{0}}

theorem exists_pow_vanishingIdeal_le_annihilator [IsLocallyNoetherian X] (F : X.Modules)
    [IsFiniteQC F] (Z : Closeds X) (W : X.affineOpens) (h : support F ∩ W.1 ⊆ Z) :
    ∃ k : ℕ, (Scheme.IdealSheafData.vanishingIdeal Z).ideal W ^ k ≤
      Module.annihilator Γ(X, W.1) Γ(F, W.1) := by
  have := finite_sections F W.2
  have : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, ← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
    ← Module.support_eq_zeroLocus, ← fromSpec_preimage_support F W.2]
  refine PrimeSpectrum.vanishingIdeal_anti_mono fun p hp => h ⟨hp, ?_⟩
  exact W.2.range_fromSpec.le ⟨p, rfl⟩

theorem pow_le_annihilator_kernel_unit (I : X.IdealSheafData) (E : X.Modules) [E.IsQuasicoherent]
    (W : X.affineOpens) {k : ℕ}
    (h : I.ideal W ^ (k + 1) ≤ Module.annihilator Γ(X, W.1) Γ(E, W.1)) :
    I.ideal W ^ k ≤ Module.annihilator Γ(X, W.1)
      Γ(kernel ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app E), W.1) := by
  set φ := (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app E with hφ
  intro a ha
  refine Module.mem_annihilator.2 fun t => ?_
  have h₁ : appLinear (kernel.ι φ) W.1 t ∈ (I.ideal W • ⊤ : Submodule Γ(X, W.1) Γ(E, W.1)) := by
    have := (surjective_and_ker_unit_subschemeι I E W).2
    rw [← hφ, ← range_kernel_ι_app] at this
    exact this.le ⟨t, rfl⟩
  have h₂ : ∀ u ∈ (I.ideal W • ⊤ : Submodule Γ(X, W.1) Γ(E, W.1)), a • u = 0 := fun u hu => by
    refine Submodule.smul_induction_on hu (fun r hr n _ => ?_) fun x y hx hy => ?_
    · rw [smul_smul]
      exact Module.mem_annihilator.1 (h (pow_succ (I.ideal W) k ▸ Ideal.mul_mem_mul ha hr)) n
    · rw [smul_add, hx, hy, add_zero]
  refine injective_kernel_ι_app φ W.1 ?_
  change appLinear (kernel.ι φ) W.1 (a • t) = appLinear (kernel.ι φ) W.1 0
  rw [map_smul, map_zero]
  exact h₂ _ h₁

theorem devissage : ∀ (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (P : X.Modules → Prop), (∀ F : X.Modules, IsZero F → P F) → (∀ S : ShortComplex X.Modules, S.ShortExact → IsFiniteQC S.X₁ → IsFiniteQC S.X₃ → P S.X₁ → P S.X₃ → P S.X₂) → (∀ (Z : Closeds X), IsIrreducible (Z : Set X) → (∀ F : X.Modules, IsFiniteQC F → GlobalTheory.QCoh.support F ⊂ (Z : Set X) → P F) → ∀ G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules, IsFiniteQC G → P ((Scheme.Modules.pushforward (redι Z)).obj G)) → ∀ F : X.Modules, IsFiniteQC F → P F := by
  intro X _ P h0 hext hZ
  suffices H : ∀ T : Closeds X, ∀ F : X.Modules, IsFiniteQC F → support F = T → P F from
    fun F hF => H ⟨support F, isClosed_support F⟩ F hF rfl
  intro T
  induction T using WellFoundedLT.induction with
  | ind T ih =>
  intro F hF hT
  have ih' : ∀ E : X.Modules, IsFiniteQC E → support E ⊂ (T : Set X) → P E := fun E hE h =>
    ih ⟨support E, isClosed_support E⟩ h E hE rfl
  rcases (T : Set X).eq_empty_or_nonempty with he | hne
  · exact h0 F (support_eq_empty_iff.1 (hT.trans he))
  obtain ⟨Z, hZc, hZi, hZT, U, hU, ⟨x, hxT, hxU⟩, hUZ⟩ :=
    exists_isIrreducible_inter_open_subset T.isClosed hne
  obtain ⟨W, hW, hxW, hWU⟩ := exists_affine_mem_le (U := ⟨U, hU⟩) x hxU
  let Z' : Closeds X := ⟨Z, hZc⟩
  have hP := hZ Z' hZi fun E hE h => ih' E hE (h.trans_subset hZT)
  obtain ⟨k, hk⟩ := exists_pow_vanishingIdeal_le_annihilator F Z' ⟨W, hW⟩
    fun y hy => hUZ ⟨hT ▸ hy.1, hWU hy.2⟩
  have key : ∀ (k : ℕ) (E : X.Modules), IsFiniteQC E → support E ⊆ T →
      (Scheme.IdealSheafData.vanishingIdeal Z').ideal ⟨W, hW⟩ ^ k ≤
        Module.annihilator Γ(X, W) Γ(E, W) → P E := by
    intro k
    induction k with
    | zero =>
      intro E hE hET h
      refine ih' E hE ⟨hET, fun hle => ?_⟩
      have h₁ := (mem_support_iff_annihilator_le (F := E) hW ⟨x, hxW⟩).1 (hle hxT)
      rw [pow_zero, Ideal.one_eq_top] at h
      exact (hW.primeIdealOf ⟨x, hxW⟩).isPrime.ne_top (top_le_iff.1 (h.trans h₁))
    | succ k ihk =>
      intro E hE hET h
      let G := (Scheme.Modules.pullback (redι Z')).obj E
      let φ : E ⟶ (Scheme.Modules.pushforward (redι Z')).obj G :=
        (Scheme.Modules.pullbackPushforwardAdjunction (redι Z')).unit.app E
      have hepi : Epi φ := (epi_iff_forall_affine φ).2 fun V hV =>
        (surjective_and_ker_unit_subschemeι _ E ⟨V, hV⟩).1
      have hS : (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).ShortExact :=
        { exact := ShortComplex.exact_kernel φ }
      have hK : IsFiniteQC (kernel φ) := inferInstance
      exact hext _ hS hK (IsFiniteQC.of_epi φ)
        (ihk _ hK ((support_subset_of_mono (kernel.ι φ)).trans hET)
          (pow_le_annihilator_kernel_unit _ E ⟨W, hW⟩ h)) (hP G inferInstance)
  exact key k F hF hT.le hk

end GlobalTheory.QCoh
end
end

