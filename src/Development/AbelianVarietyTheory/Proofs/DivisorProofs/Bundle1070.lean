module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0988
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
public import Formalism.PolynomialDimension.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0778
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianModelsConjUnitaryDifferByNorm
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem stdH_mulVec_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ)
    (y : GLw n w) (hy : y ∈ UJ (cj w) 1) (v v' : Fin n → w.adicCompletion E) :
    stdH w (y.val *ᵥ v) (y.val *ᵥ v') = stdH w v v' := by
  have h1 : (cT (cj w) y.val) * 1 * y.val = 1 := hy
  have h2 : (y.val)ᵀ * y.val.map (cj w) = 1 := by
    have := congrArg Matrix.transpose h1
    simpa [cT, Matrix.transpose_mul] using this
  have hs : ∀ z : Fin n → w.adicCompletion E, ∀ z', stdH w z z' = z ⬝ᵥ (fun k => cj w (z' k)) := by
    intro z z'; rfl
  have hc : (fun k => cj w ((y.val *ᵥ v') k)) = y.val.map (cj w) *ᵥ (fun k => cj w (v' k)) := by
    funext k; exact RingHom.map_mulVec (cj w) y.val v' k
  rw [hs, hs, hc, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, h2,
    Matrix.vecMul_one]

theorem isReduced_of_adjoin_squarefree {F A : Type} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (u : A) (hu : Algebra.adjoin F {u} = ⊤) (P : F[X]) (hP : Squarefree P) (hPu : aeval u P = 0) :
    IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨k, hk⟩ := ha
  have hmem : a ∈ Algebra.adjoin F {u} := by rw [hu]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, rfl⟩ := hmem
  have hsq : Squarefree (minpoly F u) := hP.squarefree_of_dvd (minpoly.dvd F u hPu)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  ·
    have h10 : (1 : A) = 0 := by simpa using hk
    exact (subsingleton_of_zero_eq_one h10.symm).elim _ _
  have hd : minpoly F u ∣ p ^ k := minpoly.dvd F u (by rw [map_pow]; exact hk)
  have hd' : minpoly F u ∣ p := (hsq.dvd_pow_iff_dvd hk0.ne').1 hd
  obtain ⟨r, hr⟩ := hd'
  change aeval u p = 0
  rw [hr, map_mul, minpoly.aeval, zero_mul]

theorem model_conj_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (n : ℕ) (Q : (w.adicCompletion E)[X])
    (B : GlobalTheory.UnitLemma.InvAlg K) (u x x' : B.A), Q.Separable → Fits w e B Q u →
    ∀ γ y : GLw n w, y ∈ UL n w → IsModel w e B u x γ → IsModel w e B u x' (y⁻¹ * γ * y) →
    ∃ c : B.Aˣ, x' = x * ((c : B.A) * B.σ (c : B.A)) := by
  intro E _ _ _ w hw K e n Q B u x x' hQ hF γ y hy hM hM'
  obtain ⟨hadj, hroot, -, -⟩ := hF
  have hyU : y ∈ UJ (cj w) 1 := by simpa [UL, hw] using hy
  obtain ⟨ψ, hψs, hψu, hψh⟩ := hM
  obtain ⟨ψ', hψs', hψu', hψh'⟩ := hM'

  let ψ₃ : B.A → (Fin n → w.adicCompletion E) := fun a => y.val *ᵥ ψ' a
  have h3s : ∀ (c : K.E) (a : B.A), ψ₃ (c • a) = e c • ψ₃ a := by
    intro c a; simp only [ψ₃, hψs', Matrix.mulVec_smul]
  have h3u : ∀ a, ψ₃ (u * a) = γ.val *ᵥ ψ₃ a := by
    intro a
    simp only [ψ₃, hψu', Matrix.mulVec_mulVec, Units.val_mul]
    congr 1
    rw [← mul_assoc, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have h3h : ∀ a b, stdH w (ψ₃ a) (ψ₃ b) = e (B.herm x' a b) := by
    intro a b; simp only [ψ₃]; rw [stdH_mulVec_of_mem w n y hyU, hψh']

  let φ : B.A → B.A := fun a => ψ.symm (ψ₃ a)
  have hφψ : ∀ a, ψ (φ a) = ψ₃ a := fun a => ψ.apply_symm_apply _
  have hφs : ∀ (c : K.E) (a : B.A), φ (c • a) = c • φ a := by
    intro c a; apply ψ.injective; rw [hψs, hφψ, hφψ, h3s]
  have hφu : ∀ a, φ (u * a) = u * φ a := by
    intro a; apply ψ.injective; rw [hψu, hφψ, hφψ, h3u]
  have hφadd : ∀ a b, φ (a + b) = φ a + φ b := by
    intro a b; apply ψ.injective; rw [map_add (f := _), hφψ, hφψ, hφψ]; simp [ψ₃, Matrix.mulVec_add]

  have hφmul : ∀ a b, φ (a * b) = a * φ b := by
    intro a
    have ha : a ∈ Algebra.adjoin K.E {u} := by rw [hadj]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem z hz =>
      rw [Set.mem_singleton_iff] at hz; subst hz; exact hφu
    | algebraMap r =>
      intro b; rw [← Algebra.smul_def, ← Algebra.smul_def, hφs]
    | add a₁ a₂ _ _ h₁ h₂ =>
      intro b; rw [add_mul, hφadd, h₁, h₂, add_mul]
    | mul a₁ a₂ _ _ h₁ h₂ =>
      intro b; rw [mul_assoc, h₁, h₂, mul_assoc]
  have hφ : ∀ a, φ a = a * φ 1 := fun a => by rw [← hφmul, mul_one]

  obtain ⟨a₀, ha₀⟩ : ∃ a₀, φ a₀ = 1 := by
    refine ⟨ψ'.symm ((y⁻¹ : GLw n w).val *ᵥ ψ 1), ?_⟩
    apply ψ.injective
    rw [hφψ]
    simp only [ψ₃, AddEquiv.apply_symm_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]
  let c : B.Aˣ := ⟨φ 1, a₀, by rw [mul_comm, ← hφ, ha₀], by rw [← hφ, ha₀]⟩
  refine ⟨c, ?_⟩

  have hh : ∀ a b, B.herm x' a b = B.herm x (φ a) (φ b) := by
    intro a b; apply e.injective; rw [← h3h, ← hψh, hφψ, hφψ]
  have htr : ∀ z : B.A, Algebra.trace K.E B.A ((x * ((c : B.A) * B.σ (c : B.A)) - x') * z) = 0 := by
    intro z
    have := hh z 1
    simp only [GlobalTheory.UnitLemma.InvAlg.herm, map_one, mul_one] at this
    rw [hφ z] at this
    have hc : (c : B.A) = φ 1 := rfl
    rw [hc, sub_mul, map_sub, sub_eq_zero, this]
    congr 1; ring
  haveI : IsReduced B.A := isReduced_of_adjoin_squarefree u hadj _ (hQ.map.squarefree) hroot
  exact (sub_eq_zero.1 (GlobalTheory.RegSS.eq_zero_of_trace_mul_eq_zero _ htr)).symm

end GlobalTheory.KapLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFormFrameExpansion
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.AdExt

section Mat
variable {n : ℕ} {G S x : Matrix (Fin n) (Fin n) ℂ}

theorem conj_form (hx : IsUnit x.det) (h : xᴴ * G * x = S) (A B : Matrix (Fin n) (Fin n) ℂ) :
    (x * A * x⁻¹)ᴴ * G * (x * B * x⁻¹) = x⁻¹ᴴ * (Aᴴ * S * B) * x⁻¹ := by
  rw [← h]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem conj_mem_lie (hx : IsUnit x.det) (h : xᴴ * G * x = S) {Z : Matrix (Fin n) (Fin n) ℂ}
    (hZ : Zᴴ * S + S * Z = 0) : (x * Z * x⁻¹)ᴴ * G + G * (x * Z * x⁻¹) = 0 := by
  have h1 := conj_form hx h Z 1
  have h2 := conj_form hx h 1 Z
  rw [Matrix.mul_one, mul_nonsing_inv _ hx] at h1 h2
  rw [Matrix.mul_one] at h1
  rw [conjTranspose_one, Matrix.one_mul] at h2
  rw [h1, h2, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, hZ]
  simp

theorem conj_mem_unitary (hx : IsUnit x.det) (h : xᴴ * G * x = S) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : Aᴴ * S * A = S) : (x * A * x⁻¹)ᴴ * G * (x * A * x⁻¹) = G := by
  have h2 := conj_form hx h 1 1
  rw [Matrix.mul_one, mul_nonsing_inv _ hx, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one] at h2
  rw [conj_form hx h, hA, ← h2]

theorem diag_unitary (s : Fin n → ℂ) (t : Fin n → ℝ) :
    (diagonal fun c => Complex.exp ((t c : ℂ) * Complex.I))ᴴ * diagonal s *
      (diagonal fun c => Complex.exp ((t c : ℂ) * Complex.I)) = diagonal s := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext c
  have : star (Complex.exp ((t c : ℂ) * Complex.I)) * Complex.exp ((t c : ℂ) * Complex.I) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  simp only [Pi.star_apply]
  linear_combination s c * this

theorem half_mem_lie (hG : Gᴴ = G) (hd : IsUnit G.det) (W : Matrix (Fin n) (Fin n) ℂ) :
    ((1 / 2 : ℂ) • (W + -(G⁻¹ * Wᴴ * G)))ᴴ * G + G * ((1 / 2 : ℂ) • (W + -(G⁻¹ * Wᴴ * G))) = 0 := by
  have e1 : (G⁻¹ * Wᴴ * G)ᴴ * G = G * W := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hG]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul _ hd, Matrix.mul_one]
  have e2 : G * (G⁻¹ * Wᴴ * G) = Wᴴ * G := by
    rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd]
  have e3 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [conjTranspose_smul, e3, smul_mul_assoc, mul_smul_comm, ← smul_add, conjTranspose_add, conjTranspose_neg,
    Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, e1, e2]
  simp

theorem conj_eq_of_mem_lie (hd : IsUnit G.det) {W : Matrix (Fin n) (Fin n) ℂ} (hW : Wᴴ * G + G * W = 0) :
    -(G⁻¹ * Wᴴ * G) = W := by
  rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left hW, Matrix.mul_neg, neg_neg, nonsing_inv_mul_cancel_left _ _ hd]

end Mat

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem atTau_spec (R : RealPoints θ V) (ρ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : gᴴ * gramAt D V ρ * g = gramAt D V ρ) : IsAtTau θ V ρ g (atTau θ V ρ g) := by
  have h : ∃ k, IsAtTau θ V ρ g k := by
    obtain ⟨k, hk, h⟩ := R.2.1 (fun τ => if τ = ρ then g else 1) fun τ => by
      change _ᴴ * _ * _ = _
      split_ifs with c
      · subst c; exact hg
      · simp
    exact ⟨k, hk, by simpa using h ρ, fun τ c => by simpa [c] using h τ⟩
  rw [atTau, dif_pos h]
  exact h.choose_spec

def toLie (R : RealPoints θ V) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {Ψ : Finset (D.host.E →+* ℂ)}
    (σ : D.what₂.Tau → Ψ) : Frame Ψ V.rank →ₗ[ℝ] LieN V where
  toFun Z := fun ρ => ⟨(1 / 2 : ℂ) • (x ρ * mat Z (σ ρ) * (x ρ)⁻¹ + conjAt V ρ (x ρ * mat Z (σ ρ) * (x ρ)⁻¹)),
    half_mem_lie (R.1 ρ).1 (R.1 ρ).2 _⟩
  map_add' Z Z' := funext fun ρ => Subtype.ext (by
    have : mat (Z + Z') (σ ρ) = mat Z (σ ρ) + mat Z' (σ ρ) := rfl
    change (1 / 2 : ℂ) • _ = (1 / 2 : ℂ) • _ + (1 / 2 : ℂ) • _
    simp only [this, conjAt, Matrix.mul_add, Matrix.add_mul, conjTranspose_add]
    module)
  map_smul' c Z := funext fun ρ => Subtype.ext (by
    have : mat (c • Z) (σ ρ) = c • mat Z (σ ρ) := rfl
    change (1 / 2 : ℂ) • _ = c • (1 / 2 : ℂ) • _
    simp only [this, conjAt, mul_smul_comm, smul_mul_assoc, conjTranspose_smul, star_trivial]
    module)

theorem toLie_val (R : RealPoints θ V) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {Ψ : Finset (D.host.E →+* ℂ)}
    (σ : D.what₂.Tau → Ψ) (Z : Frame Ψ V.rank) (ρ : D.what₂.Tau) : (toLie R x σ Z ρ).1 =
    (1 / 2 : ℂ) • (x ρ * mat Z (σ ρ) * (x ρ)⁻¹ + conjAt V ρ (x ρ * mat Z (σ ρ) * (x ρ)⁻¹)) := rfl

theorem toLie_I (R : RealPoints θ V) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {Ψ : Finset (D.host.E →+* ℂ)}
    (σ : D.what₂.Tau → Ψ) (Z : Frame Ψ V.rank) (ρ : D.what₂.Tau) : (toLie R x σ (Complex.I • Z) ρ).1 =
    (Complex.I / 2 : ℂ) • (x ρ * mat Z (σ ρ) * (x ρ)⁻¹ - conjAt V ρ (x ρ * mat Z (σ ρ) * (x ρ)⁻¹)) := by
  have : mat (Complex.I • Z) (σ ρ) = Complex.I • mat Z (σ ρ) := rfl
  rw [toLie_val]
  simp only [this, conjAt, mul_smul_comm, smul_mul_assoc, conjTranspose_smul, Complex.star_def, Complex.conj_I]
  module

theorem fderiv_atPlace (R : RealPoints θ V) {φ : GA D V → ℂ} (g : GA D V)
    (hf : DifferentiableAt ℝ (fun Y : LieN V => φ (g * expInf θ V Y)) 0) (ρ : D.what₂.Tau) (Y : LieAt V ρ) :
    fderiv ℝ (fun Y : LieN V => φ (g * expInf θ V Y)) 0 (atPlace V ρ Y : LieN V) = Rder θ V ρ Y.1 φ g := by
  rw [Rder_eq R]
  have h1 : ∀ Y' : LieN V, HasDerivAt (fun t : ℝ => t • Y') Y' 0 := fun Y' => by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const Y'
  have h2 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (h1 (atPlace V ρ Y)) (zero_smul ℝ _).symm
  exact h2.deriv.symm

theorem mat_unitFr {Ψ : Finset (D.host.E →+* ℂ)} {r : ℕ} (τ τ' : Ψ) (c d : Fin r) :
    mat (unitFr τ c d) τ' = if τ' = τ then Matrix.single c d 1 else 0 := by
  ext a b
  by_cases h : τ' = τ
  · simp [mat, unitFr, h, Matrix.single, eq_comm]
  · simp [mat, unitFr, h]

end GlobalTheory.HolRead.AdExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIndepRangeInc
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.SumSlope

variable {K : Type} [Field K] [NumberField K] {O : Type} [Fintype O] [DecidableEq O] {ι : O → Type}
  [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)]

def sumNorm (Y : ∀ o, (K →+* ℂ) → Matrix (ι o) (ι o) ℂ) (σ : K →+* ℂ) (x : ∀ o, ι o → K) : ℝ :=
  Real.sqrt (∑ o, matNorm (Y o) σ (x o) ^ 2)

abbrev inc (o : O) : (ι o → K) →ₗ[K] (∀ o, ι o → K) := LinearMap.single K (fun o => ι o → K) o

omit [NumberField K] [Fintype O] [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)] in
theorem inc_injective (o : O) : Function.Injective (inc (K := K) (ι := ι) o) :=
  Pi.single_injective (M := fun o => ι o → K) o

omit [NumberField K] [Fintype O] [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)] in
theorem iSupIndep_range_inc : iSupIndep fun o => LinearMap.range (inc (K := K) (ι := ι) o) := fun o => by
  have h : (⨆ p, ⨆ (_ : p ≠ o), LinearMap.range (inc (K := K) (ι := ι) p)) ≤
      LinearMap.ker (LinearMap.proj (R := K) (φ := fun o => ι o → K) o) := by
    refine iSup₂_le fun p hp => ?_
    rintro _ ⟨x, rfl⟩
    simp [Pi.single_eq_of_ne hp.symm]
  refine Submodule.disjoint_def.2 ?_
  rintro _ ⟨x, rfl⟩ hx
  have h1 : x = 0 := by simpa using h hx
  rw [h1, map_zero]

variable (Y : ∀ o, (K →+* ℂ) → Matrix (ι o) (ι o) ℂ)

omit [NumberField K] [Fintype O] [DecidableEq O] [∀ o, DecidableEq (ι o)] in
theorem matNorm_zero (o : O) (σ : K →+* ℂ) : matNorm (Y o) σ 0 = 0 := by
  have h : (fun j : ι o => σ ((0 : ι o → K) j)) = 0 := by funext j; simp
  simp only [matNorm, h, Matrix.mulVec_zero]
  simp

omit [NumberField K] [∀ o, DecidableEq (ι o)] in
theorem sumNorm_inc (o : O) (σ : K →+* ℂ) (x : ι o → K) : sumNorm Y σ (inc o x) = matNorm (Y o) σ x := by
  unfold sumNorm
  rw [Finset.sum_eq_single o]
  · simp only [LinearMap.coe_single, Pi.single_eq_same]
    exact Real.sqrt_sq (Real.sqrt_nonneg _)
  · intro p _ hp
    simp only [LinearMap.coe_single, Pi.single_eq_of_ne hp, matNorm_zero]
    simp
  · intro h; exact absurd (Finset.mem_univ o) h

omit [NumberField K] [∀ o, DecidableEq (ι o)] in
theorem sumNorm_sum (σ : K →+* ℂ) (f : O → ∀ o, ι o → K) (hf : ∀ o, f o ∈ LinearMap.range (inc (K := K) (ι := ι) o)) :
    sumNorm Y σ (∑ o, f o) ^ 2 = ∑ o, sumNorm Y σ (f o) ^ 2 := by
  choose g hg using hf
  have h : ∑ o, f o = g := by
    rw [← Finset.univ_sum_single g]
    exact Finset.sum_congr rfl fun o _ => (hg o).symm
  rw [h, sumNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun o _ => by rw [← hg o, sumNorm_inc]

theorem hasGram_sumNorm (hY : ∀ o σ, (Y o σ).det ≠ 0) : HasGram (sumNorm Y) := by
  refine GlobalTheory.OrthSumGram.orth_sum_hasGram K _ O (sumNorm Y) (fun o => LinearMap.range (inc (K := K) (ι := ι) o))
    (fun _ _ => Real.sqrt_nonneg _) iSupIndep_range_inc (LinearMap.iSup_range_single K _) (fun o => ?_)
    (fun σ f => sumNorm_sum Y σ (fun o => f o) fun o => (f o).2)
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := (isGram_matNorm K (ι o) (Y o) (hY o)).2
  let e := LinearEquiv.ofInjective (inc (K := K) (ι := ι) o) (inc_injective o)
  have h := GlobalTheory.RestrictNorm.hasGram_comp (matNorm (Y o)) e.symm.toLinearMap e.symm.injective b X hG
  convert h using 3 with σ x
  obtain ⟨y, rfl⟩ := e.surjective x
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact sumNorm_inc Y o σ y

theorem le_slope_sq_of_sum : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (O : Type) [Fintype O] [Nonempty O] (ι : O → Type) [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)] [∀ o, Nonempty (ι o)] (Nv : (K →+* ℂ) → V → ℝ) (M : Submodule (𝓞 K) V) (Y : ∀ o, (K →+* ℂ) → Matrix (ι o) (ι o) ℂ) (L : ∀ o, Submodule (𝓞 K) (ι o → K)) (Φ : (∀ o, ι o → K) →ₗ[K] V) (s : ℝ), HasGram Nv → M.FG → (∀ o σ, (Y o σ).det ≠ 0) → (∀ o, Submodule.IsFullLattice K (L o)) → Function.Injective Φ → (∀ x, (∀ o, x o ∈ L o) → Φ x ∈ M) → (∀ v ∈ M, v ∈ LinearMap.range Φ) → (∀ σ x, Nv σ (Φ x) ^ 2 ≤ ∑ o, matNorm (Y o) σ (x o) ^ 2) → (∀ o, s ≤ slope_sq (matNorm (Y o)) (L o)) → s ≤ slope_sq Nv M := by
  intro K _ _ _ V _ _ _ _ O _ _ ι _ _ _ Nv M Y L Φ s hNv hM hY hL hΦ hin hrg hle hs
  classical
  have hG := hasGram_sumNorm Y hY
  let P : O → Submodule (𝓞 K) (∀ o, ι o → K) := fun o => (L o).map ((inc o).restrictScalars (𝓞 K))
  have hsp : ∀ o, Submodule.span K (P o : Set (∀ o, ι o → K)) = LinearMap.range (inc (K := K) (ι := ι) o) := fun o => by
    letI := hL o
    have hspan : Submodule.span K (L o : Set (ι o → K)) = ⊤ := Submodule.IsFullLattice.span_eq_top
    rw [LinearMap.range_eq_map, ← hspan, ← Submodule.span_image]
    rfl
  have hP : ∀ o, (P o).FG := fun o => (hL o).fg.map _
  obtain ⟨hrk, hdeg⟩ := GlobalTheory.OrthRankDeg.rkK_deg_iSup K _ O (sumNorm Y) P hG hP
    fun σ f hf => sumNorm_sum Y σ f fun o => hsp o ▸ hf o
  have hd : ∀ o, (Formalism.HN.rkK (P o) : ℝ) * (s / 2) ≤ GlobalTheory.AllWt.deg (sumNorm Y) (P o) := fun o => by
    obtain ⟨h1, h2⟩ := (GlobalTheory.RestrictNorm.restrict_deg K _ _ (sumNorm Y) (inc o) (inc_injective o) hG).2
      (L o) (hL o).fg
    have h3 : (fun σ x => sumNorm Y σ (inc o x)) = matNorm (Y o) := by
      funext σ x; exact sumNorm_inc Y o σ x
    rw [h3] at h2
    show (Formalism.HN.rkK ((L o).map _) : ℝ) * _ ≤ GlobalTheory.AllWt.deg _ ((L o).map _)
    rw [h1, h2, GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope]
    exact mul_le_mul_of_nonneg_left (by linarith [hs o]) (Nat.cast_nonneg _)
  have htop : Submodule.span K ((⨆ o, P o : Submodule (𝓞 K) _) : Set (∀ o, ι o → K)) = ⊤ := by
    apply top_unique
    rw [← LinearMap.iSup_range_single K (fun o => ι o → K)]
    refine iSup_le fun o => ?_
    rw [← hsp o]
    exact Submodule.span_mono (le_iSup P o)
  have hmap : (⨆ o, P o).map (Φ.restrictScalars (𝓞 K)) ≤ M := by
    rw [Submodule.map_iSup]
    refine iSup_le fun o => ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine hin _ fun p => ?_
    by_cases hp : p = o
    · subst hp; simpa using hx
    · simp [Pi.single_eq_of_ne hp]
  have hspM : Submodule.span K (M : Set V) = LinearMap.range Φ := by
    refine le_antisymm (Submodule.span_le.2 hrg) ?_
    rw [LinearMap.range_eq_map, ← htop, ← Submodule.span_image]
    exact Submodule.span_mono hmap
  have hrkS : Formalism.HN.rkK (⨆ o, P o) = finrank K (∀ o, ι o → K) := by
    rw [Formalism.HN.rkK, htop, finrank_top]
  have hrkM : Formalism.HN.rkK M = Formalism.HN.rkK (⨆ o, P o) := by
    rw [hrkS, Formalism.HN.rkK, hspM, LinearMap.finrank_range_of_inj hΦ]
  have key := GlobalTheory.TwistIdeal.deg_add_le_deg_of_ideal_smul_le K _ V (sumNorm Y) Nv Φ (fun _ => 1) (⨆ o, P o) M ⊤ hG hNv hΦ
    (fun _ => one_pos) (fun _ => rfl)
    (fun σ x => by rw [one_mul]; exact (le_abs_self _).trans (Real.abs_le_sqrt (hle σ x)))
    (Submodule.fg_iSup _ hP) hM top_ne_bot (by rwa [Submodule.top_smul]) hrkM
  have hpos : (0 : ℝ) < Formalism.HN.rkK M := by
    rw [hrkM, hrkS]
    exact_mod_cast Module.finrank_pos
  have h1 : (Formalism.HN.rkK M : ℝ) * (s / 2) ≤ GlobalTheory.AllWt.deg (sumNorm Y) (⨆ o, P o) := by
    rw [hdeg, hrkM, hrk, Nat.cast_sum, Finset.sum_mul]
    exact Finset.sum_le_sum fun o _ => hd o
  simp only [Real.log_one, Finset.sum_const_zero, Ideal.absNorm_top, Nat.cast_one, zero_div, neg_zero, sub_zero,
    mul_zero, add_zero] at key
  have h2 := h1.trans key
  rw [GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope] at h2
  have h3 := le_of_mul_le_mul_left h2 hpos
  linarith

end GlobalTheory.SumSlope

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraFurther
section
namespace GlobalTheory.MulVecZeroDenominator

private lemma mulVec_eq_zero_of_map_mulVec_eq_zero {O L : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L]
    [IsFractionRing O L] {m c : ℕ} (D : Matrix (Fin m) (Fin c) O) (x : Fin c → L) (v : Fin c → O)
    (d : O) (hv : ∀ i, algebraMap O L (v i) = d • x i)
    (hD : Matrix.mulVec (Matrix.map D (algebraMap O L)) x = 0) : Matrix.mulVec D v = 0 := by
  funext i
  apply IsFractionRing.injective O L
  rw [RingHom.map_mulVec, Pi.zero_apply, map_zero]
  have hvx : (algebraMap O L ∘ v) = d • x := funext hv
  rw [hvx, Matrix.mulVec_smul, hD, smul_zero, Pi.zero_apply]

private lemma exists_common_denominator_divisor {O L : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L]
    [IsFractionRing O L] {c : ℕ} (x : Fin c → L) :
    ∃ (d : O) (v : Fin c → O), algebraMap O L d ≠ 0 ∧ ∀ i, algebraMap O L (v i) = d • x i := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x
  choose v hv using hd
  exact ⟨d, v, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2, hv⟩

theorem target : ∀ {O L : Type} [inst : CommRing O] [IsDomain O] [inst_2 : Field L] [inst_3 : Algebra O L] [IsFractionRing O L] {a b c : ℕ} (B : GlobalTheory.WachPlace.Mx O a c) (C : GlobalTheory.WachPlace.Mx O b c), (∀ (v : Fin c → O), Matrix.mulVec B v = (0 : Fin a → O) → Matrix.mulVec C v = (0 : Fin b → O) → v = (0 : Fin c → O)) → ∀ (x : Fin c → L), Matrix.mulVec (Matrix.map B (⇑(Algebra.algebraMap O L) : O → L)) x = (0 : Fin a → L) → Matrix.mulVec (Matrix.map C (⇑(Algebra.algebraMap O L) : O → L)) x = (0 : Fin b → L) → x = (0 : Fin c → L) := by
  intro O L _ _ _ _ _ a b c B C h x hB hC
  obtain ⟨d, v, hd, hv⟩ := exists_common_denominator_divisor (O := O) x
  have hv0 : v = 0 := h v (mulVec_eq_zero_of_map_mulVec_eq_zero B x v d hv hB) (mulVec_eq_zero_of_map_mulVec_eq_zero C x v d hv hC)
  funext i
  have hi := hv i
  rw [hv0, Pi.zero_apply, map_zero, Algebra.smul_def] at hi
  exact (mul_eq_zero.mp hi.symm).resolve_left hd

end GlobalTheory.MulVecZeroDenominator
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCharPolyCoeffBounded
section
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.BCT.GeoFin

theorem nrmL_mem_KGL {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (hL : IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) (GlobalTheory.LFun.KGL w (n := n))) {y : GLw n w}
    (hy : y ∈ GlobalTheory.LFun.KGL w (n := n)) : nrmL n w y ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have ht := hL.2.2 y hy
  unfold nrmL
  unfold thL at ht
  split_ifs with hs
  · exact hy
  · rw [if_neg hs] at ht
    exact mul_mem hy ht

theorem charpoly_coeff_of_mem_KGL {E : Type} [Field E] [NumberField E] (n : ℕ) (w : Pl E)
    {z : GL (Fin n) (w.adicCompletion E)} (hz : z ∈ GlobalTheory.LFun.KGL w (n := n)) :
    (∀ i, Valued.v (z.val.charpoly.coeff i) ≤ 1) ∧ 1 ≤ Valued.v (z.val.charpoly.coeff 0) := by
  obtain ⟨g, rfl⟩ := hz
  set f := (Ov E w).subtype
  have hcp : (Formalism.UG.bc f g).val.charpoly = g.val.charpoly.map f := by
    rw [← Matrix.charpoly_map]
    rfl
  have hint : ∀ a : Ov E w, Valued.v (f a) ≤ 1 := fun a => a.2
  refine ⟨fun i => ?_, ?_⟩
  · rw [hcp, Polynomial.coeff_map]
    exact hint _
  · rw [hcp, Polynomial.coeff_map]
    have hdet : IsUnit (g.val.charpoly.coeff 0) := by
      have h1 : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
      rw [Matrix.det_eq_sign_charpoly_coeff] at h1
      exact isUnit_of_mul_isUnit_right h1
    obtain ⟨u, hu⟩ := hdet
    have hmul : f (u : Ov E w) * f ((u⁻¹ : (Ov E w)ˣ) : Ov E w) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 : Valued.v (f (u : Ov E w)) * Valued.v (f ((u⁻¹ : (Ov E w)ˣ) : Ov E w)) = 1 := by
      rw [← map_mul, hmul, map_one]
    rw [← hu]
    calc (1 : _) = Valued.v (f (u : Ov E w)) * Valued.v (f ((u⁻¹ : (Ov E w)ˣ) : Ov E w)) := h2.symm
      _ ≤ Valued.v (f (u : Ov E w)) * 1 := mul_le_mul' le_rfl (hint _)
      _ = Valued.v (f (u : Ov E w)) := mul_one _

theorem charpoly_nrmL_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) (GlobalTheory.LFun.KGL w (n := n)) → ∀ y ∈ GlobalTheory.LFun.KGL w (n := n),
      (∀ i, Valued.v ((nrmL n w y).val.charpoly.coeff i) ≤ 1) ∧ 1 ≤ Valued.v ((nrmL n w y).val.charpoly.coeff 0) :=
  fun _ _ _ _ n w hL y hy => charpoly_coeff_of_mem_KGL n w (nrmL_mem_KGL n w hL hy)

end GlobalTheory.BCT.GeoFin
end

