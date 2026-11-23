module

public import Mathlib
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdLatticeMapEqIffMemGLintValuationSubring
section
open Matrix

namespace GlobalTheory.GLintLattice

variable {K : Type} [Field K] (A : ValuationSubring K) {r : ℕ}

theorem mem_span_basisFun_iff (y : Fin r → K) :
    y ∈ Submodule.span A (Set.range (Pi.basisFun K (Fin r))) ↔ ∀ i, y i ∈ A := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ i
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · intro h
    refine ⟨fun i => ⟨y i, h i⟩, ?_⟩
    ext j
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]

theorem mulVec_maps_iff (M : Matrix (Fin r) (Fin r) K) :
    (∀ y : Fin r → K, (∀ i, y i ∈ A) → ∀ i, (M *ᵥ y) i ∈ A) ↔ ∀ i j, M i j ∈ A := by
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      by_cases hk : k = j
      · subst hk; simp
      · simp [Pi.single_apply, hk]) i
    simpa [Matrix.mulVec_single_one] using this
  · intro h y hy i
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem (fun j _ => mul_mem (h i j) (hy j))

theorem mem_GLint_iff (x : GL (Fin r) K) :
    x ∈ Formalism.UG.GLint (Fin r) A.toSubring ↔
      (∀ i j, (x : Matrix (Fin r) (Fin r) K) i j ∈ A) ∧
        (∀ i j, ((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j ∈ A) := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show ((u : Matrix (Fin r) (Fin r) A.toSubring) i j : K) ∈ A
      exact (u : Matrix (Fin r) (Fin r) A.toSubring) i j |>.2
    · rw [← map_inv]
      show (((u⁻¹ : GL (Fin r) A.toSubring) : Matrix (Fin r) (Fin r) A.toSubring) i j : K) ∈ A
      exact ((u⁻¹ : GL (Fin r) A.toSubring) : Matrix (Fin r) (Fin r) A.toSubring) i j |>.2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin r) (Fin r) A.toSubring := Matrix.of fun i j => ⟨_, h1 i j⟩
    let M' : Matrix (Fin r) (Fin r) A.toSubring := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hM : M.map A.toSubring.subtype = (x : Matrix (Fin r) (Fin r) K) := by ext; rfl
    have hM' : M'.map A.toSubring.subtype = ((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) := by
      ext; rfl
    have inj : Function.Injective fun N : Matrix (Fin r) (Fin r) A.toSubring => N.map A.toSubring.subtype :=
      Matrix.map_injective Subtype.val_injective
    have e1 : M * M' = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact x.mul_inv)
    have e2 : M' * M = 1 := inj (by
      simp only
      rw [Matrix.map_mul, hM, hM', Matrix.map_one _ (map_zero _) (map_one _)]
      exact x.inv_mul)
    refine ⟨⟨M, M', e1, e2⟩, ?_⟩
    ext i j
    rfl

theorem stdLattice_map_eq_iff_mem_GLint : ∀ (K : Type) [Field K] (A : ValuationSubring K) (r : ℕ)
    (x : GL (Fin r) K),
    (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map
        ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) =
      Submodule.span A (Set.range (Pi.basisFun K (Fin r))) ↔
    x ∈ Formalism.UG.GLint (Fin r) A.toSubring := by
  intro K _ A r x
  have hf : ∀ z, ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) z =
      (x : Matrix (Fin r) (Fin r) K) *ᵥ z := fun z => rfl
  have inv_x : ∀ z : Fin r → K, ((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ
      ((x : Matrix (Fin r) (Fin r) K) *ᵥ z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have x_inv : ∀ z : Fin r → K, (x : Matrix (Fin r) (Fin r) K) *ᵥ
      (((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [mem_GLint_iff, ← mulVec_maps_iff, ← mulVec_maps_iff]
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · have hm : (x : Matrix (Fin r) (Fin r) K) *ᵥ y ∈
          (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map
            ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) :=
        ⟨y, (mem_span_basisFun_iff A y).2 hy, hf y⟩
      rw [h] at hm
      exact (mem_span_basisFun_iff A _).1 hm
    · have hm : y ∈ (Submodule.span A (Set.range (Pi.basisFun K (Fin r)))).map
            ((x : Matrix (Fin r) (Fin r) K).mulVecLin.restrictScalars A) := by
        rw [h]; exact (mem_span_basisFun_iff A y).2 hy
      obtain ⟨z, hz, hzy⟩ := hm
      rw [hf] at hzy
      rw [← hzy, inv_x]
      exact (mem_span_basisFun_iff A z).1 hz
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [hf, mem_span_basisFun_iff]
      exact h1 z ((mem_span_basisFun_iff A z).1 hz)
    · intro y hy
      refine ⟨((x⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ y,
        (mem_span_basisFun_iff A _).2 (h2 y ((mem_span_basisFun_iff A y).1 hy)), ?_⟩
      rw [hf, x_inv]

end GlobalTheory.GLintLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusInvMulPowValuationNonnegIff
section
open GlobalTheory.UnitLemma

namespace GlobalTheory.TorusInteg

theorem torus_integral_iff : ∀ (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → ∀ (r : ℕ) (e : Fin r → ι), (∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) → ∀ α : G, τ α = α → (∀ i, 0 < Multiplicative.toAdd (w i α)) → ∀ (t : T) (k : ℕ), (∀ i, 0 ≤ Multiplicative.toAdd (w i ((t : G)⁻¹ * α ^ k))) ↔ ∀ j, |Multiplicative.toAdd (((MulEquiv.funMultiplicative _ ℤ).symm.toMonoidHom.comp (MonoidHom.pi (w ∘ e))).comp T.subtype t) j| ≤ ((k * (Multiplicative.toAdd (w (e j) α)).toNat : ℕ) : ℤ) := by
  intro G _ τ T hT ι s w hs r e hcov α hα hpos t k
  have hτt : τ (t : G) = (t : G)⁻¹ := eq_inv_of_mul_eq_one_right ((hT _).1 t.2)
  have val1 : ∀ i, Multiplicative.toAdd (w i ((t : G)⁻¹ * α ^ k))
      = - Multiplicative.toAdd (w i t) + k * Multiplicative.toAdd (w i α) := by
    intro i
    simp [map_mul, map_inv, map_pow, toAdd_mul, toAdd_inv, toAdd_pow, nsmul_eq_mul]
  have val2 : ∀ i, Multiplicative.toAdd (w i (τ ((t : G)⁻¹ * α ^ k)))
      = Multiplicative.toAdd (w i t) + k * Multiplicative.toAdd (w i α) := by
    intro i
    rw [map_mul, map_inv, map_pow, hτt, hα, inv_inv]
    simp [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul]
  have rhs : ∀ j, ((k * (Multiplicative.toAdd (w (e j) α)).toNat : ℕ) : ℤ)
      = k * Multiplicative.toAdd (w (e j) α) := by
    intro j
    push_cast
    rw [Int.toNat_of_nonneg (hpos _).le]
  have lhs : ∀ j, Multiplicative.toAdd (((MulEquiv.funMultiplicative _ ℤ).symm.toMonoidHom.comp (MonoidHom.pi (w ∘ e))).comp T.subtype t) j
      = Multiplicative.toAdd (w (e j) t) := fun j => rfl
  constructor
  · intro h j
    rw [lhs, rhs, abs_le]
    have h1 := h (e j)
    have h2 := (hs (e j) _).1 (h (s (e j)))
    rw [val1] at h1
    rw [val2] at h2
    constructor <;> linarith
  · intro h i
    rcases hcov i with hi | ⟨j, rfl | rfl⟩
    · have hz : Multiplicative.toAdd (w i t) = 0 := by
        have := hs i (t : G)
        rw [hi, hτt, map_inv, toAdd_inv] at this
        rcases lt_trichotomy (Multiplicative.toAdd (w i t)) 0 with h' | h' | h'
        · exact absurd (this.2 (by linarith)) (not_le.2 h')
        · exact h'
        · exact absurd (this.1 h'.le) (not_le.2 (by linarith))
      rw [val1, hz]
      have := (hpos i).le
      positivity
    · have := h j
      rw [lhs, rhs, abs_le] at this
      rw [val1]; linarith [this.1]
    · have := h j
      rw [lhs, rhs, abs_le] at this
      apply (hs (e j) _).2
      rw [val2]; linarith [this.1]

end GlobalTheory.TorusInteg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusSubmoduleMulLeftImageMemSelfDualStableLatti
section
open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.TorusAction

open InvAlg

variable {K : UQ} (B : InvAlg K)

theorem mem_mulLat_unit (u : B.Aˣ) (L : Submodule K.O B.A) (y : B.A) :
    y ∈ mulLat K.O (u : B.A) L ↔ ((u⁻¹ : B.Aˣ) : B.A) * y ∈ L := by
  unfold mulLat
  simp only [Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [← mul_assoc, Units.inv_mul, one_mul]
  · intro h
    exact ⟨_, h, by rw [← mul_assoc, Units.mul_inv, one_mul]⟩

theorem sigma_eq_inv (t : B.Aˣ) (ht : t ∈ B.T) : B.σ (t : B.A) = ((t⁻¹ : B.Aˣ) : B.A) := by
  have h : (t : B.A) * B.σ (t : B.A) = 1 := ht
  calc B.σ (t : B.A) = ((t⁻¹ : B.Aˣ) : B.A) * ((t : B.A) * B.σ (t : B.A)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [h, mul_one]

theorem isLat_mulLat (u : B.Aˣ) (L : Submodule K.O B.A) (hL : IsLat K.O K.E L) :
    IsLat K.O K.E (mulLat K.O (u : B.A) L) := by
  refine ⟨hL.1.map _, ?_⟩
  have hc : ((mulLat K.O (u : B.A) L : Submodule K.O B.A) : Set B.A) =
      (LinearMap.mulLeft K.E (u : B.A)) '' (L : Set B.A) := by
    unfold mulLat; rw [Submodule.map_coe]; rfl
  rw [hc, Submodule.span_image, hL.2, Submodule.map_top, LinearMap.range_eq_top]
  intro y
  exact ⟨((u⁻¹ : B.Aˣ) : B.A) * y, by simp [← mul_assoc]⟩

theorem torus_mem_X (K : UQ) (B : InvAlg K) (x : B.A) :
    ∀ t ∈ B.T, ∀ L ∈ B.X x, mulLat K.O (t : B.A) L ∈ B.X x := by
  intro t ht L hL
  obtain ⟨hlat, hg, hdual⟩ := hL
  have hs := sigma_eq_inv B t ht
  refine ⟨isLat_mulLat B t L hlat, ?_, ?_⟩
  · intro y hy
    rw [mem_mulLat_unit] at hy ⊢
    have := hg _ hy
    rwa [mul_left_comm] at this
  · intro y
    rw [mem_mulLat_unit, hdual]
    constructor
    · intro h z hz
      rw [mem_mulLat_unit] at hz
      have := h _ hz
      have e : B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) (((t⁻¹ : B.Aˣ) : B.A) * z) = B.herm x y z := by
        have hs' : B.σ ((t⁻¹ : B.Aˣ) : B.A) = (t : B.A) := by rw [← hs, B.σ_σ]
        unfold InvAlg.herm; rw [map_mul B.σ, hs']
        congr 1
        linear_combination (x * y * B.σ z) * Units.inv_mul t
      rwa [e] at this
    · intro h w hw
      have hz : (t : B.A) * w ∈ mulLat K.O (t : B.A) L := by
        rw [mem_mulLat_unit, ← mul_assoc, Units.inv_mul, one_mul]; exact hw
      have := h _ hz
      have e : B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) w = B.herm x y ((t : B.A) * w) := by
        unfold InvAlg.herm; rw [map_mul B.σ, hs]; congr 1; ring
      rwa [e]

end GlobalTheory.UnitLemma.TorusAction
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitMulPowOfMaximalIdealEqSpan
section
open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat

theorem unit_mul_pow_of_maximalIdeal_eq_span {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {π : S} (hm : maximalIdeal S = Ideal.span {π}) {x : S} (hx : x ≠ 0) :
    ∃ (k : ℕ) (u : S), IsUnit u ∧ x = π ^ k * u := by
  first
  | exact @_root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit
  | exact _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit
  | (apply _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit ..)

theorem dvr_of_maximalIdeal_eq_span {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {π : S} (hm : maximalIdeal S = Ideal.span {π}) (hreg : ∀ a : S, π * a = 0 → a = 0) :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S ∧ Irreducible π := by
  have hpow : ∀ (k : ℕ) (a : S), π ^ k * a = 0 → a = 0 := by
    intro k
    induction k with
    | zero => intro a h; simpa using h
    | succ k ih => intro a h; exact ih a (hreg _ (by rw [← h, pow_succ]; ring))
  have hnzd : NoZeroDivisors S := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_contra h
    push_neg at h
    obtain ⟨a, u, hu, rfl⟩ := unit_mul_pow_of_maximalIdeal_eq_span hm h.1
    obtain ⟨b, v, hv, rfl⟩ := unit_mul_pow_of_maximalIdeal_eq_span hm h.2
    have : π ^ (a + b) * (u * v) = 0 := by rw [← hxy, pow_add]; ring
    exact (hu.mul hv).ne_zero (hpow _ _ this)
  haveI : IsDomain S := NoZeroDivisors.to_isDomain S
  have hπ0 : π ≠ 0 := fun h => one_ne_zero (hreg 1 (by rw [h, zero_mul]))
  have hnf : ¬ IsField S := by
    rw [isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot]
    exact hπ0
  have hpr : (maximalIdeal S).IsPrincipal := ⟨⟨π, hm⟩⟩
  have hdvr : IsDiscreteValuationRing S :=
    ((IsDiscreteValuationRing.TFAE S hnf).out 1 5).2 hpr
  exact ⟨inferInstance, hdvr, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 hm⟩

end GlobalTheory.Pat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryTwistInvolutionGLProperties
section
open GlobalTheory.Tw Matrix

namespace GlobalTheory.Tw.PhiConjugateTranspose

variable {n : ℕ} {R : Type} [CommRing R]

theorem phi_apply (i k : Fin n) : Phi n R i k = if k = i.rev then (-1 : R) ^ (i : ℕ) else 0 := by
  simp only [Phi, of_apply]
  congr 1
  apply propext
  rw [Fin.ext_iff, Fin.val_rev]
  omega

theorem phi_conj_apply (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Phi n R * A * (Phi n R)ᵀ) i j = (-1 : R) ^ (i : ℕ) * A i.rev j.rev * (-1 : R) ^ (j : ℕ) := by
  simp [Matrix.mul_apply, phi_apply, ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem phi_mul_transpose : Phi n R * (Phi n R)ᵀ = 1 := by
  have := phi_conj_apply (n := n) (R := R) 1
  ext i j
  have h := this i j
  rw [Matrix.mul_one] at h
  rw [h, Matrix.one_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp [← mul_pow]
  · simp [hij]

theorem phi_transpose_mul : (Phi n R)ᵀ * Phi n R = 1 := mul_eq_one_comm.mp phi_mul_transpose

theorem phi_mul_phi : Phi n R * Phi n R = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i k
  simp only [Matrix.mul_apply, phi_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  by_cases h : k = i
  · subst h
    simp only [if_true, mul_one]
    rw [← pow_add, Fin.val_rev]
    have hk := k.isLt
    rw [show (k : ℕ) + (n - ((k : ℕ) + 1)) = n - 1 by omega]
  · simp [h, Ne.symm h]

theorem phi_inv : (Phi n R)⁻¹ = (Phi n R)ᵀ := Matrix.inv_eq_left_inv phi_transpose_mul

theorem phi_transpose_inv : ((Phi n R)ᵀ)⁻¹ = Phi n R := Matrix.inv_eq_left_inv phi_mul_transpose

theorem conj_inv (A : Matrix (Fin n) (Fin n) R) :
    (Phi n R * A * (Phi n R)ᵀ)⁻¹ = Phi n R * A⁻¹ * (Phi n R)ᵀ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, phi_inv, phi_transpose_inv, Matrix.mul_assoc]

theorem det_conj (A : Matrix (Fin n) (Fin n) R) : (Phi n R * A * (Phi n R)ᵀ).det = A.det := by
  rw [det_mul, det_mul, mul_comm (Phi n R).det, mul_assoc, ← det_mul, phi_mul_transpose, det_one, mul_one]

variable [StarRing R]

theorem phi_conjTranspose : (Phi n R)ᴴ = (Phi n R)ᵀ := by
  ext i j
  simp only [conjTranspose_apply, transpose_apply, Phi, of_apply]
  split_ifs <;> simp

theorem phi_transpose_conjTranspose : ((Phi n R)ᵀ)ᴴ = Phi n R := by
  ext i j
  simp only [conjTranspose_apply, transpose_apply, Phi, of_apply]
  split_ifs <;> simp

theorem conj_conjTranspose (A : Matrix (Fin n) (Fin n) R) :
    (Phi n R * A * (Phi n R)ᵀ)ᴴ = Phi n R * Aᴴ * (Phi n R)ᵀ := by
  rw [conjTranspose_mul, conjTranspose_mul, phi_conjTranspose, phi_transpose_conjTranspose, Matrix.mul_assoc]

theorem theta_eq (g : Matrix (Fin n) (Fin n) R) : theta g = Phi n R * (g⁻¹)ᴴ * (Phi n R)ᵀ := rfl

theorem theta_mul (g h : Matrix (Fin n) (Fin n) R) : theta (g * h) = theta g * theta h := by
  simp only [theta_eq, Matrix.mul_inv_rev, conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Phi n R)ᵀ (Phi n R), phi_transpose_mul, Matrix.one_mul]

theorem theta_one : theta (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [theta_eq, inv_one, conjTranspose_one, Matrix.mul_one, phi_mul_transpose]

theorem det_theta (g : Matrix (Fin n) (Fin n) R) : (theta g).det = star (g⁻¹).det := by
  rw [theta_eq, det_conj, det_conjTranspose]

theorem theta_isUnit {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : IsUnit (theta g) := by
  rw [isUnit_iff_isUnit_det, det_theta]
  exact (isUnit_nonsing_inv_det _ ((isUnit_iff_isUnit_det g).mp hg)).star

theorem theta_theta {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : theta (theta g) = g := by
  have hd := (isUnit_iff_isUnit_det g).mp hg
  rw [theta_eq (theta g), theta_eq g, conj_inv, conj_conjTranspose, ← conjTranspose_nonsing_inv,
    nonsing_inv_nonsing_inv _ hd, conjTranspose_conjTranspose]
  have h2 : (Phi n R)ᵀ * (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← transpose_mul, phi_mul_phi, transpose_smul, transpose_one]
  calc Phi n R * (Phi n R * g * (Phi n R)ᵀ) * (Phi n R)ᵀ
      = (Phi n R * Phi n R) * g * ((Phi n R)ᵀ * (Phi n R)ᵀ) := by simp only [Matrix.mul_assoc]
    _ = g := by
      rw [phi_mul_phi, h2, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
        smul_smul, ← mul_pow]
      simp

theorem theta_blockTriangular {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) (ht : g.BlockTriangular id) :
    (theta g).BlockTriangular id := by
  have : Invertible g := hg.invertible
  have hi : (g⁻¹).BlockTriangular id := blockTriangular_inv_of_blockTriangular ht
  intro i j hji
  rw [theta_eq, phi_conj_apply, conjTranspose_apply, hi]
  · simp
  · simpa [Fin.rev_lt_rev] using hji

end GlobalTheory.Tw.PhiConjugateTranspose

open GlobalTheory.Tw.PhiConjugateTranspose in
theorem GlobalTheory.Tw.theta_props : ∀ (n : ℕ) (R : Type) [CommRing R] [StarRing R], (Phi n R * (Phi n R)ᵀ = 1) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → IsUnit (theta g) ∧ theta (theta g) = g) ∧ (∀ g h : Matrix (Fin n) (Fin n) R, IsUnit g → IsUnit h → theta (g * h) = theta g * theta h) ∧ (∀ x δ : Matrix (Fin n) (Fin n) R, IsUnit x → IsUnit δ → nrm (twConj x δ) = x⁻¹ * nrm δ * x) ∧ (∀ u δ : Matrix (Fin n) (Fin n) R, IsUnit u → IsUnit δ → nrm (δ * theta u) = nrm δ * ((theta δ)⁻¹ * theta u * theta δ) * u) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → g.BlockTriangular id → (theta g).BlockTriangular id) ∧ ∀ g : Matrix (Fin n) (Fin n) R, IsUnit g → (theta g).det * star g.det = 1 := by
  intro n R _ _
  refine ⟨phi_mul_transpose, fun g hg => ⟨theta_isUnit hg, theta_theta hg⟩, fun g h _ _ => theta_mul g h, ?_, ?_,
    fun g hg ht => theta_blockTriangular hg ht, ?_⟩
  · intro x δ hx _
    have hxd := (isUnit_iff_isUnit_det x).mp hx
    simp only [nrm, twConj, theta_mul, theta_theta hx]
    have h1 : theta x * theta x⁻¹ = 1 := by rw [← theta_mul, mul_nonsing_inv _ hxd, theta_one]
    calc x⁻¹ * δ * theta x * (theta x⁻¹ * theta δ * x)
        = x⁻¹ * δ * (theta x * theta x⁻¹) * theta δ * x := by simp only [Matrix.mul_assoc]
      _ = x⁻¹ * (δ * theta δ) * x := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  · intro u δ hu hδ
    have htd := (isUnit_iff_isUnit_det _).mp (theta_isUnit hδ)
    simp only [nrm, theta_mul, theta_theta hu]
    calc δ * theta u * (theta δ * u)
        = δ * (theta δ * (theta δ)⁻¹) * theta u * theta δ * u := by
          rw [mul_nonsing_inv _ htd, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = δ * theta δ * ((theta δ)⁻¹ * theta u * theta δ) * u := by simp only [Matrix.mul_assoc]
  · intro g hg
    have hd := (isUnit_iff_isUnit_det g).mp hg
    rw [det_theta, ← star_mul, ← det_mul, mul_nonsing_inv _ hd, det_one, star_one]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZValuationsAtIndicesTorusEqOneIff
section
open GlobalTheory.UnitLemma

namespace GlobalTheory.TorusKer

theorem valsAt_torus_eq_one_iff (G : Type) [CommGroup G] (τ : G →* G) (T : Subgroup G)
    (hT : ∀ t, t ∈ T ↔ t * τ t = 1) (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ)
    (hs : ∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x)))
    (r : ℕ) (e : Fin r → ι) (hcov : ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j)) (t : T) :
    ((MulEquiv.funMultiplicative _ ℤ).symm.toMonoidHom.comp (MonoidHom.pi (w ∘ e))).comp T.subtype t = 1 ↔ ∀ i, Multiplicative.toAdd (w i (t : G)) = 0 := by
  have hinv : ∀ i (x : G), Multiplicative.toAdd (w i x⁻¹) = - Multiplicative.toAdd (w i x) := by
    intro i x; rw [map_inv, toAdd_inv]
  have hτ : τ (t : G) = (t : G)⁻¹ := eq_inv_of_mul_eq_one_right ((hT t).1 t.2)
  have hτ' : τ ((t : G)⁻¹) = (t : G) := by rw [map_inv, hτ, inv_inv]
  constructor
  · intro h
    have he : ∀ j, Multiplicative.toAdd (w (e j) (t : G)) = 0 := by
      intro j
      have := congrArg (fun y : Multiplicative (Fin r → ℤ) => Multiplicative.toAdd y j) h
      simpa [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.piMultiplicative_symm_apply, toAdd_ofAdd, MonoidHom.pi_apply, Function.comp_apply] using this
    intro i
    rcases hcov i with hi | ⟨j, hj | hj⟩
    · have h1 := hs i (t : G)
      rw [hi, hτ, hinv] at h1
      omega
    · subst hj; exact he j
    · subst hj
      have h1 := hs (e j) (t : G)
      have h2 := hs (e j) ((t : G)⁻¹)
      rw [hτ, hinv, he j] at h1
      rw [hτ', he j, hinv] at h2
      omega
  · intro h
    apply Multiplicative.toAdd.injective
    funext j
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.piMultiplicative_symm_apply, toAdd_ofAdd, MonoidHom.pi_apply, Function.comp_apply]
    rw [h]
    rfl

end GlobalTheory.TorusKer
end

