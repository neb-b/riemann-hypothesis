module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.SmoothAutCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin
variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}

theorem conj_fixed_iff (hu : IsUnit H.det) (Z : Matrix (Fin n) (Fin n) ℂ) :
    -(H⁻¹ * Zᴴ * H) = Z ↔ Zᴴ * H + H * Z = 0 := by
  constructor
  · intro h
    have : H * Z = -(Zᴴ * H) := by
      conv_lhs => rw [← h]
      rw [mul_neg, ← mul_assoc, ← mul_assoc, mul_nonsing_inv _ hu, one_mul]
    rw [this, add_neg_cancel]
  · intro h
    have : Zᴴ * H = -(H * Z) := eq_neg_of_add_eq_zero_left h
    rw [mul_assoc, this, mul_neg, neg_neg, ← mul_assoc, nonsing_inv_mul _ hu, one_mul]

theorem conjT_conj_mul (hH : Hᴴ = H) (hu : IsUnit H.det) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (-(H⁻¹ * Zᴴ * H))ᴴ * H = -(H * Z) := by
  rw [conjTranspose_neg, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hH,
    neg_mul, mul_assoc, mul_assoc, nonsing_inv_mul _ hu, mul_one]

theorem mul_conj (hu : IsUnit H.det) (Z : Matrix (Fin n) (Fin n) ℂ) : H * (-(H⁻¹ * Zᴴ * H)) = -(Zᴴ * H) := by
  rw [mul_neg, ← mul_assoc, ← mul_assoc, mul_nonsing_inv _ hu, one_mul]

theorem re_mem (hH : Hᴴ = H) (hu : IsUnit H.det) (Z : Matrix (Fin n) (Fin n) ℂ) :
    ((1 / 2 : ℂ) • (Z + -(H⁻¹ * Zᴴ * H)))ᴴ * H + H * ((1 / 2 : ℂ) • (Z + -(H⁻¹ * Zᴴ * H))) = 0 := by
  rw [conjTranspose_smul, conjTranspose_add, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, conjT_conj_mul hH hu,
    mul_conj hu]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this, ← smul_add]
  simp

theorem im_mem (hH : Hᴴ = H) (hu : IsUnit H.det) (Z : Matrix (Fin n) (Fin n) ℂ) :
    ((1 / (2 * Complex.I)) • (Z - -(H⁻¹ * Zᴴ * H)))ᴴ * H + H * ((1 / (2 * Complex.I)) • (Z - -(H⁻¹ * Zᴴ * H))) = 0 := by
  rw [conjTranspose_smul, conjTranspose_sub, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, conjT_conj_mul hH hu,
    mul_conj hu]
  have : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by simp
  rw [this, neg_smul, sub_neg_eq_add, sub_neg_eq_add, add_comm (H * Z), neg_add_cancel]

theorem exp_mem_UH (hu : IsUnit H.det) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH H := by
  have hu' : IsUnit H := (isUnit_iff_isUnit_det H).2 hu
  have e : (t • X)ᴴ = H * (-(t • X)) * H⁻¹ := by
    have h1 : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
    have h2 : Xᴴ = -(H * X) * H⁻¹ := by rw [← h1, mul_assoc, mul_nonsing_inv _ hu, mul_one]
    rw [conjTranspose_smul, h2]
    simp
  show (NormedSpace.exp (t • X))ᴴ * H * NormedSpace.exp (t • X) = H
  rw [← Matrix.exp_conjTranspose, e, Matrix.exp_conj _ _ hu', mul_assoc _ H⁻¹, nonsing_inv_mul _ hu, mul_one, mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • X)).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]

end Lin

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem gram_det_ne : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have hx : ∀ y, V.hT y (∑ j, v j • V.frame j) = 0 := by
    intro y
    rw [← V.frame.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrFun h0 i
    simp only [mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at this
    calc _ = (starRingEnd _) (V.frame.repr y i) * ∑ j, V.hT (V.frame i) (V.frame j) * v j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [this, mul_zero]
  have := V.nondeg.2 _ hx
  exact hv (funext (Fintype.linearIndependent_iff.1 V.frame.linearIndependent v this))

theorem gramAt_unit (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det _ _).symm
  rw [this, isUnit_iff_ne_zero]
  exact (map_ne_zero _).2 (gram_det_ne V)

theorem gramAt_herm (τ : D.what₂.Tau) : (gramAt D V τ)ᴴ = gramAt D V τ := by
  ext i j
  have hcm := D.host.isCMField_hostE
  have h1 : star (V.hT (V.frame j) (V.frame i)) = V.hT (V.frame i) (V.frame j) := V.herm.eq _ _
  simp only [conjTranspose_apply, gramAt, map_apply, HSpace.gram]
  rw [← h1]
  exact (NumberField.IsCMField.complexEmbedding_complexConj _ (tauE D τ) _).symm

theorem conjAt_fixed_iff (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    conjAt V τ Z = Z ↔ Z ∈ lieAt V τ := conj_fixed_iff (gramAt_unit V τ) Z

theorem parts_mem (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    (1 / 2 : ℂ) • (Z + conjAt V τ Z) ∈ lieAt V τ ∧ (1 / (2 * Complex.I)) • (Z - conjAt V τ Z) ∈ lieAt V τ :=
  ⟨re_mem (gramAt_herm V τ) (gramAt_unit V τ) Z, im_mem (gramAt_herm V τ) (gramAt_unit V τ) Z⟩

theorem parts_sum (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    (1 / 2 : ℂ) • (Z + conjAt V τ Z) + Complex.I • ((1 / (2 * Complex.I)) • (Z - conjAt V τ Z)) = Z := by
  have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [smul_smul, this, ← smul_add, add_add_sub_cancel, ← two_smul ℂ Z, smul_smul]
  simp

theorem RderC_eq (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (φ : GA D V → ℂ) :
    RderC θ V τ X φ = Rder θ V τ X φ := by
  unfold RderC
  rw [(conjAt_fixed_iff V τ X).2 hX, sub_self, smul_zero, ← two_smul ℂ X, smul_smul]
  have : Rder θ V τ 0 φ = 0 := by
    funext g
    simp [Rder, oneP]
  rw [this]
  simp

def reSig (s : (D.host.E →+* ℂ) → ℕ × ℕ) : HSp D := { V with sig := s }

theorem isAutFunSm_reSig (s : (D.host.E →+* ℂ) → ℕ × ℕ) (φ : GA D V → ℂ) :
    IsAutFunSm θ (reSig V s) φ ↔ IsAutFunSm θ V φ :=
  ⟨fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩,
   fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩⟩

end GlobalTheory.SmoothAutCheck

end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.DualPairCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem cA_cA (x : Formalism.L2.Theta.AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e =>
    simp only [cA, sigR]
    simp
    congr 1
    exact star_star e

theorem cA_incA (e : D.host.E) : cA D (incA D e) = incA D (star e) := by
  simp only [cA, sigR, incA, inclR]
  simp
  rfl

theorem gram_star (V : HSp D) (i j) : star (V.gram i j) = V.gram j i :=
  V.herm.eq (V.frame i) (V.frame j)

section Generic
variable {A : Type} [CommRing A] {m n : ℕ}

theorem sum_small (σ : A →+* A) (P : Matrix (Fin m) (Fin m) A) (Q : Matrix (Fin n) (Fin n) A)
    (x y : Matrix (Fin m) (Fin n) A) :
    ∑ i, ∑ j, ∑ k, ∑ l, σ (x i j) * P k i * Q j l * y k l = (x.map σ * Q * yᵀ * P).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

theorem sum_large (σ : A →+* A) (P : Matrix (Fin m) (Fin m) A) (Q : Matrix (Fin n) (Fin n) A)
    (x y : Matrix (Fin m) (Fin n) A) :
    ∑ i, ∑ j, ∑ k, ∑ l, σ (x i j) * P i k * Q l j * y k l = ((x.map σ)ᵀ * P * y * Q).trace := by
  have := sum_small σ Q P xᵀ yᵀ
  simp only [Matrix.transpose_apply, Matrix.transpose_transpose] at this
  rw [← Matrix.transpose_map, ← this, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem inv_small (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (P g : Matrix (Fin m) (Fin m) A)
    (Q h : Matrix (Fin n) (Fin n) A) (hg : (g.map σ)ᵀ * P * g = P) (hh : (h.map σ)ᵀ * Q * h = Q)
    (x y : Matrix (Fin m) (Fin n) A) :
    ((g.map σ * x * hᵀ).map σ * Q * (g.map σ * y * hᵀ)ᵀ * P).trace = (x.map σ * Q * yᵀ * P).trace := by
  have e : (g.map σ).map σ = g := by ext i j; simp [hσ]
  rw [Matrix.map_mul, Matrix.map_mul, e, Matrix.transpose_map, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  calc _ = (g * (x.map σ * ((h.map σ)ᵀ * Q * h) * yᵀ * ((g.map σ)ᵀ * P))).trace := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [Matrix.trace_mul_comm, hh, Matrix.mul_assoc _ _ g, hg]

theorem inv_large (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (P g : Matrix (Fin m) (Fin m) A)
    (Q h : Matrix (Fin n) (Fin n) A) (hg : (g.map σ)ᵀ * P * g = P) (hh : (h.map σ)ᵀ * Q * h = Q)
    (x y : Matrix (Fin m) (Fin n) A) :
    (((g * x * (h.map σ)ᵀ).map σ)ᵀ * P * (g * y * (h.map σ)ᵀ) * Q).trace = ((x.map σ)ᵀ * P * y * Q).trace := by
  have c := inv_small σ hσ _ _ _ _ hh hg xᵀ yᵀ
  simp only [Matrix.transpose_transpose, Matrix.transpose_map] at c
  rw [← c]
  congr 1
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.transpose_map,
    Matrix.mul_assoc]

theorem herm_small (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (P : Fin m → Fin m → A) (Q : Fin n → Fin n → A)
    (hP : ∀ i k, σ (P i k) = P k i) (hQ : ∀ i k, σ (Q i k) = Q k i) (x y : Matrix (Fin m) (Fin n) A) :
    σ (∑ i, ∑ j, ∑ k, ∑ l, σ (x i j) * P k i * Q j l * y k l) =
      ∑ i, ∑ j, ∑ k, ∑ l, σ (y i j) * P k i * Q j l * x k l := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hσ, hP, hQ]
  have a : ∀ f : Fin m → Fin n → Fin m → Fin n → A, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l =
      ∑ p : Fin m × Fin n, ∑ q : Fin m × Fin n, f p.1 p.2 q.1 q.2 := by
    intro f; simp only [Fintype.sum_prod_type]
  rw [a, a, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Generic

theorem mt_unit (V : HSp D) (g : GA D V) :
    ((mt V g).map (cA D))ᵀ * V.gram.map (incA D) * mt V g = V.gram.map (incA D) := g.2

theorem hHom_herm (V W : HSp D) (x y : WA V W) : cA D (hHom V W x y) = hHom V W y x := by
  unfold hHom
  split_ifs with hr
  · exact herm_small (cA D) cA_cA (fun i k => incA D (V.gram i k)) (fun i k => incA D (W.gram i k))
      (fun i k => by rw [cA_incA, gram_star]) (fun i k => by rw [cA_incA, gram_star]) x y
  · exact herm_small (cA D) cA_cA (fun i k => incA D (V.gram k i)) (fun i k => incA D (W.gram k i))
      (fun i k => by rw [cA_incA, gram_star]) (fun i k => by rw [cA_incA, gram_star]) x y

theorem split_ne (e : Formalism.L2.Theta.AE D) (he : IsSplitIdem D e) : cA D e ≠ e := by
  obtain ⟨h1, h2, v, ε, ⟨α, hε, hv, -⟩, h3⟩ := he
  intro h
  rw [h, h1] at h2
  rw [h2, map_zero, add_zero] at h3
  have hinj : Function.Injective (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)) :=
    Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
  have : ε = 0 := hinj (by rw [← h3, map_zero])
  have hα : α = 0 := by
    rw [hε] at this
    exact congrArg Prod.snd this
  rw [hα, map_zero] at hv
  exact zero_ne_one hv

theorem trace_cA (x : Formalism.L2.Theta.AE D) :
    Algebra.trace (AF D.host.F) (Formalism.L2.Theta.AE D) (cA D x) = Algebra.trace (AF D.host.F) (Formalism.L2.Theta.AE D) x := by
  let f : Formalism.L2.Theta.AE D →ₐ[AF D.host.F] Formalism.L2.Theta.AE D :=
    Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig
  let e : Formalism.L2.Theta.AE D ≃ₐ[AF D.host.F] Formalism.L2.Theta.AE D :=
    AlgEquiv.ofAlgHom f f (AlgHom.ext fun x => cA_cA x) (AlgHom.ext fun x => cA_cA x)
  exact Algebra.trace_eq_of_algEquiv e x

theorem star_purely_imaginary_eq_neg (D : D7) : star D.host.xi0 = -D.host.xi0 := by
  have hs : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    have := D.host.isCMField_hostE
    have h2 : D.host.φ₀ (star D.host.sqrtMinusD) = starRingEnd ℂ (D.host.φ₀ D.host.sqrtMinusD) :=
      NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ D.host.sqrtMinusD
    rw [h2, map_neg, h1]
    simp
  unfold Host.xi0
  rw [star_div₀, star_mul', hs, star_natCast, star_neg, star_one, mul_neg, div_neg]

theorem sympl_skew (V W : HSp D) (x y : WA V W) :
    sympl V W y x = -sympl V W x y := by
  unfold sympl
  rw [← trace_cA, map_mul, cA_incA, star_purely_imaginary_eq_neg, hHom_herm, map_neg, neg_mul, map_neg]

theorem symplH_add_left (V W : HSp D) (x x' y : WA V W) :
    symplH V W (x + x') y = symplH V W x y + symplH V W x' y := by
  unfold symplH sympl hHom
  split_ifs <;> simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem symplH_add_right (V W : HSp D) (x y y' : WA V W) :
    symplH V W x (y + y') = symplH V W x y + symplH V W x y' := by
  unfold symplH sympl hHom
  split_ifs <;> simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

theorem heis_heis (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (w w' : WA V W) (f : WA V W → ℂ) :
    Heisenberg₂ ψ V W w (Heisenberg₂ ψ V W w' f) = ψ (symplH V W w w') • Heisenberg₂ ψ V W (w + w') f := by
  funext u
  simp only [Heisenberg₂, Pi.smul_apply, smul_eq_mul, symplH_add_left, symplH_add_right, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem heis_quasi (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (w₀ : WA V W) (f : WA V W → ℂ)
    (hf : ∀ γ w, f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * f w) (γ w) :
    Heisenberg₂ ψ V W w₀ f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * Heisenberg₂ ψ V W w₀ f w := by
  simp only [Heisenberg₂]
  rw [add_assoc, hf, symplH_add_left, symplH_add_right, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul,
    ← AddChar.map_add_eq_mul]
  congr 2
  ring

end GlobalTheory.DualPairCheck
end
end

