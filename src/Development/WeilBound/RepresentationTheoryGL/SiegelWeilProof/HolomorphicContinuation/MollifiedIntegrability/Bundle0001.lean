module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundAlt

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundA
section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.WR.B

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem herm_apply (y : E n) (i j : Fin n) : herm y i j = ⟨(y i j + y j i) / 2, (y i j - y j i) / 2⟩ := by
  apply Complex.ext <;> simp [herm]

theorem herm_conjTranspose (y : E n) : (herm y)ᴴ = herm y := by
  ext i j
  rw [conjTranspose_apply, herm_apply, herm_apply]
  apply Complex.ext <;> simp <;> ring

def Am (s : ℂ) (y : E n) : Matrix (Fin n) (Fin n) ℂ := 1 - (Complex.I * s) • herm y

def Bm (s : ℂ) (y : E n) : Matrix (Fin n) (Fin n) ℂ := 1 + (Complex.I * s) • herm y

theorem sq_of_pm {s : ℂ} (hs : s = 1 ∨ s = -1) : s * s = 1 := by
  rcases hs with rfl | rfl <;> norm_num

theorem star_of_pm {s : ℂ} (hs : s = 1 ∨ s = -1) : star s = s := by
  rcases hs with rfl | rfl <;> simp

theorem Is_sq {s : ℂ} (hs : s = 1 ∨ s = -1) : (Complex.I * s) * (Complex.I * s) = -1 := by
  rw [mul_mul_mul_comm, Complex.I_mul_I, sq_of_pm hs]
  ring

theorem Am_conjTranspose {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : (Am s y)ᴴ = Bm s y := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  unfold Am Bm
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, herm_conjTranspose, star_mul', star_of_pm hs, hI,
    neg_mul, neg_smul, sub_neg_eq_add]

theorem Bm_conjTranspose {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : (Bm s y)ᴴ = Am s y := by
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  unfold Am Bm
  rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, herm_conjTranspose, star_mul', star_of_pm hs, hI,
    neg_mul, neg_smul, ← sub_eq_add_neg]

theorem Bm_mul_Am {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : Bm s y * Am s y = 1 + herm y * herm y := by
  unfold Am Bm
  simp only [add_mul, mul_sub, one_mul, mul_one, smul_mul_smul_comm, Is_sq hs, neg_one_smul]
  abel

theorem Am_mul_Bm {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : Am s y * Bm s y = 1 + herm y * herm y := by
  unfold Am Bm
  simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, Is_sq hs, neg_one_smul]
  abel

theorem posDef_one_add (y : E n) : (1 + herm y * herm y).PosDef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (herm y)
  rw [herm_conjTranspose] at h
  exact Matrix.PosDef.one.add_posSemidef h

theorem det_one_add_eq (y : E n) : (1 + herm y * herm y).det = ((dP y : ℝ) : ℂ) := by
  have h := (posDef_one_add y).det_pos
  rw [Complex.lt_def] at h
  apply Complex.ext
  · simp [dP]
  · simp only [Complex.ofReal_im]
    simpa using h.2.symm

theorem dP_pos (y : E n) : 0 < dP y := by
  have h := (posDef_one_add y).det_pos
  rw [Complex.lt_def] at h
  simpa [dP] using h.1

theorem det_Bm_mul_det_Am {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) :
    (Bm s y).det * (Am s y).det = ((dP y : ℝ) : ℂ) := by
  rw [← det_mul, Bm_mul_Am hs, det_one_add_eq]

theorem det_Am_ne {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : (Am s y).det ≠ 0 := by
  intro h
  have h2 := det_Bm_mul_det_Am hs y
  rw [h, mul_zero] at h2
  exact (dP_pos y).ne' (by exact_mod_cast h2.symm)

theorem det_Bm_ne {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : (Bm s y).det ≠ 0 := by
  intro h
  have h2 := det_Bm_mul_det_Am hs y
  rw [h, zero_mul] at h2
  exact (dP_pos y).ne' (by exact_mod_cast h2.symm)

theorem uM_eq (s : ℂ) (y : E n) : uM s y = (Am s y)⁻¹ := rfl

theorem vM_eq (s : ℂ) (y : E n) : vM s y = (Bm s y)⁻¹ := rfl

theorem star_dot_self (v : Fin n → ℂ) : (star v ⬝ᵥ v) = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Complex.conj_mul' (v i)

theorem norm_sq_ge {M : Matrix (Fin n) (Fin n) ℂ} (y : E n) (hM : Mᴴ * M = 1 + herm y * herm y) (x : Fin n → ℂ) :
    ∑ i, ‖x i‖ ^ 2 ≤ ∑ i, ‖(M *ᵥ x) i‖ ^ 2 := by
  have key : ((∑ i, ‖(M *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) =
      ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) + ((∑ i, ‖(herm y *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
    rw [← star_dot_self (M *ᵥ x), ← star_dot_self x, ← star_dot_self (herm y *ᵥ x)]
    simp only [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hM, herm_conjTranspose, add_mulVec, one_mulVec,
      dotProduct_add]
  have key' : ∑ i, ‖(M *ᵥ x) i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 + ∑ i, ‖(herm y *ᵥ x) i‖ ^ 2 := by
    exact_mod_cast key
  rw [key']
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => by positivity)

theorem norm_entry_le {M : Matrix (Fin n) (Fin n) ℂ} (y : E n) (hM : Mᴴ * M = 1 + herm y * herm y)
    (hd : M.det ≠ 0) (a b : Fin n) : ‖M⁻¹ a b‖ ≤ 1 := by
  have hMx : M *ᵥ (M⁻¹ *ᵥ Pi.single b 1) = Pi.single b 1 := by
    rw [mulVec_mulVec, mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hd), one_mulVec]
  have h1 := norm_sq_ge y hM (M⁻¹ *ᵥ Pi.single b 1)
  rw [hMx] at h1
  have hsum1 : ∑ i, ‖(Pi.single b (1 : ℂ) : Fin n → ℂ) i‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  have hxa : (M⁻¹ *ᵥ Pi.single b 1) a = M⁻¹ a b := by
    simp [mulVec, dotProduct, Pi.single_apply]
  have h2 : ‖M⁻¹ a b‖ ^ 2 ≤ 1 := by
    rw [← hxa, ← hsum1]
    refine le_trans ?_ h1
    exact Finset.single_le_sum (f := fun i => ‖(M⁻¹ *ᵥ Pi.single b 1) i‖ ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ a)
  nlinarith [norm_nonneg (M⁻¹ a b)]

theorem norm_uM_le {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (a b : Fin n) : ‖uM s y a b‖ ≤ 1 := by
  rw [uM_eq]
  exact norm_entry_le y (by rw [Am_conjTranspose hs, Bm_mul_Am hs]) (det_Am_ne hs y) a b

theorem norm_vM_le {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (a b : Fin n) : ‖vM s y a b‖ ≤ 1 := by
  rw [vM_eq]
  exact norm_entry_le y (by rw [Bm_conjTranspose hs, Am_mul_Bm hs]) (det_Bm_ne hs y) a b

theorem norm_det_Am_sq {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ‖(Am s y).det‖ ^ 2 = dP y := by
  have h := det_Bm_mul_det_Am hs y
  rw [← Am_conjTranspose hs, det_conjTranspose] at h
  have h2 : star (Am s y).det * (Am s y).det = ((‖(Am s y).det‖ : ℂ)) ^ 2 := Complex.conj_mul' _
  rw [h2] at h
  exact_mod_cast h

theorem norm_det_Bm_sq {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ‖(Bm s y).det‖ ^ 2 = dP y := by
  have h := det_Bm_mul_det_Am hs y
  rw [← Bm_conjTranspose hs, det_conjTranspose, mul_comm] at h
  have h2 : star (Bm s y).det * (Bm s y).det = ((‖(Bm s y).det‖ : ℂ)) ^ 2 := Complex.conj_mul' _
  rw [h2] at h
  exact_mod_cast h

theorem norm_det_uM_sq {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ‖(uM s y).det‖ ^ 2 = (dP y)⁻¹ := by
  rw [uM_eq, det_nonsing_inv, Ring.inverse_eq_inv, norm_inv, inv_pow, norm_det_Am_sq hs]

theorem norm_det_vM_sq {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) : ‖(vM s y).det‖ ^ 2 = (dP y)⁻¹ := by
  rw [vM_eq, det_nonsing_inv, Ring.inverse_eq_inv, norm_inv, inv_pow, norm_det_Bm_sq hs]

theorem norm_det_pow {x : ℂ} {d : ℝ} (hd : 0 < d) (h : ‖x‖ ^ 2 = d⁻¹) (p : ℕ) : ‖x ^ p‖ = d ^ (-(p : ℝ) / 2) := by
  have h1 : (d ^ (-(1 : ℝ) / 2)) ^ 2 = d⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
    norm_num
    exact Real.rpow_neg_one d
  have h2 : 0 ≤ d ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hd.le _
  have hx : ‖x‖ = d ^ (-(1 : ℝ) / 2) := (pow_left_inj₀ (norm_nonneg _) h2 two_ne_zero).mp (h.trans h1.symm)
  rw [norm_pow, hx, ← Real.rpow_natCast, ← Real.rpow_mul hd.le]
  congr 1
  ring

end PositivityTheory.Rg.Sw.WR.B
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsGainBSt
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev Mc (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def cpart (i j : Fin n) (F : Mc n → ℂ) : Mc n → ℂ := fun b => fderiv ℂ F b (Matrix.single i j 1)

def word (L : List (Fin n × Fin n)) (F : Mc n → ℂ) : Mc n → ℂ := L.foldr (fun ij g => cpart ij.1 ij.2 g) F

def DeltaC (F : Mc n → ℂ) : Mc n → ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.finRange n).foldr (fun k g => cpart (σ k) k g) F

def Fr (s : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (b : Mc n) : ℂ :=
  (1 - (Complex.I * s) • b)⁻¹.det ^ p * (1 + (Complex.I * s) • b)⁻¹.det ^ q *
    MvPolynomial.eval (fun k => if k.1 then (1 + (Complex.I * s) • b)⁻¹ k.2.1 k.2.2 else (1 - (Complex.I * s) • b)⁻¹ k.2.1 k.2.2) R

def Ugood (s : ℂ) : Set (Mc n) := {b | IsUnit (1 - (Complex.I * s) • b).det ∧ IsUnit (1 + (Complex.I * s) • b).det}

def pdisc (b₀ : Mc n) (ρ : Fin n → Fin n → ℝ) : Set (Mc n) := {b | ∀ i j, ‖b i j - b₀ i j‖ ≤ ρ i j}

def CauchyW : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U →
    ∀ (b₀ : Mc n) (ρ : Fin n → Fin n → ℝ), (∀ i j, 0 < ρ i j) → pdisc b₀ ρ ⊆ U →
    ∀ M : ℝ, (∀ b ∈ pdisc b₀ ρ, ‖F b‖ ≤ M) → ∀ L : List (Fin n × Fin n),
      ‖word L F b₀‖ ≤ (L.map fun ij => (L.length : ℝ) / ρ ij.1 ij.2).prod * M

def Invar : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U →
    ∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ N : ℕ, ∀ b, k * b * kᴴ ∈ U →
      (DeltaC^[N] (fun c => F (k * c * kᴴ))) b = (DeltaC^[N] F) (k * b * kᴴ)

def PBound : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ),
    IsOpen (Ugood (n := n) s) ∧ ContDiffOn ℂ (⊤ : ℕ∞) (Fr s p q R) (Ugood s) ∧
    ∃ (c₀ C : ℝ), 0 < c₀ ∧ ∀ (k : Mc n), k ∈ Matrix.unitaryGroup (Fin n) ℂ → ∀ (lam : Fin n → ℝ),
      ∀ b ∈ pdisc (Matrix.diagonal fun i => (lam i : ℂ)) (fun i j => c₀ * Real.sqrt ((1 + |lam i|) * (1 + |lam j|))),
        k * b * kᴴ ∈ Ugood s ∧ ‖Fr s p q R (k * b * kᴴ)‖ ≤ C * (∏ i, (1 + |lam i|)) ^ (-((p + q : ℕ) : ℝ))

def Link : Prop :=
  ∀ (n : ℕ) (F : Mc n → ℂ) (U : Set (Mc n)), IsOpen U → ContDiffOn ℂ (⊤ : ℕ∞) F U → (∀ y, herm y ∈ U) →
    (∀ N y, (Delta^[N] (fun y => F (herm y))) y = (DeltaC^[N] F) (herm y)) ∧
    ∀ N : ℕ, ∀ b ∈ U, (DeltaC^[N] F) b = ∑ τ : Fin N → Equiv.Perm (Fin n),
      ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ) *
        word ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => (τ j k, k)) F b

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsGainSt
section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

abbrev MC (n : ℕ) := Fin n → Fin n → ℂ

def eU (a b : Fin n) : MC n := fun i j => if i = a ∧ j = b then 1 else 0

def cay (F : MC n → ℂ) (B : MC n) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * iteratedFDeriv ℂ n F B (fun k => eU (σ k) k)

def OmS (s : ℂ) : Set (MC n) :=
  {B | (1 - (Complex.I * s) • Matrix.of B).det ≠ 0 ∧ (1 + (Complex.I * s) • Matrix.of B).det ≠ 0 ∧
    (1 + Matrix.of B * Matrix.of B).det ∈ Complex.slitPlane}

def clsC (s z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (B : MC n) : ℂ :=
  Complex.exp (-z * Complex.log (1 + Matrix.of B * Matrix.of B).det) *
    ((1 - (Complex.I * s) • Matrix.of B)⁻¹).det ^ p * ((1 + (Complex.I * s) • Matrix.of B)⁻¹).det ^ q *
    MvPolynomial.eval (fun k => if k.1 then (1 + (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2
      else (1 - (Complex.I * s) • Matrix.of B)⁻¹ k.2.1 k.2.2) R

def Ext : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → IsOpen (OmS (n := n) s) ∧ (∀ y : E n, (herm y : MC n) ∈ OmS s) ∧
    ∀ (z : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ),
      AnalyticOnNhd ℂ (clsC s z p q R) (OmS s) ∧ ∀ y, clsC s z p q R (herm y) = cls s z p q R y

def Chain : Prop :=
  ∀ (n : ℕ) (U : Set (MC n)) (F : MC n → ℂ), IsOpen U → (∀ y : E n, (herm y : MC n) ∈ U) → AnalyticOnNhd ℂ F U →
    ∀ N y, (Delta^[N] (fun y : E n => F (herm y))) y = (cay^[N] F) (herm y)

end PositivityTheory.Rg.Sw.WR.Z
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DensDefs
section
noncomputable section

open MeasureTheory

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def hinv (T : Matrix (Fin n) (Fin n) ℂ) : E n := fun i j => (T i j).re + (T i j).im

def ip (y y' : E n) : ℝ := ∑ a, ∑ b, y a b * y' a b

def qX (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : E n := hinv (gramX ε x)

def detQ (ε : Fin m → Bool) : PX m n := (Matrix.of fun i j => Qp ε i j).det

def FP (ε : Fin m → Bool) (c t : ℝ) (P : PX m n) (y : E n) : ℂ :=
  ∫ x, evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x))

def AlgA : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool), (∀ (y : E n) (x : Fin m → Fin n → ℂ),
      (herm y * gramX ε x).trace = (ip y (qX ε x) : ℂ)) ∧
    (∀ x : Fin m → Fin n → ℂ, herm (qX ε x) = gramX ε x) ∧ (∀ y : E n, hinv (herm y) = y) ∧
    (∀ x : Fin m → Fin n → ℂ, evX (detQ ε) x = (gramX ε x).det) ∧ Continuous (qX (n := n) ε)

def IntG : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ P : PX m n, Integrable (fun x => evX P x * gs c x)

def DerivF : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ (P : PX m n) (N : ℕ),
    Continuous (FP ε c t P) ∧
    Delta^[N] (FP ε c t P) = FP ε c t ((MvPolynomial.C ((Complex.I * t) ^ n) * detQ ε) ^ N * P)

def MollId : Prop :=
  ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (μ : Measure X) [SFinite μ] (Ψ : X → ℂ) (qq : X → E n), Integrable Ψ μ →
    Measurable qq → ∀ t : ℝ, t ≠ 0 →
    Integrable (fun y : E n => ∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) →
    ∀ ψ : E n → ℂ, Continuous ψ → HasCompactSupport ψ →
      ∫ x, ψ (qq x) * Ψ x ∂μ = ∫ β, ψ β * (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) *
        ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * Complex.exp (-(Complex.I * t * ip β y)))

end PositivityTheory.Rg.Sw.WR.D
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DifferentiableOfTop
section
noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.WR.T

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def FD (L : List (Fin n × Fin n)) (f : E n → ℂ) : E n → ℂ := L.foldr (fun kl g => Dkl kl.1 kl.2 g) f

theorem FD_cons (kl : Fin n × Fin n) (L : List (Fin n × Fin n)) (f : E n → ℂ) :
    FD (kl :: L) f = Dkl kl.1 kl.2 (FD L f) := rfl

theorem FD_append (L L' : List (Fin n × Fin n)) (f : E n → ℂ) : FD (L ++ L') f = FD L (FD L' f) := by
  simp [FD, List.foldr_append]

theorem contDiff_dirC {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : Fin n → Fin n → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (dirC f w) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := (contDiff_infty_iff_fderiv.1 hf).2
  have ha : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ f y (fun a b => (w a b).re)) := h1.clm_apply contDiff_const
  have hb : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ f y (fun a b => (w a b).im)) := h1.clm_apply contDiff_const
  exact ha.add (contDiff_const.mul hb)

theorem contDiff_Dkl {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k l : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (Dkl k l f) := contDiff_dirC hf _

theorem contDiff_FD {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (L : List (Fin n × Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (FD L f) := by
  induction L with
  | nil => exact hf
  | cons kl L ih => exact contDiff_Dkl ih _ _

theorem differentiable_of_top {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Differentiable ℝ f :=
  hf.differentiable (by simp)

theorem Dkl_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → E n → ℂ) (hF : ∀ i ∈ s, Differentiable ℝ (F i))
    (k l : Fin n) : Dkl k l (fun y => ∑ i ∈ s, c i * F i y) = fun y => ∑ i ∈ s, c i * Dkl k l (F i) y := by
  funext y
  unfold Dkl dirC
  have hfun : (fun y => ∑ i ∈ s, c i * F i y) = ∑ i ∈ s, (fun y => c i * F i y) := by
    funext y; simp [Finset.sum_apply]
  rw [hfun, fderiv_sum (fun i hi => ((hF i hi) y).const_mul (c i))]
  have e : ∀ i ∈ s, fderiv ℝ (fun y => c i * F i y) y = c i • fderiv ℝ (F i) y :=
    fun i hi => fderiv_const_mul ((hF i hi) y) (c i)
  rw [Finset.sum_congr rfl e]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem FD_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → E n → ℂ) (hF : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (L : List (Fin n × Fin n)) : FD L (fun y => ∑ i ∈ s, c i * F i y) = fun y => ∑ i ∈ s, c i * FD L (F i) y := by
  induction L with
  | nil => rfl
  | cons kl L ih =>
    rw [FD_cons, ih]
    exact Dkl_sum s c (fun i => FD L (F i)) (fun i hi => differentiable_of_top (contDiff_FD (hF i hi) L)) _ _

def Ls (σ : Equiv.Perm (Fin n)) : List (Fin n × Fin n) := (List.finRange n).map fun k => (k, σ k)

theorem Delta_eq (f : E n → ℂ) :
    Delta f = fun y => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * FD (Ls σ) f y := by
  funext y
  simp only [Delta, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, FD, Ls, List.foldr_map]

def Good (f : E n → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ ∀ L : List (Fin n × Fin n), ∃ h : E n → ℝ, Integrable h ∧ ∀ y, ‖FD L f y‖ ≤ h y

theorem good_FD {f : E n → ℂ} (hf : Good f) (L : List (Fin n × Fin n)) : Good (FD L f) := by
  refine ⟨contDiff_FD hf.1 L, fun L' => ?_⟩
  rw [← FD_append]
  exact hf.2 _

theorem good_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → E n → ℂ) (hF : ∀ i ∈ s, Good (F i)) :
    Good (fun y => ∑ i ∈ s, c i * F i y) := by
  refine ⟨?_, fun L => ?_⟩
  · exact ContDiff.sum fun i hi => contDiff_const.mul (hF i hi).1
  · rw [FD_sum s c F (fun i hi => (hF i hi).1) L]
    have : ∀ i ∈ s, ∃ h : E n → ℝ, Integrable h ∧ ∀ y, ‖FD L (F i) y‖ ≤ h y := fun i hi => (hF i hi).2 L
    choose! h hint hb using this
    refine ⟨fun y => ∑ i ∈ s, ‖c i‖ * h i y, MeasureTheory.integrable_finsetSum s fun i hi => (hint i hi).const_mul _, fun y => ?_⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb i hi y) (norm_nonneg _)

theorem good_Delta {f : E n → ℂ} (hf : Good f) : Good (Delta f) := by
  rw [Delta_eq]
  exact good_sum _ _ _ fun σ _ => good_FD hf _

theorem good_iter {f : E n → ℂ} (hf : Good f) (k : ℕ) : Good (Delta^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact good_Delta ih

theorem ibp_iter (hIBP : IBP) {f : E n → ℂ} (hf : Good f) (t : ℝ) (β : E n) (ht : t ≠ 0) (hβ : (herm β).det ≠ 0)
    (N : ℕ) : ∫ y, f y * chr t β y =
      ((-1) ^ n * ((-(Complex.I * t)) ^ n * (herm β).det)⁻¹) ^ N * ∫ y, (Delta^[N] f) y * chr t β y := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, hIBP n (Delta^[N] f) t β (good_iter hf N).1 ht hβ (good_iter hf N).2, Function.iterate_succ_apply', pow_succ]
    ring

end PositivityTheory.Rg.Sw.WR.T
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussS
section
noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def Amat (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (a : Fin m) : Matrix (Fin n) (Fin n) ℂ :=
  (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (Complex.I * t * sgn ε a) • bᵀ

def IntegP : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ P : PX m n, Integrable fun x : Fin m → Fin n → ℂ => evX P x * gs c x

def Wick : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian →
    ∀ (M : PX m n) (a : Fin m) (i : Fin n),
      secN ε c t (X (a, i, true) * M) b = ∑ j, (Amat ε c t b a)⁻¹ j i * secN ε c t (pderiv (a, j, false) M) b

def Rot : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian →
    ∀ d : (Fin m × Fin n × Bool) →₀ ℕ, (∀ k, k.2.2 = true → d k = 0) → d ≠ 0 →
      secN ε c t (monomial d 1) b = 0

def Base : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ), 0 < c → ∀ b : Matrix (Fin n) (Fin n) ℂ, b.IsHermitian →
    secN ε c t 1 b = ∏ a, ((Real.pi : ℂ) ^ n / (Amat ε c t b a).det)

end PositivityTheory.Rg.Sw.WR.G
end
end

