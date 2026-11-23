module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermApply
section
noncomputable def UpperTheory.Reformulated.B.Yoa6.HasSesq :
    {G V : Type} → [inst : Group G] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → Prop :=
    fun {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V] (π : Representation ℂ G V) ↦
      ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
        B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
          ∀ (g : G) (v w : V),
            ((B : V → V →ₗ⋆[ℂ] ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) w) =
              ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w

namespace UpperTheory.Reformulated.B.Yoa6.Helpers

private noncomputable def herm {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (c : ℂ) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => c * B v w + starRingEnd ℂ c * starRingEnd ℂ (B w v))
    (by intro v v' w; simp only [map_add (f := _), LinearMap.add_apply]; ring)
    (by intro a v w; simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, map_mul, Complex.conj_conj]; ring)
    (by intro v w w'; simp only [map_add (f := _), LinearMap.add_apply]; ring)
    (by intro a v w; simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, map_mul, Complex.conj_conj]; ring)

private lemma herm_apply {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (c : ℂ) (v w : V) :
    herm B c v w = c * B v w + starRingEnd ℂ c * starRingEnd ℂ (B w v) := rfl

end UpperTheory.Reformulated.B.Yoa6.Helpers

open UpperTheory.Reformulated.B.Yoa6.Helpers in
theorem UpperTheory.Reformulated.B.Yoa6.main :
    ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] {ρ : Representation ℂ G V},
      UpperTheory.Reformulated.B.Yoa6.HasSesq ρ →
        ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
          B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
            (∀ (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) w : V → ℂ) v = (starRingEnd ℂ : ℂ → ℂ) (((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w)) ∧
              ∀ (g : G) (v w : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((ρ : G → V →ₗ[ℂ] V) g : V → V) w) =
                  ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w := by
  intro G V _ _ _ ρ h
  obtain ⟨B, hB0, hBinv⟩ := h
  have hherm : ∀ (c : ℂ) (v w : V), herm B c w v = starRingEnd ℂ (herm B c v w) := by
    intro c v w
    simp only [herm_apply, map_add (f := _), map_mul, Complex.conj_conj]
    ring
  have hinv : ∀ (c : ℂ) (g : G) (v w : V), herm B c (ρ g v) (ρ g w) = herm B c v w := by
    intro c g v w
    simp only [herm_apply, hBinv]
  by_cases h1 : herm B 1 = 0
  · refine ⟨herm B Complex.I, ?_, hherm Complex.I, hinv Complex.I⟩
    intro hI
    apply hB0
    ext v w
    have e1 := congrArg (fun f => f v w) h1
    have e2 := congrArg (fun f => f v w) hI
    simp only [herm_apply, LinearMap.zero_apply, map_one, one_mul, Complex.conj_I] at e1 e2
    simp only [LinearMap.zero_apply]
    have : (2 * Complex.I) * B v w = 0 := by
      linear_combination Complex.I * e1 + e2
    rcases mul_eq_zero.mp this with h | h
    · exfalso; simp [Complex.ext_iff] at h
    · exact h
  · exact ⟨herm B 1, h1, hherm 1, hinv 1⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianBlockDiagonal
section
private lemma ad_mul {S : Type} [CommRing S] (τ : S →+* S) {a b c : ℕ}
    (A : Matrix (Fin a) (Fin b) S) (B : Matrix (Fin b) (Fin c) S) :
    ((A * B).map τ).transpose = (B.map τ).transpose * (A.map τ).transpose := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

private lemma ad_add {S : Type} [CommRing S] (τ : S →+* S) {a b : ℕ}
    (A B : Matrix (Fin a) (Fin b) S) :
    ((A + B).map τ).transpose = (A.map τ).transpose + (B.map τ).transpose := by
  ext i j
  simp

private lemma ad_ad {S : Type} [CommRing S] (τ : S →+* S) (hτ : ∀ x, τ (τ x) = x) {a b : ℕ}
    (A : Matrix (Fin a) (Fin b) S) :
    (((A.map τ).transpose).map τ).transpose = A := by
  ext i j
  simp [hτ]

private lemma ad_one {S : Type} [CommRing S] (τ : S →+* S) {a : ℕ} :
    (((1 : Matrix (Fin a) (Fin a) S)).map τ).transpose = 1 := by
  rw [Matrix.map_one τ (map_zero τ) (map_one τ), Matrix.transpose_one]

private lemma ad_diag_mul {S : Type} [CommRing S] (τ : S →+* S) {r : ℕ} (u v : Fin r → S)
    (h : ∀ i, τ (u i) * v i = 1) :
    ((Matrix.diagonal u).map τ).transpose * Matrix.diagonal v = 1 := by
  rw [Matrix.diagonal_map (map_zero τ), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact h i

theorem UpperTheory.hermitian_block_diagonal :
    ∀ {S : Type} [CommRing S] (τ : S →+* S), (∀ x, τ (τ x) = x) → ∀ {n r : ℕ}
        (J g P m : Matrix (Fin n) (Fin n) S) (X Y : Matrix (Fin n) (Fin r) S)
        (C : Matrix (Fin r) (Fin r) S) (Xd Yd : Matrix (Fin r) (Fin n) S) (d e : Fin r → S),
        (J.map τ).transpose = J → IsUnit J.det →
        Xd = (X.map τ).transpose * J → Yd = (Y.map τ).transpose * J →
        Xd * X = 0 → Yd * Y = 0 → Xd * Y = 1 →
        (g.map τ).transpose * J * g = J →
        Xd * g = C * Xd →
        (∀ i, τ (e i) * d i = 1) →
        P = 1 - X * Yd - Y * Xd →
        m = (X * Matrix.diagonal d) * Yd + (Y * Matrix.diagonal e) * Xd + P * g * P →
        IsUnit m.det ∧ (m.map τ).transpose * J * m = J ∧
          m * X = X * Matrix.diagonal d ∧ m * Y = Y * Matrix.diagonal e := by
  intro S _ τ hτ n r J g P m X Y C Xd Yd d e hJ hdet hXd hYd hXX hYY hXY hg hC hde hP hm
  have adXd : (Xd.map τ).transpose = J * X := by rw [hXd, ad_mul, hJ, ad_ad τ hτ]
  have adYd : (Yd.map τ).transpose = J * Y := by rw [hYd, ad_mul, hJ, ad_ad τ hτ]
  have hYX : Yd * X = 1 := by
    have h := congrArg (fun A => (A.map τ).transpose) hXY
    simp only [ad_mul, adXd, ad_one] at h
    rw [hYd, Matrix.mul_assoc, h]
  have hed : ((Matrix.diagonal e).map τ).transpose * Matrix.diagonal d = 1 :=
    ad_diag_mul τ e d hde
  have hdeD : ((Matrix.diagonal d).map τ).transpose * Matrix.diagonal e = 1 :=
    ad_diag_mul τ d e (fun i => by
      have h := congrArg τ (hde i)
      rw [map_mul, hτ, map_one, mul_comm] at h
      exact h)
  have XX : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), Xd * (X * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, hXX, Matrix.zero_mul]
  have YY : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), Yd * (Y * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, hYY, Matrix.zero_mul]
  have XY : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), Xd * (Y * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hXY, Matrix.one_mul]
  have YX : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), Yd * (X * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hYX, Matrix.one_mul]
  have PX : P * X = 0 := by
    rw [hP]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hYX, hXX, Matrix.mul_one,
      Matrix.mul_zero, sub_self, sub_zero]
  have PY : P * Y = 0 := by
    rw [hP]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hYY, hXY, Matrix.mul_one,
      Matrix.mul_zero, sub_zero, sub_self]
  have XdP : Xd * P = 0 := by
    rw [hP]
    simp only [Matrix.mul_sub, Matrix.mul_one, XX, XY, sub_zero, sub_self]
  have YdP : Yd * P = 0 := by
    rw [hP]
    simp only [Matrix.mul_sub, Matrix.mul_one, YX, YY, sub_zero, sub_self]
  have PP : P * P = P := by
    calc P * P = (1 - X * Yd - Y * Xd) * P := by rw [← hP]
      _ = P := by
        simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, YdP, XdP, Matrix.mul_zero,
          sub_zero]
  have PX' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), P * (X * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, PX, Matrix.zero_mul]
  have PY' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), P * (Y * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, PY, Matrix.zero_mul]
  have XdP' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S), Xd * (P * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, XdP, Matrix.zero_mul]
  have YdP' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S), Yd * (P * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, YdP, Matrix.zero_mul]
  have PP' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S), P * (P * A) = P * A := fun A => by
    rw [← Matrix.mul_assoc, PP]
  have hed' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S),
      ((Matrix.diagonal e).map τ).transpose * (Matrix.diagonal d * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hed, Matrix.one_mul]
  have hde' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S),
      ((Matrix.diagonal d).map τ).transpose * (Matrix.diagonal e * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hdeD, Matrix.one_mul]
  have hmX : m * X = X * Matrix.diagonal d := by
    rw [hm]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hYX, hXX, PX, Matrix.mul_one, Matrix.mul_zero,
      add_zero]
  have hmY : m * Y = Y * Matrix.diagonal e := by
    rw [hm]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hYY, hXY, PY, Matrix.mul_one, Matrix.mul_zero,
      add_zero, zero_add]
  have hPJ : (P.map τ).transpose * J = J * P := by
    have hPe : P + X * Yd + Y * Xd = 1 := by rw [hP]; abel
    have h := congrArg (fun A => (A.map τ).transpose) hPe
    simp only [ad_add, ad_mul, adXd, adYd, ad_one] at h
    have h2 : (P.map τ).transpose = 1 - (J * Y) * (X.map τ).transpose
        - (J * X) * (Y.map τ).transpose := by
      rw [← h]; abel
    rw [h2, hP]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
      ← hXd, ← hYd]
    abel
  have hPJ' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S),
      (P.map τ).transpose * (J * A) = J * (P * A) := fun A => by
    rw [← Matrix.mul_assoc, hPJ, Matrix.mul_assoc]
  have hg' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S),
      (g.map τ).transpose * (J * (g * A)) = J * A := fun A => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg]
  have hgX : (g.map τ).transpose * (J * X) = J * (X * (C.map τ).transpose) := by
    have h := congrArg (fun A => (A.map τ).transpose) hC
    simp only [ad_mul, adXd] at h
    rw [h, Matrix.mul_assoc]
  have hgX' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S),
      (g.map τ).transpose * (J * (X * A)) = J * (X * ((C.map τ).transpose * A)) := fun A => by
    rw [← Matrix.mul_assoc J X A, ← Matrix.mul_assoc, hgX]
    simp only [Matrix.mul_assoc]
  have hC' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S), Xd * (g * A) = C * (Xd * A) := fun A => by
    rw [← Matrix.mul_assoc, hC, Matrix.mul_assoc]
  have hmid : (g.map τ).transpose * (J * (P * (g * P))) =
      J * P - J * (X * ((C.map τ).transpose * (Yd * (g * P)))) := by
    have hexp : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S),
        P * A = A - X * (Yd * A) - Y * (Xd * A) := fun A => by
      rw [hP]
      simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    rw [hexp (g * P)]
    simp only [Matrix.mul_sub, hg', hgX', hC', XdP, Matrix.mul_zero, sub_zero]
  have hadm : (m.map τ).transpose =
      (J * Y) * (((Matrix.diagonal d).map τ).transpose * (X.map τ).transpose)
        + (J * X) * (((Matrix.diagonal e).map τ).transpose * (Y.map τ).transpose)
        + (P.map τ).transpose * ((g.map τ).transpose * (P.map τ).transpose) := by
    rw [hm]
    simp only [ad_add, ad_mul, adXd, adYd, Matrix.mul_assoc]
  have hiso : (m.map τ).transpose * J * m = J := by
    have hmJ : (m.map τ).transpose * J =
        J * (Y * (((Matrix.diagonal d).map τ).transpose * Xd))
          + J * (X * (((Matrix.diagonal e).map τ).transpose * Yd))
          + (P.map τ).transpose * ((g.map τ).transpose * (J * P)) := by
      rw [hadm, hXd, hYd]
      simp only [Matrix.add_mul, Matrix.mul_assoc, hPJ]
    rw [hmJ]
    conv_lhs => rw [hm]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, XX, XY, YX, YY, XdP', YdP',
      PX', PY', PP', XdP, YdP, hed', hde', Matrix.mul_zero, add_zero, zero_add, hmid,
      Matrix.mul_sub, hPJ', PP]
    conv_rhs => rw [show J = J * (1 : Matrix (Fin n) (Fin n) S) from (Matrix.mul_one J).symm]
    rw [show (1 : Matrix (Fin n) (Fin n) S) = P + X * Yd + Y * Xd by rw [hP]; abel]
    simp only [Matrix.mul_add]
    abel
  refine ⟨?_, hiso, hmX, hmY⟩
  have h := congrArg Matrix.det hiso
  rw [Matrix.det_mul] at h
  rw [← h] at hdet
  exact isUnit_of_mul_isUnit_right hdet
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianBlockTriangular
section
theorem UpperTheory.hermitian_block_triangular :
    ∀ {S : Type} [CommRing S] (τ : S →+* S), (∀ x, τ (τ x) = x) → ∀ {n r : ℕ}
        (J g : Matrix (Fin n) (Fin n) S) (X Y : Matrix (Fin n) (Fin r) S)
        (B : Matrix (Fin r) (Fin r) S) (Xd Yd : Matrix (Fin r) (Fin n) S),
        (J.map τ).transpose = J →
        Xd = (X.map τ).transpose * J → Yd = (Y.map τ).transpose * J →
        Xd * Y = 1 →
        (g.map τ).transpose * J * g = J →
        B.BlockTriangular id → g * X = X * B →
        Yd * X = 1 ∧ Yd * g * X = B ∧ Xd * g = (Xd * g * Y) * Xd ∧
          ∀ i, τ ((Xd * g * Y) i i) * B i i = 1 := by
  intro S _ τ hτ n r J g X Y B Xd Yd hJ hXd hYd hXY hg hB hgX
  classical
  have star_mul : ∀ {a b c : ℕ} (P : Matrix (Fin a) (Fin b) S) (Q : Matrix (Fin b) (Fin c) S),
      ((P * Q).map τ).transpose = (Q.map τ).transpose * (P.map τ).transpose := by
    intro a b c P Q
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have star_star : ∀ {a b : ℕ} (P : Matrix (Fin a) (Fin b) S),
      (((P.map τ).transpose).map τ).transpose = P := by
    intro a b P
    ext i j
    simp [hτ]
  have star_one : (((1 : Matrix (Fin r) (Fin r) S)).map τ).transpose = 1 := by
    rw [Matrix.map_one τ (map_zero τ) (map_one τ), Matrix.transpose_one]
  have h1 : Yd * X = 1 := by
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) S => (M.map τ).transpose) hXY
    simp only [star_one] at h
    rw [star_mul, hXd, star_mul, star_star, hJ, ← Matrix.mul_assoc, ← hYd] at h
    exact h
  have h2 : Yd * g * X = B := by
    rw [Matrix.mul_assoc, hgX, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hs : (X.map τ).transpose * (g.map τ).transpose
      = (B.map τ).transpose * (X.map τ).transpose := by
    rw [← star_mul, ← star_mul, hgX]
  have hD : (B.map τ).transpose * (Xd * g) = Xd := by
    calc (B.map τ).transpose * (Xd * g)
        = ((B.map τ).transpose * (X.map τ).transpose) * J * g := by
          rw [hXd]; simp only [Matrix.mul_assoc]
      _ = (X.map τ).transpose * ((g.map τ).transpose * J * g) := by
          rw [← hs]; simp only [Matrix.mul_assoc]
      _ = Xd := by rw [hg, hXd]
  have hC : (B.map τ).transpose * (Xd * g * Y) = 1 := by
    rw [← Matrix.mul_assoc, hD, hXY]
  have hC' : (Xd * g * Y) * (B.map τ).transpose = 1 := mul_eq_one_comm.mp hC
  have h3 : Xd * g = (Xd * g * Y) * Xd := by
    calc Xd * g = ((Xd * g * Y) * (B.map τ).transpose) * (Xd * g) := by
          rw [hC', Matrix.one_mul]
      _ = (Xd * g * Y) * ((B.map τ).transpose * (Xd * g)) := by rw [Matrix.mul_assoc]
      _ = (Xd * g * Y) * Xd := by rw [hD]
  have h4 : ((Xd * g * Y).map τ).transpose * B = 1 := by
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) S => (M.map τ).transpose) hC
    simp only [star_one] at h
    rwa [star_mul, star_star] at h
  refine ⟨h1, h2, h3, fun i => ?_⟩
  letI : Invertible B := invertibleOfLeftInverse B _ h4
  have hinv : (B⁻¹) = ((Xd * g * Y).map τ).transpose := Matrix.inv_eq_left_inv h4
  have htri : (B⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hB
  have h5 := congrFun (congrFun h4 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h5
  · simpa only [Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply_eq] using h5
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have : (B⁻¹) i k = 0 := htri hlt
      rw [hinv] at this
      rw [this, zero_mul]
    · have : B k i = 0 := hB hgt
      rw [this, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianForm
section
noncomputable def UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm :
    {g : ℕ} → Matrix (Fin g) (Fin g) ℂ → (Fin g → ℂ) → (Fin g → ℂ) → ℂ :=
    fun {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) ↦ z ⬝ᵥ Hm.mulVec (Star.star w)

noncomputable def UpperTheory.Reformulated.B.HermitianFormImEqSum.hv :
    {n : ℕ} → Matrix (Fin n) (Fin n) ℂ → (Fin n → ℂ) → (Fin n → ℂ) → ℂ :=
    fun {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) ↦ Star.star y ⬝ᵥ M.mulVec x

private theorem UpperTheory.Reformulated.B.HermitianFormImEqSum.ext_span {V : Type} [AddCommGroup V] [Module ℝ V]
    (f h : V → ℝ) (S : Set V) (hS : Submodule.span ℝ S = ⊤)
    (fa : ∀ x y, f (x + y) = f x + f y) (fs : ∀ (c : ℝ) x, f (c • x) = c * f x)
    (ha : ∀ x y, h (x + y) = h x + h y) (hs : ∀ (c : ℝ) x, h (c • x) = c * h x)
    (H : ∀ a ∈ S, f a = h a) (x : V) : f x = h x := by
  have hx : x ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem a ha => exact H a ha
  | zero =>
    have h1 := fs 0 0
    have h2 := hs 0 0
    simp only [zero_smul, zero_mul] at h1 h2
    rw [h1, h2]
  | add a b _ _ h1 h2 => rw [fa, ha, h1, h2]
  | smul c a _ h1 => rw [fs, hs, h1]

private theorem UpperTheory.Reformulated.B.HermitianFormImEqSum.re_hermitian_combination_nonpos (c : ℝ) (a b : ℂ) : (a * (c • b)).re = c * (a * b).re := by
  rw [mul_smul_comm, Complex.smul_re, smul_eq_mul]

theorem UpperTheory.Reformulated.B.HermitianFormImEqSum.bil_eq :
    ∀ {P : Type} [inst : Fintype P] [DecidableEq P] {n g : ℕ} (R : (P → Fin n → ℂ) ≃ₗ[ℝ] Fin g → ℂ)
      (Hm : Matrix (Fin g) (Fin g) ℂ) (M : P → Matrix (Fin n) (Fin n) ℂ) (s : P → ℂ) (r : P → ℝ) (S : Set (P → Fin n → ℂ)),
      Submodule.span ℝ S = ⊤ →
        (∀ a ∈ S,
            ∀ b ∈ S,
              (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm ((R : (P → Fin n → ℂ) → Fin g → ℂ) a) ((R : (P → Fin n → ℂ) → Fin g → ℂ) b)).im =
                ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (a v) (b v)).re) →
          ∀ (x y : P → Fin n → ℂ),
            (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm ((R : (P → Fin n → ℂ) → Fin g → ℂ) x) ((R : (P → Fin n → ℂ) → Fin g → ℂ) y)).im =
              ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (x v) (y v)).re := by
  intro P _ _ n g R Hm M s r S hS H x y
  have step : ∀ a ∈ S, ∀ y : P → Fin n → ℂ,
      (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm (R a) (R y)).im =
        ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (a v) (y v)).re := by
    intro a ha y
    refine UpperTheory.Reformulated.B.HermitianFormImEqSum.ext_span (fun y => (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm (R a) (R y)).im)
      (fun y => ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (a v) (y v)).re)
      S hS ?_ ?_ ?_ ?_ (H a ha) y
    · intro u w
      simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm, map_add (f := _), star_add, Matrix.mulVec_add, dotProduct_add,
        Complex.add_im]
    · intro c u
      simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm, map_smul, star_smul, star_trivial, Matrix.mulVec_smul,
        dotProduct_smul, Complex.smul_im, smul_eq_mul]
    · intro u w
      simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hv, Pi.add_apply, star_add, add_dotProduct, mul_add,
        Complex.add_re, Finset.sum_add_distrib]
    · intro c u
      simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hv, Pi.smul_apply, star_smul, star_trivial, smul_dotProduct,
        UpperTheory.Reformulated.B.HermitianFormImEqSum.re_hermitian_combination_nonpos, Finset.mul_sum, mul_left_comm c]
  refine UpperTheory.Reformulated.B.HermitianFormImEqSum.ext_span (fun x => (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm (R x) (R y)).im)
    (fun x => ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (x v) (y v)).re)
    S hS ?_ ?_ ?_ ?_ (fun a ha => step a ha y) x
  · intro u w
    simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm, map_add (f := _), add_dotProduct, Complex.add_im]
  · intro c u
    simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm, map_smul, smul_dotProduct, Complex.smul_im, smul_eq_mul]
  · intro u w
    simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hv, Pi.add_apply, Matrix.mulVec_add, dotProduct_add, mul_add,
      Complex.add_re, Finset.sum_add_distrib]
  · intro c u
    simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hv, Pi.smul_apply, Matrix.mulVec_smul, dotProduct_smul,
      UpperTheory.Reformulated.B.HermitianFormImEqSum.re_hermitian_combination_nonpos, Finset.mul_sum, mul_left_comm c]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianProjectionEq
section
theorem UpperTheory.hermitian_projection_eq :
    ∀ {S : Type} [CommRing S] {n r : ℕ}
        (g P m : Matrix (Fin n) (Fin n) S) (X Y : Matrix (Fin n) (Fin r) S)
        (B C : Matrix (Fin r) (Fin r) S) (Xd Yd : Matrix (Fin r) (Fin n) S) (d e : Fin r → S),
        Xd * X = 0 → Yd * Y = 0 → Xd * Y = 1 → Yd * X = 1 →
        B.BlockTriangular id → g * X = X * B → Xd * g = C * Xd →
        (∀ i, d i = B i i) → (∀ i, IsUnit (d i)) →
        P = 1 - X * Yd - Y * Xd →
        m = (X * Matrix.diagonal d) * Yd + (Y * Matrix.diagonal e) * Xd + P * g * P →
        IsUnit m.det →
        (∃ B' : Matrix (Fin r) (Fin r) S, B'.BlockTriangular id ∧ (∀ i, B' i i = 1) ∧
            m⁻¹ * g * X = X * B') ∧
          ∀ z : Fin n → S, Xd.mulVec z = 0 →
            ∃ a : Fin r → S, (m⁻¹ * g - 1).mulVec z = X.mulVec a := by
  intro S _ n r g P m X Y B C Xd Yd d e hXdX hYdY hXdY hYdX hB hgX hXdg hd hu hP hm hdet
  have hmm : m⁻¹ * m = 1 := Matrix.nonsing_inv_mul m hdet
  obtain ⟨f, hf⟩ : ∃ f : Fin r → S, ∀ i, f i * d i = 1 :=
    ⟨fun i => (((hu i).unit⁻¹ : Sˣ) : S), fun i => (hu i).val_inv_mul⟩
  have hDF : Matrix.diagonal d * Matrix.diagonal f = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hf i
  have hPX : P * X = 0 := by
    rw [hP, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, hYdX, hXdX,
      Matrix.mul_one, Matrix.mul_zero, sub_self, sub_zero]
  have hmX : m * X = X * Matrix.diagonal d := by
    rw [hm, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc _ Yd, Matrix.mul_assoc _ Xd, hYdX, hXdX,
      Matrix.mul_assoc _ P, hPX, Matrix.mul_one, Matrix.mul_zero, Matrix.mul_zero, add_zero,
      add_zero]
  have hinvX : m⁻¹ * X = X * Matrix.diagonal f := by
    calc m⁻¹ * X = m⁻¹ * (X * (Matrix.diagonal d * Matrix.diagonal f)) := by
          rw [hDF, Matrix.mul_one]
      _ = (m⁻¹ * m) * (X * Matrix.diagonal f) := by
          rw [← Matrix.mul_assoc X, ← hmX, Matrix.mul_assoc m, Matrix.mul_assoc m⁻¹]
      _ = X * Matrix.diagonal f := by rw [hmm, Matrix.one_mul]
  have hPgX : P * g * X = 0 := by
    rw [Matrix.mul_assoc, hgX, ← Matrix.mul_assoc, hPX, Matrix.zero_mul]
  have hPg : P * g = g - X * (Yd * g) - Y * C * Xd := by
    rw [hP, sub_mul, sub_mul, Matrix.one_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, hXdg,
      Matrix.mul_assoc Y]
  have hPgP : P * g * P = P * g - P * g * Y * Xd := by
    have h0 : P * g * P = P * g * (1 - X * Yd - Y * Xd) := by rw [← hP]
    rw [h0, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc _ X, hPgX,
      Matrix.zero_mul, sub_zero, ← Matrix.mul_assoc _ Y]
  have hid : g - m = X * (Yd * g - Matrix.diagonal d * Yd)
      + (Y * C - Y * Matrix.diagonal e + P * g * Y) * Xd := by
    rw [hm, hPgP, hPg]
    simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  refine ⟨⟨Matrix.diagonal f * B, ?_, ?_, ?_⟩, ?_⟩
  · intro i j hij
    rw [Matrix.diagonal_mul, hB hij, mul_zero]
  · intro i
    rw [Matrix.diagonal_mul, ← hd i]
    exact hf i
  · rw [Matrix.mul_assoc, hgX, ← Matrix.mul_assoc, hinvX, Matrix.mul_assoc]
  · intro z hz
    refine ⟨(Matrix.diagonal f * (Yd * g - Matrix.diagonal d * Yd)).mulVec z, ?_⟩
    have h1 : m⁻¹ * g - 1 = (X * Matrix.diagonal f) * (Yd * g - Matrix.diagonal d * Yd)
        + m⁻¹ * (Y * C - Y * Matrix.diagonal e + P * g * Y) * Xd := by
      calc m⁻¹ * g - 1 = m⁻¹ * (g - m) := by rw [Matrix.mul_sub, hmm]
        _ = _ := by
          rw [hid, Matrix.mul_add, ← Matrix.mul_assoc, hinvX, ← Matrix.mul_assoc]
    rw [h1, Matrix.add_mulVec, ← Matrix.mulVec_mulVec z _ Xd, hz, Matrix.mulVec_zero, add_zero,
      Matrix.mul_assoc X, Matrix.mulVec_mulVec]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisSide
section
theorem UpperTheory.Reformulated.B.DYlb8.main :
    ∀ {n : ℕ} {S : Finset (Fin n)}, (∀ (a b : Fin n), b ≤ a → a ∈ S → b ∈ S) → ∀ (a : Fin n), a ∈ S ↔ (↑a : ℕ) < S.card := by
  intro n S h a
  constructor
  · intro ha
    have hsub : Finset.Iic a ⊆ S := fun b hb => h a b (Finset.mem_Iic.mp hb) ha
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega
  · intro hlt
    by_contra ha
    have hsub : S ⊆ Finset.Iio a :=
      fun b hb => Finset.mem_Iio.mpr (lt_of_not_ge fun hab => ha (h b a hab hb))
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega
end

