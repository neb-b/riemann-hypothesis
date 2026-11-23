module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AntidiagonalTranspose
section
universe u_1 u_3

namespace UpperTheory.Reformulated.B.AntidiagonalTranspose

noncomputable def Jmat (R : Type u_1) [CommRing R] (m : ℕ) : Matrix (Fin m) (Fin m) R :=
  fun i j ↦ if j = i.rev then (1 : R) else (0 : R)

theorem aux2 {R : Type u_1} [CommRing R] (m : ℕ) :
    Jmat R m * Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  ext i j
  simp only [Matrix.mul_apply, Jmat, Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

noncomputable def Jgl (R : Type u_1) [CommRing R] (m : ℕ) : GL (Fin m) R :=
  { val := Jmat R m, inv := Jmat R m, val_inv := aux2 m, inv_val := aux2 m :
    (Matrix (Fin m) (Fin m) R)ˣ }

theorem aux4 {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) :
    (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem aux5 {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) :
    (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R]
    (g : GL n R) : GL n R :=
  { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose,
    val_inv := aux4 g, inv_val := aux5 g : (Matrix n n R)ˣ }

noncomputable def theta {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) : GL (Fin m) R :=
  Jgl R m * trInv g * Jgl R m

private theorem Jmat_transpose {R : Type u_1} [CommRing R] (m : ℕ) :
    (Jmat R m).transpose = Jmat R m := by
  ext i j
  simp only [Matrix.transpose_apply, Jmat]
  have : (i = j.rev) ↔ (j = i.rev) := by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [this]

private theorem Jgl_mul_self {R : Type u_1} [CommRing R] (m : ℕ) : Jgl R m * Jgl R m = 1 :=
  Units.ext (aux2 m)

private theorem Jgl_inv {R : Type u_1} [CommRing R] (m : ℕ) : (Jgl R m)⁻¹ = Jgl R m :=
  inv_eq_of_mul_eq_one_left (Jgl_mul_self m)

private theorem trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R]
    (g h : GL n R) : trInv (g * h) = trInv g * trInv h := by
  apply Units.ext
  change (((g * h)⁻¹ : GL n R) : Matrix n n R).transpose =
    (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R]
    (g : GL n R) : trInv (trInv g) = g := by
  apply Units.ext
  change (↑(trInv g)⁻¹ : Matrix n n R).transpose = ↑g
  change ((↑g : Matrix n n R).transpose).transpose = ↑g
  exact Matrix.transpose_transpose _

private theorem trInv_Jgl {R : Type u_1} [CommRing R] (m : ℕ) : trInv (Jgl R m) = Jgl R m := by
  apply Units.ext
  change (((Jgl R m)⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R).transpose = Jmat R m
  rw [Jgl_inv]
  exact Jmat_transpose m

theorem aux8 {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) : theta (theta g) = g := by
  have hJ := Jgl_mul_self (R := R) m
  simp only [theta, trInv_mul, trInv_trInv, trInv_Jgl]
  calc _ = (Jgl R m * Jgl R m) * g * (Jgl R m * Jgl R m) * (Jgl R m * Jgl R m) := by
        simp only [hJ, mul_one, one_mul]
        simp only [mul_assoc, hJ, mul_one]
        simp only [← mul_assoc, hJ, one_mul]
    _ = g := by simp [hJ]

theorem aux9 {m : ℕ} {R : Type u_1} [CommRing R] (g h : GL (Fin m) R) :
    theta (g * h) = theta g * theta h := by
  have hJ := Jgl_mul_self (R := R) m
  simp only [theta, trInv_mul]
  calc _ = Jgl R m * trInv g * 1 * trInv h * Jgl R m := by simp only [mul_one, mul_assoc]
    _ = _ := by rw [← hJ]; simp only [mul_assoc]

noncomputable def thetaAut (m : ℕ) (R : Type u_1) [CommRing R] : MulAut (GL (Fin m) R) :=
  { toFun := theta, invFun := theta, left_inv := aux8, right_inv := aux8, map_mul' := aux9 :
    GL (Fin m) R ≃* GL (Fin m) R }

private theorem thetaAut_sq (m : ℕ) (R : Type u_1) [CommRing R] :
    thetaAut m R * thetaAut m R = 1 := by
  ext1 g
  exact aux8 g

theorem aux11 (m : ℕ) (R : Type u_1) [CommRing R] :
    (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) =
      (1 : MulAut (GL (Fin m) R)) :=
  if_pos rfl

theorem aux12 (m : ℕ) (R : Type u_1) [CommRing R] (s t : ℤˣ) :
    (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) =
      (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) *
        if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · simp
  · simp
  · simp
  · simp [thetaAut_sq]

noncomputable def sgnAct (m : ℕ) (R : Type u_1) [CommRing R] : ℤˣ →* MulAut (GL (Fin m) R) :=
  { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R,
    map_one' := aux11 m R, map_mul' := aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def GG (m : ℕ) (R : Type u_1) [CommRing R] : Type u_1 :=
  GL (Fin m) R ⋊[sgnAct m R] ℤˣ

@[reducible] noncomputable def ofGL {m : ℕ} {R : Type u_1} [CommRing R] : GL (Fin m) R →* GG m R :=
  SemidirectProduct.inl

noncomputable def conjBy {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G]
    (h : GL (Fin m) R) (r : G →* GG m R) : G →* GG m R :=
  (MulAut.conj (ofGL h : GG m R)).toMonoidHom.comp r

theorem conj_right {G R : Type} [Group G] [CommRing R] {m : ℕ} (h : GL (Fin m) R)
    (r : G →* GG m R) (g : G) : (conjBy h r g).right = (r g).right := by
  simp [conjBy, MulAut.conj_apply]

end UpperTheory.Reformulated.B.AntidiagonalTranspose
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlockConjugation
section
noncomputable def UpperTheory.Reformulated.B.BlockConjugation.HasFlag :
    {H k : Type} → [inst : Group H] → [inst_1 : CommRing k] → {n : ℕ} → (H →* GL (Fin n) k) → (Fin n → H →* kˣ) → Prop :=
    fun {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k) (κ : Fin n → H →* kˣ) ↦
      ∃ (g : GL (Fin n) k),
        ∀ (s : H),
          (∀ (i j : Fin n), j < i → (↑(g * (r : H → GL (Fin n) k) s * g⁻¹) : Matrix (Fin n) (Fin n) k) i j = (0 : k)) ∧
            ∀ (i : Fin n),
              (↑(g * (r : H → GL (Fin n) k) s * g⁻¹) : Matrix (Fin n) (Fin n) k) i i = (↑((κ i : H → kˣ) s) : k)

private def UpperTheory.Reformulated.B.BlockConjugation.blk {k : Type} [CommRing k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  Matrix.of (Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (A i)))

private theorem UpperTheory.Reformulated.B.BlockConjugation.blk_mul {k : Type} [CommRing k] {n : ℕ} (A B : Matrix (Fin n) (Fin n) k) :
    UpperTheory.Reformulated.B.BlockConjugation.blk A * UpperTheory.Reformulated.B.BlockConjugation.blk B = UpperTheory.Reformulated.B.BlockConjugation.blk (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [UpperTheory.Reformulated.B.BlockConjugation.blk, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem UpperTheory.Reformulated.B.BlockConjugation.blk_one {k : Type} [CommRing k] {n : ℕ} :
    UpperTheory.Reformulated.B.BlockConjugation.blk (1 : Matrix (Fin n) (Fin n) k) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [UpperTheory.Reformulated.B.BlockConjugation.blk, Matrix.one_apply, (Fin.succ_ne_zero _).symm]

private theorem UpperTheory.Reformulated.B.BlockConjugation.exists_col {k : Type} [Field k] {n : ℕ} (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    ∃ Q : GL (Fin (n + 1)) k, ∀ i, (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i 0 = v i := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hv
  have hd : (((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol a v).submatrix id (Equiv.swap 0 a)).det ≠ 0 := by
    rw [Matrix.det_permute', ← Matrix.cramer_apply, Matrix.cramer_one]
    refine mul_ne_zero ?_ (by simpa using ha)
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap 0 a)) with h | h <;> simp [h]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, fun i => ?_⟩
  change (((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol a v).submatrix id (Equiv.swap 0 a)) i 0 = v i
  simp

private theorem UpperTheory.Reformulated.B.BlockConjugation.conj_blk {k : Type} [CommRing k] {n : ℕ} (A B : Matrix (Fin n) (Fin n) k)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hM : ∀ i : Fin n, M i.succ 0 = 0) :
    (UpperTheory.Reformulated.B.BlockConjugation.blk A * M * UpperTheory.Reformulated.B.BlockConjugation.blk B) 0 0 = M 0 0 ∧
    (∀ i : Fin n, (UpperTheory.Reformulated.B.BlockConjugation.blk A * M * UpperTheory.Reformulated.B.BlockConjugation.blk B) i.succ 0 = 0) ∧
    (∀ i j : Fin n, (UpperTheory.Reformulated.B.BlockConjugation.blk A * M * UpperTheory.Reformulated.B.BlockConjugation.blk B) i.succ j.succ =
      (A * M.submatrix Fin.succ Fin.succ * B) i j) := by
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩ <;>
    simp [UpperTheory.Reformulated.B.BlockConjugation.blk, Matrix.mul_apply, Fin.sum_univ_succ, hM]

theorem UpperTheory.Reformulated.B.BlockConjugation.exists_common_eigenline :
    ∀ {H k : Type} [inst : Group H] [inst_1 : TopologicalSpace H] [inst_2 : Field k] [inst_3 : TopologicalSpace k]
      [IsTopologicalRing k] {n : ℕ} (r : H →* GL (Fin (n + (1 : ℕ))) k) (κ : Fin (n + (1 : ℕ)) → H →* kˣ)
      (v : Fin (n + (1 : ℕ)) → k),
      Continuous (⇑r : H → GL (Fin (n + (1 : ℕ))) k) →
        v ≠ (0 : Fin (n + (1 : ℕ)) → k) →
          (∀ (g : H),
              (↑((r : H → GL (Fin (n + (1 : ℕ))) k) g) : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k).mulVec v =
                (↑((κ (0 : Fin (n + (1 : ℕ))) : H → kˣ) g) : k) • v) →
            ∃ (p : GL (Fin (n + (1 : ℕ))) k) (r₁ : H →* GL (Fin (n + (1 : ℕ))) k) (r' : H →* GL (Fin n) k),
              (∀ (g : H), (r₁ : H → GL (Fin (n + (1 : ℕ))) k) g = p * (r : H → GL (Fin (n + (1 : ℕ))) k) g * p⁻¹) ∧
                Continuous (⇑r₁ : H → GL (Fin (n + (1 : ℕ))) k) ∧
                  Continuous (⇑r' : H → GL (Fin n) k) ∧
                    (∀ (g : H) (i : Fin n),
                        (↑((r₁ : H → GL (Fin (n + (1 : ℕ))) k) g) : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) i.succ
                            (0 : Fin (n + (1 : ℕ))) =
                          (0 : k)) ∧
                      (∀ (g : H),
                          (↑((r₁ : H → GL (Fin (n + (1 : ℕ))) k) g) : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k)
                              (0 : Fin (n + (1 : ℕ))) (0 : Fin (n + (1 : ℕ))) =
                            (↑((κ (0 : Fin (n + (1 : ℕ))) : H → kˣ) g) : k)) ∧
                        (∀ (g : H) (i j : Fin n),
                            (↑((r₁ : H → GL (Fin (n + (1 : ℕ))) k) g) : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k)
                                i.succ j.succ =
                              (↑((r' : H → GL (Fin n) k) g) : Matrix (Fin n) (Fin n) k) i j) ∧
                          ((UpperTheory.Reformulated.B.BlockConjugation.HasFlag r' fun (i : Fin n) ↦ κ i.succ) → UpperTheory.Reformulated.B.BlockConjugation.HasFlag r κ) := by
  intro H k _ _ _ _ _ n r κ v hr hv hev
  obtain ⟨Q, hQ⟩ := UpperTheory.Reformulated.B.BlockConjugation.exists_col v hv
  let r₁ : H →* GL (Fin (n + 1)) k := (MulAut.conj Q⁻¹).toMonoidHom.comp r
  have hr₁ : ∀ g, r₁ g = Q⁻¹ * r g * Q⁻¹⁻¹ := fun g => rfl
  have hc₁ : Continuous r₁ := by
    have : (⇑r₁) = fun g => Q⁻¹ * r g * Q⁻¹⁻¹ := funext hr₁
    rw [this]
    exact (continuous_const.mul hr).mul continuous_const
  have hQv : (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) k).mulVec (Pi.single 0 1) = v := by
    ext i
    simp [hQ]
  have hcol : ∀ g i, (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i 0 =
      ((κ 0 g : k) • (Pi.single 0 1 : Fin (n + 1) → k)) i := by
    intro g i
    have h1 : (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k).mulVec (Pi.single 0 1) =
        ((κ 0 g : k) • (Pi.single 0 1 : Fin (n + 1) → k)) := by
      rw [hr₁, inv_inv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQv, hev,
        Matrix.mulVec_smul, ← hQv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [← h1]
    simp
  have h0 : ∀ g (i : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.succ 0 = 0 := by
    intro g i
    rw [hcol]
    simp
  have h00 : ∀ g, (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) 0 0 = (κ 0 g : k) := by
    intro g
    rw [hcol]
    simp
  let φ : H →* Matrix (Fin n) (Fin n) k :=
    { toFun := fun g => (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k).submatrix Fin.succ Fin.succ
      map_one' := by
        ext i j
        simp [Matrix.one_apply]
      map_mul' := fun a b => by
        ext i j
        rw [map_mul, Units.val_mul]
        simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_succ, h0, zero_mul, zero_add] }
  have hφ : ∀ g, φ g = (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k).submatrix Fin.succ Fin.succ := fun g => rfl
  refine ⟨Q⁻¹, r₁, φ.toHomUnits, hr₁, hc₁, ?_, h0, h00, fun g i j => rfl, ?_⟩
  · rw [Units.continuous_iff]
    refine ⟨(Units.continuous_val.comp hc₁).matrix_submatrix _ _, ?_⟩
    have : (fun g => (((φ.toHomUnits g)⁻¹ : (Matrix (Fin n) (Fin n) k)ˣ) : Matrix (Fin n) (Fin n) k)) =
        fun g => (((r₁ g)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k).submatrix
          Fin.succ Fin.succ := by
      funext g
      rw [← map_inv, ← map_inv]
      rfl
    rw [this]
    exact (Units.continuous_coe_inv.comp hc₁).matrix_submatrix _ _
  · rintro ⟨a, ha⟩
    let b : GL (Fin (n + 1)) k :=
      ⟨UpperTheory.Reformulated.B.BlockConjugation.blk (a : Matrix (Fin n) (Fin n) k),
        UpperTheory.Reformulated.B.BlockConjugation.blk ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k),
        by rw [UpperTheory.Reformulated.B.BlockConjugation.blk_mul, Units.mul_inv, UpperTheory.Reformulated.B.BlockConjugation.blk_one],
        by rw [UpperTheory.Reformulated.B.BlockConjugation.blk_mul, Units.inv_mul, UpperTheory.Reformulated.B.BlockConjugation.blk_one]⟩
    refine ⟨b * Q⁻¹, fun s => ?_⟩
    have e : ((b * Q⁻¹ * r s * (b * Q⁻¹)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        UpperTheory.Reformulated.B.BlockConjugation.blk (a : Matrix (Fin n) (Fin n) k) * (r₁ s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *
          UpperTheory.Reformulated.B.BlockConjugation.blk ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
      have : b * Q⁻¹ * r s * (b * Q⁻¹)⁻¹ = b * r₁ s * b⁻¹ := by
        rw [hr₁]
        group
      rw [this]
      rfl
    obtain ⟨c1, c2, c3⟩ := UpperTheory.Reformulated.B.BlockConjugation.conj_blk (a : Matrix (Fin n) (Fin n) k)
      ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) _ (h0 s)
    obtain ⟨d1, d2⟩ := ha s
    have e' : ((a * φ.toHomUnits s * a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        (a : Matrix (Fin n) (Fin n) k) *
          (r₁ s : Matrix (Fin (n + 1)) (Fin (n + 1)) k).submatrix Fin.succ Fin.succ *
          ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := rfl
    rw [e'] at d1 d2
    rw [e]
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · intro h
        exact absurd h (Fin.not_lt_zero _)
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          exact c2 i
        · intro h
          rw [c3]
          exact d1 i j (Fin.succ_lt_succ_iff.mp h)
    · refine Fin.cases ?_ (fun i => ?_) i
      · rw [c1, h00]
      · rw [c3]
        exact d2 i
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlockFourMatrices
section
noncomputable def UpperTheory.Reformulated.B.BlockFourMatrices.blk4 :
    {R : Type} →
      {n : ℕ} →
        Matrix (Fin n) (Fin n) R →
          Matrix (Fin n) (Fin n) R →
            Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R → Matrix (Fin (n + n)) (Fin (n + n)) R :=
    fun {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) ↦
      (Matrix.fromBlocks a b c d).submatrix (⇑finSumFinEquiv.symm : Fin (n + n) → Fin n ⊕ Fin n)
        (⇑finSumFinEquiv.symm : Fin (n + n) → Fin n ⊕ Fin n)

theorem UpperTheory.Reformulated.B.BlockFourMatrices.main :
    ∀ {R S : Type} {m : ℕ} (f : R → S) (a b c d : Matrix (Fin m) (Fin m) R),
      (UpperTheory.Reformulated.B.BlockFourMatrices.blk4 a b c d).map f = UpperTheory.Reformulated.B.BlockFourMatrices.blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  intro R S m f a b c d
  unfold UpperTheory.Reformulated.B.BlockFourMatrices.blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BoxBounds
section
noncomputable def UpperTheory.Reformulated.B.BoxBounds.box :
    {K : Type} → [inst : Field K] → {i : ℕ} → K → Submodule (NumberField.RingOfIntegers K) (Fin i → K) :=
    fun {K : Type} [Field K] {i : ℕ} (c : K) ↦ Submodule.pi Set.univ fun (x : Fin i) ↦ NumberField.RingOfIntegers K ∙ c

theorem UpperTheory.Reformulated.B.BoxBounds.exists_box_le :
    ∀ {K : Type} [inst : Field K] [NumberField K] {i : ℕ} (L : Submodule (NumberField.RingOfIntegers K) (Fin i → K)),
      Submodule.span K (↑L : Set (Fin i → K)) = ⊤ →
        ∃ (e : NumberField.RingOfIntegers K),
          e ≠ (0 : NumberField.RingOfIntegers K) ∧
            UpperTheory.Reformulated.B.BoxBounds.box
                ((Algebra.algebraMap (NumberField.RingOfIntegers K) K : NumberField.RingOfIntegers K → K) e) ≤
              L := by
  intro K _ _ i L hL
  classical
  have h : ∀ j : Fin i, ∃ t : nonZeroDivisors (NumberField.RingOfIntegers K),
      (t : NumberField.RingOfIntegers K) • (Pi.single j (1 : K) : Fin i → K) ∈ L := by
    intro j
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
      (nonZeroDivisors (NumberField.RingOfIntegers K)) K (↑L : Set (Fin i → K))
      (Pi.single j (1 : K)) (hL ▸ Submodule.mem_top)
    rw [Submodule.span_eq] at ht
    exact ⟨t, ht⟩
  choose t ht using h
  refine ⟨∏ j, (t j : NumberField.RingOfIntegers K),
    Finset.prod_ne_zero_iff.mpr fun j _ => nonZeroDivisors.coe_ne_zero (t j), ?_⟩
  intro x hx
  rw [← Finset.univ_sum_single x]
  refine L.sum_mem fun j _ => ?_
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (Submodule.mem_pi.mp hx j (Set.mem_univ j))
  obtain ⟨u, hu⟩ : (t j : NumberField.RingOfIntegers K) ∣ ∏ k, (t k : NumberField.RingOfIntegers K) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have hj : (Pi.single j (x j) : Fin i → K)
      = (a * u) • (t j : NumberField.RingOfIntegers K) • (Pi.single j (1 : K) : Fin i → K) := by
    rw [← ha, hu, smul_smul, ← Pi.single_smul, Algebra.algebraMap_eq_smul_one, smul_smul]
    congr 2
    ring
  rw [hj]
  exact L.smul_mem _ (ht j)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BurnsideEnd
section
theorem UpperTheory.Reformulated.B.Qj3.burnside_end.{u_3, u_4} :
    ∀ {K : Type u_3} {V : Type u_4} [inst : Field K] [IsAlgClosed K] [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module K V] [FiniteDimensional K V] (S : Subalgebra K (Module.End K V)),
    (∀ (N : Submodule K V), (∀ f ∈ S, ∀ v ∈ N, (f : V → V) v ∈ N) → N = ⊥ ∨ N = ⊤) → ∀ (f : Module.End K V), f ∈ S := by
  intro K V _ _ _ _ _ S h f
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : f = 0 := by ext v; exact Subsingleton.elim _ _
    rw [this]; exact S.zero_mem
  haveI : IsSimpleModule S V := by
    refine { eq_bot_or_eq_top := fun N => ?_ }
    rcases h (N.restrictScalars K) (fun g hg v hv => N.smul_mem (⟨g, hg⟩ : S) hv) with h1 | h1
    · left
      exact (Submodule.restrictScalars_eq_bot_iff _ _ _).1 h1
    · right
      exact (Submodule.restrictScalars_eq_top_iff _ _ _).1 h1
  have hs := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K (A := S) (V := V)).2
  let F : Module.End (Module.End S V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => by
        obtain ⟨c, rfl⟩ := hs φ
        simp [Module.End.smul_def, Module.algebraMap_end_apply] }
  classical
  let b := Module.finBasis K V
  obtain ⟨r, hr⟩ := jacobson_density (R := S) F (Finset.univ.image b)
  have : f = (r : Module.End K V) := by
    refine b.ext fun i => ?_
    exact hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [this]; exact r.2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardCount
section
namespace ListOfFnPermExistsEquivPerm

open Finset in
private theorem card_count {α : Type} [DecidableEq α] :
    ∀ {n : ℕ} (v : Fin n → α) (a : α), #{i | v i = a} = (List.ofFn v).count a
  | 0, v, a => by simp
  | n + 1, v, a => by
    have ih := card_count (fun i : Fin n => v i.succ) a
    rw [Fin.card_filter_univ_succ', List.ofFn_succ, List.count_cons, ih]
    by_cases h : v 0 = a <;> simp [h, add_comm]

end ListOfFnPermExistsEquivPerm

theorem UpperTheory.Reformulated.B.Yde7.main :
    ∀ {α : Type} {n : ℕ} (v w : Fin n → α),
      (List.ofFn v).Perm (List.ofFn w) → ∃ (s : Equiv.Perm (Fin n)), v = w ∘ (⇑s : Fin n → Fin n) := by
  intro α n v w h
  classical
  have hc : ∀ c, Fintype.card {i // v i = c} = Fintype.card {i // w i = c} := by
    intro c
    rw [Fintype.card_subtype, Fintype.card_subtype]
    convert (ListOfFnPermExistsEquivPerm.card_count v c).trans ((h.count_eq c).trans (ListOfFnPermExistsEquivPerm.card_count w c).symm)
  refine ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)), ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map _ i).symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardEmbeddingsRestrict
section
theorem UpperTheory.Reformulated.B.CardEmbeddingsRestrict.card_embeddings_restrict.{u_1, u_2} :
    ∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [NumberField K] [inst_2 : Field L] [inst_3 : NumberField L]
    [inst_4 : Algebra K L] (τ : K →+* ℂ),
    (open Classical in Finset.filter (fun σ : L →+* ℂ => σ.comp (Algebra.algebraMap K L) = τ) Finset.univ).card = Module.finrank K L := by
  intro K L _ _ _ _ _ τ
  classical
  letI : Algebra K ℂ := τ.toAlgebra
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  rw [← AlgHom.card K L ℂ, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun (f : L →ₐ[K] ℂ) _ => (f : L →+* ℂ)) ?_ ?_ ?_
  · intro f _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, RingHom.ext fun x => f.commutes x⟩
  · intro f _ g _ h
    exact AlgHom.ext fun x => RingHom.congr_fun h x
  · intro σ hσ
    rw [Finset.mem_filter] at hσ
    exact ⟨{ σ with commutes' := fun x => RingHom.congr_fun hσ.2 x }, Finset.mem_univ _, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardFiber
section
namespace MultisetMapEqExistsEquivPerm

private lemma card_fiber {α : Type*} [DecidableEq α] {l : ℕ} (x : Fin l → α) (v : α) :
    Fintype.card {a : Fin l // x a = v} =
      (Multiset.map x Finset.univ.val).countP (fun b => b = v) := by
  rw [Multiset.countP_map, Fintype.card_subtype]
  rfl

end MultisetMapEqExistsEquivPerm

theorem UpperTheory.Reformulated.B.Yhb6.main.{u_1} :
    ∀ {α : Type u_1} {l : ℕ} {x y : Fin l → α},
      Multiset.map y Finset.univ.val = Multiset.map x Finset.univ.val →
        ∃ (e : Equiv.Perm (Fin l)), ∀ (a : Fin l), y a = x ((e : Fin l → Fin l) a) := by
  intro α l x y h
  classical
  have hc : ∀ v : α, Fintype.card {a : Fin l // y a = v} = Fintype.card {a : Fin l // x a = v} := by
    intro v
    convert (MultisetMapEqExistsEquivPerm.card_fiber y v).trans
      ((congrArg (fun m => Multiset.countP (fun b => b = v) m) h).trans (MultisetMapEqExistsEquivPerm.card_fiber x v).symm)
  let E : ∀ v : α, {a : Fin l // y a = v} ≃ {a : Fin l // x a = v} :=
    fun v => Fintype.equivOfCardEq (hc v)
  refine ⟨Equiv.ofFiberEquiv E, fun a => ?_⟩
  exact (Equiv.ofFiberEquiv_map E a).symm
end

