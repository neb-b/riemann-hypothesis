module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateElement
section
theorem UpperTheory.Reformulated.B.CMConjNegOfSqEqNegPos.conj_alt_bis :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] {d : ℕ},
    (0 : ℕ) < d → ∀ {x : E}, x ^ (2 : ℕ) = -(↑d : E) → (NumberField.IsCMField.complexConj E : E → E) x = -x := by
  intro E _ _ _ d hd x hx
  let φ : E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply φ.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, map_neg]
  have h : (φ x) ^ 2 = -(d : ℂ) := by
    rw [← map_pow, hx, map_neg, map_natCast]
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have h0 : (φ x).re * (φ x).im = 0 := by linarith
  have hr : (φ x).re = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1
    · rw [h1] at hre
      nlinarith [mul_self_nonneg (φ x).re]
  apply Complex.ext
  · rw [Complex.conj_re, Complex.neg_re, hr, neg_zero]
  · rw [Complex.conj_im, Complex.neg_im]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateOfRoots
section
open scoped ContDiff

namespace UpperTheory.Reformulated.B.ConjugateOfRoots

theorem conj_of_roots {K : Type} [Field K] {n : ℕ} (d : Fin n → K) (hd : Function.Injective d) (N D : GL (Fin n) K)
    (hD : (D : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d)
    (hN : ∀ i, (N : Matrix (Fin n) (Fin n) K).charpoly.IsRoot (d i)) : ∃ g : GL (Fin n) K, N = g * D * g⁻¹ := by
  have hv : ∀ i, ∃ v : Fin n → K, v ≠ 0 ∧
      (N : Matrix (Fin n) (Fin n) K).mulVec v = d i • v := by
    intro i
    have h := hN i
    rw [Polynomial.IsRoot.def, Matrix.eval_charpoly] at h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext j
    simp [Matrix.mulVec_diagonal]
  choose v hv0 hv using hv
  have hli : LinearIndependent K v := by
    refine Module.End.eigenvectors_linearIndependent'
      (Matrix.toLin' (N : Matrix (Fin n) (Fin n) K)) d hd v fun i => ⟨?_, hv0 i⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hv i]
  have hP : IsUnit (Matrix.of v).transpose := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  obtain ⟨g, hg⟩ := hP
  refine ⟨g, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hg, hD]
  ext i j
  have h := congrFun (hv j) i
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h

end UpperTheory.Reformulated.B.ConjugateOfRoots
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateSqrtNeg
section
theorem UpperTheory.Reformulated.B.ConjugateSqrtNeg.conj_sqrt_neg :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] (d : ℕ) (x : E),
    (0 : ℕ) < d → x ^ (2 : ℕ) = -(↑d : E) → (NumberField.IsCMField.complexConj E : E → E) x = -x := by
  intro E _ _ _ d x hd hx
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hsq : (NumberField.IsCMField.complexConj E x) ^ 2 = x ^ 2 := by
    rw [← map_pow, hx, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exfalso
    have h1 := NumberField.IsCMField.complexEmbedding_complexConj E φ x
    rw [h] at h1
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp h1.symm
    have h2 : (φ x) ^ 2 = -(d : ℂ) := by rw [← map_pow, hx, map_neg, map_natCast]
    rw [hr] at h2
    have h3 : r ^ 2 = -(d : ℝ) := by exact_mod_cast h2
    have h4 : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg r]
  · exact h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Conjugation
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conjE :
    (E : Type) → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsCMField E] → E ≃+* E :=
    fun (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] ↦ (NumberField.IsCMField.complexConj E).toRingEquiv

private theorem UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conj_eq_neg_of_sq {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : z ^ 2 = -(r : ℂ)) : starRingEnd ℂ z = -z := by
  have hre : z.re * z.re - z.im * z.im = -r := by
    simpa [pow_two] using congrArg Complex.re hz
  have him : z.re * z.im + z.im * z.re = 0 := by
    simpa [pow_two] using congrArg Complex.im hz
  have hprod : z.re * z.im = 0 := by linarith
  have h0 : z.re = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · rw [h] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [h0]

theorem UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conj_alt_bis :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {d : ℕ} {x : E},
      (0 : ℕ) < d → x ^ (2 : ℕ) = -(↑d : E) → (UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conjE E : E → E) x = -x := by
  intro E _ _ _ d x hd hx
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  change φ (NumberField.IsCMField.complexConj E x) = φ (-x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj, map_neg]
  refine UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conj_eq_neg_of_sq (r := (d : ℝ)) (Nat.cast_pos.mpr hd) ?_
  rw [← map_pow, hx, map_neg, map_natCast, Complex.ofReal_natCast]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugationByInvolution
section
noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m * UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp [UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat, Matrix.one_apply, eq_comm]
  · intro b _ hb
    simp [UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat, hb]
  · intro hb
    exact absurd (Finset.mem_univ _) hb

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m, inv := UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m, val_inv := UpperTheory.Reformulated.B.ConjugationByInvolution.aux2 m,
        inv_val := UpperTheory.Reformulated.B.ConjugationByInvolution.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.ConjugationByInvolution.aux4 g,
        inv_val := UpperTheory.Reformulated.B.ConjugationByInvolution.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m * UpperTheory.Reformulated.B.ConjugationByInvolution.trInv g * UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m

private theorem UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl_sq {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m * UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.ConjugationByInvolution.aux2 m)

private theorem UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g h : GL n R) :
    UpperTheory.Reformulated.B.ConjugationByInvolution.trInv (g * h) = UpperTheory.Reformulated.B.ConjugationByInvolution.trInv g * UpperTheory.Reformulated.B.ConjugationByInvolution.trInv h := by
  apply Units.ext
  change (↑(g * h)⁻¹ : Matrix n n R).transpose
    = (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g : GL n R) : UpperTheory.Reformulated.B.ConjugationByInvolution.trInv (UpperTheory.Reformulated.B.ConjugationByInvolution.trInv g) = g :=
  Units.ext rfl

private theorem UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_Jgl {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.ConjugationByInvolution.trInv (UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m) = UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m := by
  apply Units.ext
  change (UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m).transpose = UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat R m
  ext i j
  have : i = j.rev ↔ j = i.rev := by
    constructor <;> (rintro rfl; simp)
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.ConjugationByInvolution.Jmat, this]

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.ConjugationByInvolution.theta (UpperTheory.Reformulated.B.ConjugationByInvolution.theta g) = g := by
  intro m R _ g
  unfold UpperTheory.Reformulated.B.ConjugationByInvolution.theta
  rw [UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_mul, UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_mul, UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_Jgl,
    UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_trInv, ← mul_assoc, ← mul_assoc, UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl_sq, one_mul,
    mul_assoc, UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl_sq, mul_one]

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.ConjugationByInvolution.theta (g * h) = UpperTheory.Reformulated.B.ConjugationByInvolution.theta g * UpperTheory.Reformulated.B.ConjugationByInvolution.theta h := by
  intro m R _ g h
  unfold UpperTheory.Reformulated.B.ConjugationByInvolution.theta
  rw [UpperTheory.Reformulated.B.ConjugationByInvolution.trInv_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m) (UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl R m), UpperTheory.Reformulated.B.ConjugationByInvolution.Jgl_sq, one_mul]

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.ConjugationByInvolution.theta, invFun := UpperTheory.Reformulated.B.ConjugationByInvolution.theta, left_inv := UpperTheory.Reformulated.B.ConjugationByInvolution.aux8,
        right_inv := UpperTheory.Reformulated.B.ConjugationByInvolution.aux8, map_mul' := UpperTheory.Reformulated.B.ConjugationByInvolution.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact if_pos rfl

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R := by
  intro m R _ s t
  have hsq : UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R * UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R = 1 :=
    MulEquiv.ext fun g => UpperTheory.Reformulated.B.ConjugationByInvolution.aux8 g
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
    simp [hne, hsq]

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ConjugationByInvolution.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.ConjugationByInvolution.aux11 m R, map_mul' := UpperTheory.Reformulated.B.ConjugationByInvolution.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.ConjugationByInvolution.sgnAct m R] ℤˣ

@[reducible] noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.ConjugationByInvolution.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R) → G →* UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R → MulAut (UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R))
              ((UpperTheory.Reformulated.B.ConjugationByInvolution.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.ConjugationByInvolution.conjBy_right :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R)
      (g : G),
      ((UpperTheory.Reformulated.B.ConjugationByInvolution.conjBy h r : G → UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R) g).right = ((r : G → UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R) g).right := by
  intro G R _ _ m h r g
  change (UpperTheory.Reformulated.B.ConjugationByInvolution.ofGL h * r g * (UpperTheory.Reformulated.B.ConjugationByInvolution.ofGL h)⁻¹ : UpperTheory.Reformulated.B.ConjugationByInvolution.GG m R).right = _
  rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
    SemidirectProduct.right_inl, inv_one, one_mul, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ContinuousHom
section
theorem UpperTheory.Reformulated.B.ContinuousHomomorphism.cont_hom :
    ∀ {Γ M : Type} [inst : Group Γ]
    [inst_1 : TopologicalSpace Γ] [ContinuousInv Γ] [inst_3 : Monoid M] [inst_4 : TopologicalSpace M] (f : Γ →* Mˣ),
    (Continuous fun (g : Γ) ↦ (↑((f : Γ → Mˣ) g) : M)) → Continuous (⇑f : Γ → Mˣ) := by
  intro Γ M _ _ _ _ _ f h
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  refine (h.comp continuous_inv).congr fun g => ?_
  simp only [Function.comp_apply, map_inv]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ContinuousToZModPow
section
theorem UpperTheory.Reformulated.B.Yde3.continuous_toZModPow :
    ∀ {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] (n : ℕ), Continuous (⇑(PadicInt.toZModPow n) : ℤ_[ℓ] → ZMod (ℓ ^ n)) := by
  intro ℓ hℓ n
  refine continuous_of_continuousAt_zero (PadicInt.toZModPow (p := ℓ) n) ?_
  have hpos : (0 : ℝ) < (ℓ : ℝ) ^ (-n : ℤ) :=
    zpow_pos (by exact_mod_cast hℓ.out.pos) _
  refine (continuousAt_const (y := (0 : ZMod (ℓ ^ n)))).congr ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[ℓ]) hpos] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker] at hx
  exact hx.symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConvSqLe
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj8.E :
    ℕ → Type :=
    fun (d : ℕ) ↦ EuclideanSpace ℝ (Fin d)

theorem UpperTheory.Reformulated.B.Qj8.conv_sq_le :
    ∀ {d : ℕ} (k g : UpperTheory.Reformulated.B.Qj8.E d → ENNReal),
      Measurable k →
        Measurable g →
          ∀ (ξ : UpperTheory.Reformulated.B.Qj8.E d),
            (∫⁻ (η : UpperTheory.Reformulated.B.Qj8.E d), k (ξ - η) * g η) ^ (2 : ℕ) ≤
              (∫⁻ (ζ : UpperTheory.Reformulated.B.Qj8.E d), k ζ) * ∫⁻ (η : UpperTheory.Reformulated.B.Qj8.E d), k (ξ - η) * g η ^ (2 : ℕ) := by
  intro d k g hk hg ξ
  have hk' : Measurable (fun η : UpperTheory.Reformulated.B.Qj8.E d => k (ξ - η)) :=
    hk.comp (measurable_const.sub measurable_id)
  have hh : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hsq : ∀ a : ENNReal, (a ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = a := by
    intro a
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hsq' : ∀ a : ENNReal, (a ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = a := by
    intro a
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have H := ENNReal.lintegral_mul_norm_pow_le (μ := MeasureTheory.volume)
    (f := fun η : UpperTheory.Reformulated.B.Qj8.E d => k (ξ - η))
    (g := fun η : UpperTheory.Reformulated.B.Qj8.E d => k (ξ - η) * g η ^ (2 : ℕ))
    hk'.aemeasurable (hk'.mul (hg.pow_const 2)).aemeasurable hh hh (by norm_num)
  have hpt : ∀ η : UpperTheory.Reformulated.B.Qj8.E d,
      k (ξ - η) ^ (1 / 2 : ℝ) * (k (ξ - η) * g η ^ (2 : ℕ)) ^ (1 / 2 : ℝ) = k (ξ - η) * g η := by
    intro η
    rw [ENNReal.mul_rpow_of_nonneg _ _ hh, hsq', ← mul_assoc, ← pow_two, hsq]
  simp only [hpt] at H
  rw [MeasureTheory.lintegral_sub_left_eq_self k ξ] at H
  calc _ ≤ _ := pow_le_pow_left₀ bot_le H 2
    _ = _ := by rw [mul_pow, hsq, hsq]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoproductGeometry
section
theorem UpperTheory.Reformulated.B.CoproductGeometry.cop_geom :
    ∀ {R κ : Type} [inst : CommRing R] [IsNoetherianRing R]
    [inst_2 : NormedField κ] [IsUltrametricDist κ] (m : Ideal R) (y : R →+* κ),
    (∀ (x : R), ‖(y : R → κ) x‖ ≤ (1 : ℝ)) →
      (∀ x ∈ m, ‖(y : R → κ) x‖ < (1 : ℝ)) →
        ∃ a < (1 : ℝ), (0 : ℝ) ≤ a ∧ ∀ (n : ℕ), ∀ x ∈ m ^ n, ‖(y : R → κ) x‖ ≤ a ^ n := by
  intro R κ _ _ _ _ m y h1 hm
  classical
  have key : ∀ T : Finset R, (∀ s ∈ T, ‖y s‖ < 1) →
      ∃ a < (1 : ℝ), (0 : ℝ) ≤ a ∧ ∀ s ∈ T, ‖y s‖ ≤ a := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact ⟨0, by norm_num, le_rfl, by simp⟩
    | insert b T hb ih =>
      intro h
      obtain ⟨a, ha1, ha0, ha⟩ := ih (fun s hs => h s (Finset.mem_insert_of_mem hs))
      refine ⟨max a ‖y b‖, max_lt ha1 (h b (Finset.mem_insert_self _ _)),
        le_max_of_le_left ha0, ?_⟩
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact le_max_right _ _
      · exact (ha s hs).trans (le_max_left _ _)
  obtain ⟨S, hS⟩ : m.FG := IsNoetherian.noetherian m
  obtain ⟨a, ha1, ha0, ha⟩ := key S (fun s hs => hm s (hS ▸ Ideal.subset_span hs))
  have hgen : ∀ z ∈ m, ‖y z‖ ≤ a := by
    intro z hz
    rw [← hS] at hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact ha x hx
    | zero => simpa using ha0
    | add u v _ _ hu hv =>
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)
    | smul r u _ hu =>
      rw [smul_eq_mul, map_mul, norm_mul]
      calc ‖y r‖ * ‖y u‖ ≤ 1 * a := mul_le_mul (h1 r) hu (norm_nonneg _) zero_le_one
        _ = a := one_mul a
  refine ⟨a, ha1, ha0, ?_⟩
  intro n
  induction n with
  | zero => intro x _; simpa using h1 x
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    induction hx using Submodule.mul_induction_on' with
    | mem_mul_mem u hu v hv =>
      rw [map_mul, norm_mul, pow_succ]
      exact mul_le_mul (ih u hu) (hgen v hv) (norm_nonneg _) (pow_nonneg ha0 n)
    | add u _ v _ hu hv =>
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CountingPairs
section
noncomputable def UpperTheory.Reformulated.B.CountingPairs.rhoPair :
    {n : ℕ} → (Fin n → ℤ) → ℤ :=
    fun {n : ℕ} (l : Fin n → ℤ) ↦ ∑ i : Fin n, ((↑n : ℤ) - (1 : ℤ) - (2 : ℤ) * (↑(↑i : ℕ) : ℤ)) * l i

namespace UpperTheory.Reformulated.B.CountingPairs.Priv

private lemma cntGt {k : ℕ} (i : Fin k) :
    (∑ c : Fin k, if i < c then (1:ℤ) else 0) = (k:ℤ) - 1 - i := by
  rw [Finset.sum_boole]
  have : (Finset.univ.filter (fun c : Fin k => i < c)) = Finset.Ioi i := by
    ext c; simp
  rw [this, Fin.card_Ioi]
  have := i.isLt
  push_cast [Nat.sub_sub, show 1 + (i:ℕ) ≤ k by omega]
  ring

private lemma cntLt {k : ℕ} (c : Fin k) :
    (∑ i : Fin k, if i < c then (1:ℤ) else 0) = (c:ℤ) := by
  rw [Finset.sum_boole]
  have : (Finset.univ.filter (fun i : Fin k => i < c)) = Finset.Iio c := by
    ext i; simp
  rw [this, Fin.card_Iio]

end UpperTheory.Reformulated.B.CountingPairs.Priv

open UpperTheory.Reformulated.B.CountingPairs.Priv in
theorem UpperTheory.Reformulated.B.CountingPairs.main :
    ∀ {k : ℕ} (l : Fin k → ℤ),
      (∑ c : Fin k, ∑ i : Fin k, if i < c then l i - l c else (0 : ℤ)) = UpperTheory.Reformulated.B.CountingPairs.rhoPair l := by
  intro k l
  have h1 : ∀ c i : Fin k, (if i < c then l i - l c else (0:ℤ))
      = (if i < c then (1:ℤ) else 0) * l i - (if i < c then (1:ℤ) else 0) * l c := by
    intro c i; split_ifs <;> simp
  simp_rw [h1, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun c i => (if i < c then (1:ℤ) else 0) * l i)]
  simp_rw [← Finset.sum_mul, cntGt, cntLt]
  unfold UpperTheory.Reformulated.B.CountingPairs.rhoPair
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CubeSignEmb
section
noncomputable def UpperTheory.Reformulated.B.Qh71.cubeSign :
    {ι : Type} → [LinearOrder ι] → Finset ι → ι → ℤ :=
    fun {ι : Type} [LinearOrder ι] (t : Finset ι) (i : ι) ↦ (-1 : ℤ) ^ {x ∈ t | x < i}.card

theorem UpperTheory.Reformulated.B.Qh71.cubeSign_emb :
    ∀ {κ : Type} [inst : LinearOrder κ] (t : Finset κ) {n : ℕ} (h : t.card = n) (k : Fin n),
      UpperTheory.Reformulated.B.Qh71.cubeSign t ((t.orderEmbOfFin h : Fin n → κ) k) = (-1 : ℤ) ^ (↑k : ℕ) := by
  intro κ _ t n h k
  have key : {x ∈ t | x < t.orderEmbOfFin h k}
      = (Finset.Iio k).map (t.orderEmbOfFin h).toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio]
    constructor
    · rintro ⟨hx, hlt⟩
      have hr : x ∈ Set.range (t.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact hx
      obtain ⟨j, rfl⟩ := hr
      exact ⟨j, (t.orderEmbOfFin h).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem t h j, (t.orderEmbOfFin h).lt_iff_lt.mpr hj⟩
  unfold UpperTheory.Reformulated.B.Qh71.cubeSign
  rw [key, Finset.card_map, Fin.card_Iio]
end

