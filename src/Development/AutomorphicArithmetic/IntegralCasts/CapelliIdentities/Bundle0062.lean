module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TraceEqSumReCmType
section
theorem UpperTheory.trace_eq_sum_re_cm_type :
    ∀ {E : Type} [Field E] [NumberField E] {Ψ : Type} [Fintype Ψ] (φ : Ψ → (E →+* ℂ)),
        Function.Injective φ →
        (∀ s : E →+* ℂ, (∃ τ, φ τ = s) ↔ ¬ ∃ τ, φ τ = (starRingEnd ℂ).comp s) →
        ∀ x : E, ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ τ, 2 * (φ τ x).re := by
  intro E _ _ Ψ _ φ hinj h x
  classical
  have hcc : ∀ s : E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
    intro s
    ext y
    simp
  let g : Ψ ⊕ Ψ → (E →+* ℂ) := Sum.elim φ (fun τ => (starRingEnd ℂ).comp (φ τ))
  have hg : Function.Bijective g := by
    constructor
    · rintro (a | a) (b | b) hab
      · exact congrArg Sum.inl (hinj hab)
      · exact absurd ⟨a, hab⟩ ((h (φ b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, hab.symm⟩ ((h (φ a)).1 ⟨a, rfl⟩)
      · have h2 := congrArg (fun s => (starRingEnd ℂ).comp s) hab
        simp only [g, Sum.elim_inr, hcc] at h2
        exact congrArg Sum.inr (hinj h2)
    · intro s
      by_cases hs : ∃ τ, φ τ = s
      · obtain ⟨τ, hτ⟩ := hs
        exact ⟨Sum.inl τ, hτ⟩
      · obtain ⟨τ, hτ⟩ := not_not.1 (fun hn => hs ((h s).2 hn))
        refine ⟨Sum.inr τ, ?_⟩
        simp only [g, Sum.elim_inr, hτ, hcc]
  have h1 : ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ s : E →+* ℂ, s x := by
    have h0 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := x)
    rw [eq_ratCast] at h0
    rw [h0]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ (fun s => rfl)).symm
  rw [← Fintype.sum_bijective g hg (fun t => g t x) (fun s => s x) (fun _ => rfl),
    Fintype.sum_sum_type, ← Finset.sum_add_distrib] at h1
  have h2 := congrArg Complex.re h1
  rw [Complex.ratCast_re, Complex.re_sum] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [g, two_mul]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TracePowEqZeroOfLeDim
section
theorem UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim.{u_1} :
    ∀ {K : Type u_1}
    [inst : Field K] (r : ℕ) (N : Matrix (Fin r) (Fin r) K),
    (∀ (k : ℕ), (1 : ℕ) ≤ k → k ≤ r → (N ^ k).trace = (0 : K)) → ∀ (k : ℕ), (1 : ℕ) ≤ k → (N ^ k).trace = (0 : K) := by
  intro K _ r N h k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hkr : k ≤ r
    · exact h k hk hkr
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 + r := ⟨k - r - 1, by omega⟩
      have hd : N.charpoly.natDegree = r := by
        rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
      have hc : N.charpoly.coeff r = 1 := by
        have := (Matrix.charpoly_monic N).coeff_natDegree
        rwa [hd] at this
      have hCH := Matrix.aeval_self_charpoly N
      rw [Polynomial.aeval_eq_sum_range, hd, Finset.sum_range_succ, hc, one_smul] at hCH
      have h2 := congrArg (fun A => Matrix.trace (N ^ (m + 1) * A)) hCH
      simp only [mul_add, Finset.mul_sum, Matrix.mul_smul, ← pow_add, mul_zero, Matrix.trace_zero,
        Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul] at h2
      rw [Finset.sum_eq_zero, zero_add] at h2
      · exact h2
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [ih (m + 1 + i) (by omega) (by omega), smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TraceZero
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qf25.modFun :
    {O M ι : Type} → [inst : CommRing O] → [inst_1 : AddCommGroup M] → [_root_.Module O M] → _root_.Module O (ι → M) :=
    fun {O M ι : Type} [CommRing O] [AddCommGroup M] [_root_.Module O M] ↦ Pi.Function.module ι O M
attribute [local instance] UpperTheory.Reformulated.B.Qf25.modFun

theorem UpperTheory.Reformulated.B.Qf25.trace_zero :
    ∀ {k : Type} [inst : Field k] (S T : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) k),
      T.det ≠ (0 : k) →
        S.charpoly.Separable →
          ∀ (v : Fin (2 : ℕ) → k),
            v ≠ (0 : Fin (2 : ℕ) → k) →
              T.mulVec v ∉ k ∙ v →
                ∀ (a b c : k),
                  S.mulVec v = a • v →
                    S.mulVec (T.mulVec v) = b • T.mulVec v →
                      S.mulVec (T.mulVec (T.mulVec v)) = c • T.mulVec (T.mulVec v) → T.trace = (0 : k) := by
  intro k _ S T hdet hsep v hv hw a b c ha hb hc
  have hCH : T.mulVec (T.mulVec v) = T.trace • T.mulVec v - T.det • v := by
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.trace_fin_two,
        Matrix.det_fin_two] <;> ring
  generalize T.mulVec v = w at hw hb hc hCH
  have hD : v 0 * w 1 - v 1 * w 0 ≠ 0 := by
    intro h
    apply hw
    rw [Submodule.mem_span_singleton]
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        ext i
        fin_cases i
        · exact h0
        · exact h1
      have hw0 : w 0 = 0 := by
        have : v 1 * w 0 = 0 := by linear_combination -h + w 1 * h0
        exact (mul_eq_zero.1 this).resolve_left h1
      refine ⟨w 1 / v 1, ?_⟩
      ext i
      fin_cases i
      · simp [h0, hw0]
      · simp [h1]
    · refine ⟨w 0 / v 0, ?_⟩
      ext i
      fin_cases i
      · simp [h0]
      · show w 0 / v 0 * v 1 = w 1
        field_simp
        linear_combination -h
  rw [hCH, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, ha, hb] at hc
  have c0 : T.trace * (b * w 0) - T.det * (a * v 0) = c * (T.trace * w 0 - T.det * v 0) :=
    congrFun hc 0
  have c1 : T.trace * (b * w 1) - T.det * (a * v 1) = c * (T.trace * w 1 - T.det * v 1) :=
    congrFun hc 1
  by_contra ht
  have hac : a = c := by
    have : T.det * (a - c) * (v 0 * w 1 - v 1 * w 0) = 0 := by
      linear_combination w 0 * c1 - w 1 * c0
    exact sub_eq_zero.1 ((mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hD)).resolve_left hdet)
  have hbc : b = c := by
    have : T.trace * (b - c) * (v 0 * w 1 - v 1 * w 0) = 0 := by
      linear_combination v 0 * c1 - v 1 * c0
    exact sub_eq_zero.1 ((mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hD)).resolve_left ht)
  subst hac hbc
  have a0 := congrFun ha 0
  have a1 := congrFun ha 1
  have b0 := congrFun hb 0
  have b1 := congrFun hb 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    at a0 a1 b0 b1
  have s00 : S 0 0 = b := by
    apply mul_right_cancel₀ hD
    linear_combination w 1 * a0 - v 1 * b0
  have s01 : S 0 1 = 0 := by
    apply mul_right_cancel₀ hD
    linear_combination v 0 * b0 - w 0 * a0
  have s11 : S 1 1 = b := by
    apply mul_right_cancel₀ hD
    linear_combination v 0 * b1 - w 0 * a1
  have hp : S.charpoly = (Polynomial.X - Polynomial.C b) * (Polynomial.X - Polynomial.C b) := by
    rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, s00, s01, s11]
    simp only [map_add (f := _), map_sub, map_mul, map_zero]
    ring
  have hu := hsep.squarefree (Polynomial.X - Polynomial.C b) (hp ▸ dvd_rfl)
  exact Polynomial.not_isUnit_X_sub_C b hu
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TransferOfCompSubtype
section
theorem UpperTheory.Reformulated.B.Qe30.transfer_of_comp_subtype.{u_1} :
    ∀ {Γ : Type u_1} [inst : Group Γ] (H : Subgroup Γ)
    [inst_1 : H.FiniteIndex] (g : Γ),
    ((Abelianization.of.comp H.subtype).transfer : Γ → Abelianization Γ) g =
      (Abelianization.of : Γ → Abelianization Γ) g ^ H.index := by
  intro Γ _ H _ g
  classical
  let _ := H.fintypeQuotientOfFiniteIndex
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    Subgroup.index_eq_sum_minimalPeriod H g, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [MonoidHom.comp_apply, Subgroup.subtype_apply, map_mul, map_mul, map_inv, map_pow,
    inv_mul_cancel_comm]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TransposeInverseTheta
section
noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m * UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  simp only [Matrix.mul_apply, UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat, Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  simp only [eq_comm]

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m, inv := UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m, val_inv := UpperTheory.Reformulated.B.TransposeInverseTheta.aux2 m,
        inv_val := UpperTheory.Reformulated.B.TransposeInverseTheta.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.TransposeInverseTheta.aux4 g,
        inv_val := UpperTheory.Reformulated.B.TransposeInverseTheta.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m * UpperTheory.Reformulated.B.TransposeInverseTheta.trInv g * UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m

private theorem UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g h : GL n R) :
    UpperTheory.Reformulated.B.TransposeInverseTheta.trInv (g * h) = UpperTheory.Reformulated.B.TransposeInverseTheta.trInv g * UpperTheory.Reformulated.B.TransposeInverseTheta.trInv h := by
  apply Units.ext
  change (↑(g * h)⁻¹ : Matrix n n R).transpose = (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g : GL n R) : UpperTheory.Reformulated.B.TransposeInverseTheta.trInv (UpperTheory.Reformulated.B.TransposeInverseTheta.trInv g) = g := by
  apply Units.ext
  change (↑g : Matrix n n R).transpose.transpose = ↑g
  rw [Matrix.transpose_transpose]

private theorem UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl_mul_self {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m * UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.TransposeInverseTheta.aux2 m)

private theorem UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_Jgl {m : ℕ} {R : Type*} [CommRing R] :
    UpperTheory.Reformulated.B.TransposeInverseTheta.trInv (UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m) = UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m := by
  apply Units.ext
  change (UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m).transpose = UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.TransposeInverseTheta.Jmat]
  by_cases h : j = i.rev
  · have h' : i = j.rev := by rw [h, Fin.rev_rev]
    simp [h, ← h']
  · have h' : ¬ i = j.rev := fun e => h (by rw [e, Fin.rev_rev])
    simp [h, h']

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.TransposeInverseTheta.theta (UpperTheory.Reformulated.B.TransposeInverseTheta.theta g) = g := by
  intro m R _ g
  have hJ := UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl_mul_self (m := m) (R := R)
  simp only [UpperTheory.Reformulated.B.TransposeInverseTheta.theta, UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_mul, UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_trInv,
    UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_Jgl]
  calc _ = (UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m * UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m) * g *
        (UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m * UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m) := by simp only [mul_assoc]
    _ = g := by rw [hJ, one_mul, mul_one]

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.TransposeInverseTheta.theta (g * h) = UpperTheory.Reformulated.B.TransposeInverseTheta.theta g * UpperTheory.Reformulated.B.TransposeInverseTheta.theta h := by
  intro m R _ g h
  have hJ := UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl_mul_self (m := m) (R := R)
  simp only [UpperTheory.Reformulated.B.TransposeInverseTheta.theta, UpperTheory.Reformulated.B.TransposeInverseTheta.trInv_mul]
  calc _ = UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m * UpperTheory.Reformulated.B.TransposeInverseTheta.trInv g * 1 * UpperTheory.Reformulated.B.TransposeInverseTheta.trInv h *
        UpperTheory.Reformulated.B.TransposeInverseTheta.Jgl R m := by simp only [mul_assoc, one_mul]
    _ = _ := by rw [← hJ]; simp only [mul_assoc]

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.TransposeInverseTheta.theta, invFun := UpperTheory.Reformulated.B.TransposeInverseTheta.theta, left_inv := UpperTheory.Reformulated.B.TransposeInverseTheta.aux8,
        right_inv := UpperTheory.Reformulated.B.TransposeInverseTheta.aux8, map_mul' := UpperTheory.Reformulated.B.TransposeInverseTheta.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact if_pos rfl

private theorem UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut_mul_self (m : ℕ) (R : Type*) [CommRing R] :
    UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R * UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R = 1 := by
  ext1 g
  exact UpperTheory.Reformulated.B.TransposeInverseTheta.aux8 g

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R := by
  intro m R _ s t
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · simp
  · simp [hne]
  · simp [hne]
  · simp [hne, UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut_mul_self]

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.TransposeInverseTheta.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.TransposeInverseTheta.aux11 m R, map_mul' := UpperTheory.Reformulated.B.TransposeInverseTheta.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.TransposeInverseTheta.sgnAct m R] ℤˣ

@[reducible] noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.TransposeInverseTheta.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) → G →* UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R → MulAut (UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R))
              ((UpperTheory.Reformulated.B.TransposeInverseTheta.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.TransposeInverseTheta.conj_left :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R)
      (g : G),
      ((UpperTheory.Reformulated.B.TransposeInverseTheta.conjBy h r : G → UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) g).left =
        h * ((r : G → UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) g).left *
          ((UpperTheory.Reformulated.B.TransposeInverseTheta.sgnAct m R : ℤˣ → MulAut (GL (Fin m) R)) ((r : G → UpperTheory.Reformulated.B.TransposeInverseTheta.GG m R) g).right :
              GL (Fin m) R → GL (Fin m) R)
            h⁻¹ := by
  intro G R _ _ m h r g
  have e : (UpperTheory.Reformulated.B.TransposeInverseTheta.conjBy h r) g =
      SemidirectProduct.inl h * r g * (SemidirectProduct.inl h)⁻¹ := rfl
  rw [e, ← map_inv, SemidirectProduct.mul_left, SemidirectProduct.mul_left]
  simp [mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TriDiag
section
theorem UpperTheory.Reformulated.B.Qk9.tri_diag :
    ∀ {R : Type} [inst : CommRing R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R),
    A.BlockTriangular id → B.BlockTriangular id → ∀ (i : Fin n), (A * B) i i = A i i * B i i := by
  intro R _ n A B hA hB i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i ?_ ?_
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA (show id j < id i from h), zero_mul]
    · rw [hB (show id i < id j from h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TripleNe
section
theorem UpperTheory.Reformulated.B.Qk1.triple_ne :
    ∀ {R ι : Type} [inst : CommRing R] [inst_1 : Fintype ι]
    {A Y B : Matrix ι ι R} {a b : ι},
    (A * Y * B) a b ≠ (0 : R) → ∃ (c : ι) (d : ι), A a c ≠ (0 : R) ∧ Y c d ≠ (0 : R) ∧ B d b ≠ (0 : R) := by
  intro R ι _ _ A Y B a b h
  rw [Matrix.mul_apply] at h
  obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := left_ne_zero_of_mul hd
  rw [Matrix.mul_apply] at h1
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  exact ⟨c, d, left_ne_zero_of_mul hc, right_ne_zero_of_mul hc, right_ne_zero_of_mul hd⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Tube
section
theorem UpperTheory.Reformulated.B.Qi19.tube.{u_1, u_2} :
    ∀ {G : Type u_1} {X : Type u_2} [inst : Group G] [inst_1 : TopologicalSpace G] [ContinuousInv G]
    [inst_3 : TopologicalSpace X] (T : G → X → X),
    (Continuous fun (p : G × X) ↦ T p.1 p.2) →
      (∀ (w : X), T (1 : G) w = w) →
        (∀ (k : G) (w : X), T k⁻¹ (T k w) = w) →
          ∀ {g : X → ℂ},
            IsLocallyConstant g → HasCompactSupport g → ∀ᶠ (k : G) in nhds (1 : G), ∀ (w : X), g (T k w) = g w := by
  intro G X _ _ _ _ T hT h1 hinv g hg hc
  have hK : ∀ᶠ k : G in nhds (1 : G), ∀ w ∈ tsupport g, g (T k w) = g w := by
    refine IsCompact.eventually_forall_of_forall_eventually
      (P := fun (k : G) (w : X) => g (T k w) = g w) hc.isCompact ?_
    intro y _
    have ha := (hg.comp_continuous hT).eventually_eq ((1 : G), y)
    have hb := (hg.comp_continuous (continuous_snd : Continuous fun p : G × X => p.2)).eventually_eq
      ((1 : G), y)
    filter_upwards [ha, hb] with z hza hzb
    simp only [Function.comp_apply, h1] at hza hzb
    rw [hza, hzb]
  have hi : Filter.Tendsto (fun k : G => k⁻¹) (nhds 1) (nhds 1) := by
    simpa using (continuous_inv (G := G)).tendsto 1
  filter_upwards [hK, hi.eventually hK] with k hk hk' w
  by_cases hw : w ∈ tsupport g
  · exact hk w hw
  · by_cases hw' : T k w ∈ tsupport g
    · have h := hk' _ hw'
      rw [hinv] at h
      exact h.symm
    · rw [image_eq_zero_of_notMem_tsupport hw, image_eq_zero_of_notMem_tsupport hw']
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UlZero
section
noncomputable def UpperTheory.Reformulated.B.Rb1.Zc :
    {D N : Type} → [inst : Group D] → [TopologicalSpace D] → [inst_2 : AddCommGroup N] → Representation ℤ D N → Set (D → N) :=
    fun {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N) ↦
      {z : D → N | IsLocallyConstant z ∧ ∀ (s t : D), z (s * t) = z s + ((ρ : D → N →ₗ[ℤ] N) s : N → N) (z t)}

theorem UpperTheory.Reformulated.B.Rb1.ul_zero :
    ∀ {D N : Type} [inst : Group D] [inst_1 : TopologicalSpace D] [inst_2 : IsTopologicalGroup D] [inst_3 : AddCommGroup N]
      (ρ : Representation ℤ D N) (I : Subgroup D) (φ : D),
      (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ →
        ∀ z ∈ UpperTheory.Reformulated.B.Rb1.Zc ρ, (∀ s ∈ I, z s = (0 : N)) → z φ = (0 : N) → ∀ (s : D), z s = (0 : N) := by
  intro D N _ _ _ _ ρ I φ hcl z hz hI hφ s
  have hlc : IsLocallyConstant z := hz.1
  have hco : ∀ (s t : D), z (s * t) = z s + ((ρ : D → N →ₗ[ℤ] N) s : N → N) (z t) := hz.2
  have h1 : z 1 = 0 := by
    have h := hco 1 1
    rw [mul_one, map_one] at h
    simpa using h
  let K : Subgroup D :=
    { carrier := z ⁻¹' {0}
      mul_mem' := by
        intro a b ha hb
        have ha' : z a = 0 := ha
        have hb' : z b = 0 := hb
        show z (a * b) = 0
        rw [hco, ha', hb', map_zero, add_zero]
      one_mem' := h1
      inv_mem' := by
        intro a ha
        have ha' : z a = 0 := ha
        show z a⁻¹ = 0
        have h := hco a⁻¹ a
        rw [inv_mul_cancel, h1, ha', map_zero, add_zero] at h
        exact h.symm }
  have hK : IsClosed (K : Set D) := hlc.isClosed_fiber 0
  have hle : I ⊔ Subgroup.zpowers φ ≤ K :=
    sup_le hI (by
      rw [Subgroup.zpowers_le]
      exact hφ)
  have htop : (⊤ : Subgroup D) ≤ K := by
    rw [← hcl]
    exact Subgroup.topologicalClosure_minimal _ hle hK
  exact htop (Subgroup.mem_top s)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UniAMulDiag
section
theorem UpperTheory.Reformulated.B.Qh23.uniA_mul_diag :
    ∀ {F : Type} [inst : Field F] {k : ℕ} (A B : Matrix (Fin k) (Fin k) F),
    A.BlockTriangular id → B.BlockTriangular id → ∀ (i : Fin k), (A * B) i i = A i i * B i i := by
  intro F _ k A B hA hB i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA (show id j < id i from h), zero_mul]
  · rw [hB (show id i < id j from h), mul_zero]
end

