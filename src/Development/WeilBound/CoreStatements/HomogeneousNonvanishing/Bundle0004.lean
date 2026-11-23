module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0004
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0001
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGLam
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0002
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LGenflagLU
section
open GlobalTheory.CompanionTheory.Ar Matrix

namespace PositivityTheory.UnitarySelfGeneration.GF

variable {r : ℕ}

def trunc {R : Type} [CommRing R] (k : Fin r) (A : Matrix (Fin r) (Fin r) R) : Matrix (Fin r) (Fin r) R :=
  Matrix.of fun i j => if i ≤ k ∧ j ≤ k then A i j else if i = j then 1 else 0

def Uni {R : Type} [CommRing R] (L : Matrix (Fin r) (Fin r) R) : Prop :=
  (∀ k, L k k = 1) ∧ ∀ l k, l < k → L l k = 0

def Up {R : Type} [CommRing R] (C : Matrix (Fin r) (Fin r) R) : Prop := ∀ l k, k < l → C l k = 0

section Ring

variable {R R' : Type} [CommRing R] [CommRing R']

theorem trunc_map (φ : R →+* R') (k : Fin r) (A : Matrix (Fin r) (Fin r) R) :
    trunc k (A.map φ) = (trunc k A).map φ := by
  ext i j
  simp only [trunc, of_apply, map_apply]
  split_ifs <;> simp

theorem det_trunc_map (φ : R →+* R') (k : Fin r) (A : Matrix (Fin r) (Fin r) R) :
    (trunc k (A.map φ)).det = φ (trunc k A).det := by
  rw [trunc_map, RingHom.map_det, RingHom.mapMatrix_apply]

theorem Uni.map {L : Matrix (Fin r) (Fin r) R} (h : Uni L) (φ : R →+* R') : Uni (L.map φ) :=
  ⟨fun k => by simp [h.1], fun l k hlk => by simp [h.2 l k hlk]⟩

theorem Up.map {L : Matrix (Fin r) (Fin r) R} (h : Up L) (φ : R →+* R') : Up (L.map φ) :=
  fun l k hlk => by simp [h l k hlk]

theorem Uni.det {L : Matrix (Fin r) (Fin r) R} (h : Uni L) : L.det = 1 := by
  rw [det_of_isLowerTriangular L (fun i j hij => h.2 i j hij)]
  simp [h.1]

theorem Uni.trunc {L : Matrix (Fin r) (Fin r) R} (h : Uni L) (k : Fin r) : Uni (trunc k L) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp [GF.trunc, h.1]
  · simp [GF.trunc, h.2 i j hij, hij.ne]

theorem uni_one : Uni (1 : Matrix (Fin r) (Fin r) R) :=
  ⟨fun k => by simp, fun l k h => by simp [h.ne]⟩

theorem trunc_mul (k : Fin r) (A C : Matrix (Fin r) (Fin r) R) (hC : Up C) :
    trunc k (A * C) = trunc k A * trunc k C := by
  ext i j
  simp only [trunc, of_apply, Matrix.mul_apply]
  by_cases hi : i ≤ k
  · by_cases hj : j ≤ k
    · simp only [hi, hj, and_self, if_true, true_and, and_true]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : l ≤ k
      · simp [hl]
      · have h1 : j < l := lt_of_le_of_lt hj (not_le.1 hl)
        simp [hl, hC l j h1, h1.ne']
    · have hij : i ≠ j := fun e => hj (e ▸ hi)
      simp only [hi, hj, and_false, if_false, true_and, hij]
      refine (Finset.sum_eq_zero fun l _ => ?_).symm
      by_cases hl : l = j
      · subst hl; simp [hj, hij]
      · simp [hl]
  · simp only [hi, false_and, if_false]
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro l _ hl; simp [Ne.symm hl]
    · simp

theorem Up.mul {A B : Matrix (Fin r) (Fin r) R} (hA : Up A) (hB : Up B) : Up (A * B) := by
  have h : BlockTriangular (A * B) id :=
    BlockTriangular.mul (fun i j h => hA i j h) (fun i j h => hB i j h)
  exact fun i j hij => h hij

end Ring

variable {F F' : Type} [Field F] [Field F']

theorem Up.inv {A : Matrix (Fin r) (Fin r) F} (hA : Up A) (h0 : A.det ≠ 0) : Up A⁻¹ := by
  let _ := A.invertibleOfIsUnitDet (IsUnit.mk0 _ h0)
  have h : BlockTriangular A⁻¹ id := blockTriangular_inv_of_blockTriangular (fun i j h => hA i j h)
  exact fun i j hij => h hij

theorem exists_lu (A : Matrix (Fin r) (Fin r) F) (h : ∀ k, (trunc k A).det ≠ 0) :
    ∃ C, Up C ∧ Uni (A * C) := by
  have hx : ∀ k, ∃ x : Fin r → F, trunc k A *ᵥ x = Pi.single k 1 := fun k =>
    ⟨(trunc k A)⁻¹ *ᵥ Pi.single k 1, by
      rw [mulVec_mulVec, mul_nonsing_inv _ (IsUnit.mk0 _ (h k)), one_mulVec]⟩
  choose x hx using hx
  have hup : ∀ l k, k < l → x k l = 0 := by
    intro l k hkl
    have := congrFun (hx k) l
    simp only [mulVec, dotProduct, trunc, of_apply, not_le.2 hkl, false_and, if_false] at this
    rw [Finset.sum_eq_single l] at this
    · simpa [hkl.ne'] using this
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have key : ∀ l k, l ≤ k → (A * Matrix.of fun l k => x k l) l k = (Pi.single k 1 : Fin r → F) l := by
    intro l k hlk
    rw [← congrFun (hx k) l]
    simp only [Matrix.mul_apply, mulVec, dotProduct, trunc, of_apply, hlk, true_and]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b ≤ k
    · simp [hb]
    · simp [hup b k (not_le.1 hb)]
  refine ⟨Matrix.of fun l k => x k l, hup, fun k => ?_, fun l k hlk => ?_⟩
  · rw [key k k le_rfl]; simp
  · rw [key l k hlk.le]; simp [hlk.ne]

theorem dets_of_lu {A C : Matrix (Fin r) (Fin r) F} (hC : Up C) (h : Uni (A * C)) :
    A.det ≠ 0 ∧ C.det ≠ 0 ∧ ∀ k, (trunc k A).det ≠ 0 ∧ (trunc k C).det ≠ 0 := by
  have h1 := h.det
  rw [det_mul] at h1
  refine ⟨left_ne_zero_of_mul_eq_one h1, right_ne_zero_of_mul_eq_one h1, fun k => ?_⟩
  have h2 := (h.trunc k).det
  rw [trunc_mul k A C hC, det_mul] at h2
  exact ⟨left_ne_zero_of_mul_eq_one h2, right_ne_zero_of_mul_eq_one h2⟩

theorem uni_mul_up {L W : Matrix (Fin r) (Fin r) F} (hL : Uni L) (hW : Up W) (h : Uni (L * W)) : W = 1 := by
  have hL0 : L.det ≠ 0 := by rw [hL.det]; exact one_ne_zero
  have h1 : Up (Lᵀ) := fun i j hij => hL.2 j i hij
  have h2 : Up ((L * W)ᵀ) := fun i j hij => h.2 j i hij
  have h3 : Up ((L * W)ᵀ * (Lᵀ)⁻¹) := h2.mul (h1.inv (by rwa [det_transpose]))
  rw [transpose_mul, Matrix.mul_assoc, mul_nonsing_inv _ (IsUnit.mk0 _ (by rwa [det_transpose])),
    Matrix.mul_one] at h3
  have hoff : ∀ i j, i ≠ j → W i j = 0 := fun i j hij =>
    (lt_or_gt_of_ne hij).elim (fun h => h3 j i h) (fun h => hW i j h)
  ext i j
  by_cases hij : i = j
  · subst hij
    have := h.1 i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at this
    · simpa [hL.1] using this
    · intro b _ hb; simp [hoff b i hb]
    · simp
  · rw [hoff i j hij, one_apply_ne hij]

theorem lu_unique {A C C' : Matrix (Fin r) (Fin r) F} (hC : Up C) (h : Uni (A * C)) (hC' : Up C')
    (h' : Uni (A * C')) : A * C = A * C' := by
  have h0 := (dets_of_lu hC h).2.1
  have e : A * C' = A * C * (C⁻¹ * C') := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, mul_nonsing_inv _ (IsUnit.mk0 _ h0), Matrix.one_mul]
  have := uni_mul_up h ((hC.inv h0).mul hC') (e ▸ h')
  rw [e, this, Matrix.mul_one]

theorem lu_mem (K : Subfield F) {A C : Matrix (Fin r) (Fin r) F} (hC : Up C) (h : Uni (A * C))
    (hA : ∀ i j, A i j ∈ K) : ∀ i j, (A * C) i j ∈ K := by
  let A₀ : Matrix (Fin r) (Fin r) K := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have e : A₀.map K.subtype = A := rfl
  obtain ⟨C₀, h1, h2⟩ := exists_lu A₀ fun k h0 => ((dets_of_lu hC h).2.2 k).1 (by
    rw [← e, det_trunc_map, h0, map_zero])
  have h3 := h2.map K.subtype
  have e2 : (A₀ * C₀).map K.subtype = A * C₀.map K.subtype := by rw [Matrix.map_mul, e]
  rw [e2] at h3
  rw [lu_unique hC h (h1.map K.subtype) h3, ← e2]
  exact fun i j => ((A₀ * C₀) i j).2

theorem exists_general (g : Matrix (Fin r) (Fin r) F) (hg : g.det ≠ 0) :
    ∃ w : Matrix (Fin r) (Fin r) (RatFunc F), Uni w ∧
      ∀ k, (trunc k (g.map (algebraMap F (RatFunc F)) * w)).det ≠ 0 := by
  let N : Matrix (Fin r) (Fin r) (Polynomial F) :=
    (Polynomial.X : Polynomial F) • 1 + (1 - Polynomial.X : Polynomial F) • (g⁻¹).map Polynomial.C
  let φ := algebraMap (Polynomial F) (RatFunc F)
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have e1 : N.map (Polynomial.evalRingHom (1 : F)) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [N, h, Matrix.one_apply]
  have e0 : (g.map Polynomial.C * N).map (Polynomial.evalRingHom (0 : F)) = 1 := by
    rw [Matrix.map_mul, ← mul_nonsing_inv g (IsUnit.mk0 _ hg)]
    congr 1
    · ext i j; simp
    · ext i j
      by_cases h : i = j <;> simp [N, h, one_apply]
  have nz : ∀ (M : Matrix (Fin r) (Fin r) (Polynomial F)) (a : F), M.map (Polynomial.evalRingHom a) = 1 →
      ∀ k, (trunc k (M.map φ)).det ≠ 0 := by
    intro M a hM k h0
    rw [det_trunc_map, map_eq_zero_iff _ hφ] at h0
    have := det_trunc_map (Polynomial.evalRingHom a) k M
    rw [hM, h0, map_zero, (uni_one.trunc k).det] at this
    exact one_ne_zero this
  obtain ⟨C, hC, hU⟩ := exists_lu (N.map φ) (nz N 1 e1)
  refine ⟨_, hU, fun k => ?_⟩
  have e : g.map (algebraMap F (RatFunc F)) * N.map φ = (g.map Polynomial.C * N).map φ := by
    rw [Matrix.map_mul, Matrix.map_map]
    rfl
  rw [← Matrix.mul_assoc, trunc_mul _ _ _ hC, det_mul, e]
  exact mul_ne_zero (nz _ 0 e0 k) ((dets_of_lu hC hU).2.2 k).2

def fl (M : Matrix (Fin r) (Fin r) F) (i : ℕ) : Submodule F (Fin r → F) := flagStep F (fun k l => M l k) i

theorem fl_mul_le (M C : Matrix (Fin r) (Fin r) F) (hC : Up C) (i : ℕ) : fl (M * C) i ≤ fl M i := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, hk, rfl⟩
  have : (fun l => (M * C) l k) = ∑ b, C b k • fun l => M l b := by
    funext l
    simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
  simp only [this]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : k < b
  · rw [hC b k hb, zero_smul]; exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, ?_, rfl⟩)
    exact lt_of_le_of_lt (Fin.le_def.1 (not_lt.1 hb)) hk

theorem fl_mul (M C : Matrix (Fin r) (Fin r) F) (hC : Up C) (h0 : C.det ≠ 0) (i : ℕ) : fl (M * C) i = fl M i := by
  refine le_antisymm (fl_mul_le M C hC i) ?_
  have := fl_mul_le (M * C) C⁻¹ (hC.inv h0) i
  rwa [Matrix.mul_assoc, mul_nonsing_inv _ (IsUnit.mk0 _ h0), Matrix.mul_one] at this

theorem flagStep_map {E E' : Type} [AddCommGroup E] [Module F E] [AddCommGroup E'] [Module F E'] (f : E →ₗ[F] E')
    (b : Fin r → E) (i : ℕ) : (flagStep F b i).map f = flagStep F (fun k => f (b k)) i := by
  unfold flagStep
  rw [Submodule.map_span, Set.image_image]

theorem fl_of_indep {E : Type} [AddCommGroup E] [Module F E] {e : Fin r → E} (he : LinearIndependent F e)
    {M N : Matrix (Fin r) (Fin r) F} {i : ℕ}
    (h : flagStep F (fun k => ∑ l, M l k • e l) i = flagStep F (fun k => ∑ l, N l k • e l) i) : fl M i = fl N i := by
  apply Submodule.map_injective_of_injective (f := Fintype.linearCombination F e)
    (he.fintypeLinearCombination_injective)
  unfold fl
  rw [flagStep_map, flagStep_map]
  simpa only [Fintype.linearCombination_apply] using h

end PositivityTheory.UnitarySelfGeneration.GF
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGPadic
section
open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

section

variable {Z O L : Type} [CommRing Z] [CommRing O] [AddCommGroup L] [Module O L]

theorem padic_act {N : ℕ} (φ : (Z ⊗[ℤ] L) ≃ₗ[Z] (Fin N → Z ⊗[ℤ] O))
    (hφ : ∀ (z : Z) (a : O) (x : L), φ (z ⊗ₜ (a • x)) = ((1 : Z) ⊗ₜ[ℤ] a : Z ⊗[ℤ] O) • φ (z ⊗ₜ x)) (a : O)
    (u : Z ⊗[ℤ] L) :
    φ (LinearMap.baseChange Z (LinearMap.lsmul O L a).toAddMonoidHom.toIntLinearMap u) =
      ((1 : Z) ⊗ₜ[ℤ] a : Z ⊗[ℤ] O) • φ u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul z x =>
    rw [LinearMap.baseChange_tmul]
    exact hφ z a x
  | add u v hu hv => simp only [map_add (f := _), hu, hv, smul_add]

private theorem baseChange_antisymm_of_self_eq_zero (B : LinearMap.BilinForm ℤ L) (hB : ∀ x, B x x = 0) (u v : Z ⊗[ℤ] L) :
    B.baseChange Z u v = - B.baseChange Z v u := by
  have hs : ∀ x y, B x y = - B y x := by
    intro x y
    have h := hB (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, hB, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul z x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul w y =>
      rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hs x y, neg_smul, mul_comm]
    | add v w hv hw => simp only [map_add (f := _), LinearMap.add_apply, hv, hw, neg_add]
  | add u u' hu hu' => simp only [map_add (f := _), LinearMap.add_apply, hu, hu', neg_add]

theorem padic_alt (B : LinearMap.BilinForm ℤ L) (hB : ∀ x, B x x = 0) (u : Z ⊗[ℤ] L) :
    B.baseChange Z u u = 0 := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul z x => rw [LinearMap.BilinForm.baseChange_tmul, hB, zero_smul]
  | add u v hu hv =>
    simp only [map_add (f := _), LinearMap.add_apply, hu, hv]
    rw [baseChange_antisymm_of_self_eq_zero B hB u v]
    abel

theorem padic_adj (bar : O ≃+* O) (B : LinearMap.BilinForm ℤ L) (hB : ∀ (a : O) x y, B (a • x) y = B x (bar a • y))
    (a : O) (u v : Z ⊗[ℤ] L) :
    B.baseChange Z (LinearMap.baseChange Z (LinearMap.lsmul O L a).toAddMonoidHom.toIntLinearMap u) v =
      B.baseChange Z u (LinearMap.baseChange Z (LinearMap.lsmul O L (bar a)).toAddMonoidHom.toIntLinearMap v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul z x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul w y =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
      simp only [AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe, LinearMap.lsmul_apply,
        LinearMap.BilinForm.baseChange_tmul]
      rw [hB]
    | add v w hv hw => simp only [map_add (f := _), hv, hw]
  | add u u' hu hu' => simp only [map_add (f := _), LinearMap.add_apply, hu, hu']

theorem padic_form {N : ℕ} (bar : O ≃+* O) (φ : (Z ⊗[ℤ] L) ≃ₗ[Z] (Fin N → Z ⊗[ℤ] O))
    (hφ : ∀ (z : Z) (a : O) (x : L), φ (z ⊗ₜ (a • x)) = ((1 : Z) ⊗ₜ[ℤ] a : Z ⊗[ℤ] O) • φ (z ⊗ₜ x))
    (B : LinearMap.BilinForm ℤ L) (h1 : ∀ x, B x x = 0) (h2 : Function.Bijective (B.baseChange Z))
    (h3 : ∀ (a : O) x y, B (a • x) y = B x (bar a • y)) :
    ∃ ψ : LinearMap.BilinForm Z (Fin N → Z ⊗[ℤ] O), (∀ u v, ψ (φ u) (φ v) = B.baseChange Z u v) ∧
      (∀ x, ψ x x = 0) ∧ Function.Bijective ψ ∧ ∀ (a : Z ⊗[ℤ] O) x y, ψ (a • x) y =
        ψ x (Algebra.TensorProduct.map (AlgHom.id Z Z) bar.toRingHom.toIntAlgHom a • y) := by
  refine ⟨(B.baseChange Z).compl₁₂ φ.symm.toLinearMap φ.symm.toLinearMap, ?_, ?_, ?_, ?_⟩
  · intro u v
    simp
  · intro x
    simp [padic_alt B h1]
  · constructor
    · intro x y hxy
      apply φ.symm.injective
      apply h2.1
      refine LinearMap.ext fun w => ?_
      have := LinearMap.congr_fun hxy (φ w)
      simpa using this
    · intro f
      obtain ⟨u, hu⟩ := h2.2 (f.comp φ.toLinearMap)
      refine ⟨φ u, LinearMap.ext fun y => ?_⟩
      have := LinearMap.congr_fun hu (φ.symm y)
      simpa using this
  · intro a x y
    obtain ⟨u, rfl⟩ := φ.surjective x
    obtain ⟨v, rfl⟩ := φ.surjective y
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul z c =>
      have hz : ∀ (c' : O) (w : Z ⊗[ℤ] L), (z ⊗ₜ[ℤ] c' : Z ⊗[ℤ] O) • φ w =
          z • φ (LinearMap.baseChange Z (LinearMap.lsmul O L c').toAddMonoidHom.toIntLinearMap w) := by
        intro c' w
        rw [padic_act φ hφ c' w, ← smul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [Algebra.TensorProduct.map_tmul]
      have e1 : (AlgHom.id Z Z) z = z := rfl
      have e2 : bar.toRingHom.toIntAlgHom c = bar c := rfl
      rw [e1, e2, hz, hz]
      simp only [LinearMap.map_smul, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearMap.smul_apply, padic_adj bar B h3]
    | add a a' ha ha' => simp only [add_smul, map_add (f := _), LinearMap.add_apply, ha, ha']

end

theorem padic_unit (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Algebra ℤ_[p] R] [Module.Finite ℤ_[p] R] (d : R)
    (h : IsCoprime d (p : R)) : IsUnit d := by
  obtain ⟨a, b, hab⟩ := h
  have hp : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have hN : (⊤ : Submodule ℤ_[p] R) ≤ (Ideal.span {a * d}).restrictScalars ℤ_[p] := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal ℤ_[p])
      Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    intro x _
    have hx : x = a * d * x + (p : ℤ_[p]) • (b * x) := by
      rw [Algebra.smul_def, map_natCast]
      linear_combination (-x) * hab
    rw [hx]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Submodule.smul_mem_smul hp Submodule.mem_top)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hN Submodule.mem_top : (1 : R) ∈ _)
  have hu : IsUnit (a * d) := IsUnit.of_mul_eq_one y (by rw [mul_comm]; exact hy)
  exact isUnit_of_mul_isUnit_right hu

theorem padic_freeZ (E : Type) [Field E] [NumberField E] (L : Type) [AddCommGroup L] [Module (𝓞 E) L]
    [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] : Module.Finite ℤ L ∧ Module.Free ℤ L := by
  have h1 : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have h2 : Module.Flat ℤ L := Module.Flat.trans ℤ (𝓞 E) L
  exact ⟨h1, inferInstance⟩

theorem tw_g_padic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ (p : ℕ) [Fact p.Prime] (L L' : Type) [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L'] [Module.Finite (𝓞 E) L'] [Module.Projective (𝓞 E) L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), Module.finrank (𝓞 E) L = Module.finrank (𝓞 E) L' → (∀ x, B x x = 0) → Function.Bijective B → (∀ (a : 𝓞 E) x y, B (a • x) y = B x (bar a • y)) → (∀ x, B' x x = 0) → Function.Bijective B' → (∀ (a : 𝓞 E) x y, B' (a • x) y = B' x (bar a • y)) → ∃ φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L'), (∀ (a : 𝓞 E) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul (𝓞 E) L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) ∧ ∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v := by
  intro E _ _ _ bar hbar hunr p _ L L' _ _ _ _ _ _ _ _ B B' hrk h1 h2 h3 k1 k2 k3
  obtain ⟨_, _⟩ := padic_freeZ E L
  obtain ⟨_, _⟩ := padic_freeZ E L'
  obtain ⟨φ, hφ⟩ := tw_g_free E p L
  have hL' := tw_g_free E p L'
  rw [← hrk] at hL'
  obtain ⟨φ', hφ'⟩ := hL'
  obtain ⟨ψ, hψ, a1, a2, a3⟩ := padic_form bar φ hφ B h1 (GlobalTheory.CompanionTheory.UnimodularBaseChange.bijective_baseChange ℤ_[p] L B h2) h3
  obtain ⟨ψ', hψ', b1, b2, b3⟩ := padic_form bar φ' hφ' B' k1 (GlobalTheory.CompanionTheory.UnimodularBaseChange.bijective_baseChange ℤ_[p] L' B' k2) k3
  obtain ⟨lam, l1, l2⟩ := tw_g_lam E bar hbar hunr p
  obtain ⟨θ, hθ⟩ := tw_g_theta E bar hbar hunr p Fact.out
  have hbb : ∀ a, bar (bar a) = a := fun a => RingOfIntegers.ext (by
    rw [hbar, hbar, IsCMField.complexConj_apply_apply])
  have hσ : ∀ r : ℤ_[p] ⊗[ℤ] 𝓞 E, Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p]) bar.toRingHom.toIntAlgHom
      (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p]) bar.toRingHom.toIntAlgHom r) = r := by
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
      exact congrArg (z ⊗ₜ[ℤ] ·) (hbb a)
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hu : ∃ t : ℤ_[p] ⊗[ℤ] 𝓞 E,
      IsUnit (t - Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p]) bar.toRingHom.toIntAlgHom t) := by
    refine ⟨1 ⊗ₜ θ, padic_unit p _ _ ?_⟩
    have := hθ.map (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := 𝓞 E)).toRingHom
    rw [map_natCast, map_sub] at this
    exact this
  obtain ⟨e, he⟩ := tw_g_std ℤ_[p] _ _ hσ lam l1 l2 _ (tw_g_semi p _ _ hσ hu _) ψ ψ' a1 a2 a3 b1 b2 b3
  refine ⟨φ ≪≫ₗ e.restrictScalars ℤ_[p] ≪≫ₗ φ'.symm, fun a x => ?_, fun u v => ?_⟩
  · apply φ'.injective
    rw [padic_act φ' hφ']
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.restrictScalars_apply]
    rw [hφ, map_smul]
  · rw [← hψ', ← hψ]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.restrictScalars_apply]
    exact he _ _

end PositivityTheory.UnitarySelfGeneration
end

