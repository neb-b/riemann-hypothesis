module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobTop
section
noncomputable section
open scoped NumberField

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI Submodule NumberField

lemma isIntegral_algebraMap_O (F : IntermediateField ℚ ℂ) (o : 𝓞 F) :
    IsIntegral ℤ (algebraMap (𝓞 F) ℂ o) := by
  first
    | exact (NumberField.RingOfIntegers.isIntegral o).algebraMap
    | exact IsIntegral.algebraMap o.isIntegral_coe
    | exact (o.isIntegral_coe).map (IsScalarTower.toAlgHom ℤ F ℂ)

lemma lunit_of (F : IntermediateField ℚ ℂ) {α β u : ℂ} {k l : ℕ} (hα : α ≠ 0) (hβ : β ≠ 0) (hu : u ≠ 0)
    (hl : ¬ l ∣ k)
    (h1 : span (𝓞 F) {(k : ℂ) * α} ≤ span (𝓞 F) {u * β})
    (h2 : span (𝓞 F) {(k : ℂ) * (u * β)} ≤ span (𝓞 F) {α}) :
    IsLUnit l (α / β / u) := by
  refine ⟨div_ne_zero (div_ne_zero hα hβ) hu, k, hl, ?_, ?_⟩
  · obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.mp (h1 (Submodule.mem_span_singleton_self _))
    rw [Algebra.smul_def] at ho
    have e : (k : ℂ) * (α / β / u) = algebraMap (𝓞 F) ℂ o := by
      field_simp
      first | linear_combination ho | linear_combination -ho
    rw [e]
    exact isIntegral_algebraMap_O F o
  · obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.mp (h2 (Submodule.mem_span_singleton_self _))
    rw [Algebra.smul_def] at ho
    have e : (k : ℂ) * (α / β / u)⁻¹ = algebraMap (𝓞 F) ℂ o := by
      field_simp
      first | linear_combination ho | linear_combination -ho
    rw [e]
    exact isIntegral_algebraMap_O F o

lemma ne_bot_of_smul {F : IntermediateField ℚ ℂ} {S T : Submodule (𝓞 F) ℂ} {c : ℂ} (hc : c ≠ 0)
    (hST : span (𝓞 F) {c} * S ≤ T) (hS : S ≠ ⊥) : T ≠ ⊥ := by
  obtain ⟨x, hxS, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  intro hT
  have hmem : c * x ∈ span (𝓞 F) {c} * S :=
    Submodule.mul_mem_mul (Submodule.mem_span_singleton_self c) hxS
  have h2 := hST hmem
  rw [hT, Submodule.mem_bot] at h2
  exact mul_ne_zero hc hx0 h2

theorem globalLUnit_of
    (hV1 : ∀ (F : IntermediateField ℚ ℂ) (m : Type) [Fintype m] [DecidableEq m] (Λ Λ' : AddSubgroup (m → ℂ))
      (c : ℂ), (∀ x ∈ Λ, c • x ∈ Λ') → span (𝓞 F) {c ^ Fintype.card m} * vol F Λ ≤ vol F Λ')
    (hV2 : ∀ (F : IntermediateField ℚ ℂ) (m : Type) [Fintype m] [DecidableEq m]
      (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) (Λ : AddSubgroup (m → ℂ)),
      vol F (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ) =
        span (𝓞 F) {LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))} * vol F Λ)
    (hV3 : ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
      (m : Type) [Fintype m] [DecidableEq m], UnitDetRootDefs.CmOK a b c d →
      vol (KF b d) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≤ span (𝓞 (KF b d)) {lam ^ Fintype.card m})
    (hV4 : ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
      (m : Type) [Fintype m] [DecidableEq m], UnitDetRootDefs.CmOK a b c d →
      vol (KF b d) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ ⊥) :
    GlobalLUnit := by
  intro a b c d ha hd lam hlam m _ _ Λa hH
  obtain ⟨hok, -, -, hi1, hi2⟩ := hH
  have : FiniteDimensional ℚ (KF b d) := IntermediateField.adjoin.finiteDimensional (theta_isIntegral hok)
  have : NumberField (KF b d) := { }
  set F := KF b d with hFdef
  set Lt := UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m with hLt
  set N1 := UnitDetRootDefs.relIdx Lt Λa with hN1
  set N2 := UnitDetRootDefs.relIdx Λa Lt with hN2
  set e := Fintype.card m with he
  set h := hF F with hh
  have hN10 : (N1 : ℂ) ≠ 0 := by exact_mod_cast hi1
  have hN20 : (N2 : ℂ) ≠ 0 := by exact_mod_cast hi2
  have hL0 : vol F Lt ≠ ⊥ := hV4 a b c d ha hd lam hlam m hok
  have hLle : vol F Lt ≤ span (𝓞 F) {lam ^ e} := hV3 a b c d ha hd lam hlam m hok
  have hA1 : span (𝓞 F) {(N1 : ℂ) ^ e} * vol F Λa ≤ vol F Lt :=
    hV1 F m Λa Lt _ fun x hx => by rw [Nat.cast_smul_eq_nsmul]; exact nsmul_relIdx_mem Lt Λa hx
  have hA2 : span (𝓞 F) {(N2 : ℂ) ^ e} * vol F Lt ≤ vol F Λa :=
    hV1 F m Lt Λa _ fun x hx => by rw [Nat.cast_smul_eq_nsmul]; exact nsmul_relIdx_mem Λa Lt hx
  have hA0 : vol F Λa ≠ ⊥ := ne_bot_of_smul (pow_ne_zero _ hN20) hA2 hL0
  have hAle : vol F Λa ≤ span (𝓞 F) {lam ^ e / (N1 : ℂ) ^ e} := by
    intro x hx
    obtain ⟨o, ho⟩ := mem_span_singleton.mp (hLle (hA1 (mul_mem_mul (mem_span_singleton_self _) hx)))
    rw [mem_span_singleton]
    refine ⟨o, ?_⟩
    rw [Algebra.smul_def] at ho ⊢
    rw [mul_div_assoc', div_eq_iff (pow_ne_zero _ hN10)]
    linear_combination ho
  obtain ⟨y1, hy1, e1⟩ := sub_pow_principal F (vol F Lt) hL0 (lam ^ e) (pow_ne_zero _ hlam) hLle
  obtain ⟨y2, hy2, e2⟩ := sub_pow_principal F (vol F Λa) hA0 (lam ^ e / (N1 : ℂ) ^ e)
    (div_ne_zero (pow_ne_zero _ hlam) (pow_ne_zero _ hN10)) hAle
  have hy1' : (y1 : ℂ) ≠ 0 := fun h0 => hy1 (Subtype.ext h0)
  have hy2' : (y2 : ℂ) ≠ 0 := fun h0 => hy2 (Subtype.ext h0)
  set α := (lam ^ e) ^ h * (y1 : ℂ) with hα
  set β := (lam ^ e / (N1 : ℂ) ^ e) ^ h * (y2 : ℂ) with hβ
  have hα0 : α ≠ 0 := mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hlam)) hy1'
  have hβ0 : β ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (div_ne_zero (pow_ne_zero _ hlam) (pow_ne_zero _ hN10))) hy2'
  have hγ : α / β = (N1 : ℂ) ^ (e * h) * (y1 : ℂ) / (y2 : ℂ) := by
    rw [hα, hβ, div_pow, pow_mul]
    field_simp
  have hγmem : α / β ∈ KF b d := by
    rw [hγ]
    exact div_mem (mul_mem (pow_mem (IntermediateField.natCast_mem _ N1) _) y1.2) y2.2
  have hpos : 0 < h := Fintype.card_pos
  refine ⟨α / β, hγmem, div_ne_zero hα0 hβ0, h, hpos, ?_⟩
  intro l _ δ _ hE
  obtain ⟨k, hk, hk1, hk2⟩ := hE
  set u := LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) with hu
  have hu0 : u ≠ 0 := (LinearEquiv.isUnit_det' δ).ne_zero
  have hvi := hV2 F m δ Λa
  have i1 : span (𝓞 F) {(k : ℂ) ^ e} * vol F Lt ≤ span (𝓞 F) {u} * vol F Λa :=
    hvi ▸ hV1 F m _ _ _ hk1
  have i2 : span (𝓞 F) {(k : ℂ) ^ e} * (span (𝓞 F) {u} * vol F Λa) ≤ vol F Lt :=
    hvi ▸ hV1 F m _ _ _ hk2
  have j1 := sub_pow_le F i1 h
  have j2 := sub_pow_le F i2 h
  rw [mul_pow, mul_pow, span_single_pow, span_single_pow, e1, e2, span_single_mul,
    span_single_mul] at j1
  rw [mul_pow, mul_pow, span_single_pow, span_single_pow, e1, e2, span_single_mul,
    span_single_mul] at j2
  have hkc : ((k : ℂ) ^ e) ^ h = ((k ^ (e * h) : ℕ) : ℂ) := by push_cast; rw [pow_mul]
  rw [hkc] at j1 j2
  have hl : ¬ l ∣ k ^ (e * h) := fun hd' => hk ((Fact.out : l.Prime).dvd_of_dvd_pow hd')
  exact lunit_of F hα0 hβ0 (pow_ne_zero _ hu0) hl j1 j2

end PI.UnitaryGroupMassFormula.UnitDetRoot
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobVol
section
noncomputable section
open scoped NumberField ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI

section Vol

variable (F : IntermediateField ℚ ℂ) {m : Type} [Fintype m] [DecidableEq m]

lemma vol_smul_le {Λ Λ' : AddSubgroup (m → ℂ)} (c : ℂ) (h : ∀ x ∈ Λ, c • x ∈ Λ') :
    Submodule.span (𝓞 F) {c ^ Fintype.card m} * vol F Λ ≤ vol F Λ' := by
  unfold vol volSet
  rw [Submodule.span_mul_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, _, ⟨v, hv, rfl⟩, rfl⟩
  obtain rfl := Set.mem_singleton_iff.mp hx
  apply Submodule.subset_span
  refine ⟨fun j => c • v j, fun j => h _ (hv j), ?_⟩
  rw [show (Matrix.of fun j => c • v j) = c • Matrix.of v from by ext i j; rfl, Matrix.det_smul]

lemma det_rows_map (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (w : m → m → ℂ) :
    (Matrix.of fun j => δ (w j)).det = LinearMap.det δ * (Matrix.of w).det := by
  have h : Matrix.of (fun j => δ (w j)) = Matrix.of w * Matrix.transpose (LinearMap.toMatrix' δ) := by
    ext j i
    rw [Matrix.of_apply, ← LinearMap.toMatrix'_mulVec]
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  rw [h, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix', mul_comm]

lemma vol_img (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) (Λ : AddSubgroup (m → ℂ)) :
    vol F (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ)
      = Submodule.span (𝓞 F) {LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))} * vol F Λ := by
  unfold UnitDetRootDefs.imgLat vol volSet
  rw [Submodule.span_mul_span]
  congr 1
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    choose w hw hwv using fun j => AddSubgroup.mem_map.mp (hv j)
    refine Set.mem_mul.mpr ⟨_, Set.mem_singleton _, _, ⟨w, hw, rfl⟩, ?_⟩
    have hv' : v = fun j => (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (w j) := funext fun j => (hwv j).symm
    rw [hv', det_rows_map]
  · intro hz
    obtain ⟨_, h1, _, ⟨w, hw, rfl⟩, rfl⟩ := Set.mem_mul.mp hz
    obtain rfl := Set.mem_singleton_iff.mp h1
    refine ⟨fun j => (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (w j), fun j => AddSubgroup.mem_map.mpr ⟨w j, hw j, rfl⟩, ?_⟩
    rw [det_rows_map]

end Vol

def thetaO {a : ℕ} {b c : ℤ} {d : ℕ} (hok : UnitDetRootDefs.CmOK a b c d) : 𝓞 (KF b d) :=
  ⟨⟨UnitDetRootDefs.cmTheta b d, theta_mem b d⟩, by
    rw [mem_integralClosure_iff]
    refine ⟨Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X + Polynomial.C ((a : ℤ) * c), ?_, ?_⟩
    · monicity!
    · apply (KF b d).val.injective
      have h : ((KF b d).val.toRingHom) ((Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X +
          Polynomial.C ((a : ℤ) * c)).eval₂ (algebraMap ℤ (KF b d)) ⟨UnitDetRootDefs.cmTheta b d, theta_mem b d⟩)
          = (Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X +
          Polynomial.C ((a : ℤ) * c)).eval₂ (Int.castRingHom ℂ) (UnitDetRootDefs.cmTheta b d) := by
        rw [Polynomial.hom_eval₂, RingHom.ext_int ((KF b d).val.toRingHom.comp (algebraMap ℤ (KF b d)))
          (Int.castRingHom ℂ)]
        rfl
      change ((KF b d).val.toRingHom) _ = (KF b d).val 0
      rw [h, map_zero]
      rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X]
      simp only [eq_intCast, Int.cast_mul, Int.cast_natCast]
      linear_combination theta_sq hok⟩

lemma algebraMap_thetaO {a : ℕ} {b c : ℤ} {d : ℕ} (hok : UnitDetRootDefs.CmOK a b c d) :
    algebraMap (𝓞 (KF b d)) ℂ (thetaO hok) = UnitDetRootDefs.cmTheta b d := by
  rfl

lemma vol_std_le {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    (hok : UnitDetRootDefs.CmOK a b c d) {m : Type} [Fintype m] [DecidableEq m] :
    vol (KF b d) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≤ Submodule.span (𝓞 (KF b d)) {lam ^ Fintype.card m} := by
  unfold vol volSet UnitDetRootDefs.stdLat
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  have h1 : ∀ j i, v j i ∈ (UnitDetRootDefs.cmL a b d ha hd lam hlam).lattice :=
    fun j i => (show ∀ i ∈ (Set.univ : Set m), v j i ∈ _ from hv j) i (Set.mem_univ i)
  clear hv
  have hent : ∀ j i, ∃ o : 𝓞 (KF b d), v j i = lam * algebraMap (𝓞 (KF b d)) ℂ o := by
    intro j i
    have h2 := h1 j i
    simp only [PeriodPair.lattice, UnitDetRootDefs.cmL, UnitDetRootDefs.scalePair,
      UnitDetRootDefs.cmPair] at h2
    obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp h2
    refine ⟨p * (a : 𝓞 (KF b d)) + q * thetaO hok, ?_⟩
    rw [← hpq]
    simp only [map_add (f := _), map_mul, algebraMap_thetaO, map_intCast, map_natCast, zsmul_eq_mul]
    ring
  choose o ho using hent
  have hM : Matrix.of v = lam • (algebraMap (𝓞 (KF b d)) ℂ).mapMatrix (Matrix.of o) := by
    ext j i
    simp [ho j i]
  rw [hM, Matrix.det_smul, ← RingHom.map_det]
  refine Submodule.mem_span_singleton.mpr ⟨(Matrix.of o).det, ?_⟩
  rw [Algebra.smul_def, mul_comm]

lemma vol_std_ne_bot {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [Fintype m] [DecidableEq m] :
    vol (KF b d) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ ⊥ := by
  unfold vol volSet UnitDetRootDefs.stdLat
  rw [Submodule.ne_bot_iff]
  refine ⟨(Matrix.of fun (j i : m) => if i = j then lam * (a : ℂ) else 0).det,
    Submodule.subset_span ⟨_, fun j => ?_, rfl⟩, ?_⟩
  · refine fun i _ => ?_
    show (if i = j then lam * (a : ℂ) else 0) ∈ (UnitDetRootDefs.cmL a b d ha hd lam hlam).lattice
    have hω : lam * (a : ℂ) ∈ (UnitDetRootDefs.cmL a b d ha hd lam hlam).lattice := by
      simp only [PeriodPair.lattice, UnitDetRootDefs.cmL, UnitDetRootDefs.scalePair,
        UnitDetRootDefs.cmPair]
      exact Submodule.subset_span (Set.mem_insert _ _)
    by_cases h : i = j
    · rw [if_pos h]
      exact hω
    · rw [if_neg h]
      exact zero_mem _
  · have hD : (Matrix.of fun (j i : m) => if i = j then lam * (a : ℂ) else 0) =
        Matrix.diagonal (fun _ => lam * (a : ℂ)) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.diagonal_apply, h, eq_comm]
    rw [hD, Matrix.det_diagonal, Finset.prod_const]
    exact pow_ne_zero _ (mul_ne_zero hlam (by exact_mod_cast ha.ne'))

end PI.UnitaryGroupMassFormula.UnitDetRoot
end
end

