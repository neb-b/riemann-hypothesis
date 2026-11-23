module

public import Formalism.SatakeDualWeyl.Bundle0001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0004
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SphericalA
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001

@[expose] public section

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckecomm
section
noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section Gelfand

variable {G : Type} [Group G]

theorem heckecomm_theta_one (θ : G → G) (hm : ∀ x y, θ (x * y) = θ y * θ x) : θ 1 = 1 := by
  have h := hm 1 1
  rw [mul_one] at h
  have h' : θ 1 * θ 1 = θ 1 * 1 := by rw [mul_one, ← h]
  exact mul_left_cancel h'

theorem heckecomm_theta_inv (θ : G → G) (hm : ∀ x y, θ (x * y) = θ y * θ x) (x : G) :
    θ x⁻¹ = (θ x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hm, mul_inv_cancel, heckecomm_theta_one θ hm]

theorem heckecomm_coset_inv (K : Subgroup G) (θ : G → G)
    (hm : ∀ x y, θ (x * y) = θ y * θ x) (hi : ∀ x, θ (θ x) = x) (hK : ∀ x ∈ K, θ x ∈ K)
    (h : G) (y : G ⧸ K) :
    ((θ h * (θ (((h * (θ y.out)⁻¹ : G) : G ⧸ K).out))⁻¹ : G) : G ⧸ K) = y := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K (h * (θ y.out)⁻¹)
  rw [hc]
  conv_rhs => rw [← QuotientGroup.out_eq' y]
  rw [QuotientGroup.eq]
  have hinv := heckecomm_theta_inv θ hm
  rw [hm, hm, hinv, hi]
  convert hK _ c.2 using 1
  group

theorem heckecomm_gelfand {k : Type} [CommRing k] (K : Subgroup G) (θ : G → G)
    (hm : ∀ x y, θ (x * y) = θ y * θ x) (hi : ∀ x, θ (θ x) = x) (hK : ∀ x ∈ K, θ x ∈ K)
    (hdc : ∀ g, ∃ a b : K, θ g = (a : G) * g * b)
    (f₁ f₂ : G → k) (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) :
    conv K f₁ f₂ = conv K f₂ f₁ := by
  have hθf : ∀ f : G → k, IsBiInv K f → ∀ x, f (θ x) = f x := by
    intro f hf x
    obtain ⟨a, b, e⟩ := hdc x
    rw [e, hf]
  have hinv := heckecomm_theta_inv θ hm
  funext g
  rw [← hθf _ (conv_biInv K f₁ f₂ hf₁ hf₂) g]
  let e : G ⧸ K ≃ G ⧸ K :=
    { toFun := fun y => ((g * (θ y.out)⁻¹ : G) : G ⧸ K)
      invFun := fun y => ((θ g * (θ y.out)⁻¹ : G) : G ⧸ K)
      left_inv := fun y => heckecomm_coset_inv K θ hm hi hK g y
      right_inv := fun y => by
        have := heckecomm_coset_inv K θ hm hi hK (θ g) y
        rwa [hi] at this }
  unfold conv
  conv_rhs => rw [← finsum_comp_equiv e]
  refine finsum_congr fun y => ?_
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K (g * (θ y.out)⁻¹)
  have he : (e y).out = g * (θ y.out)⁻¹ * c := hc
  rw [he, mul_comm (f₁ _)]
  have h1 : (g * (θ y.out)⁻¹ * c)⁻¹ * g = (c⁻¹ : K) * θ y.out * (1 : K) := by
    simp only [Subgroup.coe_inv, OneMemClass.coe_one, mul_one]
    group
  have h2 : g * (θ y.out)⁻¹ * c = (1 : K) * (g * (θ y.out)⁻¹) * c := by
    simp only [OneMemClass.coe_one, one_mul]
  rw [h1, hf₁, hθf _ hf₁, h2, hf₂, ← hθf _ hf₂, hm, hinv, hi]

end Gelfand

section Transpose

variable {R : Type} [CommRing R] {n : ℕ}

def heckecomm_tr (g : GL (Fin n) R) : GL (Fin n) R :=
  ⟨Matrix.transpose (g : Matrix (Fin n) (Fin n) R), Matrix.transpose ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R),
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

theorem heckecomm_tr_val (g : GL (Fin n) R) :
    ((heckecomm_tr g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Matrix.transpose (g : Matrix (Fin n) (Fin n) R) := rfl

theorem heckecomm_tr_mul (x y : GL (Fin n) R) :
    heckecomm_tr (x * y) = heckecomm_tr y * heckecomm_tr x := by
  apply Units.ext
  simp only [heckecomm_tr_val, Units.val_mul, Matrix.transpose_mul]

theorem heckecomm_tr_tr (x : GL (Fin n) R) : heckecomm_tr (heckecomm_tr x) = x := by
  apply Units.ext
  simp only [heckecomm_tr_val, Matrix.transpose_transpose]

theorem heckecomm_tr_mem {L : Type} [Field L] (O : Subring L) (x : GL (Fin n) L)
    (hx : x ∈ GLint (Fin n) O) : heckecomm_tr x ∈ GLint (Fin n) O := by
  obtain ⟨h, rfl⟩ := hx
  refine ⟨heckecomm_tr h, ?_⟩
  apply Units.ext
  ext i j
  simp [bc, heckecomm_tr_val]

end Transpose

theorem heckecomm_tr_dc (hC : CartanDecomp) (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (g : GL (Fin n) (v.adicCompletion F)) :
    ∃ a b : GLint (Fin n) (Ov F v), heckecomm_tr g = (a : GL (Fin n) (v.adicCompletion F)) * g * b := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hϖO : (π : v.adicCompletion F) ∈ Ov F v := by
    show Valued.v (π : v.adicCompletion F) ≤ 1
    rw [HeightOneSpectrum.adicCompletion.valued_coe, hπ]
    exact (WithZero.exp_le_exp.mpr (by norm_num : (-1:ℤ) ≤ 0)).trans (le_of_eq WithZero.exp_zero)
  have hϖU : IsUnifV F v (π : v.adicCompletion F) := by
    unfold IsUnifV
    rw [HeightOneSpectrum.adicCompletion.valued_coe, hπ]
    rfl
  obtain ⟨a, -, k₁, hk₁, k₂, hk₂, e⟩ := hC F v n _ hϖO hϖU g
  obtain ⟨D, hDdef⟩ : ∃ D : GL (Fin n) (v.adicCompletion F), D = k₁⁻¹ * g * k₂⁻¹ := ⟨_, rfl⟩
  have hD : (D : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = diagPow F v (π : v.adicCompletion F) a := by
    rw [hDdef]
    simp only [Units.val_mul, e, mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one]
  have hDt : heckecomm_tr D = D := by
    apply Units.ext
    rw [heckecomm_tr_val, hD]
    exact Matrix.diagonal_transpose _
  have hg : g = k₁ * D * k₂ := by rw [hDdef]; group
  have hK := heckecomm_tr_mem (n := n) (Ov F v)
  refine ⟨⟨heckecomm_tr k₂ * k₁⁻¹, (GLint (Fin n) (Ov F v)).mul_mem (hK _ hk₂)
      ((GLint (Fin n) (Ov F v)).inv_mem hk₁)⟩,
    ⟨k₂⁻¹ * heckecomm_tr k₁, (GLint (Fin n) (Ov F v)).mul_mem ((GLint (Fin n) (Ov F v)).inv_mem hk₂)
      (hK _ hk₁)⟩, ?_⟩
  conv_lhs => rw [hg]
  rw [heckecomm_tr_mul, heckecomm_tr_mul, hDt, hDdef]
  simp only
  group

theorem hecke_algebra_GL_comm_of_cartan (hCartanDecomp : Formalism.UG.CartanDecomp) : Formalism.UG.HeckeCommGL := by
  intro F _ _ v n k _ f₁ hf₁ f₂ hf₂
  exact heckecomm_gelfand _ heckecomm_tr heckecomm_tr_mul heckecomm_tr_tr
    (heckecomm_tr_mem (Ov F v)) (heckecomm_tr_dc hCartanDecomp F v n) f₁ f₂ hf₁.1 hf₂.1

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Spherical
section
open NumberField IsDedekindDomain Formalism.UG

namespace Formalism.UG.P

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private lemma exists_GLint_of_integral_inverse {n : ℕ} (A B : Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hA : ∀ i j, A i j ∈ Ov F v) (hB : ∀ i j, B i j ∈ Ov F v) (hAB : A * B = 1) (hBA : B * A = 1) :
    ∃ k ∈ GLint (Fin n) (Ov F v), (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = A := by
  let A' : Matrix (Fin n) (Fin n) (Ov F v) := Matrix.of fun i j => ⟨A i j, hA i j⟩
  let B' : Matrix (Fin n) (Fin n) (Ov F v) := Matrix.of fun i j => ⟨B i j, hB i j⟩
  have hinj : ∀ M N : Matrix (Fin n) (Fin n) (Ov F v),
      RingHom.mapMatrix (Ov F v).subtype M = RingHom.mapMatrix (Ov F v).subtype N → M = N := by
    intro M N h
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
  have hmA : RingHom.mapMatrix (Ov F v).subtype A' = A := Matrix.ext fun i j => rfl
  have hmB : RingHom.mapMatrix (Ov F v).subtype B' = B := Matrix.ext fun i j => rfl
  have hAB' : A' * B' = 1 := hinj _ _ (by rw [map_mul, map_one, hmA, hmB, hAB])
  have hBA' : B' * A' = 1 := hinj _ _ (by rw [map_mul, map_one, hmA, hmB, hBA])
  let u : GL (Fin n) (Ov F v) := ⟨A', B', hAB', hBA'⟩
  exact ⟨bc (Ov F v).subtype u, ⟨u, rfl⟩, Matrix.ext fun i j => rfl⟩

private lemma mul_column_operation_apply {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (r : Fin n)
    (c : Fin n → R) (x b : Fin n) :
    (M * Matrix.of fun a b => (if a = b then (1 : R) else 0) + (if a = r ∧ b ≠ r then c b else 0)) x b =
      M x b + (if b ≠ r then M x r * c b else 0) := by
  by_cases hb : b = r
  · subst hb
    simp [Matrix.mul_apply]
  · simp [Matrix.mul_apply, hb, mul_add, Finset.sum_add_distrib]

private lemma column_operation_mul_neg_eq_one {R : Type*} [CommRing R] {n : ℕ} (r : Fin n) (c : Fin n → R) :
    (Matrix.of fun a b => (if a = b then (1 : R) else 0) + (if a = r ∧ b ≠ r then c b else 0)) *
      (Matrix.of fun a b => (if a = b then (1 : R) else 0) + (if a = r ∧ b ≠ r then -c b else 0)) = 1 := by
  ext a b
  rw [mul_column_operation_apply _ r (fun b => -c b)]
  by_cases hbr : b = r
  · subst hbr
    simp [Matrix.one_apply]
  · by_cases har : a = r
    · subst har
      have hne : a ≠ b := fun h => hbr h.symm
      simp [Matrix.one_apply, hbr, hne]
    · simp [Matrix.one_apply, hbr, har]

private lemma exists_GLint_eq_column_operation {n : ℕ} (r : Fin n) (c : Fin n → v.adicCompletion F)
    (hc : ∀ b, c b ∈ Ov F v) :
    ∃ k ∈ GLint (Fin n) (Ov F v), (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      Matrix.of fun a b => (if a = b then (1 : v.adicCompletion F) else 0) +
        (if a = r ∧ b ≠ r then c b else 0) := by
  refine exists_GLint_of_integral_inverse F v _
    (Matrix.of fun a b => (if a = b then (1 : v.adicCompletion F) else 0) + (if a = r ∧ b ≠ r then -c b else 0))
    ?_ ?_ (column_operation_mul_neg_eq_one r c) ?_
  · intro i j
    simp only [Matrix.of_apply]
    refine Subring.add_mem _ ?_ ?_
    · split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · split_ifs
      · exact hc j
      · exact Subring.zero_mem _
  · intro i j
    simp only [Matrix.of_apply]
    refine Subring.add_mem _ ?_ ?_
    · split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · split_ifs
      · exact Subring.neg_mem _ (hc j)
      · exact Subring.zero_mem _
  · have h := column_operation_mul_neg_eq_one r (fun b => -c b)
    simpa using h

private lemma mem_Ov_of_valuation_le_one (x : v.adicCompletion F) (h : Valued.v x ≤ 1) : x ∈ Ov F v := by
  change x ∈ v.adicCompletionIntegers F
  exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h

private lemma exists_GLint_mul_clears_below_diag_from {n : ℕ} (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) (i0 : Fin n)
    (hM : ∀ i j : Fin n, i0 < i → j < i → M i j = 0) :
    ∃ k ∈ GLint (Fin n) (Ov F v), ∀ i j : Fin n, i0 ≤ i → j < i →
      (M * (k : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i j = 0 := by
  classical
  by_cases hz : ∀ j, j < i0 → M i0 j = 0
  · refine ⟨1, Subgroup.one_mem _, fun i j hi hj => ?_⟩
    simp only [Units.val_one, Matrix.mul_one]
    rcases hi.lt_or_eq with h | h
    · exact hM i j h hj
    · subst h
      exact hz j hj
  push_neg at hz
  obtain ⟨j1, hj1, hj1ne⟩ := hz
  obtain ⟨p, hpS, hpmax⟩ := Finset.exists_max_image (Finset.univ.filter (fun j => j ≤ i0))
    (fun j => Valued.v (M i0 j)) ⟨i0, by simp⟩
  have hp : p ≤ i0 := (Finset.mem_filter.mp hpS).2
  have hmax : ∀ j, j ≤ i0 → Valued.v (M i0 j) ≤ Valued.v (M i0 p) := fun j hj => hpmax j (by simp [hj])
  have hppos : 0 < Valued.v (M i0 p) :=
    lt_of_lt_of_le ((Valuation.pos_iff _).mpr hj1ne) (hmax j1 hj1.le)
  obtain ⟨k1, hk1, hrows1, hpiv1, hne1⟩ : ∃ k1 ∈ GLint (Fin n) (Ov F v),
      (∀ i j : Fin n, i0 < i → j < i →
        (M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i j = 0) ∧
      (∀ j, j ≤ i0 → Valued.v ((M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i0 j) ≤
        Valued.v ((M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i0 i0)) ∧
      (M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i0 i0 ≠ 0 := by
    by_cases heq : Valued.v (M i0 i0) = Valued.v (M i0 p)
    · refine ⟨1, Subgroup.one_mem _, ?_, ?_, ?_⟩
      · simpa using hM
      · intro j hj
        simpa [heq] using hmax j hj
      · simp only [Units.val_one, Matrix.mul_one]
        intro h0
        rw [h0, map_zero] at heq
        exact (ne_of_lt hppos) heq
    · have hlt : Valued.v (M i0 i0) < Valued.v (M i0 p) := lt_of_le_of_ne (hmax i0 le_rfl) heq
      have hpi0 : p ≠ i0 := fun h => heq (by rw [h])
      obtain ⟨k1, hk1, hk1eq⟩ := exists_GLint_eq_column_operation F v p (fun b => if b = i0 then 1 else 0) (fun b => by
        split_ifs
        · exact Subring.one_mem _
        · exact Subring.zero_mem _)
      have hdiag : (M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i0 i0 = M i0 i0 + M i0 p := by
        rw [hk1eq, mul_column_operation_apply]
        simp [Ne.symm hpi0]
      refine ⟨k1, hk1, ?_, ?_, ?_⟩
      · intro i j hi hj
        rw [hk1eq, mul_column_operation_apply, hM i j hi hj, hM i p hi (lt_of_le_of_lt hp hi)]
        simp
      · intro j hj
        rw [hdiag, Valuation.map_add_eq_of_lt_right _ hlt]
        by_cases hji : j = i0
        · subst hji
          rw [hdiag, Valuation.map_add_eq_of_lt_right _ hlt]
        · rw [hk1eq, mul_column_operation_apply]
          simp only [hji, if_false, mul_zero, ite_self, add_zero]
          exact hmax j hj
      · rw [hdiag]
        intro h0
        have h1 := Valuation.map_add_eq_of_lt_right Valued.v hlt
        rw [h0, map_zero] at h1
        exact (ne_of_lt hppos) h1
  set M1 := M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) with hM1
  obtain ⟨k2, hk2, hk2eq⟩ := exists_GLint_eq_column_operation F v i0
    (fun b => if b < i0 then -(M1 i0 b / M1 i0 i0) else 0) (fun b => by
      split_ifs with hb
      · apply mem_Ov_of_valuation_le_one
        rw [Valuation.map_neg, map_div₀]
        exact div_le_one_of_le₀ (hpiv1 b hb.le) zero_le'
      · exact Subring.zero_mem _)
  refine ⟨k1 * k2, Subgroup.mul_mem _ hk1 hk2, fun i j hi hj => ?_⟩
  rw [Units.val_mul, ← Matrix.mul_assoc, ← hM1, hk2eq, mul_column_operation_apply]
  rcases hi.lt_or_eq with h | h
  · rw [hrows1 i j h hj, hrows1 i i0 h h]
    simp
  · subst h
    have hji : j ≠ i0 := ne_of_lt hj
    simp only [hji, ne_eq, not_false_eq_true, if_true, hj]
    field_simp
    ring

theorem spherical_iwasawa {n : ℕ} (g : GL (Fin n) (v.adicCompletion F)) :
    ∃ b k : GL (Fin n) (v.adicCompletion F),
      (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id ∧
      k ∈ GLint (Fin n) (Ov F v) ∧ g = b * k := by
  classical
  have key : ∀ r, r ≤ n → ∃ k ∈ GLint (Fin n) (Ov F v), ∀ i j : Fin n, n - r ≤ i.val → j < i →
      ((g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        (k : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i j = 0 := by
    intro r
    induction r with
    | zero =>
      intro _
      refine ⟨1, Subgroup.one_mem _, fun i j hi _ => ?_⟩
      have := i.isLt
      omega
    | succ r ih =>
      intro hr
      obtain ⟨k, hk, hup⟩ := ih (by omega)
      obtain ⟨k2, hk2, h2⟩ := exists_GLint_mul_clears_below_diag_from F v
        ((g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)))
        ⟨n - r - 1, by omega⟩ (fun i j hi hj => hup i j (by rw [Fin.lt_def] at hi; simp at hi; omega) hj)
      refine ⟨k * k2, Subgroup.mul_mem _ hk hk2, fun i j hi hj => ?_⟩
      rw [Units.val_mul, ← Matrix.mul_assoc]
      exact h2 i j (by rw [Fin.le_def]; simp; omega) hj
  obtain ⟨k, hk, hup⟩ := key n le_rfl
  refine ⟨g * k, k⁻¹, ?_, Subgroup.inv_mem _ hk, by group⟩
  rw [← spherical_upper_iff]
  intro i j hji
  rw [Units.val_mul]
  exact hup i j (by omega) hji

theorem spherical_wd {n : ℕ} (α : Fin n → ℂ) (hα : ∀ i, α i ≠ 0) (b b' k k' : GL (Fin n) (v.adicCompletion F))
    (hb : (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id)
    (hb' : (b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id)
    (hk : k ∈ GLint (Fin n) (Ov F v)) (hk' : k' ∈ GLint (Fin n) (Ov F v)) (h : b * k = b' * k') :
    chiDelta F v α b = chiDelta F v α b' := by
  have hq : b'⁻¹ * b = k' * k⁻¹ := by
    calc b'⁻¹ * b = b'⁻¹ * (b * k) * k⁻¹ := by group
      _ = b'⁻¹ * (b' * k') * k⁻¹ := by rw [h]
      _ = k' * k⁻¹ := by group
  have hup : ((b'⁻¹ * b : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id :=
    spherical_upper_mul _ _ (spherical_upper_inv _ hb') hb
  have hint : b'⁻¹ * b ∈ GLint (Fin n) (Ov F v) := by
    rw [hq]
    exact Subgroup.mul_mem _ hk' (Subgroup.inv_mem _ hk)
  have hb_eq : b = b' * (b'⁻¹ * b) := by group
  rw [hb_eq, spherical_chiDelta_mul F v α hα b' _ hb' hup, spherical_chiDelta_int F v α _ hup hint, mul_one]

theorem exists_spherical_function : Formalism.UG.SphericalExists := by
  intro F _ _ v n α hα
  classical
  have dec := fun g : GL (Fin n) (v.adicCompletion F) => spherical_iwasawa F v g
  let φ : GL (Fin n) (v.adicCompletion F) → ℂ := fun g => chiDelta F v α (Classical.choose (dec g))
  have hφ : ∀ g b k : GL (Fin n) (v.adicCompletion F),
      (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id →
      k ∈ GLint (Fin n) (Ov F v) → g = b * k → φ g = chiDelta F v α b := by
    intro g b k hb hk hg
    obtain ⟨k0, hb0, hk0, hg0⟩ := Classical.choose_spec (dec g)
    exact spherical_wd F v α hα _ _ _ _ hb0 hb hk0 hk (hg0.symm.trans hg)
  have hone : ((1 : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id :=
    (spherical_upper_iff 1).mp (fun i j h => by simp [Matrix.one_apply_ne (ne_of_gt h)])
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro b g k hb hk
    have hb' := (spherical_upper_iff b).mp hb
    obtain ⟨b0, k0, hb0, hk0, hg0⟩ := dec g
    rw [hφ g b0 k0 hb0 hk0 hg0,
      hφ (b * g * k) (b * b0) (k0 * k) (spherical_upper_mul b b0 hb' hb0)
        (Subgroup.mul_mem _ hk0 hk) (by rw [hg0]; group),
      spherical_chiDelta_mul F v α hα b b0 hb' hb0]
  · rw [hφ 1 1 1 hone (Subgroup.one_mem _) (by simp)]
    exact spherical_chiDelta_int F v α 1 hone (Subgroup.one_mem _)
  · intro ψ hψ
    funext g
    obtain ⟨b0, k0, hb0, hk0, hg0⟩ := dec g
    have h1 := hψ b0 1 k0 ((spherical_upper_iff b0).mpr hb0) hk0
    rw [mul_one] at h1
    rw [hg0, hφ (b0 * k0) b0 k0 hb0 hk0 rfl, h1, mul_comm]

end Formalism.UG.P
end

