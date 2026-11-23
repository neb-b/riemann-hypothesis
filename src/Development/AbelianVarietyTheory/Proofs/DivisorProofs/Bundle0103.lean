module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqInertiaDegAffineChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.ResidueDegreeChart

theorem inertiaDeg_eq_finrank_of_ker {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [Algebra R S] [Algebra K L] (φ : R →+* K) (ψ : S →+* L) (q : Ideal S)
    (hq : ∀ s, s ∈ q ↔ ψ s = 0)
    (hφ : ∀ z : K, ∃ a b, z = φ a / φ b) (hψ : ∀ z : L, ∃ a b, z = ψ a / ψ b)
    (hc : ∀ r, algebraMap K L (φ r) = ψ (algebraMap R S r)) :
    q.inertiaDeg R = Module.finrank K L := by
  have hq' : q = RingHom.ker ψ := by ext s; simp [hq, RingHom.mem_ker]
  subst hq'
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have : (RingHom.ker ψ).LiesOver (RingHom.ker φ) := ⟨by
    ext r
    simp only [RingHom.mem_ker, Ideal.under, Ideal.mem_comap, ← hc]
    simp⟩
  let _ : Algebra R K := φ.toAlgebra
  let _ : Algebra S L := ψ.toAlgebra
  let _ : Algebra R L := (ψ.comp (algebraMap R S)).toAlgebra
  let _ : Algebra (R ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  let _ : Algebra (S ⧸ RingHom.ker ψ) L := (RingHom.kerLift ψ).toAlgebra
  have : FaithfulSMul (R ⧸ RingHom.ker φ) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective φ)
  have : FaithfulSMul (S ⧸ RingHom.ker ψ) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective ψ)
  have : IsFractionRing (R ⧸ RingHom.ker φ) K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, h⟩ := hφ z
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b, h⟩
  have : IsFractionRing (S ⧸ RingHom.ker ψ) L := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, h⟩ := hψ z
    exact ⟨Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b, h⟩
  have : IsScalarTower R (R ⧸ RingHom.ker φ) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower S (S ⧸ RingHom.ker ψ) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun r => (hc r).symm
  exact Ideal.inertiaDeg_eq_of_isFractionRing (RingHom.ker φ) (RingHom.ker ψ) K L

theorem mem_primeIdealOf_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) (s : Γ(X, U)) :
    s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔ (X.evaluation U x hx).hom s = 0 := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal s, ← IsLocalRing.residue_eq_zero_iff]
  rfl

theorem exists_eq_div_evaluation {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) (z : X.residueField x) :
    ∃ a b, z = (X.evaluation U x hx).hom a / (X.evaluation U x hx).hom b := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨t, rfl⟩ := X.residue_surjective x z
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (S := X.presheaf.stalk x) t
  refine ⟨a, b, ?_⟩
  have hb : (X.evaluation U x hx).hom b ≠ 0 := fun h0 =>
    b.2 ((mem_primeIdealOf_iff hU x hx b).2 h0)
  rw [eq_div_iff hb]
  have := congrArg (X.residue x).hom h
  rw [map_mul] at this
  exact this

theorem residueDegree_eq_inertiaDeg : ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hU : IsAffineOpen (g ⁻¹ᵁ V)) (w : Y) (hw : w ∈ g ⁻¹ᵁ V), g.residueDegree w = @Ideal.inertiaDeg Γ(Y, g ⁻¹ᵁ V) _ (hU.primeIdealOf ⟨w, hw⟩).asIdeal Γ(X, V) _ (g.app V).hom.toAlgebra := by
  intro X Y g V hV hU w hw
  let _ : Algebra Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := (g.app V).hom.toAlgebra
  let _ : Algebra (X.residueField (g w)) (Y.residueField w) := (g.residueFieldMap w).hom.toAlgebra
  symm
  exact inertiaDeg_eq_finrank_of_ker (X.evaluation V (g w) hw).hom
    (Y.evaluation (g ⁻¹ᵁ V) w hw).hom _ (mem_primeIdealOf_iff hU w hw)
    (exists_eq_div_evaluation hV (g w) hw) (exists_eq_div_evaluation hU w hw)
    (fun r => Scheme.evaluation_naturality_apply g w hw r)

end GlobalTheory.ResidueDegreeChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannSumOfOneSidedIncrements
section
open Filter Topology

namespace GlobalTheory

theorem polynomial_increment_near_derivative (s : Polynomial ℝ) {η δ : ℝ}
    (hδ : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, dist x y < δ →
      dist (s.derivative.eval x) (s.derivative.eval y) < η)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hba : b - a < δ) :
    (b - a) * s.derivative.eval a ≤ s.eval b - s.eval a + η * (b - a) ∧
    s.eval b - s.eval a ≤ (b - a) * s.derivative.eval b + η * (b - a) := by
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope (fun x => s.eval x) hab
    s.continuous.continuousOn (fun x _ => s.differentiableAt.differentiableWithinAt)
  rw [Polynomial.deriv] at hcd
  have hpos : 0 < b - a := sub_pos.mpr hab
  have hsc : s.eval b - s.eval a = (b - a) * s.derivative.eval c := by
    rw [hcd]; field_simp
  have h1 := hδ c ⟨by linarith [hc.1], by linarith [hc.2]⟩ a ⟨ha, by linarith⟩
    (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hc.1, hc.2])
  have h2 := hδ c ⟨by linarith [hc.1], by linarith [hc.2]⟩ b ⟨by linarith, hb⟩
    (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hc.1, hc.2])
  rw [Real.dist_eq, abs_lt] at h1 h2
  constructor
  · rw [hsc]; nlinarith [mul_lt_mul_of_pos_left h1.1 hpos]
  · rw [hsc]; nlinarith [mul_lt_mul_of_pos_left h2.2 hpos]

theorem riemann_sum_of_one_sided_increments : ∀ (s : Polynomial ℝ) (ℓ : ℚ → ℕ → ℝ),
    (∀ t t' : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop, ℓ t m - ℓ t' m ≤ ((t' : ℝ) - t) * s.derivative.eval (t : ℝ) + ε) →
    Tendsto (fun m => ℓ 0 m - ℓ 1 m) atTop (𝓝 (s.eval 1 - s.eval 0)) := by
  intro s ℓ h
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε / 4 := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; positivity
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous s.derivative.continuous.continuousOn) η hηpos
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  have hnpos : (0:ℝ) < n := lt_trans (by positivity) hn
  have hn0 : n ≠ 0 := by exact_mod_cast hnpos.ne'
  have hstep : (1:ℝ) / n < δ := by
    rw [div_lt_iff₀ hnpos]; rw [div_lt_iff₀ hδpos] at hn; linarith
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℚ, t = fun j : ℕ => (j : ℚ) / n := ⟨_, rfl⟩
  have ht0 : ∀ j, 0 ≤ t j := fun j => by rw [ht]; positivity
  have ht1 : ∀ j ≤ n, t j ≤ 1 := fun j hj => by
    rw [ht]; show (j:ℚ) / n ≤ 1
    rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn0)]; exact_mod_cast hj
  have htR : ∀ j, ((t j : ℚ) : ℝ) = (j : ℝ) / n := fun j => by rw [ht]; push_cast; ring
  have hdiff : ∀ j, ((t (j+1) : ℚ) : ℝ) - t j = 1 / n := fun j => by
    rw [htR, htR]; push_cast; ring
  have hηn : η * (1 / (n:ℝ)) = η / n := by ring
  have hup : ∀ᶠ m in atTop, ∀ j ∈ Finset.range n, ℓ (t j) m - ℓ (t (j+1)) m ≤
      (((t (j+1)) : ℝ) - t j) * s.derivative.eval (t j : ℝ) + η / n := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact h _ _ (ht0 j) (ht1 j hj'.le) (ht0 (j+1)) (ht1 (j+1) hj') _ (by positivity)
  have hlo : ∀ᶠ m in atTop, ∀ j ∈ Finset.range n, ℓ (t (j+1)) m - ℓ (t j) m ≤
      (((t j) : ℝ) - t (j+1)) * s.derivative.eval (t (j+1) : ℝ) + η / n := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact h _ _ (ht0 (j+1)) (ht1 (j+1) hj') (ht0 j) (ht1 j hj'.le) _ (by positivity)
  filter_upwards [hup, hlo] with m hu hl
  have t0 : t 0 = 0 := by rw [ht]; simp
  have tn : t n = 1 := by
    rw [ht]; show (n:ℚ) / n = 1; exact div_self (by exact_mod_cast hn0)
  have hsumℓ : ℓ 0 m - ℓ 1 m = ∑ j ∈ Finset.range n, (ℓ (t j) m - ℓ (t (j+1)) m) := by
    have := Finset.sum_range_sub' (fun j => ℓ (t j) m) n
    rw [this, t0, tn]
  have hsums : s.eval 1 - s.eval 0 =
      ∑ j ∈ Finset.range n, (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ)) := by
    have := Finset.sum_range_sub (fun j => s.eval (t j : ℝ)) n
    rw [this, t0, tn]; simp
  have hstepb : ∀ j ∈ Finset.range n,
      |(ℓ (t j) m - ℓ (t (j+1)) m) - (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ))| ≤ 2 * (η / n) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hd := hdiff j
    have h1n : (0:ℝ) < 1 / n := by positivity
    obtain ⟨k1, k2⟩ := polynomial_increment_near_derivative s hδ (a := t j) (b := t (j+1))
      (by exact_mod_cast ht0 j) (by linarith) (by exact_mod_cast ht1 _ hj') (by rw [hd]; exact hstep)
    have u := hu j hj
    have l := hl j hj
    have hd' : ((t j : ℚ) : ℝ) - t (j+1) = -(1 / n) := by linarith
    rw [hd] at k1 k2 u
    rw [hd'] at l
    rw [hηn] at k1 k2
    rw [abs_le]; constructor
    · nlinarith
    · nlinarith
  rw [Real.dist_eq, hsumℓ, hsums, ← Finset.sum_sub_distrib]
  calc |∑ j ∈ Finset.range n, ((ℓ (t j) m - ℓ (t (j+1)) m) - (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ)))|
      ≤ ∑ j ∈ Finset.range n, |(ℓ (t j) m - ℓ (t (j+1)) m) - (s.eval (t (j+1) : ℝ) - s.eval (t j : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, 2 * (η / n) := Finset.sum_le_sum hstepb
    _ = 2 * η := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    _ < ε := by rw [hη]; linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightInvariantGLOfUpperTriangularRightInvariant
section
open Matrix Polynomial

namespace GlobalTheory

theorem poly_eval_eq_eval_zero_of_eq_inv {k : Type} [Field k] [Infinite k] (p q : k[X]) (c : k)
    (h : ∀ x : k, x ≠ 0 → p.eval x = c * q.eval x⁻¹) : ∀ x : k, p.eval x = p.eval 0 := by
  set N := q.natDegree
  have key : X ^ N * p = C c * reflect N q := by
    apply eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := ({0}ᶜ : Set k))
    · intro x hx
      have hx0 : x ≠ 0 := hx
      letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx0)
      have hr := eval₂_reflect_mul_pow (RingHom.id k) x⁻¹ N q le_rfl
      rw [invOf_eq_inv, inv_inv] at hr
      simp only [Set.mem_setOf_eq, eval_mul, eval_pow, eval_X, eval_C, h x hx0]
      rw [← eval₂_id, ← eval₂_id, ← hr, inv_pow]
      field_simp
    · exact (Set.finite_singleton (0 : k)).infinite_compl
  by_cases hp : p = 0
  · intro x; simp [hp]
  have hdeg : (X ^ N * p).natDegree = N + p.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hp, natDegree_X_pow]
  have hle : (C c * reflect N q).natDegree ≤ N :=
    (natDegree_C_mul_le _ _).trans (natDegree_reflect_le.trans (by simp [N]))
  rw [key] at hdeg
  have h0 : p.natDegree = 0 := by omega
  intro x
  rw [eq_C_of_natDegree_eq_zero h0]
  simp

section Lower
variable {k : Type} [Field k] {m : ℕ}

def swapLine (i j : Fin m) (t : k) : Matrix (Fin m) (Fin m) k :=
  (1 - single j j 1 - single i i 1 + single j i 1 + single i j 1) + t • single j j 1

def upperFactor (i j : Fin m) (x : k) : Matrix (Fin m) (Fin m) k :=
  diagonal (Function.update (Function.update (1 : Fin m → k) j x⁻¹) i (-x)) * transvection j i x

theorem transvection_isUpper {i j : Fin m} (hji : j < i) (x : k) :
    (transvection j i x).BlockTriangular id := by
  intro a b hba
  simp only [id] at hba
  simp only [transvection, Matrix.add_apply, one_apply_ne (ne_of_gt hba), single_apply, zero_add]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact absurd hba (not_lt.mpr hji.le)
  · rfl

theorem upperFactor_isUpper {i j : Fin m} (hji : j < i) (x : k) :
    (upperFactor i j x).BlockTriangular id :=
  (blockTriangular_diagonal _).mul (transvection_isUpper hji x)

theorem upperFactor_det {i j : Fin m} (hji : j < i) {x : k} (hx : x ≠ 0) :
    (upperFactor i j x).det = -1 := by
  have hij : i ≠ j := ne_of_gt hji
  rw [upperFactor, det_mul, det_transvection_of_ne j i (ne_of_lt hji), det_diagonal,
    Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_update_of_mem (by simp [hij.symm] : j ∈ Finset.univ \ {i})]
  simp [hx]

theorem transvection_mul_upperFactor {i j : Fin m} (hji : j < i) {x : k} (hx : x ≠ 0) :
    transvection i j x * upperFactor i j x = swapLine i j x⁻¹ := by
  have hij : i ≠ j := ne_of_gt hji
  ext a b
  rw [transvection, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
  by_cases ha : a = i
  · subst ha
    rw [single_mul_apply_same]
    by_cases hb : b = a
    · subst hb
      simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
        Function.update_apply, hij, hij.symm, hx]
    · by_cases hbj : b = j
      · subst hbj
        simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
          Function.update_apply, hij, hij.symm, hx]
      · simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
          Function.update_apply, hij, hij.symm, hx, hb, hbj, Ne.symm hb, Ne.symm hbj]
  · rw [single_mul_apply_of_ne _ _ _ _ _ ha, add_zero]
    by_cases haj : a = j
    · subst haj
      by_cases hb : b = a
      · subst hb
        simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
          Function.update_apply, hij, hij.symm, hx]
      · by_cases hbi : b = i
        · subst hbi
          simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
            Function.update_apply, hij, hij.symm, hx]
        · simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
            Function.update_apply, hij, hij.symm, hx, hb, hbi, Ne.symm hb, Ne.symm hbi]
    · simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
        Function.update_apply, hij, hij.symm, hx, ha, haj, Ne.symm ha, Ne.symm haj]

end Lower

section Main
variable {k : Type} [Field k] [Infinite k] {m : ℕ}

theorem rightInv_lower_transvection (ψ Φ : Matrix (Fin m) (Fin m) k → k) (r : k → k)
    (hΦ : ∀ A₀ D : Matrix (Fin m) (Fin m) k, ∃ p : Polynomial k, ∀ x : k, Φ (A₀ + x • D) = p.eval x)
    (hψ : ∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ A = r A.det * Φ A)
    (hT : ∀ A T : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id →
      ψ (A * T) = ψ A)
    (A : Matrix (Fin m) (Fin m) k) (hA : A.det ≠ 0) {i j : Fin m} (hji : j < i) (x : k) :
    ψ (A * transvection i j x) = ψ A := by
  have hij : i ≠ j := ne_of_gt hji
  have hl : ∀ y : k, (transvection i j y).det = 1 := fun y => det_transvection_of_ne i j hij y
  have hAl : ∀ y : k, (A * transvection i j y).det = A.det := fun y => by
    rw [det_mul, hl, mul_one]
  obtain ⟨p, hp⟩ := hΦ A (A * single i j 1)
  obtain ⟨q, hq⟩ := hΦ (A * (1 - single j j 1 - single i i 1 + single j i 1 + single i j 1))
    (A * single j j 1)
  have e1 : ∀ y : k, ψ (A * transvection i j y) = r A.det * p.eval y := by
    intro y
    rw [hψ _ (by rw [hAl]; exact hA), hAl, ← hp]
    congr 2
    rw [transvection, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_smul, smul_single, smul_eq_mul,
      mul_one]
  have e2 : ∀ y : k, y ≠ 0 → r A.det * p.eval y = r (-A.det) * q.eval y⁻¹ := by
    intro y hy
    have hdT : (upperFactor i j y).det ≠ 0 := by rw [upperFactor_det hji hy]; norm_num
    rw [← e1, ← hT _ _ (by rw [hAl]; exact hA) hdT (upperFactor_isUpper hji y), Matrix.mul_assoc,
      transvection_mul_upperFactor hji hy]
    have hdM : (A * swapLine i j y⁻¹).det = -A.det := by
      rw [← transvection_mul_upperFactor hji hy, ← Matrix.mul_assoc, det_mul, hAl,
        upperFactor_det hji hy, mul_neg_one]
    rw [hψ _ (by rw [hdM]; exact neg_ne_zero.mpr hA), hdM, ← hq, swapLine, Matrix.mul_add,
      Matrix.mul_smul]
  by_cases hr : r A.det = 0
  · rw [e1, hr, zero_mul, hψ A hA, hr, zero_mul]
  have hconst := poly_eval_eq_eval_zero_of_eq_inv p q (r (-A.det) / r A.det) (fun y hy => by
    rw [div_mul_eq_mul_div, eq_div_iff hr, mul_comm, e2 y hy])
  rw [e1, hconst x, hψ A hA, ← hp, zero_smul, add_zero]

theorem rightInv_of_upperTriangular_rightInv :
    ∀ {k : Type} [Field k] [Infinite k] {m : ℕ} (ψ Φ : Matrix (Fin m) (Fin m) k → k) (r : k → k),
      (∀ A₀ D : Matrix (Fin m) (Fin m) k, ∃ p : Polynomial k, ∀ x : k, Φ (A₀ + x • D) = p.eval x) →
      (∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ A = r A.det * Φ A) →
      (∀ A T : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id →
        ψ (A * T) = ψ A) →
      ∀ A B : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → B.det ≠ 0 → ψ (A * B) = ψ A := by
  intro k _ _ m ψ Φ r hΦ hψ hT A B hA hB
  refine diagonal_transvection_induction_of_det_ne_zero
    (fun B => ∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ (A * B) = ψ A) B hB ?_ ?_ ?_ A hA
  · intro D hD A hA
    exact hT A _ hA hD (blockTriangular_diagonal D)
  · intro t A hA
    rcases lt_or_gt_of_ne t.hij with h | h
    · have hdet : (t.toMatrix).det ≠ 0 := by
        rw [TransvectionStruct.toMatrix, det_transvection_of_ne _ _ t.hij]; exact one_ne_zero
      exact hT A _ hA hdet (transvection_isUpper h t.c)
    · exact rightInv_lower_transvection ψ Φ r hΦ hψ hT A hA h t.c
  · intro B₁ B₂ h₁ h₂ P₁ P₂ A hA
    rw [← Matrix.mul_assoc, P₂ _ (by rw [det_mul]; exact mul_ne_zero hA h₁), P₁ _ hA]

end Main

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomDualNumberSndEqZero
section
namespace GlobalTheory

open Polynomial

theorem ringHom_dualNumber_snd_eq_zero (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F]
    {R : Type} [CommRing R] (φ : F →+* DualNumber R) (a : F) : (φ a).snd = 0 := by
  classical
  let ψ : F →+* R := (TrivSqZeroExt.fstHom R R R).toRingHom.comp φ
  have hψ : ∀ x, ψ x = (φ x).fst := fun x => rfl
  have hcomp : φ.comp (algebraMap ℚ F) =
      (TrivSqZeroExt.inlHom R R).comp (ψ.comp (algebraMap ℚ F)) := RingHom.ext_rat _ _
  have hint : IsIntegral ℚ a := Algebra.IsIntegral.isIntegral a
  have hsep : (minpoly ℚ a).Separable := (minpoly.irreducible hint).separable
  have hf0 : aeval a (minpoly ℚ a) = 0 := minpoly.aeval ℚ a
  have hd : aeval a (derivative (minpoly ℚ a)) ≠ 0 := hsep.aeval_derivative_ne_zero hf0
  have hu : IsUnit (ψ (aeval a (derivative (minpoly ℚ a)))) := (isUnit_iff_ne_zero.mpr hd).map ψ
  have hsplit : φ a = TrivSqZeroExt.inl (φ a).fst + TrivSqZeroExt.inr (φ a).snd :=
    (TrivSqZeroExt.inl_fst_add_inr_snd_eq _).symm
  have hsq : (TrivSqZeroExt.inr (φ a).snd : DualNumber R) ^ 2 = 0 := by
    rw [sq, TrivSqZeroExt.inr_mul_inr]
  have hev : ∀ p : ℚ[X], (p.map (φ.comp (algebraMap ℚ F))).eval (TrivSqZeroExt.inl (φ a).fst) =
      TrivSqZeroExt.inl (ψ (aeval a p)) := by
    intro p
    rw [hcomp, eval_map, aeval_def, ← hψ, Polynomial.hom_eval₂]
    change eval₂ _ (TrivSqZeroExt.inlHom R R (ψ a)) p = TrivSqZeroExt.inlHom R R _
    rw [Polynomial.hom_eval₂]
  have hlhs : ((minpoly ℚ a).map (φ.comp (algebraMap ℚ F))).eval (φ a) = 0 := by
    rw [eval_map, ← Polynomial.hom_eval₂, ← aeval_def, hf0, map_zero]
  have key := eval_add_of_sq_eq_zero ((minpoly ℚ a).map (φ.comp (algebraMap ℚ F)))
    (TrivSqZeroExt.inl (φ a).fst) (TrivSqZeroExt.inr (φ a).snd) hsq
  rw [← hsplit, hlhs, derivative_map, hev, hev, hf0, map_zero] at key
  have h2 := congrArg TrivSqZeroExt.snd key
  simp only [TrivSqZeroExt.snd_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    DualNumber.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inr,
    mul_zero, zero_add, add_zero] at h2
  exact (hu.mul_right_eq_zero).mp h2.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtTensorAlt
section
namespace GlobalTheory.TensorRingHomExtensionality

open scoped TensorProduct

theorem ringHom_ext_tensor {R S B C : Type} [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] (φ ψ : TensorProduct R S B →+* C)
    (h₁ : ∀ s : S, φ (s ⊗ₜ[R] (1 : B)) = ψ (s ⊗ₜ[R] (1 : B)))
    (h₂ : ∀ b : B, φ ((1 : S) ⊗ₜ[R] b) = ψ ((1 : S) ⊗ₜ[R] b)) : φ = ψ := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s b =>
    have h : s ⊗ₜ[R] b = (s ⊗ₜ[R] (1 : B)) * ((1 : S) ⊗ₜ[R] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h, map_mul, map_mul, h₁, h₂]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end GlobalTheory.TensorRingHomExtensionality
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtendOfIsIntegralIsAlgClosed
section
open Polynomial

namespace GlobalTheory

theorem ringHom_extend_of_isIntegral_isAlgClosed (A C K : Type) [CommRing A] [CommRing C]
    [Algebra A C] [Algebra.IsIntegral A C] [Field K] [IsAlgClosed K] (h : A →+* K)
    (hk : RingHom.ker (algebraMap A C) ≤ RingHom.ker h) :
    ∃ ψ : C →+* K, ψ.comp (algebraMap A C) = h := by
  classical
  haveI hp : (RingHom.ker h).IsPrime := RingHom.ker_isPrime h
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker h) (⊥ : Ideal C)
    (by simpa [← RingHom.ker_eq_comap_bot] using hk)
  haveI : Q.LiesOver (RingHom.ker h) := (Ideal.liesOver_iff _ _).mpr hQc.symm
  letI : Algebra (A ⧸ RingHom.ker h) K := (RingHom.kerLift h).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker h) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective h)
  haveI : FaithfulSMul (A ⧸ RingHom.ker h) (C ⧸ Q) := inferInstance
  haveI : Nontrivial (A ⧸ RingHom.ker h) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker h) (C ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver (A := A) (p := RingHom.ker h) (P := Q)
  haveI : Algebra.IsAlgebraic (A ⧸ RingHom.ker h) (C ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker h) (C ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker h) K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective h)
  let φ : (C ⧸ Q) →ₐ[A ⧸ RingHom.ker h] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  ext a
  have e1 : (Ideal.Quotient.mk Q) (algebraMap A C a) =
      algebraMap (A ⧸ RingHom.ker h) (C ⧸ Q) (Ideal.Quotient.mk _ a) := rfl
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [e1, φ.commutes]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIteratedFDerivTendstoZeroCocompact
section
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem schwartz_iteratedFDeriv_tendsto_zero_cocompact
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : SchwartzMap E F) (j : ℕ) :
    Tendsto (fun z => iteratedFDeriv ℝ j f z) (cocompact E) (𝓝 0) := by
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  obtain ⟨C, -, hC⟩ := f.decay 1 j
  have hn : Tendsto (fun z : E => ‖z‖) (cocompact E) atTop := by first | exact tendsto_norm_cocompact_atTop | exact tendsto_norm_cocompact_atTop _
  have h0 : Tendsto (fun z : E => C / ‖z‖) (cocompact E) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [hn.eventually_gt_atTop 0] with z hz
  rw [le_div_iff₀ hz, mul_comm]
  simpa using hC z

end GlobalTheory
end

