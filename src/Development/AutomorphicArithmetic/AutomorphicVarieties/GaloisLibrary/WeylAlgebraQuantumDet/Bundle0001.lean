module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.CoefDiff
section
open Matrix UpperTheory.V.Weyl

private theorem UpperTheory.V.Weyl.differentiable_eval_polynomial_entries (n : ℕ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → Fin n → ℂ => MvPolynomial.eval (fun ab => x ab.1 ab.2) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval_C]; fun_prop
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p ab hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (by fun_prop)

theorem UpperTheory.V.Weyl.coefDiff :
    ∀ (n : ℕ) (Ξ : Pre n) (i j : Fin Ξ.d), Differentiable ℂ (Ξ.coef i j) := by
  intro n Ξ i j
  obtain ⟨p, hp⟩ := Ξ.poly i j
  have h : Ξ.coef i j = fun x : Fin n → Fin n → ℂ => MvPolynomial.eval (fun ab => x ab.1 ab.2) p := by
    funext x
    exact hp (Matrix.of x)
  rw [h]
  exact UpperTheory.V.Weyl.differentiable_eval_polynomial_entries n p
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.DegRank
section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.degRank :
    ∀ (n N : ℕ), Module.finrank ℂ (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N) ≤ (N + 1) ^ (n * n) := by
  intro n N
  change Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
    {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N}) ≤ _
  rw [Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport ℂ _)]
  have key : ∀ m : {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N},
      ∀ i, (m : Fin n × Fin n →₀ ℕ) i < N + 1 := by
    intro m i
    have h1 := Finsupp.le_degree i (m : Fin n × Fin n →₀ ℕ)
    have h2 : Finsupp.degree (m : Fin n × Fin n →₀ ℕ)
        = (m : Fin n × Fin n →₀ ℕ).sum fun _ e => e := rfl
    have h3 := m.2
    simp only [Set.mem_setOf_eq] at h3
    omega
  calc Nat.card {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N}
      ≤ Nat.card (Fin n × Fin n → Fin (N + 1)) :=
        Nat.card_le_card_of_injective (fun m i => ⟨(m : Fin n × Fin n →₀ ℕ) i, key m i⟩)
          (by
            intro a b h
            apply Subtype.ext
            ext i
            have := congrArg Fin.val (congrFun h i)
            simpa using this)
    _ = (N + 1) ^ (n * n) := by
      simp [Nat.card_eq_fintype_card, Fintype.card_fun]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.InvCurve
section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.invCurve :
    ∀ (n : ℕ) (a b : Fin n), ∃ P Q : ℂ → Matrix (Fin n) (Fin n) ℂ, P 0 = 1 ∧ Q 0 = 1 ∧ (∀ t, Q t * P t = 1) ∧
      ∀ i j, HasDerivAt (fun t => P t i j) (Matrix.single a b (1 : ℂ) i j) 0 ∧ HasDerivAt (fun t => Q t i j) (-Matrix.single a b (1 : ℂ) i j) 0 := by
  intro n a b
  by_cases hab : a = b
  · subst hab
    set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a a 1 with hEdef
    have hE : E * E = E := by
      rw [hEdef, Matrix.single_mul_single_same, one_mul]
    refine ⟨fun t => 1 + (Complex.exp t - 1) • E, fun t => 1 + (Complex.exp (-t) - 1) • E,
      by simp, by simp, ?_, ?_⟩
    · intro t
      have key : (Complex.exp (-t) - 1) + ((Complex.exp t - 1)
          + (Complex.exp (-t) - 1) * (Complex.exp t - 1)) = 0 := by
        have h1 : Complex.exp (-t) * Complex.exp t = 1 := by
          rw [← Complex.exp_add]; simp
        linear_combination h1
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hE]
      rw [add_assoc, ← add_smul, ← add_smul, key, zero_smul, add_zero]
    · intro i j
      constructor
      · have h := (((Complex.hasDerivAt_exp 0).sub_const 1).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
      · have h0 : HasDerivAt (fun t : ℂ => Complex.exp (-t)) (-1) 0 := by
          simpa using (hasDerivAt_neg (0 : ℂ)).cexp
        have h := ((h0.sub_const 1).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
  · set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1 with hEdef
    have hE : E * E = 0 := by
      rw [hEdef]
      simp [Ne.symm hab]
    refine ⟨fun t => 1 + t • E, fun t => 1 - t • E, by simp, by simp, ?_, ?_⟩
    · intro t
      simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hE, smul_zero]
      abel
    · intro i j
      constructor
      · have h := ((hasDerivAt_id (0 : ℂ)).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h
      · have h := ((hasDerivAt_id (0 : ℂ)).mul_const (E i j)).const_sub ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
        simpa [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.MinorDeg
section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.minorDeg :
    ∀ (n : ℕ) (k : Fin n), minor k ≠ 0 ∧ (minor k).totalDegree ≤ (k : ℕ) + 1 := by
  intro n k
  constructor
  · intro h
    have h0 := congrArg
      (MvPolynomial.eval (fun ab : Fin n × Fin n => if ab.1 = ab.2 then (1 : ℂ) else 0)) h
    rw [minor, RingHom.map_det, map_zero] at h0
    rw [show (RingHom.mapMatrix _) _ = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) from ?_] at h0
    · simp at h0
    · ext i j
      simp [Matrix.one_apply, Fin.castLE_inj]
  · rw [minor, Matrix.det_apply]
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun σ _ => ?_)
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]
    refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    simp [MvPolynomial.totalDegree_X]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.MinorRtr
section
open Matrix UpperTheory.V.Weyl

private theorem prod_fin_castLE_eq_prod_le {M : Type*} [CommMonoid M] {n : ℕ} (k : Fin n) (f : Fin n → M) :
    ∏ l : Fin ((k : ℕ) + 1), f (Fin.castLE k.isLt l) = ∏ i : Fin n with i ≤ k, f i := by
  apply Finset.prod_bij (fun l _ => Fin.castLE k.isLt l)
  · intro l _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val, Fin.coe_castLE]
    omega
  · intro a _ b _ h
    exact Fin.castLE_injective _ h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val] at hi
    exact ⟨⟨i.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
  · intro _ _
    rfl

private theorem sum_fin_castLE_eq_sum_le {M : Type*} [AddCommMonoid M] {n : ℕ} (k : Fin n) (f : Fin n → M) :
    ∑ l : Fin ((k : ℕ) + 1), f (Fin.castLE k.isLt l) = ∑ i : Fin n with i ≤ k, f i := by
  apply Finset.sum_bij (fun l _ => Fin.castLE k.isLt l)
  · intro l _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val, Fin.coe_castLE]
    omega
  · intro a _ b _ h
    exact Fin.castLE_injective _ h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val] at hi
    exact ⟨⟨i.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
  · intro _ _
    rfl

theorem UpperTheory.V.Weyl.minorRtr :
    ∀ (n : ℕ) (k : Fin n) (b : Matrix (Fin n) (Fin n) ℂ), (∀ i j, j < i → b i j = 0) →
      rtr b (minor k) = (∏ i : Fin n with i ≤ k, b i i) • minor k := by
  intro n k b hb
  have hmat : (rtr b).mapMatrix (Matrix.of fun i j : Fin ((k : ℕ) + 1) =>
        (MvPolynomial.X (Fin.castLE k.isLt i, Fin.castLE k.isLt j) : Pol n)) =
      (Matrix.of fun i j : Fin ((k : ℕ) + 1) =>
        (MvPolynomial.X (Fin.castLE k.isLt i, Fin.castLE k.isLt j) : Pol n)) *
      (Matrix.of fun i j : Fin ((k : ℕ) + 1) => b (Fin.castLE k.isLt i) (Fin.castLE k.isLt j)).map
        (MvPolynomial.C : ℂ →+* Pol n) := by
    refine Matrix.ext fun i j => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, rtr,
      MvPolynomial.aeval_X]
    rw [sum_fin_castLE_eq_sum_le k (fun m => MvPolynomial.X (Fin.castLE k.isLt i, m) *
      MvPolynomial.C (b m (Fin.castLE k.isLt j)))]
    symm
    apply Finset.sum_filter_of_ne
    intro m _ hm
    by_contra hmk
    apply hm
    rw [hb m (Fin.castLE k.isLt j) ?_, map_zero, mul_zero]
    simp only [not_le] at hmk
    rw [Fin.lt_iff_val_lt_val] at hmk ⊢
    simp only [Fin.coe_castLE]
    omega
  have hup : (Matrix.of fun i j : Fin ((k : ℕ) + 1) =>
      b (Fin.castLE k.isLt i) (Fin.castLE k.isLt j)).det =
      ∏ i : Fin n with i ≤ k, b i i := by
    rw [Matrix.det_of_upperTriangular, ← prod_fin_castLE_eq_prod_le k (fun i => b i i)]
    · rfl
    · intro i j hij
      simp only [Matrix.of_apply]
      apply hb
      rw [Fin.lt_iff_val_lt_val] at hij ⊢
      simpa using hij
  have hC : ((Matrix.of fun i j : Fin ((k : ℕ) + 1) =>
      b (Fin.castLE k.isLt i) (Fin.castLE k.isLt j)).map (MvPolynomial.C : ℂ →+* Pol n)).det =
      MvPolynomial.C (∏ i : Fin n with i ≤ k, b i i) := by
    rw [← hup, RingHom.map_det]
    rfl
  unfold minor
  rw [AlgHom.map_det, hmat, Matrix.det_mul, hC, MvPolynomial.smul_eq_C_mul, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.QdetRect
section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.qdetRect :
    ∀ (n d d' : ℕ) (E : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (E' : Fin n → Fin n → Matrix (Fin d') (Fin d') ℂ)
      (A : Matrix (Fin d) (Fin d') ℂ), (∀ a b, E a b * A = A * E' a b) → ∀ u : ℂ, Formalism.REAL.qdet E u * A = A * Formalism.REAL.qdet E' u := by
  intro n d d' E E' A h u
  have hs : ∀ v : ℂ, (algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ) v) * A = A * algebraMap ℂ (Matrix (Fin d') (Fin d') ℂ) v := by
    intro v
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  have hT : ∀ (v : ℂ) a b, Formalism.REAL.Tm E v a b * A = A * Formalism.REAL.Tm E' v a b := by
    intro v a b
    simp only [Formalism.REAL.Tm]
    rw [Matrix.add_mul, Matrix.mul_add, h]
    split_ifs
    · rw [hs]
    · rw [Matrix.zero_mul, Matrix.mul_zero]
  have hL : ∀ (m : ℕ) (f : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → Matrix (Fin d') (Fin d') ℂ),
      (∀ k, f k * A = A * g k) → (List.ofFn f).prod * A = A * (List.ofFn g).prod := by
    intro m
    induction m with
    | zero => intro f g _; simp
    | succ m ih =>
      intro f g hfg
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Matrix.mul_assoc,
        ih _ _ (fun k => hfg k.succ), ← Matrix.mul_assoc, hfg 0, Matrix.mul_assoc]
  have hz : ∀ z : ℤ, (z : Matrix (Fin d) (Fin d) ℂ) * A = A * (z : Matrix (Fin d') (Fin d') ℂ) := by
    intro z
    rw [← map_intCast (algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ)), ← map_intCast (algebraMap ℂ (Matrix (Fin d') (Fin d') ℂ))]
    exact hs _
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor]
  rw [Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Matrix.mul_assoc, hL _ _ _ (fun k => hT _ _ _), ← Matrix.mul_assoc, hz, Matrix.mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.RtrDeg
section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.rtrDeg :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (f : Pol n), (rtr g f).totalDegree ≤ f.totalDegree := by
  intro n g f
  have hY : ∀ ij : Fin n × Fin n,
      (∑ k, MvPolynomial.X (ij.1, k) * MvPolynomial.C (g k ij.2) : MvPolynomial (Fin n × Fin n) ℂ).totalDegree ≤ 1 := by
    intro ij
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun k _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
  conv_lhs => rw [MvPolynomial.as_sum f]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rtr, map_sum, MvPolynomial.aeval_monomial]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc s i * _ ≤ s i * 1 := Nat.mul_le_mul_left _ (hY i)
    _ = s i := mul_one _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.RtrMul
section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.rtrMul :
    ∀ (n : ℕ), (∀ f : Pol n, rtr 1 f = f) ∧ ∀ (g h : Matrix (Fin n) (Fin n) ℂ) (f : Pol n), rtr (g * h) f = rtr g (rtr h f) := by
  intro n
  constructor
  · intro f
    have e : (rtr (1 : Matrix (Fin n) (Fin n) ℂ) : Pol n →ₐ[ℂ] Pol n) = AlgHom.id ℂ (Pol n) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      simp [rtr, Matrix.one_apply, mul_ite, Finset.sum_ite_eq']
    rw [e]
    rfl
  · intro g h f
    have e : (rtr (g * h) : Pol n →ₐ[ℂ] Pol n) = (rtr g).comp (rtr h) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      rw [AlgHom.comp_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [rtr, MvPolynomial.aeval_X, map_sum]
      have hx : ∀ x, (MvPolynomial.aeval (fun ij : Fin n × Fin n => ∑ k, MvPolynomial.X (ij.1, k) *
          MvPolynomial.C (g k ij.2)) : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ)
          (MvPolynomial.X (i, x) * MvPolynomial.C (h x j)) =
          ∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (g k x * h x j) := by
        intro x
        rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Finset.sum_mul]
        simp only [mul_assoc, ← map_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hx, Matrix.mul_apply, map_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [e]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.RtrPoly
section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.rtrPoly :
    ∀ (n : ℕ) (f : Pol n) (φ : Pol n →ₗ[ℂ] ℂ), ∃ p : Pol n, ∀ g : Matrix (Fin n) (Fin n) ℂ,
      φ (rtr g f) = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
  intro n f
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro φ
    refine ⟨MvPolynomial.C (φ (MvPolynomial.C a)), fun g => ?_⟩
    have hc := (rtr g).commutes a
    rw [MvPolynomial.algebraMap_eq] at hc
    rw [hc, MvPolynomial.eval_C]
  | add p q hp hq =>
    intro φ
    obtain ⟨p1, h1⟩ := hp φ
    obtain ⟨p2, h2⟩ := hq φ
    exact ⟨p1 + p2, fun g => by rw [map_add (f := _), map_add (f := _), h1, h2, map_add (f := _)]⟩
  | mul_X p ij hp =>
    intro φ
    choose P hP using fun k : Fin n =>
      hp (φ.comp (LinearMap.mulRight ℂ (MvPolynomial.X (ij.1, k) : Pol n)))
    refine ⟨∑ k, MvPolynomial.X (k, ij.2) * P k, fun g => ?_⟩
    have hX : rtr g (MvPolynomial.X ij : Pol n)
        = ∑ k, (MvPolynomial.X (ij.1, k) : Pol n) * MvPolynomial.C (g k ij.2) := by
      simp [rtr, MvPolynomial.aeval_X]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, hX, Finset.mul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := hP k g
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply] at hk
    rw [show rtr g p * ((MvPolynomial.X (ij.1, k) : Pol n) * MvPolynomial.C (g k ij.2))
        = MvPolynomial.C (g k ij.2) * (rtr g p * MvPolynomial.X (ij.1, k)) by ring,
      MvPolynomial.C_mul', map_smul, smul_eq_mul, hk, MvPolynomial.eval_mul,
      MvPolynomial.eval_X]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.SubMat
section
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.subMat :
    ∀ (G : Type) [Monoid G] (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ) (S : Submodule ℂ (Fin d → ℂ)),
      (∀ y, ∀ v ∈ S, ρ y *ᵥ v ∈ S) →
      ∃ (d' : ℕ) (A : Matrix (Fin d) (Fin d') ℂ) (B : Matrix (Fin d') (Fin d) ℂ) (ρ' : G →* Matrix (Fin d') (Fin d') ℂ),
        d' = Module.finrank ℂ S ∧ B * A = 1 ∧ (∀ w, A *ᵥ w ∈ S) ∧ (∀ y, ρ' y = B * ρ y * A) ∧ ∀ y, ρ y * A = A * ρ' y := by
  intro G _ d ρ S hS
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl S
  let b := Module.finBasis ℂ S
  let P : (Fin d → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    b.equivFun.toLinearMap ∘ₗ Submodule.linearProjOfIsCompl S T hT
  let I : (Fin (Module.finrank ℂ S) → ℂ) →ₗ[ℂ] (Fin d → ℂ) := S.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hIP : ∀ v, v ∈ S → I (P v) = v := by
    intro v hv
    have e : S.linearProjOfIsCompl T hT v = ⟨v, hv⟩ := Submodule.linearProjOfIsCompl_apply_left hT ⟨v, hv⟩
    show ((b.equivFun.symm (b.equivFun (S.linearProjOfIsCompl T hT v)) : S) : Fin d → ℂ) = v
    rw [e, LinearEquiv.symm_apply_apply]
  have hPI : P ∘ₗ I = LinearMap.id := by
    apply LinearMap.ext
    intro w
    have e : S.linearProjOfIsCompl T hT ((b.equivFun.symm w : S) : Fin d → ℂ) = b.equivFun.symm w :=
      Submodule.linearProjOfIsCompl_apply_left hT _
    show b.equivFun (S.linearProjOfIsCompl T hT ((b.equivFun.symm w : S) : Fin d → ℂ)) = w
    rw [e, LinearEquiv.apply_symm_apply]
  let A := LinearMap.toMatrix' I
  let B := LinearMap.toMatrix' P
  have hAw : ∀ w, A *ᵥ w = I w := fun w => LinearMap.toMatrix'_mulVec I w
  have hBw : ∀ v, B *ᵥ v = P v := fun v => LinearMap.toMatrix'_mulVec P v
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp, hPI, LinearMap.toMatrix'_id]
  have key : ∀ M : Matrix (Fin d) (Fin (Module.finrank ℂ S)) ℂ, (∀ w, M *ᵥ w ∈ S) → A * (B * M) = M := by
    intro M hM
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBw, hAw,
      hIP _ (hM w)]
  have hAS : ∀ w, A *ᵥ w ∈ S := by
    intro w
    rw [hAw]
    exact (b.equivFun.symm w).2
  have hcol : ∀ y w, (ρ y * A) *ᵥ w ∈ S := by
    intro y w
    rw [← Matrix.mulVec_mulVec]
    exact hS y _ (hAS w)
  let ρ' : G →* Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ :=
    { toFun := fun y => B * ρ y * A
      map_one' := by simp only [map_one, Matrix.mul_one, hBA]
      map_mul' := by
        intro x y
        simp only [map_mul, Matrix.mul_assoc]
        rw [key _ (hcol y)] }
  refine ⟨_, A, B, ρ', rfl, hBA, hAS, fun y => rfl, fun y => ?_⟩
  show ρ y * A = A * (B * ρ y * A)
  rw [Matrix.mul_assoc B, key _ (hcol y)]
end

