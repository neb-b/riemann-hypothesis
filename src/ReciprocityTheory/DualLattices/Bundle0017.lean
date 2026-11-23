module

public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0013
public import ReciprocityTheory.DualLattices.Bundle0016
public import ReciprocityTheory.DualLattices.Bundle0004
public import ReciprocityTheory.DualLattices.Bundle0015

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.EigenLengthFrobeniusStatement
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Defs

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

def bt2 (H : HodgeTateDatum p g v R O σ cp) (U : UnramData p g v R O σ cp H) : Matrix (Fin g) (Ix g) R :=
  ∑ i, U.εL i * H.Bt * U.εT i

end Defs

def EigenLengthProductStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (g m : ℕ) (Ht Bt : Matrix (Fin g) (Ix g) R)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)), (∀ i, π (π i) = i) →
    (∀ i j, εT i * εT j = if i = j then εT i else 0) → ∑ i, εT i = 1 →
    (∀ i j, εL i * εL j = if i = j then εL i else 0) → ∑ i, εL i = 1 →
    (∀ i, Ht * εT i = (εL (π i))ᵀ * Ht) → (∀ i, Bt * εT i = εL i * Bt) →
    ∀ X : Fin m → NNReal, (∀ i, HasLen v R (xModE Ht Bt εT εL π i) (X i)) →
      ∏ i, X i = v (algebraMap R C (fromRows Ht Bt).det)

def EigenLengthFrobeniusStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal),
    (∀ i, HasLen v R (xModE H.Ht (bt2 H U) U.εT U.εL U.cj i) (X i)) →
    ∏ i, X i = v (algebraMap R C cp) ^ g →
    ∀ i, X i ^ p ≤ X (U.φ i) * v (algebraMap R C (p : R)) ^ U.r (U.φ i)

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.ExistsUnitMinor
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {v : Valuation C NNReal}

theorem freePts_integral {n h : ℕ} {a : Fin n → C} (ha : ∀ τ, v (a τ) ≤ 1)
    (F : Lat v (Fin n × Fin h)) (hF : F.B = freeMat a h) {w : Fin n × Fin h → C} (hw : w ∈ F.pts)
    (y : Fin n × Fin h) : v (w y) ≤ 1 := by
  obtain ⟨c, hc, rfl⟩ := hw
  rw [hF]
  simp only [Matrix.mulVec, dotProduct]
  refine v.map_sum_le fun x _ => ?_
  rw [map_mul]
  refine mul_le_one₀ ?_ (zero_le) (hc x)
  simp only [freeMat, Matrix.of_apply]
  split_ifs
  · rw [map_pow]
    exact pow_le_one₀ (zero_le) (ha _)
  · simp

def fder {n : ℕ} (a : Fin n → C) (τ : Fin n) : C := ∏ τ' ∈ Finset.univ.erase τ, (a τ - a τ')

theorem prod_fder {n : ℕ} (a : Fin n → C) : ∏ τ, fder a τ = discr a := rfl

private lemma valuation_coeff_prod_X_sub_C_le_one {n : ℕ} {a : Fin n → C} (ha : ∀ τ, v (a τ) ≤ 1)
    (s : Finset (Fin n)) (k : ℕ) :
    v ((∏ τ' ∈ s, (Polynomial.X - Polynomial.C (a τ'))).coeff k) ≤ 1 := by
  have h : (∏ τ' ∈ s, (Polynomial.X - Polynomial.C (a τ'))) =
      (∏ τ' ∈ s, (Polynomial.X - Polynomial.C (⟨a τ', ha τ'⟩ : v.integer))).map v.integer.subtype := by
    simp [Polynomial.map_prod]
  rw [h, Polynomial.coeff_map]
  exact (Valuation.mem_integer_iff _ _).1 (Subtype.prop _)

theorem conductor_mem {n h : ℕ} {a : Fin n → C} (ha : ∀ τ, v (a τ) ≤ 1)
    (F : Lat v (Fin n × Fin h)) (hF : F.B = freeMat a h) (τ : Fin n) (u : Fin h → C)
    (hu : ∀ l, v (u l) ≤ 1) :
    (fun y : Fin n × Fin h => if y.1 = τ then fder a τ * u y.2 else 0) ∈ F.pts := by
  classical
  have hdeg : (∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).natDegree < n := by
    rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    exact Nat.sub_lt (Fin.pos τ) one_pos
  have heval : ∀ τ', (∏ τ'' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ''))).eval (a τ') =
      if τ' = τ then fder a τ else 0 := by
    intro τ'
    rw [Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    split_ifs with h
    · subst h
      rfl
    · exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩) (sub_self _)
  refine ⟨fun x => (∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).coeff x.1 * u x.2,
    fun x => ?_, ?_⟩
  · rw [map_mul]
    exact mul_le_one₀ (valuation_coeff_prod_X_sub_C_le_one ha _ _) (zero_le) (hu _)
  · rw [hF]
    funext y
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, freeMat, Matrix.of_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hsum : ∑ k : Fin n, a y.1 ^ (k : ℕ) *
        ((∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).coeff k * u y.2) =
        (∏ τ' ∈ Finset.univ.erase τ, (Polynomial.X - Polynomial.C (a τ'))).eval (a y.1) * u y.2 := by
      rw [Polynomial.eval_eq_sum_range' hdeg, Finset.sum_mul,
        ← Fin.sum_univ_eq_sum_range (fun i => _ * a y.1 ^ i * u y.2)]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsum, heval]
    split_ifs <;> simp

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.FischerSelfNeZero
section
noncomputable section

open MvPolynomial Matrix Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

theorem fischer_self_ne_zero (P : MvPolynomial (Fin ν × ι) ℂ) (hP : P ≠ 0) : fischer P P ≠ 0 := by
  intro h0
  have hsum : fischer P P = ((∑ A ∈ P.support,
      ‖AddMonoidAlgebra.coeff P A‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
    unfold fischer
    rw [Finset.union_self]
    push_cast
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [Finsupp.prod]
    push_cast
    ring
  have hne : P.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun h => hP (MvPolynomial.support_eq_empty.mp h))
  have hpos : 0 < ∑ A ∈ P.support, ‖AddMonoidAlgebra.coeff P A‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ) := by
    refine Finset.sum_pos (fun A hA => ?_) hne
    have h1 : AddMonoidAlgebra.coeff P A ≠ 0 := MvPolynomial.mem_support_iff.mp hA
    have h2 : 0 < ((A.prod fun _ e => e.factorial : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos fun _ _ => Nat.factorial_pos _
    have h3 : 0 < ‖AddMonoidAlgebra.coeff P A‖ ^ 2 := by positivity
    positivity
  rw [hsum] at h0
  have h4 : (∑ A ∈ P.support, ‖AddMonoidAlgebra.coeff P A‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ) : ℝ) = 0 := by
    exact_mod_cast h0
  linarith

theorem rowSubst_mul (g h : Matrix (Fin ν) (Fin ν) ℂ) (P : MvPolynomial (Fin ν × ι) ℂ) :
    rowSubst h (rowSubst g P) = rowSubst (h * g) P := by
  have key : (rowSubst (ι := ι) h).comp (rowSubst g) = rowSubst (h * g) := by
    apply MvPolynomial.algHom_ext
    intro p
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, rowSubst, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, MvPolynomial.C_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  exact congrArg (fun F => F P) key

theorem rowSubst_one (P : MvPolynomial (Fin ν × ι) ℂ) : rowSubst (1 : Matrix (Fin ν) (Fin ν) ℂ) P = P := by
  have h : (fun p : Fin ν × ι => ∑ l, C ((1 : Matrix (Fin ν) (Fin ν) ℂ) l p.1) * X (l, p.2)) = X := by
    funext p
    rw [Finset.sum_eq_single p.1]
    · simp
    · intro l _ hl
      simp [Matrix.one_apply_ne hl]
    · simp
  unfold rowSubst
  rw [h, MvPolynomial.aeval_X_left_apply]

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.ImportsAlt
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.L2

theorem h1 (C R : Type) [Field C] [CommRing R] [Algebra R C] :
    DualHopfOrderStatement (C := C) (R := R) := by
  intro v hv N H _ _ _ _ _ _ e he hcard AA
  obtain ⟨B, hB, hAA⟩ := AA.lat
  have σ : H ≃ N := Fintype.equivOfCardEq hcard
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix H H C,
      M = ((tableM e σ)ᵀ * (B⁻¹)ᵀ).submatrix σ σ := ⟨_, rfl⟩
  have hdual : dualLat AA.carrier = Submodule.span R (Set.range fun j x => (B⁻¹)ᵀ x j) := by
    rw [hAA]; exact dualLat_spanCols B hB
  have hmap : (dualLat AA.carrier).map (fourier (R := R) fun h a => e h a) =
      Submodule.span R (Set.range fun k h => M h k) := by
    rw [hdual, hMdef]; exact map_fourier_spanCols e σ _
  have hBB : B.det * B⁻¹.det = 1 := by
    rw [← Matrix.det_mul, Matrix.mul_nonsing_inv B hB, Matrix.det_one]
  have hBinv : IsUnit B⁻¹.det := ⟨⟨B⁻¹.det, B.det, by rw [mul_comm]; exact hBB, hBB⟩, rfl⟩
  have hdetM : M.det = (tableM e σ).det * B⁻¹.det := by
    rw [hMdef, Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_transpose]
  have hMunit : IsUnit M.det := by
    rw [hdetM]; exact (tableM_isUnit e σ).mul hBinv
  have hdd : dualLat (dualLat AA.carrier) = AA.carrier := by
    rw [hAA]; exact dualLat_dualLat_spanCols B hB
  refine ⟨{ carrier := (dualLat AA.carrier).map (fourier (R := R) fun h a => e h a)
            lat := ⟨M, hMunit, hmap⟩
            le_int := by
              rintro w ⟨u, hu, rfl⟩ h
              exact hv.exists_of_le_one (valuation_fourier_le_one v hv (fun h => e h) AA hu h)
            one_mem := Submodule.mem_map.mpr ⟨(Pi.single 0 1 : N → C),
              single_mem_dualLat AA,
              funext fun h => fourier_single (R := R) (fun h => e h) h⟩
            mul_mem := by
              rintro f g ⟨u, hu, rfl⟩ ⟨w, hw, rfl⟩
              exact Submodule.mem_map.mpr ⟨conv u w,
                conv_mem_dualLat AA hu hw,
                funext fun h => fourier_conv (R := R) (fun h => e h) u w h⟩
            comul := by
              rintro f ⟨u, hu, rfl⟩
              exact comul_fourier e he AA B hB hAA u hu
            antipode := by
              rintro f ⟨u, hu, rfl⟩
              exact antipode_fourier e he AA u hu }, rfl, ?_, ?_⟩
  · ext f
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h1 := (mem_dualLat_map_fourier e (dualLat AA.carrier) w).mp hw
      rwa [hdd] at h1
    · intro hf
      obtain ⟨w, hw⟩ := fourier'_surjective (R := R) e σ f
      refine ⟨w, (mem_dualLat_map_fourier e (dualLat AA.carrier) w).mpr ?_, hw⟩
      rw [hw, hdd]; exact hf
  · intro c c' hc hc'
    obtain ⟨B₀, hB₀, rfl⟩ := hc
    obtain ⟨B₁, hB₁, rfl⟩ := hc'
    have e0 : v B₀.det = v B.det :=
      valuation_det_eq_of_span_eq v hv B₀ B (hB₀.symm.trans hAA)
    have e1 : v B₁.det = v M.det :=
      valuation_det_eq_of_span_eq v hv B₁ M (hB₁.symm.trans hmap)
    have key : v B.det * v M.det = v (tableM e σ).det := by
      rw [← map_mul, hdetM, mul_left_comm, hBB, mul_one]
    have h2 : (tableM e σ).det ^ 2 = (Fintype.card N : C) ^ Fintype.card N ∨
        (tableM e σ).det ^ 2 = -(Fintype.card N : C) ^ Fintype.card N :=
      ReciprocityTheory.PGsh.charTable C N (σ.symm.trans e)
    rw [e0, e1, key]
    calc v (tableM e σ).det ^ 2 = v ((tableM e σ).det ^ 2) :=
          (map_pow v _ 2).symm
      _ = v (Fintype.card N : C) ^ Fintype.card N := by
        rcases h2 with h | h <;> rw [h] <;> simp [Valuation.map_neg, map_pow]

end ReciprocityTheory.PGsh.L2
end
end

-- bundled from ReciprocityTheory.DualLattices.MemOfSumSingleEqZero
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

section

variable {R : Type} [CommRing R]

lemma single_smul_self {m : ℕ} (c : Fin m → R) (i : Fin m) :
    c i • (Pi.single i (1 : R ⧸ Ideal.span {c i}) : (i : Fin m) → R ⧸ Ideal.span {c i}) = 0 := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
  · simp [Pi.single_eq_of_ne hk]

lemma eq_sum_single {m : ℕ} (c : Fin m → R) (x : (i : Fin m) → R ⧸ Ideal.span {c i}) :
    x = ∑ i, (Quotient.out (x i) : R) • (Pi.single i (1 : R ⧸ Ideal.span {c i}) :
      (i : Fin m) → R ⧸ Ideal.span {c i}) := by
  funext k
  rw [Finset.sum_apply, Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_eq_of_ne' hj]) (by simp)]
  simp [Algebra.smul_def]

end

theorem hasLen_ext {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C]
    (hS2 : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R),
      HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)))
    {A B D : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup D]
    [Module R D] (ι : A →ₗ[R] B) (π : B →ₗ[R] D) (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (hex : LinearMap.range ι = LinearMap.ker π) {a c : NNReal}
    (ha : HasLen v R A a) (hc : HasLen v R D c) : HasLen v R B (a * c) := by
  classical
  obtain ⟨m, α, ⟨eA⟩, hαa⟩ := ha
  obtain ⟨m', δ, ⟨eD⟩, hδc⟩ := hc
  set gA : Fin m → A := fun i => eA.symm (Pi.single i 1) with hgA
  set gD : Fin m' → D := fun j => eD.symm (Pi.single j 1) with hgD
  have hgA0 : ∀ i, α i • gA i = 0 := fun i => by
    simp only [hgA]
    rw [← map_smul, single_smul_self, map_zero]
  have hgD0 : ∀ j, δ j • gD j = 0 := fun j => by
    simp only [hgD]
    rw [← map_smul, single_smul_self, map_zero]
  have reprA : ∀ y : A, y = ∑ i, (Quotient.out (eA y i) : R) • gA i := fun y => by
    conv_lhs => rw [← eA.symm_apply_apply y, eq_sum_single α (eA y)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hgA, map_sum, map_smul]
  have reprD : ∀ y : D, y = ∑ j, (Quotient.out (eD y j) : R) • gD j := fun y => by
    conv_lhs => rw [← eD.symm_apply_apply y, eq_sum_single δ (eD y)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hgD, map_sum, map_smul]
  have memA : ∀ r : Fin m → R, ∑ i, r i • gA i = 0 → ∀ i, r i ∈ Ideal.span {α i} := by
    intro r hr i
    have h1 : eA (∑ i, r i • gA i) = 0 := by rw [hr, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hgA, map_sum, map_smul, LinearEquiv.apply_symm_apply] at h1
    have h3 := congrFun h1 i
    rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne' hj]) (by simp)] at h3
    simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] using h3
  have memD : ∀ r : Fin m' → R, ∑ j, r j • gD j = 0 → ∀ j, r j ∈ Ideal.span {δ j} := by
    intro r hr i
    have h1 : eD (∑ j, r j • gD j) = 0 := by rw [hr, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hgD, map_sum, map_smul, LinearEquiv.apply_symm_apply] at h1
    have h3 := congrFun h1 i
    rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne' hj]) (by simp)] at h3
    simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] using h3
  have hπι : ∀ y : A, π (ι y) = 0 := fun y => by
    have h1 : ι y ∈ LinearMap.range ι := ⟨y, rfl⟩
    rw [hex] at h1
    exact h1
  choose b hb using fun j => hπ (gD j)
  have hdb : ∀ j, ∃ y : A, ι y = δ j • b j := fun j => by
    have h1 : δ j • b j ∈ LinearMap.ker π := by rw [LinearMap.mem_ker, map_smul, hb, hgD0]
    rw [← hex] at h1
    exact h1
  choose aj haj using hdb
  set x : Fin m' → Fin m → R := fun j i => (Quotient.out (eA (aj j) i) : R) with hxdef
  have hx : ∀ j, aj j = ∑ i, x j i • gA i := fun j => reprA (aj j)
  set gen : Fin m ⊕ Fin m' → B := Sum.elim (fun i => ι (gA i)) b with hgen
  let Φ : (Fin m ⊕ Fin m' → R) →ₗ[R] B :=
    { toFun := fun p => ∑ k, p k • gen k
      map_add' := fun p q => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c p => by simp [Finset.smul_sum, smul_smul] }
  have hΦ : ∀ p, Φ p = ∑ i, p (Sum.inl i) • ι (gA i) + ∑ j, p (Sum.inr j) • b j := fun p => by
    show ∑ k, p k • gen k = _
    rw [Fintype.sum_sum_type]
    rfl
  let X : Matrix (Fin m ⊕ Fin m') (Fin m ⊕ Fin m') R :=
    Matrix.fromBlocks (Matrix.diagonal α) (Matrix.of fun i j => -x j i) 0 (Matrix.diagonal δ)
  have hdet : X.det = (∏ i, α i) * ∏ j, δ j := by
    simp [X, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal]
  have hXl : ∀ w i, X.mulVec w (Sum.inl i) = α i * w (Sum.inl i) - ∑ j, x j i * w (Sum.inr j) := by
    intro w i
    simp [X, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.diagonal_apply, Finset.sum_neg_distrib,
      sub_eq_add_neg]
  have hXr : ∀ w j, X.mulVec w (Sum.inr j) = δ j * w (Sum.inr j) := by
    intro w j
    simp [X, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.diagonal_apply]
  have hιx : ∀ j, ι (aj j) = ∑ i, x j i • ι (gA i) := fun j => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx j, map_sum]
    simp only [map_smul]
  have hΦX : ∀ w, Φ (X.mulVec w) = 0 := by
    intro w
    rw [hΦ]
    simp only [hXl, hXr, sub_smul, Finset.sum_sub_distrib]
    have e1 : ∀ i, (α i * w (Sum.inl i)) • ι (gA i) = 0 := by
      intro i
      rw [mul_comm, mul_smul, ← map_smul, hgA0, map_zero, smul_zero]
    have e2 : ∀ j, (δ j * w (Sum.inr j)) • b j = w (Sum.inr j) • ι (aj j) := by
      intro j
      rw [mul_comm, mul_smul, haj]
    have e3 : ∑ i, (∑ j, x j i * w (Sum.inr j)) • ι (gA i) = ∑ j, w (Sum.inr j) • ι (aj j) := by
      simp only [hιx, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
    simp only [e1, e2, Finset.sum_const_zero, zero_sub, e3, neg_add_cancel]
  have hker : LinearMap.ker Φ = LinearMap.range X.mulVecLin := by
    ext p
    constructor
    · intro hp
      rw [LinearMap.mem_ker, hΦ] at hp
      have hπs : ∑ j, p (Sum.inr j) • gD j = 0 := by
        have h1 := congrArg π hp
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [map_add (f := _), map_sum, map_smul, hb, hπι] using h1
      choose t ht using fun j => Ideal.mem_span_singleton'.1 (memD _ hπs j)
      have hsb : ∑ j, p (Sum.inr j) • b j = ι (∑ i, (∑ j, t j * x j i) • gA i) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [map_smul]
        have e4 : ∀ j, p (Sum.inr j) • b j = t j • ι (aj j) := by
          intro j
          rw [← ht j, mul_smul, haj]
        simp only [e4, hιx, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
      have hι0 : ι (∑ i, (p (Sum.inl i) + ∑ j, t j * x j i) • gA i) = 0 := by
        rw [← hp, hsb]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [add_smul, Finset.sum_add_distrib, map_add (f := _), map_sum, map_smul]
      have hA0 : ∑ i, (p (Sum.inl i) + ∑ j, t j * x j i) • gA i = 0 :=
        hι (hι0.trans (map_zero ι).symm)
      choose q hq using fun i => Ideal.mem_span_singleton'.1 (memA _ hA0 i)
      refine ⟨Sum.elim q t, ?_⟩
      funext k
      cases k with
      | inl i =>
        show X.mulVec (Sum.elim q t) (Sum.inl i) = p (Sum.inl i)
        rw [hXl]
        simp only [Sum.elim_inl, Sum.elim_inr]
        have hqi := hq i
        rw [show ∑ j, x j i * t j = ∑ j, t j * x j i from Finset.sum_congr rfl fun j _ => mul_comm _ _]
        linear_combination hqi
      | inr j =>
        show X.mulVec (Sum.elim q t) (Sum.inr j) = p (Sum.inr j)
        rw [hXr]
        simp only [Sum.elim_inr]
        rw [mul_comm]
        exact ht j
    · rintro ⟨w, rfl⟩
      exact hΦX w
  have hsurj : Function.Surjective Φ := by
    intro y
    set s : Fin m' → R := fun j => (Quotient.out (eD (π y) j) : R) with hs
    have hys : y - ∑ j, s j • b j ∈ LinearMap.range ι := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hex, LinearMap.mem_ker, map_sub, map_sum]
      simp only [map_smul, hb]
      rw [← reprD (π y), sub_self]
    obtain ⟨zA, hzA⟩ := hys
    refine ⟨Sum.elim (fun i => (Quotient.out (eA zA i) : R)) s, ?_⟩
    rw [hΦ]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have e5 : ∑ i, (Quotient.out (eA zA i) : R) • ι (gA i) = ι zA := by
      conv_rhs => rw [reprA zA]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_smul]
    rw [e5, hzA, sub_add_cancel]
  let e1 : ((Fin m ⊕ Fin m' → R) ⧸ LinearMap.range X.mulVecLin) ≃ₗ[R] B :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hsurj)
  obtain ⟨k, cc, ⟨e2⟩, hcc⟩ := hS2 (Fin m ⊕ Fin m') X
  refine ⟨k, cc, ⟨e1.symm.trans e2⟩, ?_⟩
  rw [hcc, hdet, map_mul, map_mul, map_prod, map_prod, map_prod, map_prod, hαa, hδc]

end ReciprocityTheory.PGsh.Up
end
end

