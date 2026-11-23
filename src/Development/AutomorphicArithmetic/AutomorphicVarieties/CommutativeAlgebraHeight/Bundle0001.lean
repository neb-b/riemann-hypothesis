module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GDetrad
section
open IsLocalRing

private theorem exists_col {K : Type} [Field K] {n : ℕ} (a : Fin (n+1) → K) (ha : a ≠ 0) :
    ∃ U : Matrix (Fin (n+1)) (Fin (n+1)) K, U.det ≠ 0 ∧ ∀ i, U i 0 = a i := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  refine ⟨((1 : Matrix (Fin (n+1)) (Fin (n+1)) K).updateCol i a).submatrix id (Equiv.swap 0 i), ?_, ?_⟩
  · rw [Matrix.det_permute', ← Matrix.cramer_apply, Matrix.cramer_one]
    refine mul_ne_zero ?_ (by simpa using hi)
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (n+1)) i)) with h | h <;> simp [h]
  · intro j
    simp

private def Emat (K : Type) [CommRing K] (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) K :=
  Matrix.diagonal (fun i => if i = 0 then 0 else 1)

private theorem exists_param {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (m : Fin (n+1) → K) (h1 : M.mulVec m = 0) (h2 : M.det = 0) :
    ∃ (N U : Matrix (Fin (n+1)) (Fin (n+1)) K) (t : K),
      N * Emat K n * U.adjugate = M ∧ ∀ i, t * U i 0 = m i := by
  have : ∃ (a : Fin (n+1) → K) (t : K), a ≠ 0 ∧ M.mulVec a = 0 ∧ ∀ i, t * a i = m i := by
    by_cases hm : m = 0
    · obtain ⟨a, ha, hMa⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h2
      exact ⟨a, 0, ha, hMa, by simp [hm]⟩
    · exact ⟨m, 1, hm, h1, by simp⟩
  obtain ⟨a, t, ha, hMa, hta⟩ := this
  obtain ⟨U, hU, hUa⟩ := exists_col a ha
  refine ⟨(U.det)⁻¹ • (M * U), U, t, ?_, fun i => by rw [hUa, hta]⟩
  have hE : M * U * Emat K n = M * U := by
    ext i j
    rw [Emat, Matrix.mul_diagonal]
    by_cases hj : j = 0
    · subst hj
      have := congrFun hMa i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      simp [Matrix.mul_apply, hUa, this]
    · simp [hj]
  rw [Matrix.smul_mul, hE, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul,
    Matrix.mul_one, smul_smul, inv_mul_cancel₀ hU, one_smul]

private theorem param_mulVec {B : Type} [CommRing B] {n : ℕ} (N U : Matrix (Fin (n+1)) (Fin (n+1)) B)
    (t : B) (a : Fin (n+1)) :
    ∑ b, (N * Emat B n * U.adjugate) a b * (t * U b 0) = 0 := by
  have h : (N * Emat B n * U.adjugate * U) a 0 = 0 := by
    rw [Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply,
      Emat, Matrix.mul_diagonal]
    simp
  rw [Matrix.mul_apply] at h
  calc _ = t * ∑ b, (N * Emat B n * U.adjugate) a b * U b 0 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by ring)
    _ = 0 := by rw [h, mul_zero]

private theorem param_det {B : Type} [CommRing B] {n : ℕ} (N U : Matrix (Fin (n+1)) (Fin (n+1)) B) :
    (N * Emat B n * U.adjugate).det = 0 := by
  have : (Emat B n).det = 0 := by
    rw [Emat, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ 0) (by simp)
  simp [Matrix.det_mul, this]

private abbrev Bv (n : ℕ) := Option ((Fin (n+1) × Fin (n+1)) ⊕ (Fin (n+1) × Fin (n+1)))

private noncomputable def phi (R : Type) [CommRing R] (n : ℕ) :
    MvPolynomial ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R →ₐ[R] MvPolynomial (Bv n) R :=
  MvPolynomial.aeval (Sum.elim
    (fun p => (((Matrix.of fun a b => (MvPolynomial.X (some (Sum.inl (a, b))) : MvPolynomial (Bv n) R))
      * Emat (MvPolynomial (Bv n) R) n * (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inr (a, b))) : MvPolynomial (Bv n) R)).adjugate : Matrix (Fin (n+1)) (Fin (n+1)) (MvPolynomial (Bv n) R))) p.1 p.2)
    (fun i => MvPolynomial.X none * MvPolynomial.X (some (Sum.inr (i, 0)))))

private theorem factor (R : Type) [CommRing R] (n : ℕ) {K : Type} [Field K] [Algebra R K]
    (ψ : MvPolynomial ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R →ₐ[R] K)
    (h1 : ∀ a, ψ (∑ b : Fin (n + 1), MvPolynomial.X (Sum.inl (a, b)) * MvPolynomial.X (Sum.inr b)) = 0)
    (h2 : ψ (Matrix.det (Matrix.of fun a b : Fin (n + 1) => MvPolynomial.X (Sum.inl (a, b)))) = 0)
    (f) (hf : phi R n f = 0) : ψ f = 0 := by
  obtain ⟨N, U, t, hM, hm⟩ := exists_param (Matrix.of fun a b => ψ (MvPolynomial.X (Sum.inl (a, b))))
    (fun b => ψ (MvPolynomial.X (Sum.inr b)))
    (by ext a; simpa [Matrix.mulVec, dotProduct] using h1 a)
    (by rw [AlgHom.map_det] at h2; exact h2)
  let χ : MvPolynomial (Bv n) R →ₐ[R] K := MvPolynomial.aeval
    (fun o => Option.elim o t (Sum.elim (fun p => N p.1 p.2) (fun p => U p.1 p.2)))
  have hc : χ.comp (phi R n) = ψ := by
    apply MvPolynomial.algHom_ext
    rintro (⟨a, b⟩ | i)
    · have e1 : χ.mapMatrix (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inl (a, b))) : MvPolynomial (Bv n) R)) = N := by
        ext a b; simp [χ]
      have e2 : χ.mapMatrix (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inr (a, b))) : MvPolynomial (Bv n) R)) = U := by
        ext a b; simp [χ]
      have e3 : χ.mapMatrix (Emat _ n) = Emat K n := by
        ext a b; simp [Emat, Matrix.diagonal_apply]; split_ifs <;> simp
      have e4 := congrFun (congrFun hM a) b
      rw [← e1, ← e2, ← e3, ← AlgHom.map_adjugate, ← map_mul, ← map_mul] at e4
      simpa [phi] using e4
    · simpa [phi, χ] using hm i
  rw [← hc, AlgHom.comp_apply, hf, map_zero]

private theorem phi_row (R : Type) [CommRing R] (n : ℕ) (a : Fin (n+1)) :
    phi R n (∑ b : Fin (n + 1), MvPolynomial.X (Sum.inl (a, b)) * MvPolynomial.X (Sum.inr b)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← param_mulVec (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inl (a, b))) : MvPolynomial (Bv n) R)) (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inr (a, b))) : MvPolynomial (Bv n) R)) (MvPolynomial.X none) a]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [map_mul, phi, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  rfl

private theorem phi_det (R : Type) [CommRing R] (n : ℕ) :
    phi R n (Matrix.det (Matrix.of fun a b : Fin (n + 1) => MvPolynomial.X (Sum.inl (a, b)))) = 0 := by
  rw [AlgHom.map_det, ← param_det (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inl (a, b))) : MvPolynomial (Bv n) R)) (Matrix.of fun a b => (MvPolynomial.X (some (Sum.inr (a, b))) : MvPolynomial (Bv n) R))]
  congr 1
  ext1 a b
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, phi, MvPolynomial.aeval_X]
  rfl

theorem UpperTheory.V.CA.g_detrad :
    (∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ),
      let A := MvPolynomial ((Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) R
      let I : Ideal A := Ideal.span (Set.range (fun a : Fin (n + 1) => ∑ b : Fin (n + 1), (MvPolynomial.X (Sum.inl (a, b)) * MvPolynomial.X (Sum.inr b) : A)) ∪ {Matrix.det (Matrix.of fun a b : Fin (n + 1) => (MvPolynomial.X (Sum.inl (a, b)) : A))})
      I.radical.IsPrime ∧ (MvPolynomial.X (Sum.inr 0) : A) ∉ I.radical ∧ (∀ r : R, MvPolynomial.C r ∈ I.radical → r = 0) ∧
        ∀ f ∈ I.radical, ∀ d : ℕ, MvPolynomial.homogeneousComponent d f ∈ I.radical) := by
  intro R _ _ n A I
  have hP : (RingHom.ker (phi R n)).IsPrime := RingHom.ker_isPrime _
  have hle : I ≤ RingHom.ker (phi R n) := by
    rw [Ideal.span_le]
    rintro x (⟨a, rfl⟩ | rfl)
    · exact phi_row R n a
    · exact phi_det R n
  have heq : I.radical = RingHom.ker (phi R n) := by
    apply le_antisymm (hP.radical_le_iff.mpr hle)
    rw [Ideal.radical_eq_sInf]
    apply le_sInf
    rintro q ⟨hIq, hq⟩ f hf
    let ψ : A →ₐ[R] FractionRing (A ⧸ q) :=
      (IsScalarTower.toAlgHom R (A ⧸ q) (FractionRing (A ⧸ q))).comp (Ideal.Quotient.mkₐ R q)
    have hψ : ∀ g, ψ g = 0 ↔ g ∈ q := by
      intro g
      simp [ψ, Ideal.Quotient.eq_zero_iff_mem]
    rw [← hψ]
    refine factor R n ψ (fun a => ?_) ?_ f hf
    · rw [hψ]; exact hIq (Ideal.subset_span (Or.inl ⟨a, rfl⟩))
    · rw [hψ]; exact hIq (Ideal.subset_span (Or.inr rfl))
  refine ⟨heq ▸ hP, ?_, ?_, ?_⟩
  · rw [heq, RingHom.mem_ker]
    simp [phi, MvPolynomial.X_ne_zero]
  · intro r hr
    rw [heq, RingHom.mem_ker] at hr
    simpa [phi] using hr
  · letI := MvPolynomial.gradedAlgebra (σ := (Fin (n + 1) × Fin (n + 1)) ⊕ Fin (n + 1)) (R := R)
    have hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ R) := by
      apply Ideal.homogeneous_span
      rintro x (⟨a, rfl⟩ | rfl)
      · refine ⟨1 + 1, ?_⟩
        rw [MvPolynomial.mem_homogeneousSubmodule]
        exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun b _ =>
          (MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _))
      · refine ⟨∑ _i : Fin (n+1), 1, ?_⟩
        rw [Matrix.det_apply]
        refine Submodule.sum_mem _ (fun σ _ => ?_)
        rw [Units.smul_def]
        refine zsmul_mem ?_ _
        rw [MvPolynomial.mem_homogeneousSubmodule]
        exact MvPolynomial.IsHomogeneous.prod _ _ (fun _ => 1) (fun b _ => MvPolynomial.isHomogeneous_X _ _)
    intro f hf d
    have := hI.radical d hf
    rw [← MvPolynomial.decomposition.decompose'_apply]
    exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GGram
section
open IsLocalRing

theorem UpperTheory.V.CA.g_gram :
    ∀ (K ι : Type) [Field K] [Fintype ι] [DecidableEq ι] (s : Set (Matrix ι ι K)),
      Submodule.span K s = ⊤ ↔ ∃ x : ι × ι → Matrix ι ι K, (∀ a, x a ∈ s) ∧
        Matrix.det (Matrix.of fun a b : ι × ι => (x a * x b).trace) ≠ 0 := by
  intro K ι _ _ _ s
  have hG : ∀ (x : ι × ι → Matrix ι ι K) (v : ι × ι → K) (a : ι × ι),
      (Matrix.of (fun a b : ι × ι => (x a * x b).trace)).mulVec v a
        = (x a * ∑ b, v b • x b).trace := by
    intro x v a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum, Matrix.trace_sum,
      Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  constructor
  · intro hs
    obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent K s
    have htop : ⊤ ≤ Submodule.span K (Set.range (Subtype.val : b → Matrix ι ι K)) := by
      rw [Subtype.range_coe, hspan, hs]
    let B := Module.Basis.mk hli htop
    let e := B.indexEquiv (Matrix.stdBasis K ι ι)
    let x : ι × ι → Matrix ι ι K := fun a => (e.symm a : Matrix ι ι K)
    have hxli : LinearIndependent K x := hli.comp e.symm e.symm.injective
    have hxspan : Submodule.span K (Set.range x) = ⊤ := by
      have hr : Set.range x = Set.range (Subtype.val : b → Matrix ι ι K) := by
        ext m
        constructor
        · rintro ⟨a, rfl⟩
          exact ⟨e.symm a, rfl⟩
        · rintro ⟨c, rfl⟩
          exact ⟨e c, by simp [x]⟩
      rw [hr, Subtype.range_coe, hspan, hs]
    refine ⟨x, fun a => hbs (e.symm a).2, ?_⟩
    intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hxy : ∀ a, (x a * ∑ b, v b • x b).trace = 0 := fun a => by
      rw [← hG x v a, hv]
      rfl
    have hall : ∀ z ∈ Submodule.span K (Set.range x), (z * ∑ b, v b • x b).trace = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨a, rfl⟩ := hz
        exact hxy a
      | zero => simp
      | add z w _ _ hz hw => rw [add_mul, Matrix.trace_add, hz, hw, add_zero]
      | smul c z _ hz => rw [Matrix.smul_mul, Matrix.trace_smul, hz, smul_zero]
    have hy0 : ∑ b, v b • x b = 0 := by
      ext i k
      have h := hall (Matrix.single k i 1) (by rw [hxspan]; exact Submodule.mem_top)
      rw [Matrix.trace_single_mul, one_smul] at h
      simpa using h
    apply hv0
    funext a
    exact Fintype.linearIndependent_iff.mp hxli v hy0 a
  · rintro ⟨x, hxs, hdet⟩
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact Subsingleton.elim _ _
    have hli : LinearIndependent K x := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have hm : (Matrix.of fun a b : ι × ι => (x a * x b).trace).mulVec g = 0 := by
        funext a
        rw [hG, hg, Matrix.mul_zero, Matrix.trace_zero]
        rfl
      exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hm) i
    have htop := hli.span_eq_top_of_card_eq_finrank (by
      rw [Module.finrank_matrix, Module.finrank_self, mul_one, Fintype.card_prod])
    rw [eq_top_iff, ← htop]
    exact Submodule.span_mono (Set.range_subset_iff.mpr hxs)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GHommem
section
open IsLocalRing

private theorem UpperTheory.V.CA.exists_part {R σ : Type} [CommRing R] [Finite σ]
    (F : MvPowerSeries σ R) (d : ℕ) :
    ∃ g : MvPolynomial σ R, ∀ m : σ →₀ ℕ,
      g.coeff m = if m.degree ≤ d then MvPowerSeries.coeff m F else 0 := by
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  set D : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => d) with hD
  refine ⟨∑ m ∈ Finset.Iic D, MvPolynomial.monomial m
    (if m.degree ≤ d then MvPowerSeries.coeff m F else 0), fun m => ?_⟩
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : m.degree ≤ d
  · have hm : m ∈ Finset.Iic D := by
      refine Finset.mem_Iic.mpr (Finsupp.le_def.mpr fun i => (Finsupp.le_degree i m).trans (h.trans ?_))
      simp [hD]
    rw [if_pos hm]
  · simp [h]

theorem UpperTheory.V.CA.g_hommem :
    ∀ (R σ : Type) [CommRing R] [IsNoetherianRing R] [Finite σ] (P : Ideal (MvPolynomial σ R)),
      (∀ f ∈ P, ∀ d : ℕ, MvPolynomial.homogeneousComponent d f ∈ P) → ∀ F : MvPowerSeries σ R,
        F ∈ P.map (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R)) ↔
          ∀ (d : ℕ) (g : MvPolynomial σ R),
            (∀ m : σ →₀ ℕ, g.coeff m = if m.degree = d then MvPowerSeries.coeff m F else 0) → g ∈ P := by
  intro R σ _ _ _ P hP F
  classical
  have hsumco : ∀ (f : MvPolynomial σ R) (d : ℕ) (m : σ →₀ ℕ),
      AddMonoidAlgebra.coeff (∑ k ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent k f) m =
        if m.degree ≤ d then AddMonoidAlgebra.coeff f m else 0 := by
    intro f d m
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_homogeneousComponent]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range, Nat.lt_succ_iff]
  have htr := UpperTheory.V.CA.exists_part (R := R) (σ := σ)
  have hpolyQ : ∀ f ∈ P, ∀ (d : ℕ) (g : MvPolynomial σ R),
      (∀ m : σ →₀ ℕ, g.coeff m = if m.degree ≤ d then AddMonoidAlgebra.coeff f m else 0) → g ∈ P := by
    intro f hf d g hg
    have hgeq : g = ∑ k ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent k f := by
      ext m
      rw [hg, hsumco]
    rw [hgeq]
    exact Ideal.sum_mem _ fun k _ => hP f hf k
  have hRQ : ∀ G : MvPowerSeries σ R,
      ((∀ (d : ℕ) (g : MvPolynomial σ R),
        (∀ m : σ →₀ ℕ, g.coeff m = if m.degree = d then MvPowerSeries.coeff m G else 0) → g ∈ P) ↔
      (∀ (d : ℕ) (g : MvPolynomial σ R),
        (∀ m : σ →₀ ℕ, g.coeff m = if m.degree ≤ d then MvPowerSeries.coeff m G else 0) → g ∈ P)) := by
    intro G
    constructor
    · intro h d g hg
      have hgeq : g = ∑ k ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent k g := by
        ext m
        rw [hsumco]
        by_cases hm : m.degree ≤ d
        · rw [if_pos hm]
        · rw [if_neg hm, hg, if_neg hm]
      rw [hgeq]
      refine Ideal.sum_mem _ fun k hk => h k _ fun m => ?_
      have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [MvPolynomial.coeff_homogeneousComponent, hg]
      split_ifs <;> first | rfl | (exfalso; omega)
    · intro h d g hg
      obtain ⟨T, hT⟩ := htr G d
      have hTP : T ∈ P := h d T hT
      have hgeq : g = MvPolynomial.homogeneousComponent d T := by
        ext m
        rw [hg, MvPolynomial.coeff_homogeneousComponent, hT]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [hgeq]
      exact hP T hTP d
  refine Iff.trans ?_ (hRQ F).symm
  constructor
  · intro hF
    have hF' : F ∈ Submodule.span (MvPowerSeries σ R)
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R) '' (P : Set (MvPolynomial σ R))) := hF
    refine Submodule.span_induction (p := fun x _ => ∀ (d : ℕ) (g : MvPolynomial σ R),
        (∀ m : σ →₀ ℕ, g.coeff m = if m.degree ≤ d then MvPowerSeries.coeff m x else 0) → g ∈ P)
      ?_ ?_ ?_ ?_ hF'
    · rintro x ⟨f, hf, rfl⟩ d g hg
      refine hpolyQ f hf d g fun m => ?_
      rw [hg, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe]
    · intro d g hg
      have hg0 : g = 0 := by
        ext m
        simp [hg]
      rw [hg0]
      exact P.zero_mem
    · intro x y _ _ hx hy d g hg
      obtain ⟨gx, hgx⟩ := htr x d
      obtain ⟨gy, hgy⟩ := htr y d
      have hgeq : g = gx + gy := by
        ext m
        rw [hg, MvPolynomial.coeff_add, hgx, hgy, map_add (f := _)]
        split_ifs <;> simp
      rw [hgeq]
      exact P.add_mem (hx d gx hgx) (hy d gy hgy)
    · intro a x _ hx d g hg
      obtain ⟨Ta, hTa⟩ := htr a d
      obtain ⟨Tx, hTx⟩ := htr x d
      have hTxP := hx d Tx hTx
      have hgeq : g = ∑ k ∈ Finset.range (d + 1), MvPolynomial.homogeneousComponent k (Ta * Tx) := by
        ext m
        rw [hsumco, hg, smul_eq_mul]
        by_cases hm : m.degree ≤ d
        · rw [if_pos hm, if_pos hm, MvPowerSeries.coeff_mul, MvPolynomial.coeff_mul]
          refine Finset.sum_congr rfl fun p hp => ?_
          have hpm : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
          have hdeg : p.1.degree + p.2.degree = m.degree := by rw [← map_add (f := _), hpm]
          rw [hTa, hTx, if_pos (by omega), if_pos (by omega)]
        · rw [if_neg hm, if_neg hm]
      rw [hgeq]
      exact Ideal.sum_mem _ fun k _ => hP _ (P.mul_mem_left Ta hTxP) k
  · intro hQ
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian P : P.FG)
    set D := s.sup MvPolynomial.totalDegree with hD
    let h : ↥s × Fin (D + 1) → MvPolynomial σ R := fun i =>
      MvPolynomial.homogeneousComponent i.2.val i.1.val
    have hhP : ∀ i, h i ∈ P := by
      intro i
      have hi : (i.1 : MvPolynomial σ R) ∈ P := by
        rw [← hs]
        exact Submodule.subset_span i.1.2
      exact hP _ hi _
    have hPspan : P ≤ Ideal.span (Set.range h) := by
      rw [← hs, Submodule.span_le]
      intro f hf
      have hf' : f ∈ s := Finset.mem_coe.mp hf
      have hfsum : f = ∑ k ∈ Finset.range (D + 1), MvPolynomial.homogeneousComponent k f := by
        rw [← Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ (Finset.le_sup (f := MvPolynomial.totalDegree) hf'))) ?_,
          MvPolynomial.sum_homogeneousComponent]
        intro k _ hk
        simp only [Finset.mem_range] at hk
        exact MvPolynomial.homogeneousComponent_eq_zero k f (by omega)
      rw [SetLike.mem_coe, hfsum]
      exact Ideal.sum_mem _ fun k hk =>
        Ideal.subset_span ⟨(⟨f, hf'⟩, ⟨k, Finset.mem_range.mp hk⟩), rfl⟩
    have hcomp : ∀ d : ℕ, ∃ c : ↥s × Fin (D + 1) → MvPolynomial σ R,
        ∑ i, c i • h i = MvPolynomial.homogeneousComponent d (Classical.choose (htr F d)) := by
      intro d
      have hmem : MvPolynomial.homogeneousComponent d (Classical.choose (htr F d)) ∈ P :=
        hP _ (hQ d _ (Classical.choose_spec (htr F d))) d
      exact (Submodule.mem_span_range_iff_exists_fun _).mp (hPspan hmem)
    choose c hc using hcomp
    have hcoefF : ∀ m : σ →₀ ℕ,
        AddMonoidAlgebra.coeff (∑ i, c m.degree i • h i) m = MvPowerSeries.coeff m F := by
      intro m
      rw [hc, MvPolynomial.coeff_homogeneousComponent, if_pos rfl,
        Classical.choose_spec (htr F m.degree) m, if_pos le_rfl]
    let C : ↥s × Fin (D + 1) → MvPowerSeries σ R := fun i p =>
      AddMonoidAlgebra.coeff (c (p.degree + i.2.val) i) p
    have hFeq : F = ∑ i, C i * MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R) (h i) := by
      ext m
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hcoefF m, map_sum, MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MvPowerSeries.coeff_mul, smul_eq_mul, MvPolynomial.coeff_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe]
      have hpm : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have hdeg : p.1.degree + p.2.degree = m.degree := by rw [← map_add (f := _), hpm]
      show AddMonoidAlgebra.coeff (c m.degree i) p.1 * AddMonoidAlgebra.coeff (h i) p.2 =
        AddMonoidAlgebra.coeff (c (p.1.degree + i.2.val) i) p.1 * AddMonoidAlgebra.coeff (h i) p.2
      by_cases h2 : p.2.degree = i.2.val
      · rw [← h2, hdeg]
      · have h0 : AddMonoidAlgebra.coeff (h i) p.2 = 0 := by
          show AddMonoidAlgebra.coeff (MvPolynomial.homogeneousComponent i.2.val i.1.val) p.2 = 0
          rw [MvPolynomial.coeff_homogeneousComponent, if_neg h2]
        rw [h0, mul_zero, mul_zero]
    rw [hFeq]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hhP i))
end

