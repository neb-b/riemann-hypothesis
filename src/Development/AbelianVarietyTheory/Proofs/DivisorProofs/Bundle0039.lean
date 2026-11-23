module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumDen
section
open IsLocalRing

namespace GlobalTheory
namespace SpreadOut

lemma exists_num_den {T : Type} [CommRing T] (p : Ideal T) [p.IsPrime]
    (y : Localization.AtPrime p) :
    ∃ a s : T, s ∉ p ∧ algebraMap T _ s * y = algebraMap T _ a := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl y
  exact ⟨a, s, s.2, IsLocalization.mk'_spec' _ a s⟩

lemma prod_not_mem {T : Type} [CommRing T] {ι : Type} (p : Ideal T) [p.IsPrime]
    (S : Finset ι) (g : ι → T) (h : ∀ i ∈ S, g i ∉ p) : ∏ i ∈ S, g i ∉ p :=
  Submonoid.prod_mem p.primeCompl (fun i hi => h i hi)

lemma exists_kill {T : Type} [CommRing T] (p : Ideal T) [p.IsPrime] (f₀ : T)
    (z : Localization.Away f₀)
    (ι₀ : Localization.Away f₀ →ₐ[T] Localization.AtPrime p) (hz : ι₀ z = 0) :
    ∃ t : T, t ∉ p ∧ ∀ (B : Type) [CommRing B] [Algebra T B]
      (κ : Localization.Away f₀ →ₐ[T] B), IsUnit (algebraMap T B t) → κ z = 0 := by
  obtain ⟨⟨b, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f₀) z
  have hspec := IsLocalization.mk'_spec' (Localization.Away f₀) b m
  have h1 : algebraMap T (Localization.AtPrime p) b = 0 := by
    have := congrArg ι₀ hspec
    rw [map_mul, AlgHom.commutes, AlgHom.commutes, hz, mul_zero] at this
    exact this.symm
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ b).1 h1
  refine ⟨t, t.2, fun B _ _ κ hu => ?_⟩
  have h2 := congrArg κ hspec
  rw [map_mul, AlgHom.commutes, AlgHom.commutes] at h2
  have hb : algebraMap T B b = 0 := by
    apply hu.mul_left_cancel
    rw [← map_mul, ht, map_zero, mul_zero]
  have hm : IsUnit (algebraMap T B m) := by
    rw [← AlgHom.commutes κ]
    exact (IsLocalization.map_units (Localization.Away f₀) m).map κ
  rw [hb] at h2
  exact hm.mul_right_eq_zero.1 h2

theorem spread_out : ∀ (T A : Type) [CommRing T] [CommRing A] [Algebra T A]
    [Algebra.FinitePresentation T A] (p : Ideal T) [p.IsPrime]
    (φ : A →ₐ[T] Localization.AtPrime p), ∃ f : T, f ∉ p ∧
      ∃ (s : A →ₐ[T] Localization.Away f) (ι : Localization.Away f →ₐ[T] Localization.AtPrime p),
        ι.comp s = φ := by
  intro T A _ _ _ _ p _ φ
  obtain ⟨n, π, hπ, hker⟩ := Algebra.FinitePresentation.out (R := T) (A := A)
  obtain ⟨G, hG⟩ := hker
  choose a s hs hy using fun i : Fin n => exists_num_den p (φ (π (MvPolynomial.X i)))
  set f₀ : T := ∏ i, s i with hf₀
  have hf₀p : f₀ ∉ p := prod_not_mem p _ s (fun i _ => hs i)
  have hu₀ : IsUnit ((Algebra.ofId T (Localization.AtPrime p)) f₀) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨f₀, hf₀p⟩ : p.primeCompl)
  let ι₀ : Localization.Away f₀ →ₐ[T] Localization.AtPrime p :=
    IsLocalization.Away.liftAlgHom (S := Localization.Away f₀) f₀ hu₀
  have hu : ∀ i, IsUnit (algebraMap T (Localization.Away f₀) (s i)) := fun i =>
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem s (Finset.mem_univ i)))
      (IsLocalization.Away.algebraMap_isUnit f₀)
  let x : Fin n → Localization.Away f₀ := fun i =>
    algebraMap T _ (a i) * ↑(hu i).unit⁻¹
  let ψ₀ : MvPolynomial (Fin n) T →ₐ[T] Localization.Away f₀ := MvPolynomial.aeval x
  have hι0 : ∀ i, ι₀ (x i) = φ (π (MvPolynomial.X i)) := by
    intro i
    have hu' : IsUnit (algebraMap T (Localization.AtPrime p) (s i)) :=
      IsLocalization.map_units _ (⟨s i, hs i⟩ : p.primeCompl)
    apply hu'.mul_left_cancel
    rw [hy i, ← AlgHom.commutes ι₀ (s i), ← map_mul]
    simp only [x]
    rw [mul_left_comm, IsUnit.mul_val_inv, mul_one, AlgHom.commutes]
  have hφ : ι₀.comp ψ₀ = φ.comp π := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, ψ₀, MvPolynomial.aeval_X]
    exact hι0 i
  have hzero : ∀ g : G, ι₀ (ψ₀ g) = 0 := by
    intro g
    have hg : (g : MvPolynomial (Fin n) T) ∈ RingHom.ker π.toRingHom := by
      rw [← hG]; exact Ideal.subset_span g.2
    rw [RingHom.mem_ker] at hg
    have := congrArg (fun h => h (g : MvPolynomial (Fin n) T)) hφ
    simp only [AlgHom.comp_apply] at this
    rw [this]
    have hg' : π g = 0 := hg
    rw [hg', map_zero]
  choose t ht hkill using fun g : G => exists_kill p f₀ (ψ₀ g) ι₀ (hzero g)
  set f : T := f₀ * ∏ g, t g with hfdef
  have hfp : f ∉ p :=
    p.primeCompl.mul_mem hf₀p (prod_not_mem p _ t (fun g _ => ht g))
  have huj : IsUnit ((Algebra.ofId T (Localization.Away f)) f₀) :=
    isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right f₀ _)) (IsLocalization.Away.algebraMap_isUnit f)
  let j : Localization.Away f₀ →ₐ[T] Localization.Away f :=
    IsLocalization.Away.liftAlgHom (S := Localization.Away f₀) f₀ huj
  let ψ : MvPolynomial (Fin n) T →ₐ[T] Localization.Away f := j.comp ψ₀
  have hψG : ∀ g : G, ψ g = 0 := by
    intro g
    apply hkill g (Localization.Away f) j
    exact isUnit_of_dvd_unit
      (map_dvd _ (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem t (Finset.mem_univ g)) f₀))
      (IsLocalization.Away.algebraMap_isUnit f)
  have hspan : Ideal.span (G : Set (MvPolynomial (Fin n) T)) ≤
      RingHom.ker (ψ : MvPolynomial (Fin n) T →+* Localization.Away f) := by
    rw [Ideal.span_le]
    intro g hg
    rw [SetLike.mem_coe, RingHom.mem_ker]
    exact hψG ⟨g, hg⟩
  have hψker : ∀ q : MvPolynomial (Fin n) T, q ∈ RingHom.ker π → ψ q = 0 := by
    intro q hq
    have hq' : q ∈ Ideal.span (G : Set (MvPolynomial (Fin n) T)) := by
      rw [hG]; exact hq
    exact (RingHom.mem_ker).1 (hspan hq')
  let sq := Ideal.Quotient.liftₐ (RingHom.ker π) ψ hψker
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  let σ : A →ₐ[T] Localization.Away f := sq.comp e.symm.toAlgHom
  have hσ : ∀ q, σ (π q) = ψ q := by
    intro q
    have : e.symm (π q) = Ideal.Quotient.mk (RingHom.ker π) q := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    show sq (e.symm (π q)) = ψ q
    rw [this]
    simp only [sq, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    rfl
  have huι : IsUnit ((Algebra.ofId T (Localization.AtPrime p)) f) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨f, hfp⟩ : p.primeCompl)
  let ι : Localization.Away f →ₐ[T] Localization.AtPrime p :=
    IsLocalization.Away.liftAlgHom (S := Localization.Away f) f huι
  refine ⟨f, hfp, σ, ι, ?_⟩
  have hιj : ι.comp j = ι₀ :=
    (IsLocalization.algHom_subsingleton (Submonoid.powers f₀)).elim _ _
  apply AlgHom.ext
  intro y
  obtain ⟨q, rfl⟩ := hπ y
  rw [AlgHom.comp_apply, hσ q]
  have h1 := congrArg (fun h => h (ψ₀ q)) hιj
  have h2 := congrArg (fun h => h q) hφ
  simp only [AlgHom.comp_apply] at h1 h2
  simp only [ψ, AlgHom.comp_apply]
  rw [h1, h2]

end SpreadOut
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
section
noncomputable section

namespace GlobalTheory.ValIwasawa

open Matrix

variable {V F : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]


variable (V) in
abbrev valI : Valuation F (ValuationRing.ValueGroup V F) := ValuationRing.valuation V F

theorem exists_of_valI_le_one {x : F} (h : valI (V := V) x ≤ 1) : ∃ a : V, algebraMap V F a = x :=
  (ValuationRing.mem_integer_iff V F x).1 h

theorem exists_clear_col {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (hA : A.det ≠ 0) :
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) V, IsUnit Q.det ∧
      ∀ i : Fin n, (Q.map (algebraMap V F) * A) i.succ 0 = 0 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun r => valI (V := V) (A r 0)) Finset.univ_nonempty
  have hcol : ∃ r, A r 0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (Matrix.det_eq_zero_of_column_eq_zero 0 h)
  have hp0 : A p 0 ≠ 0 := by
    obtain ⟨r, hr⟩ := hcol
    intro h0
    have := hp r (Finset.mem_univ _)
    rw [h0, map_zero] at this
    exact hr ((valI (V := V)).zero_iff.1 (le_antisymm this zero_le))
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p
  let P : Matrix (Fin (n + 1)) (Fin (n + 1)) V := σ.toPEquiv.toMatrix
  have hc : ∀ i, ∃ a : V, algebraMap V F a = A (σ i) 0 / A p 0 := by
    intro i
    apply exists_of_valI_le_one
    rw [map_div₀]
    have hpos : valI (V := V) (A p 0) ≠ 0 := by simpa using hp0
    rw [div_le_one₀ (zero_lt_iff.2 hpos)]
    exact hp _ (Finset.mem_univ _)
  choose c hc using hc
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) V := Matrix.of fun i j =>
    if i = j then 1 else if j = 0 then -c i else 0
  refine ⟨E * P, ?_, ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul ?_ ?_
    · have hE : E.det = 1 := by
        rw [Matrix.det_of_lowerTriangular E]
        · simp [E]
        · intro i j hij
          have hij' : i < j := hij
          have hj : j ≠ 0 := fun h => by subst h; exact Fin.not_lt_zero _ hij'
          simp only [E, Matrix.of_apply, if_neg (ne_of_lt hij'), if_neg hj]
      rw [hE]; exact isUnit_one
    · simp only [P, Matrix.det_permutation]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · intro i
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_succ]
    have hPA : ∀ r, (P.map (algebraMap V F) * A) r 0 = A (σ r) 0 := by
      intro r
      simp [P, Matrix.mul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp only [hPA, Matrix.map_apply, E, Matrix.of_apply]
    rw [if_neg (Fin.succ_ne_zero i)]
    simp only [if_true, Fin.succ_ne_zero, map_neg, map_one, map_zero, zero_mul]
    rw [Finset.sum_eq_single i]
    · simp only [if_true, map_one, one_mul]
      rw [hc]
      have : σ 0 = p := by simp [σ]
      rw [this]
      field_simp
      ring
    · intro j _ hji
      rw [if_neg (fun h => hji (Fin.succ_injective _ h).symm)]
      simp
    · intro h; exact absurd (Finset.mem_univ i) h

theorem iwasawa_matrix : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) F), A.det ≠ 0 →
    ∃ (k : Matrix (Fin n) (Fin n) V) (U : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ U.BlockTriangular id ∧
      (∀ i, U i i ≠ 0) ∧ A = k.map (algebraMap V F) * U := by
  intro n
  induction n with
  | zero =>
    intro A _
    exact ⟨1, A, by simp, fun i => i.elim0, fun i => i.elim0, by ext i; exact i.elim0⟩
  | succ n ih =>
    intro A hA
    obtain ⟨Q, hQ, hQA⟩ := exists_clear_col (V := V) (n := n) A hA
    set B := Q.map (algebraMap V F) * A with hB
    have hdetB : B.det = B 0 0 * (B.submatrix Fin.succ Fin.succ).det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp [hQA, B]
    have hQF : (Q.map (algebraMap V F)).det = algebraMap V F Q.det := by
      rw [RingHom.map_det]; rfl
    have hBne : B.det ≠ 0 := by
      rw [hB, Matrix.det_mul, hQF]
      exact mul_ne_zero (hQ.map (algebraMap V F)).ne_zero hA
    have hB00 : B 0 0 ≠ 0 := by intro h; apply hBne; rw [hdetB, h, zero_mul]
    obtain ⟨k', U', hk', hU', hd', hA'⟩ := ih (B.submatrix Fin.succ Fin.succ) (by
      intro h; apply hBne; rw [hdetB, h, mul_zero])
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) V := Matrix.of fun i j =>
      Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => k' i' j') j) i
    let U : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i j =>
      Fin.cases (B 0 j) (fun i' => Fin.cases 0 (fun j' => U' i' j') j) i
    have hKU : K.map (algebraMap V F) * U = B := by
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ]
      · refine Fin.cases ?_ (fun j' => ?_) j
        · simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ, hQA]
        · have h1 := congrFun (congrFun hA' i') j'
          simp only [Matrix.submatrix_apply] at h1
          rw [h1]
          simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ]
    have hKdet : K.det = k'.det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp [K]
      rfl
    refine ⟨Q⁻¹ * K, U, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul, hKdet]
      exact (Matrix.isUnit_nonsing_inv_det Q hQ).mul hk'
    · intro i j hij
      induction i using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero _)
      | succ i' =>
        induction j using Fin.cases with
        | zero => simp [U]
        | succ j' =>
          have : j' < i' := Fin.succ_lt_succ_iff.1 hij
          simpa [U] using hU' this
    · intro i
      induction i using Fin.cases with
      | zero => simpa [U] using hB00
      | succ i' => simpa [U] using hd' i'
    · rw [Matrix.map_mul, Matrix.mul_assoc, hKU, hB, ← Matrix.mul_assoc, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul Q hQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem iwasawa : ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] (N : ℕ) (g : GL (Fin N) K), ∃ (k : GL (Fin N) V) (b : GL (Fin N) K),
    b.1.BlockTriangular id ∧ g = GeneralLinearGroup.map (algebraMap V K) k * b := by
  intro V K _ _ _ _ _ _ N g
  obtain ⟨k, U, hk, hU, -, hg⟩ := iwasawa_matrix (V := V) g.1 (Matrix.GeneralLinearGroup.det_ne_zero g)
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det k).2 hk
  refine ⟨u, (GeneralLinearGroup.map (n := Fin N) (algebraMap V K) u)⁻¹ * g, ?_, by simp⟩
  have : ((GeneralLinearGroup.map (n := Fin N) (algebraMap V K) u)⁻¹ * g).1 = U := by
    have h1 : g.1 = (GeneralLinearGroup.map (n := Fin N) (algebraMap V K) u).1 * U := hg
    rw [Units.val_mul, h1, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [this]
  exact hU

end GlobalTheory.ValIwasawa
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyAnnihilatesCommutingLinearCombination
section
noncomputable section

open Polynomial

namespace GlobalTheory.CommutingPoly

theorem exists_poly_annihilates_linear_combination : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Type} [Fintype ι] (A : ι → Module.End ℂ M),
    (∀ i j, Commute (A i) (A j)) → ∀ (c : ι → ℂ) (P : ι → Polynomial ℂ), (∀ i, P i ≠ 0) →
      ∃ p : Polynomial ℂ, p ≠ 0 ∧ ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) →
        Polynomial.aeval (∑ i, c i • A i) p v = 0 := by
  intro M _ _ ι _ A hc c P hP
  classical
  letI : IsMulCommutative (Algebra.adjoin ℂ (Set.range A)) :=
    Algebra.isMulCommutative_adjoin ℂ (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hc i j)
  open scoped IsMulCommutative in
  let S := Algebra.adjoin ℂ (Set.range A)
  let I : Ideal S :=
    { carrier := {a | ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) → (a : Module.End ℂ M) v = 0}
      add_mem' := by
        intro a b ha hb v hv
        simp only [Set.mem_setOf_eq] at ha hb
        simp [ha v hv, hb v hv]
      zero_mem' := by intro v _; simp
      smul_mem' := by
        intro a b hb v hv
        show ((a * b : S) : Module.End ℂ M) v = 0
        rw [Subalgebra.coe_mul, Module.End.mul_apply, hb v hv, map_zero] }
  have hI : ∀ a : S, a ∈ I ↔ ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) → (a : Module.End ℂ M) v = 0 :=
    fun a => Iff.rfl
  let t : ι → S := fun i => ⟨A i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  let q : S →ₐ[ℂ] S ⧸ I := Ideal.Quotient.mkₐ ℂ I
  have hint : ∀ i, IsIntegral ℂ (q (t i)) := by
    intro i
    refine IsAlgebraic.isIntegral ⟨P i, hP i, ?_⟩
    rw [aeval_algHom_apply]
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    rw [hI]
    intro v hv
    rw [aeval_subalgebra_coe]
    exact hv i
  have hs : IsIntegral ℂ (q (∑ i, c i • t i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact IsIntegral.sum _ (fun i _ => by rw [map_smul]; exact (hint i).smul _)
  obtain ⟨p, hpm, hp⟩ := hs
  refine ⟨p, hpm.ne_zero, fun v hv => ?_⟩
  have hq : q (aeval (∑ i, c i • t i) p) = 0 := by
    rw [← aeval_algHom_apply, aeval_def]
    exact hp
  have hmem : aeval (∑ i, c i • t i) p ∈ I := (Ideal.Quotient.eq_zero_iff_mem).mp hq
  have h := (hI _).mp hmem v hv
  rw [aeval_subalgebra_coe] at h
  have hsum : ((∑ i, c i • t i : S) : Module.End ℂ M) = ∑ i, c i • A i := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show ((∑ i, c i • t i : S) : Module.End ℂ M) = S.val (∑ i, c i • t i) from rfl, map_sum]
    simp [t]
  rw [hsum] at h
  exact h

end GlobalTheory.CommutingPoly
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyEntriesConjLeftRightMul
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.PolyEntryMul

theorem totalDegree_bind₁_le_of_le_one {σ τ : Type*} (f : σ → MvPolynomial τ ℂ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (Q : MvPolynomial σ ℂ) :
    (bind₁ f Q).totalDegree ≤ Q.totalDegree := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [Q.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hs)
  refine (Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left _ (hf i))).trans ?_
  simp [Finsupp.sum]

def subst {n : ℕ} (a b : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n × Fin n) ⊕ (Fin n × Fin n) → MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ
  | Sum.inl z => ∑ k : Fin n, ∑ l : Fin n, C (a z.1 k * b l z.2) * X (Sum.inl (k, l))
  | Sum.inr z => ∑ k : Fin n, ∑ l : Fin n, C (star (a z.1 k * b l z.2)) * X (Sum.inr (k, l))

theorem totalDegree_subst {n : ℕ} (a b : Matrix (Fin n) (Fin n) ℂ) (i) :
    (subst a b i).totalDegree ≤ 1 := by
  rcases i with z | z <;>
  · refine totalDegree_finsetSum_le fun k _ => totalDegree_finsetSum_le fun l _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]

theorem main : ∀ (n : ℕ) (a b : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ), ∃ Q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, Q.totalDegree ≤ P.totalDegree ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (a * g * b) z.1 z.2) (fun z : Fin n × Fin n => star ((a * g * b) z.1 z.2))) P = MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (g) z.1 z.2) (fun z : Fin n × Fin n => star ((g) z.1 z.2))) Q := by
  intro n a b P
  refine ⟨bind₁ (subst a b) P, totalDegree_bind₁_le_of_le_one _ (totalDegree_subst a b) P, fun g => ?_⟩
  conv_rhs => rw [eval, eval₂Hom_bind₁]
  rw [eval]
  refine congrArg (fun x => eval₂Hom (RingHom.id ℂ) x P) (funext fun i => ?_)
  rcases i with z | z
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [Sum.elim_inl, subst, map_sum, map_mul, coe_eval₂Hom, eval₂_C, eval₂_X,
      RingHom.id_apply, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [Sum.elim_inr, subst, map_sum, map_mul, coe_eval₂Hom, eval₂_C, eval₂_X,
      RingHom.id_apply, Matrix.mul_apply, Finset.sum_mul, star_sum, star_mul']
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    ring

end GlobalTheory.PolyEntryMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneIsUnitOneSubPow
section
namespace GlobalTheory

theorem exists_pow_eq_one_isUnit_one_sub_pow (T : Type) [CommRing T] [IsDomain T] (q : ℕ) (hq0 : 0 < q) (hq : IsUnit (q : T))
    (hT : ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) :
    ∃ ζ : T, ζ ^ q = 1 ∧ ∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k) := by
  classical
  haveI : NeZero (q : T) := ⟨hq.ne_zero⟩
  obtain ⟨x, hx⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T)
    (by rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 hq0)
  have hprim : IsPrimitiveRoot x q := (Polynomial.isRoot_cyclotomic_iff).1 hx
  refine ⟨x, hprim.pow_eq_one, fun k hk hkq => ?_⟩
  set S := Polynomial.nthRootsFinset q (1 : T) with hS
  have h1S : (1 : T) ∈ S := (Polynomial.mem_nthRootsFinset hq0 (1 : T)).2 (one_pow _)
  have hprod := Polynomial.X_pow_sub_one_eq_prod hq0 hprim
  rw [← Finset.mul_prod_erase S _ h1S] at hprod
  have hgeom : (Polynomial.X - Polynomial.C (1 : T)) * ∑ i ∈ Finset.range q, (Polynomial.X : Polynomial T) ^ i
      = Polynomial.X ^ q - 1 := by
    rw [Polynomial.C_1]; exact mul_geom_sum _ _
  have hne : (Polynomial.X - Polynomial.C (1 : T)) ≠ 0 := Polynomial.X_sub_C_ne_zero 1
  have hcan : ∑ i ∈ Finset.range q, (Polynomial.X : Polynomial T) ^ i
      = ∏ ζ ∈ S.erase 1, (Polynomial.X - Polynomial.C ζ) :=
    mul_left_cancel₀ hne (hgeom.trans hprod)
  have hev := congrArg (Polynomial.eval (1 : T)) hcan
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_C] at hev
  have hmem : x ^ k ∈ S.erase 1 := by
    refine Finset.mem_erase.2 ⟨hprim.pow_ne_one_of_pos_of_lt hk.ne' hkq, ?_⟩
    exact (Polynomial.mem_nthRootsFinset hq0 (1 : T)).2 (by rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow])
  have hdvd : (1 - x ^ k) ∣ (q : T) := hev ▸ Finset.dvd_prod_of_mem _ hmem
  exact isUnit_of_dvd_unit hdvd hq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulNormLeOne
section
namespace GlobalTheory.PowerScaledNormBound

theorem exists_pow_mul_norm_le_one (p : ℕ) [Fact (Nat.Prime p)] (y : PadicAlgCl p) :
    ∃ k : ℕ, ‖(p : PadicAlgCl p) ^ k * y‖ ≤ (1 : ℝ) := by
  have hprime : p.Prime := Fact.out
  have hp : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
    rw [← PadicAlgCl.valuation_coe, PadicAlgCl.valuation_p p]
    simp
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hprime.one_lt)
  have hy := norm_nonneg y
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (‖y‖ + 1) by positivity) hp1
  refine ⟨k, ?_⟩
  rw [norm_mul, norm_pow, hp]
  calc (p : ℝ)⁻¹ ^ k * ‖y‖ ≤ 1 / (‖y‖ + 1) * ‖y‖ := mul_le_mul_of_nonneg_right hk.le hy
    _ ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      linarith

end GlobalTheory.PowerScaledNormBound
end

