module

public import Mathlib
public import Formalism.GL3MeanSquares.Bundle0003
public import Formalism.GL3MeanSquares.RationalMatrixPrimeOrderBound
public import Formalism.GL3MeanSquares.HookFormulaTorsion.LengthQuotientBoundGeneral

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.BimultiplicativeDivisibleTorsion
section
namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

theorem no_form_of_bidegree_one_one : PowerCongruenceIffEqual := by
  unfold PowerCongruenceIffEqual
  intro l d s s' hl hs hs' hdiv
  have h1 : l ^ s < l ^ d := Nat.pow_lt_pow_right (by omega) hs
  have h2 : l ^ s' < l ^ d := Nat.pow_lt_pow_right (by omega) hs'
  have h3 : 1 ≤ l ^ s := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ l ^ s' := Nat.one_le_pow _ _ (by omega)
  have h5 : 1 ≤ l ^ d := Nat.one_le_pow _ _ (by omega)
  rw [Nat.cast_sub h5, Nat.cast_pow, Nat.cast_one] at hdiv
  have h1' : (l : ℤ) ^ s < (l : ℤ) ^ d := by exact_mod_cast h1
  have h2' : (l : ℤ) ^ s' < (l : ℤ) ^ d := by exact_mod_cast h2
  have h3' : (1 : ℤ) ≤ (l : ℤ) ^ s := by exact_mod_cast h3
  have h4' : (1 : ℤ) ≤ (l : ℤ) ^ s' := by exact_mod_cast h4
  have hz := Int.eq_zero_of_abs_lt_dvd hdiv (by rw [abs_lt]; constructor <;> linarith)
  have h6 : (l : ℤ) ^ s = (l : ℤ) ^ s' := by linarith
  have h7 : l ^ s = l ^ s' := by exact_mod_cast h6
  exact Nat.pow_right_injective hl h7

end Formalism.HermitianLattices.IntegralLatticeDensity
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.FourFoldOrthogonalSum
section
namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

theorem integer_mean_log_bound : IntegerMeanLog := by
  intro K _ _ x hx
  have hx' : (x : K) ≠ 0 := by exact_mod_cast hx
  have hne : ∀ φ : K →+* ℂ, ‖φ (x : K)‖ ≠ 0 := fun φ => by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero φ).mpr hx'
  rw [← Real.log_prod (fun φ _ => hne φ)]
  apply Real.log_nonneg
  rw [← norm_prod]
  have key : (∏ φ : K →+* ℂ, φ (x : K)) = algebraMap ℚ ℂ (Algebra.norm ℚ (x : K)) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun φ => rfl)
  rw [key, ← Algebra.coe_norm_int x]
  have hN0 : Algebra.norm ℤ x ≠ 0 := by
    intro h0
    have h5 : Algebra.norm ℚ (x : K) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx'
    apply h5
    rw [← Algebra.coe_norm_int x, h0, Int.cast_zero]
  rw [eq_ratCast, Rat.cast_intCast, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hN0

theorem weber_function_root : WeberRoot := by
  intro x j s hs hj hx
  have hs0 : (s : ℂ) ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  refine ⟨?_, ?_⟩
  · let R := integralClosure ℤ ℂ
    let jR : R := ⟨j, hj⟩
    let q : Polynomial R := (Polynomial.X - Polynomial.C (s : R)) ^ 3 - Polynomial.C jR * Polynomial.X
    have hq : q.Monic := by
      apply Polynomial.Monic.sub_of_left ((Polynomial.monic_X_sub_C _).pow 3)
      rw [Polynomial.degree_pow, Polynomial.degree_X_sub_C]
      refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) ?_
      norm_num
    have hxR : IsIntegral R x := by
      refine ⟨q, hq, ?_⟩
      simp only [q, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, Polynomial.eval₂_mul]
      simp only [map_intCast]
      have hjR : algebraMap R ℂ jR = j := rfl
      rw [hjR]
      linear_combination hx
    exact isIntegral_trans x hxR
  · intro h
    rw [h] at hx
    apply hs0
    have h3 : (s : ℂ) ^ 3 = 0 := by linear_combination -hx
    exact (pow_eq_zero_iff (by norm_num)).mp h3

end Formalism.HermitianLattices.IntegralLatticeDensity
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.HyperbolicPlaneSplit
section
namespace Formalism.HermitianLattices.IntegralLatticeDensity.PD

open Finset Formalism.HermitianLattices.IntegralLatticeDensity

section calculus

variable {M Q : Type} [AddCommGroup M] [AddCommGroup Q] {φ : M → Q}

theorem cob_symm' (a b : M) : cob φ a b = cob φ b a := by
  simp only [cob]
  rw [add_comm a b]
  abel

theorem phi_add' (a b : M) : φ (a + b) = φ a + φ b + cob φ a b := by
  simp only [cob]
  abel

theorem cob_add_right' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) (a b b' : M) :
    cob φ a (b + b') = cob φ a b + cob φ a b' := by
  rw [cob_symm', h1, cob_symm' b, cob_symm' b']

theorem cob_zero_left' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) (b : M) :
    cob φ 0 b = 0 := by
  have h := h1 0 0 b
  rw [add_zero] at h
  calc cob φ 0 b = (cob φ 0 b + cob φ 0 b) - cob φ 0 b := by abel
    _ = cob φ 0 b - cob φ 0 b := by rw [← h]
    _ = 0 := sub_self _

theorem cob_zero_right' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) (a : M) :
    cob φ a 0 = 0 := by
  rw [cob_symm', cob_zero_left' h1]

theorem phi_zero' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) : φ 0 = 0 := by
  have h := cob_zero_left' h1 (0 : M)
  simp only [cob, add_zero, sub_self, zero_sub, neg_eq_zero] at h
  exact h

theorem cob_sum_right' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    {J : Type} (a : M) (s : Finset J) (x : J → M) :
    cob φ a (∑ j ∈ s, x j) = ∑ j ∈ s, cob φ a (x j) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, cob_zero_right' h1]
  | cons j s hj ih => rw [Finset.sum_cons, Finset.sum_cons, cob_add_right' h1, ih]

theorem cob_sum_left' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    {J : Type} (b : M) (s : Finset J) (x : J → M) :
    cob φ (∑ j ∈ s, x j) b = ∑ j ∈ s, cob φ (x j) b := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, cob_zero_left' h1]
  | cons j s hj ih => rw [Finset.sum_cons, Finset.sum_cons, h1, ih]

variable {O : Type} [CommRing O] [StarRing O] [Module O M]

theorem cross' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    (h2 : ∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b))
    {n J : Type} [Fintype n] (c : n → O) (d : n → J → O) (a : M) (s : Finset J) (x : J → M) :
    ∑ i, cob φ (c i • a) (∑ j ∈ s, d i j • x j) =
      ∑ j ∈ s, cob φ a ((∑ i, star (c i) * d i j) • x j) := by
  simp_rw [h2, Finset.smul_sum, smul_smul, cob_sum_right' h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_smul, cob_sum_right' h1]

variable {Z : Type} [CommRing Z] [Module Z Q] {nm : O → Z}

theorem diag' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    (h2 : ∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b))
    (h3 : ∀ (α : O) u, φ (α • u) = nm α • φ u)
    {n J : Type} [Fintype n] (c : n → J → O)
    (hG : ∀ a j, a ≠ j → ∑ i, star (c i a) * c i j = 0) (u : J → M) (s : Finset J) :
    ∑ i, φ (∑ j ∈ s, c i j • u j) = ∑ j ∈ s, (∑ i, nm (c i j)) • φ (u j) := by
  induction s using Finset.cons_induction with
  | empty => simp [phi_zero' h1]
  | cons k s hk ih =>
    have hcross : ∑ i, cob φ (c i k • u k) (∑ j ∈ s, c i j • u j) = 0 := by
      rw [cross' h1 h2 (fun i => c i k) c (u k) s u]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hne : k ≠ j := by
        rintro rfl
        exact hk hj
      rw [hG k j hne, zero_smul, cob_zero_right' h1]
    simp only [Finset.sum_cons]
    simp only [phi_add', Finset.sum_add_distrib, h3]
    rw [hcross, ih, ← Finset.sum_smul, add_zero]

end calculus

end Formalism.HermitianLattices.IntegralLatticeDensity.PD

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset PD

theorem unitary_invariance : UnitaryInvariance := by
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm hinj hnm h1 h2 h3 n _ _ δ hδ u
  have hG : ∀ a j, a ≠ j → ∑ i, star (δ i a) * δ i j = 0 := by
    intro a j hne
    have := congrFun (congrFun hδ a) j
    simpa [Matrix.mul_apply, Matrix.one_apply_ne hne] using this
  have hN : ∀ j, ∑ i, nm (δ i j) = 1 := by
    intro j
    apply hinj
    have := congrFun (congrFun hδ j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    simpa [hnm] using this
  rw [diag' h1 h2 h3 δ hG u Finset.univ]
  simp [hN]

theorem hyperbolic_plane_split : HyperbolicSplit := by
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm hinj hnm h1 h2 h3 n ι _ _ _ f f' hff hf'f' hff' t t'

  have hiso : ∀ (g : ι → n → O) (w : ι → M), (∀ e e', ∑ i, star (g e i) * g e' i = 0) →
      ∑ i, φ (∑ e, g e i • w e) = 0 := by
    intro g w hg
    have hz : ∀ e, ∑ i, nm (g e i) = 0 := by
      intro e
      apply hinj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero]
      simpa [hnm] using hg e e
    rw [diag' h1 h2 h3 (fun i e => g e i) (fun a j _ => hg a j) w Finset.univ]
    simp [hz]

  have hcross : ∑ i, cob φ (∑ e, f e i • t e) (∑ e, f' e i • t' e) = ∑ e, cob φ (t e) (t' e) := by
    simp_rw [cob_sum_left' h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [cross' h1 h2 (fun i => f e i) (fun i e' => f' e' i) (t e) Finset.univ t',
      Finset.sum_eq_single e]
    · rw [hff' e e, if_pos rfl, one_smul]
    · intro e' _ hne
      rw [hff' e e', if_neg (fun h => hne h.symm), zero_smul, cob_zero_right' h1]
    · intro h
      exact absurd (Finset.mem_univ e) h
  calc ∑ i, φ (∑ e, (f e i • t e + f' e i • t' e))
      = ∑ i, (φ (∑ e, f e i • t e) + φ (∑ e, f' e i • t' e) +
          cob φ (∑ e, f e i • t e) (∑ e, f' e i • t' e)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_add_distrib, phi_add' (φ := φ)]
    _ = ∑ e, cob φ (t e) (t' e) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hiso f t hff, hiso f' t' hf'f', hcross,
          zero_add, zero_add]

end Formalism.HermitianLattices.IntegralLatticeDensity
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.InvariantKernelTraceVanishes
section
namespace Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums

open Module Finset Matrix

section IdxDet

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem lenQuotSpan (ϖ : R) (hϖ : Irreducible ϖ) (a : R) (ha : a ≠ 0) :
    Module.length R (R ⧸ Ideal.span ({a} : Set R)) = emultiplicity ϖ a := by
  obtain ⟨k, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have h1 : Ideal.span ({(w : R) * ϖ ^ k} : Set R) = IsLocalRing.maximalIdeal R ^ k := by
    rw [Ideal.span_singleton_mul_left_unit w.isUnit, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [h1, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal,
    emultiplicity_eq_of_associated_right (associated_unit_mul_left (ϖ ^ k) (w : R) w.isUnit),
    emultiplicity_pow_self_of_prime hϖ.prime]

theorem mulVecLin_inj {n : Type} [Fintype n] [DecidableEq n] (u : Matrix n n R) (hu : u.det ≠ 0) :
    Function.Injective u.mulVecLin := by
  intro x y hxy
  simp only [Matrix.mulVecLin_apply] at hxy
  have h2 : u.adjugate *ᵥ (u *ᵥ x) = u.adjugate *ᵥ (u *ᵥ y) := by rw [hxy]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.one_mulVec] at h2
  exact smul_right_injective _ hu h2

theorem endo_inj {n : Type} [Fintype n] [DecidableEq n] (P : (n → R) →ₗ[R] (n → R))
    (hP : LinearMap.det P ≠ 0) : Function.Injective P := by
  have h := mulVecLin_inj (LinearMap.toMatrix' P) (by rwa [LinearMap.det_toMatrix'])
  rwa [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix'] at h

theorem index_det (ϖ : R) (hϖ : Irreducible ϖ) {n : Type} [Fintype n] [DecidableEq n]
    (u : Matrix n n R) (hu : u.det ≠ 0) :
    Module.length R ((n → R) ⧸ LinearMap.range u.mulVecLin) = emultiplicity ϖ u.det := by
  set L := u.mulVecLin with hL
  have hinj : Function.Injective L := mulVecLin_inj u hu
  have h : Module.finrank R (LinearMap.range L) = Module.finrank R (n → R) :=
    LinearMap.finrank_range_of_inj hinj
  let b := Pi.basisFun R n
  rw [(Submodule.quotientEquivPiSpan (LinearMap.range L) b h).length_eq,
    Module.length_pi_of_fintype]
  rw [Finset.sum_congr rfl (fun i _ => lenQuotSpan ϖ hϖ _ (Submodule.smithNormalFormCoeffs_ne_zero b h i)),
    ← Finset.emultiplicity_prod hϖ.prime]
  set a := Submodule.smithNormalFormCoeffs b h
  set b' := Submodule.smithNormalFormTopBasis b h
  set ab := Submodule.smithNormalFormBotBasis b h
  have hab : ∀ i, (ab i : n → R) = a i • b' i := Submodule.smithNormalFormBotBasis_def b h
  let P : (n → R) →ₗ[R] (n → R) := b'.constr R (fun i => (ab i : n → R))
  have hPb : ∀ i, P (b' i) = a i • b' i := by
    intro i; simp only [P, Basis.constr_basis, hab]
  have hdetP : LinearMap.det P = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b']
    have : LinearMap.toMatrix b' b' P = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply, hPb, map_smul, b'.repr_self, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [this, Matrix.det_diagonal]
  have hPinj : Function.Injective P := endo_inj P (by
    rw [hdetP]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => Submodule.smithNormalFormCoeffs_ne_zero b h i))
  have hPL : ∀ x, P x ∈ LinearMap.range L := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b'.sum_repr x, map_sum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [map_smul, hPb, ← hab]
    exact Submodule.smul_mem _ _ (ab i).2
  have hLP : ∀ x, L x ∈ LinearMap.range P := by
    intro x
    let y : LinearMap.range L := ⟨L x, LinearMap.mem_range_self L x⟩
    refine ⟨∑ i, ab.repr y i • b' i, ?_⟩
    have e2 := congrArg Subtype.val (ab.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    calc ∑ i, P (ab.repr y i • b' i) = ∑ i, ab.repr y i • (ab i : n → R) :=
          Finset.sum_congr rfl (fun i _ => by rw [map_smul, hPb, hab])
      _ = L x := e2
  let g : (n → R) →ₗ[R] (n → R) :=
    (LinearEquiv.ofInjective P hPinj).symm.toLinearMap ∘ₗ L.codRestrict (LinearMap.range P) hLP
  let g' : (n → R) →ₗ[R] (n → R) :=
    (LinearEquiv.ofInjective L hinj).symm.toLinearMap ∘ₗ P.codRestrict (LinearMap.range L) hPL
  have hg : P ∘ₗ g = L := by
    refine LinearMap.ext fun x => ?_
    exact congrArg Subtype.val ((LinearEquiv.ofInjective P hPinj).apply_symm_apply
      (L.codRestrict (LinearMap.range P) hLP x))
  have hg' : L ∘ₗ g' = P := by
    refine LinearMap.ext fun x => ?_
    exact congrArg Subtype.val ((LinearEquiv.ofInjective L hinj).apply_symm_apply
      (P.codRestrict (LinearMap.range L) hPL x))
  have hdetL : LinearMap.det L = u.det := by
    rw [hL, ← Matrix.toLin'_apply', LinearMap.det_toLin']
  have d1 : LinearMap.det P ∣ u.det := ⟨LinearMap.det g, by rw [← hdetL, ← hg, LinearMap.det_comp]⟩
  have d2 : u.det ∣ LinearMap.det P := ⟨LinearMap.det g', by rw [← hdetL, ← hg', LinearMap.det_comp]⟩
  rw [← hdetP]
  exact emultiplicity_eq_of_associated_right (associated_of_dvd_dvd d1 d2)

end IdxDet

section Count

variable {F : Type} [Field F] [Fintype F]

end Count

end Formalism.HermitianLattices.RamifiedLatticeOperators.IndexDeterminantCharacterSums
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.LemmaCTwistRamified
section
namespace Formalism.HermitianLattices.RamifiedHeckeModels

theorem lemma_c_twist_ramified : LemmaC_twist_ram := by
  unfold LemmaC_twist_ram
  intro R _ _ _ ϖ hϖ M _ _ P S B U D e b hSB hBU hSD hPU hPD hsat hUD hfree hfin
  have hpow : ∀ n : ℕ, ∀ x : M, ϖ ^ n • x ∈ P → x ∈ P := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      apply hsat
      apply ih
      rwa [← mul_smul, ← pow_succ]
  have h1 : (S ⊓ P).map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M)) ≤ B ⊓ P := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hSB ⟨s, hs.1, rfl⟩, by simpa using P.smul_mem (ϖ ^ b) hs.2⟩
  have h2 : (B ⊓ P).map U ≤ S ⊓ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hBU ⟨x, hx.1, rfl⟩, hPU ⟨x, hx.2, rfl⟩⟩
  have h3 : (S ⊓ P).map D ≤ B ⊓ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hSD ⟨x, hx.1, rfl⟩, hPD ⟨x, hx.2, rfl⟩⟩
  let ι : (S ⊓ P : Submodule R M) →ₗ[R] S := Submodule.inclusion inf_le_left
  have hι : Function.Injective ι := Submodule.inclusion_injective _
  obtain ⟨n, bN⟩ := Submodule.basisOfPid (Module.Free.chooseBasis R S)
    ((S ⊓ P).comap S.subtype)
  let eN : ((S ⊓ P).comap S.subtype) ≃ₗ[R] (S ⊓ P : Submodule R M) :=
    Submodule.comapSubtypeEquivOfLe inf_le_left
  haveI : Module.Free R (S ⊓ P : Submodule R M) := Module.Free.of_basis (bN.map eN)
  haveI : Module.Finite R (S ⊓ P : Submodule R M) := Module.Finite.of_basis (bN.map eN)
  have key := lemma_c_under_twist
  unfold LemmaC_twist at key
  have key' := key R ϖ hϖ M (S ⊓ P) (B ⊓ P) U D e b h1 h2 h3 hUD inferInstance inferInstance
  have hrank : Module.finrank R (S ⊓ P : Submodule R M) ≤ Module.finrank R S :=
    LinearMap.finrank_le_finrank_of_injective hι
  have hlen : Module.length R ((B ⊓ P : Submodule R M) ⧸
      ((S ⊓ P).map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap (B ⊓ P).subtype) ≤
      Module.length R (B ⧸ (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap B.subtype) := by
    refine Module.length_le_of_injective
      (Submodule.mapQ _ _ (Submodule.inclusion (inf_le_left : B ⊓ P ≤ B)) ?_) ?_
    · intro x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
      exact Submodule.map_mono inf_le_left hx
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro q hq
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hq ⊢
      obtain ⟨s, hs, hsx⟩ := hq
      refine ⟨s, ⟨hs, ?_⟩, hsx⟩
      apply hpow b
      have hx' : (ϖ ^ b • s : M) = x := by simpa using hsx
      rw [hx']
      exact x.2.2
  refine key'.trans (add_le_add hlen ?_)
  exact_mod_cast Nat.mul_le_mul_left e hrank

end Formalism.HermitianLattices.RamifiedHeckeModels
end

