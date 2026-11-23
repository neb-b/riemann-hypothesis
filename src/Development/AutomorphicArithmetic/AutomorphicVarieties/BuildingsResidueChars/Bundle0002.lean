module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFixedRotationBasisOfCharpoly
section
open Matrix

private lemma cayley_hamilton_rank_three_factored {K : Type} [Field K] (τ : K) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X + 1)) :
    (M - 1) * (M * M - τ • M + 1) = 0 := by
  have h := Matrix.aeval_self_charpoly M
  rw [hM] at h
  simp only [map_mul, map_sub, map_add (f := _), map_one, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C] at h
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, sq] at h
  exact h

private lemma trace_inverseGram_conj_smul_eq {K : Type} [Field K] [CharZero K] (τ : K) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X + 1)) :
    Matrix.trace M = 1 + τ ∧ Matrix.trace (M * M) = τ ^ 2 - 1 := by
  have hp : ∀ t : K, (Matrix.scalar (Fin 3) t - M).det = (t - 1) * (t ^ 2 - τ * t + 1) := by
    intro t
    rw [← Matrix.eval_charpoly, hM]
    simp
  have e0 := hp 0
  have e1 := hp 1
  have em := hp (-1)
  simp only [Matrix.det_fin_three, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply] at e0 e1 em
  simp only [Fin.isValue, Fin.reduceEq, if_true, if_false, eq_self_iff_true] at e0 e1 em
  constructor
  · rw [Matrix.trace_fin_three]
    linear_combination e0 - e1 / 2 - em / 2
  · rw [Matrix.trace_fin_three]
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (M 0 0 + M 1 1 + M 2 2 + 1 + τ) * (e0 - e1 / 2 - em / 2) - (e1 - em)

theorem UpperTheory.exists_fixed_rotation_basis_of_charpoly :
    ∀ (K : Type) [Field K] [CharZero K] (τ : K), τ ^ 2 - 4 ≠ 0 → ∀ M : Matrix (Fin 3) (Fin 3) K,
        M.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X + 1) →
        ∃ e v : Fin 3 → K, M *ᵥ e = e ∧ M *ᵥ (M *ᵥ v) = τ • (M *ᵥ v) - v ∧ (Matrix.of ![e, v, M *ᵥ v]).det ≠ 0 := by
  intro K _ _ τ hτ M hM
  have hPQ := cayley_hamilton_rank_three_factored τ M hM
  obtain ⟨htr1, htr2⟩ := trace_inverseGram_conj_smul_eq τ M hM
  have hc : (2 - τ : K) ≠ 0 := by
    intro h0
    apply hτ
    have h2 : τ = 2 := by linear_combination -h0
    rw [h2]
    norm_num
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin 3) (Fin 3) K, Q = M * M - τ • M + 1 := ⟨_, rfl⟩
  rw [← hQdef] at hPQ
  have hMQ : M * Q = Q := by
    rw [sub_mul, one_mul, sub_eq_zero] at hPQ
    exact hPQ
  have hQM : Q * M = Q := by
    have hc' : Q * M = M * Q := by
      rw [hQdef]
      simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
        mul_smul_comm, mul_assoc]
    rw [hc', hMQ]
  have hQQ : Q * Q = (2 - τ) • Q := by
    calc Q * Q = Q * (M * M - τ • M + 1) := by rw [← hQdef]
      _ = Q * M * M - τ • (Q * M) + Q := by
        simp only [mul_add, mul_sub, mul_one, mul_smul_comm, mul_assoc]
      _ = (2 - τ) • Q := by
        rw [hQM, hQM, sub_smul, two_smul]
        abel
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin 3) (Fin 3) K, E = (2 - τ)⁻¹ • Q := ⟨_, rfl⟩
  have hEE : E * E = E := by
    rw [hE, smul_mul_smul_comm, hQQ, smul_smul]
    congr 1
    field_simp
  have hME : M * E = E := by rw [hE, mul_smul_comm, hMQ]
  have hEM : E * M = E := by rw [hE, smul_mul_assoc, hQM]
  have htrQ : Matrix.trace Q = 2 - τ := by
    rw [hQdef, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, htr1, htr2, Matrix.trace_one]
    simp only [Fintype.card_fin, smul_eq_mul]
    push_cast
    ring
  have htrE : Matrix.trace E = 1 := by
    rw [hE, Matrix.trace_smul, htrQ, smul_eq_mul, inv_mul_cancel₀ hc]
  obtain ⟨F, hF⟩ : ∃ F : Matrix (Fin 3) (Fin 3) K, F = 1 - E := ⟨_, rfl⟩
  have htrF : Matrix.trace F = 2 := by
    rw [hF, Matrix.trace_sub, Matrix.trace_one, htrE]
    simp only [Fintype.card_fin]
    norm_num
  have hQF : Q * F = 0 := by
    rw [hF, mul_sub, mul_one, hE, mul_smul_comm, hQQ, smul_smul, inv_mul_cancel₀ hc, one_smul,
      sub_self]
  have hEF : E * F = 0 := by rw [hF, mul_sub, mul_one, hEE, sub_self]
  have hMF : M * F = F * M := by rw [hF, mul_sub, sub_mul, mul_one, one_mul, hME, hEM]
  have hQv : ∀ x : Fin 3 → K, Q *ᵥ x = M *ᵥ (M *ᵥ x) - τ • (M *ᵥ x) + x := by
    intro x
    rw [hQdef, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_mulVec]
  have hdet : (Matrix.scalar (Fin 3) (1 : K) - M).det = 0 := by
    rw [← Matrix.eval_charpoly, hM]
    simp
  obtain ⟨e, he0, he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hMe : M *ᵥ e = e := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at he
    simpa using he.symm
  have hEe : E *ᵥ e = e := by
    have h1 : Q *ᵥ e = (2 - τ) • e := by
      rw [hQv, hMe, hMe, sub_smul, two_smul]
      abel
    rw [hE, Matrix.smul_mulVec, h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
  let W : Submodule K (Fin 3 → K) := LinearMap.range (Matrix.toLin' F)
  have hW : ∀ x ∈ W, Matrix.toLin' M x ∈ W := by
    rintro x ⟨y, rfl⟩
    refine ⟨M *ᵥ y, ?_⟩
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hMF]
  let g : W →ₗ[K] W := (Matrix.toLin' M).restrict hW
  obtain ⟨v0, hv0⟩ : ∃ v : W, LinearIndependent K ![v, g v] := by
    by_contra hno
    push_neg at hno
    obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hno
    have hMFx : ∀ x : Fin 3 → K, M *ᵥ (F *ᵥ x) = a • (F *ᵥ x) := by
      intro x
      have h := congrArg (fun h : W →ₗ[K] W => ((h ⟨F *ᵥ x, x, rfl⟩ : W) : Fin 3 → K)) ha
      simpa [g, LinearMap.restrict_apply, Matrix.toLin'_apply] using h
    have hMFm : M * F = a • F := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro z
      rw [map_smul, LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
        ← Matrix.mulVec_mulVec, hMFx]
    have htrM : Matrix.trace M = 1 + 2 * a := by
      have hsplit : M = M * E + M * F := by rw [← mul_add, hF, add_sub_cancel, mul_one]
      rw [hsplit, Matrix.trace_add, hME, hMFm, Matrix.trace_smul, htrE, htrF, smul_eq_mul]
      ring
    have hF0 : ∃ x : Fin 3 → K, F *ᵥ x ≠ 0 := by
      by_contra hall
      push_neg at hall
      have hF00 : F = 0 := by
        apply Matrix.toLin'.injective
        apply LinearMap.ext
        intro z
        rw [map_zero, LinearMap.zero_apply, Matrix.toLin'_apply, hall z]
      rw [hF00, Matrix.trace_zero] at htrF
      norm_num at htrF
    obtain ⟨x, hx⟩ := hF0
    have hq : (a ^ 2 - τ * a + 1) • (F *ᵥ x) = 0 := by
      have h := hQv (F *ᵥ x)
      rw [Matrix.mulVec_mulVec, hQF, Matrix.zero_mulVec, hMFx, Matrix.mulVec_smul, hMFx] at h
      rw [h]
      module
    have hq' : a ^ 2 - τ * a + 1 = 0 := by
      rcases smul_eq_zero.mp hq with h | h
      · exact h
      · exact absurd h hx
    apply hτ
    have ht : τ = 2 * a := by linear_combination htr1.symm.trans htrM
    linear_combination (τ - 2 * a) * ht - 4 * hq'
  obtain ⟨y, hy⟩ := v0.2
  set v : Fin 3 → K := (v0 : Fin 3 → K) with hvdef
  have hvF : v = F *ᵥ y := by rw [← hy, Matrix.toLin'_apply]
  have hv : LinearIndependent K ![v, M *ᵥ v] := by
    have h := hv0.map' W.subtype (Submodule.ker_subtype W)
    have hfun : (W.subtype ∘ ![v0, g v0]) = ![v, M *ᵥ v] := by
      ext i : 1
      fin_cases i <;> simp [g, LinearMap.restrict_apply, Matrix.toLin'_apply, hvdef]
    rw [hfun] at h
    exact h
  have hQv0 : Q *ᵥ v = 0 := by rw [hvF, Matrix.mulVec_mulVec, hQF, Matrix.zero_mulVec]
  refine ⟨e, v, hMe, ?_, ?_⟩
  · have h := hQv v
    rw [hQv0] at h
    rw [eq_sub_iff_add_eq, ← sub_eq_zero, h]
    abel
  · have hEv : E *ᵥ v = 0 := by rw [hvF, Matrix.mulVec_mulVec, hEF, Matrix.zero_mulVec]
    have hEMv : E *ᵥ (M *ᵥ v) = 0 := by rw [Matrix.mulVec_mulVec, hEM, hEv]
    have hli : LinearIndependent K ![e, v, M *ᵥ v] := by
      change LinearIndependent K (Fin.cons e ![v, M *ᵥ v])
      refine linearIndependent_finCons.mpr ⟨hv, fun hmem => ?_⟩
      have hle : Submodule.span K (Set.range ![v, M *ᵥ v]) ≤ LinearMap.ker (Matrix.toLin' E) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i <;> simp [Matrix.toLin'_apply, hEv, hEMv]
      have h0 := hle hmem
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, hEe] at h0
      exact he0 h0
    have hu : IsUnit (Matrix.of ![e, v, M *ᵥ v]) := Matrix.linearIndependent_rows_iff_isUnit.mp hli
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIntegralRepDetectingInvariantSubspace
section
open Matrix

namespace UpperTheory.V

private def transl (R : Type) [CommRing R] {G : Type} [Group G] (g : G) : (G → R) →ₗ[R] (G → R) where
  toFun x := fun h => x (g⁻¹ * h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end UpperTheory.V

private theorem UpperTheory.sum_B_smul_pi_sum_smul_eq_sum_smul {G N : Type} [Group G] [Fintype G] [AddCommGroup N] [Module ℂ N]
    (π : Representation ℂ G N) {m : ℕ} (u : Fin m → G → ℂ) (B : G → Matrix (Fin m) (Fin m) ℂ)
    (hR : ∀ g i h, u i (g * h) = ∑ j, B g j i * u j h) (v : N) (g : G) (i : Fin m) :
    ∑ j, B g j i • π g (∑ h, u j h • π h v) = ∑ h, u i h • π h v := by
  have hπ : ∀ (a b : G) (y : N), π a (π b y) = π (a * b) y := fun a b y => by
    rw [map_mul]
    rfl
  calc _ = ∑ h, u i (g * h) • π (g * h) v := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp_rw [map_sum, map_smul, hπ, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun h _ => ?_)
        rw [← Finset.sum_smul, hR]
    _ = _ := Equiv.sum_comp (Equiv.mulLeft g) (fun h => u i h • π h v)

private theorem UpperTheory.sum_smul_pi_average_eq_card_smul_of_dual {G N : Type} [Group G] [Fintype G] [AddCommGroup N] [Module ℂ N]
    (π : Representation ℂ G N) {m : ℕ} (u : Fin m → G → ℂ) (B : G → Matrix (Fin m) (Fin m) ℂ)
    (hR : ∀ g i h, u i (g * h) = ∑ j, B g j i * u j h) (c : Fin m → G → ℂ)
    (hc : ∀ k j, ∑ h, c k h * u j h = if k = j then 1 else 0) (F : Fin m → N)
    (hF : ∀ g i, ∑ j, B g j i • π g (F j) = F i) (i : Fin m) :
    ∑ h, u i h • π h (∑ g, ∑ k, c k g⁻¹ • π g (F k)) = (Fintype.card G : ℂ) • F i := by
  have hπ : ∀ (a b : G) (y : N), π a (π b y) = π (a * b) y := fun a b y => by
    rw [map_mul]
    rfl
  have hinner : ∀ g k, ∑ h, u i h * c k (g⁻¹ * h) = B g k i := by
    intro g k
    rw [← Equiv.sum_comp (Equiv.mulLeft g)]
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
    simp_rw [hR, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    have hc' : ∀ j, ∑ h, u j h * c k h = if k = j then 1 else 0 := fun j => by
      rw [← hc k j]
      exact Finset.sum_congr rfl (fun h _ => mul_comm _ _)
    simp [hc']
  calc ∑ h, u i h • π h (∑ g, ∑ k, c k g⁻¹ • π g (F k))
      = ∑ h, ∑ g, ∑ k, (u i h * c k (g⁻¹ * h)) • π g (F k) := by
        refine Finset.sum_congr rfl (fun h _ => ?_)
        rw [← Equiv.sum_comp (Equiv.mulLeft h⁻¹)]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Equiv.coe_mulLeft, map_sum, map_smul, hπ, Finset.smul_sum, smul_smul,
          _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    _ = ∑ g, ∑ k, (∑ h, u i h * c k (g⁻¹ * h)) • π g (F k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_smul]
    _ = (Fintype.card G : ℂ) • F i := by
        simp_rw [hinner, hF]
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

private theorem UpperTheory.exists_dual_family_of_linearIndependent' (O : Type) [CommRing O] [IsDomain O] [Algebra O ℂ] [FaithfulSMul O ℂ]
    {G : Type} [Fintype G] {m : ℕ} (u : Fin m → G → O) (hu : LinearIndependent O u) :
    ∃ c : Fin m → G → ℂ, ∀ k j, ∑ h, c k h * algebraMap O ℂ (u j h) = if k = j then 1 else 0 := by
  classical
  letI : Algebra (FractionRing O) ℂ := FractionRing.liftAlgebra O ℂ
  haveI : IsScalarTower O (FractionRing O) ℂ := FractionRing.isScalarTower_liftAlgebra O ℂ
  let w : Fin m → G → FractionRing O := fun j h => algebraMap O (FractionRing O) (u j h)
  have hw : LinearIndependent (FractionRing O) w := by
    rw [← LinearIndependent.iff_fractionRing O (FractionRing O)]
    have hinj : Function.Injective
        (LinearMap.compLeft (Algebra.linearMap O (FractionRing O)) G) := by
      intro x y hxy
      funext h
      exact IsFractionRing.injective O (FractionRing O) (congrFun hxy h)
    exact hu.map' _ (LinearMap.ker_eq_bot.2 hinj)
  let f : (Fin m → FractionRing O) →ₗ[FractionRing O] (G → FractionRing O) :=
    { toFun := fun x => ∑ j, x j • w j
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.smul_sum, smul_smul] }
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    funext j
    exact Fintype.linearIndependent_iff.1 hw x hx j
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective f hf
  have hPw : ∀ j, P (w j) = fun k => if j = k then 1 else 0 := by
    intro j
    have h1 : f (fun k => if j = k then 1 else 0) = w j := by
      simp [f, ite_smul, Finset.sum_ite_eq]
    rw [← h1, ← LinearMap.comp_apply, hP, LinearMap.id_apply]
  refine ⟨fun k h => algebraMap (FractionRing O) ℂ (P (fun h' => if h = h' then 1 else 0) k), ?_⟩
  intro k j
  have hsum : ∑ h, w j h • (fun h' => if h = h' then (1 : FractionRing O) else 0) = w j :=
    (pi_eq_sum_univ (w j)).symm
  have h2 : ∑ h, P (fun h' => if h = h' then 1 else 0) k * w j h = if k = j then 1 else 0 := by
    have := congrFun (congrArg P hsum) k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, hPw] at this
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [eq_comm] at this
    simp only [mul_comm]
    rw [← this]
    simp [eq_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [IsScalarTower.algebraMap_apply O (FractionRing O) ℂ, ← map_mul, ← map_sum]
  rw [show (∑ h, P (fun h' => if h = h' then 1 else 0) k * algebraMap O (FractionRing O) (u j h))
    = if k = j then 1 else 0 from h2]
  split_ifs <;> simp

theorem UpperTheory.exists_integral_rep_detecting_invariant_subspace :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O ℂ] [FaithfulSMul O ℂ] (G : Type) [Group G] [Fintype G] (I : Submodule ℂ (G → ℂ)), (∀ g, ∀ x ∈ I, (fun h => x (g⁻¹ * h)) ∈ I) → I ≤ Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} → ∃ (m : ℕ) (τ : G →* GL (Fin m) O), ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N), (∃ F : Fin m → N, F ≠ 0 ∧ ∀ g i, ∑ j, algebraMap O ℂ (τ g i j) • π g (F j) = F i) ↔ ∃ x ∈ I, ∃ v, ∑ g, x g • π g v ≠ 0 := by
  intro O _ _ _ _ _ G _ _ I hI hspan
  classical
  let ι : (G → O) →ₗ[O] (G → ℂ) := LinearMap.compLeft (Algebra.linearMap O ℂ) G
  let Λ : Submodule O (G → O) := (I.restrictScalars O).comap ι
  obtain ⟨m, b⟩ := Submodule.basisOfPid (Pi.basisFun O G) Λ
  let T : G → (G → O) →ₗ[O] (G → O) := fun g => LinearMap.funLeft O O (fun h => g⁻¹ * h)
  have hT : ∀ g, ∀ y ∈ Λ, T g y ∈ Λ := by
    intro g y hy
    exact hI g _ hy
  let A : G → Matrix (Fin m) (Fin m) O := fun g => LinearMap.toMatrix b b ((T g).restrict (hT g))
  have hA1 : A 1 = 1 := by
    have e : (T 1).restrict (hT 1) = LinearMap.id := by
      refine LinearMap.ext fun y => Subtype.ext (funext fun h => ?_)
      simp [T, LinearMap.funLeft_apply, LinearMap.restrict_apply]
    simp only [A, e, LinearMap.toMatrix_id]
  have hAmul : ∀ g g', A (g * g') = A g * A g' := by
    intro g g'
    have e : (T (g * g')).restrict (hT _) = ((T g).restrict (hT g)).comp ((T g').restrict (hT g')) := by
      refine LinearMap.ext fun y => Subtype.ext (funext fun h => ?_)
      simp [T, LinearMap.funLeft_apply, LinearMap.restrict_apply, _root_.mul_inv_rev, mul_assoc]
    simp only [A, e]
    exact LinearMap.toMatrix_comp b b b _ _
  let τ0 : G →* Matrix (Fin m) (Fin m) O :=
    { toFun := fun g => (A g⁻¹)ᵀ
      map_one' := by simp [hA1]
      map_mul' := by
        intro g g'
        simp only [_root_.mul_inv_rev, hAmul, Matrix.transpose_mul] }
  have hRO : ∀ g i h, (b i : G → O) (g * h) = ∑ j, A g⁻¹ j i * (b j : G → O) h := by
    intro g i h
    have e := b.sum_repr ((T g⁻¹).restrict (hT g⁻¹) (b i))
    have e2 := congrArg (fun z : Λ => (z : G → O) h) e
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at e2
    have e3 : (((T g⁻¹).restrict (hT g⁻¹) (b i) : Λ) : G → O) h = (b i : G → O) (g * h) := by
      simp [T, LinearMap.funLeft_apply, LinearMap.restrict_apply]
    rw [← e3, ← e2]
    simp only [A, LinearMap.toMatrix_apply]
  let u' : Fin m → G → ℂ := fun j h => algebraMap O ℂ ((b j : G → O) h)
  let B : G → Matrix (Fin m) (Fin m) ℂ := fun g j i => algebraMap O ℂ (A g⁻¹ j i)
  have hR : ∀ g i h, u' i (g * h) = ∑ j, B g j i * u' j h := by
    intro g i h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [u', B, hRO, map_sum, map_mul]
  have hsp : I ≤ Submodule.span ℂ (Set.range u') := by
    refine hspan.trans (Submodule.span_le.2 ?_)
    rintro x ⟨hxI, hxO⟩
    simp only [RingHom.mem_range] at hxO
    choose y hy using hxO
    have hyΛ : y ∈ Λ := by
      show ι y ∈ I
      convert hxI using 1
      funext g
      exact hy g
    have e := b.sum_repr ⟨y, hyΛ⟩
    have hx : x = ∑ j, algebraMap O ℂ (b.repr ⟨y, hyΛ⟩ j) • u' j := by
      funext g
      have e2 := congrArg (fun z : Λ => (z : G → O) g) e
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at e2
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, u']
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hy g, ← e2, map_sum]
      simp [map_mul]
    rw [hx]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hli : LinearIndependent O (fun j => (b j : G → O)) :=
    b.linearIndependent.map' Λ.subtype (Submodule.ker_subtype _)
  obtain ⟨c, hc⟩ := UpperTheory.exists_dual_family_of_linearIndependent' O (fun j => (b j : G → O)) hli
  refine ⟨m, τ0.toHomUnits, ?_⟩
  intro N _ _ π
  constructor
  · rintro ⟨F, hF0, hF⟩
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hF0
    refine ⟨u' k, (b k).2, ∑ g, ∑ k, c k g⁻¹ • π g (F k), ?_⟩
    rw [UpperTheory.sum_smul_pi_average_eq_card_smul_of_dual π u' B hR c hc F (fun g i => hF g i) k]
    exact smul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero) hk
  · rintro ⟨x, hx, v, hv⟩
    refine ⟨fun j => ∑ h, u' j h • π h v, ?_, fun g i => UpperTheory.sum_B_smul_pi_sum_smul_eq_sum_smul π u' B hR v g i⟩
    intro hF0
    apply hv
    let Φ : (G → ℂ) →ₗ[ℂ] N :=
      { toFun := fun y => ∑ g, y g • π g v
        map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
        map_smul' := by intros; simp [Finset.smul_sum, smul_smul] }
    have hker : Submodule.span ℂ (Set.range u') ≤ LinearMap.ker Φ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      show Φ (u' j) = 0
      exact congrFun hF0 j
    exact hker (hsp hx)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ResidueIsIntegralOfAlgebraicOverDvr
section
private theorem UpperTheory.algebraic_over_finite_field_integral (k L : Type) [Field k] [Finite k] [Field L] [Algebra k L]
    (y : L) (h : IsAlgebraic k y) : IsIntegral ℤ y := by
  have hi : IsIntegral k y := h.isIntegral
  haveI : FiniteDimensional k (IntermediateField.adjoin k {y}) := IntermediateField.adjoin.finiteDimensional hi
  haveI : Finite (IntermediateField.adjoin k {y}) := Module.finite_of_finite k
  let g : ℕ → IntermediateField.adjoin k {y} := fun n =>
    ⟨y ^ (n + 1), pow_mem (IntermediateField.mem_adjoin_simple_self k y) _⟩
  obtain ⟨m, n, hmn, hg⟩ := Finite.exists_ne_map_eq_of_infinite g
  have hpow : y ^ (m + 1) = y ^ (n + 1) := congrArg Subtype.val hg
  rcases lt_or_gt_of_ne hmn with hlt | hlt
  · refine ⟨Polynomial.X ^ (n + 1) - Polynomial.X ^ (m + 1), Polynomial.monic_X_pow_sub ?_, ?_⟩
    · rw [Polynomial.degree_X_pow]
      exact_mod_cast Nat.succ_lt_succ hlt
    · simp [hpow]
  · refine ⟨Polynomial.X ^ (m + 1) - Polynomial.X ^ (n + 1), Polynomial.monic_X_pow_sub ?_, ?_⟩
    · rw [Polynomial.degree_X_pow]
      exact_mod_cast Nat.succ_lt_succ hlt
    · simp [hpow]

open Polynomial in
theorem UpperTheory.residue_isIntegral_of_algebraic_over_dvr :
    ∀ (A K : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] [Field K] (V : ValuationSubring K) (f : A →+* V), Function.Injective f → IsLocalHom f → ∀ x : V, (∃ p : Polynomial A, p ≠ 0 ∧ p.eval₂ (V.subtype.comp f) x = 0) → IsIntegral ℤ (IsLocalRing.residue V x) := by
  intro A K _ _ _ _ _ V f hf _ x hx
  classical
  obtain ⟨p, hp0, hpx⟩ := hx
  letI : NormalizationMonoid A := UniqueFactorizationMonoid.normalizationMonoid.toNormalizationMonoid
  letI : NormalizedGCDMonoid A := UniqueFactorizationMonoid.toNormalizedGCDMonoid A
  have hV : Polynomial.eval₂ f x p = 0 := by
    apply Subtype.val_injective
    rw [ZeroMemClass.coe_zero]
    exact (Polynomial.hom_eval₂ p f V.subtype x).trans hpx
  set q := p.primPart with hq
  have hcont : f p.content ≠ 0 := by
    intro h0
    apply hp0
    rw [← Polynomial.content_eq_zero_iff]
    exact hf (h0.trans (map_zero f).symm)
  have hqx : Polynomial.eval₂ f x q = 0 := by
    have e := Polynomial.eq_C_content_mul_primPart p
    rw [e, Polynomial.eval₂_mul, Polynomial.eval₂_C] at hV
    exact (mul_eq_zero.1 hV).resolve_left hcont
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hqbar : q.map (IsLocalRing.residue A) ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C π ∣ q := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have hi : IsLocalRing.residue A (q.coeff i) = 0 := by
        rw [← Polynomial.coeff_map, h0, Polynomial.coeff_zero]
      rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hi
      exact hi
    exact hπ.not_isUnit (Polynomial.isPrimitive_primPart p π hdvd)
  letI : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V) :=
    (IsLocalRing.ResidueField.map f).toAlgebra
  have halg : IsAlgebraic (IsLocalRing.ResidueField A) (IsLocalRing.residue V x) := by
    refine ⟨q.map (IsLocalRing.residue A), hqbar, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have e : (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V)).comp (IsLocalRing.residue A) =
        (IsLocalRing.residue V).comp f := by
      ext a
      exact IsLocalRing.ResidueField.map_residue f a
    rw [e, ← Polynomial.hom_eval₂, hqx, map_zero]
  exact UpperTheory.algebraic_over_finite_field_integral (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V) _ halg
end

