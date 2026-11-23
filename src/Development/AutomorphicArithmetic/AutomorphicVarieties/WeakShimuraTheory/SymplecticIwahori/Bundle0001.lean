module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.AdjMulSelf
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.ExtFg
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

open TensorProduct in
theorem UpperTheory.V.Ws.Pp.extFg :
    ∀ {B C K : Type} [CommRing B] [CommRing C] [Field K] [IsAlgClosed K] [Algebra B C] [Algebra.FiniteType B C] (q : Ideal C) [q.IsPrime] (f : B →+* K), RingHom.ker f = q.comap (algebraMap B C) → ∃ φ : C →+* K, φ.comp (algebraMap B C) = f := by
  intro B C K _ _ _ _ _ _ q _ f hf
  letI : Algebra B K := f.toAlgebra
  let p : Ideal B := q.comap (algebraMap B C)
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  have hunit : ∀ {L : Type} [Field L] (g : B →+* L), RingHom.ker g = p →
      ∃ g' : p.ResidueField →+* L, g'.comp (algebraMap B p.ResidueField) = g := by
    intro L _ g hg
    have h2 : p.primeCompl ≤ Submonoid.comap g (IsUnit.submonoid L) := by
      intro x hx
      have : g x ≠ 0 := fun h => hx (by rw [← hg]; exact h)
      exact (isUnit_iff_ne_zero.2 this)
    exact ⟨Ideal.ResidueField.lift p g hg.ge h2,
      RingHom.ext fun x => Ideal.ResidueField.lift_algebraMap p g hg.ge h2 x⟩
  obtain ⟨a, ha⟩ := hunit f hf
  obtain ⟨b, hb⟩ := hunit ((algebraMap C q.ResidueField).comp (algebraMap B C)) (by
    rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField])
  haveI hnt : Nontrivial (K ⊗[B] C) := by
    letI : Algebra p.ResidueField K := a.toAlgebra
    letI : Algebra p.ResidueField q.ResidueField := b.toAlgebra
    haveI : IsScalarTower B p.ResidueField K := IsScalarTower.of_algebraMap_eq' ha.symm
    let T := K ⊗[p.ResidueField] q.ResidueField
    haveI : Nontrivial T := inferInstance
    let u : K →ₐ[B] T := (Algebra.TensorProduct.includeLeft : K →ₐ[B] T)
    let v : C →ₐ[B] T :=
      { toRingHom := ((Algebra.TensorProduct.includeRight : q.ResidueField →ₐ[p.ResidueField] T) : q.ResidueField →+* T).comp (algebraMap C q.ResidueField)
        commutes' := fun x => by
          have h1 : algebraMap C q.ResidueField (algebraMap B C x) =
              algebraMap p.ResidueField q.ResidueField (algebraMap B p.ResidueField x) :=
            (RingHom.congr_fun hb x).symm
          show (Algebra.TensorProduct.includeRight : q.ResidueField →ₐ[p.ResidueField] T) (algebraMap C q.ResidueField (algebraMap B C x)) = _
          rw [h1, AlgHom.commutes, ← IsScalarTower.algebraMap_apply] }
    exact (Algebra.TensorProduct.lift u v (fun _ _ => Commute.all _ _)).toRingHom.domain_nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[B] C)
  letI : Field ((K ⊗[B] C) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite K ((K ⊗[B] C) ⧸ m) := finite_of_finite_type_of_isJacobsonRing _ _
  have hbij : Function.Bijective (algebraMap K ((K ⊗[B] C) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ψ : ((K ⊗[B] C) ⧸ m) →ₐ[K] K := (AlgEquiv.ofBijective (Algebra.ofId K _) hbij).symm.toAlgHom
  let χ : (K ⊗[B] C) →ₐ[K] K := ψ.comp (Ideal.Quotient.mkₐ K m)
  refine ⟨(χ : K ⊗[B] C →+* K).comp ((Algebra.TensorProduct.includeRight : C →ₐ[B] K ⊗[B] C) : C →+* K ⊗[B] C), ?_⟩
  ext x
  show χ ((Algebra.TensorProduct.includeRight : C →ₐ[B] K ⊗[B] C) (algebraMap B C x)) = f x
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply B K (K ⊗[B] C), AlgHom.commutes]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.GramCore
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

private theorem gram_core {R : Type} [CommRing R] (Q : M4 R) (hQ : IsUp Q) (a' d' : R)
    (ha : Q 0 0 * a' = 1) (hd : Q 1 1 * d' = 1)
    (h33 : Q 3 3 = Q 0 0) (h22 : Q 2 2 = Q 1 1) (h23 : Q 2 3 = Q 0 1) (h13 : Q 1 3 = - Q 0 2)
    (h03 : Q 0 3 = 0) (h12 : Q 1 2 = 0) :
    ∃ t : M4 R, IsUp t ∧ adj t * Q * t = 1 := by
  have h10 := hQ 1 0 (by decide)
  have h20 := hQ 2 0 (by decide)
  have h21 := hQ 2 1 (by decide)
  have h30 := hQ 3 0 (by decide)
  have h31 := hQ 3 1 (by decide)
  have h32 := hQ 3 2 (by decide)
  refine ⟨!![a', -(a' * (Q 0 1 * d')), -(a' * Q 0 2), 0; 0, d', 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, h10, h20, h21, h30, h31, h32,
        h33, h22, h23, h13, h03, h12]
    all_goals first
      | linear_combination ha
      | linear_combination hd
      | linear_combination (-(Q 0 1 * d')) * ha
      | linear_combination (-Q 0 2) * ha
      | linear_combination (Q 0 2) * ha

theorem UpperTheory.V.Ws.Pp.gram :
    ∀ {R : Type} [CommRing R] (k : (M4 R)ˣ), IsUp (adj (k : M4 R) * (k : M4 R)) → ∃ t : (M4 R)ˣ, IsUp (t : M4 R) ∧ IsGSp (1 : R) ((k : M4 R) * (t : M4 R)) := by
  intro R _ k hQ
  have hinv : adj (k : M4 R) * adj ((k⁻¹ : (M4 R)ˣ) : M4 R) = 1 := by
    rw [← (grp R).1, Units.inv_mul, (grp R).2.2.2.2.1]
  have hdet : IsUnit (adj (k : M4 R) * (k : M4 R)).det := by
    apply Matrix.isUnit_det_of_right_inverse
      (B := ((k⁻¹ : (M4 R)ˣ) : M4 R) * adj ((k⁻¹ : (M4 R)ˣ) : M4 R))
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (k : M4 R), Units.mul_inv, Matrix.one_mul, hinv]
  rw [Matrix.det_of_upperTriangular (fun i j h => hQ i j h), Fin.prod_univ_four] at hdet
  obtain ⟨a', ha⟩ := (isUnit_of_mul_isUnit_left
    (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hdet))).exists_right_inv
  obtain ⟨d', hd⟩ := (isUnit_of_mul_isUnit_right
    (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hdet))).exists_right_inv
  obtain ⟨t, ht, htQ⟩ := gram_core _ hQ a' d' ha hd
    (by simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn] <;> ring)
    (by simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn] <;> ring)
    (by simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn] <;> ring)
    (by simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn] <;> ring)
    (by simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn] <;> ring)
    (by simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn] <;> ring)
  refine ⟨⟨t, adj t * (adj (k : M4 R) * (k : M4 R)), mul_eq_one_comm.mp htQ, htQ⟩, ht, ?_⟩
  show adj ((k : M4 R) * t) * ((k : M4 R) * t) = (1 : R) • 1
  rw [(grp R).1, one_smul, ← htQ]
  simp only [Matrix.mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.NilPoly
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

theorem UpperTheory.V.Ws.Pp.nilPoly :
    ∀ {B S : Type} [CommRing B] [IsLocalRing B] [CommRing S] [IsLocalRing S] [Algebra B S] [Module.Finite B S] (v : S), v ∈ maximalIdeal S → ∃ p : B[X], Dist (maximalIdeal B) p ∧ aeval v p = 0 := by
  intro B S _ _ _ _ _ _ v hv
  have hrad : v ∈ ((maximalIdeal B).map (algebraMap B S)).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro J hJ'
    obtain ⟨hJ, hJp⟩ := hJ'
    have hle : maximalIdeal B ≤ Ideal.comap (algebraMap B S) J := by
      intro b hb
      exact hJ (Ideal.mem_map_of_mem _ hb)
    have hc : Ideal.comap (algebraMap B S) J = maximalIdeal B :=
      ((IsLocalRing.maximalIdeal.isMaximal B).eq_of_le (Ideal.comap_ne_top _ hJp.ne_top) hle).symm
    have hcm : (Ideal.comap (algebraMap B S) J).IsMaximal := by
      rw [hc]
      exact IsLocalRing.maximalIdeal.isMaximal B
    have hJm : J.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := B) J hcm
    rw [IsLocalRing.eq_maximalIdeal hJm]
    exact hv
  obtain ⟨n, hn⟩ := hrad
  have hN : v ^ (n + 1) ∈ (maximalIdeal B).map (algebraMap B S) := by
    rw [pow_succ]
    exact Ideal.mul_mem_right _ _ hn
  have hrange : LinearMap.range (Algebra.lmul B S (v ^ (n + 1))) ≤
      (maximalIdeal B) • (⊤ : Submodule B S) := by
    rintro _ ⟨s, rfl⟩
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    simpa using Ideal.mul_mem_right s _ hN
  obtain ⟨p, hpm, -, hpc, hpa⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
      (R := B) (M := S) (Algebra.lmul B S (v ^ (n + 1))) (maximalIdeal B) hrange
  refine ⟨expand B (n + 1) p, ⟨hpm.expand (Nat.succ_pos n), ?_⟩, ?_⟩
  · intro k hk
    rw [natDegree_expand] at hk
    rw [coeff_expand (Nat.succ_pos n)]
    split_ifs with hd
    · have hlt : k / (n + 1) < p.natDegree := by
        rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos n)]
        exact hk
      exact Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hlt) (hpc _)
    · exact zero_mem _
  · rw [expand_aeval]
    rw [Polynomial.aeval_algHom_apply] at hpa
    have h1 := LinearMap.congr_fun hpa 1
    simpa using h1
end

