module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle0006
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfLoZero
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle0005

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.LamAddC
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.QB

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

theorem multiInv {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (r : ℕ)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A)
    (hv : ∀ l j : Fin (r + 1 + 1), l < j → colAddGen A l j v = rename some v)
    (θ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A →ₐ[A] S) (e : Fin r → S) (J : Finset (Fin r)) :
    aeval (fun w : Fin (r + 1 + 1) × Fin (r + 1 + 1) =>
      θ (X w) + (∑ j ∈ J, if w.2 = midI r j then e j else 0) * θ (X (w.1, 0))) v = θ v := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, zero_mul, add_zero]
    exact (congrArg (fun ψ => ψ v) (MvPolynomial.aeval_unique θ)).symm
  | @insert j0 J hj0 ih =>
    have h0 := hv 0 (midI r j0) (Fin.succ_pos _)
    set f : Fin (r + 1 + 1) × Fin (r + 1 + 1) → S := fun w =>
      θ (X w) + (∑ j ∈ J, if w.2 = midI r j then e j else 0) * θ (X (w.1, 0)) with hf
    have hz : ∀ j : Fin r, ((0 : Fin (r + 1 + 1)) = midI r j) ↔ False :=
      fun j => ⟨fun h => Fin.succ_ne_zero _ h.symm, False.elim⟩
    have hφ : (aeval (Option.elim' (e j0) f)).comp (colAddGen A 0 (midI r j0)) =
        aeval (fun w : Fin (r + 1 + 1) × Fin (r + 1 + 1) =>
          θ (X w) + (∑ j ∈ insert j0 J, if w.2 = midI r j then e j else 0) * θ (X (w.1, 0))) := by
      rw [colAddGen, MvPolynomial.comp_aeval]
      congr 1
      funext w
      by_cases hw : w.2 = midI r j0
      · simp [hw, hf, Finset.sum_insert hj0, hz]
        try ring
      · simp [hw, hf, Finset.sum_insert hj0, hz]
        try ring
    rw [← hφ, AlgHom.comp_apply, h0, MvPolynomial.aeval_rename]
    exact ih

variable {K : Type} [Field K] {r : ℕ}

theorem caseC (j0 : Fin r) (c : K) (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : ∀ l j : Fin (r + 1 + 1), l < j → colAddGen K l j v = rename some v) :
    psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) (colAdd K 0 (midI r j0) c) (th K r b v) = th K r b v := by
  classical

  have hmidOf_midI : ∀ j : Fin r, midOf (midI r j) = some j := by
    intro j
    unfold midOf midI
    rw [dite_eq_left (by first | (simp [Fin.val_succ]; done) | (simp [Fin.val_succ]; omega))]
    exact congrArg some (Fin.ext (by simp [Fin.val_succ]))
  have hsome : ∀ (t : Fin (r + 1 + 1)) (j : Fin r), midOf t = some j → t = midI r j := by
    intro t j h
    unfold midOf at h
    split_ifs at h with h1
    cases h
    apply Fin.ext
    simp [midI, Fin.val_succ]
    omega
  have hnone : ∀ (t : Fin (r + 1 + 1)) (j : Fin r), midOf t = none → t ≠ midI r j := by
    intro t j h ht
    rw [ht, hmidOf_midI] at h
    cases h
  have h00 : midOf (0 : Fin (r + 1 + 1)) = none := by
    unfold midOf
    rw [dite_eq_right (by simp)]
  have hth0 : ∀ a, th K r b (X (a, 0)) = X (a, 0) := by
    intro a
    simp [th, Formalism.MainNotions.flipOneThree.Pf.subY, h00]
  let e : Fin r → MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K) :=
    fun j => C (C c * X (b, (j0, j)))
  have hmult := multiInv r v hv (th K r b) e Finset.univ
  have key : (psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) (colAdd K 0 (midI r j0) c)).comp (th K r b).toRingHom =
      (aeval (fun w : Fin (r + 1 + 1) × Fin (r + 1 + 1) =>
        th K r b (X w) + (∑ j ∈ Finset.univ, if w.2 = midI r j then e j else 0) * th K r b (X (w.1, 0)))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp [th, psiB, MvPolynomial.algebraMap_apply]
    · rintro ⟨a, t⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, hth0]
      rcases hw : midOf t with _ | j
      · have e1 : th K r b (X (a, t)) = X (a, t) := by simp [th, Formalism.MainNotions.flipOneThree.Pf.subY, hw]
        have hz : (∑ j ∈ Finset.univ, if t = midI r j then e j else 0) = 0 :=
          Finset.sum_eq_zero fun j _ => if_neg (hnone t j hw)
        rw [e1, hz, zero_mul, add_zero]
        simp [psiB, Formalism.GradedWeylDivisibility.colAdd, hnone t j0 hw]
      · have ht : t = midI r j := hsome t j hw
        subst ht
        have e1 : th K r b (X (a, midI r j)) = ∑ i : Fin r, C (X (b, (i, j))) * X (a, midI r i) := by
          simp [th, Formalism.MainNotions.flipOneThree.Pf.subY, hmidOf_midI, Formalism.GradedWeylDivisibility.blockEmb]
        have hz : (∑ j' ∈ Finset.univ, if midI r j = midI r j' then e j' else 0) = e j := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro j' _ hj'
            rw [if_neg]
            intro h
            apply hj'
            have := congrArg midOf h
            rw [hmidOf_midI, hmidOf_midI] at this
            exact (Option.some_injective _ this).symm
          · simp
        have hmid : ∀ i : Fin r, i ≠ j0 → midI r i ≠ midI r j0 := by
          intro i hi h
          apply hi
          have h2 := congrArg midOf h
          rw [hmidOf_midI, hmidOf_midI] at h2
          exact Option.some_injective _ h2
        have hterm : ∀ i : Fin r, psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) (colAdd K 0 (midI r j0) c)
            (C (X (b, (i, j))) * X (a, midI r i)) =
            C (X (b, (i, j))) * X (a, midI r i) + (if i = j0 then e j * X (a, 0) else 0) := by
          intro i
          simp only [psiB, map_mul, coe_eval₂Hom, eval₂_C, eval₂_X, Formalism.GradedWeylDivisibility.colAdd, aeval_X]
          by_cases hi : i = j0
          · subst hi
            simp [e, MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
            ring
          · simp [hmid i hi, hi]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [e1, hz, map_sum, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
        simp
  exact (RingHom.congr_fun key v).trans hmult

theorem lam_addC (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) (j0 : Fin r) (c : K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : ∀ l j : Fin (r + 1 + 1), l < j → colAddGen K l j v = rename some v)
    (ht : ∀ l j : Fin (r + 1 + 1), l < j → colAddGen K l j t = rename some t) :
    colAdd K 0 (midI r j0) c (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      lamOf K r L (blockEmb K true v * blockEmb K false t) := by
  rw [lam_eq, lcoef_comm, map_mul, caseC j0 c true v hv, caseC j0 c false t ht]

end Formalism.MainNotions.flipOneThree.Pf.QB

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.RowActTransv
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.QB

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

variable {K : Type} [Field K] {r : ℕ}

theorem caseN (t0 : Fin (r + 1 + 1)) (h0 : midOf t0 = none) (c : K) (b : Bool)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) (scCol K (r + 1 + 1) t0 c) (th K r b v) =
      th K r b (scCol K (r + 1 + 1) t0 c v) := by
  have key := hom_eq_on
    ((psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) (scCol K (r + 1 + 1) t0 c)).comp (th K r b).toRingHom)
    ((th K r b).toRingHom.comp (scCol K (r + 1 + 1) t0 c).toRingHom) ?_ ?_ v
  · simpa using key
  · intro a
    simp [th_C, psiB_C]
  · rintro ⟨a, t⟩
    rcases midOf_cases t with ⟨j, rfl⟩ | ⟨ht, -⟩
    · have hne : ∀ i : Fin r, midI r i ≠ t0 := fun i => midOf_none_ne h0 i
      set_option synthInstance.maxHeartbeats 100000 in
        simp [th_X_mid, psiB_X, scCol_X, hne, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [psiB_C]
    · simp [th_X_none _ _ _ _ _ ht, psiB_X, scCol_X]

theorem lam_scaleN (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) (t0 : Fin (r + 1 + 1)) (h0 : midOf t0 = none)
    (c : K) (ν ν' : Fin (r + 1 + 1) → ℕ) (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : IsWeightedHomogeneous (colW (r + 1 + 1) (r + 1 + 1)) v ν)
    (ht : IsWeightedHomogeneous (colW (r + 1 + 1) (r + 1 + 1)) t ν') :
    scCol K (r + 1 + 1) t0 c (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      c ^ (ν t0 + ν' t0) • lamOf K r L (blockEmb K true v * blockEmb K false t) := by
  rw [lam_eq, lcoef_comm, map_mul, caseN t0 h0, caseN t0 h0, scCol_of_hom _ _ _ _ hv, scCol_of_hom _ _ _ _ ht,
    map_smul, map_smul, smul_mul_smul_comm, ← pow_add, map_smul]

def thR (K : Type) [Field K] (r : ℕ) (ρ : MvPolynomial (Fin r × Fin r) K →ₐ[K] MvPolynomial (Fin r × Fin r) K) (b : Bool) :
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K →ₐ[K]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K) :=
  (mapAlgHom ((blockEmb K (k := r) (n := r) b).comp ρ)).comp (subY K r)

theorem thR_coeff (ρ : MvPolynomial (Fin r × Fin r) K →ₐ[K] MvPolynomial (Fin r × Fin r) K) (b : Bool)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ) :
    AddMonoidAlgebra.coeff (thR K r ρ b v) u = blockEmb K b (ρ (AddMonoidAlgebra.coeff (subY K r v) u)) := by
  simp only [thR, AlgHom.comp_apply, mAH_coeff]

theorem caseM (ψ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K →ₐ[K] MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (ρ : MvPolynomial (Fin r × Fin r) K →ₐ[K] MvPolynomial (Fin r × Fin r) K)
    (hgen : ∀ (b : Bool) (a : Fin (r + 1 + 1)) (j' : Fin r),
      ∑ i : Fin r, (C (X (b, (i, j'))) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)) *
          map (algebraMap K (MvPolynomial (Bool × (Fin r × Fin r)) K)) (ψ (X (a, midI r i))) =
        ∑ i : Fin r, C (blockEmb K b (ρ (X (i, j')))) * X (a, midI r i))
    (hnone : ∀ a t, midOf t = none → ψ (X (a, t)) = X (a, t)) (b : Bool)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) ψ (th K r b v) = thR K r ρ b v := by
  have key := hom_eq_on
    ((psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) ψ).comp (th K r b).toRingHom)
    (thR K r ρ b).toRingHom ?_ ?_ v
  · simpa using key
  · intro a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, th_C]
    rw [psiB_C]
    simp only [thR, AlgHom.comp_apply, subY_C, mAH_C, AlgHom.commutes]
    simp
  · rintro ⟨a, t⟩
    rcases midOf_cases t with ⟨j, rfl⟩ | ⟨ht, -⟩
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, th_X_mid, map_sum, map_mul]
      simp only [thR, AlgHom.comp_apply, mAH_subY_mid]
      rw [← hgen b a j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [psiB_C, psiB_X]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, th_X_none _ _ _ _ _ ht]
      simp only [thR, AlgHom.comp_apply, mAH_subY_none _ _ _ _ ht]
      rw [psiB_X, hnone a t ht, map_X]

theorem lam_caseM (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) (N : ℕ) (α α' : Fin r → ℕ)
    (hInv : PhInv K r N α α' L)
    (ψ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K →ₐ[K] MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (l : Matrix (Fin r) (Fin r) K) (hl : IsUnit l.det)
    (hgen : ∀ (b : Bool) (a : Fin (r + 1 + 1)) (j' : Fin r),
      ∑ i : Fin r, (C (X (b, (i, j'))) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)) *
          map (algebraMap K (MvPolynomial (Bool × (Fin r × Fin r)) K)) (ψ (X (a, midI r i))) =
        ∑ i : Fin r, C (blockEmb K b (rowAct K l (X (i, j')))) * X (a, midI r i))
    (hnone : ∀ a t, midOf t = none → ψ (X (a, t)) = X (a, t))
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : ∀ u, AddMonoidAlgebra.coeff (subY K r v) u ∈ dualWeyl K r r α) (ht : ∀ u, AddMonoidAlgebra.coeff (subY K r t) u ∈ dualWeyl K r r α') :
    ψ (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      l.det ^ N • lamOf K r L (blockEmb K true v * blockEmb K false t) := by
  have hc : ∀ (h : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K))
      (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ), AddMonoidAlgebra.coeff (lcoef L h) u = L (AddMonoidAlgebra.coeff h u) := by
    intro h u
    exact coeff_sum_monomial_linear L h u
  rw [lam_eq, lcoef_comm, map_mul, caseM ψ (rowAct K l) hgen hnone, caseM ψ (rowAct K l) hgen hnone]
  ext u
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_smul, hc, hc, coeff_mul, coeff_mul, map_sum, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [thR_coeff, thR_coeff, th_coeff, th_coeff]
  exact hInv l hl _ (hv p.1) _ (ht p.2)

theorem lam_scaleM (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) (N : ℕ) (α α' : Fin r → ℕ)
    (hInv : PhInv K r N α α' L) (j : Fin r) (c : K) (hc : c ≠ 0)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : ∀ u, AddMonoidAlgebra.coeff (subY K r v) u ∈ dualWeyl K r r α) (ht : ∀ u, AddMonoidAlgebra.coeff (subY K r t) u ∈ dualWeyl K r r α') :
    scCol K (r + 1 + 1) (midI r j) c (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      c ^ N • lamOf K r L (blockEmb K true v * blockEmb K false t) := by
  classical
  have hdet : (Matrix.diagonal (fun i : Fin r => if i = j then c else 1)).det = c := by
    rw [Matrix.det_diagonal, Finset.prod_ite_eq']
    simp
  have key := lam_caseM L N α α' hInv (scCol K (r + 1 + 1) (midI r j) c)
    (Matrix.diagonal (fun i : Fin r => if i = j then c else 1)) (by rw [hdet]; exact hc.isUnit) ?_ ?_ v t hv ht
  · rw [hdet] at key
    exact key
  · intro b a j'
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [scCol_X, midI_inj, rowAct, aeval_X, Matrix.diagonal_apply, blockEmb, map_mul, map_C, map_X,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, rename_C, rename_X]
    rw [Finset.sum_eq_single i (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
    simp only [if_true, MvPolynomial.algebraMap_eq]
    ring
  · intro a t' ht'
    rw [scCol_X]
    have hne : t' ≠ midI r j := fun e => midOf_none_ne ht' j e.symm
    simp [hne]

theorem rowAct_transv (l j : Fin r) (c : K) (i t : Fin r) :
    rowAct K (Matrix.transvection l j c) (X (i, t)) = X (i, t) + if i = l then C c * X (j, t) else 0 := by
  classical
  simp only [rowAct, aeval_X, Matrix.transvection, Matrix.add_apply, Matrix.one_apply]
  simp only [map_add (f := _), add_mul, Finset.sum_add_distrib, apply_ite C, ite_mul, map_one, map_zero, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  by_cases h : i = l
  · subst h
    simp only [Matrix.single_apply, true_and]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · have h' : ¬ l = i := fun e => h e.symm
    simp [Matrix.single_apply, h, h']

theorem lam_addM (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) (N : ℕ) (α α' : Fin r → ℕ)
    (hInv : PhInv K r N α α' L) (l j : Fin r) (hlj : l ≠ j) (c : K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : ∀ u, AddMonoidAlgebra.coeff (subY K r v) u ∈ dualWeyl K r r α) (ht : ∀ u, AddMonoidAlgebra.coeff (subY K r t) u ∈ dualWeyl K r r α') :
    colAdd K (midI r l) (midI r j) c (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      lamOf K r L (blockEmb K true v * blockEmb K false t) := by
  classical
  have hdet : (Matrix.transvection l j c).det = 1 := Matrix.det_transvection_of_ne l j hlj c
  have key := lam_caseM L N α α' hInv (colAdd K (midI r l) (midI r j) c) (Matrix.transvection l j c)
    (by rw [hdet]; exact isUnit_one) ?_ ?_ v t hv ht
  · rw [hdet, one_pow, one_smul] at key
    exact key
  · intro b a j'
    simp only [rowAct_transv, colAdd, aeval_X, midI_inj]
    have e : ∀ i : Fin r, (if i = j then X (a, midI r i) + C c * X (a, midI r l) else X (a, midI r i) :
        MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) =
        X (a, midI r i) + if i = j then C c * X (a, midI r l) else 0 := by
      intro i
      split_ifs <;> simp
    simp only [e, map_add (f := _), map_mul, map_C, map_X, blockEmb, rename_X, rename_C, mul_add, add_mul,
      Finset.sum_add_distrib, apply_ite, map_zero, mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hs : ∀ (k : Fin r)
        (f g : Fin r → MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)),
        (∑ x : Fin r, if x = k then f x + g x else f x + 0) = (∑ x : Fin r, f x) + g k := by
      intro k f g
      have h1 : ∀ x, (if x = k then f x + g x else f x + 0) = f x + if x = k then g x else 0 := by
        intro x
        split_ifs <;> simp
      simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hs j (fun x => C (X (b, x, j')) * X (a, midI r x))
        (fun x => C (X (b, x, j')) * (C ((algebraMap K (MvPolynomial (Bool × Fin r × Fin r) K)) c) * X (a, midI r l))),
      hs l (fun x => C (X (b, x, j')) * X (a, midI r x)) (fun x => C (C c) * C (X (b, j, j')) * X (a, midI r x))]
    simp only [MvPolynomial.algebraMap_eq]
    ring
  · intro a t' ht'
    have hne : t' ≠ midI r j := fun e => midOf_none_ne ht' j e.symm
    simp [colAdd, hne]

end Formalism.MainNotions.flipOneThree.Pf.QB

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.SubYDPsiMonomial
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem midOf_zero (r : ℕ) : midOf (0 : Fin (r + 1 + 1)) = none := by
  unfold midOf
  rw [dite_eq_right]
  simp

theorem subY_X_zero (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) : subY A r (X (a, 0)) = X (a, 0) := by
  simp only [subY, aeval_X, midOf_zero]

theorem subY_X_mid (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) (j : Fin r) :
    subY A r (X (a, midI r j)) = ∑ i : Fin r, C (X (i, j)) * X (a, midI r i) := by
  simp only [subY, aeval_X, midOf_midI]

def dOneY (A : Type) [CommRing A] (r : ℕ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A)) :=
  fun s t => Fin.cases (Fin.cases 1 (fun _ => 0) t) (fun s' => Fin.cases 0 (fun t' => C (X (s', t'))) t) s

theorem det_dOneY (A : Type) [CommRing A] (r : ℕ) : (dOneY A r).det = C (detY A r) := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h0 : ∀ i : Fin r, dOneY A r i.succ 0 = 0 := fun i => rfl
  have h1 : dOneY A r 0 0 = 1 := rfl
  simp only [h0, h1, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
  unfold detY
  have h := RingHom.map_det (C : MvPolynomial (Fin r × Fin r) A →+*
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A))
    (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))
  refine Eq.trans ?_ h.symm
  congr 1

theorem subY_covY (K : Type) [Field K] (r : ℕ) (i : Fin (r + 1 + 1)) :
    subY K r (covY K (r + 1) i) = C (detY K r) * map C (covY K (r + 1) i) := by
  unfold covY
  rw [map_mul, map_mul, map_pow, map_pow, map_neg, map_neg, map_one, map_one]
  have hA := AlgHom.map_det (subY K r)
    (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K))
  have hB := RingHom.map_det (map (C : K →+* MvPolynomial (Fin r × Fin r) K))
    (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K))
  have hM : (subY K r).mapMatrix
      (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) =
      (map (C : K →+* MvPolynomial (Fin r × Fin r) K)).mapMatrix
        (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) *
        dOneY K r := by
    apply Matrix.ext
    intro a b
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    induction b using Fin.cases with
    | zero =>
      have h0 : ∀ s : Fin r, dOneY K r s.succ 0 = 0 := fun s => rfl
      have h1 : dOneY K r 0 0 = 1 := rfl
      simp only [h0, h1, mul_zero, Finset.sum_const_zero, add_zero, mul_one]
      show subY K r (X (i.succAbove a, (0 : Fin (r + 1)).castSucc)) = map C (X (i.succAbove a, (0 : Fin (r + 1)).castSucc))
      rw [Fin.castSucc_zero, subY_X_zero, map_X]
    | succ j =>
      have h0 : dOneY K r 0 j.succ = 0 := rfl
      have h1 : ∀ s : Fin r, dOneY K r s.succ j.succ = C (X (s, j)) := fun s => rfl
      simp only [h0, h1, mul_zero, zero_add]
      show subY K r (X (i.succAbove a, j.succ.castSucc)) =
        ∑ s : Fin r, map C (X (i.succAbove a, s.succ.castSucc)) * C (X (s, j))
      have e : ∀ s : Fin r, s.succ.castSucc = midI r s := fun s => (Fin.succ_castSucc s).symm
      simp only [e, map_X]
      rw [subY_X_mid]
      exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have hdet : subY K r (Matrix.det fun a b : Fin (r + 1) =>
      (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) =
      C (detY K r) * map C (Matrix.det fun a b : Fin (r + 1) =>
      (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) := by
    refine hA.trans ?_
    rw [hM, Matrix.det_mul, det_dOneY, mul_comm]
    congr 1
    exact hB.symm
  rw [hdet]
  ring

theorem subY_dPsi_monomial (K : Type) [Field K] (r : ℕ) (v : XY (r + 1 + 1) →₀ ℕ) (c : K) :
    subY K r (deltaB K (r + 1) (PsiXY K (r + 1) (monomial v c))) =
      C (detY K r ^ yDeg v) * map C (deltaB K (r + 1) (PsiXY K (r + 1) (monomial v c))) := by
  have hx : ∀ i : Fin (r + 1 + 1), deltaB K (r + 1) (PsiXY K (r + 1) (X (Sum.inl i))) = X (i, 0) := by
    intro i
    simp [PsiXY, deltaB]
  have hy : ∀ i : Fin (r + 1 + 1), deltaB K (r + 1) (PsiXY K (r + 1) (X (Sum.inr i))) = covY K (r + 1) i := by
    intro i
    simp only [PsiXY, deltaB, aeval_X, Sum.elim_inr, rename_rename]
    have : (Prod.snd ∘ Prod.mk false : Fin (r + 1 + 1) × Fin (r + 1 + 1) → Fin (r + 1 + 1) × Fin (r + 1 + 1)) = id := rfl
    rw [this, rename_id_apply]
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, hx, hy, subY_X_zero, subY_covY, mul_pow, Finset.prod_mul_distrib, map_X]
  have hC : subY K r (deltaB K (r + 1) (PsiXY K (r + 1) (C c))) = map C (deltaB K (r + 1) (PsiXY K (r + 1) (C c))) := by
    simp only [← algebraMap_eq, AlgHom.commutes]
    simp [algebraMap_eq]
  rw [hC]
  have hp : ∏ i : Fin (r + 1 + 1), (C (detY K r) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1))
      (MvPolynomial (Fin r × Fin r) K)) ^ v (Sum.inr i) = C (detY K r) ^ yDeg v := by
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hp]
  ring

theorem subMuP_of (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) : SubMuP := by
  intro p n' R r hr P Q F hF
  rw [← tie3 h2 h5 hCO R (r + 1) (by omega) P Q] at hF
  obtain ⟨f, hf, rfl⟩ := hF
  rw [dPsi_apply, f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [subY_dPsi_monomial, (hf v hv).2]

end Formalism.MainNotions.flipOneThree.Pf

end
end

