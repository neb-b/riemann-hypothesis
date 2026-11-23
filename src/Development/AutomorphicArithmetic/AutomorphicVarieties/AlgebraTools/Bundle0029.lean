module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetMin
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.exists_least_prime_detIdeal :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) → Nonempty ι →
      ∃ K : Ideal P, K.IsPrime ∧ detIdeal z m ≤ K ∧ ∀ Q : Ideal P, Q.IsPrime → detIdeal z m ≤ Q → K ≤ Q := by
  intro P _ _ ι _ _ z m h hι
  obtain ⟨c0⟩ := id hι
  refine ⟨genKer z m c0, (genKer_isPrime P ι z m h c0).1, (genKer_isPrime P ι z m h c0).2, ?_⟩
  intro Q hQ hle
  let f : P →+* FractionRing (P ⧸ Q) :=
    (algebraMap (P ⧸ Q) (FractionRing (P ⧸ Q))).comp (Ideal.Quotient.mk Q)
  have hf : ∀ x, f x = 0 ↔ x ∈ Q := by
    intro x
    simp only [f, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective (P ⧸ Q) (FractionRing (P ⧸ Q))),
      Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  have h1 : (z.map f).mulVec (fun j => f (m j)) = 0 := by
    funext i
    have hi : z.mulVec m i ∈ Q :=
      hle (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
    have h2 := (hf _).2 hi
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [Matrix.mulVec, dotProduct, map_sum, map_mul] using h2
  have h2 : (z.map f).det = 0 := by
    have hi : z.det ∈ Q := hle (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have h3 := (hf _).2 hi
    rw [RingHom.map_det] at h3
    exact h3
  obtain ⟨c, l, hc, hl, hz, hm⟩ := exists_kernel_vector _ V ι (z.map f) (fun j => f (m j)) h1 h2
  haveI : IsLocalRing V.toSubring := inferInstanceAs (IsLocalRing V)
  have hk := genKer_le_ker P ι z m h c V.toSubring (f.codRestrict V.toSubring hV)
    (fun j => ⟨l j, hl j⟩) (Subtype.ext hc) (by
      funext i
      apply Subtype.ext
      have h4 := congrFun hz i
      simpa [Matrix.mulVec, dotProduct] using h4) (fun j => Subtype.ext (hm j))
  rw [genKer_eq P ι z m h c0 c]
  intro x hx
  have h5 := hk hx
  rw [RingHom.mem_ker] at h5
  exact (hf x).1 (congrArg Subtype.val h5)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwPermMul
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem pm_conj_apply (R : Type) [CommRing R] {n : ℕ} (w : Equiv.Perm (Fin n)) (g : GL (Fin n) R)
    (a b : Fin n) :
    (((pm R n w)⁻¹ * g * pm R n w : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b =
      (g : Matrix (Fin n) (Fin n) R) (w a) (w b) := by
  have hinv : (pm R n w)⁻¹ = pm R n w⁻¹ := (map_inv _ _).symm
  rw [hinv, Units.val_mul, Units.val_mul, Matrix.mul_apply]
  simp [-map_inv, Matrix.mul_apply, pm_apply, Equiv.Perm.eq_inv_iff_eq, Equiv.eq_symm_apply]

private theorem pm_mem_KO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (w : Equiv.Perm (Fin n)) : pm k n w ∈ KO k (Fin n) := by
  refine ⟨pm 𝒪[k] n w, ?_⟩
  ext a b
  simp [pm_apply]

private theorem invLen_one (n : ℕ) : invLen (1 : Equiv.Perm (Fin n)) = 0 := by
  unfold invLen
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro p - ⟨h1, h2⟩
  exact lt_asymm h1 h2

theorem UpperTheory.V.AlgebraTools.permMul :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (w : Equiv.Perm (Fin n)) (i j : Fin n), (j : ℕ) = i + 1 → w⁻¹ i < w⁻¹ j → hk ρ (iwC k n C) (pm k n (Equiv.swap i j)) * hk ρ (iwC k n C) (pm k n w) = hk ρ (iwC k n C) (pm k n (Equiv.swap i j * w)) := by
  intro k _ _ _ _ n C A M _ _ _ ρ w i j hij hlt
  rw [map_mul]
  have hP := (heckePairIwC k n C).1
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  have hU : unipO k n ≤ iwC k n C := by
    unfold iwC
    exact le_sup_right.trans le_sup_left
  apply hkMul A _ M ρ _ _ _ hP
  · intro b hb
    obtain ⟨r, hr⟩ : ∃ r : 𝓀[k] → 𝒪[k], ∀ c, IsLocalRing.residue 𝒪[k] (r c) = c :=
      ⟨fun c => (IsLocalRing.residue_surjective c).choose,
        fun c => (IsLocalRing.residue_surjective c).choose_spec⟩
    obtain ⟨x, hx1, hx2, -, hx4⟩ := simpleOrbit k n C i j hij r hr
    obtain ⟨c, b', hb', he⟩ := hx4 b hb
    have hxc : x c ∈ unipB k (Fin n) ⊓ KO k (Fin n) := hx2 c
    have hmem : (pm k n w)⁻¹ * x c * pm k n w ∈ unipO k n := by
      unfold unipO
      refine Subgroup.mem_inf.2 ⟨(mem_unipB k).2 ⟨?_, ?_⟩, ?_⟩
      · intro a b hba
        rw [pm_conj_apply, hx1 c]
        have hab : w a ≠ w b := fun h => (ne_of_lt hba) (w.injective h).symm
        rw [Matrix.add_apply, Matrix.one_apply_ne hab, zero_add, Matrix.single_apply, if_neg]
        rintro ⟨h1, h2⟩
        apply absurd hlt
        rw [h1, h2]
        simpa using hba.le
      · intro a
        rw [pm_conj_apply, hx1 c]
        rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply, if_neg, add_zero]
        rintro ⟨h1, h2⟩
        exact hne (h1.trans h2.symm)
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (pm_mem_KO k w))
          (Subgroup.mem_inf.1 hxc).2) (pm_mem_KO k w)
    refine ⟨b', hb', (pm k n w)⁻¹ * x c * pm k n w, hU hmem, ?_⟩
    rw [he]
    group
  · rw [← map_mul, permCard, permCard, permCard, ((lenStep n w).1 i j hij).1 hlt]
    have hij' : (1 : Equiv.Perm (Fin n))⁻¹ i < (1 : Equiv.Perm (Fin n))⁻¹ j := by
      rw [inv_one]
      show i < j
      rw [Fin.lt_def]
      omega
    have h1 := ((lenStep n 1).1 i j hij).1 hij'
    rw [mul_one, invLen_one] at h1
    rw [h1]
    ring
end

