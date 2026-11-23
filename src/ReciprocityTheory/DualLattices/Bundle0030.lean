module

public import ReciprocityTheory.DualLattices.Bundle0027
public import ReciprocityTheory.DualLattices.Bundle0021
public import ReciprocityTheory.DualLattices.PowMemCarrier
public import ReciprocityTheory.DualLattices.Bundle0010
public import ReciprocityTheory.DualLattices.Bundle0017

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.FormMonomialUnitVector
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.UnitVectorPowers

open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

section Res

variable [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) p]

def Lk (D : Lifts H U X) : Matrix (Ix g) (Ix g) (IsLocalRing.ResidueField R) :=
  D.Λ.map (IsLocalRing.residue R)

def Mk (D : Lifts H U X) : Matrix (Ix g) (Ix g) (IsLocalRing.ResidueField R) :=
  (Lk D).map (fun a => a ^ p) * (Lk D)⁻¹

theorem Lk_det (D : Lifts H U X) : IsUnit (Lk D).det := by
  unfold Lk
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact D.Λ_det.map _

theorem lam_p (D : Lifts H U X) (j : Ix g) (y : Nb p g) :
    lam (Lk D) j y ^ p = ∑ l, Mk D j l * lam (Lk D) l y := by
  have hinv : (Lk D)⁻¹ * Lk D = 1 := Matrix.nonsing_inv_mul _ (Lk_det D)
  have hxc : ∀ i, (xc (IsLocalRing.ResidueField R) i y) ^ p = xc (IsLocalRing.ResidueField R) i y := by
    intro i
    simp only [xc]
    rw [← map_pow, ZMod.pow_card]
  have hR : ∑ l, Mk D j l * lam (Lk D) l y =
      ((Mk D * Lk D) *ᵥ fun i => xc (IsLocalRing.ResidueField R) i y) j := by
    rw [← Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct, lam]
  rw [hR]
  unfold Mk
  rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
  simp only [lam, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [sum_pow_char]
  simp only [mul_pow, hxc]

theorem formMonomial_unitVector (D : Lifts H U X) (l : Ix g) (y : Nb p g) :
    monF (Lk D) (e1 l) y = lam (Lk D) l y := by
  simp only [monF, e1]
  rw [Finset.prod_eq_single l]
  · simp [ZMod.val_one]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem MuR_map (hv : v.Integers R) (D : Lifts H U X) :
    (MuR hv D).map (IsLocalRing.residue R) = Matrix.of fun (y α : Nb p g) => monF (Lk D) α y := by
  ext y α
  simp [MuR, monF, Lk, residue_uR hv]

theorem res_bR (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j l : Ix g) : IsLocalRing.residue R (bR hv D j (e1 l)) = Mk D j l := by
  classical
  have hMu := MuR_mulVec_bR hv hp1 D j
  have hdet : IsUnit ((MuR hv D).map (IsLocalRing.residue R)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_det_MuR hv hp1 D).map _
  let c : Nb p g → IsLocalRing.ResidueField R := fun α => ∑ l', if α = e1 l' then Mk D j l' else 0
  have hvecres : ((MuR hv D).map (IsLocalRing.residue R)) *ᵥ
      (fun α => IsLocalRing.residue R (bR hv D j α)) = ((MuR hv D).map (IsLocalRing.residue R)) *ᵥ c := by
    funext y
    have h1 : ((MuR hv D).map (IsLocalRing.residue R) *ᵥ fun α => IsLocalRing.residue R (bR hv D j α)) y =
        IsLocalRing.residue R (hvec hv D j y) := by
      rw [← hMu, RingHom.map_mulVec]
      rfl
    rw [h1, hvec, map_pow, residue_uR hv]
    change lam (Lk D) j y ^ p = _
    rw [lam_p, MuR_map hv D]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, c, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, formMonomial_unitVector]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hinv := Matrix.nonsing_inv_mul _ hdet
  have hinj : (fun α => IsLocalRing.residue R (bR hv D j α)) = c := by
    calc (fun α => IsLocalRing.residue R (bR hv D j α))
        = (((MuR hv D).map (IsLocalRing.residue R))⁻¹ * (MuR hv D).map (IsLocalRing.residue R)) *ᵥ
            (fun α => IsLocalRing.residue R (bR hv D j α)) := by rw [hinv, Matrix.one_mulVec]
      _ = c := by rw [← Matrix.mulVec_mulVec, hvecres, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hc : IsLocalRing.residue R (bR hv D j (e1 l)) = c (e1 l) := congrFun hinj (e1 l)
  rw [hc]
  simp only [c]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    have h2 := congrFun h l
    simp [e1, Pi.single_apply, Ne.symm hb] at h2
  · simp

theorem Mk_det (D : Lifts H U X) : (Mk D).det ≠ 0 := by
  have h0 := (Lk_det D).ne_zero
  have hfrob : (Lk D).map (fun a => a ^ p) =
      (frobenius (IsLocalRing.ResidueField R) p).mapMatrix (Lk D) := by
    ext a b
    simp [frobenius_def]
  have hdet : ((Lk D).map (fun a => a ^ p)).det = (Lk D).det ^ p := by
    rw [hfrob, ← RingHom.map_det, frobenius_def]
  unfold Mk
  rw [Matrix.det_mul, hdet, Matrix.det_nonsing_inv]
  exact mul_ne_zero (pow_ne_zero _ h0) (by simpa [Ring.inverse_eq_inv] using h0)

theorem Mk_off (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j l : Ix g) (hl : D.κ l ≠ U.φ (D.κ j)) : Mk D j l = 0 := by
  rw [← res_bR hv hp1 D j l, bR_off hv hp1 D j l hl, map_zero]

theorem block_det_ne (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (i : Fin U.m) (e : {j // D.κ j = i} ≃ {l // D.κ l = U.φ i}) :
    (Matrix.of fun j l : {j // D.κ j = i} => Mk D j.1 (e l).1).det ≠ 0 := by
  classical
  intro h0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  let W : Ix g → IsLocalRing.ResidueField R := fun j => if hj : D.κ j = i then w ⟨j, hj⟩ else 0
  apply Mk_det D
  rw [← Matrix.exists_vecMul_eq_zero_iff]
  refine ⟨W, ?_, ?_⟩
  · intro hW
    apply hw0
    funext j
    have h1 := congrFun hW j.1
    simpa [W, j.2] using h1
  · funext l
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    by_cases hl : D.κ l = U.φ i
    · have h1 := congrFun hw (e.symm ⟨l, hl⟩)
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Equiv.apply_symm_apply,
        Pi.zero_apply] at h1
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => D.κ j = i)]
      have h2 : ∑ j : {j // ¬ D.κ j = i}, W j.1 * Mk D j.1 l = 0 :=
        Finset.sum_eq_zero fun j _ => by simp [W, j.2]
      have h3 : ∑ j : {j // D.κ j = i}, W j.1 * Mk D j.1 l = ∑ j, w j * Mk D j.1 l :=
        Finset.sum_congr rfl fun j _ => by simp [W, j.2]
      rw [h2, h3, add_zero]
      exact h1
    · refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : D.κ j = i
      · rw [Mk_off hv hp1 D j l (by rw [hj]; exact hl), mul_zero]
      · simp [W, hj]

end Res

end ReciprocityTheory.PGsh.Up.UnitVectorPowers
end
end

-- bundled from ReciprocityTheory.DualLattices.HasLenLeOfSurj
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

theorem hasLen_le_of_surj {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {z : NNReal}
    (hz : HasLen v R M z) (q : R) (r : ℕ)
    (π : M →ₗ[R] ((t : Fin r) → R ⧸ Ideal.span {q})) (hπ : Function.Surjective π) :
    z ≤ v (algebraMap R C q) ^ r := by
  obtain ⟨m, c, ⟨e⟩, hzc⟩ := hz
  have hx : HasLen v R ((t : Fin r) → R ⧸ Ideal.span {q}) (v (algebraMap R C q) ^ r) :=
    ⟨r, fun _ => q, ⟨LinearEquiv.refl R _⟩, by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]⟩
  have hs : Submodule.span R (Set.range fun i : Fin m =>
      (Pi.single i 1 : (j : Fin m) → R ⧸ Ideal.span {c j})) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [show x = ∑ i, (Pi.single i (x i) : (j : Fin m) → R ⧸ Ideal.span {c j}) from
      (Finset.univ_sum_single x).symm]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x i)
    have hsi : (Pi.single i (x i) : (j : Fin m) → R ⧸ Ideal.span {c j}) = a • Pi.single i 1 := by
      rw [← ha]
      ext j
      by_cases hj : j = i
      · subst hj
        rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, Algebra.smul_def, mul_one,
          Ideal.Quotient.algebraMap_eq]
      · simp [Pi.single_eq_of_ne hj]
    rw [hsi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hy : Submodule.span R (Set.range fun i : Fin m =>
      π (e.symm (Pi.single i 1 : (j : Fin m) → R ⧸ Ideal.span {c j}))) = ⊤ := by
    have hr : (Set.range fun i : Fin m => π (e.symm (Pi.single i 1 : (j : Fin m) → R ⧸ Ideal.span {c j}))) =
        (π ∘ₗ e.symm.toLinearMap) '' Set.range fun i : Fin m =>
          (Pi.single i 1 : (j : Fin m) → R ⧸ Ideal.span {c j}) := by
      rw [← Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, hs, Submodule.map_top, LinearMap.range_eq_top]
    exact hπ.comp e.symm.surjective
  have key := prod_le_of_gen hv hx _ hy c (fun i => ⟨0, ?_⟩)
  · rw [← hzc]
    exact key
  · simp only [Pi.zero_apply, ite_self, zero_smul, Finset.sum_const_zero]
    have h0 : c i • (Pi.single i 1 : (j : Fin m) → R ⧸ Ideal.span {c j}) = 0 := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply]
        rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
      · simp [Pi.single_eq_of_ne hj]
    rw [← LinearMap.map_smul, ← LinearEquiv.map_smul, h0, map_zero, map_zero]

section Mono

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

lemma monX_eq (D : Lifts H U X) (α : Nb p g) : monX D α = ∏ j, xL D j ^ (α j).val := by
  funext y
  simp only [monX, Finset.prod_apply, Pi.pow_apply]

lemma monX_mem (D : Lifts H U X) (α : Nb p g) : monX D α ∈ H.AA.carrier := by
  have hx : ∀ j, xL D j ∈ H.AA.carrier := fun j => (Submodule.mem_inf.mp (D.x_mem j)).1
  have hpow : ∀ (f : Nb p g → C) (n : ℕ), f ∈ H.AA.carrier → f ^ n ∈ H.AA.carrier := by
    intro f n hf
    induction n with
    | zero => simpa using H.AA.one_mem
    | succ n ih =>
      rw [pow_succ]
      exact H.AA.mul_mem _ _ ih hf
  rw [monX_eq]
  exact Finset.prod_induction _ (· ∈ H.AA.carrier) (fun a b ha hb => H.AA.mul_mem a b ha hb)
    H.AA.one_mem (fun j _ => hpow _ _ (hx j))

lemma monX_zero_at (D : Lifts H U X) {α : Nb p g} (hα : α ≠ 0) : monX D α 0 = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hα
  have hj' : α j ≠ 0 := hj
  have h0 : xL D j 0 = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp (D.x_mem j)).2
  have hv : (α j).val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
  simp only [monX]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [h0, zero_pow hv])

lemma monX_mem_aug (D : Lifts H U X) {α : Nb p g} (hα : α ≠ 0) :
    monX D α ∈ augIdeal H.AA.carrier :=
  Submodule.mem_inf.mpr ⟨monX_mem D α, LinearMap.mem_ker.mpr (monX_zero_at D hα)⟩

lemma monX_single (D : Lifts H U X) (k : Ix g) : monX D (Pi.single k 1) = xL D k := by
  rw [monX_eq, Finset.prod_eq_single k]
  · simp [ZMod.val_one]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ k) h

lemma monX_zero (D : Lifts H U X) : monX D 0 = 1 := by
  rw [monX_eq]
  simp

lemma monX_split (D : Lifts H U X) {α : Nb p g} {j : Ix g} (hj : α j ≠ 0) :
    monX D α = xL D j * monX D (Function.update α j (α j - 1)) := by
  rw [monX_eq, monX_eq, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  have hrest : ∏ i ∈ Finset.univ.erase j, xL D i ^ (Function.update α j (α j - 1) i).val =
      ∏ i ∈ Finset.univ.erase j, xL D i ^ (α i).val :=
    Finset.prod_congr rfl fun i hi => by simp [Function.update_apply, Finset.ne_of_mem_erase hi]
  have hself : (Function.update α j (α j - 1) j) = α j - 1 := by simp [Function.update_apply]
  rw [hrest, hself]
  have hv1 : 1 ≤ (α j).val := Nat.one_le_iff_ne_zero.mpr (by rwa [Ne, ZMod.val_eq_zero])
  have hsub : (α j - 1).val = (α j).val - 1 := by
    rw [ZMod.val_sub (by rw [ZMod.val_one]; exact hv1), ZMod.val_one]
  rw [hsub, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hv1]

lemma monX_mem_sq (D : Lifts H U X) {α : Nb p g} (h0 : α ≠ 0) (h1 : ∀ k, α ≠ Pi.single k 1) :
    monX D α ∈ sqIdeal (augIdeal H.AA.carrier) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h0
  have hj' : α j ≠ 0 := hj
  have hβ : Function.update α j (α j - 1) ≠ 0 := by
    intro hz
    apply h1 j
    funext i
    by_cases hi : i = j
    · subst hi
      rw [Pi.single_eq_same]
      simpa [Function.update_apply, sub_eq_zero] using congrFun hz i
    · rw [Pi.single_eq_of_ne hi]
      simpa [Function.update_apply, hi] using congrFun hz i
  exact Submodule.subset_span ⟨xL D j, D.x_mem j, monX D (Function.update α j (α j - 1)),
    monX_mem_aug D hβ, monX_split D hj'⟩

lemma sub_lin_mem_sq (hv : v.Integers R) (D : Lifts H U X) (hdet : (valM D).det ≠ 0)
    (hbasis : H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val))
    {f : Nb p g → C} (hf : f ∈ augIdeal H.AA.carrier) :
    ∃ c : Ix g → R, (∀ k, algebraMap R C (c k) = linX D f k) ∧
      f - ∑ k, c k • xL D k ∈ sqIdeal (augIdeal H.AA.carrier) := by
  classical
  have hfA : f ∈ Submodule.span R (Set.range fun α => monX D α) := by
    have h := (Submodule.mem_inf.mp hf).1
    rw [hbasis] at h
    exact h
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hfA
  have hf0 : f 0 = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hf).2
  have hval : f = (valM D) *ᵥ (fun α => algebraMap R C (c α)) := by
    rw [← hc]
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, Matrix.mulVec, dotProduct, valM,
      Matrix.of_apply]
    exact Finset.sum_congr rfl fun α _ => mul_comm _ _
  have hcoef : coefX D f = fun α => algebraMap R C (c α) := by
    rw [coefX, hval, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  refine ⟨fun k => c (Pi.single k 1), fun k => ?_, ?_⟩
  · rw [linX, hcoef]
  · set P : Nb p g → Prop := fun α => α ≠ 0 ∧ ∀ k, α ≠ Pi.single k 1 with hP
    have hw0 : algebraMap R C (c 0) = 0 := by
      have h := congrFun hval 0
      rw [hf0] at h
      simp only [Matrix.mulVec, dotProduct, valM, Matrix.of_apply] at h
      rw [Finset.sum_eq_single 0 (fun α _ hα => by rw [monX_zero_at D hα, zero_mul])
        (fun h => absurd (Finset.mem_univ 0) h), monX_zero] at h
      simpa using h.symm
    have hB : ∑ α, (if P α then 0 else c α • monX D α) = ∑ k, c (Pi.single k 1) • xL D k := by
      have hsub : ∑ α, (if P α then 0 else c α • monX D α) =
          ∑ α ∈ Finset.univ.image (fun k : Ix g => (Pi.single k (1 : ZMod p) : Nb p g)),
            (if P α then 0 else c α • monX D α) := by
        symm
        refine Finset.sum_subset (Finset.subset_univ _) fun α _ hα => ?_
        by_cases hPα : P α
        · simp [hPα]
        · rw [if_neg hPα]
          have h0 : α = 0 := by
            by_contra h0
            apply hPα
            refine ⟨h0, fun k hk => hα ?_⟩
            exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk.symm⟩
          subst h0
          rw [monX_zero]
          funext y
          simp [Algebra.smul_def, hw0]
      rw [hsub, Finset.sum_image (fun k _ k' _ h => by
        by_contra hne
        have h2 := congrFun h k
        rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h2
        exact one_ne_zero h2)]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hnP : ¬ P (Pi.single k 1) := fun h => h.2 k rfl
      rw [if_neg hnP, monX_single]
    have hA : ∀ α, (if P α then c α • monX D α else 0) ∈ sqIdeal (augIdeal H.AA.carrier) := by
      intro α
      split_ifs with h
      · exact Submodule.smul_mem _ _ (monX_mem_sq D h.1 h.2)
      · exact Submodule.zero_mem _
    have hsum : f = ∑ α, (if P α then c α • monX D α else 0) +
        ∑ α, (if P α then 0 else c α • monX D α) := by
      rw [← Finset.sum_add_distrib, ← hc]
      refine Finset.sum_congr rfl fun α _ => ?_
      split_ifs <;> simp
    rw [← hB, hsum, add_sub_cancel_right]
    exact Submodule.sum_mem _ fun α _ => hA α

end Mono

end ReciprocityTheory.PGsh.Up
end
end

