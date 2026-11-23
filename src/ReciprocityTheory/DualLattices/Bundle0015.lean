module

public import ReciprocityTheory.DualLattices.Bundle0011
public import ReciprocityTheory.DualLattices.Bundle0010

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.PrimeHopfOrderOfAddEquiv
section
noncomputable section

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Transport

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X Y : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
  [AddCommGroup Y] [Fintype Y] [DecidableEq Y]

abbrev pbE (e : X ≃+ Y) : (Y → C) ≃ₗ[R] (X → C) := LinearEquiv.funCongrLeft R C e.toEquiv

lemma pbE_apply (e : X ≃+ Y) (f : Y → C) (x : X) : pbE (C := C) (R := R) e f x = f (e x) := rfl

lemma pbE_symm_apply (e : X ≃+ Y) (f : X → C) (y : Y) :
    (pbE (C := C) (R := R) e).symm f y = f (e.symm y) := by
  rfl

lemma det_sub (e : X ≃+ Y) (B : Matrix Y Y C) : (B.submatrix e e).det = B.det :=
  Matrix.det_submatrix_equiv_self e.toEquiv B

lemma map_cols (e : X ≃+ Y) (B : Matrix Y Y C) :
    (Submodule.span R (Set.range fun j y => B y j)).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) =
      Submodule.span R (Set.range fun j x => (B.submatrix e e) x j) := by
  rw [Submodule.map_span, ← Set.range_comp]
  have h : (fun j x => (B.submatrix e e) x j) =
      ((pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) ∘ fun j y => B y j) ∘ e := by
    funext j x
    rfl
  rw [h, e.surjective.range_comp]

lemma hasColen_map (v : Valuation C NNReal) (e : X ≃+ Y) (M : Submodule R (Y → C)) (c : NNReal)
    (h : HasColen R v M c) : HasColen R v (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) c := by
  obtain ⟨B, hM, hc⟩ := h
  exact ⟨B.submatrix e e, by rw [hM, map_cols], by rw [det_sub, hc]⟩

lemma map_pbE_symm (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))).map (pbE (C := C) (R := R) e.symm : (X → C) →ₗ[R] (Y → C)) = M := by
  rw [← Submodule.map_comp]
  have h : ((pbE (C := C) (R := R) e.symm : (X → C) →ₗ[R] (Y → C)).comp
      (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) = LinearMap.id := by
    refine LinearMap.ext fun f => funext fun y => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, pbE_apply, LinearMap.id_apply,
      AddEquiv.apply_symm_apply]
  rw [h, Submodule.map_id]

def hopfPull (e : X ≃+ Y) (A : HopfOrder (C := C) R Y) : HopfOrder (C := C) R X where
  carrier := A.carrier.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))
  lat := by
    obtain ⟨B, hB, hA⟩ := A.lat
    exact ⟨B.submatrix e e, by rwa [det_sub], by rw [hA, map_cols]⟩
  le_int := by
    intro f hf
    rw [Submodule.mem_map_equiv] at hf
    have h := A.le_int hf
    intro x
    obtain ⟨r, hr⟩ := h (e x)
    exact ⟨r, by rw [hr, pbE_symm_apply, AddEquiv.symm_apply_apply]⟩
  one_mem := by
    rw [Submodule.mem_map_equiv]
    convert A.one_mem using 1
    funext y
    simp [pbE_symm_apply]
  mul_mem := fun f g hf hg => by
    rw [Submodule.mem_map_equiv] at hf hg ⊢
    convert A.mul_mem _ _ hf hg using 1
    funext y
    simp only [pbE_symm_apply, Pi.mul_apply]
  comul := by
    intro f hf
    rw [Submodule.mem_map_equiv] at hf
    set g := (pbE (C := C) (R := R) e).symm f with hg
    have hfg : f = pbE (C := C) (R := R) e g := by rw [hg, LinearEquiv.apply_symm_apply]
    let pb2 : (Y × Y → C) →ₗ[R] (X × X → C) :=
      LinearMap.funLeft R C (fun q : X × X => (e q.1, e q.2))
    have h1 : addPull R X f = pb2 (addPull R Y g) := by
      funext q
      rw [hfg]
      simp only [addPull, pb2, LinearMap.funLeft_apply, pbE_apply, map_add (f := _)]
    rw [h1]
    have h2 := A.comul g hf
    have h3 : (tensorSpan R A.carrier).map pb2 ≤ tensorSpan R (A.carrier.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) := by
      rw [tensorSpan, Submodule.map_span_le]
      rintro F ⟨g1, hg1, h1', hh1, rfl⟩
      exact Submodule.subset_span ⟨pbE (C := C) (R := R) e g1, Submodule.mem_map_of_mem hg1,
        pbE (C := C) (R := R) e h1', Submodule.mem_map_of_mem hh1, rfl⟩
    exact h3 (Submodule.mem_map_of_mem h2)
  antipode := fun f hf => by
    rw [Submodule.mem_map_equiv] at hf ⊢
    convert A.antipode _ hf using 1
    funext y
    simp only [pbE_symm_apply, map_neg]

private theorem pbE_symm_pow (e : X ≃+ Y) (f : X → C) (n : ℕ) :
    (pbE (C := C) (R := R) e).symm (f ^ n) = ((pbE (C := C) (R := R) e).symm f) ^ n := by
  funext y
  simp only [pbE_symm_apply, Pi.pow_apply]

lemma mem_augIdeal_pull (e : X ≃+ Y) (A : HopfOrder (C := C) R Y) (f : X → C) :
    f ∈ augIdeal (hopfPull e A).carrier ↔ (pbE (C := C) (R := R) e).symm f ∈ augIdeal A.carrier := by
  rw [show (hopfPull e A).carrier =
      A.carrier.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) from rfl]
  simp only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply,
    Submodule.mem_map_equiv, pbE_symm_apply, map_zero]

end Transport

lemma pow_mem_aug {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {X : Type}
    [AddCommGroup X] [Fintype X] [DecidableEq X] (A : HopfOrder (C := C) R X) {x : X → C}
    (hx : x ∈ augIdeal A.carrier) : ∀ k : ℕ, x ^ (k + 1) ∈ augIdeal A.carrier := by
  intro k
  simp only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply] at hx ⊢
  refine ⟨?_, by rw [Pi.pow_apply, hx.2, zero_pow (Nat.succ_ne_zero k)]⟩
  induction k with
  | zero => rw [zero_add, pow_one]; exact hx.1
  | succ k ih => rw [pow_succ]; exact A.mul_mem _ _ ih hx.1

theorem primeHopfOrder_of_addEquiv (hU3 : PrimeHopfOrderStatement) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (hv : v.Integers R) (hp : v (p : C) < 1) {K : Type} [AddCommGroup K] [Fintype K]
    [DecidableEq K] (e : ZMod p ≃+ K) (AK : HopfOrder (C := C) R K) :
    ∃ (xK : K → C) (δ : R) (x1 : C), xK ∈ augIdeal AK.carrier ∧
      xK ^ p = (fun a => algebraMap R C δ * xK a) ∧ v (algebraMap R C δ) = v x1 ^ (p - 1) ∧
      (∀ f ∈ augIdeal AK.carrier, ∃ r : R,
        f - r • xK ∈ augIdeal AK.carrier * augIdeal AK.carrier) ∧
      HasColen R v AK.carrier (v x1 ^ (p * (p - 1) / 2)) := by
  obtain ⟨x, _, δ, hx, hx0, -, -, -, hxp, hδ, -, haug, -, hcol⟩ :=
    hU3 p C v R hv hp (hopfPull e AK)
  have hxa : x ∈ ReciprocityTheory.PGsh.L2.augIdeal (hopfPull e AK).carrier := by
    simp only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply]
    exact ⟨hx, hx0⟩
  have hxK := (mem_augIdeal_pull e AK x).1 hxa
  refine ⟨(pbE (C := C) (R := R) e).symm x, δ, x 1, hxK, ?_, hδ, ?_, ?_⟩
  · funext k
    have h := congrFun hxp (e.symm k)
    simp only [Pi.pow_apply] at h ⊢
    rw [pbE_symm_apply]
    exact h
  · have key : ∀ F ∈ Submodule.span R {y | ∃ j : ℕ, 1 ≤ j ∧ j < p ∧ y = x ^ j},
        ∃ r : R, (pbE (C := C) (R := R) e).symm F - r • (pbE (C := C) (R := R) e).symm x ∈
          ReciprocityTheory.PGsh.L2.augIdeal AK.carrier * ReciprocityTheory.PGsh.L2.augIdeal AK.carrier := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, hj1, -, rfl⟩ := hy
        rcases Nat.lt_or_ge j 2 with hj | hj
        · obtain rfl : j = 1 := by omega
          refine ⟨1, ?_⟩
          rw [pow_one, one_smul, sub_self]
          exact zero_mem _
        · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
          refine ⟨0, ?_⟩
          rw [zero_smul, sub_zero, pbE_symm_pow, show m + 2 = (m + 1) + 1 from rfl, pow_succ]
          exact Submodule.mul_mem_mul (pow_mem_aug AK hxK m) hxK
      | zero =>
        refine ⟨0, ?_⟩
        rw [map_zero, zero_smul, sub_zero]
        exact zero_mem _
      | add a b _ _ ha hb =>
        obtain ⟨r1, h1⟩ := ha
        obtain ⟨r2, h2⟩ := hb
        refine ⟨r1 + r2, ?_⟩
        convert add_mem h1 h2 using 1
        rw [map_add (f := _), add_smul]
        abel
      | smul c a _ ha =>
        obtain ⟨r1, h1⟩ := ha
        refine ⟨c * r1, ?_⟩
        convert Submodule.smul_mem _ c h1 using 1
        rw [map_smul, smul_sub, mul_smul]
    intro f hf
    have hF : pbE (C := C) (R := R) e f ∈
        ReciprocityTheory.PGsh.L2.augIdeal (hopfPull e AK).carrier := by
      rw [mem_augIdeal_pull, LinearEquiv.symm_apply_apply]
      exact hf
    rw [haug] at hF
    obtain ⟨r, hr⟩ := key _ hF
    rw [LinearEquiv.symm_apply_apply] at hr
    exact ⟨r, hr⟩
  · have hc := hasColen_map v e.symm _ _ hcol
    rwa [show (hopfPull e AK).carrier =
        AK.carrier.map (pbE (C := C) (R := R) e : (K → C) →ₗ[R] (ZMod p → C)) from rfl,
      map_pbE_symm] at hc

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.ProdDvdOfIso
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

private lemma pi_quotient_eq_sum_smul_single {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (I : ι → Ideal R) (y : (i : ι) → R ⧸ I i) (a : ι → R)
    (ha : ∀ i, Ideal.Quotient.mk (I i) (a i) = y i) : y = ∑ i, a i • Pi.single i 1 := by
  funext i'
  rw [Finset.sum_apply, Finset.sum_eq_single i']
  · rw [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one,
      Ideal.Quotient.algebraMap_eq, ha]
  · intro j _ hj
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ i') h

private lemma nonempty_pi_quotient_equiv_maximal_restrict {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι]
    [DecidableEq ι] (a : ι → R) :
    Nonempty (((i : ι) → R ⧸ Ideal.span {a i}) ≃ₗ[R]
      ((i : {i // a i ∈ IsLocalRing.maximalIdeal R}) → R ⧸ Ideal.span {a i})) := by
  classical
  have hsub : ∀ i, a i ∉ IsLocalRing.maximalIdeal R → ∀ x : R ⧸ Ideal.span {a i}, x = 0 := by
    intro i hi x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hu : IsUnit (a i) := by
      by_contra h
      exact hi ((IsLocalRing.mem_maximalIdeal _).mpr h)
    rw [Ideal.span_singleton_eq_top.mpr hu]
    exact Submodule.mem_top
  let g : ((i : ι) → R ⧸ Ideal.span {a i}) →ₗ[R]
      ((i : {i // a i ∈ IsLocalRing.maximalIdeal R}) → R ⧸ Ideal.span {a i}) :=
    { toFun := fun x i => x i
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl }
  refine ⟨LinearEquiv.ofBijective g ⟨fun x y hxy => ?_, fun z => ?_⟩⟩
  · funext i
    by_cases hi : a i ∈ IsLocalRing.maximalIdeal R
    · exact congrFun hxy ⟨i, hi⟩
    · rw [hsub i hi (x i), hsub i hi (y i)]
  · refine ⟨fun i => if hi : a i ∈ IsLocalRing.maximalIdeal R then z ⟨i, hi⟩ else 0, ?_⟩
    funext i
    exact dif_pos i.2

private lemma prod_mem_span_prod_of_linearEquiv_pi_quotient {R : Type} [CommRing R] [IsLocalRing R] {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (c : ι → R) (d : κ → R)
    (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal R) (hd : ∀ j, d j ∈ IsLocalRing.maximalIdeal R)
    (f : ((i : ι) → R ⧸ Ideal.span {c i}) ≃ₗ[R] ((j : κ) → R ⧸ Ideal.span {d j})) :
    ∏ i, c i ∈ Ideal.span {∏ j, d j} := by
  classical
  let A : Matrix κ ι R := fun j i =>
    Function.surjInv (f := Ideal.Quotient.mk (Ideal.span {d j})) Ideal.Quotient.mk_surjective
      (f (Pi.single i 1) j)
  let B : Matrix ι κ R := fun i j =>
    Function.surjInv (f := Ideal.Quotient.mk (Ideal.span {c i})) Ideal.Quotient.mk_surjective
      (f.symm (Pi.single j 1) i)
  have hA : ∀ j i, Ideal.Quotient.mk (Ideal.span {d j}) (A j i) = f (Pi.single i 1) j :=
    fun j i => Function.surjInv_eq _ _
  have hB : ∀ i j, Ideal.Quotient.mk (Ideal.span {c i}) (B i j) = f.symm (Pi.single j 1) i :=
    fun i j => Function.surjInv_eq _ _
  have hsing : ∀ i, c i • (Pi.single i 1 : (i : ι) → R ⧸ Ideal.span {c i}) = 0 := by
    intro i
    funext i'
    rw [Pi.smul_apply, Pi.zero_apply]
    by_cases h : i' = i
    · subst h
      rw [Pi.single_eq_same, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    · rw [Pi.single_eq_of_ne h, smul_zero]
  have relA : ∀ j i, c i * A j i ∈ Ideal.span {d j} := by
    intro j i
    have h1 : f (c i • Pi.single i 1) j = 0 := by simp [hsing]
    rw [map_smul, Pi.smul_apply, ← hA, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  have relBA : ∀ i' i, (∑ j, B i' j * A j i) - (if i' = i then 1 else 0) ∈
      Ideal.span {c i'} := by
    intro i' i
    have h1 : (∑ j, Ideal.Quotient.mk (Ideal.span {c i'}) (B i' j * A j i)) =
        (Pi.single i 1 : (i : ι) → R ⧸ Ideal.span {c i}) i' := by
      have h0 := congrArg (fun y => y i') (f.symm_apply_apply (Pi.single i 1))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h0, pi_quotient_eq_sum_smul_single _ (f (Pi.single i 1)) (fun j => A j i) (fun j => hA j i),
        map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, Pi.smul_apply, ← hB, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        ← map_mul, mul_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_sum, h1]
    by_cases h : i' = i
    · subst h
      rw [Pi.single_eq_same, if_pos rfl, map_one]
    · rw [Pi.single_eq_of_ne h, if_neg h, map_zero]
  have relAB : ∀ j j', (∑ i, A j i * B i j') - (if j = j' then 1 else 0) ∈
      Ideal.span {d j} := by
    intro j j'
    have h1 : (∑ i, Ideal.Quotient.mk (Ideal.span {d j}) (A j i * B i j')) =
        (Pi.single j' 1 : (j : κ) → R ⧸ Ideal.span {d j}) j := by
      have h0 := congrArg (fun y => y j) (f.apply_symm_apply (Pi.single j' 1))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h0, pi_quotient_eq_sum_smul_single _ (f.symm (Pi.single j' 1)) (fun i => B i j') (fun i => hB i j'),
        map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Pi.smul_apply, ← hA, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        ← map_mul, mul_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_sum, h1]
    by_cases h : j = j'
    · subst h
      rw [Pi.single_eq_same, if_pos rfl, map_one]
    · rw [Pi.single_eq_of_ne h, if_neg h, map_zero]
  have hBA : (B * A).map (IsLocalRing.residue R) = 1 := by
    ext i' i
    rw [Matrix.map_apply, Matrix.mul_apply, Matrix.one_apply]
    have h3 : IsLocalRing.residue R ((∑ j, B i' j * A j i) - if i' = i then 1 else 0) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr
        ((Ideal.span_singleton_le_iff_mem _).mpr (hc i') (relBA i' i))
    rw [map_sub, sub_eq_zero] at h3
    rw [h3]
    split_ifs <;> simp
  have hAB : (A * B).map (IsLocalRing.residue R) = 1 := by
    ext j j'
    rw [Matrix.map_apply, Matrix.mul_apply, Matrix.one_apply]
    have h3 : IsLocalRing.residue R ((∑ i, A j i * B i j') - if j = j' then 1 else 0) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr
        ((Ideal.span_singleton_le_iff_mem _).mpr (hd j) (relAB j j'))
    rw [map_sub, sub_eq_zero] at h3
    rw [h3]
    split_ifs <;> simp
  have hcard : Fintype.card ι = Fintype.card κ := by
    apply le_antisymm
    · calc Fintype.card ι = (1 : Matrix ι ι (IsLocalRing.ResidueField R)).rank :=
            Matrix.rank_one.symm
        _ = ((B * A).map (IsLocalRing.residue R)).rank := by rw [hBA]
        _ = (B.map (IsLocalRing.residue R) * A.map (IsLocalRing.residue R)).rank := by
            rw [Matrix.map_mul]
        _ ≤ (A.map (IsLocalRing.residue R)).rank := Matrix.rank_mul_le_right _ _
        _ ≤ Fintype.card κ := Matrix.rank_le_card_height _
    · calc Fintype.card κ = (1 : Matrix κ κ (IsLocalRing.ResidueField R)).rank :=
            Matrix.rank_one.symm
        _ = ((A * B).map (IsLocalRing.residue R)).rank := by rw [hAB]
        _ = (A.map (IsLocalRing.residue R) * B.map (IsLocalRing.residue R)).rank := by
            rw [Matrix.map_mul]
        _ ≤ (B.map (IsLocalRing.residue R)).rank := Matrix.rank_mul_le_right _ _
        _ ≤ Fintype.card ι := Matrix.rank_le_card_height _
  let e : ι ≃ κ := Fintype.equivOfCardEq hcard
  choose X hX using fun j i => Ideal.mem_span_singleton'.mp (relA j i)
  let A' : Matrix κ κ R := fun j j' => A j (e.symm j')
  let B' : Matrix κ κ R := fun j' j => B (e.symm j') j
  let X' : Matrix κ κ R := fun j j' => X j (e.symm j')
  have hmat : A' * Matrix.diagonal (fun j => c (e.symm j)) = Matrix.diagonal d * X' := by
    ext j j'
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    show A j (e.symm j') * c (e.symm j') = d j * X j (e.symm j')
    rw [mul_comm (A _ _), ← hX, mul_comm]
  have hprod : ∏ j, c (e.symm j) = ∏ i, c i := Equiv.prod_comp e.symm c
  have hdet : A'.det * ∏ i, c i = (∏ j, d j) * X'.det := by
    have h := congrArg Matrix.det hmat
    rwa [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hprod] at h
  have hdetBA : IsUnit (B * A).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hBA,
      Matrix.det_one]
    exact one_ne_zero
  have hBA' : B' * A' = (B * A).submatrix e.symm e.symm := by
    ext j1 j2
    simp only [Matrix.mul_apply, Matrix.submatrix_apply]
    rfl
  have hdetA' : IsUnit A'.det := by
    have h := congrArg Matrix.det hBA'
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul] at h
    rw [← h] at hdetBA
    exact isUnit_of_mul_isUnit_right hdetBA
  obtain ⟨u, hu⟩ := hdetA'
  rw [Ideal.mem_span_singleton']
  refine ⟨↑u⁻¹ * X'.det, ?_⟩
  calc ↑u⁻¹ * X'.det * ∏ j, d j = ↑u⁻¹ * (A'.det * ∏ i, c i) := by rw [hdet]; ring
    _ = ∏ i, c i := by rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]

lemma prod_dvd_of_iso {R : Type} [CommRing R] [IsLocalRing R] {m n : ℕ} (c : Fin m → R)
    (d : Fin n → R)
    (f : ((i : Fin m) → R ⧸ Ideal.span {c i}) ≃ₗ[R] ((j : Fin n) → R ⧸ Ideal.span {d j})) :
    ∏ i, c i ∈ Ideal.span {∏ j, d j} := by
  classical
  obtain ⟨gc⟩ := nonempty_pi_quotient_equiv_maximal_restrict c
  obtain ⟨gd⟩ := nonempty_pi_quotient_equiv_maximal_restrict d
  have core := prod_mem_span_prod_of_linearEquiv_pi_quotient (fun i : {i // c i ∈ IsLocalRing.maximalIdeal R} => c i)
    (fun j : {j // d j ∈ IsLocalRing.maximalIdeal R} => d j) (fun i => i.2) (fun j => j.2)
    ((gc.symm.trans f).trans gd)
  have hunit : ∀ {k : ℕ} (a : Fin k → R),
      IsUnit (∏ i : {i // ¬ a i ∈ IsLocalRing.maximalIdeal R}, a i) := by
    intro k a
    refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one fun i _ => ?_
    by_contra h
    exact i.2 ((IsLocalRing.mem_maximalIdeal _).mpr h)
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => c i ∈ IsLocalRing.maximalIdeal R) c,
    ← Fintype.prod_subtype_mul_prod_subtype (fun j => d j ∈ IsLocalRing.maximalIdeal R) d,
    Ideal.span_singleton_mul_right_unit (hunit d)]
  exact Ideal.mul_mem_right _ _ core

theorem hasLen_unique {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {x y : NNReal}
    (hx : HasLen v R M x) (hy : HasLen v R M y) : x = y := by
  obtain ⟨m, c, ⟨φ⟩, rfl⟩ := hx
  obtain ⟨n, d, ⟨ψ⟩, rfl⟩ := hy
  haveI : Nontrivial R := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' := congrArg (algebraMap R C) h
    rw [map_zero, map_one] at h'
    exact zero_ne_one h'
  have hlt : ∀ z : R, ¬ IsUnit z → v (algebraMap R C z) < 1 := fun z hz =>
    lt_of_le_of_ne (hv.map_le_one z) fun h1 => hz (hv.isUnit_iff_valuation_eq_one.mpr h1)
  haveI : IsLocalRing R := by
    refine IsLocalRing.of_nonunits_add fun a b ha hb hab => ?_
    have h1 := hv.isUnit_iff_valuation_eq_one.mp hab
    rw [map_add (f := _)] at h1
    have h2 := (v.map_add _ _).trans_lt (max_lt (hlt a ha) (hlt b hb))
    rw [h1] at h2
    exact lt_irrefl _ h2
  have h1 := prod_dvd_of_iso c d (φ.symm.trans ψ)
  have h2 := prod_dvd_of_iso d c (ψ.symm.trans φ)
  rw [Ideal.mem_span_singleton, hv.dvd_iff_le] at h1 h2
  simp only [map_prod] at h1 h2
  exact le_antisymm h1 h2

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.TangentPairingStatement
section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀)

def evK {R' R : LAlg R₀} (π : LHom R' R) (h : B.gg →ₗ[R₀] R') (V : B.gg ⊗[R₀] π.ker) : R' :=
  LinearMap.mul' R₀ R' (TensorProduct.map h π.ker.subtype V)

end BX

def TangentPairingStatement (B : BX R₀) : Prop :=
  ∀ (R' R : LAlg R₀) (π : LHom R' R) (ξ : (R' : Type u)) (Dp : DualPair R) (N : ℕ)
    (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0),
    (∀ a, a * ξ = 0 → a ∈ Ideal.span {ξ}) → (N : (R' : Type u)) = 0 →
    ∀ (sh th : B.G R') (Vs Vt : B.gg ⊗[R₀] π.ker) (hs ht : B.gg →ₗ[R₀] R')
      (zh : (R' : Type u)ˣ) (z : (R : Type u)ˣ),
      N • sh = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) Vs → N • th = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) Vt →
      B.IsHeight Dp N (B.map π sh) (π.1.toLinearMap ∘ₗ hs) →
      B.IsHeight Dp N (B.map π th) (π.1.toLinearMap ∘ₗ ht) →
      B.IsPairing N (B.map π sh) (B.map π th) z → Units.map (π.1 : R' →* R) zh = z →
      (zh : (R' : Type u)) ^ N = 1 + (B.evK π ht Vs - B.evK π hs Vt)

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.ToSigmaAddFstZeroFst
section
noncomputable section

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

def tot (B : BX R₀) {R : LAlg R₀} {x y : B.G R} (u : B.P R x y) : Σ x y : B.G R, B.P R x y :=
  ⟨x, y, u⟩

def tmap (B : BX R₀) {R S : LAlg R₀} (f : LHom R S) (t : Σ x y : B.G R, B.P R x y) :
    Σ x y : B.G S, B.P S x y :=
  ⟨B.map f t.1, B.map f t.2.1, B.pmap f t.2.2⟩

variable {B : BX R₀} {R S T : LAlg R₀}

end BX

end ReciprocityTheory.PGsh
end
end

