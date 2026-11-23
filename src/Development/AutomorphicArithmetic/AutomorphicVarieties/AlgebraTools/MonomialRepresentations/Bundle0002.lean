module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.HenselDiag
section
open Polynomial Matrix

section
variable {C ι : Type} [CommRing C] [Fintype ι] [DecidableEq ι]

private theorem res_one [IsLocalRing C] (u : Matrix ι ι C) :
    (∀ i j, (u - 1) i j ∈ IsLocalRing.maximalIdeal C) ↔ (IsLocalRing.residue C).mapMatrix u = 1 := by
  rw [← map_one (IsLocalRing.residue C).mapMatrix, ← sub_eq_zero, ← map_sub, ← Matrix.ext_iff]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, IsLocalRing.residue_eq_zero_iff]

private theorem unit_of_res [IsLocalRing C] (x : C) (h : IsLocalRing.residue C x ≠ 0) : IsUnit x := by
  by_contra hx
  exact h ((IsLocalRing.residue_eq_zero_iff _).mpr hx)

private theorem res_diag [IsLocalRing C] (M : Matrix ι ι C)
    (h : ∀ i j, i ≠ j → M i j ∈ IsLocalRing.maximalIdeal C) :
    (IsLocalRing.residue C).mapMatrix M = diagonal fun i => IsLocalRing.residue C (M i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, IsLocalRing.residue_eq_zero_iff, h i j hij]

private theorem exists_root [HenselianLocalRing C] (M : Matrix ι ι C)
    (h : ∀ i j, i ≠ j → M i j ∈ IsLocalRing.maximalIdeal C) (hu : ∀ i j, i ≠ j → IsUnit (M i i - M j j)) (i : ι) :
    ∃ d : C, (Matrix.scalar ι d - M).det = 0 ∧ d - M i i ∈ IsLocalRing.maximalIdeal C := by
  have hc : M.charpoly.map (IsLocalRing.residue C) = ∏ j, (X - Polynomial.C (IsLocalRing.residue C (M j j))) := by
    rw [← Matrix.charpoly_map, ← RingHom.mapMatrix_apply, res_diag M h, Matrix.charpoly_diagonal]
  have h1 : M.charpoly.eval (M i i) ∈ IsLocalRing.maximalIdeal C := by
    rw [← IsLocalRing.residue_eq_zero_iff, ← Polynomial.eval_map_apply, hc, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have h2 : IsUnit (M.charpoly.derivative.eval (M i i)) := by
    apply unit_of_res
    rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map, hc,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), derivative_mul]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X,
      eval_C, sub_self, zero_mul, add_zero, eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun a ha => ?_
    rw [← map_sub]
    exact ((hu i a (Finset.ne_of_mem_erase ha).symm).map _).ne_zero
  obtain ⟨d, hd, hd'⟩ := HenselianLocalRing.is_henselian M.charpoly M.charpoly_monic (M i i) h1 h2
  exact ⟨d, by rw [← Matrix.eval_charpoly]; exact hd, hd'⟩

private theorem exists_vec [IsLocalRing C] (M : Matrix ι ι C)
    (h : ∀ i j, i ≠ j → M i j ∈ IsLocalRing.maximalIdeal C) (hu : ∀ i j, i ≠ j → IsUnit (M i i - M j j)) (i : ι)
    (d : C) (hd : (Matrix.scalar ι d - M).det = 0) (hd' : d - M i i ∈ IsLocalRing.maximalIdeal C) :
    ∃ v : ι → C, (∀ k, ∑ j, M k j * v j = v k * d) ∧ v i = 1 ∧ ∀ k, k ≠ i → v k ∈ IsLocalRing.maximalIdeal C := by
  have hdi : IsLocalRing.residue C d = IsLocalRing.residue C (M i i) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hd'
  set A := (Matrix.scalar ι d - M).adjugate with hA
  have h0 : (Matrix.scalar ι d - M) * A = 0 := by rw [hA, Matrix.mul_adjugate, hd, zero_smul]
  have h1 : (IsLocalRing.residue C).mapMatrix (Matrix.scalar ι d - M) =
      diagonal fun k => IsLocalRing.residue C (M i i - M k k) := by
    rw [map_sub, res_diag M h]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hdi]
    · simp [hab]
  have h2 : (IsLocalRing.residue C).mapMatrix A =
      diagonal fun k => ∏ j ∈ Finset.univ.erase k, IsLocalRing.residue C (M i i - M j j) := by
    rw [hA, RingHom.map_adjugate, h1, Matrix.adjugate_diagonal]
  have h3 : IsUnit (A i i) := by
    apply unit_of_res
    have := congrFun (congrFun h2 i) i
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_eq] at this
    rw [this]
    exact Finset.prod_ne_zero_iff.mpr fun a ha => ((hu i a (Finset.ne_of_mem_erase ha).symm).map _).ne_zero
  obtain ⟨c, hc⟩ := h3.exists_right_inv
  refine ⟨fun k => A k i * c, fun k => ?_, hc, fun k hk => ?_⟩
  · rw [sub_mul, sub_eq_zero] at h0
    have := congrFun (congrFun h0 k) i
    rw [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_apply] at this
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, ← this]; ring
  · have := congrFun (congrFun h2 k) i
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_ne _ hk,
      IsLocalRing.residue_eq_zero_iff] at this
    exact Ideal.mul_mem_right _ _ this

end

theorem UpperTheory.V.AlgebraTools.henselDiag :
    ∀ (C ι : Type) [CommRing C] [HenselianLocalRing C] [Fintype ι] [DecidableEq ι] (M : Matrix ι ι C),
      (∀ i j, i ≠ j → M i j ∈ IsLocalRing.maximalIdeal C) → (∀ i j, i ≠ j → IsUnit (M i i - M j j)) →
      ∃ (u : Matrix ι ι C) (d : ι → C), (∀ i j, (u - 1) i j ∈ IsLocalRing.maximalIdeal C) ∧ M * u = u * diagonal d ∧
        (∀ i, d i - M i i ∈ IsLocalRing.maximalIdeal C) ∧
        ∀ (u' : Matrix ι ι C) (d' : ι → C), (∀ i j, (u' - 1) i j ∈ IsLocalRing.maximalIdeal C) → M * u' = u' * diagonal d' →
          d' = d ∧ ∃ t : ι → C, u' = u * diagonal t := by
  intro C ι _ _ _ _ M h hu
  choose d hd hd' using exists_root M h hu
  choose v hv hv1 hv0 using fun i => exists_vec M h hu i (d i) (hd i) (hd' i)
  let u : Matrix ι ι C := Matrix.of fun k i => v i k
  have hu1 : ∀ i j, (u - 1) i j ∈ IsLocalRing.maximalIdeal C := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [u, hv1]
    · simpa [u, hij] using hv0 j i hij
  have hMu : M * u = u * diagonal d := by
    ext k i
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    exact hv i k
  refine ⟨u, d, hu1, hMu, hd', fun u' d' hu' hM' => ?_⟩
  have r1 := (res_one u).mp hu1
  have r2 := (res_one u').mp hu'
  have hdet : IsUnit u := by
    rw [Matrix.isUnit_iff_isUnit_det]
    apply unit_of_res
    rw [RingHom.map_det, r1, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨U, hU⟩ := hdet
  set w : Matrix ι ι C := (U⁻¹ : (Matrix ι ι C)ˣ) * u' with hw
  have huw : u' = u * w := by rw [hw, ← hU, Units.mul_inv_cancel_left]
  have r3 : (IsLocalRing.residue C).mapMatrix w = 1 := by
    rw [huw, map_mul, r1, one_mul] at r2; exact r2
  have hcomm : diagonal d * w = w * diagonal d' := by
    rw [huw, ← mul_assoc, hMu, mul_assoc, mul_assoc, ← hU] at hM'
    exact (Units.mul_right_inj U).mp hM'
  have he : ∀ i j, (d i - d' j) * w i j = 0 := by
    intro i j
    have := congrFun (congrFun hcomm i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
    rw [sub_mul, this]; ring
  have hd2 : ∀ j, IsLocalRing.residue C (d' j) = IsLocalRing.residue C (M j j) := by
    intro j
    have := congrArg (IsLocalRing.residue C).mapMatrix hM'
    rw [map_mul, map_mul, r2, mul_one, one_mul] at this
    have := congrFun (congrFun this j) j
    simpa using this.symm
  have hd1 : ∀ j, IsLocalRing.residue C (d j) = IsLocalRing.residue C (M j j) := by
    intro j
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hd' j
  constructor
  · funext i
    have hwi : IsUnit (w i i) := by
      apply unit_of_res
      have := congrFun (congrFun r3 i) i
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply_eq] at this
      rw [this]; exact one_ne_zero
    exact (sub_eq_zero.mp (hwi.mul_left_eq_zero.mp (he i i))).symm
  · refine ⟨fun i => w i i, ?_⟩
    rw [huw]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      refine (unit_of_res (d i - d' j) ?_).mul_right_eq_zero.mp (he i j)
      rw [map_sub, hd1, hd2, ← map_sub]
      exact ((hu i j hij).map _).ne_zero
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.MonomialOfComm
section
open Polynomial Matrix

private theorem monomial_eigenbasis {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : A.charpoly.Separable) :
    ∃ (b : Module.Basis (Fin n) K (Fin n → K)) (l : Fin n → K), Function.Injective l ∧
      ∀ i, A *ᵥ b i = l i • b i := by
  classical
  have hnd : A.charpoly.roots.Nodup := Polynomial.nodup_roots hA
  have hcard : A.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, ← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e : A.charpoly.roots.toFinset ≃ Fin n := Finset.equivFinOfCardEq hcard
  let l : Fin n → K := fun i => (e.symm i : K)
  have hl : Function.Injective l := fun i j h => e.symm.injective (Subtype.ext h)
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' A) (l i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    have := (e.symm i).2
    rw [Multiset.mem_toFinset] at this
    exact Polynomial.isRoot_of_mem_roots this
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) l hl v hv
  have hsp : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  refine ⟨Module.Basis.mk hli hsp.ge, l, hl, fun i => ?_⟩
  rw [Module.Basis.mk_apply]
  have := (hv i).apply_eq_smul
  rwa [Matrix.toLin'_apply] at this

private theorem monomial_eigvec {K : Type} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (b : Module.Basis (Fin n) K (Fin n → K)) (l : Fin n → K)
    (hl : Function.Injective l) (hb : ∀ i, A *ᵥ b i = l i • b i) (v : Fin n → K) (c : K)
    (hv : A *ᵥ v = c • v) (j : Fin n) (hj : l j ≠ c) : b.repr v j = 0 := by
  classical
  have h1 : (b.coord j) ∘ₗ (Matrix.toLin' A) = l j • b.coord j := by
    refine b.ext fun i => ?_
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, hb, map_smul, LinearMap.smul_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    split_ifs with h
    · rw [h]
    · simp
  have h2 := LinearMap.congr_fun h1 v
  simp only [LinearMap.comp_apply, Matrix.toLin'_apply, hv, map_smul, LinearMap.smul_apply,
      Module.Basis.coord_apply, smul_eq_mul] at h2
  have h3 : (l j - c) * b.repr v j = 0 := by rw [sub_mul, h2, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hj)

private theorem monomial_eigvec' {K : Type} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (b : Module.Basis (Fin n) K (Fin n → K)) (l : Fin n → K)
    (hl : Function.Injective l) (hb : ∀ i, A *ᵥ b i = l i • b i) (v : Fin n → K)
    (i : Fin n) (hv : A *ᵥ v = l i • v) : ∃ a : K, v = a • b i := by
  classical
  refine ⟨b.repr v i, b.ext_elem fun j => ?_⟩
  by_cases h : i = j
  · subst h; simp
  · rw [monomial_eigvec A b l hl hb v _ hv j (fun h' => h (hl h').symm)]
    simp [h]

theorem UpperTheory.V.AlgebraTools.monomialOfComm :
    ∀ (K G : Type) [Field K] [IsAlgClosed K] [Group G] (n : ℕ) (r : G →* Matrix (Fin n) (Fin n) K), Submodule.span K (Set.range r) = ⊤ →
      ∀ (N : Subgroup G) [N.Normal], (∀ g ∈ N, ∀ h ∈ N, r g * r h = r h * r g) → (∃ u ∈ N, (r u).charpoly.Separable) →
      ∃ (b : Module.Basis (Fin n) K (Fin n → K)) (π : G →* Equiv.Perm (Fin n)), N ≤ π.ker ∧
        (∀ g i, ∃ a : K, r g *ᵥ b i = a • b (π g i)) ∧ ∀ i j, ∃ g, π g i = j := by
  classical
  intro K G _ _ _ n r hspan N hN hcomm ⟨u, hu, hsep⟩
  obtain ⟨b, l, hl, hb⟩ := monomial_eigenbasis (r u) hsep
  have hne : ∀ g i, r g *ᵥ b i ≠ 0 := by
    intro g i h
    have : r g⁻¹ *ᵥ (r g *ᵥ b i) = b i := by
      rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
    rw [h, Matrix.mulVec_zero] at this
    exact b.ne_zero i this.symm
  have hNs : ∀ h ∈ N, ∀ i, ∃ a : K, r h *ᵥ b i = a • b i := by
    intro h hh i
    refine monomial_eigvec' (r u) b l hl hb _ i ?_
    rw [Matrix.mulVec_mulVec, hcomm u hu h hh, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_smul]
  have hex : ∀ g i, ∃ j, ∃ a : K, r g *ᵥ b i = a • b j := by
    intro g i
    obtain ⟨c, hc⟩ := hNs (g⁻¹ * u * g⁻¹⁻¹) (hN.conj_mem u hu g⁻¹) i
    have hv : r u *ᵥ (r g *ᵥ b i) = c • (r g *ᵥ b i) := by
      rw [← Matrix.mulVec_smul, ← hc, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← map_mul,
        ← map_mul]
      congr 2
      group
    by_cases hc' : ∃ j, l j = c
    · obtain ⟨j, rfl⟩ := hc'
      exact ⟨j, monomial_eigvec' (r u) b l hl hb _ j hv⟩
    · exfalso
      apply hne g i
      refine b.ext_elem fun j => ?_
      rw [monomial_eigvec (r u) b l hl hb _ _ hv j (fun h => hc' ⟨j, h⟩)]
      simp
  choose f hf using hex
  have huniq : ∀ g i j (a : K), r g *ᵥ b i = a • b j → f g i = j := by
    intro g i j a h
    obtain ⟨a', ha'⟩ := hf g i
    by_contra hij
    have h1 := congrArg (fun v => b.repr v j) (h.symm.trans ha')
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, hij,
      if_true, if_false, smul_eq_mul, mul_one, mul_zero] at h1
    apply hne g i
    rw [h, h1, zero_smul]
  let F : G →* Function.End (Fin n) :=
    { toFun := f
      map_one' := funext fun i => huniq 1 i i 1 (by simp)
      map_mul' := fun g h => funext fun i => by
        obtain ⟨a, ha⟩ := hf h i
        obtain ⟨a', ha'⟩ := hf g (f h i)
        refine huniq (g * h) i (f g (f h i)) (a * a') ?_
        rw [map_mul, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_smul, ha', smul_smul] }
  have hπ : ∀ g i, F.toHomPerm g i = f g i := fun g i => rfl
  refine ⟨b, F.toHomPerm, ?_, ?_, ?_⟩
  · intro h hh
    rw [MonoidHom.mem_ker]
    ext i
    obtain ⟨a, ha⟩ := hNs h hh i
    rw [hπ, huniq h i i a ha]
    rfl
  · intro g i
    exact hf g i
  · intro i j
    by_contra hno
    push Not at hno
    let φ : Matrix (Fin n) (Fin n) K →ₗ[K] K :=
      { toFun := fun M => b.repr (M *ᵥ b i) j
        map_add' := fun M M' => by simp [Matrix.add_mulVec]
        map_smul' := fun c M => by simp [Matrix.smul_mulVec] }
    have hle : Submodule.span K (Set.range r) ≤ LinearMap.ker φ := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      obtain ⟨a, ha⟩ := hf g i
      have hij : f g i ≠ j := hno g
      change b.repr (r g *ᵥ b i) j = 0
      rw [ha]
      simp [hij]
    have hM : LinearMap.toMatrix' ((b.coord i).smulRight (b j)) ∈ LinearMap.ker φ :=
      hle (hspan ▸ Submodule.mem_top)
    change b.repr (LinearMap.toMatrix' ((b.coord i).smulRight (b j)) *ᵥ b i) j = 0 at hM
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix'] at hM
    simp at hM
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.PermChar
section
open Polynomial Matrix

private theorem UpperTheory.V.AlgebraTools.perm_four_pow_three_or_four :
    ∀ σ : Equiv.Perm (Fin 4), σ ^ 3 = 1 ∨ σ ^ 4 = 1 := by
  set_option maxRecDepth 100000 in
  decide

theorem UpperTheory.V.AlgebraTools.permChar :
    ∀ (G K : Type) [Group G] [Field K] (π : G →* Equiv.Perm (Fin 4)) (χ : G →* Kˣ), π.ker ≤ χ.ker → 0 < orderOf χ ∧ orderOf χ ≤ 4 := by
  intro G K _ _ π χ hker
  have hχ : ∀ g : G, χ g ^ 3 = 1 ∨ χ g ^ 4 = 1 := fun g => by
    rcases UpperTheory.V.AlgebraTools.perm_four_pow_three_or_four (π g) with h | h
    · left
      have hm : g ^ 3 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, h]
      have hm' := hker hm
      rwa [MonoidHom.mem_ker, map_pow] at hm'
    · right
      have hm : g ^ 4 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, h]
      have hm' := hker hm
      rwa [MonoidHom.mem_ker, map_pow] at hm'
  have hall : (∀ g : G, χ g ^ 3 = 1) ∨ (∀ g : G, χ g ^ 4 = 1) := by
    by_contra hne
    push_neg at hne
    obtain ⟨⟨g, hg⟩, ⟨g', hg'⟩⟩ := hne
    have h4 : χ g ^ 4 = 1 := (hχ g).resolve_left hg
    have h3 : χ g' ^ 3 = 1 := (hχ g').resolve_right hg'
    rcases hχ (g * g') with h | h
    · rw [map_mul, mul_pow, h3, mul_one] at h
      exact hg h
    · rw [map_mul, mul_pow, h4, one_mul] at h
      exact hg' h
  have key : ∀ k, 0 < k → (∀ g : G, χ g ^ k = 1) → 0 < orderOf χ ∧ orderOf χ ≤ k := by
    intro k hk0 h
    have hp : χ ^ k = 1 := MonoidHom.ext fun g => by
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]
      exact h g
    exact ⟨orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨k, hk0, hp⟩),
      orderOf_le_of_pow_eq_one hk0 hp⟩
  rcases hall with h | h
  · obtain ⟨a, b⟩ := key 3 (by norm_num) h
    exact ⟨a, b.trans (by norm_num)⟩
  · exact key 4 (by norm_num) h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.RelWeight
section
open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.relWeight :
    ∀ (A : Type) [CommGroup A] (ι : Type) [Fintype ι] (a : ι → A), (∀ i j, i ≠ j → ¬ IsOfFinOrder (a i / a j)) →
      ∃ w : ι → ℤ, Function.Injective w ∧ ∀ m : ι → ℤ, ∏ i, a i ^ m i = 1 → ∑ i, m i * w i = 0 := by
  intro A _ ι _ a ha
  classical
  obtain ⟨P, hP⟩ : ∃ P : (ι → ℤ) → A, ∀ m, P m = ∏ i, a i ^ m i := ⟨_, fun _ => rfl⟩
  have hPadd : ∀ m n, P (m + n) = P m * P n := by
    intro m n
    rw [hP, hP, hP, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.add_apply, _root_.zpow_add]
  have hPsmul : ∀ (c : ℤ) m, P (c • m) = P m ^ c := by
    intro c m
    rw [hP, hP, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, _root_.zpow_mul]
  have hPsub : ∀ m n, P (m - n) = P m / P n := by
    intro m n
    rw [eq_div_iff_mul_eq', ← hPadd, sub_add_cancel]
  have hPe : ∀ i, P (Pi.single i 1) = a i := by
    intro i
    rw [hP]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  let L : Submodule ℤ (ι → ℤ) :=
    { carrier := {m | ∃ k : ℤ, k ≠ 0 ∧ P (k • m) = 1}
      add_mem' := by
        rintro m n ⟨k, hk, hm⟩ ⟨l, hl, hn⟩
        refine ⟨k * l, mul_ne_zero hk hl, ?_⟩
        have e1 : P ((k * l) • m) = 1 := by rw [mul_comm, mul_smul, hPsmul, hm, _root_.one_zpow]
        have e2 : P ((k * l) • n) = 1 := by rw [mul_smul, hPsmul, hn, _root_.one_zpow]
        rw [smul_add, hPadd, e1, e2, one_mul]
      zero_mem' := ⟨1, one_ne_zero, by simp [hP]⟩
      smul_mem' := by
        rintro c m ⟨k, hk, hm⟩
        exact ⟨k, hk, by rw [smul_comm, hPsmul, hm, _root_.one_zpow]⟩ }
  haveI : Module.IsTorsionFree ℤ ((ι → ℤ) ⧸ L) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x hx => by
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective L x
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨k, hk, h⟩ := hx
      by_cases hr : r = 0
      · exact Or.inl hr
      · right
        rw [Submodule.Quotient.mk_eq_zero]
        exact ⟨k * r, mul_ne_zero hk hr, by rw [mul_smul]; exact h⟩
  let q : ι → (ι → ℤ) ⧸ L := fun i => L.mkQ (Pi.single i 1)
  have hq : ∀ i j, i ≠ j → q i - q j ≠ 0 := by
    intro i j hij h
    rw [← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨k, hk, hk1⟩ := h
    apply ha i j hij
    rw [isOfFinOrder_iff_zpow_eq_one]
    refine ⟨k, hk, ?_⟩
    rw [hPsmul, hPsub, hPe, hPe] at hk1
    exact hk1
  have hex : ∃ f : Module.Dual ℤ ((ι → ℤ) ⧸ L), ∀ i j, i ≠ j → f (q i) ≠ f (q j) := by
    by_contra hno
    push_neg at hno
    let s : Finset (ι × ι) := Finset.univ.filter fun x => x.1 ≠ x.2
    let p : ι × ι → Submodule ℤ (Module.Dual ℤ ((ι → ℤ) ⧸ L)) :=
      fun x => LinearMap.ker (Module.Dual.eval ℤ _ (q x.1 - q x.2))
    have hc : ⋃ x ∈ s, (p x : Set (Module.Dual ℤ ((ι → ℤ) ⧸ L))) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro f
      obtain ⟨i, j, hij, h⟩ := hno f
      simp only [Set.mem_iUnion]
      refine ⟨(i, j), by simp [s, hij], ?_⟩
      simp [p, h]
    obtain ⟨⟨i, j⟩, hx, hfi⟩ := Submodule.exists_finiteIndex_of_cover hc
    have hij : i ≠ j := by simpa [s] using hx
    apply hq i j hij
    rw [← Module.forall_dual_apply_eq_zero_iff ℤ]
    intro f
    have h1 := AddSubgroup.nsmul_index_mem (p (i, j)).toAddSubgroup f
    have h2 : ((p (i, j)).toAddSubgroup.index • f) (q i - q j) = 0 := h1
    rw [LinearMap.smul_apply, smul_eq_zero] at h2
    exact h2.resolve_left hfi.index_ne_zero
  obtain ⟨f, hf⟩ := hex
  refine ⟨fun i => f (q i), fun i j h => ?_, fun m hm => ?_⟩
  · by_contra hij
    exact hf i j hij h
  · have hm0 : L.mkQ m = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨1, one_ne_zero, by rw [one_smul, hP]; exact hm⟩
    have hsum : m = ∑ i, m i • (Pi.single i 1 : ι → ℤ) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
    have h3 : ∑ i, m i • q i = 0 := by
      rw [← hm0]
      conv_rhs => rw [hsum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [q, map_sum, LinearMap.map_smul]
    calc ∑ i, m i * f (q i) = f (∑ i, m i • q i) := by simp [map_sum]
      _ = 0 := by rw [h3, map_zero]
end

