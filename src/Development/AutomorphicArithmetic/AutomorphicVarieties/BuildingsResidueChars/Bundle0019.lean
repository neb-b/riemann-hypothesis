module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModBotOfMemAdjoinCommuting
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem adjoin_alg {V : Type} [AddCommGroup V] [Module ℂ V] {R : Type} [CommRing R] [Algebra ℂ R]
    (φ : R →ₐ[ℂ] Module.End ℂ V) (S : Submodule ℂ V) (t : Set R) (ht : ∀ r ∈ t, AlgMod S ⊥ (φ r)) :
    ∀ r ∈ Algebra.adjoin ℂ t, AlgMod S ⊥ (φ r) := by
  let I : Ideal R :=
    { carrier := {r | ∀ x ∈ S, φ r x = 0}
      add_mem' := fun {a b} ha hb x hx => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add (f := _), LinearMap.add_apply, ha x hx, hb x hx, add_zero]
      zero_mem' := fun x _ => by simp
      smul_mem' := fun c r hr x hx => by
        simp only [Set.mem_setOf_eq] at hr ⊢
        rw [smul_eq_mul, map_mul, Module.End.mul_apply, hr x hx, map_zero] }
  have hint : ∀ r ∈ t, IsIntegral ℂ (Ideal.Quotient.mkₐ ℂ I r) := by
    intro r hr
    obtain ⟨p, hp, hx⟩ := ht r hr
    refine ⟨p, hp, ?_⟩
    rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    intro x hxS
    have hx' := hx x hxS
    rw [Polynomial.aeval_algHom_apply, Submodule.mem_bot] at hx'
    exact hx'
  intro r hr
  have h1 : Ideal.Quotient.mkₐ ℂ I r ∈ Algebra.adjoin ℂ (Ideal.Quotient.mkₐ ℂ I '' t) := by
    rw [Algebra.adjoin_image]
    exact ⟨r, hr, rfl⟩
  have h2 : Ideal.Quotient.mkₐ ℂ I r ∈ integralClosure ℂ (R ⧸ I) := by
    refine Algebra.adjoin_le ?_ h1
    rintro _ ⟨r', hr', rfl⟩
    exact hint r' hr'
  obtain ⟨p, hp, hev⟩ := h2
  refine ⟨p, hp, fun x hx => ?_⟩
  rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem] at hev
  rw [Polynomial.aeval_algHom_apply, Submodule.mem_bot]
  exact hev x hx

theorem UpperTheory.algMod_bot_of_mem_adjoin_commuting :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (s : Set (Module.End ℂ M)), (∀ x ∈ s, ∀ y ∈ s, x * y = y * x) → (∀ T ∈ s, AlgMod S ⊥ T) → ∀ T ∈ Algebra.adjoin ℂ s, AlgMod S ⊥ T := by
  intro M _ _ S s hcomm hs T hT
  letI : IsMulCommutative (Algebra.adjoin ℂ s) :=
    Algebra.isMulCommutative_adjoin ℂ (fun x hx y hy _ => hcomm x hx y hy)
  open scoped IsMulCommutative in
    have hmem : (⟨T, hT⟩ : Algebra.adjoin ℂ s) ∈
        Algebra.adjoin ℂ (((↑) : Algebra.adjoin ℂ s → Module.End ℂ M) ⁻¹' s) := by
      rw [Algebra.adjoin_adjoin_coe_preimage]
      trivial
    exact adjoin_alg (Algebra.adjoin ℂ s).val S
      (((↑) : Algebra.adjoin ℂ s → Module.End ℂ M) ⁻¹' s)
      (fun r hr => hs r hr) ⟨T, hT⟩ hmem
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModOfInjectiveIntertwining
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem UpperTheory.quantum_determinant_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

theorem UpperTheory.algMod_of_injective_intertwining :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (f : M →ₗ[ℂ] N) (E : Fin n → Fin n → Module.End ℂ M) (E' : Fin n → Fin n → Module.End ℂ N), (∀ i j x, f (E i j x) = E' i j (f x)) → ∀ u x, f (Formalism.REAL.qdet E u x) = Formalism.REAL.qdet E' u (f x) := by
  intro M _ _ N _ _ n f E E' h u x
  let S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ N) :=
    { carrier := {p | ∀ y, f (p.1 y) = p.2 (f y)}
      mul_mem' := fun {a b} ha hb y => (ha _).trans (congrArg a.2 (hb y))
      add_mem' := fun {a b} ha hb y => by
        simp only [Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add (f := _), ha y, hb y]
      algebraMap_mem' := fun c y => map_smul f c y }
  let Z : Fin n → Fin n → S := fun i j => ⟨(E i j, E' i j), h i j⟩
  have h1 : (Formalism.REAL.qdet Z u).1.1 = Formalism.REAL.qdet E u :=
    UpperTheory.quantum_determinant_map ((AlgHom.fst ℂ _ _).comp S.val) Z u
  have h2 : (Formalism.REAL.qdet Z u).1.2 = Formalism.REAL.qdet E' u :=
    UpperTheory.quantum_determinant_map ((AlgHom.snd ℂ _ _).comp S.val) Z u
  rw [← h1, ← h2]
  exact (Formalism.REAL.qdet Z u).2 x
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockDiagConjUnipotentLinear
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private def LowZ {n : ℕ} {R : Type} [CommRing R] (r : ℕ) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, r ≤ (i : ℕ) → (j : ℕ) < r → M i j = 0

private theorem LowZ.mul {n r : ℕ} {R : Type} [CommRing R] {M N : Matrix (Fin n) (Fin n) R}
    (hM : LowZ r M) (hN : LowZ r N) : LowZ r (M * N) := fun i j hi hj => by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (k : ℕ) r with hk | hk
  · rw [hM i k hi hk, zero_mul]
  · rw [hN k j hk hj, mul_zero]

private theorem lower_zero_first_block_embedding {r s : ℕ} {R : Type} [CommRing R] (g : GL (Fin r) R) :
    LowZ r (emb (e1 r s) g).val := fun i j hi hj => by
  have hij : i ≠ j := fun h => by subst h; omega
  rw [coe_emb, Matrix.add_apply, Matrix.one_apply_ne hij, extendByZero_apply_eq_zero_of_row_not_mem, add_zero]
  intro k hk
  have := congrArg Fin.val hk
  simp at this
  omega

private theorem lower_zero_second_block_embedding {r s : ℕ} {R : Type} [CommRing R] (g : GL (Fin s) R) :
    LowZ r (emb (e2 r s) g).val := fun i j hi hj => by
  have hij : i ≠ j := fun h => by subst h; omega
  rw [coe_emb, Matrix.add_apply, Matrix.one_apply_ne hij, matrixExtendByZero_apply_of_outside_col, add_zero]
  intro k hk
  have := congrArg Fin.val hk
  simp at this
  omega

private theorem blockEntry_eq_sum {n r : ℕ} {S : Type} [CommRing S] (Y : UPos n r → S) :
    blockEntry Y = ∑ q : UPos n r, Matrix.single q.1.1 q.1.2 (Y q) := by
  ext i j
  rw [blockEntry_apply, Matrix.sum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨(i, j), h⟩ : UPos n r)]
    · simp
    · intro q _ hq
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hq rfl
    · simp
  · symm
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact h q.2

private theorem conj_blockEntry {n r : ℕ} {S : Type} [CommRing S] {M N : Matrix (Fin n) (Fin n) S}
    (hM : LowZ r M) (hN : LowZ r N) (Y : UPos n r → S) :
    M * blockEntry Y * N = blockEntry (fun p : UPos n r => ∑ q : UPos n r, M p.1.1 q.1.1 * N q.1.2 p.1.2 * Y q) := by
  ext i j
  have h0 : (M * blockEntry Y * N) i j = ∑ q : UPos n r, M i q.1.1 * N q.1.2 j * Y q := by
    rw [blockEntry_eq_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_zero, ite_and, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, ite_mul, zero_mul]
    ring
  rw [h0, blockEntry_apply]
  split_ifs with h
  · rfl
  · refine Finset.sum_eq_zero fun q _ => ?_
    rcases lt_or_ge (i : ℕ) r with hi | hi
    · rw [hN _ j q.2.2 (by omega), mul_zero, zero_mul]
    · rw [hM i _ hi q.2.1, zero_mul, zero_mul]

theorem UpperTheory.blockDiag_conj_unipotent_linear :
    ∀ (R : Type) [CommRing R] (r s : ℕ) (m₁ : GL (Fin r) R) (m₂ : GL (Fin s) R), ∃ c : UPos (r + s) r → UPos (r + s) r → R, ∀ (S : Type) [CommRing S] (f : R →+* S) (Y : UPos (r + s) r → S), Matrix.GeneralLinearGroup.map f (blk m₁ m₂) * unipGL Y = unipGL (fun p => ∑ q, f (c p q) * Y q) * Matrix.GeneralLinearGroup.map f (blk m₁ m₂) := by
  intro R _ r s m₁ m₂
  have h1 : LowZ r (blk m₁ m₂).val := (lower_zero_first_block_embedding m₁).mul (lower_zero_second_block_embedding m₂)
  have h2 : LowZ r ((blk m₁ m₂)⁻¹).val := by
    rw [blk, _root_.mul_inv_rev, ← map_inv, ← map_inv]
    exact (lower_zero_second_block_embedding _).mul (lower_zero_first_block_embedding _)
  generalize blk m₁ m₂ = m at h1 h2
  refine ⟨fun p q => m.val p.1.1 q.1.1 * (m⁻¹).val q.1.2 p.1.2, fun S _ f Y => ?_⟩
  rw [← mul_inv_eq_iff_eq_mul, ← map_inv]
  refine Units.ext ?_
  have hmm : m.val.map f * (m⁻¹).val.map f = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero f) (map_one f)]
  have h1' : LowZ r (m.val.map f) := fun i j hi hj => by rw [Matrix.map_apply, h1 i j hi hj, map_zero]
  have h2' : LowZ r ((m⁻¹).val.map f) := fun i j hi hj => by rw [Matrix.map_apply, h2 i j hi hj, map_zero]
  change m.val.map f * (1 + blockEntry Y) * (m⁻¹).val.map f = 1 + blockEntry _
  rw [mul_add, add_mul, mul_one, hmm, conj_blockEntry h1' h2']
  simp only [Matrix.map_apply, map_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingAdelicNormCompat
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem vecMul_emb {a n : ℕ} (e : Fin a ↪ Fin n) {R : Type} [CommRing R] (g : GL (Fin a) R) (y : Fin n → R) :
    y ᵥ* (emb e g).val = y + ((fun i => y (e i)) ᵥ* g.val - fun i => y (e i)) ᵥ* (inc e R)ᵀ := by
  have h : y ᵥ* inc e R = fun i => y (e i) := by
    ext i
    simp [inc, vecMul, dotProduct]
  rw [coe_emb, vecMul_add, vecMul_one, ext0, ← vecMul_vecMul, ← vecMul_vecMul, h, vecMul_sub, vecMul_one]

private theorem norm_emb {a n : ℕ} (e : Fin a ↪ Fin n) {R : Type} [NormedField R] (g : GL (Fin a) R)
    (hg : ∀ y, Reduction.euclidNorm (y ᵥ* g.val) = Reduction.euclidNorm y) (y : Fin n → R) :
    Reduction.euclidNorm (y ᵥ* (emb e g).val) = Reduction.euclidNorm y := by
  have h := hg fun i => y (e i)
  unfold Reduction.euclidNorm at h ⊢
  rw [Real.sqrt_inj (by positivity) (by positivity)] at h
  congr 1
  rw [← Finset.sum_add_sum_compl (Finset.univ.map e), ← Finset.sum_add_sum_compl (Finset.univ.map e),
    Finset.sum_map, Finset.sum_map, ← h, vecMul_emb]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have : ∀ z : Fin a → R, (z ᵥ* (inc e R)ᵀ) (e j) = z j := fun z => by simp [inc, vecMul, dotProduct]
    rw [Pi.add_apply, this, Pi.sub_apply, add_sub_cancel]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : ∀ k, j ≠ e k := fun k hk => by simp [hk] at hj
    have : ∀ z : Fin a → R, (z ᵥ* (inc e R)ᵀ) j = 0 := fun z => by simp [inc, vecMul, dotProduct, hj']
    rw [Pi.add_apply, this, add_zero]

private theorem emb_transfer {a n : ℕ} (e : Fin a ↪ Fin n) {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (g : GL (Fin a) R) (g' : GL (Fin a) S) (h' : GL (Fin n) S) (hg : ∀ i j, g'.val i j = f (g.val i j))
    (hh : ∀ i j, h'.val i j = f ((emb e g).val i j)) : h' = emb e g' := by
  have h1 : g' = Matrix.GeneralLinearGroup.map f g := Units.ext (Matrix.ext hg)
  have h2 : h' = Matrix.GeneralLinearGroup.map f (emb e g) := Units.ext (Matrix.ext hh)
  rw [h1, h2, emb_map]

private theorem int_emb {a n : ℕ} (e : Fin a ↪ Fin n) {F : Type} [Field F] [ValuativeRel F] (g : GL (Fin a) F)
    (hg : g ∈ GLnLocal.integralGL F a) : emb e g ∈ GLnLocal.integralGL F n := by
  obtain ⟨u, rfl⟩ := hg
  exact ⟨emb e u, emb_transfer e (ValuativeRel.valuation F).integer.subtype u _ _ (fun _ _ => rfl) (fun _ _ => rfl)⟩

theorem UpperTheory.blockEmbedding_adelic_norm_compat :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n), ∀ k ∈ Reduction.maxCompact (K := K) (n := a), emb e k ∈ Reduction.maxCompact (K := K) (n := n) := by
  intro K _ _ a n e k hk
  rw [Reduction.mem_maxCompact] at hk ⊢
  refine ⟨fun w => ?_, fun v => ?_⟩
  · rw [emb_transfer e (Reduction.infEval w) k (Reduction.infAt w k) (Reduction.infAt w (emb e k))
      (fun i j => Reduction.infAt_apply w k i j) (fun i j => Reduction.infAt_apply w _ i j), Reduction.mem_archCompact]
    exact norm_emb e _ (Reduction.mem_archCompact.1 (hk.1 w))
  · rw [emb_transfer e (Reduction.finEval v) k (Reduction.finAt v k) (Reduction.finAt v (emb e k))
      (fun i j => Reduction.finAt_apply v k i j) (fun i j => Reduction.finAt_apply v _ i j)]
    exact int_emb e _ (hk.2 v)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingCommInfEmbAndExp
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem exp_block_extension (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n) (Y : ArchMatrix K a) :
    (1 : ArchMatrix K n) + (show ArchMatrix K n from ext0 (R := mixedSpace K) e (NormedSpace.exp Y - 1 : ArchMatrix K a)) =
      NormedSpace.exp (show ArchMatrix K n from ext0 (R := mixedSpace K) e Y) := by
  have hsm : ∀ (c : ℝ) (Z : Matrix (Fin a) (Fin a) (mixedSpace K)), ext0 e (c • Z) = c • ext0 e Z := by
    intro c Z
    simp only [ext0, Matrix.mul_smul, Matrix.smul_mul]
  let g : ArchMatrix K a →ₗ[ℝ] ArchMatrix K n :=
    { toFun := fun X => ext0 (R := mixedSpace K) e X
      map_add' := fun X Z => matrixExtendByZero_add e X Z
      map_smul' := fun c X => hsm c X }
  have hg : Continuous g := LinearMap.continuous_of_finiteDimensional g
  have hpow : ∀ k : ℕ, (g Y) ^ (k + 1) = g (Y ^ (k + 1)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ Y (k + 1)]
      exact matrixExtendByZero_mul e _ _
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) Y).map g hg
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (g Y)
  have h3 : HasSum (fun k : ℕ => if k = 0 then (1 - g 1 : ArchMatrix K n) else 0) (1 - g 1) :=
    hasSum_ite_eq 0 _
  have h4 := h1.add h3
  have heq : (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • (g Y) ^ k) =
      fun k : ℕ => g (((k.factorial : ℝ)⁻¹) • Y ^ k) + if k = 0 then (1 - g 1) else 0 := by
    funext k
    cases k with
    | zero => simp
    | succ k => rw [if_neg (Nat.succ_ne_zero k), add_zero, map_smul, hpow]
  rw [heq] at h2
  have h5 := h2.unique h4
  have hsub : g (NormedSpace.exp Y - 1) = g (NormedSpace.exp Y) - g 1 := map_sub g _ _
  change (1 : ArchMatrix K n) + g (NormedSpace.exp Y - 1) = NormedSpace.exp (g Y)
  rw [hsub, h5]
  abel

private theorem UpperTheory.prodEquiv_apply_eq_map_fst_snd (K : Type) [Field K] [NumberField K] (m : ℕ)
    (g : AdelicGLn.AdelicGL K m) :
    AdelicGLn.prodEquiv K m g =
      (GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g,
        GeneralLinearGroup.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g) := by
  ext i j <;> rfl

private theorem UpperTheory.archEquiv_symm_apply_eq_map_mixedSpace (K : Type) [Field K] [NumberField K] (m : ℕ) (x : archGroup K m) :
    (archEquiv K m).symm x =
      GeneralLinearGroup.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom
        (show GL (Fin m) (mixedSpace K) from (x : (ArchMatrix K m)ˣ)) := by
  ext i j
  rfl

theorem UpperTheory.blockEmbedding_comm_infEmb_and_exp :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n), (∀ x, emb e (infEmb K a x) = infEmb K n (embArch e x)) ∧ ∀ Y : Matrix (Fin a) (Fin a) (mixedSpace K), embArch e ((isExpLieAlgebra K a).expG ((isExpLieAlgebra K a).ofLie (toLie K a Y))) = (isExpLieAlgebra K n).expG ((isExpLieAlgebra K n).ofLie (toLie K n (ext0 e Y))) := by
  intro K _ _ a n e
  refine ⟨fun x => ?_, fun Y => ?_⟩
  · apply (AdelicGLn.prodEquiv K n).injective
    have hx := prodEquiv_infEmb (K := K) (n := a) x
    rw [UpperTheory.prodEquiv_apply_eq_map_fst_snd] at hx
    rw [Prod.mk.injEq] at hx
    rw [UpperTheory.prodEquiv_apply_eq_map_fst_snd, prodEquiv_infEmb]
    refine Prod.ext ?_ ?_
    · refine (emb_map e (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
        (infEmb K a x)).trans ((congrArg (emb e) hx.1).trans ?_)
      rw [UpperTheory.archEquiv_symm_apply_eq_map_mixedSpace, UpperTheory.archEquiv_symm_apply_eq_map_mixedSpace]
      exact (emb_map e _ _).symm
    · exact (emb_map e (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
        (infEmb K a x)).trans ((congrArg (emb e) hx.2).trans (map_one _))
  · apply Subtype.ext
    apply Units.ext
    exact exp_block_extension K e Y
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingFiniteAdelicGLCompatContinuous
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem continuous_emb' {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {a n : ℕ}
    (e : Fin a ↪ Fin n) : Continuous (emb e : GL (Fin a) R → GL (Fin n) R) := by
  refine Continuous.units_map (embM (R := R) e) ?_
  change Continuous fun X : Matrix (Fin a) (Fin a) R => 1 + inc e R * (X - 1) * (inc e R)ᵀ
  exact continuous_const.add
    ((continuous_const.matrix_mul (continuous_id.sub continuous_const)).matrix_mul continuous_const)

private theorem prodEquiv_eq (K : Type) [Field K] [NumberField K] (n : ℕ) (g : AdelicGLn.AdelicGL K n) :
    AdelicGLn.prodEquiv K n g =
      (Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g,
        Matrix.GeneralLinearGroup.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g) := by
  refine Prod.ext ?_ ?_
  · ext i j : 2
    exact AdelicGLn.prodEquiv_apply_fst K n g i j
  · ext i j : 2
    exact AdelicGLn.prodEquiv_apply_snd K n g i j

private theorem prodEquiv_emb (K : Type) [Field K] [NumberField K] {a n : ℕ} (e : Fin a ↪ Fin n)
    (g : AdelicGLn.AdelicGL K a) :
    AdelicGLn.prodEquiv K n (emb e g) =
      (emb e (AdelicGLn.prodEquiv K a g).1, emb e (AdelicGLn.prodEquiv K a g).2) := by
  rw [prodEquiv_eq, prodEquiv_eq]
  exact Prod.ext
    (emb_map e (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g)
    (emb_map e (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) g)

theorem UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n), (∀ y, emb e (finEmb K a y) = finEmb K n (emb e y)) ∧ (∀ γ, emb e (AdelicGLn.diagonal K a γ) = AdelicGLn.diagonal K n (emb e γ)) ∧ Continuous (emb e : AdelicGLn.FiniteAdelicGL K a → AdelicGLn.FiniteAdelicGL K n) := by
  intro K _ _ a n e
  refine ⟨fun y => ?_, fun γ => ?_, continuous_emb' e⟩
  · apply (AdelicGLn.prodEquiv K n).injective
    rw [prodEquiv_emb, prodEquiv_finEmb, prodEquiv_finEmb, map_one]
  · exact (emb_map e (algebraMap K (AdeleRing (𝓞 K) K)) γ).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermConvolutionArch
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTerm_convolution_arch :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (μ : Measure (archGroup K n)) [μ.IsHaarMeasure] (φ ψ : AdelicGLn.AdelicGL K n → ℂ) (D : archGroup K n → ℂ), Continuous φ → Continuous D → HasCompactSupport D → (∀ g, ψ g = ∫ y, φ (g * infEmb K n y) * D y ∂μ) → ∀ g, constantTerm r ψ g = ∫ y, constantTerm r φ (g * infEmb K n y) * D y ∂μ := by
  intro K _ _ n r _ _ μ _ φ ψ D hφ hD hDc hψ g
  obtain ⟨C, hC, hFC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  let f : (UPos n r → AdeleRing (𝓞 K) K) × archGroup K n → ℂ :=
    fun p => φ (unipGL p.1 * g * infEmb K n p.2) * D p.2
  have hfc : Continuous f := by
    refine Continuous.mul (hφ.comp ?_) (hD.comp continuous_snd)
    exact ((continuous_unipGL.comp continuous_fst).mul continuous_const).mul
      (continuous_infEmb.comp continuous_snd)
  have hint : Integrable f (((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod μ) := by
    have h1 : IntegrableOn f (C ×ˢ tsupport D) ((unipMeasure K n r).prod μ) :=
      hfc.continuousOn.integrableOn_compact (hC.prod hDc)
    have h2 : IntegrableOn f (unipFundamentalDomain K n r ×ˢ Set.univ) ((unipMeasure K n r).prod μ) := by
      refine h1.of_forall_diff_eq_zero (measurableSet_unipFundamentalDomain.prod MeasurableSet.univ) ?_
      rintro ⟨X, y⟩ ⟨⟨hX, -⟩, hn⟩
      have hy : y ∉ tsupport D := fun hy => hn ⟨hFC hX, hy⟩
      show φ (unipGL X * g * infEmb K n y) * D y = 0
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    have h3 : ((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod μ
        = ((unipMeasure K n r).prod μ).restrict (unipFundamentalDomain K n r ×ˢ Set.univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [h3]
    exact h2
  have key := integral_integral_swap (f := fun X y => φ (unipGL X * g * infEmb K n y) * D y) hint
  show ∫ X in unipFundamentalDomain K n r, ψ (unipGL X * g) ∂unipMeasure K n r
    = ∫ y, (∫ X in unipFundamentalDomain K n r, φ (unipGL X * (g * infEmb K n y)) ∂unipMeasure K n r) * D y ∂μ
  simp_rw [hψ]
  refine key.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ∫ X in unipFundamentalDomain K n r, φ (unipGL X * g * infEmb K n y) * D y ∂unipMeasure K n r
    = (∫ X in unipFundamentalDomain K n r, φ (unipGL X * (g * infEmb K n y)) ∂unipMeasure K n r) * D y
  rw [← integral_mul_const]
  simp_rw [mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermUnipotentLeftInvariant
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTerm_unipotent_left_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ),
      IsLeftInvariant φ → ∀ (X : UPos n r → AdeleRing (𝓞 K) K) g,
        constantTerm (r := r) φ (unipGL X * g) = constantTerm (r := r) φ g := by
  intro K _ _ n r φ hφ X g
  have hfd := isAddFundamentalDomain_unipFundamentalDomain (K := K) (n := n) (r := r)
  have hfd' := hfd.vadd_of_comm X
  rw [constantTerm_eq_setIntegral hφ hfd, constantTerm_eq_setIntegral hφ hfd' g, ← Set.image_vadd]
  simp only [vadd_eq_add]
  rw [(measurePreserving_add_left (unipMeasure K n r) X).setIntegral_image_emb
      (MeasurableEquiv.addLeft X).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
  show φ (unipGL Y * (unipGL X * g)) = φ (unipGL (X + Y) * g)
  rw [add_comm X Y, unipGL_add, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ContinuousConstantTerm
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem cont_setIntegral {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    (μ : Measure Y) (f : X → Y → ℂ) (hf : Continuous f.uncurry) {s C : Set Y} (hs : MeasurableSet s)
    (hC : IsCompact C) (hsC : s ⊆ C) (hμ : μ s < ⊤) (hi : ∀ x, IntegrableOn (f x) s μ) :
    Continuous fun x => ∫ y in s, f x y ∂μ := by
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hm : 0 ≤ (μ s).toReal := ENNReal.toReal_nonneg
  have hδ : 0 < ε / ((μ s).toReal + 1) := div_pos hε (by linarith)
  have hc : Continuous fun z : X × Y => f z.1 z.2 - f x₀ z.2 :=
    hf.sub (hf.comp (Continuous.prodMk continuous_const continuous_snd))
  have htube : ∀ᶠ x in nhds x₀, ∀ y ∈ C, ‖f x y - f x₀ y‖ < ε / ((μ s).toReal + 1) := by
    apply hC.eventually_forall_of_forall_eventually
    intro y _
    exact (hc.norm.tendsto (x₀, y)).eventually (gt_mem_nhds (by simpa using hδ))
  filter_upwards [htube] with x hx
  rw [dist_eq_norm, ← integral_sub (hi x) (hi x₀)]
  calc ‖∫ y in s, (f x y - f x₀ y) ∂μ‖ ≤ ε / ((μ s).toReal + 1) * (μ s).toReal :=
        norm_setIntegral_le_of_norm_le_const hμ (fun y hy => (hx y (hsC hy)).le)
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

theorem UpperTheory.continuous_constantTerm :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ),
      Continuous φ → Continuous (constantTerm (r := r) φ) := by
  intro K _ _ n r φ hφ
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  exact cont_setIntegral (unipMeasure K n r) (fun g X => φ (unipGL X * g))
    (hφ.comp ((continuous_unipGL.comp continuous_snd).mul continuous_fst))
    measurableSet_unipFundamentalDomain hC hDC ((measure_mono hDC).trans_lt hC.measure_lt_top)
    (fun g => integrableOn_constantTerm hφ g)
end

