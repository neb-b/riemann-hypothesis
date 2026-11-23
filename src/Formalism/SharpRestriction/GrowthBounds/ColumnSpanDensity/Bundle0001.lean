module

public import Mathlib

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.BlockSplit
section
namespace Formalism.MainNotions.flipOneThree.Pf.KP

open Module

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private noncomputable def bspZ (n : ℕ) (z : O) : Submodule O (Fin n → O) :=
  LinearMap.range (z • (LinearMap.id : (Fin n → O) →ₗ[O] (Fin n → O)))

private theorem bsp_one (n : ℕ) (z : O) (A : Matrix (Fin n) (Fin n) O) :
    ∃ (ν : ℕ) (v : Fin ν → (Fin n → O)),
      LinearMap.range (Matrix.mulVecLin A) ≤
        Submodule.span O (Set.range v) ⊔ IsLocalRing.maximalIdeal O • bspZ n z ∧
      ∃ (P : Matrix (Fin ν) (Fin n) O) (Q : Matrix (Fin n) (Fin ν) O),
        P * A * Q = z • (1 : Matrix (Fin ν) (Fin ν) O) := by
  classical
  haveI : ValuationRing O :=
    ((IsDiscreteValuationRing.TFAE O (IsDiscreteValuationRing.not_isField O)).out 1 2).mp
      (inferInstance : IsDiscreteValuationRing O)
  obtain ⟨m, S⟩ := Submodule.smithNormalForm (Pi.basisFun O (Fin n))
    (LinearMap.range (Matrix.mulVecLin A))
  let T : Finset (Fin m) := Finset.univ.filter (fun k => S.a k ∣ z)
  let e : Fin T.card ≃ T := T.equivFin.symm
  choose x hx using fun k : Fin m => (S.bN k).2
  have hc : ∀ t : T, ∃ c, z = S.a t.1 * c := fun t => (Finset.mem_filter.mp t.2).2
  choose c hc' using hc
  let w : Fin T.card → (Fin n → O) := fun i => c (e i) • x (e i).1
  have hAw : ∀ i, Matrix.mulVec A (w i) = z • S.bM (S.f (e i).1) := by
    intro i
    have h1 := hx (e i).1
    rw [Matrix.mulVecLin_apply] at h1
    show Matrix.mulVec A (c (e i) • x (e i).1) = _
    rw [Matrix.mulVec_smul, h1, S.snf, smul_smul, hc' (e i), mul_comm]
  refine ⟨T.card, fun i => S.bM (S.f (e i).1), ?_, ?_⟩
  · intro y hy
    have e2 := congrArg Subtype.val (S.bN.sum_repr ⟨y, hy⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e2
    rw [← e2]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    rw [S.snf]
    by_cases hk : S.a k ∣ z
    · apply Submodule.mem_sup_left
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨e.symm ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩, by simp⟩
    · apply Submodule.mem_sup_right
      obtain ⟨d, hd⟩ := (ValuationRing.dvd_total (S.a k) z).resolve_left hk
      have hdm : d ∈ IsLocalRing.maximalIdeal O := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact hk ⟨↑hu.unit⁻¹, by rw [hd, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
      rw [hd, mul_comm, ← smul_smul]
      exact Submodule.smul_mem_smul hdm ⟨S.bM (S.f k), rfl⟩
  · refine ⟨Matrix.of fun i r => S.bM.coord (S.f (e i).1) (fun j => if r = j then 1 else 0),
      Matrix.of fun r i => w i r, ?_⟩
    ext i i'
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    have hcol : ∀ r, (A * Matrix.of fun r i => w i r) r i' = (z • S.bM (S.f (e i').1)) r := by
      intro r
      rw [← hAw i']
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    simp only [hcol, Matrix.of_apply]
    have hφ : ∑ r, S.bM.coord (S.f (e i).1) (fun j => if r = j then 1 else 0) *
        (z • S.bM (S.f (e i').1)) r = S.bM.coord (S.f (e i).1) (z • S.bM (S.f (e i').1)) := by
      rw [LinearMap.pi_apply_eq_sum_univ (S.bM.coord (S.f (e i).1)) (z • S.bM (S.f (e i').1))]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [smul_eq_mul, mul_comm]
    rw [hφ, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, smul_eq_mul]
    by_cases hii : i = i'
    · subst hii
      simp
    · have hne : S.f (e i).1 ≠ S.f (e i').1 := fun h =>
        hii (e.injective (Subtype.ext (S.f.injective h)))
      simp [Finsupp.single_apply, hne, hii]

theorem blockSplit {J : Type} [Fintype J] (n : ℕ) (z : O) (hz : z ≠ 0)
    (A : J → Matrix (Fin n) (Fin n) O) (h : ∑ j, A j = z • (1 : Matrix (Fin n) (Fin n) O)) :
    ∃ ν : J → ℕ, n ≤ ∑ j, ν j ∧ ∀ j, ∃ (P : Matrix (Fin (ν j)) (Fin n) O)
      (Q : Matrix (Fin n) (Fin (ν j)) O), P * A j * Q = z • (1 : Matrix _ _ O) := by
  classical
  choose ν v hv P Q hPQ using fun j => bsp_one n z (A j)
  refine ⟨ν, ?_, fun j => ⟨P j, Q j, hPQ j⟩⟩
  let V : (Σ j, Fin (ν j)) → (Fin n → O) := fun jk => v jk.1 jk.2
  let W : Submodule O (Fin n → O) := Submodule.span O (Set.range V)
  have hvW : ∀ j, Submodule.span O (Set.range (v j)) ≤ W := by
    intro j
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨j, k⟩, rfl⟩
  have hsum : ∀ (s : Finset J) (x : Fin n → O), Matrix.mulVec (∑ j ∈ s, A j) x = ∑ j ∈ s, Matrix.mulVec (A j) x := by
    intro s x
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Matrix.add_mulVec, ih]
  have hZ : bspZ n z ≤ W ⊔ IsLocalRing.maximalIdeal O • bspZ n z := by
    rintro _ ⟨x, rfl⟩
    have hx : (z • (LinearMap.id : (Fin n → O) →ₗ[O] (Fin n → O))) x = ∑ j, Matrix.mulVec (A j) x := by
      rw [LinearMap.smul_apply, LinearMap.id_apply, ← hsum, h, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    rw [hx]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact sup_le_sup_right (hvW j) _ (hv j ⟨x, rfl⟩)
  have hfg : (bspZ n z).FG := by
    unfold bspZ
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  have hjac : IsLocalRing.maximalIdeal O ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hZW : bspZ n z ≤ W := Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac hZ
  let f := z • (LinearMap.id : (Fin n → O) →ₗ[O] (Fin n → O))
  have hinj : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    exact smul_right_injective _ hz hxy
  have hli : LinearIndependent O (fun i : Fin n => f (Pi.basisFun O (Fin n) i)) :=
    (Pi.basisFun O (Fin n)).linearIndependent.map' f hinj
  have hle := linearIndependent_le_span' _ hli (Set.range V) (by
    rintro _ ⟨i, rfl⟩
    exact hZW ⟨_, rfl⟩)
  calc n = Fintype.card (Fin n) := (Fintype.card_fin n).symm
    _ ≤ Fintype.card (Set.range V) := by
        rw [Cardinal.mk_fintype] at hle
        exact_mod_cast hle
    _ ≤ Fintype.card (Σ j, Fin (ν j)) := Fintype.card_range_le V
    _ = ∑ j, ν j := by simp [Fintype.card_sigma]

end Formalism.MainNotions.flipOneThree.Pf.KP
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatRetract
section
namespace Formalism.MainNotions.flipOneThree.Pf.KP

open Submodule

section LatRetract

variable {O K V V' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V] [AddCommGroup V'] [Module K V'] [Module O V'] [IsScalarTower O K V']
  {ι ι' : Type} [Fintype ι] [Fintype ι']

omit [IsDiscreteValuationRing O] in
private theorem lrt_am_ne {a : O} (ha : a ≠ 0) : algebraMap O K a ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 ha

private theorem lrt_tf (O K V : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] :
    Module.IsTorsionFree O V :=
  ⟨fun r hr x y hxy => by
    have hr0 : r ≠ 0 := hr.ne_zero
    have h1 : algebraMap O K r • x = algebraMap O K r • y := by
      rw [algebraMap_smul, algebraMap_smul]; exact hxy
    exact smul_right_injective V (lrt_am_ne (K := K) hr0) h1⟩


omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [Fintype ι] in
private theorem lrt_coord (b : Module.Basis ι K V) {y : V}
    (hy : y ∈ span O (Set.range b)) (i : ι) : b.repr y i ∈ Set.range (algebraMap O K) := by
  classical
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases hji : j = i
    · subst hji; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [hji]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by simp [hu, hv]⟩
  | smul a x _ hx =>
    obtain ⟨u, hu⟩ := hx
    exact ⟨a * u, by
      rw [← algebraMap_smul K a x, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hu]⟩


omit [IsDiscreteValuationRing O] in
private theorem lrt_den (b : Module.Basis ι K V) (F : V) :
    ∃ a : O, a ≠ 0 ∧ a • F ∈ span O (Set.range b) := by
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun i => b.repr F i)
  refine ⟨a, nonZeroDivisors.ne_zero a.2, ?_⟩
  have hF : (a : O) • F = ∑ i, (a : O) • (b.repr F i • b i) := by
    rw [← Finset.smul_sum, b.sum_repr F]
  rw [hF]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨z, hz⟩ := ha i
  rw [← smul_assoc, ← hz, algebraMap_smul]
  exact Submodule.smul_mem _ _ (subset_span ⟨i, rfl⟩)

private theorem lrt_inj (b : Module.Basis ι K V) (b' : Module.Basis ι' K V') (io : V →ₗ[K] V')
    (h : ∀ F, io F ∈ Submodule.span O (Set.range b') ↔ F ∈ Submodule.span O (Set.range b)) :
    Function.Injective io := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro F hF
  by_contra hne
  have h0 : b.repr F ≠ 0 := by simpa using hne
  obtain ⟨i, hi⟩ := DFunLike.ne_iff.1 h0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmem : ((b.repr F i * algebraMap O K ϖ)⁻¹) • F ∈ span O (Set.range b) := by
    rw [← h, map_smul, hF, smul_zero]; exact zero_mem _
  obtain ⟨z, hz⟩ := lrt_coord b hmem i
  have hϖ0 : algebraMap O K ϖ ≠ 0 := lrt_am_ne hϖ.ne_zero
  have hi' : b.repr F i ≠ 0 := by simpa using hi
  have h1 : algebraMap O K (ϖ * z) = algebraMap O K 1 := by
    rw [map_mul, hz, map_one, map_smul, Finsupp.smul_apply, smul_eq_mul]
    field_simp
  have h2 := IsFractionRing.injective O K h1
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one _ h2)

theorem latRetract {O K V V' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [AddCommGroup V'] [Module K V'] [Module O V'] [IsScalarTower O K V'] {ι ι' : Type} [Fintype ι] [Fintype ι'] (b : Module.Basis ι K V) (b' : Module.Basis ι' K V') (io : V →ₗ[K] V') (h : ∀ F, io F ∈ Submodule.span O (Set.range b') ↔ F ∈ Submodule.span O (Set.range b)) : ∃ ret : V' →ₗ[K] V, (∀ F, ret (io F) = F) ∧ ∀ G ∈ Submodule.span O (Set.range b'), ret G ∈ Submodule.span O (Set.range b) := by
  classical
  have : Module.IsTorsionFree O V := lrt_tf O K V
  have : Module.IsTorsionFree O V' := lrt_tf O K V'
  let R : Submodule O V := span O (Set.range b)
  let R' : Submodule O V' := span O (Set.range b')
  have : Module.Finite O R := Module.Finite.span_of_finite O (Set.finite_range b)
  have : Module.Finite O R' := Module.Finite.span_of_finite O (Set.finite_range b')
  let ioR : R →ₗ[O] R' := (io.restrictScalars O).restrict (fun F hF => (h F).2 hF)
  have hinj : Function.Injective ioR := fun x y hxy =>
    Subtype.ext (lrt_inj b b' io h (congrArg Subtype.val hxy))
  let N : Submodule O R' := LinearMap.range ioR
  have : Module.IsTorsionFree O (R' ⧸ N) := by
    refine ⟨fun r hr x y hxy => ?_⟩
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    have h1 : N.mkQ (r • (x - y)) = 0 := by
      rw [smul_sub, map_sub, map_smul, map_smul, sub_eq_zero]; exact hxy
    rw [mkQ_apply, Quotient.mk_eq_zero] at h1
    obtain ⟨F, hF⟩ := h1
    have hr0 : r ≠ 0 := hr.ne_zero
    rw [← sub_eq_zero, ← map_sub, mkQ_apply, Quotient.mk_eq_zero]
    have hFv : io (F : V) = r • ((x - y : R') : V') := congrArg Subtype.val hF
    have hcalc : io ((algebraMap O K r)⁻¹ • (F : V)) = ((x - y : R') : V') := by
      rw [map_smul, hFv, ← algebraMap_smul K r, smul_smul, inv_mul_cancel₀ (lrt_am_ne hr0),
        one_smul]
    have hmem : (algebraMap O K r)⁻¹ • (F : V) ∈ R := by
      rw [← h, hcalc]
      exact (x - y).2
    exact ⟨⟨_, hmem⟩, Subtype.ext hcalc⟩
  obtain ⟨s, hs⟩ := N.mkQ.exists_rightInverse_of_surjective N.range_mkQ
  let e := LinearEquiv.ofInjective ioR hinj
  let p : R' →ₗ[O] N := (LinearMap.id - s ∘ₗ N.mkQ).codRestrict N (fun y => by
    rw [← Quotient.mk_eq_zero, ← mkQ_apply, LinearMap.sub_apply, map_sub, sub_eq_zero]
    exact (LinearMap.congr_fun hs (N.mkQ y)).symm)
  let retO : R' →ₗ[O] R := e.symm.toLinearMap ∘ₗ p
  have hretO : ∀ x : R, retO (ioR x) = x := by
    intro x
    show e.symm (p (ioR x)) = x
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    have h0 : N.mkQ (ioR x) = 0 := by
      rw [mkQ_apply, Quotient.mk_eq_zero]; exact ⟨x, rfl⟩
    show (LinearMap.id - s ∘ₗ N.mkQ : R' →ₗ[O] R') (ioR x) = ioR x
    simp [h0]
  let ret : V' →ₗ[K] V :=
    b'.constr K (fun j => ((retO ⟨b' j, subset_span ⟨j, rfl⟩⟩ : R) : V))
  have hret : ∀ G (hG : G ∈ R'), ret G = retO ⟨G, hG⟩ := by
    intro G hG
    induction hG using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact b'.constr_basis K _ j
    | zero =>
      rw [map_zero]
      exact (congrArg Subtype.val (map_zero retO)).symm
    | add x y hx hy ihx ihy =>
      rw [map_add (f := _), ihx, ihy]
      exact (congrArg Subtype.val (map_add retO ⟨x, hx⟩ ⟨y, hy⟩)).symm
    | smul a x hx ih =>
      have h1 : ret (a • x) = a • ret x := by
        rw [← algebraMap_smul K a x, map_smul, algebraMap_smul]
      rw [h1, ih]
      exact (congrArg Subtype.val (map_smul retO a ⟨x, hx⟩)).symm
  refine ⟨ret, fun F => ?_, fun G hG => by rw [hret G hG]; exact (retO _).2⟩
  obtain ⟨a, ha, haF⟩ := lrt_den (O := O) b F
  have h1 : ret (io (a • F)) = a • F := by
    rw [hret _ ((h _).2 haF)]
    exact congrArg Subtype.val (hretO ⟨a • F, haF⟩)
  have h2 : a • ret (io F) = a • F := by
    rw [← h1, ← algebraMap_smul K a F, map_smul, map_smul, algebraMap_smul]
  exact smul_right_injective V ha h2

end LatRetract

end Formalism.MainNotions.flipOneThree.Pf.KP
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LemmaSMat
section
namespace Formalism.MainNotions.flipOneThree.Pf.KP

open Module

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem smt_unit {s ρ : ℕ} (E : Matrix (Fin s) (Fin ρ) O) (C : Matrix (Fin ρ) (Fin s) O)
    (hE : ∀ i j, E i j ∈ IsLocalRing.maximalIdeal O) : IsUnit (1 - E * C).det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hE0 : E.map (IsLocalRing.residue O) = 0 := by
    ext i j
    simpa [Matrix.map_apply, IsLocalRing.residue_eq_zero_iff] using hE i j
  have h : (RingHom.mapMatrix (IsLocalRing.residue O)) (1 - E * C) = 1 := by
    rw [map_sub, map_one, RingHom.mapMatrix_apply, Matrix.map_mul, hE0, Matrix.zero_mul, sub_zero]
  rw [h, Matrix.det_one]
  exact one_ne_zero

private theorem smt_block {s ρ : ℕ} (z1 z2 : O) (E : Matrix (Fin s) (Fin ρ) O)
    (C : Matrix (Fin ρ) (Fin s) O) (hE : ∀ i j, E i j ∈ IsLocalRing.maximalIdeal O) :
    ∃ M : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O,
      Matrix.fromBlocks (z1 • (1 : Matrix (Fin s) (Fin s) O)) ((z1 * z2) • E) C
        (z2 • (1 : Matrix (Fin ρ) (Fin ρ) O)) * M =
      (z1 * z2) • (1 : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O) := by
  have hU := smt_unit E C hE
  have hV : IsUnit (1 - C * E).det := by rw [Matrix.det_one_sub_mul_comm]; exact hU
  have hUi : (1 - E * C) * (1 - E * C)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have hVi : (1 - C * E) * (1 - C * E)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hV
  refine ⟨Matrix.fromBlocks (z2 • (1 - E * C)⁻¹) (-(z1 * z2) • (E * (1 - C * E)⁻¹))
    (-(C * (1 - E * C)⁻¹)) (z1 • (1 - C * E)⁻¹), ?_⟩
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero,
    Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : (z1 * z2) • (1 : Matrix (Fin s) (Fin s) O) = (z1 * z2) • ((1 - E * C) * (1 - E * C)⁻¹) := by
      rw [hUi]
    rw [e]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg,
      Matrix.mul_assoc, smul_smul]
    module
  · simp only [Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc, smul_smul, neg_smul]
    module
  · simp only [Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc, smul_smul]
    module
  · have e : (z1 * z2) • (1 : Matrix (Fin ρ) (Fin ρ) O) = (z1 * z2) • ((1 - C * E) * (1 - C * E)⁻¹) := by
      rw [hVi]
    rw [e]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_assoc, smul_smul, neg_smul]
    module

theorem lemmaSMat {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (σ ρ : ℕ) (z1 z2 : O) (h1 : z1 ≠ 0) (h2 : z2 ≠ 0) (N : Matrix (Fin σ) (Fin ρ) O) (B : Matrix (Fin ρ) (Fin σ) O) :
  ∃ (r s : ℕ), r + s = σ ∧
    (∃ (P : Matrix (Fin r) (Fin σ) O) (Q : Matrix (Fin ρ) (Fin r) O), P * N * Q = (z1 * z2) • (1 : Matrix (Fin r) (Fin r) O)) ∧
    (∃ (P' : Matrix (Fin s) (Fin σ) O) (P'' : Matrix (Fin σ) (Fin s) O) (M : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O), P' * P'' = 1 ∧
      Matrix.fromBlocks (z1 • (1 : Matrix (Fin s) (Fin s) O)) (P' * N) (B * P'') (z2 • (1 : Matrix (Fin ρ) (Fin ρ) O)) * M = (z1 * z2) • (1 : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O)) := by
  classical
  have hz0 : z1 * z2 ≠ 0 := mul_ne_zero h1 h2
  have key : ∀ (n : ℕ) (N : Matrix (Fin n) (Fin ρ) O), ∃ (r s : ℕ), r + s = n ∧
      (∃ (P : Matrix (Fin r) (Fin n) O) (Q : Matrix (Fin ρ) (Fin r) O),
        P * N * Q = (z1 * z2) • (1 : Matrix (Fin r) (Fin r) O)) ∧
      (∃ (P' : Matrix (Fin s) (Fin n) O) (P'' : Matrix (Fin n) (Fin s) O), P' * P'' = 1 ∧
        ∀ i j, ∃ e ∈ IsLocalRing.maximalIdeal O, (P' * N) i j = z1 * z2 * e) := by
    intro n
    induction n with
    | zero =>
      intro N
      refine ⟨0, 0, rfl, ⟨0, 0, ?_⟩, ⟨0, 0, ?_, fun i => i.elim0⟩⟩
      · ext i; exact i.elim0
      · ext i; exact i.elim0
    | succ n ih =>
      intro N
      by_cases hall : ∀ i j, ∃ e ∈ IsLocalRing.maximalIdeal O, N i j = z1 * z2 * e
      · refine ⟨0, n + 1, by omega, ⟨0, 0, ?_⟩, ⟨1, 1, Matrix.one_mul 1, ?_⟩⟩
        · ext i; exact i.elim0
        · intro i j; rw [Matrix.one_mul]; exact hall i j
      obtain ⟨ia, hia⟩ := not_forall.mp hall
      obtain ⟨ja, hna⟩ := not_forall.mp hia
      obtain ⟨⟨i0, j0⟩, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin (n + 1) × Fin ρ))
        (fun p => IsDiscreteValuationRing.addVal O (N p.1 p.2)) ⟨(ia, ja), Finset.mem_univ _⟩
      have hdiv : ∀ p : Fin (n + 1) × Fin ρ, N i0 j0 ∣ N p.1 p.2 := fun p =>
        (IsDiscreteValuationRing.addVal_le_iff_dvd).mp (hmin p (Finset.mem_univ _))
      have haz : N i0 j0 ∣ z1 * z2 := by
        by_contra hnd
        rcases le_total (IsDiscreteValuationRing.addVal O (N i0 j0))
            (IsDiscreteValuationRing.addVal O (z1 * z2)) with h | h
        · exact hnd ((IsDiscreteValuationRing.addVal_le_iff_dvd).mp h)
        · obtain ⟨e, he⟩ := (IsDiscreteValuationRing.addVal_le_iff_dvd).mp h
          have hem : e ∈ IsLocalRing.maximalIdeal O := by
            rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
            rintro ⟨u, rfl⟩
            exact hnd ⟨↑u⁻¹, by rw [he, mul_assoc, Units.mul_inv, mul_one]⟩
          apply hna
          obtain ⟨b, hb⟩ : N i0 j0 ∣ N ia ja := hdiv (ia, ja)
          exact ⟨e * b, Ideal.mul_mem_right _ _ hem, by rw [hb, he, mul_assoc]⟩
      obtain ⟨t, ht⟩ := haz
      choose f hf using hdiv
      have hf' : ∀ i l, N i l = N i0 j0 * f (i, l) := fun i l => hf (i, l)
      have ha0 : N i0 j0 ≠ 0 := by
        intro h0; apply hz0; rw [ht, h0, zero_mul]
      have hf00 : f (i0, j0) = 1 := by
        apply mul_left_cancel₀ ha0
        rw [mul_one]; exact (hf' i0 j0).symm
      let N1 : Matrix (Fin n) (Fin ρ) O :=
        Matrix.of fun k l => N (i0.succAbove k) l - f (i0.succAbove k, j0) * N i0 l
      obtain ⟨r1, s1, hrs, ⟨P1, Q1, hPQ⟩, ⟨P1', P1'', hP1, hgood⟩⟩ := ih N1
      let S : Matrix (Fin n) (Fin (n + 1)) O := Matrix.of fun k i =>
        (if i = i0.succAbove k then 1 else 0) - (if i = i0 then f (i0.succAbove k, j0) else 0)
      let Em : Matrix (Fin (n + 1)) (Fin n) O := Matrix.of fun i k => if i = i0.succAbove k then 1 else 0
      let Ei : Matrix (Fin 1) (Fin (n + 1)) O := Matrix.of fun _ i => if i = i0 then t else 0
      let ej : Matrix (Fin ρ) (Fin 1) O := Matrix.of fun l _ => if l = j0 then 1 else 0
      let dd : Matrix (Fin 1) (Fin ρ) O := Matrix.of fun _ l => f (i0, l)
      let Q1' : Matrix (Fin ρ) (Fin r1) O := Q1 - ej * (dd * Q1)
      have hSN : S * N = N1 := by
        ext k l
        simp [S, N1, Matrix.mul_apply, sub_mul, Finset.sum_sub_distrib, ite_mul]
      have hSE : S * Em = 1 := by
        ext k k'
        have hne : i0 ≠ i0.succAbove k' := Fin.ne_succAbove i0 k'
        have hne' : i0.succAbove k' ≠ i0 := Fin.succAbove_ne i0 k'
        simp only [S, Em, Matrix.mul_apply, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul,
          one_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.one_apply]
        simp [hne, hne', Fin.succAbove_right_inj]
      have hrow : Ei * N = (z1 * z2) • dd := by
        ext i l
        simp [Ei, dd, Matrix.mul_apply, ite_mul]
        rw [hf' i0 l, ht]; ring
      have hdd : dd * ej = 1 := by
        ext i j
        fin_cases i; fin_cases j
        simp [dd, ej, Matrix.mul_apply, hf00]
      have hN1e : N1 * ej = 0 := by
        ext k j
        simp [N1, ej, Matrix.mul_apply]
        rw [hf' (i0.succAbove k) j0]; ring
      have hblocks : Matrix.fromRows Ei (P1 * S) * N * Matrix.fromCols ej Q1' =
          (z1 * z2) • (1 : Matrix (Fin 1 ⊕ Fin r1) (Fin 1 ⊕ Fin r1) O) := by
        rw [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one,
          Matrix.fromBlocks_smul, smul_zero, smul_zero, Matrix.fromBlocks_inj]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hrow, Matrix.smul_mul, hdd]
        · rw [hrow, Matrix.mul_sub, Matrix.smul_mul, Matrix.smul_mul, ← Matrix.mul_assoc dd ej, hdd,
            Matrix.one_mul, sub_self]
        · rw [Matrix.mul_assoc P1 S N, hSN, Matrix.mul_assoc, hN1e, Matrix.mul_zero]
        · rw [Matrix.mul_assoc P1 S N, hSN, Matrix.mul_sub, ← Matrix.mul_assoc (P1 * N1) ej,
            Matrix.mul_assoc P1 N1 ej, hN1e, Matrix.mul_zero, Matrix.zero_mul, sub_zero, hPQ]
      refine ⟨1 + r1, s1, by omega, ⟨(Matrix.fromRows Ei (P1 * S)).submatrix finSumFinEquiv.symm id,
        (Matrix.fromCols ej Q1').submatrix id finSumFinEquiv.symm, ?_⟩, ⟨P1' * S, Em * P1'', ?_, ?_⟩⟩
      · rw [← Matrix.submatrix_id_id N, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
          ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hblocks]
        ext i j
        simp [Matrix.one_apply]
      · rw [Matrix.mul_assoc, ← Matrix.mul_assoc S Em, hSE, Matrix.one_mul, hP1]
      · intro i j
        rw [Matrix.mul_assoc, hSN]
        exact hgood i j
  obtain ⟨r, s, hrs, hP, P', P'', hP', hg⟩ := key σ N
  refine ⟨r, s, hrs, hP, P', P'', ?_⟩
  choose E hEm hE using hg
  obtain ⟨M, hM⟩ := smt_block z1 z2 (Matrix.of E) (B * P'') (fun i j => hEm i j)
  refine ⟨M, hP', ?_⟩
  have hPN : P' * N = (z1 * z2) • Matrix.of E := by
    ext i j
    simp [hE i j]
  rw [hPN]
  exact hM

end Formalism.MainNotions.flipOneThree.Pf.KP
end

