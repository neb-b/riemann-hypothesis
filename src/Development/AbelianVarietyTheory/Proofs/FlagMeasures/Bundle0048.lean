module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexMulMeasure
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical NNReal

namespace GlobalTheory.BaseModule

@[to_additive addRelIndex_mul_measure
]
theorem relIndex_mul_measure' {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H L : Subgroup G) (hHL : H ≤ L) [(H.subgroupOf L).FiniteIndex]
    (hH : MeasurableSet (H : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] :
    (H.relIndex L : ENNReal) * μ H = μ L := by
  classical
  obtain ⟨s, hs, -⟩ := (H.subgroupOf L).exists_isComplement_left 1
  have hfin : Finite s := hs.finite_left_iff.mpr inferInstance
  have hU : (L : Set G) = ⋃ a : s, ((a : L) : G) • (H : Set G) := by
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hx
      have hy : (⟨x, hx⟩ : L) ∈ s * ((H.subgroupOf L : Subgroup L) : Set L) := by
        rw [hs.mul_eq]; exact Set.mem_univ _
      obtain ⟨a, ha, h, hh, hah⟩ := hy
      refine ⟨⟨a, ha⟩, (h : G), Subgroup.mem_subgroupOf.mp hh, ?_⟩
      have := congrArg Subtype.val hah
      simpa using this
    · rintro ⟨a, z, hz, rfl⟩
      exact L.mul_mem (a : L).2 (hHL hz)
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => ((a : L) : G) • (H : Set G)) := by
    intro a b hab
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, he⟩
    apply hab
    have key := hs.1 (a₁ := (a, ⟨⟨z₁, hHL hz₁⟩, Subgroup.mem_subgroupOf.mpr hz₁⟩))
      (a₂ := (b, ⟨⟨z₂, hHL hz₂⟩, Subgroup.mem_subgroupOf.mpr hz₂⟩)) (Subtype.ext (by simpa using he.symm))
    exact congrArg Prod.fst key
  calc (H.relIndex L : ENNReal) * μ H = ∑' a : s, μ (((a : L) : G) • (H : Set G)) := by
        simp [measure_smul, hs.encard_left, Subgroup.relIndex]
    _ = μ L := by
        rw [hU, measure_iUnion hdisj (fun _ => hH.const_smul _)]

theorem modK_algebraMap : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ ϖ : 𝒪[F], Irreducible ϖ → Nat.card 𝓀[F] = resQ ϖ ∧ ∀ x : F, x ≠ 0 → M.modK (algebraMap F E x) = (resQ ϖ : ℝ) ^ (-(2 * vE M.L ϖ (algebraMap F E x))) := by
  intro F _ _ _ E _ _ _ _ M hM ϖ hϖ
  have := hM.loc
  have := hM.char0
  have := hM.borel
  have := hM.haar.haar
  obtain ⟨hTR, hT2, hLC, hSC, hCS, -, -, hOc, hOo, -⟩ := GlobalTheory.SgLoc.Top.model_topology M hM
  have hq2 : 2 ≤ resQ ϖ := (GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.2.2.2.1
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.HL.resQ
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    rfl
  intro x hx
  have : IsTopologicalAddGroup E := inferInstance
  have : M.mu.Regular := inferInstance
  have hsmul : ∀ (a : F) (y : E), a ∈ 𝒪[F] → y ∈ M.L.O → a • y ∈ M.L.O := fun a y ha hy => by
    rw [Algebra.smul_def]
    exact M.L.O.mul_mem ((GlobalTheory.UnramOrder.algebraMap_mem_iff M.L a).mpr ha) hy
  have hO0 : M.mu (M.L.O : Set E) ≠ 0 := hOo.measure_ne_zero M.mu ⟨0, M.L.O.zero_mem⟩
  have hOT : M.mu (M.L.O : Set E) ≠ ⊤ := hOc.measure_lt_top.ne

  have hunit : ∀ u : (𝒪[F])ˣ, distribHaarChar E (Units.mk0 ((u : 𝒪[F]) : F) (by simp)) = 1 := by
    intro u
    apply distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOT
    have hinv : (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) = ((u : 𝒪[F]) : F)⁻¹ := by
      have h1 : ((((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (u : 𝒪[F]) : 𝒪[F]) : F) = ((1 : 𝒪[F]) : F) := by
        rw [u.inv_mul]
      rw [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
      exact eq_inv_of_mul_eq_one_left h1
    have hset : Units.mk0 ((u : 𝒪[F]) : F) (by simp) • (M.L.O : Set E) = M.L.O := by
      ext y
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      constructor
      · intro hy
        have h2 := hsmul ((u : 𝒪[F]) : F) _ (u : 𝒪[F]).2 hy
        rw [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, smul_inv_smul₀ (by simp)] at h2
        exact h2
      · intro hy
        have h2 := hsmul (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) y (u⁻¹ : (𝒪[F])ˣ).1.2 hy
        rw [Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, ← hinv]
        exact h2
    rw [hset]
    simp

  have hϖ0 : (ϖ : F) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hwO : algebraMap F E (ϖ : F) ∈ M.L.O := (GlobalTheory.UnramOrder.algebraMap_mem_iff M.L _).mpr ϖ.2
  have hI : Ideal.span {y : M.L.O | (y : E) = algebraMap F E ((ϖ : F) ^ 1)} =
      Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)} := by
    congr 1
    ext y
    simp [Subtype.ext_iff]
  have hcard : Nat.card (M.L.O ⧸ Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}) = resQ ϖ ^ 2 := by
    have h := (GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.2.2.1 1
    rw [hI, mul_one] at h
    exact h
  have hfinj : Function.Injective (M.L.O.subtype.toAddMonoidHom) := Subtype.val_injective
  have hrange : (⊤ : AddSubgroup M.L.O).map M.L.O.subtype.toAddMonoidHom = M.L.O.toAddSubgroup := by
    ext z
    simp
  have hrel : ((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom).relIndex M.L.O.toAddSubgroup = resQ ϖ ^ 2 := by
    rw [← hrange, AddSubgroup.relIndex_map_map_of_injective _ _ hfinj, AddSubgroup.relIndex_top_right]
    exact hcard
  have hHK : (Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom ≤ M.L.O.toAddSubgroup := by
    rintro z ⟨y, -, rfl⟩
    exact y.2
  have hHset : (((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom : AddSubgroup E) : Set E) = Units.mk0 (ϖ : F) hϖ0 • (M.L.O : Set E) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      refine ⟨(a : E), a.2, ?_⟩
      simp [Algebra.smul_def, mul_comm]
    · rintro ⟨b, hb, rfl⟩
      refine ⟨⟨b, hb⟩ * ⟨algebraMap F E (ϖ : F), hwO⟩,
        Ideal.mul_mem_left _ _ (Ideal.subset_span rfl), ?_⟩
      simp [Algebra.smul_def, mul_comm]
  have hHm : MeasurableSet (((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom : AddSubgroup E) : Set E) := by
    rw [hHset]
    exact (hOo.smul _).measurableSet
  have : (((Ideal.span {(⟨algebraMap F E (ϖ : F), hwO⟩ : M.L.O)}).toAddSubgroup.map
      M.L.O.subtype.toAddMonoidHom).addSubgroupOf M.L.O.toAddSubgroup).FiniteIndex := by
    refine ⟨?_⟩
    change AddSubgroup.relIndex _ _ ≠ 0
    rw [hrel]
    exact pow_ne_zero _ (by omega)
  have key := addRelIndex_mul_measure _ _ hHK hHm M.mu
  rw [hrel, hHset] at key
  have key2 : ((resQ ϖ ^ 2 : ℕ) : ENNReal) * M.mu (Units.mk0 (ϖ : F) hϖ0 • (M.L.O : Set E)) =
      M.mu (M.L.O : Set E) := key
  have hΔp : distribHaarChar E (Units.mk0 (ϖ : F) hϖ0) = ((resQ ϖ : NNReal) ^ 2)⁻¹ := by
    apply distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOT
    have h0 : ((resQ ϖ ^ 2 : ℕ) : ENNReal) ≠ 0 := by
      exact_mod_cast pow_ne_zero _ (by omega)
    have hT : ((resQ ϖ ^ 2 : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hc : (((((resQ ϖ : NNReal) ^ 2)⁻¹ : NNReal)) : ENNReal) = ((resQ ϖ ^ 2 : ℕ) : ENNReal)⁻¹ := by
      rw [ENNReal.coe_inv (by exact_mod_cast pow_ne_zero _ (by omega))]
      push_cast
      rfl
    rw [hc]
    rw [← key2, ← mul_assoc, ENNReal.inv_mul_cancel h0 hT, one_mul]

  obtain ⟨u, hu⟩ := (GlobalTheory.UnramVal.vE_valuation M.L ϖ hϖ).2.2.2 x hx
  have hgx : Units.mk0 x hx = Units.mk0 (ϖ : F) hϖ0 ^ (vE M.L ϖ (algebraMap F E x)) *
      Units.mk0 ((u : 𝒪[F]) : F) (by simp) := by
    ext
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_mk0, Units.val_mk0]
    exact hu
  have himg : (fun y => algebraMap F E x * y) '' (M.R : Set E) = Units.mk0 x hx • (M.R : Set E) := by
    rw [← Set.image_smul]
    congr 1
    funext y
    rw [Units.smul_def, Units.val_mk0, Algebra.smul_def]
  unfold Formalism.MainNotions.S.Loc.Model.modK
  rw [himg, ← distribHaarChar_mul M.mu, hM.haar.volR, mul_one, hgx, map_mul, map_zpow, hunit u, mul_one,
    hΔp, ENNReal.coe_toReal]
  push_cast
  rw [← zpow_natCast, ← zpow_neg, ← zpow_mul]
  congr 1
  push_cast
  ring

end GlobalTheory.BaseModule
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanEqMap
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.MatrixIndex

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_basis [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) :
    ∃ b : Module.Basis (Fin 2) F E, (∀ x, x ∈ L.O ↔ ∀ i, b.repr x i ∈ 𝒪[F]) ∧
      ∀ x, algebraMap F E (Algebra.norm F x) = x * L.cj x := by
  obtain ⟨ω, hω, e, he, hωe⟩ := GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  have hint : ∀ a : F, a ∈ 𝒪[F] → algebraMap F E a ∈ L.O := fun a h =>
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L a).2 h
  have he' : (L.cj ω - ω) * L.cj e = 1 := by simpa [L.cj_cj] using congrArg L.cj hωe
  have hce : L.cj e = -e := by linear_combination (-e) * he' - (L.cj e) * hωe
  have hli : LinearIndependent F ![(1 : E), ω] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    simp only [Algebra.smul_def, mul_one] at h
    have h' := congrArg L.cj h
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes, map_zero] at h'
    have ht : algebraMap F E t = 0 := by
      linear_combination e * h - e * h' - algebraMap F E t * hωe
    have hs : algebraMap F E s = 0 := by rw [ht] at h; simpa using h
    exact ⟨GlobalTheory.UnramOrder.algebraMap_inj L (by simpa using hs),
      GlobalTheory.UnramOrder.algebraMap_inj L (by simpa using ht)⟩
  let b : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [L.rank])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = ω := by simp [b]
  have hx : ∀ x, x = algebraMap F E (b.repr x 0) + algebraMap F E (b.repr x 1) * ω := by
    intro x
    have := b.sum_repr x
    rw [Fin.sum_univ_two, hb0, hb1] at this
    simpa [Algebra.smul_def] using this.symm
  refine ⟨b, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_⟩
  · have h1 := hx x
    have h2 := congrArg L.cj h1
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes] at h2
    have h3 : algebraMap F E (b.repr x 1) = (x - L.cj x) * e := by
      linear_combination -e * h1 + e * h2 - algebraMap F E (b.repr x 1) * hωe
    have h4 : algebraMap F E (b.repr x 1) ∈ L.O := by
      rw [h3]
      exact L.O.mul_mem (L.O.sub_mem h (GlobalTheory.UnramOrder.cj_mem L h)) he
    have h5 : algebraMap F E (b.repr x 0) ∈ L.O := by
      have : algebraMap F E (b.repr x 0) = x - algebraMap F E (b.repr x 1) * ω := by
        linear_combination -h1
      rw [this]
      exact L.O.sub_mem h (L.O.mul_mem h4 hω)
    intro i
    fin_cases i
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 h5
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 h4
  · rw [hx x]
    exact L.O.add_mem (hint _ (h 0)) (L.O.mul_mem (hint _ (h 1)) hω)
  · rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hb0, hb1, mul_one, map_sub, map_mul]
    have h1 := hx x
    have h2 := congrArg L.cj h1
    have h3 := hx (x * ω)
    have h4 := congrArg L.cj h3
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes] at h2 h4
    generalize algebraMap F E (b.repr x 0) = a at *
    generalize algebraMap F E (b.repr x 1) = c at *
    generalize algebraMap F E (b.repr (x * ω) 0) = a' at *
    generalize algebraMap F E (b.repr (x * ω) 1) = c' at *
    have key : (ω - L.cj ω) * (a * c' - a' * c - x * L.cj x) = 0 := by
      linear_combination (-(L.cj x)) * h3 + x * h4 + (a' + c' * L.cj ω) * h1 - (a' + c' * ω) * h2
    linear_combination e * key - (a * c' - a' * c - x * L.cj x) * hωe

theorem span_eq_map (L : LocE F E) {n m : ℕ} (y : Fin m → Fin n → E) :
    (Submodule.span L.O (Set.range y)).toAddSubgroup =
      (AddSubgroup.pi Set.univ fun _ : Fin m => L.O.toAddSubgroup).map
        (Fintype.linearCombination E y).toAddMonoidHom := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun,
    AddSubgroup.mem_map, AddSubgroup.mem_pi, Set.mem_univ, forall_true_left,
    LinearMap.toAddMonoidHom_coe, Fintype.linearCombination_apply, Subring.mem_toAddSubgroup]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun i => c i, fun i => (c i).2, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨fun i => ⟨c i, hc i⟩, rfl⟩

theorem index_rmul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n m : ℕ} (y : Fin m → Fin n → E), LinearIndependent E y → ∀ A : Matrix (Fin m) (Fin m) E, IsIntM L A → IsUnit A.det → 0 ≤ vE L ϖ (A.det * L.cj A.det) ∧ (Submodule.span L.O (Set.range (rmul y A))).toAddSubgroup.relIndex (Submodule.span L.O (Set.range y)).toAddSubgroup = resQ ϖ ^ (vE L ϖ (A.det * L.cj A.det)).toNat := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n m y hy A hA hu
  obtain ⟨b, hbO, hnorm⟩ := exists_basis L
  have := L.free
  have : Module.Finite F E := Module.Finite.of_basis b
  obtain ⟨-, -, hv3, hv4⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  have hdO : A.det ∈ L.O := by
    rw [Matrix.det_apply']
    exact L.O.sum_mem fun σ _ => L.O.mul_mem (intCast_mem _ _) (L.O.prod_mem fun i _ => hA _ _)
  have hN0 : Algebra.norm F A.det ≠ 0 := (hu.map (Algebra.norm F)).ne_zero
  have hNO : Algebra.norm F A.det ∈ 𝒪[F] := by
    rw [← GlobalTheory.UnramOrder.algebraMap_mem_iff L, hnorm]
    exact L.O.mul_mem hdO (GlobalTheory.UnramOrder.cj_mem L hdO)
  rw [← hnorm]
  have ha := (hv3 _ hN0).2 hNO
  obtain ⟨u, hu'⟩ := hv4 _ hN0
  refine ⟨ha, ?_⟩
  generalize vE L ϖ (algebraMap F E (Algebra.norm F A.det)) = a at *
  let φ : (Fin m → E) ≃ₗ[F] (Fin m → E) :=
    (Matrix.toLinearEquiv (Pi.basisFun E (Fin m)) A hu).restrictScalars F
  have hφ : ∀ v, φ v = A.mulVec v := fun v => by
    simp [φ, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin']
  have hdet : LinearMap.det (φ : (Fin m → E) →ₗ[F] (Fin m → E)) = Algebra.norm F A.det := by
    have : (φ : (Fin m → E) →ₗ[F] (Fin m → E)) = (Matrix.toLin' A).restrictScalars F := by
      ext1 v; exact LinearMap.ext fun w => hφ _
    rw [this, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  set W0 := (AddSubgroup.pi Set.univ fun _ : Fin m => L.O.toAddSubgroup) with hW0
  have hmem : ∀ x, x ∈ W0 ↔ ∀ i, x i ∈ L.O := fun x => by
    simp [hW0, AddSubgroup.mem_pi]
  obtain ⟨h1, -, h3⟩ := _root_.GlobalTheory.HL.LatDet.relVol_map ϖ hϖ (Pi.basis fun _ : Fin m => b) φ a u (hdet.trans hu') W0
    (fun x => by
      simp only [hmem, hbO, Pi.basis_repr, Sigma.forall])
  have hle : W0.map φ.toAddEquiv.toAddMonoidHom ≤ W0 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hmem]
    intro i
    change φ v i ∈ _
    rw [hφ, Matrix.mulVec, dotProduct]
    exact L.O.sum_mem fun j _ => L.O.mul_mem (hA _ _) ((hmem v).1 hv j)
  have hcomp : (Fintype.linearCombination E (rmul y A)).toAddMonoidHom =
      (Fintype.linearCombination E y).toAddMonoidHom.comp φ.toAddEquiv.toAddMonoidHom := by
    refine AddMonoidHom.ext fun v => ?_
    change Fintype.linearCombination E (rmul y A) v = Fintype.linearCombination E y (φ v)
    rw [hφ]
    simp only [Fintype.linearCombination_apply, rmul, Matrix.mulVec, dotProduct, Finset.smul_sum,
      Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have hinj : Function.Injective (Fintype.linearCombination E y).toAddMonoidHom := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    exact funext (Fintype.linearIndependent_iff.1 hy v hv)
  rw [span_eq_map, span_eq_map, ← hW0, hcomp, ← AddSubgroup.map_map,
    AddSubgroup.relIndex_map_map_of_injective _ _
      hinj]
  rw [relVol, AddSubgroup.relIndex_eq_one.2 hle] at h3
  lift a to ℕ using ha
  rw [zpow_neg, zpow_natCast, Nat.cast_one, one_div, inv_inj] at h3
  rw [Int.toNat_natCast]
  exact_mod_cast h3

end GlobalTheory.MatrixIndex
end

