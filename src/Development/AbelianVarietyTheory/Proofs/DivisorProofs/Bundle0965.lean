module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeRealSpecialUnitaryEqFlagDomainMass
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCoordinateWedgeLinearIndependentSpanEqTop
section
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR

theorem ofCard_symm_apply_eq_sort {n : ℕ} (s : Finset (Fin n)) (k : ℕ) (hk : k < s.card) :
    Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (rfl : s.card = s.card)) ⟨k, hk⟩ =
      (s.sort (· ≤ ·))[k]'(by rw [Finset.length_sort]; exact hk) := by
  show s.orderEmbOfFin rfl ⟨k, hk⟩ = _
  rw [Finset.orderEmbOfFin_apply]
  rfl

noncomputable def dlogBasis {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) :
    Module.Basis (Fin n) K Ω[K⁄ℤ] :=
  (Module.Basis.mk hx.1 (by rw [hx.2])).unitsSMul fun i => (x i)⁻¹

theorem dlogBasis_apply {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) (i : Fin n) :
    dlogBasis x hx i = dlog (x i) := by
  rw [dlogBasis, Module.Basis.unitsSMul_apply, Module.Basis.mk_apply, Units.smul_def]
  rfl

theorem logWedge_eq_basis {K : Type} [Field K] {n : ℕ} (x : Fin n → Kˣ) (hx : IsCoord x) :
    logWedge x = ⇑(dlogBasis x hx).ExteriorAlgebra := by
  funext s
  rw [ExteriorAlgebra.basis_apply_ofCard _ rfl, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    logWedge]
  congr 1
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_ofFn, Function.comp_apply, dlogBasis_apply]
    rw [ofCard_symm_apply_eq_sort]

theorem logWedge_basis : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ), IsCoord x →
    LinearIndependent K (logWedge x) ∧ Submodule.span K (Set.range (logWedge x)) = ⊤ := by
  intro K _ n x hx
  rw [logWedge_eq_basis x hx]
  exact ⟨(dlogBasis x hx).ExteriorAlgebra.linearIndependent, (dlogBasis x hx).ExteriorAlgebra.span_eq⟩

end GlobalTheory.LogDR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDifferentialMulLogCoordinateWedge
section
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR.WedgeMul

theorem prod_perm_sign {A : Type} [Ring A] {α : Type} (f : α → A)
    (hf : ∀ a b, f a * f b = -(f b * f a)) {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (l₁.map f).prod = ε • (l₂.map f).prod := by
  induction h with
  | nil => exact ⟨1, Or.inl rfl, by simp⟩
  | cons x _ ih =>
    obtain ⟨ε, hε, e⟩ := ih
    exact ⟨ε, hε, by simp only [List.map_cons, List.prod_cons, e, mul_smul_comm]⟩
  | swap x y l =>
    refine ⟨-1, Or.inr rfl, ?_⟩
    simp only [List.map_cons, List.prod_cons, ← mul_assoc, hf y x, neg_mul, neg_smul, one_smul]
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨ε₁, h₁, e₁⟩ := ih₁
    obtain ⟨ε₂, h₂, e₂⟩ := ih₂
    refine ⟨ε₁ * ε₂, ?_, by rw [e₁, e₂, smul_smul]⟩
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp

end GlobalTheory.LogDR.WedgeMul


open GlobalTheory.LogDR.WedgeMul in
theorem GlobalTheory.LogDR.dlog_mul_logWedge : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ) (i : Fin n) (I : Finset (Fin n)), (i ∈ I → ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = 0) ∧ (i ∉ I → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = ε • logWedge x (insert i I)) := by
  intro K _ n x i I
  set f : Fin n → abelian₂ K := fun j => ExteriorAlgebra.ι K (dlog (x j)) with hfdef
  have hf : ∀ a b, f a * f b = -(f b * f a) := fun a b =>
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  constructor
  · intro hi
    have hp : (I.sort (· ≤ ·)).Perm (i :: (I.erase i).sort (· ≤ ·)) := by
      refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ?_).2 fun a => ?_
      · refine List.nodup_cons.2 ⟨?_, Finset.sort_nodup _ _⟩
        simp
      · by_cases ha : a = i
        · subst ha; simp [hi]
        · simp [ha]
    obtain ⟨ε, -, e⟩ := prod_perm_sign f hf hp
    show f i * ((I.sort (· ≤ ·)).map f).prod = 0
    rw [e, mul_smul_comm, List.map_cons, List.prod_cons, ← mul_assoc]
    simp [hfdef, ExteriorAlgebra.ι_sq_zero]
  · intro hi
    have hp : ((insert i I).sort (· ≤ ·)).Perm (i :: I.sort (· ≤ ·)) := by
      refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ?_).2 fun a => ?_
      · exact List.nodup_cons.2 ⟨by simpa using hi, Finset.sort_nodup _ _⟩
      · simp
    obtain ⟨ε, hε, e⟩ := prod_perm_sign f hf hp
    refine ⟨ε, hε, ?_⟩
    show f i * ((I.sort (· ≤ ·)).map f).prod = ε • (((insert i I).sort (· ≤ ·)).map f).prod
    rw [e, List.map_cons, List.prod_cons, smul_smul]
    rcases hε with rfl | rfl <;> simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFrobeniusLiftSmulLogCoordinateWedge
section
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem cartierMap_smul_logWedge : ∀ (K : Type) [Field K] (p : ℕ) (n : ℕ) (x : Fin n → Kˣ) (γ : abelian₂ K →+* abelian₂ K),
    IsCartierMap p x γ → ∀ (c : K) (I : Finset (Fin n)), γ (c • logWedge x I) = c ^ p • logWedge x I := by
  intro K _ p n x γ hγ c I
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, hγ.1]
  congr 1
  unfold logWedge
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact hγ.2 i

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulVecOfMemTD
section
noncomputable section

open scoped Matrix

namespace GlobalTheory.HaarLin

def TD (R : Type) [CommRing R] (κ : Type) [Fintype κ] [DecidableEq κ] : Submonoid (Matrix κ κ R) :=
  Submonoid.closure ({M | ∃ i j : κ, ∃ c : R, i ≠ j ∧ M = Matrix.transvection i j c} ∪
    {M | ∃ d : κ → Rˣ, M = Matrix.diagonal fun i => (d i : R)})

def HasStableRangeOne (R : Type) [CommRing R] : Prop := ∀ a b : R, IsCoprime a b → ∃ t : R, IsUnit (a + t * b)

end GlobalTheory.HaarLin

open NumberField MeasureTheory Matrix
open scoped NNReal ENNReal
namespace GlobalTheory.HaarLin

private lemma nnreal_eq_of_smul_addHaar_eq {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    {a b : ℝ≥0} (h : a • μ = b • μ) : a = b := by
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : X)
  have h1 : μ K ≠ 0 := (μ.measure_pos_of_mem_nhds hK0).ne'
  have h2 : μ K ≠ ∞ := hK.measure_lt_top.ne
  have h3 : (a • μ) K = (b • μ) K := by rw [h]
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at h3
  exact_mod_cast (ENNReal.mul_left_inj h1 h2).1 h3

private lemma map_mul_lemma_2 {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {κ : Type} [Fintype κ] [MeasurableSpace (κ → R)] [BorelSpace (κ → R)]
    (A B : Matrix κ κ R) (μ : Measure (κ → R)) :
    μ.map (fun x => (A * B) *ᵥ x) = (μ.map (fun x => B *ᵥ x)).map (fun x => A *ᵥ x) := by
  have hA : Measurable (fun x : κ → R => A *ᵥ x) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hB : Measurable (fun x : κ → R => B *ᵥ x) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  rw [Measure.map_map hA hB]
  congr 1
  funext x
  simp [Function.comp, Matrix.mulVec_mulVec]

private lemma exists_map_mulVec_eq_smul_of_invertible {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (P Q : Matrix κ κ R) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    ∃ c : ℝ≥0, ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure → μ.map (fun x => P *ᵥ x) = c • μ := by
  let e : (κ → R) ≃+ (κ → R) :=
    { toFun := fun x => P *ᵥ x
      invFun := fun x => Q *ᵥ x
      left_inv := fun x => by simp [Matrix.mulVec_mulVec, hQP]
      right_inv := fun x => by simp [Matrix.mulVec_mulVec, hPQ]
      map_add' := fun x y => Matrix.mulVec_add P x y }
  have he : Continuous (fun x : κ → R => P *ᵥ x) := Continuous.matrix_mulVec continuous_const continuous_id
  have he' : Continuous (fun x : κ → R => Q *ᵥ x) := Continuous.matrix_mulVec continuous_const continuous_id
  have key : ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure → (μ.map (fun x => P *ᵥ x)).IsAddHaarMeasure :=
    fun μ _ => e.isAddHaarMeasure_map μ he he'
  let μ₀ : Measure (κ → R) := Measure.addHaar
  haveI := key μ₀ inferInstance
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μ₀.map (fun x => P *ᵥ x) = c • μ₀ :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun μ hμ => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • μ₀ := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  rw [hk, Measure.map_smul, hc, smul_comm]
  exact he.measurable.aemeasurable

private lemma map_transvection_mulVec_addHaar_eq_self {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (i j : κ) (hij : i ≠ j) (c : R)
    (μ : Measure (κ → R)) [μ.IsAddHaarMeasure] :
    μ.map (fun x => transvection i j c *ᵥ x) = μ := by
  set D : Matrix κ κ R := diagonal (Function.update (1 : κ → R) i (-1)) with hD0
  have hD : D * D = 1 := by
    rw [hD0, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    by_cases hk : k = i <;> simp [Function.update_apply, hk]
  have hT : transvection i j c * transvection i j (-c) = 1 := by
    rw [transvection_mul_transvection_same (h := hij), add_neg_cancel, transvection_zero]
  have hT' : transvection i j (-c) * transvection i j c = 1 := by
    rw [transvection_mul_transvection_same (h := hij), neg_add_cancel, transvection_zero]
  have hconj : D * transvection i j c * D = transvection i j (-c) := by
    have hji : j ≠ i := Ne.symm hij
    clear hD hT hT'
    ext a b
    simp only [hD0, Matrix.mul_diagonal, Matrix.diagonal_mul, transvection, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply, Function.update_apply, Pi.one_apply]
    clear hD0
    split_ifs <;> grind
  have hone : μ.map (fun x => (1 : Matrix κ κ R) *ᵥ x) = μ := by
    simp only [Matrix.one_mulVec, Measure.map_id']
  obtain ⟨a, ha⟩ := exists_map_mulVec_eq_smul_of_invertible D D hD hD
  obtain ⟨t, ht⟩ := exists_map_mulVec_eq_smul_of_invertible _ _ hT hT'
  obtain ⟨t', ht'⟩ := exists_map_mulVec_eq_smul_of_invertible _ _ hT' hT
  have haa : a * a = 1 := by
    have h := map_mul_lemma_2 D D μ
    rw [hD, hone, ha μ inferInstance, Measure.map_smul, ha μ inferInstance, smul_smul] at h
    all_goals try exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable.aemeasurable
    exact nnreal_eq_of_smul_addHaar_eq μ (by rw [one_smul]; exact h.symm)
  have htt : t' * t = 1 := by
    have h := map_mul_lemma_2 (transvection i j c) (transvection i j (-c)) μ
    rw [hT, hone, ht' μ inferInstance, Measure.map_smul, ht μ inferInstance, smul_smul] at h
    all_goals try exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable.aemeasurable
    exact nnreal_eq_of_smul_addHaar_eq μ (by rw [one_smul]; exact h.symm)
  have hcj : t' = a * t * a := by
    have h := map_mul_lemma_2 (D * transvection i j c) D μ
    rw [hconj, ht' μ inferInstance, ha μ inferInstance, Measure.map_smul, map_mul_lemma_2,
      ht μ inferInstance, Measure.map_smul, ha μ inferInstance, smul_smul, smul_smul] at h
    all_goals try exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable.aemeasurable
    exact nnreal_eq_of_smul_addHaar_eq μ h
  have h2 : t * t = 1 := by
    rw [hcj] at htt
    calc t * t = t * t * (a * a) := by rw [haa, mul_one]
      _ = a * t * a * t := by ring
      _ = 1 := htt
  have h3 : t = 1 := by
    have h4 : (t : ℝ) * t = 1 := by exact_mod_cast h2
    apply NNReal.eq
    have h5 := t.coe_nonneg
    push_cast
    nlinarith
  rw [ht μ inferInstance, h3, one_smul]

private lemma map_diagonal_mulVec_eq_inv_prod_smul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [inst : MeasurableSpace (κ → R)] [hb : BorelSpace (κ → R)] (d : κ → Rˣ)
    (μ : Measure (κ → R)) [μ.IsAddHaarMeasure] :
    μ.map (fun x => diagonal (fun i => (d i : R)) *ᵥ x) = (∏ i, distribHaarChar R (d i))⁻¹ • μ := by
  letI : MeasurableSpace R := borel R
  haveI : BorelSpace R := ⟨rfl⟩
  have e : inst = MeasurableSpace.pi :=
    (@BorelSpace.measurable_eq (κ → R) _ inst hb).trans
      (@BorelSpace.measurable_eq (κ → R) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst e
  have h1 : ∀ u : Rˣ, (Measure.addHaar : Measure R).map (fun y => (u : R) * y) =
      (distribHaarChar R u)⁻¹ • Measure.addHaar := by
    intro u
    have hu : (fun y : R => (u : R) * y) = fun y => (DomMulAct.mk.symm (DomMulAct.mk u⁻¹)⁻¹ : Rˣ) • y := by
      funext y
      simp [Units.smul_def]
    rw [hu]
    change DomMulAct.mk u⁻¹ • (Measure.addHaar : Measure R) = _
    rw [Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk u⁻¹ • (Measure.addHaar : Measure R)) Measure.addHaar,
      addHaarScalarFactor_smul_eq_distribHaarChar, map_inv]
  set ν : Measure (κ → R) := Measure.pi (fun _ => (Measure.addHaar : Measure R)) with hν0
  have hν : ν.map (fun x => diagonal (fun i => (d i : R)) *ᵥ x) = (∏ i, distribHaarChar R (d i))⁻¹ • ν := by
    have hf : (fun x : κ → R => diagonal (fun i => (d i : R)) *ᵥ x) = fun x i => (d i : R) * x i := by
      funext x i
      exact mulVec_diagonal _ _ _
    haveI : ∀ i, SigmaFinite ((Measure.addHaar : Measure R).map (fun y => (d i : R) * y)) := fun i => by
      rw [h1]; infer_instance
    rw [hf, hν0, Measure.pi_map_pi (f := fun i y => (d i : R) * y)
      (fun i => (continuous_const_mul (d i : R)).measurable.aemeasurable)]
    simp_rw [h1]
    refine Measure.pi_eq (fun s hs => ?_)
    rw [Measure.smul_apply, Measure.nnreal_smul_coe_apply, Measure.pi_pi]
    simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply, ← Finset.prod_inv_distrib,
      Finset.prod_mul_distrib]
    norm_cast
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  rw [hk, Measure.map_smul, hν, smul_comm]
  exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable.aemeasurable

private lemma exists_unit_det_map_mulVec_haar_eq_inv_smul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (M : Matrix κ κ R) (hM : M ∈ TD R κ) :
    ∃ v : Rˣ, (v : R) = M.det ∧ ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure →
      μ.map (fun x => M *ᵥ x) = (distribHaarChar R v)⁻¹ • μ := by
  induction hM using Submonoid.closure_induction with
  | mem M hM =>
    simp only [Set.mem_union, Set.mem_setOf_eq] at hM
    rcases hM with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩
    · refine ⟨1, by rw [det_transvection_of_ne (h := hij), Units.val_one], fun μ hμ => ?_⟩
      rw [map_one, inv_one, one_smul]
      exact map_transvection_mulVec_addHaar_eq_self i j hij c μ
    · refine ⟨∏ i, d i, by simp [det_diagonal], fun μ hμ => ?_⟩
      rw [map_prod]
      exact map_diagonal_mulVec_eq_inv_prod_smul d μ
  | one => exact ⟨1, by simp, fun μ hμ => by simp [Measure.map_id']⟩
  | mul M N _ _ hM hN =>
    obtain ⟨v, hv, hvμ⟩ := hM
    obtain ⟨w, hw, hwμ⟩ := hN
    refine ⟨v * w, by simp [hv, hw, det_mul], fun μ hμ => ?_⟩
    rw [map_mul_lemma_2, hwμ μ hμ, Measure.map_smul, hvμ μ hμ, smul_smul, map_mul, mul_inv, mul_comm]
    exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable.aemeasurable

theorem map_mulVec_of_mem_TD : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] (κ : Type) [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ R), M ∈ TD R κ → ∀ u : Rˣ, u.1 = M.det → ∀ μ : @Measure (κ → R) (borel _),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    @Measure.map _ _ (borel _) (borel _) (fun x : κ → R => M *ᵥ x) μ = ((distribHaarChar R u)⁻¹ : ℝ≥0) • μ := by
  intro R _ _ _ _ _ _ κ _ _ M hM u hu μ hμ
  letI : MeasurableSpace (κ → R) := borel (κ → R)
  haveI : BorelSpace (κ → R) := ⟨rfl⟩
  obtain ⟨v, hv, hvμ⟩ := exists_unit_det_map_mulVec_haar_eq_inv_smul M hM
  have huv : u = v := Units.ext (hu.trans hv.symm)
  subst huv
  exact hvμ μ hμ

end GlobalTheory.HaarLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkNormSqEqSimilitudeFactor
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem Pair.mark_norm_sq : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), P.Mark μ →
    ‖μ‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  intro p _ G P μ hμ
  obtain ⟨v, _, x, hx, hpos⟩ := hμ
  obtain ⟨_, _, hlaw⟩ := GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude p G P v
  set H := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hH
  set A := G.psi v (P.γ : G.C) with hA
  set q : ℂ := star x ⬝ᵥ (H *ᵥ x) with hq
  have hq0 : q ≠ 0 := by
    intro h0; rw [h0] at hpos; simp at hpos
  have key : star x ⬝ᵥ ((Aᴴ * H * A) *ᵥ x) = (star μ * μ) * q := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, hx, dotProduct_mulVec, ← star_mulVec, hx, mulVec_smul, star_smul,
      smul_dotProduct, dotProduct_smul, hq]
    simp only [smul_eq_mul]; ring
  rw [hlaw, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at key
  have hc : star μ * μ = ((P.c : ℚ) : ℂ) := by
    have := mul_right_cancel₀ hq0 key.symm
    exact this
  have h2 : ((‖μ‖ ^ 2 : ℝ) : ℂ) = ((((P.c : ℚ) : ℝ)) : ℂ) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    push_cast
    exact hc
  exact_mod_cast h2

end GlobalTheory.LKMid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedSimilitudePairMinpolyRootsNormSqEqStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.marked_similitude_pair_minpoly_roots_normSq_eq : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ → ∀ (φ : G.F →+* ℂ) (z : ℂ), P.pol.eval₂ φ z = 0 → ‖z‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  first | (exact @GlobalTheory.LKMid.MarkEll.mark_ell) | (exact GlobalTheory.LKMid.MarkEll.mark_ell) | (intros; apply GlobalTheory.LKMid.MarkEll.mark_ell  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassBoundOfTamagawaUnitary
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.UCls

theorem massBound_of_tamagawa : GlobalTheory.Published.TamagawaSpecialUnitary → GlobalTheory.UCls.MassBound := by
  intro hT E _ _ _ r M h m G Λ Ψ X g x0 FF hr hM hU hSD htor hUA hdist hX
  classical
  set Cc : ℝ := ((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E with hCc
  set P0 : ℝ := (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E with hP0
  set R : ℝ := rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) with hR
  set K : ℝ := (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R * P0 with hK
  have hCpos : 0 < Cc := pow_pos (mul_pos (mul_pos (by positivity) (by positivity))
    (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < r)))) _
  have hprod : 0 ≤ ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i :=
    Finset.prod_nonneg fun i _ => tsum_nonneg fun n => by positivity
  have hP0nn : 0 ≤ P0 := pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) hprod) _
  have hRnn : 0 ≤ R := Real.rpow_nonneg (by unfold rdE; exact Real.rpow_nonneg (by unfold dE; positivity) _) _
  have hP0le : P0 ≤ Cc := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hprod) (GlobalTheory.volumeConstant_le r hr) _
  have hKnn : 0 ≤ K := by positivity
  have hdet : ∀ i, ∀ γ ∈ (X i).Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1 := fun i =>
    _root_.GlobalTheory.UnitaryCongruenceDet.det_eq_one E r M (X i) hM (by rw [(hX i).1]; exact (hX i).2.2.2.1)
  let cv : Fin m → ℝ≥0∞ := fun i => covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm)
    (riemHaar (X i).Ψ (X i).Gm (x0 i))
  have hV1 : ∀ i, ENNReal.ofReal Cc * muF (X i) (x0 i) (FF i) = cv i := fun i =>
    _root_.GlobalTheory.SUCovol.covolume_realSU E r (X i) (x0 i) (FF i) (by omega) (hdet i) (hX i).2.2.2.2.1 (hX i).2.2.2.2.2
  have hTA : ∀ i, IsTA (IsCMField.complexConj E) (g i).det := fun i => _root_.GlobalTheory.unitary_det_isTA E r G (g i) hSD.2.1 (hUA i)
  let f : Fin m → Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
      TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1 := fun i => Quot.mk _ ⟨(g i).det, hTA i⟩
  have hQfin : Finite (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
      TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    have h1 : torusNo (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M = ⊤ := ENat.card_eq_top_of_infinite
    rw [h1] at htor
    exact absurd htor (by simp)
  have hcard : (Finset.univ.image f).card ≤ h := by
    have h1 : (Finset.univ.image f).card ≤ Nat.card (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1) := by
      haveI := Fintype.ofFinite (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1)
      rw [Nat.card_eq_fintype_card]; exact Finset.card_le_univ _
    have h2 : ((Nat.card (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1) : ℕ) : ℕ∞) ≤ h := by
      rw [← ENat.card_eq_coe_natCard]; exact htor
    exact h1.trans (by exact_mod_cast h2)
  have hfib : ∀ q ∈ Finset.univ.image f, ∑ i ∈ Finset.univ.filter (fun i => f i = q), cv i ≤ ENNReal.ofReal K := by
    intro q hq
    obtain ⟨i0, -, hi0⟩ := Finset.mem_image.1 hq
    refine _root_.GlobalTheory.ClassSum.sum_covolume_le hT E r M m G Λ Ψ X g x0 _ (g i0) hr hM hU hSD (hUA i0) hUA ?_ (fun i _ j _ => hdist i j)
      (fun i _ => ⟨(hX i).1, (hX i).2.1, (hX i).2.2.1, (hX i).2.2.2.1, (hX i).2.2.2.2.1⟩)
    intro i hi
    have hfi : f i0 = f i := by rw [hi0, (Finset.mem_filter.1 hi).2]
    exact _root_.GlobalTheory.UCls.torus_eqvGen_main E r M G (Λ : Set (Fin r → E)) ⟨(g i0).det, hTA i0⟩ ⟨(g i).det, hTA i⟩ (Quot.eqvGen_exact hfi)
  have hsum : ∑ i, cv i ≤ ENNReal.ofReal (h * K) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image f) (g := f)
      (fun i _ => Finset.mem_image_of_mem f (Finset.mem_univ i))]
    calc _ ≤ ∑ q ∈ Finset.univ.image f, ENNReal.ofReal K := Finset.sum_le_sum hfib
      _ = ((Finset.univ.image f).card : ℝ≥0∞) * ENNReal.ofReal K := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (h : ℝ≥0∞) * ENNReal.ofReal K := by gcongr
      _ = ENNReal.ofReal (h * K) := by rw [ENNReal.ofReal_mul (p := (h : ℝ)) (by positivity), ENNReal.ofReal_natCast]
  have hmu : ∀ i, muF (X i) (x0 i) (FF i) = cv i / ENNReal.ofReal Cc := by
    intro i
    rw [ENNReal.eq_div_iff (ENNReal.ofReal_pos.2 hCpos).ne' ENNReal.ofReal_ne_top]
    exact hV1 i
  calc ∑ i, muF (X i) (x0 i) (FF i) = (∑ i, cv i) * (ENNReal.ofReal Cc)⁻¹ := by
        simp only [hmu, div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ENNReal.ofReal (h * K) * (ENNReal.ofReal Cc)⁻¹ := by gcongr
    _ = ENNReal.ofReal (h * K / Cc) := by rw [ENNReal.ofReal_div_of_pos hCpos, div_eq_mul_inv]
    _ ≤ ENNReal.ofReal (massBd E r M h) := by
        apply ENNReal.ofReal_le_ofReal
        have hA : 0 ≤ (h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R := by positivity
        have hq : P0 / Cc ≤ 1 := (div_le_one hCpos).2 hP0le
        calc (h : ℝ) * K / Cc = ((h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R) * (P0 / Cc) := by
              rw [hK]; ring
          _ ≤ ((h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R) * 1 := mul_le_mul_of_nonneg_left hq hA
          _ ≤ 2 * (h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R := by nlinarith
          _ = massBd E r M h := rfl

end GlobalTheory.UCls
end

