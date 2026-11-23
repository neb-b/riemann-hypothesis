module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0030
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Slopes.PCanonicalFiltration
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AbelianPartHeightLinear
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights Polynomial

theorem exists_integral_generator (E : Type) [Field E] [NumberField E] :
    ∃ (θ : 𝓞 E) (m : ℤ[X]), m.Monic ∧ aeval θ m = 0 ∧ m.natDegree = Module.finrank ℚ E ∧
      ∀ a : 𝓞 E, ∃ (n : ℤ) (P : ℤ[X]), n ≠ 0 ∧ (n : 𝓞 E) * a = aeval θ P := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  have halg : IsAlgebraic ℤ α :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic α)
  obtain ⟨n, hn, hint⟩ := halg.exists_integral_multiple
  set β : E := n • α with hβ
  have hnq : ((n : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hn
  have hαβ : α = ((n : ℚ))⁻¹ • β := by
    rw [hβ, ← Int.cast_smul_eq_zsmul ℚ n α, smul_smul, inv_mul_cancel₀ hnq, one_smul]
  have htop : IntermediateField.adjoin ℚ {β} = ⊤ := by
    rw [eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff, hαβ]
    exact (IntermediateField.adjoin ℚ {β}).smul_mem (IntermediateField.mem_adjoin_simple_self ℚ β)
  have hintQ : IsIntegral ℚ β := Algebra.IsIntegral.isIntegral β
  let θ : 𝓞 E := ⟨β, hint⟩
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := RingOfIntegers.coe_injective
  have hcoe : ∀ P : ℤ[X], algebraMap (𝓞 E) E (aeval θ P) = aeval β P := fun P => by
    have := aeval_algHom_apply (IsScalarTower.toAlgHom ℤ (𝓞 E) E) θ P
    exact this.symm
  refine ⟨θ, minpoly ℤ β, minpoly.monic hint, ?_, ?_, ?_⟩
  · apply hinj
    rw [hcoe, minpoly.aeval, map_zero]
  · have h1 := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
    have h2 := IntermediateField.adjoin.finrank hintQ
    rw [htop, IntermediateField.finrank_top', h1, (minpoly.monic hint).natDegree_map] at h2
    exact h2.symm
  · intro a
    have ha : (a : E) ∈ Algebra.adjoin ℚ {β} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hintQ.isAlgebraic, htop]
      exact Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨Q, hQ⟩ := ha
    obtain ⟨b, hbmem, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) Q
    refine ⟨b, IsLocalization.integerNormalization (nonZeroDivisors ℤ) Q,
      nonZeroDivisors.coe_ne_zero ⟨b, hbmem⟩, ?_⟩
    apply hinj
    have hQ' : aeval β Q = (a : E) := hQ
    rw [hcoe, ← aeval_map_algebraMap ℚ, hb, map_mul, map_intCast, zsmul_eq_mul, map_mul, map_intCast, hQ']

theorem ker_aeval_prod_le {L V : Type} [Field L] [AddCommGroup V] [Module L V] (T : Module.End L V) (S : Finset L) :
    LinearMap.ker (aeval T (∏ c ∈ S, (X - C c))) ≤ ⨆ c ∈ S, Module.End.eigenspace T c := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Module.End.one_eq_id]
  | insert c S hc ih =>
    rw [Finset.prod_insert hc]
    have hcop : IsCoprime (X - C c) (∏ d ∈ S, (X - C d)) :=
      IsCoprime.prod_right fun d hd => isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero.2 (fun h : c = d => hc (by rw [h]; exact hd))).isUnit
    rw [← sup_ker_aeval_eq_ker_aeval_mul_of_coprime T hcop, Finset.iSup_insert]
    refine sup_le_sup ?_ ih
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Module.End.mem_eigenspace_iff]
    simpa [sub_eq_zero] using hx

theorem iSup_eigSp_eq_top {E L V ι : Type} [Field E] [NumberField E] [Field L] [CharZero L] [AddCommGroup V] [Module L V]
    [Fintype ι] (ρ : 𝓞 E →+* Module.End L V) (σ : ι → (𝓞 E →+* L)) (hσ : Function.Injective σ)
    (hcard : Fintype.card ι = Module.finrank ℚ E) : ⨆ s, eigSp ρ (σ s) = ⊤ := by
  classical
  obtain ⟨θ, m, hmon, hm0, hdeg, hgen⟩ := exists_integral_generator E
  have hagree : ∀ (τ : 𝓞 E →+* L) (P : ℤ[X]), τ (aeval θ P) = aeval (τ θ) P := fun τ P =>
    (aeval_algHom_apply τ.toIntAlgHom θ P).symm
  have hinjc : Function.Injective fun s => σ s θ := by
    intro s t hst
    apply hσ
    ext a
    obtain ⟨n, P, hn, hP⟩ := hgen a
    have h1 := hagree (σ s) P
    have h2 := hagree (σ t) P
    have hst' : σ s θ = σ t θ := hst
    rw [hst', ← h2, ← hP, map_mul, map_mul, map_intCast, map_intCast] at h1
    exact mul_left_cancel₀ (by exact_mod_cast hn) h1
  set S : Finset L := Finset.univ.image fun s => σ s θ with hS
  have hScard : S.card = Module.finrank ℚ E := by
    rw [hS, Finset.card_image_of_injective _ hinjc, Finset.card_univ, hcard]
  set mL : L[X] := m.map (algebraMap ℤ L) with hmL
  have hmLmon : mL.Monic := hmon.map _
  have hmLdeg : mL.natDegree = Module.finrank ℚ E := by rw [hmL, hmon.natDegree_map, hdeg]
  have hprodmon : (∏ c ∈ S, (X - C c)).Monic := monic_prod_of_monic _ _ fun c _ => monic_X_sub_C c
  have hprodeg : (∏ c ∈ S, (X - C c) : L[X]).natDegree = Module.finrank ℚ E := by
    rw [natDegree_prod_of_monic _ _ fun c _ => monic_X_sub_C c]
    simp [hScard]
  have hdvd : (∏ c ∈ S, (X - C c)) ∣ mL := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro c _ d _ hcd
      exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hcd).isUnit
    · intro c hc
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hc
      rw [dvd_iff_isRoot, IsRoot.def, hmL, eval_map_algebraMap, ← hagree, hm0, map_zero]
  have heq : mL = ∏ c ∈ S, (X - C c) :=
    eq_of_monic_of_dvd_of_natDegree_le hprodmon hmLmon hdvd (by rw [hmLdeg, hprodeg])
  have hρ : ∀ P : ℤ[X], aeval (ρ θ) P = ρ (aeval θ P) := fun P =>
    aeval_algHom_apply ρ.toIntAlgHom θ P
  have hT : aeval (ρ θ) (∏ c ∈ S, (X - C c)) = 0 := by
    rw [← heq, hmL, aeval_map_algebraMap, hρ, hm0, map_zero]
  rw [eq_top_iff]
  have hker : (⊤ : Submodule L V) ≤ LinearMap.ker (aeval (ρ θ) (∏ c ∈ S, (X - C c))) := by
    rw [hT, LinearMap.ker_zero]
  refine hker.trans ((ker_aeval_prod_le (ρ θ) S).trans (iSup₂_le fun c hc => ?_))
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hc
  refine le_trans ?_ (le_iSup _ s)
  intro x hx
  rw [Module.End.mem_eigenspace_iff] at hx
  have hpow : ∀ k : ℕ, ((ρ θ) ^ k) x = (σ s θ) ^ k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ]
  have hP : ∀ P : ℤ[X], (aeval (ρ θ) P) x = (aeval (σ s θ) P) • x := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq, add_smul]
    | monomial k a =>
      simp only [aeval_monomial, Module.End.mul_apply, hpow, eq_intCast, map_intCast]
      rw [Module.End.intCast_apply, mul_smul, Int.cast_smul_eq_zsmul]
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  intro a
  obtain ⟨n, P, hn, hnP⟩ := hgen a
  have h2 := hP P
  rw [hρ, ← hagree, ← hnP, map_mul, map_mul, map_intCast, map_intCast] at h2
  rw [Module.End.mul_apply, Module.End.intCast_apply, mul_smul, ← Int.cast_smul_eq_zsmul L n] at h2
  exact smul_right_injective V (by exact_mod_cast hn : (n : L) ≠ 0) h2

section Lattice

variable {L V : Type} [Field L] [NumberField L] [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
  [IsScalarTower (𝓞 L) L V]

theorem exists_smul_mem_of_span {Λ : Submodule (𝓞 L) V} (h : Submodule.span L (Λ : Set V) = ⊤) (p : V) :
    ∃ b : 𝓞 L, b ≠ 0 ∧ b • p ∈ Λ :=
  by apply _root_.UpperTheory.Reformulated.B.ClearDenominatorsLattice.exists_integer_smul_mem_of_span_top <;> assumption

end Lattice

namespace LinPt

variable {E L Ψ : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] {V : Type} [AddCommGroup V]
  [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V)

theorem img_eq (s : Ψ ⊕ Ψ) :
    A.img s = (((eigSp A.ρ (A.σ s)).restrictScalars (𝓞 L)).comap A.Λ.subtype).map A.f := by
  unfold img eig
  rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]

theorem saturation_iSup_img (hcard : 2 * Fintype.card Ψ = Module.finrank ℚ E) :
    CanonicalFiltration.saturation A.Bq (⨆ s, A.img s) = ⊤ := by
  have htop := iSup_eigSp_eq_top A.ρ A.σ A.σ_bij.1 (by rw [Fintype.card_sum, ← hcard]; ring)
  have key : ∀ x : V, ∃ b : 𝓞 L, b ≠ 0 ∧ ∃ h : b • x ∈ A.Λ, A.f ⟨b • x, h⟩ ∈ ⨆ s, A.img s := by
    intro x
    have hx : x ∈ ⨆ s, eigSp A.ρ (A.σ s) := htop ▸ Submodule.mem_top
    refine Submodule.iSup_induction _
      (motive := fun x => ∃ b : 𝓞 L, b ≠ 0 ∧ ∃ h : b • x ∈ A.Λ, A.f ⟨b • x, h⟩ ∈ ⨆ s, A.img s) hx ?_ ?_ ?_
    · intro s x hx
      obtain ⟨b, hb, hbx⟩ := exists_smul_mem_of_span A.span x
      refine ⟨b, hb, hbx, Submodule.mem_iSup_of_mem s ?_⟩
      rw [img_eq]
      refine Submodule.mem_map_of_mem ?_
      show b • x ∈ eigSp A.ρ (A.σ s)
      rw [← algebraMap_smul L b x]
      exact Submodule.smul_mem _ _ hx
    · have h0 : (1 : 𝓞 L) • (0 : V) ∈ A.Λ := by simp
      refine ⟨1, one_ne_zero, h0, ?_⟩
      have e : (⟨(1 : 𝓞 L) • (0 : V), h0⟩ : A.Λ) = 0 := Subtype.ext (by simp)
      rw [e, map_zero]
      exact Submodule.zero_mem _
    · rintro x y ⟨b, hb, hbx, hfx⟩ ⟨c, hc, hcy, hfy⟩
      have e0 : (b * c) • (x + y) = c • (b • x) + b • (c • y) := by
        rw [smul_add, smul_smul, smul_smul, mul_comm c b]
      have h1 : (b * c) • (x + y) ∈ A.Λ := by
        rw [e0]
        exact A.Λ.add_mem (A.Λ.smul_mem _ hbx) (A.Λ.smul_mem _ hcy)
      have e : (⟨(b * c) • (x + y), h1⟩ : A.Λ) = c • ⟨b • x, hbx⟩ + b • ⟨c • y, hcy⟩ := Subtype.ext e0
      refine ⟨b * c, mul_ne_zero hb hc, h1, ?_⟩
      rw [e, map_add (f := _), map_smul, map_smul]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hfx) (Submodule.smul_mem _ _ hfy)
  rw [eq_top_iff]
  intro y _
  obtain ⟨a, x, ha, hfx⟩ := A.full y
  obtain ⟨b, hb, hbx, hf⟩ := key x
  refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
  have e : (⟨b • (x : V), hbx⟩ : A.Λ) = b • x := Subtype.ext rfl
  rw [e, map_smul, hfx, smul_smul] at hf
  exact hf

end LinPt

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagValuationNormalization
section
noncomputable section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.IwBlock

theorem exists_blocks_add {L : Type} [Field L] (V : ValuationSubring L) (n m : ℕ)
    (A : Matrix (Fin (n + m)) (Fin (n + m)) L)
    (hA : ∀ a b : Fin (n + m), ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → A a b = 0) (hd : A.det ≠ 0) :
    ∃ (K : Matrix (Fin (n + m)) (Fin (n + m)) V) (U : Matrix (Fin (n + m)) (Fin (n + m)) L),
      IsUnit K.det ∧ (∀ a b : Fin (n + m), ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → U a b = 0) ∧
      U.BlockTriangular id ∧ (∀ a, U a a ≠ 0) ∧ A = K.map (algebraMap V L) * U := by
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  let A₁ : Matrix (Fin n) (Fin n) L := fun i k => A (e (Sum.inl i)) (e (Sum.inl k))
  let A₂ : Matrix (Fin m) (Fin m) L := fun i k => A (e (Sum.inr i)) (e (Sum.inr k))
  have lt_l : ∀ i : Fin n, ((e (Sum.inl i) : Fin (n + m)) : ℕ) < n := fun i => by simp [e]
  have ge_r : ∀ i : Fin m, ¬ ((e (Sum.inr i) : Fin (n + m)) : ℕ) < n := fun i => by simp [e]
  have val_l : ∀ i : Fin n, ((e (Sum.inl i) : Fin (n + m)) : ℕ) = i := fun i => by simp [e]
  have val_r : ∀ i : Fin m, ((e (Sum.inr i) : Fin (n + m)) : ℕ) = n + i := fun i => by simp [e]
  have hB : A.submatrix e e = fromBlocks A₁ 0 0 A₂ := by
    ext (i | i) (k | k)
    · rfl
    · exact hA _ _ fun h => ge_r k (h.1 (lt_l i))
    · exact hA _ _ fun h => ge_r i (h.2 (lt_l k))
    · rfl
  have hdet : A₁.det * A₂.det ≠ 0 := by
    rw [← det_fromBlocks_zero₂₁ A₁ 0 A₂, ← hB, det_submatrix_equiv_self]
    exact hd
  obtain ⟨k₁, U₁, hk₁, hU₁, hd₁, e₁⟩ := GlobalTheory.ValIwasawa.iwasawa_matrix (V := V) A₁ (left_ne_zero_of_mul hdet)
  obtain ⟨k₂, U₂, hk₂, hU₂, hd₂, e₂⟩ := GlobalTheory.ValIwasawa.iwasawa_matrix (V := V) A₂ (right_ne_zero_of_mul hdet)
  refine ⟨(fromBlocks k₁ 0 0 k₂).submatrix e.symm e.symm, (fromBlocks U₁ 0 0 U₂).submatrix e.symm e.symm,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁]
    exact hk₁.mul hk₂
  · intro a b h
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    rcases x with i | i <;> rcases y with k | k
    · exact absurd (iff_of_true (lt_l i) (lt_l k)) h
    · simp
    · simp
    · exact absurd (iff_of_false (ge_r i) (ge_r k)) h
  · intro a b h
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    have h' : ((e y : Fin (n + m)) : ℕ) < (e x : Fin (n + m)) := h
    rcases x with i | i <;> rcases y with k | k
    · rw [val_l, val_l] at h'
      simpa using hU₁ (show k < i from h')
    · simp
    · simp
    · rw [val_r, val_r] at h'
      simpa using hU₂ (show k < i from Nat.lt_of_add_lt_add_left h')
  · intro a
    obtain ⟨x, rfl⟩ := e.surjective a
    rcases x with i | i
    · simpa using hd₁ i
    · simpa using hd₂ i
  · have h1 : A = (fromBlocks A₁ 0 0 A₂).submatrix e.symm e.symm := by
      rw [← hB]; ext a b; simp
    have h3 : fromBlocks A₁ 0 0 A₂ =
        (fromBlocks k₁ 0 0 k₂).map (algebraMap V L) * fromBlocks U₁ 0 0 U₂ := by
      rw [fromBlocks_map, fromBlocks_multiply, ← e₁, ← e₂,
        Matrix.map_zero _ (map_zero (algebraMap V L)), Matrix.map_zero _ (map_zero (algebraMap V L))]
      simp
    rw [h1, h3, ← submatrix_mul_equiv _ _ _ e.symm _]
    rfl

theorem exists_blocks {L : Type} [Field L] (V : ValuationSubring L) (N n : ℕ) (hn : n ≤ N)
    (A : Matrix (Fin N) (Fin N) L)
    (hA : ∀ a b : Fin N, ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → A a b = 0) (hd : A.det ≠ 0) :
    ∃ (K : Matrix (Fin N) (Fin N) V) (U : Matrix (Fin N) (Fin N) L),
      IsUnit K.det ∧ (∀ a b : Fin N, ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → U a b = 0) ∧
      U.BlockTriangular id ∧ (∀ a, U a a ≠ 0) ∧ A = K.map (algebraMap V L) * U := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact exists_blocks_add V n m A hA hd

theorem inv_diag_ne_zero {L : Type} [Field L] {N : ℕ} {U : Matrix (Fin N) (Fin N) L}
    (hU : U.BlockTriangular id) (hd : IsUnit U.det) (a : Fin N) : U⁻¹ a a ≠ 0 := by
  have hI : U⁻¹.BlockTriangular id := by
    letI := Matrix.invertibleOfIsUnitDet U hd
    exact blockTriangular_inv_of_blockTriangular hU
  intro e
  have h := congrFun (congrFun (nonsing_inv_mul U hd) a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single a (fun c _ hc => ?_) (by simp), e,
    zero_mul] at h
  · exact zero_ne_one h
  · rcases lt_or_gt_of_ne hc with l | l
    · rw [hI l, zero_mul]
    · rw [hU l, mul_zero]

theorem main : ∀ (L : Type) [Field L] (V : ValuationSubring L) (N j : ℕ) (A : Matrix (Fin N) (Fin N) L), IsBlockDiag j A → A.det ≠ 0 → ∃ b : Matrix (Fin N) (Fin N) L, IsBlockDiag j b ∧ b.BlockTriangular id ∧ (∀ a, b a a ≠ 0) ∧ (∀ a c, (A * b) a c ∈ V) ∧ (A * b).det ≠ 0 ∧ ((A * b).det)⁻¹ ∈ V := by
  intro L _ V N j A hA hd
  obtain ⟨K, U, hK, hUb, hUt, hUd, hAe⟩ := exists_blocks V N (N - j) (Nat.sub_le N j) A hA hd
  have hUdet : IsUnit U.det := by
    rw [det_of_upperTriangular hUt]
    exact (Finset.prod_ne_zero_iff.2 fun a _ => hUd a).isUnit
  have hAU : A * U⁻¹ = K.map (algebraMap V L) := by
    rw [hAe, Matrix.mul_nonsing_inv_cancel_right _ _ hUdet]
  have hKdet : (K.map (algebraMap V L)).det = algebraMap V L K.det := (RingHom.map_det _ K).symm
  have hUb' : IsBlockDiag j U := hUb
  refine ⟨U⁻¹, hUb'.inv hUdet, ?_, inv_diag_ne_zero hUt hUdet, fun a c => ?_, ?_, ?_⟩
  · letI := Matrix.invertibleOfIsUnitDet U hUdet
    exact blockTriangular_inv_of_blockTriangular hUt
  · rw [hAU]
    exact (K a c).2
  · rw [hAU, hKdet]
    exact (hK.map (algebraMap V L)).ne_zero
  · rw [hAU, hKdet]
    obtain ⟨u, hu⟩ := hK
    rw [← hu]
    have e : (algebraMap V L (u : V))⁻¹ = algebraMap V L ((u⁻¹ : Vˣ) : V) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← map_mul, Units.mul_inv, map_one]
    rw [e]
    exact ((u⁻¹ : Vˣ) : V).2

end GlobalTheory.CompanionTheory.Ar.PB.IwBlock
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CompatibleChartProductProjection
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.ChartSwap

variable {e n : ℕ}

theorem continuous_comp_emb (σ : Fin n ↪ Fin e) :
    Continuous (fun w : Fin e → ℂ => w ∘ σ) :=
  continuous_pi fun j => continuous_apply (σ j)

theorem analyticAt_comp_emb (σ : Fin n ↪ Fin e) (w : Fin e → ℂ) :
    AnalyticAt ℂ (fun v : Fin e → ℂ => v ∘ σ) w := by
  rw [analyticAt_pi_iff]
  intro j
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) (σ j)).analyticAt w

theorem extend_comp_emb (σ : Fin n ↪ Fin e) (g : Fin n → ℂ) (w : Fin e → ℂ) :
    Function.extend σ g w ∘ σ = g :=
  funext fun j => σ.injective.extend_apply g w j

theorem extend_extend_emb (σ : Fin n ↪ Fin e) (g : Fin n → ℂ) (w : Fin e → ℂ) :
    Function.extend σ (w ∘ σ) (Function.extend σ g w) = w := by
  funext i
  by_cases h : ∃ j, σ j = i
  · obtain ⟨j, rfl⟩ := h
    exact σ.injective.extend_apply _ _ j
  · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]

theorem analyticAt_extend_emb (σ : Fin n ↪ Fin e) {f : (Fin n → ℂ) → Fin n → ℂ} {w : Fin e → ℂ}
    (hf : AnalyticAt ℂ f (w ∘ σ)) :
    AnalyticAt ℂ (fun v : Fin e → ℂ => Function.extend σ (f (v ∘ σ)) v) w := by
  rw [analyticAt_pi_iff]
  intro i
  by_cases h : ∃ j, σ j = i
  · obtain ⟨j, rfl⟩ := h
    have hfun : (fun v : Fin e → ℂ => Function.extend σ (f (v ∘ σ)) v (σ j)) =
        (fun y : Fin n → ℂ => f y j) ∘ (fun v : Fin e → ℂ => v ∘ σ) := by
      funext v
      exact σ.injective.extend_apply _ _ j
    rw [hfun]
    exact AnalyticAt.comp (analyticAt_pi_iff.1 hf j) (analyticAt_comp_emb σ w)
  · have hfun : (fun v : Fin e → ℂ => Function.extend σ (f (v ∘ σ)) v i) = fun v => v i := by
      funext v
      exact Function.extend_apply' _ _ _ h
    rw [hfun]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i).analyticAt w

noncomputable def extendHomeo (σ : Fin n ↪ Fin e)
    (τ : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ))
    (h₁ : AnalyticOnNhd ℂ τ τ.source) (h₂ : AnalyticOnNhd ℂ τ.symm τ.target) :
    OpenPartialHomeomorph (Fin e → ℂ) (Fin e → ℂ) where
  toFun w := Function.extend σ (τ (w ∘ σ)) w
  invFun w := Function.extend σ (τ.symm (w ∘ σ)) w
  source := {w | w ∘ σ ∈ τ.source}
  target := {w | w ∘ σ ∈ τ.target}
  map_source' w hw := by
    show Function.extend σ (τ (w ∘ σ)) w ∘ σ ∈ τ.target
    rw [extend_comp_emb]
    exact τ.map_source hw
  map_target' w hw := by
    show Function.extend σ (τ.symm (w ∘ σ)) w ∘ σ ∈ τ.source
    rw [extend_comp_emb]
    exact τ.map_target hw
  left_inv' w hw := by
    show Function.extend σ (τ.symm (Function.extend σ (τ (w ∘ σ)) w ∘ σ))
      (Function.extend σ (τ (w ∘ σ)) w) = w
    rw [extend_comp_emb, τ.left_inv hw, extend_extend_emb]
  right_inv' w hw := by
    show Function.extend σ (τ (Function.extend σ (τ.symm (w ∘ σ)) w ∘ σ))
      (Function.extend σ (τ.symm (w ∘ σ)) w) = w
    rw [extend_comp_emb, τ.right_inv hw, extend_extend_emb]
  open_source := τ.open_source.preimage (continuous_comp_emb σ)
  open_target := τ.open_target.preimage (continuous_comp_emb σ)
  continuousOn_toFun := fun w hw =>
    (analyticAt_extend_emb σ (h₁ _ hw)).continuousAt.continuousWithinAt
  continuousOn_invFun := fun w hw =>
    (analyticAt_extend_emb σ (h₂ _ hw)).continuousAt.continuousWithinAt

theorem chart_swap :
    ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X) (Ab : FinHolAtlas n Z) (pr : X → Z) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e) (ψb : OpenPartialHomeomorph Z (Fin n → ℂ)), IsCompatChart A ψ → IsCompatChart Ab ψb → (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i)) → ∃ ψ' : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ' ∧ ψ'.source = ψ.source ∩ pr ⁻¹' ψb.source ∧ ∀ y ∈ ψ'.source, ∀ i, ψ' y (σ i) = ψb (pr y) i := by
  intro e n X Z _ _ A Ab pr ψ kb σ ψb hψ hb hpr
  have h₁ : AnalyticOnNhd ℂ ((Ab.chart kb).symm.trans ψb)
      ((Ab.chart kb).symm.trans ψb).source := by
    intro y hy
    exact (hb kb).1 y hy
  have h₂ : AnalyticOnNhd ℂ ((Ab.chart kb).symm.trans ψb).symm
      ((Ab.chart kb).symm.trans ψb).target := by
    intro y hy
    exact (hb kb).2 y hy
  have hcomp : ∀ y ∈ ψ.source, ψ y ∘ σ = Ab.chart kb (pr y) := fun y hy =>
    funext fun i => ((hpr y hy).2 i).symm
  let T := extendHomeo σ ((Ab.chart kb).symm.trans ψb) h₁ h₂
  have hTan : ∀ w ∈ T.source, AnalyticAt ℂ T w := fun w hw =>
    analyticAt_extend_emb σ (h₁ _ hw)
  have hTsan : ∀ w ∈ T.target, AnalyticAt ℂ T.symm w := fun w hw =>
    analyticAt_extend_emb σ (h₂ _ hw)
  have hsrc : (ψ.trans T).source = ψ.source ∩ pr ⁻¹' ψb.source := by
    ext y
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      have h3 : ψ y ∘ σ ∈ ((Ab.chart kb).symm.trans ψb).source := hy'
      rw [hcomp y hy, OpenPartialHomeomorph.trans_source] at h3
      have h4 := h3.2
      simp only [Set.mem_preimage] at h4
      rwa [(Ab.chart kb).left_inv (hpr y hy).1] at h4
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      show ψ y ∘ σ ∈ ((Ab.chart kb).symm.trans ψb).source
      rw [hcomp y hy, OpenPartialHomeomorph.trans_source]
      refine ⟨(Ab.chart kb).map_source (hpr y hy).1, ?_⟩
      simp only [Set.mem_preimage]
      rwa [(Ab.chart kb).left_inv (hpr y hy).1]
  refine ⟨ψ.trans T, ?_, hsrc, ?_⟩
  · intro j
    refine ⟨?_, ?_⟩
    · rintro y ⟨hy1, hy2⟩
      rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source] at hy2
      have h := (hψ j).1 y ⟨hy1, hy2.1⟩
      exact AnalyticAt.comp (g := T) (f := ψ ∘ (A.chart j).symm) (hTan _ hy2.2) h
    · rintro z ⟨hz1, hz2⟩
      rw [OpenPartialHomeomorph.trans_target] at hz1
      have h := (hψ j).2 (T.symm z) ⟨hz1.2, hz2⟩
      exact AnalyticAt.comp (g := A.chart j ∘ ψ.symm) (f := T.symm) h (hTsan z hz1.1)
  · intro y hy i
    rw [hsrc] at hy
    show Function.extend σ (((Ab.chart kb).symm.trans ψb) (ψ y ∘ σ)) (ψ y) (σ i) = ψb (pr y) i
    rw [σ.injective.extend_apply, hcomp y hy.1]
    show ψb ((Ab.chart kb).symm (Ab.chart kb (pr y))) i = ψb (pr y) i
    rw [(Ab.chart kb).left_inv (hpr y hy.1).1]

end GlobalTheory.CompanionTheory.Ar.PB.ChartSwap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SquareParametrizedDensityFormulaStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_parametrized_density_formula : ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ (n k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Q.U n → paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z = maDens (fun (r : Fin (d + 1)) (z' : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (Q.G n (Fin.tail z')) (z' 0) else ∑ a, c a * Q.α n a (Fin.tail z')) z) ∧ ∀ i < k, ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Q.U n → paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z = maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; fun (r : Fin (d + 2)) (z' : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 0) + u r 1 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 1) else ∑ a, c a * Q.α n a (Fin.tail (Fin.tail z'))) z := by
  first | exact @GlobalTheory.CompanionTheory.Relay.square_parametrized_density_formula | exact GlobalTheory.CompanionTheory.Relay.square_parametrized_density_formula | (intros; apply GlobalTheory.CompanionTheory.Relay.square_parametrized_density_formula <;> assumption)
end

