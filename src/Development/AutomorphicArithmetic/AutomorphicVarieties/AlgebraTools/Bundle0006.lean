module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotExtend
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.cotInd_extend :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (κ : Type) [Fintype κ] (x : κ → R), CotInd R x →
      ∃ (s : ℕ) (y : Fin s → R), CotInd R (Sum.elim x y) ∧
        Ideal.span (Set.range (Sum.elim x y)) = maximalIdeal R ∧
        Fintype.card κ + s = (maximalIdeal R).spanFinrank := by
  intro R _ _ _ κ _ x hx
  obtain ⟨hm, hli⟩ := (cotInd_iff R x).mp hx
  set v : κ → CotangentSpace R := fun k => (maximalIdeal R).toCotangent ⟨x k, hm k⟩ with hv
  let bW := Module.Basis.span hli
  let bQ := Module.finBasis (ResidueField R) (CotangentSpace R ⧸ Submodule.span (ResidueField R) (Set.range v))
  let B := Module.Basis.sumQuot bW bQ
  choose z hz using fun i => (maximalIdeal R).toCotangent_surjective (B (Sum.inr i))
  refine ⟨_, fun i => (z i : R), ?_⟩
  have hmem : ∀ j, Sum.elim x (fun i => (z i : R)) j ∈ maximalIdeal R := by
    rintro (k | i)
    · exact hm k
    · exact (z i).2
  have hB : (fun j => (maximalIdeal R).toCotangent ⟨Sum.elim x (fun i => (z i : R)) j, hmem j⟩) = ⇑B := by
    funext j
    rcases j with k | i
    · simp [B, bW, Module.Basis.span_apply, hv]
    · simpa using hz i
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  refine ⟨(cotInd_iff R _).mpr ⟨hmem, ?_⟩, ?_, ?_⟩
  · rw [hB]
    exact B.linearIndependent
  · let g : κ ⊕ Fin _ → maximalIdeal R := fun j => ⟨Sum.elim x (fun i => (z i : R)) j, hmem j⟩
    have hspan : Submodule.span R (Set.range g) = ⊤ := by
      rw [← CotangentSpace.span_image_eq_top_iff, ← Set.range_comp]
      have : (maximalIdeal R).toCotangent ∘ g = ⇑B := hB
      rw [this, B.span_eq]
    have := congrArg (Submodule.map (maximalIdeal R).subtype) hspan
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    exact this
  · rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg hfg, Module.finrank_eq_card_basis B,
      Fintype.card_sum, Fintype.card_fin]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotOfSpan
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.cotInd_of_span :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (κ : Type) [Fintype κ] (x : κ → R),
      Ideal.span (Set.range x) = maximalIdeal R → Fintype.card κ ≤ (maximalIdeal R).spanFinrank → CotInd R x := by
  intro R _ _ _ κ _ x hx hcard
  have hm : ∀ k, x k ∈ maximalIdeal R := fun k => hx ▸ Ideal.subset_span ⟨k, rfl⟩
  refine (cotInd_iff R x).mpr ⟨hm, ?_⟩
  let g : κ → maximalIdeal R := fun k => ⟨x k, hm k⟩
  have hg : Submodule.span R (Set.range g) = ⊤ := by
    apply Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact hx
  have hV : Submodule.span (ResidueField R) (Set.range ((maximalIdeal R).toCotangent ∘ g)) = ⊤ := by
    rw [Set.range_comp, CotangentSpace.span_image_eq_top_iff]
    exact hg
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  have hle := finrank_range_le_card (R := ResidueField R) ((maximalIdeal R).toCotangent ∘ g)
  rw [Set.finrank, hV, finrank_top] at hle
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg hfg] at hcard
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hV.ge (le_antisymm hcard hle)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplMap
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.map_pow_eq :
    ∀ (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R p B → ∀ n : ℕ, (p ^ n).map (algebraMap R B) = maximalIdeal B ^ n := by
  intro R _ p B _ _ _ h n
  have hnoeth := h.noeth
  have hle : p.map (algebraMap R B) ≤ maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, h.comap_eq]
  have heq : p.map (algebraMap R B) = maximalIdeal B := by
    refine le_antisymm hle ?_
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top).ge
    intro b hb
    obtain ⟨a, s, hs, hsa⟩ := h.dense 2 b
    have hsu : IsUnit (algebraMap R B s) := by
      by_contra hn
      apply hs
      rw [← h.comap_eq, Ideal.mem_comap]
      exact (IsLocalRing.mem_maximalIdeal _).mpr hn
    have hm2 : maximalIdeal B ^ 2 ≤ maximalIdeal B := Ideal.pow_le_self two_ne_zero
    have ha : a ∈ p := by
      rw [← h.comap_eq, Ideal.mem_comap]
      have : algebraMap R B a = algebraMap R B s * b - (algebraMap R B s * b - algebraMap R B a) := by ring
      rw [this]
      exact sub_mem (Ideal.mul_mem_left _ _ hb) (hm2 hsa)
    obtain ⟨u, hu⟩ := hsu
    have hb' : b = (↑u⁻¹ : B) * (algebraMap R B a + (algebraMap R B s * b - algebraMap R B a)) := by
      rw [← hu]
      simp
    rw [hb', smul_eq_mul, ← pow_two]
    apply Ideal.mul_mem_left
    exact add_mem (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)) (Ideal.mem_sup_right hsa)
  rw [Ideal.map_pow, heq]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetAdj
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.det_mem_of_rel :
    ∀ (P : Type) [CommRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P)
      (Q : Ideal P), Q.IsPrime → relIdeal z m ≤ Q → (∃ j, m j ∉ Q) → detIdeal z m ≤ Q := by
  intro P _ ι _ _ z m Q hQ hrel ⟨j, hj⟩
  have hzm : ∀ k, z.mulVec m k ∈ Q := fun k => hrel (Ideal.subset_span ⟨k, rfl⟩)
  have hdet : z.det * m j ∈ Q := by
    have h1 : (z.adjugate.mulVec (z.mulVec m)) j = z.det * m j := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp
    rw [← h1, Matrix.mulVec, dotProduct]
    exact Q.sum_mem fun k _ => Q.mul_mem_left _ (hzm k)
  have hd : z.det ∈ Q := (hQ.mem_or_mem hdet).resolve_right hj
  exact sup_le hrel ((Ideal.span_singleton_le_iff_mem _).mpr hd)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetChartCot
section
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.chartGen_cotInd :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι B) (m l : ι → B) (c : ι),
      CotInd B (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) → l c = 1 →
      CotInd B (Sum.elim (z.mulVec l) (fun j : {j : ι // j ≠ c} => m j.1 - l j.1 * m c)) := by
  intro B _ _ ι _ _ z m l c hx hl
  have hmem := hx.mem
  refine ⟨?_, ?_⟩
  · intro k
    rcases k with i | j
    · simp only [Sum.elim_inl, Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hmem (Sum.inl (i, j)))
    · simp only [Sum.elim_inr]
      exact Ideal.sub_mem _ (hmem (Sum.inr j.1)) (Ideal.mul_mem_left _ _ (hmem (Sum.inr c)))
  · intro a ha
    let b : ι × ι ⊕ ι → B := Sum.elim (fun ij => a (Sum.inl ij.1) * l ij.2)
      (fun j => if h : j = c then -(∑ k : {k // k ≠ c}, a (Sum.inr k) * l k.1)
        else a (Sum.inr ⟨j, h⟩))
    have key : ∑ k, b k * Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m k
        = ∑ k, a k * Sum.elim (z.mulVec l) (fun j : {j : ι // j ≠ c} => m j.1 - l j.1 * m c) k := by
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.sum_eq_add_sum_subtype_ne (fun j => b (Sum.inr j) * m j) c]
      simp only [b, Sum.elim_inl, Sum.elim_inr, Matrix.mulVec, dotProduct, dite_true]
      have e : ∀ j : {j // j ≠ c}, (if h : (j : ι) = c then
          -(∑ k : {k // k ≠ c}, a (Sum.inr k) * l k.1) else a (Sum.inr ⟨j, h⟩)) * m j
          = a (Sum.inr j) * m j := fun j => by rw [dite_eq_right j.2]
      rw [Finset.sum_congr rfl (fun j _ => e j)]
      have e2 : ∀ i, ∑ j, a (Sum.inl i) * l j * z i j = a (Sum.inl i) * ∑ j, z i j * l j := by
        intro i
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [Finset.sum_congr rfl (fun i _ => e2 i)]
      have e3 : ∑ j : {j // j ≠ c}, a (Sum.inr j) * (m j - l j * m c)
          = ∑ j : {j // j ≠ c}, a (Sum.inr j) * m j - (∑ k : {k // k ≠ c}, a (Sum.inr k) * l k) * m c := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [e3]
      ring
    have hb : ∀ k, b k ∈ maximalIdeal B := hx.indep b (by rw [key]; exact ha)
    intro k
    rcases k with i | j
    · have := hb (Sum.inl (i, c))
      simpa [b, hl] using this
    · have := hb (Sum.inr j.1)
      simpa [b, j.2] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CocycleTraceZero
section
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.cocycle_trace_zero :
    ∀ {K G : Type} [CommRing K] [Group G] {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ → Type) [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)] (r : G →* (∀ s, Matrix (d s) (d s) K)) (φ : G → ∀ s, Matrix (d s) (d s) K), Submodule.span K (Set.range r) = ⊤ → (∀ g h, φ (g * h) = φ g + r g * φ h * r g⁻¹) → (∀ g, ∑ s, ((φ g * r g) s).trace = 0) → ∃ Y, ∀ g, φ g = Y - r g * Y * r g⁻¹ := by
  intro K G _ _ σ _ _ d _ _ _ r φ hspan hφ htr
  classical
  let m : G → ∀ s, Matrix (d s) (d s) K := fun g => φ g * r g
  have hinv : ∀ g, r g⁻¹ * r g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  have hinv' : ∀ g, r g * r g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hm : ∀ g h, m (g * h) = m g * r h + r g * m h := by
    intro g h
    simp only [m, hφ, map_mul, add_mul, mul_assoc]
    rw [← mul_assoc (r g⁻¹), hinv, one_mul]
  let T : (∀ s, Matrix (d s) (d s) K) →ₗ[K] K :=
    ∑ s, (Matrix.traceLinearMap (d s) K K) ∘ₗ LinearMap.proj s
  have hT : ∀ x, T x = ∑ s, (x s).trace := by
    intro x
    simp [T, LinearMap.sum_apply]
  have hnd : ∀ x, (∀ y, T (x * y) = 0) → x = 0 := by
    intro x hx
    funext s
    rw [Matrix.ext_iff_trace_mul_right]
    intro y
    have := hx (Pi.single s y)
    rw [hT, Finset.sum_eq_single s] at this
    · simpa using this
    · intro t _ ht
      simp [Pi.single_eq_of_ne ht]
    · simp
  have hkey : ∀ g h, T (m g * r h) = - T (r g * m h) := by
    intro g h
    have : T (m (g * h)) = 0 := by rw [hT]; exact htr _
    rw [hm, map_add (f := _)] at this
    exact eq_neg_of_add_eq_zero_left this
  let R := Finsupp.linearCombination K (fun g => r g)
  let M := Finsupp.linearCombination K m
  have hR : Function.Surjective R := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hspan
  have hkey2 : ∀ f h, T (M f * r h) = - T (R f * m h) := by
    intro f h
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ h₁ h₂ => simp only [map_add (f := _), add_mul, h₁, h₂]; ring
    | single g a =>
      simp only [R, M, Finsupp.linearCombination_single, smul_mul_assoc, map_smul, hkey, smul_neg]
  have hle : LinearMap.ker R ≤ LinearMap.ker M := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    apply hnd
    intro y
    have hy : y ∈ Submodule.span K (Set.range r) := hspan ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [hkey2, hf]; simp
    | zero => simp
    | add x y _ _ h₁ h₂ => rw [mul_add, map_add (f := _), h₁, h₂, add_zero]
    | smul a x _ h₁ => rw [mul_smul_comm, map_smul, h₁, smul_zero]
  let D : (∀ s, Matrix (d s) (d s) K) →ₗ[K] (∀ s, Matrix (d s) (d s) K) :=
    (LinearMap.ker R).liftQ M hle ∘ₗ (R.quotKerEquivOfSurjective hR).symm.toLinearMap
  have hDR : ∀ f, D (R f) = M f := by
    intro f
    have : (R.quotKerEquivOfSurjective hR).symm (R f) = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp [D, this]
  have hDr : ∀ g, D (r g) = m g := by
    intro g
    simpa [R, M] using hDR (Finsupp.single g 1)
  have hder : ∀ x y, D (x * y) = D x * y + x * D y := by
    intro x y
    have hx : x ∈ Submodule.span K (Set.range r) := hspan ▸ Submodule.mem_top
    have hy : y ∈ Submodule.span K (Set.range r) := hspan ▸ Submodule.mem_top
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨h, rfl⟩ := hy
      rw [← map_mul, hDr, hDr, hDr, hm]
    | zero_left => simp
    | zero_right => simp
    | add_left x y z _ _ _ h₁ h₂ => simp only [add_mul, map_add (f := _), h₁, h₂]; abel
    | add_right x y z _ _ _ h₁ h₂ => simp only [mul_add, map_add (f := _), h₁, h₂]; abel
    | smul_left a x y _ _ h₁ => simp only [smul_mul_assoc, map_smul, h₁, smul_add]
    | smul_right a x y _ _ h₁ => simp only [mul_smul_comm, map_smul, h₁, smul_add]
  obtain ⟨Y, hY⟩ := UpperTheory.V.AlgebraTools.der_inner d (AlgHom.id K _) D hder
  refine ⟨Y, fun g => ?_⟩
  have h1 : φ g = m g * r g⁻¹ := by simp only [m, mul_assoc, hinv', mul_one]
  rw [h1, ← hDr, hY]
  simp only [AlgHom.id_apply, sub_mul]
  rw [mul_assoc Y, hinv', mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeEqDet
section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem de_eq_det (R : Type) [CommRing R] (n : ℕ) :
    De R n = (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)).det := by
  rw [Matrix.det_vandermonde, De, pairs, Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext j
  simp

private theorem nn_ne (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) : NN n q ≠ 0 := by
  rw [NN, Finset.prod_ne_zero_iff]
  intro p hp
  have hlt : p.1 < p.2 := by simpa [pairs] using hp
  intro h
  have hc := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single p.2 1)) h
  rw [coeff_sub, coeff_C_mul, coeff_X, coeff_X] at hc
  simp [Finsupp.single_left_inj one_ne_zero, hlt.ne] at hc

theorem UpperTheory.V.AlgebraTools.hkDe :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ), De R n ≠ 0 ∧ (∀ w : Perm (Fin n), rename w (De R n) = Perm.sign w • De R n) ∧ ∀ q : R, NN n q ≠ 0 := by
  intro R _ _ n
  refine ⟨?_, ?_, nn_ne R n⟩
  · rw [de_eq_det, Matrix.det_vandermonde_ne_zero_iff]
    exact X_injective
  · intro w
    rw [de_eq_det, AlgHom.map_det]
    have hm : (rename w : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R).mapMatrix
        (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)) =
        (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)).submatrix w id := by
      ext i j
      simp [Matrix.vandermonde_apply]
    rw [hm, Matrix.det_permute, Units.smul_def, zsmul_eq_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DualLattice
section
open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.dual_lattice_denom {A : Type} [CommRing A] [IsDomain A]
    {F V : Type} [Field F] [Algebra A F] [IsFractionRing A F] [AddCommGroup V] [Module F V]
    [Module A V] [IsScalarTower A F V] (Y : Submodule A V) (hY : Submodule.IsFullLattice F Y)
    (z : V) : ∃ a : A, a ≠ 0 ∧ a • z ∈ Y :=
  _root_.UpperTheory.Reformulated.B.ExistsSmulMemOfIsLattice₂.dual_lattice_denom Y hY z

private theorem UpperTheory.V.AlgebraTools.dual_lattice_pow {A : Type} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (a : A) (ha : a ≠ 0) :
    ∃ s : ℕ, maximalIdeal A ^ s ≤ Ideal.span {a} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  refine ⟨n, ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
  exact (Units.isUnit u).mul_left_dvd.mpr dvd_rfl

theorem UpperTheory.V.AlgebraTools.dual_lattice :
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {F V : Type} [Field F] [Algebra A F] [IsFractionRing A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V] [Module.Finite F V] (Bf : LinearMap.BilinForm F V), Bf.IsSymm → Bf.Nondegenerate → ∀ Y : Submodule A V, Submodule.IsFullLattice F Y → Submodule.IsFullLattice F (Bf.dualSubmodule Y) ∧ Bf.dualSubmodule (Bf.dualSubmodule Y) = Y ∧ ∀ Z : Submodule A V, Submodule.IsLattice F Z → ∃ s : ℕ, maximalIdeal A ^ s • Z ≤ Y := by
  intro A _ _ _ F V _ _ _ _ _ _ _ _ Bf hs hn Y hY
  classical
  haveI : Module.Free A Y := Submodule.IsLattice.free F Y
  haveI : Module.Finite A Y := Submodule.IsLattice.finite F Y
  let b0 := Module.Free.chooseBasis A Y
  let b := b0.extendOfIsFullLattice F
  have hb : Submodule.span A (Set.range b) = Y := by
    have : (b : _ → V) = Y.subtype ∘ b0 := by
      funext i; simp [b]
    rw [this, Set.range_comp, ← Submodule.map_span, b0.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hb, LinearMap.BilinForm.dualSubmodule_span_of_basis Bf hn b]
    exact { toIsLattice := Submodule.IsLattice.of_fg _ (Submodule.fg_span (Set.finite_range _))
            span_eq_top := by rw [Submodule.span_span_of_tower, Module.Basis.span_eq] }
  · rw [← hb]
    exact LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis Bf hn hs b
  · intro Z hZ
    have hfg := hZ.fg
    clear hZ
    induction Z, hfg using Submodule.fg_induction with
    | singleton x =>
      obtain ⟨a, ha, hax⟩ := UpperTheory.V.AlgebraTools.dual_lattice_denom Y hY x
      obtain ⟨s, hs⟩ := UpperTheory.V.AlgebraTools.dual_lattice_pow a ha
      refine ⟨s, (Submodule.smul_mono_left hs).trans ?_⟩
      refine Submodule.smul_le.mpr fun r hr y hy => ?_
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [mul_smul, smul_comm a c]
      exact Y.smul_mem _ (Y.smul_mem _ hax)
    | sup M N _ _ hM hN =>
      obtain ⟨s, hs⟩ := hM
      obtain ⟨t, ht⟩ := hN
      refine ⟨s + t, ?_⟩
      rw [Submodule.smul_sup]
      refine sup_le ?_ ?_
      · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right s t))).trans hs
      · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_left t s))).trans ht
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.FreeProf
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

open ProfiniteGrp ProfiniteGrp.ProfiniteCompletion CategoryTheory in
theorem UpperTheory.V.AlgebraTools.exists_free_profinite :
    ∀ r : ℕ, ∃ (P : Type) (_ : Group P) (_ : TopologicalSpace P) (_ : IsTopologicalGroup P) (_ : CompactSpace P)
      (_ : TotallyDisconnectedSpace P) (x : Fin r → P), TopGen (Set.range x) ∧
        ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (y : Fin r → G), ∃ f : P →* G, Continuous f ∧ ∀ i, f (x i) = y i := by
  intro r
  let F : GrpCat.{0} := GrpCat.of (FreeGroup (Fin r))
  let P : ProfiniteGrp.{0} := completion F
  let η : FreeGroup (Fin r) →* P := (eta F).hom
  refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun i => η (FreeGroup.of i), ?_, ?_⟩
  · unfold TopGen
    have hr : Set.range (fun i => η (FreeGroup.of i)) = η '' Set.range FreeGroup.of := by
      rw [← Set.range_comp]
      rfl
    rw [hr, ← MonoidHom.map_closure, FreeGroup.closure_range_of, ← MonoidHom.range_eq_map,
      MonoidHom.coe_range]
    exact denseRange (G := F)
  · intro G _ _ _ _ _ y
    let Q : ProfiniteGrp.{0} := ProfiniteGrp.of G
    let f0 : F ⟶ GrpCat.of Q := GrpCat.ofHom (FreeGroup.lift y)
    let L : P ⟶ Q := lift f0
    refine ⟨L.hom.toMonoidHom, L.hom.continuous, ?_⟩
    intro i
    have h : ((eta F) ≫ (forget₂ ProfiniteGrp GrpCat).map L).hom (FreeGroup.of i) =
        f0.hom (FreeGroup.of i) := by
      rw [lift_eta]
    exact h.trans FreeGroup.lift_apply_of
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDedekind
section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

theorem UpperTheory.V.AlgebraTools.hkDedekind :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (K : Type) [Field K] [Algebra (MvPolynomial (Fin n) R) K] [IsFractionRing (MvPolynomial (Fin n) R) K] (f : Perm (Fin n) → K),
      (∀ x : MvPolynomial (Fin n) R, ∑ u, f u * algebraMap _ K (rename u x) = 0) → f = 0 := by
  intro R _ _ n K _ _ _ f hf
  classical
  let φ : Perm (Fin n) → (MvPolynomial (Fin n) R →* K) := fun u =>
    (algebraMap (MvPolynomial (Fin n) R) K).toMonoidHom.comp (rename u : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R).toRingHom.toMonoidHom
  have hinj : Function.Injective φ := by
    intro u v huv
    ext i
    have h := DFunLike.congr_fun huv (X i)
    simp only [φ, MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_toRingHom, rename_X] at h
    have h2 := IsFractionRing.injective (MvPolynomial (Fin n) R) K h
    exact congrArg Fin.val (X_injective h2)
  have hli := (linearIndependent_monoidHom (MvPolynomial (Fin n) R) K).comp φ hinj
  rw [Fintype.linearIndependent_iff] at hli
  funext u
  apply hli f
  funext x
  simpa [φ, Finset.sum_apply] using hf x
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagMap
section
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.lag_map :
    ∀ {R R' E E' ι : Type} [CommRing R] [CommRing R'] [Ring E] [Ring E'] [Algebra R E] [Algebra R' E'] [Fintype ι] [DecidableEq ι] (φ : R →+* R') (π : E →+* E') (a : ι → R) (P : E), (∀ c, π (algebraMap R E c) = algebraMap R' E' (φ c)) → (∀ i j, i ≠ j → IsUnit (a i - a j)) → ∀ i, π (lag a P i) = lag (fun j => φ (a j)) (π P) i := by
  intro R R' E E' ι _ _ _ _ _ _ _ _ φ π a P hc ha i
  have key : ∀ q : R[X], π (aeval P q) = aeval (π P) (q.map φ) := by
    intro q
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map]
    congr 1
    exact RingHom.ext hc
  have hsm : ∀ (c : R) (x : E), π (c • x) = φ c • π x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hc]
  have h0 := (eq_lag_iff a P i (fun j hj => ha i j (Ne.symm hj)) (lag a P i)).1 rfl
  have h1 := congrArg π h0
  rw [hsm, key] at h1
  simp only [map_prod, Polynomial.map_prod, map_sub, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C] at h1
  rw [eq_lag_iff (fun j => φ (a j)) (π P) i (fun j hj => by
      rw [← map_sub]; exact (ha i j (Ne.symm hj)).map φ) (π (lag a P i))]
  exact h1
end

