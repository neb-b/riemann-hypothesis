module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0257
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKOOfDet
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj

namespace GlobalTheory.FunObj.DiagLattice

theorem exists_KO_of_det {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι k)
    (h1 : ∀ i j, M i j ∈ 𝒪[k]) (h2 : valuation k M.det = 1) : ∃ g ∈ KO k ι, g.val = M := by
  let A : Matrix ι ι 𝒪[k] := fun i j => ⟨M i j, h1 i j⟩
  have hA : (algebraMap 𝒪[k] k).mapMatrix A = M := rfl
  have hd : algebraMap 𝒪[k] k A.det = M.det := by rw [RingHom.map_det, hA]
  have hu : IsUnit A.det :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers (valuation k))).2 (by rw [hd, h2])
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hu
  refine ⟨Matrix.GeneralLinearGroup.map (n := ι) (algebraMap 𝒪[k] k) u, ⟨u, rfl⟩, ?_⟩
  change u.val.map (algebraMap 𝒪[k] k) = _
  rw [hu]; rfl

theorem exists_unip {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (p : ℕ)
    (v : Fin c → n ⊕ Fin c → k) (h1 : ∀ i, v i (Sum.inr i) = 1) (h2 : ∀ i l, i < l → v i (Sum.inr l) = 0)
    (h3 : ∀ i : Fin c, i.val < p → ∀ r, v i (Sum.inl r) = 0) :
    ∃ u ∈ N k n c p, (∀ r i, u.val r (Sum.inr i) = v i r) ∧
      ∀ r s, u.val r (Sum.inl s) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (Sum.inl s) := by
  refine ⟨(Model.mkNel p fun rs => Sum.elim (fun _ => (0 : k)) (fun i => v i rs.1.1) rs.1.2).1,
    Subtype.property _, ?_, ?_⟩
  · intro r i
    show Model.mkN p (fun rs => Sum.elim (fun _ => (0 : k)) (fun i => v i rs.1.1) rs.1.2) r (Sum.inr i) = _
    simp only [Model.mkN, of_apply, Sum.elim_inr]
    split_ifs with h
    · rfl
    · rcases r with r | r
      · rw [h3 i (by simp [lev] at h; omega)]; simp
      · simp only [lev, Sum.elim_inr] at h
        rcases eq_or_lt_of_le (show i ≤ r by rw [Fin.le_def]; omega) with e | e
        · subst e; simp [h1]
        · rw [h2 i r e, Matrix.one_apply_ne]
          simpa using e.ne'
  · intro r s
    show Model.mkN p (fun rs => Sum.elim (fun _ => (0 : k)) (fun i => v i rs.1.1) rs.1.2) r (Sum.inl s) = _
    simp only [Model.mkN, of_apply, Sum.elim_inl]
    split_ifs with h
    · rw [Matrix.one_apply_ne]
      rintro rfl; exact lt_irrefl _ h
    · rfl

theorem exists_symR_diag : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (d : Fin c → kˣ) (H : GL (n ⊕ Fin c) k),
  (∀ i : Fin c, ∃ v : n ⊕ Fin c → k, v (Sum.inr i) = 1 ∧ (∀ l : Fin c, i < l → v (Sum.inr l) = 0) ∧ (i.val < (c + 1) / 2 → ∀ r, v (Sum.inl r) = 0) ∧ ∀ t, ((H⁻¹).val *ᵥ ((d i : k) • v)) t ∈ 𝒪[k]) →
  (∀ (i : Fin c) (y : n ⊕ Fin c → k), (∀ t, y t ∈ 𝒪[k]) → (∀ l : Fin c, i < l → (H.val *ᵥ y) (Sum.inr l) = 0) → (i.val < c / 2 → ∀ r, (H.val *ᵥ y) (Sum.inl r) = 0) → valuation k ((H.val *ᵥ y) (Sum.inr i)) ≤ valuation k (d i : k)) →
  ∃ r ∈ symR k n c, ∃ w ∈ KO k (n ⊕ Fin c), H = r * diagGL (Sum.elim (fun _ => 1) d) * w := by
  intro k _ _ _ _ n _ _ c d H hA hB
  choose v v1 v2 v3 v4 using hA
  obtain ⟨u, hu, uc, uX⟩ := exists_unip ((c + 1) / 2) v v1 v2 v3
  let lv : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * (c / 2)) (fun i => 2 * i.val + 1)
  obtain ⟨b, hb, w, hw, hbw⟩ := iwasawa_blockTriangular k (n ⊕ Fin c) lv (u⁻¹ * H)
  have hbi : (b⁻¹).val.BlockTriangular lv := by
    rw [Matrix.coe_units_inv]
    haveI := b.invertible
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  have hH : H = u * b * w := by rw [mul_assoc, ← hbw]; simp
  obtain ⟨w1, w2⟩ := (mem_KO_iff w).1 hw
  have hdiag : ∀ i, (b⁻¹).val (Sum.inr i) (Sum.inr i) * b.val (Sum.inr i) (Sum.inr i) = 1 := by
    intro i
    have h := congrFun (congrFun b.inv_mul (Sum.inr i)) (Sum.inr i)
    rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i)] at h
    · simpa using h
    · intro t _ ht
      rcases lt_trichotomy (lv t) (lv (Sum.inr i)) with e | e | e
      · rw [hbi e, zero_mul]
      · exfalso
        rcases t with t | t
        · simp only [lv, Sum.elim_inl, Sum.elim_inr] at e; omega
        · simp only [lv, Sum.elim_inr] at e; exact ht (congrArg _ (Fin.ext (by omega)))
      · rw [hb e, mul_zero]
    · simp
  have hbl : ∀ i l : Fin c, i < l → b.val (Sum.inr l) (Sum.inr i) = 0 := fun i l h =>
    hb (by simp only [lv, Sum.elim_inr]; rw [Fin.lt_def] at h; omega)
  have h3 : ∀ i, valuation k (b.val (Sum.inr i) (Sum.inr i)) ≤ valuation k (d i : k) := by
    intro i
    have key : ∀ t, (H.val *ᵥ fun s => (w⁻¹).val s (Sum.inr i)) t =
        ∑ s, u.val t (Sum.inl s) * b.val (Sum.inl s) (Sum.inr i) + ∑ l, v l t * b.val (Sum.inr l) (Sum.inr i) := by
      intro t
      have : (H * w⁻¹).val t (Sum.inr i) = (u * b).val t (Sum.inr i) := by rw [hH]; simp
      rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type
        (fun j => u.val t j * b.val j (Sum.inr i))] at this
      simp only [uc] at this
      exact this
    have h := hB i (fun s => (w⁻¹).val s (Sum.inr i)) (fun t => w2 _ _) ?_ ?_
    · rw [key, Finset.sum_eq_single i] at h
      · simpa [uX, v1] using h
      · intro l _ hl
        rcases lt_or_gt_of_ne hl with e | e
        · rw [v2 l i e, zero_mul]
        · rw [hbl i l e, mul_zero]
      · simp
    · intro l hl
      rw [key, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
      · intro m _
        rcases lt_or_ge m l with e | e
        · rw [v2 m l e, zero_mul]
        · rw [hbl i m (hl.trans_le e), mul_zero]
      · intro s _; simp [uX]
    · intro hi r
      rw [key, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
      · intro m _
        rcases lt_or_ge i m with e | e
        · rw [hbl i m e, mul_zero]
        · rw [v3 m (by rw [Fin.le_def] at e; omega), zero_mul]
      · intro s _
        rw [hb (show lv (Sum.inr i) < lv (Sum.inl s) by simp only [lv, Sum.elim_inr, Sum.elim_inl]; omega), mul_zero]
  have h4 : ∀ t i, (b⁻¹).val t (Sum.inr i) * (d i : k) ∈ 𝒪[k] := by
    intro t i
    have e : b⁻¹ = w * H⁻¹ * u := by rw [hH]; group
    have : (b⁻¹).val t (Sum.inr i) * (d i : k) = (w.val *ᵥ ((H⁻¹).val *ᵥ ((d i : k) • v i))) t := by
      rw [Matrix.mulVec_mulVec, e, Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_mul]
      simp only [Matrix.mulVec, dotProduct, uc, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    exact sum_mem fun j _ => mul_mem (w1 _ _) (v4 i j)
  let A : Matrix (Fin c) (Fin c) k := Matrix.of fun l i => (b⁻¹).val (Sum.inr l) (Sum.inr i) * d i
  let β : Matrix n (Fin c) k := Matrix.of fun r i => (b⁻¹).val (Sum.inl r) (Sum.inr i) * d i
  have hAtri : A.BlockTriangular id := fun l i h => by
    simp only [A, of_apply]
    rw [hbi (by simp only [lv, Sum.elim_inr]; rw [id, id, Fin.lt_def] at h; omega), zero_mul]
  obtain ⟨κ, hκ, hκv⟩ := exists_KO_of_det (fromBlocks 1 β 0 A) (by
    rintro (r | r) (s | s)
    · simp only [fromBlocks_apply₁₁, Matrix.one_apply]; split_ifs <;> simp
    · exact h4 _ _
    · exact zero_mem _
    · exact h4 _ _) (by
    rw [det_fromBlocks_zero₂₁, det_one, one_mul, det_of_upperTriangular hAtri, map_prod]
    refine Finset.prod_eq_one fun i _ => le_antisymm (h4 (Sum.inr i) i) ?_
    simp only [A, of_apply, map_mul]
    calc (1 : ValueGroupWithZero k) = valuation k ((b⁻¹).val (Sum.inr i) (Sum.inr i)) *
          valuation k (b.val (Sum.inr i) (Sum.inr i)) := by rw [← map_mul, hdiag, map_one]
      _ ≤ _ := mul_le_mul_right (h3 i) _)
  have hB : (b * κ).val = fromBlocks b.val.toBlocks₁₁ 0 b.val.toBlocks₂₁ (diagonal fun i => (d i : k)) := by
    have col : ∀ t i, (b * κ).val t (Sum.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) t (Sum.inr i) * d i := by
      intro t i
      rw [← b.mul_inv, Units.val_mul, hκv, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      rintro (j | j) _ <;> simp [A, β, mul_assoc]
    ext (r | r) (s | s)
    · simp [hκv, Matrix.mul_apply, Matrix.one_apply, toBlocks₁₁]
    · rw [col]; simp
    · simp [hκv, Matrix.mul_apply, Matrix.one_apply, toBlocks₂₁]
    · rw [col]
      by_cases h : r = s
      · subst h; simp
      · simp [h]
  have hg : b.val.toBlocks₁₁.det ≠ 0 := by
    have := Matrix.GeneralLinearGroup.det_ne_zero (b * κ)
    rw [hB, det_fromBlocks_zero₁₂] at this
    exact left_ne_zero_of_mul this
  let g : GL n k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hg
  have hlow : lowU b.val.toBlocks₂₁ ∈ N k n c (c / 2 + 1) := by
    rw [Model.mem_N_iff]
    rintro (r | r) (s | s) h
    · simp [lowU, Matrix.one_apply]
    · simp [lowU]
    · simp only [lev, Sum.elim_inl, Sum.elim_inr] at h
      simp only [lowU, fromBlocks_apply₂₁, toBlocks₂₁, of_apply]
      rw [hb (show lv (Sum.inl s) < lv (Sum.inr r) by simp only [lv, Sum.elim_inr, Sum.elim_inl]; omega)]
      simp
    · simp [lowU, Matrix.one_apply]
  have hfac : b * κ = embX c g * lowU b.val.toBlocks₂₁ * diagGL (Sum.elim (fun _ => 1) d) := by
    refine Units.ext ?_
    have hD : (diagGL (Sum.elim (fun _ : n => (1 : kˣ)) d)).val = fromBlocks 1 0 0 (diagonal fun i => (d i : k)) := by
      rw [diagGL_val, ← diagonal_one, fromBlocks_diagonal]
      congr 1
      funext x; rcases x with x | x <;> simp
    rw [hB, Units.val_mul, Units.val_mul, hD]
    show _ = fromBlocks b.val.toBlocks₁₁ 0 0 1 * fromBlocks 1 0 b.val.toBlocks₂₁ 1 * _
    simp [fromBlocks_multiply]
  refine ⟨u * (embX c g * lowU b.val.toBlocks₂₁), ?_, κ⁻¹ * w, mul_mem (inv_mem hκ) hw, ?_⟩
  · exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_sup_left hu))
      (mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right (Subgroup.mem_sup_right hlow)))
  · rw [mul_assoc u, ← hfac, hH]; group

end GlobalTheory.FunObj.DiagLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormMulOfHermitianModelUnitaryConj
section
open GlobalTheory.UnitLemma Polynomial Matrix

noncomputable section

namespace GlobalTheory.InertUnitOrb

theorem stdH_mulVec_eq_of_unitary {K : UQ} {n : ℕ} (u : Matrix (Fin n) (Fin n) K.E)
    (hu : (u.map K.c)ᵀ * u = 1) (a b : Fin n → K.E) :
    stdH K n (u *ᵥ a) (u *ᵥ b) = stdH K n a b := by
  have hu' : uᵀ * u.map K.c = 1 := by
    have := congrArg Matrix.transpose hu
    rwa [transpose_mul, transpose_transpose, transpose_one] at this
  have hS : ∀ y z : Fin n → K.E, stdH K n y z = y ⬝ᵥ (fun k => K.c (z k)) := fun _ _ => rfl
  have hc : (fun k => K.c ((u *ᵥ b) k)) = u.map K.c *ᵥ (fun k => K.c (b k)) := by
    funext k
    exact RingHom.map_mulVec (K.c : K.E →+* K.E) u b k
  rw [hS, hS, hc, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hu', vecMul_one]

theorem class_eq_of_conj :
    ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ γ' u : Matrix (Fin n) (Fin n) K.E)
      (x x' : B.Aˣ) (ψ ψ' : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ →
      GlobalTheory.InertUnitOrb.IsModel B γ' x' ψ' → (u.map K.c)ᵀ * u = 1 → γ * u = u * γ' → B.P.Separable →
      ∃ v : B.Aˣ, (x' : B.A) = x * (v * B.σ v) := by
  intro K B n γ γ' u x x' ψ ψ' ⟨_, hg, hh⟩ ⟨_, hg', hh'⟩ hu hγ hsep
  have hgen := GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable K B hsep
  let φ : B.A →ₗ[K.E] B.A := ψ.symm.toLinearMap ∘ₗ Matrix.toLin' u ∘ₗ ψ'.toLinearMap
  have hφ_apply : ∀ y, φ y = ψ.symm (u *ᵥ ψ' y) := fun y => by
    simp [φ, Matrix.toLin'_apply]
  have hψg : ∀ w, ψ.symm (γ *ᵥ w) = B.g * ψ.symm w := fun w => by
    apply ψ.injective
    rw [hg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hφg : ∀ y, φ (B.g * y) = B.g * φ y := fun y => by
    rw [hφ_apply, hφ_apply, hg', mulVec_mulVec, ← hγ, ← mulVec_mulVec, hψg]
  have hpow : ∀ (k : ℕ) y, φ (B.g ^ k * y) = B.g ^ k * φ y := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih => intro y; rw [pow_succ', mul_assoc, hφg, ih, ← mul_assoc]
  have hφp : ∀ (f : K.E[X]) y, φ (aeval B.g f * y) = aeval B.g f * φ y := by
    intro f
    induction f using Polynomial.induction_on' with
    | add p q hp hq => intro y; rw [map_add (f := _), add_mul, add_mul, map_add (f := _), hp, hq]
    | monomial k e =>
      intro y
      rw [aeval_monomial, mul_assoc, ← Algebra.smul_def, map_smul, hpow, Algebra.smul_def, mul_assoc]
  have hφ : ∀ y, φ y = y * φ 1 := fun y => by
    obtain ⟨f, rfl⟩ := hgen y
    simpa using hφp f 1

  have hu2 : u * (u.map K.c)ᵀ = 1 := mul_eq_one_comm.mp hu
  have hy0 : φ (ψ'.symm ((u.map K.c)ᵀ *ᵥ ψ 1)) = 1 := by
    rw [hφ_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec, hu2, one_mulVec,
      LinearEquiv.symm_apply_apply]
  have hunit : IsUnit (φ 1) := by
    have h1 : ψ'.symm ((u.map K.c)ᵀ *ᵥ ψ 1) * φ 1 = 1 := by rw [← hφ, hy0]
    exact ⟨⟨φ 1, ψ'.symm ((u.map K.c)ᵀ *ᵥ ψ 1), by rw [mul_comm]; exact h1, h1⟩, rfl⟩
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec]

  have hiso : ∀ y z, B.herm x' y z = B.herm x (y * φ 1) (z * φ 1) := fun y z => by
    rw [← hh', ← stdH_mulVec_eq_of_unitary u hu, ← hh, ← hφ, ← hφ, hφ_apply, hφ_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have key : ∀ y, Algebra.trace K.E B.A (((x' : B.A) - x * (φ 1 * B.σ (φ 1))) * y) = 0 := fun y => by
    have h1 := hiso y 1
    simp only [InvAlg.herm, map_one, mul_one, one_mul] at h1
    rw [sub_mul, map_sub, h1, sub_eq_zero]
    congr 1
    ring
  exact sub_eq_zero.mp (GlobalTheory.UnitLemma.TraceNondeg.eq_zero_of_trace_mul_eq_zero K B hsep hgen _ key)

end GlobalTheory.InertUnitOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupPeriodic
section
open Filter Topology

namespace GlobalTheory.WeilM

theorem SB.exists_periodic {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] {ι : Type}
    (L : ι → AddSubgroup X) (hL : ∀ i, IsOpen (L i : Set X)) (hb : ∀ W ∈ 𝓝 (0 : X), ∃ i, (L i : Set X) ⊆ W) :
    ∀ f ∈ GlobalTheory.WeilM.SB X, ∃ i, ∀ Y, ∀ C ∈ L i, f (Y + C) = f Y := by
  intro f hf
  obtain ⟨hlc, hcs⟩ := hf
  have key : ∀ Y : X, ∃ i, ∀ C ∈ L i, f (Y + C) = f Y := by
    intro Y
    have h1 : f ⁻¹' {f Y} ∈ 𝓝 (Y + 0) := by rw [add_zero]; exact (hlc.isOpen_fiber _).mem_nhds rfl
    have h2 : {C : X | f (Y + C) = f Y} ∈ 𝓝 (0 : X) := (continuous_const_add Y).continuousAt.preimage_mem_nhds h1
    obtain ⟨i, hi⟩ := hb _ h2
    exact ⟨i, fun C hC => hi hC⟩
  choose g hg using key
  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover (fun Y => {Z : X | Z - Y ∈ L (g Y)})
    (fun Y => (hL _).preimage (continuous_sub_right Y))
    (fun Z _ => Set.mem_iUnion.2 ⟨Z, by simp⟩)
  have hW : (⋂ Y ∈ t, (L (g Y) : Set X)) ∈ 𝓝 (0 : X) :=
    (Filter.biInter_finset_mem t).2 fun Y _ => (hL _).mem_nhds (L (g Y)).zero_mem
  obtain ⟨j, hj⟩ := hb _ hW
  refine ⟨j, fun Y C hC => ?_⟩
  have hCt : ∀ Y0 ∈ t, C ∈ L (g Y0) := fun Y0 h0 => by
    have := hj hC
    simp only [Set.mem_iInter] at this
    exact this Y0 h0
  by_cases h : ∃ Y0 ∈ t, Y - Y0 ∈ L (g Y0)
  · obtain ⟨Y0, h0, hY⟩ := h
    have e1 := hg Y0 _ hY
    have e2 := hg Y0 _ (add_mem hY (hCt Y0 h0))
    rw [show Y0 + (Y - Y0) = Y by abel] at e1
    rw [show Y0 + (Y - Y0 + C) = Y + C by abel] at e2
    rw [e1, e2]
  · push_neg at h
    have hn : ∀ Z, Z ∈ tsupport f → ∃ Y0 ∈ t, Z - Y0 ∈ L (g Y0) := fun Z hZ => by
      have := ht hZ
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
      obtain ⟨Y0, h0, h1⟩ := this
      exact ⟨Y0, h0, h1⟩
    have hY : Y ∉ tsupport f := fun hZ => by
      obtain ⟨Y0, h0, h1⟩ := hn Y hZ
      exact h Y0 h0 h1
    have hYC : Y + C ∉ tsupport f := fun hZ => by
      obtain ⟨Y0, h0, h1⟩ := hn _ hZ
      apply h Y0 h0
      have := sub_mem h1 (hCt Y0 h0)
      rwa [show Y + C - Y0 - C = Y - Y0 by abel] at this
    rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hYC]

end GlobalTheory.WeilM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreservesFilteredColimitsIsoOnFiniteType
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.FinExt

def finTypeZ : ObjectProperty CommRingCat.{0} := fun A => Algebra.FiniteType ℤ A

section
variable {H : Type*} [Category H] {G : finTypeZ.FullSubcategory ⥤ H}
  (E : finTypeZ.ι.LeftExtension G)

lemma comp_eq_of_fac {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}}
    {c : Cocone D} (hc : IsColimit c) (s : Cocone (D ⋙ E.right))
    (X : finTypeZ.FullSubcategory) {j j' : J} (ψ : finTypeZ.ι.obj X ⟶ D.obj j)
    (ψ' : finTypeZ.ι.obj X ⟶ D.obj j') (h : ψ ≫ c.ι.app j = ψ' ≫ c.ι.app j') :
    E.hom.app X ≫ E.right.map ψ ≫ s.ι.app j = E.hom.app X ≫ E.right.map ψ' ≫ s.ι.app j' := by
  obtain ⟨k, a, b, -⟩ := IsFilteredOrEmpty.cocone_objs j j'
  have hk : (ψ ≫ D.map a) ≫ c.ι.app k = (ψ' ≫ D.map b) ≫ c.ι.app k := by
    simpa only [Category.assoc, Cocone.w] using h
  obtain ⟨l, f, hf⟩ := (GlobalTheory.finiteType_int_hom_filteredColimit (finTypeZ.ι.obj X) X.property J D c hc).2 k _ _ hk
  have e1 : s.ι.app j = E.right.map (D.map (a ≫ f)) ≫ s.ι.app l := (s.w (a ≫ f)).symm
  have e2 : s.ι.app j' = E.right.map (D.map (b ≫ f)) ≫ s.ι.app l := (s.w (b ≫ f)).symm
  rw [e1, e2, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 3
  simpa only [Functor.map_comp, Category.assoc] using hf

end

section
variable {H : Type*} [Category H] {G : finTypeZ.FullSubcategory ⥤ H}
  {E : finTypeZ.ι.LeftExtension G}

theorem preservesFilteredColimits_of_isPointwiseLeftKanExtension
    (hE : E.IsPointwiseLeftKanExtension) : PreservesFilteredColimitsOfSize.{0, 0} E.right := by
  refine ⟨fun J _ _ => ⟨fun {D} => ⟨fun {c} hc => ⟨?_⟩⟩⟩⟩
  have hfac := fun (g : CostructuredArrow finTypeZ.ι c.pt) =>
    (GlobalTheory.finiteType_int_hom_filteredColimit (finTypeZ.ι.obj g.left) g.left.property J D c hc).1 g.hom
  choose j ψ hψ using hfac
  let t : ∀ s : Cocone (D ⋙ E.right), Cocone (CostructuredArrow.proj finTypeZ.ι c.pt ⋙ G) :=
    fun s =>
    { pt := s.pt
      ι := { app := fun g => E.hom.app g.left ≫ E.right.map (ψ g) ≫ s.ι.app (j g)
             naturality := by
               intro g g' f
               have hn := E.hom.naturality f.left
               dsimp at hn ⊢
               simp only [Category.comp_id]
               change G.map f.left ≫ _ = _
               erw [reassoc_of% hn, ← Functor.map_comp_assoc]
               exact comp_eq_of_fac E hc s g.left _ _
                 (by rw [Category.assoc, hψ g', hψ g]; exact CostructuredArrow.w f) } }
  have ht : ∀ (s : Cocone (D ⋙ E.right)) (X : finTypeZ.FullSubcategory) (φ : finTypeZ.ι.obj X ⟶ c.pt),
      E.hom.app X ≫ E.right.map φ ≫ (hE c.pt).desc (t s) =
        E.hom.app X ≫ E.right.map (ψ (CostructuredArrow.mk φ)) ≫ s.ι.app (j (CostructuredArrow.mk φ)) := by
    intro s X φ
    have := (hE c.pt).fac (t s) (CostructuredArrow.mk φ)
    exact (Category.assoc _ _ _).symm.trans this
  exact
  { desc := fun s => (hE c.pt).desc (t s)
    fac := fun s k => by
      apply (hE (D.obj k)).hom_ext'
      intro X φ
      have h1 := ht s X (φ ≫ c.ι.app k)
      simp only [Functor.mapCocone_ι_app]
      erw [← Functor.map_comp_assoc, h1]
      exact comp_eq_of_fac E hc s X _ _ (hψ _)
    uniq := fun s m hm => by
      apply (hE c.pt).hom_ext'
      intro X φ
      rw [ht s X φ]
      have h2 := hψ (CostructuredArrow.mk φ)
      dsimp at h2
      conv_lhs => rw [← h2, Functor.map_comp, Category.assoc]
      have h3 := hm (j (CostructuredArrow.mk φ))
      simp only [Functor.mapCocone_ι_app] at h3
      rw [h3] }

end

theorem exists_preservesFilteredColimits_isIso :
    ∀ (𝒜 : Type 2) [Category.{1} 𝒜] [HasColimitsOfSize.{1, 1} 𝒜] (M : CommRingCat.{0} ⥤ 𝒜),
      ∃ (N : CommRingCat.{0} ⥤ 𝒜) (ε : N ⟶ M), PreservesFilteredColimitsOfSize.{0, 0} N ∧
        (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) := by
  intro 𝒜 _ _ M
  haveI : HasColimitsOfSize.{0, 1} 𝒜 := hasColimitsOfSizeShrink.{0, 1, 1, 1} 𝒜
  haveI : finTypeZ.ι.HasPointwiseLeftKanExtension (finTypeZ.ι ⋙ M) := fun _ => inferInstance
  let E := Functor.LeftExtension.mk _ (finTypeZ.ι.pointwiseLeftKanExtensionUnit (finTypeZ.ι ⋙ M))
  have hE : E.IsPointwiseLeftKanExtension :=
    finTypeZ.ι.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension _
  let φ := hE.homFrom (Functor.LeftExtension.mk M (𝟙 _))
  refine ⟨E.right, φ.right, preservesFilteredColimits_of_isPointwiseLeftKanExtension hE,
    fun A hA => ?_⟩
  let X : finTypeZ.FullSubcategory := ⟨A, hA⟩
  have h1 : IsIso (E.hom.app X) := (hE (finTypeZ.ι.obj X)).isIso_hom_app
  have h2 : E.hom.app X ≫ φ.right.app (finTypeZ.ι.obj X) = 𝟙 _ := by
    have := congr_app (StructuredArrow.w φ) X
    simpa using this
  have h4 : IsIso (E.hom.app X ≫ φ.right.app (finTypeZ.ι.obj X)) := by
    rw [h2]; exact ⟨⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩
  exact IsIso.of_isIso_comp_left (E.hom.app X) (φ.right.app (finTypeZ.ι.obj X))

end GlobalTheory.FinExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilteredColimitCohomologyTransportQuasiIsoStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filteredColimitCohomology_transport_quasiIso : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M), (∀ A, SurjH (ε.app A) ∧ InjH (ε.app A)) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((M).obj c.pt).X n, ((M).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((M).obj (D.obj j)).X n) (y : ((M).obj c.pt).X (n - 1)), ((M).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((M).map (c.ι.app j)).f n w = z + ((M).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((M).obj (D.obj j)).X n), ((M).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((M).obj c.pt).X (n - 1), ((M).map (c.ι.app j)).f n w = ((M).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((M).obj (D.obj k)).X (n - 1)), ((M).map (D.map f)).f n w = ((M).obj (D.obj k)).d (n - 1) n y) := by
  first | (exact @GlobalTheory.EtC.contH_transport_quasiIso) | (exact GlobalTheory.EtC.contH_transport_quasiIso) | (intros; apply GlobalTheory.EtC.contH_transport_quasiIso  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtaleOfGaloisDescentHartogsStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteEtale_of_galois_descent_hartogs : ∀ (A R C O : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [IsNoetherianRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O] [Module.FaithfullyFlat R O]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → GlobalTheory.GoodEtale.Hart A R C → GlobalTheory.GoodEtale.EtaleLow A R C →
    Nonempty (C →ₐ[R] O) →
    Module.Finite R C ∧ Algebra.Etale R C := by
  first | (exact @GlobalTheory.GoodEtale.descent_finiteEtale) | (exact GlobalTheory.GoodEtale.descent_finiteEtale) | (intros; apply GlobalTheory.GoodEtale.descent_finiteEtale  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureAdditiveAutomorphismScale
section
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv MeasureTheory

namespace GlobalTheory.HaarScaleMatrix


open scoped Matrix in
open MeasureTheory in
theorem _root_.GlobalTheory.HaarScaleMatrix.secondCountable_of_localField (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] : SecondCountableTopology k :=
  _root_.GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field.1

end GlobalTheory.HaarScaleMatrix
end

