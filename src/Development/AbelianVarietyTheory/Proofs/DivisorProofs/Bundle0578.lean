module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstEqZeroOfDegreeLt
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

theorem coeff_subst_eq_zero_of_degree_lt :
    ∀ (R : Type) [CommRing R] (σ τ : Type) [Fintype σ] (u : σ → MvPowerSeries τ R)
      (f : MvPowerSeries σ R) (M : ℕ), (∀ i, constantCoeff (u i) = 0) →
      (∀ α : σ →₀ ℕ, α.degree < M → coeff α f = 0) →
      ∀ β : τ →₀ ℕ, β.degree < M → coeff β (subst u f) = 0 := by
  intro R _ σ τ _ u f M hu hf β hβ
  have hs : HasSubst u := ⟨fun i => by rw [hu i]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  rw [coeff_subst hs]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d.degree < M
  · simp [hf d hd]
  · push_neg at hd
    have hord : ((d.degree : ℕ) : ℕ∞) ≤ (d.prod fun s e => u s ^ e).order := by
      unfold Finsupp.prod
      refine le_trans ?_ (le_order_prod (fun s => u s ^ d s) d.support)
      have hdeg : d.degree = ∑ i ∈ d.support, d i := rfl
      rw [hdeg, Nat.cast_sum]
      exact Finset.sum_le_sum fun s _ => le_order_pow_of_constantCoeff_eq_zero (d s) (hu s)
    have h0 : coeff β (d.prod fun s e => u s ^ e) = 0 := by
      apply coeff_of_lt_order
      exact lt_of_lt_of_le (by exact_mod_cast (lt_of_lt_of_le hβ hd)) hord
    rw [h0, smul_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstMapToFractionsMemSubmodule
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SubstSub

theorem coeff_subst_up_mem : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ τ : Type) [Fintype σ] (S : Submodule B Q) (f : MvPowerSeries σ Q) (u : σ → MvPowerSeries τ B), (∀ i, constantCoeff (u i) = 0) → (∀ α, coeff α f ∈ S) → ∀ β, coeff β (subst (up Q u) f) ∈ S := by
  intro B Q _ _ _ σ τ _ S f u hu hf β
  have hc : ∀ i, constantCoeff (up Q u i) = 0 := fun i => by
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hu, map_zero]
  have ha : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero hc
  rw [coeff_subst ha]
  refine finsum_induction (fun x => x ∈ S) S.zero_mem (fun x y hx hy => S.add_mem hx hy) ?_
  intro d
  have hp : (d.prod fun s e => (up Q u s) ^ e) = map (algebraMap B Q) (d.prod fun s e => (u s) ^ e) := by
    simp only [up, Finsupp.prod, map_prod, map_pow]
  simp only [hp, coeff_map, smul_eq_mul]
  rw [mul_comm, ← Algebra.smul_def]
  exact S.smul_mem _ (hf d)

end GlobalTheory.SubstSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstRestrictSumVariables
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

open Classical in
theorem coeff_prod_pow_of_embedding {σ τ R : Type} [CommRing R] (j : σ → τ) (hj : Function.Injective j)
    (a : τ → MvPowerSeries σ R) (ha : ∀ s, a (j s) = X s) (h0 : ∀ t, t ∉ Set.range j → a t = 0)
    (d : τ →₀ ℕ) (α : σ →₀ ℕ) :
    coeff α (d.prod fun t e => a t ^ e) = if d = α.mapDomain j then 1 else 0 := by
  classical
  by_cases h : ∀ t, t ∉ Set.range j → d t = 0
  · obtain ⟨β, rfl⟩ := (Finsupp.mem_range_mapDomain_iff j hj d).mpr h
    rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    simp only [ha]
    rw [Finsupp.prod]
    simp only [X_pow_eq]
    rw [prod_monomial, Finset.prod_const_one]
    have hs : (∑ i ∈ β.support, Finsupp.single i (β i)) = β := Finsupp.sum_single β
    rw [hs, coeff_monomial]
    simp only [(Finsupp.mapDomain_injective hj).eq_iff, eq_comm]
  · push_neg at h
    obtain ⟨t, ht, hdt⟩ := h
    have hne : d ≠ α.mapDomain j := by
      intro hd
      have : d ∈ Set.range (Finsupp.mapDomain j) := ⟨α, hd.symm⟩
      exact hdt (((Finsupp.mem_range_mapDomain_iff j hj d).mp this) t ht)
    rw [if_neg hne, Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hdt)
      (by rw [h0 t ht, zero_pow hdt]), map_zero]

theorem coeff_subst_of_embedding {σ τ R : Type} [CommRing R] [Finite τ] (j : σ → τ)
    (hj : Function.Injective j)
    (a : τ → MvPowerSeries σ R) (ha : ∀ s, a (j s) = X s) (h0 : ∀ t, t ∉ Set.range j → a t = 0)
    (g : MvPowerSeries τ R) (α : σ →₀ ℕ) :
    coeff α (subst a g) = coeff (α.mapDomain j) g := by
  classical
  have hsub : HasSubst a := hasSubst_of_constantCoeff_zero (fun t => by
    by_cases ht : t ∈ Set.range j
    · obtain ⟨s, rfl⟩ := ht
      rw [ha]; exact constantCoeff_X s
    · rw [h0 t ht]; exact map_zero _)
  rw [coeff_subst hsub, finsum_eq_single _ (α.mapDomain j)]
  · rw [coeff_prod_pow_of_embedding j hj a ha h0, if_pos rfl, smul_eq_mul, mul_one]
  · intro d hd
    rw [coeff_prod_pow_of_embedding j hj a ha h0, if_neg hd, smul_zero]

theorem coeff_subst_restrict_sum {R ι κ : Type} [CommRing R] [Fintype ι] [Fintype κ]
    (g : MvPowerSeries (ι ⊕ κ) R) :
    (∀ α : ι →₀ ℕ, coeff α (subst (Sum.elim (fun i => (X i : MvPowerSeries ι R)) (fun _ => 0)) g) =
      coeff (α.mapDomain Sum.inl) g) ∧
    (∀ α : κ →₀ ℕ, coeff α (subst (Sum.elim (fun _ => 0) (fun i => (X i : MvPowerSeries κ R))) g) =
      coeff (α.mapDomain Sum.inr) g) := by
  refine ⟨fun α => coeff_subst_of_embedding Sum.inl Sum.inl_injective _ (fun _ => rfl) ?_ g α,
    fun α => coeff_subst_of_embedding Sum.inr Sum.inr_injective _ (fun _ => rfl) ?_ g α⟩
  · rintro (i | k) h
    · exact absurd ⟨i, rfl⟩ h
    · rfl
  · rintro (i | k) h
    · rfl
    · exact absurd ⟨k, rfl⟩ h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSumElimPowerSeriesSwapVariableGroups
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SwapCoeff

theorem swap_eq_rename (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    swap c = rename (Equiv.sumComm (Fin d) (Fin d)) c := by
  rw [rename_eq_subst]
  unfold swap at2
  congr 1
  funext s
  rcases s with i | i <;> rfl

theorem coeff_swap : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a e) (swap c) = coeff (Finsupp.sumElim e a) c := by
  intro R _ d c a e
  have h := coeff_embDomain_rename (Equiv.sumComm (Fin d) (Fin d)).toEmbedding c (Finsupp.sumElim e a)
  have hinj : Function.Injective (Equiv.sumComm (Fin d) (Fin d)) := (Equiv.sumComm _ _).injective
  have hE : Finsupp.embDomain (Equiv.sumComm (Fin d) (Fin d)).toEmbedding (Finsupp.sumElim e a) =
      Finsupp.sumElim a e := by
    rw [Finsupp.embDomain_eq_mapDomain]
    ext x
    rcases x with i | i
    · have := Finsupp.mapDomain_apply_of_injective hinj (Finsupp.sumElim e a) (Sum.inr i)
      simpa using this
    · have := Finsupp.mapDomain_apply_of_injective hinj (Finsupp.sumElim e a) (Sum.inl i)
      simpa using this
  rw [hE] at h
  rw [swap_eq_rename]
  exact h

end GlobalTheory.SwapCoeff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffsInIdealOfPowerSeriesIffImage
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem series_in_ideal_iff_image :
    ∀ (B Q σ : Type) [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B) (f : MvPowerSeries σ Q),
      (In N f ↔ ∃ s : MvPowerSeries σ B, (∀ α, coeff α s ∈ N) ∧ map (algebraMap B Q) s = f) ∧
      ∀ g : MvPowerSeries σ Q, In N f → In N g → ∀ a : B,
        In N (f + algebraMap B Q a • g) ∧ In N (f - g) := by
  intro B Q σ _ _ _ N f
  refine ⟨⟨fun h => ?_, fun ⟨s, hs, hsf⟩ α => ?_⟩, fun g hf hg a => ⟨fun α => ?_, fun α => ?_⟩⟩
  · choose b hbN hb using h
    obtain ⟨s, hs⟩ : ∃ s : MvPowerSeries σ B, ∀ α, coeff α s = b α := ⟨b, fun _ => rfl⟩
    refine ⟨s, fun α => (hs α).symm ▸ hbN α, ?_⟩
    ext α
    rw [coeff_map, hs]
    exact (hb α).symm
  · exact ⟨coeff α s, hs α, by rw [← hsf, coeff_map]⟩
  · obtain ⟨b₁, hb₁N, hb₁⟩ := hf α
    obtain ⟨b₂, hb₂N, hb₂⟩ := hg α
    refine ⟨b₁ + a * b₂, N.add_mem hb₁N (N.mul_mem_left a hb₂N), ?_⟩
    rw [map_add (f := _), map_smul, smul_eq_mul, hb₁, hb₂, map_add (f := _), map_mul]
  · obtain ⟨b₁, hb₁N, hb₁⟩ := hf α
    obtain ⟨b₂, hb₂N, hb₂⟩ := hg α
    exact ⟨b₁ - b₂, N.sub_mem hb₁N hb₂N, by rw [map_sub, hb₁, hb₂, map_sub]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffsInIdealSolutionOfUnipotentSeriesMatrix
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.InvSolve

theorem in_iff_mem {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B)
    (f : MvPowerSeries σ Q) :
    In N f ↔ ∀ α, coeff α f ∈ N.toAddSubmonoid.map (algebraMap B Q).toAddMonoidHom := by
  simp only [In, AddSubmonoid.mem_map, Submodule.mem_toAddSubmonoid, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe]
  constructor
  · intro h α; obtain ⟨b, hb, e⟩ := h α; exact ⟨b, hb, e.symm⟩
  · intro h α; obtain ⟨b, hb, e⟩ := h α; exact ⟨b, hb, e.symm⟩

theorem in_mul_map {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B)
    (f : MvPowerSeries σ Q) (h : MvPowerSeries σ B) (hf : In N f) :
    In N (f * map (algebraMap B Q) h) := by
  classical
  rw [in_iff_mem] at hf ⊢
  intro α
  rw [coeff_mul]
  refine AddSubmonoid.sum_mem _ fun x _ => ?_
  obtain ⟨b, hb, e⟩ := AddSubmonoid.mem_map.1 (hf x.1)
  refine AddSubmonoid.mem_map.2 ⟨b * coeff x.2 h, N.mul_mem_right _ hb, ?_⟩
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at e ⊢
  rw [map_mul, e, coeff_map]

theorem in_sum {B Q σ ι : Type} [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B)
    (s : Finset ι) (f : ι → MvPowerSeries σ Q) (hf : ∀ i ∈ s, In N (f i)) :
    In N (∑ i ∈ s, f i) := by
  rw [in_iff_mem] at *
  intro α
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact AddSubmonoid.sum_mem _ fun i hi => (in_iff_mem N (f i)).1 (hf i hi) α

theorem solve : ∀ {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} (N : Ideal B) (M : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) B)), (∀ i j, constantCoeff (M i j) = if i = j then 1 else 0) → ∀ (v g : Fin d → MvPowerSeries (Fin d) Q), (∀ i, ∑ j, v j * map (algebraMap B Q) (M j i) = g i) → (∀ i, In N (g i)) → ∀ j, In N (v j) := by
  intro B Q _ _ _ d N M hM v g hv hg j
  classical
  have hc : (constantCoeff : MvPowerSeries (Fin d) B →+* B).mapMatrix M = 1 := by
    ext i k; simp [hM, Matrix.one_apply]
  have hdet : IsUnit M.det := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, hc, Matrix.det_one]
    exact isUnit_one
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet
  let φ : MvPowerSeries (Fin d) B →+* MvPowerSeries (Fin d) Q := map (algebraMap B Q)
  have h2 : φ.mapMatrix M * φ.mapMatrix M⁻¹ = 1 := by rw [← map_mul, h1, map_one]
  have hvg : Matrix.vecMul v (φ.mapMatrix M) = g := funext fun i => by
    simpa [Matrix.vecMul, dotProduct, φ] using hv i
  have hv' : v = Matrix.vecMul g (φ.mapMatrix M⁻¹) := by
    rw [← hvg, Matrix.vecMul_vecMul, h2, Matrix.vecMul_one]
  rw [hv']
  simp only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, φ]
  exact in_sum N _ _ fun i _ => in_mul_map N _ _ (hg i)

end GlobalTheory.InvSolve
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffFrob
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.QLog.Window

section Integral

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_top_iff (f : MvPowerSeries σ Q) :
    In (⊤ : Ideal B) f ↔ ∃ s : MvPowerSeries σ B, f = map (algebraMap B Q) s := by
  constructor
  · intro h
    choose b _ hb using h
    let s : MvPowerSeries σ B := fun α => b α
    refine ⟨s, ?_⟩
    ext α
    rw [coeff_map, hb]
    rfl
  · rintro ⟨s, rfl⟩ α
    exact ⟨coeff α s, Submodule.mem_top, by rw [coeff_map]⟩

theorem in_zero (N : Ideal B) : In N (0 : MvPowerSeries σ Q) := fun _ =>
  ⟨0, N.zero_mem, by simp⟩

theorem in_add {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) :
    In N (f + g) := fun α => by
  obtain ⟨a, ha, ea⟩ := hf α
  obtain ⟨b, hb, eb⟩ := hg α
  exact ⟨a + b, N.add_mem ha hb, by rw [map_add (f := _), ea, eb, map_add (f := _)]⟩

theorem in_neg {N : Ideal B} {f : MvPowerSeries σ Q} (hf : In N f) : In N (-f) := fun α => by
  obtain ⟨a, ha, ea⟩ := hf α
  exact ⟨-a, N.neg_mem ha, by rw [map_neg, ea, map_neg]⟩

theorem in_smul {N : Ideal B} {f : MvPowerSeries σ Q} (hf : In N f) (b : B) :
    In N (algebraMap B Q b • f) := fun α => by
  obtain ⟨a, ha, ea⟩ := hf α
  exact ⟨b * a, N.mul_mem_left b ha, by rw [map_smul, smul_eq_mul, ea, ← map_mul]⟩

theorem in_sum {N : Ideal B} {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ Q)
    (hf : ∀ i ∈ s, In N (f i)) : In N (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using in_zero (σ := σ) (Q := Q) N
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact in_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Integral

section Frob

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] (p : ℕ) [hp : Fact p.Prime]
  {σ : Type} [Finite σ] (s : Q →+* Q)

theorem hasSubst_X_pow : HasSubst (fun i : σ => (X i : MvPowerSeries σ Q) ^ p) :=
  HasSubst.X_pow hp.out.ne_zero

theorem frob_add (f g : MvPowerSeries σ Q) : frob p s (f + g) = frob p s f + frob p s g := by
  unfold frob
  rw [map_add (f := _), subst_add (hasSubst_X_pow p)]

theorem frob_zero : frob p s (0 : MvPowerSeries σ Q) = 0 := by
  have h := frob_add p s (0 : MvPowerSeries σ Q) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem frob_sub (f g : MvPowerSeries σ Q) : frob p s (f - g) = frob p s f - frob p s g := by
  unfold frob
  rw [map_sub, subst_sub (hasSubst_X_pow p)]

theorem map_smul' {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r : R)
    (f : MvPowerSeries σ R) : map φ (r • f) = φ r • map φ f := by
  ext α
  rw [coeff_map, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, coeff_map, map_mul]

theorem frob_smul (r : Q) (f : MvPowerSeries σ Q) : frob p s (r • f) = s r • frob p s f := by
  unfold frob
  rw [map_smul', subst_smul (hasSubst_X_pow p)]

theorem frob_sum {ι : Type} (t : Finset ι) (f : ι → MvPowerSeries σ Q) :
    frob p s (∑ i ∈ t, f i) = ∑ i ∈ t, frob p s (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using frob_zero p s
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, frob_add, ih]

theorem frob_comb (σ' : B →+* B) (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (σ' b))
    {ι : Type} [Fintype ι] (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    frob p s (comb b e) = comb (fun i => σ' (b i)) fun i => frob p s (e i) := by
  unfold comb
  rw [frob_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [frob_smul, hs]

theorem constantCoeff_frob {f : MvPowerSeries σ Q} (hf : constantCoeff f = 0) :
    constantCoeff (frob p s f) = 0 := by
  unfold frob
  refine constantCoeff_subst_eq_zero (hasSubst_X_pow p) (fun i => ?_) ?_
  · rw [map_pow, constantCoeff_X, zero_pow hp.out.ne_zero]
  · rw [constantCoeff_map, hf, map_zero]

theorem in_frob (σ' : B →+* B) (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (σ' b))
    {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) : In (⊤ : Ideal B) (frob p s f) := by
  obtain ⟨t, rfl⟩ := (in_top_iff f).1 hf
  refine (in_top_iff _).2 ⟨subst (fun i : σ => (X i : MvPowerSeries σ B) ^ p) (map σ' t), ?_⟩
  have hm : map s (map (algebraMap B Q) t) = map (algebraMap B Q) (map σ' t) := by
    ext α
    simp only [coeff_map, hs]
  unfold frob
  rw [hm, map_subst (HasSubst.X_pow hp.out.ne_zero)]
  simp only [map_pow, map_X]

end Frob

section Cob

theorem map_formalGroupLawCoboundaryOne_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (h : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) R) :
    map φ (cob1 μ f) = cob1 (fun i => map φ (μ i)) (map φ f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero h),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ}
  {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}

theorem constantCoeff_up (hμ : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) :
    constantCoeff (up Q μ i) = 0 := by
  rw [up, constantCoeff_map, hμ, map_zero]

theorem ql_zero (hμ : ∀ i, constantCoeff (μ i) = 0) (N : Ideal B) :
    QL μ N (0 : MvPowerSeries (Fin d) Q) := by
  refine ⟨map_zero _, fun i => ⟨0, N.zero_mem, by simp [lin]⟩, ?_⟩
  have h := formalCoboundary_smul (constantCoeff_up (Q := Q) hμ) (0 : Q) 0
  rw [zero_smul, zero_smul] at h
  rw [h]
  exact in_zero N

theorem ql_add_smul (hμ : ∀ i, constantCoeff (μ i) = 0) {N : Ideal B}
    {f g : MvPowerSeries (Fin d) Q} (hf : QL μ N f) (hg : QL μ N g) (b : B) :
    QL μ N (f + algebraMap B Q b • g) := by
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, map_add (f := _), map_smul, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, hf.1, hg.1, smul_zero, add_zero]
  · obtain ⟨a, ha, ea⟩ := hf.2.1 i
    obtain ⟨a', ha', ea'⟩ := hg.2.1 i
    refine ⟨a + b * a', N.add_mem ha (N.mul_mem_left b ha'), ?_⟩
    simp only [lin] at ea ea' ⊢
    rw [map_add (f := _), map_smul, ea, ea', smul_eq_mul, map_add (f := _), map_mul]
  · rw [formalCoboundary_add (constantCoeff_up hμ), formalCoboundary_smul (constantCoeff_up hμ)]
    exact in_add hf.2.2 (in_smul hg.2.2 b)

theorem ql_comb (hμ : ∀ i, constantCoeff (μ i) = 0) {N : Ideal B} {ι : Type} [Fintype ι]
    (e : ι → MvPowerSeries (Fin d) Q) (he : ∀ i, QL μ N (e i)) (b : ι → B) :
    QL μ N (comb b e) := by
  classical
  unfold comb
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using ql_zero (Q := Q) hμ N
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, add_comm]
    exact ql_add_smul hμ ih (he a) (b a)

end Cob

end GlobalTheory.QLog.Window
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLIsCharacterNormOneOfRegular
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem isChar_cusp_and_norm_of_reg (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (m k : ℕ) (hm : 0 < m)
    (hk : Reg (Nat.card F) m k) :
    IsChar ℂ ℂ (cusp θ m k) ∧
      ∑ᶠ x, cusp θ m k x * star (cusp θ m k x) = (Nat.card (GL (Fin m) F) : ℂ) := by
  obtain ⟨h1, h2⟩ := isChar_psi_rootSum_of_regular F θ hθ m k hm hk
  refine ⟨h1, ?_⟩
  have hip := ipGL_eq_finsum_GL (F := F) (d := m) (psi (rootSum θ k) (Fin m → F))
    (psi (rootSum θ k) (Fin m → F))
  rw [h2] at hip
  have hsq : ((-1 : ℂ) ^ (m - 1)) * star ((-1 : ℂ) ^ (m - 1)) = 1 := by
    rw [star_pow, star_neg, star_one, ← mul_pow]
    norm_num
  have hterm : ∀ x : GL (Fin m) F, cusp θ m k x * star (cusp θ m k x) =
      psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) *
        star (psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F))) := by
    intro x
    simp only [cusp, psiG, star_mul']
    linear_combination (psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) *
        star (psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)))) * hsq
  rw [finsum_congr hterm, ← hip]
  rfl

end GlobalTheory.Shin
end

