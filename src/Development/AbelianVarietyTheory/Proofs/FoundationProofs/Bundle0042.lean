module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdjacentSelfDualLatticesIndexSimple
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

open Classical in
open scoped BigOperators in
private lemma existsUnique_quotient_sub_smul_mem {R X : Type} [CommRing R] [AddCommGroup X]
    [Module R X] (A B : Submodule R X) (x : X) (P : Ideal R)
    (hxP : ∀ r : R, r • x ∈ A ↔ r ∈ P) (hBle : B ≤ (A ⊓ B) ⊔ Submodule.span R {x}) :
    ∀ b ∈ B, ∃! q : R ⧸ P, b - (Quotient.out q : R) • x ∈ A := by
  intro b hb
  obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.1 (hBle hb)
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
  refine ⟨Ideal.Quotient.mk P r, ?_, ?_⟩
  · have h1 : (r - Quotient.out (Ideal.Quotient.mk P r)) • x ∈ A := by
      rw [hxP, ← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
    have h2 : c + r • x - Quotient.out (Ideal.Quotient.mk P r) • x =
        c + (r - Quotient.out (Ideal.Quotient.mk P r)) • x := by
      rw [sub_smul]; abel
    show c + r • x - Quotient.out (Ideal.Quotient.mk P r) • x ∈ A
    rw [h2]
    exact A.add_mem (Submodule.mem_inf.1 hc).1 h1
  · intro q hq
    have h2 : (r - Quotient.out q) • x ∈ A := by
      have h3 : (r - Quotient.out q) • x = (c + r • x - Quotient.out q • x) - c := by
        rw [sub_smul]; abel
      rw [h3]
      exact A.sub_mem hq (Submodule.mem_inf.1 hc).1
    rw [hxP, ← Ideal.Quotient.eq, Ideal.Quotient.mk_out] at h2
    exact h2.symm

open Classical in
open scoped BigOperators in
private lemma le_or_eq_of_inf_le_of_le_of_isMaximal {R X : Type} [CommRing R] [AddCommGroup X]
    [Module R X] (A B : Submodule R X) (x : X) (hx : x ∈ B) (P : Ideal R) (hP : P.IsMaximal)
    (hxP : ∀ r : R, r • x ∈ A ↔ r ∈ P) (hBle : B ≤ (A ⊓ B) ⊔ Submodule.span R {x})
    (T : Submodule R X) (h1 : A ⊓ B ≤ T) (h2 : T ≤ B) : T ≤ A ∨ T = B := by
  by_cases hTA : T ≤ A
  · exact Or.inl hTA
  right
  obtain ⟨t, htT, htA⟩ := Set.not_subset.1 hTA
  obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.1 (hBle (h2 htT))
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hr : r ∉ P := fun hr => htA (A.add_mem (Submodule.mem_inf.1 hc).1 ((hxP r).2 hr))
  obtain ⟨s, i, hi, hsi⟩ := hP.exists_inv hr
  have hrx : r • x ∈ T := by
    have h3 := T.sub_mem htT (h1 hc)
    rwa [add_sub_cancel_left] at h3
  have hix : i • x ∈ T := h1 (Submodule.mem_inf.2 ⟨(hxP i).2 hi, B.smul_mem i hx⟩)
  have hxT : x ∈ T := by
    have h4 : x = s • r • x + i • x := by rw [smul_smul, ← add_smul, hsi, one_smul]
    rw [h4]
    exact T.add_mem (T.smul_mem s hrx) hix
  refine le_antisymm h2 (hBle.trans (sup_le h1 ?_))
  rw [Submodule.span_singleton_le_iff_mem]
  exact hxT

open Classical in
open scoped BigOperators in
private lemma toAddSubgroup_inf {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) : (A ⊓ B).toAddSubgroup = A.toAddSubgroup ⊓ B.toAddSubgroup := by
  ext; simp


open Classical in
open scoped BigOperators in
theorem _root_.GlobalTheory.FinWeil.adjacent_selfDual_simple : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ (A B : Submodule R X), _root_.GlobalTheory.FinWeil.SelfDual γ A → _root_.GlobalTheory.FinWeil.SelfDual γ B → ∀ x ∈ B, ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) → (∀ r : R, r • x ∈ A ↔ r ∈ P) → B ≤ (A ⊓ B) ⊔ Submodule.span R {x} → _root_.GlobalTheory.FinWeil.idx A B = Nat.card (R ⧸ P) ∧ _root_.GlobalTheory.FinWeil.idx B A = Nat.card (R ⧸ P) ∧ (∀ b ∈ B, ∃! q : R ⧸ P, b - (Quotient.out q : R) • x ∈ A) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ B → T ≤ A ∨ T = B) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ A → T ≤ B ∨ T = A) := by
  intro R X M _ _ _ _ _ σ w γ W hW A B hA hB x hx P hP hfin hxP hBle
  have hA' : ∀ y, y ∈ A ↔ ∀ a ∈ A, γ y a = 1 := hA
  have hB' : ∀ y, y ∈ B ↔ ∀ b ∈ B, γ y b = 1 := hB
  have hrep := existsUnique_quotient_sub_smul_mem A B x P hxP hBle
  have hN : Nat.card (R ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hAB : _root_.GlobalTheory.FinWeil.idx A B = Nat.card (R ⧸ P) := by
    haveI := Fintype.ofFinite (R ⧸ P)
    rw [Nat.card_eq_fintype_card]
    exact (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A B hB (0 : M) (fun a _ => map_zero (W a)) (R ⧸ P)
      (fun q => Quotient.out q • x) (fun q => B.smul_mem _ hx) hrep).2
  have hAB' : A.toAddSubgroup.relIndex B.toAddSubgroup = Nat.card (R ⧸ P) := hAB
  have hBA : B.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (R ⧸ P) := by
    have key := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW B.toAddSubgroup A.toAddSubgroup A.toAddSubgroup
      B.toAddSubgroup (fun a _ => by simpa only [Submodule.mem_toAddSubgroup] using hB' a)
      (fun t ht => by
        simp only [Submodule.mem_toAddSubgroup] at ht ⊢
        rw [hA' t]
        exact ⟨fun h a ha => hW.swap_eq_one (h a ha),
          fun h a ha => hW.swap_eq_one (h a ha)⟩)
      (by rw [hAB']; exact hN)).1
    rw [key, hAB']
  have hdich := le_or_eq_of_inf_le_of_le_of_isMaximal A B x hx P hP hxP hBle
  refine ⟨hAB, hBA, hrep, hdich, ?_⟩
  intro T h1 h2
  by_cases hTB : T ≤ B
  · exact Or.inl hTB
  right
  let T' : Submodule R X :=
    { carrier := {b | b ∈ B ∧ ∀ t ∈ T, γ t b = 1}
      add_mem' := fun {b b'} hb hb' => ⟨B.add_mem hb.1 hb'.1, fun t ht => by
        rw [hW.add_right, hb.2 t ht, hb'.2 t ht, one_mul]⟩
      zero_mem' := ⟨B.zero_mem, fun t _ => hW.zero_right t⟩
      smul_mem' := fun r b hb => ⟨B.smul_mem r hb.1, fun t ht => by
        have h3 := hW.adj (σ r) t b
        rw [hW.sg_sg] at h3
        rw [← h3]
        exact hb.2 _ (T.smul_mem _ ht)⟩ }
  have hmemT' : ∀ b, b ∈ T' ↔ b ∈ B ∧ ∀ t ∈ T, γ t b = 1 := fun b => Iff.rfl
  have hT'1 : A ⊓ B ≤ T' := fun c hc => (hmemT' c).2
    ⟨(Submodule.mem_inf.1 hc).2, fun t ht =>
      hW.iso hA (h2 ht) (Submodule.mem_inf.1 hc).1⟩
  have hT'2 : T' ≤ B := fun b hb => ((hmemT' b).1 hb).1
  rcases hdich T' hT'1 hT'2 with hle | heq
  · have hT'eq : T' = A ⊓ B := le_antisymm (le_inf hle hT'2) hT'1
    have hprod : (A ⊓ B).toAddSubgroup.relIndex T.toAddSubgroup *
        T.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (R ⧸ P) := by
      rw [AddSubgroup.relIndex_mul_relIndex (A ⊓ B).toAddSubgroup T.toAddSubgroup
        A.toAddSubgroup (fun y hy => h1 hy) (fun y hy => h2 hy),
        toAddSubgroup_inf, AddSubgroup.inf_relIndex_left, hBA]
    have hne : (A ⊓ B).toAddSubgroup.relIndex T.toAddSubgroup ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hprod; exact hN hprod.symm
    have key := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW T'.toAddSubgroup B.toAddSubgroup
      (A ⊓ B).toAddSubgroup T.toAddSubgroup
      (fun b hb => by
        simp only [Submodule.mem_toAddSubgroup] at hb ⊢
        rw [hmemT']
        exact ⟨fun h t ht => hW.swap_eq_one (h.2 t ht),
          fun h => ⟨hb, fun t ht => hW.swap_eq_one (h t ht)⟩⟩)
      (fun t ht => by
        simp only [Submodule.mem_toAddSubgroup, Submodule.mem_inf] at ht ⊢
        rw [hB' t]
        exact ⟨fun h b hb => hW.swap_eq_one (h.2 b hb),
          fun h => ⟨h2 ht, fun b hb => hW.swap_eq_one (h b hb)⟩⟩)
      hne).1
    rw [hT'eq, toAddSubgroup_inf, AddSubgroup.inf_relIndex_right, hAB',
      ← toAddSubgroup_inf] at key
    rw [← key] at hprod
    have hone : T.toAddSubgroup.relIndex A.toAddSubgroup = 1 := by
      have h5 : Nat.card (R ⧸ P) * T.toAddSubgroup.relIndex A.toAddSubgroup =
          Nat.card (R ⧸ P) * 1 := by rw [hprod, mul_one]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN) h5
    have hAT := AddSubgroup.relIndex_eq_one.1 hone
    exact le_antisymm h2 (fun a ha => hAT ha)
  · exfalso
    apply hTB
    intro t ht
    rw [hB' t]
    intro b hb
    rw [← heq] at hb
    exact ((hmemT' b).1 hb).2 t ht

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleOfSl2Action
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

private theorem natCast_mul_act_mem_range_intCast (c : ℕ) (z : Fin 2 → ℚ) (δ : SL(2, ℤ))
    (h0 : (c : ℚ) * z 0 ∈ Set.range ((↑) : ℤ → ℚ)) (h1 : (c : ℚ) * z 1 ∈ Set.range ((↑) : ℤ → ℚ))
    (i : Fin 2) : (c : ℚ) * act z δ i ∈ Set.range ((↑) : ℤ → ℚ) := by
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  refine ⟨a * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 i + b * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 i, ?_⟩
  simp only [act, Fin.sum_univ_two]
  push_cast
  rw [ha, hb]
  ring

private theorem act_act_inv' (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : act (act x γ) γ⁻¹ = x := by
  have hd := γ.2
  rw [Matrix.det_fin_two] at hd
  have hq : ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ)) : ℚ) = 1 := by
    rw [hd]; simp
  push_cast at hq
  funext i
  fin_cases i <;>
    simp [act, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] <;>
    push_cast
  · linear_combination x 0 * hq
  · linear_combination x 1 * hq

theorem admissible_act_SL2 : ∀ (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)), admitted c x → admitted c (act x γ) := by
  rintro c x γ ⟨h1, h2, h3⟩
  refine ⟨h1, h2, fun ⟨k0, k1⟩ => h3 ?_⟩
  rw [← act_act_inv' x γ]
  exact ⟨natCast_mul_act_mem_range_intCast c _ _ k0 k1 0, natCast_mul_act_mem_range_intCast c _ _ k0 k1 1⟩

end GlobalTheory.Sieg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjective
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem norm_surjective_of_norm_form {K L : Type} [Field K] [Field L] [Algebra K L] (hC : IsFirstChernClassOfLineBundle K) (m : ℕ) (hm0 : 0 < m)
    (B : Module.Basis (Fin m) K L) (f : MvPolynomial (Fin m) K) (hf : f.IsHomogeneous m)
    (hnorm : ∀ x : L, Algebra.norm K x = MvPolynomial.eval (fun i => B.repr x i) f)
    (hpow : ∀ a : K, Algebra.norm K (algebraMap K L a) = a ^ m)
    (b : K) : ∃ x : L, Algebra.norm K x = b := by
  let g : MvPolynomial (Fin (m + 1)) K :=
    MvPolynomial.rename Fin.succ f - MvPolynomial.C b * MvPolynomial.X 0 ^ m
  have hg : g.IsHomogeneous m := by
    refine (hf.rename_isHomogeneous).sub ?_
    have := (MvPolynomial.isHomogeneous_C (Fin (m + 1)) b).mul (MvPolynomial.isHomogeneous_X_pow (0 : Fin (m + 1)) m)
    rwa [zero_add] at this
  obtain ⟨y, hy0, hy⟩ := hC (m + 1) m g hg hm0 (Nat.lt_succ_self m)
  let x : L := B.equivFun.symm (fun i => y i.succ)
  have hrepr : ∀ i, B.repr x i = y i.succ := by
    intro i
    have h := congrFun (B.equivFun.apply_symm_apply (fun i => y i.succ)) i
    rw [Module.Basis.equivFun_apply] at h
    exact h
  have hev : Algebra.norm K x = b * y 0 ^ m := by
    have h1 := hy
    simp only [g, map_sub, map_mul, map_pow, MvPolynomial.eval_rename, MvPolynomial.eval_C,
      MvPolynomial.eval_X] at h1
    rw [hnorm]
    have e : (fun i => B.repr x i) = y ∘ Fin.succ := funext hrepr
    rw [e]; exact sub_eq_zero.mp h1
  have hnz : ∀ z : L, Algebra.norm K z = 0 → z = 0 := by
    intro z hz
    by_contra hz'
    have hu : IsUnit z := (isUnit_iff_ne_zero).mpr hz'
    exact (hu.map (Algebra.norm K)).ne_zero hz
  have hy00 : y 0 ≠ 0 := by
    intro h0
    apply hy0
    have hx : x = 0 := hnz x (by rw [hev, h0, zero_pow hm0.ne', mul_zero])
    funext i
    refine Fin.cases h0 (fun j => ?_) i
    have := hrepr j
    rw [hx, map_zero] at this
    simpa using this.symm
  refine ⟨x * algebraMap K L (y 0)⁻¹, ?_⟩
  rw [map_mul, hpow, hev, mul_assoc, ← mul_pow, mul_inv_cancel₀ hy00, one_pow, mul_one]

theorem norm_surjective_of_is_c1 : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L], IsFirstChernClassOfLineBundle K →
    ∀ b : K, b ≠ 0 → ∃ x : L, Algebra.norm K x = b := by
  intro K L _ _ _ _ hC b _
  obtain ⟨f, hf, hnorm⟩ := _root_.GlobalTheory.norm_isHomogeneous_poly_coords K L
  exact norm_surjective_of_norm_form hC _ Module.finrank_pos (Module.finBasis K L) f hf hnorm
    (fun a => Algebra.norm_algebraMap a) b

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CountSpanSingletonRingEquiv
section
open IsDedekindDomain Polynomial
open scoped nonZeroDivisors

namespace GlobalTheory.OrdTransport

theorem count_spanSingleton_ringEquiv : ∀ (A F : Type) [CommRing A] [IsDedekindDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F] (τ : A ≃+* A) (σ : F ≃+* F),
    (∀ a : A, σ (algebraMap A F a) = algebraMap A F (τ a)) → ∀ v w : HeightOneSpectrum A,
    (∀ a : A, a ∈ v.asIdeal ↔ τ a ∈ w.asIdeal) → ∀ x : F, x ≠ 0 →
    FractionalIdeal.count F w (FractionalIdeal.spanSingleton A⁰ (σ x)) =
      FractionalIdeal.count F v (FractionalIdeal.spanSingleton A⁰ x) := by
  intro A F _ _ _ _ _ τ σ hc v w hvw x hx
  have h : v.asIdeal = w.asIdeal.comap τ := Ideal.ext fun a => by
    rw [Ideal.mem_comap]; exact hvw a
  have hv : v.valuation F x = w.valuation F (σ x) := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    rw [map_div₀ σ, hc, hc, map_div₀, map_div₀]
    simp only [HeightOneSpectrum.valuation_of_algebraMap,
      GlobalTheory.QNorm.intValuation_of_eq_comap τ w v h]
  have hσx : σ x ≠ 0 := (map_ne_zero σ).2 hx
  rw [GlobalTheory.Idele.valuation_eq_exp_neg_count v hx, GlobalTheory.Idele.valuation_eq_exp_neg_count w hσx,
    WithZero.exp_inj, neg_inj] at hv
  exact hv.symm

end GlobalTheory.OrdTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CthFacMultipliable
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

noncomputable section

namespace GlobalTheory.Sieg.CthMult

end GlobalTheory.Sieg.CthMult


open scoped UpperHalfPlane MatrixGroups Manifold in
theorem _root_.GlobalTheory.Sieg.cthFac_multipliable : ∀ (c : ℕ) (q t : ℂ), ‖q‖ < 1 → t ≠ 0 →
    Multipliable (fun m : ℕ => _root_.GlobalTheory.Sieg.cthFac c q t (m + 1)) := by
  intro c q t hq _
  set g : ℂ → ℂ := fun u => (1 - u * t) ^ c ^ 2 * (1 - u * t⁻¹) ^ c ^ 2 /
    ((1 - u * t ^ c) * (1 - u * (t ^ c)⁻¹)) with hg
  have hgd : DifferentiableAt ℂ g 0 := by
    apply DifferentiableAt.div (by fun_prop) (by fun_prop)
    simp
  have hg0 : g 0 = 1 := by simp [hg]
  have hbig : (fun m : ℕ => g (q ^ (m + 1)) - 1) =O[Filter.atTop] (fun m : ℕ => q ^ (m + 1)) := by
    have h := hgd.isBigO_sub
    rw [hg0] at h
    simp only [sub_zero] at h
    have ht : Filter.Tendsto (fun m : ℕ => q ^ (m + 1)) Filter.atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp (Filter.tendsto_add_atTop_nat 1)
    exact h.comp_tendsto ht
  have hsum : Summable (fun m : ℕ => ‖g (q ^ (m + 1)) - 1‖) := by
    refine summable_of_isBigO_nat (g := fun m : ℕ => ‖q‖ ^ (m + 1)) ?_ ?_
    · exact (summable_geometric_of_lt_one (norm_nonneg _) hq).comp_injective (add_left_injective 1)
    · simpa [norm_pow] using hbig.norm_left.norm_right
  have hmul := multipliable_one_add_of_summable hsum
  simpa [hg, _root_.GlobalTheory.Sieg.cthFac] using hmul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormIsCuspidalAtAllCuspsSL2
section
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem cuspForm_cuspAll : ∀ (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (f : CuspForm Γ k), CuspAll k f := by
  intro Γ _ k f
  refine ⟨f.holo', fun c hc => ?_⟩
  rw [← Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (Γ : Subgroup (GL (Fin 2) ℝ))] at hc
  exact f.zero_at_cusps' hc

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationEqZeroOfIsAlgebraicOverPadicIntegers
section
open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.DerAlg

open Polynomial

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

abbrev phiZ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] : ℤ_[p] →+* Ω :=
  (algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))

theorem phiZ_injective [CharZero Ω] : Function.Injective (phiZ p Ω) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hc
  have hu : IsUnit (phiZ p Ω (PadicInt.unitCoeff h0 : ℤ_[p])) :=
    (Units.isUnit _).map _
  have hp : ((p : Ω)) ^ c.valuation ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  exact mul_ne_zero hu.ne_zero hp hc

theorem der_eval₂ (E : Derivation ℤ Ω Ω)
    (hE : ∀ r : ℤ_[p], E (algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) r)) = 0)
    (x : Ω) (Q : ℤ_[p][X]) :
    E (eval₂ (phiZ p Ω) x Q) = eval₂ (phiZ p Ω) x (derivative Q) * E x := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => rw [eval₂_add, map_add (f := _), hP, hQ, derivative_add, eval₂_add, add_mul]
  | monomial n c =>
    have hc : E (phiZ p Ω c) = 0 := hE c
    rw [eval₂_monomial, Derivation.leibniz, Derivation.leibniz_pow, hc, smul_zero, add_zero,
      derivative_monomial, eval₂_monomial]
    simp only [smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
    ring

theorem der_algZp : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ E : Derivation ℤ Ω Ω, (∀ r : ℤ_[p], E (algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) r)) = 0) →
    ∀ x : Ω, IsAlgZp (p := p) x → E x = 0 := by
  intro p _ Ω _ _ hC E hE x hx
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hC
  obtain ⟨P, hP0, hPx⟩ := hx
  rw [aeval_def, eval₂_map] at hPx
  change eval₂ (phiZ p Ω) x P = 0 at hPx
  by_contra hEx
  have key : ∀ n, ∀ P : ℤ_[p][X], P.natDegree = n → P ≠ 0 → eval₂ (phiZ p Ω) x P ≠ 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P hn hP hzero
      by_cases hd : P.natDegree = 0
      · rw [eq_C_of_natDegree_eq_zero hd, eval₂_C] at hzero
        have := phiZ_injective (p := p) (Ω := Ω) (hzero.trans (map_zero _).symm)
        exact hP (by rw [eq_C_of_natDegree_eq_zero hd, this, C_0])
      · have hD : derivative P ≠ 0 := fun h => hd (natDegree_eq_zero_of_derivative_eq_zero h)
        have hlt := natDegree_derivative_lt hd
        refine ih _ (hn ▸ hlt) (derivative P) rfl hD ?_
        have h1 := der_eval₂ E hE x P
        rw [hzero, map_zero] at h1
        exact (mul_eq_zero.1 h1.symm).resolve_right hEx
  exact key _ P rfl hP0 hPx

end GlobalTheory.K5.DerAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationModIntegralAlmostDualPSqIsInt
section
open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.KumDlog

theorem der_dual_p_sq_int : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω),
    DualData B C u v tr →
  ∀ D : Ω → Ω, IsDer C D → ∀ x ∈ C, (∀ k l, IsInt (p := p) (D (tr (u l * (x * v k))))) →
    IsInt (p := p) ((p : Ω) ^ 2 * D x) := by
  intro p _ Ω _ _ B C ι _ u v tr hd D hD x hx hT
  obtain ⟨hBC, hCi, hu, hv, htr, -, -, hsu, hsv, huv⟩ := hd
  have s1 : ∀ k, IsInt (p := p) ((p : Ω) * D (x * v k) - ∑ l, tr (u l * (x * v k)) * D (v l)) := by
    intro k
    have hy : x * v k ∈ C := mul_mem hx (hv k)
    have a1 := hD.alg_mul hCi (p : O0 p) hy
    simp only [map_natCast] at a1
    rw [← hsv _ hy] at a1
    have a2 := hD.sum Finset.univ (fun l => v l * tr (u l * (x * v k)))
      (fun l _ => mul_mem (hv l) (hBC (htr _ (mul_mem (hu l) hy))))
    have a3 : IsInt (p := p) (∑ l, D (v l * tr (u l * (x * v k))) -
        ∑ l, tr (u l * (x * v k)) * D (v l)) := by
      rw [← Finset.sum_sub_distrib]
      refine int_sum _ _ fun l _ => ?_
      have ht : tr (u l * (x * v k)) ∈ C := hBC (htr _ (mul_mem (hu l) hy))
      exact int_congr (int_add (hD.2.1 _ (hv l) _ ht) (int_mul (hCi _ (hv l)) (hT k l))) (by ring)
    exact int_congr (int_add (int_add (int_neg a1) a2) a3) (by ring)
  have e2 : ∀ l, ∑ k, u k * (tr (u l * (x * v k)) * D (v l)) = (p : Ω) * (x * (u l * D (v l))) := by
    intro l
    have h := hsu (x * u l) (mul_mem hx (hu l))
    calc ∑ k, u k * (tr (u l * (x * v k)) * D (v l))
        = (∑ k, u k * tr (v k * (x * u l))) * D (v l) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [show u l * (x * v k) = v k * (x * u l) by ring]; ring
      _ = _ := by rw [h]; ring
  have e : ∑ k, u k * ∑ l, tr (u l * (x * v k)) * D (v l) = (p : Ω) * (x * ∑ l, u l * D (v l)) := by
    calc _ = ∑ l, ∑ k, u k * (tr (u l * (x * v k)) * D (v l)) := by
            simp_rw [Finset.mul_sum]; exact Finset.sum_comm
      _ = ∑ l, (p : Ω) * (x * (u l * D (v l))) := Finset.sum_congr rfl fun l _ => e2 l
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
  have s2 : IsInt (p := p) ((p : Ω) * ∑ k, u k * D (x * v k) - (p : Ω) * (x * ∑ l, u l * D (v l))) := by
    have a : IsInt (p := p) (∑ k, u k * ((p : Ω) * D (x * v k) - ∑ l, tr (u l * (x * v k)) * D (v l))) :=
      int_sum _ _ fun k _ => int_mul (hCi _ (hu k)) (s1 k)
    refine int_congr a ?_
    rw [← e, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have s3 : IsInt (p := p) (∑ k, u k * D (x * v k) - x * ∑ k, u k * D (v k) - (p : Ω) * D x) := by
    have a : IsInt (p := p) (∑ k, u k * (D (x * v k) - x * D (v k) - v k * D x)) :=
      int_sum _ _ fun k _ => int_mul (hCi _ (hu k)) (hD.2.1 x hx (v k) (hv k))
    refine int_congr a ?_
    rw [← huv, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  exact int_congr (int_sub s2 (int_mul (int_nat p) s3)) (by ring)

end GlobalTheory.KumDlog
end

