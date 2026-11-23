module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeftCosetsDoubleCosetInvEq
section
open MeasureTheory

namespace GlobalTheory

theorem card_leftCosets_doubleCoset_inv_eq : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (ν : Measure G) [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] (J : Subgroup G) (α : G) (R R' : Finset G), MeasurableSet (J : Set G) → ν J ≠ 0 → ν J ≠ ⊤ → (∀ γ ∈ R, ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * α * k₂) → (∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ J) → (∀ γ ∈ R', ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * α⁻¹ * k₂) → (∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * α⁻¹ * k₂) → ∃! γ, γ ∈ R' ∧ γ⁻¹ * x ∈ J) → R.card = R'.card := by
  intro G _ _ _ ν _ _ J α R R' hJ h0 htop hR hRu hR' hR'u
  set S : Set G := {x | ∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * α * k₂} with hS
  have hA : ∀ γ ∈ R, ∀ x, γ⁻¹ * x ∈ J → x ∈ S := by
    intro γ hγ x hx
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hR γ hγ
    exact ⟨k₁, h₁, k₂ * ((k₁ * α * k₂)⁻¹ * x), J.mul_mem h₂ hx, by group⟩
  have hB : ∀ γ ∈ R', ∀ x, x * γ ∈ J → x ∈ S := by
    intro γ hγ x hx
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hR' γ hγ
    exact ⟨x * (k₁ * α⁻¹ * k₂) * k₂⁻¹, J.mul_mem hx (J.inv_mem h₂), k₁⁻¹, J.inv_mem h₁, by group⟩
  have hBu : ∀ x ∈ S, ∃! γ, γ ∈ R' ∧ x * γ ∈ J := by
    rintro x ⟨k₁, h₁, k₂, h₂, hx⟩
    have := hR'u x⁻¹ ⟨k₂⁻¹, J.inv_mem h₂, k₁⁻¹, J.inv_mem h₁, by rw [hx]; group⟩
    simpa only [← mul_inv_rev, J.inv_mem_iff] using this
  have e1 : S = ⋃ γ ∈ R, (fun x => γ⁻¹ * x) ⁻¹' (J : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
    exact ⟨fun hx => (hRu x hx).exists, fun ⟨γ, h, h'⟩ => hA γ h x h'⟩
  have e2 : S = ⋃ γ ∈ R', (fun x => x * γ) ⁻¹' (J : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
    exact ⟨fun hx => (hBu x hx).exists, fun ⟨γ, h, h'⟩ => hB γ h x h'⟩
  have m1 : ν S = R.card * ν J := by
    rw [e1, measure_biUnion_finset]
    · simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul]
    · intro a ha b hb hab
      rw [Function.onFun, Set.disjoint_left]
      intro x hxa hxb
      exact hab ((hRu x (hA a ha x hxa)).unique ⟨ha, hxa⟩ ⟨hb, hxb⟩)
    · intro b _
      exact measurable_const_mul _ hJ
  have m2 : ν S = R'.card * ν J := by
    rw [e2, measure_biUnion_finset]
    · simp only [measure_preimage_mul_right, Finset.sum_const, nsmul_eq_mul]
    · intro a ha b hb hab
      rw [Function.onFun, Set.disjoint_left]
      intro x hxa hxb
      exact hab ((hBu x (hB a ha x hxa)).unique ⟨ha, hxa⟩ ⟨hb, hxb⟩)
    · intro b _
      exact measurable_mul_const _ hJ
  have := (ENNReal.mul_left_inj h0 htop).1 (m1.symm.trans m2)
  exact_mod_cast this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardQuotPrimeSmulEqCardKerMulPowFinrank
section
open CategoryTheory Limits

namespace GlobalTheory

theorem index_range_eq_card_ker_of_finite {D : Type} [AddCommGroup D] [Finite D] (f : D →+ D) :
    f.range.index = Nat.card f.ker := by
  have h1 := f.range.card_mul_index
  have h2 := f.ker.card_mul_index
  rw [AddSubgroup.index_ker] at h2
  have h3 : 0 < Nat.card f.range := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left h3
  rw [h1, mul_comm, h2]

theorem card_quot_smul_eq_of_equiv_prod {M D : Type} [AddCommGroup M] [AddCommGroup D] [Finite D]
    {n : ℕ} (e : M ≃+ (Fin n → ℤ) × D) (p : ℕ) (hp : p ≠ 0) :
    Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) *
        p ^ Module.finrank ℤ M := by
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  let f : D →+ D := zsmulAddGroupHom (p : ℤ)
  have hf : ∀ d, f d = (p : ℤ) • d := fun d => rfl
  have hrank : Module.finrank ℤ M = n := by
    rw [e.toIntLinearEquiv.finrank_eq]
    have hD : Module.rank ℤ (LinearMap.ker (LinearMap.fst ℤ (Fin n → ℤ) D)) = 0 := by
      rw [Module.rank_eq_zero_iff_isTorsion]
      intro x
      refine ⟨⟨(Nat.card D : ℤ), mem_nonZeroDivisors_of_ne_zero ?_⟩, ?_⟩
      · exact_mod_cast (Nat.card_pos (α := D)).ne'
      · have hx : x.1.1 = 0 := x.2
        apply Subtype.ext
        refine Prod.ext ?_ ?_
        · simp [Submonoid.smul_def, hx]
        · simp [Submonoid.smul_def]
    have : Module.rank ℤ ((Fin n → ℤ) × D) = n := by
      rw [← (LinearMap.fst ℤ (Fin n → ℤ) D).rank_range_add_rank_ker, hD,
        LinearMap.range_eq_top.2 LinearMap.fst_surjective]
      simp
    simp [Module.finrank, this]
  have hker : Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      Nat.card f.ker := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(e x.1).2, ?_⟩
        invFun := fun d => ⟨e.symm (0, d.1), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hx : (p : ℤ) • x.1 = 0 := x.2
      have := congrArg (fun y => (e y).2) hx
      simpa [hf] using this
    · have hd : (p : ℤ) • d.1 = 0 := d.2
      change (p : ℤ) • e.symm (0, d.1) = 0
      rw [← map_zsmul, Prod.smul_mk, hd, smul_zero]
      exact map_zero _
    · intro x
      have hx : (p : ℤ) • x.1 = 0 := x.2
      have h1 : (p : ℤ) • (e x.1).1 = 0 := by
        have := congrArg (fun y => (e y).1) hx
        simpa only [map_zsmul, map_zero, Prod.smul_fst, Prod.fst_zero] using this
      have h2 : (e x.1).1 = 0 := (smul_eq_zero.1 h1).resolve_left hp'
      apply Subtype.ext
      change e.symm (0, (e x.1).2) = x.1
      rw [← h2]
      exact e.symm_apply_apply _
    · intro d
      apply Subtype.ext
      simp
  have hrange : (LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))).toAddSubgroup =
      ((AddSubgroup.pi Set.univ fun _ : Fin n => AddSubgroup.zmultiples (p : ℤ)).prod
        f.range).comap e.toAddMonoidHom := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [AddSubgroup.mem_comap]
      change e ((p : ℤ) • y) ∈ _
      rw [map_zsmul]
      refine ⟨fun i _ => ⟨(e y).1 i, ?_⟩, ⟨(e y).2, rfl⟩⟩
      simp [mul_comm]
    · rintro ⟨h1, d, hd⟩
      have h1' : ∀ i, ∃ k : ℤ, k • (p : ℤ) = (e x).1 i := fun i => h1 i (Set.mem_univ i)
      choose k hk using h1'
      refine ⟨e.symm (k, d), ?_⟩
      change (p : ℤ) • e.symm (k, d) = x
      rw [← map_zsmul, AddEquiv.symm_apply_eq]
      refine Prod.ext (funext fun i => ?_) hd
      rw [← hk i]
      simp [mul_comm]
  have hq : Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      (LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))).toAddSubgroup.index := rfl
  rw [hq, hrange, AddSubgroup.index_comap_of_surjective _ e.surjective, AddSubgroup.index_prod,
    AddSubgroup.index_pi, index_range_eq_card_ker_of_finite, hker, hrank, mul_comm]
  simp [Int.index_zmultiples]

theorem card_quot_prime_smul_eq_card_ker_mul_pow_finrank (M : Type) [AddCommGroup M]
    [inst : Module ℤ M] [Module.Finite ℤ M] (p : ℕ) [Fact p.Prime] :
    Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) *
        p ^ Module.finrank ℤ M := by
  obtain rfl : inst = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  haveI : AddGroup.FG M := Module.Finite.iff_addGroup_fg.1 inferInstance
  obtain ⟨n, ι, _, q, hq, k, ⟨e⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  haveI : ∀ i, NeZero (q i ^ k i) := fun i => ⟨pow_ne_zero _ (hq i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (q i ^ k i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  exact card_quot_smul_eq_of_equiv_prod
    (e.trans ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).toAddEquiv.prodCongr (AddEquiv.refl _)))
    p (Fact.out : p.Prime).ne_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionBySetPowOfDivisibleNumberField
section
open NumberField

namespace GlobalTheory

open Submodule

theorem torsion_pow_card_succ {R : Type} [CommRing R] [IsDedekindDomain R]
    (M : Type) [AddCommGroup M] [Module R M] (w0 : Ideal R) (hmax : w0.IsMaximal) (hne : w0 ≠ ⊥)
    (hdiv : ∀ c : R, c ≠ 0 → Function.Surjective (fun g : M => c • g)) (j : ℕ) :
    Nat.card (torsionBySet R M ((w0 ^ (j + 1) : Ideal R) : Set R)) =
      Nat.card (torsionBySet R M ((w0 ^ j : Ideal R) : Set R)) *
        Nat.card (torsionBySet R M ((w0 : Ideal R) : Set R)) := by
  have hlt : w0 ^ 2 < w0 := by simpa using Ideal.pow_succ_lt_pow hne 1
  obtain ⟨c0, hc0, hc02⟩ := SetLike.exists_of_lt hlt
  have hdvd : w0 ∣ Ideal.span {c0} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hc0)
  obtain ⟨b, hb⟩ := hdvd
  have hbw : ¬ b ≤ w0 := by
    intro hle
    apply hc02
    have : Ideal.span {c0} ≤ w0 ^ 2 := by rw [hb, pow_two]; exact Ideal.mul_mono_right hle
    exact this (Ideal.subset_span rfl)
  have hbtop : b ⊔ w0 = ⊤ := by
    by_contra h
    exact hbw (le_sup_left.trans (hmax.eq_of_le h le_sup_right).symm.le)
  have hcop : ∀ n : ℕ, b ⊔ w0 ^ n = ⊤ := by
    intro n
    rw [← Ideal.isCoprime_iff_sup_eq]
    exact (Ideal.isCoprime_iff_sup_eq.mpr hbtop).pow_right
  have hc0ne : c0 ≠ 0 := by rintro rfl; exact hc02 (zero_mem _)

  let Tj := torsionBySet R M ((w0 ^ j : Ideal R) : Set R)
  let Tj1 := torsionBySet R M ((w0 ^ (j + 1) : Ideal R) : Set R)
  let T1 := torsionBySet R M ((w0 : Ideal R) : Set R)
  have hmapsto : ∀ x ∈ Tj1, c0 • x ∈ Tj := by
    intro x hx
    rw [mem_torsionBySet_iff] at hx ⊢
    rintro ⟨a, ha⟩
    have : a * c0 ∈ w0 ^ (j + 1) := by rw [pow_succ]; exact Ideal.mul_mem_mul ha hc0
    simpa [smul_smul] using hx ⟨_, this⟩
  let φ : Tj1 →ₗ[R] Tj :=
    { toFun := fun x => ⟨c0 • (x : M), hmapsto x x.2⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun r x => by ext; simp [smul_comm c0 r] }
  have hsurj : Function.Surjective φ := by
    rintro ⟨g, hg⟩
    obtain ⟨g', hg'⟩ := hdiv c0 hc0ne g
    simp only at hg'
    have h1 : (1 : R) ∈ b ⊔ w0 ^ (j + 1) := by rw [hcop]; trivial
    obtain ⟨v, hv, u, hu, huv⟩ := Submodule.mem_sup.mp h1
    have hmem : v • g' ∈ Tj1 := by
      rw [mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      have hav : a * v ∈ w0 ^ j * Ideal.span {c0} := by
        rw [hb, ← mul_assoc, ← pow_succ]
        exact Ideal.mul_mem_mul ha hv
      obtain ⟨z, hz, hzc⟩ := (Submodule.mem_mul_span_singleton).mp hav
      simp only
      rw [smul_smul, ← hzc, ← smul_smul, hg']
      exact (mem_torsionBySet_iff _ _).mp hg ⟨z, hz⟩
    refine ⟨⟨v • g', hmem⟩, ?_⟩
    ext
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_comm, hg']
    have hug : u • g = 0 := by
      have : u ∈ w0 ^ j := Ideal.pow_le_pow_right (Nat.le_succ j) hu
      exact (mem_torsionBySet_iff _ _).mp hg ⟨u, this⟩
    have : v = 1 - u := by rw [← huv]; ring
    rw [this, sub_smul, one_smul, hug, sub_zero]
  have hsub : T1 ≤ Tj1 := torsionBySet_le_torsionBySet_of_subset (by
    intro a ha
    exact Ideal.pow_le_self (Nat.succ_ne_zero j) ha)
  have hker : ∀ x : Tj1, x ∈ LinearMap.ker φ ↔ (x : M) ∈ T1 := by
    intro x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx
      have hx' : c0 • (x : M) = 0 := by
        have := congrArg Subtype.val hx
        simpa [φ] using this
      rw [mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      have hw : w0 ≤ Ideal.span {c0} ⊔ w0 ^ (j + 1) := by
        have e : w0 * (b ⊔ w0 ^ j) = Ideal.span {c0} ⊔ w0 ^ (j + 1) := by
          rw [Ideal.mul_sup, ← hb, ← pow_succ']
        rw [hcop, Ideal.mul_top] at e
        exact e.le
      obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp (hw ha)
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hs
      have key : (r * c0 + t) • (x : M) = 0 := by
        rw [add_smul, mul_smul, hx', smul_zero, zero_add]
        exact (mem_torsionBySet_iff _ _).mp x.2 ⟨t, ht⟩
      rwa [hst] at key
    · intro hx
      ext
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, ZeroMemClass.coe_zero]
      exact (mem_torsionBySet_iff _ _).mp hx ⟨c0, hc0⟩
  have e1 : Nat.card (Tj1 ⧸ LinearMap.ker φ) = Nat.card Tj :=
    Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv
  have e2 : Nat.card (LinearMap.ker φ) = Nat.card T1 :=
    Nat.card_congr
      { toFun := fun x => ⟨(x.1 : M), (hker x.1).mp x.2⟩
        invFun := fun y => ⟨⟨y.1, hsub y.2⟩, (hker _).mpr y.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ), e1, e2, mul_comm]

theorem torsion_pow_card (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M]
    [Module (𝓞 F) M] (w0 : Ideal (𝓞 F)) (h : ℕ) :
    w0.IsMaximal → w0 ≠ ⊥ → (∀ c : 𝓞 F, c ≠ 0 → Function.Surjective (fun g : M => c • g)) →
    Nat.card (Submodule.torsionBySet (𝓞 F) M (w0 : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ w0) ^ h →
    ∀ j : ℕ, Nat.card (Submodule.torsionBySet (𝓞 F) M ((w0 ^ j : Ideal (𝓞 F)) : Set (𝓞 F))) =
      Nat.card (𝓞 F ⧸ w0) ^ (j * h) := by
  intro hmax hne hdiv h1 j
  induction j with
  | zero =>
    simp only [pow_zero, zero_mul]
    have : torsionBySet (𝓞 F) M ((⊤ : Ideal (𝓞 F)) : Set (𝓞 F)) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [mem_torsionBySet_iff] at hx
      simpa using hx ⟨1, trivial⟩
    rw [Ideal.one_eq_top, this]
    simp
  | succ n ih =>
    rw [torsion_pow_card_succ M w0 hmax hne hdiv n, ih, h1, ← pow_add]
    ring_nf

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardZmodTensorEqCardQuotPrimeMultiples
section
open CategoryTheory Limits

namespace GlobalTheory

theorem ideal_span_natCast_smul_top_eq_range (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ) :
    (Ideal.span {(p : ℤ)}) • (⊤ : Submodule ℤ M) =
      LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M)) := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  simp [Submodule.mem_smul_pointwise_iff_exists, Nat.cast_smul_eq_nsmul]

noncomputable def intQuotSpanNatLinearEquivZMod (p : ℕ) :
    (ℤ ⧸ Ideal.span {(p : ℤ)}) ≃ₗ[ℤ] ZMod p :=
  LinearEquiv.ofBijective (Int.quotientSpanNatEquivZMod p).toRingHom.toIntAlgHom.toLinearMap
    (Int.quotientSpanNatEquivZMod p).bijective

theorem card_zmod_tensor_eq_card_quot (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ) :
    Nat.card (TensorProduct ℤ (ZMod p) M) =
      Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) := by
  rw [← Nat.card_congr ((intQuotSpanNatLinearEquivZMod p).rTensor M).toEquiv,
    Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul M (Ideal.span {(p : ℤ)})).toEquiv,
    ideal_span_natCast_smul_top_eq_range]

theorem card_zmod_tensor_eq_card_quot' : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ),
    Nat.card (TensorProduct ℤ (ZMod p) M) =
      Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) :=
  fun M _ _ p => card_zmod_tensor_eq_card_quot M p

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
section
noncomputable section
open scoped TensorProduct

namespace GlobalTheory.LKInvGood

def locOrder (ℓ : ℕ) [Fact ℓ.Prime] {B : Type} [Ring B] [Algebra ℚ B] (OB : Subring B) :
    Subalgebra ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B) :=
  Algebra.adjoin ℤ_[ℓ] ((fun b : B => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b) '' (OB : Set B))

def cenOrder (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F] [NumberField F] :
    Subalgebra ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] F) :=
  Algebra.adjoin ℤ_[ℓ] (Set.range fun a : NumberField.RingOfIntegers F => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (a : F))

def cenMap (ℓ : ℕ) [Fact ℓ.Prime] (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] : ℚ_[ℓ] ⊗[ℚ] F →ₐ[ℚ_[ℓ]] ℚ_[ℓ] ⊗[ℚ] B :=
  Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) ((Algebra.ofId F B).restrictScalars ℚ)

def CentreCompat (ℓ : ℕ) [Fact ℓ.Prime] {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (OB : Subring B) {n : ℕ}
    (ψ : locOrder ℓ OB ≃ₐ[ℤ_[ℓ]] Matrix (Fin n) (Fin n) (cenOrder ℓ F)) : Prop :=
  ∀ a : cenOrder ℓ F, ∃ h : cenMap ℓ F B (a : ℚ_[ℓ] ⊗[ℚ] F) ∈ locOrder ℓ OB,
    ψ ⟨_, h⟩ = Matrix.scalar (Fin n) a

end GlobalTheory.LKInvGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDvdPowOfAevalEqZero
section
open Polynomial

namespace GlobalTheory.SepCharpoly

theorem charpoly_dvd_pow_of_aeval_eq_zero {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (p : R[X]) (hp : aeval M p = 0) : M.charpoly ∣ p ^ Fintype.card n := by
  set a : Matrix n n R[X] := algebraMap R[X] (Matrix n n R[X]) X with ha_def
  set b : Matrix n n R[X] := (Algebra.ofId R R[X]).mapMatrix M with hb_def
  have hab : Commute a b := Algebra.commutes X b
  have key : ∀ q : R[X], ∃ H, (a - b) * H = aeval a q - aeval b q := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨H1, h1⟩ := hp
      obtain ⟨H2, h2⟩ := hq
      exact ⟨H1 + H2, by rw [mul_add, h1, h2, map_add (f := _), map_add (f := _)]; abel⟩
    | monomial k c =>
      refine ⟨algebraMap R (Matrix n n R[X]) c * ∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i), ?_⟩
      rw [aeval_monomial, aeval_monomial, ← mul_assoc, ← Algebra.commutes, mul_assoc, hab.mul_geom_sum₂,
        mul_sub]
  obtain ⟨H, hH⟩ := key p
  have hb : aeval b p = 0 := by
    rw [hb_def, aeval_algHom_apply, hp, map_zero]
  have ha : aeval a p = algebraMap R[X] (Matrix n n R[X]) p := by
    rw [ha_def, aeval_algebraMap_apply, aeval_X_left_apply]
  have hch : (a - b).det = M.charpoly := rfl
  refine ⟨H.det, ?_⟩
  rw [← hch, ← Matrix.det_mul, hH, hb, sub_zero, ha, Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal]
  simp

theorem not_separable_charpoly : ∀ (F L C : Type) [Field F] [Field L] [Algebra F L] [Ring C] [Algebra F C]
    [FiniteDimensional F C] (n : ℕ) (ι : C →ₐ[F] Matrix (Fin n) (Fin n) L) (y : C),
    ((minpoly F y).natDegree < n ∨ ((minpoly F y).natDegree = n ∧ ¬ (minpoly F y).Separable)) →
      ¬ (ι y).charpoly.Separable := by
  intro F L C _ _ _ _ _ _ n ι y h hc
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  have hpm : (minpoly F y).Monic := minpoly.monic hyi
  have h1 : aeval (ι y) ((minpoly F y).map (algebraMap F L)) = 0 := by
    rw [aeval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]
  have h2 : minpoly L (ι y) ∣ (minpoly F y).map (algebraMap F L) := minpoly.dvd L _ h1
  have h3 : (ι y).charpoly ∣ (minpoly L (ι y)) ^ Fintype.card (Fin n) :=
    charpoly_dvd_pow_of_aeval_eq_zero _ _ (minpoly.aeval L _)
  have h4 : (ι y).charpoly ∣ minpoly L (ι y) := hc.squarefree.isRadical _ _ h3
  have h5 := h4.trans h2
  have hmm : ((minpoly F y).map (algebraMap F L)).Monic := hpm.map _
  have hdc : (ι y).charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hdm : ((minpoly F y).map (algebraMap F L)).natDegree = (minpoly F y).natDegree := natDegree_map _
  rcases h with h | ⟨h, hns⟩
  · have := natDegree_le_of_dvd h5 hmm.ne_zero
    omega
  · have e := eq_of_monic_of_dvd_of_natDegree_le (Matrix.charpoly_monic _) hmm h5 (by omega)
    rw [← e] at hc
    exact hns ((separable_map (algebraMap F L)).mp hc)

end GlobalTheory.SepCharpoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqPowOfIrreducible
section
open Polynomial

namespace GlobalTheory.CharpolyPowIrred

theorem charpoly_dvd_pow_of_aeval {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (G : K[X]) (hG : aeval M G = 0) :
    M.charpoly ∣ G ^ Fintype.card ι := by
  classical
  by_cases h0 : G = 0
  · subst h0
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
    · have : M.charpoly = 1 := by
        apply Polynomial.eq_one_of_monic_natDegree_zero M.charpoly_monic
        rw [Matrix.charpoly_natDegree_eq_dim, h]
      rw [this, h, pow_zero]
    · rw [zero_pow h.ne']
      exact dvd_zero _
  let Ω := AlgebraicClosure K
  let f := algebraMap K Ω
  rw [← Polynomial.map_dvd_map' f, Polynomial.map_pow, ← Matrix.charpoly_map]
  set N := M.map f with hNdef
  have hN : aeval N (G.map f) = 0 := by
    rw [aeval_map_algebraMap]
    have := congrArg (AlgHom.mapMatrix (m := ι) (Algebra.ofId K Ω)) hG
    rw [← aeval_algHom_apply, map_zero] at this
    exact this
  have hG0 : G.map f ≠ 0 := Polynomial.map_ne_zero h0
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots N.charpoly_monic.ne_zero ?_
  rw [roots_pow, Multiset.le_iff_count]
  intro μ
  rw [Multiset.count_nsmul]
  by_cases hμ : μ ∈ N.charpoly.roots
  · have h1 : μ ∈ spectrum Ω N := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      exact isRoot_of_mem_roots hμ
    have h2 := spectrum.subset_polynomial_aeval N (G.map f) ⟨μ, h1, rfl⟩
    rw [hN] at h2
    have h3 : (G.map f).eval μ = 0 := by
      by_contra hne
      exact (spectrum.mem_iff.1 h2)
        (by simpa using (IsUnit.mk0 _ hne).map (algebraMap Ω (Matrix ι ι Ω)))
    have h4 : 1 ≤ (G.map f).roots.count μ :=
      Multiset.one_le_count_iff_mem.2 ((mem_roots hG0).2 h3)
    calc N.charpoly.roots.count μ ≤ Multiset.card N.charpoly.roots := Multiset.count_le_card _ _
      _ ≤ N.charpoly.natDegree := card_roots' _
      _ = Fintype.card ι := Matrix.charpoly_natDegree_eq_dim N
      _ ≤ Fintype.card ι * (G.map f).roots.count μ := Nat.le_mul_of_pos_right _ h4
  · rw [Multiset.count_eq_zero.2 hμ]
    exact Nat.zero_le _

end GlobalTheory.CharpolyPowIrred
end

