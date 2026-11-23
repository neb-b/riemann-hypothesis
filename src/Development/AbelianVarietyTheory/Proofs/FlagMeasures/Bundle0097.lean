module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIpowSmulOfSmulMem
section
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.DegCnt
open scoped Pointwise nonZeroDivisors

namespace GlobalTheory.RowStab

section Gen
variable {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def gen (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K) : V →ₗ[K] V :=
  LinearMap.id + ∑ b ∈ J, ((H.B.flip (e b)).smulRight (ρ b) - (H.B.flip (ρ b)).smulRight (e b) +
    ∑ a ∈ J, (c a b • H.B.flip (e b)).smulRight (e a))

theorem gen_apply (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K) (v : V) :
    gen H J e ρ c v = v + ∑ b ∈ J, (H.B v (e b) • ρ b - H.B v (ρ b) • e b +
      ∑ a ∈ J, (c a b * H.B v (e b)) • e a) := by
  simp [gen, LinearMap.sum_apply, mul_smul]

end Gen

section Ideal
variable {K : Type} [Field K] [NumberField K]

theorem ipow_mul_mem {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) {m n : ℤ} {x y : K} (hx : x ∈ ipow 𝔡 m)
    (hy : y ∈ ipow 𝔡 n) : x * y ∈ ipow 𝔡 (m + n) := by
  have h0 : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := by
    simpa using h𝔡
  unfold ipow at *
  rw [zpow_add₀ h0, FractionalIdeal.coe_mul]
  exact Submodule.mul_mem_mul hx hy

theorem one_mem_ipow_mul {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) (m : ℤ) :
    (1 : K) ∈ ipow 𝔡 m * ipow 𝔡 (-m) := by
  have h0 : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := by
    simpa using h𝔡
  unfold ipow
  rw [← FractionalIdeal.coe_mul, ← zpow_add₀ h0, add_neg_cancel, zpow_zero, FractionalIdeal.coe_one]
  exact Submodule.one_le.mp le_rfl

theorem ipow_zero (𝔡 : Ideal (𝓞 K)) : ipow 𝔡 0 = 1 := by
  simp [ipow]

theorem mem_ipow_of_mul {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) {m n : ℤ} {x : K}
    (h : ∀ t ∈ ipow 𝔡 (-m), t * x ∈ ipow 𝔡 n) : x ∈ ipow 𝔡 (m + n) := by
  have key : ∀ y ∈ ipow 𝔡 m * ipow 𝔡 (-m), y * x ∈ ipow 𝔡 (m + n) := by
    intro y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha t ht
      rw [mul_assoc]
      exact ipow_mul_mem h𝔡 ha (h t ht)
    · intro a b ha hb
      rw [add_mul]
      exact Submodule.add_mem _ ha hb
  simpa using key 1 (one_mem_ipow_mul h𝔡 m)

end Ideal

section Smul
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem smul_mem_of_mem_ipow_smul {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) {m : ℤ} {M : Submodule (𝓞 K) V} {v : V}
    (hv : v ∈ ipow 𝔡 m • M) {t : K} (ht : t ∈ ipow 𝔡 (-m)) : t • v ∈ M := by
  refine Submodule.smul_induction_on hv ?_ ?_
  · intro a ha n hn
    have h1 : t * a ∈ ipow 𝔡 0 := by
      simpa [add_comm] using ipow_mul_mem h𝔡 ht ha
    rw [ipow_zero] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.mp h1
    rw [smul_smul, ← ho, algebraMap_smul]
    exact M.smul_mem o hn
  · intro x y hx hy
    rw [smul_add]
    exact M.add_mem hx hy

theorem mem_ipow_smul_of_smul_mem {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) {m : ℤ} {M : Submodule (𝓞 K) V} {v : V}
    (h : ∀ t ∈ ipow 𝔡 (-m), t • v ∈ M) : v ∈ ipow 𝔡 m • M := by
  have key : ∀ y ∈ ipow 𝔡 m * ipow 𝔡 (-m), y • v ∈ ipow 𝔡 m • M := by
    intro y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha t ht
      rw [mul_smul]
      exact Submodule.smul_mem_smul ha (h t ht)
    · intro a b ha hb
      rw [add_smul]
      exact Submodule.add_mem _ ha hb
  simpa using key 1 (one_mem_ipow_mul h𝔡 m)

end Smul

section Star
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem star_integral (y : 𝓞 K) : ∃ y' : 𝓞 K, (y' : K) = star (y : K) := by
  have h : IsIntegral ℤ (star (y : K)) := by
    exact (RingOfIntegers.isIntegral_coe y).map ((starRingEnd K).toIntAlgHom)
  exact ⟨⟨star (y : K), h⟩, rfl⟩

theorem star_pow_mem {𝔡 : Ideal (𝓞 K)} (h𝔡s : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (k : ℕ) :
    ∀ x ∈ 𝔡 ^ k, ∃ y ∈ 𝔡 ^ k, (y : K) = star (x : K) := by
  induction k with
  | zero =>
    intro x _
    obtain ⟨y, hy⟩ := star_integral x
    exact ⟨y, by simp, hy⟩
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨a', ha', ea⟩ := ih a ha
      obtain ⟨b', hb', eb⟩ := h𝔡s b hb
      refine ⟨a' * b', ?_, ?_⟩
      · rw [pow_succ]; exact Submodule.mul_mem_mul ha' hb'
      · simp [ea, eb, star_mul']
    · rintro a b ⟨a', ha', ea⟩ ⟨b', hb', eb⟩
      exact ⟨a' + b', Submodule.add_mem _ ha' hb', by simp [ea, eb]⟩

theorem star_mem_one {x : K} (hx : x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    star x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.mem_one_iff] at *
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨y', hy'⟩ := star_integral y
  exact ⟨y', hy'⟩

theorem star_mem_ipow {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥)
    (h𝔡s : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℤ) {x : K} (hx : x ∈ ipow 𝔡 n) :
    star x ∈ ipow 𝔡 n := by
  have hA : ∀ k : ℕ, ∀ x : K, x ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ k) →
      star x ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ k) := by
    intro k x hx
    rw [← FractionalIdeal.coeIdeal_pow, FractionalIdeal.mem_coeIdeal] at *
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', e⟩ := star_pow_mem h𝔡s k y hy
    exact ⟨y', hy', e⟩
  unfold ipow at *
  rw [FractionalIdeal.mem_coe] at *
  rcases n with k | k
  · simp only [Int.ofNat_eq_coe, zpow_natCast] at *
    exact hA k x hx
  · have h0 : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ^ (k + 1) ≠ 0 := by
      apply pow_ne_zero; simpa using h𝔡
    rw [zpow_negSucc, FractionalIdeal.mem_inv_iff h0] at *
    intro y hy
    have := star_mem_one (hx (star y) (hA _ y hy))
    simpa [star_mul', mul_comm] using this

end Star

end GlobalTheory.RowStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexCongruenceSubgroupLeAbsNormPow
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.CongIndex


open scoped TensorProduct in
theorem quot_smul_top_span_card {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    (∃ v : Fin (Module.finrank R N) → N ⧸ (I • ⊤ : Submodule R N), Submodule.span R (Set.range v) = ⊤) ∧
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  refine ⟨⟨(TensorProduct.quotTensorEquivQuotSMul N I) ∘ b, ?_⟩, ?_⟩
  · have h1 : Submodule.span R (Set.range b) = ⊤ := by
      rw [← Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective, b.span_eq,
        Submodule.restrictScalars_top]
    have h2 := congrArg (Submodule.map (TensorProduct.quotTensorEquivQuotSMul N I).toLinearMap) h1
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h2
    rw [Set.range_comp]
    exact h2
  · rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv,
      Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

theorem card_hom_quot_smul_top {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Finite (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) ∧
    Nat.card (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) ≤ Nat.card (R ⧸ I) ^ (Module.finrank R N ^ 2) := by
  obtain ⟨⟨v, hv⟩, hc⟩ := quot_smul_top_span_card (R := R) (N := N) I
  have : Finite (N ⧸ (I • ⊤ : Submodule R N)) := Submodule.finite_quotient_smul I Module.Finite.fg_top
  have hk : ∀ f : N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N), (I • ⊤ : Submodule R N) ≤ LinearMap.ker f := by
    intro f
    refine Submodule.smul_le.2 fun a ha x _ => ?_
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (f x)
    rw [LinearMap.mem_ker, map_smul, ← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  let Φ : (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) → (Fin (Module.finrank R N) → N ⧸ (I • ⊤ : Submodule R N)) :=
    fun f i => Submodule.liftQ _ f (hk f) (v i)
  have hΦ : Function.Injective Φ := by
    intro f g hfg
    have : Submodule.liftQ _ f (hk f) = Submodule.liftQ _ g (hk g) :=
      LinearMap.ext_on_range hv fun i => congrFun hfg i
    ext x
    simpa using LinearMap.congr_fun this (Submodule.Quotient.mk x)
  refine ⟨Finite.of_injective Φ hΦ, (Nat.card_le_card_of_injective Φ hΦ).trans_eq ?_⟩
  rw [Nat.card_fun, hc, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin, ← pow_mul, sq]

theorem finrank_le_finrank_span {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V) :
    Module.finrank (𝓞 K) M ≤ Module.finrank K (Submodule.span K (M : Set V)) := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := M) le_rfl
  have h1 : LinearIndependent (𝓞 K) (M.subtype ∘ f) := hf.map' _ (Submodule.ker_subtype M)
  have h2 : LinearIndependent K (M.subtype ∘ f) := (LinearIndependent.iff_fractionRing (𝓞 K) K).1 h1
  let g : Fin (Module.finrank (𝓞 K) M) → Submodule.span K (M : Set V) :=
    fun i => ⟨f i, Submodule.subset_span (f i).2⟩
  have h3 : LinearIndependent K g :=
    LinearIndependent.of_comp (Submodule.span K (M : Set V)).subtype h2
  simpa using h3.fintype_card_le_finrank

theorem relIndex_le : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (G : Subgroup (V ≃ₗ[K] V)) (M : Submodule (𝓞 K) V) (𝔪 : Ideal (𝓞 K)) (B : Subgroup (V ≃ₗ[K] V)), M.FG → 𝔪 ≠ ⊥ → (∀ s ∈ G, s • M = M) → (∀ s ∈ G, (∀ x ∈ M, s x - x ∈ 𝔪 • M) → s ∈ B) → B.relIndex G ≠ 0 ∧ B.relIndex G ≤ Ideal.absNorm 𝔪 ^ (Module.finrank K (Submodule.span K (M : Set V)) ^ 2) := by
  intro K V _ _ _ _ _ _ _ G M 𝔪 B hM h𝔪 hG hB
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.2 hM
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.Flat (𝓞 K) M := inferInstance
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 K ⧸ 𝔪) := Ideal.finiteQuotientOfFreeOfNeBot 𝔪 h𝔪
  obtain ⟨hfin, hcard⟩ := card_hom_quot_smul_top (R := 𝓞 K) (N := M) 𝔪
  have hmem : ∀ s ∈ G, ∀ x ∈ M, s x ∈ M := by
    intro s hs x hx
    rw [← hG s hs]
    exact Submodule.smul_mem_pointwise_smul x s M hx
  have hmem' : ∀ s ∈ G, ∀ x ∈ 𝔪 • M, s x ∈ 𝔪 • M := by
    intro s hs x hx
    refine Submodule.smul_induction_on hx (fun a ha y hy => ?_) (fun y z hy hz => ?_)
    · rw [LinearMapClass.map_smul_of_tower]
      exact Submodule.smul_mem_smul ha (hmem s hs y hy)
    · rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  let ρ : G → (M →ₗ[𝓞 K] M) := fun s =>
    (((s : V ≃ₗ[K] V) : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict (hmem s s.2)
  let Φ : G → (M →ₗ[𝓞 K] M ⧸ (𝔪 • ⊤ : Submodule (𝓞 K) M)) := fun s => (Submodule.mkQ _).comp (ρ s)
  have hΦ : ∀ s t : G, Φ s = Φ t → s⁻¹ * t ∈ B.subgroupOf G := by
    intro s t hst
    refine hB _ (s⁻¹ * t).2 fun x hx => ?_
    have h1 : ρ t ⟨x, hx⟩ - ρ s ⟨x, hx⟩ ∈ (𝔪 • ⊤ : Submodule (𝓞 K) M) :=
      (Submodule.Quotient.eq _).1 (LinearMap.congr_fun hst ⟨x, hx⟩).symm
    have h2 : (t : V ≃ₗ[K] V) x - (s : V ≃ₗ[K] V) x ∈ 𝔪 • M := by
      have := Submodule.mem_map_of_mem (f := M.subtype) h1
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at this
      exact this
    have h3 := hmem' _ (s⁻¹).2 _ h2
    simpa using h3
  let Ψ : G ⧸ B.subgroupOf G → _ := fun q => Φ q.out
  have hΨ : Function.Injective Ψ := by
    intro q q' h
    rw [← q.out_eq, ← q'.out_eq]
    exact QuotientGroup.eq.2 (hΦ _ _ h)
  have : Finite (G ⧸ B.subgroupOf G) := Finite.of_injective Ψ hΨ
  refine ⟨Subgroup.index_ne_zero_of_finite, ?_⟩
  refine (Nat.card_le_card_of_injective Ψ hΨ).trans (hcard.trans ?_)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.pow_le_pow_right Nat.card_pos (Nat.pow_le_pow_left (finrank_le_finrank_span M) 2)

end GlobalTheory.CongIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexNeZero
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.Unimod

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_mul_mem {A : Submodule (𝓞 K) V} (hA : Submodule.span K (A : Set V) = ⊤) (x : V) :
    ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ A := by
  first
  | exact @_root_.GlobalTheory.IntMulIntegral.main
  | exact _root_.GlobalTheory.IntMulIntegral.main
  | (apply _root_.GlobalTheory.IntMulIntegral.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntMulIntegral.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntMulIntegral.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntMulIntegral.main ..)

theorem exists_mul_le {A : Submodule (𝓞 K) V} (hA : Submodule.span K (A : Set V) = ⊤)
    {B : Submodule (𝓞 K) V} (hB : B.FG) : ∃ N : ℤ, N ≠ 0 ∧ ∀ x ∈ B, N • x ∈ A := by
  first
  | exact @_root_.GlobalTheory.IntegerMultipleIntegral.exists_int_smul_le
  | exact _root_.GlobalTheory.IntegerMultipleIntegral.exists_int_smul_le
  | (apply _root_.GlobalTheory.IntegerMultipleIntegral.exists_int_smul_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegerMultipleIntegral.exists_int_smul_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegerMultipleIntegral.exists_int_smul_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegerMultipleIntegral.exists_int_smul_le ..)

theorem finite_between {Λ : Submodule (𝓞 K) V} (hΛ : Λ.FG) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    {M : Submodule (𝓞 K) V | (∀ x ∈ Λ, a • x ∈ M) ∧ ∀ x ∈ M, b • x ∈ Λ}.Finite := by
  haveI : Module.Finite (𝓞 K) Λ := Module.Finite.iff_fg.2 hΛ
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 K) Λ
  let P : Submodule ℤ Λ := LinearMap.range (LinearMap.lsmul ℤ Λ (b * a))
  haveI : Finite (Λ ⧸ P) := by
    refine Module.finite_of_fg_torsion _ ?_
    intro q
    obtain ⟨x, rfl⟩ := P.mkQ_surjective q
    refine ⟨⟨b * a, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hb ha)⟩, ?_⟩
    change (b * a) • P.mkQ x = 0
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  let f : Submodule (𝓞 K) V → Set (Λ ⧸ P) := fun M =>
    {q | ∃ x ∈ M, ∃ h : b • x ∈ Λ, P.mkQ ⟨b • x, h⟩ = q}
  have key : ∀ M M' : Submodule (𝓞 K) V, (∀ x ∈ M, b • x ∈ Λ) → (∀ x ∈ Λ, a • x ∈ M') →
      f M = f M' → M ≤ M' := by
    intro M M' hM hM' e x hx
    have : P.mkQ ⟨b • x, hM x hx⟩ ∈ f M' := e ▸ ⟨x, hx, hM x hx, rfl⟩
    obtain ⟨y, hy, hy', h⟩ := this
    obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).1 h
    have hz' : (b * a) • (z : V) = b • y - b • x := congrArg Subtype.val hz
    have h2 : (b : K) • (a • (z : V)) = (b : K) • (y - x) := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, ← mul_smul, hz', smul_sub]
    have h3 := smul_right_injective V (by exact_mod_cast hb : (b : K) ≠ 0) h2
    have h4 : x = y - a • (z : V) := by
      have h3' : a • (z : V) = y - x := h3
      rw [h3']; abel
    rw [h4]
    exact M'.sub_mem hy (hM' _ z.2)
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro M hM M' hM' e
  exact le_antisymm (key M M' hM.2 hM'.1 e) (key M' M hM'.2 hM.1 e.symm)

theorem mem_smul_iff (g : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (x : V) :
    x ∈ g • Λ ↔ g⁻¹ x ∈ Λ := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, by simp⟩

theorem isLattice_smul (g : V ≃ₗ[K] V) {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsFullLattice K Λ) :
    Submodule.IsFullLattice K (g • Λ) := by
  letI := hΛ
  refine { toIsLattice := ⟨hΛ.fg.map _, ?_⟩, span_eq_top := ?_ }
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · rw [Submodule.coe_pointwise_smul]
    change Submodule.span K ((g : V →ₗ[K] V) '' (Λ : Set V)) = ⊤
    rw [← Submodule.map_span, Submodule.IsFullLattice.span_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr g.surjective
theorem relIndex_ne_zero (G : Subgroup (V ≃ₗ[K] V)) {Λ Λ' : Submodule (𝓞 K) V}
    (hΛ : Submodule.IsFullLattice K Λ) (hΛ' : Submodule.IsFullLattice K Λ') :
    (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ).relIndex
      (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ') ≠ 0 := by
  letI := hΛ
  letI := hΛ'
  obtain ⟨a, ha, h₁⟩ := exists_mul_le (Submodule.IsFullLattice.span_eq_top (A := K) (M := Λ)) hΛ'.fg
  obtain ⟨b, hb, h₂⟩ := exists_mul_le (Submodule.IsFullLattice.span_eq_top (A := K) (M := Λ')) hΛ.fg
  set H := G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ' with hH
  have e : (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ).relIndex H = (MulAction.stabilizer H Λ).index := by
    rw [Subgroup.relIndex]
    congr 1
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨g.2.1, h⟩⟩
  rw [e, MulAction.index_stabilizer]
  refine Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self Λ) ?_
  refine (finite_between hΛ'.fg ha hb).subset ?_
  rintro _ ⟨g, rfl⟩
  have hg : (g : V ≃ₗ[K] V) • Λ' = Λ' := g.2.2
  have hg' : ∀ x, (g : V ≃ₗ[K] V)⁻¹ x ∈ Λ' ↔ x ∈ Λ' := fun x => by rw [← mem_smul_iff, hg]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · change a • x ∈ (g : V ≃ₗ[K] V) • Λ
    rw [mem_smul_iff, map_zsmul]
    exact h₁ _ ((hg' x).2 hx)
  · have hx' : x ∈ (g : V ≃ₗ[K] V) • Λ := hx
    rw [mem_smul_iff] at hx'
    rw [← hg', map_zsmul]
    exact h₂ _ hx'

theorem exists_den {s : V ≃ₗ[K] V} {n : ℕ} (hs : ((s : V →ₗ[K] V) - 1) ^ n = 0)
    {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsFullLattice K Λ) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ m : ℕ, ∀ x ∈ Λ, N • (s ^ m) x ∈ Λ := by
  let u : V →ₗ[K] V := (s : V →ₗ[K] V) - 1
  let B : Submodule (𝓞 K) V := ⨆ i : Fin (n + 1), Λ.map ((u ^ (i : ℕ)).restrictScalars (𝓞 K))
  have hB : B.FG := Submodule.fg_iSup _ fun i => hΛ.fg.map _
  have hm : ∀ i : ℕ, ∀ x ∈ Λ, (u ^ i) x ∈ B := by
    intro i x hx
    by_cases hi : i < n + 1
    · exact Submodule.mem_iSup_of_mem (⟨i, hi⟩ : Fin (n + 1)) ⟨x, hx, rfl⟩
    · rw [pow_eq_zero_of_le (by omega : n ≤ i) hs]
      exact B.zero_mem
  have hu : B ≤ B.comap (u.restrictScalars (𝓞 K)) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨x, hx, rfl⟩
    have := hm (i + 1) x hx
    rw [pow_succ'] at this
    exact this
  have hsB : ∀ x ∈ B, s x ∈ B := by
    intro x hx
    have h1 : u x ∈ B := hu hx
    have : s x = u x + x := by simp [u]
    rw [this]
    exact B.add_mem h1 hx
  have hp : ∀ m : ℕ, ∀ x ∈ Λ, (s ^ m) x ∈ B := by
    intro m x hx
    induction m with
    | zero => simpa using hm 0 x hx
    | succ m ih => rw [pow_succ']; exact hsB _ ih
  letI := hΛ
  obtain ⟨N, hN, h⟩ := exists_mul_le (Submodule.IsFullLattice.span_eq_top (A := K) (M := Λ)) hB
  exact ⟨N, hN, fun m x hx => h _ (hp m x hx)⟩

theorem inf_stab_smul {Γ X : Type} [Group Γ] [MulAction Γ X] (G : Subgroup Γ) {s : Γ} (hs : s ∈ G) (x : X) :
    G ⊓ MulAction.stabilizer Γ (s • x) = MulAut.conj s • (G ⊓ MulAction.stabilizer Γ x) := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨G.mul_mem (G.mul_mem (G.inv_mem hs) h1) hs, ?_⟩
    rw [mul_smul, mul_smul, h2, inv_smul_smul]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := G.mul_mem (G.mul_mem hs h1) (G.inv_mem hs)
      simpa [mul_assoc] using this
    · rw [mul_smul, mul_smul, inv_smul_eq_iff] at h2
      exact h2

theorem invVol_smul : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (G : Subgroup (V ≃ₗ[K] V)) (n : ℕ), (∀ s ∈ G, ((s : V →ₗ[K] V) - 1) ^ n = 0) → ∀ Λ Λ' : Submodule (𝓞 K) V, Submodule.IsFullLattice K Λ → Submodule.IsFullLattice K Λ' → (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ).relIndex (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ') ≠ 0 ∧ ∀ s ∈ G, GlobalTheory.HL.invVol (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ') (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) (s • Λ)) = GlobalTheory.HL.invVol (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ') (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ) := by
  intro K V _ _ _ _ _ _ _ G n hG Λ Λ' hΛ hΛ'
  refine ⟨relIndex_ne_zero G hΛ hΛ', fun s hs => ?_⟩
  let S : Submodule (𝓞 K) V → Subgroup (V ≃ₗ[K] V) := fun M =>
    G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) M
  have main : ∀ A B C : Submodule (𝓞 K) V, Submodule.IsFullLattice K A → Submodule.IsFullLattice K B →
      Submodule.IsFullLattice K C → _ := fun A B C hA hB hC =>
    GlobalTheory.HL.invVol_mul_pos_le_conj (S A) (S B) (S C) (relIndex_ne_zero G hA hB)
      (relIndex_ne_zero G hB hA) (relIndex_ne_zero G hA hC) (relIndex_ne_zero G hC hA)
  set d : ℝ := GlobalTheory.HL.invVol (S Λ) (S (s • Λ)) with hd
  have hdpos : 0 < d := (main Λ Λ (s • Λ) hΛ hΛ (isLattice_smul s hΛ)).2.1
  have hpow : ∀ m : ℕ, GlobalTheory.HL.invVol (S Λ) (S (s ^ m • Λ)) = d ^ m := by
    intro m
    induction m with
    | zero => simp [GlobalTheory.HL.invVol]
    | succ m ih =>
      have h1 := (main Λ (s • Λ) (s ^ (m + 1) • Λ) hΛ (isLattice_smul _ hΛ) (isLattice_smul _ hΛ)).1
      have h2 := (main Λ Λ (s ^ m • Λ) hΛ hΛ (isLattice_smul _ hΛ)).2.2.2 s
      have e1 : MulAut.conj s • S Λ = S (s • Λ) := (inf_stab_smul G hs Λ).symm
      have e2 : MulAut.conj s • S (s ^ m • Λ) = S (s ^ (m + 1) • Λ) := by
        rw [pow_succ', mul_smul]
        exact (inf_stab_smul G hs _).symm
      rw [e1, e2, ih] at h2
      rw [h1, h2, pow_succ']
  obtain ⟨b, hb, h₂⟩ := exists_den (hG s hs) hΛ
  obtain ⟨a, ha, h₁⟩ := exists_den (hG s⁻¹ (G.inv_mem hs)) hΛ
  have hfin := finite_between hΛ.fg ha hb
  have hmaps : ∀ m : ℕ, s ^ m • Λ ∈
      {M : Submodule (𝓞 K) V | (∀ x ∈ Λ, a • x ∈ M) ∧ ∀ x ∈ M, b • x ∈ Λ} := by
    intro m
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [mem_smul_iff, map_zsmul, ← inv_pow]
      exact h₁ m x hx
    · rw [mem_smul_iff] at hx
      simpa using h₂ m _ hx
  obtain ⟨i, j, hij, e⟩ := hfin.exists_lt_map_eq_of_forall_mem hmaps
  have hd1 : d = 1 := by
    have h : d ^ i = d ^ j := by rw [← hpow, ← hpow, e]
    by_contra hne
    exact hij.ne (pow_right_injective₀ hdpos hne h)
  have h := (main Λ' Λ (s • Λ) hΛ' hΛ (isLattice_smul s hΛ)).1
  rw [← hd, hd1, mul_one] at h
  exact h

end GlobalTheory.DegCnt.Unimod
end

