module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IdxAbs
section
noncomputable section

namespace PI.LocMassTypW

open MeasureTheory

theorem idx_abs {G V : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure G) [μ.IsMulLeftInvariant] (ν : Measure V) [ν.IsAddLeftInvariant]
    (K : Subgroup G) (hK : MeasurableSet (K : Set G)) (B : AddSubgroup V)
    (hB : MeasurableSet (B : Set V)) [Countable (V ⧸ B)] (N : Set G) (C : Set V) (φ : G → V)
    (hNK : ∀ x ∈ N, ∀ k ∈ K, x * k ∈ N) (hCB : ∀ u ∈ C, ∀ b ∈ B, u + b ∈ C)
    (hφ : ∀ x ∈ N, φ x ∈ C) (hco : ∀ x ∈ N, ∀ y ∈ N, x⁻¹ * y ∈ K ↔ -φ x + φ y ∈ B)
    (hsur : ∀ u ∈ C, ∃ x ∈ N, -φ x + u ∈ B) :
    μ N * ν B = μ K * ν C := by
  classical
  have hI : ∀ q : {q : V ⧸ B | ∃ x ∈ N, (QuotientAddGroup.mk (φ x) : V ⧸ B) = q},
      ∃ x ∈ N, (QuotientAddGroup.mk (φ x) : V ⧸ B) = q := fun q => q.2
  choose x hxN hxq using hI
  have hmk : ∀ a b : V, -a + b ∈ B ↔ (QuotientAddGroup.mk a : V ⧸ B) = QuotientAddGroup.mk b :=
    fun a b => QuotientAddGroup.eq.symm
  have hC : C = ⋃ q, (fun v => -φ (x q) + v) ⁻¹' (B : Set V) := by
    ext v
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hv
      obtain ⟨y, hy, hyB⟩ := hsur v hv
      refine ⟨⟨QuotientAddGroup.mk (φ y), y, hy, rfl⟩, ?_⟩
      rw [hmk] at hyB ⊢
      rw [hxq]
      exact hyB
    · rintro ⟨q, hq⟩
      have hc := hCB _ (hφ _ (hxN q)) _ hq
      simpa using hc
  have hN : N = ⋃ q, (fun y => (x q)⁻¹ * y) ⁻¹' (K : Set G) := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hy
      refine ⟨⟨QuotientAddGroup.mk (φ y), y, hy, rfl⟩, ?_⟩
      rw [hco _ (hxN _) _ hy, hmk, hxq]
    · rintro ⟨q, hq⟩
      have hc := hNK _ (hxN q) _ hq
      simpa using hc
  have hdC : Pairwise (Function.onFun Disjoint fun q => (fun v => -φ (x q) + v) ⁻¹' (B : Set V)) := by
    intro q q' hqq
    rw [Function.onFun, Set.disjoint_left]
    intro v h1 h2
    apply hqq
    apply Subtype.ext
    simp only [Set.mem_preimage, SetLike.mem_coe, hmk] at h1 h2
    rw [← hxq q, ← hxq q', h1, h2]
  have hdN : Pairwise (Function.onFun Disjoint fun q => (fun y => (x q)⁻¹ * y) ⁻¹' (K : Set G)) := by
    intro q q' hqq
    rw [Function.onFun, Set.disjoint_left]
    intro y h1 h2
    apply hqq
    apply Subtype.ext
    simp only [Set.mem_preimage, SetLike.mem_coe] at h1 h2
    have hy : y ∈ N := by simpa using hNK _ (hxN q) _ h1
    rw [hco _ (hxN q) _ hy, hmk] at h1
    rw [hco _ (hxN q') _ hy, hmk] at h2
    rw [← hxq q, ← hxq q', h1, h2]
  have e1 : μ N = ∑' q : {q : V ⧸ B | ∃ x ∈ N, (QuotientAddGroup.mk (φ x) : V ⧸ B) = q}, μ K := by
    conv_lhs => rw [hN]
    rw [measure_iUnion hdN fun q => (measurable_const_mul _) hK]
    exact tsum_congr fun q => measure_preimage_mul μ _ _
  have e2 : ν C = ∑' q : {q : V ⧸ B | ∃ x ∈ N, (QuotientAddGroup.mk (φ x) : V ⧸ B) = q}, ν B := by
    rw [hC, measure_iUnion hdC fun q => (measurable_const_add _) hB]
    exact tsum_congr fun q => measure_preimage_add ν _ _
  rw [e1, e2, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]

end PI.LocMassTypW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.LatBasis
section
noncomputable section

namespace PI.LocMassTypL

open NumberField IsDedekindDomain

theorem lat_basis {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (L : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F)) (hfg : L.FG)
    (hsp : Submodule.span (v.adicCompletion F) (L : Set (Fin n → v.adicCompletion F)) = ⊤) :
    ∃ A : Matrix (Fin n) (Fin n) (v.adicCompletion F), IsUnit A ∧
      ∀ y, y ∈ L ↔ ∃ c : Fin n → v.adicCompletion F, (∀ i, c i ∈ v.adicCompletionIntegers F) ∧
        y = A.mulVec c := by
  classical
  haveI : Module.Finite (v.adicCompletionIntegers F) L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free (v.adicCompletionIntegers F) L := Module.free_of_finite_type_torsion_free'
  obtain ⟨ι, hιf, b, hb⟩ : ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι (v.adicCompletionIntegers F) L), True :=
    ⟨_, inferInstance, Module.Free.chooseBasis (v.adicCompletionIntegers F) L, trivial⟩
  obtain ⟨w, hw⟩ : ∃ w : ι → (Fin n → v.adicCompletion F), w = fun i => (b i : Fin n → v.adicCompletion F) :=
    ⟨_, rfl⟩
  have hsmul : ∀ (o : v.adicCompletionIntegers F) (x : Fin n → v.adicCompletion F),
      o • x = (o : v.adicCompletion F) • x := fun o x => rfl
  have hliO : LinearIndependent (v.adicCompletionIntegers F) w := by
    rw [hw]
    exact b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliK : LinearIndependent (v.adicCompletion F) w :=
    (LinearIndependent.iff_fractionRing (v.adicCompletionIntegers F) (v.adicCompletion F)).mp hliO
  have hspanO : Submodule.span (v.adicCompletionIntegers F) (Set.range w) = L := by
    have h1 := congrArg (Submodule.map L.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h1
    rw [hw]
    exact h1
  have hspK : ⊤ ≤ Submodule.span (v.adicCompletion F) (Set.range w) := by
    rw [← hsp, Submodule.span_le]
    intro y hy
    rw [← hspanO] at hy
    exact Submodule.span_le_restrictScalars (v.adicCompletionIntegers F) (v.adicCompletion F) _ hy
  let bK : Module.Basis ι (v.adicCompletion F) (Fin n → v.adicCompletion F) := Module.Basis.mk hliK hspK
  have hcard : Fintype.card ι = n := by
    have h1 := Module.finrank_eq_card_basis bK
    rw [Module.finrank_fin_fun] at h1
    exact h1.symm
  let e : Fin n ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  have hAv : ∀ c : Fin n → v.adicCompletion F,
      (Matrix.of fun i j => w (e j) i).mulVec c = ∑ j, c j • w (e j) := by
    intro c
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  refine ⟨Matrix.of fun i j => w (e j) i, ?_, ?_⟩
  · have hA : (Matrix.of fun i j => w (e j) i) = (Pi.basisFun (v.adicCompletion F) (Fin n)).toMatrix (bK.reindex e.symm) := by
      refine Matrix.ext fun i j => ?_
      simp [Module.Basis.toMatrix_apply, Module.Basis.reindex_apply, bK, Module.Basis.mk_apply]
    rw [hA]
    letI := (Pi.basisFun (v.adicCompletion F) (Fin n)).invertibleToMatrix (bK.reindex e.symm)
    exact isUnit_of_invertible _
  · intro y
    constructor
    · intro hy
      refine ⟨fun j => (b.repr ⟨y, hy⟩ (e j) : v.adicCompletion F), fun j => (b.repr ⟨y, hy⟩ (e j)).2, ?_⟩
      rw [hAv]
      have h1 := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
      rw [Submodule.coe_sum] at h1
      rw [← Equiv.sum_comp e] at h1
      refine (show y = _ from h1.symm).trans ?_
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Submodule.coe_smul, hsmul, hw]
    · rintro ⟨c, hc, rfl⟩
      rw [hAv, ← hspanO]
      refine Submodule.sum_mem _ (fun j _ => ?_)
      have : c j • w (e j) = (⟨c j, hc j⟩ : v.adicCompletionIntegers F) • w (e j) := by rw [hsmul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e j, rfl⟩)

end PI.LocMassTypL
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.WCoreDef
section
noncomputable section

namespace PI.LocMassTypW

open Matrix

def WCore : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (n m : ℕ) (A0 A B0 B : Matrix (Fin n) (Fin m) O),
    (∃ L : Matrix (Fin m) (Fin n) O, L * A0 = 1) → (∃ L : Matrix (Fin m) (Fin n) O, L * A = 1) →
    (∃ L : Matrix (Fin m) (Fin n) O, L * B0 = 1) → (∃ L : Matrix (Fin m) (Fin n) O, L * B = 1) →
    A0ᵀ * B0 = Aᵀ * B →
    ∃ k : Matrix (Fin n) (Fin n) O, IsUnit k ∧ k * A0 = A ∧ kᵀ * B = B0

end PI.LocMassTypW
end
end

