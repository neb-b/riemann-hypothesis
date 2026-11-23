module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0044

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenIsCompactPrincipal
section
open ValuativeRel Matrix
open scoped Topology

namespace GlobalTheory.CompanionTheory.PrincipalCongruence

variable {k : Type*} [Field k] [ValuativeRel k]

theorem inv_congr {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n k)
    (hAB : A * B = 1) {t : k} (ht : valuation k t < 1)
    (hA : ∀ i j, valuation k (A i j - (1 : Matrix n n k) i j) ≤ valuation k t) :
    ∀ i j, valuation k (B i j - (1 : Matrix n n k) i j) ≤ valuation k t := by
  by_contra h
  push_neg at h
  obtain ⟨i₁, j₁, h₁⟩ := h
  haveI : Nonempty (n × n) := ⟨(i₁, j₁)⟩
  obtain ⟨⟨i₀, j₀⟩, hm⟩ := Finite.exists_max
    (fun p : n × n => valuation k (B p.1 p.2 - (1 : Matrix n n k) p.1 p.2))
  have hm' : ∀ l j, valuation k (B l j - (1 : Matrix n n k) l j) ≤
      valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) := fun l j => hm (l, j)
  have hM : valuation k t < valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) :=
    h₁.trans_le (hm' i₁ j₁)
  have hM0 : 0 < valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) :=
    lt_of_le_of_lt zero_le' hM
  have hmat : (A - 1) * (B - 1) = -(A - 1) - (B - 1) := by
    simp only [sub_mul, mul_sub, hAB, one_mul, mul_one]
    abel
  have key : B i₀ j₀ - (1 : Matrix n n k) i₀ j₀ = -(A i₀ j₀ - (1 : Matrix n n k) i₀ j₀) -
      ∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) * (B l j₀ - (1 : Matrix n n k) l j₀) := by
    have := congrFun (congrFun hmat i₀) j₀
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply] at this
    rw [this]
    ring
  have hsum : valuation k (∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) *
      (B l j₀ - (1 : Matrix n n k) l j₀)) ≤
      valuation k t * valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) := by
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hA i₀ l) (hm' l j₀)
  have hlt : valuation k t * valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) <
      valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) :=
    mul_lt_of_lt_one_left hM0 ht
  have hle := Valuation.map_sub (valuation k) (-(A i₀ j₀ - (1 : Matrix n n k) i₀ j₀))
    (∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) * (B l j₀ - (1 : Matrix n n k) l j₀))
  rw [← key, Valuation.map_neg] at hle
  rcases le_max_iff.mp hle with h | h
  · exact absurd ((h.trans (hA i₀ j₀))) (not_le.mpr hM)
  · exact absurd (h.trans hsum) (not_le.mpr hlt)

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def congSet (n : Type*) [DecidableEq n] (t : k) : Set (Matrix n n k) :=
  {A | ∀ i j, valuation k (A i j - (1 : Matrix n n k) i j) ≤ valuation k t}

theorem isOpen_congSet (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0) :
    IsOpen (congSet n t) := by
  have h : congSet n t = ⋂ i, ⋂ j, (fun A : Matrix n n k => A i j - (1 : Matrix n n k) i j) ⁻¹'
      GlobalTheory.SplitWeil.cball (Units.mk0 t ht) := by
    ext A
    simp [congSet, GlobalTheory.SplitWeil.cball]
  rw [h]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (GlobalTheory.SplitWeil.isOpen_cball _).preimage
    ((continuous_id.matrix_elem i j).sub continuous_const)

theorem isCompact_congSet (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0) :
    IsCompact (congSet n t) := by
  have h : congSet n t = Set.pi Set.univ fun i => Set.pi Set.univ fun j =>
      (fun x : k => x + (1 : Matrix n n k) i j) '' GlobalTheory.SplitWeil.cball (Units.mk0 t ht) := by
    ext A
    constructor
    · intro hA i _ j _
      exact ⟨A i j - (1 : Matrix n n k) i j, hA i j, by simp⟩
    · intro hA i j
      obtain ⟨x, hx, hxA⟩ := hA i (Set.mem_univ _) j (Set.mem_univ _)
      have hx' : A i j - (1 : Matrix n n k) i j = x := by
        rw [← hxA]
        simp
      rw [hx']
      exact hx
  rw [h]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    (GlobalTheory.SplitWeil.isCompact_cball _).image (continuous_id.add continuous_const)

def congGL (n : Type*) [Fintype n] [DecidableEq n] (t : k) : Set (GL n k) :=
  {g | (g : Matrix n n k) ∈ congSet n t}

theorem isOpen_congGL (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0) :
    IsOpen (congGL n t) :=
  (isOpen_congSet n ht).preimage Units.continuous_val

theorem isCompact_congGL (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0)
    (ht1 : valuation k t < 1) : IsCompact (congGL n t) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  have hc : IsCompact ((congSet n t ×ˢ (MulOpposite.op '' congSet n t)) ∩
      {p : Matrix n n k × (Matrix n n k)ᵐᵒᵖ |
        p.1 * p.2.unop = 1 ∧ p.2.unop * p.1 = 1}) := by
    refine ((isCompact_congSet n ht).prod
      ((isCompact_congSet n ht).image MulOpposite.continuous_op)).inter_right ?_
    have hu : Continuous fun p : Matrix n n k × (Matrix n n k)ᵐᵒᵖ => p.2.unop :=
      MulOpposite.continuous_unop.comp continuous_snd
    exact (isClosed_eq (continuous_fst.matrix_mul hu) continuous_const).inter
      (isClosed_eq (hu.matrix_mul continuous_fst) continuous_const)
  convert hc using 1
  ext ⟨A, B⟩
  constructor
  · rintro ⟨g, hg, hgp⟩
    simp only [Units.embedProduct_apply, Prod.mk.injEq] at hgp
    obtain ⟨rfl, rfl⟩ := hgp
    refine ⟨⟨hg, _, inv_congr (g : Matrix n n k) _ g.mul_inv ht1 hg, rfl⟩, ?_⟩
    exact ⟨g.mul_inv, g.inv_mul⟩
  · rintro ⟨⟨hA, -⟩, h₁, h₂⟩
    refine ⟨⟨A, B.unop, h₁, h₂⟩, hA, ?_⟩
    simp [Units.embedProduct_apply]

theorem isOpen_isCompact_principal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (t : k), t ≠ 0 → ValuativeRel.valuation k (t) < 1 →
    IsOpen {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
        ValuativeRel.valuation k (t)} ∧
    IsCompact {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
        ValuativeRel.valuation k (t)} :=
  fun _ _ _ _ _ N _ ht ht1 => ⟨isOpen_congGL (Fin N) ht, isCompact_congGL (Fin N) ht ht1⟩

end GlobalTheory.CompanionTheory.PrincipalCongruence
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionStatement
section
@[expose] public section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.Jp.Iw

section Ops

variable {O L ι : Type} [CommRing O] [Field L] [Algebra O L] [Fintype ι] [DecidableEq ι]

def admitted (O : Type) [CommRing O] [Algebra O L] (T : Finset ι) (k : GL ι L) : Prop :=
  (∃ κ : GL ι O, Matrix.GeneralLinearGroup.map (algebraMap O L) κ = k) ∧
    ∀ v : ι → L, (∀ i ∈ T, v i = 0) → v ᵥ* k.1 = v

lemma admitted.one (T : Finset ι) : admitted O T (1 : GL ι L) :=
  ⟨⟨1, map_one _⟩, fun v _ => by simp⟩

lemma admitted.mul {T : Finset ι} {k k' : GL ι L} (h : admitted O T k) (h' : admitted O T k') : admitted O T (k * k') := by
  obtain ⟨⟨κ, rfl⟩, f⟩ := h
  obtain ⟨⟨κ', rfl⟩, f'⟩ := h'
  refine ⟨⟨κ * κ', map_mul _ _ _⟩, fun v hv => ?_⟩
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, f v hv, f' v hv]

lemma exists_transv {T : Finset ι} {i j : ι} (hi : i ∈ T) (hij : i ≠ j) (c : O) :
    ∃ k : GL ι L, admitted O T k ∧
      ∀ z : ι → L, z ᵥ* k.1 = z + Pi.single j (z i * algebraMap O L c) := by
  let κ : GL ι O := ⟨transvection i j c, transvection i j (-c),
    by simp [transvection_mul_transvection_same, hij], by simp [transvection_mul_transvection_same, hij]⟩
  have key : ∀ z : ι → L, z ᵥ* (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1 =
      z + Pi.single j (z i * algebraMap O L c) := by
    intro z
    have e : (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1 =
        1 + Matrix.single i j (algebraMap O L c) := by
      ext a b
      simp [κ, transvection, Matrix.one_apply, Matrix.single_apply, apply_ite (algebraMap O L)]
    rw [e, Matrix.vecMul_add, Matrix.vecMul_one]
    congr 1
    ext l
    by_cases h : l = j
    · subst h
      simp [Matrix.vecMul, dotProduct, Matrix.single_apply]
    · simp [Matrix.vecMul, dotProduct, Matrix.single_apply, h, Ne.symm h]
  exact ⟨_, ⟨⟨κ, rfl⟩, fun v hv => by rw [key, hv i hi]; simp⟩, key⟩

lemma exists_mul_or [IsDomain O] [ValuationRing O] [IsFractionRing O L] (a b : L) :
    (∃ c : O, b = algebraMap O L c * a) ∨ ∃ c : O, a = algebraMap O L c * b := by
  by_cases ha : a = 0
  · exact Or.inr ⟨0, by simp [ha]⟩
  by_cases hb : b = 0
  · exact Or.inl ⟨0, by simp [hb]⟩
  rcases ValuationRing.isInteger_or_isInteger O (b / a) with ⟨c, hc⟩ | ⟨c, hc⟩
  · refine Or.inl ⟨c, ?_⟩
    have hc' : algebraMap O L c = b / a := hc
    rw [hc']; field_simp
  · refine Or.inr ⟨c, ?_⟩
    have hc' : algebraMap O L c = (b / a)⁻¹ := hc
    rw [hc']; field_simp

lemma exists_clear [IsDomain O] [ValuationRing O] [IsFractionRing O L] {T : Finset ι} {j p : ι}
    (hj : j ∈ T) (hp : p ∈ T) (hjp : j ≠ p) (z : ι → L) :
    ∃ k : GL ι L, admitted O T k ∧ (z ᵥ* k.1) j = 0 ∧ ∀ l, l ≠ j → l ≠ p → (z ᵥ* k.1) l = z l := by
  rcases exists_mul_or (O := O) (z j) (z p) with ⟨c, hc⟩ | ⟨c, hc⟩
  · obtain ⟨k₁, a₁, h₁⟩ := exists_transv (O := O) (L := L) hj hjp (1 - c)
    obtain ⟨k₂, a₂, h₂⟩ := exists_transv (O := O) (L := L) hp hjp.symm (-1)
    refine ⟨k₁ * k₂, a₁.mul a₂, ?_, fun l hl hl' => ?_⟩
    · rw [Units.val_mul, ← Matrix.vecMul_vecMul, h₂, h₁]
      simp [Pi.single_apply, hjp, hjp.symm, hc]
      ring
    · rw [Units.val_mul, ← Matrix.vecMul_vecMul, h₂, h₁]
      simp [Pi.single_apply, hl, hl']
  · obtain ⟨k, a, h⟩ := exists_transv (O := O) (L := L) hp hjp.symm (-c)
    refine ⟨k, a, ?_, fun l hl _ => ?_⟩
    · rw [h]
      simp [hc]
      ring
    · rw [h]
      simp [Pi.single_apply, hl]

lemma exists_clear_set [IsDomain O] [ValuationRing O] [IsFractionRing O L] {T : Finset ι} {p : ι}
    (hp : p ∈ T) (z : ι → L) (s : Finset ι) (hs : s ⊆ T) (hps : p ∉ s) :
    ∃ k : GL ι L, admitted O T k ∧ ∀ l ∈ s, (z ᵥ* k.1) l = 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, admitted.one T, by simp⟩
  | insert a s ha ih =>
    obtain ⟨k, hk, h⟩ := ih ((Finset.subset_insert a s).trans hs)
      (fun hh => hps (Finset.mem_insert_of_mem hh))
    have hap : a ≠ p := fun e => hps (e ▸ Finset.mem_insert_self a s)
    obtain ⟨k', hk', h0, h1⟩ := exists_clear (O := O) (hs (Finset.mem_insert_self a s)) hp hap (z ᵥ* k.1)
    refine ⟨k * k', hk.mul hk', fun l hl => ?_⟩
    rw [Units.val_mul, ← Matrix.vecMul_vecMul]
    rcases Finset.mem_insert.1 hl with rfl | hl
    · exact h0
    · rw [h1 l (fun e => ha (e ▸ hl)) (fun e => hps (e ▸ Finset.mem_insert_of_mem hl))]
      exact h l hl

lemma exists_rows [IsDomain O] [ValuationRing O] [IsFractionRing O L] {ρ : Type} [DecidableEq ρ]
    (f : ρ → ι) (hf : Function.Injective f) (g : Matrix ι ι L) (S : Finset ρ) :
    ∃ κ : GL ι O, ∀ i ∈ S, ∀ c ∉ S.image f,
      (g * (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1) (f i) c = 0 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a S ha ih =>
    obtain ⟨κ, h⟩ := ih
    have hpT : f a ∈ (S.image f)ᶜ := by
      simp only [Finset.mem_compl, Finset.mem_image, not_exists, not_and]
      exact fun x hx e => ha (hf e ▸ hx)
    obtain ⟨k, ⟨⟨κ', rfl⟩, fix⟩, hk⟩ := exists_clear_set (O := O) hpT
      ((g * (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1) (f a)) (((S.image f)ᶜ).erase (f a))
      (Finset.erase_subset _ _) (Finset.notMem_erase _ _)
    refine ⟨κ * κ', fun i hi c hc => ?_⟩
    have row : ∀ r, (g * (Matrix.GeneralLinearGroup.map (algebraMap O L) (κ * κ')).1) r =
        (g * (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1) r ᵥ*
          (Matrix.GeneralLinearGroup.map (algebraMap O L) κ').1 := by
      intro r
      rw [map_mul, Units.val_mul, ← Matrix.mul_assoc, Matrix.mul_apply_eq_vecMul]
    have hcS : c ∉ S.image f := fun e => hc (by
      rw [Finset.image_insert]; exact Finset.mem_insert_of_mem e)
    have hca : c ≠ f a := fun e => hc (by
      rw [Finset.image_insert, e]; exact Finset.mem_insert_self _ _)
    rw [row]
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hk c (Finset.mem_erase.2 ⟨hca, Finset.mem_compl.2 hcS⟩)
    · rw [fix _ (fun l hl => h i hi l (Finset.mem_compl.1 hl))]
      exact h i hi c hcS

end Ops

theorem jpIw : JpIw := by
  intro O L _ _ _ _ _ _ n g
  obtain ⟨κ, h⟩ := exists_rows (O := O) (L := L) (ι := Ix n) (Sum.inr : Fin n → Ix n)
    Sum.inr_injective g.1 Finset.univ
  set k : GL (Ix n) L := inL κ with hk
  set G : Matrix (Ix n) (Ix n) L := (g * k).1 with hG
  have hC : G.toBlocks₂₁ = 0 := by
    ext i j
    exact h i (Finset.mem_univ _) (Sum.inl j) (by simp)
  have hGb : G = fromBlocks G.toBlocks₁₁ G.toBlocks₁₂ 0 G.toBlocks₂₂ := by
    rw [← hC, Matrix.fromBlocks_toBlocks]
  have hdet : G.toBlocks₁₁.det * G.toBlocks₂₂.det ≠ 0 := by
    rw [← Matrix.det_fromBlocks_zero₂₁ G.toBlocks₁₁ G.toBlocks₁₂ G.toBlocks₂₂, ← hGb]
    exact (Matrix.isUnits_det_units (g * k)).ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (left_ne_zero_of_mul hdet),
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ (right_ne_zero_of_mul hdet), G.toBlocks₁₂, κ⁻¹, ?_⟩
  have hp : pM (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (left_ne_zero_of_mul hdet))
      (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (right_ne_zero_of_mul hdet)) G.toBlocks₁₂ = g * k := by
    apply Units.ext
    exact hGb.symm
  rw [hp, map_inv, ← hk, mul_inv_cancel_right]

end GlobalTheory.CompanionTheory.Jp.Iw

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFirstProperty
section
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.LatticeCoset

variable {F : Type} [Field F] [ValuativeRel F] {n : ℕ}

theorem mem_unitGL_iff (h : GL (Fin n) F) :
    h ∈ unitGL (n := Fin n) F ↔
      (∀ i j, (h : Matrix (Fin n) (Fin n) F) i j ∈ intO F) ∧
      (∀ i j, ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F) := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨fun i j => (k.1 i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((k⁻¹).1 i j).2
  · rintro ⟨h1, h2⟩
    let O := (ValuativeRel.valuation F).integer
    let A : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨(h : Matrix (Fin n) (Fin n) F) i j, h1 i j⟩
    let B : Matrix (Fin n) (Fin n) O :=
      Matrix.of fun i j => ⟨((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j, h2 i j⟩
    have hA : A.map O.subtype = (h : Matrix (Fin n) (Fin n) F) := by ext i j; rfl
    have hB : B.map O.subtype = ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by ext i j; rfl
    have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) O => M.map O.subtype) :=
      Matrix.map_injective Subtype.val_injective
    have hAB : A * B = 1 := by
      apply inj
      show (A * B).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
      rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have hBA : B * A = 1 := by
      apply inj
      show (B * A).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
      rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    ext i j
    rfl

theorem latticeOf_subset_of_integral (g g' : GL (Fin n) F)
    (h : ∀ i j, ((g⁻¹ * g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F) :
    latticeOf g' ⊆ latticeOf g := by
  rintro v ⟨w, hw, rfl⟩
  refine ⟨((g⁻¹ * g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec w, fun i => ?_, ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (h i j) (hw j)
  · rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left]

theorem integral_of_latticeOf_subset (g g' : GL (Fin n) F)
    (h : latticeOf g' ⊆ latticeOf g) (i j : Fin n) :
    ((g⁻¹ * g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F := by
  have hs : ∀ k, (Pi.single j (1 : F) : Fin n → F) k ∈ intO F := by
    intro k
    rcases eq_or_ne k j with rfl | hk
    · rw [Pi.single_eq_same]; exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne hk]; exact Subring.zero_mem _
  obtain ⟨w', hw', he⟩ := h ⟨Pi.single j 1, hs, rfl⟩
  have key : ((g⁻¹ * g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec (Pi.single j 1) = w' := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, he, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mulVec]
  have hi := congrFun key i
  rw [Matrix.mulVec_single_one] at hi
  change ((g⁻¹ * g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = w' i at hi
  rw [hi]
  exact hw' i

theorem latticeOf_eq_iff : PositivityTheory.Rg.Tf.Loc.L1 := by
  intro F _ _ _ _ n g g'
  constructor
  · intro h
    rw [mem_unitGL_iff]
    refine ⟨integral_of_latticeOf_subset g g' h.symm.subset, ?_⟩
    rw [mul_inv_rev, inv_inv]
    exact integral_of_latticeOf_subset g' g h.subset
  · intro hm
    rw [mem_unitGL_iff] at hm
    obtain ⟨h1, h2⟩ := hm
    rw [mul_inv_rev, inv_inv] at h2
    exact Set.Subset.antisymm (latticeOf_subset_of_integral g' g h2) (latticeOf_subset_of_integral g g' h1)

end GlobalTheory.CompanionTheory.LatticeCoset
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSecondProperty
section
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.Tf.Loc

theorem isUnitIntegral_of_conj_mem_unitGL {F : Type} [Field F] [ValuativeRel F] {n : ℕ}
    (γ g : GL (Fin n) F) (h : g⁻¹ * γ * g ∈ unitGL (n := Fin n) F) : IsUnitIntegral γ := by
  obtain ⟨u, hu⟩ := h
  have hcp : (γ : Matrix (Fin n) (Fin n) F).charpoly =
      ((u : Matrix (Fin n) (Fin n) (intO F)).charpoly).map (intO F).subtype := by
    have h1 : ((g⁻¹ * γ * g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).charpoly =
        (γ : Matrix (Fin n) (Fin n) F).charpoly := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
    rw [← h1, ← hu, ← Matrix.charpoly_map]
    rfl
  have hint := Valuation.integer.integers (ValuativeRel.valuation F)
  refine ⟨fun i => ?_, ?_⟩
  · rw [hcp, Polynomial.coeff_map]
    exact SetLike.coe_mem _
  · rw [hcp, Polynomial.coeff_map]
    have hdet : IsUnit (u : Matrix (Fin n) (Fin n) (intO F)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
    have hc : IsUnit ((u : Matrix (Fin n) (Fin n) (intO F)).charpoly.coeff 0) := by
      rw [Matrix.det_eq_sign_charpoly_coeff] at hdet
      exact isUnit_of_mul_isUnit_right hdet
    exact hint.isUnit_iff_valuation_eq_one.1 hc

theorem normGL_mem_unitGL {k E : Type} [Field k] [Field E] [ValuativeRel E] [Algebra k E] {n : ℕ}
    (σ : E ≃ₐ[k] E)
    (hστ : ∀ (τ : E ≃ₐ[k] E) (g : GL (Fin n) E),
      sigmaGL τ g ∈ unitGL (n := Fin n) E ↔ g ∈ unitGL (n := Fin n) E)
    {u : GL (Fin n) E} (hu : u ∈ unitGL (n := Fin n) E) :
    normGL σ u ∈ unitGL (n := Fin n) E := by
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  rw [← sigmaGL_pow]
  exact (hστ _ _).2 hu

theorem stableLattice_unitIntegral : D0a → L2 := by
  intro hD
  refine ⟨?_, ?_⟩
  · rintro F _ _ _ _ n γ ⟨g, hg⟩
    exact isUnitIntegral_of_conj_mem_unitGL γ g hg
  · intro k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ hgen n δ g hmem
    have hστ := (hD k E hun σ hgen).2.2.2.1
    have hℓ : σ ^ Module.finrank k E = 1 := by
      rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
    have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
      rw [← sigmaGL_pow, hℓ, sigmaGL_one]
    have h := normGL_mem_unitGL σ (hστ · n ·) hmem
    rw [normGL, twNorm_twConj_of_pow_eq_one _ hθ] at h
    exact h

end GlobalTheory.CompanionTheory.Tf.Loc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LaurentEqToLaurentSubInvert
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem laurent_eq_toLaurent_sub_invert {K : Type} [CommRing K] (h : K[T;T⁻¹]) :
    ∃ α β : Polynomial K, h = Polynomial.toLaurent α -
      LaurentPolynomial.invert (Polynomial.toLaurent β) := by
  induction h using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
    obtain ⟨α₁, β₁, rfl⟩ := hf
    obtain ⟨α₂, β₂, rfl⟩ := hg
    refine ⟨α₁ + α₂, β₁ + β₂, ?_⟩
    simp only [map_add (f := _)]
    ring
  | C_mul_T n a =>
    rcases le_total 0 n with hn | hn
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      refine ⟨Polynomial.monomial m a, 0, ?_⟩
      simp [Polynomial.toLaurent_C_mul_T]
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hn)
      refine ⟨0, -Polynomial.monomial m a, ?_⟩
      have hn' : n = -(m : ℤ) := by omega
      subst hn'
      simp [Polynomial.toLaurent_C_mul_T, map_mul, LaurentPolynomial.invert_T,
        LaurentPolynomial.invert_C]

theorem b_surj : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (K₃ : Type) [CommRing K₃] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (i₃ : K[T;T⁻¹] →+* K₃) (ρ₁ : K₁ →+* K₃) (ρ₂ : K₂ →+* K₃), Pf p K → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → PQ p i₃ (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → (∀ α, ρ₁ (i₁ α) = i₃ (Polynomial.toLaurent α)) → (∀ β, ρ₂ (i₂ β) = i₃ (LaurentPolynomial.invert (Polynomial.toLaurent β))) → ∀ y : K₃, ∃ (b₁ : K₁) (b₂ : K₂), y = ρ₁ b₁ - ρ₂ b₂ := by
  intro p _ K _ K₁ _ K₂ _ K₃ _ f g i₁ i₂ i₃ ρ₁ ρ₂ _ h₁ h₂ h₃ e₁ e₂ y
  obtain ⟨k, h, hy⟩ := h₃.pow y
  obtain ⟨α, β, rfl⟩ := laurent_eq_toLaurent_sub_invert h
  obtain ⟨-, -, root₁, -, -⟩ := pf_facts p K₁ h₁.pf
  obtain ⟨-, -, root₂, -, -⟩ := pf_facts p K₂ h₂.pf
  obtain ⟨-, -, -, inj₃, -⟩ := pf_facts p K₃ h₃.pf
  obtain ⟨b₁, hb₁⟩ := root₁ k (i₁ α)
  obtain ⟨b₂, hb₂⟩ := root₂ k (i₂ β)
  obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p K₃ h₃.pf.char k
  refine ⟨b₁, b₂, inj₃ k _ _ ?_⟩
  have key : (ρ₁ b₁ - ρ₂ b₂) ^ p ^ k = ρ₁ (b₁ ^ p ^ k) - ρ₂ (b₂ ^ p ^ k) := by
    rw [← hF (ρ₁ b₁ - ρ₂ b₂), map_sub F, hF, hF, map_pow, map_pow]
  rw [hy, key, hb₁, hb₂, e₁, e₂, map_sub]

end GlobalTheory.CompanionTheory.PerfectRing
end

