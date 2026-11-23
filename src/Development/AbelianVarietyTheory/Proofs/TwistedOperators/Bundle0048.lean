module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsParabolicDoubleCosetFunctionEqOne
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.CosetFn
section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem deltaR_mul (g g' : GL n k) : deltaR c (g * g') = deltaR c g * deltaR c g' := by
  simp only [deltaR, nabs, map_mul, NNReal.coe_mul, mul_zpow]

theorem deltaR_one : deltaR c (1 : GL n k) = 1 := by
  simp [deltaR, nabs]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mul_embX_mem_R {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c 1) (g : GL n k) :
    u * embX c g ∈ R k n c 1 :=
  mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left ⟨g, rfl⟩)

theorem deltaR_eq {J : Subgroup (GL (n ⊕ Fin c) k)} {h : GL (n ⊕ Fin c) k}
    (H : ∀ g ∈ prX (Cgrp J h), deltaR c g = 1) {u u' j j' : GL (n ⊕ Fin c) k} {g g' : GL n k}
    (hu : u ∈ N k n c 1) (hu' : u' ∈ N k n c 1) (hj : j ∈ J) (hj' : j' ∈ J)
    (e : u * embX c g * h * j = u' * embX c g' * h * j') : deltaR c g = deltaR c g' := by
  have h1 : g'⁻¹ * g ∈ prX (Cgrp J h) := by
    refine ⟨embX c g'⁻¹ * (u'⁻¹ * u) * (embX c g'⁻¹)⁻¹,
      Radical.conj_mem _ (mul_mem (inv_mem hu') hu), ?_⟩
    have e2 : embX c g'⁻¹ * (u'⁻¹ * u) * (embX c g'⁻¹)⁻¹ * embX c (g'⁻¹ * g)
        = (u' * embX c g')⁻¹ * (u * embX c g) := by
      simp only [map_mul, map_inv]; group
    rw [e2]
    refine Subgroup.mem_inf.2
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (mul_embX_mem_R hu' g')) (mul_embX_mem_R hu g), ?_⟩
    have e3 : u * embX c g = u' * embX c g' * h * j' * j⁻¹ * h⁻¹ := by
      rw [← e]; group
    have e4 : h⁻¹ * ((u' * embX c g')⁻¹ * (u * embX c g)) * h⁻¹⁻¹ = j' * j⁻¹ := by
      rw [e3]; group
    show h⁻¹ * ((u' * embX c g')⁻¹ * (u * embX c g)) * h⁻¹⁻¹ ∈ J
    rw [e4]
    exact mul_mem hj' (inv_mem hj)
  have h2 := deltaR_mul (c := c) g' (g'⁻¹ * g)
  rw [H _ h1, mul_inv_cancel_left, mul_one] at h2
  exact h2

end

theorem exists_isCosetFn (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k)
    (H : ∀ g ∈ prX (Cgrp J h), deltaR c g = 1) : ∃ f, IsCosetFn J h f ∧ f h = 1 := by
  classical
  let P : GL (n ⊕ Fin c) k → GL n k → Prop := fun x g =>
    ∃ u ∈ N k n c 1, ∃ j ∈ J, x = u * embX c g * h * j
  let f : GL (n ⊕ Fin c) k → ℂ := fun x =>
    if hx : ∃ g, P x g then (deltaR c hx.choose : ℂ) else 0
  have fpos : ∀ x g, P x g → f x = (deltaR c g : ℂ) := by
    intro x g hg
    have hx : ∃ g, P x g := ⟨g, hg⟩
    obtain ⟨u, hu, j, hj, e⟩ := hx.choose_spec
    obtain ⟨u', hu', j', hj', e'⟩ := hg
    simp only [f, dif_pos hx]
    rw [deltaR_eq H hu hu' hj hj' (e.symm.trans e')]
  have fneg : ∀ x, (¬ ∃ g, P x g) → f x = 0 := fun x hx => by simp only [f, dif_neg hx]
  have left : ∀ u ∈ N k n c 1, ∀ (g g' : GL n k) x, P x g' → P (u * embX c g * x) (g * g') := by
    rintro u hu g g' x ⟨u', hu', j, hj, rfl⟩
    refine ⟨u * (embX c g * u' * (embX c g)⁻¹), mul_mem hu (Radical.conj_mem _ hu'), j, hj, ?_⟩
    simp only [map_mul]; group
  have right : ∀ j ∈ J, ∀ g x, P x g → P (x * j) g := by
    rintro j hj g x ⟨u', hu', j', hj', rfl⟩
    exact ⟨u', hu', j' * j, mul_mem hj' hj, by group⟩
  refine ⟨f, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro u hu g x
    by_cases hx : ∃ g', P x g'
    · obtain ⟨g', hg'⟩ := hx
      rw [fpos _ _ (left u hu g g' x hg'), fpos _ _ hg', deltaR_mul]
      push_cast; rfl
    · rw [fneg x hx, mul_zero]
      apply fneg
      rintro ⟨g', hg'⟩
      apply hx
      have := left _ (Radical.conj_mem g⁻¹ (inv_mem hu)) g⁻¹ g' _ hg'
      have e : embX c g⁻¹ * u⁻¹ * (embX c g⁻¹)⁻¹ * embX c g⁻¹ * (u * embX c g * x) = x := by
        simp only [map_inv]; group
      rw [e] at this
      exact ⟨_, this⟩
  · intro x j hj
    by_cases hx : ∃ g', P x g'
    · obtain ⟨g', hg'⟩ := hx
      rw [fpos _ _ (right j hj g' x hg'), fpos _ _ hg']
    · rw [fneg x hx]
      apply fneg
      rintro ⟨g', hg'⟩
      apply hx
      have := right _ (inv_mem hj) g' _ hg'
      rw [mul_inv_cancel_right] at this
      exact ⟨_, this⟩
  · intro x hx
    apply fneg
    rintro ⟨g, u, hu, j, hj, e⟩
    apply hx
    symm
    rw [DoubleCoset.eq]
    exact ⟨_, mul_embX_mem_R hu g, j, hj, e⟩
  · rw [fpos h 1 ⟨1, one_mem _, 1, one_mem _, by simp⟩, deltaR_one]
    simp

end GlobalTheory.CosetFn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumPureTensorOfIsTensorDepth
section
open MeasureTheory GlobalTheory.FunObj

noncomputable section
namespace GlobalTheory.TensorExpansion
open GlobalTheory.SplitFlip ValuativeRel Matrix
open scoped Pointwise

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unitsPowInv_val (ϖ : kˣ) (e : ℕ) : (((ϖ ^ e)⁻¹ : kˣ) : k) = ((ϖ : k) ^ e)⁻¹ := by
  simp [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]

theorem resMk_eq_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (a b : 𝒪[k]) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) a = Ideal.Quotient.mk _ b ↔
      (((ϖ ^ e)⁻¹ : kˣ) : k) * ((a : k) - b) ∈ 𝒪[k] := by
  have h0 : (ϖ : k) ^ e ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    unitsPowInv_val]
  constructor
  · rintro ⟨c, hc⟩
    have h1 : (a : k) - b = (ϖ : k) ^ e * c := by
      have := congrArg Subtype.val hc
      simpa using this
    rw [h1, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
    exact c.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul]

theorem mem_of_inv_mul_mem {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) {x : k}
    (h : (((ϖ ^ e)⁻¹ : kˣ) : k) * x ∈ 𝒪[k]) : x ∈ 𝒪[k] := by
  have hx : x = (ϖ : k) ^ e * ((((ϖ ^ e)⁻¹ : kˣ) : k) * x) := by
    rw [unitsPowInv_val, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ϖ.ne_zero), one_mul]
  rw [hx]
  exact mul_mem (pow_mem hϖ.mem _) h

theorem mem_matLat_pow_smul_iff (ϖ : kˣ) (e : ℕ) {m n : ℕ} {Z : Matrix (Fin m) (Fin n) k} :
    Z ∈ matLat (Fin m) (ϖ ^ e • stdLat k (Fin n)) ↔ ∀ i j, (((ϖ ^ e)⁻¹ : kˣ) : k) * Z i j ∈ 𝒪[k] :=
  ⟨fun h i j => mem_stdLat.1 ((mem_smul_lat _ _ _).1 (h i)) j,
   fun h i => (mem_smul_lat _ _ _).2 (mem_stdLat.2 fun j => h i j)⟩

def resClass (ϖ : kˣ) {e : ℕ} {m n : ℕ} (c : Fin m → Fin n → Res k e) : Set (Matrix (Fin m) (Fin n) k) :=
  {X | ∀ i j, X i j ∈ 𝒪[k] ∧ (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j - liftRes c i j) ∈ 𝒪[k]}

theorem isNatDatum_resClass {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) {m n : ℕ} (c : Fin m → Fin n → Res k e) :
    IsNatDatum ϖ e ((resClass ϖ c).indicator (1 : Matrix (Fin m) (Fin n) k → ℂ)) := by
  classical
  refine ⟨fun X hX => Set.indicator_of_notMem (fun h => hX (mem_matLat_stdLat.2 fun i j => (h i j).1)) _,
    fun X Z hZ => ?_⟩
  have hZ' := (mem_matLat_pow_smul_iff ϖ e).1 hZ
  have hiff : X + Z ∈ resClass ϖ c ↔ X ∈ resClass ϖ c := by
    refine forall_congr' fun i => forall_congr' fun j => ?_
    have hz : Z i j ∈ 𝒪[k] := mem_of_inv_mul_mem hϖ e (hZ' i j)
    have h1 : (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j + Z i j - liftRes c i j) =
        (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j - liftRes c i j) + (((ϖ ^ e)⁻¹ : kˣ) : k) * Z i j := by ring
    show (X i j + Z i j ∈ 𝒪[k] ∧ (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j + Z i j - liftRes c i j) ∈ 𝒪[k]) ↔
      (X i j ∈ 𝒪[k] ∧ (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j - liftRes c i j) ∈ 𝒪[k])
    rw [h1, add_mem_cancel_right hz, add_mem_cancel_right (hZ' i j)]
  simp only [Set.indicator_apply, hiff, Pi.one_apply]

theorem exists_sum_pureTensor : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : GlobalTheory.SplitFlip.Grid k) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (e : ℕ) (γ : List GlobalTheory.SplitFlip.Edge) (T : G.Args → ℂ), G.IsTensor ϖ e γ T → ∃ (n : ℕ) (x : Fin n → ℂ) (φ : Fin n → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ i, ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (φ i b)) ∧ ∀ z, T z = ∑ i, x i * G.lines₂ γ (φ i) z := by
  intro k _ _ _ _ G ϖ hϖ e γ T hT
  classical
  let L := γ.toFinset
  let I := ∀ b : L, Fin (G.rank b.1.tgt) → Fin (G.rank b.1.src) → Res k e
  let rep : I → G.Args := fun c b => if h : b ∈ L then liftRes (c ⟨b, h⟩) else 0
  let ψ : I → ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ :=
    fun c b => if h : b ∈ L then (resClass ϖ (c ⟨b, h⟩)).indicator 1 else 1
  have key : ∀ z, T z = ∑ c, T (rep c) * G.lines₂ γ (ψ c) z := by
    intro z
    simp only [Grid.lines₂]
    by_cases hint : ∀ b ∈ γ, z b ∈ matLat _ (stdLat k _)
    · let c0 : I := fun b i j => Ideal.Quotient.mk _
        ⟨z b.1 i j, mem_matLat_stdLat.1 (hint b.1 (List.mem_toFinset.1 b.2)) i j⟩
      have hmem : ∀ (c : I) (b : L), z b.1 ∈ resClass ϖ (c b) ↔ c b = c0 b := by
        intro c b
        have hz := mem_matLat_stdLat.1 (hint b.1 (List.mem_toFinset.1 b.2))
        constructor
        · intro h
          funext i j
          have := (resMk_eq_iff hϖ e ⟨z b.1 i j, hz i j⟩ (Quotient.out (c b i j))).2 (h i j).2
          rw [Ideal.Quotient.mk_out] at this
          exact this.symm
        · rintro h i j
          refine ⟨hz i j, ?_⟩
          exact (resMk_eq_iff hϖ e ⟨z b.1 i j, hz i j⟩ (Quotient.out (c b i j))).1
            (by rw [Ideal.Quotient.mk_out, h])
      rw [Finset.sum_eq_single c0]
      · have hprod : (γ.map fun b => ψ c0 b (z b)).prod = 1 := by
          refine List.prod_eq_one fun x hx => ?_
          obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
          have hb' : b ∈ L := List.mem_toFinset.2 hb
          simp only [ψ, dif_pos hb']
          exact Set.indicator_of_mem ((hmem c0 ⟨b, hb'⟩).2 rfl) _
        rw [hprod, mul_one]
        let w : G.Args := fun b => if b ∈ γ then z b - rep c0 b else 0
        have hw : ∀ b, w b ∈ matLat _ (ϖ ^ e • stdLat k _) := by
          intro b
          by_cases hb : b ∈ γ
          · have hb' : b ∈ L := List.mem_toFinset.2 hb
            have h2 := (hmem c0 ⟨b, hb'⟩).2 rfl
            refine (mem_matLat_pow_smul_iff ϖ e).2 fun i j => ?_
            simp only [w, if_pos hb, rep, dif_pos hb', Matrix.sub_apply]
            exact (h2 i j).2
          · simp only [w, if_neg hb]
            exact zero_mem _
        rw [← hT.2.2 (rep c0) w hw]
        refine hT.1 fun b hb => ?_
        have hb : b ∈ γ := hb
        simp [w, hb]
      · intro c _ hc
        obtain ⟨b, hb⟩ : ∃ b : L, c b ≠ c0 b := by
          by_contra hne
          push_neg at hne
          exact hc (funext hne)
        rw [List.prod_eq_zero (List.mem_map.2 ⟨b.1, List.mem_toFinset.1 b.2, ?_⟩), mul_zero]
        simp only [ψ, dif_pos b.2]
        exact Set.indicator_of_notMem (mt (hmem c b).1 hb) _
      · intro h
        exact absurd (Finset.mem_univ _) h
    · push_neg at hint
      obtain ⟨b, hb, hz⟩ := hint
      rw [hT.2.1 z b hb hz]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      rw [List.prod_eq_zero (List.mem_map.2 ⟨b, hb, ?_⟩), mul_zero]
      have hb' : b ∈ L := List.mem_toFinset.2 hb
      simp only [ψ, dif_pos hb']
      have hn : z b ∉ resClass ϖ (c ⟨b, hb'⟩) := fun h =>
        hz (mem_matLat_stdLat.2 fun i j => (h i j).1)
      exact Set.indicator_of_notMem hn _
  refine ⟨Fintype.card I, fun i => T (rep ((Fintype.equivFin I).symm i)),
    fun i => ψ ((Fintype.equivFin I).symm i), ?_, ?_⟩
  · intro i b hb
    have hb' : b ∈ L := List.mem_toFinset.2 hb
    simp only [ψ, dif_pos hb']
    exact isNatDatum_resClass hϖ e _
  · intro z
    rw [key z]
    exact (Equiv.sum_comp (Fintype.equivFin I).symm (fun c => T (rep c) * G.lines₂ γ (ψ c) z)).symm

end GlobalTheory.TensorExpansion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationEqZpow
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.StepData.NormalForm

section Plain
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

end Plain

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.StepData.NormalForm.exists_valuation_eq_zpow {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k)
    (d : kˣ) : ∃ e : ℤ, valuation k (d : k) = valuation k (ϖ : k) ^ e := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have hu0 : φ (uniformizer k) ≠ 0 := by
    rw [ne_eq, map_eq_zero]; exact (uniformizer_pos).ne'
  have hu1 : φ (uniformizer k) < 1 := by
    rw [← map_one φ]; exact φ.strictMono uniformizer_lt_one
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp hu0
  have ha1 : a.toAdd < 0 := by
    rw [← ha] at hu1
    exact_mod_cast hu1
  have ha2 : -1 ≤ a.toAdd := by
    have h1 : φ.symm ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) < 1 := by
      rw [← map_one φ.symm]
      exact φ.symm.strictMono
        (by exact_mod_cast (show (Multiplicative.ofAdd (-1 : ℤ)) < 1 by decide))
    have h2 := le_uniformizer_iff.mpr h1
    have h3 := φ.strictMono.monotone h2
    simp only [OrderMonoidIso.apply_symm_apply, ← ha] at h3
    exact_mod_cast h3
  have ha3 : a = Multiplicative.ofAdd (-1 : ℤ) := by
    apply Multiplicative.toAdd.injective; simp; omega
  have hd0 : φ (valuation k (d : k)) ≠ 0 := by
    rw [ne_eq, map_eq_zero, map_eq_zero]; exact d.ne_zero
  obtain ⟨b, hb⟩ := WithZero.ne_zero_iff_exists.mp hd0
  have hz : φ (uniformizer k ^ (-b.toAdd)) = φ (uniformizer k) ^ (-b.toAdd) := map_zpow₀ φ _ _
  have key : φ (valuation k (d : k)) = φ (valuation k (ϖ : k) ^ (-b.toAdd)) := by
    rw [hϖ, hz, ← ha, ← hb, ha3, ← WithZero.coe_zpow]
    congr 1
    apply Multiplicative.toAdd.injective
    simp
  exact ⟨-b.toAdd, φ.injective key⟩

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private lemma latOf_mul_of_mem_KO' {K : Type} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] {Y : Type} [Fintype Y] [DecidableEq Y]
    (x w : GL Y K) (hw : w ∈ _root_.GlobalTheory.SplitWeil.KO K Y) :
    _root_.GlobalTheory.StepData.latOf (x * w) = _root_.GlobalTheory.StepData.latOf x := by
  rw [_root_.GlobalTheory.StepData.mem_KO] at hw
  apply le_antisymm
  · rw [_root_.GlobalTheory.StepData.latOf_le_iff]
    simpa [← mul_assoc] using hw.1
  · rw [_root_.GlobalTheory.StepData.latOf_le_iff]
    simpa [mul_assoc] using hw.2


open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.StepData.NormalForm.normalFormModN : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.NormalFormModN k := by
  intro k _ _ _ _ ϖ hϖ n _ _ c h
  obtain ⟨b, hbT, w, hw, rfl⟩ := _root_.GlobalTheory.SplitWeil.iwasawa_blockTriangular k (n ⊕ Fin c)
    (Sum.elim (fun _ => 0) (fun i => (i : ℕ) + 1)) h
  have hbP : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).BlockTriangular
      (_root_.GlobalTheory.RootEx.lev 1) := by
    intro i j hij
    apply hbT
    unfold _root_.GlobalTheory.RootEx.lev at hij
    rcases i with i | i <;> rcases j with j | j <;> simp at hij ⊢ <;> omega
  obtain ⟨u', hu', m, hm0, hmb, hbum⟩ := _root_.GlobalTheory.RootEx.BlockLevi.exists_unip_mul_levi k n c 1 b hbP
  have h21 : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₂₁ = 0 := by
    ext i j
    exact hbT (by simp)
  have hT : ((b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₂₂).BlockTriangular id := by
    intro i j hij
    exact hbT (by simp only [Sum.elim_inr]; exact Nat.succ_lt_succ hij)
  have hdet : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).det ≠ 0 := b.det_ne_zero
  have hbB := fromBlocks_toBlocks (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
  rw [← hbB, h21, det_fromBlocks_zero₂₁, det_of_upperTriangular hT] at hdet
  have hG : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁.det ≠ 0 := left_ne_zero_of_mul hdet
  have ht : ∀ i : Fin c, (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inr i) ≠ 0 :=
    fun i => Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hdet) i (Finset.mem_univ i)
  set g : GL n k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hG with hg
  have hgv : (g : Matrix n n k) = (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k).toBlocks₁₁ := rfl
  choose e he using fun i => _root_.GlobalTheory.StepData.NormalForm.exists_valuation_eq_zpow hϖ (Units.mk0 _ (ht i))
  set z : n → k := fun r => if hc : 0 < c then
    (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl r) (Sum.inr ⟨0, hc⟩) *
      ((b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr ⟨0, hc⟩) (Sum.inr ⟨0, hc⟩))⁻¹ else 0 with hz
  set εv : n ⊕ Fin c → kˣ := Sum.elim (fun _ => 1) (fun i => Units.mk0 _ (ht i) * ϖ ^ (-e i)) with hεv
  have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
  have key : m = _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis ϖ g e z * _root_.GlobalTheory.SplitFlip.diagGL εv := by
    clear hbum hu' hbP hdet hbB hw hT h21 hϖ he
    ext r s
    rw [Units.val_mul, _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis_val, _root_.GlobalTheory.SplitFlip.diagGL_val,
      mul_diagonal]
    rcases r with r | i <;> rcases s with s | j
    · rw [hmb _ _ (by simp [_root_.GlobalTheory.RootEx.lev])]
      simp [hεv, hgv, toBlocks₁₁]
    · by_cases hj : (j : ℕ) = 0
      · rw [hmb _ _ (by simp [_root_.GlobalTheory.RootEx.lev, hj])]
        have hc : 0 < c := j.pos
        have hj' : j = ⟨0, hc⟩ := Fin.ext hj
        subst hj'
        simp only [fromBlocks_apply₁₂, of_apply, hj, if_true, hz, dif_pos hc, hεv, Sum.elim_inr,
          Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val, _root_.zpow_neg,
          Units.val_inv_eq_inv_val]
        have := ht ⟨0, hc⟩
        field_simp
      · rw [hm0 _ _ (by simp [_root_.GlobalTheory.RootEx.lev]; omega)]
        simp [hj]
    · by_cases hi : (i : ℕ) = 0
      · rw [hmb _ _ (by simp [_root_.GlobalTheory.RootEx.lev, hi])]
        simp only [fromBlocks_apply₂₁, Matrix.zero_apply, zero_mul]
        exact hbT (by simp)
      · rw [hm0 _ _ (by simp [_root_.GlobalTheory.RootEx.lev]; omega)]
        rw [fromBlocks_apply₂₁, Matrix.zero_apply, zero_mul]
    · by_cases hij : i = j
      · subst hij
        have := ht i
        rw [hmb _ _ rfl]
        simp only [fromBlocks_apply₂₂, diagonal_apply_eq, hεv, Sum.elim_inr,
          Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val, _root_.zpow_neg,
          Units.val_inv_eq_inv_val]
        field_simp
      · rw [hm0 _ _ (by simp [_root_.GlobalTheory.RootEx.lev]; omega)]
        simp [diagonal_apply_ne _ hij]
  have hεinv : (_root_.GlobalTheory.SplitFlip.diagGL εv)⁻¹ = _root_.GlobalTheory.SplitFlip.diagGL εv⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    ext i j
    rw [Units.val_mul, _root_.GlobalTheory.SplitFlip.diagGL_val, _root_.GlobalTheory.SplitFlip.diagGL_val,
      diagonal_mul_diagonal, Units.val_one]
    simp [diagonal_apply, Matrix.one_apply]
  have hv0 : valuation k (ϖ : k) ≠ 0 := (map_ne_zero _).mpr hϖ0
  have hval : ∀ i, valuation k (εv i : k) = 1 := by
    rintro (i | i)
    · simp [hεv]
    · have hei := he i
      rw [Units.val_mk0] at hei
      simp only [hεv, Sum.elim_inr, Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val,
        map_mul, map_zpow₀]
      rw [hei, ← zpow_add₀ hv0, add_neg_cancel, zpow_zero]
  have hε : _root_.GlobalTheory.SplitFlip.diagGL εv ∈ _root_.GlobalTheory.SplitWeil.KO k (n ⊕ Fin c) := by
    rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff]
    constructor
    · intro i j
      rw [_root_.GlobalTheory.SplitFlip.diagGL_val, diagonal_apply]
      split_ifs
      · rw [Valuation.mem_integer_iff, hval]
      · exact zero_mem _
    · intro i j
      rw [hεinv, _root_.GlobalTheory.SplitFlip.diagGL_val, diagonal_apply]
      split_ifs
      · rw [Valuation.mem_integer_iff, Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hval,
          inv_one]
      · exact zero_mem _
  refine ⟨u'⁻¹, inv_mem hu', g, e, z, ?_, ?_⟩
  · have hub : u'⁻¹ * (b * w) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.nfBasis ϖ g e z * (_root_.GlobalTheory.SplitFlip.diagGL εv * w) := by
      rw [hbum, key]; group
    rw [hub, latOf_mul_of_mem_KO' _ _ (mul_mem hε hw)]
  · rw [latOf_mul_of_mem_KO' _ _ hw]
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice.MeetsIn
    intro y
    rw [_root_.GlobalTheory.StepData.mem_latOf, _root_.GlobalTheory.StepData.mem_latOf]
    have h1 : (b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *ᵥ Sum.elim ((↑g⁻¹ : Matrix n n k) *ᵥ y) 0 =
        Sum.elim y 0 := by
      rw [← hbB, h21, fromBlocks_mulVec]
      simp [← hgv, mulVec_mulVec]
    have hv : (↑b⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *ᵥ Sum.elim y 0 =
        Sum.elim ((↑g⁻¹ : Matrix n n k) *ᵥ y) 0 := by
      rw [← h1, mulVec_mulVec, Units.inv_mul, one_mulVec]
    rw [hv]
    constructor
    · intro H i
      simpa using H (Sum.inl i)
    · rintro H (i | i)
      · simpa using H i
      · simp

end GlobalTheory.StepData.NormalForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorMovedTensorFinsetSumLinear
section
open MeasureTheory GlobalTheory.FunObj

namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

theorem flatTensor_moved_sum {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s)
    (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (hψ : Continuous ψ) (ϖ : kˣ) (e : ℕ) (keep : Bool)
    (g : G.VertexGroup) {ι : Type} (S : Finset ι) (x : ι → ℂ) (T : ι → G.Args → ℂ)
    (hT : ∀ i ∈ S, G.IsTensor ϖ e (GlobalTheory.SplitFlip.oppositePath G.m) (T i)) (X : ColArgs G) (Y : RowArgs G) :
    flatTensor hs ψ ν (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y =
      ∑ i ∈ S, x i * flatTensor hs ψ ν (moved G keep g (T i)) X Y := by
  classical
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hint : ∀ i ∈ S, Integrable (flatIntegrand hs ψ (moved G keep g (T i)) X Y) (varsVol G ν) := by
    intro i hi
    unfold varsVol
    exact (continuous_flatIntegrand hs hψ (hT i hi) keep g X Y).integrable_of_hasCompactSupport
      (hasCompactSupport_flatIntegrand hs ψ (hT i hi) keep g X Y)
  have h : ∀ v, flatIntegrand hs ψ (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y v =
      ∑ i ∈ S, x i * flatIntegrand hs ψ (moved G keep g (T i)) X Y v := by
    intro v
    simp only [flatIntegrand, moved, GlobalTheory.SplitFlip.Grid.pathAct, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [flatTensor, h]
  rw [MeasureTheory.integral_finsetSum _ fun i hi => (hint i hi).const_mul _]
  simp only [integral_const_mul]

end GlobalTheory.FunObj
end

