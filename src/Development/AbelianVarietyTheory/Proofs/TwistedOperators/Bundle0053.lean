module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0043
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemNormalizerOfTri
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped NNReal

noncomputable section
namespace GlobalTheory.RootEx.ConjVol

section Abstract
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def cj (U : Subgroup G) (g : Subgroup.normalizer (U : Set G)) : U ≃ₜ* U where
  toMulEquiv := U.normalizerMonoidHom g
  continuous_toFun := Continuous.subtype_mk
    (f := fun u : U => (g : G) * u * (g : G)⁻¹) (by fun_prop) _
  continuous_invFun := Continuous.subtype_mk
    (f := fun u : U => ((g⁻¹ : Subgroup.normalizer (U : Set G)) : G) * u *
      ((g⁻¹ : Subgroup.normalizer (U : Set G)) : G)⁻¹) (by fun_prop) _

theorem cj_coe (U : Subgroup G) (g : Subgroup.normalizer (U : Set G)) (u : U) :
    (cj U g u : G) = g * u * (g : G)⁻¹ := rfl

variable (U : Subgroup G) [MeasurableSpace U] [BorelSpace U] [LocallyCompactSpace U]

def md : Subgroup.normalizer (U : Set G) →* ℝ≥0 where
  toFun g := mulEquivHaarChar (cj U g)
  map_one' := by
    have : cj U 1 = ContinuousMulEquiv.refl U := by ext u; simp [cj_coe]
    simp only [this, mulEquivHaarChar_refl]
  map_mul' a b := by
    have : cj U (a * b) = (cj U b).trans (cj U a) := by ext u; simp [cj_coe, mul_assoc]
    simp only [this, mulEquivHaarChar_trans, mul_comm]

theorem md_ne_zero (g : Subgroup.normalizer (U : Set G)) : md U g ≠ 0 := (mulEquivHaarChar_pos _).ne'

theorem md_conj (x g : Subgroup.normalizer (U : Set G)) : md U (x * g * x⁻¹) = md U g := by
  rw [map_mul, map_mul, mul_right_comm, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem integral_conj_of_md (μ : Measure U) [μ.IsHaarMeasure] [μ.Regular]
    (g : Subgroup.normalizer (U : Set G)) (hg : md U g = 1) (f : G → ℂ) :
    ∫ u : U, f (g * (u : G) * (g : G)⁻¹) ∂μ = ∫ u : U, f u ∂μ := by
  have h := mulEquivHaarChar_smul_map μ (cj U g)
  rw [show mulEquivHaarChar (cj U g) = 1 from hg, one_smul] at h
  have h3 := integral_map_equiv (μ := μ) (cj U g).toHomeomorph.toMeasurableEquiv (fun u : U => f u)
  rw [show ⇑(cj U g).toHomeomorph.toMeasurableEquiv = ⇑(cj U g) from rfl, h] at h3
  exact h3.symm

end Abstract

section Alg
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem conj_mem_of_tri {p : ℕ} {g u : GL (n ⊕ Fin c) k} (hg : g.val.BlockTriangular (lev p))
    (hg' : (g⁻¹).val.BlockTriangular (lev p)) (hu : u ∈ N k n c p) : g * u * g⁻¹ ∈ N k n c p := by
  rw [Model.mem_N_iff] at hu ⊢
  intro r s hrs
  have e : (g * u * g⁻¹).val = 1 + g.val * (u.val - 1) * (g⁻¹).val := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.mul_inv, Units.val_mul, Units.val_mul]
    abel
  rw [e, Matrix.add_apply, add_eq_left, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases ht : lev p s < lev p t
  · rw [hg' ht, mul_zero]
  rw [Matrix.mul_apply]
  refine mul_eq_zero_of_left (Finset.sum_eq_zero fun v _ => ?_) _
  by_cases hv : lev p v < lev p r
  · rw [hg hv, zero_mul]
  rw [Matrix.sub_apply, hu v t (by omega), sub_self, mul_zero]

theorem mem_normalizer_of_tri {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g.val.BlockTriangular (lev p))
    (hg' : (g⁻¹).val.BlockTriangular (lev p)) :
    g ∈ Subgroup.normalizer (N k n c p : Set (GL (n ⊕ Fin c) k)) := by
  rw [Subgroup.mem_normalizer_iff]
  refine fun u => ⟨conj_mem_of_tri hg hg', fun h => ?_⟩
  have := conj_mem_of_tri hg' (by rwa [inv_inv]) h
  simpa [mul_assoc] using this

theorem embX_tri (p : ℕ) (x : GL n k) : (embX c x).val.BlockTriangular (lev p) := by
  rintro (r | r) (s | s) h
  · simp [lev] at h
  · simp [VolN.val_embX]
  · simp [VolN.val_embX]
  · have : r ≠ s := by rintro rfl; exact lt_irrefl _ h
    simp [VolN.val_embX, this]

theorem colE_tri (p : ℕ) (β : n → k) : (colE c p β).val.BlockTriangular (lev p) := by
  rintro (r | r) (s | s) h
  · simp [lev] at h
  · have : s.val + 1 ≠ p := by simp [lev] at h; omega
    simp [colE, upU, this]
  · simp [colE, upU]
  · have : r ≠ s := by rintro rfl; exact lt_irrefl _ h
    simp [colE, upU, this]

theorem embX_mem (p : ℕ) (x : GL n k) :
    embX c x ∈ Subgroup.normalizer (N k n c p : Set (GL (n ⊕ Fin c) k)) :=
  mem_normalizer_of_tri (embX_tri p x) (by rw [← map_inv]; exact embX_tri p _)

theorem colE_mem (p : ℕ) (β : n → k) :
    colE c p β ∈ Subgroup.normalizer (N k n c p : Set (GL (n ⊕ Fin c) k)) :=
  mem_normalizer_of_tri (colE_tri p β) (by
    rw [inv_eq_of_mul_eq_one_right (QuotStep.colE_neg p β)]; exact colE_tri p _)

theorem colE_add (p : ℕ) (u w : n → k) : colE c p (u + w) = colE c p u * colE c p w := by
  apply Units.ext
  simp only [colE, upU, Units.val_mul, fromBlocks_multiply]
  congr 1 <;> simp
  ext r i
  by_cases h : i.val + 1 = p <;> simp [h, add_comm]

end Alg

section Meas
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem exists_ne_zero_one [ValuativeRel.IsNontrivial k] : ∃ a : k, a ≠ 0 ∧ a ≠ 1 := by
  obtain ⟨γ, h0, h1⟩ := ValuativeRel.IsNontrivial.condition (R := k)
  obtain ⟨a, rfl⟩ := ValuativeRel.valuation_surjective γ
  exact ⟨a, by rintro rfl; simp at h0, by rintro rfl; simp at h1⟩

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem integral_conj_colE' (p : ℕ) (β : n → k) (f : GL (n ⊕ Fin c) k → ℂ) :
    ∫ u : N k n c p, f (colE c p β * (u : GL (n ⊕ Fin c) k) * (colE c p β)⁻¹) ∂(volN ν n c p) =
      ∫ u : N k n c p, f u ∂(volN ν n c p) := by
  haveI := secondCountable k
  haveI := t2Space k
  haveI : LocallyCompactSpace (N k n c p) := (VolN.isClosed_N p).locallyCompactSpace
  haveI := VolN.isHaarMeasure_volN (n := n) (c := c) ν p
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  let E : (n → k) → Subgroup.normalizer (N k n c p : Set (GL (n ⊕ Fin c) k)) := fun b => ⟨_, colE_mem p b⟩
  have hs : ∀ a : k, a ≠ 0 → md (N k n c p) (E (a • β)) = md (N k n c p) (E β) := fun a ha => by
    let x : GL n k := Matrix.GeneralLinearGroup.scalar n (Units.mk0 a ha)
    rw [← md_conj (N k n c p) ⟨_, embX_mem p x⟩ (E β)]
    congr 1
    apply Subtype.ext
    refine Eq.trans ?_ (QuotStep.conj_colE p x β).symm
    change colE c p (a • β) = _
    congr 1
    funext i
    simp [x, Matrix.mulVec_diagonal]
  obtain ⟨a, h0, h1⟩ := exists_ne_zero_one (k := k)
  have e : E β = E (a • β) * E ((1 - a) • β) := by
    apply Subtype.ext
    change colE c p β = colE c p (a • β) * colE c p ((1 - a) • β)
    rw [← colE_add, ← add_smul, add_sub_cancel, one_smul]
  have h := congrArg (md (N k n c p)) e
  rw [map_mul, hs a h0, hs _ (sub_ne_zero.2 h1.symm)] at h
  exact integral_conj_of_md (N k n c p) _ (E β)
    (mul_left_cancel₀ (md_ne_zero _ (E β)) (h.symm.trans (mul_one _).symm)) f

end Meas

theorem integral_conj_colE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure] (β : n → k) (f : GL (n ⊕ Fin c) k → ℂ), ∫ u : N k n c (ρ + 1), f (colE c (ρ + 1) β * (u : GL (n ⊕ Fin c) k) * (colE c (ρ + 1) β)⁻¹) ∂(volN ν n c (ρ + 1)) = ∫ u : N k n c (ρ + 1), f u ∂(volN ν n c (ρ + 1)) :=
  fun _ _ _ _ _ _ _ _ _ _ _ ρ _ _ ν _ β f => integral_conj_colE' ν (ρ + 1) β f

end GlobalTheory.RootEx.ConjVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemRootExchangeParabolicAndFourierJacobiIffEntri
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx.ParabolicEntries

open GlobalTheory.RootEx.Radical

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

def Par (L : ℕ) (b : Fin c → ℕ) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) : Prop :=
  ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => L) b s ≤ Sum.elim (fun _ => L) b r →
    M r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s

omit [Fintype n] in
theorem Par.blockTri {L : ℕ} {b : Fin c → ℕ} {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Par L b M) :
    M.BlockTriangular (Sum.elim (fun _ => L) b) := by
  intro r s hrs
  have hne : r ≠ s := by
    rintro rfl
    exact lt_irrefl _ hrs
  rw [h r s _ hrs.le, Matrix.one_apply_ne hne]
  rcases r with r | r <;> rcases s with s | s <;> simp_all

theorem Par.mul_left {L : ℕ} {b : Fin c → ℕ} {M M' : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Par L b M)
    (h' : M'.BlockTriangular (Sum.elim (fun _ => L) b)) {r s : n ⊕ Fin c} (hr : r.isRight)
    (hrs : Sum.elim (fun _ => L) b s ≤ Sum.elim (fun _ => L) b r) : (M * M') r s = M' r s := by
  have : (M * M') r s = ((1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * M') r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (Sum.elim (fun _ => L) b t) (Sum.elim (fun _ => L) b r) with ht | ht
    · rw [h r t (Or.inl hr) ht]
    · rw [h' (lt_of_le_of_lt hrs ht), mul_zero, mul_zero]
  rw [this, Matrix.one_mul]

theorem Par.mul_right {L : ℕ} {b : Fin c → ℕ} {M M' : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Par L b M)
    (h' : M'.BlockTriangular (Sum.elim (fun _ => L) b)) {r s : n ⊕ Fin c} (hs : s.isRight)
    (hrs : Sum.elim (fun _ => L) b s ≤ Sum.elim (fun _ => L) b r) : (M' * M) r s = M' r s := by
  have : (M' * M) r s = (M' * (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) r s := by
    simp only [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rcases le_or_gt (Sum.elim (fun _ => L) b s) (Sum.elim (fun _ => L) b t) with ht | ht
    · rw [h t s (Or.inr hs) ht]
    · rw [h' (lt_of_lt_of_le ht hrs), zero_mul, zero_mul]
  rw [this, Matrix.mul_one]

theorem Par.blockTri_inv {L : ℕ} {b : Fin c → ℕ} {g : GL (n ⊕ Fin c) k} (h : Par L b g.val) :
    (g⁻¹).val.BlockTriangular (Sum.elim (fun _ => L) b) := by
  letI : Invertible g.val := g.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular h.blockTri

def parGroup (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (L : ℕ) (b : Fin c → ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | Par L b g.val}
  one_mem' := fun _ _ _ _ => rfl
  mul_mem' := by
    intro g h hg hh r s hor hrs
    rw [Units.val_mul]
    rcases hor with hr | hs
    · rw [Par.mul_left hg (Par.blockTri hh) hr hrs, hh r s (Or.inl hr) hrs]
    · rw [Par.mul_right hh (Par.blockTri hg) hs hrs, hg r s (Or.inr hs) hrs]
  inv_mem' := by
    intro g hg r s hor hrs
    rcases hor with hr | hs
    · rw [← Par.mul_left hg (Par.blockTri_inv hg) hr hrs, Units.mul_inv]
    · rw [← Par.mul_right hg (Par.blockTri_inv hg) hs hrs, Units.inv_mul]

theorem embX_mem (L : ℕ) (b : Fin c → ℕ) (x : GL n k) : embX c x ∈ parGroup k n L b := by
  intro r s hor _
  rw [embX_val]
  rcases r with r | r <;> rcases s with s | s <;> simp_all [Matrix.one_apply]

theorem toBlocks₁₁_mul {L : ℕ} {b : Fin c → ℕ} {g h : GL (n ⊕ Fin c) k} (hg : g ∈ parGroup k n L b)
    (hh : h ∈ parGroup k n L b) : (g * h).val.toBlocks₁₁ = g.val.toBlocks₁₁ * h.val.toBlocks₁₁ := by
  ext r s
  simp only [Units.val_mul, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_sum_type]
  rw [add_eq_left]
  refine Finset.sum_eq_zero fun t _ => ?_
  rcases le_total (b t) L with ht | ht
  · rw [hg (Sum.inl r) (Sum.inr t) (by simp) ht, Matrix.one_apply_ne (by simp), zero_mul]
  · rw [hh (Sum.inr t) (Sum.inl s) (by simp) ht, Matrix.one_apply_ne (by simp), mul_zero]

theorem exists_eq_embX_mul {L : ℕ} {b : Fin c → ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ parGroup k n L b) :
    ∃ (x : GL n k) (u : GL (n ⊕ Fin c) k), Uni (Sum.elim (fun _ => L) b) u.val ∧ g = embX c x * u := by
  have h1 : ((1 : GL (n ⊕ Fin c) k)).val.toBlocks₁₁ = 1 := by
    ext r s
    simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  let x : GL n k := ⟨g.val.toBlocks₁₁, (g⁻¹).val.toBlocks₁₁,
    by rw [← toBlocks₁₁_mul hg (inv_mem hg), mul_inv_cancel, h1],
    by rw [← toBlocks₁₁_mul (inv_mem hg) hg, inv_mul_cancel, h1]⟩
  refine ⟨x, embX c x⁻¹ * g, ?_, by rw [map_inv, mul_inv_cancel_left]⟩
  have hm : embX c x⁻¹ * g ∈ parGroup k n L b := mul_mem (embX_mem L b _) hg
  have h11 : (embX c x⁻¹ * g).val.toBlocks₁₁ = 1 := by
    rw [toBlocks₁₁_mul (embX_mem L b _) hg, embX_val, Matrix.toBlocks_fromBlocks₁₁]
    exact x.inv_mul
  intro r s hrs
  by_cases hor : r.isRight ∨ s.isRight
  · exact hm r s hor hrs
  · rcases r with r | r <;> rcases s with s | s
    · have := congrFun (congrFun h11 r) s
      simp only [Matrix.toBlocks₁₁, Matrix.of_apply] at this
      rw [this]
      simp [Matrix.one_apply]
    all_goals simp at hor

theorem embX_mem_R (p : ℕ) (x : GL n k) : embX c x ∈ R k n c p :=
  Subgroup.mem_sup_left ⟨x, rfl⟩

theorem R_le {L p : ℕ} {b : Fin c → ℕ} (h : N k n c p ≤ parGroup k n L b) : R k n c p ≤ parGroup k n L b := by
  refine sup_le ?_ h
  rintro _ ⟨x, rfl⟩
  exact embX_mem L b x

theorem mem_R_iff_and_mem_RFJ_iff : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), (∀ g : GL (n ⊕ Fin c) k, g ∈ R k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) s ≤ Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) ∧ (1 ≤ ρ → ρ < c → ∀ g : GL (n ⊕ Fin c) k, g ∈ RFJ k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) := by
  intro k _ n _ _ c ρ
  refine ⟨fun g => ⟨fun hg => ?_, fun hg => ?_⟩, fun h1 hc g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · exact R_le (L := ρ) (b := fun i : Fin c => i.val + 1)
      (fun u hu r s _ hrs => (mem_N_iff u).1 hu r s hrs) hg
  · obtain ⟨x, u, hu, rfl⟩ := exists_eq_embX_mul (L := ρ) (b := fun i : Fin c => i.val + 1) hg
    exact mul_mem (embX_mem_R ρ x) (Subgroup.mem_sup_right ((mem_N_iff u).2 hu))
  · have hN : NFJ k n c ρ ≤ parGroup k n (2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) :=
      fun u hu r s _ hrs => ((GlobalTheory.RootEx.FJUnipotent.fj_unipotent k n c ρ h1 hc).2.1 u).1 hu r s hrs
    exact sup_le (R_le (le_sup_left.trans hN)) (R_le (le_sup_right.trans hN)) hg
  · obtain ⟨x, u, hu, rfl⟩ :=
      exists_eq_embX_mul (L := 2 * ρ + 1) (b := fun i : Fin c => 2 * (i.val + 1)) hg
    have hN : NFJ k n c ρ ≤ RFJ k n c ρ := sup_le_sup le_sup_right le_sup_right
    exact mul_mem (Subgroup.mem_sup_left (embX_mem_R ρ x))
      (hN (((GlobalTheory.RootEx.FJUnipotent.fj_unipotent k n c ρ h1 hc).2.1 u).2 hu))

end GlobalTheory.RootEx.ParabolicEntries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulMemOfHatCosetIndNeZero
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.StepData

open MeasureTheory ValuativeRel Matrix in
private theorem sigmaCompactSpace_of_isNonarchimedeanLocalField' (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] : SigmaCompactSpace k := by
  obtain ⟨a, ha0, ha1⟩ := Valuation.RankOne.nontrivial (valuation k)
  obtain ⟨b, hb0, hb1⟩ : ∃ b : k, valuation k b ≠ 0 ∧ valuation k b < 1 := by
    rcases lt_or_gt_of_ne ha1 with h | h
    · exact ⟨a, ha0, h⟩
    · refine ⟨a⁻¹, by simpa using ha0, ?_⟩
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ h
  have hb : b ≠ 0 := by
    intro h
    simp [h] at hb0
  refine ⟨⟨fun m : ℕ => (fun x => (b ^ m)⁻¹ * x) '' (𝒪[k] : Set k),
    fun m => (_root_.GlobalTheory.SplitWeil.isCompact_int k).image (continuous_const.mul continuous_id), ?_⟩⟩
  refine Set.eq_univ_of_forall fun x => ?_
  set S := (IsRankLeOne.nonempty (R := k)).some
  have hf := S.strictMono
  obtain ⟨m, hm⟩ : ∃ m : ℕ, S.emb (valuation k b) ^ m * S.emb (valuation k x) ≤ 1 := by
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨0, by simp⟩
    have hpos : 0 < S.emb (valuation k x) := by
      rw [← map_zero S.emb]
      exact hf (zero_lt_iff.2 (by simpa using hx))
    have hlt : S.emb (valuation k b) < 1 := by
      rw [← map_one S.emb]
      exact hf hb1
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hpos) hlt
    refine ⟨m, ?_⟩
    calc _ ≤ (S.emb (valuation k x))⁻¹ * S.emb (valuation k x) := by gcongr
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  simp only [Set.mem_iUnion, Set.mem_image]
  refine ⟨m, b ^ m * x, ?_, by field_simp⟩
  rw [SetLike.mem_coe, Valuation.mem_integer_iff, ← hf.le_iff_le, map_one, map_mul, map_mul,
    map_pow, map_pow]
  exact hm


open MeasureTheory ValuativeRel Matrix in
theorem _root_.GlobalTheory.StepData.mul_mem_of_hat_cosetInd_ne_zero : ∀ (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (ψ : AddChar k Circle) (_ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) (ν : Measure k)
    [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : kˣ) (ε : k)
    (yb : (n → k) ⧸ _root_.GlobalTheory.StepData.box n c) (η : n → k),
    _root_.GlobalTheory.StepData.hat ψ ν ε (_root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb) η ≠ 0 →
    ∀ i, ε * η i * (c : k) ∈ 𝒪[k] := by
  intro k _ _ _ _ _ _ ψ hψ ν _ n _ _ c ε yb η hne i
  haveI := sigmaCompactSpace_of_isNonarchimedeanLocalField' k
  by_contra hx
  obtain ⟨t, ht, hψt⟩ : ∃ t ∈ 𝒪[k], ψ (t * (ε * η i * c)) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hx (_root_.GlobalTheory.RootEx.Unram.mem_of_psi hψ h)
  have hvmem : Pi.single i ((c : k) * t) ∈ _root_.GlobalTheory.StepData.box n c := by
    show ∀ j, valuation k (Pi.single (M := fun _ => k) i ((c : k) * t) j) ≤ valuation k (c : k)
    intro j
    rcases eq_or_ne j i with rfl | hj
    · simp only [Pi.single_eq_same, map_mul]
      exact mul_le_of_le_one_right' ht
    · simp [Pi.single_eq_of_ne hj]
  apply hne
  unfold _root_.GlobalTheory.StepData.hat
  set g : (n → k) → ℂ := fun y => _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb y *
    (ψ (ε * η ⬝ᵥ y) : ℂ) with hg
  have hshift : ∀ y, g (y + Pi.single i ((c : k) * t)) = (ψ (t * (ε * η i * c)) : ℂ) * g y := by
    intro y
    have hind : _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb
        (y + Pi.single i ((c : k) * t)) =
          _root_.GlobalTheory.StepData.cosetInd (_root_.GlobalTheory.StepData.box n c) yb y := by
      unfold _root_.GlobalTheory.StepData.cosetInd
      simp only [Set.indicator]
      have hq : Submodule.Quotient.mk (p := _root_.GlobalTheory.StepData.box n c)
          (y + Pi.single i ((c : k) * t)) = Submodule.Quotient.mk y := by
        rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hvmem, add_zero]
      have hv0 := (Submodule.Quotient.mk_eq_zero _).2 hvmem
      split_ifs with h₁ h₂ h₂
      · rfl
      · exact absurd (hq.symm.trans h₁) h₂
      · exact absurd (hq.trans h₂) h₁
      · rfl
    simp only [hg, hind, dotProduct_add, dotProduct_single, mul_add, AddChar.map_add_eq_mul,
      Circle.coe_mul]
    have hr : ε * (η i * ((c : k) * t)) = t * (ε * η i * c) := by ring
    rw [hr]
    ring
  have h1 := integral_add_right_eq_self (μ := Measure.pi fun _ : n => ν) g
    (Pi.single i ((c : k) * t))
  simp only [hshift, integral_const_mul] at h1
  have hne1 : (ψ (t * (ε * η i * c)) : ℂ) ≠ 1 := by
    intro h
    exact hψt (Circle.ext_iff.mpr (by simpa using h))
  have hzero : ((ψ (t * (ε * η i * c)) : ℂ) - 1) * (∫ y, g y ∂Measure.pi fun _ => ν) = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 hzero).resolve_left (sub_ne_zero.2 hne1)

end GlobalTheory.StepData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicHaarVolumeConjIntersectionEqMul
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

noncomputable section
namespace GlobalTheory.CosetVolProd


open MeasureTheory ValuativeRel Matrix Topology in
theorem _root_.GlobalTheory.CosetVolProd.volR_Cgrp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k), IsOpen (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h) : Set (GL n k)) → ∀ m : Measure (GL n k), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.volR ν m (_root_.GlobalTheory.StepData.Cgrp J h) = _root_.GlobalTheory.RootEx.volN ν n c 1 ((_root_.GlobalTheory.StepData.Cgrp J h).subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1)) * m (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h)) := by
  intro k _ _ _ _ _ _ ν _ n _ _ c J h hopen m
  set C := _root_.GlobalTheory.StepData.Cgrp J h
  set N := _root_.GlobalTheory.RootEx.N k n c 1
  haveI := _root_.GlobalTheory.RootEx.VolN.isHaarMeasure_volN ν (n := n) (c := c) 1
  have key : ∀ g : GL n k, _root_.GlobalTheory.RootEx.volN ν n c 1
      {u : N | _root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) ∈ C}
      = (_root_.GlobalTheory.StepData.prX C : Set (GL n k)).indicator
          (fun _ => _root_.GlobalTheory.RootEx.volN ν n c 1 (C.subgroupOf N)) g := by
    intro g
    by_cases hg : g ∈ _root_.GlobalTheory.StepData.prX C
    · rw [Set.indicator_of_mem hg]
      obtain ⟨u₀, hu₀, hC⟩ := (_root_.GlobalTheory.StepData.mem_prX).1 hg
      have hv : (_root_.GlobalTheory.RootEx.embX c g)⁻¹ * u₀ * _root_.GlobalTheory.RootEx.embX c g ∈ N :=
        _root_.GlobalTheory.RootEx.Model.conj_mem hu₀ g
      set v : N := ⟨_, hv⟩
      have hset : {u : N | _root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) ∈ C}
          = (fun w => v⁻¹ * w) ⁻¹' (C.subgroupOf N : Set N) := by
        ext u
        show _ ∈ C ↔ ((v⁻¹ * u : N) : GL (n ⊕ Fin c) k) ∈ C
        have e : _root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k)
            = (u₀ * _root_.GlobalTheory.RootEx.embX c g) *
              (((_root_.GlobalTheory.RootEx.embX c g)⁻¹ * u₀ * _root_.GlobalTheory.RootEx.embX c g)⁻¹
                * u) := by group
        rw [e, C.mul_mem_cancel_left hC]
        rfl
      rw [hset, measure_preimage_mul]
    · rw [Set.indicator_of_notMem hg]
      have hset : {u : N | _root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) ∈ C} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun u hu => ?_
        apply hg
        refine (_root_.GlobalTheory.StepData.mem_prX).2 ⟨_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) * (_root_.GlobalTheory.RootEx.embX c g)⁻¹,
          _root_.GlobalTheory.RootEx.Radical.conj_mem g u.2, ?_⟩
        rwa [inv_mul_cancel_right]
      rw [hset, measure_empty]
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.volR
  refine (lintegral_congr key).trans ?_
  rw [lintegral_indicator_const hopen.measurableSet]

end GlobalTheory.CosetVolProd
end
end

