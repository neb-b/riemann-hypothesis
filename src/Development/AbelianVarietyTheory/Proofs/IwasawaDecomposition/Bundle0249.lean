module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneRelUnique
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjWD

section

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

end

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end GlobalTheory.ConjWD

namespace GlobalTheory.ConjWD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_weil_eq_on {g : G E Ω} (hg : g ∈ Dec (F := E) A) (L : IntermediateField E Ω)
    [FiniteDimensional E L] : ∃ τ : Weil h, ∀ x ∈ L, (τ : G E Ω) x = g x := by
  obtain ⟨k, hk⟩ := GlobalTheory.T.decomposition_element_frobenius_power E Ω A w h L inferInstance g hg
  set φ : Weil h := frob h ^ k
  have hφ : ActsAs A (normV w) (φ : G E Ω) k 0 := actsAs_of_deg (by simp [φ])
  have hψ : ((φ : G E Ω) * g) ∈ Dec (F := E) A := (Dec (F := E) A).mul_mem hφ.1 hg
  obtain ⟨ι, hι, hιL⟩ := GlobalTheory.T.inertia_lift_of_residual_trivial E Ω A w h L _ hψ fun x hx hxi => by
    have hx1 : A.valuation x ≤ 1 := (A.valuation_le_one_iff x).mpr (mem_of_isIntegral_int A hxi)
    have hgx : A.valuation (g x) ≤ 1 := val_apply_le_one hg hx1
    have h1 := hφ.2 _ hgx
    simp only [pow_zero, pow_one] at h1
    exact cong_trans h1 (hk x hx hxi)
  refine ⟨φ⁻¹ * ineIncl h ⟨ι, hι⟩, fun x hx => ?_⟩
  show (φ : G E Ω)⁻¹ (ι x) = g x
  rw [hιL x hx, AlgEquiv.mul_apply]
  show ((φ : G E Ω)⁻¹ * (φ : G E Ω)) (g x) = g x
  simp

end GlobalTheory.ConjWD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerFunctionalTorusValuationBound
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Topology

noncomputable section
namespace GlobalTheory.RootUp

variable {k : Type} [Field k]

theorem single_sq {n : ℕ} {i j : Fin n} (h : i ≠ j) (y : k) :
    Matrix.single i j y * Matrix.single i j y = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  split_ifs with h1 h2 <;> first | rfl | exact absurd (h2.2.trans h1.1.symm) h.symm | exact absurd (h2.1.trans h1.2.symm) h | simp

def elem {n : ℕ} {i j : Fin n} (h : i ≠ j) (y : k) : GL (Fin n) k :=
  ⟨1 + Matrix.single i j y, 1 - Matrix.single i j y, by
    rw [add_mul, one_mul, mul_sub, mul_one, single_sq h]; abel,
   by
    rw [sub_mul, one_mul, mul_add, mul_one, single_sq h]; abel⟩

theorem val_elem {n : ℕ} {i j : Fin n} (h : i ≠ j) (y : k) :
    (elem h y : Matrix (Fin n) (Fin n) k) = 1 + Matrix.single i j y := rfl

theorem continuous_elem [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    Continuous (elem (k := k) h) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun a b => ?_
    simp only [Function.comp_apply, val_elem, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  · refine continuous_matrix fun a b => ?_
    show Continuous fun y => (1 - Matrix.single i j y : Matrix (Fin n) (Fin n) k) a b
    simp only [Matrix.sub_apply, Matrix.single_apply]
    split_ifs <;> fun_prop

theorem val_conj_elem {n : ℕ} (t : Fin n → kˣ) {i j : Fin n} (h : i ≠ j) (y : k) :
    ((diagT k (Fin n) t * elem h y * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      1 + Matrix.single i j ((t i : k) / t j * y) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, val_elem]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Pi.inv_apply]
  by_cases hab : a = b
  · subst hab
    have : ¬ (i = a ∧ j = a) := fun h' => h (h'.1.trans h'.2.symm)
    simp [this]
  · by_cases hh : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hh
      simp [hab]
      field_simp
    · simp [hab, hh]

theorem elem_conj_mem {n : ℕ} (t : Fin n → kˣ) {i j : Fin n} (hij : i < j) (y : k) :
    diagT k (Fin n) t * elem hij.ne y * (diagT k (Fin n) t)⁻¹ ∈ unipB k (Fin n) := by
  refine (mem_unipB k).2 ⟨fun a b hba => ?_, fun a => ?_⟩
  · rw [val_conj_elem]
    have hab : a ≠ b := (ne_of_lt hba).symm
    have : ¬ (i = a ∧ j = b) := by
      rintro ⟨rfl, rfl⟩; exact absurd hij (not_lt.2 hba.le)
    simp [Matrix.one_apply, Matrix.single_apply, hab, this]
  · rw [val_conj_elem]
    have : ¬ (i = a ∧ j = a) := fun h' => hij.ne (h'.1.trans h'.2.symm)
    simp [Matrix.single_apply, this]

theorem superDiag_conj_elem {n : ℕ} (t : Fin n → kˣ) {i j : Fin n} (hij : j.val = i.val + 1) (hne : i ≠ j) (y : k) :
    superDiag (diagT k (Fin n) t * elem hne y * (diagT k (Fin n) t)⁻¹) = (t i : k) / t j * y := by
  rw [superDiag, val_conj_elem]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [Matrix.one_apply, hne]
    · intro b hb hbj
      have hib : i ≠ b := by
        rintro rfl; simp at hb
      simp [Matrix.one_apply, Matrix.single_apply, hib, Ne.symm hbj]
    · intro hj; simp [hij] at hj
  · intro a _ hai
    refine Finset.sum_eq_zero fun b hb => ?_
    have hab : a ≠ b := by
      rintro rfl; simp at hb
    simp [Matrix.one_apply, Matrix.single_apply, hab, Ne.symm hai]
  · simp

theorem whittaker_torus_root_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l → ∀ x : V, ∃ r : kˣ, ∀ (t : Fin n → kˣ) (i j : Fin n), j.val = i.val + 1 → l (ρ (diagT k (Fin n) t) x) ≠ 0 → valuation k ((t i : k) / t j) ≤ valuation k (r : k) := by
  intro k _ _ _ _ ψ hψ hψ1 n V _ _ ρ hρ l hl x
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ hψ1
  have hU : {g : GL (Fin n) k | ρ g x = x} ∈ 𝓝 (1 : GL (Fin n) k) := (hρ x).mem_nhds (by simp)
  have hall : ∀ᶠ y in 𝓝 (0 : k), ∀ i j : Fin n, ∀ h : i ≠ j, ρ (elem h y) x = x := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      Filter.eventually_all.2 fun h => ?_
    have hc0 : elem h (0 : k) = 1 := Units.ext (by simp [val_elem])
    exact (continuous_elem h).continuousAt.preimage_mem_nhds (by rw [hc0]; exact hU)
  obtain ⟨s, hs⟩ := exists_cball_subset hall
  refine ⟨c * s⁻¹, fun t i j hij hne0 => ?_⟩
  have hlt : i < j := by rw [Fin.lt_iff_val_lt_val]; omega
  have key : ∀ y ∈ cball s, ψ (y * ((t i : k) / t j)) = 1 := by
    intro y hy
    have hfix : ρ (elem hlt.ne y) x = x := hs hy i j hlt.ne
    have h1 := hl _ (elem_conj_mem t hlt y) (ρ (diagT k (Fin n) t) x)
    rw [superDiag_conj_elem t hij hlt.ne, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right,
      map_mul, Module.End.mul_apply, hfix] at h1
    have h2 : ((ψ ((t i : k) / t j * y) : Circle) : ℂ) = 1 := (mul_eq_right₀ hne0).1 h1.symm
    rw [mul_comm]
    exact Circle.coe_eq_one.1 h2
  by_contra hv
  obtain ⟨y, hy, hne⟩ := hc.exists_ne_one s (x := (t i : k) / t j) hv
  exact hne (key y hy)
end GlobalTheory.RootUp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerTorusTwKerRootBound
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RootDown

variable {k : Type} [Field k]

theorem blk_stdBlocks_eq_zero {n a b : ℕ} (h : ∑ i, ![a, b] i = n) (p : Fin n) :
    GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) p = 0 ↔ p.val < a := by
  obtain ⟨⟨c, r⟩, rfl⟩ := (stdBlocks ![a, b] h).surjective p
  rw [GlobalTheory.SmGL.blk_apply, stdBlocks_val]
  rcases c with ⟨_ | _ | c, hc⟩
  · have := r.isLt
    simp at this ⊢
    omega
  · have := r.isLt
    simp
  · omega

theorem unip_entry {n a b : ℕ} (h : ∑ i, ![a, b] i = n) {u : GL (Fin n) k}
    (hu : u ∈ unipRad k (stdBlocks ![a, b] h)) (p q : Fin n) (hpq : ¬ (p.val < a ∧ a ≤ q.val)) :
    (u : Matrix (Fin n) (Fin n) k) p q = (1 : Matrix (Fin n) (Fin n) k) p q := by
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hu
  rcases lt_trichotomy (GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) q) (GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) p)
    with hlt | heq | hgt
  · rw [mem_parab.1 hP p q hlt]
    have : p ≠ q := by rintro rfl; exact lt_irrefl _ hlt
    simp [Matrix.one_apply_ne this]
  · obtain ⟨⟨c, r⟩, rfl⟩ := (stdBlocks ![a, b] h).surjective p
    obtain ⟨⟨c', s⟩, rfl⟩ := (stdBlocks ![a, b] h).surjective q
    simp only [GlobalTheory.SmGL.blk_apply] at heq
    subst heq
    rw [hD c' r s]
    simp [Matrix.one_apply]
  · exfalso
    apply hpq
    have h1 := Fin.lt_def.1 hgt
    have h2 := (GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) q).isLt
    have hp0 : GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) p = 0 := Fin.ext (by simp; omega)
    have hq0 : GlobalTheory.SmGL.blk (stdBlocks ![a, b] h) q ≠ 0 := fun h0 => by
      rw [h0] at h1; simp at h1
    exact ⟨(blk_stdBlocks_eq_zero h p).1 hp0,
      not_lt.1 fun hq => hq0 ((blk_stdBlocks_eq_zero h q).2 hq)⟩

theorem conj_entry {n : ℕ} (t : Fin n → kˣ) (u : GL (Fin n) k) (p q : Fin n) :
    ((diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q =
      (t p : k) * (u : Matrix (Fin n) (Fin n) k) p q * (((t q)⁻¹ : kˣ) : k) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  simp

end GlobalTheory.RootDown

open GlobalTheory.RootDown in
theorem GlobalTheory.whittaker_torus_twKer_rootBound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V) (l : Module.Dual ℂ V), IsFunctional ψ ρ l → ∀ (a b : ℕ) (h : ∑ i, ![a, b] i = n) (i j : Fin n), i.val + 1 = a → j.val = a → ∀ x ∈ twKer ρ (unipRad k (stdBlocks ![a, b] h)) 1, ∃ r : kˣ, ∀ t : Fin n → kˣ, l (ρ (diagT k (Fin n) t) x) ≠ 0 → valuation k (r : k) ≤ valuation k ((t i : k) / t j) := by
  intro k _ _ _ _ ψ hψ n V _ _ ρ l hl a b h i j hi hj x hx
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_addChar_eq_one ψ hψ
  unfold twKer at hx
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨u, hu⟩, y, rfl⟩ := hw
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    have key : ∀ t : Fin n → kˣ, l (ρ (diagT k (Fin n) t) (ρ u y - y)) =
        ((ψ ((t i : k) / t j * (u : Matrix (Fin n) (Fin n) k) i j) : ℂ) - 1) *
          l (ρ (diagT k (Fin n) t) y) := by
      intro t
      have hmem : diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ ∈ unipB k (Fin n) := by
        refine (mem_unipB k).2 ⟨fun p q hqp => ?_, fun p => ?_⟩
        · have hqp' := Fin.lt_def.1 hqp
          rw [conj_entry, unip_entry h hu p q (by omega), Matrix.one_apply_ne hqp.ne']
          simp
        · rw [conj_entry, unip_entry h hu p p (by omega), Matrix.one_apply_eq]
          simp
      have hsd : GlobalTheory.Whittaker.superDiag (diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹) =
          (t i : k) / t j * (u : Matrix (Fin n) (Fin n) k) i j := by
        unfold GlobalTheory.Whittaker.superDiag
        rw [Finset.sum_eq_single i]
        · rw [Finset.sum_eq_single_of_mem j (by simp; omega)]
          · rw [conj_entry, Units.val_inv_eq_inv_val, div_eq_mul_inv]
            ring
          · intro q hq hqj
            simp at hq
            exact absurd (Fin.ext (by omega)) hqj
        · intro p _ hpi
          refine Finset.sum_eq_zero fun q hq => ?_
          simp at hq
          have hpq : p ≠ q := fun e => by rw [e] at hq; omega
          rw [conj_entry, unip_entry h hu p q ?_, Matrix.one_apply_ne hpq]
          · simp
          · rintro ⟨h1, h2⟩
            exact hpi (Fin.ext (by omega))
        · intro hi'
          simp at hi'
      have hρ : ρ (diagT k (Fin n) t) (ρ u y) =
          ρ (diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹) (ρ (diagT k (Fin n) t) y) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hρ, hl _ hmem, hsd]
      ring
    by_cases hu0 : (u : Matrix (Fin n) (Fin n) k) i j = 0
    · refine ⟨1, fun t ht => absurd ?_ ht⟩
      rw [key, hu0, mul_zero, AddChar.map_zero_eq_one]
      simp
    · refine ⟨s * (Units.mk0 _ hu0)⁻¹, fun t ht => ?_⟩
      rw [key] at ht
      have hψ1 : ψ ((t i : k) / t j * (u : Matrix (Fin n) (Fin n) k) i j) ≠ 1 := fun h1 =>
        ht (by rw [h1]; simp)
      have hlt : valuation k (s : k) <
          valuation k ((t i : k) / t j * (u : Matrix (Fin n) (Fin n) k) i j) :=
        lt_of_not_ge fun hle => hψ1 (hs _ hle)
      rw [map_mul] at hlt
      have hpos : 0 < valuation k ((u : Matrix (Fin n) (Fin n) k) i j) := by
        simp [zero_lt_iff, hu0]
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, map_mul, map_inv₀]
      exact ((mul_inv_lt_iff₀ hpos).2 hlt).le
  | zero => exact ⟨1, fun t ht => absurd (by simp) ht⟩
  | add x y _ _ hx hy =>
    obtain ⟨r₁, h₁⟩ := hx
    obtain ⟨r₂, h₂⟩ := hy
    rcases le_total (valuation k (r₁ : k)) (valuation k (r₂ : k)) with h12 | h21
    · refine ⟨r₁, fun t ht => ?_⟩
      rw [map_add (f := _), map_add (f := _)] at ht
      by_cases h0 : l (ρ (diagT k (Fin n) t) x) = 0
      · rw [h0, zero_add] at ht
        exact h12.trans (h₂ t ht)
      · exact h₁ t h0
    · refine ⟨r₂, fun t ht => ?_⟩
      rw [map_add (f := _), map_add (f := _)] at ht
      by_cases h0 : l (ρ (diagT k (Fin n) t) y) = 0
      · rw [h0, add_zero] at ht
        exact h21.trans (h₁ t ht)
      · exact h₂ t h0
  | smul c x _ hx =>
    obtain ⟨r, hr⟩ := hx
    exact ⟨r, fun t ht => hr t fun h0 => ht (by rw [map_smul, map_smul, h0, smul_zero])⟩
end

