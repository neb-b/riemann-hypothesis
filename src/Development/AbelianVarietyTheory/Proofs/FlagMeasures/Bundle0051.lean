module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCommonDenominatorForHermitianLatticeData
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DenClear

theorem ringOfIntegers_smul_eq {E : Type} [Field E] [NumberField E] (o : 𝓞 E) (x : E) :
    o • x = (o : E) * x := rfl

theorem coeO_mul {E : Type} [Field E] [NumberField E] (a b : 𝓞 E) :
    ((a * b : 𝓞 E) : E) = (a : E) * b := rfl

theorem coeO_add {E : Type} [Field E] [NumberField E] (a b : 𝓞 E) :
    ((a + b : 𝓞 E) : E) = (a : E) + b := rfl

theorem coeO_int {E : Type} [Field E] [NumberField E] (k : ℤ) : ((k : 𝓞 E) : E) = (k : E) := by
  rfl

theorem exists_int_mul_eq {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ o : 𝓞 E, (m : E) * e = o := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
  have h := hy e (Finset.mem_singleton_self e)
  rw [zsmul_eq_mul] at h
  exact ⟨y, hy0, ⟨(y : E) * e, h⟩, rfl⟩

theorem clear_of_dvd {E : Type} [Field E] [NumberField E] {m D : ℤ} (h : m ∣ D) {e : E}
    (he : ∃ o : 𝓞 E, (m : E) * e = o) : ∃ o : 𝓞 E, (D : E) * e = o := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨o, ho⟩ := he
  refine ⟨(k : 𝓞 E) * o, ?_⟩
  rw [coeO_mul, coeO_int, ← ho]
  push_cast
  ring

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsFullLattice E Λ) (w : Fin n → E) :
    ∃ m : ℤ, m ≠ 0 ∧ (m : 𝓞 E) • w ∈ Λ := by
  exact _root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice Λ hΛ w

theorem den_clear : ∀ {E : Type} [Field E] [NumberField E] {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ] (v : ι → E) (g : κ → Fin n → E) (Hm : Matrix (Fin n) (Fin n) E) (sg : E →+* E) (Λ : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E Λ → ∃ D : ℤ, D ≠ 0 ∧ (∀ i, ∃ o : 𝓞 E, (D : E) * v i = o) ∧ (∀ x ∈ Λ, ∀ l, ∃ o : 𝓞 E, (D : E) * ∑ a, ∑ b, x a * Hm a b * sg (g l b) = o) ∧ ∀ l, (D : 𝓞 E) • g l ∈ Λ := by
  intro E _ _ n ι κ _ _ v g Hm sg Λ hΛ
  choose mv hmv0 hmv using fun i => exists_int_mul_eq (v i)
  choose mg hmg0 hmg using fun l => exists_int_smul_mem Λ hΛ (g l)
  obtain ⟨s, hs⟩ := Submodule.IsLattice.fg (A := E) (M := Λ)
  choose mp hmp0 hmp using fun (p : κ × (Fin n → E)) =>
    exists_int_mul_eq (∑ a, ∑ b, p.2 a * Hm a b * sg (g p.1 b))
  let T : Finset (κ × (Fin n → E)) := Finset.univ ×ˢ s
  let A : ℤ := ∏ i, mv i
  let B : ℤ := ∏ l, mg l
  let C : ℤ := ∏ p ∈ T, mp p
  have hA : A ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hmv0 i
  have hB : B ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hmg0 i
  have hC : C ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hmp0 i
  have dA : ∀ i, mv i ∣ A * B * C := fun i =>
    ((Finset.dvd_prod_of_mem mv (Finset.mem_univ i)).mul_right B).mul_right C
  have dB : ∀ l, mg l ∣ A * B * C := fun l =>
    ((Finset.dvd_prod_of_mem mg (Finset.mem_univ l)).mul_left A).mul_right C
  have dC : ∀ p ∈ T, mp p ∣ A * B * C := fun p hp =>
    (Finset.dvd_prod_of_mem mp hp).mul_left _
  refine ⟨A * B * C, mul_ne_zero (mul_ne_zero hA hB) hC, fun i => clear_of_dvd (dA i) (hmv i),
    ?_, ?_⟩
  · intro x hx l
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      exact clear_of_dvd (dC (l, x) (Finset.mem_product.2 ⟨Finset.mem_univ l, hx⟩)) (hmp (l, x))
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨o₁, h₁⟩ := hx
      obtain ⟨o₂, h₂⟩ := hy
      refine ⟨o₁ + o₂, ?_⟩
      rw [coeO_add, ← h₁, ← h₂, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Pi.add_apply]
      ring
    | smul c x _ hx =>
      obtain ⟨o, h⟩ := hx
      refine ⟨c * o, ?_⟩
      rw [coeO_mul, ← h]
      simp only [Pi.smul_apply, ringOfIntegers_smul_eq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  · intro l
    obtain ⟨k, hk⟩ := dB l
    have : ((A * B * C : ℤ) : 𝓞 E) • g l = (k : 𝓞 E) • ((mg l : 𝓞 E) • g l) := by
      rw [smul_smul, hk]
      push_cast
      rw [mul_comm]
    rw [this]
    exact Λ.smul_mem _ (hmg l)

end GlobalTheory.DenClear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfSameTrace
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.SameTrace

open GlobalTheory.HL.Eichler GlobalTheory.UnramOrder

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem hf_zero_l (y : Fin n → E) : hf L Hm 0 y = 0 := by simp [hf]

theorem hf_zero_r (y : Fin n → E) : hf L Hm y 0 = 0 := by simp [hf]

theorem hf_sum_l {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, a i) y = ∑ i ∈ s, hf L Hm (a i) y := by
  induction s using Finset.induction_on with
  | empty => simp [hf_zero_l]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, ih]

theorem hf_sum_r {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm y (∑ i ∈ s, a i) = ∑ i ∈ s, hf L Hm y (a i) := by
  induction s using Finset.induction_on with
  | empty => simp [hf_zero_r]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_r, ih]

theorem exists_smul_mem [IsNonarchimedeanLocalField F] {Λ : Submodule L.O (Fin n → E)}
    (hΛ : IsLat L Λ) (x : Fin n → E) : ∃ t : 𝒪[F], t ≠ 0 ∧ algebraMap F E t • x ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.CommonDenominator.main
  | exact _root_.GlobalTheory.CommonDenominator.main
  | (apply _root_.GlobalTheory.CommonDenominator.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonDenominator.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonDenominator.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonDenominator.main ..)

noncomputable def shear {m : ℕ} (b d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0) :
    (Fin n → E) ≃ₗ[E] (Fin n → E) where
  toFun v := v + ∑ j, hf L Hm v (b j) • d j
  map_add' v w := by simp only [hf_add_l, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c v := by
    simp only [hf_smul_l, RingHom.id_apply, smul_add, Finset.smul_sum, mul_smul]
  invFun v := v - ∑ j, hf L Hm v (b j) • d j
  left_inv v := by simp [hf_add_l, hf_sum_l, hf_smul_l, hdb]
  right_inv v := by simp [hf_sub_l, hf_sum_l, hf_smul_l, hdb]

theorem shear_apply {m : ℕ} (b d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0)
    (v : Fin n → E) : shear L Hm b d hdb v = v + ∑ j, hf L Hm v (b j) • d j := rfl

theorem shear_symm_apply {m : ℕ} (b d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0)
    (v : Fin n → E) : (shear L Hm b d hdb).symm v = v - ∑ j, hf L Hm v (b j) • d j := rfl

theorem shear_mem_isomG {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) {m : ℕ}
    (b c d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0)
    (hdd : ∀ i j, hf L Hm (d i) (d j) = 0)
    (hv : ∀ v k, hf L Hm v (d k) = ∑ j, hf L Hm v (b j) * hf L Hm (c j) (d k))
    (hcd : ∀ j k, hf L Hm (c j) (d k) + hf L Hm (d j) (c k) = 0) :
    shear L Hm b d hdb ∈ isomG L Hm := by
  intro v w
  have hw : ∀ k, hf L Hm (d k) w = ∑ j, L.cj (hf L Hm w (b j)) * hf L Hm (d k) (c j) := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hf_cj L h, hv, map_sum]
    simp only [map_mul, hf_cj L h]
  simp only [shear_apply, hf_add_l, hf_add_r, hf_sum_l, hf_sum_r, hf_smul_l, hf_smul_r, hdd,
    mul_zero, Finset.sum_const_zero, add_zero]
  simp only [hw]
  simp only [hv v, Finset.mul_sum]
  have key : ∑ k, ∑ j, L.cj (hf L Hm w (b k)) * (hf L Hm v (b j) * hf L Hm (c j) (d k))
      + ∑ j, ∑ k, hf L Hm v (b j) * (L.cj (hf L Hm w (b k)) * hf L Hm (d j) (c k)) = 0 := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    linear_combination L.cj (hf L Hm w (b k)) * hf L Hm v (b j) * hcd j k
  linear_combination key

end

theorem exists_isometry_of_same_trace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ La Lb, IsSD L Hm La → IsSD L Hm Lb → ∀ (m : ℕ) (e : Fin m → Fin n → E), LinearIndependent E e → (∀ i j, hf L Hm (e i) (e j) = 0) → (∀ x ∈ perp L Hm (Submodule.span E (Set.range e)), x ∈ La ↔ x ∈ Lb) → ∃ g ∈ isomG L Hm, (∀ x ∈ perp L Hm (Submodule.span E (Set.range e)), g x = x) ∧ g • La = Lb := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH La Lb hLa hLb m e he hee hab
  obtain ⟨-, hA, -, b, c, hb, hc, hbc⟩ := GlobalTheory.T.dual_inter_selfDualHermitianLattice_subspace L Hm hH La hLa m e he
  obtain ⟨-, hB, -, -⟩ := GlobalTheory.T.dual_inter_selfDualHermitianLattice_subspace L Hm hH Lb hLb m e he
  set X := Submodule.span E (Set.range e) with hX
  have hcj := hf_cj L hH.1

  have hXp : ∀ x ∈ X, x ∈ perp L Hm X := by
    have h1 : ∀ i, e i ∈ perp L Hm X := by
      intro i y hy
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hy
      simp [hf_sum_r, hf_smul_r, hee]
    exact Submodule.span_le.2 (Set.range_subset_iff.2 h1)
  have hbm : ∀ j, b j ∈ La ∧ b j ∈ X := fun j => by
    have : b j ∈ La ⊓ X.restrictScalars L.O := by
      rw [hb]; exact Submodule.subset_span ⟨j, rfl⟩
    exact this
  have hbLb : ∀ j, b j ∈ Lb := fun j => (hab _ (hXp _ (hbm j).2)).1 (hbm j).1
  have hcb : ∀ i j, hf L Hm (c i) (b j) = if i = j then 1 else 0 := fun i j => by
    rw [← hcj, hbc]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]

  have hperp : ∀ v, (∀ j, hf L Hm v (b j) = 0) → v ∈ perp L Hm X := by
    intro v hv x hx
    obtain ⟨t, ht, htx⟩ := exists_smul_mem L hLa.1 x
    have h1 : algebraMap F E t • x ∈ Submodule.span L.O (Set.range b) := by
      rw [← hb]; exact ⟨htx, X.smul_mem _ hx⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 h1
    have h2 : hf L Hm v (algebraMap F E t • x) = 0 := by
      rw [← ha]
      simp [hf_sum_r, Subring.smul_def, hf_smul_r, hv]
    rw [hf_smul_r, AlgEquiv.commutes] at h2
    have ht' : (t : F) ≠ 0 := fun h => ht (Subtype.ext h)
    exact ((IsUnit.mk0 _ ht').map (algebraMap F E)).mul_right_eq_zero.1 h2
  have hint : ∀ {Λ}, IsSD L Hm Λ → ∀ x ∈ Λ, ∀ y ∈ Λ, hf L Hm x y ∈ L.O :=
    fun hΛ x hx y hy => (hΛ.2 y).2 hy x hx

  have hc' : ∀ j, ∃ a ∈ Lb, c j - a ∈ X := fun j =>
    (hB (c j)).1 fun x hx hxp => hint hLa x ((hab x hxp).2 hx) _ (hc j)
  choose c' hc'b hc'X using hc'
  obtain ⟨ω, hω, ε, hε, hωε⟩ := exists_sub_cj_mul_eq_one L
  have hε' : (L.cj ω - ω) * L.cj ε = 1 := by simpa [L.cj_cj] using congrArg L.cj hωε
  have hcε : L.cj ε = -ε := by linear_combination (-ε) * hε' - (L.cj ε) * hωε
  obtain ⟨τ, hτO, hτ⟩ : ∃ τ ∈ L.O, τ + L.cj τ = 1 :=
    ⟨ω * ε, L.O.mul_mem hω hε, by rw [map_mul, hcε]; linear_combination hωε⟩
  let d₀ : Fin m → Fin n → E := fun j => c' j - c j
  have hd₀ : ∀ j, d₀ j ∈ X := fun j => by
    have := X.neg_mem (hc'X j)
    rwa [neg_sub] at this
  let H : Fin m → Fin m → E := fun j k => hf L Hm (c j) (d₀ k) + hf L Hm (d₀ j) (c k)
  have hHO : ∀ j k, H j k ∈ L.O := fun j k => by
    have h0 : hf L Hm (d₀ j) (d₀ k) = 0 := hXp _ (hd₀ j) _ (hd₀ k)
    have h1 : H j k = hf L Hm (c' j) (c' k) - hf L Hm (c j) (c k) := by
      simp only [H, d₀, hf_sub_l, hf_sub_r] at h0 ⊢
      linear_combination -h0
    rw [h1]
    exact L.O.sub_mem (hint hLb _ (hc'b j) _ (hc'b k)) (hint hLa _ (hc j) _ (hc k))
  have hHc : ∀ j k, L.cj (H k j) = H j k := fun j k => by
    simp only [H, map_add (f := _), hcj]; ring
  let d : Fin m → Fin n → E := fun j => d₀ j - ∑ l, (τ * H j l) • b l
  have hd : ∀ j, d j ∈ X := fun j =>
    X.sub_mem (hd₀ j) (X.sum_mem fun l _ => X.smul_mem _ (hbm l).2)
  have hcdb : ∀ j, c j + d j ∈ Lb := fun j => by
    have h1 : c j + d j = c' j - ∑ l, (τ * H j l) • b l := by
      simp only [d, d₀]; abel
    rw [h1]
    exact Lb.sub_mem (hc'b j) (Lb.sum_mem fun l _ =>
      Lb.smul_mem ⟨_, L.O.mul_mem hτO (hHO j l)⟩ (hbLb l))
  have hdb : ∀ i j, hf L Hm (d i) (b j) = 0 := fun i j => hXp _ (hd i) _ (hbm j).2
  have hdd : ∀ i j, hf L Hm (d i) (d j) = 0 := fun i j => hXp _ (hd i) _ (hd j)
  have hv0 : ∀ v, v - ∑ j, hf L Hm v (b j) • c j ∈ perp L Hm X := fun v =>
    hperp _ fun k => by simp [hf_sub_l, hf_sum_l, hf_smul_l, hcb]
  have hv : ∀ v k, hf L Hm v (d k) = ∑ j, hf L Hm v (b j) * hf L Hm (c j) (d k) := fun v k => by
    have h1 := hv0 v _ (hd k)
    simp only [hf_sub_l, hf_sum_l, hf_smul_l] at h1
    exact sub_eq_zero.1 h1
  have hcd : ∀ j k, hf L Hm (c j) (d k) + hf L Hm (d j) (c k) = 0 := fun j k => by
    have h1 : hf L Hm (c j) (d k) = hf L Hm (c j) (d₀ k) - L.cj τ * H j k := by
      simp [d, hf_sub_r, hf_sum_r, hf_smul_r, hcb, hHc]
    have h2 : hf L Hm (d j) (c k) = hf L Hm (d₀ j) (c k) - τ * H j k := by
      simp [d, hf_sub_l, hf_sum_l, hf_smul_l, hbc]
    have h3 : H j k = hf L Hm (c j) (d₀ k) + hf L Hm (d₀ j) (c k) := rfl
    rw [h1, h2]
    linear_combination -h3 - H j k * hτ
  refine ⟨shear L Hm b d hdb, shear_mem_isomG L hH.1 b c d hdb hdd hv hcd, fun x hx => ?_, ?_⟩
  · have h1 : ∀ j, hf L Hm x (b j) = 0 := fun j => hx _ (hbm j).2
    simp [shear_apply, h1]
  · apply le_antisymm
    · rintro _ ⟨v, hva, rfl⟩
      show shear L Hm b d hdb v ∈ Lb
      have hβ : ∀ j, hf L Hm v (b j) ∈ L.O := fun j => hint hLa _ hva _ (hbm j).1
      have h1 : shear L Hm b d hdb v = (v - ∑ j, hf L Hm v (b j) • c j)
          + ∑ j, hf L Hm v (b j) • (c j + d j) := by
        simp only [shear_apply, smul_add, Finset.sum_add_distrib]; abel
      rw [h1]
      refine Lb.add_mem ((hab _ (hv0 v)).1 (La.sub_mem hva (La.sum_mem fun j _ =>
        La.smul_mem ⟨_, hβ j⟩ (hc j)))) (Lb.sum_mem fun j _ => Lb.smul_mem ⟨_, hβ j⟩ (hcdb j))
    · intro w hw
      refine ⟨(shear L Hm b d hdb).symm w, ?_, (shear L Hm b d hdb).apply_symm_apply w⟩
      have hβ : ∀ j, hf L Hm w (b j) ∈ L.O := fun j => hint hLb _ hw _ (hbLb j)
      have h1 : (shear L Hm b d hdb).symm w = (w - ∑ j, hf L Hm w (b j) • (c j + d j))
          + ∑ j, hf L Hm w (b j) • c j := by
        simp only [shear_symm_apply, smul_add, Finset.sum_add_distrib]; abel
      have h2 : w - ∑ j, hf L Hm w (b j) • (c j + d j) ∈ perp L Hm X :=
        hperp _ fun k => by simp [hf_sub_l, hf_sum_l, hf_smul_l, hf_add_l, hcb, hdb]
      show (shear L Hm b d hdb).symm w ∈ La
      rw [h1]
      refine La.add_mem ((hab _ h2).2 (Lb.sub_mem hw (Lb.sum_mem fun j _ =>
        Lb.smul_mem ⟨_, hβ j⟩ (hcdb j)))) (La.sum_mem fun j _ => La.smul_mem ⟨_, hβ j⟩ (hc j))

end GlobalTheory.HL.SameTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNatBoundLocalLatticesStandardAe
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

theorem exists_uniform_bound {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (n : ℕ)
    (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep))
    (hfin : {p | Λ p ≠ Submodule.span (A.L p).O
      (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite)
    (hm : ∀ p, ∃ m : ℕ, m ≠ 0 ∧ (∀ v : Fin n → (A.loc p).Ep, (∀ i, v i ∈ (A.L p).O) →
      (m : (A.loc p).Ep) • v ∈ Λ p) ∧ ∀ v ∈ Λ p, ∀ i, (m : (A.loc p).Ep) * v i ∈ (A.L p).O) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ p, (∀ v : Fin n → (A.loc p).Ep, (∀ i, v i ∈ (A.L p).O) →
      (N : (A.loc p).Ep) • v ∈ Λ p) ∧ ∀ v ∈ Λ p, ∀ i, (N : (A.loc p).Ep) * v i ∈ (A.L p).O := by
  choose m hm0 hm1 hm2 using hm
  refine ⟨∏ q ∈ hfin.toFinset, m q, Finset.prod_ne_zero_iff.mpr fun q _ => hm0 q, fun p => ?_⟩
  by_cases hp : p ∈ hfin.toFinset
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hp
    rw [hk]
    refine ⟨fun v hv => ?_, fun v hv i => ?_⟩
    · have h1 := hm1 p v hv
      have h2 : ((m p * k : ℕ) : (A.loc p).Ep) • v = k • ((m p : (A.loc p).Ep) • v) := by
        rw [← Nat.cast_smul_eq_nsmul (A.loc p).Ep, smul_smul]
        push_cast
        ring_nf
      rw [h2]
      exact nsmul_mem h1 k
    · have h1 := hm2 p v hv i
      have h2 : ((m p * k : ℕ) : (A.loc p).Ep) * v i = (k : (A.loc p).Ep) * ((m p : (A.loc p).Ep) * v i) := by
        push_cast; ring
      rw [h2]
      exact (A.L p).O.mul_mem (natCast_mem (A.L p).O k) h1
  · have hΛ : Λ p = Submodule.span (A.L p).O
        (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep)) := by
      by_contra h
      exact hp (hfin.mem_toFinset.mpr h)
    refine ⟨fun v hv => ?_, fun v hv i => ?_⟩
    · rw [hΛ, mem_span_single_iff]
      intro i
      have := (A.L p).O.mul_mem (natCast_mem (A.L p).O (∏ q ∈ hfin.toFinset, m q)) (hv i)
      simpa only [Pi.smul_apply, smul_eq_mul] using this
    · rw [hΛ, mem_span_single_iff] at hv
      exact (A.L p).O.mul_mem (natCast_mem (A.L p).O _) (hv i)

end GlobalTheory.HL.Glue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNatMulMemIntegersQuadraticCompletion
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

theorem exists_nat_mul_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig)
    (happ : ∀ y : ∀ p, (A.loc p).Ep, {p | y p ∉ (A.L p).O}.Finite →
      ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = o)
    (p : HeightOneSpectrum (𝓞 F)) (y : (A.loc p).Ep) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : (A.loc p).Ep) * y ∈ (A.L p).O := by
  set Y : ∀ q, (A.loc q).Ep := Pi.single (M := fun q => (A.loc q).Ep) p y with hY
  have hfin : {q | Y q ∉ (A.L q).O}.Finite := by
    refine (Set.finite_singleton p).subset fun q hq => ?_
    by_contra hne
    apply hq
    simp only [hY]
    rw [Pi.single_eq_of_ne (Set.mem_singleton_iff.not.1 hne)]
    exact (A.L q).O.zero_mem
  obtain ⟨x, hx⟩ := happ Y hfin
  obtain ⟨o, ho, hxo⟩ := hx p
  have hYp : Y p = y := by simp [hY]
  rw [hYp] at hxo
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨d, hd0, hd⟩ := halg.exists_integral_multiple
  refine ⟨d.natAbs, Int.natAbs_ne_zero.2 hd0, ?_⟩
  have hint : IsIntegral ℤ ((d.natAbs : E) * x) := by
    rcases Int.natAbs_eq d with h | h
    · have : ((d.natAbs : E) * x) = d • x := by
        rw [zsmul_eq_mul]; congr 1
        exact (Int.cast_natCast (R := E) d.natAbs).symm.trans (congrArg _ h.symm)
      rw [this]; exact hd
    · have : ((d.natAbs : E) * x) = -(d • x) := by
        rw [zsmul_eq_mul, ← neg_mul]; congr 1
        have h' := congrArg (Int.cast (R := E)) h
        rw [h', Int.cast_neg, Int.cast_natCast, neg_neg]
      rw [this]; exact hd.neg
  have h1 := ιE_mem A p _ hint
  have hy : (d.natAbs : (A.loc p).Ep) * y =
      (A.loc p).ιE ((d.natAbs : E) * x) - (d.natAbs : (A.loc p).Ep) * o := by
    rw [map_mul, map_natCast, ← hxo]; ring
  rw [hy]
  exact (A.L p).O.sub_mem h1 ((A.L p).O.mul_mem (natCast_mem (A.L p).O _) ho)

end GlobalTheory.HL.Glue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntCastIsUnitCompletionAlmostAllPlaces
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PlacesInt

theorem intCast_isUnit_almost_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (D : ℤ), D ≠ 0 → {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = (D : (A.loc p).Fp)}.Finite := by
  intro F E _ _ _ _ _ sig A D hD
  have hDF : (D : F) ≠ 0 := Int.cast_ne_zero.2 hD
  refine (HeightOneSpectrum.Support.finite (𝓞 F) ((D : F)⁻¹)).subset fun p hp => ?_
  by_contra hs
  apply hp
  have hs' : p.valuation F ((D : F)⁻¹) ≤ 1 := by
    have := hs
    simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at this
    exact this
  have h1 : p.valuation F (D : F) ≤ 1 := by
    have := p.valuation_le_one (K := F) (D : 𝓞 F)
    simpa using this
  have m1 := ((integers_local A).2.2.1 (D : F) p).2 h1
  have m2 := ((integers_local A).2.2.1 ((D : F)⁻¹) p).2 hs'
  have hne : (A.loc p).ιF (D : F) ≠ 0 := by
    rw [map_ne_zero]; exact hDF
  refine ⟨⟨⟨_, m1⟩, ⟨_, m2⟩, ?_, ?_⟩, ?_⟩
  · apply Subtype.ext
    change (A.loc p).ιF (D : F) * (A.loc p).ιF ((D : F)⁻¹) = 1
    rw [← map_mul, mul_inv_cancel₀ hDF, map_one]
  · apply Subtype.ext
    change (A.loc p).ιF ((D : F)⁻¹) * (A.loc p).ιF (D : F) = 1
    rw [← map_mul, inv_mul_cancel₀ hDF, map_one]
  · change (A.loc p).ιF (D : F) = _
    exact map_intCast _ D

end GlobalTheory.HL.PlacesInt
end

