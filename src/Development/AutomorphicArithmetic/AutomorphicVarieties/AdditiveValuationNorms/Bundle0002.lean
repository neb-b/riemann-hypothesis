module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ImportsFurther
section
open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.twist :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (g : Module.End ℤ_[l] X) (a : ℤ_[l]), (l : ℤ_[l]) ∣ a - 1 →
      Unip g → Unip (a • g) := by
  intro l _ X _ _ g a ha hg
  obtain ⟨N, hN⟩ := hg
  obtain ⟨c, hc⟩ := ha
  have left : ∀ f h : Module.End ℤ_[l] X, InPow 1 f → InPow 1 (h * f) := by
    intro f h hf v
    obtain ⟨w, hw⟩ := hf v
    exact ⟨h w, by rw [Module.End.mul_apply, hw, map_smul]⟩
  have right : ∀ f h : Module.End ℤ_[l] X, InPow 1 f → InPow 1 (f * h) := by
    intro f h hf v
    exact hf (h v)
  have zero : InPow 1 (0 : Module.End ℤ_[l] X) := fun v => ⟨0, by simp⟩
  have add : ∀ f h : Module.End ℤ_[l] X, InPow 1 f → InPow 1 h → InPow 1 (f + h) := by
    intro f h hf hh v
    obtain ⟨w, hw⟩ := hf v
    obtain ⟨u, hu⟩ := hh v
    exact ⟨w + u, by rw [LinearMap.add_apply, hw, hu, smul_add]⟩
  have hB : InPow 1 ((a - 1) • g) := by
    intro v
    refine ⟨c • g v, ?_⟩
    rw [LinearMap.smul_apply, hc, mul_smul, pow_one]
  have hcomm : Commute (g - 1) ((a - 1) • g) :=
    ((Commute.refl g).sub_left (Commute.one_left g)).smul_right (a - 1)
  have hsplit : a • g - 1 = (g - 1) + (a - 1) • g := by
    rw [sub_smul, one_smul]
    abel
  refine ⟨N, ?_⟩
  rw [hsplit, hcomm.add_pow]
  refine Finset.sum_induction _ (InPow 1) add zero ?_
  intro m hm
  rcases Nat.lt_or_ge m N with hlt | hge
  · obtain ⟨k, hk⟩ : ∃ k, N - m = k + 1 := ⟨N - m - 1, by omega⟩
    rw [hk, pow_succ']
    apply right
    rw [← mul_assoc]
    apply right
    exact left _ _ hB
  · have hmN : m = N := by
      simp only [Finset.mem_range] at hm
      omega
    subst hmN
    exact right _ _ (right _ _ hN)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ImportsTer
section
open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.phi :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] [Module.Finite ℤ_[l] X] (w : Module.End ℤ_[l] X), InPow 2 (w - 1) →
      LinearMap.range ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X)) ≤ LinearMap.range (∑ i ∈ Finset.range l, w ^ i) := by
  intro l _ X _ _ _ w hw
  have hpow : ∀ (i : ℕ) (x : X), ∃ y : X, (w ^ i) x = x + (l : ℤ_[l]) ^ 2 • y := by
    intro i
    induction i with
    | zero => intro x; exact ⟨0, by simp⟩
    | succ i ih =>
      intro x
      obtain ⟨y, hy⟩ := ih (w x)
      obtain ⟨z, hz⟩ := hw x
      refine ⟨z + y, ?_⟩
      rw [pow_succ, Module.End.mul_apply, hy, smul_add, ← hz]
      simp only [LinearMap.sub_apply, Module.End.one_apply]
      abel
  have hsum : ∀ (n : ℕ) (x : X), ∃ y : X,
      (∑ i ∈ Finset.range n, w ^ i) x = (n : ℤ_[l]) • x + (l : ℤ_[l]) ^ 2 • y := by
    intro n x
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨z, hz⟩ := hpow n x
      refine ⟨y + z, ?_⟩
      rw [Finset.sum_range_succ, LinearMap.add_apply, hy, hz, smul_add, Nat.cast_succ, add_smul, one_smul]
      abel
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {(l : ℤ_[l])}) ?_ ?_ ?_
  · exact IsNoetherian.noetherian _
  · rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, PadicInt.maximalIdeal_eq_span_p]
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hsum l x
    have e : ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X)) x
        = (∑ i ∈ Finset.range l, w ^ i) x + (l : ℤ_[l]) • (((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X)) (-y)) := by
      rw [hy]
      simp only [LinearMap.smul_apply, Module.End.one_apply, smul_neg, pow_two, mul_smul]
      abel
    rw [e]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _)
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (LinearMap.mem_range_self _ _))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.LteNorm
section
open UpperTheory.V UpperTheory.V.PropA

private theorem norm_le_of_dvd' {l : ℕ} [Fact l.Prime] {x y : ℤ_[l]} (h : x ∣ y) : ‖y‖ ≤ ‖x‖ := by
  obtain ⟨z, rfl⟩ := h
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one z)

private theorem norm_eq_of_addVal {l : ℕ} [Fact l.Prime] {x y : ℤ_[l]}
    (h : IsDiscreteValuationRing.addVal ℤ_[l] x = IsDiscreteValuationRing.addVal ℤ_[l] y) :
    ‖x‖ = ‖y‖ := by
  have h1 : x ∣ y := IsDiscreteValuationRing.addVal_le_iff_dvd.mp h.le
  have h2 : y ∣ x := IsDiscreteValuationRing.addVal_le_iff_dvd.mp h.ge
  exact le_antisymm (norm_le_of_dvd' h2) (norm_le_of_dvd' h1)

theorem UpperTheory.V.PropA.lteNorm :
    ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]) (c : ℕ), IsLevel l u c → ‖u‖ = 1 ∧ (l : ℤ_[l]) ∣ u - 1 ∧
      ∀ j a b : ℕ, ‖(u ^ l ^ j) ^ a - (u ^ l ^ j) ^ b‖ = ((l : ℝ) ^ (j + c))⁻¹ * ‖(a : ℤ_[l]) - b‖ := by
  intro l _ u c hc
  obtain ⟨hv, hc1, hc2⟩ := hc
  have hval1 : IsDiscreteValuationRing.addVal ℤ_[l] (l : ℤ_[l]) = 1 :=
    IsDiscreteValuationRing.addVal_uniformizer PadicInt.irreducible_p
  have hl : (l : ℤ_[l]) ∣ u - 1 := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, hval1]
    simp only [vl] at hv
    rw [hv]
    exact_mod_cast hc1
  have hn1 : ‖u - 1‖ < 1 := (PadicInt.norm_lt_one_iff_dvd _).2 hl
  have hu : ‖u‖ = 1 := by
    have := PadicInt.norm_eq_of_norm_add_lt_right (z1 := u) (z2 := -1)
      (by rw [norm_neg, norm_one, ← sub_eq_add_neg]; exact hn1)
    rwa [norm_neg, norm_one] at this
  refine ⟨hu, hl, ?_⟩
  intro j a b
  have hunit : IsUnit u := PadicInt.isUnit_iff.2 hu
  set v := hunit.unit with hvdef
  have hvu : (v : ℤ_[l]) = u := hunit.unit_spec
  have hvmem : v ∈ abelian₂.oneUnits ℤ_[l] := by
    show (v : ℤ_[l]) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[l]
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, hvu]
    exact hn1
  let U : abelian₂.oneUnits ℤ_[l] := ⟨v, hvmem⟩
  set n : ℤ := ((l ^ j * a : ℕ) : ℤ) - ((l ^ j * b : ℕ) : ℤ) with hndef
  have hlm : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hptU : IsDiscreteValuationRing.addVal ℤ_[l] ↑(abelian₂.pt U) = c := by
    rw [abelian₂.coe_pt]
    simp only [vl] at hv
    rw [show ((U : ℤ_[l]ˣ) : ℤ_[l]) = u from hvu]
    exact hv
  have hcond : IsDiscreteValuationRing.addVal ℤ_[l] (l : ℤ_[l]) <
      ↑(l - 1) * IsDiscreteValuationRing.addVal ℤ_[l] ↑(abelian₂.pt U) := by
    rw [hval1, hptU]
    have hlt : 1 < (l - 1) * c := by
      have hp := (Fact.out : l.Prime).two_le
      rcases Nat.lt_or_ge l 3 with h | h
      · have h2 : l = 2 := by omega
        have := hc2 h2
        subst h2
        omega
      · have h3 : 2 ≤ l - 1 := by omega
        calc 1 < 2 * 1 := by norm_num
          _ ≤ (l - 1) * c := Nat.mul_le_mul h3 hc1
    exact_mod_cast hlt
  have key := abelian₂.lte ℤ_[l] l Fact.out hlm U hcond n
  have hfac : (u ^ l ^ j) ^ a - (u ^ l ^ j) ^ b = (u ^ l ^ j) ^ b * ↑(abelian₂.pt (U ^ n)) := by
    rw [abelian₂.coe_pt]
    have h1 : ((U ^ n : abelian₂.oneUnits ℤ_[l]) : ℤ_[l]ˣ) = v ^ n := rfl
    have h2 : v ^ ((l ^ j * a : ℕ) : ℤ) = v ^ ((l ^ j * b : ℕ) : ℤ) * v ^ n := by
      rw [← zpow_add]
      congr 1
      rw [hndef]
      ring
    have h3 : ∀ k : ℕ, (u ^ l ^ j) ^ k = ((v ^ ((l ^ j * k : ℕ) : ℤ) : ℤ_[l]ˣ) : ℤ_[l]) := by
      intro k
      rw [zpow_natCast, Units.val_pow_eq_pow_val, hvu, pow_mul]
    rw [h1, h3 a, h3 b, h2, Units.val_mul]
    ring
  rw [hfac, norm_mul, norm_pow, norm_pow, hu, one_pow, one_pow, one_mul]
  rw [norm_eq_of_addVal (y := (l : ℤ_[l]) ^ (j + c) * ((a : ℤ_[l]) - (b : ℤ_[l])))]
  · rw [norm_mul, PadicInt.norm_p_pow, zpow_neg, zpow_natCast]
  · have hcast : ((n : ℤ) : ℤ_[l]) = (l : ℤ_[l]) ^ j * ((a : ℤ_[l]) - (b : ℤ_[l])) := by
      rw [hndef]
      push_cast
      ring
    rw [key, hptU, hcast, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, hval1]
    simp only [nsmul_eq_mul, mul_one]
    push_cast
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.UnipPow
section
open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.unipPow :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (R : ℕ) (g : Module.End ℤ_[l] X), GenBy l R X → Unip g → InPow 1 ((g - 1) ^ R) := by
  intro l _ X _ _ R g hgen hu
  obtain ⟨N, hN⟩ := hu
  let p : Submodule ℤ_[l] X := LinearMap.range ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X))
  have memp : ∀ v : X, v ∈ p ↔ ∃ y, v = (l : ℤ_[l]) ^ 1 • y := by
    intro v
    simp only [p, LinearMap.mem_range, LinearMap.smul_apply, Module.End.one_apply, pow_one]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩
  have hp : p ≤ p.comap (g - 1) := by
    intro v hv
    obtain ⟨y, rfl⟩ := (memp v).mp hv
    rw [Submodule.mem_comap, map_smul]
    exact (memp _).mpr ⟨(g - 1) y, rfl⟩
  let F : Module.End ℤ_[l] (X ⧸ p) := p.mapQ p (g - 1) hp
  have hFx : ∀ x : X, F (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((g - 1) x) :=
    fun x => Submodule.mapQ_apply _ _ _ x
  have key : ∀ (k : ℕ) (x : X), (F ^ k) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (((g - 1) ^ k) x) := by
    intro k
    induction k with
    | zero =>
      intro x
      simp
    | succ k ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, hFx, ih, pow_succ, Module.End.mul_apply]
  have hnil : IsNilpotent F := by
    refine ⟨N, ?_⟩
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective p z
    rw [Submodule.mkQ_apply, key, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero, memp]
    exact hN x
  have hlen : Module.length ℤ_[l] (X ⧸ p) ≤ R := cokL l X R hgen
  have hF0 := nilLen ℤ_[l] (X ⧸ p) F R hnil hlen
  intro x
  have hk := key R x
  rw [hF0, LinearMap.zero_apply, eq_comm, Submodule.Quotient.mk_eq_zero, memp] at hk
  exact hk
end

