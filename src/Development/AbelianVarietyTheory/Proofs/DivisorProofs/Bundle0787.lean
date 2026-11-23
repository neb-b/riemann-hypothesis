module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ
open scoped Matrix

namespace GlobalTheory.ThetaTransform

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

abbrev VA (F : Type) [Field F] [NumberField F] (N : ℕ) : Type := (Fin N → AF F) × (Fin N → AF F)

def symV (w w' : VA F N) : AF F := w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2

def embR {κ : Type} (t : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i)) 0

def IsRealLine (M : ℝ →+ VA F N) : Prop := Continuous M ∧ ∀ t, fin (M t).1 = 0 ∧ fin (M t).2 = 0

def half (F : Type) [Field F] (N : ℕ) : Fin N → F := fun _ => 1 / 2

variable [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)

def heisV (u : VA F N) (f : VA F N → ℂ) : VA F N → ℂ := fun w => ψ (⅟(2 : AF F) * symV w u) * f (w + u)

def thV (Φ : (Fin N → AF F) → ℂ) : VA F N → ℂ := fun w => GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)

def invV (ν : Measure (AF F)) (𝓓 : Set (Fin N → AF F)) (f : VA F N → ℂ) : (Fin N → AF F) → ℂ :=
  fun x => ∫ y in 𝓓, f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) ∂(muV N ν)

def QuasiV (f : VA F N → ℂ) : Prop :=
  ∀ (a b : Fin N → F) (w : VA F N), f ((rat a, rat b) + w) = ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w)) * f w

def LevelV (f : VA F N → ℂ) : Prop :=
  ∃ U : AddSubgroup (VA F N), IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 → heisV ψ u f = f

abbrev ratSub (F : Type) [Field F] [NumberField F] (N : ℕ) : AddSubgroup (Fin N → AF F) :=
  AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))

theorem invOf_two_eq : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  simp

omit [Invertible (2 : AF F)] in
theorem Bd_half (u u' : Fin N → AF F) : Bd (AF F) (half F N) u u' = u ⬝ᵥ u' := by
  simp [Bd, half, dotProduct]

omit [NumberField F] [Invertible (2 : AF F)] in
theorem half_ne_zero [CharZero F] (l : Fin N) : half F N l ≠ 0 := by
  simp [half]

theorem schr_eq_rho (w : VA F N) (Φ : (Fin N → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ w Φ = rho ψ (half F N) w.1 w.2 Φ := by
  funext x
  rw [GlobalTheory.WeilM.schr, rho, Bd_half, Bd_half, invOf_two_eq]

theorem thV_eq_th (Φ : (Fin N → AF F) → ℂ) (w : VA F N) : thV ψ Φ w = th (rho ψ (half F N) w.1 w.2 Φ) := by
  rw [thV, schr_eq_rho]
  rfl

theorem two_mul_invOf (a : AF F) : ⅟(2 : AF F) * a + ⅟(2 : AF F) * a = a := by
  rw [← add_mul, invOf_two_add_invOf_two, one_mul]

theorem schr_schr (w u : VA F N) (Φ : (Fin N → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ u Φ) = ψ (⅟(2 : AF F) * symV w u) • GlobalTheory.WeilM.schr ψ (w + u) Φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  simp only [symV, add_dotProduct, dotProduct_add]
  linear_combination (-1 : AF F) * two_mul_invOf (w.1 ⬝ᵥ u.2)

theorem thV_schr (u : VA F N) (Φ : (Fin N → AF F) → ℂ) : thV ψ (GlobalTheory.WeilM.schr ψ u Φ) = heisV ψ u (thV ψ Φ) := by
  funext w
  rw [thV, schr_schr, heisV, thV]
  exact tsum_mul_left

theorem quasiV_thV (hψ : ∀ a : F, ψ (algebraMap F (AF F) a) = 1) (Φ : (Fin N → AF F) → ℂ) : QuasiV ψ (thV ψ Φ) := by
  intro a b w
  simp only [thV, GlobalTheory.WeilM.thetaSum]
  rw [← tsum_mul_left, ← (Equiv.addRight a).tsum_eq (fun ξ : Fin N → F => ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w)) *
    GlobalTheory.WeilM.schr ψ w Φ fun i => algebraMap F (AF F) (ξ i))]
  refine tsum_congr fun ξ => ?_
  have e1 : (fun i => algebraMap F (AF F) ((Equiv.addRight a ξ) i)) = rat ξ + rat a := by
    funext i; simp [rat]
  have e2 : (fun i => algebraMap F (AF F) (ξ i)) = rat ξ := rfl
  have e3 : ∀ c d : Fin N → F, rat c ⬝ᵥ rat d = algebraMap F (AF F) (c ⬝ᵥ d) := fun c d => by
    simp [rat, dotProduct]
  rw [e1, e2]
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc]
  congr 1
  have h1 := hψ (ξ ⬝ᵥ b + 1 / 2 * (a ⬝ᵥ b))
  rw [← mul_one (ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w) + _)), ← h1, ← AddChar.map_add_eq_mul]
  congr 1
  rw [map_add (f := _), map_mul, ← invOf_two_eq, ← e3, ← e3]
  simp only [symV, add_dotProduct, dotProduct_add]
  linear_combination two_mul_invOf (rat a ⬝ᵥ w.2)

end GlobalTheory.ThetaTransform

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentDoubleCosetCellFiniteDisjointIUnion
section
open Matrix Topology

namespace GlobalTheory.JSW.Cut

open Pointwise

variable {F : Type} [NormedField F] {n : ℕ}

theorem cell_eq_of_mem (B' : Subgroup (GL (Fin n) F)) {x y g : GL (Fin n) F}
    (hx : g ∈ cell x (B' : Set (GL (Fin n) F))) (hy : g ∈ cell y (B' : Set (GL (Fin n) F))) :
    cell x (B' : Set (GL (Fin n) F)) = cell y (B' : Set (GL (Fin n) F)) := by
  obtain ⟨u, hu, k, hk, rfl⟩ := hx
  obtain ⟨u', hu', k', hk', he⟩ := hy
  have hy' : y = (u'⁻¹ * u) * x * (k * k'⁻¹) := by
    calc y = u'⁻¹ * (u' * y * k') * k'⁻¹ := by group
      _ = (u'⁻¹ * u) * x * (k * k'⁻¹) := by rw [← he]; group
  have hx' : x = (u⁻¹ * u') * y * (k' * k⁻¹) := by
    calc x = u⁻¹ * (u * x * k) * k⁻¹ := by group
      _ = (u⁻¹ * u') * y * (k' * k⁻¹) := by rw [he]; group
  ext g
  constructor
  · rintro ⟨v, hv, l, hl, rfl⟩
    refine ⟨v * (u⁻¹ * u'), mul_mem hv (mul_mem (inv_mem hu) hu'), k' * k⁻¹ * l,
      mul_mem (mul_mem hk' (inv_mem hk)) hl, ?_⟩
    rw [hx']; group
  · rintro ⟨v, hv, l, hl, rfl⟩
    refine ⟨v * (u'⁻¹ * u), mul_mem hv (mul_mem (inv_mem hu') hu), k * k'⁻¹ * l,
      mul_mem (mul_mem hk (inv_mem hk')) hl, ?_⟩
    rw [hy']; group

theorem cell_finite_disjoint_union (B B' : Subgroup (GL (Fin n) F)) (hB : IsCompact (B : Set (GL (Fin n) F)))
    (hB' : IsOpen (B' : Set (GL (Fin n) F))) (hle : B' ≤ B) (h₀ : GL (Fin n) F) :
    ∃ s : Finset (GL (Fin n) F), (∀ x ∈ s, x ∈ cell h₀ (B : Set (GL (Fin n) F))) ∧
      cell h₀ (B : Set (GL (Fin n) F)) = (⋃ x ∈ s, cell x (B' : Set (GL (Fin n) F))) ∧
      (s : Set (GL (Fin n) F)).PairwiseDisjoint fun x => cell x (B' : Set (GL (Fin n) F)) := by
  classical

  obtain ⟨t, ht⟩ := hB.elim_finite_subcover (fun b : B => (b : GL (Fin n) F) • (B' : Set (GL (Fin n) F)))
    (fun b => hB'.smul _) (fun b hb => Set.mem_iUnion.2 ⟨⟨b, hb⟩, ⟨1, one_mem _, by simp⟩⟩)
  set S : Finset (GL (Fin n) F) := t.image fun b : B => h₀ * (b : GL (Fin n) F) with hS
  have hSmem : ∀ x ∈ S, x ∈ cell h₀ (B : Set (GL (Fin n) F)) := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨1, one_mem _, b, b.2, by simp⟩
  have hunion : cell h₀ (B : Set (GL (Fin n) F)) = ⋃ x ∈ S, cell x (B' : Set (GL (Fin n) F)) := by
    ext g
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨u, hu, k, hk, rfl⟩
      obtain ⟨b, hbt, hkb⟩ := Set.mem_iUnion₂.1 (ht hk)
      obtain ⟨k', hk', hkk⟩ := hkb
      refine ⟨h₀ * b, Finset.mem_image.2 ⟨b, hbt, rfl⟩, u, hu, k', hk', ?_⟩
      rw [← hkk]; simp [smul_eq_mul, mul_assoc]
    · rintro ⟨x, hx, u, hu, k, hk, rfl⟩
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨u, hu, b * k, mul_mem b.2 (hle hk), by simp [mul_assoc]⟩

  set f : GL (Fin n) F → Set (GL (Fin n) F) := fun x => cell x (B' : Set (GL (Fin n) F)) with hf
  set C : Finset (Set (GL (Fin n) F)) := S.image f with hC
  let rep : C → GL (Fin n) F := fun c => Classical.choose (Finset.mem_image.1 c.2)
  have rep_mem : ∀ c : C, rep c ∈ S := fun c => (Classical.choose_spec (Finset.mem_image.1 c.2)).1
  have rep_eq : ∀ c : C, f (rep c) = c := fun c => (Classical.choose_spec (Finset.mem_image.1 c.2)).2
  refine ⟨C.attach.image rep, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    exact hSmem _ (rep_mem c)
  · rw [hunion]
    ext g
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, hg⟩
      have hc : f x ∈ C := Finset.mem_image.2 ⟨x, hx, rfl⟩
      refine ⟨rep ⟨f x, hc⟩, Finset.mem_image.2 ⟨⟨f x, hc⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
      have := rep_eq ⟨f x, hc⟩
      change g ∈ f (rep ⟨f x, hc⟩)
      rw [this]; exact hg
    · rintro ⟨x, hx, hg⟩
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨rep c, rep_mem c, hg⟩
  · intro x hx y hy hxy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    rw [Function.onFun, Set.disjoint_left]
    intro g hgc hgd
    apply hxy
    have h1 := cell_eq_of_mem B' hgc hgd
    have hcd : c = d := by
      apply Subtype.ext
      rw [← rep_eq c, ← rep_eq d]
      exact h1
    rw [hcd]

theorem cell_finite_disjoint_union' : ∀ {F : Type} [NormedField F] {n : ℕ} (B B' : Subgroup (GL (Fin n) F)), IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B' : Set (GL (Fin n) F)) → B' ≤ B → ∀ h₀ : GL (Fin n) F, ∃ s : Finset (GL (Fin n) F), (∀ x ∈ s, x ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F))) ∧ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F)) = (⋃ x ∈ s, GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F))) ∧ (s : Set (GL (Fin n) F)).PairwiseDisjoint fun x => GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F)) :=
  fun B B' hB hB' hle h₀ => cell_finite_disjoint_union B B' hB hB' hle h₀

end GlobalTheory.JSW.Cut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDerivWeierstrassPOddTorsion
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory

theorem finset_prod_eq_one_of_le_one_eq_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → Γ) (hle : ∀ i ∈ s, f i ≤ 1)
    (hprod : ∏ i ∈ s, f i = 1) : ∀ i ∈ s, f i = 1 := by
  intro i hi
  refine le_antisymm (hle i hi) ?_
  rw [← Finset.mul_prod_erase s f hi] at hprod
  have h2 : ∏ j ∈ s.erase i, f j ≤ 1 :=
    Finset.prod_le_one' (fun j hj => hle j (Finset.mem_of_mem_erase hj))
  calc (1 : Γ) = f i * ∏ j ∈ s.erase i, f j := hprod.symm
    _ ≤ f i := mul_le_of_le_one_right' h2

theorem valuation_derivWeierstrassP_torsion_odd :
    ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 →
      V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N →
      ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice →
        V.valuation (L.derivWeierstrassP z) = V.valuation u ^ 3 := by
  intro L β u V N hβ hβim hu hN hodd z hz hNz
  classical
  have hN0 : (N : ℂ) ≠ 0 := by
    have : N ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
    exact_mod_cast this
  have hstab : MulStable L (N : ℂ) := by
    intro ω hω
    have := L.lattice.smul_mem (N : ℤ) hω
    simpa [zsmul_eq_mul] using this
  have hΔ := latticeCurve_Δ_ne_zero L
  have hvΔ : V.valuation (latticeCurve L).Δ ≠ 0 := by
    simpa using hΔ
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hvΔ
    rw [← hu]; simp
  have hvu : V.valuation u ≠ 0 := by simpa using hu0
  obtain ⟨S, hS⟩ := kerRepsExist L (N : ℂ) hN0 hstab
  have hcard := kerRepsCard L (N : ℂ) S hN0 hstab hS
  have hcardN : S.card + 1 = N * N := by
    have : ((S.card + 1 : ℕ) : ℝ) = ((N * N : ℕ) : ℝ) := by
      push_cast; rw [hcard]; simp [Complex.normSq_apply]
    exact_mod_cast this
  have heven : Even S.card := by
    have hodd2 : Odd (N * N) := hodd.mul hodd
    rw [← hcardN] at hodd2
    obtain ⟨k, hk⟩ := hodd2
    exact ⟨k, by omega⟩
  have hpf := _root_.GlobalTheory.CMModel.prod_derivWeierstrassP_kerReps_pow_four_mul L (N : ℂ) S hN0 hstab hS heven
  have hmem : ∀ t ∈ S, V.valuation (L.derivWeierstrassP t / u ^ 3) ≤ 1 := by
    intro t ht
    rw [ValuationSubring.valuation_le_one_iff]
    exact (_root_.GlobalTheory.CMModel.TorsMemVal.main L β u V N hβ hβim hu hN t t (hS.1 t ht).2 (hS.1 t ht).2 (hS.1 t ht).1
      (hS.1 t ht).1).1
  have hprod : ∏ t ∈ S, V.valuation (L.derivWeierstrassP t / u ^ 3) ^ 4 = 1 := by
    have hv := congrArg V.valuation hpf
    simp only [map_mul, map_pow, map_prod, hN, one_pow, mul_one] at hv
    simp only [map_div₀, map_pow, div_pow, Finset.prod_div_distrib, Finset.prod_pow,
      Finset.prod_const, ← pow_mul]
    rw [hv, ← hu, ← pow_mul, div_eq_one_iff_eq (pow_ne_zero _ hvu)]
    ring_nf
  have hall := finset_prod_eq_one_of_le_one_eq_one S _ (fun t ht => pow_le_one' (hmem t ht) 4) hprod
  obtain ⟨t, ht, hzt⟩ := hS.2.2 z (by simpa [mul_comm] using hNz) hz
  have hper : L.derivWeierstrassP z = L.derivWeierstrassP t := by
    have := L.derivWeierstrassP_add_coe t ⟨z - t, hzt⟩
    simpa using this
  have h1 : V.valuation (L.derivWeierstrassP t / u ^ 3) = 1 := by
    have h4 := hall t ht
    by_contra hne
    have hlt : V.valuation (L.derivWeierstrassP t / u ^ 3) < 1 := lt_of_le_of_ne (hmem t ht) hne
    exact absurd h4 (ne_of_lt (pow_lt_one' hlt (by norm_num)))
  rw [hper]
  rw [map_div₀, map_pow, div_eq_one_iff_eq (pow_ne_zero _ hvu)] at h1
  exact h1
end GlobalTheory
end

