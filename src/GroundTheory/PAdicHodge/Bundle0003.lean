module

public import Mathlib
public import GroundTheory.PAdicHodge.KerTheta
public import GroundTheory.PAdicHodge.TiltValuation
public import GroundTheory.PAdicHodge.SenTateCharUnits
public import GroundTheory.PAdicHodge.NormalizedTraceClosure
public import GroundTheory.PAdicHodge.NormalizedTrace
public import GroundTheory.PAdicHodge.AxLemma
public import GroundTheory.PAdicHodge.Bundle0002
public import GroundTheory.PAdicHodge.Bundle0001
public import GroundTheory.PAdicHodge.PerfectoidField

@[expose] public section

-- bundled from GroundTheory.PAdicHodge.KerFontaineThetaCompFrobeniusEquivSymmPow
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open WittVector

section WittGeneral

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

variable [CharP R p]

theorem WittVector.frobenius_teichmuller (a : R) :
    frobenius (teichmuller p a) = teichmuller p (a ^ p) := by
  rw [frobenius_eq_map_frobenius, map_teichmuller, frobenius_def]


def WittVector.teichmullerSeries (a : ℕ → R) : WittVector p R :=
  WittVector.mk p fun n => a n ^ p ^ n

omit hp [CharP R p] in
theorem WittVector.teichmullerSeries_coeff (a : ℕ → R) (n : ℕ) :
    (WittVector.teichmullerSeries (p := p) a).coeff n = a n ^ p ^ n := rfl

theorem WittVector.coeff_sum_teichmuller_mul_pow (a : ℕ → R) (n j : ℕ) :
    (∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : WittVector p R) ^ i).coeff j =
      if j ≤ n then a j ^ p ^ j else 0 := by
  rw [WittVector.sum_coeff_eq_coeff_sum]
  · split_ifs with hj
    · rw [Finset.sum_eq_single_of_mem j (Finset.mem_Iic.2 hj) fun i _ hij =>
        teichmuller_mul_pow_coeff_of_ne _ (Ne.symm hij), teichmuller_mul_pow_coeff]
    · refine Finset.sum_eq_zero fun i hi => teichmuller_mul_pow_coeff_of_ne _ ?_
      rintro rfl
      exact hj (Finset.mem_Iic.1 hi)
  · refine fun m => ⟨fun ⟨i, _, hi⟩ ⟨k, _, hk⟩ => ?_⟩
    ext
    dsimp only [ne_eq, Set.mem_ofPred_eq] at hi hk ⊢
    rw [← Not.imp_symm (teichmuller_mul_pow_coeff_of_ne _) hi]
    exact Not.imp_symm (teichmuller_mul_pow_coeff_of_ne _) hk

variable [PerfectRing R p]

theorem WittVector.eq_teichmullerSeries_iff (a : ℕ → R) (x : WittVector p R) :
    x = WittVector.teichmullerSeries a ↔
      ∀ n, (p : WittVector p R) ^ (n + 1) ∣
        x - ∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : WittVector p R) ^ i := by
  have key : ∀ (n : ℕ) (d : WittVector p R), (p : WittVector p R) ^ (n + 1) ∣ d ↔
      ∀ j < n + 1, d.coeff j = 0 := fun n d => by
    rw [← Ideal.mem_span_singleton, mem_span_p_pow_iff_le_coeff_eq_zero]
  simp_rw [key, ← le_coeff_eq_iff_le_sub_coeff_eq_zero]
  constructor
  · rintro rfl n j hj
    rw [WittVector.coeff_sum_teichmuller_mul_pow, if_pos (Nat.lt_succ_iff.1 hj),
      WittVector.teichmullerSeries_coeff]
  · intro h
    ext j
    rw [h j j (Nat.lt_succ_self j), WittVector.coeff_sum_teichmuller_mul_pow, if_pos le_rfl,
      WittVector.teichmullerSeries_coeff]

theorem WittVector.dvd_sub_sum_teichmullerSeries (a : ℕ → R) (n : ℕ) :
    (p : WittVector p R) ^ (n + 1) ∣ WittVector.teichmullerSeries a -
      ∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : WittVector p R) ^ i :=
  (WittVector.eq_teichmullerSeries_iff a _).1 rfl n

theorem frobeniusEquiv_pow_apply (y : R) (n : ℕ) :
    ((_root_.frobeniusEquiv R p) ^ n) y = y ^ p ^ n := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RingAut.mul_apply, ih, _root_.frobeniusEquiv_apply, frobenius_def, ← pow_mul,
      ← pow_succ']

theorem frobeniusEquiv_symm_pow_apply_pow (y : R) (n : ℕ) :
    ((_root_.frobeniusEquiv R p).symm ^ n) y ^ p ^ n = y := by
  rw [← frobeniusEquiv_pow_apply]
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ', RingAut.mul_apply, RingAut.mul_apply, RingEquiv.apply_symm_apply, ih]

theorem WittVector.teichmullerSeries_coeff_eq (x : WittVector p R) :
    WittVector.teichmullerSeries (fun n => ((_root_.frobeniusEquiv R p).symm ^ n) (x.coeff n)) =
      x := by
  ext n
  rw [WittVector.teichmullerSeries_coeff, frobeniusEquiv_symm_pow_apply_pow]

end WittGeneral

section Frobenius

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]



theorem WittVector.frobeniusEquiv_coeff (x : WittVector p R) (n : ℕ) :
    (WittVector.frobeniusEquiv p R x).coeff n = x.coeff n ^ p := by
  rw [WittVector.frobeniusEquiv_apply, coeff_frobenius_charP]

theorem WittVector.frobeniusEquiv_teichmuller (a : R) :
    WittVector.frobeniusEquiv p R (teichmuller p a) = teichmuller p (a ^ p) := by
  rw [WittVector.frobeniusEquiv_apply, WittVector.frobenius_teichmuller]

theorem WittVector.frobeniusEquiv_symm_teichmuller (a : R) :
    (WittVector.frobeniusEquiv p R).symm (teichmuller p a) =
      teichmuller p ((_root_.frobeniusEquiv R p).symm a) := by
  apply (WittVector.frobeniusEquiv p R).injective
  rw [RingEquiv.apply_symm_apply, WittVector.frobeniusEquiv_teichmuller, frobeniusEquiv_symm_pow_p]

theorem WittVector.frobeniusEquiv_symm_pow_teichmuller (a : R) (n : ℕ) :
    ((WittVector.frobeniusEquiv p R).symm ^ n) (teichmuller p a) =
      teichmuller p (((_root_.frobeniusEquiv R p).symm ^ n) a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', RingAut.mul_apply, ih, WittVector.frobeniusEquiv_symm_teichmuller, pow_succ',
      RingAut.mul_apply]

theorem WittVector.frobeniusEquiv_pow_teichmuller (a : R) (n : ℕ) :
    (WittVector.frobeniusEquiv p R ^ n) (teichmuller p a) = teichmuller p (a ^ p ^ n) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', RingAut.mul_apply, ih, WittVector.frobeniusEquiv_teichmuller, ← pow_mul,
      ← pow_succ]

end Frobenius

abbrev AInf (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] (p : ℕ) [Fact p.Prime] :=
  WittVector p (PreTilt (normInteger K) p)

namespace AInf

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]


end AInf

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.SenTateCharClosure
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open IntermediateField

variable {p : ℕ} [hp : Fact p.Prime]

def inertiaGal (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Subgroup Gal(PadicAlgCl p/K) where
  carrier := {σ | ∀ y : PadicAlgCl p, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1}
  one_mem' := fun y _ => by simp
  mul_mem' := fun {σ τ} hσ hτ y hy => by
    have hτy : ‖τ y‖ ≤ 1 := by rwa [norm_gal_apply]
    have e : (σ * τ) y - y = (σ (τ y) - τ y) + (τ y - y) := by
      rw [AlgEquiv.mul_apply]; ring
    rw [e]
    exact lt_of_le_of_lt ((PadicAlgCl.isNonarchimedean p) _ _) (max_lt (hσ _ hτy) (hτ y hy))
  inv_mem' := fun {σ} hσ y hy => by
    have e : σ (σ⁻¹ y - y) = -(σ y - y) := by
      rw [map_sub, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]; ring
    rw [← norm_gal_apply σ, e, norm_neg]
    exact hσ y hy

theorem mem_inertiaGal {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {σ : Gal(PadicAlgCl p/K)} :
    σ ∈ inertiaGal K ↔ ∀ y : PadicAlgCl p, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1 := Iff.rfl

namespace SenTateChar

open SenTateChar

theorem exists_mem_inertiaGal_unitsOneAdd_two (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ) (hη : Continuous η)
    (hinf : (η '' (inertiaGal K : Set Gal(PadicAlgCl p/K))).Infinite) :
    ∃ τ ∈ inertiaGal K, η τ ∈ unitsOneAdd p 2 ∧ η τ ≠ 1 := by
  by_contra hne
  push Not at hne
  apply hinf
  set U : Subgroup Gal(PadicAlgCl p/K) := (unitsOneAdd p 2).comap η
  have hU : IsOpen (U : Set Gal(PadicAlgCl p/K)) := (isOpen_unitsOneAdd 2).preimage hη
  have hfin : Finite (Gal(PadicAlgCl p/K) ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  classical

  let f : Gal(PadicAlgCl p/K) ⧸ U → ℤ_[p]ˣ := fun c =>
    if h : ∃ τ ∈ inertiaGal K, (τ : Gal(PadicAlgCl p/K) ⧸ U) = c then η h.choose else 1
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨τ, hτ, rfl⟩
  refine ⟨(τ : Gal(PadicAlgCl p/K) ⧸ U), ?_⟩
  have h : ∃ τ' ∈ inertiaGal K, (τ' : Gal(PadicAlgCl p/K) ⧸ U) = τ := ⟨τ, hτ, rfl⟩
  simp only [f, dif_pos h]
  obtain ⟨hτ', hτ'U⟩ := h.choose_spec
  have hq : (h.choose)⁻¹ * τ ∈ U := QuotientGroup.eq.1 hτ'U
  have hI : (h.choose)⁻¹ * τ ∈ inertiaGal K := mul_mem (inv_mem hτ') hτ
  have h1 : η ((h.choose)⁻¹ * τ) = 1 := hne _ hI hq
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

theorem eq_zero_of_tower (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ)
    (M : ℕ → IntermediateField K (PadicAlgCl p)) (hM : Monotone M)
    [∀ k, FiniteDimensional K (M k)]
    (hstab : ∀ (σ : Gal(PadicAlgCl p/K)) (k : ℕ), ∀ y ∈ M k, σ y ∈ M k)
    (hker : ∀ σ : Gal(PadicAlgCl p/K), (∀ k, σ ∈ (M k).fixingSubgroup) → η σ = 1)
    (C : ℝ) (n₁ : ℕ)
    (hbound : ∀ n, n₁ ≤ n → ∀ m, ∀ y ∈ M m, ‖normTrace (M n) y‖ ≤ C * ‖y‖)
    (hgen : ∀ n, n₁ ≤ n → ∃ γ ∈ (M n).fixingSubgroup, η γ ≠ 1)
    {x : ℂ_[p]}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), algebraMap ℚ_[p] ℂ_[p] ((η σ : ℤ_[p]) : ℚ_[p]) * (σ • x) = x) :
    x = 0 := by
  classical
  set Ms : IntermediateField K (PadicAlgCl p) := ⨆ k, M k with hMs
  set E : IntermediateField ℚ_[p] (PadicAlgCl p) := Ms.restrictScalars ℚ_[p] with hE
  have hdir : Directed (· ≤ ·) M := hM.directed_le
  have hmemE : ∀ {y : PadicAlgCl p}, y ∈ E → ∃ m, y ∈ M m := fun {y} hy => by
    have h : y ∈ ((⨆ k, M k : IntermediateField K (PadicAlgCl p)) : Set (PadicAlgCl p)) :=
      (mem_restrictScalars _).1 hy
    rw [coe_iSup_of_directed hdir, Set.mem_iUnion] at h
    exact h
  have hME : ∀ {m} {y : PadicAlgCl p}, y ∈ M m → y ∈ E := fun {m} {y} hy =>
    (mem_restrictScalars _).2 (le_iSup M m hy)

  have hxc : x ∈ closureInCp E := by
    have hfixed : ∀ σ ∈ Ms.fixingSubgroup, σ • x = x := by
      intro σ hσ
      have h1 : η σ = 1 := hker σ fun k => by
        rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
        exact fun y hy => hσ y (le_iSup M k hy)
      have := hx σ
      rwa [h1, Units.val_one, PadicInt.coe_one, map_one, one_mul] at this
    have h := fixedPoints_closedSubgroup_eq_closure Ms.fixingSubgroup
      (InfiniteGalois.fixingSubgroup_isClosed Ms)
    have hx' : x ∈ {x : ℂ_[p] | ∀ σ ∈ Ms.fixingSubgroup, σ • x = x} := hfixed
    rw [h, InfiniteGalois.fixedField_fixingSubgroup] at hx'
    exact hx'

  have hC1 : 1 ≤ C := by
    have h := hbound n₁ le_rfl n₁ 1 (one_mem _)
    rwa [normTrace_of_mem _ (one_mem _), norm_one, mul_one] at h
  have hC0 : 0 ≤ C := zero_le_one.trans hC1

  have hadd : ∀ n, ∀ y ∈ E, ∀ z ∈ E, normTrace (M n) (y + z) = normTrace (M n) y + normTrace (M n) z :=
    fun n y _ z _ => normTrace_add _ y z
  have hbd : ∀ n, n₁ ≤ n → ∀ y ∈ E, ‖normTrace (M n) y‖ ≤ C * ‖y‖ := by
    intro n hn y hy
    obtain ⟨m, hm⟩ := hmemE hy
    exact hbound n hn m y hm
  have hmapsE : ∀ (σ : Gal(PadicAlgCl p/K)), ∀ y ∈ E, σ y ∈ E := by
    intro σ y hy
    obtain ⟨m, hm⟩ := hmemE hy
    exact hME (hstab σ m y hm)
  have hcomm : ∀ (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p),
      normTrace (M n) (σ y) = σ (normTrace (M n) y) := by
    intro σ n y
    refine normTrace_map_of_map_eq (M n) σ ?_ y
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hstab σ n z hz
    · intro z hz
      refine ⟨σ⁻¹ z, hstab σ⁻¹ n z hz, ?_⟩
      change σ (σ⁻¹ z) = z
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

  have hR : ∀ n, n₁ ≤ n → extendToClosure E (normTrace (M n)) x = 0 := by
    intro n hn
    set k' : IntermediateField ℚ_[p] (PadicAlgCl p) := (M n).restrictScalars ℚ_[p]
    have : FiniteDimensional ℚ_[p] (M n) := Module.Finite.trans K (M n)
    have : FiniteDimensional ℚ_[p] k' := (inferInstance : FiniteDimensional ℚ_[p] (M n))
    have hkE : k' ≤ E := fun y hy => hME ((mem_restrictScalars _).1 hy)
    have hmaps : ∀ y ∈ E, normTrace (M n) y ∈ k' := fun y _ =>
      (mem_restrictScalars _).2 (normTrace_mem _ y)
    have hfix : ∀ a ∈ k', normTrace (M n) a = a := fun a ha =>
      normTrace_of_mem _ ((mem_restrictScalars _).1 ha)
    have hmul : ∀ a ∈ k', ∀ y ∈ E, normTrace (M n) (a * y) = a * normTrace (M n) y :=
      fun a ha y _ => normTrace_mul_of_mem _ ((mem_restrictScalars _).1 ha) y
    obtain ⟨γ, hγ, hγη⟩ := hgen n hn
    obtain ⟨b, hb, hbx⟩ := extendToClosure_mem (hadd n) (hbd n hn) hmaps hxc

    set q : ℚ_[p] := ((η γ : ℤ_[p]) : ℚ_[p])
    have hq : algebraMap ℚ_[p] ℂ_[p] q = ((algebraMap ℚ_[p] (PadicAlgCl p) q : PadicAlgCl p) : ℂ_[p]) :=
      rfl
    have hqk : algebraMap ℚ_[p] (PadicAlgCl p) q ∈ k' := k'.algebraMap_mem q
    have hγx : γ • x ∈ closureInCp E := smul_mem_closureInCp γ (hmapsE γ) hxc
    have key : extendToClosure E (normTrace (M n)) x =
        algebraMap ℚ_[p] ℂ_[p] q * extendToClosure E (normTrace (M n)) x := by
      conv_lhs => rw [← hx γ]
      rw [hq, extendToClosure_mul (hadd n) (hbd n hn) hkE hmul hqk hγx,
        extendToClosure_smul (hadd n) (hbd n hn) γ (hmapsE γ) (fun y _ => hcomm γ n y) hxc, ← hbx,
        gal_smul_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hγ b ((mem_restrictScalars _).1 hb)]
    have hq1 : algebraMap ℚ_[p] ℂ_[p] q ≠ 1 := by
      rw [Ne, ← map_one (algebraMap ℚ_[p] ℂ_[p]), (algebraMap ℚ_[p] ℂ_[p]).injective.eq_iff]
      intro h
      apply hγη
      have h' : (η γ : ℤ_[p]) = 1 := Subtype.ext (by simpa [q] using h)
      exact Units.ext h'
    have h2 : (algebraMap ℚ_[p] ℂ_[p] q - 1) * extendToClosure E (normTrace (M n)) x = 0 := by
      rw [sub_mul, one_mul, ← key, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hq1)

  have hbound' : ∀ ε > 0, ‖x‖ ≤ (1 + C) * ε := by
    intro ε hε
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := Metric.mem_closure_iff.1 hxc ε hε
    obtain ⟨m, hm⟩ := hmemE hy
    set m' := max m n₁
    have hym : y ∈ M m' := hM (le_max_left _ _) hm
    have hyc : (y : ℂ_[p]) ∈ closureInCp E := coe_mem_closureInCp hy
    have hsub : (y : ℂ_[p]) - x ∈ closureInCp E := sub_mem_closureInCp hyc hxc
    have hadd' := hadd m'
    have hbd' := hbd m' (le_max_right _ _)
    have h1 : extendToClosure E (normTrace (M m')) (y : ℂ_[p]) =
        extendToClosure E (normTrace (M m')) ((y : ℂ_[p]) - x) +
          extendToClosure E (normTrace (M m')) x := by
      rw [extendToClosure_sub hadd' hbd' hyc hxc]
      ring
    rw [extendToClosure_coe hadd' hbd' hy, normTrace_of_mem _ hym, hR m' (le_max_right _ _),
      add_zero] at h1
    have h2 : ‖(y : ℂ_[p])‖ ≤ C * ε := by
      rw [h1]
      refine (norm_extendToClosure_le hadd' hbd' hsub).trans ?_
      rw [← dist_eq_norm, dist_comm]
      exact mul_le_mul_of_nonneg_left hxy.le hC0
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - (y : ℂ_[p])‖ + ‖(y : ℂ_[p])‖ := norm_add_le _ _
      _ ≤ ε + C * ε := add_le_add (by rw [← dist_eq_norm]; exact hxy.le) h2
      _ = (1 + C) * ε := by ring
  by_contra hx0
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have h := hbound' (‖x‖ / (2 * (1 + C))) (by positivity)
  have h' : (1 + C) * (‖x‖ / (2 * (1 + C))) = ‖x‖ / 2 := by
    field_simp
  rw [h'] at h
  linarith

end SenTateChar

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.SlopeRobbaDegree
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent Module

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)]


variable (K) in
def dvUnif : K := ((IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose : K)

theorem irreducible_dvUnif :
    Irreducible (IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose :=
  (IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose_spec

theorem norm_eq_one_of_isUnit {z : normInteger K} (hz : IsUnit z) : ‖(z : K)‖ = 1 := by
  have := (normInteger_integers (K := K)).isUnit_iff_valuation_eq_one.1 hz
  rw [NormedField.valuation_apply, ← NNReal.coe_eq_one] at this
  exact this

theorem exists_norm_eq_zpow {x : K} (hx : x ≠ 0) : ∃ n : ℤ, ‖x‖ = ‖dvUnif K‖ ^ n := by
  have key : ∀ y : K, y ≠ 0 → ‖y‖ ≤ 1 → ∃ n : ℕ, ‖y‖ = ‖dvUnif K‖ ^ n := by
    intro y hy hy1
    let z : normInteger K := ⟨y, mem_normInteger.2 hy1⟩
    have hz : z ≠ 0 := fun h => hy (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz irreducible_dvUnif
    refine ⟨n, ?_⟩
    have h2 := congrArg (fun w : normInteger K => (w : K)) hu
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow] at h2
    rw [show y = (z : K) from rfl, h2, norm_mul, norm_pow, norm_eq_one_of_isUnit u.isUnit, one_mul]
    rfl
  rcases le_total ‖x‖ 1 with h | h
  · obtain ⟨n, hn⟩ := key x hx h
    exact ⟨n, by rw [hn, zpow_natCast]⟩
  · obtain ⟨n, hn⟩ := key x⁻¹ (inv_ne_zero hx) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h)
    refine ⟨-(n : ℤ), ?_⟩
    rw [norm_inv] at hn
    rw [zpow_neg, zpow_natCast, ← hn, inv_inv]

namespace Robba

end Robba

namespace Robba

end Robba

namespace PhiModule

open Matrix

end PhiModule

end GroundTheory.PAdicHodge
end
end

