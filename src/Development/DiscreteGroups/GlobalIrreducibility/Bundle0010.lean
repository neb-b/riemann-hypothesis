module

public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0009
public import Mathlib
public import Development.DiscreteGroups.GlobalIrreducibility.LConvSepL

@[expose] public section

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.ExistsAvgNotMem
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.LConvGenF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) {c : kˣ} (hc : HasConductor ψ c)

include hc in
theorem exists_avg_notMem (W : Submodule ℂ V) {s t : kˣ} {x : V} (hx : ∀ h ∈ ball s, σ h x = x)
    (hxW : x ∉ W) : ∃ ξ ∈ ball (c * s⁻¹), avg ψ σ s t ξ x ∉ W := by
  by_contra hall
  push Not at hall
  apply hxW
  have hsum := sum_avg ψ σ (c := c) hc (t := t) hx
  have hm : ((Fintype.card (Q (c * t⁻¹) (c * s⁻¹)) : ℕ) : ℂ) • x ∈ W := by
    rw [← hsum]
    exact W.sum_mem fun f _ => hall _ (out_mem f)
  exact (W.smul_mem_iff (card_ne_zero _ _)).1 hm

include hc in
theorem avg_shift {s t : kˣ} {ξ h : k} (hh : h ∈ ball (c * t⁻¹)) : avg ψ σ s t (ξ + h) = avg ψ σ s t ξ := by
  simp only [avg]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [add_mul, neg_add, ch_add ψ, psi_neg_triv hc hh (out_mem q), Circle.coe_one, mul_one]

include hc in
theorem isClosed_notMem (W : Submodule ℂ V) (s t : kˣ) (x : V) :
    IsClosed {ξ : k | avg ψ σ s t ξ x ∉ W} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro ξ hξ
  have hU : (fun η => η - ξ) ⁻¹' ((ball (c * t⁻¹) : AddSubgroup k) : Set k) ∈ nhds ξ :=
    ((isOpen_ball _).preimage (continuous_sub_right ξ)).mem_nhds (by simp [(ball _).zero_mem])
  refine Filter.mem_of_superset hU fun η hη => ?_
  have : η = ξ + (η - ξ) := by ring
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hξ ⊢
  rw [this, avg_shift ψ σ hc hη]
  exact hξ

variable (hadd : ∀ a b, σ (a + b) = σ a * σ b)

include hadd in
theorem key_step (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W)
    (hsm : ∀ v : V, ∃ s : kˣ, ∀ h ∈ ball s, σ h v = v) {s : kˣ} {x : V} (hs : ∀ h ∈ ball s, σ h x = x) {ξ : k}
    (hξs : ∀ h ∈ ball s, ψ (ξ * h) = 1)
    (hx : x ∈ W ⊔ Submodule.span ℂ {z | ∃ (a : k) (y : V), z = σ a y - ((ψ (ξ * a) : Circle) : ℂ) • y}) :
    ∃ t' : kˣ, valuation k (s : k) ≤ valuation k (t' : k) ∧ avg ψ σ s t' ξ x ∈ W := by
  let P : V → Prop := fun z => ∃ s' t' : kˣ, valuation k (s' : k) ≤ valuation k (s : k) ∧
    valuation k (s : k) ≤ valuation k (t' : k) ∧ ∀ s'' t'' : kˣ, valuation k (s'' : k) ≤ valuation k (s' : k) →
      valuation k (t' : k) ≤ valuation k (t'' : k) → avg ψ σ s'' t'' ξ z ∈ W
  have Padd : ∀ z1 z2, P z1 → P z2 → P (z1 + z2) := by
    rintro z1 z2 ⟨s1, t1, hs1, ht1, h1⟩ ⟨s2, t2, hs2, ht2, h2⟩
    obtain ⟨s', a1, a2⟩ := exists_min s1 s2
    obtain ⟨t', b1, b2⟩ := exists_max t1 t2
    refine ⟨s', t', a1.trans hs1, ht1.trans b1, fun s'' t'' h1' h2' => ?_⟩
    rw [map_add (f := _)]
    exact W.add_mem (h1 _ _ (h1'.trans a1) (b1.trans h2')) (h2 _ _ (h1'.trans a2) (b2.trans h2'))
  have PW : ∀ w ∈ W, P w := fun w hw => ⟨s, s, le_rfl, le_rfl, fun _ _ _ _ => avg_mem ψ σ W hW _ _ _ hw⟩
  have Pspan : ∀ z ∈ Submodule.span ℂ {z | ∃ (a : k) (y : V), z = σ a y - ((ψ (ξ * a) : Circle) : ℂ) • y},
      P z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, y, rfl⟩ := hz
      obtain ⟨sy, hsy⟩ := hsm y
      obtain ⟨ta, hta⟩ := exists_ball_mem a
      obtain ⟨s', a1, a2⟩ := exists_min s sy
      obtain ⟨t', b1, b2⟩ := exists_max s ta
      refine ⟨s', t', a1, b1, fun s'' t'' h1 h2 => ?_⟩
      have hy'' : ∀ h ∈ ball s'', σ h y = y := fun h hh => hsy h (ball_mono (h1.trans a2) hh)
      have hξ'' : ∀ h ∈ ball s'', ψ (ξ * h) = 1 := fun h hh => hξs h (ball_mono (h1.trans a1) hh)
      have ha : a ∈ ball t'' := ball_mono (b2.trans h2) hta
      rw [map_sub, map_smul, ← Module.End.mul_apply, avg_comm ψ σ hadd, Module.End.mul_apply,
        avg_eigen ψ σ hadd hξ'' hy'' ha, sub_self]
      exact W.zero_mem
    | zero => exact PW 0 W.zero_mem
    | add z1 z2 _ _ h1 h2 => exact Padd z1 z2 h1 h2
    | smul r z _ h =>
      obtain ⟨s', t', a1, b1, hz⟩ := h
      exact ⟨s', t', a1, b1, fun s'' t'' h1 h2 => by rw [map_smul]; exact W.smul_mem r (hz _ _ h1 h2)⟩
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨s', t', hs', ht', h⟩ := Padd w y (PW w hw) (Pspan y hy)
  refine ⟨t', ht', ?_⟩
  have h1 := h s' t' le_rfl le_rfl
  have e := avg_level ψ σ hadd (t := t') hs' hξs hs
  have hm : ((Fintype.card (Q s' t') : ℕ) : ℂ) • avg ψ σ s t' ξ (w + y) ∈ W := by
    rw [← e]; exact W.smul_mem _ h1
  exact (W.smul_mem_iff (card_ne_zero _ _)).1 hm


include hc hadd in
theorem exists_character_sup_ne_top (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W)
    (hsm : ∀ v : V, ∃ s : kˣ, ∀ h ∈ ball s, σ h v = v) (hne : W ≠ ⊤) :
    ∃ ξ : k, W ⊔ Submodule.span ℂ {z | ∃ (a : k) (y : V), z = σ a y - ((ψ (ξ * a) : Circle) : ℂ) • y} ≠ ⊤ := by
  obtain ⟨x, hxW⟩ : ∃ x, x ∉ W := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun x _ => h x)
  obtain ⟨s, hs⟩ := hsm x
  let ι := {t : kˣ // valuation k (s : k) ≤ valuation k (t : k)}
  haveI : Nonempty ι := ⟨⟨s, le_rfl⟩⟩
  let C : ι → Set k := fun t => ((ball (c * s⁻¹) : AddSubgroup k) : Set k) ∩ {ξ | avg ψ σ s t.1 ξ x ∉ W}
  have hdir : Directed (· ⊇ ·) C := by
    intro t1 t2
    rcases le_total (valuation k (t1.1 : k)) (valuation k (t2.1 : k)) with h | h
    · exact ⟨t2, fun ξ hξ => ⟨hξ.1, fun hm => hξ.2 (avg_mono_mem ψ σ hadd W hW h (psi_triv hc hξ.1) hs hm)⟩,
        le_rfl⟩
    · exact ⟨t1, le_rfl, fun ξ hξ => ⟨hξ.1, fun hm => hξ.2 (avg_mono_mem ψ σ hadd W hW h (psi_triv hc hξ.1) hs hm)⟩⟩
  have hnon : ∀ t, (C t).Nonempty := fun t => by
    obtain ⟨ξ, h1, h2⟩ := exists_avg_notMem ψ σ hc W (t := t.1) hs hxW
    exact ⟨ξ, h1, h2⟩
  have hcl : ∀ t, IsClosed (C t) := fun t =>
    ((ball _).isClosed_of_isOpen (isOpen_ball _)).inter (isClosed_notMem ψ σ hc W s t.1 x)
  have hcpt : ∀ t, IsCompact (C t) := fun t => (isCompact_cball _).inter_right (isClosed_notMem ψ σ hc W s t.1 x)
  obtain ⟨ξ, hξ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hnon hcpt hcl
  rw [Set.mem_iInter] at hξ
  have hξs := psi_triv hc (hξ ⟨s, le_rfl⟩).1
  refine ⟨ξ, fun htop => ?_⟩
  obtain ⟨t', ht', hm⟩ := key_step ψ σ hadd W hW hsm hs hξs (x := x) (by rw [htop]; exact Submodule.mem_top)
  exact (hξ ⟨t', ht'⟩).2 hm

end DiscreteGroups.sglob.LConvGenF
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvKirC
section
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConvKir

theorem sum_char_eq_zero {A : Type} [AddCommGroup A] (L L'' : AddSubgroup A)
    [Fintype (L ⧸ L''.addSubgroupOf L)] (χ : A → ℂ) (hχ : ∀ x y, χ (x + y) = χ x * χ y)
    (h'' : ∀ x ∈ L'', χ x = 1) (x₀ : L) (hne : χ x₀ ≠ 1) :
    ∑ q : L ⧸ L''.addSubgroupOf L, χ ((Quotient.out q : L) : A) = 0 := by
  have hterm : ∀ q : L ⧸ L''.addSubgroupOf L,
      χ ((Quotient.out ((x₀ : L ⧸ L''.addSubgroupOf L) + q) : L) : A) = χ x₀ * χ ((Quotient.out q : L) : A) := by
    intro q
    set z := Quotient.out ((x₀ : L ⧸ L''.addSubgroupOf L) + q) with hz
    have hq : ((z : L) : L ⧸ L''.addSubgroupOf L) = ((x₀ + Quotient.out q : L) : L ⧸ L''.addSubgroupOf L) := by
      rw [hz, QuotientAddGroup.out_eq', QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
    have hd := AddSubgroup.mem_addSubgroupOf.1 (QuotientAddGroup.eq.1 hq)
    have e : (x₀ : A) + ((Quotient.out q : L) : A) = (z : A) + ((-z + (x₀ + Quotient.out q) : L) : A) := by
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]; abel
    rw [← hχ, e, hχ, h'' _ hd, mul_one]
  have hT := Equiv.sum_comp (Equiv.addLeft ((x₀ : L ⧸ L''.addSubgroupOf L))) (fun q => χ ((Quotient.out q : L) : A))
  simp only [Equiv.coe_addLeft, hterm, ← Finset.mul_sum] at hT
  have h0 : (χ x₀ - 1) * ∑ q : L ⧸ L''.addSubgroupOf L, χ ((Quotient.out q : L) : A) = 0 := by
    rw [sub_mul, hT, one_mul, sub_self]
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)

variable {k : Type} [Field k]

theorem psi_neg_mul (ψ : AddChar k Circle) (t : k) : ((ψ (-t) : Circle) : ℂ) * (ψ t : ℂ) = 1 := by
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]

theorem l_gU {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle)
    (ρ : Representation ℂ (GL (Fin (m + 1)) k) V) (l : Module.Dual ℂ V) (hl : IsFunctional ψ ρ l)
    (j : ℕ) (hj : j + 1 < m + 1) (g : GL (Fin (m + 1)) k) (hg : InH (j + 1) g) (x : Fin (m + 1) → k) (w : V) :
    l (ρ g (ρ (U ⟨j + 1, hj⟩ x) w)) =
      (ψ (∑ r, (if r < (⟨j + 1, hj⟩ : Fin (m + 1)) then
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ⟨j, by omega⟩ r else 0) * x r) : ℂ) * l (ρ g w) := by
  rw [← Module.End.mul_apply, ← map_mul, conj_U j hj g hg x, map_mul, Module.End.mul_apply,
    hl _ (U_mem _ _), superDiag_U]

end DiscreteGroups.sglob.LConvKir
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvSepW
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle} (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ}
  {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ}

include hψ in
theorem lam_unip (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) (y : WT (m := m) ψ) {u : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) :
    lam ψ hψ I B (rhoW ψ u y) = ((ψ⁻¹ (superDiag u) : Circle) : ℂ) * lam ψ hψ I B y := by
  obtain ⟨K, hK, hKy⟩ := exists_good_fix hψ y y
  have hK' := good_conj hK hu
  have hfix' : ∀ κ ∈ K.map (MulAut.conj u).toMonoidHom, rhoW ψ κ (rhoW ψ u y) = rhoW ψ u y := by
    intro κ hκ
    have e : κ * u = u * (u⁻¹ * κ * u) := by group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (hKy _ (mem_conj.1 hκ)).1]
  rw [lam_eq hψ hI hB hK' hfix', lam_eq hψ hI hB hK (fun κ hκ => (hKy κ hκ).1)]
  have hB' : B (rhoW ψ u y) (delta ψ (K.map (MulAut.conj u).toMonoidHom)) =
      ((ψ⁻¹ (superDiag u) : Circle) : ℂ) * B y (delta ψ K) := by
    rw [← hB.2.2 u⁻¹ (rhoW ψ u y), ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, rhoW_inv_delta_conj hK hu, map_smul, smul_eq_mul]
  have hc' : cK ψ I (K.map (MulAut.conj u).toMonoidHom) = cK ψ I K := by
    rw [cK, cK, ← (isInvForm_formI hI).2.2 u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom)),
      rhoW_inv_delta_conj hK hu]
    simp only [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    linear_combination (formI ψ I (delta ψ K) (delta ψ K)) * circle_conj_mul (ψ⁻¹ (superDiag u))
  rw [lamK, lamK, hB', hc', mul_div_assoc]

include hψ in
theorem lam_eq_zero (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) {z : WT (m := m) ψ} (hz : B z z = 0)
    (g : GL (Fin m) k) : lam ψ hψ I B (rhoW ψ g z) = 0 := by
  obtain ⟨K, hK, hKy⟩ := exists_good_fix hψ (rhoW ψ g z) (rhoW ψ g z)
  rw [lam_eq hψ hI hB hK (fun κ hκ => (hKy κ hκ).1), lamK,
    form_eq_zero_of_self hB.1 hB.2.1 (by rw [hB.2.2]; exact hz), zero_div]


variable (ψ) in
def Wf (hψ : Continuous ψ) (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ)
    (y : WT (m := m) ψ) (g : GL (Fin m) k) : ℂ :=
  lam ψ hψ I B (rhoW ψ g y)

theorem Wf_apply (y : WT (m := m) ψ) (g : GL (Fin m) k) : Wf ψ hψ I B y g = lam ψ hψ I B (rhoW ψ g y) := rfl

theorem Wf_right (y : WT (m := m) ψ) (g x : GL (Fin m) k) : Wf ψ hψ I B y (g * x) = Wf ψ hψ I B (rhoW ψ x y) g := by
  simp only [Wf, map_mul, Module.End.mul_apply]

theorem Wf_left (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) (y : WT (m := m) ψ) {u : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) (g : GL (Fin m) k) :
    Wf ψ hψ I B y (u * g) = ((ψ⁻¹ (superDiag u) : Circle) : ℂ) * Wf ψ hψ I B y g := by
  simp only [Wf]
  rw [map_mul, Module.End.mul_apply, lam_unip hψ hI hB _ hu]

theorem Wf_add (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) (y z : WT (m := m) ψ) :
    Wf ψ hψ I B (y + z) = Wf ψ hψ I B y + Wf ψ hψ I B z := by
  funext g
  simp only [Wf, map_add (f := _), Pi.add_apply]
  exact lam_add hψ hI hB _ _

theorem Wf_smul (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) (a : ℂ) (y : WT (m := m) ψ) :
    Wf ψ hψ I B (a • y) = (starRingEnd ℂ) a • Wf ψ hψ I B y := by
  funext g
  simp only [Wf, map_smul, Pi.smul_apply, smul_eq_mul]
  exact lam_smul hψ hI hB _ _

theorem Wf_eq_zero (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) {z : WT (m := m) ψ} (hz : B z z = 0) :
    Wf ψ hψ I B z = 0 :=
  funext fun g => lam_eq_zero hψ hI hB hz g

theorem isLocallyConstant_Wf (y : WT (m := m) ψ) : IsLocallyConstant (Wf ψ hψ I B y) := by
  obtain ⟨K, hKo, -, hK⟩ := exists_fix y
  refine (IsLocallyConstant.iff_exists_open _).2 fun g =>
    ⟨(fun x => g⁻¹ * x) ⁻¹' K, hKo.preimage (by fun_prop), by simp [K.one_mem], fun x hx => ?_⟩
  have e : x = g * (g⁻¹ * x) := by group
  rw [e, Wf_right, hK _ hx]

end DiscreteGroups.sglob.LConv

end
end

