module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusOrbitLatticeCountBoundedByRho
section
noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.TorusOrbitLat

section General

variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]

theorem mem_stabLat_iff (t : Aˣ) (L : Submodule O A) :
    t ∈ stabLat O L ↔ ∀ y, y ∈ L ↔ (t : A) * y ∈ L := Iff.rfl

theorem mem_intUnits_iff (t : Aˣ) :
    t ∈ intUnits O A ↔ IsIntegral O (t : A) ∧ IsIntegral O ((t⁻¹ : Aˣ) : A) := Iff.rfl

theorem mem_mulLat_unit (u : Aˣ) (L : Submodule O A) (w : A) :
    w ∈ mulLat O (u : A) L ↔ ((u⁻¹ : Aˣ) : A) * w ∈ L := by
  simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, by simp⟩

theorem mulLat_eq_iff (u v : Aˣ) (L : Submodule O A) :
    mulLat O (u : A) L = mulLat O (v : A) L ↔ u⁻¹ * v ∈ stabLat O L := by
  rw [mem_stabLat_iff]
  constructor
  · intro h y
    calc y ∈ L ↔ (v : A) * y ∈ mulLat O (v : A) L := by rw [mem_mulLat_unit]; simp
      _ ↔ (v : A) * y ∈ mulLat O (u : A) L := by rw [h]
      _ ↔ ((u⁻¹ * v : Aˣ) : A) * y ∈ L := by rw [mem_mulLat_unit, Units.val_mul, mul_assoc]
  · intro h
    ext w
    rw [mem_mulLat_unit, mem_mulLat_unit, h (((v⁻¹ : Aˣ) : A) * w)]
    simp [mul_assoc]

theorem isIntegral_inv_mul_iff (t u : Aˣ) (hu : u ∈ intUnits O A) (w : A) :
    IsIntegral O ((((t * u)⁻¹ : Aˣ) : A) * w) ↔ IsIntegral O (((t⁻¹ : Aˣ) : A) * w) := by
  rw [mem_intUnits_iff] at hu
  rw [mul_inv_rev, Units.val_mul, mul_assoc]
  constructor
  · intro h
    have := hu.1.mul h
    simpa using this
  · intro h
    exact hu.2.mul h

end General

section Main

variable {K : UQ} (B : InvAlg K)

theorem rho_cond_mk (t : B.T) (w : B.A) :
    IsIntegral K.O (((((Quotient.out (QuotientGroup.mk t : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T) : B.T) :
      B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w) ↔ IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((intUnits K.O B.A).subgroupOf B.T) t
  rw [hh, Subgroup.coe_mul]
  exact isIntegral_inv_mul_iff _ _ (Subgroup.mem_subgroupOf.mp h.2) w

theorem orbit_count : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A → (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 → ∀ a : K.O, (∀ j : ℕ, 0 < B.rho (algebraMap K.O B.A a ^ j)) → ∀ m k : ℕ, m ≤ k → (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ m * y ∈ L) → (∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ m * y)) → Finite {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k - m)) ≤ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ∧ Nat.card {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ algebraMap K.O B.A a ^ k ∈ M} ≤ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) * B.rho (algebraMap K.O B.A a ^ (k + m)) := by
  intro K B L hSle hidx a hrho m k hmk hin hout
  set w : B.A := algebraMap K.O B.A a with hw
  set H : Subgroup B.T := (stabLat K.O L).subgroupOf B.T with hH
  set Kc : Subgroup B.T := (intUnits K.O B.A).subgroupOf B.T with hKc
  have hHK : H ≤ Kc := by
    intro x hx
    rw [hH, Subgroup.mem_subgroupOf] at hx
    rw [hKc, Subgroup.mem_subgroupOf]
    exact hSle ⟨hx, x.2⟩
  have hidx_eq : (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) = (H.subgroupOf Kc).index := by
    rw [← Subgroup.relIndex_subgroupOf (inf_le_right : intUnits K.O B.A ⊓ B.T ≤ B.T),
      Subgroup.inf_subgroupOf_right, Subgroup.inf_subgroupOf_right]
    rfl
  have hQfin : Finite (Kc ⧸ H.subgroupOf Kc) := by
    rw [← Subgroup.index_ne_zero_iff_finite, ← hidx_eq]; exact hidx
  have hRfin : ∀ j, Finite {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ j : B.A)} :=
    fun j => (Nat.card_pos_iff.mp (hrho j)).2
  have hrho_eq : ∀ j, B.rho (w ^ j) = Nat.card {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ j : B.A)} :=
    fun j => rfl
  let e := Subgroup.quotientEquivProdOfLE hHK
  have he1 : ∀ g : B.T, (e (QuotientGroup.mk g)).1 = QuotientGroup.mk g := fun g => rfl

  let Y := {c : B.T ⧸ H // w ^ k ∈ mulLat K.O (((Quotient.out c : B.T) : B.Aˣ) : B.A) L}
  let fY : Y → {M : Submodule K.O B.A // (∃ t ∈ B.T, M = mulLat K.O (t : B.A) L) ∧ w ^ k ∈ M} :=
    fun c => ⟨mulLat K.O (((Quotient.out c.1 : B.T) : B.Aˣ) : B.A) L, ⟨_, (Quotient.out c.1).2, rfl⟩, c.2⟩
  have hfY : Function.Bijective fY := by
    constructor
    · rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
      have h' : mulLat K.O (((Quotient.out c : B.T) : B.Aˣ) : B.A) L = mulLat K.O (((Quotient.out c' : B.T) : B.Aˣ) : B.A) L :=
        congrArg Subtype.val h
      rw [mulLat_eq_iff] at h'
      apply Subtype.ext
      change c = c'
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq]
      exact Subgroup.mem_subgroupOf.mpr (by simpa using h')
    · rintro ⟨M, ⟨t, ht, rfl⟩, hM⟩
      have hc := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk ⟨t, ht⟩ : B.T ⧸ H))
      rw [hH, Subgroup.mem_subgroupOf] at hc
      have key : mulLat K.O (((Quotient.out (QuotientGroup.mk ⟨t, ht⟩ : B.T ⧸ H) : B.T) : B.Aˣ) : B.A) L =
          mulLat K.O (t : B.A) L := by
        rw [mulLat_eq_iff]; simpa using hc
      exact ⟨⟨_, key ▸ hM⟩, Subtype.ext key⟩
  have hcardXY := Nat.card_congr (Equiv.ofBijective fY hfY)

  have key1 : ∀ g : B.T, ((((g : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w ^ k ∈ L) →
      IsIntegral K.O ((((Quotient.out (e (QuotientGroup.mk g)).1 : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k + m) : B.A) := by
    intro g hg
    rw [he1 g, rho_cond_mk]
    have := hout _ hg
    convert this using 1
    rw [pow_add]; ring
  let U : Y → {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k + m) : B.A)} ×
      (Kc ⧸ H.subgroupOf Kc) := fun c =>
    (⟨(e c.1).1, by
      have := key1 (Quotient.out c.1) (by rw [← mem_mulLat_unit]; exact c.2)
      rwa [QuotientGroup.out_eq'] at this⟩, (e c.1).2)
  have hU : Function.Injective U := by
    intro c c' h
    apply Subtype.ext
    apply e.injective
    have h1 := congrArg (fun p => p.1.1) h
    have h2 := congrArg Prod.snd h
    exact Prod.ext h1 h2
  have hYfin : Finite Y := by
    haveI := hRfin (k + m)
    exact Finite.of_injective U hU

  have key2 : ∀ g : B.T,
      IsIntegral K.O ((((Quotient.out (e (QuotientGroup.mk g)).1 : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k - m) : B.A) →
      w ^ k ∈ mulLat K.O ((g : B.Aˣ) : B.A) L := by
    intro g hg
    rw [he1 g, rho_cond_mk] at hg
    rw [mem_mulLat_unit]
    have := hin _ hg
    convert this using 1
    rw [← Nat.add_sub_cancel' hmk, pow_add, Nat.add_sub_cancel_left]; ring
  let D : {d : B.T ⧸ Kc // IsIntegral K.O ((((Quotient.out d : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w ^ (k - m) : B.A)} ×
      (Kc ⧸ H.subgroupOf Kc) → Y := fun p =>
    ⟨e.symm (p.1.1, p.2), by
      have hc : e (e.symm (p.1.1, p.2)) = (p.1.1, p.2) := e.apply_symm_apply _
      apply key2
      rw [QuotientGroup.out_eq', hc]
      exact p.1.2⟩
  have hD : Function.Injective D := by
    intro p p' h
    have h' := e.symm.injective (congrArg Subtype.val h)
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact Prod.ext (Subtype.ext h1) h2
  refine ⟨?_, ?_, ?_⟩
  · exact Finite.of_equiv Y (Equiv.ofBijective fY hfY)
  · rw [← hcardXY, hidx_eq, hrho_eq, mul_comm]
    exact (Nat.card_prod _ _).symm.trans_le (Nat.card_le_card_of_injective D hD)
  · rw [← hcardXY, hidx_eq, hrho_eq, mul_comm]
    haveI := hRfin (k + m)
    exact (Nat.card_le_card_of_injective U hU).trans_eq (Nat.card_prod _ _)

end Main

end GlobalTheory.TorusOrbitLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportSelfDualHaarMeasureKernelAddEquiv
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.TransportSD

theorem map_map_equiv_left {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (e : α ≃ᵐ β) (g : β → γ) : (μ.map e).map g = μ.map (g ∘ e) := by
  by_cases hg : AEMeasurable g (μ.map e)
  · exact AEMeasurable.map_map_of_aemeasurable hg e.measurable.aemeasurable
  · have hg' : ¬ AEMeasurable (g ∘ e) μ := by rwa [← aemeasurable_map_equiv_iff e]
    by_cases hμ : μ = 0
    · simp [hμ]
    · have heμ : Measure.map e μ ≠ 0 := (Measure.map_ne_zero_iff e.measurable.aemeasurable).mpr hμ
      rw [Measure.map_of_not_aemeasurable_of_ne_zero hg heμ,
        Measure.map_of_not_aemeasurable_of_ne_zero hg' hμ]

open scoped Classical in
theorem map_map_equiv_right {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (T : α → β) (e : β ≃ᵐ γ) :
    (if AEMeasurable T μ then μ.map T else 0).map e =
      (if AEMeasurable (e ∘ T) μ then μ.map (e ∘ T) else 0) := by
  by_cases hT : AEMeasurable T μ
  · have hT' := e.measurable.comp_aemeasurable hT
    simpa only [if_pos hT, if_pos hT'] using
      AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hT
  · have hT' : ¬ AEMeasurable (e ∘ T) μ := by
      intro h
      apply hT
      have := e.symm.measurable.comp_aemeasurable h
      simpa [Function.comp_def] using this
    simp only [if_neg hT, if_neg hT', Measure.map_zero]

end GlobalTheory.TransportSD

open GlobalTheory.TransportSD in
theorem GlobalTheory.transport_selfDual_fourB :
    ∀ {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup V'] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V']
    (h : V' ≃+ V), Continuous h → Continuous h.symm → ∀ (μ : Measure V) (B : V → V → ℂ),
    (SelfDual μ B ∧ (∀ x : V, AEMeasurable (x + ·) μ) →
      SelfDual (Measure.map h.symm μ) (fun x y => B (h x) (h y)) ∧
        (∀ x : V', AEMeasurable (x + ·) (Measure.map h.symm μ))) ∧
    ∀ (f : V' → ℂ) (y : V'),
      fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y =
        fourB μ B (fun v => f (h.symm v)) (h y) := by
  intro V V' _ _ _ _ _ _ _ _ h hc hs μ B
  let he : V ≃ₜ V' := { toEquiv := h.symm.toEquiv, continuous_toFun := hs, continuous_invFun := hc }
  let e : V ≃ᵐ V' := he.toMeasurableEquiv
  have he_eq : (e : V → V') = h.symm := rfl
  have hμ : Measure.map h.symm μ = Measure.map e μ := by rw [he_eq]
  have four : ∀ (f : V' → ℂ) (y : V'), fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y = fourB μ B (fun v => f (h.symm v)) (h y) := by
    intro f y
    unfold fourB
    rw [hμ, integral_map_equiv]
    congr 1
    funext v
    rw [he_eq]
    simp
  -- The old zero fallback in `Measure.map` made left invariance imply AE measurability.
  refine ⟨fun ⟨hsd, hAe⟩ => ?_, four⟩
  have hcomp (x' : V') :
      (fun y' => x' + y') ∘ (e : V → V') = (e : V → V') ∘ (fun v => h x' + v) := by
    funext v; rw [he_eq]; simp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨hH, -⟩ := hsd
    rw [hμ]
    have h1 : IsFiniteMeasureOnCompacts (Measure.map e μ) := by
      refine ⟨fun K hK => ?_⟩
      rw [MeasurableEquiv.map_apply]
      have : (e : V → V') ⁻¹' K = h '' K := by
        ext v; rw [he_eq]; simp [Set.mem_image]
        constructor
        · intro hv; exact ⟨h.symm v, hv, by simp⟩
        · rintro ⟨w, hw, rfl⟩; simpa using hw
      rw [this]
      exact (hK.image hc).measure_lt_top
    have h2 : (Measure.map e μ).IsAddLeftInvariant := by
      refine ⟨fun x' => ?_⟩
      rw [map_map_equiv_left, hcomp,
        ← AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable (hAe (h x')),
        hH.toIsAddLeftInvariant.map_add_left_eq_self (h x')]
    have h3 : (Measure.map e μ).IsOpenPosMeasure := by
      refine ⟨fun U hU hne => ?_⟩
      rw [MeasurableEquiv.map_apply]
      have hU' : IsOpen ((e : V → V') ⁻¹' U) := hU.preimage (by rw [he_eq]; exact hs)
      have hne' : ((e : V → V') ⁻¹' U).Nonempty := by
        obtain ⟨u, hu⟩ := hne
        exact ⟨h u, by rw [he_eq]; simpa using hu⟩
      exact hU'.measure_ne_zero μ hne'
    exact { toIsFiniteMeasureOnCompacts := h1, toIsAddLeftInvariant := h2, toIsOpenPosMeasure := h3 }
  · intro f hf y
    have hf' : IsTest (fun v => f (h.symm v)) :=
      ⟨hf.1.comp_continuous hs, hf.2.comp_homeomorph he⟩
    rw [four]
    have : (fun v => fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f (h.symm v)) =
        fourB μ B (fun v => f (h.symm v)) := by
      funext v; rw [four]; simp
    rw [this, hsd.2 _ hf' (h y)]
    simp
  · intro x'
    rw [hμ, aemeasurable_map_equiv_iff e, hcomp]
    exact e.measurable.comp_aemeasurable (hAe (h x'))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UUEqSumOverTorusOrbits
section
noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

namespace InvAlg

variable {K : UQ} (B : InvAlg K)

theorem torusOrb_mem_mulLat_unit (u : B.Aˣ) (L : Submodule K.O B.A) (y : B.A) :
    y ∈ mulLat K.O (u : B.A) L ↔ ((u⁻¹ : B.Aˣ) : B.A) * y ∈ L := by
  unfold mulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [LinearMap.mulLeft_apply, ← mul_assoc] using hz
  · intro h
    exact ⟨_, h, by simp [LinearMap.mulLeft_apply, ← mul_assoc]⟩

theorem torusOrb_mulLat_one (L : Submodule K.O B.A) : mulLat K.O (1 : B.A) L = L := by
  ext y; simpa using torusOrb_mem_mulLat_unit B 1 L y

theorem torusOrb_mulLat_mul (s t : B.Aˣ) (L : Submodule K.O B.A) :
    mulLat K.O ((s : B.A)) (mulLat K.O (t : B.A) L) = mulLat K.O ((s * t : B.Aˣ) : B.A) L := by
  ext y
  rw [torusOrb_mem_mulLat_unit, torusOrb_mem_mulLat_unit, torusOrb_mem_mulLat_unit, mul_inv_rev, Units.val_mul, mul_assoc]

theorem torusOrb_mulLat_inv (t : B.Aˣ) (L : Submodule K.O B.A) :
    mulLat K.O ((t⁻¹ : B.Aˣ) : B.A) (mulLat K.O (t : B.A) L) = L := by
  rw [torusOrb_mulLat_mul, inv_mul_cancel, Units.val_one, torusOrb_mulLat_one]

theorem herm_torus_mul_right_eq_inv_mul_middle (x y : B.A) (t : B.Aˣ) (ht : t ∈ B.T) (z : B.A) :
    B.herm x y ((t : B.A) * z) = B.herm x (((t⁻¹ : B.Aˣ) : B.A) * y) z := by
  have h1 : ((t⁻¹ : B.Aˣ) : B.A) = B.σ (t : B.A) := Units.inv_eq_of_mul_eq_one_right ht
  unfold herm
  rw [show B.σ ((t : B.A) * z) = B.σ (t : B.A) * B.σ z from map_mul B.σ _ _, ← h1]
  congr 1
  ring

theorem torusOrb_mulLat_mem_X (x : B.A) (t : B.Aˣ) (ht : t ∈ B.T) (L : Submodule K.O B.A) (hL : L ∈ B.X x) :
    mulLat K.O (t : B.A) L ∈ B.X x := by
  obtain ⟨⟨hfg, hsp⟩, hg, hsd⟩ := hL
  refine ⟨⟨hfg.map _, ?_⟩, ?_, ?_⟩
  · rw [eq_top_iff]
    intro a _
    have hmem : ((t⁻¹ : B.Aˣ) : B.A) * a ∈ Submodule.span K.E (L : Set B.A) := by rw [hsp]; trivial
    have h2 := Submodule.mem_map_of_mem (f := LinearMap.mulLeft K.E (t : B.A)) hmem
    rw [Submodule.map_span] at h2
    have h3 : (LinearMap.mulLeft K.E (t : B.A)) ((((t⁻¹ : B.Aˣ) : B.A) * a)) = a := by
      simp [LinearMap.mulLeft_apply, ← mul_assoc]
    rw [h3] at h2
    have e : ((mulLat K.O (t : B.A) L : Submodule K.O B.A) : Set B.A) =
        (LinearMap.mulLeft K.E (t : B.A)) '' (L : Set B.A) := by
      show ((L.map (LinearMap.mulLeft K.O (t : B.A)) : Submodule K.O B.A) : Set B.A) = _
      rw [Submodule.map_coe]
      rfl
    rw [e]
    exact h2
  · intro y hy
    rw [torusOrb_mem_mulLat_unit] at hy ⊢
    rw [mul_left_comm]
    exact hg _ hy
  · intro y
    rw [torusOrb_mem_mulLat_unit, hsd]
    constructor
    · intro h z hz
      rw [torusOrb_mem_mulLat_unit] at hz
      have := h _ hz
      rw [← herm_torus_mul_right_eq_inv_mul_middle B x y t ht] at this
      simpa [← mul_assoc] using this
    · intro h z hz
      rw [← herm_torus_mul_right_eq_inv_mul_middle B x y t ht]
      apply h
      rw [torusOrb_mem_mulLat_unit]
      simpa [← mul_assoc] using hz

def torusOrbRel (x : B.A) (L M : B.X x) : Prop :=
  ∃ t ∈ B.T, (M : Submodule K.O B.A) = mulLat K.O (t : B.A) (L : Submodule K.O B.A)

theorem torusOrb_orbRel_equivalence (x : B.A) : Equivalence (B.torusOrbRel x) := by
  refine { refl := ?_, symm := ?_, trans := ?_ }
  · intro L
    exact ⟨1, B.T.one_mem, by rw [Units.val_one, torusOrb_mulLat_one]⟩
  · rintro L M ⟨t, ht, h⟩
    refine ⟨t⁻¹, B.T.inv_mem ht, ?_⟩
    rw [h, torusOrb_mulLat_inv]
  · rintro L M N ⟨s, hs, h1⟩ ⟨t, ht, h2⟩
    refine ⟨t * s, B.T.mul_mem ht hs, ?_⟩
    rw [h2, h1, torusOrb_mulLat_mul]

theorem torusOrb_orb_mk_eq (x : B.A) {L M : B.X x}
    (h : (Quot.mk (B.torusOrbRel x) L : Orb K.O B.T (B.X x)) = Quot.mk (B.torusOrbRel x) M) : B.torusOrbRel x L M :=
  (Equivalence.eqvGen_iff (B.torusOrb_orbRel_equivalence x)).1 (Quot.eqvGen_exact h)

def torusOrb_orbSplit (x w : B.A) : {L : B.X x // w ∈ (L : Submodule K.O B.A)} ≃
    Σ o : Orb K.O B.T (B.X x), {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} where
  toFun L := ⟨(Quot.mk (B.torusOrbRel x) L.1 : Orb K.O B.T (B.X x)), L.1.1,
    B.torusOrb_orb_mk_eq x (Quot.out_eq (Quot.mk (B.torusOrbRel x) L.1 : Orb K.O B.T (B.X x))), L.2⟩
  invFun p := ⟨⟨p.2.1, by
      obtain ⟨t, ht, h⟩ := p.2.2.1
      rw [h]
      exact B.torusOrb_mulLat_mem_X x t ht _ (Quot.out p.1).2⟩, p.2.2.2⟩
  left_inv L := rfl
  right_inv p := by
    obtain ⟨o, M, h⟩ := p
    refine Sigma.subtype_ext ?_ rfl
    dsimp only
    conv_rhs => rw [← Quot.out_eq o]
    symm
    apply Quot.sound
    exact h.1

theorem torusOrb_UU_eq_finsum (x w : B.A) (hfin : Finite (Orb K.O B.T (B.X x)))
    (hfib : ∀ o : Orb K.O B.T (B.X x), Finite {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M}) :
    B.UU x w = ∑ᶠ o : Orb K.O B.T (B.X x), Nat.card {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} := by
  haveI := Fintype.ofFinite (Orb K.O B.T (B.X x))
  unfold UU
  rw [Nat.card_congr (B.torusOrb_orbSplit x w), Nat.card_sigma, finsum_eq_sum_of_fintype]

end InvAlg

theorem UU_eq_sum_orbits : ∀ (K : UQ) (B : InvAlg K) (x w : B.A), Finite (Orb K.O B.T (B.X x)) →
    (∀ o : Orb K.O B.T (B.X x), Finite {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M}) →
    B.UU x w = ∑ᶠ o : Orb K.O B.T (B.X x), Nat.card {M : Submodule K.O B.A //
      (∃ t ∈ B.T, M = mulLat K.O (t : B.A) (Quot.out o).1) ∧ w ∈ M} :=
  fun _ B x w h1 h2 => B.torusOrb_UU_eq_finsum x w h1 h2

end GlobalTheory.UnitLemma
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnifConst
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.TestFn

theorem unif_const (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (f : X → ℂ)
    (hf : IsTest f) : ∃ V ∈ 𝓝 (0 : X), ∀ x v, v ∈ V → f (x + v) = f x := by
  classical
  have hC : IsCompact (tsupport f) := hf.2
  have hW : ∀ x : X, ∃ W ∈ 𝓝 (0 : X), ∀ w₁ ∈ W, ∀ w₂ ∈ W, f (x + w₁ + w₂) = f x := by
    intro x
    have ho : IsOpen (f ⁻¹' {f x}) := hf.1.isOpen_fiber (f x)
    have hmem : f ⁻¹' {f x} ∈ 𝓝 (x + (0 : X) + 0) := by simpa using ho.mem_nhds (by simp)
    have hcont : Continuous (fun p : X × X => x + p.1 + p.2) := by fun_prop
    have h2 := hcont.continuousAt (x := ((0 : X), (0 : X))) hmem
    rw [nhds_prod_eq] at h2
    obtain ⟨W₁, hW₁, W₂, hW₂, hsub⟩ := Filter.mem_prod_iff.mp h2
    refine ⟨W₁ ∩ W₂, Filter.inter_mem hW₁ hW₂, fun w₁ h₁ w₂ h₂ => ?_⟩
    exact hsub (Set.mk_mem_prod h₁.1 h₂.2)
  choose W hW0 hWf using hW
  have hnb : ∀ x ∈ tsupport f, (fun w => x + w) '' W x ∈ 𝓝 x := by
    intro x _
    have h1 : (fun w => x + w) '' W x = (fun y => -x + y) ⁻¹' W x := by
      ext y; constructor
      · rintro ⟨w, hw, rfl⟩; simpa using hw
      · intro hy; exact ⟨-x + y, hy, by abel⟩
    rw [h1]
    exact (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW0 x)
  obtain ⟨t, htC, hcover⟩ := hC.elim_nhds_subcover _ hnb
  set V₀ : Set X := ⋂ x ∈ t, W x
  have hV₀ : V₀ ∈ 𝓝 (0 : X) := (Filter.biInter_finset_mem t).mpr fun x _ => hW0 x
  have hcase : ∀ y ∈ tsupport f, ∀ v ∈ V₀, f (y + v) = f y := by
    intro y hy v hv
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (hcover hy)
    obtain ⟨w, hw, rfl⟩ := hyx
    have hvx : v ∈ W x := Set.mem_iInter₂.mp hv x hxt
    have e1 := hWf x w hw v hvx
    have e2 : f (x + w) = f x := by simpa using hWf x w hw 0 (mem_of_mem_nhds (hW0 x))
    rw [e2, ← e1]
  refine ⟨V₀ ∩ (fun v => -v) ⁻¹' V₀, Filter.inter_mem hV₀ (continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hV₀)),
    fun x v hv => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hcase x hx v hv.1
  by_cases hxv : x + v ∈ tsupport f
  · have := hcase (x + v) hxv (-v) hv.2
    simp only [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxv]

theorem slice_test {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (T : X × Y → ℂ) (hT : IsTest T) (y : Y) :
    IsTest (fun x => T (x, y)) := by
  refine ⟨hT.1.comp_continuous (Continuous.prodMk_left y), ?_⟩
  have hc : IsCompact (Prod.fst '' tsupport T) := hT.2.image continuous_fst
  refine hc.of_isClosed_subset (isClosed_tsupport _) ?_
  have h1 : IsClosed ((fun x => (x, y)) ⁻¹' tsupport T) := (isClosed_tsupport T).preimage (Continuous.prodMk_left y)
  refine (closure_minimal ?_ h1).trans ?_
  · intro x hx; exact subset_tsupport T hx
  · intro x hx; exact ⟨(x, y), hx, rfl⟩

end GlobalTheory.TestFn
end

