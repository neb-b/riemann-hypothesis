module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGFC

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GramIff
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

section Coord2

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]

theorem gram_iff [IsDiscreteValuationRing 𝒪[F]] (e : E ≃ₐ[F] F × F)
    (hes : ∀ x, e (M.L.cj x) = (e x).swap)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) (H : Loc.HermSp M V)
    (Λ : Submodule M.L.O V) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F)) (Ph : Matrix (Fin n) (Fin n) 𝒪[F])
    (hπ : IsSplitCoord e H Λ π Ph) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {ι : Type} [Fintype ι] (G₀ : Matrix ι ι E)
    (h1 : ∀ a b, G₀ a b ∈ M.L.O) (h2 : ∀ a b, G₀ b a = M.L.cj (G₀ a b)) (v : ι → V) (hv : ∀ a, v a ∈ Λ) :
    (∀ a b, H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}) ↔
      ∀ a b, resF F (∑ k, ∑ l, (π (v b)).1 k * (Ph k l : F) * (π (v a)).2 l) = resF F ((e (G₀ a b)).1) := by
  have hform := hπ.2.2.2
  have hL := fun a => (hπ.2.1 (v a)).1 (hv a)
  have hc : ∀ a b, InP ϖ (e (H.h (v b) (v a) - G₀ a b)).1 ↔
      resF F (∑ k, ∑ l, (π (v b)).1 k * (Ph k l : F) * (π (v a)).2 l) = resF F ((e (G₀ a b)).1) := by
    intro a b
    rw [map_sub, Prod.fst_sub, hform]
    exact inP_sub_iff hϖ (bil_mem _ _ (hL b).1 (hL a).2 Ph) ((hO _).1 (h1 a b)).1
  have hc2 : ∀ a b, (e (H.h (v b) (v a) - G₀ a b)).2 = (e (H.h (v a) (v b) - G₀ b a)).1 := by
    intro a b
    have hg : e (G₀ a b) = (e (G₀ b a)).swap := by rw [h2 b a, hes]
    rw [map_sub, map_sub, Prod.snd_sub, Prod.fst_sub, hform, hform, hg]
    rfl
  constructor
  · intro h a b
    exact (hc a b).1 ((mem_span_irr_iff e hO ϖ _).1 (h a b)).1
  · intro h a b
    rw [mem_span_irr_iff e hO ϖ]
    exact ⟨(hc a b).2 (h a b), by rw [hc2]; exact (hc b a).2 (h b a)⟩

theorem pi_sum (e : E ≃ₐ[F] F × F) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    {ι : Type} [Fintype ι] (v : ι → V) (c : ι → E) :
    π (∑ i, c i • v i) = (∑ i, (e (c i)).1 • (π (v i)).1, ∑ i, (e (c i)).2 • (π (v i)).2) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [hπa]
  exact Prod.ext (by simp [Prod.fst_sum]) (by simp [Prod.snd_sum])

theorem prim_iff [IsDiscreteValuationRing 𝒪[F]] (e : E ≃ₐ[F] F × F)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) (H : Loc.HermSp M V)
    (Λ : Submodule M.L.O V) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    (hπL : ∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ a, v a ∈ Λ) :
    H.Prim Λ v ↔ LinearIndependent 𝓀[F] (redM F fun a => (π (v a)).1) ∧
      LinearIndependent 𝓀[F] (redM F fun a => (π (v a)).2) := by
  set X : ι → Fin n → F := fun a => (π (v a)).1 with hXd
  set Y : ι → Fin n → F := fun a => (π (v a)).2 with hYd
  have hX : ∀ a k, X a k ∈ 𝒪[F] := fun a k => ((hπL (v a)).1 (hv a)).1 k
  have hY : ∀ a k, Y a k ∈ 𝒪[F] := fun a k => ((hπL (v a)).1 (hv a)).2 k
  have hsum := pi_sum e π hπa v
  have hpiS : ∀ u w : Fin n → F, π (π.symm (u, w)) = (u, w) := fun u w => AddEquiv.apply_symm_apply _ _

  have hLI : LinearIndependent E v ↔ LinearIndependent F X ∧ LinearIndependent F Y := by
    constructor
    · intro hind
      constructor
      · rw [Fintype.linearIndependent_iff]
        intro c hc i
        have h0 := Fintype.linearIndependent_iff.1 hind (fun i => e.symm (c i, 0)) (by
          apply π.injective
          rw [hsum, map_zero]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          ext k
          · simpa [hXd] using congrFun hc k
          · simp) i
        have := congrArg (fun z => (e z).1) h0
        simpa using this
      · rw [Fintype.linearIndependent_iff]
        intro c hc i
        have h0 := Fintype.linearIndependent_iff.1 hind (fun i => e.symm (0, c i)) (by
          apply π.injective
          rw [hsum, map_zero]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          ext k
          · simp
          · simpa [hYd] using congrFun hc k) i
        have := congrArg (fun z => (e z).2) h0
        simpa using this
    · rintro ⟨hXi, hYi⟩
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have h0 := congrArg π hc
      rw [hsum, map_zero] at h0
      have a1 := Fintype.linearIndependent_iff.1 hXi (fun i => (e (c i)).1) (congrArg Prod.fst h0) i
      have a2 := Fintype.linearIndependent_iff.1 hYi (fun i => (e (c i)).2) (congrArg Prod.snd h0) i
      apply e.injective
      rw [map_zero]
      exact Prod.ext a1 a2

  have hSat : (∀ x ∈ Λ, x ∈ Submodule.span E (Set.range v) → x ∈ Submodule.span M.L.O (Set.range v)) ↔
      SatF F X ∧ SatF F Y := by
    have hOsum : ∀ d : ι → M.L.O, ∑ i, d i • v i = ∑ i, (d i : E) • v i := fun d => rfl
    constructor
    · intro hs
      constructor
      · rintro u hu ⟨c, hc⟩
        have hxL : π.symm (u, 0) ∈ Λ := (hπL _).2 (by rw [hpiS]; exact ⟨hu, fun k => Subring.zero_mem _⟩)
        have hxs : π.symm (u, 0) ∈ Submodule.span E (Set.range v) := by
          rw [Submodule.mem_span_range_iff_exists_fun]
          refine ⟨fun i => e.symm (c i, 0), ?_⟩
          apply π.injective
          rw [hsum, hpiS]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          rw [← hc]
        obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hs _ hxL hxs)
        refine ⟨fun i => (e (d i)).1, fun i => ((hO _).1 (d i).2).1, ?_⟩
        have h0 := congrArg (fun z => (π z).1) hd
        simp only [hOsum, hsum, hpiS] at h0
        exact h0
      · rintro u hu ⟨c, hc⟩
        have hxL : π.symm (0, u) ∈ Λ := (hπL _).2 (by rw [hpiS]; exact ⟨fun k => Subring.zero_mem _, hu⟩)
        have hxs : π.symm (0, u) ∈ Submodule.span E (Set.range v) := by
          rw [Submodule.mem_span_range_iff_exists_fun]
          refine ⟨fun i => e.symm (0, c i), ?_⟩
          apply π.injective
          rw [hsum, hpiS]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          rw [← hc]
        obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hs _ hxL hxs)
        refine ⟨fun i => (e (d i)).2, fun i => ((hO _).1 (d i).2).2, ?_⟩
        have h0 := congrArg (fun z => (π z).2) hd
        simp only [hOsum, hsum, hpiS] at h0
        exact h0
    · rintro ⟨sX, sY⟩ x hx hxs
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxs
      have hπx := hsum c
      rw [hc] at hπx
      have hxc := (hπL x).1 hx
      obtain ⟨c1, hc1, hs1⟩ := sX (π x).1 hxc.1 ⟨_, (congrArg Prod.fst hπx).symm⟩
      obtain ⟨c2, hc2, hs2⟩ := sY (π x).2 hxc.2 ⟨_, (congrArg Prod.snd hπx).symm⟩
      have hmem : ∀ i, e.symm (c1 i, c2 i) ∈ M.L.O := fun i => by
        rw [hO, AlgEquiv.apply_symm_apply]; exact ⟨hc1 i, hc2 i⟩
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => ⟨_, hmem i⟩, ?_⟩
      rw [hOsum]
      apply π.injective
      rw [hsum]
      simp only [AlgEquiv.apply_symm_apply]
      exact Prod.ext hs1 hs2
  have hP : H.Prim Λ v ↔ (LinearIndependent F X ∧ LinearIndependent F Y) ∧ (SatF F X ∧ SatF F Y) := by
    unfold Loc.HermSp.Prim
    rw [← hLI, ← hSat]
    exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hv, h.1, h.2⟩⟩
  rw [hP, ← dvr_prim_iff hϖ X hX, ← dvr_prim_iff hϖ Y hY]
  tauto

end Coord2

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.IndepOf
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel
open Classical

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]
variable {ϖ : 𝒪[F]} {k : Type} [Field k] {r : M.L.O →+* k} {n : ℕ} {b : Fin n → V}
  {Λ : Submodule M.L.O V}

theorem prim_of (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ a, v a ∈ Λ) (hP : H.Prim Λ v) :
    LinearIndependent k (fun a => red hR (v a)) := by
  obtain ⟨-, hind, hsat⟩ := hP
  have hϖ0 : ((ϖ : 𝒪[F]) : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  rw [Fintype.linearIndependent_iff]
  intro g hg a0
  choose h hh using fun a => hR.surj (g a)
  have hsum_mem : ∑ a, ((h a : M.L.O) : E) • v a ∈ Λ :=
    Submodule.sum_mem _ fun a _ => Λ.smul_mem (h a) (hv a)
  have hred : red hR (∑ a, ((h a : M.L.O) : E) • v a) = 0 := by
    rw [red_lincomb hR h v hv]
    simp only [hh]
    exact hg
  obtain ⟨w, hw, hweq⟩ := (red_zero_iff hR hsum_mem).mp hred

  have hwspan : w ∈ Submodule.span E (Set.range v) := by
    have e : w = algebraMap F E ((ϖ : F))⁻¹ • ∑ a, ((h a : M.L.O) : E) • v a := by
      rw [hweq, smul_smul, ← map_mul, inv_mul_cancel₀ hϖ0, map_one, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).mp (hsat w hw hwspan)

  have hzero : ∑ a, (((h a : M.L.O) : E) - algebraMap F E (ϖ : F) * (c a : E)) • v a = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
    rw [← Finset.smul_sum, sub_eq_zero, hweq, ← hc]
    simp only [Subring.smul_def]
  have ha0 := Fintype.linearIndependent_iff.mp hind _ hzero a0
  rw [← hh a0]
  exact (hR.ker (h a0)).mpr ⟨c a0, (c a0).2, sub_eq_zero.mp ha0⟩

theorem indep_of (hR : RedData ϖ k r n b Λ) (hϖ : Irreducible ϖ)
    (o2 : ∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ j : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧
      x = algebraMap F E ϖ ^ j * u)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ a, v a ∈ Λ)
    (hX : LinearIndependent k (fun a => red hR (v a))) : LinearIndependent E v := by
  have hϖ0 : ((ϖ : 𝒪[F]) : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hOalg : ∀ c : 𝒪[F], algebraMap F E (c : F) ∈ M.L.O := by
    intro c
    rw [M.L.O_def]
    exact (isIntegral_algebraMap (R := 𝒪[F]) (A := F) (x := c)).map (IsScalarTower.toAlgHom 𝒪[F] F E)
  rw [Fintype.linearIndependent_iff]
  intro g hg a0
  by_contra hne

  choose c hc0 hcO using fun a => o2 (g a)
  have hDne : (∏ a, c a) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hc0 a
  have hD0 : (((∏ a, c a : 𝒪[F])) : F) ≠ 0 := fun h => hDne (Subtype.ext h)
  have hDg : ∀ a, algebraMap F E ((∏ b, c b : 𝒪[F]) : F) * g a ∈ M.L.O := by
    intro a
    have e : ((∏ b, c b : 𝒪[F]) : F) = (c a : F) * ((∏ b ∈ Finset.univ.erase a, c b : 𝒪[F]) : F) := by
      rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ a)]
      rfl
    rw [e, map_mul, mul_comm (algebraMap F E (c a : F)), mul_assoc]
    exact M.L.O.mul_mem (hOalg _) (hcO a)
  let h : ι → M.L.O := fun a => ⟨algebraMap F E ((∏ b, c b : 𝒪[F]) : F) * g a, hDg a⟩
  have hsum : ∑ a, ((h a : M.L.O) : E) • v a = 0 := by
    simp only [h, mul_smul, ← Finset.smul_sum, hg, smul_zero]
  have hh0 : ((h a0 : M.L.O) : E) ≠ 0 := by
    intro h0
    apply hne
    have h1 := congrArg (algebraMap F E (((∏ b, c b : 𝒪[F]) : F))⁻¹ * ·) h0
    simp only [h, mul_zero, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hD0, map_one, one_mul] at h1
    exact h1
  obtain ⟨j, z, hz, hzeq, a1, ha1⟩ :=
    minpow hR hϖ o3 (fun a => ((h a : M.L.O) : E)) (fun a => (h a).2) a0 hh0
  have hsumz : ∑ a, z a • v a = 0 := by
    have e1 : ∑ a, ((h a : M.L.O) : E) • v a = (algebraMap F E (ϖ : F)) ^ j • ∑ a, z a • v a := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hzeq a, mul_smul]
    rw [e1] at hsum
    have h2 := congrArg (fun x => (algebraMap F E ((ϖ : F))⁻¹) ^ j • x) hsum
    simp only [smul_smul, ← mul_pow, ← map_mul, inv_mul_cancel₀ hϖ0, map_one, one_pow, one_smul,
      smul_zero] at h2
    exact h2
  have hred : ∑ a, r ⟨z a, hz a⟩ • red hR (v a) = 0 := by
    rw [← red_lincomb hR (fun a => (⟨z a, hz a⟩ : M.L.O)) v hv]
    simp only [hsumz, red_zero]
  exact ha1 (Fintype.linearIndependent_iff.mp hX _ hred a1)

theorem sat_of (hR : RedData ϖ k r n b Λ) (hϖ : Irreducible ϖ)
    (o2 : ∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ j : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧
      x = algebraMap F E ϖ ^ j * u)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ a, v a ∈ Λ)
    (hX : LinearIndependent k (fun a => red hR (v a))) :
    ∀ x ∈ Λ, x ∈ Submodule.span E (Set.range v) → x ∈ Submodule.span M.L.O (Set.range v) := by
  have hϖ0 : ((ϖ : 𝒪[F]) : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hOalg : ∀ c : 𝒪[F], algebraMap F E (c : F) ∈ M.L.O := by
    intro c
    rw [M.L.O_def]
    exact (isIntegral_algebraMap (R := 𝒪[F]) (A := F) (x := c)).map (IsScalarTower.toAlgHom 𝒪[F] F E)
  have hϖO : algebraMap F E (ϖ : F) ∈ M.L.O := hOalg ϖ
  have hϖu : IsUnit (algebraMap F E (ϖ : F)) := (isUnit_iff_ne_zero.mpr hϖ0).map (algebraMap F E)
  intro x hx hxs
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hxs

  choose c hc0 hcO using fun a => o2 (g a)
  have hDne : (∏ a, c a) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hc0 a
  have hD0 : (((∏ a, c a : 𝒪[F])) : F) ≠ 0 := fun h => hDne (Subtype.ext h)
  have hDg : ∀ a, algebraMap F E ((∏ b, c b : 𝒪[F]) : F) * g a ∈ M.L.O := by
    intro a
    have e : ((∏ b, c b : 𝒪[F]) : F) = (c a : F) * ((∏ b ∈ Finset.univ.erase a, c b : 𝒪[F]) : F) := by
      rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ a)]
      rfl
    rw [e, map_mul, mul_comm (algebraMap F E (c a : F)), mul_assoc]
    exact M.L.O.mul_mem (hOalg _) (hcO a)
  have hdO : algebraMap F E ((∏ b, c b : 𝒪[F]) : F) ∈ M.L.O := hOalg _
  have hdu : IsUnit (algebraMap F E ((∏ b, c b : 𝒪[F]) : F)) :=
    (isUnit_iff_ne_zero.mpr hD0).map (algebraMap F E)
  let h : ι → M.L.O := fun a => ⟨algebraMap F E ((∏ b, c b : 𝒪[F]) : F) * g a, hDg a⟩
  have hdx : algebraMap F E ((∏ b, c b : 𝒪[F]) : F) • x = ∑ a, ((h a : M.L.O) : E) • v a := by
    rw [← hg, Finset.smul_sum]
    simp only [h, mul_smul]
  by_cases hall : ∀ a, ((h a : M.L.O) : E) = 0
  · have h0 : algebraMap F E ((∏ b, c b : 𝒪[F]) : F) • x = 0 := by
      rw [hdx]
      simp [hall]
    have hx0 : x = 0 := by
      rw [← smul_zero (algebraMap F E ((∏ b, c b : 𝒪[F]) : F))] at h0
      exact hdu.smul_left_cancel.mp h0
    rw [hx0]
    exact zero_mem _
  push_neg at hall
  obtain ⟨a0, ha0⟩ := hall
  obtain ⟨j, z, hz, hzeq, a1, ha1⟩ :=
    minpow hR hϖ o3 (fun a => ((h a : M.L.O) : E)) (fun a => (h a).2) a0 ha0
  haveI : Nontrivial E := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have h10 : (1 : M.L.O) = 0 := Subtype.ext (Subsingleton.elim _ _)
    have h11 := congrArg r h10
    simp at h11
  obtain ⟨m, u, huO, ⟨w, hwO, huw⟩, hdeq⟩ := o3 _ hdO hdu.ne_zero
  have key : (algebraMap F E (ϖ : F)) ^ m • (u • x) =
      (algebraMap F E (ϖ : F)) ^ j • ∑ a, z a • v a := by
    rw [smul_smul, ← hdeq, hdx, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hzeq a, mul_smul]
  by_cases hjm : m ≤ j
  · rw [show j = m + (j - m) by omega, pow_add, mul_smul] at key
    have e1 := (hϖu.pow m).smul_left_cancel.mp key
    have hx' : x = ∑ a, (w * (algebraMap F E (ϖ : F)) ^ (j - m) * z a) • v a := by
      have e2 : x = w • (u • x) := by rw [smul_smul, mul_comm w u, huw, one_smul]
      rw [e2, e1, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_smul, smul_smul, mul_assoc]
    rw [hx']
    refine Submodule.sum_mem _ fun a _ => ?_
    have hmem : w * (algebraMap F E (ϖ : F)) ^ (j - m) * z a ∈ M.L.O :=
      M.L.O.mul_mem (M.L.O.mul_mem hwO (M.L.O.pow_mem hϖO _)) (hz a)
    have h3 := Submodule.smul_mem (Submodule.span M.L.O (Set.range v)) (⟨_, hmem⟩ : M.L.O)
      (Submodule.subset_span ⟨a, rfl⟩)
    rwa [Subring.smul_def] at h3
  · push_neg at hjm
    rw [show m = j + ((m - j - 1) + 1) by omega, pow_add, mul_smul] at key
    have e1 := (hϖu.pow j).smul_left_cancel.mp key
    have hzs : ∑ a, z a • v a = algebraMap F E (ϖ : F) •
        ((algebraMap F E (ϖ : F)) ^ (m - j - 1) • (u • x)) := by
      rw [← e1, pow_succ, mul_smul, smul_comm]
    have hmemΛ : ∑ a, z a • v a ∈ Λ :=
      Submodule.sum_mem _ fun a _ => Λ.smul_mem (⟨z a, hz a⟩ : M.L.O) (hv a)
    have hred0 : red hR (∑ a, z a • v a) = 0 := by
      rw [red_zero_iff hR hmemΛ]
      refine ⟨(algebraMap F E (ϖ : F)) ^ (m - j - 1) • (u • x), ?_, hzs⟩
      have hc : (algebraMap F E (ϖ : F)) ^ (m - j - 1) * u ∈ M.L.O :=
        M.L.O.mul_mem (M.L.O.pow_mem hϖO _) huO
      have h4 := Λ.smul_mem (⟨_, hc⟩ : M.L.O) hx
      rwa [Subring.smul_def, mul_smul] at h4
    have hred : ∑ a, r ⟨z a, hz a⟩ • red hR (v a) = 0 := by
      rw [← red_lincomb hR (fun a => (⟨z a, hz a⟩ : M.L.O)) v hv]
      exact hred0
    exact absurd (Fintype.linearIndependent_iff.mp hX _ hred a1) ha1

theorem prim_iff (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hϖ : Irreducible ϖ)
    (o2 : ∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ j : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧
      x = algebraMap F E ϖ ^ j * u)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ a, v a ∈ Λ) :
    H.Prim Λ v ↔ LinearIndependent k (fun a => red hR (v a)) :=
  ⟨prim_of hR H hϖ v hv, fun hX => ⟨hv, indep_of hR hϖ o2 o3 v hv hX, sat_of hR hϖ o2 o3 v hv hX⟩⟩

end FC

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFRepTop
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fixedOK_of_rows (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : RowsOf u F0 what₂) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Λ ∈ what₂) : FixedOK D F0 Λ := by
  obtain ⟨hE, hz, hrr, -⟩ := hR
  obtain ⟨-, ⟨hlat, hunim, -, -⟩, hx⟩ := hrr.1 Λ hΛ
  refine ⟨hlat, hunim, hE, ?_, (D.cOf u)⁻¹, inv_ne_zero (D.cOf_ne u), ?_⟩
  · unfold XLam at hx
    intro a
    have hmem : F0.e a ∈ XS D F0 := by
      unfold XS
      clear hrr hz hunim hlat hΛ what₂ hE hx
      apply Submodule.subset_span
      refine ⟨a, 1, ?_, (one_smul _ _).symm⟩
      unfold ddS
      have hne : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ≠ ⊥ :=
        Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot
      have hk : ((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = ((D.R.rS - (a : ℕ) : ℕ) : ℤ) := by
        have := a.isLt
        omega
      rw [hk, zpow_neg, zpow_natCast, ← FractionalIdeal.coeIdeal_pow,
        FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 (pow_ne_zero _ hne))]
      intro y hy
      rw [one_mul]
      exact FractionalIdeal.coeIdeal_le_one hy
    rw [← hx] at hmem
    exact hmem.1
  · rw [hz]
    rfl

theorem orbitReps_of (hN : UnipotentIntegralIsGroup) (hRk : RankG) (hG : GoodEZ) (h1 : Stage1) (h2 : Stage2) (hK : FinK) :
    OrbitReps := by
  intro D δ M hA L u u' hT F0 what₂ hR Z Λ hΛ
  have hF := fixedOK_of_rows D u F0 what₂ hR hΛ
  by_cases hne : (EZ (Tn u') F0 Λ Z).Nonempty
  · obtain ⟨F1, hF1⟩ := hne
    have hGZ : GZ (Tn u) (Tn u') Z ≠ 0 := by
      have h := hF1.1.2.2
      rw [gz_eq, hF1.2.2.2.2] at h
      exact h
    obtain ⟨R, hRm⟩ := hRk D (Tn u) (Tn u') Z hGZ
    obtain ⟨Wf, hWf, hW⟩ := h1 D (Tn u') F0 Λ hF Z R hRm
    obtain ⟨Af, hAf, hAx⟩ := h2 D (Tn u') F0 Λ hF Z R hRm Wf hWf
    refine ⟨{x | Good D (Tn u') F0 Λ Z x ∧ pWf D x ∈ Wf ∧ alM D x * R ∈ Af},
      hK D (Tn u') F0 Λ hF Z R hRm Wf Af hWf hAf, fun F' hF' => ?_⟩
    have g0 := hG D (Tn u') F0 Λ Z F' hF'
    obtain ⟨n1, hn1, hw1⟩ := hW _ g0
    have g1 := good_move D (Tn u') F0 Λ Z g0 hn1
    obtain ⟨n2, hn2, hw2, ha2⟩ := hAx _ g1 hw1
    have g2 := good_move D (Tn u') F0 Λ Z g1 hn2
    refine ⟨n1.trans n2, (hN D F0 Λ).2.2 n1 hn1 n2 hn2, ?_⟩
    have hact : act D (n1.trans n2) (F'.fl.e, F'.fl.z) = act D n2 (act D n1 (F'.fl.e, F'.fl.z)) := rfl
    show act D (n1.trans n2) (F'.fl.e, F'.fl.z) ∈ _
    rw [hact]
    exact ⟨g2, hw2 ▸ hw1, ha2⟩
  · refine ⟨∅, Set.finite_empty, fun F' hF' => absurd ⟨F', hF'⟩ hne⟩

end PI.UnitaryGroupMassFormula.CntFormula
end
end

