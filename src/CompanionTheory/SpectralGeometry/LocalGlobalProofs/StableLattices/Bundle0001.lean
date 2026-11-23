module

public import Mathlib

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommuteOfMemAdjoin
section
namespace GlobalTheory.CompanionTheory.CommStep

open Module

theorem commute_of_mem_adjoin {V : Type} [AddCommGroup V] [Module ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (hc : ∀ i j, Commute (a i) (a j)) (i : Fin (l + 1))
    {y : Module.End ℂ V} (hy : y ∈ Algebra.adjoin ℂ (Set.range a)) : Commute y (a i) := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact hc j i
  | algebraMap r => exact Algebra.commutes r (a i)
  | add x y _ _ hx hy => exact hx.add_left hy
  | mul x y _ _ hx hy => exact hx.mul_left hy

theorem adjoin_le_sup {V : Type} [AddCommGroup V] [Module ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (hc : ∀ i j, Commute (a i) (a j)) :
    Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)) ⊔
        (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
          (LinearMap.mulRight ℂ (a 0)) := by
  have hBC : Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ) ≤
      Algebra.adjoin ℂ (Set.range a) :=
    Algebra.adjoin_mono (Set.range_subset_iff.2 fun k => ⟨k.succ, rfl⟩)
  have ha0 : a 0 ∈ Algebra.adjoin ℂ (Set.range a) := Algebra.subset_adjoin ⟨0, rfl⟩
  intro y hy
  rw [Subalgebra.mem_toSubmodule] at hy
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    induction j using Fin.cases with
    | zero =>
      refine Submodule.mem_sup_right (Submodule.mem_map.2 ⟨1, ?_, ?_⟩)
      · exact (Subalgebra.mem_toSubmodule _).2 (one_mem _)
      · rw [LinearMap.mulRight_apply, one_mul]
    | succ k => exact Submodule.mem_sup_left (Algebra.subset_adjoin ⟨k, rfl⟩)
  | algebraMap r => exact Submodule.mem_sup_left (Subalgebra.algebraMap_mem _ r)
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    obtain ⟨p₁, hp₁, z₁, hz₁, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨p₂, hp₂, z₂, hz₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨q₁, hq₁, rfl⟩ := Submodule.mem_map.1 hz₁
    obtain ⟨q₂, hq₂, rfl⟩ := Submodule.mem_map.1 hz₂
    rw [Subalgebra.mem_toSubmodule] at hp₁ hp₂ hq₁ hq₂
    rw [LinearMap.mulRight_apply, LinearMap.mulRight_apply]
    have hp₂c : Commute p₂ (a 0) := GlobalTheory.CompanionTheory.CommStep.commute_of_mem_adjoin a hc 0 (hBC hp₂)
    have hq₂c : Commute q₂ (a 0) := GlobalTheory.CompanionTheory.CommStep.commute_of_mem_adjoin a hc 0 hq₂
    have e₁ : q₁ * a 0 * p₂ = q₁ * p₂ * a 0 := by
      rw [mul_assoc, ← hp₂c.eq, ← mul_assoc]
    have e₂ : q₁ * a 0 * (q₂ * a 0) = q₁ * q₂ * a 0 * a 0 := by
      rw [← mul_assoc, mul_assoc q₁, ← hq₂c.eq, ← mul_assoc]
    have key : (p₁ + q₁ * a 0) * (p₂ + q₂ * a 0) =
        p₁ * p₂ + (p₁ * q₂ + q₁ * p₂ + q₁ * q₂ * a 0) * a 0 := by
      rw [add_mul, mul_add, mul_add, e₁, e₂]
      simp only [add_mul, mul_assoc, add_assoc]
    rw [key]
    refine Submodule.add_mem_sup ((Subalgebra.mem_toSubmodule _).2 (mul_mem hp₁ hp₂))
      (Submodule.mem_map.2 ⟨p₁ * q₂ + q₁ * p₂ + q₁ * q₂ * a 0, ?_, LinearMap.mulRight_apply _ _ _⟩)
    rw [Subalgebra.mem_toSubmodule]
    exact add_mem (add_mem (mul_mem (hBC hp₁) hq₂) (mul_mem hq₁ (hBC hp₂)))
      (mul_mem (mul_mem hq₁ hq₂) ha0)

theorem finrank_map_pow_le {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (hc : ∀ i j, Commute (a i) (a j)) (k : ℕ) :
    finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
        (LinearMap.mulRight ℂ (a 0 ^ k))) ≤
      finrank ℂ (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)) +
        finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
          (LinearMap.mulRight ℂ (a 0 ^ (k + 1)))) := by
  have h := Submodule.map_mono (f := LinearMap.mulRight ℂ (a 0 ^ k))
    (GlobalTheory.CompanionTheory.CommStep.adjoin_le_sup a hc)
  have hcomp : (LinearMap.mulRight ℂ (a 0 ^ k)).comp (LinearMap.mulRight ℂ (a 0)) =
      LinearMap.mulRight ℂ (a 0 ^ (k + 1)) :=
    LinearMap.ext fun b => by
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, pow_succ', mul_assoc]
  rw [Submodule.map_sup, ← Submodule.map_comp, hcomp] at h
  have h1 := Submodule.finrank_mono h
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ))).map
      (LinearMap.mulRight ℂ (a 0 ^ k)))
    ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
      (LinearMap.mulRight ℂ (a 0 ^ (k + 1))))
  have h3 := Submodule.finrank_map_le (LinearMap.mulRight ℂ (a 0 ^ k))
    (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)))
  rw [Subalgebra.finrank_toSubmodule] at h3
  omega

theorem comm_step : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (l : ℕ)
    (a : Fin (l + 1) → Module.End ℂ V), (∀ i j, Commute (a i) (a j)) → ∀ x : ℕ,
    Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
      x * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)) +
        Module.finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
          (LinearMap.mulRight ℂ (a 0 ^ x))) := by
  intro V _ _ _ l a hc x
  induction x with
  | zero =>
    have hid : LinearMap.mulRight ℂ (a 0 ^ 0) = LinearMap.id :=
      LinearMap.ext fun b => by simp
    rw [hid, Submodule.map_id, Nat.zero_mul, Nat.zero_add, Subalgebra.finrank_toSubmodule]
  | succ x ih =>
    have h := GlobalTheory.CompanionTheory.CommStep.finrank_map_pow_le a hc x
    rw [add_mul, one_mul]
    omega

end GlobalTheory.CompanionTheory.CommStep
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CompactSubgroupFiniteOpenCosets
section
namespace GlobalTheory.CompanionTheory.CosetCover

theorem exists_finite_coset_cover :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K₀ K : Subgroup G),
      IsCompact (K₀ : Set G) → IsOpen (K : Set G) →
        ∃ (d : ℕ) (c : Fin d → G), (∀ i, c i ∈ K₀) ∧ ∀ g ∈ K₀, ∃ i, ∃ κ ∈ K, g = κ * c i := by
  intro G _ _ _ K₀ K hK₀ hK
  classical
  obtain ⟨t, ht⟩ := hK₀.elim_finite_subcover
    (fun g : K₀ => (fun x => x * (g : G)⁻¹) ⁻¹' (K : Set G))
    (fun g => hK.preimage (continuous_mul_const _))
    (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp⟩)
  refine ⟨t.card, fun i => ((t.equivFin.symm i : K₀) : G), fun i => (t.equivFin.symm i : K₀).2,
    fun g hg => ?_⟩
  obtain ⟨a, ha, hga⟩ := Set.mem_iUnion₂.1 (ht hg)
  refine ⟨t.equivFin ⟨a, ha⟩, g * (a : G)⁻¹, hga, ?_⟩
  simp

end GlobalTheory.CompanionTheory.CosetCover
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EigenvalueGapExists
section
namespace GlobalTheory.CompanionTheory.UGeoGap

theorem exists_gap_of_mem_Icc_top :
    ∀ (n : ℕ) (l : Fin n → ℝ) (L : ℝ), 0 < L → (∀ i, 0 ≤ l i ∧ l i ≤ L) → (∃ i, l i = L) →
      ∃ r : ℕ, r < n ∧ ∀ i, l i < r * (L / (n + 1)) ∨ (r + 1) * (L / (n + 1)) ≤ l i := by
  intro n l L hL _ hex
  obtain ⟨i₀, hi₀⟩ := hex
  by_contra hcon
  push Not at hcon
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hδpos : 0 < L / (n + 1) := div_pos hL hn
  choose f hf using fun r : Fin n => hcon r r.2
  have hinj : Function.Injective f := by
    intro r s hrs
    have h1 := hf r
    have h2 := hf s
    rw [hrs] at h1
    have a1 : ((r : ℕ) : ℝ) < (s : ℕ) + 1 :=
      lt_of_mul_lt_mul_right (lt_of_le_of_lt h1.1 h2.2) hδpos.le
    have a2 : ((s : ℕ) : ℝ) < (r : ℕ) + 1 :=
      lt_of_mul_lt_mul_right (lt_of_le_of_lt h2.1 h1.2) hδpos.le
    have b1 : (r : ℕ) < (s : ℕ) + 1 := by exact_mod_cast a1
    have b2 : (s : ℕ) < (r : ℕ) + 1 := by exact_mod_cast a2
    exact Fin.ext (by omega)
  obtain ⟨r, hr⟩ := (Finite.injective_iff_surjective.mp hinj) i₀
  have h1 := (hf r).2
  rw [hr, hi₀] at h1
  have hr1 : ((r : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast r.2
  have h2 : (((r : ℕ) : ℝ) + 1) * (L / (n + 1)) ≤ n * (L / (n + 1)) :=
    mul_le_mul_of_nonneg_right hr1 hδpos.le
  have h3 : (n : ℝ) * (L / (n + 1)) < (n + 1) * (L / (n + 1)) :=
    mul_lt_mul_of_pos_right (by linarith) hδpos
  have h4 : ((n : ℝ) + 1) * (L / (n + 1)) = L := by
    field_simp
  linarith

end GlobalTheory.CompanionTheory.UGeoGap
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FinrankAdjoinLeAdd
section
namespace GlobalTheory.CompanionTheory.CommSplit

open Module

variable {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def compr (W W' : Submodule ℂ V) (hc : IsCompl W W') :
    End ℂ V →ₗ[ℂ] End ℂ W where
  toFun b := (W.linearProjOfIsCompl W' hc) ∘ₗ b ∘ₗ W.subtype
  map_add' b c := by ext w; simp
  map_smul' t b := by ext w; simp

lemma compr_of_inv (W W' : Submodule ℂ V) (hc : IsCompl W W') (b : End ℂ V)
    (hb : ∀ w ∈ W, b w ∈ W) (w : W) : compr W W' hc b w = ⟨b w, hb w w.2⟩ := by
  show W.linearProjOfIsCompl W' hc (b w) = _
  exact Submodule.linearProjOfIsCompl_apply_left hc ⟨b w, hb w w.2⟩

lemma compr_eq_restrict (W W' : Submodule ℂ V) (hc : IsCompl W W') (b : End ℂ V)
    (hb : ∀ w ∈ W, b w ∈ W) : compr W W' hc b = b.restrict hb := by
  refine LinearMap.ext fun w => ?_
  rw [compr_of_inv W W' hc b hb w]
  rfl

lemma compr_mul (W W' : Submodule ℂ V) (hc : IsCompl W W') (b c : End ℂ V)
    (hcW : ∀ w ∈ W, c w ∈ W) :
    compr W W' hc (b * c) = compr W W' hc b * compr W W' hc c := by
  refine LinearMap.ext fun w => ?_
  rw [Module.End.mul_apply, compr_of_inv W W' hc c hcW w]
  rfl

lemma compr_algebraMap (W W' : Submodule ℂ V) (hc : IsCompl W W') (t : ℂ) :
    compr W W' hc (algebraMap ℂ (End ℂ V) t) = algebraMap ℂ (End ℂ W) t := by
  have hb : ∀ w ∈ W, algebraMap ℂ (End ℂ V) t w ∈ W := fun w hw => by
    rw [Module.algebraMap_end_apply]
    exact W.smul_mem t hw
  rw [compr_eq_restrict W W' hc _ hb]
  ext w
  simp [Module.algebraMap_end_apply]

lemma adjoin_compr {l : ℕ} (a : Fin l → End ℂ V) (W W' : Submodule ℂ V) (hc : IsCompl W W')
    (h : ∀ i, ∀ w ∈ W, a i w ∈ W) (b : End ℂ V) (hb : b ∈ Algebra.adjoin ℂ (Set.range a)) :
    (∀ w ∈ W, b w ∈ W) ∧ compr W W' hc b ∈
      Algebra.adjoin ℂ (Set.range fun i => ((a i).restrict (h i) : End ℂ W)) := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨h i, ?_⟩
    rw [compr_eq_restrict W W' hc _ (h i)]
    exact Algebra.subset_adjoin ⟨i, rfl⟩
  | algebraMap r =>
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [Module.algebraMap_end_apply]
      exact W.smul_mem r hw
    · rw [compr_algebraMap]
      exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy =>
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [LinearMap.add_apply]
      exact W.add_mem (hx.1 w hw) (hy.1 w hw)
    · rw [map_add (f := _)]
      exact Subalgebra.add_mem _ hx.2 hy.2
  | mul x y _ _ hx hy =>
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [Module.End.mul_apply]
      exact hx.1 _ (hy.1 w hw)
    · rw [compr_mul W W' hc x y hy.1]
      exact Subalgebra.mul_mem _ hx.2 hy.2

theorem finrank_adjoin_le_add :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (l : ℕ)
      (a : Fin l → Module.End ℂ V) (W W' : Submodule ℂ V), IsCompl W W' →
      ∀ (h : ∀ i, ∀ w ∈ W, a i w ∈ W) (h' : ∀ i, ∀ w ∈ W', a i w ∈ W'),
      Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i =>
          ((a i).restrict (h i) : Module.End ℂ W))) +
        Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i =>
          ((a i).restrict (h' i) : Module.End ℂ W'))) := by
  intro V _ _ _ l a W W' hc h h'
  let AW := Algebra.adjoin ℂ (Set.range fun i => ((a i).restrict (h i) : Module.End ℂ W))
  let AW' := Algebra.adjoin ℂ (Set.range fun i => ((a i).restrict (h' i) : Module.End ℂ W'))
  let Φ : Algebra.adjoin ℂ (Set.range a) →ₗ[ℂ] AW × AW' :=
    { toFun := fun b => (⟨compr W W' hc b, (adjoin_compr a W W' hc h b b.2).2⟩,
        ⟨compr W' W hc.symm b, (adjoin_compr a W' W hc.symm h' b b.2).2⟩)
      map_add' := fun b c => by
        ext <;> simp [map_add (f := _)]
      map_smul' := fun t b => by
        ext <;> simp [map_smul] }
  have hinj : Function.Injective Φ := by
    intro b c hbc
    have h1 := congrArg (fun p => (p.1 : Module.End ℂ W)) hbc
    have h2 := congrArg (fun p => (p.2 : Module.End ℂ W')) hbc
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h1 h2
    apply Subtype.ext
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ W ⊔ W' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
    have e1 : (b : Module.End ℂ V) w = (c : Module.End ℂ V) w := by
      have e := LinearMap.congr_fun h1 ⟨w, hw⟩
      rw [compr_of_inv W W' hc _ (adjoin_compr a W W' hc h b b.2).1,
        compr_of_inv W W' hc _ (adjoin_compr a W W' hc h c c.2).1] at e
      exact congrArg Subtype.val e
    have e2 : (b : Module.End ℂ V) w' = (c : Module.End ℂ V) w' := by
      have e := LinearMap.congr_fun h2 ⟨w', hw'⟩
      rw [compr_of_inv W' W hc.symm _ (adjoin_compr a W' W hc.symm h' b b.2).1,
        compr_of_inv W' W hc.symm _ (adjoin_compr a W' W hc.symm h' c c.2).1] at e
      exact congrArg Subtype.val e
    rw [map_add (f := _), map_add (f := _), e1, e2]
  calc Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ Module.finrank ℂ (AW × AW') :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = Module.finrank ℂ AW + Module.finrank ℂ AW' := Module.finrank_prod

end GlobalTheory.CompanionTheory.CommSplit
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FinrankRangePowConvex
section
namespace GlobalTheory.CompanionTheory.CommNil

open Module

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem finrank_map_add_finrank_inf_ker' {E F : Type} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] [AddCommGroup F] [Module ℂ F] (f : E →ₗ[ℂ] F) (A : Submodule ℂ E) :
    finrank ℂ (A.map f) + finrank ℂ (A ⊓ LinearMap.ker f : Submodule ℂ E) = finrank ℂ A := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict A)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
  exact h

theorem exists_rel_compl [FiniteDimensional ℂ V] (W' W : Submodule ℂ V) (h : W' ≤ W) :
    ∃ Y : Submodule ℂ V, Y ⊔ W' = W ∧ finrank ℂ Y + finrank ℂ W' = finrank ℂ W := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W'
  have hsup : C ⊓ W ⊔ W' = W := by
    rw [sup_comm, ← sup_inf_assoc_of_le C h, hC.sup_eq_top, top_inf_eq]
  have hinf : C ⊓ W ⊓ W' = ⊥ := by
    have hle : C ⊓ W ⊓ W' ≤ C ⊓ W' := inf_le_inf_right W' inf_le_left
    rw [inf_comm C W', hC.inf_eq_bot] at hle
    exact le_bot_iff.1 hle
  refine ⟨C ⊓ W, hsup, ?_⟩
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (C ⊓ W) W'
  rw [hsup, hinf, finrank_bot, add_zero] at hdim
  exact hdim.symm

theorem range_pow_succ (a : Module.End ℂ V) (i : ℕ) :
    LinearMap.range (a ^ (i + 1)) = (LinearMap.range (a ^ i)).map a := by
  rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]

theorem range_pow_succ_le (a : Module.End ℂ V) (i : ℕ) :
    LinearMap.range (a ^ (i + 1)) ≤ LinearMap.range (a ^ i) := by
  rw [pow_succ, Module.End.mul_eq_comp]
  exact LinearMap.range_comp_le_range _ _

theorem finrank_range_pow_convex [FiniteDimensional ℂ V] (a : Module.End ℂ V) (i : ℕ) :
    2 * finrank ℂ (LinearMap.range (a ^ (i + 1))) ≤
      finrank ℂ (LinearMap.range (a ^ i)) + finrank ℂ (LinearMap.range (a ^ (i + 2))) := by
  have h0 : finrank ℂ (LinearMap.range (a ^ (i + 1))) +
      finrank ℂ (LinearMap.range (a ^ i) ⊓ LinearMap.ker a : Submodule ℂ V) = finrank ℂ (LinearMap.range (a ^ i)) := by
    have h := finrank_map_add_finrank_inf_ker' a (LinearMap.range (a ^ i))
    rw [← range_pow_succ] at h
    exact h
  have h1 : finrank ℂ (LinearMap.range (a ^ (i + 2))) +
      finrank ℂ (LinearMap.range (a ^ (i + 1)) ⊓ LinearMap.ker a : Submodule ℂ V) =
        finrank ℂ (LinearMap.range (a ^ (i + 1))) := by
    have h := finrank_map_add_finrank_inf_ker' a (LinearMap.range (a ^ (i + 1)))
    rw [← range_pow_succ] at h
    exact h
  have hmono : finrank ℂ (LinearMap.range (a ^ (i + 1)) ⊓ LinearMap.ker a : Submodule ℂ V) ≤
      finrank ℂ (LinearMap.range (a ^ i) ⊓ LinearMap.ker a : Submodule ℂ V) :=
    Submodule.finrank_mono (inf_le_inf_right _ (range_pow_succ_le a i))
  omega

theorem succ_mul_drop_le [FiniteDimensional ℂ V] (a : Module.End ℂ V) (x : ℕ) :
    (x + 1) * finrank ℂ (LinearMap.range (a ^ x)) + finrank ℂ (LinearMap.range (a ^ (x + 1))) ≤
      (x + 1) * finrank ℂ (LinearMap.range (a ^ (x + 1))) +
        finrank ℂ (LinearMap.range (a ^ 0)) := by
  induction x with
  | zero => omega
  | succ x ih =>
    have conv : 2 * finrank ℂ (LinearMap.range (a ^ (x + 1))) ≤
        finrank ℂ (LinearMap.range (a ^ x)) + finrank ℂ (LinearMap.range (a ^ (x + 1 + 1))) :=
      finrank_range_pow_convex a x
    have hm := Nat.mul_le_mul_left (x + 1) conv
    nlinarith [ih, hm]

theorem range_le_ker_of_commute (a b : Module.End ℂ V) (hab : Commute b a) (ha : IsNilpotent a)
    (x : ℕ) (Y : Submodule ℂ V) (hY : Y ⊔ LinearMap.range (a ^ (x + 1)) = LinearMap.range (a ^ x))
    (hb : Y ≤ LinearMap.ker b) : LinearMap.range (a ^ x) ≤ LinearMap.ker b := by
  have step : ∀ v ∈ LinearMap.range (a ^ x), ∃ u ∈ LinearMap.range (a ^ x), b v = a (b u) := by
    intro v hv
    rw [← hY] at hv
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [range_pow_succ] at hz
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hz
    refine ⟨u, hu, ?_⟩
    have hba := LinearMap.congr_fun hab.eq u
    rw [Module.End.mul_apply, Module.End.mul_apply] at hba
    rw [map_add (f := _), LinearMap.mem_ker.1 (hb hy), zero_add, hba]
  have key : ∀ k : ℕ, ∀ v ∈ LinearMap.range (a ^ x), ∃ u ∈ LinearMap.range (a ^ x),
      b v = (a ^ k) (b u) := by
    intro k
    induction k with
    | zero => exact fun v hv => ⟨v, hv, by simp⟩
    | succ k ih =>
      intro v hv
      obtain ⟨u, hu, h1⟩ := ih v hv
      obtain ⟨u', hu', h2⟩ := step u hu
      exact ⟨u', hu', by rw [h1, h2, pow_succ, Module.End.mul_apply]⟩
  obtain ⟨N, hN⟩ := ha
  intro v hv
  obtain ⟨u, _, hu⟩ := key N v hv
  rw [LinearMap.mem_ker, hu, hN, LinearMap.zero_apply]

theorem finrank_map_le_of_ker {E F G : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup F] [Module ℂ F] [AddCommGroup G] [Module ℂ G]
    (f : E →ₗ[ℂ] F) (T : E →ₗ[ℂ] G) (A : Submodule ℂ E)
    (h : ∀ b ∈ A, T b = 0 → f b = 0) : finrank ℂ (A.map f) ≤ finrank ℂ (A.map T) := by
  have hf := finrank_map_add_finrank_inf_ker' f A
  have hT := finrank_map_add_finrank_inf_ker' T A
  have hle : finrank ℂ (A ⊓ LinearMap.ker T : Submodule ℂ E) ≤ finrank ℂ (A ⊓ LinearMap.ker f : Submodule ℂ E) :=
    Submodule.finrank_mono fun b hb => Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 hb).1,
      LinearMap.mem_ker.2 (h b (Submodule.mem_inf.1 hb).1 (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hb).2))⟩
  omega

theorem succ_mul_finrank_map_le :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : Module.End ℂ V),
      IsNilpotent a → ∀ (x : ℕ) (A : Submodule ℂ (Module.End ℂ V)), (∀ b ∈ A, Commute b a) →
        (x + 1) * Module.finrank ℂ (A.map (LinearMap.mulRight ℂ (a ^ x))) ≤
          Module.finrank ℂ V ^ 2 := by
  intro V _ _ _ a ha x A hA
  obtain ⟨Y, hY, hdim⟩ := exists_rel_compl (LinearMap.range (a ^ (x + 1))) (LinearMap.range (a ^ x))
    (range_pow_succ_le a x)
  let T : Module.End ℂ V →ₗ[ℂ] (Y →ₗ[ℂ] V) := LinearMap.lcomp ℂ V Y.subtype
  have hker : ∀ b ∈ A, T b = 0 → LinearMap.mulRight ℂ (a ^ x) b = 0 := by
    intro b hbA hTb
    have hYk : Y ≤ LinearMap.ker b := by
      intro y hy
      have hy0 := LinearMap.congr_fun hTb ⟨y, hy⟩
      rw [LinearMap.lcomp_apply, LinearMap.zero_apply] at hy0
      exact LinearMap.mem_ker.2 hy0
    have hR := range_le_ker_of_commute a b (hA b hbA) ha x Y hY hYk
    rw [LinearMap.mulRight_apply]
    ext v
    rw [Module.End.mul_apply, LinearMap.zero_apply]
    exact LinearMap.mem_ker.1 (hR (LinearMap.mem_range_self _ v))
  have h7 := finrank_map_le_of_ker (LinearMap.mulRight ℂ (a ^ x)) T A hker
  have h8 : Module.finrank ℂ (A.map T) ≤ Module.finrank ℂ Y * Module.finrank ℂ V :=
    (Submodule.finrank_le _).trans (le_of_eq (Module.finrank_linearMap ℂ ℂ Y V))
  have h5 := succ_mul_drop_le a x
  have hr0 : Module.finrank ℂ (LinearMap.range (a ^ 0)) ≤ Module.finrank ℂ V := Submodule.finrank_le _
  rw [← hdim] at h5
  have hY1 : (x + 1) * Module.finrank ℂ Y ≤ Module.finrank ℂ V := by nlinarith [h5, hr0]
  calc (x + 1) * Module.finrank ℂ (A.map (LinearMap.mulRight ℂ (a ^ x)))
      ≤ (x + 1) * (Module.finrank ℂ Y * Module.finrank ℂ V) := Nat.mul_le_mul_left _ (h7.trans h8)
    _ = ((x + 1) * Module.finrank ℂ Y) * Module.finrank ℂ V := by ring
    _ ≤ Module.finrank ℂ V * Module.finrank ℂ V := Nat.mul_le_mul_right _ hY1
    _ = Module.finrank ℂ V ^ 2 := by ring

end GlobalTheory.CompanionTheory.CommNil
end

