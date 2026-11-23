module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SurjectiveOfKerLeMapSupSq
section
namespace GlobalTheory.SurjectiveOfKerSq

theorem eq_of_le_sup_sq {B : Type} [CommRing B] (I K : Ideal B) (m : ℕ)
    (hnil : I ^ (m + 1) = ⊥) (h1 : K ≤ I) (h2 : I ≤ K ⊔ I ^ 2) : I = K := by
  have key : ∀ n : ℕ, I ≤ K ⊔ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine h2.trans (sup_le le_sup_left ?_)
      calc I ^ 2 = I * I := pow_two I
        _ ≤ I * (K ⊔ I ^ (n + 1)) := Ideal.mul_mono_right ih
        _ = I * K ⊔ I ^ (n + 1 + 1) := by rw [Ideal.mul_sup, ← pow_succ']
        _ ≤ K ⊔ I ^ (n + 1 + 1) := sup_le_sup_right Ideal.mul_le_right _
  have := key m
  rw [hnil, sup_bot_eq] at this
  exact le_antisymm this h1

theorem surjective_of_ker_le_map_sup_sq {V : Type} [CommRing V] {A B : Type} [CommRing A]
    [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B) (aug : B →ₐ[V] V) (m : ℕ)
    (hnil : RingHom.ker aug ^ (m + 1) = ⊥) (J : Ideal A)
    (h1 : Ideal.map f J ≤ RingHom.ker aug)
    (h2 : RingHom.ker aug ≤ Ideal.map f J ⊔ RingHom.ker aug ^ 2) :
    Function.Surjective f := by
  have hI : RingHom.ker aug = Ideal.map f J := eq_of_le_sup_sq _ _ m hnil h1 h2
  have base : ∀ b : B, ∃ a : A, b - f a ∈ RingHom.ker aug := by
    intro b
    refine ⟨algebraMap V A (aug b), ?_⟩
    simp [RingHom.mem_ker]
  have step : ∀ n : ℕ, ∀ x ∈ RingHom.ker aug ^ n, ∀ b : B,
      ∃ a : A, b * x - f a ∈ RingHom.ker aug ^ (n + 1) := by
    intro n x hx
    have hpow : RingHom.ker aug ^ n = Ideal.span (f '' (J ^ n : Ideal A)) := by
      rw [hI, ← Ideal.map_pow]; rfl
    have hx' := hx
    rw [hpow] at hx'
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      intro b
      obtain ⟨j, hj, rfl⟩ := hy
      obtain ⟨a, ha⟩ := base b
      refine ⟨a * j, ?_⟩
      have hfj : f j ∈ RingHom.ker aug ^ n := by
        rw [hpow]; exact Ideal.subset_span ⟨j, hj, rfl⟩
      have e : b * f j - f (a * j) = f j * (b - f a) := by rw [map_mul]; ring
      rw [e, pow_succ]
      exact Ideal.mul_mem_mul hfj ha
    | zero => intro b; exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      intro b
      obtain ⟨a, ha⟩ := hy b
      obtain ⟨c, hc⟩ := hz b
      refine ⟨a + c, ?_⟩
      have e : b * (y + z) - f (a + c) = (b * y - f a) + (b * z - f c) := by
        rw [map_add (f := _)]; ring
      rw [e]
      exact Ideal.add_mem _ ha hc
    | smul c y _ hy =>
      intro b
      obtain ⟨a, ha⟩ := hy (b * c)
      exact ⟨a, by rwa [smul_eq_mul, ← mul_assoc]⟩
  have all : ∀ n : ℕ, ∀ b : B, ∃ a : A, b - f a ∈ RingHom.ker aug ^ n := by
    intro n
    induction n with
    | zero => intro b; exact ⟨0, by simp⟩
    | succ n ih =>
      intro b
      obtain ⟨a, ha⟩ := ih b
      obtain ⟨c, hc⟩ := step n _ ha 1
      refine ⟨a + c, ?_⟩
      have e : b - f (a + c) = 1 * (b - f a) - f c := by rw [map_add (f := _)]; ring
      rw [e]
      exact hc
  intro b
  obtain ⟨a, ha⟩ := all (m + 1) b
  rw [hnil, Ideal.mem_bot, sub_eq_zero] at ha
  exact ⟨a, ha.symm⟩

end GlobalTheory.SurjectiveOfKerSq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TendstoIntegralInnerOfTendstoELpNormTwo
section
open MeasureTheory Filter Topology

namespace GlobalTheory

theorem tendsto_integral_inner_of_tendsto_eLpNorm_two :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v v' : ℕ → X → E) (u u' : X → E), (∀ n, MemLp (v n) 2 μ) → (∀ n, MemLp (v' n) 2 μ) → MemLp u 2 μ → MemLp u' 2 μ → Tendsto (fun n => eLpNorm (v n - u) 2 μ) atTop (𝓝 0) → Tendsto (fun n => eLpNorm (v' n - u') 2 μ) atTop (𝓝 0) → Tendsto (fun n => ∫ x, inner ℂ (v' n x) (v n x) ∂μ) atTop (𝓝 (∫ x, inner ℂ (u' x) (u x) ∂μ)) := by
  intro X _ μ E _ _ v v' u u' hv hv' hu hu' h h'
  have key : ∀ (f g : X → E) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ),
      ∫ x, inner ℂ (f x) (g x) ∂μ = inner ℂ (hf.toLp f) (hg.toLp g) := by
    intro f g hf hg
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  have h1 : Tendsto (fun n => (hv n).toLp (v n)) atTop (𝓝 (hu.toLp u)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hv u hu).2 h
  have h2 : Tendsto (fun n => (hv' n).toLp (v' n)) atTop (𝓝 (hu'.toLp u')) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v' hv' u' hu').2 h'
  rw [key u' u hu' hu]
  simp_rw [fun n => key (v' n) (v n) (hv' n) (hv n)]
  exact h2.inner h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitsZpowSurjective
section
namespace GlobalTheory.DivisibleUnits

theorem units_zpow_surjective {F : Type} [Field F] [IsAlgClosed F] {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun a : Fˣ => a ^ n) := by
  have nat_root : ∀ (m : ℕ), 0 < m → ∀ x : Fˣ, ∃ y : Fˣ, y ^ m = x := by
    intro m hm x
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : F) hm
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hm.ne'] at hz
      exact x.ne_zero hz.symm
    refine ⟨Units.mk0 z hz0, ?_⟩
    ext
    simp [hz]
  intro x
  rcases Int.lt_or_gt_of_ne hn with h | h
  · obtain ⟨y, hy⟩ := nat_root n.natAbs (Int.natAbs_pos.mpr hn) x⁻¹
    refine ⟨y, ?_⟩
    show y ^ n = x
    have : n = -(n.natAbs : ℤ) := by omega
    rw [this, zpow_neg, zpow_natCast, hy, inv_inv]
  · obtain ⟨y, hy⟩ := nat_root n.natAbs (Int.natAbs_pos.mpr hn) x
    refine ⟨y, ?_⟩
    show y ^ n = x
    have : n = (n.natAbs : ℤ) := by omega
    rw [this, zpow_natCast, hy]

noncomputable def divisibleUnits (F : Type) [Field F] [IsAlgClosed F] :
    DivisibleBy (Additive Fˣ) ℤ :=
  divisibleByOfSMulRightSurj (Additive Fˣ) ℤ (fun {n} hn x => by
    obtain ⟨y, hy⟩ := units_zpow_surjective (F := F) hn (Additive.toMul x)
    exact ⟨Additive.ofMul y, by simpa using congrArg Additive.ofMul hy⟩)

theorem exists_extension {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (hΦ : Function.Injective Φ) (χ : H →* Fˣ) :
    ∃ κ : M →* Fˣ, ∀ x : H, κ (Φ x) = χ x := by
  letI := divisibleUnits F
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive Fˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive Φ) hΦ (MonoidHom.toAdditive χ)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  have := DFunLike.congr_fun hh (Additive.ofMul x)
  exact this

theorem target : ∀ {H M F : Type} [inst : CommGroup H] [inst_1 : CommGroup M] [inst_2 : Field F] [IsAlgClosed F] (Φ : H →* M), Function.Injective (⇑Φ : H → M) → ∀ (χ : H →* Fˣ), ∃ (κ : M →* Fˣ), ∀ (x : H), (κ : M → Fˣ) ((Φ : H → M) x) = (χ : H → Fˣ) x :=
  fun Φ hΦ χ => exists_extension Φ hΦ χ

end GlobalTheory.DivisibleUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.VecPolyMemSpanValues
section
namespace GlobalTheory

theorem vecPoly_mem_span_values (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (Z : ℂ → V)
    (X : ℕ → V) (ν : Fin n → ℂ) (hν : Function.Injective ν)
    (hZ : ∀ s : ℂ, Z s = ∑ j ∈ Finset.range n, s ^ j • X j) :
    (∀ j, j < n → X j ∈ Submodule.span ℂ (Set.range fun i => Z (ν i))) ∧
      ∀ s : ℂ, Z s ∈ Submodule.span ℂ (Set.range fun i => Z (ν i)) := by
  classical
  set W := Submodule.span ℂ (Set.range fun i => Z (ν i)) with hW
  set M : Matrix (Fin n) (Fin n) ℂ := Matrix.vandermonde ν with hM
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hν)
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunit
  have hZν : ∀ i, Z (ν i) = ∑ l : Fin n, M i l • X l := by
    intro i
    rw [hZ, ← Fin.sum_univ_eq_sum_range (fun j => ν i ^ j • X j) n]
    simp [hM, Matrix.vandermonde_apply]
  have hX : ∀ k : Fin n, X k ∈ W := by
    intro k
    have key : ∀ l, ∑ i, M⁻¹ k i * M i l = (1 : Matrix (Fin n) (Fin n) ℂ) k l := fun l => by
      rw [← hinv, Matrix.mul_apply]
    have hsum : ∑ i : Fin n, M⁻¹ k i • Z (ν i) = X k := by
      simp_rw [hZν, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, key, Matrix.one_apply, ite_smul, one_smul, zero_smul]
      simp
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨fun j hj => hX ⟨j, hj⟩, fun s => ?_⟩
  rw [hZ]
  exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hX ⟨j, Finset.mem_range.mp hj⟩)

end GlobalTheory
end

