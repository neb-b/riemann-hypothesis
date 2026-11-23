module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SimplicialConeTilesSign
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0017

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PlaceApply
section
set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance

theorem abs_le_of_sum_eq_zero {F : Type} [Field F] [NumberField F] (f : InfinitePlace F → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hs : ∑ w, f w = 0) (hf : ∀ w, w ≠ w₀ → |f w| ≤ C) (w : InfinitePlace F) :
    |f w| ≤ (Fintype.card (InfinitePlace F) : ℝ) * C := by
  classical
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨w⟩
  by_cases hw : w = w₀
  · subst hw
    have h1 : f w₀ = -∑ v ∈ Finset.univ.erase w₀, f v := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w₀)] at hs
      linarith
    rw [h1, abs_neg]
    calc |∑ v ∈ Finset.univ.erase w₀, f v| ≤ ∑ v ∈ Finset.univ.erase w₀, |f v| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ Finset.univ.erase w₀, C :=
          Finset.sum_le_sum fun v hv => hf v (Finset.ne_of_mem_erase hv)
      _ = ((Finset.univ.erase w₀).card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card (InfinitePlace F) : ℝ) * C := by
          refine mul_le_mul_of_nonneg_right ?_ hC
          exact_mod_cast (Finset.card_erase_le).trans (Finset.card_le_univ _)
  · calc |f w| ≤ C := hf w hw
      _ = 1 * C := (one_mul C).symm
      _ ≤ (Fintype.card (InfinitePlace F) : ℝ) * C := mul_le_mul_of_nonneg_right hcard hC

theorem place_apply {F : Type} [Field F] [NumberField F] (σ : F →+* ℝ) (y : F) :
    (InfinitePlace.mk (Complex.ofRealHom.comp σ)) y = |σ y| := by
  rw [InfinitePlace.apply]
  simp

theorem balance : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∃ M : ℝ, ∀ x : F, TotPos F x → ∃ u : (𝓞 F)ˣ, u ∈ congUnits 𝔣 ∧
      ∀ σ τ : F →+* ℝ, σ (((u : 𝓞 F) : F) * x) ≤ M * τ (((u : 𝓞 F) : F) * x) := by
  intro F _ _ _ 𝔣 h𝔣
  obtain ⟨e, he, hpow⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.exists_pow_mem_congUnits F 𝔣 h𝔣
  obtain ⟨C, hC, hbound⟩ := GlobalTheory.T.unit_log_lattice_bounded_translate F e he
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (Fintype.card (InfinitePlace F) : ℝ) := ⟨_, rfl⟩
  refine ⟨Real.exp (2 * (n * C)), fun x hx => ?_⟩
  have hx0 : x ≠ 0 := by
    intro h0
    have h := hx (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal (w₀ : InfinitePlace F)))
    rw [h0, map_zero] at h
    exact lt_irrefl _ h
  have hwx : ∀ w : InfinitePlace F, 0 < w x := fun w => InfinitePlace.pos_iff.mpr hx0
  have hn0 : n ≠ 0 := by
    rw [hn]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(w₀ : InfinitePlace F)⟩).ne'
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ∑ w : InfinitePlace F, Real.log (w x) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ := hbound (fun w => Real.log (w.1 x) - s / n)
  have hv := hpow u
  refine ⟨u ^ e, hv, fun σ τ => ?_⟩
  obtain ⟨-, hvpos⟩ := hv
  have hpowc : (((u ^ e : (𝓞 F)ˣ) : 𝓞 F) : F) = (algebraMap (𝓞 F) F (u : 𝓞 F)) ^ e := by
    rw [Units.val_pow_eq_pow_val]
    exact map_pow (algebraMap (𝓞 F) F) _ _
  have hξpos : ∀ ρ : F →+* ℝ, 0 < ρ ((((u ^ e : (𝓞 F)ˣ) : 𝓞 F) : F) * x) := by
    intro ρ
    rw [map_mul]
    exact mul_pos (hvpos ρ) (hx ρ)
  generalize hξ : (((u ^ e : (𝓞 F)ˣ) : 𝓞 F) : F) * x = ξ at hξpos ⊢
  have hlog : ∀ w : InfinitePlace F,
      Real.log (w ξ) = e * Real.log (w (algebraMap (𝓞 F) F (u : 𝓞 F))) + Real.log (w x) := by
    intro w
    have hwu : w (algebraMap (𝓞 F) F (u : 𝓞 F)) ≠ 0 :=
      (InfinitePlace.pos_iff.mpr (NumberField.Units.coe_ne_zero u)).ne'
    rw [← hξ, hpowc, map_mul, map_pow, Real.log_mul (pow_ne_zero _ hwu) (hwx w).ne', Real.log_pow]
  set f : InfinitePlace F → ℝ := fun w => Real.log (w ξ) - s / n with hf
  have hsumu : ∑ w : InfinitePlace F, Real.log (w (algebraMap (𝓞 F) F (u : 𝓞 F))) = 0 := by
    have h := NumberField.Units.sum_mult_mul_log u
    simpa only [IsTotallyReal.mult_eq, Nat.cast_one, one_mul] using h
  have hsum : ∑ w, f w = 0 := by
    have h1 : ∀ w, f w = (e : ℝ) * Real.log (w (algebraMap (𝓞 F) F (u : 𝓞 F))) + Real.log (w x) - s / n :=
      fun w => by
        show Real.log (w ξ) - s / n = _
        rw [hlog w]
    rw [Finset.sum_congr rfl (fun w _ => h1 w), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hsumu, ← hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]
    have h2 : n * (s / n) = s := by field_simp
    rw [h2]
    ring
  have hfC : ∀ w, w ≠ w₀ → |f w| ≤ C := by
    intro w hw
    have h := hu ⟨w, hw⟩
    simp only [logEmbedding_component, IsTotallyReal.mult_eq, Nat.cast_one, one_mul] at h
    have h2 : f w = Real.log (w x) - s / n + e * Real.log (w (algebraMap (𝓞 F) F (u : 𝓞 F))) := by
      show Real.log (w ξ) - s / n = _
      rw [hlog w]
      ring
    rw [h2]
    exact h
  have hbd : ∀ w, |f w| ≤ n * C := fun w => by
    rw [hn]
    exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance.abs_le_of_sum_eq_zero f C hC hsum hfC w
  have hρ : ∀ ρ : F →+* ℝ, Real.log (ρ ξ) = f (InfinitePlace.mk (Complex.ofRealHom.comp ρ)) + s / n := by
    intro ρ
    rw [hf]
    simp only []
    rw [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance.place_apply, abs_of_pos (hξpos ρ)]
    ring
  have key : Real.log (σ ξ) ≤ 2 * (n * C) + Real.log (τ ξ) := by
    rw [hρ σ, hρ τ]
    have h1 := abs_le.mp (hbd (InfinitePlace.mk (Complex.ofRealHom.comp σ)))
    have h2 := abs_le.mp (hbd (InfinitePlace.mk (Complex.ofRealHom.comp τ)))
    linarith [h1.2, h2.1]
  calc σ ξ = Real.exp (Real.log (σ ξ)) := (Real.exp_log (hξpos σ)).symm
    _ ≤ Real.exp (2 * (n * C) + Real.log (τ ξ)) := Real.exp_le_exp.mpr key
    _ = Real.exp (2 * (n * C)) * τ ξ := by rw [Real.exp_add, Real.exp_log (hξpos τ)]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ShintaniValuesNegativeIntegersRational
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay

theorem zpow_le_two_pow_mul {E u : ℝ} (hE : 0 < E) (h1 : E ≤ u) (h2 : u ≤ 2 * E) (z : ℤ) :
    u ^ z ≤ 2 ^ z.natAbs * E ^ z := by
  have hu : 0 < u := lt_of_lt_of_le hE h1
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simp only [Int.natAbs_natCast, zpow_natCast]
    calc u ^ n ≤ (2 * E) ^ n := pow_le_pow_left₀ hu.le h2 n
      _ = 2 ^ n * E ^ n := mul_pow _ _ _
  · simp only [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast]
    have hEn : 0 < E ^ n := pow_pos hE n
    have a1 : (u ^ n)⁻¹ ≤ (E ^ n)⁻¹ := inv_anti₀ hEn (pow_le_pow_left₀ hE.le h1 n)
    have a2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    calc (u ^ n)⁻¹ ≤ (E ^ n)⁻¹ := a1
      _ = 1 * (E ^ n)⁻¹ := (one_mul _).symm
      _ ≤ 2 ^ n * (E ^ n)⁻¹ := mul_le_mul_of_nonneg_right a2 (inv_nonneg.2 hEn.le)

theorem one_le_sizeE {r : ℕ} {x : Fin r → ℝ} (hx : ∀ i, 0 ≤ x i) : 1 ≤ sizeE x := by
  have : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
  unfold sizeE; linarith

theorem sizeE_add_smul {r : ℕ} (x : Fin r → ℝ) (c : Fin r) (τ : ℝ) :
    sizeE (x + τ • (Pi.single c 1 : Fin r → ℝ)) = sizeE x + τ := by
  simp [sizeE, Finset.sum_add_distrib, Pi.single_apply]
  ring

theorem nonneg_add_smul {r : ℕ} {x : Fin r → ℝ} (hx : ∀ i, 0 ≤ x i) (c : Fin r) {τ : ℝ} (hτ : 0 ≤ τ) (k : Fin r) :
    0 ≤ (x + τ • (Pi.single c 1 : Fin r → ℝ)) k := by
  have : 0 ≤ τ * (Pi.single c 1 : Fin r → ℝ) k := by
    refine mul_nonneg hτ ?_
    by_cases h : k = c
    · subst h; simp
    · simp [Pi.single_apply, h]
  simpa using add_nonneg (hx k) this

theorem sum_add_single {ι : Type} [Fintype ι] [DecidableEq ι] (β : ι → ℕ) (j : ι) :
    ∑ i, (((β + Pi.single j 1 : ι → ℕ) i : ℕ) : ℤ) = ∑ i, (β i : ℤ) + 1 := by
  simp [Finset.sum_add_distrib, Pi.single_apply]

theorem diff_bound (ι : Type) [Fintype ι] [DecidableEq ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j) (B R : ℕ) (cs : List (Fin r)) (β : ι → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re → ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
      ‖DLR cs (Fr a b s β) x‖ ≤ C * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ) - (cs.length : ℤ)) := by
  induction cs generalizing β with
  | nil =>
    obtain ⟨C, hC, h⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.baseBound ι r a b ha hb B R β
    refine ⟨C, hC, fun s hs hB x hx => ?_⟩
    simpa [DLR] using h s hs hB x hx
  | cons c cs ih =>
    choose C hC0 hC using fun j => ih (β + Pi.single j 1)
    obtain ⟨z, hz⟩ : ∃ z : ℤ, z = (Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ) - ((c :: cs).length : ℤ) := ⟨_, rfl⟩
    rw [← hz]
    have hzj : ∀ j, (Fintype.card ι : ℤ) * (B : ℤ) - ∑ i, (((β + Pi.single j 1 : ι → ℕ) i : ℕ) : ℤ) - (cs.length : ℤ) = z := by
      intro j
      rw [sum_add_single, hz, List.length_cons]
      push_cast
      ring
    have hterm : ∀ j, 0 ≤ ((R : ℝ) + β j) * a j c * C j := fun j =>
      mul_nonneg (mul_nonneg (by positivity) (ha j c).le) (hC0 j)
    refine ⟨(∑ j, ((R : ℝ) + β j) * a j c * C j) * 2 ^ z.natAbs,
      mul_nonneg (Finset.sum_nonneg fun j _ => hterm j) (by positivity), fun s hs hB x hx => ?_⟩
    have hE1 : 1 ≤ sizeE x := one_le_sizeE hx
    have hE0 : 0 < sizeE x := by linarith
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := fun t : ℝ => DLR cs (Fr a b s β) (x + t • (Pi.single c 1 : Fin r → ℝ)))
      (f' := fun τ => ∑ j, (-s - (β j : ℂ)) * (a j c : ℂ) *
        DLR cs (Fr a b s (β + Pi.single j 1)) (x + τ • (Pi.single c 1 : Fin r → ℝ)))
      (C := (∑ j, ((R : ℝ) + β j) * a j c * C j) * 2 ^ z.natAbs * sizeE x ^ z)
      (fun τ hτ => (GlobalTheory.T.cone_series_real_derivative_formula ι r a b ha hb s β cs c x τ hx hτ.1).hasDerivWithinAt)
      (fun τ hτ => ?_)
    · simpa [DLR, fdR] using hmv
    · have hu1 : sizeE x ≤ sizeE (x + τ • (Pi.single c 1 : Fin r → ℝ)) := by
        rw [sizeE_add_smul]; linarith [hτ.1]
      have hu2 : sizeE (x + τ • (Pi.single c 1 : Fin r → ℝ)) ≤ 2 * sizeE x := by
        rw [sizeE_add_smul]; linarith [hτ.2.le]
      have hpow := zpow_le_two_pow_mul hE0 hu1 hu2 z
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      have hD := hC j s hs hB _ (nonneg_add_smul hx c hτ.1)
      rw [hzj j] at hD
      have hs1 : ‖-s - (β j : ℂ)‖ ≤ (R : ℝ) + β j := by
        refine (norm_sub_le _ _).trans ?_
        simpa using hs
      have ha1 : ‖(a j c : ℂ)‖ = a j c := by
        simp [abs_of_pos (ha j c)]
      rw [norm_mul, norm_mul, ha1]
      calc ‖-s - (β j : ℂ)‖ * a j c * ‖DLR cs (Fr a b s (β + Pi.single j 1)) (x + τ • (Pi.single c 1 : Fin r → ℝ))‖
          ≤ ((R : ℝ) + β j) * a j c * (C j * (2 ^ z.natAbs * sizeE x ^ z)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hs1 (ha j c).le) (hD.trans ?_) (norm_nonneg _)
              (mul_nonneg (by positivity) (ha j c).le)
            exact mul_le_mul_of_nonneg_left hpow (hC0 j)
        _ = ((R : ℝ) + β j) * a j c * C j * 2 ^ z.natAbs * sizeE x ^ z := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DiffDecay
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SimplicialConeTiling
section
set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.SignTiles

variable {V : Type} [AddCommGroup V] [Module ℚ V]

theorem tile_mono {P : Set V} {Q Q' : Set V → Prop} (hQ : ∀ A, Q A → Q' A) {C : Set V} (h : Tile P Q C) :
    Tile P Q' C := by
  induction h with
  | empty => exact .empty
  | cone s hli hP hQs => exact .cone s hli hP (hQ _ hQs)
  | union _ _ hAB ihA ihB => exact .union ihA ihB hAB

theorem tile_refine {P : Set V} {Q Q' : Set V → Prop}
    (hc : ∀ s : Finset V, LinearIndepOn ℚ id (s : Set V) → (s : Set V) ⊆ P → Q (coneOn s) → Tile P Q' (coneOn s))
    {C : Set V} (h : Tile P Q C) : Tile P Q' C := by
  induction h with
  | empty => exact .empty
  | cone s hli hP hQs => exact hc s hli hP hQs
  | union _ _ hAB ihA ihB => exact .union ihA ihB hAB

theorem tile_inside {P : Set V} {Q : Set V → Prop} {C : Set V} (h : Tile P Q C) :
    Tile P (fun A => Q A ∧ A ⊆ C) C := by
  induction h with
  | empty => exact .empty
  | cone s hli hP hQs => exact .cone s hli hP ⟨hQs, subset_rfl⟩
  | @union A B _ _ hAB ihA ihB =>
    exact .union (tile_mono (fun X hX => ⟨hX.1, hX.2.trans Set.subset_union_left⟩) ihA)
      (tile_mono (fun X hX => ⟨hX.1, hX.2.trans Set.subset_union_right⟩) ihB) hAB

theorem signConst_mono {l : V →ₗ[ℚ] ℚ} {A C : Set V} (h : SignConst l C) (hAC : A ⊆ C) : SignConst l A := by
  rcases h with h | h | h
  · exact Or.inl fun x hx => h x (hAC hx)
  · exact Or.inr (Or.inl fun x hx => h x (hAC hx))
  · exact Or.inr (Or.inr fun x hx => h x (hAC hx))

theorem sign_eq_of_signConst {l : V →ₗ[ℚ] ℚ} {A : Set V} (h : SignConst l A) {x y : V} (hx : x ∈ A) (hy : y ∈ A) :
    SignType.sign (l x) = SignType.sign (l y) := by
  rcases h with h | h | h
  · rw [h x hx, h y hy]
  · rw [sign_pos (h x hx), sign_pos (h y hy)]
  · rw [sign_neg (h x hx), sign_neg (h y hy)]

theorem tile_signs (P : ConvexCone ℚ V) (s : Finset V) (hli : LinearIndepOn ℚ id (s : Set V))
    (hP : (s : Set V) ⊆ (P : Set V)) (Λ : Set (V →ₗ[ℚ] ℚ)) (hΛ : Λ.Finite) :
    Tile (P : Set V) (fun A => A ⊆ coneOn s ∧ ∀ l ∈ Λ, SignConst l A) (coneOn s) := by
  classical
  obtain ⟨t, rfl⟩ := hΛ.exists_finset_coe
  refine Finset.induction_on t ?_ ?_
  · exact .cone s hli hP ⟨subset_rfl, fun l hl => by simp at hl⟩
  · intro l t _ ih
    refine tile_refine (fun u hu huP hQu => ?_) ih
    refine tile_mono (fun A hA => ⟨hA.2.trans hQu.1, fun l' hl' => ?_⟩)
      (tile_inside (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.TileSign.main P l u hu huP))
    rcases Finset.mem_insert.1 (Finset.mem_coe.1 hl') with rfl | h'
    · exact hA.1
    · exact signConst_mono (hQu.2 l' (Finset.mem_coe.2 h')) hA.2

theorem tile_inter {P E C : Set V} (h : Tile P (fun A => A ⊆ E ∨ Disjoint A E) C) :
    Tile P (fun _ => True) (C ∩ E) := by
  induction h with
  | empty =>
    rw [Set.empty_inter]
    exact .empty
  | cone s hli hP hQs =>
    rcases hQs with hs | hs
    · rw [Set.inter_eq_left.2 hs]
      exact .cone s hli hP trivial
    · rw [Set.disjoint_iff_inter_eq_empty.1 hs]
      exact .empty
  | union _ _ hAB ihA ihB =>
    rw [Set.union_inter_distrib_right]
    exact .union ihA ihB (hAB.mono Set.inter_subset_left Set.inter_subset_left)

theorem mem_coneOn_basis [DecidableEq V] {κ : Type} [Fintype κ] (b : Module.Basis κ ℚ V) (x : V) :
    x ∈ coneOn (Finset.univ.image b) ↔ ∀ i, 0 < b.repr x i := by
  classical
  constructor
  · rintro ⟨t, ht, rfl⟩ i
    rw [Finset.sum_image (fun a _ c _ hac => b.injective hac)]
    have hrep : b.repr (∑ j, t (b j) • b j) i = t (b i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
        Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_single i]
      · rw [Finsupp.single_apply, if_pos rfl]
      · intro j _ hji
        rw [Finsupp.single_apply, if_neg hji]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [hrep]
    exact ht _ (Finset.mem_image_of_mem b (Finset.mem_univ i))
  · intro hx
    have key : ∀ i, ∑ j, b.repr (b i) j * b.repr x j = b.repr x i := by
      intro i
      rw [Module.Basis.repr_self, Finset.sum_eq_single i]
      · rw [Finsupp.single_apply, if_pos rfl, one_mul]
      · intro j _ hji
        rw [Finsupp.single_apply, if_neg (Ne.symm hji), zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    refine ⟨fun v => ∑ j, b.repr v j * b.repr x j, ?_, ?_⟩
    · intro v hv
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      show 0 < ∑ j, b.repr (b i) j * b.repr x j
      rw [key]
      exact hx i
    · rw [Finset.sum_image (fun a _ c _ hac => b.injective hac)]
      conv_lhs => rw [← b.sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      show b.repr x i • b i = (∑ j, b.repr (b i) j * b.repr x j) • b i
      rw [key]

theorem tile_of_signs : ∀ {V : Type} [AddCommGroup V] [Module ℚ V] {κ : Type} [Fintype κ] (P : ConvexCone ℚ V)
    (b : Module.Basis κ ℚ V), (∀ i, b i ∈ P) → ∀ (Λ : Set (V →ₗ[ℚ] ℚ)), Λ.Finite → ∀ (E : Set V),
    (∀ x ∈ E, ∀ i, 0 < b.repr x i) →
    (∀ x y, (∀ i, 0 < b.repr x i) → (∀ i, 0 < b.repr y i) →
      (∀ l ∈ Λ, SignType.sign (l x) = SignType.sign (l y)) → x ∈ E → y ∈ E) →
    Tile (P : Set V) (fun _ => True) E := by
  classical
  intro V _ _ κ _ P b hb Λ hΛ E hE hdec
  have hcoe : ((Finset.univ.image b : Finset V) : Set V) = Set.range b := by
    simp [Set.image_univ]
  have hli : LinearIndepOn ℚ id ((Finset.univ.image b : Finset V) : Set V) := by
    rw [hcoe]
    exact (linearIndepOn_id_range_iff b.injective).2 b.linearIndependent
  have hP' : ((Finset.univ.image b : Finset V) : Set V) ⊆ (P : Set V) := by
    rw [hcoe]
    rintro v ⟨i, rfl⟩
    exact hb i
  have hT := tile_inter (tile_mono (Q' := fun A => A ⊆ E ∨ Disjoint A E) (fun A hA => ?_)
    (tile_signs P _ hli hP' Λ hΛ))
  · have hEs : coneOn (Finset.univ.image b) ∩ E = E :=
      Set.inter_eq_right.2 fun x hx => (mem_coneOn_basis b x).2 (hE x hx)
    rw [hEs] at hT
    exact hT
  · obtain ⟨hAs, hAl⟩ := hA
    by_cases hex : ∃ x ∈ A, x ∈ E
    · left
      obtain ⟨x, hxA, hxE⟩ := hex
      intro y hyA
      exact hdec x y ((mem_coneOn_basis b x).1 (hAs hxA)) ((mem_coneOn_basis b y).1 (hAs hyA))
        (fun l hl => sign_eq_of_signConst (hAl l hl) hxA hyA) hxE
    · right
      exact Set.disjoint_left.2 fun x hxA hxE => hex ⟨x, hxA, hxE⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.SignTiles
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.TendstoTailInfiniteProductOne
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem expansion_on_finset (r l N : ℕ) (w : (Fin r → ℕ) → ℚ) (hl : 0 < l) (hw : GoodWeight l w)
    (I : Finset (Fin r)) :
    ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ),
      (∀ q, BddW (u q)) ∧ (∀ q i, i ∉ I → GoodAt l i (u q) ∧ (cs q).count i = 0) ∧
      (∀ q i, i ∈ I → (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧
      ∀ g : (Fin r → ℕ) → ℂ, Summable g →
        ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨Unit, inferInstance, fun _ => [], fun _ => w,
      fun _ => GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic r l w hl (fun i m => hw.1 m i),
      fun _ i _ => ⟨⟨fun m => hw.1 m i, fun m => hw.2 m i⟩, by simp⟩,
      fun _ i hi => absurd hi (by simp), fun g _ => by simp [DL]⟩
  | insert a I ha ih =>
    obtain ⟨Q, _, cs, u, hb, hg, hs, hid⟩ := ih
    choose u' h1 h2 h3 h4 h5 using
      fun q => GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OneVar.abel_oneVar r l N a (u q) hl (hg q a ha).1 (hb q)
    refine ⟨Q × Fin (N + 1), inferInstance, fun p => List.replicate (p.2 : ℕ) a ++ cs p.1,
      fun p => u' p.1 p.2, fun p => h1 p.1 p.2, ?_, ?_, ?_⟩
    · rintro ⟨q, c⟩ k hk
      have hka : k ≠ a := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkI : k ∉ I := fun h => hk (Finset.mem_insert_of_mem h)
      refine ⟨h3 q c k hka (hg q k hkI).1, ?_⟩
      simp [List.count_append, List.count_replicate, (hg q k hkI).2, hka.symm]
    · rintro ⟨q, c⟩ k hk
      by_cases hka : k = a
      · subst hka
        have h0 : (cs q).count k = 0 := (hg q k ha).2
        rcases h2 q c with h | h
        · left
          simp [List.count_append, h0, h]
        · exact Or.inr h
      · have hkI : k ∈ I := (Finset.mem_insert.1 hk).resolve_left hka
        have hak : a ≠ k := fun h => hka h.symm
        rcases hs q k hkI with h | h
        · left
          simp [List.count_append, List.count_replicate, hak, h]
        · exact Or.inr (h4 q c k hka h)
    · intro g hgs
      rw [hid g hgs, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [h5 q _ (GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_DL r (cs q) g hgs)]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [DL, List.foldr_append]

theorem expansion_all_variables : ∀ (r l N : ℕ) (w : (Fin r → ℕ) → ℚ), 0 < l → GoodWeight l w →
    ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ),
      (∀ q, BddW (u q)) ∧ (∀ q i, (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧
      ∀ g : (Fin r → ℕ) → ℂ, Summable g →
        ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  intro r l N w hl hw
  obtain ⟨Q, iQ, cs, u, hb, -, hs, hid⟩ := expansion_on_finset r l N w hl hw Finset.univ
  exact ⟨Q, iQ, cs, u, hb, fun q i => hs q i (Finset.mem_univ i), hid⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

