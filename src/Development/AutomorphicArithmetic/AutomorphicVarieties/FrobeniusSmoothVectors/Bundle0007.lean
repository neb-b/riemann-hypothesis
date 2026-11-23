module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FramePointFiberNonempty
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.framePoint_fiber_nonempty :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (Q : Type) [CommRing Q] [Algebra k Q] (ρ : NRep F 2 Q), ρ.IsBar (algebraMap k Q) → ρ.triM = ⊥ → (∀ i j, IsLocallyConstant fun g => ρ.r g i j) → (fun g => ρ.r g 1 0) ∈ F.strS Q := by
  intro l _ k _ _ F C₀ hF Q _ _ ρ hbar htri hlc
  have hd0 : ∀ g : F.G0, ρ.r g 0 0 = algebraMap k Q ((F.Ψ (g : F.Γ) : k)) := by
    intro g
    have h := hbar.1 g 0
    simpa [w] using h
  have hd1 : ∀ g : F.G0, ρ.r g 1 1 = algebraMap k Q ((F.Ψ (g : F.Γ) : k))⁻¹ := by
    intro g
    have h := hbar.1 g 1
    simpa [w] using h
  have hup : ∀ g : F.G0, ρ.r g 0 1 = 0 := by
    intro g
    have h : ρ.r g 0 1 ∈ ρ.triM := by
      apply Ideal.subset_span (s := {x | ∃ g i j, i < j ∧ x = ρ.r g i j})
      exact ⟨g, 0, 1, by decide, rfl⟩
    rw [htri, Ideal.mem_bot] at h
    exact h
  have hψ0 : ∀ v (s : F.Gv v), ((ρ.ψ v 0 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k)) := by
    intro v s
    have h := hbar.2 v 0 s
    simpa [w] using h
  have hψ1 : ∀ v (s : F.Gv v), ((ρ.ψ v 1 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k))⁻¹ := by
    intro v s
    have h := hbar.2 v 1 s
    simpa [w] using h
  refine ⟨hlc 1 0, ?_, ?_, ?_⟩
  · intro g h
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def, Units.val_inv_eq_inv_val]
    rw [hd0, hd1]
    ring
  · intro g
    show ρ.r (F.star g) 1 0 = ρ.r g 1 0
    rw [(UpperTheory.V.Fr.star hF).2.2.2.2 ρ g 1 0]
    rfl
  · intro v
    obtain ⟨t, ht⟩ := hF.f3 v
    set d : k := ((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹ with hdd
    have hne := Units.ne_zero (F.Ψ (F.loc v t))
    have hd : d ≠ 0 := by
      intro h
      apply ht
      rw [hdd, sub_eq_zero] at h
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, pow_two]
      calc ((F.Ψ (F.loc v t) : k)) * (F.Ψ (F.loc v t) : k)
          = (F.Ψ (F.loc v t) : k) * ((F.Ψ (F.loc v t) : k))⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hne
    refine ⟨algebraMap k Q d⁻¹ * ρ.r (F.loc0 v t) 1 0, fun s => ?_⟩
    have h10 := congrFun (congrFun (ρ.ord v ![s, t]) 1) 0
    simp only [ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ_zero_eq_one, (by decide : (1 : Fin 2) ≠ 0), if_false, if_true, smul_zero,
      sub_zero, smul_eq_mul, mul_one] at h10
    have hl : ∀ s, ((F.loc0 v s : F.G0) : F.Γ) = F.loc v s := fun _ => rfl
    rw [hd0, hd1, hψ0, hψ1, hl, hl] at h10
    simp only [mul_zero, sub_zero] at h10
    have hinv : (algebraMap k Q ((F.Ψ (F.loc v t) : k)) - algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹)
        * algebraMap k Q d⁻¹ = 1 := by
      rw [← map_sub, ← map_mul, ← hdd, mul_inv_cancel₀ hd, map_one]
    simp only [Algebra.smul_def, Units.val_inv_eq_inv_val, map_sub]
    linear_combination algebraMap k Q d⁻¹ * h10 - ρ.r (F.loc0 v s) 1 0 * hinv
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FramePointYCoordEq
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.framePoint_y_coord_eq :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (Q : Type) [CommRing Q] [Algebra k Q] (ρ : NRep F 3 Q), ρ.IsBar (algebraMap k Q) → ρ.triM = ⊥ → (∀ i j, IsLocallyConstant fun g => ρ.r g i j) → (fun g => ρ.r g 1 0) ∈ F.strY Q := by
  intro l _ k _ _ F C₀ hF Q _ _ ρ hbar htri hlc
  have hd0 : ∀ g : F.G0, ρ.r g 0 0 = algebraMap k Q ((F.Ψ (g : F.Γ) : k)) := by
    intro g
    have h := hbar.1 g 0
    simpa [w] using h
  have hd1 : ∀ g : F.G0, ρ.r g 1 1 = 1 := by
    intro g
    have h := hbar.1 g 1
    simpa [w] using h
  have hd2 : ∀ g : F.G0, ρ.r g 2 2 = algebraMap k Q ((F.Ψ (g : F.Γ) : k))⁻¹ := by
    intro g
    have h := hbar.1 g 2
    simpa [w] using h
  have hup : ∀ (g : F.G0) (i j : Fin 3), i < j → ρ.r g i j = 0 := by
    intro g i j hij
    have h : ρ.r g i j ∈ ρ.triM := by
      apply Ideal.subset_span
      exact ⟨g, i, j, hij, rfl⟩
    rw [htri, Ideal.mem_bot] at h
    exact h
  have h01 := fun g => hup g 0 1 (by decide)
  have h02 := fun g => hup g 0 2 (by decide)
  have h12 := fun g => hup g 1 2 (by decide)
  have hψ0 : ∀ v (s : F.Gv v), ((ρ.ψ v 0 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k)) := by
    intro v s
    have h := hbar.2 v 0 s
    simpa [w] using h
  have hψ1 : ∀ v (s : F.Gv v), ((ρ.ψ v 1 s : Qˣ) : Q) = 1 := by
    intro v s
    have h := hbar.2 v 1 s
    simpa [w] using h
  have hψ2 : ∀ v (s : F.Gv v), ((ρ.ψ v 2 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k))⁻¹ := by
    intro v s
    have h := hbar.2 v 2 s
    simpa [w] using h
  refine ⟨hlc 1 0, ?_, ?_, ?_, ?_⟩
  · intro g h
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_three, Algebra.smul_def]
    rw [hd0, hd1, h12]
    ring
  · have h := ρ.diag 1 0 (by decide)
    rw [Matrix.sub_apply, sub_eq_zero] at h
    exact h
  · intro v
    obtain ⟨t, ht⟩ := hF.f3 v
    have hne := Units.ne_zero (F.Ψ (F.loc v t))
    have hsq : ((F.Ψ (F.loc v t) : k)) * (F.Ψ (F.loc v t) : k) ≠ 1 := by
      intro h
      apply ht
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, pow_two, h]
    have hf : ((F.Ψ (F.loc v t) : k)) - 1 ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      apply hsq
      rw [h, one_mul]
    have he : ((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹ ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      apply hsq
      calc ((F.Ψ (F.loc v t) : k)) * (F.Ψ (F.loc v t) : k)
          = (F.Ψ (F.loc v t) : k) * ((F.Ψ (F.loc v t) : k))⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hne
    have hl : ∀ s, ((F.loc0 v s : F.G0) : F.Γ) = F.loc v s := fun _ => rfl
    refine ⟨algebraMap k Q (((F.Ψ (F.loc v t) : k)) - 1)⁻¹ * ρ.r (F.loc0 v t) 1 0, fun s => ?_⟩
    have h10 := congrFun (congrFun (ρ.ord v ![t, s, t]) 1) 0
    simp [ordProd, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd0, hd1, hd2, h01, h02, h12,
      hψ0, hψ1, hψ2, hl] at h10
    simp only [Algebra.smul_def, mul_one] at h10
    have hE : (algebraMap k Q ((F.Ψ (F.loc v t) : k)) - algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹) * algebraMap k Q (((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ = 1 := by
      rw [← map_sub, ← map_mul, mul_inv_cancel₀ he, map_one]
    have hF : (algebraMap k Q ((F.Ψ (F.loc v t) : k)) - 1) * algebraMap k Q (((F.Ψ (F.loc v t) : k)) - 1)⁻¹ = 1 := by
      rw [← map_one (algebraMap k Q), ← map_sub, ← map_mul, mul_inv_cancel₀ hf, map_one]
    simp only [Algebra.smul_def, map_sub, map_one]
    linear_combination (-(algebraMap k Q (((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ * algebraMap k Q (((F.Ψ (F.loc v t) : k)) - 1)⁻¹)) * h10
      + ((algebraMap k Q ((F.Ψ (F.loc v s) : k)) - 1) * algebraMap k Q (((F.Ψ (F.loc v t) : k)) - 1)⁻¹ * ρ.r (F.loc0 v t) 1 0 - ρ.r (F.loc0 v s) 1 0) * hE
      - algebraMap k Q (((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ * (algebraMap k Q ((F.Ψ (F.loc v t) : k)) - algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹) * ρ.r (F.loc0 v s) 1 0 * hF
  · intro v
    obtain ⟨t, ht⟩ := hF.f3 v
    have hne := Units.ne_zero (F.Ψ (F.loc v t))
    have hsq : ((F.Ψ (F.loc v t) : k)) * (F.Ψ (F.loc v t) : k) ≠ 1 := by
      intro h
      apply ht
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, pow_two, h]
    have hf : ((F.Ψ (F.loc v t) : k)) - 1 ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      apply hsq
      rw [h, one_mul]
    have he : ((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹ ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      apply hsq
      calc ((F.Ψ (F.loc v t) : k)) * (F.Ψ (F.loc v t) : k)
          = (F.Ψ (F.loc v t) : k) * ((F.Ψ (F.loc v t) : k))⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hne
    have hl : ∀ s, ((F.loc0 v s : F.G0) : F.Γ) = F.loc v s := fun _ => rfl
    have hg : 1 - ((F.Ψ (F.loc v t) : k))⁻¹ ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      exact hf (by rw [← inv_eq_one.mp h.symm, sub_self])
    refine ⟨algebraMap k Q (1 - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ * ρ.r (F.loc0 v t) 2 1, fun s => ?_⟩
    have h21 := congrFun (congrFun (ρ.ord v ![t, s, t]) 2) 1
    simp [ordProd, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd0, hd1, hd2, h01, h02, h12,
      hψ0, hψ1, hψ2, hl] at h21
    simp only [Algebra.smul_def, mul_one] at h21
    have hD : (algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹ - algebraMap k Q ((F.Ψ (F.loc v t) : k))) * algebraMap k Q (((F.Ψ (F.loc v t) : k))⁻¹ - ((F.Ψ (F.loc v t) : k)))⁻¹ = 1 := by
      rw [← map_sub, ← map_mul, mul_inv_cancel₀ (by rw [← neg_sub]; exact neg_ne_zero.mpr he), map_one]
    have hG : (1 - algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹) * algebraMap k Q (1 - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ = 1 := by
      rw [← map_one (algebraMap k Q), ← map_sub, ← map_mul, mul_inv_cancel₀ hg, map_one]
    show ρ.r (F.star (F.loc0 v s)) 1 0 = _
    rw [(UpperTheory.V.Fr.star hF).2.2.2.2 ρ _ 1 0]
    change ρ.r (F.loc0 v s) 2 1 = _
    simp only [Algebra.smul_def, map_sub, map_one, Units.val_inv_eq_inv_val]
    linear_combination (algebraMap k Q (((F.Ψ (F.loc v t) : k))⁻¹ - ((F.Ψ (F.loc v t) : k)))⁻¹ * algebraMap k Q (1 - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹) * h21
      + ((1 - algebraMap k Q ((F.Ψ (F.loc v s) : k))⁻¹) * algebraMap k Q (1 - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ * ρ.r (F.loc0 v t) 2 1 - ρ.r (F.loc0 v s) 2 1) * hD
      - algebraMap k Q (((F.Ψ (F.loc v t) : k))⁻¹ - ((F.Ψ (F.loc v t) : k)))⁻¹ * (algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹ - algebraMap k Q ((F.Ψ (F.loc v t) : k))) * ρ.r (F.loc0 v s) 2 1 * hG
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusCornerConeMap
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem max_map {O : Type} [CommRing O] [IsLocalRing O] {C : Type} [CommRing C] [Algebra O C] [IsCO O C]
    {C' : Type} [CommRing C'] [Algebra O C'] [IsCO O C'] (φ : C →ₐ[O] C') {c : C} (hc : c ∈ maximalIdeal C) :
    φ c ∈ maximalIdeal C' := by
  rwa [← res_eq_zero_iff O, UpperTheory.V.Alg.res_map φ, res_eq_zero_iff]

private theorem pow_map {O : Type} [CommRing O] [IsLocalRing O] {C : Type} [CommRing C] [Algebra O C] [IsCO O C]
    {C' : Type} [CommRing C'] [Algebra O C'] [IsCO O C'] (φ : C →ₐ[O] C') (N : ℕ) {c : C}
    (hc : c ∈ maximalIdeal C ^ N) : φ c ∈ maximalIdeal C' ^ N := by
  have h : (maximalIdeal C).map φ ≤ maximalIdeal C' := Ideal.map_le_iff_le_comap.2 fun _ h => max_map φ h
  have h2 := Ideal.mem_map_of_mem φ hc
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h N h2

private theorem span_map {C C' K K' : Type} [CommRing C] [CommRing C'] [CommRing K] [CommRing K'] [Algebra C K]
    [Algebra C' K'] (φ : C → C') (f : K →+* K') (h : ∀ c, f (algebraMap C K c) = algebraMap C' K' (φ c))
    {s : Set K} {M : Submodule C' K'} (hs : ∀ x ∈ s, f x ∈ M) {x : K} (hx : x ∈ Submodule.span C s) : f x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add f]; exact add_mem hx hy
  | smul a x _ hx => rw [Algebra.smul_def, map_mul, h, ← Algebra.smul_def]; exact M.smul_mem _ hx

private theorem lc_of {X A B : Type} [TopologicalSpace X] {u : X → A} {v : X → B} (hu : IsLocallyConstant u)
    (h : ∀ x y, u x = u y → v x = v y) : IsLocallyConstant v := by
  rw [IsLocallyConstant.iff_eventually_eq] at hu ⊢
  exact fun x => (hu x).mono fun y hy => h _ _ hy

theorem UpperTheory.V.Fr.frobenius_corner_cone_map :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [CommRing K] [Algebra C K] (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (K' : Type) [CommRing K'] [Algebra C' K'] (β : C →ₐ[O] C') (f : K →+* K'), (∀ c, f (algebraMap C K c) = algebraMap C' K' (β c)) → ∀ ρ : NRep F n K, Cone O C ρ → Cone O C' (ρ.map f) := by
  intro l _ O _ _ F n C _ _ _ K _ _ C' _ _ _ K' _ _ φ f h ρ H
  have hsp : ∀ i j, ∀ x ∈ Submodule.span C (Set.range fun g => ρ.r g i j),
      f x ∈ Submodule.span C' (Set.range fun g => (ρ.map f).r g i j) := fun i j x hx =>
    span_map φ f h (by rintro _ ⟨g, rfl⟩; exact Submodule.subset_span ⟨g, rfl⟩) hx
  refine ⟨fun g i => ?_, fun L hL hs => ?_, fun i j => ?_, fun i j N => ?_, ?_⟩
  · obtain ⟨c, h1, h2⟩ := H.dg g i
    exact ⟨φ c, by rw [← h, h1, NRep.map_r], by rw [UpperTheory.V.Alg.res_map, h2]⟩
  · obtain ⟨c, h1, h2⟩ := H.cyc L hL hs
    refine ⟨φ c, max_map φ h1, ?_⟩
    rw [← h, h2, map_list_prod, List.map_map]
    rfl
  · classical
    obtain ⟨t, ht⟩ := H.fg i j
    refine ⟨t.image f, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact hsp i j x (ht ▸ Submodule.subset_span hx)
    · rintro _ ⟨g, rfl⟩
      refine span_map φ f h (s := (t : Set K)) (fun x hx => Submodule.subset_span ?_) (x := ρ.r g i j) ?_
      · exact Finset.mem_coe.2 (Finset.mem_image_of_mem f hx)
      · rw [ht]; exact Submodule.subset_span ⟨g, rfl⟩
  · refine lc_of (H.cont i j N) fun x y hxy => ?_
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hxy ⊢
    rw [NRep.map_r, NRep.map_r, ← map_sub]
    refine Submodule.smul_induction_on hxy (fun a ha z hz => ?_) (fun a b ha hb => ?_)
    · rw [Algebra.smul_def a z, map_mul, h, ← Algebra.smul_def (φ a) (f z)]
      exact Submodule.smul_mem_smul (pow_map φ N ha) (hsp i j z hz)
    · rw [map_add f]; exact add_mem ha hb
  · obtain ⟨χ, h1, h2⟩ := H.psi
    refine ⟨fun v i g => φ (χ v i g), fun v i => ⟨fun N => ?_, fun g => ?_⟩, fun v i g => ?_⟩
    · refine lc_of ((h1 v i).1 N) fun x y hxy => ?_
      rw [Ideal.Quotient.eq] at hxy ⊢
      rw [← map_sub]
      exact pow_map φ N hxy
    · rw [UpperTheory.V.Alg.res_map, (h1 v i).2]
    · rw [← h, h2, NRep.map_ψ]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusCornerMiddleTrivial
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem exists_prime_power_pow_eq_one {l : ℕ} [Fact l.Prime] {D : Type} [CommRing D] [IsDomain D] [IsLocalRing D]
    [CharP D l] {x : D} (hx : x - 1 ∈ maximalIdeal D) {h : ℕ} (hh : h ≠ 0) (hp : x ^ h = 1) : x = 1 := by
  have hl : l.Prime := Fact.out
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hh l hl.ne_one
  have h1 : (x ^ m - 1) ^ l ^ a = 0 := by
    rw [sub_pow_char_pow, one_pow, ← pow_mul, mul_comm, hp, sub_self]
  have h2 : x ^ m - 1 = 0 := (pow_eq_zero_iff (pow_ne_zero _ hl.ne_zero)).1 h1
  rw [← mul_geom_sum, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact sub_eq_zero.1 h2
  · exfalso
    have h3 : residue D x = 1 := by
      have := (residue_eq_zero_iff _).2 hx
      rwa [map_sub, map_one, sub_eq_zero] at this
    have h4 := congrArg (residue D) h2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_pow, h3, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      map_zero] at h4
    have h5 : (l : ResidueField D) = 0 := by
      rw [← map_natCast (residue D), CharP.cast_eq_zero, map_zero]
    haveI : CharP (ResidueField D) l := (CharP.charP_iff_prime_eq_zero hl).2 h5
    exact hm ((CharP.cast_eq_zero_iff _ l m).1 h4)

theorem UpperTheory.V.Fr.frobenius_corner_middle_trivial :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra O D] [IsCO O D], (∀ c ∈ maximalIdeal O, algebraMap O D c = 0) → ∀ χ : F.G0 →* D, AdicCont (maximalIdeal D) χ → (∀ g, χ g - 1 ∈ maximalIdeal D) → (∀ g, χ (F.star g) = χ g) → (∀ v g, g ∈ F.Iv v → F.Ψ (F.loc v g) = 1 → χ (F.loc0 v g) = 1) → ∀ g, χ g = 1 := by
  intro l _ O _ _ _ _ F C₀ hF D _ _ _ _ hO χ hc h1 hs hI g
  have hl : l.Prime := Fact.out
  have hlO : (l : O) ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
  haveI : CharP D l := (CharP.charP_iff_prime_eq_zero hl).2 (by
    rw [← map_natCast (algebraMap O D), hO _ hlO])
  haveI : CompactSpace F.G0 :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ hF.del_open).isCompact
  obtain ⟨s, s', h, hh, -, hs', H⟩ := UpperTheory.V.Fr.ab_gen hF
  refine exists_prime_power_pow_eq_one (h1 g) hh ?_
  have key : ∀ N : ℕ, χ g ^ h - 1 ∈ maximalIdeal D ^ N := by
    intro N
    let q := Ideal.Quotient.mk (maximalIdeal D ^ N)
    let φ : F.G0 →* (D ⧸ maximalIdeal D ^ N)ˣ := ((q : D →* _).comp χ).toHomUnits
    have hφ : ∀ x, (φ x : D ⧸ maximalIdeal D ^ N) = q (χ x) := fun _ => rfl
    have hone : ∀ x n, φ.rangeRestrict x ^ n = 1 ↔ χ x ^ n - 1 ∈ maximalIdeal D ^ N := by
      intro x n
      rw [← Ideal.Quotient.eq, Subtype.ext_iff, Units.ext_iff, map_pow, map_one]
      rfl
    haveI : Finite φ.range := by
      haveI hf : Finite (Set.range fun g => q (χ g)) := (hc N).range_finite
      refine Finite.of_injective (β := Set.range fun g => q (χ g))
        (fun y => ⟨(y.1 : D ⧸ maximalIdeal D ^ N), ?_⟩) ?_
      · obtain ⟨_, x, rfl⟩ := y
        exact ⟨x, rfl⟩
      · intro y z hyz
        exact Subtype.ext (Units.ext (congrArg Subtype.val hyz))
    have hP : IsPGroup l φ.range := by
      intro y
      obtain ⟨x, rfl⟩ := φ.rangeRestrict_surjective y
      refine ⟨N, (hone x _).2 ?_⟩
      have e : χ x ^ l ^ N - 1 = (χ x - 1) ^ l ^ N := by rw [sub_pow_char_pow, one_pow]
      rw [e]
      exact Ideal.pow_le_pow_right (Nat.lt_pow_self hl.one_lt).le (Ideal.pow_mem_pow (h1 x) _)
    have hop : IsOpen (φ.rangeRestrict.ker : Set F.G0) := by
      convert (hc N).isOpen_fiber 1 using 1
      ext x
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq]
      rw [Subtype.ext_iff, Units.ext_iff]
      rfl
    refine (hone g h).1 ((H φ.range hP φ.rangeRestrict hop).2 (fun x => ?_) (fun a => ?_) g)
    · refine Subtype.ext (Units.ext ?_)
      show q (χ _) = q (χ _)
      rw [hs]
    · obtain ⟨v, x, hx, hΨ, e⟩ := hs' a
      refine Subtype.ext (Units.ext ?_)
      show q (χ _) = 1
      rw [e, hI v x hx hΨ, map_one]
  rw [← sub_eq_zero]
  have hb := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal D) (maximalIdeal.isMaximal D).ne_top
  rw [← Ideal.mem_bot, ← hb]
  exact Ideal.mem_iInf.2 key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusCornerMonomial
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem idx_cases (a b : Fin 3) :
    Odd (w 3 a - w 3 b) ∨ (a = 1 ∧ b = 1) ∨ ∃ i j, a = cor i ∧ b = cor j := by
  revert a b
  decide

theorem UpperTheory.V.Fr.frobenius_corner_monomial :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [CommRing K] (ρ : NRep F 3 K) (σ : NRep F 2 K), IsCorner ρ σ → ∀ (j : ℤ), ∀ x ∈ ρ.mon j, x = 0 ∨ ∃ T : List F.G0, ∃ y ∈ σ.mon j, x = (T.map fun g => ρ.r g 1 1).prod * y := by
  intro l _ k _ F K _ ρ σ hc j x hx
  obtain ⟨L, hL, rfl⟩ := hx
  induction L generalizing j with
  | nil =>
    right
    refine ⟨[], 1, ⟨[], ?_, ?_⟩, ?_⟩
    · simpa using hL
    · simp
    · simp
  | cons s L ih =>
    obtain ⟨g, a, b⟩ := s
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hL ⊢
    rcases ih _ rfl with h | ⟨T, y, ⟨M, hM, hy⟩, he⟩
    · left
      rw [h, mul_zero]
    · rcases idx_cases a b with hab | ⟨rfl, rfl⟩ | ⟨i, i', rfl, rfl⟩
      · left
        rw [hc.odd g a b hab, zero_mul]
      · right
        refine ⟨g :: T, y, ⟨M, ?_, hy⟩, ?_⟩
        · rw [hM, ← hL]
          simp
        · rw [he]
          simp only [List.map_cons, List.prod_cons]
          ring
      · right
        refine ⟨T, σ.r g i i' * y, ⟨(g, i, i') :: M, ?_, ?_⟩, ?_⟩
        · simp only [List.map_cons, List.sum_cons]
          rw [hM, ← hL, w_cor, w_cor]
        · simp only [List.map_cons, List.prod_cons]
          rw [hy]
        · rw [he, hc.r]
          ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusCornerUnits
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.frobenius_corner_units :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [CommRing K] [Algebra C K] (ρ : NRep F 3 K), Cone O C ρ → CornerUnits ρ := by
  intro l _ O _ _ _ _ F C₀ hF C _ _ _ K _ _ ρ hC v
  obtain ⟨g, hg⟩ := hF.f3 v
  obtain ⟨χ, hχ, hχρ⟩ := hC.psi
  have key : ∀ a : C, res O C a ≠ 0 → IsUnit (algebraMap C K a) := by
    intro a ha
    apply IsUnit.map
    by_contra hu
    exact ha ((res_eq_zero_iff O C a).mpr ((IsLocalRing.mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr hu)))
  have w0 : w 3 0 = 1 := by simp [w]
  have w1 : w 3 1 = 0 := by simp [w]
  have w2 : w 3 2 = -1 := by simp [w]
  have hg' : F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ) ^ 2 ≠ 1 := hg
  have hu1 : ((F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ) : (ResidueField O)ˣ) : ResidueField O) ≠ 1 := by
    intro h
    apply hg'
    ext
    rw [Units.val_pow_eq_pow_val, h, one_pow, Units.val_one]
  have hu2 : (((F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ))⁻¹ : (ResidueField O)ˣ) : ResidueField O) ≠ 1 := by
    intro h
    apply hg'
    have h1 : F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ) = 1 := inv_eq_one.mp (Units.ext (by rw [h, Units.val_one]))
    rw [h1, one_pow]
  obtain ⟨c0, hc0, hr0⟩ := hC.dg (F.loc0 v g) 0
  obtain ⟨c1, hc1, hr1⟩ := hC.dg (F.loc0 v g) 1
  obtain ⟨c2, hc2, hr2⟩ := hC.dg (F.loc0 v g) 2
  rw [w0, zpow_one] at hr0
  rw [w1, zpow_zero, Units.val_one] at hr1
  rw [w2, _root_.zpow_neg_one] at hr2
  have x0 : res O C (χ v 0 g) = ((F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ) : (ResidueField O)ˣ) : ResidueField O) := by
    have h := (hχ v 0).2 g
    rw [w0, zpow_one] at h
    exact h
  have x1 : res O C (χ v 1 g) = 1 := by
    have h := (hχ v 1).2 g
    rw [w1, zpow_zero, Units.val_one] at h
    exact h
  have x2 : res O C (χ v 2 g) = (((F.Ψ ((F.loc0 v g : F.del.ker) : F.Γ))⁻¹ : (ResidueField O)ˣ) : ResidueField O) := by
    have h := (hχ v 2).2 g
    rw [w2, _root_.zpow_neg_one] at h
    exact h
  have h02 : ((0 : Fin 3) : Fin 3) ≠ 2 := by decide
  obtain ⟨m, hm, hme⟩ := hC.cyc [(F.loc0 v g, 0, 2), (F.loc0 v g, 2, 0)] (by simp [w])
    ⟨(F.loc0 v g, 0, 2), by simp, h02⟩
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hme
  refine ⟨g, ?_, ?_, ?_⟩
  · have hk := key (c1 - χ v 0 g) ?_
    · rwa [map_sub, hc1, hχρ] at hk
    · rw [map_sub, hr1, x0]
      exact sub_ne_zero.mpr (Ne.symm hu1)
  · have hk := key (c1 - χ v 2 g) ?_
    · rwa [map_sub, hc1, hχρ] at hk
    · rw [map_sub, hr1, x2]
      exact sub_ne_zero.mpr (Ne.symm hu2)
  · have hk := key ((c0 - χ v 1 g) * (c2 - χ v 1 g) - m) ?_
    · rwa [map_sub, map_mul, map_sub, map_sub, hc0, hc2, hχρ, hme] at hk
    · rw [map_sub, map_mul, map_sub, map_sub, hr0, hr2, x1, (res_eq_zero_iff O C m).mpr hm, sub_zero]
      exact mul_ne_zero (sub_ne_zero.mpr hu1) (sub_ne_zero.mpr hu2)
end

