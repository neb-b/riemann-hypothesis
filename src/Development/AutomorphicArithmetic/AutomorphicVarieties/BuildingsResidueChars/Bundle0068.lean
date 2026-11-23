module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InducedAutomorphicForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Mathlib.FieldTheory.Galois.Infinite

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MixInvariantPlaneDecomposition
section
open UpperTheory.V.Sd.S2 UpperTheory.V.AlgebraTools UpperTheory.V.Af
open scoped Matrix

section

variable {k : Type} [Field k]

private noncomputable def pX (α β : kˣ) : (Fin 2 → k) →ₗ[k] (Fin 4 → k) where
  toFun a := ![a 1 / β, a 0 / α, -(a 1 / β), a 0 / α]
  map_add' a b := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c a := by ext i; fin_cases i <;> simp <;> ring

private noncomputable def pY : (Fin 2 → k) →ₗ[k] (Fin 4 → k) where
  toFun b := ![b 1, -b 0, b 1, b 0]
  map_add' a b := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c a := by ext i; fin_cases i <;> simp

private theorem pX_apply (α β : kˣ) (a : Fin 2 → k) : pX α β a = ![a 1 / β, a 0 / α, -(a 1 / β), a 0 / α] := rfl

private theorem pY_apply (b : Fin 2 → k) : pY b = ![b 1, -b 0, b 1, b 0] := rfl

private theorem pX_inj (α β : kˣ) : Function.Injective (pX α β) := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [pX_apply] at h0 h1
  ext i; fin_cases i <;> simp [h0, h1]

private theorem pY_inj : Function.Injective (pY (k := k)) := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 3
  simp [pY_apply] at h0 h1
  ext i; fin_cases i <;> simp [h0, h1]

private theorem mix_pX (h2 : (2 : k) ≠ 0) (α β : kˣ) (A B : Matrix (Fin 2) (Fin 2) k) (a : Fin 2 → k) :
    mix (β / α) A B *ᵥ pX α β a = pX α β (A *ᵥ a) := by
  have hα := α.ne_zero
  have hβ := β.ne_zero
  ext i
  fin_cases i <;>
    simp [mix, pX_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_two] <;> field_simp <;> ring

private theorem mix_pY (h2 : (2 : k) ≠ 0) (γ : kˣ) (A B : Matrix (Fin 2) (Fin 2) k) (a : Fin 2 → k) :
    mix γ A B *ᵥ pY a = pY (B *ᵥ a) := by
  have hγ := γ.ne_zero
  ext i
  fin_cases i <;>
    simp [mix, pY_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_two] <;> field_simp <;> ring

private theorem diag_pX (α β : kˣ) (a : Fin 2 → k) :
    Matrix.diagonal ![(β : k), -(α : k), -(β : k), (α : k)] *ᵥ pX α β a = pY a := by
  have hα := α.ne_zero
  have hβ := β.ne_zero
  ext i
  fin_cases i <;> simp [pX_apply, pY_apply, Matrix.mulVec_diagonal] <;> field_simp

private theorem compl_XY (h2 : (2 : k) ≠ 0) (α β : kˣ) :
    IsCompl (LinearMap.range (pX α β)) (LinearMap.range (pY (k := k))) := by
  have hα := α.ne_zero
  have hβ := β.ne_zero
  constructor
  · rw [Submodule.disjoint_def]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    have h0 := congrFun hb 0
    have h1 := congrFun hb 1
    have h2' := congrFun hb 2
    have h3 := congrFun hb 3
    simp [pX_apply, pY_apply] at h0 h1 h2' h3
    have e1 : b 1 = 0 := mul_left_cancel₀ h2 (by linear_combination h0 + h2')
    have e0 : b 0 = 0 := mul_left_cancel₀ h2 (by linear_combination h3 - h1)
    rw [← hb]
    ext i; fin_cases i <;> simp [pY_apply, e0, e1]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    refine Submodule.mem_sup.2 ⟨_, ⟨![α * (v 1 + v 3) / 2, β * (v 0 - v 2) / 2], rfl⟩, _,
      ⟨![(v 3 - v 1) / 2, (v 0 + v 2) / 2], rfl⟩, ?_⟩
    ext i; fin_cases i <;> simp [pX_apply, pY_apply] <;> field_simp <;> ring

private theorem gl_surj (g : GL (Fin 2) k) (b : Fin 2 → k) : ∃ a, (g : Matrix (Fin 2) (Fin 2) k) *ᵥ a = b :=
  ⟨((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *ᵥ b, by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩

end

theorem UpperTheory.mix_invariant_plane_decomposition :
    UpperTheory.V.Sd.S2.MixIrr := by
  intro k Γ₀ Γ _ _ _ j t α β ρ R hm U hU hirr hne
  have hi := hm.index
  have hcj : ∀ h : Γ₀, ∃ h', j h' = t⁻¹ * j h * t := by
    intro h
    have : t⁻¹ * j h * t ∈ j.range := by
      rw [mul_assoc]
      simp only [Subgroup.mul_mem_iff_of_index_two hi, inv_mem_iff, hm.nmem]
      simp
    exact this
  have hX : ∀ h a, (R (j h) : Matrix (Fin 4) (Fin 4) k) *ᵥ pX α β a = pX α β ((ρ h : Matrix (Fin 2) (Fin 2) k) *ᵥ a) := by
    intro h a
    obtain ⟨h', e⟩ := hcj h
    rw [hm.on h h' e, mix_pX hm.two]
  have hY : ∀ h h', j h' = t⁻¹ * j h * t → ∀ a,
      (R (j h) : Matrix (Fin 4) (Fin 4) k) *ᵥ pY a = pY ((ρ h' : Matrix (Fin 2) (Fin 2) k) *ᵥ a) := by
    intro h h' e a
    rw [hm.on h h' e, mix_pY hm.two]
  obtain ⟨s, hsU, hs⟩ := SetLike.not_le_iff_exists.1 hU
  obtain ⟨h₀, hh₀⟩ : s * t⁻¹ ∈ j.range := by
    simp only [Subgroup.mul_mem_iff_of_index_two hi, inv_mem_iff, hm.nmem, hs]
  obtain ⟨h₀', e₀⟩ := hcj h₀
  have hsX : ∀ a, (R s : Matrix (Fin 4) (Fin 4) k) *ᵥ pX α β a = pY ((ρ h₀' : Matrix (Fin 2) (Fin 2) k) *ᵥ a) := by
    intro a
    have : s = j h₀ * t := by rw [hh₀]; group
    rw [this, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hm.off, diag_pX, hY h₀ h₀' e₀]
  have hmap : (LinearMap.range (pX α β)).map (matRep (R.comp U.subtype) ⟨s, hsU⟩) = LinearMap.range (pY (k := k)) := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨_, (hsX a).symm⟩
    · rintro _ ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := gl_surj (ρ h₀') b
      exact ⟨_, ⟨a, rfl⟩, hsX a⟩
  have key := mackeyTwo (matRep (R.comp U.subtype)) (j.range.subgroupOf U) ⟨s, hsU⟩ (LinearMap.range (pX α β))
    ?_ hs ?_ ?_ ?_ ?_
  · refine ⟨top_ne_bot, fun _ _ _ => trivial, fun W _ hW => key W fun g _ v hv => hW g v hv⟩
  · rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨s, hsU⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mul_mem_iff_of_index_two hi, hs]
    by_cases hb : (b : Γ) ∈ j.range <;> simp [hb]
  · rintro ⟨g, hg⟩ ⟨h, rfl : j h = g⟩ _ ⟨a, rfl⟩
    exact ⟨_, (hX h a).symm⟩
  · intro W hle hW
    rcases hirr.2.2 (W.comap (pX α β)) le_top (by
      rintro ⟨h, hh⟩ a ha
      have := hW ⟨j h, hh⟩ ⟨h, rfl⟩ _ ha
      change (R (j h) : Matrix (Fin 4) (Fin 4) k) *ᵥ pX α β a ∈ W at this
      rw [hX] at this
      exact this) with h0 | h0
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨a, rfl⟩ := hle hw
      have : a ∈ W.comap (pX α β) := hw
      rw [h0, Submodule.mem_bot] at this
      simp [this]
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨a, rfl⟩
      have : a ∈ W.comap (pX α β) := by rw [h0]; trivial
      exact this
  · rw [hmap]; exact compl_XY hm.two α β
  · rw [hmap]
    rintro ⟨e, he⟩
    let f : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k) :=
      (LinearEquiv.ofInjective _ (pX_inj α β)).trans (e.trans (LinearEquiv.ofInjective _ pY_inj).symm)
    have hf : ∀ a, pY (f a) = e ⟨pX α β a, a, rfl⟩ := by
      intro a
      have := congrArg Subtype.val ((LinearEquiv.ofInjective _ (pY_inj (k := k))).apply_symm_apply (e ⟨pX α β a, a, rfl⟩))
      exact this
    let M : GL (Fin 2) k :=
      ⟨LinearMap.toMatrix' (f : (Fin 2 → k) →ₗ[k] (Fin 2 → k)), LinearMap.toMatrix' (f.symm : (Fin 2 → k) →ₗ[k] (Fin 2 → k)),
        by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
    have hM : ∀ a, (M : Matrix (Fin 2) (Fin 2) k) *ᵥ a = f a := by
      intro a
      simp [M, LinearMap.toMatrix'_mulVec]
    refine hne ⟨M, fun h h' hh e' => ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro a
    simp only [Matrix.toLin'_apply, Units.val_mul, ← Matrix.mulVec_mulVec, hM]
    apply pY_inj
    rw [← hY h h' e', hf, hf]
    exact (he ⟨j h, hh⟩ ⟨h, rfl⟩ ⟨pX α β a, a, rfl⟩ ⟨_, _, rfl⟩ (hX h a).symm).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MixSignTwist
section
open Matrix UpperTheory.V.Af

private theorem schur2 {G κ : Type} [Group G] [Field κ] [IsAlgClosed κ] (ρ : G →* GL (Fin 2) κ)
    (h : IsIrr ρ) (N : Matrix (Fin 2) (Fin 2) κ)
    (hN : ∀ g, N * (ρ g : Matrix (Fin 2) (Fin 2) κ) = (ρ g : Matrix (Fin 2) (Fin 2) κ) * N) : ∃ x : κ, N = x • 1 := by
  obtain ⟨x, hx⟩ := Module.End.exists_eigenvalue (Matrix.toLin' N)
  have htop : Module.End.eigenspace (Matrix.toLin' N) x = ⊤ := by
    refine (h.2.2 _ le_top fun g v hv => ?_).resolve_left hx
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hN g, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  refine ⟨x, Matrix.toLin'.injective (LinearMap.ext fun v => ?_)⟩
  have : v ∈ Module.End.eigenspace (Matrix.toLin' N) x := by rw [htop]; trivial
  rw [Module.End.mem_eigenspace_iff.1 this]
  simp

theorem UpperTheory.mix_sign_twist :
    UpperTheory.V.Sd.S2.SignTw := by
  intro k Γ _ _ _ ρ ρ' H' M hirr hM s hs hdet
  set N : GL (Fin 2) k := (ρ s)⁻¹ * (M⁻¹ * ρ' s * M) with hN
  have hcomm : ∀ h ∈ H', N * ρ h = ρ h * N := by
    intro h hh
    have e1 := hM h hh
    have e2 := hM _ (hs h hh)
    simp only [map_mul, map_inv, e1] at e2
    have e3 : ρ' s * (M * ρ h * M⁻¹) = M * (ρ s * ρ h * (ρ s)⁻¹) * M⁻¹ * ρ' s := by
      rw [← e2]; group
    calc N * ρ h = (ρ s)⁻¹ * M⁻¹ * (ρ' s * (M * ρ h * M⁻¹)) * M := by rw [hN]; group
      _ = ρ h * N := by rw [e3, hN]; group
  obtain ⟨x, hx⟩ := schur2 _ hirr (N : Matrix (Fin 2) (Fin 2) k) (fun g => by
    have := congrArg Units.val (hcomm g g.2)
    simpa using this)
  have hd : Matrix.GeneralLinearGroup.det N = 1 := by
    rw [hN]
    simp only [map_mul, map_inv, hdet]
    rw [mul_right_comm, inv_mul_cancel, one_mul, inv_mul_cancel]
  have hx2 : x * x = 1 := by
    have h1 : (N : Matrix (Fin 2) (Fin 2) k).det = 1 := congrArg Units.val hd
    rw [hx] at h1
    simpa [pow_two] using h1
  have hc : ∀ A : GL (Fin 2) k, N * A = A * N := fun A => Units.ext (by simp [hx])
  have hNN : N * N = 1 := Units.ext (by simp [hx, smul_smul, hx2])
  have e : ρ' s = M * (ρ s * N) * M⁻¹ := by rw [hN]; group
  clear_value N
  rw [map_mul, map_mul, e]
  calc M * (ρ s * N) * M⁻¹ * (M * (ρ s * N) * M⁻¹) = M * (ρ s * (N * ρ s) * N) * M⁻¹ := by group
    _ = M * (ρ s * ρ s * (N * N)) * M⁻¹ := by rw [hc]; simp only [mul_assoc]
    _ = _ := by rw [hNN, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MixStableLineLocal
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2
open scoped Matrix

private theorem col_eq {k : Type} [Field k] (g r : GL (Fin 2) k) (a b : kˣ) (h10 : (g * r * g⁻¹ : GL (Fin 2) k) 1 0 = 0)
    (h00 : (g * r * g⁻¹ : GL (Fin 2) k) 0 0 = a) (h11 : (g * r * g⁻¹ : GL (Fin 2) k) 1 1 = b) :
    r 0 0 * g⁻¹ 0 0 + r 0 1 * g⁻¹ 1 0 = a * g⁻¹ 0 0 ∧ r 1 0 * g⁻¹ 0 0 + r 1 1 * g⁻¹ 1 0 = a * g⁻¹ 1 0 ∧
      Matrix.GeneralLinearGroup.det r = a * b := by
  have e : ((r : Matrix (Fin 2) (Fin 2) k) * (g⁻¹ : GL (Fin 2) k)) =
      ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (g * r * g⁻¹ : GL (Fin 2) k) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have e0 := congrFun (congrFun e 0) 0
  have e1 := congrFun (congrFun e 1) 0
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at e0 e1
  have t : Matrix.GeneralLinearGroup.det (g * r * g⁻¹) = Matrix.GeneralLinearGroup.det r := by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  rw [h10, h00] at e0 e1
  refine ⟨?_, ?_, ?_⟩
  · rw [e0]; ring
  · rw [e1]; ring
  · rw [← t]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10, h00, h11, mul_zero, sub_zero]
    rfl

private theorem one_le_norm {K : Type} [NormedField K] [IsUltrametricDist K] {x y a b : K} (h : ¬ ‖x - y‖ < 1)
    (ha : ‖a - x‖ < 1) (hb : ‖b - y‖ < 1) : 1 ≤ ‖a - b‖ ∧ 1 ≤ ‖b - a‖ := by
  have : 1 ≤ ‖a - b‖ := by
    by_contra hlt
    apply h
    rw [norm_sub_rev] at ha
    have e : x - y = (x - a) + ((a - b) + (b - y)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha ?_)
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (not_le.mp hlt) hb)
  exact ⟨this, by rwa [norm_sub_rev]⟩

private theorem norm_le_of {K : Type} [NormedField K] {c d p q : K} (hc : 1 ≤ ‖c‖) (e : c * q = d * p) :
    ‖q‖ ≤ ‖d‖ * ‖p‖ :=
  calc ‖q‖ ≤ ‖c‖ * ‖q‖ := le_mul_of_one_le_left (norm_nonneg _) hc
    _ = ‖d‖ * ‖p‖ := by rw [← norm_mul, e, norm_mul]

theorem UpperTheory.mix_stable_line_local :
    UpperTheory.V.Sd.S2.LocLine := by
  intro l _ S A x κ ⟨s₀, hne⟩ hA ⟨g, hg⟩
  have key := fun s => col_eq g (A s) _ _ (hg s).1 ((hg s).2 0) ((hg s).2 1)
  have hdet : (g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 1 -
      (g⁻¹ : GL (Fin 2) (Qbar l)) 0 1 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 ≠ 0 := by
    have := (g⁻¹).det_ne_zero
    rwa [Matrix.det_fin_two] at this
  generalize (g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 = p at key hdet
  generalize (g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 = q at key hdet
  have hne' : ¬ ‖(x s₀ : Qbar l) - 1‖ < 1 := hne
  obtain ⟨a00, a11, a10, a01⟩ := hA s₀
  refine ⟨fun s => (key s).2.2, fun hκ => ?_, fun hκ => ?_⟩
  · have h1 : ‖(κ 0 s₀ : Qbar l) - (x s₀ : Qbar l)‖ < 1 := hκ s₀
    have hge := (one_le_norm hne' h1 a00).1
    have hpq : ‖p‖ ≤ ‖A s₀ 0 1‖ * ‖q‖ := norm_le_of hge (by linear_combination -(key s₀).1)
    have hq : q ≠ 0 := by
      rintro rfl
      rw [norm_zero, mul_zero, norm_le_zero_iff] at hpq
      simp [hpq] at hdet
    refine ⟨p / q, ?_, fun s => ?_⟩
    · rw [norm_div, div_le_one (norm_pos_iff.mpr hq)]
      exact hpq.trans (mul_le_of_le_one_left (norm_nonneg _) a01)
    · obtain ⟨k1, k2, -⟩ := key s
      ext i
      fin_cases i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
        linear_combination k1
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
        linear_combination k2
  · have h1 : ‖(κ 0 s₀ : Qbar l) - 1‖ < 1 := hκ s₀
    have hge := (one_le_norm hne' a11 h1).2
    have hpq : ‖q‖ ≤ ‖A s₀ 1 0‖ * ‖p‖ := norm_le_of hge (by linear_combination -(key s₀).2.1)
    have hp : p ≠ 0 := by
      rintro rfl
      rw [norm_zero, mul_zero, norm_le_zero_iff] at hpq
      simp [hpq] at hdet
    refine ⟨q / p, ?_, fun s => ?_⟩
    · rw [norm_div, div_lt_one (norm_pos_iff.mpr hp)]
      exact hpq.trans_lt (mul_lt_of_lt_one_left (norm_pos_iff.mpr hp) a10)
    · obtain ⟨k1, k2, -⟩ := key s
      ext i
      fin_cases i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
        linear_combination k1
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
        linear_combination k2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PeriodicIntegralFundamentalDomainInvariant
section
open UpperTheory.V.Sd.Eis
open MeasureTheory Measure Pointwise

private theorem perMean_fin {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] (Γ : AddSubgroup A) [Countable Γ] (hc : Cocpt Γ) (μ : Measure A) [μ.IsAddHaarMeasure]
    (D : Set A) (hD : IsAddFundamentalDomain Γ D μ) : μ D ≠ ⊤ := by
  obtain ⟨C, hC, hcov⟩ := hc
  have h1 : D ⊆ ⋃ g : Γ, ((g +ᵥ C) ∩ D) := by
    intro x hx
    obtain ⟨γ, hγ, h⟩ := hcov x
    refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨x - γ, h, ?_⟩, hx⟩
    change γ + (x - γ) = x
    abel
  have h2 : μ D ≤ μ C := by
    rw [hD.measure_eq_tsum C]
    exact (measure_mono h1).trans (measure_iUnion_le _)
  exact ne_top_of_le_ne_top hC.measure_lt_top.ne h2

private theorem perMean_key {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] (Γ : AddSubgroup A) [Countable Γ] (μ : Measure A) [μ.IsAddHaarMeasure]
    (D : Set A) (hD : IsAddFundamentalDomain Γ D μ) (hfin : μ D ≠ ⊤) (e : A ≃ᵐ A) (c : NNReal)
    (he : μ.map e = c • μ) (σ : Γ → Γ) (hσ : Function.Bijective σ) (hs : ∀ (g : Γ) x, e ((σ g : A) + x) = (g : A) + e x)
    (f : A → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) :
    ∫ x in D, f (e x) ∂μ = ∫ x in D, f x ∂μ := by
  have hq : QuasiMeasurePreserving e μ μ := ⟨e.measurable.aemeasurable, by rw [he]; exact Measure.smul_absolutelyContinuous⟩
  have hD' : IsAddFundamentalDomain Γ (e ⁻¹' D) μ := hD.preimage_of_equiv hq hσ (fun g x => hs g x)
  have hm : μ (e ⁻¹' D) = μ D := by
    have := hD'.measure_set_eq hD MeasurableSet.univ (fun g => by simp)
    simpa using this
  have h0 : μ D ≠ 0 := hD.measure_ne_zero (NeZero.ne μ)
  have hc : (c : ENNReal) = 1 := by
    rw [← e.map_apply, he, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hm
    exact (ENNReal.mul_left_inj h0 hfin).1 (by rw [hm, one_mul])
  have hc' : c = 1 := by exact_mod_cast hc
  rw [hc', one_smul] at he
  have h1 : ∫ x in D, f (e x) ∂μ = ∫ x in e ⁻¹' D, f (e x) ∂μ := by
    refine hD.setIntegral_eq hD' (fun g x => ?_)
    obtain ⟨g', rfl⟩ := hσ.2 g
    change f (e ((σ g' : A) + x)) = _
    rw [hs, hf _ g'.2]
  rw [h1, ← setIntegral_map_equiv, he]

theorem UpperTheory.periodic_integral_fundamentalDomain_invariant :
    UpperTheory.V.Sd.Eis.PerMean := by
  intro A _ _ _ _ _ _ _ _ Γ _ hc μ _ D hD
  have hfin := perMean_fin Γ hc μ D hD
  refine ⟨hfin, fun f hf => ⟨fun hcont => ?_, fun y => ?_, fun e he => ?_⟩⟩
  · obtain ⟨C, hC, hcov⟩ := hc
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
    refine Measure.integrableOn_of_bounded hfin hcont.aestronglyMeasurable (M := M) (Filter.Eventually.of_forall fun x => ?_)
    obtain ⟨γ, hγ, h⟩ := hcov x
    have := hf γ hγ (x - γ)
    rw [add_sub_cancel] at this
    rw [this]
    exact hM _ h
  · refine perMean_key Γ μ D hD hfin (MeasurableEquiv.addRight y) 1 ?_ id Function.bijective_id ?_ f hf
    · rw [one_smul]
      exact map_add_right_eq_self μ y
    · intro g x
      exact add_assoc _ _ _
  · haveI : (μ.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ e
    refine perMean_key Γ μ D hD hfin e.toHomeomorph.toMeasurableEquiv _
      (Measure.isAddLeftInvariant_eq_smul (μ.map e) μ)
      (fun g => ⟨e.symm g, (he _).1 (by simpa using g.2)⟩) ⟨fun a b h => ?_, fun b => ⟨⟨e b, (he _).2 b.2⟩, ?_⟩⟩ ?_ f hf
    · exact Subtype.ext (e.symm.injective (congrArg Subtype.val h))
    · exact Subtype.ext (e.symm_apply_apply _)
    · intro g x
      change e (e.symm g + x) = g + e x
      rw [map_add (f := _), e.apply_symm_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricCubeOverField
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem key {R : Type} [Field R] {g s t : M2 R} {x y : R} (h : g * t = s * g) (hg0 : g 0 0 ≠ 0)
    (hg : g 1 1 = 1 ∧ g 0 1 = 0) (hs : s 1 1 = 1 ∧ s 0 1 = 0) (ht : t 1 1 = 1 ∧ t 0 1 = 0) (hne : s 0 0 ≠ 1)
    (hx : t 1 0 + t 1 1 * x = (t 0 0 + t 0 1 * x) * x) (hy : s 1 0 + s 1 1 * y = (s 0 0 + s 0 1 * y) * y) :
    g 1 0 + g 1 1 * x - (g 0 0 + g 0 1 * x) * y = 0 := by
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hg.1, hg.2, hs.1, hs.2, ht.1, ht.2] at h0 h1 hx hy ⊢
  have e : t 0 0 = s 0 0 := mul_left_cancel₀ hg0 (by linear_combination h0)
  rw [e] at h1 hx
  refine mul_left_cancel₀ (sub_ne_zero.2 hne) ?_
  linear_combination h1 - hx + g 0 0 * hy
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricCubeRootMem
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

theorem UpperTheory.symmetric_cube_root_mem :
    UpperTheory.V.Sd.S3.RootMem := by
  intro l _ E a b c d x ha hb hc hd hb1 had hx hrel
  have hn : ∀ (σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l) (y : Qbar l), ‖σ y‖ = ‖y‖ := by
    intro σ y
    show spectralNorm ℚ_[l] (PadicAlgCl l) (σ y) = spectralNorm ℚ_[l] (PadicAlgCl l) y
    unfold spectralNorm
    rw [minpoly.algEquiv_eq]
  rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  have hrel' : c + d * σ x = (a + b * σ x) * σ x := by
    have h := congrArg σ hrel
    simpa only [map_add (f := _), map_mul, hσ a ha, hσ b hb, hσ c hc, hσ d hd] using h
  by_contra hne
  have hyn : ‖σ x‖ ≤ 1 := by rw [hn]; exact hx
  have key : (σ x - x) * (b * (x + σ x) - (d - a)) = 0 := by linear_combination hrel - hrel'
  have hsub : σ x - x ≠ 0 := sub_ne_zero.mpr hne
  have heq : b * (x + σ x) = d - a := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hsub)
  have hlt : ‖a - d‖ < 1 := by
    rw [← norm_neg, neg_sub, ← heq, norm_mul]
    have hxy : ‖x + σ x‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max x (σ x)).trans (max_le hx hyn)
    calc ‖b‖ * ‖x + σ x‖ ≤ ‖b‖ * 1 := mul_le_mul_of_nonneg_left hxy (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hb1
  rw [had] at hlt
  exact lt_irrefl _ hlt
end

