module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InducedAutomorphicForms.IsIrreducibleIff

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InducedAutomorphicForms.IndSymp
section
open UpperTheory.V.AlgebraTools

private lemma indSymp_two {R : Type} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) :
    A.transpose * !![0, 1; -1, 0] * A = A.det • !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem UpperTheory.V.AlgebraTools.indSymp :
    ∀ {R G : Type} [CommRing R] [Group G] (H : Subgroup G) (s : G), H.index = 2 → s ∉ H → ∀ (r : H →* GL (Fin 2) R) (θ : G →* Rˣ) (I : G →* GL (Fin 2 ⊕ Fin 2) R), (∀ h : H, (r h : Matrix (Fin 2) (Fin 2) R).det = θ h) → (∀ h h' : H, (h' : G) = s⁻¹ * h * s → (I h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = Matrix.fromBlocks (r h : Matrix (Fin 2) (Fin 2) R) 0 0 (r h' : Matrix (Fin 2) (Fin 2) R)) → (∀ t : H, (t : G) = s * s → (I s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = Matrix.fromBlocks 0 (r t : Matrix (Fin 2) (Fin 2) R) 1 0) → ∀ g, (I g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R).transpose * Matrix.fromBlocks !![0, 1; -1, 0] 0 0 ((θ s : R) • !![0, 1; -1, 0]) * (I g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = (θ g : R) • Matrix.fromBlocks !![0, 1; -1, 0] 0 0 ((θ s : R) • !![0, 1; -1, 0]) := by
  intro R G _ _ H s hi hs r θ I hdet hH hS
  have hN : H.Normal := Subgroup.normal_of_index_eq_two hi
  set J : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0] with hJ
  have h2 : ∀ A : Matrix (Fin 2) (Fin 2) R, A.transpose * J * A = A.det • J :=
    fun A => indSymp_two A
  set B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
    Matrix.fromBlocks J 0 0 ((θ s : R) • J) with hB
  have key1 : ∀ h ∈ H, (I h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R).transpose * B *
      (I h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = (θ h : R) • B := by
    intro h hh
    have hh' : s⁻¹ * h * s ∈ H := by simpa using hN.conj_mem h hh s⁻¹
    have e := hH ⟨h, hh⟩ ⟨_, hh'⟩ rfl
    have d1 := hdet ⟨h, hh⟩
    have d2 := hdet ⟨_, hh'⟩
    have d3 : θ (s⁻¹ * h * s) = θ h := by
      simp only [map_mul, map_inv]
      rw [mul_right_comm, inv_mul_cancel, one_mul]
    simp only [d3] at d1 d2 e
    rw [e, hB, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
    simp only [Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      smul_zero, Matrix.mul_smul, Matrix.smul_mul, h2, d1, d2]
    rw [smul_comm (θ s : R)]
  have key2 : (I s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R).transpose * B *
      (I s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = (θ s : R) • B := by
    have ht : s * s ∈ H := Subgroup.mul_self_mem_of_index_two hi s
    have e := hS ⟨_, ht⟩ rfl
    have d := hdet ⟨_, ht⟩
    simp only [map_mul, Units.val_mul] at d
    rw [e, hB, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
    simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.mul_one, Matrix.one_mul,
      smul_zero, Matrix.mul_smul, Matrix.smul_mul, h2, d, smul_smul]
  intro g
  by_cases hg : g ∈ H
  · exact key1 g hg
  · have hh : g * s⁻¹ ∈ H := by
      rw [Subgroup.mul_mem_iff_of_index_two hi]
      simp [hg, hs]
    have eg : g = (g * s⁻¹) * s := by group
    have k := key1 _ hh
    generalize g * s⁻¹ = h at eg k
    subst eg
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.transpose_mul]
    calc _ = (I s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R).transpose *
          ((I h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R).transpose * B *
          (I h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) *
          (I s : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by
            rw [k, Matrix.mul_smul, Matrix.smul_mul, key2, smul_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InducedAutomorphicForms.IndTwo
section
open UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.indTwo :
    ∀ {R G n : Type} [CommRing R] [Group G] [Fintype n] [DecidableEq n] (H : Subgroup G) (s : G), H.index = 2 → s ∉ H → ∀ r : H →* GL n R, ∃ I : G →* GL (n ⊕ n) R, (∀ h h' : H, (h' : G) = s⁻¹ * h * s → (I h : Matrix (n ⊕ n) (n ⊕ n) R) = Matrix.fromBlocks (r h : Matrix n n R) 0 0 (r h' : Matrix n n R)) ∧ ∀ t : H, (t : G) = s * s → (I s : Matrix (n ⊕ n) (n ⊕ n) R) = Matrix.fromBlocks 0 (r t : Matrix n n R) 1 0 := by
  intro R G n _ _ _ _ H s hH hs r
  classical
  obtain ⟨r0, hin, hout⟩ : ∃ r0 : G → Matrix n n R,
      (∀ h : H, r0 h = (r h : Matrix n n R)) ∧ ∀ g, g ∉ H → r0 g = 0 := by
    refine ⟨fun g => if h : g ∈ H then (r ⟨g, h⟩ : Matrix n n R) else 0, ?_, ?_⟩
    · intro h
      simp only [dif_pos h.2]
    · intro g hg
      simp only [dif_neg hg]
  have hs' : s⁻¹ ∉ H := fun h => hs (by simpa using h)
  have hm : ∀ a b : G, a * b ∈ H ↔ (a ∈ H ↔ b ∈ H) := fun a b =>
    Subgroup.mul_mem_iff_of_index_two hH
  have hmul : ∀ a b : G, a ∈ H → b ∈ H → r0 (a * b) = r0 a * r0 b := by
    intro a b ha hb
    have h1 := hin ⟨a, ha⟩
    have h2 := hin ⟨b, hb⟩
    have h3 := hin (⟨a, ha⟩ * ⟨b, hb⟩)
    rw [map_mul, Units.val_mul, ← h1, ← h2] at h3
    exact h3
  have hone : r0 1 = 1 := by
    have := hin 1
    rw [map_one] at this
    simpa using this
  have key : ∀ a b : G, r0 (a * b) = r0 a * r0 b + r0 (a * s) * r0 (s⁻¹ * b) := by
    intro a b
    by_cases ha : a ∈ H <;> by_cases hb : b ∈ H
    · rw [hmul a b ha hb, hout (a * s) (by rw [hm]; tauto), zero_mul, add_zero]
    · rw [hout (a * b) (by rw [hm]; tauto), hout b hb, hout (a * s) (by rw [hm]; tauto)]
      simp
    · rw [hout (a * b) (by rw [hm]; tauto), hout a ha, hout (s⁻¹ * b) (by rw [hm]; tauto)]
      simp
    · rw [hout a ha, zero_mul, zero_add,
        ← hmul _ _ (by rw [hm]; tauto) (by rw [hm]; tauto)]
      congr 1
      group
  let M : G →* Matrix (n ⊕ n) (n ⊕ n) R :=
    { toFun := fun g => Matrix.fromBlocks (r0 g) (r0 (g * s)) (r0 (s⁻¹ * g)) (r0 (s⁻¹ * g * s))
      map_one' := by
        rw [one_mul, mul_one, inv_mul_cancel, hone, hout s hs, hout _ hs', Matrix.fromBlocks_one]
      map_mul' := by
        intro a b
        rw [Matrix.fromBlocks_multiply]
        have e1 := key a b
        have e2 := key a (b * s)
        have e3 := key (s⁻¹ * a) b
        have e4 := key (s⁻¹ * a) (b * s)
        simp only [mul_assoc] at e1 e2 e3 e4 ⊢
        rw [e1, e2, e3, e4] }
  have hM : ∀ g, (M.toHomUnits g : Matrix (n ⊕ n) (n ⊕ n) R) =
      Matrix.fromBlocks (r0 g) (r0 (g * s)) (r0 (s⁻¹ * g)) (r0 (s⁻¹ * g * s)) := fun g => rfl
  refine ⟨M.toHomUnits, ?_, ?_⟩
  · intro h h' hh
    have h2 := h.2
    rw [hM, ← hh, hin, hin, hout (h * s) (by rw [hm]; tauto),
      hout (s⁻¹ * h) (by rw [hm]; tauto)]
  · intro t ht
    rw [hM, ← ht, hin, inv_mul_cancel, one_mul, hone, hout s hs]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InducedAutomorphicForms.MackeyTwo
section
open UpperTheory.V.AlgebraTools

private theorem graph_equiv {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (A B W : Submodule k V) (hA : IsCompl A W) (hB : IsCompl B W) :
    ∃ e : A ≃ₗ[k] B, ∀ v : A, (v : V) - e v ∈ W := by
  have key : ∀ x : V, x - (B.projectionOnto W hB x : V) ∈ W := by
    intro x
    rw [← Submodule.projectionOnto_apply_eq_zero_iff hB, map_sub,
      Submodule.projectionOnto_apply_left, sub_self]
  refine ⟨LinearEquiv.ofBijective ((B.projectionOnto W hB) ∘ₗ A.subtype) ⟨?_, ?_⟩, fun v => key v⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : (a : V) ∈ W := (Submodule.projectionOnto_apply_eq_zero_iff hB).1 ha
    exact Subtype.ext (Submodule.disjoint_def.1 hA.disjoint _ a.2 h1)
  · intro b
    have hb : (b : V) ∈ A ⊔ W := by rw [hA.sup_eq_top]; trivial
    obtain ⟨a, ha, w, hw, hsum⟩ := Submodule.mem_sup.1 hb
    refine ⟨⟨a, ha⟩, ?_⟩
    have h1 : a = (b : V) - w := by rw [← hsum]; abel
    have h2 : B.projectionOnto W hB w = 0 := (Submodule.projectionOnto_apply_eq_zero_iff hB).2 hw
    show B.projectionOnto W hB a = b
    rw [h1, map_sub, h2, sub_zero, Submodule.projectionOnto_apply_left]

theorem UpperTheory.V.AlgebraTools.mackeyTwo :
    ∀ {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] (ρ : Representation k G V) (H : Subgroup G) (s : G) (V₁ : Submodule k V), H.index = 2 → s ∉ H → StableOn ρ H V₁ → (∀ W ≤ V₁, StableOn ρ H W → W = ⊥ ∨ W = V₁) → IsCompl V₁ (V₁.map (ρ s)) → (¬ ∃ e : V₁ ≃ₗ[k] V₁.map (ρ s), ∀ h ∈ H, ∀ v w : V₁, (w : V) = ρ h v → (e w : V) = ρ h (e v)) → IrrOn ρ ⊤ := by
  intro k G V _ _ _ _ ρ H s V₁ hi hs hst hirr hc hne W hW
  have hmul : ∀ (a b : G) (x : V), ρ a (ρ b x) = ρ (a * b) x := by
    intro a b x; rw [map_mul]; rfl
  have hinv : ∀ x : V, ρ s⁻¹ (ρ s x) = x := by
    intro x; rw [hmul, inv_mul_cancel, map_one]; rfl
  have hinv' : ∀ x : V, ρ s (ρ s⁻¹ x) = x := by
    intro x; rw [hmul, mul_inv_cancel, map_one]; rfl
  have hconj : ∀ h ∈ H, s⁻¹ * (h * s) ∈ H := by
    intro h hh
    simp [Subgroup.mul_mem_iff_of_index_two hi, hs, hh]
  have hss : s * s ∈ H := by simp [Subgroup.mul_mem_iff_of_index_two hi]
  have hst2 : StableOn ρ H (V₁.map (ρ s)) := by
    rintro h hh _ ⟨v, hv, rfl⟩
    refine ⟨ρ (s⁻¹ * (h * s)) v, hst _ (hconj h hh) v hv, ?_⟩
    rw [hmul, hmul, mul_inv_cancel_left]
  have hW' : ∀ g, ∀ v ∈ W, ρ g v ∈ W := fun g => hW g trivial
  rcases hirr (V₁ ⊓ W) inf_le_left
      (fun h hh v hv => ⟨hst h hh v hv.1, hW' h v hv.2⟩) with h0 | h1
  swap
  · right
    have hle : V₁ ≤ W := inf_eq_left.1 h1
    rw [eq_top_iff, ← hc.sup_eq_top]
    refine sup_le hle ?_
    rintro _ ⟨v, hv, rfl⟩
    exact hW' s v (hle hv)
  have d1 : Disjoint V₁ W := disjoint_iff.2 h0
  have d2 : Disjoint (V₁.map (ρ s)) W := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨v, hv, rfl⟩ hw
    have : v ∈ W := hinv v ▸ hW' s⁻¹ _ hw
    rw [Submodule.disjoint_def.1 d1 v hv this, map_zero]
  rcases hirr (V₁ ⊓ (V₁.map (ρ s) ⊔ W)) inf_le_left (fun h hh v hv => ⟨hst h hh v hv.1, by
      obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 hv.2
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hst2 h hh a ha) (hW' h w hw)⟩) with h2 | h2
  · left
    rw [eq_bot_iff]
    intro w hw
    have hb : w ∈ V₁ ⊔ V₁.map (ρ s) := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, hsum⟩ := Submodule.mem_sup.1 hb
    have ha' : a ∈ V₁ ⊓ (V₁.map (ρ s) ⊔ W) := by
      refine ⟨ha, ?_⟩
      have : a = -b + w := by rw [← hsum]; abel
      rw [this]
      exact Submodule.add_mem_sup (neg_mem hb) hw
    rw [h2, Submodule.mem_bot] at ha'
    rw [ha', zero_add] at hsum
    exact Submodule.disjoint_def.1 d2 w (hsum ▸ hb) hw
  exfalso
  have hle : V₁ ≤ V₁.map (ρ s) ⊔ W := inf_eq_left.1 h2
  have c2 : IsCompl (V₁.map (ρ s)) W := by
    refine ⟨d2, codisjoint_iff.2 ?_⟩
    rw [eq_top_iff, ← hc.sup_eq_top]
    exact sup_le hle le_sup_left
  have c1 : IsCompl V₁ W := by
    refine ⟨d1, codisjoint_iff.2 ?_⟩
    rw [eq_top_iff, ← hc.sup_eq_top]
    refine sup_le le_sup_left ?_
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨_, ⟨a, ha, rfl⟩, w, hw, rfl⟩ := Submodule.mem_sup.1 (hle hv)
    rw [map_add (f := _), hmul]
    exact Submodule.add_mem_sup (hst _ hss a ha) (hW' s w hw)
  obtain ⟨e, he⟩ := graph_equiv _ _ _ c1 c2
  refine hne ⟨e, fun h hh v w hvw => ?_⟩
  have m1 : (e w : V) - ρ h (e v) ∈ V₁.map (ρ s) := sub_mem (e w).2 (hst2 h hh _ (e v).2)
  have m2 : (e w : V) - ρ h (e v) ∈ W := by
    have : (e w : V) - ρ h (e v) = ρ h ((v : V) - e v) - ((w : V) - e w) := by
      rw [map_sub, ← hvw]; abel
    rw [this]
    exact sub_mem (hW' h _ (he v)) (he w)
  exact sub_eq_zero.1 (Submodule.disjoint_def.1 d2 _ m1 m2)
end

