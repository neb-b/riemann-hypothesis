module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.FinrankKerAdRepComplexConjSubOneEqBoxDef
section
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg

namespace UpperTheory.V.U3.FixDim

variable {k : Type} [Field k]

private def sw (k : Type) [Field k] : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k := Matrix.fromBlocks 0 1 1 0

private def am (x y z : k) : Matrix (Fin 3) (Fin 3) k := !![x, y, 0; z, 0, -y; 0, -z, -x]

private def bm (x y z : k) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k :=
  Matrix.fromBlocks (am x y z) 0 0 (am x y z)

private theorem emb_c {Γ : Type} [Group Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* kˣ) (c : Γ) (h1 : η c = -1) (h2 : Ψ c = 1) :
    emb (r0 η Ψ c) = sw k := by
  rw [emb_apply, GG.mat, unitaryThreeReflection_left, theta_tor, unitaryThreeReflection_right, h1, h2, map_one, if_neg (by decide)]
  rfl

private theorem J3 : Jmat k 3 = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Jmat] <;> decide

private theorem sw_bm (x y z : k) : sw k * bm x y z * sw k = bm x y z := by
  simp [sw, bm, Matrix.fromBlocks_multiply]

private theorem bm_smul (t x y z : k) : t • bm x y z = bm (t * x) (t * y) (t * z) := by
  have : t • am x y z = am (t * x) (t * y) (t * z) := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [am]
  simp [bm, Matrix.fromBlocks_smul, this]

private theorem bm_mem (O : Type) [CommRing O] [Algebra O k] (j : ℤ) (x y z : k) (hx : j ≠ 0 → x = 0)
    (hy : j ≠ 1 → y = 0) (hz : j ≠ -1 → z = 0) : bm x y z ∈ (form6 O).gw k j := by
  have h0 : (am x y z)ᵀ * Jmat k 3 + Jmat k 3 * am x y z = 0 := by
    rw [J3]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [am, Matrix.mul_apply, Fin.sum_univ_three]
  have h1 : ∀ a b : Fin 3, wt1 a - wt1 b ≠ j → am x y z a b = 0 := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [wt1] at h <;> simp [am] <;>
      first | exact hx (by omega) | exact hy (by omega) | exact hz (by omega)
  refine ⟨⟨?_, fun a b h => ?_⟩, fun a b h => ?_⟩
  · rw [blockPairingForm_JR]
    simp [bm, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, h0]
  · rcases a with a | a <;> rcases b with b | b <;> first | rfl | exact absurd rfl h
  · rcases a with a | a <;> rcases b with b | b <;> first | rfl | exact h1 a b h

private theorem eq_bm (O : Type) [CommRing O] [Algebra O k] (h2 : (2 : k) ≠ 0) (j : ℤ)
    (Y : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k) (hY : Y ∈ (form6 O).gw k j) (hs : sw k * Y * sw k = Y) :
    ∃ x y z : k, Y = bm x y z ∧ (j ≠ 0 → x = 0) ∧ (j ≠ 1 → y = 0) ∧ (j ≠ -1 → z = 0) := by
  obtain ⟨⟨y1, y2⟩, y3⟩ := hY
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, Y = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks Y).symm⟩
  have hB : B = 0 := by
    ext a b
    exact y2 (.inl a) (.inr b) (by simp [form6])
  have hC : C = 0 := by
    ext a b
    exact y2 (.inr a) (.inl b) (by simp [form6])
  subst hB hC
  have hD : D = A := by
    simp [sw, Matrix.fromBlocks_multiply] at hs
    exact hs.1
  subst hD
  rw [blockPairingForm_JR] at y1
  have h0 : Dᵀ * Jmat k 3 + Jmat k 3 * D = 0 := by
    ext a b
    have := congrFun (congrFun y1 (.inl a)) (.inr b)
    simpa [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add] using this
  rw [J3] at h0
  have e := fun a b => congrFun (congrFun h0 a) b
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e11 := e 1 1
  have e12 := e 1 2
  have e22 := e 2 2
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, ← two_mul, h2] at e00 e01 e02 e11 e12 e22
  refine ⟨D 0 0, D 0 1, D 1 0, ?_, fun h => y3 (.inl 0) (.inl 0) ?_, fun h => y3 (.inl 0) (.inl 1) ?_,
    fun h => y3 (.inl 1) (.inl 0) ?_⟩
  · have : D = am (D 0 0) (D 0 1) (D 1 0) := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [am] <;>
        first | assumption | linear_combination e01 | linear_combination e02 | linear_combination e12
    rw [bm, ← this]
  · simp [wt6, wt1]; omega
  · simp [wt6, wt1]; omega
  · simp [wt6, wt1]; omega

end UpperTheory.V.U3.FixDim

open UpperTheory.V.U3.FixDim in
theorem UpperTheory.finrank_ker_adRep_complexConj_sub_one_eq_boxDef :
    ∀ (O k : Type) [CommRing O] [Field k] [Algebra O k], (2 : k) ≠ 0 → ∀ {Γ : Type} [Group Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* kˣ) (c : Γ), η c = -1 → Ψ c = 1 → ∀ j : ℤ,
          Module.finrank k (LinearMap.ker (FormData.adRep (blockPairingForm_normalises_baseLift O η Ψ) j c - 1)) = boxDef j := by
  intro O k _ _ _ h2 Γ _ η Ψ c h1 hΨ j
  have e1 := emb_c η Ψ c h1 hΨ
  have e2 := emb_c η Ψ c⁻¹ (by rw [map_inv, h1]; rfl) (by rw [map_inv, hΨ, inv_one])
  have hk : ∀ Y : (form6 O).gw k j, Y ∈ LinearMap.ker (FormData.adRep (blockPairingForm_normalises_baseLift O η Ψ) j c - 1) ↔
      sw k * Y.1 * sw k = Y.1 := by
    intro Y
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Subtype.ext_iff]
    show emb (r0 η Ψ c) * Y.1 * emb (r0 η Ψ c⁻¹) = Y.1 ↔ _
    rw [e1, e2]
  have one : ∀ x y z : k, (j ≠ 0 → x = 0) → (j ≠ 1 → y = 0) → (j ≠ -1 → z = 0) → bm x y z ≠ 0 →
      (∀ x' y' z' : k, (j ≠ 0 → x' = 0) → (j ≠ 1 → y' = 0) → (j ≠ -1 → z' = 0) →
        ∃ t : k, t * x = x' ∧ t * y = y' ∧ t * z = z') →
      Module.finrank k (LinearMap.ker (FormData.adRep (blockPairingForm_normalises_baseLift O η Ψ) j c - 1)) = 1 := by
    intro x y z hx hy hz hne hgen
    refine finrank_eq_one_iff'.2 ⟨⟨⟨bm x y z, bm_mem O j x y z hx hy hz⟩, (hk _).2 (sw_bm x y z)⟩, ?_, ?_⟩
    · intro h
      exact hne (congrArg (fun v => v.1.1) h)
    · rintro ⟨Y, hY⟩
      obtain ⟨x', y', z', e, h⟩ := eq_bm O h2 j Y.1 Y.2 ((hk Y).1 hY)
      obtain ⟨t, rfl, rfl, rfl⟩ := hgen x' y' z' h.1 h.2.1 h.2.2
      refine ⟨t, Subtype.ext (Subtype.ext ?_)⟩
      show t • bm x y z = Y.1
      rw [e, bm_smul]
  by_cases j0 : j = 0
  · subst j0
    refine one 1 0 0 (by simp) (by simp) (by simp) (fun h => ?_) (fun x y z _ hy hz => ⟨x, by simp, ?_, ?_⟩)
    · simpa [bm, am] using congrFun (congrFun h (.inl 0)) (.inl 0)
    · simp [hy (by decide)]
    · simp [hz (by decide)]
  by_cases j1 : j = 1
  · subst j1
    refine one 0 1 0 (by simp) (by simp) (by simp) (fun h => ?_) (fun x y z hx _ hz => ⟨y, ?_, by simp, ?_⟩)
    · simpa [bm, am] using congrFun (congrFun h (.inl 0)) (.inl 1)
    · simp [hx (by decide)]
    · simp [hz (by decide)]
  by_cases j2 : j = -1
  · subst j2
    refine one 0 0 1 (by simp) (by simp) (by simp) (fun h => ?_) (fun x y z hx hy _ => ⟨z, ?_, ?_, by simp⟩)
    · simpa [bm, am] using congrFun (congrFun h (.inl 1)) (.inl 0)
    · simp [hx (by decide)]
    · simp [hy (by decide)]
  rw [boxDef, if_neg (by rw [abs_le]; omega), Submodule.finrank_eq_zero, eq_bot_iff]
  intro Y hY
  obtain ⟨x, y, z, e, hx, hy, hz⟩ := eq_bm O h2 j Y.1 Y.2 ((hk Y).1 hY)
  rw [Submodule.mem_bot]
  refine Subtype.ext ?_
  rw [e, hx j0, hy j1, hz j2]
  simpa using (bm_smul (0 : k) 0 0 0).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.NotPrimeDvdRelIndexKerInducedUnitaryRep
section
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg

theorem UpperTheory.not_prime_dvd_relIndex_ker_inducedUnitaryRep :
    ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l], l ≠ 2 → ∀ {Γ : Type} [Group Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* kˣ) (I : Subgroup Γ),
          ¬ l ∣ (I ⊓ (r0 η Ψ).ker).relIndex I := by
  intro l _ k _ _ _ hl2 Γ _ η Ψ I
  haveI := Fintype.ofFinite k
  have hp : l.Prime := Fact.out
  obtain ⟨n, -, hcard⟩ := FiniteField.card k l
  let φ : Γ →* kˣ × ℤˣ := Ψ.prod η
  let ψ : kˣ × ℤˣ →* GG (m := 3) (R := k) := r0 (MonoidHom.snd kˣ ℤˣ) (MonoidHom.fst kˣ ℤˣ)
  have hle : (φ.domRestrict I).ker ≤ ((r0 η Ψ).domRestrict I).ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    show ψ (φ.domRestrict I g) = 1
    rw [hg, map_one]
  have h1 : (I ⊓ (r0 η Ψ).ker).relIndex I ∣ (φ.domRestrict I).ker.index := by
    rw [inf_comm, Subgroup.inf_relIndex_right, Subgroup.relIndex, ← MonoidHom.ker_restrict]
    exact Subgroup.index_dvd_of_le hle
  have h2 : (φ.domRestrict I).ker.index ∣ (Nat.card k - 1) * 2 := by
    rw [Subgroup.index_ker]
    have hd := Subgroup.card_subgroup_dvd_card (φ.domRestrict I).range
    rwa [Nat.card_prod, Nat.card_units, Nat.card_eq_fintype_card (α := ℤˣ),
      Fintype.card_units_int] at hd
  rw [Nat.card_eq_fintype_card, hcard] at h2
  intro hdvd
  have h3 := dvd_trans hdvd (dvd_trans h1 h2)
  rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
  · have h5 : l ∣ l ^ (n : ℕ) := dvd_pow_self l n.ne_zero
    have hpos : 1 ≤ l ^ (n : ℕ) := Nat.one_le_pow _ _ hp.pos
    have he : l ^ (n : ℕ) = (l ^ (n : ℕ) - 1) + 1 := by omega
    rw [he] at h5
    have h6 := (Nat.dvd_add_right h4).mp h5
    exact hp.one_lt.ne' (Nat.dvd_one.mp h6)
  · have h7 := Nat.le_of_dvd (by norm_num) h4
    have h8 := hp.two_le
    omega
end

