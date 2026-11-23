module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.AsAlgebraHomSurjectiveOfFinrankIntertwiningMapEq
section
namespace GlobalTheory

open scoped MonoidAlgebra

theorem asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one :
    ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (τ : Representation K G V), Module.finrank K (Representation.IntertwiningMap τ τ) = 1 → Nontrivial V ∧ Function.Surjective τ.asAlgebraHom := by
  intro K _ _ G _ _ V _ _ _ τ h
  classical
  have : NeZero (Nat.card G : K) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hV : Nontrivial V := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : Subsingleton (Representation.IntertwiningMap τ τ) :=
      ⟨fun f g => Representation.IntertwiningMap.ext (Subsingleton.elim _ _)⟩
    rw [Module.finrank_zero_of_subsingleton] at h
    exact zero_ne_one h
  refine ⟨hV, ?_⟩
  have : Nontrivial τ.asModule := hV
  have hE : Module.finrank K (Module.End K[G] τ.asModule) = 1 := by
    rw [← (Representation.IntertwiningMap.equivAlgEnd τ).toLinearEquiv.finrank_eq]
    exact h
  have hscalar : ∀ φ : Module.End K[G] τ.asModule, ∃ c : K, c • (1 : Module.End K[G] τ.asModule) = φ :=
    (finrank_eq_one_iff_of_nonzero' _ one_ne_zero).mp hE
  have : IsScalarTower K (Module.End K[G] τ.asModule) τ.asModule := ⟨fun _ _ _ => rfl⟩
  have : Module.Finite (Module.End K[G] τ.asModule) τ.asModule :=
    Module.Finite.of_restrictScalars_finite K _ _
  intro f
  let F : Module.End (Module.End K[G] τ.asModule) τ.asModule :=
    { toFun := fun m => f m
      map_add' := fun x y => f.map_add x y
      map_smul' := fun φ m => by
        obtain ⟨c, rfl⟩ := hscalar φ
        exact f.map_smul c m }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := K[G]) (M := τ.asModule) F
  refine ⟨a, LinearMap.ext fun v => ?_⟩
  exact congrArg (fun g => g v) ha

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardFixedByPowPrimePowModEq
section
namespace GlobalTheory

theorem card_fixedBy_pow_prime_pow_modEq (G : Type) [Group G] (X : Type) [Finite X] [MulAction G X]
    (x : G) (p k : ℕ) (hp : p.Prime) :
    Nat.card (MulAction.fixedBy X (x ^ p ^ k)) ≡ Nat.card (MulAction.fixedBy X x) [MOD p] := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype X := Fintype.ofFinite X
  let f : Function.End (MulAction.fixedBy X (x ^ p ^ k)) := fun y => ⟨x • (y : X), by
    have hy : (x ^ p ^ k) • (y : X) = y := y.2
    show (x ^ p ^ k) • x • (y : X) = x • (y : X)
    rw [← mul_smul, ← pow_succ, pow_succ', mul_smul, hy]⟩
  have hf : ∀ (n : ℕ) (y : MulAction.fixedBy X (x ^ p ^ k)), (((f ^ n) y : MulAction.fixedBy X (x ^ p ^ k)) : X) = x ^ n • (y : X) := by
    intro n
    induction n with
    | zero => intro y; rw [pow_zero, pow_zero, one_smul]; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', pow_succ', mul_smul, ← ih y]
      rfl
  have h1 : f ^ p ^ k = 1 := by
    funext y
    apply Subtype.ext
    rw [hf]
    exact y.2
  have h2 := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := k) h1
  have e : (Function.fixedPoints f) ≃ MulAction.fixedBy X x :=
    { toFun := fun y => ⟨(y.1 : X), congrArg Subtype.val y.2⟩
      invFun := fun y => ⟨⟨y.1, MulAction.fixedBy_subset_fixedBy_zpow X x ((p ^ k : ℕ) : ℤ) y.2 |> fun h => by
          rwa [zpow_natCast] at h⟩, Subtype.ext y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  convert h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardFixedByQuotientEqRelIndexOfPRegular
section
namespace GlobalTheory

theorem conj_mem_zpowers_of_mem_of_pRegular {G : Type} [Group G] (c : G) (p : ℕ) (H : Subgroup G)
    (hc : Nat.Coprime (orderOf c) p)
    (hp : ∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ Subgroup.zpowers c) (g : G)
    (hg : g⁻¹ * c * g ∈ H) : g⁻¹ * c * g ∈ Subgroup.zpowers c := by
  obtain ⟨k, hk⟩ := hp _ hg
  have ho : orderOf (g⁻¹ * c * g) = orderOf c := by
    have := (MulAut.conj g⁻¹).orderOf_eq c
    simpa using this
  have hcop : Nat.Coprime (p ^ k) (orderOf (g⁻¹ * c * g)) := by
    rw [ho]
    exact Nat.Coprime.pow_left k hc.symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact Subgroup.pow_mem _ hk m

theorem card_fixedBy_quotient_eq_relIndex_of_pRegular :
    ∀ (G : Type) [Group G] [Finite G] (c : G) (p : ℕ) (H N : Subgroup G), Nat.Coprime (orderOf c) p → Subgroup.zpowers c ≤ H → (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ Subgroup.zpowers c) → (∀ g : G, g ∈ N ↔ ∀ d ∈ Subgroup.zpowers c, g * d * g⁻¹ ∈ Subgroup.zpowers c) → Nat.card (MulAction.fixedBy (G ⧸ H) c) = H.relIndex N := by
  intro G _ _ c p H N hc hH hp hN
  have key : ∀ g : G, c • (g : G ⧸ H) = (g : G ⧸ H) ↔ g ∈ N := by
    intro g
    have h1 : c • (g : G ⧸ H) = (g : G ⧸ H) ↔ g⁻¹ * c * g ∈ H := by
      rw [eq_comm, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, mul_assoc]
    rw [h1]
    constructor
    · intro hg
      have hy := conj_mem_zpowers_of_mem_of_pRegular c p H hc hp g hg
      rw [← N.inv_mem_iff, hN]
      rintro d ⟨n, rfl⟩
      have h2 := Subgroup.zpow_mem _ hy n
      have h3 : (g⁻¹ * c * g) ^ n = g⁻¹ * c ^ n * g⁻¹⁻¹ := by
        rw [← conj_zpow, inv_inv]
      rw [h3] at h2
      exact h2
    · intro hg
      have := (hN _).1 (N.inv_mem hg) c (Subgroup.mem_zpowers c)
      rw [inv_inv] at this
      exact hH this
  let f : N ⧸ H.subgroupOf N → MulAction.fixedBy (G ⧸ H) c :=
    Quotient.lift (fun n : N => ⟨((n : G) : G ⧸ H), (key n).2 n.2⟩) (by
      intro a b hab
      apply Subtype.ext
      have h : a⁻¹ * b ∈ H.subgroupOf N := QuotientGroup.leftRel_apply.1 hab
      exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using h))
  have hf : Function.Bijective f := by
    constructor
    · intro x y
      induction x using QuotientGroup.induction_on with
      | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
      intro hab
      have h : ((a : G) : G ⧸ H) = ((b : G) : G ⧸ H) := congrArg Subtype.val hab
      rw [QuotientGroup.eq] at h ⊢
      simpa [Subgroup.mem_subgroupOf] using h
    · rintro ⟨x, hx⟩
      induction x using QuotientGroup.induction_on with
      | H g => exact ⟨((⟨g, (key g).1 hx⟩ : N) : N ⧸ H.subgroupOf N), rfl⟩
  exact (Nat.card_eq_of_bijective f hf).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCoprimeOrderOfPowPrimePow
section
namespace GlobalTheory

theorem exists_coprime_orderOf_pow_prime_pow (G : Type) [Group G] [Finite G] (x : G) (p : ℕ)
    (hp : p.Prime) : ∃ k : ℕ, Nat.Coprime (orderOf (x ^ p ^ k)) p := by
  obtain ⟨k, u, hu, h⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.ne_one
  refine ⟨k, ?_⟩
  have h1 : orderOf (x ^ p ^ k) ∣ u := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, ← h, pow_orderOf_eq_one]
  exact Nat.Coprime.coprime_dvd_left h1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hu).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsSmulEqTransposeMulDiagonalMul
section
open Matrix Polynomial
open scoped BigOperators

namespace GlobalTheory

theorem exists_rat_eq_transpose_mul_diagonal_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hs : A.IsSymm) (hp : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < x ⬝ᵥ A *ᵥ x) :
    ∃ (d : Fin n → ℚ) (Q : Matrix (Fin n) (Fin n) ℚ), (∀ i, 0 < d i) ∧ Q.det ≠ 0 ∧
      A = Qᵀ * Matrix.diagonal d * Q := by
  have hsym : (Matrix.toBilin' A).IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hs
  obtain ⟨v₀, hv₀⟩ := LinearMap.BilinForm.exists_orthogonal_basis (K := ℚ) (V := Fin n → ℚ)
    (B := Matrix.toBilin' A) (LinearMap.BilinForm.isSymm_iff.mp hsym)
  have hr : Module.finrank ℚ (Fin n → ℚ) = n := by simp
  let e : Fin (Module.finrank ℚ (Fin n → ℚ)) ≃ Fin n := finCongr hr
  let v := v₀.reindex e
  have hv : ∀ i j, i ≠ j → v i ⬝ᵥ A *ᵥ v j = 0 := by
    intro i j hij
    have h := hv₀ (e.symm.injective.ne hij)
    simp only [Function.onFun] at h
    rw [Matrix.toBilin'_apply'] at h
    simpa only [v, Module.Basis.reindex_apply] using h
  let P : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => v i j
  have hP : IsUnit P := Matrix.linearIndependent_rows_iff_isUnit.mp v.linearIndependent
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hdiag : P * A * Pᵀ = Matrix.diagonal fun i => v i ⬝ᵥ A *ᵥ v i := by
    ext i j
    have : (P * A * Pᵀ) i j = v i ⬝ᵥ A *ᵥ v j := by
      rw [Matrix.mul_assoc]
      simp [Matrix.mul_apply, P, dotProduct, Matrix.mulVec]
    rw [this]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij, hv i j hij]
  refine ⟨fun i => v i ⬝ᵥ A *ᵥ v i, (P⁻¹)ᵀ, fun i => hp _ (v.ne_zero i), ?_, ?_⟩
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_nonsing_inv_det P hPd).ne_zero
  · rw [← hdiag, Matrix.transpose_transpose]
    have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
    have h2 : Pᵀ * (P⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
    calc A = (P⁻¹ * P) * A * (Pᵀ * (P⁻¹)ᵀ) := by rw [h1, h2]; simp
      _ = P⁻¹ * (P * A * Pᵀ) * (P⁻¹)ᵀ := by simp only [Matrix.mul_assoc]

theorem exists_pos_nat_mul_eq_intCast {ι : Type} [Finite ι] (f : ι → ℚ) :
    ∃ (b : ℕ) (g : ι → ℤ), 0 < b ∧ ∀ i, (g i : ℚ) = b * f i := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) f
  choose g hg using hb
  have hb0 : (b : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  refine ⟨((b : ℤ) * b).toNat, fun i => b * g i, ?_, fun i => ?_⟩
  · have := mul_self_pos.mpr hb0
    omega
  · have h1 : ((((b : ℤ) * b).toNat : ℕ) : ℤ) = b * b := Int.toNat_of_nonneg (mul_self_nonneg _)
    have h2 : ((((b : ℤ) * b).toNat : ℕ) : ℚ) = ((b : ℤ) : ℚ) * (b : ℤ) := by exact_mod_cast h1
    have h3 : (g i : ℚ) = ((b : ℤ) : ℚ) * f i := by
      have := hg i
      simpa [zsmul_eq_mul] using this
    rw [h2]
    push_cast
    rw [h3]
    ring

theorem exists_smul_eq_transpose_mul_diagonal_mul :
    (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), (A.map (fun x : ℤ => (x : ℝ))).PosDef → ∃ (N : ℕ) (c : Fin n → ℕ) (l : Matrix (Fin n) (Fin n) ℤ), 0 < N ∧ (∀ i, 0 < c i) ∧ l.det ≠ 0 ∧ (N : ℤ) • A = lᵀ * Matrix.diagonal (fun i => (c i : ℤ)) * l) := by
  intro n A hA
  have hs : (A.map (fun x : ℤ => (x : ℚ))).IsSymm := by
    ext i j
    have := hA.isHermitian.apply j i
    simp only [Matrix.map_apply, star_trivial, Int.cast_inj] at this
    simp [this]
  have hp : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < x ⬝ᵥ (A.map (fun x : ℤ => (x : ℚ))) *ᵥ x := by
    intro x hx
    have hx' : (fun i => (x i : ℝ)) ≠ 0 := by
      intro h
      apply hx
      ext i
      have := congrFun h i
      simpa using this
    have h := hA.dotProduct_mulVec_pos hx'
    have h2 : star (fun i => (x i : ℝ)) ⬝ᵥ (A.map (fun x : ℤ => (x : ℝ))) *ᵥ (fun i => (x i : ℝ))
        = ((x ⬝ᵥ (A.map (fun x : ℤ => (x : ℚ))) *ᵥ x : ℚ) : ℝ) := by
      simp [dotProduct, Matrix.mulVec]
    rw [h2] at h
    exact_mod_cast h
  obtain ⟨d, Q, hd, hQ, hAQ⟩ := exists_rat_eq_transpose_mul_diagonal_mul _ hs hp
  obtain ⟨a, g, ha, hg⟩ := exists_pos_nat_mul_eq_intCast (fun p : Fin n × Fin n => Q p.1 p.2)
  obtain ⟨b, k, hb, hk⟩ := exists_pos_nat_mul_eq_intCast d
  have hkpos : ∀ i, 0 < k i := by
    intro i
    have : (0 : ℚ) < k i := by
      rw [hk i]
      exact mul_pos (by exact_mod_cast hb) (hd i)
    exact_mod_cast this
  let l : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => g (i, j)
  have hl : l.map (Int.castRingHom ℚ) = (a : ℚ) • Q := by
    ext i j
    simp [l, hg]
  have hc : (Matrix.diagonal fun i => (((k i).toNat : ℕ) : ℤ)).map (Int.castRingHom ℚ)
      = (b : ℚ) • Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
      rw [Int.toNat_of_nonneg (hkpos i).le]
      exact hk i
    · simp [Matrix.diagonal_apply_ne _ hij]
  refine ⟨a * b * a, fun i => (k i).toNat, l, by positivity, fun i => ?_, ?_, ?_⟩
  · have := hkpos i
    show 0 < (k i).toNat
    omega
  · intro h0
    have h1 : (l.map (Int.castRingHom ℚ)).det = 0 := by
      have := (Int.castRingHom ℚ).map_det l
      rw [RingHom.mapMatrix_apply, h0] at this
      simpa using this.symm
    rw [hl, Matrix.det_smul] at h1
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    exact (mul_ne_zero (pow_ne_zero _ ha') hQ) h1
  · apply Matrix.map_injective (f := Int.castRingHom ℚ) (Int.cast_injective (α := ℚ))
    simp only
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hl, hc]
    have : (((a * b * a : ℕ) : ℤ) • A).map (Int.castRingHom ℚ)
        = ((a : ℚ) * b * a) • A.map (fun x : ℤ => (x : ℚ)) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast]
      push_cast
      ring
    rw [this, hAQ]
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsSylowOverSubgroup
section
namespace GlobalTheory

theorem exists_sylow_over_subgroup (G : Type) [Group G] [Finite G] (C : Subgroup G) (p : ℕ)
    (hp : p.Prime) :
    ∃ H : Subgroup G, C ≤ H ∧ (∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧
      (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ C) ∧
      ∀ N : Subgroup G, (∀ g : G, g ∈ N ↔ ∀ c ∈ C, g * c * g⁻¹ ∈ C) → ¬ p ∣ H.relIndex N := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let N : Subgroup G :=
    { carrier := {g | ∀ c ∈ C, g * c * g⁻¹ ∈ C}
      one_mem' := by intro c hc; simpa using hc
      mul_mem' := by
        intro a b ha hb c hc
        have := ha _ (hb c hc)
        simpa [mul_assoc] using this
      inv_mem' := by
        intro a ha c hc
        have key : ∀ n : ℕ, ∀ c ∈ C, a ^ n * c * (a ^ n)⁻¹ ∈ C := by
          intro n
          induction n with
          | zero => intro c hc; simpa using hc
          | succ n ih =>
            intro c hc
            have := ha _ (ih c hc)
            simpa [pow_succ', mul_assoc] using this
        have h1 : a ^ (orderOf a - 1) = a⁻¹ := by
          have hpos : 0 < orderOf a := orderOf_pos a
          apply eq_inv_of_mul_eq_one_left
          rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
        have := key (orderOf a - 1) c hc
        rwa [h1] at this }
  have hN : ∀ g : G, g ∈ N ↔ ∀ c ∈ C, g * c * g⁻¹ ∈ C := fun g => Iff.rfl
  let C' : Subgroup N := C.subgroupOf N
  haveI hC' : C'.Normal := ⟨fun n hn g => by
    simp only [C', Subgroup.mem_subgroupOf] at hn ⊢
    exact (hN g).1 g.2 _ hn⟩
  let P : Sylow p (N ⧸ C') := Classical.arbitrary _
  let H' : Subgroup N := (P : Subgroup (N ⧸ C')).comap (QuotientGroup.mk' C')
  refine ⟨H'.map N.subtype, ?_, ?_, ?_, ?_⟩
  · intro c hc
    have hcN : c ∈ N := (hN c).2 fun d hd => C.mul_mem (C.mul_mem hc hd) (C.inv_mem hc)
    refine ⟨⟨c, hcN⟩, ?_, rfl⟩
    have : QuotientGroup.mk' C' ⟨c, hcN⟩ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hc
    change QuotientGroup.mk' C' ⟨c, hcN⟩ ∈ (P : Subgroup (N ⧸ C'))
    rw [this]
    exact one_mem _
  · rintro _ ⟨h, -, rfl⟩
    exact (hN h).1 h.2
  · rintro _ ⟨h, hh, rfl⟩
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨QuotientGroup.mk' C' h, hh⟩
    refine ⟨k, ?_⟩
    have h2 : QuotientGroup.mk' C' (h ^ p ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h2
  · intro N' hN'
    obtain rfl : N' = N := by
      ext g
      rw [hN', hN]
    have h1 : (H'.map N.subtype).subgroupOf N = H' :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective H'
    rw [Subgroup.relIndex, h1]
    have h2 : H'.index = (P : Subgroup (N ⧸ C')).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective C')
    rw [h2]
    exact P.not_dvd_index

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsWeightIdempotent
section
namespace GlobalTheory


open Finset in
theorem exists_weight_idempotent (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G]
    (V : Type) [AddCommGroup V] [Module L V] (ρ : Representation L G V) (B T : Subgroup G)
    (lam : B →* Lˣ) (v : V) (hB : B.Normal) (hv : v ≠ 0)
    (hlam : ∀ b : B, ρ b v = (lam b : L) • v)
    (hT : ∀ g : G, g ∈ T ↔ ∀ b b' : B, (b' : G) = g⁻¹ * b * g → lam b' = lam b) :
    ∃ e : Module.End L V, e ≠ 0 ∧ e * e = e ∧ (∀ b : B, ρ b * e = (lam b : L) • e) ∧
      (∀ t ∈ T, ρ t * e = e * ρ t) ∧ ∀ g ∉ T, e * ρ g * e = 0 := by
  classical
  letI : Fintype B := Fintype.ofFinite B
  have hc : (Fintype.card B : L) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set s : Module.End L V := ∑ b : B, (((lam b)⁻¹ : Lˣ) : L) • ρ b with hs
  set e : Module.End L V := (Fintype.card B : L)⁻¹ • s with he
  have h1 : ∀ b : B, ρ b * s = (lam b : L) • s := by
    intro b
    rw [hs, Finset.mul_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft b) _ _ ?_
    intro c
    simp only [Equiv.coe_mulLeft, map_mul, Subgroup.coe_mul, smul_smul, mul_smul_comm]
    congr 1
    simp [mul_comm]
  have h1e : ∀ b : B, ρ b * e = (lam b : L) • e := by
    intro b
    rw [he, mul_smul_comm, h1, smul_comm]
  have h2 : ∀ f : Module.End L V, (∀ b : B, ρ b * f = (lam b : L) • f) → e * f = f := by
    intro f hf
    rw [he, smul_mul_assoc, hs, Finset.sum_mul]
    have : ∀ b : B, ((((lam b)⁻¹ : Lˣ) : L) • ρ b) * f = f := by
      intro b
      rw [smul_mul_assoc, hf, smul_smul]
      simp
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul L, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hev : e v = v := by
    rw [he, hs]
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, hlam, smul_smul, Units.inv_mul, one_smul,
      Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul L, smul_smul, inv_mul_cancel₀ hc, one_smul]
  let κ : G → B ≃* B := fun g => (MulAut.conjNormal (H := B) g⁻¹)
  have hκ : ∀ g (b : B), (κ g b : G) = g⁻¹ * b * g := by
    intro g b
    simp [κ]
  have hcomm : ∀ g (b : B), ρ b * ρ g = ρ g * ρ (κ g b) := by
    intro g b
    rw [← map_mul, ← map_mul, hκ]
    congr 1
    group
  refine ⟨e, ?_, h2 e h1e, h1e, ?_, ?_⟩
  · intro h
    rw [h] at hev
    exact hv hev.symm
  · intro t ht
    have ht' := (hT t).1 ht
    rw [he, mul_smul_comm, smul_mul_assoc, hs, Finset.mul_sum, Finset.sum_mul]
    congr 1
    symm
    refine Fintype.sum_equiv (κ t).toEquiv _ _ ?_
    intro b
    have := ht' b (κ t b) (hκ t b)
    rw [smul_mul_assoc, mul_smul_comm, hcomm, ← this]
    rfl
  · intro g hg
    let f : B →* L := (Units.coeHom L).comp (lam⁻¹ * lam.comp (κ g).toMonoidHom)
    have hf : f ≠ 1 := by
      intro h
      apply hg
      rw [hT]
      intro b b' hb
      have hb' : b' = κ g b := Subtype.ext (by rw [hb, hκ])
      have h3 : f b = 1 := by rw [h]; rfl
      have h4 : (lam b)⁻¹ * lam (κ g b) = 1 := Units.ext h3
      rw [hb']
      exact (inv_mul_eq_one.mp h4).symm
    have h0 := sum_hom_units_eq_zero f hf
    have : s * ρ g * e = 0 := by
      rw [hs, Finset.sum_mul, Finset.sum_mul]
      have : ∀ b : B, ((((lam b)⁻¹ : Lˣ) : L) • ρ b) * ρ g * e = f b • (ρ g * e) := by
        intro b
        rw [smul_mul_assoc, smul_mul_assoc, hcomm, mul_assoc, h1e, mul_smul_comm, smul_smul]
        rfl
      simp only [this]
      rw [← Finset.sum_smul, h0, zero_smul]
    calc e * ρ g * e = (Fintype.card B : L)⁻¹ • (s * ρ g * e) := by
          rw [← smul_mul_assoc, ← smul_mul_assoc]
      _ = 0 := by rw [this, smul_zero]

end GlobalTheory
end

