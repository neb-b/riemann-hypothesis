module

public import Development.WeilBound.ThetaLifts.SphericalLattices.Bundle0005
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0086

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.SphericalLattices.MemIntGL
section
noncomputable section

namespace PositivityTheory.Sph.M2.GenB

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L} {m : ℕ}

theorem mem_PW {g : GL (Fin m ⊕ Fin m) L} : g ∈ PW L c m ↔
    Iso c (Wm L (Fin m)) (Wm L (Fin m)) (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) ∧
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).toBlocks₂₁ = 0 := by
  change g ∈ GW L c m ⊓ GlobalTheory.LGrp.blockQ L (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m)) ↔ _
  rw [Subgroup.mem_inf]
  apply and_congr Iff.rfl
  change (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).BlockTriangular
    (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m)) ↔ _
  constructor
  · intro h
    ext i j
    exact h (show GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m) (Sum.inl j) <
      GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m) (Sum.inr i) from Nat.zero_lt_one)
  · intro h i j hij
    cases i with
    | inl i => exact absurd hij (Nat.not_lt_zero _)
    | inr i =>
      cases j with
      | inl j => exact congrFun (congrFun h i) j
      | inr j => exact absurd hij (lt_irrefl 1)

theorem lev_val (t : GL (Fin m) L) :
    ((lev L c m t : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) = levM L c m t := rfl

theorem lev_mem (hc : ∀ x, c (c x) = x) (t : GL (Fin m) L) : lev L c m t ∈ PW L c m := by
  rw [mem_PW, lev_val]
  refine ⟨?_, rfl⟩
  have h1 : (↑t : Matrix (Fin m) (Fin m) L)ᵀ * (↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
  have h2 : (↑t⁻¹ : Matrix (Fin m) (Fin m) L).map c * (↑t : Matrix (Fin m) (Fin m) L).map c = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero c) (map_one c)]
  have h3 : ((↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ.map c).map c = (↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ := by
    ext i j
    simp [hc]
  have h4 : ((↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ.map c)ᵀ = (↑t⁻¹ : Matrix (Fin m) (Fin m) L).map c := by
    rw [Matrix.transpose_map, Matrix.transpose_transpose]
  have hlev : levM L c m t = fromBlocks (↑t : Matrix (Fin m) (Fin m) L) 0 0
      ((↑t⁻¹ : Matrix (Fin m) (Fin m) L)ᵀ.map c) := rfl
  have hW : Wm L (Fin m) = fromBlocks (0 : Matrix (Fin m) (Fin m) L) 1 1 0 := rfl
  change (levM L c m t)ᵀ * Wm L (Fin m) * (levM L c m t).map c = Wm L (Fin m)
  rw [hlev, hW]
  simp only [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, h3, h4,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero c), Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, h1, h2]

def un (X : Matrix (Fin m) (Fin m) L) : GL (Fin m ⊕ Fin m) L :=
  ⟨fromBlocks 1 X 0 1, fromBlocks 1 (-X) 0 1, by simp [fromBlocks_multiply, fromBlocks_one],
    by simp [fromBlocks_multiply, fromBlocks_one]⟩

theorem un_val (X : Matrix (Fin m) (Fin m) L) :
    ((un X : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) = fromBlocks 1 X 0 1 := rfl

theorem un_mem {X : Matrix (Fin m) (Fin m) L} (h : X.map c = -Xᵀ) : un X ∈ PW L c m := by
  rw [mem_PW, un_val]
  refine ⟨?_, rfl⟩
  have hW : Wm L (Fin m) = fromBlocks (0 : Matrix (Fin m) (Fin m) L) 1 1 0 := rfl
  change (fromBlocks 1 X 0 1)ᵀ * Wm L (Fin m) * (fromBlocks 1 X 0 1).map c = Wm L (Fin m)
  rw [hW]
  simp only [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, h,
    Matrix.transpose_zero, Matrix.transpose_one, Matrix.map_zero _ (map_zero c),
    Matrix.map_one _ (map_zero c) (map_one c), Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.mul_neg, neg_add_cancel, neg_zero]

theorem un_mul (X Y : Matrix (Fin m) (Fin m) L) : un X * un Y = un (X + Y) := by
  ext1
  rw [Units.val_mul, un_val, un_val, un_val, fromBlocks_multiply]
  simp [add_comm]

theorem zW_val (x : Lˣ) : ((zW L m x : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) =
    fromBlocks ((x : L) • 1) 0 0 (((x⁻¹ : Lˣ) : L) • 1) := rfl

theorem zW_un (x : Lˣ) (X : Matrix (Fin m) (Fin m) L) :
    zW L m x * un X = un (((x : L) * x) • X) * zW L m x := by
  have hx : (↑x⁻¹ : L) * (↑x * ↑x) = ↑x := by rw [← mul_assoc, Units.inv_mul, one_mul]
  ext1
  simp only [Units.val_mul, zW_val, un_val, fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    smul_zero, hx]

theorem decomp (hc : ∀ x, c (c x) = x) {p : GL (Fin m ⊕ Fin m) L} (hp : p ∈ PW L c m) :
    ∃ (t : GL (Fin m) L) (X : Matrix (Fin m) (Fin m) L), X.map c = -Xᵀ ∧ p = lev L c m t * un X := by
  rw [mem_PW] at hp
  obtain ⟨hiso, h21⟩ := hp
  set P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L := (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) with hP
  have hPb : P = fromBlocks P.toBlocks₁₁ P.toBlocks₁₂ 0 P.toBlocks₂₂ := by
    rw [← h21]
    exact (Matrix.fromBlocks_toBlocks P).symm
  have hW : Wm L (Fin m) = fromBlocks (0 : Matrix (Fin m) (Fin m) L) 1 1 0 := rfl
  change Pᵀ * Wm L (Fin m) * P.map c = Wm L (Fin m) at hiso
  rw [hPb, hW] at hiso
  simp only [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero c), Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.fromBlocks_inj] at hiso
  obtain ⟨-, h12, h21', h22⟩ := hiso
  set A := P.toBlocks₁₁ with hA
  set B := P.toBlocks₁₂ with hB
  set D := P.toBlocks₂₂ with hD
  have hDD : (D.map c).map c = D := by
    ext i j
    simp [hc]
  have hinv1 : (D.map c)ᵀ * A = 1 := by
    have := congrArg Matrix.transpose h12
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have hinv2 : A * (D.map c)ᵀ = 1 := by
    first
    | exact mul_eq_one_comm.mp hinv1
    | exact Matrix.mul_eq_one_comm.mp hinv1
    | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) hinv1
  refine ⟨⟨A, (D.map c)ᵀ, hinv2, hinv1⟩, (D.map c)ᵀ * B, ?_, ?_⟩
  · rw [Matrix.map_mul, Matrix.transpose_map, hDD, Matrix.transpose_mul, Matrix.transpose_transpose]
    exact eq_neg_of_add_eq_zero_left h22
  · ext1
    rw [Units.val_mul, lev_val, un_val]
    change P = _
    rw [hPb]
    change _ = fromBlocks (A : Matrix (Fin m) (Fin m) L) 0 0
      ((((⟨A, (D.map c)ᵀ, hinv2, hinv1⟩ : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L)ᵀ.map c) * _
    simp only [Units.inv_mk, Units.val_mk, Matrix.transpose_transpose, hDD, fromBlocks_multiply,
      Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add,
      ← Matrix.mul_assoc, hinv2]

theorem mem_IntGL {g : GL (Fin m ⊕ Fin m) L}
    (h1 : ∀ i j, (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) i j ∈ intL L)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) i j ∈ intL L) :
    g ∈ IntGL L m := by
  change g ∈ (Matrix.GeneralLinearGroup.map (intL L).subtype).range
  rw [MonoidHom.mem_range]
  let A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (intL L) :=
    Matrix.of fun a b => ⟨(g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) a b, h1 a b⟩
  let B : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (intL L) :=
    Matrix.of fun a b => ⟨((g⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) a b, h2 a b⟩
  have hinj : ∀ M N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (intL L),
      M.map (intL L).subtype = N.map (intL L).subtype → M = N :=
    fun M N h => Matrix.map_injective Subtype.val_injective h
  have hA : A.map (intL L).subtype = (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) := by
    ext a b; rfl
  have hB : B.map (intL L).subtype =
      ((g⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) := by
    ext a b; rfl
  have hAB : A * B = 1 := hinj _ _ (by
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Units.mul_inv g)
  have hBA : B * A = 1 := hinj _ _ (by
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Units.inv_mul g)
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  exact hA

end PositivityTheory.Sph.M2.GenB

end
end

-- bundled from Development.WeilBound.ThetaLifts.SphericalLattices.MemRangeOfEntries
section
noncomputable section

namespace PositivityTheory.Sph.M2

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

namespace Comm

section Abs

variable {L : Type} [Field L] (O : Subring L) {n : Type} [Fintype n] [DecidableEq n]

theorem mem_range_of_entries (g : GL n L) (h1 : ∀ i j, (g : Matrix n n L) i j ∈ O)
    (h2 : ∀ i j, ((g⁻¹ : GL n L) : Matrix n n L) i j ∈ O) :
    g ∈ (Matrix.GeneralLinearGroup.map (n := n) O.subtype).range := by
  let A : Matrix n n O := fun i j => ⟨_, h1 i j⟩
  let B : Matrix n n O := fun i j => ⟨_, h2 i j⟩
  have hA : O.subtype.mapMatrix A = (g : Matrix n n L) := by ext i j; rfl
  have hB : O.subtype.mapMatrix B = ((g⁻¹ : GL n L) : Matrix n n L) := by ext i j; rfl
  have hinj : Function.Injective (O.subtype.mapMatrix : Matrix n n O →+* Matrix n n L) := by
    intro X Y h
    ext i j
    exact congrFun (congrFun h i) j
  refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, ?_⟩
  · rw [map_mul, hA, hB, map_one]; exact Units.mul_inv g
  · rw [map_mul, hA, hB, map_one]; exact Units.inv_mul g
  · ext1; exact hA

theorem entries_conj (a : L) (A B X : Matrix n n L) (hAB : A * B = 1)
    (h : ∀ i j k l, a * (A i j * B k l) ∈ O) (hX : ∀ i j, ∃ y ∈ O, (X - 1) i j = a * y) (i j : n) :
    (A * X * B) i j ∈ O := by
  have e : A * X * B = 1 + A * (X - 1) * B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAB]; abel
  rw [e, Matrix.add_apply]
  refine O.add_mem ?_ ?_
  · rw [Matrix.one_apply]; split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  · rw [Matrix.mul_apply]
    refine O.sum_mem fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine O.sum_mem fun k _ => ?_
    obtain ⟨y, hy, e⟩ := hX k l
    rw [e]
    have : A i k * (a * y) * B l j = a * (A i k * B l j) * y := by ring
    rw [this]
    exact O.mul_mem (h _ _ _ _) hy

theorem ker_entries (a : O) (k : GL n O)
    (hk : k ∈ (Matrix.GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk (Ideal.span {a}))).ker) (i j : n) :
    ∃ y ∈ O, (((Matrix.GeneralLinearGroup.map (n := n) O.subtype k : GL n L) : Matrix n n L) - 1) i j = (a : L) * y := by
  have h1 : Ideal.Quotient.mk (Ideal.span {a}) ((k : Matrix n n O) i j) =
      Ideal.Quotient.mk (Ideal.span {a}) ((1 : Matrix n n O) i j) := by
    have := congrArg (fun g : GL n (O ⧸ Ideal.span {a}) => (g : Matrix n n (O ⧸ Ideal.span {a})) i j)
      (MonoidHom.mem_ker.1 hk)
    refine Eq.trans this ?_
    simp only [Units.val_one, Matrix.one_apply]
    split_ifs <;> simp
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h1
  obtain ⟨y, hy⟩ := h1
  refine ⟨y, y.2, ?_⟩
  have h2 := congrArg O.subtype hy
  rw [map_sub, map_mul] at h2
  refine Eq.trans ?_ h2
  rw [Matrix.sub_apply]
  congr 1
  simp only [Matrix.one_apply]
  split_ifs <;> simp

theorem ker_le_conj (a : O) (p : GL n L)
    (h : ∀ i j k l, (a : L) * (((p⁻¹ : GL n L) : Matrix n n L) i j * (p : Matrix n n L) k l) ∈ O) :
    ((Matrix.GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk (Ideal.span {a}))).ker).map
        (Matrix.GeneralLinearGroup.map (n := n) O.subtype) ≤
      ((Matrix.GeneralLinearGroup.map (n := n) O.subtype).range).map (MulAut.conj p).toMonoidHom := by
  rintro _ ⟨k, hk, rfl⟩
  refine ⟨p⁻¹ * Matrix.GeneralLinearGroup.map (n := n) O.subtype k * p, ?_, ?_⟩
  · refine mem_range_of_entries O _ ?_ ?_
    · intro i j
      rw [Units.val_mul, Units.val_mul]
      exact entries_conj O a _ _ _ (Units.inv_mul p) h (ker_entries O a k hk) i j
    · intro i j
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← mul_assoc, ← map_inv, Units.val_mul, Units.val_mul]
      exact entries_conj O a _ _ _ (Units.inv_mul p) h (ker_entries O a k⁻¹ (Subgroup.inv_mem _ hk)) i j
  · simp [mul_assoc]

theorem relIndex_conj_range (a : O) [Finite (O ⧸ Ideal.span {a})] (p : GL n L)
    (h : ∀ i j k l, (a : L) * (((p⁻¹ : GL n L) : Matrix n n L) i j * (p : Matrix n n L) k l) ∈ O) :
    (((Matrix.GeneralLinearGroup.map (n := n) O.subtype).range).map (MulAut.conj p).toMonoidHom).relIndex
      (Matrix.GeneralLinearGroup.map (n := n) O.subtype).range ≠ 0 := by
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := n) O.subtype) := by
    intro X Y h
    ext i j
    exact congrArg (fun g : GL n L => (g : Matrix n n L) i j) h
  have h1 : (((Matrix.GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk (Ideal.span {a}))).ker).map
        (Matrix.GeneralLinearGroup.map (n := n) O.subtype)).relIndex
        (Matrix.GeneralLinearGroup.map (n := n) O.subtype).range ≠ 0 := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hinj, Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  intro h0
  exact h1 (Subgroup.relIndex_eq_zero_of_le_left (ker_le_conj O a p h) h0)

end Abs

section Grp

variable {G : Type} [Group G]

theorem conj_inf (P K : Subgroup G) (p : G) (hp : p ∈ P) :
    (P ⊓ K).map (MulAut.conj p).toMonoidHom = P ⊓ K.map (MulAut.conj p).toMonoidHom := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨P.mul_mem (P.mul_mem hp h1) (P.inv_mem hp), ⟨x, h2, rfl⟩⟩
  · rintro _ ⟨h1, x, h2, rfl⟩
    refine ⟨x, ⟨?_, h2⟩, rfl⟩
    have h3 : p⁻¹ * (p * x * p⁻¹) * p ∈ P := P.mul_mem (P.mul_mem (P.inv_mem hp) h1) hp
    simpa [mul_assoc] using h3

theorem relIndex_conj_inf (P K : Subgroup G) (p : G) (hp : p ∈ P)
    (h : (K.map (MulAut.conj p).toMonoidHom).relIndex K ≠ 0) :
    ((P ⊓ K).map (MulAut.conj p).toMonoidHom).relIndex (P ⊓ K) ≠ 0 := by
  rw [conj_inf P K p hp, inf_comm P, inf_comm P]
  exact Subgroup.relIndex_inter_ne_zero h P

theorem relIndex_conj_swap (K : Subgroup G) (p : G)
    (h : (K.map (MulAut.conj p⁻¹).toMonoidHom).relIndex K ≠ 0) :
    K.relIndex (K.map (MulAut.conj p).toMonoidHom) ≠ 0 := by
  rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj p).toMonoidHom) _ _ (MulAut.conj p).injective,
    Subgroup.map_map] at h
  have e : (MulAut.conj p).toMonoidHom.comp (MulAut.conj p⁻¹).toMonoidHom = MonoidHom.id G := by
    ext x; simp [mul_assoc]
  rwa [e, Subgroup.map_id] at h

end Grp

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_intL (x : L) : x ∈ intL L ↔ Valued.v x ≤ (1 : WithZero (Multiplicative ℤ)) := Iff.rfl

theorem eventually_int (ϖ : L)
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) (x : L) :
    ∀ᶠ N : ℕ in Filter.atTop, ϖ ^ N * x ∈ intL L := by
  by_cases hx : Valued.v x = (0 : WithZero (Multiplicative ℤ))
  · refine Filter.Eventually.of_forall fun N => ?_
    rw [mem_intL, map_mul, hx, mul_zero]; exact zero_le_one
  · obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 hx
    refine Filter.eventually_atTop.2 ⟨(Multiplicative.toAdd u).toNat, fun N hN => ?_⟩
    rw [mem_intL, map_mul, map_pow, hv, ← hu, ← WithZero.coe_pow, ← WithZero.coe_mul, ← WithZero.coe_one,
      WithZero.coe_le_coe, ← Multiplicative.toAdd_le]
    simp only [toAdd_mul, toAdd_pow, toAdd_ofAdd, toAdd_one, smul_neg, nsmul_eq_mul, mul_one]
    omega

theorem le_of_lt_one (ϖ : L)
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) (x : L)
    (hx : Valued.v x < (1 : WithZero (Multiplicative ℤ))) : x / ϖ ∈ intL L := by
  by_cases h0 : Valued.v x = (0 : WithZero (Multiplicative ℤ))
  · rw [mem_intL, map_div₀, h0, zero_div]; exact zero_le_one
  · obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 h0
    rw [← hu, ← WithZero.coe_one, WithZero.coe_lt_coe, ← Multiplicative.toAdd_lt] at hx
    rw [mem_intL, map_div₀, hv, ← hu, ← WithZero.coe_div, ← WithZero.coe_one,
      WithZero.coe_le_coe, ← Multiplicative.toAdd_le]
    simp only [toAdd_div, toAdd_ofAdd, toAdd_one] at hx ⊢
    omega

theorem finite_quot (ϖ : L) (c : L →+* L) (q : ℕ) (h : IsUnramInv ϖ c q) :
    ∃ a : intL L, (a : L) = ϖ ∧ ∀ N : ℕ, Finite (intL L ⧸ Ideal.span {a ^ N}) := by
  obtain ⟨-, -, -, hv, -, hq, hc⟩ := h
  have hϖ : ϖ ∈ intL L := by
    rw [mem_intL, hv, ← WithZero.coe_one, WithZero.coe_le_coe, ← Multiplicative.toAdd_le]; simp
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact WithZero.zero_ne_coe hv
  refine ⟨⟨ϖ, hϖ⟩, rfl, fun N => ?_⟩
  let M : Ideal (intL L) :=
    IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hM : Finite (intL L ⧸ M) := by
    have : Nat.card (intL L ⧸ M) = q ^ 2 := hc
    exact Nat.finite_of_card_ne_zero (by rw [this]; positivity)
  have hle : M ≤ Ideal.span {(⟨ϖ, hϖ⟩ : intL L)} := by
    intro x hx
    have hx' : Valued.v (x : L) < (1 : WithZero (Multiplicative ℤ)) :=
      (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))) (a := x)).1 hx
    rw [Ideal.mem_span_singleton]
    refine ⟨⟨_, le_of_lt_one ϖ hv x hx'⟩, Subtype.ext ?_⟩
    show (x : L) = ϖ * ((x : L) / ϖ)
    field_simp
  have hF : Finite (intL L ⧸ Ideal.span {(⟨ϖ, hϖ⟩ : intL L)}) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)
  rw [← Ideal.span_singleton_pow]
  exact Ideal.finite_quotient_pow ⟨{⟨ϖ, hϖ⟩}, by simp⟩ N

theorem relIndex_intGL (ϖ : L) (c : L →+* L) (q : ℕ) (h : IsUnramInv ϖ c q) (m : ℕ) (p : GL (Fin m ⊕ Fin m) L) :
    ((IntGL L m).map (MulAut.conj p).toMonoidHom).relIndex (IntGL L m) ≠ 0 := by
  obtain ⟨a, ha, hF⟩ := finite_quot ϖ c q h
  have hev : ∀ᶠ N : ℕ in Filter.atTop, ∀ i j k l,
      ϖ ^ N * (((p⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) i j *
        (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) k l) ∈ intL L := by
    simp only [Filter.eventually_all]
    intro i j k l
    exact eventually_int ϖ h.2.2.2.1 _
  obtain ⟨N, hN⟩ := hev.exists
  haveI := hF N
  refine relIndex_conj_range (intL L) (a ^ N) p ?_
  rw [SubmonoidClass.coe_pow, ha]
  exact hN

theorem KPW_eq (c : L →+* L) (m : ℕ) : KPW L c m = PW L c m ⊓ IntGL L m := by
  show PW L c m ⊓ (GW L c m ⊓ IntGL L m) = _
  have hle : PW L c m ≤ GW L c m := inf_le_left
  rw [← inf_assoc, inf_eq_left.2 hle]

end Val

end Comm

theorem locComm : LocCommSt := by
  intro L _ _ ϖ c q h m p hp
  rw [Comm.KPW_eq]
  exact ⟨Comm.relIndex_conj_inf _ _ p hp (Comm.relIndex_intGL ϖ c q h m p),
    Comm.relIndex_conj_swap _ p
      (Comm.relIndex_conj_inf _ _ p⁻¹ (Subgroup.inv_mem _ hp) (Comm.relIndex_intGL ϖ c q h m p⁻¹))⟩

end PositivityTheory.Sph.M2

end
end

-- bundled from Development.WeilBound.ThetaLifts.SphericalLattices.RelIndexTransport
section
noncomputable section

namespace PositivityTheory.Sph.M2

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  PositivityTheory.ThK PositivityTheory.ThKH.Iwas MeasureTheory GlobalTheory.Doubling

theorem relIndex_transport {G H : Type} [Group G] [Group H] (U : Subgroup G) (Φ : G →* H)
    (hinj : ∀ g ∈ U, ∀ g' ∈ U, Φ g = Φ g' → g = g') {A B : Subgroup G} (hA : A ≤ U) (hB : B ≤ U) :
    (A.map Φ).relIndex (B.map Φ) = A.relIndex B := by
  have hφ : Function.Injective (Φ.comp U.subtype) := fun x y e => Subtype.ext (hinj _ x.2 _ y.2 e)
  have e : ∀ C : Subgroup G, C ≤ U → (C.subgroupOf U).map (Φ.comp U.subtype) = C.map Φ := fun C hC => by
    rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left hC]
  rw [← e A hA, ← e B hB, Subgroup.relIndex_map_map_of_injective _ _ hφ, Subgroup.relIndex_subgroupOf hB]

theorem map_conj_map {G H : Type} [Group G] [Group H] (Φ : G →* H) (g : G) (A : Subgroup G) :
    (A.map (MulAut.conj g).toMonoidHom).map Φ = (A.map Φ).map (MulAut.conj (Φ g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

theorem modSt_of (hC : ChartSt) (hL : LocModSt) : PositivityTheory.Sph.ModSt := by
  intro F E _ _ _ _ _ σ d B W r s hB hW v w hw _ m Cy hLag hAd p hp t ht u hu
  obtain rfl : d = m + m := hLag.rank.trans (two_mul m)
  have hσ := hB.cm
  have h : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw h
  obtain ⟨ϖ, hU⟩ := exists_isUnramInv hσ hw hc
  obtain ⟨Φ, hG, hinj, hsurj, hK, hP, hdet⟩ := hC F E σ B r s m W hB hW v w hw h c hc Cy hLag
  set KP := PositivityTheory.Sph.PSub σ W v Cy ⊓ KSub σ W v with hKP
  have hKPU : KP ≤ USub σ W v := fun g hg => (hg.2 : g ∈ KAt σ W v).1
  have hpU : p ∈ USub σ W v := (hp.1 : p ∈ PAt σ W v Cy).1
  have himg : KP.map Φ = KPW (w.adicCompletion E) c m := by
    ext M
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hgU := hKPU hg
      exact ⟨(hP g hgU).1 hg.1, hG g, (hK g hgU).1 hg.2⟩
    · rintro ⟨hM1, hM2, hM3⟩
      obtain ⟨g, hgU, rfl⟩ := hsurj _ hM2
      exact ⟨g, ⟨(hP g hgU).2 hM1, (hK g hgU).2 hM3⟩, rfl⟩
  have hconj : ∀ g ∈ USub σ W v, KP.map (MulAut.conj g).toMonoidHom ≤ USub σ W v := fun g hg => by
    rintro _ ⟨k, hk, rfl⟩
    exact (USub σ W v).mul_mem ((USub σ W v).mul_mem hg (hKPU hk)) ((USub σ W v).inv_mem hg)
  have tr : ∀ g ∈ USub σ W v, (KP.map (MulAut.conj g).toMonoidHom).relIndex KP =
      ((KPW (w.adicCompletion E) c m).map (MulAut.conj (Φ g)).toMonoidHom).relIndex (KPW (w.adicCompletion E) c m) :=
    fun g hg => by
      rw [← relIndex_transport (USub σ W v) Φ hinj (hconj g hg) hKPU, map_conj_map, himg]
  have hPW : Φ p ∈ PW (w.adicCompletion E) c m := (hP p hpU).1 hp
  have key := hL (w.adicCompletion E) ϖ c (Formalism.UG.qV F v) hU m (Φ p) hPW
  rw [← map_inv, ← tr p⁻¹ ((USub σ W v).inv_mem hpU), ← tr p hpU, hdet p hp t ht] at key
  rw [key]
  congr 1
  have h21 : (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).toBlocks₂₁ = 0 :=
    GlobalTheory.LGrp.mem_blockQ_two.1 hPW.2
  have hdetΦ : (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).det =
      (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).toBlocks₁₁.det *
        (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).toBlocks₂₂.det := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)), h21]
    exact Matrix.det_fromBlocks_zero₂₁ _ _ _
  have hne : piE h t.det ≠ 0 := by
    rw [← hdet p hp t ht]
    intro h0
    have hu' := (Matrix.isUnit_iff_isUnit_det _).1 (Φ p).isUnit
    rw [hdetΦ, h0, zero_mul] at hu'
    exact not_isUnit_zero hu'
  let x : (Fv F v ⊗[F] E)ˣ := Units.map (complEquiv hw h).symm.toMonoidHom (Units.mk0 _ hne)
  have hx1 : x.1 = (t.map (compFin F E v)).det := by
    change (complEquiv hw h).symm ((complEquiv hw h) (compFin F E v t.det)) = _
    rw [RingEquiv.symm_apply_apply]
    exact RingHom.map_det _ _
  have habs := GlobalTheory.AbsInert.absEv_inert F E σ hσ v w h hw x
  have hm : (((sbClass (Fv F v)).modu u : NNReal) : ℝ) = (absEv F E v x : ℝ) := by
    have e1 := GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v (u : Fv F v) u.ne_zero
    rw [Units.mk0_val] at e1
    change ((distribHaarChar (Fv F v) u : NNReal) : ℝ) = _
    rw [e1, absEv_apply, hx1, ← hu]
  have hx : piE h t.det = toCompl h x.1 := by
    rw [hx1]
    change toCompl h (compFin F E v t.det) = toCompl h (t.map (compFin F E v)).det
    rw [RingHom.map_det]
    rfl
  rw [hm, habs, hx, ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

end PositivityTheory.Sph.M2

end
end

