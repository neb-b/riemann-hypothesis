module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.GoodXgFin
section
open Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV

section Fin

variable {G : Type} [Group G] [Fintype G]

def gxIrrSet (k : Type) [Field k] : Set (G → k) :=
  {ψ | ∃ (n : ℕ) (ρ : Representation k G (Fin n → k)), ρ.IsIrreducible ∧ ρ.character = ψ}


open Classical in
theorem gx_orth {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {ψ ψ' : G → k}
    (hψ : ψ ∈ gxIrrSet (G := G) k) (hψ' : ψ' ∈ gxIrrSet (G := G) k) :
    (Nat.card G : k)⁻¹ * ∑ g : G, ψ g * ψ' g⁻¹ = if ψ = ψ' then 1 else 0 := by
  classical
  obtain ⟨n, ρ, hρ, rfl⟩ := hψ
  obtain ⟨n', ρ', hρ', rfl⟩ := hψ'
  have := hρ
  have := hρ'
  letI : Invertible (Nat.card G : k) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  rw [Representation.char_orthonormal ρ ρ']
  by_cases h : ρ.character = ρ'.character
  · rw [if_pos h]
    have : Nonempty (ρ'.Equiv ρ) := by

      by_contra hne
      have h1 := Representation.char_orthonormal ρ ρ
      rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at h1
      have h2 := Representation.char_orthonormal ρ ρ'
      rw [if_neg hne] at h2
      rw [← h] at h2
      rw [h2] at h1
      exact zero_ne_one h1
    rw [if_pos this]
  · rw [if_neg h]
    have : ¬ Nonempty (ρ'.Equiv ρ) := fun ⟨φ⟩ => h (Representation.char_iso φ).symm
    rw [if_neg this]

theorem gx_linInd {k : Type} [Field k] [IsAlgClosed k] [CharZero k] :
    LinearIndependent k (fun ψ : gxIrrSet (G := G) k => (ψ : G → k)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hs ψ0 hψ0
  have key : ∀ g : G, ∑ ψ ∈ s, c ψ * (ψ : G → k) g = 0 := by
    intro g
    have := congrFun hs g
    simpa [Finset.sum_apply] using this
  have h3 : ∑ ψ ∈ s, c ψ * ((Nat.card G : k)⁻¹ * ∑ g : G, (ψ : G → k) g * (ψ0 : G → k) g⁻¹) = 0 := by
    have hre : ∑ ψ ∈ s, c ψ * ((Nat.card G : k)⁻¹ * ∑ g : G, (ψ : G → k) g * (ψ0 : G → k) g⁻¹)
        = (Nat.card G : k)⁻¹ * ∑ g : G, (∑ ψ ∈ s, c ψ * (ψ : G → k) g) * (ψ0 : G → k) g⁻¹ := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ψ _ => ?_
      ring
    rw [hre]
    simp [key]
  have h4 : ∀ ψ ∈ s, c ψ * ((Nat.card G : k)⁻¹ * ∑ g : G, (ψ : G → k) g * (ψ0 : G → k) g⁻¹) =
      if ψ = ψ0 then c ψ else 0 := by
    intro ψ _
    rw [gx_orth ψ.2 ψ0.2]
    by_cases h : ψ = ψ0
    · simp [h]
    · have h' : (ψ : G → k) ≠ ψ0 := fun e => h (Subtype.ext e)
      simp [h, h']
  rw [Finset.sum_congr rfl h4, Finset.sum_ite_eq' s ψ0 c] at h3
  simpa [hψ0] using h3

theorem gxIrrSet_finite {k : Type} [Field k] [IsAlgClosed k] [CharZero k] : (gxIrrSet (G := G) k).Finite := Set.finite_coe_iff.1 (gx_linInd (G := G) (k := k)).finite

theorem absIrrChar_finite {K : Type} [Field K] [CharZero K] : {χ : G → K | IsAbsIrrChar χ}.Finite := by
  haveI : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  apply Set.Finite.of_finite_image (f := fun χ : G → K => fun t => algebraMap K (AlgebraicClosure K) (χ t))
  · apply (gxIrrSet_finite (G := G) (k := AlgebraicClosure K)).subset
    rintro _ ⟨χ, ⟨n, ρ, hρ, hχ⟩, rfl⟩
    exact ⟨n, ρ, hρ, funext hχ⟩
  · intro a _ b _ hab
    funext t
    exact (algebraMap K (AlgebraicClosure K)).injective (congrFun hab t)

end Fin

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.LevGSym
section
noncomputable section

open Matrix

namespace Formalism.L2.Col

section SymFrame

def symIdx (k rS i : ℕ) : ℕ := if i < k then i + rS else if i < k + rS then i - k else i

def symIdxInv (k rS i : ℕ) : ℕ := if i < rS then i + k else if i < rS + k then i - rS else i

theorem symIdxInv_symIdx (k rS i : ℕ) : symIdxInv k rS (symIdx k rS i) = i := by
  unfold symIdx symIdxInv
  split_ifs <;> omega

theorem symIdx_symIdxInv (k rS i : ℕ) : symIdx k rS (symIdxInv k rS i) = i := by
  unfold symIdx symIdxInv
  split_ifs <;> omega

theorem symIdx_lt {k rS n i : ℕ} (h : k + rS ≤ n) (hi : i < n) : symIdx k rS i < n := by
  unfold symIdx
  split_ifs <;> omega

theorem symIdxInv_lt {k rS n i : ℕ} (h : k + rS ≤ n) (hi : i < n) : symIdxInv k rS i < n := by
  unfold symIdxInv
  split_ifs <;> omega

def symPerm (n k rS : ℕ) : Equiv.Perm (Fin n) :=
  if h : k + rS ≤ n then
    { toFun := fun i => ⟨symIdx k rS i.val, symIdx_lt h i.2⟩
      invFun := fun i => ⟨symIdxInv k rS i.val, symIdxInv_lt h i.2⟩
      left_inv := fun i => Fin.ext (symIdxInv_symIdx k rS i.val)
      right_inv := fun i => Fin.ext (symIdx_symIdxInv k rS i.val) }
  else Equiv.refl _

theorem symPerm_val {n k rS : ℕ} (h : k + rS ≤ n) (i : Fin n) : (symPerm n k rS i).val = symIdx k rS i.val := by
  rw [symPerm, dif_pos h]
  rfl

theorem symPerm_symm_val {n k rS : ℕ} (h : k + rS ≤ n) (i : Fin n) : ((symPerm n k rS).symm i).val = symIdxInv k rS i.val := by
  rw [symPerm, dif_pos h]
  rfl

variable (κ : Type) [CommRing κ]

def toSymOrd (n k rS : ℕ) : GL (Fin n) κ →* GL (Fin n) κ :=
  (Units.mapEquiv (Matrix.reindexAlgEquiv κ κ (symPerm n k rS)).toMulEquiv).toMonoidHom

variable {κ}

theorem toSymOrd_val (n k rS : ℕ) (M : GL (Fin n) κ) (i j : Fin n) :
    ((toSymOrd κ n k rS M : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i j =
      (M : Matrix (Fin n) (Fin n) κ) ((symPerm n k rS).symm i) ((symPerm n k rS).symm j) := rfl

theorem toSymOrd_val' (n k rS : ℕ) (M : GL (Fin n) κ) (i j : Fin n) :
    ((toSymOrd κ n k rS M : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) (symPerm n k rS i) (symPerm n k rS j) =
      (M : Matrix (Fin n) (Fin n) κ) i j := by
  rw [toSymOrd_val, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

variable (κ)

def HPsymF (n k rS : ℕ) : Subgroup (GL (Fin n) κ) := (HPsym κ n k rS).comap (toSymOrd κ n k rS)

variable {κ}

theorem mem_HPsymF {n k rS : ℕ} {M : GL (Fin n) κ} : M ∈ HPsymF κ n k rS ↔ toSymOrd κ n k rS M ∈ HPsym κ n k rS := Iff.rfl

variable {K : Type} [Field K]

def chiSymF (ψ : AddChar κ K) (n k rS : ℕ) : ↥(HPsymF κ n k rS) →* Kˣ :=
  (chiSym ψ n k rS).comp ((toSymOrd κ n k rS).subgroupComap (HPsym κ n k rS))

theorem chiSymF_apply (ψ : AddChar κ K) (n k rS : ℕ) (M : ↥(HPsymF κ n k rS)) :
    chiSymF ψ n k rS M = chiSym ψ n k rS ⟨toSymOrd κ n k rS M.1, M.2⟩ := rfl

variable (κ)

abbrev HJsym (n k r t j rS : ℕ) (h : r ≤ n) : Subgroup (GL (Fin n) κ) :=
  HPar n κ h (List.replicate j t) (HPsymF κ r k rS)

variable {κ}

def lamJsym (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n k r t j rS : ℕ) (h : r ≤ n) : ↥(HJsym κ n k r t j rS h) →* Kˣ :=
  lamPar h (List.replicate j t) (chiSymF ψ r k rS) χ

variable (κ)

def HXmsym (n k r t m rS : ℕ) (h : r ≤ n) : Subgroup (GL (Fin n) κ) := HJsym κ n k r t m rS h ⊓ fixCol n κ (r + m * t)

variable {κ}

def lamXmsym (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n k r t m rS : ℕ) (h : r ≤ n) : ↥(HXmsym κ n k r t m rS h) →* Kˣ :=
  (lamJsym ψ χ n k r t m rS h).comp (Subgroup.inclusion inf_le_left)

end SymFrame

section SymFrameLemmas

variable {κ : Type} [CommRing κ]

theorem fine_self_lt {n i : ℕ} (h : i < n) : fine n [] i = i := by
  unfold fine
  rw [if_pos h]

theorem mem_HPsymF_iff {n k rS : ℕ} (h : k + rS ≤ n) {M : GL (Fin n) κ} :
    M ∈ HPsymF κ n k rS ↔
      (∀ i j : Fin n, symIdx k rS j.val < symIdx k rS i.val → (M : Matrix (Fin n) (Fin n) κ) i j = 0) ∧
      (∀ i : Fin n, (M : Matrix (Fin n) (Fin n) κ) i i = 1) ∧
      (∀ i j : Fin n, i.val < k → j.val = k + rS → (M : Matrix (Fin n) (Fin n) κ) i j = 0) := by
  rw [mem_HPsymF]
  constructor
  · rintro ⟨⟨hbt, hdiag⟩, hN⟩
    refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hi hj => ?_⟩
    · rw [← toSymOrd_val' n k rS M i j]
      apply hbt
      show fine n [] (symPerm n k rS j).val < fine n [] (symPerm n k rS i).val
      rw [fine_self_lt (symPerm n k rS j).2, fine_self_lt (symPerm n k rS i).2, symPerm_val h, symPerm_val h]
      exact hij
    · rw [← toSymOrd_val' n k rS M i i]
      exact hdiag _ (symPerm n k rS i).2
    · rw [← toSymOrd_val' n k rS M i j]
      apply hN
      · rw [symPerm_val h]; unfold symIdx; split_ifs <;> omega
      · rw [symPerm_val h]; unfold symIdx; split_ifs <;> omega
      · rw [symPerm_val h, hj]; unfold symIdx; split_ifs <;> omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨fun i j hij => ?_, fun i _ => ?_⟩, fun i j hi1 hi2 hj => ?_⟩
    · have hij' : j.val < i.val := by simpa [fine_self_lt j.2, fine_self_lt i.2] using hij
      rw [toSymOrd_val]
      apply h1
      rw [← symPerm_val h ((symPerm n k rS).symm j), ← symPerm_val h ((symPerm n k rS).symm i),
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hij'
    · rw [toSymOrd_val]; exact h2 _
    · rw [toSymOrd_val]
      apply h3
      · rw [symPerm_symm_val h]; unfold symIdxInv; split_ifs <;> omega
      · rw [symPerm_symm_val h, hj]; unfold symIdxInv; split_ifs <;> omega

end SymFrameLemmas

section InsId

def insEquiv (N c k N' : ℕ) (hk : k ≤ N) (hN : N' = N + c) : Fin N' ≃ Fin N ⊕ Fin c where
  toFun a := if h1 : a.val < k then Sum.inl ⟨a.val, by omega⟩ else if h2 : a.val < k + c then Sum.inr ⟨a.val - k, by omega⟩
    else Sum.inl ⟨a.val - c, by omega⟩
  invFun
    | Sum.inl i => ⟨if i.val < k then i.val else i.val + c, by split_ifs <;> omega⟩
    | Sum.inr j => ⟨k + j.val, by omega⟩
  left_inv a := by
    by_cases h1 : a.val < k
    · simp only [dif_pos h1]; apply Fin.ext; simp [h1]
    · by_cases h2 : a.val < k + c
      · simp only [dif_neg h1, dif_pos h2]; apply Fin.ext; simp; omega
      · simp only [dif_neg h1, dif_neg h2]; apply Fin.ext; simp; split_ifs <;> omega
  right_inv x := by
    rcases x with i | j
    · by_cases h : i.val < k
      · simp [h]
      · have h1 : ¬ i.val + c < k := by omega
        have h2 : ¬ i.val + c < k + c := by omega
        simp only [if_neg h, dif_neg h1, dif_neg h2]
        congr 1; apply Fin.ext; simp
    · have h1 : ¬ k + j.val < k := by omega
      have h2 : k + j.val < k + c := by omega
      simp only [dif_neg h1, dif_pos h2]
      congr 1; apply Fin.ext; simp

variable (κ : Type) [CommRing κ]

def blkOneHom (N c : ℕ) : Matrix (Fin N) (Fin N) κ →* Matrix (Fin N ⊕ Fin c) (Fin N ⊕ Fin c) κ where
  toFun A := Matrix.fromBlocks A 0 0 1
  map_one' := Matrix.fromBlocks_one
  map_mul' A B := by rw [Matrix.fromBlocks_multiply]; simp

def insGL (N c k N' : ℕ) (hk : k ≤ N) (hN : N' = N + c) : GL (Fin N) κ →* GL (Fin N') κ :=
  Units.map (((Matrix.reindexAlgEquiv κ κ (insEquiv N c k N' hk hN).symm).toAlgHom.toRingHom.toMonoidHom).comp (blkOneHom κ N c))

variable {κ}

theorem insGL_val (N c k N' : ℕ) (hk : k ≤ N) (hN : N' = N + c) (A : GL (Fin N) κ) (a b : Fin N') :
    ((insGL κ N c k N' hk hN A : GL (Fin N') κ) : Matrix (Fin N') (Fin N') κ) a b =
      Matrix.fromBlocks (A : Matrix (Fin N) (Fin N) κ) 0 0 1 (insEquiv N c k N' hk hN a) (insEquiv N c k N' hk hN b) := rfl

end InsId

section SymNonVac

variable {κ : Type} [CommRing κ]

def elemGL {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : κ) : GL (Fin n) κ :=
  ⟨Matrix.transvection i j c, Matrix.transvection i j (-c),
    (Matrix.transvection_mul_transvection_same i j hij c (-c)).trans (by rw [add_neg_cancel, Matrix.transvection_zero]),
    (Matrix.transvection_mul_transvection_same i j hij (-c) c).trans (by rw [neg_add_cancel, Matrix.transvection_zero])⟩

theorem elemGL_apply {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : κ) (a b : Fin n) :
    ((elemGL i j hij c : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) a b = (1 : Matrix (Fin n) (Fin n) κ) a b + if a = i ∧ b = j then c else 0 := by
  show (Matrix.transvection i j c) a b = _
  rw [Matrix.transvection, Matrix.add_apply]
  congr 1
  by_cases h1 : a = i
  · subst h1
    by_cases h2 : b = j
    · subst h2; simp [Matrix.single_apply]
    · simp [Matrix.single_apply, h2, Ne.symm h2]
  · simp [Matrix.single_apply, h1, Ne.symm h1]

theorem HPsymF_not_le_HU [Nontrivial κ] {n k rS : ℕ} (hn : n = k + 2 * rS + 1) (hk : 1 ≤ k) (hr : 1 ≤ rS) :
    ¬ HPsymF κ n k rS ≤ HU κ n := by
  intro hle
  have hkn : k < n := by omega
  have h0n : 0 < n := by omega
  have hne : (⟨k, hkn⟩ : Fin n) ≠ ⟨0, h0n⟩ := by
    intro e; have := congrArg Fin.val e; simp at this; omega
  have hmem : elemGL (⟨k, hkn⟩ : Fin n) ⟨0, h0n⟩ hne (1 : κ) ∈ HPsymF κ n k rS := by
    rw [mem_HPsymF_iff (by omega)]
    refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hi hj => ?_⟩
    · rw [elemGL_apply]
      have hij' : i ≠ j := fun e => by rw [e] at hij; exact lt_irrefl _ hij
      rw [Matrix.one_apply_ne hij', zero_add, if_neg]
      rintro ⟨rfl, rfl⟩
      simp only [symIdx, Fin.val_mk] at hij
      split_ifs at hij <;> omega
    · rw [elemGL_apply, Matrix.one_apply_eq, if_neg, add_zero]
      rintro ⟨h1, h2⟩
      have := congrArg Fin.val (h1.symm.trans h2)
      simp at this; omega
    · rw [elemGL_apply, Matrix.one_apply_ne, zero_add, if_neg]
      · rintro ⟨h1, -⟩; have := congrArg Fin.val h1; simp at this; omega
      · intro e; have := congrArg Fin.val e; omega
  have hU := hle hmem
  have h1 : ((elemGL (⟨k, hkn⟩ : Fin n) ⟨0, h0n⟩ hne (1 : κ) : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ)
      ⟨k, hkn⟩ ⟨0, h0n⟩ = 0 := by
    apply hU.1
    show fine n [] 0 < fine n [] k
    rw [fine_self_lt h0n, fine_self_lt hkn]; omega
  rw [elemGL_apply, Matrix.one_apply_ne hne, zero_add, if_pos ⟨rfl, rfl⟩] at h1
  exact one_ne_zero h1

end SymNonVac

end Formalism.L2.Col
end
end

