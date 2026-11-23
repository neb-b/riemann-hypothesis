module

public import Mathlib

@[expose] public section

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm

namespace GlobalTheory.Hk

def lev (N l : ℕ) : Subgroup SL(2, ℤ) := Gamma1 N ⊓ Gamma0 l

def uOp (q : ℕ) (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  (q : ℂ)⁻¹ * ∑ j ∈ Finset.range q, f (ofComplex (((τ : ℂ) + j) / q))

def vOp (q : ℕ) (f : ℍ → ℂ) (τ : ℍ) : ℂ := f (ofComplex ((q : ℂ) * τ))

def IsDia (N l : ℕ) (d : ℤ) (σ : SL(2, ℤ)) : Prop :=
  ((σ 1 0 : ℤ) : ZMod (N * l)) = 0 ∧ ((σ 1 1 : ℤ) : ZMod N) = d

def dia (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) : ℍ → ℂ := f ∣[k] σ

def heckeT (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) : ℍ → ℂ :=
  uOp q f + ((q : ℂ) ^ (k - 1)) • vOp q (f ∣[k] σ)

def coef (f : ℍ → ℂ) (n : ℕ) : ℂ := (qExpansion 1 f).coeff n

def pet (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : ℍ → ℂ) : ℂ :=
  ∑ᶠ γ : SL(2, ℤ) ⧸ Γ, ∫ z in ModularGroup.fd, petersson k f g (γ.out⁻¹ • z)

def pmGrp (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {γ | γ ∈ Γ ∨ -γ ∈ Γ}
  one_mem' := Or.inl Γ.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (Γ.mul_mem ha hb)
    · exact Or.inr (by simpa using Γ.mul_mem ha hb)
    · exact Or.inr (by simpa using Γ.mul_mem ha hb)
    · exact Or.inl (by simpa using Γ.mul_mem ha hb)
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (Γ.inv_mem ha)
    · refine Or.inr ?_
      have h : -a⁻¹ = (-a)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]; simp
      rw [h]; exact Γ.inv_mem ha

theorem le_pmGrp (Γ : Subgroup SL(2, ℤ)) : Γ ≤ pmGrp Γ := fun _ h => Or.inl h

theorem neg_one_mem_pmGrp (Γ : Subgroup SL(2, ℤ)) : -1 ∈ pmGrp Γ :=
  Or.inr (by simpa using Γ.one_mem)

theorem pmGrp_eq_self {Γ : Subgroup SL(2, ℤ)} (h : -1 ∈ Γ) : pmGrp Γ = Γ := by
  apply le_antisymm _ (le_pmGrp Γ)
  rintro γ (hγ | hγ)
  · exact hγ
  · simpa using Γ.mul_mem h hγ

instance pmGrp_finiteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : (pmGrp Γ).FiniteIndex :=
  Subgroup.finiteIndex_of_le (le_pmGrp Γ)

theorem relIndex_pmGrp_of_notMem {Γ : Subgroup SL(2, ℤ)} (h : -1 ∉ Γ) :
    Γ.relIndex (pmGrp Γ) = 2 := by
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨-1, neg_one_mem_pmGrp Γ⟩, ?_⟩
  rintro ⟨b, hb⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, mul_neg, mul_one]
  have hne : ¬ (b ∈ Γ ∧ -b ∈ Γ) := fun ⟨h1, h2⟩ => h (by simpa using Γ.mul_mem h2 (Γ.inv_mem h1))
  rcases hb with hb | hb
  · exact Or.inr ⟨hb, fun h2 => hne ⟨hb, h2⟩⟩
  · exact Or.inl ⟨hb, fun h1 => hne ⟨h1, hb⟩⟩

theorem neg_one_notMem_lev {N : ℕ} (l : ℕ) (hN : 3 ≤ N) : -1 ∉ lev N l := by
  rintro ⟨h, -⟩
  have h1 := ((Gamma1_mem N _).1 h).1
  have h2 : (((-1 : ℤ) : ℤ) : ZMod N) = 1 := by simpa using h1
  have h3 : ((2 : ℕ) : ZMod N) = 0 := by
    push_cast at h2 ⊢
    linear_combination -h2
  rw [ZMod.natCast_eq_zero_iff] at h3
  have := Nat.le_of_dvd two_pos h3
  omega

def petProd (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : ℍ → ℂ) : ℂ :=
  ∑ᶠ γ : SL(2, ℤ) ⧸ pmGrp Γ, ∫ z in ModularGroup.fd, petersson k g f (γ.out⁻¹ • z)

theorem petProd_smul_left (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (c : ℂ) (f g : ℍ → ℂ) :
    petProd Γ k (c • f) g = c * petProd Γ k f g := by
  unfold petProd
  haveI : Fintype (SL(2, ℤ) ⧸ pmGrp Γ) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← integral_const_mul]
  congr 1
  ext z
  simp [petersson]
  ring

theorem petProd_smul_right (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (c : ℂ) (f g : ℍ → ℂ) :
    petProd Γ k f (c • g) = (starRingEnd ℂ) c * petProd Γ k f g := by
  unfold petProd
  haveI : Fintype (SL(2, ℤ) ⧸ pmGrp Γ) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← integral_const_mul]
  congr 1
  ext z
  simp [petersson]
  ring

theorem petProd_level_one (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) {f g : ℍ → ℂ}
    (hf : ∀ γ : SL(2, ℤ), f ∣[k] γ = f) (hg : ∀ γ : SL(2, ℤ), g ∣[k] γ = g) :
    petProd Γ k f g = ((pmGrp Γ).index : ℂ) * ∫ z in ModularGroup.fd, petersson k g f z := by
  unfold petProd
  haveI : Fintype (SL(2, ℤ) ⧸ pmGrp Γ) := Fintype.ofFinite _
  simp only [← petersson_slash_SL, hf, hg]
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Subgroup.index, Nat.card_eq_fintype_card]
  simp

end GlobalTheory.Hk
