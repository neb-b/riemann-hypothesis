module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0182
public import GroundTheory.Brauer.IsBrauerEquivalentIffNonemptyAlgEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTwistedCentralizerBlockIff
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.CentPar

theorem intertwiner_eq_zero {K : Type} [Field K] {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K)
    (hc : IsCoprime A.charpoly B.charpoly) (hC : C * A = B * C) : C = 0 := by
  first
  | exact @_root_.GlobalTheory.IntertwinerCoprimeCharpoly.main
  | exact _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main
  | (apply _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main ..)

variable {E : Type} [Field E] [NumberField E]

theorem blk_zero_val {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) :
    ((blk h w m 0 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m.1.val 0 0 m.2.val) := by
  have hM : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.mul_zero, Matrix.det_fromBlocks_zero₁₂]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit)
  simp only [blk]
  rw [dite_eq_left hM]
  simp

theorem blk_zero_mul {n a b : ℕ} (h : a + b = n) (w : Pl E) (x y : GLw a w × GLw b w) :
    blk h w (x * y) 0 = blk h w x 0 * blk h w y 0 := by
  apply Units.ext
  rw [Units.val_mul, blk_zero_val, blk_zero_val, blk_zero_val]
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Prod.fst_mul, Prod.snd_mul]

end GlobalTheory.LeviDesc.CentPar


open GlobalTheory.LeviDesc.CentPar in
theorem GlobalTheory.LeviDesc.mem_twistedCentralizer_parabolic_iff : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable →
    ∀ (hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w) (p : GlobalTheory.LeviDesc.parP a n w),
      p ∈ twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) ↔
        ∃ t ∈ twCent (MonoidHom.id _) m, blk h w t 0 = (p : GLw n w) := by
  intro E _ _ n a b h w m hsep hγ p
  have hcop := hsep.isCoprime
  have hmem : p ∈ twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) ↔
      (p : GLw n w) * blk h w m 0 = blk h w m 0 * (p : GLw n w) := by
    show p * _ = _ * MonoidHom.id _ p ↔ _
    rw [MonoidHom.id_apply, Subtype.ext_iff]
    rfl
  rw [hmem]
  constructor
  · intro hc
    set e := finSumFinEquiv.trans (finCongr h) with he
    set g' := Matrix.reindex e.symm e.symm ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hg'
    have hgg : ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.reindex e e g' := by
      simp [hg']
    have hcM := congrArg Units.val hc
    rw [Units.val_mul, Units.val_mul, blk_zero_val, ← he, hgg, ← Matrix.fromBlocks_toBlocks g'] at hcM
    have hc2 := congrArg (Matrix.reindex e.symm e.symm) hcM
    simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix,
      Equiv.symm_comp_self, Matrix.submatrix_id_id, Matrix.fromBlocks_multiply] at hc2
    rw [Matrix.fromBlocks_inj] at hc2
    obtain ⟨h11, h12, h21, h22⟩ := hc2
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h11 h12 h21 h22
    have hC0 : g'.toBlocks₂₁ = 0 := intertwiner_eq_zero _ _ _ hcop h21
    have hB0 : g'.toBlocks₁₂ = 0 := intertwiner_eq_zero _ _ _ hcop.symm h12
    have hg'2 : g' = Matrix.fromBlocks g'.toBlocks₁₁ 0 0 g'.toBlocks₂₂ := by
      rw [← hB0, ← hC0, Matrix.fromBlocks_toBlocks]
    have hdet : IsUnit g'.det := by
      rw [hg', Matrix.det_reindex_self]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (p : GLw n w).isUnit
    rw [hg'2, Matrix.det_fromBlocks_zero₂₁] at hdet
    have hA : IsUnit g'.toBlocks₁₁ := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_left hdet)
    have hD : IsUnit g'.toBlocks₂₂ := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_right hdet)
    refine ⟨(hA.unit, hD.unit), ?_, ?_⟩
    · show (hA.unit, hD.unit) * m = m * MonoidHom.id _ (hA.unit, hD.unit)
      rw [MonoidHom.id_apply]
      refine Prod.ext (Units.ext ?_) (Units.ext ?_)
      · simpa using h11
      · simpa using h22
    · apply Units.ext
      rw [blk_zero_val, ← he, hgg]
      conv_rhs => rw [hg'2]
      rfl
  · rintro ⟨t, ht, hp⟩
    have ht' : t * m = m * t := ht
    rw [← hp, ← blk_zero_mul, ← blk_zero_mul, ht']
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorTwoByTwoTriangularProduct
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush.LowMul

variable {K : Type} [Field K] {n : ℕ}

def Lo (L : Matrix (Fin n) (Fin n) K) : Prop := ∀ i j, i < j → L i j = 0

def AL (E : Fin n → Fin n → Prop) (C : Matrix (Fin n) (Fin n) K) : Prop := ∀ i j, i < j → ¬ E i j → C i j = 0

theorem al_mul {E : Fin n → Fin n → Prop} (hE : ∀ i j k, E k j → k ≤ i → i < j → E i j)
    {L C : Matrix (Fin n) (Fin n) K} (hL : Lo L) (hC : AL E C) : AL E (L * C) := by
  intro i j hij hn
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge i k with h | h
  · rw [hL i k h, zero_mul]
  · rw [hC k j (lt_of_le_of_lt h hij) (fun he => hn (hE i j k he h hij)), mul_zero]

theorem mul_al {E : Fin n → Fin n → Prop} (hE : ∀ i j l, E i l → j ≤ l → i < j → E i j)
    {C R : Matrix (Fin n) (Fin n) K} (hC : AL E C) (hR : Lo R) : AL E (C * R) := by
  intro i j hij hn
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge l j with h | h
  · rw [hR l j h, mul_zero]
  · rw [hC i l (lt_of_lt_of_le hij h) (fun he => hn (hE i j l he h hij)), zero_mul]

theorem diag_mul {E : Fin n → Fin n → Prop} {L C : Matrix (Fin n) (Fin n) K} (hL : Lo L) (hC : AL E C)
    (x : Fin n) (hx : ∀ k, k < x → ¬ E k x) : (L * C) x x = L x x * C x x := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single x fun k hk => ?_
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hC k x h (hx k h), mul_zero]
  · rw [hL x k h, zero_mul]

theorem mul_diag {E : Fin n → Fin n → Prop} {C R : Matrix (Fin n) (Fin n) K} (hC : AL E C) (hR : Lo R)
    (x : Fin n) (hx : ∀ l, x < l → ¬ E x l) : (C * R) x x = C x x * R x x := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single x fun l hl => ?_
  rcases lt_or_gt_of_ne hl with h | h
  · rw [hR l x h, mul_zero]
  · rw [hC x l h (hx l h), zero_mul]

theorem lo_diag_ne {M : Matrix (Fin n) (Fin n) K} (hM : Lo M) (hd : M.det ≠ 0) (i : Fin n) : M i i ≠ 0 := by
  rw [Matrix.det_of_lowerTriangular M (fun i j h => hM i j (OrderDual.toDual_lt_toDual.1 h))] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)

section Pair
variable {a b : Fin n} {L C R : Matrix (Fin n) (Fin n) K}

theorem lower_index_pair_unique (hab : (b : ℕ) = a + 1) : ∀ i j k : Fin n, (k = a ∧ j = b) → k ≤ i → i < j → (i = a ∧ j = b) := by
  rintro i j k ⟨rfl, rfl⟩ h1 h2
  refine ⟨Fin.ext ?_, rfl⟩
  rw [Fin.le_iff_val_le_val] at h1; rw [Fin.lt_iff_val_lt_val] at h2; omega

theorem l_aa (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) a a = L a a * C a a :=
  diag_mul hL hC a fun _ _ e => absurd (congrArg Fin.val e.2) (by omega)

theorem l_ab (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) a b = L a a * C a b := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single a fun k hk => ?_
  have hk' : (k : ℕ) ≠ a := fun h => hk (Fin.ext h)
  rcases lt_or_gt_of_ne hk' with h | h
  · rw [hC k b (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hk e.1), mul_zero]
  · rw [hL a k (Fin.lt_iff_val_lt_val.2 h), zero_mul]

theorem l_ba (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) b a = L b a * C a a + L b b * C b a := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun k ⟨hka, hkb⟩ => ?_
  have hka' : (k : ℕ) ≠ a := fun h => hka (Fin.ext h)
  have hkb' : (k : ℕ) ≠ b := fun h => hkb (Fin.ext h)
  rcases lt_or_gt_of_ne hkb' with h | h
  · rw [hC k a (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hka e.1), mul_zero]
  · rw [hL b k (Fin.lt_iff_val_lt_val.2 h), zero_mul]

theorem l_bb (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) b b = L b a * C a b + L b b * C b b := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun k ⟨hka, hkb⟩ => ?_
  have hka' : (k : ℕ) ≠ a := fun h => hka (Fin.ext h)
  have hkb' : (k : ℕ) ≠ b := fun h => hkb (Fin.ext h)
  rcases lt_or_gt_of_ne hkb' with h | h
  · rw [hC k b h (fun e => hka e.1), mul_zero]
  · rw [hL b k (Fin.lt_iff_val_lt_val.2 h), zero_mul]

theorem r_aa (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) a a = C a a * R a a + C a b * R b a := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun l ⟨hla, hlb⟩ => ?_
  have hla' : (l : ℕ) ≠ a := fun h => hla (Fin.ext h)
  have hlb' : (l : ℕ) ≠ b := fun h => hlb (Fin.ext h)
  rcases lt_or_gt_of_ne hla' with h | h
  · rw [hR l a (Fin.lt_iff_val_lt_val.2 h), mul_zero]
  · rw [hC a l (Fin.lt_iff_val_lt_val.2 h) (fun e => hlb e.2), zero_mul]

theorem r_ab (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) a b = C a b * R b b := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single b fun l hl => ?_
  have hl' : (l : ℕ) ≠ b := fun h => hl (Fin.ext h)
  rcases lt_or_gt_of_ne hl' with h | h
  · rw [hR l b (Fin.lt_iff_val_lt_val.2 h), mul_zero]
  · rw [hC a l (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hl e.2), zero_mul]

theorem r_ba (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) b a = C b a * R a a + C b b * R b a := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun l ⟨hla, hlb⟩ => ?_
  have hla' : (l : ℕ) ≠ a := fun h => hla (Fin.ext h)
  have hlb' : (l : ℕ) ≠ b := fun h => hlb (Fin.ext h)
  rcases lt_or_gt_of_ne hla' with h | h
  · rw [hR l a (Fin.lt_iff_val_lt_val.2 h), mul_zero]
  · rw [hC b l (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hne e.1.symm), zero_mul]

theorem r_bb (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) b b = C b b * R b b :=
  mul_diag hC hR b fun _ _ e => absurd (congrArg Fin.val e.1) (by omega)

end Pair

section Root
variable {ι : Type} {m : ι → ℕ} {τ : ι} {a b : Fin (m τ)}

theorem root_lower_pair_unique_left (hab : (b : ℕ) = a + 1) (σ : ι) : ∀ i j k : Fin (m σ),
    ((⟨σ, k⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) → k ≤ i → i < j →
      ((⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) := by
  rintro i j k ⟨h1, h2⟩ hki hij
  obtain ⟨rfl, hk⟩ := Sigma.mk.inj_iff.1 h1
  obtain rfl := eq_of_heq hk
  obtain rfl := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
  refine ⟨congrArg (Sigma.mk _) (Fin.ext ?_), rfl⟩
  rw [Fin.le_iff_val_le_val] at hki; rw [Fin.lt_iff_val_lt_val] at hij; omega

theorem root_lower_pair_unique_right (hab : (b : ℕ) = a + 1) (σ : ι) : ∀ i j l : Fin (m σ),
    ((⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, l⟩ : Root m) = ⟨τ, b⟩) → j ≤ l → i < j →
      ((⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) := by
  rintro i j l ⟨h1, h2⟩ hjl hij
  obtain ⟨rfl, hk⟩ := Sigma.mk.inj_iff.1 h1
  obtain rfl := eq_of_heq hk
  obtain rfl := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
  refine ⟨rfl, congrArg (Sigma.mk _) (Fin.ext ?_)⟩
  rw [Fin.le_iff_val_le_val] at hjl; rw [Fin.lt_iff_val_lt_val] at hij; omega

end Root

end GlobalTheory.FlagPush.LowMul

namespace GlobalTheory.FlagPush


open LowMul in
theorem almostLow_mul_entries : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ (K : Type) [Field K] (S T C : Mat m K), Par m ⊤ S → Par m ⊤ T → AlmostLow τ a b C → AlmostLow τ a b (S * C * T) ∧ (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → (S * C * T) x.1 x.2 x.2 = S x.1 x.2 x.2 * C x.1 x.2 x.2 * T x.1 x.2 x.2) ∧ (S * C * T) τ a b = S τ a a * C τ a b * T τ b b ∧ minor τ a b (S * C * T) = S τ a a * S τ b b * minor τ a b C * (T τ a a * T τ b b) := by
  intro ι m τ a b hab K _ S T C hS hT hC
  have hSl : ∀ σ, Lo (S σ) := fun σ i j h => (hS σ).2.2.2 i j i.isLt h
  have hTl : ∀ σ, Lo (T σ) := fun σ i j h => (hT σ).2.2.2 i j i.isLt h
  have hCr : ∀ σ, AL (fun i j => (⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) (C σ) :=
    fun σ => hC.2.2 σ
  have hCt : AL (fun i j => i = a ∧ j = b) (C τ) := fun i j h hn =>
    hC.2.2 τ i j h fun e => hn ⟨eq_of_heq (Sigma.mk.inj_iff.1 e.1).2, eq_of_heq (Sigma.mk.inj_iff.1 e.2).2⟩
  have hP : AL (fun i j => i = a ∧ j = b) (S τ * C τ) := al_mul (lower_index_pair_unique hab) (hSl τ) hCt
  have h3 : (S * C * T) τ a b = S τ a a * C τ a b * T τ b b := by
    show (S τ * C τ * T τ) a b = _
    rw [r_ab hab hP (hTl τ), l_ab hab (hSl τ) hCt]
  refine ⟨⟨fun σ => ?_, ?_, fun σ => ?_⟩, fun x hxa hxb => ?_, h3, ?_⟩
  · show (S σ * C σ * T σ).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero (hS.det_ne σ) (hC.1 σ)) (hT.det_ne σ)
  · rw [h3]
    exact mul_ne_zero (mul_ne_zero (lo_diag_ne (hSl τ) (hS.det_ne τ) a) hC.2.1) (lo_diag_ne (hTl τ) (hT.det_ne τ) b)
  · exact mul_al (root_lower_pair_unique_right hab σ) (al_mul (root_lower_pair_unique_left hab σ) (hSl σ) (hCr σ)) (hTl σ)
  · show (S x.1 * C x.1 * T x.1) x.2 x.2 = _
    rw [mul_diag (al_mul (root_lower_pair_unique_left hab x.1) (hSl x.1) (hCr x.1)) (hTl x.1) x.2 (fun _ _ e => hxa e.1),
      diag_mul (hSl x.1) (hCr x.1) x.2 (fun _ _ e => hxb e.2)]
  · show (S τ * C τ * T τ) a a * (S τ * C τ * T τ) b b - (S τ * C τ * T τ) a b * (S τ * C τ * T τ) b a =
      S τ a a * S τ b b * (C τ a a * C τ b b - C τ a b * C τ b a) * (T τ a a * T τ b b)
    rw [r_aa hab hP (hTl τ), r_bb hab hP (hTl τ), r_ab hab hP (hTl τ), r_ba hab hP (hTl τ),
      l_aa hab (hSl τ) hCt, l_bb hab (hSl τ) hCt, l_ab hab (hSl τ) hCt, l_ba hab (hSl τ) hCt]
    ring

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegInvRatioIsNormOfNegRatioIsNorm
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory.PlaneSU.NormSwap

theorem neg_inv_ratio_norm : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (δ : F) (b : Module.Basis (Fin 2) F E), b 0 = 1 → σ (b 1) = -b 1 → b 1 * b 1 = algebraMap F E δ → ∀ f₁ f₂ : F, f₁ ≠ 0 → f₂ ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] (ε : R) (t : R ⊗[F] E), algebraMap R (R ⊗[F] E) ε * (t * sigR R σ t + algebraMap F (R ⊗[F] E) (f₁ / f₂)) = 0 → ∃ p q : R, ε * (algebraMap F R (-(f₂ / f₁)) - (p ^ 2 - algebraMap F R δ * q ^ 2)) = 0 := by
  intro F E _ _ _ σ δ b hb0 hb1 hsq f₁ f₂ hf₁ hf₂ R _ _ ε t hε
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have h0 : B 0 = 1 := by rw [hB, hb0]; rfl
  have h1 : B 1 * B 1 = algebraMap F R δ • B 0 := by
    rw [hB, hB, Algebra.TensorProduct.tmul_mul_tmul, hsq, hb0, Algebra.algebraMap_eq_smul_one (A := E),
      TensorProduct.tmul_smul, one_mul, algebraMap_smul]
  have hs : ∀ (r : R) (e : E), sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := fun r e => rfl
  have key : ∀ x y : R, (x • B 0 + y • B 1) * sigR R σ (x • B 0 + y • B 1) =
      algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
    intro x y
    have e : sigR R σ (x • B 0 + y • B 1) = x • B 0 - y • B 1 := by
      rw [map_add (f := _), hB, hB, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hs, hs, hb1, hb0,
        map_one, TensorProduct.tmul_neg, sub_eq_add_neg]
    rw [e]
    rw [h0] at h1 ⊢
    generalize algebraMap F R δ = d at h1 ⊢
    simp only [Algebra.smul_def, mul_one, map_sub, map_mul, map_pow] at h1 ⊢
    linear_combination (-(algebraMap R (R ⊗[F] E) y) ^ 2) * h1
  have hz := B.sum_repr t
  rw [Fin.sum_univ_two] at hz
  set p₀ := B.repr t 0
  set q₀ := B.repr t 1
  rw [← hz, key, IsScalarTower.algebraMap_apply F R (R ⊗[F] E), ← map_add (f := _), ← map_mul] at hε
  have hinj : Function.Injective (algebraMap R (R ⊗[F] E)) := by
    have := Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := R) (B := E)
      (algebraMap F E).injective
    intro x y hxy
    apply this
    simpa [Algebra.TensorProduct.algebraMap_apply] using hxy
  have h : ε * (p₀ ^ 2 - algebraMap F R δ * q₀ ^ 2 + algebraMap F R (f₁ / f₂)) = 0 :=
    hinj (by rw [hε, map_zero])
  set c := algebraMap F R (f₂ / f₁)
  have hca : c * algebraMap F R (f₁ / f₂) = 1 := by
    rw [← map_mul, div_mul_div_comm, mul_comm f₂ f₁, div_self (mul_ne_zero hf₁ hf₂), map_one]
  refine ⟨c * p₀, c * q₀, ?_⟩
  rw [map_neg]
  linear_combination (-c ^ 2) * h + ε * c * hca

end GlobalTheory.PlaneSU.NormSwap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetLeOfWeightedEntryBound
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem norm_det_le_of_weighted {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (u : Equiv.Perm (Fin n))
    (w : Fin n → ℝ) (c : ℝ) (hw : ∀ a, 0 < w a)
    (h : ∀ i b, ‖M i b‖ * (w (u i) * w b) ≤ c) :
    ‖M.det‖ ≤ (n.factorial : ℝ) * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
  have hM : ∀ i b, ‖M i b‖ ≤ |c| * ((w (u i))⁻¹ * (w b)⁻¹) := by
    intro i b
    have hp : 0 < w (u i) * w b := mul_pos (hw _) (hw _)
    rw [← mul_inv, ← div_eq_mul_inv, le_div_iff₀ hp]
    exact (h i b).trans (le_abs_self c)
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (σ i) i‖ ≤ |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
    intro σ
    have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
    rw [norm_mul, hs, one_mul, norm_prod]
    calc ∏ i, ‖M (σ i) i‖ ≤ ∏ i, |c| * ((w (u (σ i)))⁻¹ * (w i)⁻¹) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hM _ _)
      _ = |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
          have e : ∏ i, (w (u (σ i)))⁻¹ = ∏ a, (w a)⁻¹ :=
            Equiv.prod_comp (σ.trans u) (fun a => (w a)⁻¹)
          rw [e, ← Finset.prod_mul_distrib]
          simp only [sq]
  rw [Matrix.det_apply']
  calc _ ≤ ∑ σ : Equiv.Perm (Fin n), ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (σ i) i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 :=
        Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul, mul_assoc]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIrreducibleCharacterUnitaryMaxCompactEqOne
section
noncomputable section

open MeasureTheory
open Formalism.REAL (KG toMK muK)
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.PcEF

theorem norm_irreducibleCharacter_unitaryMaxCompact_eq_one : SchurOne := by
  intro n ε γ W _ _ _ T hT
  obtain ⟨hnt, hU, hK⟩ := hT
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  let π : KG ε →* (W →L[ℂ] W) :=
    { toFun := fun k => T (toMK k)
      map_one' := hU.1.1
      map_mul' := fun a b => hU.1.2 _ a.2 _ b.2 }
  have hπU : GlobalTheory.OpTrace.IsUnitaryRep π :=
    ⟨fun k v => hU.2.1 _ k.2 v, fun v => (hU.2.2 v).comp_continuous hemb.continuous fun k => k.2⟩
  have hπI : GlobalTheory.AutomorphicL2Unitary.IsTopIrreducible π := by
    refine ⟨hnt, fun S hS => ?_⟩
    refine hK.2.2.1 S le_top fun g hg v hv => ?_
    have : g ∈ Set.range (fun k : KG ε => toMK k) := by rw [Formalism.REAL.range_toMK]; exact hg
    obtain ⟨k, rfl⟩ := this
    exact hS.2 k v hv
  have h := GlobalTheory.Orb.integral_conj_trace_mul_trace (μ := muK ε) hπU hπI
  have h1 : (muK ε).real Set.univ = 1 := by
    rw [Measure.real, Formalism.REAL.muK, ← TopologicalSpace.PositiveCompacts.coe_top, Measure.haarMeasure_self]
    rfl
  rw [h1] at h
  exact_mod_cast h

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalSupportFinitePrimeSet
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

theorem starT_invol {p : ℕ} [Fact p.Prime] (G : HTGroup p) (K : Type) [CommRing K] [Algebra ℚ K]
    (x : K ⊗[ℚ] G.C) : (starT G.star K (starT G.star K x).unop).unop = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r c => rw [starT_tmul, starT_tmul, G.star_star]
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

end GlobalTheory.FinClsLoc
end
end

