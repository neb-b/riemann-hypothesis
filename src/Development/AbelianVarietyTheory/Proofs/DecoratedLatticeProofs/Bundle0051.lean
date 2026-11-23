module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsScalarMulIntegralOfNormalizesSymmetricLevel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterArgumentCongrRootEntrySumMod
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FlagChi

open Formalism.L2.SG.Pf.unitaryCongruence

theorem rootSum_eq {A : Type} [CommRing A] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (ε : A) (m : Matrix (Fin n) (Fin n) A) :
    rootSum ρ k ε m =
      (∑ a : Fin ρ, m ⟨a.1, by omega⟩ ⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by split_ifs <;> omega⟩) +
      ∑ i : Fin k, if h : i.1 + 1 < k then ε * m ⟨ρ + i.1, by omega⟩ ⟨ρ + (i.1 + 1), by omega⟩ else 0 := by
  obtain rfl : n = ρ + (k + (ρ + 1)) := by omega
  unfold rootSum
  rw [Fin.sum_univ_add, Fin.sum_univ_add, ← add_assoc]
  have h3 : ∀ x y z : A, z = 0 → x = y → x + z = y := by
    intro x y z hz hx; rw [hz, hx, add_zero]
  refine h3 _ _ _ (Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun j _ => ?_) ?_
  · simp only [Fin.val_natAdd]
    rw [if_neg (by omega), if_neg (by omega)]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    have ha := a.2
    rw [Finset.sum_eq_single (⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by split_ifs <;> omega⟩ : Fin (ρ + (k + (ρ + 1))))]
    · rw [if_pos]
      · rfl
      · simp only [Fin.val_castAdd]
        split_ifs <;> omega
    · intro j _ hj
      have hj' : j.1 ≠ if a.1 + 1 < ρ then a.1 + 1 else ρ + k := fun h => hj (Fin.ext h)
      simp only [Fin.val_castAdd]
      rw [if_neg (by split_ifs at hj' <;> omega), if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.2
    by_cases h : i.1 + 1 < k
    · rw [dite_eq_left h, Finset.sum_eq_single (⟨ρ + (i.1 + 1), by omega⟩ : Fin (ρ + (k + (ρ + 1))))]
      · rw [if_neg, if_pos]
        · rfl
        · simp only [Fin.val_natAdd, Fin.val_castAdd]
          omega
        · simp only [Fin.val_natAdd, Fin.val_castAdd]
          omega
      · intro j _ hj
        have hj' : j.1 ≠ ρ + (i.1 + 1) := fun h => hj (Fin.ext h)
        simp only [Fin.val_natAdd, Fin.val_castAdd]
        rw [if_neg (by omega), if_neg (by omega)]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dite_eq_right h]
      refine Finset.sum_eq_zero fun j _ => ?_
      simp only [Fin.val_natAdd, Fin.val_castAdd]
      rw [if_neg (by omega), if_neg (by omega)]

theorem hatL_eq_Lf (I : AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z.1, z.2, rfl⟩

def colOf (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (j : Fin I.n) : VA I :=
  fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l j

theorem matIn_int (I : AutInst) {β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} {x : I.Gf}
    (hx : (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β) (i j : Fin I.n) :
    matIn I β x i j ∈ IntAf I.F I.E := by
  obtain ⟨y, hy⟩ := hx
  have hconj : β⁻¹ * frGL β y * β = intGL I.F I.E I.n y := by
    simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hy] at hconj
  unfold matIn
  rw [hconj]
  exact ((y : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) i j).2

theorem mul_matIn (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (x : I.Gf) :
    (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * matIn I β x =
      I.fmat x * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) := by
  unfold matIn
  rw [← Units.val_mul, ← Units.val_mul]
  congr 1
  group

theorem mulVec_mem_Lf (I : AutInst) {β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (hβ : IsFrame β I.L) {x : I.Gf}
    (hx : (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β) {v : VA I} (hv : v ∈ I.Lf) : I.fmat x *ᵥ v ∈ I.Lf := by
  rw [← hatL_eq_Lf] at hv ⊢
  refine (hβ _).2 fun i => ?_
  have h := (hβ v).1 hv
  have e : ((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *ᵥ
      (I.fmat x *ᵥ v) = matIn I β x *ᵥ
      (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *ᵥ v) := by
    unfold matIn
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  rw [e, Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (matIn_int I hx i l) (h l)

theorem col_mem_Lf (I : AutInst) {β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (hβ : IsFrame β I.L) (j : Fin I.n) :
    colOf I β j ∈ I.Lf := by
  rw [← hatL_eq_Lf]
  refine (hβ _).2 fun i => ?_
  show (((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) *
      (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))) i j ∈ _
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem mL_le_Lf (I : AutInst) (g : ℕ) : mL I g ≤ I.Lf :=
  Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact I.Lf.smul_mem (⟨(g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), natCast_mem _ g⟩ : IntAf I.F I.E) hy)

theorem mulVec_mem_mL (I : AutInst) (g : ℕ) {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)}
    (hM : ∀ y ∈ I.Lf, M *ᵥ y ∈ I.Lf) {v : VA I} (hv : v ∈ mL I g) : M *ᵥ v ∈ mL I g := by
  have : mL I g ≤ (mL I g).comap (mvO I M) := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact mL_mv I hM g le_rfl y hy)
  exact this hv

theorem hA_col (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (x : I.Gf) (p q : Fin I.n) :
    hA I (colOf I β p) (I.fmat x *ᵥ colOf I β q) = ∑ l, matIn I β x l q * gramIn I β p l := by
  have e : I.fmat x *ᵥ colOf I β q = ∑ l, matIn I β x l q • colOf I β l := by
    funext i
    have := congrFun (congrFun (mul_matIn I β x) i) q
    rw [Finset.sum_apply]
    refine Eq.trans this.symm ?_
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, ← hL_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hL_apply, hA_smul_right]
  rfl

theorem pair_zmod (I : AutInst) (g ρ k : ℕ) (b : ℕ → VA I) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))
    (hβ : IsLiftFrame I g b β)
    (hG : ∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) (x : I.Gf)
    (hx : (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β) (p q t : Fin I.n) (hp : p.1 ≠ ρ + k)
    (ht : t.1 = dualIdx ρ k p.1) : ZMod' I g (hA I (b p.1) (I.fmat x *ᵥ b q.1) - matIn I β x t q) := by
  have hM : ∀ y ∈ I.Lf, I.fmat x *ᵥ y ∈ I.Lf := fun y hy => mulVec_mem_Lf I hβ.1 hx hy
  have hp' : colOf I β p - b p.1 ∈ mL I g := hβ.2 p
  have hq' : colOf I β q - b q.1 ∈ mL I g := hβ.2 q
  have hbp : b p.1 ∈ I.Lf := by
    have := sub_mem (col_mem_Lf I hβ.1 p) (mL_le_Lf I g hp')
    rwa [sub_sub_cancel] at this
  have h1 : ZMod' I g (hA I (b p.1) (I.fmat x *ᵥ (colOf I β q - b q.1))) :=
    mL_Qs I g hbp (mulVec_mem_mL I g hM hq')
  have h2 : ZMod' I g (hA I (colOf I β p - b p.1) (I.fmat x *ᵥ colOf I β q)) := by
    rw [hA_symm]
    exact Z_sig I g (mL_Qs I g (hM _ (col_mem_Lf I hβ.1 q)) hp')
  have h3 : ZMod' I g (∑ l, matIn I β x l q * (gramIn I β p l - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k p l)) :=
    Z_sum I g _ _ fun l _ => Z_smul I g (matIn_int I hx l q) (hG p l)
  have e1 : ∑ l, matIn I β x l q * flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k p l = matIn I β x t q := by
    rw [Finset.sum_eq_single t]
    · unfold flagGram
      rw [if_pos ht, if_neg hp, mul_one]
    · intro l _ hl
      unfold flagGram
      rw [if_neg (fun h => hl (Fin.ext (h.trans ht.symm))), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [mul_sub] at h3
  rw [Finset.sum_sub_distrib, e1, ← hA_col] at h3
  have e2 : hA I (colOf I β p) (I.fmat x *ᵥ colOf I β q) =
      hA I (colOf I β p - b p.1) (I.fmat x *ᵥ colOf I β q) + hA I (b p.1) (I.fmat x *ᵥ colOf I β q) := by
    rw [← hA_add_left, sub_add_cancel]
  rw [Matrix.mulVec_sub, hA_sub_right] at h1
  rw [e2] at h3
  convert Z_sub I g (Z_sub I g h3 h2) h1 using 1
  ring

theorem chiArg_sub_rootSum : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 → ∀ β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β → (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) → ∀ x : I.Gf, (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β → ZMod' I g (chiArg I e0 f0 z0 bw bwd x - rootSum ρ k ew (matIn I β x)) := by
  intro I g ρ k e0 f0 z0 bw bwd ew hF hn β hβ hG x hx
  obtain ⟨-, -, -, -, ⟨hid, hor, hint, -⟩, ⟨hw, hwd⟩, -, -⟩ := hF
  rw [rootSum_eq hn]
  unfold chiArg
  rw [add_sub_add_comm, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Z_add I g (Z_sum I g _ _ fun a _ => ?_) (Z_sum I g _ _ fun i _ => ?_)
  · have ha := a.2
    have key := pair_zmod I g ρ k _ β hβ hG x hx ⟨2 * ρ + k - a.1, by omega⟩
      ⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by split_ifs <;> omega⟩ ⟨a.1, by omega⟩ (by show 2 * ρ + k - a.1 ≠ _; omega)
      (by show a.1 = dualIdx ρ k (2 * ρ + k - a.1); unfold dualIdx; split_ifs <;> omega)
    have e1 : flagVec e0 f0 z0 bw bwd (2 * ρ + k - a.1) = f0 a := by
      unfold flagVec
      rw [dite_eq_right (by omega), dite_eq_right (by omega), if_neg (by omega), dite_eq_left (by omega)]
      congr 1
      apply Fin.ext
      show 2 * ρ + k - (2 * ρ + k - a.1) = a.1
      omega
    have e2 : flagVec e0 f0 z0 bw bwd (if a.1 + 1 < ρ then a.1 + 1 else ρ + k) = nxt e0 z0 a := by
      unfold nxt
      by_cases h : a.1 + 1 < ρ
      · rw [if_pos h, dite_eq_left h]
        unfold flagVec
        rw [dite_eq_left h]
      · rw [if_neg h, dite_eq_right h]
        unfold flagVec
        rw [dite_eq_right (by omega), dite_eq_right (by omega), if_pos rfl]
    rw [← e1, ← e2]
    exact key
  · have hi := i.2
    by_cases h : i.1 + 1 < k
    swap
    · rw [dite_eq_right h, dite_eq_right h, sub_zero]
      exact Z_zero I g
    rw [dite_eq_left h, dite_eq_left h]
    have key := pair_zmod I g ρ k _ β hβ hG x hx ⟨ρ + (k - (i.1 + 1)), by omega⟩
      ⟨ρ + (i.1 + 1), by omega⟩ ⟨ρ + i.1, by omega⟩ (by show ρ + (k - (i.1 + 1)) ≠ _; omega)
      (by show ρ + i.1 = dualIdx ρ k (ρ + (k - (i.1 + 1))); unfold dualIdx; split_ifs <;> omega)
    have c : ∀ l : Fin k, flagVec e0 f0 z0 bw bwd (ρ + l.1) = bw l + bwd (Fin.rev l) := by
      intro l
      have hl := l.2
      have : (⟨ρ + l.1 - ρ, by omega⟩ : Fin k) = l := Fin.ext (by show ρ + l.1 - ρ = l.1; omega)
      unfold flagVec
      rw [dite_eq_right (by omega), dite_eq_left (by omega), this]
    have e1 : bwd i = sigA I ew • flagVec e0 f0 z0 bw bwd (ρ + (k - (i.1 + 1))) := by
      have := c (Fin.rev i)
      rw [Fin.val_rev, Fin.rev_rev] at this
      rw [this, smul_add, hw, smul_smul, mul_comm, hor, zero_smul, zero_add]
      exact hwd i
    have e2 : bw ⟨i.1 + 1, h⟩ = ew • flagVec e0 f0 z0 bw bwd (ρ + (i.1 + 1)) := by
      rw [c ⟨i.1 + 1, h⟩, smul_add, hwd, smul_smul, hor, zero_smul, add_zero]
      exact hw _
    rw [e1, e2, Matrix.mulVec_smul, hA_smul_left, hA_smul_right, sigA_sigA, ← mul_assoc, hid, ← mul_sub]
    exact Z_smul I g hint key

end GlobalTheory.FlagChi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterResidueFieldsEqProdGenericShift
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

namespace GlobalTheory.LeviBlockCharacter

theorem exists_shift {F : Type} [Field F] [Finite F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (χ : AddChar F ℂ) : ∃ a : F, ∀ x, χ x = ψ (a * x) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hinj : Function.Injective ψ.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hψ)
  have hbij : Function.Bijective ψ.mulShift :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, (AddChar.card_eq).symm⟩
  obtain ⟨a, ha⟩ := hbij.2 χ
  exact ⟨a, fun x => by rw [← ha, AddChar.mulShift_apply]⟩

theorem prod_shift {ι : Type} (k : ι → Type) [∀ i, CommRing (k i)] {S : Type} [CommRing S]
    (Pg : Finset ι) (p p' : ∀ i, S →+* k i) (χ : S → ℂ) (ψ : ∀ i, AddChar (k i) ℂ)
    (hψ : ∀ i ∈ Pg, ∀ χ' : AddChar (k i) ℂ, ∃ a, ∀ x, χ' x = ψ i (a * x))
    (hadd : ∀ s t, χ (s + t) = χ s * χ t)
    (hker : ∀ s, (∀ i ∈ Pg, p i s = 0 ∧ p' i s = 0) → χ s = 1)
    (hsurj : ∀ u u' : ∀ i, k i, ∃ s, ∀ i ∈ Pg, p i s = u i ∧ p' i s = u' i)
    (hposition : ∀ i ∈ Pg, (∃ s, (∀ j ∈ Pg, (j ≠ i → p j s = 0) ∧ p' j s = 0) ∧ χ s ≠ 1) ∧
      ∃ s, (∀ j ∈ Pg, p j s = 0 ∧ (j ≠ i → p' j s = 0)) ∧ χ s ≠ 1) :
    ∃ a₁ a₂ : ∀ i, k i, (∀ i ∈ Pg, a₁ i ≠ 0 ∧ a₂ i ≠ 0) ∧
      ∀ s, χ s = ∏ i ∈ Pg, ψ i (a₁ i * p i s + a₂ i * p' i s) := by
  classical
  have h0 : χ 0 = 1 := hker 0 (fun i _ => ⟨map_zero _, map_zero _⟩)
  have hdep : ∀ s t, (∀ i ∈ Pg, p i s = p i t ∧ p' i s = p' i t) → χ s = χ t := by
    intro s t h
    have h1 : χ (s - t) = 1 := hker _ (fun i hi => by
      rw [map_sub, map_sub, (h i hi).1, (h i hi).2, sub_self, sub_self]; exact ⟨rfl, rfl⟩)
    have h2 := hadd t (s - t)
    rw [h1, mul_one, add_sub_cancel] at h2
    exact h2
  choose σ hσ using hsurj
  have hsum : ∀ (A : Finset ι) (f : ι → S), χ (∑ i ∈ A, f i) = ∏ i ∈ A, χ (f i) := by
    intro A f
    induction A using Finset.induction_on with
    | empty => simpa using h0
    | insert a A ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]
  let c₁ : ∀ i, AddChar (k i) ℂ := fun i =>
    { toFun := fun x => χ (σ (Pi.single i x) 0)
      map_zero_eq_one' := hker _ (fun j hj => by
        rw [(hσ _ _ j hj).1, (hσ _ _ j hj).2]; simp)
      map_add_eq_mul' := fun x y => by
        rw [← hadd]
        refine hdep _ _ (fun j hj => ?_)
        rw [map_add (f := _), map_add (f := _), (hσ _ _ j hj).1, (hσ _ _ j hj).2, (hσ _ _ j hj).1, (hσ _ _ j hj).2,
          (hσ _ _ j hj).1, (hσ _ _ j hj).2, Pi.single_add]
        simp }
  let c₂ : ∀ i, AddChar (k i) ℂ := fun i =>
    { toFun := fun x => χ (σ 0 (Pi.single i x))
      map_zero_eq_one' := hker _ (fun j hj => by
        rw [(hσ _ _ j hj).1, (hσ _ _ j hj).2]; simp)
      map_add_eq_mul' := fun x y => by
        rw [← hadd]
        refine hdep _ _ (fun j hj => ?_)
        rw [map_add (f := _), map_add (f := _), (hσ _ _ j hj).1, (hσ _ _ j hj).2, (hσ _ _ j hj).1, (hσ _ _ j hj).2,
          (hσ _ _ j hj).1, (hσ _ _ j hj).2, Pi.single_add]
        simp }
  have hc₁ : ∀ i x, c₁ i x = χ (σ (Pi.single i x) 0) := fun _ _ => rfl
  have hc₂ : ∀ i x, c₂ i x = χ (σ 0 (Pi.single i x)) := fun _ _ => rfl
  have e₁ : ∀ i, ∃ a : k i, i ∈ Pg → ∀ x, c₁ i x = ψ i (a * x) := fun i => by
    by_cases hi : i ∈ Pg
    · obtain ⟨a, ha⟩ := hψ i hi (c₁ i); exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hi⟩
  have e₂ : ∀ i, ∃ a : k i, i ∈ Pg → ∀ x, c₂ i x = ψ i (a * x) := fun i => by
    by_cases hi : i ∈ Pg
    · obtain ⟨a, ha⟩ := hψ i hi (c₂ i); exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose a₁ ha₁ using e₁
  choose a₂ ha₂ using e₂
  refine ⟨a₁, a₂, fun i hi => ⟨fun h => ?_, fun h => ?_⟩, fun s => ?_⟩
  · obtain ⟨s, hs, hne⟩ := (hposition i hi).1
    apply hne
    have h1 := ha₁ i hi (p i s)
    rw [h, zero_mul, AddChar.map_zero_eq_one, hc₁] at h1
    rw [← h1]
    refine hdep _ _ (fun j hj => ?_)
    rw [(hσ _ _ j hj).1, (hσ _ _ j hj).2]
    refine ⟨?_, (hs j hj).2⟩
    by_cases hji : j = i
    · subst hji; simp
    · rw [(hs j hj).1 hji, Pi.single_eq_of_ne hji]
  · obtain ⟨s, hs, hne⟩ := (hposition i hi).2
    apply hne
    have h1 := ha₂ i hi (p' i s)
    rw [h, zero_mul, AddChar.map_zero_eq_one, hc₂] at h1
    rw [← h1]
    refine hdep _ _ (fun j hj => ?_)
    rw [(hσ _ _ j hj).1, (hσ _ _ j hj).2]
    refine ⟨(hs j hj).1, ?_⟩
    by_cases hji : j = i
    · subst hji; simp
    · rw [(hs j hj).2 hji, Pi.single_eq_of_ne hji]
  · have h1 : χ s = χ (∑ i ∈ Pg, (σ (Pi.single i (p i s)) 0 + σ 0 (Pi.single i (p' i s)))) := by
      refine hdep _ _ (fun j hj => ?_)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_add (f := _), (hσ _ _ j hj).1, (hσ _ _ j hj).2, Pi.zero_apply, add_zero,
        zero_add]
      constructor
      · rw [Finset.sum_eq_single j (fun b _ hb => Pi.single_eq_of_ne (Ne.symm hb) _)
          (fun h => absurd hj h), Pi.single_eq_same]
      · rw [Finset.sum_eq_single j (fun b _ hb => Pi.single_eq_of_ne (Ne.symm hb) _)
          (fun h => absurd hj h), Pi.single_eq_same]
    rw [h1, hsum]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [hadd, ← hc₁, ← hc₂, ha₁ i hi, ha₂ i hi, AddChar.map_add_eq_mul]

theorem char_eq_prod_shift : ∀ (E : Type) [Field E] [NumberField E] (S : Type) [CommRing S] (Pg : Finset (Pl E)) (p p' : ∀ PP : Pl E, S →+* kP PP) (χ : S → ℂ) (ψ0 : ∀ PP : Pl E, AddChar (kP PP) ℂ), IsGenericPsi Pg ψ0 → (∀ s t, χ (s + t) = χ s * χ t) → (∀ s, (∀ PP ∈ Pg, p PP s = 0 ∧ p' PP s = 0) → χ s = 1) → (∀ u u' : ∀ PP : Pl E, kP PP, ∃ s, ∀ PP ∈ Pg, p PP s = u PP ∧ p' PP s = u' PP) → (∀ PP ∈ Pg, (∃ s, (∀ PP' ∈ Pg, (PP' ≠ PP → p PP' s = 0) ∧ p' PP' s = 0) ∧ χ s ≠ 1) ∧ ∃ s, (∀ PP' ∈ Pg, p PP' s = 0 ∧ (PP' ≠ PP → p' PP' s = 0)) ∧ χ s ≠ 1) → ∃ a₁ a₂ : ∀ PP : Pl E, kP PP, (∀ PP ∈ Pg, a₁ PP ≠ 0 ∧ a₂ PP ≠ 0) ∧ ∀ s, χ s = ∏ PP ∈ Pg, ψ0 PP (a₁ PP * p PP s + a₂ PP * p' PP s) := by
  intro E _ _ S _ Pg p p' χ ψ0 hψ hadd hker hsurj hposition
  refine prod_shift (fun PP : Pl E => kP PP) Pg p p' χ ψ0 (fun PP hPP χ' => ?_) hadd hker hsurj hposition
  have : PP.asIdeal.IsMaximal := PP.isMaximal
  let : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  exact exists_shift (F := kP PP) (ψ0 PP) (hψ PP hPP) χ'

end GlobalTheory.LeviBlockCharacter
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagCorollary
section
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk
open scoped InnerProductSpace

namespace GlobalTheory.Core.Rk

theorem dstar_pos_of (D : D7) (u : D.what₂.Word) : 0 < D.what₂.Dstar := by
  rw [← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos

theorem diagS_mono {D : D7} {u : D.what₂.Word} {e e' : ℝ} (h : DiagS D u e) (he : e ≤ e') : DiagS D u e' := by
  unfold DiagS at *
  exact h.trans (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))

theorem kfk_nonneg (D : D7) : 0 ≤ kfk D := by
  unfold kfk
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.log_natCast_nonneg _)

theorem diag_corollary :
    (∀ (D : D7) (u : D.what₂.Word) (A x κ : ℝ), 0 ≤ A → TwoTerm D u A x → (d0 D u : ℝ) ≤ κ * D.what₂.Dstar →
      DiagS D u (A * κ + x)) ∧
    (∀ (D : D7) (u : D.what₂.Word) (L C : ℝ), 0 ≤ C * mfL D L → SDiag D u L C → Small D u L C →
      DiagS D u (eDiag D L C)) ∧
    (∀ (D : D7) (u : D.what₂.Word) (Γ₀ : ℝ), SAbs D u Γ₀ ↔ TwoTerm D u Γ₀ (1 / 4)) := by
  have first : ∀ (D : D7) (u : D.what₂.Word) (A x κ : ℝ), 0 ≤ A → TwoTerm D u A x → (d0 D u : ℝ) ≤ κ * D.what₂.Dstar →
      DiagS D u (A * κ + x) := by
    intro D u A x κ hA h hd
    have hD := dstar_pos_of D u
    have hd0 : (0 : ℝ) ≤ (d0 D u : ℝ) := Nat.cast_nonneg _
    have hq : (d0 D u : ℝ) ^ 2 / D.what₂.Dstar ≤ κ * (d0 D u : ℝ) := by
      rw [div_le_iff₀ hD]
      have := mul_le_mul_of_nonneg_left hd hd0
      nlinarith
    unfold DiagS
    unfold TwoTerm at h
    calc hsDev D u ≤ A * (d0 D u : ℝ) ^ 2 / D.what₂.Dstar + x * (d0 D u : ℝ) := h
      _ = A * ((d0 D u : ℝ) ^ 2 / D.what₂.Dstar) + x * (d0 D u : ℝ) := by rw [mul_div_assoc]
      _ ≤ A * (κ * (d0 D u : ℝ)) + x * (d0 D u : ℝ) := by gcongr
      _ = (A * κ + x) * (d0 D u : ℝ) := by ring
  refine ⟨first, ?_, ?_⟩
  · intro D u L C hc hS hSm
    set c := C * mfL D L with hcdef
    have h2 : Real.exp (-(2 * C * mfL D L)) = Real.exp (-c) * Real.exp (-c) := by
      rw [← Real.exp_add]; congr 1; rw [hcdef]; ring
    have h1 : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
    have hle : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hpos : 0 < Real.exp (-c) := Real.exp_pos _
    have hk := kfk_nonneg D
    have hkk : Real.exp (-kfk D) ≤ Real.exp (-(kfk D / 2)) := Real.exp_le_exp.2 (by linarith)
    have hd := first D u (4 * (Real.exp c + 1)) (4 * Real.exp (-(kfk D / 2)) + 2 * Real.exp (-kfk D))
      (Real.exp (-(2 * C * mfL D L))) (by positivity) hS (by unfold Small at hSm; linarith [hSm])
    refine diagS_mono hd ?_
    unfold eDiag
    rw [h2, ← hcdef]
    have : 4 * (Real.exp c + 1) * (Real.exp (-c) * Real.exp (-c)) = 4 * Real.exp (-c) + 4 * (Real.exp (-c) * Real.exp (-c)) := by
      have e : 4 * (Real.exp c + 1) * (Real.exp (-c) * Real.exp (-c))
          = 4 * (Real.exp c * Real.exp (-c)) * Real.exp (-c) + 4 * (Real.exp (-c) * Real.exp (-c)) := by ring
      rw [e, h1]; ring
    rw [this]
    nlinarith
  · intro D u Γ₀
    unfold SAbs TwoTerm
    rw [show (1 / 4 : ℝ) * (d0 D u : ℝ) = (d0 D u : ℝ) / 4 by ring]

end GlobalTheory.Core.Rk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinrankKerPuLeHsDev
section
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk
open scoped InnerProductSpace

namespace GlobalTheory.Core.Rk

theorem finrank_ker_Pu_le_hsDev (D : D7) (u : D.what₂.Word) :
    (Module.finrank ℂ (LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH)) : ℝ) ≤ hsDev D u := by
  unfold hsDev
  refine GlobalTheory.T.finrank_ker_le_hilbertSchmidtNormSq_sub_id (Kmat D.s u u) _ ?_
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hx' : D.s.Pu u x = 0 := hx
  simp [Kmat, hx']

end GlobalTheory.Core.Rk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsScalarMulIntegralOfNormalizesSymmetricLevelStatement
section
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isScalarMul_integral_of_normalizes_symmetricLevel : ∀ (K : Type) [Field K] (O : ValuationSubring K) (k : Type) [Field k] (r : O →+* k), Function.Surjective r → ∀ (n ρ κ : ℕ), n = 2 * ρ + κ + 1 → 1 ≤ ρ → ∀ ψ : AddChar k ℂ, ψ ≠ 1 → ∀ a : Fin n → Fin n → k, (∀ i j, symEdge ρ κ i j → a i j ≠ 0) → ∀ m : GL (Fin n) K, (∀ x : GL (Fin n) O, bc r x ∈ unipSym k n ρ κ → ∃ x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹ ∧ ψ (edgeVal ρ κ a (bc r x')) = ψ (edgeVal ρ κ a (bc r x))) → (∀ x : GL (Fin n) O, bc r x ∈ unipSym k n ρ κ → ∃ x' : GL (Fin n) O, bc O.subtype x' = m⁻¹ * bc O.subtype x * m) → IsScal O m := by
  first | exact @GlobalTheory.ScalInt.isScal_of_normalises | exact GlobalTheory.ScalInt.isScal_of_normalises | (intros; apply GlobalTheory.ScalInt.isScal_of_normalises <;> assumption)
end

