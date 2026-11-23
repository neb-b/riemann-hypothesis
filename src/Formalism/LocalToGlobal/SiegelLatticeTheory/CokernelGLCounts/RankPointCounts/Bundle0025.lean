module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanTermANonneg
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints

set_option linter.dupNamespace false

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Asm

variable {D : D7} {X : HidaSetting D}

theorem kloostermanTermA_nonneg (large₂ : SizeData₂ D) {C Ch Cc : ℝ} (hC : 0 ≤ C) (hCh : 0 ≤ Ch) (hCc : 0 ≤ Cc) (j : ℕ) :
    0 ≤ k2A1 large₂ C Ch Cc j := by
  have hHb : ∀ c, 0 < Hb large₂.sc.b c D.R.m D.R.f := fun c => by unfold Hb Scale.b; positivity
  have h1 : 0 ≤ C / (D.R.k : ℝ) := div_nonneg hC (Nat.cast_nonneg _)
  unfold k2A1
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg h1 _)
    (Real.rpow_nonneg (hHb C).le _)) (Real.rpow_nonneg (hHb Ch).le _)) (Real.rpow_nonneg (hHb C).le _))
    (Real.rpow_nonneg (hHb Cc).le _)

theorem label_sum {large₂ : SizeData₂ D} {Y : Full X} {u : D.what₂.Word} {CH Cs C Ch Cp Cc : ℝ}
    (hC : 0 ≤ C) (hCh : 0 ≤ Ch) (hCs : Cp + 4 ≤ Cs)
    (hDel : ∀ t ∈ relSet Y u, 0 < k2Del D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.rS)
    (hcos : ∀ T : Finset (ℕ → D.host.E), (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) →
      ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ)))
    (T : Finset (ℕ → D.host.E)) (hTm : ∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) :
    ∑ δ ∈ T, k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ ≤ k2A1 large₂ C Ch Cc j := by
  have hH : H1C large₂ CH = large₂.sc.b ^ (CH * (D.R.m : ℝ)) := rfl
  rw [hH] at hDel hcos
  have hHb : ∀ c, 0 < Hb large₂.sc.b c D.R.m D.R.f := fun c => by unfold Hb Scale.b; positivity
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hrk : D.R.rS + 3 ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    unfold Ranks.rS
    omega
  have hrkR : (D.R.rS : ℝ) + 3 ≤ D.R.k := by exact_mod_cast hrk
  have hjr : (j : ℝ) ≤ D.R.rS := by exact_mod_cast (Finset.mem_Icc.1 hj).2
  have hS1 : ∀ δ, 1 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := by
    intro δ
    unfold k2S
    refine Finset.prod_induction _ (fun x => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
      le_rfl fun τ _ => ?_
    unfold k2sg
    exact (Finset.le_fold_max 1).2 (Or.inl le_rfl)
  have hK0 : 0 ≤ ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg hC hk) _) (Real.rpow_nonneg (hHb C).le _))
      (Real.rpow_nonneg (hHb Ch).le _)
  have hK : 0 ≤ ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) := mul_nonneg hK0 (Real.rpow_nonneg (hHb C).le _)
  have key : ∀ δ ∈ T, k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ ≤
      (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) := by
    intro δ hδ
    obtain ⟨t, ht, hjt, hlt⟩ := hTm δ hδ
    obtain ⟨hΔ0, hΔle⟩ := hDel t ht
    rw [hjt, hlt] at hΔ0 hΔle
    have hS := hS1 δ
    have hS0 : 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := by linarith
    have e1 : k2Del D j δ ^ (-(((D.R.k : ℝ) - 1 - j) / 2)) * k2Del D j δ ^ ((D.R.k : ℝ) / 2) =
        k2Del D j δ ^ (((j : ℝ) + 1) / 2) := by
      rw [← Real.rpow_add hΔ0]; congr 1; ring
    have e2 : k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(Cs * D.R.k)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (Cp * D.R.k) = k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k) := by
      rw [← Real.rpow_add (by linarith)]; congr 1; ring
    have b1 : k2Del D j δ ^ (((j : ℝ) + 1) / 2) ≤ Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((j : ℝ) + 1) := by
      calc k2Del D j δ ^ (((j : ℝ) + 1) / 2) ≤ (Hb large₂.sc.b C D.R.m D.R.f * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ 2) ^ (((j : ℝ) + 1) / 2) :=
            Real.rpow_le_rpow hΔ0.le hΔle (by positivity)
        _ = Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * (k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ 2) ^ (((j : ℝ) + 1) / 2) :=
            Real.mul_rpow (hHb C).le (by positivity)
        _ = Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((j : ℝ) + 1) := by
            rw [← Real.rpow_natCast (k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ) 2, ← Real.rpow_mul hS0]; congr 2; push_cast; ring
    have b2 : k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((j : ℝ) + 1) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k) ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) := by
      rw [← Real.rpow_add (by linarith)]
      apply Real.rpow_le_rpow_of_exponent_le hS
      nlinarith [mul_le_mul_of_nonneg_right hCs hk]
    calc k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ
        = ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * (k2Del D j δ ^ (-(((D.R.k : ℝ) - 1 - j) / 2)) * k2Del D j δ ^ ((D.R.k : ℝ) / 2)) *
            (k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(Cs * D.R.k)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (Cp * D.R.k)) := by
          unfold k2a k2e; ring
      _ = ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * k2Del D j δ ^ (((j : ℝ) + 1) / 2) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k) := by rw [e1, e2]
      _ ≤ ((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * (Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((j : ℝ) + 1)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b1 hK0) (Real.rpow_nonneg hS0 _)
      _ = (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) *
            (k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((j : ℝ) + 1) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ ((Cp - Cs) * D.R.k)) := by ring
      _ ≤ (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) :=
          mul_le_mul_of_nonneg_left b2 hK
  calc ∑ δ ∈ T, k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ
      ≤ ∑ δ ∈ T, (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) * k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) :=
        Finset.sum_le_sum key
    _ = (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) * ∑ δ ∈ T, k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ ^ (-(3 * (D.R.rS : ℝ))) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (((C / D.R.k) ^ ((j : ℝ) * ((D.R.k : ℝ) - 1 - j) * D.R.f) * Hb large₂.sc.b C D.R.m D.R.f ^ (C * (D.R.rS : ℝ) ^ 4) *
        Hb large₂.sc.b Ch D.R.m D.R.f ^ (Ch * (D.R.rS : ℝ) ^ 4)) * Hb large₂.sc.b C D.R.m D.R.f ^ (((j : ℝ) + 1) / 2)) * Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ)) :=
        mul_le_mul_of_nonneg_left (hcos T hTm) hK
    _ = k2A1 large₂ C Ch Cc j := by unfold k2A1; ring

theorem rank_bound {large₂ : SizeData₂ D} {Y : Full X} {u : D.what₂.Word} {CH Cs C Ch Cp Cc : ℝ}
    (hC : 0 ≤ C) (hCh : 0 ≤ Ch) (hCs : Cp + 4 ≤ Cs) (hK : 0 ≤ dpiC X u * massC Y u)
    (hType : TypeAt large₂ Y u CH Cs C Ch Cp)
    (hDel : ∀ t ∈ relSet Y u, 0 < k2Del D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2)
    (hcos : ∀ j ∈ Finset.Icc 1 D.R.rS, ∀ T : Finset (ℕ → D.host.E),
      (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) →
      ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ)))
    (j' : ℕ) (hj' : j' ∈ Finset.Icc 1 D.R.rS) (j'' : ℕ) (hj'' : j'' ∈ Finset.Icc 1 D.R.rS)
    (S : Finset (GTu Y u × GTu Y u))
    (hS : ∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ jT p.1 = j' ∧ jT p.2 = j'') :
    ∑ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≤
      dpiC X u * massC Y u * (k2A1 large₂ C Ch Cc j' * k2A1 large₂ C Ch Cc j'') := by
  have hHb : ∀ c, 0 < Hb large₂.sc.b c D.R.m D.R.f := fun c => by unfold Hb Scale.b; positivity
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hSpos : ∀ j δ, 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := by
    intro j δ
    unfold k2S
    refine Finset.prod_nonneg fun τ _ => ?_
    unfold k2sg
    exact le_trans zero_le_one ((Finset.le_fold_max 1).2 (Or.inl le_rfl))
  have hA0 : ∀ j δ, (∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) →
      0 ≤ k2a large₂ CH Cs C j δ * k2e large₂ CH Ch Cp j δ := by
    rintro j δ ⟨t, ht, rfl, rfl⟩
    have hΔ := (hDel t ht).1
    unfold k2a k2e
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg hC hk) _)
      (Real.rpow_nonneg hΔ.le _)) (Real.rpow_nonneg (hHb C).le _)) (Real.rpow_nonneg (hSpos _ _) _))
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hΔ.le _) (Real.rpow_nonneg (hHb Ch).le _))
        (Real.rpow_nonneg (hSpos _ _) _))
  have hT1 : ∀ δ ∈ S.image (fun p => labT p.1), ∃ t ∈ relSet Y u, jT t = j' ∧ labT t = δ := by
    intro δ hδ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hδ
    exact ⟨p.1, (hS p hp).1.1, (hS p hp).2.1, rfl⟩
  have hT2 : ∀ δ ∈ S.image (fun p => labT p.2), ∃ t ∈ relSet Y u, jT t = j'' ∧ labT t = δ := by
    intro δ hδ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hδ
    exact ⟨p.2, (hS p hp).1.2.1, (hS p hp).2.2, rfl⟩
  have hmap : ∀ p ∈ S, (labT p.1, labT p.2) ∈
      S.image (fun p => labT p.1) ×ˢ S.image (fun p => labT p.2) := fun p hp =>
    Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hL1 := label_sum hC hCh hCs hDel j' hj' (hcos j' hj') _ hT1
  have hL2 := label_sum hC hCh hCs hDel j'' hj'' (hcos j'' hj'') _ hT2
  have hs1 := Finset.sum_nonneg fun δ hδ => hA0 _ _ (hT1 δ hδ)
  have hs2 := Finset.sum_nonneg fun δ hδ => hA0 _ _ (hT2 δ hδ)
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  calc _ ≤ ∑ l ∈ S.image (fun p => labT p.1) ×ˢ S.image (fun p => labT p.2),
        dpiC X u * massC Y u * ((k2a large₂ CH Cs C j' l.1 * k2e large₂ CH Ch Cp j' l.1) *
          (k2a large₂ CH Cs C j'' l.2 * k2e large₂ CH Ch Cp j'' l.2)) := by
        refine Finset.sum_le_sum fun l _ => hType j' hj' j'' hj'' l.1 l.2 _ fun p hp => ?_
        obtain ⟨hpS, hpl⟩ := Finset.mem_filter.1 hp
        obtain ⟨h1, h2, h3⟩ := hS p hpS
        exact ⟨h1, h2, h3, congrArg Prod.fst hpl, congrArg Prod.snd hpl⟩
    _ = dpiC X u * massC Y u *
          ((∑ δ ∈ S.image (fun p => labT p.1), k2a large₂ CH Cs C j' δ * k2e large₂ CH Ch Cp j' δ) *
           (∑ δ ∈ S.image (fun p => labT p.2), k2a large₂ CH Cs C j'' δ * k2e large₂ CH Ch Cp j'' δ)) := by
        rw [← Finset.mul_sum, Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ dpiC X u * massC Y u * (k2A1 large₂ C Ch Cc j' * k2A1 large₂ C Ch Cc j'') :=
        mul_le_mul_of_nonneg_left (mul_le_mul hL1 hL2 hs2 (hs1.trans hL1)) hK

theorem fin_bound {large₂ : SizeData₂ D} {Y : Full X} {u : D.what₂.Word} {CH Cs C Ch Cp Cc : ℝ}
    (hC : 0 ≤ C) (hCh : 0 ≤ Ch) (hCs : Cp + 4 ≤ Cs) (hK : 0 ≤ dpiC X u * massC Y u)
    (hIrr : ∀ t ∈ (Y.tO u u).degSet, ¬ t.relevant → (Y.tO u u).vec t = 0)
    (hJ : ∀ t ∈ relSet Y u, 1 ≤ jT t)
    (hType : TypeAt large₂ Y u CH Cs C Ch Cp)
    (hDel : ∀ t ∈ relSet Y u, 0 < k2Del D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2)
    (hcos : ∀ j ∈ Finset.Icc 1 D.R.rS, ∀ T : Finset (ℕ → D.host.E),
      (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) →
      ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ)))
    (S : Finset (GTu Y u × GTu Y u)) (hS : ∀ p ∈ S, p ∈ (Y.tO u u).allPairs (Y.tO u u).degSet) :
    ∑ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≤
      dpiC X u * massC Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
  have hne : ∀ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≠ 0 →
      p.1.relevant ∧ p.2.relevant := by
    intro p hp hF
    by_contra h
    apply hF
    rcases not_and_or.1 h with h1 | h1
    · rw [hIrr _ (hS p hp).1 h1, norm_zero, zero_mul]
    · rw [hIrr _ (hS p hp).2.1 h1, norm_zero, mul_zero]
  have hmap : ∀ p ∈ S.filter (fun p => p.1.relevant ∧ p.2.relevant),
      (jT p.1, jT p.2) ∈ Finset.Icc 1 D.R.rS ×ˢ Finset.Icc 1 D.R.rS := by
    intro p hp
    obtain ⟨hpS, h1, h2⟩ := Finset.mem_filter.1 hp
    have r1 : p.1 ∈ relSet Y u := Set.mem_inter (hS p hpS).1 h1
    have r2 : p.2 ∈ relSet Y u := Set.mem_inter (hS p hpS).2.1 h2
    refine Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hJ _ r1, ?_⟩, Finset.mem_Icc.2 ⟨hJ _ r2, ?_⟩⟩ <;>
      exact Nat.sub_le _ _
  rw [← Finset.sum_filter_of_ne hne, ← Finset.sum_fiberwise_of_maps_to hmap]
  calc _ ≤ ∑ l ∈ Finset.Icc 1 D.R.rS ×ˢ Finset.Icc 1 D.R.rS,
        dpiC X u * massC Y u * (k2A1 large₂ C Ch Cc l.1 * k2A1 large₂ C Ch Cc l.2) := by
        refine Finset.sum_le_sum fun l hl => rank_bound hC hCh hCs hK hType hDel hcos l.1
          (Finset.mem_product.1 hl).1 l.2 (Finset.mem_product.1 hl).2 _ fun p hp => ?_
        obtain ⟨hpF, hpl⟩ := Finset.mem_filter.1 hp
        obtain ⟨hpS, h1, h2⟩ := Finset.mem_filter.1 hpF
        exact ⟨⟨Set.mem_inter (hS p hpS).1 h1, Set.mem_inter (hS p hpS).2.1 h2, (hS p hpS).2.2⟩,
          congrArg Prod.fst hpl, congrArg Prod.snd hpl⟩
    _ = dpiC X u * massC Y u * (∑ j ∈ Finset.Icc 1 D.R.rS, k2A1 large₂ C Ch Cc j) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_product, sq, Finset.sum_mul_sum]

end Asm

end Formalism.L2.SG.KappaOffDiagonal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGDictPf
section
noncomputable section

open scoped Classical
open ValuativeRel

namespace Formalism.L2.SG.Pf

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.MainNotions.BridgeLemma Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.NGDict

section HpSec

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} {P : FPair H r}

omit [TopologicalSpace E] [MeasurableSpace E] [CommRing E] in
theorem le_mul_mul_rpow_neg_half_of_le_inv_sq {a b c q : ℝ} (hq : 0 < q) (a0 : 0 < a) (a1 : a ≤ 1) (b0 : 0 < b) (b1 : b ≤ 1)
    (c0 : 0 < c) (h : c ≤ (q ^ 2)⁻¹) : q ≤ (a * b * c) ^ (-(1 / 2 : ℝ)) := by
  have hx : a * b * c ≤ (q ^ 2)⁻¹ := by
    calc a * b * c ≤ 1 * 1 * c := by gcongr
      _ = c := by ring
      _ ≤ _ := h
  have e : ((q ^ 2)⁻¹) ^ (-(1 / 2 : ℝ)) = q := by
    rw [Real.rpow_neg (by positivity), Real.inv_rpow (by positivity), inv_inv, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq hq.le]
  calc q = ((q ^ 2)⁻¹) ^ (-(1 / 2 : ℝ)) := e.symm
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity) hx (by norm_num)

theorem ends_isUnit {l : ℕ} (hl : l ∈ P.ends) : IsUnit (P.Dm l) :=
  (((@Finset.mem_filter _ _ (Classical.decPred _) _ _).1 hl).2).2

theorem residue_le_height_nonprime (hOK : M.OK) (hR : P.RelG (theta M))
    (hex : ∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) (hp : ¬ P.PrimeTo) : StepHp P := by
  obtain ⟨d, t, ht⟩ := hex
  have hG : P.Gv ≠ 0 := hR.2.2.1
  obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩, c0, c1⟩ := ng_factors hOK hG ht
  have hq : (0 : ℝ) < qF F := by
    have := two_le_residue_card hOK
    exact_mod_cast (by omega : 0 < qF F)
  have hnt := Formalism.MainNotions.LocalModelPeriodLattices.nontrivial_E M.L
  have hm1 : ((-1 : F) ^ (r + 1)) ∈ 𝒪[F] := pow_mem (neg_mem (one_mem _)) _
  unfold StepHp FPair.Hp
  rcases hs : M.split with _ | g
  · have hnot : ¬ IsUnitO M P.Gv ∨ ∃ l ∈ P.ends, ¬ IsUnitO M (P.Dm l) := by
      by_contra hc
      push Not at hc
      exact hp ⟨hs, hc.1, hc.2⟩
    rcases hnot with hGn | ⟨l, hl, hDn⟩
    · refine ng_real_q hq a0 a1 b0 b1 c0 c1 (Or.inr ?_)
      have hfix : M.L.cj P.Gv = P.Gv := by
        unfold FPair.Gv HermSp.Gdet HermSp.normE
        simp only [map_sub, map_mul, M.L.cj_cj, AlgEquiv.commutes]
        ring
      obtain ⟨a, ha⟩ := (M.L.cj_fix _).1 hfix
      have hdet : (H.gram P.MMgen).det = algebraMap F E ((-1) ^ (r + 1) * a) := by
        rw [gram_det_eq P hs, ← ha, map_mul, map_pow, map_neg, map_one]
      have hmem : (H.gram P.MMgen).det ∈ M.L.O := by
        rw [← ng_term_gram ht]
        exact ng_det_mem _ (fun a b => ng_term_int ht (ng_term_MM ht _) (ng_term_MM ht _))
      have haO : (-1) ^ (r + 1) * a ∈ 𝒪[F] :=
        Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L _ (by rw [← hdet]; exact hmem)
      have haO' : a ∈ 𝒪[F] := by
        have h2 := mul_mem hm1 haO
        have e : ((-1 : F) ^ (r + 1)) * ((-1) ^ (r + 1) * a) = a := by
          rw [← mul_assoc, ← mul_pow]; simp
        rwa [e] at h2
      have ha0 : (-1) ^ (r + 1) * a ≠ 0 := by
        refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (fun h => hG ?_)
        rw [← ha, h, map_zero]
      rw [hdet]
      refine ng_modK_nonunit hOK ⟨_, haO⟩ ha0 (fun hu => hGn ?_)
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      have hy' : ((-1) ^ (r + 1) * a) * (y : F) = 1 := congrArg Subtype.val hy
      refine ⟨?_, algebraMap F E ((-1) ^ (r + 1) * (y : F)), ?_, ?_⟩
      · rw [← ha]; exact Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L ⟨a, haO'⟩
      · exact Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L ⟨_, mul_mem hm1 y.2⟩
      · rw [← ha, ← map_mul]
        have : a * ((-1) ^ (r + 1) * (y : F)) = ((-1) ^ (r + 1) * a) * (y : F) := by ring
        rw [this, hy', map_one]
    · have hlu : IsUnit (P.Dm l) := ends_isUnit hl
      have hfac : ∀ l' ∈ P.ends, 0 < M.modK (P.Dm l' * M.L.cj (P.Dm l')) ∧
          M.modK (P.Dm l' * M.L.cj (P.Dm l')) ≤ 1 := by
        intro l' hl'
        have hu := ends_isUnit hl'
        have h := ng_modK hOK (hu.mul (hu.map M.L.cj))
        exact ⟨h.1, h.2 (M.L.O.mul_mem (ng_term_Dm ht l')
          (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (ng_term_Dm ht l')))⟩
      have hcl : ∏ l' ∈ P.ends, M.modK (P.Dm l' * M.L.cj (P.Dm l')) ≤
          M.modK (P.Dm l * M.L.cj (P.Dm l)) := by
        rw [← Finset.mul_prod_erase _ _ hl]
        have h1 : ∏ x ∈ P.ends.erase l, M.modK (P.Dm x * M.L.cj (P.Dm x)) ≤ 1 :=
          Finset.prod_le_one₀ (fun x hx => (hfac x (Finset.mem_of_mem_erase hx)).1.le)
            (fun x hx => (hfac x (Finset.mem_of_mem_erase hx)).2)
        have h0 := (hfac l hl).1.le
        calc _ ≤ M.modK (P.Dm l * M.L.cj (P.Dm l)) * 1 := mul_le_mul_of_nonneg_left h1 h0
          _ = _ := mul_one _
      refine le_mul_mul_rpow_neg_half_of_le_inv_sq hq a0 a1 b0 b1 c0 (le_trans hcl ?_)
      have hfix : M.L.cj (P.Dm l * M.L.cj (P.Dm l)) = P.Dm l * M.L.cj (P.Dm l) := by
        rw [map_mul, M.L.cj_cj, mul_comm]
      obtain ⟨a, ha⟩ := (M.L.cj_fix _).1 hfix
      have hxO : P.Dm l * M.L.cj (P.Dm l) ∈ M.L.O :=
        M.L.O.mul_mem (ng_term_Dm ht l) (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (ng_term_Dm ht l))
      have haO : a ∈ 𝒪[F] := Formalism.MainNotions.LocalModelPeriodLattices.mem_OF_of_mem_O M.L _ (by rw [ha]; exact hxO)
      have hxu : IsUnit (P.Dm l * M.L.cj (P.Dm l)) := hlu.mul (hlu.map M.L.cj)
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [map_zero] at ha
        rw [← ha] at hxu
        exact not_isUnit_zero hxu
      rw [← ha]
      refine ng_modK_nonunit hOK ⟨a, haO⟩ ha0 (fun hu => hDn ?_)
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      have hy' : a * (y : F) = 1 := congrArg Subtype.val hy
      refine ⟨ng_term_Dm ht l, M.L.cj (P.Dm l) * algebraMap F E (y : F),
        M.L.O.mul_mem (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (ng_term_Dm ht l))
          (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L y), ?_⟩
      rw [← mul_assoc, ← ha, ← map_mul, hy', map_one]
  · refine ng_real_q hq a0 a1 b0 b1 c0 c1 (Or.inl ?_)
    have hθ : theta M = (g.q : F) := by
      unfold theta
      split
      · rename_i hg
        rw [hs] at hg
        cases hg
      · rename_i g' hg
        rw [hs] at hg
        cases hg
        rfl
    rw [hθ]
    exact ng_modK_nonunit hOK g.q (fun h => g.q_irr.ne_zero (Subtype.ext h)) g.q_irr.not_isUnit

end HpSec

section GlueSec

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ} {P : FPair H r}

end GlueSec

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

namespace Formalism.L2.SG.NGVanish

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hsEmb_eq_zero {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (A : Wq →L[ℂ] Wp)
    (h : Formalism.L2.SG.PackageTie.hsEmb A = 0) : A = 0 := by
  have hi : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := by
    intro i
    have := congrArg (fun v : Formalism.L2.SG.PackageTie.HS Wq Wp => WithLp.ofLp v i) h
    simpa [Formalism.L2.SG.PackageTie.hsEmb] using this
  have hA : (A : Wq →ₗ[ℂ] Wp) = 0 :=
    (stdOrthonormalBasis ℂ Wq).toBasis.ext (fun i => by simpa using hi i)
  ext x
  simpa using congrArg (fun f : Wq →ₗ[ℂ] Wp => f x) hA

def FormNGC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ ν, Pinned X u u' ν → ∀ t ∈ (Y.tO u u').ngSet, (Y.tO u u').vec t ≠ 0 →
        (∃ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) ∧
        ∀ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) →
          ∃ (c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (B : X.Vpi u' →L[ℂ] X.Vpi u'),
            OOt t = c • A.comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
              OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u')
                (Formalism.L2.SG.RealObj.gamW X u u' w)).comp B)

theorem stepTermVanish_of_form (h : FormNGC) : StepTermVanish := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a₀, b₀, h2⟩ := h Cg cb Cw cT CT C0
  refine ⟨a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u u' hc ν hν t ht hJ => ?_⟩
  by_contra hv
  obtain ⟨⟨w, hw, hrep⟩, hform⟩ := h2 C' Cl e1 e2 D large₂ X Y u u' hc ν hν t ht hv
  have hex : ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w' g :=
    ⟨w, hw, hrep⟩
  unfold J2of at hJ
  rw [dite_eq_left hex] at hJ
  have hJw : Jw Y u u' ν hex.choose = 0 :=
    hsEmb_eq_zero _ (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hJ))
  obtain ⟨c, A, B, hO⟩ := hform hex.choose hex.choose_spec.1 hex.choose_spec.2
  have key : ∀ (k χ c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (Z : X.Vpi u' →L[ℂ] X.Vpi u)
      (B : X.Vpi u' →L[ℂ] X.Vpi u'), k • Z = 0 → k • (χ • (c • A.comp (Z.comp B))) = 0 := by
    intro k χ c A Z B hZ
    have hy : ∀ y, k • Z y = 0 := fun y => by simpa using congrArg (fun T => T y) hZ
    ext x
    simp only [smul_apply, ContinuousLinearMap.comp_apply, zero_apply]
    rw [smul_comm k χ, smul_comm k c, ← map_smul A k, hy]
    simp
  have hamp : ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0 := by
    unfold ampN
    rw [hO]
    unfold Jw at hJw
    exact key _ _ _ _ _ _ hJw
  apply hv
  show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
  unfold vec
  rw [hamp]
  simp
  rfl

end Formalism.L2.SG.NGVanish
end
end

