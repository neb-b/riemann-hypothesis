module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DensityNumericalFacts
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

def P1 (m al be j : ℕ) : ℝ := (dimHar m al be : ℝ) / ((dimPol m (al + j) : ℝ) * dimPol m (be + j))

structure DensityNumericalFacts (K : Cst) (X : Dat) : Prop where
  m1 : 1 ≤ X.m
  cardP : 0 < (X.WaP K).card ∧ 0 < (X.WbP K).card
  dens : ∃ δ : ℝ, 0 ≤ δ ∧
    (∀ τ ≤ X.ccl, ∀ al ∈ X.Wa τ, ∀ be ∈ X.Wb τ, δ ≤ ∑ j ∈ Finset.range (X.Jn K + 1), P1 X.m al be j) ∧
    ((X.WaP K).card : ℝ) ^ X.N * ((X.WbP K).card : ℝ) ^ X.N ≤
      2 * δ ^ X.N * (((X.Wa 0).card : ℝ) ^ X.N * ((X.Wb 0).card : ℝ) ^ X.N)

open Classical in
theorem sum_map_le {α β : Type*} (S : Finset α) (S' : Finset β) (φ : α → β) (hinj : Set.InjOn φ S)
    (hmap : ∀ x ∈ S, φ x ∈ S') (g : β → ℝ) (hg : ∀ y ∈ S', 0 ≤ g y) :
    ∑ x ∈ S, g (φ x) ≤ ∑ y ∈ S', g y := by
  calc ∑ x ∈ S, g (φ x) = ∑ y ∈ S.image φ, g y := (Finset.sum_image hinj).symm
    _ ≤ ∑ y ∈ S', g y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.2 hmap) (fun y hy _ => hg y hy)

theorem dimPol_pos (m A : ℕ) : 0 < dimPol m A := Nat.choose_pos (Nat.le_add_left _ _)

theorem Ne_pos {p n' : ℕ} (R : RS p n') (k : ℕ) : 0 < gaussianNumber (p ^ n') (k + 1) := by
  have hp : 5 ≤ p := R.std.1.five_le
  have hn : 2 ≤ n' := R.std.1.two_le
  have hq : (1 : ℝ) < ((p ^ n' : ℕ) : ℝ) := by
    have : 1 < p ^ n' := Nat.one_lt_pow (by omega) (by omega)
    exact_mod_cast this
  unfold gaussianNumber
  apply div_pos
  · have := one_lt_pow₀ hq (by omega : k + 1 ≠ 0)
    linarith
  · linarith

theorem card_Wa (X : Dat) (τ : ℕ) : (X.Wa τ).card = (X.Wa 0).card := by
  simp only [Dat.Wa, Nat.card_Icc]; omega

theorem card_Wb (X : Dat) (τ : ℕ) : (X.Wb τ).card = (X.Wb 0).card := by
  simp only [Dat.Wb, Nat.card_Icc]; omega

theorem sum_kF_mul_prod_le_kx (hD : RestDims) (K : Cst) (X : Dat) (hm : 1 ≤ X.m) (R : RS X.p X.n') (hK : KeyIneq K X R)
    (A : X.TT → ℕ) (hA : A ∈ Fintype.piFinset (fun _ : X.TT => X.WaP K))
    (B : X.TT → ℕ) (hB : B ∈ Fintype.piFinset (fun _ : X.TT => X.WbP K)) :
    ∑ j ∈ Fintype.piFinset (fun _ : X.TT => Finset.range (X.Jn K + 1)),
        X.kF K R (fun s => A s - j s) (fun s => B s - j s) *
          ∏ s, ((dimHar X.m (A s - j s) (B s - j s) : ℝ) / ((dimPol X.m (A s) : ℝ) * dimPol X.m (B s))) ≤
      X.kx K R A B := by
  have h := hK A hA B hB
  have hNe := Ne_pos R X.m
  have hHH : ((dimHH (m := X.m) R.Kf X.TT (ex A) (ex B) : ℕ) : ℝ) =
      ∏ s, ((dimPol X.m (A s) : ℝ) * dimPol X.m (B s)) := by
    rw [(hD X.p X.n' R X.m hm X.TT A B).1]; push_cast; rfl
  have hPpos : 0 < ∏ s, ((dimPol X.m (A s) : ℝ) * dimPol X.m (B s)) :=
    Finset.prod_pos fun s _ => mul_pos (by exact_mod_cast dimPol_pos _ _) (by exact_mod_cast dimPol_pos _ _)
  rw [hHH] at h
  have hterm : ∀ j : X.TT → ℕ,
      X.kF K R (fun s => A s - j s) (fun s => B s - j s) *
          ∏ s, ((dimHar X.m (A s - j s) (B s - j s) : ℝ) / ((dimPol X.m (A s) : ℝ) * dimPol X.m (B s))) =
      (X.kF K R (fun s => A s - j s) (fun s => B s - j s) *
          dL R (flatW X.m (fun s => A s - j s) (fun s => B s - j s))) *
        (gaussianNumber (X.p ^ X.n') (X.m + 1) / ∏ s, ((dimPol X.m (A s) : ℝ) * dimPol X.m (B s))) := by
    intro j
    unfold dL
    rw [(hD X.p X.n' R X.m hm X.TT (fun s => A s - j s) (fun s => B s - j s)).2, Finset.prod_div_distrib]
    push_cast
    field_simp
  simp only [hterm]
  rw [← Finset.sum_mul]
  calc _ ≤ (X.kx K R A B * ((∏ s, ((dimPol X.m (A s) : ℝ) * dimPol X.m (B s))) / gaussianNumber (X.p ^ X.n') (X.m + 1))) *
        (gaussianNumber (X.p ^ X.n') (X.m + 1) / ∏ s, ((dimPol X.m (A s) : ℝ) * dimPol X.m (B s))) :=
        mul_le_mul_of_nonneg_right h (le_of_lt (div_pos hNe hPpos))
    _ = X.kx K R A B := by field_simp

theorem avg_abs {ι : Type} [Fintype ι] [DecidableEq ι] (SaP SbP Sa Sb : Finset ℕ) (J : ℕ)
    (kf kx : (ι → ℕ) → (ι → ℕ) → ℝ) (q : ℕ → ℕ → ℕ → ℝ) (hq : ∀ A B j, 0 ≤ q A B j) (hkf : ∀ A B, 0 ≤ kf A B)
    (hkey : ∀ A ∈ Fintype.piFinset (fun _ : ι => SaP), ∀ B ∈ Fintype.piFinset (fun _ : ι => SbP),
      ∑ j ∈ Fintype.piFinset (fun _ : ι => Finset.range (J + 1)),
        kf (fun s => A s - j s) (fun s => B s - j s) * ∏ s, q (A s) (B s) (j s) ≤ kx A B)
    (hsa : ∀ a ∈ Sa, ∀ j ≤ J, a + j ∈ SaP) (hsb : ∀ b ∈ Sb, ∀ j ≤ J, b + j ∈ SbP)
    (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ al ∈ Sa, ∀ be ∈ Sb, δ ≤ ∑ j ∈ Finset.range (J + 1), q (al + j) (be + j) j)
    (hcard : (SaP.card : ℝ) ^ Fintype.card ι * (SbP.card : ℝ) ^ Fintype.card ι ≤
      2 * δ ^ Fintype.card ι * ((Sa.card : ℝ) ^ Fintype.card ι * (Sb.card : ℝ) ^ Fintype.card ι))
    (hpa : 0 < SaP.card) (hpb : 0 < SbP.card) :
    meanN Sa Sb kf ≤ 2 * meanN SaP SbP kx := by
  set SJ := Fintype.piFinset (fun _ : ι => Finset.range (J + 1)) with hSJ
  set SA := Fintype.piFinset (fun _ : ι => SaP) with hSA
  set SB := Fintype.piFinset (fun _ : ι => SbP) with hSB
  set Ta := Fintype.piFinset (fun _ : ι => Sa) with hTa
  set Tb := Fintype.piFinset (fun _ : ι => Sb) with hTb
  let F : (ι → ℕ) → (ι → ℕ) → (ι → ℕ) → ℝ := fun A B j =>
    kf (fun s => A s - j s) (fun s => B s - j s) * ∏ s, q (A s) (B s) (j s)
  have hFnn : ∀ A B j, 0 ≤ F A B j := fun A B j =>
    mul_nonneg (hkf _ _) (Finset.prod_nonneg fun s _ => hq _ _ _)
  have h1 : ∑ A ∈ SA, ∑ B ∈ SB, ∑ j ∈ SJ, F A B j ≤ ∑ A ∈ SA, ∑ B ∈ SB, kx A B :=
    Finset.sum_le_sum fun A hA => Finset.sum_le_sum fun B hB => hkey A hA B hB
  have h2 : ∑ al ∈ Ta, ∑ be ∈ Tb, ∑ j ∈ SJ, F (al + j) (be + j) j ≤ ∑ A ∈ SA, ∑ B ∈ SB, ∑ j ∈ SJ, F A B j := by
    have e1 : ∑ al ∈ Ta, ∑ be ∈ Tb, ∑ j ∈ SJ, F (al + j) (be + j) j =
        ∑ j ∈ SJ, ∑ al ∈ Ta, ∑ be ∈ Tb, F (al + j) (be + j) j := by
      calc _ = ∑ al ∈ Ta, ∑ j ∈ SJ, ∑ be ∈ Tb, F (al + j) (be + j) j :=
            Finset.sum_congr rfl fun al _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    have e2 : ∑ A ∈ SA, ∑ B ∈ SB, ∑ j ∈ SJ, F A B j = ∑ j ∈ SJ, ∑ A ∈ SA, ∑ B ∈ SB, F A B j := by
      calc _ = ∑ A ∈ SA, ∑ j ∈ SJ, ∑ B ∈ SB, F A B j := Finset.sum_congr rfl fun A _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    rw [e1, e2]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' : ∀ s, j s ≤ J := fun s => by
      have := (Fintype.mem_piFinset.1 hj) s
      exact Nat.lt_succ_iff.1 (Finset.mem_range.1 this)
    have hmapA : ∀ al ∈ Ta, al + j ∈ SA := fun al hal =>
      Fintype.mem_piFinset.2 fun s => hsa _ ((Fintype.mem_piFinset.1 hal) s) _ (hj' s)
    have hmapB : ∀ be ∈ Tb, be + j ∈ SB := fun be hbe =>
      Fintype.mem_piFinset.2 fun s => hsb _ ((Fintype.mem_piFinset.1 hbe) s) _ (hj' s)
    calc ∑ al ∈ Ta, ∑ be ∈ Tb, F (al + j) (be + j) j
        ≤ ∑ al ∈ Ta, ∑ B ∈ SB, F (al + j) B j := Finset.sum_le_sum fun al _ =>
          sum_map_le Tb SB (fun be => be + j) (fun x _ y _ h => add_right_cancel h) hmapB
            (fun B => F (al + j) B j) (fun _ _ => hFnn _ _ _)
      _ ≤ ∑ A ∈ SA, ∑ B ∈ SB, F A B j :=
          sum_map_le Ta SA (fun al => al + j) (fun x _ y _ h => add_right_cancel h) hmapA
            (fun A => ∑ B ∈ SB, F A B j) (fun _ _ => Finset.sum_nonneg fun _ _ => hFnn _ _ _)
  have h3 : ∀ al ∈ Ta, ∀ be ∈ Tb, δ ^ Fintype.card ι * kf al be ≤ ∑ j ∈ SJ, F (al + j) (be + j) j := by
    intro al hal be hbe
    have e : ∀ j : ι → ℕ, F (al + j) (be + j) j = kf al be * ∏ s, q (al s + j s) (be s + j s) (j s) := by
      intro j
      simp only [F, Pi.add_apply, Nat.add_sub_cancel]
    simp only [e]
    rw [← Finset.mul_sum, hSJ,
      ← Finset.prod_univ_sum (fun _ : ι => Finset.range (J + 1)) (fun s j => q (al s + j) (be s + j) j), mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (hkf _ _)
    calc δ ^ Fintype.card ι = ∏ _s : ι, δ := by rw [Finset.prod_const, Finset.card_univ]
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hδ0) fun s _ =>
        hδ (al s) ((Fintype.mem_piFinset.1 hal) s) (be s) ((Fintype.mem_piFinset.1 hbe) s)
  have h4 : δ ^ Fintype.card ι * ∑ al ∈ Ta, ∑ be ∈ Tb, kf al be ≤ ∑ A ∈ SA, ∑ B ∈ SB, kx A B := by
    refine le_trans ?_ (le_trans h2 h1)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun al hal => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun be hbe => h3 al hal be hbe
  unfold meanN
  set s := ∑ al ∈ Ta, ∑ be ∈ Tb, kf al be with hs
  set x := ∑ A ∈ SA, ∑ B ∈ SB, kx A B with hx
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hkf _ _
  have hx0 : 0 ≤ x := le_trans (mul_nonneg (pow_nonneg hδ0 _) hs0) h4
  set u := (Sa.card : ℝ) ^ Fintype.card ι * (Sb.card : ℝ) ^ Fintype.card ι with hu
  set v := (SaP.card : ℝ) ^ Fintype.card ι * (SbP.card : ℝ) ^ Fintype.card ι with hv
  have hv0 : 0 < v := mul_pos (pow_pos (by exact_mod_cast hpa) _) (pow_pos (by exact_mod_cast hpb) _)
  have hu0 : 0 ≤ u := by positivity
  rcases eq_or_lt_of_le hu0 with hu' | hu'
  · rw [← hu', div_zero]; positivity
  · rw [div_le_iff₀ hu', ← mul_div_assoc, div_mul_eq_mul_div, le_div_iff₀ hv0]
    calc s * v ≤ s * (2 * δ ^ Fintype.card ι * u) := mul_le_mul_of_nonneg_left hcard hs0
      _ = 2 * (δ ^ Fintype.card ι * s) * u := by ring
      _ ≤ 2 * x * u := by gcongr

theorem avg_of (hD : RestDims) (K : Cst) (X : Dat) (hF : DensityNumericalFacts K X) (R : RS X.p X.n') (hK : KeyIneq K X R)
    (τ : ℕ) (hτ : τ ≤ X.ccl) : Avg K X R τ := by
  obtain ⟨δ, hδ0, hδ, hcard⟩ := hF.dens
  refine avg_abs (X.WaP K) (X.WbP K) (X.Wa τ) (X.Wb τ) (X.Jn K) (X.kF K R) (X.kx K R)
    (fun A B j => (dimHar X.m (A - j) (B - j) : ℝ) / ((dimPol X.m A : ℝ) * dimPol X.m B))
    (fun A B j => by positivity) (fun _ _ => Real.sInf_nonneg fun _ h => h.1)
    (fun A hA B hB => sum_kF_mul_prod_le_kx hD K X hF.m1 R hK A hA B hB) ?_ ?_ δ hδ0 ?_ ?_ hF.cardP.1 hF.cardP.2
  · intro a ha j hj
    have := Finset.mem_Icc.1 ha
    simp only [Dat.WaP, Finset.mem_Icc]
    omega
  · intro b hb j hj
    have := Finset.mem_Icc.1 hb
    simp only [Dat.WbP, Finset.mem_Icc]
    omega
  · intro al hal be hbe
    have := hδ τ hτ al hal be hbe
    simpa only [P1, Nat.add_sub_cancel] using this
  · rw [card_Wa, card_Wb, Fintype.card_coe]
    exact hcard

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FourDepthLtConductorOfBounds
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem dle_abs (CA CH N ns N1 k Y L lg la u0 k1 Dp : ℝ) (hCA : 0 < CA) (hCH : 8 * CA + 93 ≤ CH) (hN : 2 ≤ N)
    (hns0 : 0 ≤ ns) (hns : ns ≤ N) (hN1 : 1 ≤ N1) (sq_level_le_degree : N1 ^ 2 ≤ k) (hNk : N ≤ k) (hk : 5 ≤ k) (hY : 1 ≤ Y)
    (hL : 1 ≤ L) (hlg0 : 0 ≤ lg) (hlg : lg ≤ 3 * L) (hla0 : 0 ≤ la) (hla : la ≤ 2 * L)
    (hu0 : u0 ≤ (k + 1) * lg + 1) (hk1 : k1 ≤ (k - 1) ^ 2 * lg + 1)
    (hD : CH * N * Y ^ 2 * (N1 ^ 5 + k ^ 3) * L ≤ Dp) :
    2 * ((ns * (CA * Y ^ 2 * N1 ^ 2 * k ^ 2 * lg + 2 * (2 * N * k * la)) + 4 * (2 * N * k * la)) + 4 * N * u0) +
      N * k1 ≤ Dp := by
  have hN0 : 0 ≤ N := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hN10 : 0 ≤ N1 := by linarith
  have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ hY
  have hNL : 0 ≤ N * L := mul_nonneg hN0 hL0
  have hk2 : k ^ 2 ≤ Y ^ 2 * k ^ 3 := by
    have h1 : (1 : ℝ) ≤ Y ^ 2 * k := one_le_mul_of_one_le_of_one_le hY2 (by linarith)
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ k ^ 2)
    calc k ^ 2 = k ^ 2 * 1 := by ring
      _ ≤ k ^ 2 * (Y ^ 2 * k) := this
      _ = _ := by ring
  have hk1' : k ≤ k ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  set P := N * Y ^ 2 * k ^ 3 * L with hP
  have hP0 : 0 ≤ P := by positivity
  have hB : N * k ^ 2 * L ≤ P := by
    have := mul_le_mul_of_nonneg_left hk2 hNL
    calc N * k ^ 2 * L = N * L * k ^ 2 := by ring
      _ ≤ N * L * (Y ^ 2 * k ^ 3) := this
      _ = P := by rw [hP]; ring
  have hA : N * k * L ≤ P := by
    have := mul_le_mul_of_nonneg_left hk1' hNL
    calc N * k * L = N * L * k := by ring
      _ ≤ N * L * k ^ 2 := this
      _ = N * k ^ 2 * L := by ring
      _ ≤ P := hB
  have t1 : ns * (CA * Y ^ 2 * N1 ^ 2 * k ^ 2 * lg) ≤ 3 * CA * P := by
    calc ns * (CA * Y ^ 2 * N1 ^ 2 * k ^ 2 * lg) ≤ N * (CA * Y ^ 2 * k * k ^ 2 * (3 * L)) := by gcongr
      _ = 3 * CA * P := by rw [hP]; ring
  have t2 : ns * (2 * (2 * N * k * la)) ≤ 8 * P := by
    calc ns * (2 * (2 * N * k * la)) ≤ N * (2 * (2 * k * k * (2 * L))) := by gcongr
      _ = 8 * (N * k ^ 2 * L) := by ring
      _ ≤ 8 * P := by linarith
  have t3 : 4 * (2 * N * k * la) ≤ 16 * P := by
    calc 4 * (2 * N * k * la) ≤ 4 * (2 * N * k * (2 * L)) := by gcongr
      _ = 16 * (N * k * L) := by ring
      _ ≤ 16 * P := by linarith
  have hkL : 0 ≤ k * L := mul_nonneg hk0 hL0
  have t4 : 4 * N * u0 ≤ 16 * P := by
    have h1 : u0 ≤ 4 * (k * L) := by
      have h2 : (k + 1) * lg ≤ (k + 1) * (3 * L) := by gcongr
      have h3 : 4 * L ≤ k * L := by
        have := mul_le_mul_of_nonneg_right (by linarith : (4 : ℝ) ≤ k) hL0
        linarith
      nlinarith
    calc 4 * N * u0 ≤ 4 * N * (4 * (k * L)) := by gcongr
      _ = 16 * (N * k * L) := by ring
      _ ≤ 16 * P := by linarith
  have t5 : N * k1 ≤ 4 * P := by
    have h1 : k1 ≤ 4 * (k ^ 2 * L) := by
      have h2 : (k - 1) ^ 2 ≤ k ^ 2 := by nlinarith
      have h3 : (k - 1) ^ 2 * lg ≤ k ^ 2 * (3 * L) := by
        have h0 : (0 : ℝ) ≤ (k - 1) ^ 2 := by positivity
        gcongr
      have h4 : 1 ≤ k ^ 2 * L := one_le_mul_of_one_le_of_one_le (by nlinarith) hL
      linarith
    calc N * k1 ≤ N * (4 * (k ^ 2 * L)) := by gcongr
      _ = 4 * (N * k ^ 2 * L) := by ring
      _ ≤ 4 * P := by linarith
  have hfin : (8 * CA + 93) * P ≤ Dp := by
    have h1 : (8 * CA + 93) * P ≤ CH * P := mul_le_mul_of_nonneg_right hCH hP0
    have h2 : CH * P ≤ CH * N * Y ^ 2 * (N1 ^ 5 + k ^ 3) * L := by
      have hCH0 : 0 ≤ CH := by linarith
      have h5 : (0 : ℝ) ≤ N1 ^ 5 := by positivity
      have : k ^ 3 ≤ N1 ^ 5 + k ^ 3 := by linarith
      calc CH * P = CH * N * Y ^ 2 * k ^ 3 * L := by rw [hP]; ring
        _ ≤ CH * N * Y ^ 2 * (N1 ^ 5 + k ^ 3) * L := by gcongr
    linarith
  have hCAP : 0 ≤ CA * P := mul_nonneg hCA.le hP0
  have e : 2 * ((ns * (CA * Y ^ 2 * N1 ^ 2 * k ^ 2 * lg + 2 * (2 * N * k * la)) + 4 * (2 * N * k * la)) +
      4 * N * u0) + N * k1 =
      2 * ((ns * (CA * Y ^ 2 * N1 ^ 2 * k ^ 2 * lg) + ns * (2 * (2 * N * k * la)) + 4 * (2 * N * k * la)) +
      4 * N * u0) + N * k1 := by ring
  rw [e]
  nlinarith

theorem logs_of {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) :
    1 ≤ lgA X.p X.a X.m ∧ lgA X.p X.a X.m ≤ 3 * Real.logb X.p X.ar ∧
      0 ≤ Real.logb X.p X.a ∧ Real.logb X.p X.a ≤ 2 * Real.logb X.p X.ar := by
  have hp1 : (1 : ℝ) < X.p := by linarith [B.hp25]
  have har200 : (200 : ℝ) ≤ X.ar := by
    have := mul_le_mul B.hp25 B.hb8 (by norm_num) (by linarith [B.hp25])
    linarith [B.hpa]
  have hpar : (X.p : ℝ) ≤ X.ar := by
    have := le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ X.p) (by linarith [B.hb8] : (1 : ℝ) ≤ X.b')
    linarith [B.hpa]
  have ha1 : (1 : ℝ) ≤ X.a := by linarith [B.haa]
  have hm : (X.m : ℝ) ≤ X.ar := by
    have := B.hkp
    unfold Dat.k at this
    linarith
  have hm0 : (0 : ℝ) ≤ X.m := by positivity
  have hsq : X.ar ^ 2 = X.ar * X.ar := by ring
  have h10 : 10 * X.ar ≤ X.ar ^ 2 := by
    rw [hsq]
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have e2 : Real.logb X.p (X.ar ^ 2) = 2 * Real.logb X.p X.ar := by
    rw [Real.logb_pow]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold lgA
    have : 0 ≤ Real.logb X.p (8 * (X.a : ℝ) + X.m) := Real.logb_nonneg hp1 (by linarith)
    linarith
  · unfold lgA
    have h1 : Real.logb X.p (8 * (X.a : ℝ) + X.m) ≤ Real.logb X.p (X.ar ^ 2) :=
      Real.logb_le_logb_of_le hp1 (by linarith) (by linarith [B.haa1])
    rw [e2] at h1
    linarith [B.hL1]
  · exact Real.logb_nonneg hp1 ha1
  · have h1 : Real.logb X.p (X.a : ℝ) ≤ Real.logb X.p (X.ar ^ 2) :=
      Real.logb_le_logb_of_le hp1 (by linarith) (by linarith [B.haa1])
    rw [e2] at h1
    exact h1

theorem D0_eq_numSeg_mul_add (K : Cst) (X : Dat) :
    X.D0 K = (numSeg X.TT : ℝ) * (K.CA * X.Y ^ 2 * (X.N₁ : ℝ) ^ 2 * X.k ^ 2 * lgA X.p X.a X.m +
      2 * (2 * X.N * X.k * Real.logb X.p X.a)) + 4 * (2 * X.N * X.k * Real.logb X.p X.a) := by
  unfold Dat.D0 totalDegreeBudget DjI depthD kappaZeroExponent kap0I kap0G4 Dat.k Dat.N
  rfl

theorem D1nn_of {K : Cst} (hK : K.Pos) {CH : ℝ} {X : Dat} (B : Base K CH X) : 0 ≤ X.D1 K := by
  obtain ⟨h1, -, h3, -⟩ := logs_of B
  unfold Dat.D1
  rw [D0_eq_numSeg_mul_add]
  have hCA : 0 < K.CA := hK.2.2.1
  have hk : 0 ≤ X.k := by linarith [B.hk5]
  have hY : 0 ≤ X.Y := by linarith [B.hY]
  have hlg : 0 ≤ lgA X.p X.a X.m := by linarith
  positivity

theorem dle_of {K : Cst} (hK : K.Pos) {CH : ℝ} (hCH : K.TLP ≤ CH) {X : Dat} (h : X.Hyp K.C₀ CH) (B : Base K CH X) :
    2 * X.D1 K + X.N * X.kap1c ≤ X.Dp := by
  obtain ⟨h1, h2, h3, h4⟩ := logs_of B
  have hD : CH * X.N * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + X.k ^ 3) * Real.logb X.p X.ar ≤ X.Dp :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlg0 : 0 ≤ lgA X.p X.a X.m := by linarith
  have hk : 0 ≤ X.k := by linarith [B.hk5]
  have hu : (X.u0c : ℝ) ≤ (X.k + 1) * lgA X.p X.a X.m + 1 := by
    unfold Dat.u0c
    have : (0 : ℝ) ≤ ((X.m : ℝ) + 2) * lgA X.p X.a X.m := by positivity
    have h5 := (Nat.ceil_lt_add_one this).le
    have e : X.k + 1 = (X.m : ℝ) + 2 := by unfold Dat.k; ring
    rw [e]
    exact h5
  have hk1 : (X.kap1c : ℝ) ≤ (X.k - 1) ^ 2 * lgA X.p X.a X.m + 1 := by
    unfold Dat.kap1c
    have : (0 : ℝ) ≤ kappaOneExponent X.p X.a X.m := by unfold kappaOneExponent; positivity
    have h5 := (Nat.ceil_lt_add_one this).le
    have e : (X.k - 1) ^ 2 * lgA X.p X.a X.m = kappaOneExponent X.p X.a X.m := by unfold Dat.k kappaOneExponent; ring
    rw [e]
    exact h5
  have := dle_abs K.CA CH X.N (numSeg X.TT) X.N₁ X.k X.Y (Real.logb X.p X.ar) (lgA X.p X.a X.m)
    (Real.logb X.p X.a) X.u0c X.kap1c X.Dp hK.2.2.1
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCH) B.hN2 (by positivity) B.hns B.hN1 B.sq_level_le_degree B.hNk
    B.hk5 B.hY B.hL1 hlg0 h2 h3 h4 hu hk1 hD
  unfold Dat.D1
  rw [D0_eq_numSeg_mul_add]
  exact this

theorem four_depth_lt_conductor_of_bounds {K : Cst} {X : Dat} (hd : 2 * X.D1 K + X.N * X.kap1c ≤ X.Dp) (hc : 8 * (X.Dp + 1) ≤ X.cStar) :
    4 * X.D1 K < X.c4 := by
  have h1 : (0 : ℝ) ≤ (X.N : ℝ) * X.kap1c := by positivity
  have h2 : (8 : ℝ) * ((X.Dp : ℝ) + 1) ≤ X.cStar := by exact_mod_cast hc
  have h3 : (X.cStar : ℝ) ≤ X.c4 := by
    unfold Dat.c4
    push_cast
    have : (0 : ℝ) ≤ 2 * (X.N : ℝ) * X.ccl + 2 * (X.n' : ℝ) * X.ccl := by positivity
    linarith
  have h4 : (0 : ℝ) ≤ X.Dp := by positivity
  linarith

theorem k_le_G {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) :
    X.k ≤ X.k ^ 3 * X.N * ((X.p : ℝ) ^ X.G') ^ 4 * X.Y := by
  have hk1 : (1 : ℝ) ≤ X.k := by linarith [B.hk5]
  have h1 : (1 : ℝ) ≤ X.k ^ 2 * X.N * ((X.p : ℝ) ^ X.G') ^ 4 * X.Y :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hk1) (by linarith [B.hN2])) (one_le_pow₀ B.hQ)) B.hY
  have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ X.k)
  calc X.k = X.k * 1 := by ring
    _ ≤ X.k * (X.k ^ 2 * X.N * ((X.p : ℝ) ^ X.G') ^ 4 * X.Y) := this
    _ = _ := by ring

theorem Nccl_le (X : Dat) : (X.N : ℝ) * X.ccl ≤ (X.cStar : ℝ) + X.N * X.ccl + X.n' * X.ccl := by
  have h1 : (0 : ℝ) ≤ X.cStar := by positivity
  have h2 : (0 : ℝ) ≤ (X.n' : ℝ) * X.ccl := by positivity
  linarith

theorem eps_of {K : Cst} {CH : ℝ} (hCH : K.TLP ≤ CH) {X : Dat} (B : Base K CH X) :
    12 * (X.N : ℝ) * X.k * X.ccl / X.b' ≤ 1 / 9 := by
  have hb : 0 < X.b' := by linarith [B.hb8]
  have h108 : (108 : ℝ) ≤ CH := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCH
  have h := B.hsz X.k ((X.N : ℝ) * X.ccl) (by linarith [B.hk5]) (k_le_G B) (by positivity) (Nccl_le X)
  have h0 : (0 : ℝ) ≤ X.k * ((X.N : ℝ) * X.ccl) := mul_nonneg (by linarith [B.hk5]) (by positivity)
  have h1 : 108 * (X.k * ((X.N : ℝ) * X.ccl)) ≤ CH * (X.k * ((X.N : ℝ) * X.ccl)) :=
    mul_le_mul_of_nonneg_right h108 h0
  rw [div_le_iff₀ hb]
  linarith

theorem ccl_le_b {K : Cst} {CH : ℝ} (hCH : K.TLP ≤ CH) {X : Dat} (B : Base K CH X) : (X.ccl : ℝ) ≤ X.b' := by
  have h108 : (108 : ℝ) ≤ CH := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCH
  have h := B.hsz X.k ((X.N : ℝ) * X.ccl) (by linarith [B.hk5]) (k_le_G B) (by positivity) (Nccl_le X)
  have hc0 : (0 : ℝ) ≤ X.ccl := by positivity
  have h1 : (1 : ℝ) * 1 * (1 * X.ccl) ≤ CH * X.k * ((X.N : ℝ) * X.ccl) := by
    have a1 : (1 : ℝ) ≤ CH := by linarith
    have a2 : (1 : ℝ) ≤ X.k := by linarith [B.hk5]
    have a3 : (1 : ℝ) ≤ X.N := by linarith [B.hN2]
    gcongr
  linarith

theorem b_le_a {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) : X.b' ≤ X.a := by
  have hb : 0 ≤ X.b' := by linarith [B.hb8]
  have := mul_le_mul_of_nonneg_right (by linarith [B.hp25] : (1 : ℝ) ≤ X.p) hb
  linarith [B.hpa, B.haa]

theorem second_moment_of_columns {K : Cst} {CH : ℝ} (hCH : K.TLP ≤ CH) {X : Dat} (B : Base K CH X) : 2 * X.ccl ≤ 8 * X.a := by
  have h : (X.ccl : ℝ) ≤ X.a := le_trans (ccl_le_b hCH B) (b_le_a B)
  have h' : X.ccl ≤ X.a := by exact_mod_cast h
  omega

theorem lowa_of {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) : X.b' / 3 ≤ X.a := by
  have := b_le_a B
  linarith [B.hb8]

theorem lowb_of {C₀ CH : ℝ} {X : Dat} (h : X.Hyp C₀ CH) : X.b' / 3 ≤ X.bl := by
  obtain ⟨-, -, -, -, -, -, -, -, hb, -, hbu, -, hIb2, -⟩ := h
  linarith

end Formalism.MainNotions.flipOneThree.Pf

end
end

