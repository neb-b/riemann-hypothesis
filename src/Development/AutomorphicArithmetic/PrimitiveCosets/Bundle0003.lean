module

public import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
public import Development.AutomorphicArithmetic.PrimitiveCosets.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.PrimitiveCosets.GmAEq
section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private theorem UpperTheory.Comparison₂.character_trivial_on_generator_iff (φ : Frame) (ψ : AddChar (E0 × φ.A) ℂ) (s : φ.A) :
    chr φ ψ (φ.tau1 s) = 1 ↔ ψ (0, s) = 1 := by
  rw [← Units.val_eq_one, (chr_bij φ).2.2.2.2.1 ψ (φ.tau1 s)]
  simp [toE, Frame.tau1, Frame.iotaInv, Frame.iota]
  exact Iff.rfl

private theorem UpperTheory.Comparison₂.gmA_eq_triv (φ : Frame) (θ : φ.Char) (hi : θ φ.iod = 1) :
    (∀ h : φ.A, θ (φ.tau1 h) = 1) ↔ θ = 1 ∨ θ = φ.psC := by
  constructor
  · intro h
    have hM : ∀ m : φ.MA, θ ((1, 1), m) = 1 := fun m => h (Multiplicative.toAdd m)
    have hB : ∀ b : ℤˣ, θ ((1, b), 1) = 1 := by
      intro b
      rcases Int.units_eq_one_or b with rfl | rfl
      · exact θ.map_one
      · exact hi
    have hred : ∀ (a b : ℤˣ) (m : φ.MA), θ ((a, b), m) = θ ((a, 1), 1) := by
      intro a b m
      have e : (((a, b), m) : φ.GG) = ((a, 1), 1) * ((1, b), 1) * ((1, 1), m) := by
        ext <;> simp
      rw [e, map_mul, map_mul, hM, hB, mul_one, mul_one]
    have hsq : (θ φ.sg : ℂ) * (θ φ.sg : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul]
      have e : φ.sg * φ.sg = 1 := by
        simp only [Frame.sg]
        ext <;> simp
      rw [e, map_one, Units.val_one]
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · left
      refine MonoidHom.ext fun g => ?_
      obtain ⟨⟨a, b⟩, m⟩ := g
      rw [hred]
      apply Units.ext
      rcases Int.units_eq_one_or a with rfl | rfl
      · rw [hB 1]
        simp
      · simpa [Frame.sg] using h1
    · right
      refine MonoidHom.ext fun g => ?_
      obtain ⟨⟨a, b⟩, m⟩ := g
      rw [hred]
      apply Units.ext
      rcases Int.units_eq_one_or a with rfl | rfl
      · rw [hB 1]
        simp [Frame.psC, Frame.chQ]
      · simpa [Frame.psC, Frame.chQ, Frame.sg] using h1
  · rintro (rfl | rfl) h
    · simp
    · apply Units.ext
      simp [Frame.psC, Frame.chQ, Frame.tau1]

theorem UpperTheory.Comparison₂.gmA_eq :
    ∀ (Λ : Level) (φ : Frame) (H : HostAx φ) (TT : Finset φ.A) (x eps C : ℝ) (ell : AddChar (E0 × φ.A) ℂ → ℂ),
      EAtH Λ H.toHostRaw TT x eps C → HostAddCharCompatible H.toHostRaw ell → ∀ y,
        GmA (arith H.toHostRaw) ell (keptA Λ H.toHostRaw) (3 * (Λ.o : ℝ) + 1)⁻¹ y = Λ.Gm y := by
  intro Λ φ H TT x eps C ell hE hell y
  classical
  obtain ⟨hbij, -, -, -, -⟩ := chr_bij φ
  obtain ⟨hpinj, hp1⟩ := prim_inj φ H
  have hmem : ∀ ψ, ψ ∈ keptA Λ H.toHostRaw ↔ H.prim (chr φ ψ) ∈ Λ.KEPT := by
    intro ψ
    simp [keptA, HostRaw.kept_iff]
  have hXp : ∀ ψ, ψ ∈ keptA Λ H.toHostRaw → chr φ ψ ∈ φ.Xp := by
    intro ψ hψ
    obtain ⟨θ, hθ, hpr⟩ := hE.kept _ ((hmem ψ).1 hψ)
    rw [HostRaw.isPrimOf_iff] at hpr
    have e := hpinj hpr
    rw [e]
    exact hθ
  have hKimg : Λ.KEPT = (keptA Λ H.toHostRaw).image (fun ψ => H.prim (chr φ ψ)) := by
    ext p
    simp only [Finset.mem_image]
    constructor
    · intro hp
      obtain ⟨θ, -, hpr⟩ := hE.kept p hp
      rw [HostRaw.isPrimOf_iff] at hpr
      obtain ⟨ψ, rfl⟩ := hbij.2 θ
      refine ⟨ψ, (hmem ψ).2 ?_, hpr.symm⟩
      rw [← hpr]
      exact hp
    · rintro ⟨ψ, hψ, rfl⟩
      exact (hmem ψ).1 hψ
  have hinj : Set.InjOn (fun ψ => H.prim (chr φ ψ)) (keptA Λ H.toHostRaw) :=
    fun a _ b _ h => hbij.1 (hpinj h)
  have hw : ∀ ψ ∈ keptA Λ H.toHostRaw, wtA (3 * (Λ.o : ℝ) + 1)⁻¹ ψ =
      (if H.prim (chr φ ψ) = PChar.one then 1 else Λ.wt (H.prim (chr φ ψ))) := by
    intro ψ hψ
    have hiod : chr φ ψ φ.iod = 1 := (hXp ψ hψ).2
    have htriv : (∀ h : φ.A, ψ (0, h) = 1) ↔ chr φ ψ = 1 ∨ chr φ ψ = φ.psC := by
      rw [← gmA_eq_triv φ (chr φ ψ) hiod]
      exact forall_congr' fun h => (character_trivial_on_generator_iff φ ψ h).symm
    obtain ⟨hps1, hps2⟩ := hE.ps
    unfold wtA
    by_cases hA : ∀ h : φ.A, ψ (0, h) = 1
    · rw [if_pos hA]
      rcases htriv.1 hA with h1 | h1
      · rw [h1, hp1, if_pos rfl]
      · have hK : H.toHostRaw.Kept Λ.KEPT φ.psC := by
          rw [HostRaw.kept_iff, ← h1]
          exact (hmem ψ).1 hψ
        rw [h1]
        split_ifs with hone
        · rfl
        · cases hk : Λ.psK with
          | none => exact absurd hK (hps2 hk)
          | some p =>
            have e := hps1 p hk
            rw [HostRaw.isPrimOf_iff] at e
            simp [Level.wt, hk, e]
    · rw [if_neg hA]
      have hn1 : chr φ ψ ≠ 1 := fun h => hA (htriv.2 (Or.inl h))
      have hnps : chr φ ψ ≠ φ.psC := fun h => hA (htriv.2 (Or.inr h))
      rw [if_neg (fun h => hn1 (hpinj (h.trans hp1.symm)))]
      unfold Level.wt
      rw [if_neg]
      intro hk
      have e := hps1 _ hk
      rw [HostRaw.isPrimOf_iff] at e
      exact hnps (hpinj e)
  have hG : ∀ ψ, (GPsi (arith H.toHostRaw) ell ψ y).re = (An.gChi (H.prim (chr φ ψ)).χ y).re := by
    intro ψ
    rw [(prim_read φ H ell hell ψ).2 y]
  have key : ∑ ψ ∈ keptA Λ H.toHostRaw,
      (if H.prim (chr φ ψ) = PChar.one then 1 else Λ.wt (H.prim (chr φ ψ))) *
        (An.gChi (H.prim (chr φ ψ)).χ y).re =
      ∑ p ∈ Λ.KEPT, (if p = PChar.one then 1 else Λ.wt p) * (An.gChi p.χ y).re := by
    rw [hKimg, Finset.sum_image hinj]
  have hone : (An.gChi PChar.one.χ y).re = An.G y := by
    have h1 : PChar.one.χ = 1 := rfl
    unfold An.gChi
    rw [if_pos h1]
    simp
  unfold GmA Level.Gm Level.Nt
  rw [Finset.sum_congr rfl (fun ψ hψ => by rw [hw ψ hψ, hG ψ]), key,
    ← Finset.add_sum_erase _ _ Λ.one_mem]
  congr 1
  · rw [if_pos rfl, one_mul, (Gz_eq y).1, hone]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [if_neg (Finset.ne_of_mem_erase hp)]
end

-- bundled from Development.AutomorphicArithmetic.PrimitiveCosets.LevelFamily
section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

open Classical in
private noncomputable def UpperTheory.Comparison₂.level_family_wt (Λ : Level) (ψ : PChar) : ℝ :=
  if ψ = PChar.one then 1 else Λ.wt ψ

private theorem UpperTheory.Comparison₂.level_family_wt_pos (Λ : Level) (ψ : PChar) : 0 < UpperTheory.Comparison₂.level_family_wt Λ ψ := by
  unfold UpperTheory.Comparison₂.level_family_wt Level.wt
  split_ifs
  · exact one_pos
  · exact one_pos
  · positivity

private theorem UpperTheory.Comparison₂.level_family_adm (ψ : PChar) : ψ.N = 1 ∨ ψ.χ ≠ 1 := by
  by_cases h : ψ.χ = 1
  · left
    have hp := ψ.prim
    rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at hp
    exact hp.symm
  · exact Or.inr h

private theorem UpperTheory.Comparison₂.level_family_sum (Λ : Level) (y : ℝ) :
    ∑ ψ ∈ Λ.KEPT, UpperTheory.Comparison₂.level_family_wt Λ ψ * (Deduction.Gchi ψ.χ y).re = Λ.Gm y := by
  classical
  rw [← Finset.add_sum_erase _ _ Λ.one_mem, Level.Gm, Level.Nt]
  congr 1
  · have h1 : UpperTheory.Comparison₂.level_family_wt Λ PChar.one = 1 := by
      simp [UpperTheory.Comparison₂.level_family_wt]
    have hG : Formalism.Gz y = An.G y := by
      unfold Formalism.Gz Formalism.Sz An.G
      have hsum : (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / n - 1)) =
          ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / n - 1) 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.mp hn
        have hn_pos : 0 < n := Nat.zero_lt_of_lt hn₁
        have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff' hn_pos.ne').mp hn₂
        have hnonneg : 0 ≤ y / (n : ℝ) - 1 := by
          rw [sub_nonneg, le_div_iff₀ (Nat.cast_pos.mpr hn_pos), one_mul]
          exact hny
        rw [max_eq_left hnonneg]
      rw [hsum]
      ring
    rw [h1, one_mul, ← gChi_eq, hG]
    simp only [An.gChi, PChar.one]
    exact (congrArg Complex.re (ite_eq_left rfl)).trans (Complex.ofReal_re _)
  · refine Finset.sum_congr (by congr) fun ψ hψ => ?_
    have hne : ψ ≠ PChar.one := Finset.ne_of_mem_erase hψ
    simp only [UpperTheory.Comparison₂.level_family_wt, ite_eq_right hne, gChi_eq]

theorem UpperTheory.Comparison₂.level_family :
    ∀ Λ : Level, ∃ F : Deduction.CharFamily, (∀ y, Deduction.Gm F y = Λ.Gm y) ∧ ∀ θ, Deduction.ZeroFree F θ ↔ Λ.ZeroFreeAbove θ := by
  intro Λ
  refine ⟨@Deduction.CharFamily.mk Λ.KEPT _ (fun i => i.1.N) (fun i => i.1.ne) (fun i => i.1.χ) (fun i => UpperTheory.Comparison₂.level_family_wt Λ i.1) (fun i => UpperTheory.Comparison₂.level_family_wt_pos Λ i.1) (fun i => UpperTheory.Comparison₂.level_family_adm i.1), fun y => ?_, fun θ => ?_⟩
  · rw [← UpperTheory.Comparison₂.level_family_sum Λ y, Deduction.Gm]
    exact Finset.sum_coe_sort Λ.KEPT (fun ψ => UpperTheory.Comparison₂.level_family_wt Λ ψ * (Deduction.Gchi ψ.χ y).re)
  · simp only [Deduction.ZeroFree, Level.ZeroFreeAbove, PChar.ZeroFreeAbove]
    constructor
    · intro h ψ hψ s hs
      exact h ⟨ψ, hψ⟩ s hs
    · intro h i s hs
      exact h i.1 i.2 s hs
end

-- bundled from Development.AutomorphicArithmetic.PrimitiveCosets.SigALe
section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private theorem character_trivial_first_factor (φ : Frame) (ψ : AddChar (E0 × φ.A) ℂ) (h : ψ ∈ PsiA φ.A0) : Frame.TrivialOnFirstFactor (chr φ ψ) := by
  intro s hs
  apply Units.ext
  simp only [PsiA, Finset.mem_filter, Finset.mem_univ, true_and] at h
  have e : ((chr φ ψ (φ.tau1 s)) : ℂ) = ψ (0, s) := by
    simp [chr, toE, Frame.tau1, Frame.iotaInv, Frame.iota]
    rfl
  rw [e, Units.val_one]
  exact h s hs

private theorem chr_bounded (Λ : Level) (φ : Frame) (H : HostRaw φ) (ψ : AddChar (E0 × φ.A) ℂ) (h : ψ ∈ PsiA φ.A0)
    (hk : ψ ∉ keptA Λ H) : chr φ ψ ∈ H.Bounded Λ.KEPT := by
  have hT := character_trivial_first_factor φ ψ h
  have hsq : chr φ ψ φ.iod * chr φ ψ φ.iod = 1 := by
    rw [← map_mul]
    have e : φ.iod * φ.iod = 1 := by
      simp only [Frame.iod]
      ext <;> simp
    rw [e, map_one]
  have hv : (chr φ ψ φ.iod : ℂ) * (chr φ ψ φ.iod : ℂ) = 1 := by
    rw [← Units.val_mul, hsq, Units.val_one]
  rcases mul_self_eq_one_iff.mp hv with h1 | h1
  · left
    refine ⟨⟨hT, Units.ext (by simpa using h1)⟩, ?_⟩
    intro hK
    apply hk
    simpa [keptA] using hK
  · right
    exact ⟨hT, Units.ext (by simpa using h1)⟩

theorem UpperTheory.Comparison₂.sigA_le :
    ∀ (Λ : Level) (φ : Frame) (H : HostAx φ) (TT : Finset φ.A) (x eps C : ℝ) (ell : AddChar (E0 × φ.A) ℂ → ℂ), 0 < x →
      EAtH Λ H.toHostRaw TT x eps C → HostAddCharCompatible H.toHostRaw ell →
        SigA (arith H.toHostRaw) ell φ.A0 (keptA Λ H.toHostRaw) x ≤ 4 * (Λ.o : ℝ) * x ^ ((1 : ℝ) / 2 + eps) := by
  intro Λ φ H TT x eps C ell hx hE hell
  classical
  unfold SigA
  have hb : ∀ ψ ∈ PsiA φ.A0 \ keptA Λ H.toHostRaw,
      ‖GPsi (arith H.toHostRaw) ell ψ x‖ ≤ x ^ ((1 : ℝ) / 2 + eps) := by
    intro ψ hψ
    rw [Finset.mem_sdiff] at hψ
    rw [(prim_read φ H ell hell ψ).2 x]
    exact hE.bdG _ (chr_bounded Λ φ H.toHostRaw ψ hψ.1 hψ.2) _ _ (HostRaw.isPrimOf_prim _ _)
  calc _ ≤ ∑ ψ ∈ PsiA φ.A0 \ keptA Λ H.toHostRaw, x ^ ((1 : ℝ) / 2 + eps) := Finset.sum_le_sum hb
    _ = ((PsiA φ.A0 \ keptA Λ H.toHostRaw).card : ℝ) * x ^ ((1 : ℝ) / 2 + eps) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((PsiA φ.A0).card : ℝ) * x ^ ((1 : ℝ) / 2 + eps) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
        exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    _ = 4 * (Λ.o : ℝ) * x ^ ((1 : ℝ) / 2 + eps) := by
        rw [card_PsiA, hE.o_eq]
        push_cast
        ring
end

