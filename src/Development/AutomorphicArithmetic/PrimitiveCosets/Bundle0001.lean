module

public import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.PrimitiveCosets.CardPsiA
section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private theorem exists_comp_eq {G Q M : Type} [AddCommGroup G] [AddCommGroup Q] [CommGroupWithZero M] (π : G →+ Q)
    (hπ : Function.Surjective π) (ψ : AddChar G M) (h : ∀ x, π x = 0 → ψ x = 1) :
    ∃ χ : AddChar Q M, χ.compAddMonoidHom π = ψ := by
  have wd : ∀ x y, π x = π y → ψ x = ψ y := by
    intro x y hxy
    have h0 : π (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    calc ψ x = ψ (y + (x - y)) := by rw [add_sub_cancel]
      _ = ψ y * ψ (x - y) := AddChar.map_add_eq_mul ψ _ _
      _ = ψ y := by rw [h _ h0, mul_one]
  let s := Function.surjInv hπ
  have hs : ∀ q, π (s q) = q := Function.surjInv_eq hπ
  refine ⟨{ toFun := fun q => ψ (s q), map_zero_eq_one' := ?_, map_add_eq_mul' := ?_ }, ?_⟩
  · rw [wd (s 0) 0 (by rw [hs, map_zero]), AddChar.map_zero_eq_one]
  · intro a b
    rw [← AddChar.map_add_eq_mul, wd (s (a + b)) (s a + s b) (by rw [hs, map_add (f := _), hs, hs])]
  · ext x
    exact wd _ _ (hs _)

private theorem card_PsiA_index {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (A0 : AddSubgroup H) :
    (PsiA A0).card = 4 * A0.index := by
  classical
  let π : E0 × H →+ E0 × (H ⧸ A0) := (AddMonoidHom.id E0).prodMap (QuotientAddGroup.mk' A0)
  have hπ : Function.Surjective π := by
    rintro ⟨a, q⟩
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective A0 q
    exact ⟨(a, b), rfl⟩
  have inj : Function.Injective (fun χ : AddChar (E0 × (H ⧸ A0)) ℂ => χ.compAddMonoidHom π) := by
    intro χ1 χ2 h
    ext q
    obtain ⟨x, rfl⟩ := hπ q
    exact DFunLike.congr_fun h x
  have himg : PsiA A0 = Finset.univ.image (fun χ : AddChar (E0 × (H ⧸ A0)) ℂ => χ.compAddMonoidHom π) := by
    ext ψ
    simp only [PsiA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine exists_comp_eq π hπ ψ fun x hx => ?_
      obtain ⟨a, b⟩ := x
      have ha : a = 0 := congrArg Prod.fst hx
      have hb : (QuotientAddGroup.mk' A0 b) = 0 := congrArg Prod.snd hx
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at hb
      subst ha
      exact h b hb
    · rintro ⟨χ, rfl⟩ s hs
      show χ (π (0, s)) = 1
      have : π (0, s) = 0 := by
        simp [π, QuotientAddGroup.eq_zero_iff, hs]
      rw [this, AddChar.map_zero_eq_one]
  rw [himg, Finset.card_image_of_injective _ inj, Finset.card_univ, AddChar.card_eq, Fintype.card_prod,
    AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
  simp [E0]

theorem UpperTheory.Comparison₂.card_PsiA :
    ∀ φ : Frame, (PsiA φ.A0).card = 4 * φ.o := by
  intro φ
  rw [card_PsiA_index, φ.index_A0_eq_o]
end

-- bundled from Development.AutomorphicArithmetic.PrimitiveCosets.ChrBij
section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private theorem chr_val (φ : Frame) (ψ : AddChar (E0 × φ.A) ℂ) (g : φ.GG) :
    ((chr φ ψ g : ℂˣ) : ℂ) = ψ (Multiplicative.toAdd (toE φ g)) := rfl

private theorem sgn_val (s : ℤˣ) :
    (if Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 s) = 0 then (1 : ℂ) else -1) = ((s : ℤ) : ℂ) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · have h0 : Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 1) = 0 := by
      rw [map_one, toAdd_one]
    rw [if_pos h0]
    simp
  · have h1 : Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 (-1)) = 1 := by decide
    rw [h1, if_neg (by decide)]
    simp

theorem UpperTheory.Comparison₂.chr_bij :
    ∀ φ : Frame, Function.Bijective (chr φ) ∧ chr φ 0 = 1 ∧ chr φ chC = φ.chC ∧ chr φ psC = φ.psC ∧
      (∀ ψ g, ((chr φ ψ g : ℂˣ) : ℂ) = ψ (Multiplicative.toAdd (toE φ g))) ∧
      (∀ ψ, ψ ∈ PsiA φ.A0 ↔ Frame.TrivialOnFirstFactor (chr φ ψ)) ∧ ∀ ψ, chr φ ψ ∈ φ.Xp ↔ (ψ ∈ PsiA φ.A0 ∧ ψ sgc0 = 1) := by
  intro φ
  obtain ⟨hbij, hiod, -, htau, -⟩ := toE_bij φ
  have trivA : ∀ ψ, ψ ∈ PsiA φ.A0 ↔ Frame.TrivialOnFirstFactor (chr φ ψ) := by
    intro ψ
    have key : ∀ s : φ.A, ((chr φ ψ (φ.tau1 s) : ℂˣ) : ℂ) = ψ ((0 : E0), s) := by
      intro s
      rw [chr_val, htau]
      rfl
    simp only [PsiA, Frame.TrivialOnFirstFactor, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h s hs
      apply Units.ext
      rw [Units.val_one, key]
      exact h s hs
    · intro h s hs
      have h2 := congrArg Units.val (h s hs)
      rw [key, Units.val_one] at h2
      exact h2
  let e := MulEquiv.ofBijective (toE φ) hbij
  have he : ∀ g, e g = toE φ g := fun g => rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, chr_val φ, trivA, ?_⟩
  · intro ψ ψ' h
    apply AddChar.ext
    intro a
    obtain ⟨g, hg⟩ := hbij.2 (Multiplicative.ofAdd a)
    have h2 := congrArg (fun θ : φ.Char => ((θ g : ℂˣ) : ℂ)) h
    simp only [chr_val, hg, toAdd_ofAdd] at h2
    exact h2
  · intro θ
    let ψ : AddChar (E0 × φ.A) ℂ :=
      { toFun := fun a => ((θ (e.symm (Multiplicative.ofAdd a)) : ℂˣ) : ℂ)
        map_zero_eq_one' := by
          simp only [ofAdd_zero, map_one, Units.val_one]
        map_add_eq_mul' := by
          intro a b
          simp only [ofAdd_add, map_mul, Units.val_mul] }
    refine ⟨ψ, ?_⟩
    refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val]
    show ((θ (e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (toE φ g)))) : ℂˣ) : ℂ) = _
    rw [ofAdd_toAdd, ← he, MulEquiv.symm_apply_apply]
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val, MonoidHom.one_apply, Units.val_one, AddChar.zero_apply]
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val]
    show (if Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 g.1.2) = 0 then (1 : ℂ) else -1) = _
    rw [sgn_val]
    simp [Frame.chC, Frame.chD]
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val]
    show (if Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 g.1.1) = 0 then (1 : ℂ) else -1) = _
    rw [sgn_val]
    simp [Frame.psC, Frame.chQ]
  · intro ψ
    have hv : ((chr φ ψ φ.iod : ℂˣ) : ℂ) = ψ sgc0 := by
      rw [chr_val, hiod]
      rfl
    simp only [Frame.Xp, Set.mem_setOf_eq]
    rw [← trivA]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [← hv, h2, Units.val_one]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, Units.ext ?_⟩
      rw [hv, h2, Units.val_one]
end

-- bundled from Development.AutomorphicArithmetic.PrimitiveCosets.GChiEq
section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private theorem UpperTheory.Comparison₂.gChi_eq_ramp (f : ℕ → ℂ) (y : ℝ) :
    Deduction.ramp f y = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (An.abelian₂ n : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ) := by
  unfold Deduction.ramp
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _), zero_add]
  have e : Finset.Ico 1 ⌊y⌋₊.succ = Finset.Icc 1 ⌊y⌋₊ := by
    ext n
    simp [Nat.lt_succ_iff]
  rw [e]
  simp

theorem UpperTheory.Comparison₂.gChi_eq :
    ∀ (ψ : PChar) (y : ℝ), An.gChi ψ.χ y = Deduction.Gchi ψ.χ y := by
  intro ψ y
  unfold An.gChi Deduction.Gchi
  rw [UpperTheory.Comparison₂.gChi_eq_ramp]
  by_cases h : ψ.χ = 1
  · rw [if_pos h, if_pos h]
    have hN : ψ.N = 1 := by
      have hp : ψ.χ.conductor = ψ.N := ψ.prim
      rw [h, DirichletCharacter.conductor_one] at hp
      exact hp.symm
    have h2 : ∀ n : ℕ, ψ.χ (n : ZMod ψ.N) = 1 := fun n => by
      rw [h]
      refine MulChar.one_apply ?_
      rw [ZMod.isUnit_iff_coprime, hN]
      exact Nat.coprime_one_right n
    simp only [h2, An.G, mul_one]
    push_cast
    ring
  · rw [if_neg h, if_neg h]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.PrimitiveCosets.GzEq
section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

theorem UpperTheory.Comparison₂.Gz_eq :
    ∀ y : ℝ, Formalism.Gz y = An.G y ∧ An.G y = Deduction.G y := by
  intro y
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / (n : ℝ) - 1)
      = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / (n : ℝ) - 1) 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hy : (n : ℝ) ≤ y := by
      have hk : 0 < ⌊y⌋₊ := lt_of_lt_of_le Nat.zero_lt_one (le_trans hn.1 hn.2)
      have hy0 : 0 ≤ y := by
        by_contra hneg
        push_neg at hneg
        rw [Nat.floor_eq_zero.2 (lt_trans hneg zero_lt_one)] at hk
        exact lt_irrefl 0 hk
      exact le_trans (by exact_mod_cast hn.2) (Nat.floor_le hy0)
    have hpos : (0 : ℝ) < n := by linarith
    have : 0 ≤ y / (n : ℝ) - 1 := by
      rw [sub_nonneg, le_div_iff₀ hpos, one_mul]
      exact hy
    rw [max_eq_left this]
  have hre : (Deduction.ramp (fun _ => 1) y).re
      = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / (n : ℝ) - 1) 0 := by
    have hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.range (⌊y⌋₊ + 1) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_range]
      omega
    rw [Finset.sum_subset hsub]
    · simp [Deduction.ramp, Complex.re_sum]
    · intro n hn hn'
      have h0 : n = 0 := by
        rw [Finset.mem_range] at hn
        rw [Finset.mem_Icc] at hn'
        omega
      subst h0
      simp
  refine ⟨?_, ?_⟩
  · simp only [Formalism.Gz, Formalism.Sz, An.G]
    rw [hsum]
    ring
  · simp only [An.G, Deduction.G]
    rw [hre]
    ring
end

-- bundled from Development.AutomorphicArithmetic.PrimitiveCosets.PrimInj
section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

theorem UpperTheory.Comparison₂.prim_inj :
    ∀ (φ : Frame) (H : HostAx φ), Function.Injective H.toHostRaw.prim ∧ H.toHostRaw.prim 1 = PChar.one := by
  intro φ H
  constructor
  · intro θ θ' h
    apply MonoidHom.ext
    intro g
    obtain ⟨u, rfl⟩ := HostDer.art_surj H.der g
    have h1 := (H.toHostRaw.isPrimOf_prim θ).2
    have h2 := (H.toHostRaw.isPrimOf_prim θ').2
    rw [← h] at h2
    have hc := ZMod.val_coe_unit_coprime u
    have e := (h1 _ hc).symm.trans (h2 _ hc)
    apply Units.ext
    rw [← HostRaw.dir_unit, ← HostRaw.dir_unit]
    simpa [HostRaw.dirAt, ZMod.natCast_zmod_val] using e
  · have hd : H.toHostRaw.dir 1 = 1 := by
      apply MulChar.ext
      intro u
      rw [HostRaw.dir_unit]
      simp
    rw [HostRaw.prim, hd, PChar.of_one]
end

-- bundled from Development.AutomorphicArithmetic.PrimitiveCosets.PrimRead
section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private theorem UpperTheory.Comparison₂.prim_read_dir (φ : Frame) (H : HostRaw φ) (ψ : AddChar (E0 × φ.A) ℂ) :
    H.dir (chr φ ψ) = dirChar (recH H) ψ := by
  refine MulChar.ext fun u => ?_
  rw [H.dir_unit, dirChar_unit]
  rfl

private theorem UpperTheory.Comparison₂.prim_read_surj (φ : Frame) : Function.Surjective (toE φ) := by
  have key : ∀ a : ZMod 2, ∃ s : ℤˣ, Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 s) = a := by
    intro a
    fin_cases a
    · exact ⟨1, by simp [LFunctionChainParameters.LHost.sgn2] <;> rfl⟩
    · exact ⟨-1, by simp [LFunctionChainParameters.LHost.sgn2] <;> rfl⟩
  intro x
  obtain ⟨s1, hs1⟩ := key (Multiplicative.toAdd x).1.1
  obtain ⟨s2, hs2⟩ := key (Multiplicative.toAdd x).1.2
  refine ⟨((s2, s1), Multiplicative.ofAdd (Multiplicative.toAdd x).2), ?_⟩
  simp only [toE, MonoidHom.coe_mk, OneHom.coe_mk, hs1, hs2]
  rfl

private theorem UpperTheory.Comparison₂.prim_read_max (y : ℝ) (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊y⌋₊) :
    max (y / n - 1) 0 = y / n - 1 := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
  have hpos : (0 : ℝ) < n := by exact_mod_cast h1
  have hfl : 0 < ⌊y⌋₊ := by omega
  have hy : 1 ≤ y := Nat.floor_pos.mp hfl
  have hny : (n : ℝ) ≤ y := (Nat.cast_le.mpr h2).trans (Nat.floor_le (by linarith))
  have h1y : 1 ≤ y / n := (one_le_div hpos).mpr hny
  exact max_eq_left (by linarith)

private theorem UpperTheory.Comparison₂.prim_read_Gz (y : ℝ) : Gz y = An.G y := by
  unfold Gz Sz An.G
  rw [Finset.sum_congr rfl fun n hn => congrArg (fun t => An.abelian₂ n * t) (UpperTheory.Comparison₂.prim_read_max y n hn)]
  ring

private theorem UpperTheory.Comparison₂.prim_read_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    χ.primitiveCharacter = 1 ↔ χ = 1 := by
  constructor
  · intro h
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h, map_one]
  · rintro rfl
    exact DirichletCharacter.primitiveCharacter_one

theorem UpperTheory.Comparison₂.prim_read :
    ∀ (φ : Frame) (H : HostAx φ) (ell : AddChar (E0 × φ.A) ℂ → ℂ), HostAddCharCompatible H.toHostRaw ell → ∀ ψ : AddChar (E0 × φ.A) ℂ,
      (ψ ≠ 0 → ell ψ = An.logDerivativeAtOne (H.toHostRaw.prim (chr φ ψ)).χ) ∧
        ∀ y, GPsi (arith H.toHostRaw) ell ψ y = An.gChi (H.toHostRaw.prim (chr φ ψ)).χ y := by
  intro φ H ell hell ψ
  unfold HostAddCharCompatible at hell
  set R := H.toHostRaw with hR
  have hdir : R.dir (chr φ ψ) = dirChar (recH R) ψ := prim_read_dir φ R ψ
  have hval : ∀ n : ℕ, n ≠ 0 → (R.prim (chr φ ψ)).χ n = primVal (arith R) ψ n := by
    intro n hn
    show (R.dir (chr φ ψ)).primitiveCharacter n = _
    rw [hdir]
    exact (primitive_value_primitive (H := φ.A) R.condN R.q R.d (recH R) ψ n
      (HostRaw.condN_pos R).ne' hn).symm
  have h1 : ψ ≠ 0 → ell ψ = An.logDerivativeAtOne (R.prim (chr φ ψ)).χ := fun hψ =>
    @hell ψ hψ _ (R.prim (chr φ ψ)).ne _ (R.prim (chr φ ψ)).prim hval
  have hone : (R.prim (chr φ ψ)).χ = 1 ↔ ψ = 0 := by
    show (R.dir (chr φ ψ)).primitiveCharacter = 1 ↔ ψ = 0
    rw [prim_read_one, hdir]
    constructor
    · intro h
      rw [AddChar.eq_zero_iff]
      intro x
      obtain ⟨g, hg⟩ := prim_read_surj φ (Multiplicative.ofAdd x)
      obtain ⟨u, hu⟩ := HostDer.art_surj H.der g
      have hu1 : (dirChar (recH R) ψ) u = 1 := by
        rw [h]
        exact MulChar.one_apply_coe u
      rw [dirChar_unit] at hu1
      have e : recH R u = Multiplicative.ofAdd x := by
        show toE φ (R.art u) = _
        rw [hu, hg]
      rwa [e, toAdd_ofAdd] at hu1
    · rintro rfl
      refine MulChar.ext fun u => ?_
      rw [dirChar_unit, AddChar.zero_apply, MulChar.one_apply_coe]
  refine ⟨h1, fun y => ?_⟩
  by_cases hψ : ψ = 0
  · have hχ : (R.prim (chr φ ψ)).χ = 1 := hone.mpr hψ
    unfold GPsi An.gChi
    rw [if_pos hψ, if_pos hχ, prim_read_Gz]
  · have hχ : (R.prim (chr φ ψ)).χ ≠ 1 := fun h => hψ (hone.mp h)
    unfold GPsi An.gChi
    rw [if_neg hψ, if_neg hχ, ← h1 hψ, An.sumLamChi]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    rw [hval n hn0, prim_read_max y n hn]
end

