module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SLetCastSucc
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0011
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0005

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationZpOfNumericBound
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Inst

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestValNum : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      ∀ l ∈ levels (gB C0 CE1 CE2 X aTop aPlus b),
        ∀ (j' : Fin (gB C0 CE1 CE2 X aTop aPlus b).T.t → ℕ) (jp' : ℕ), (gB C0 CE1 CE2 X aTop aPlus b).LevelOK j' jp' →
        ∀ μ : Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t →₀ ℕ,
          (∀ a, Finsupp.weight (wL (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) a) μ =
            dLvl (gB C0 CE1 CE2 X aTop aPlus b) j' jp' a) →
          (padicValNat X.p (lvC (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2 *
              degFact (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2) : ℝ) +
            2 * (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ) ≤
          (padicValNat X.p (μ.prod fun _ k => k.factorial) : ℝ) + levelPassageLoss X

theorem restVal_of_num (h : RestValNum C0 CE1 CE2 X) : RestVal C0 CE1 CE2 X := by
  intro aTop hT aPlus hP b hK l hl z hz μ hμ
  obtain ⟨j', jp', hl', hw⟩ := SSZ_support X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) z hz μ hμ
  exact h aTop hT aPlus hP b hK l hl j' jp' hl' μ hw

theorem block_valuation_Zp_of_numeric_bound {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (hV : RestValNum C0 CE1 CE2 X) : BlockBoundIntegers C0 CE1 CE2 X :=
  block_valuation_Zp_of_valuation_bound C0 CE1 CE2 X hCYb hCE1 hCE2 hH (restVal_of_num C0 CE1 CE2 X hV)

end Inst

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.CmapMemRestrictSupport
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G

section CMap

variable {K L σ : Type} [CommRing K] [CommRing L] (f : K →+ L)

theorem cmap_add (y z : MvPolynomial σ K) : cmap f (y + z) = cmap f y + cmap f z := by
  ext m; simp only [MvPolynomial.coeff_add, coeff_cmap, map_add (f := _)]

theorem cmap_zero : cmap f (0 : MvPolynomial σ K) = 0 := by
  ext m; simp only [coeff_cmap, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_zero]

theorem cmap_neg (y : MvPolynomial σ K) : cmap f (-y) = -cmap f y := by
  ext m; simp only [coeff_cmap, coeff_neg, map_neg]

theorem cmap_monomial (n : σ →₀ ℕ) (c : K) : cmap f (monomial n c) = monomial n (f c) := by
  classical
  ext m
  rw [coeff_cmap, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

def cmapHom : MvPolynomial σ K →+ MvPolynomial σ L where
  toFun := cmap f
  map_zero' := cmap_zero f
  map_add' := cmap_add f

theorem X_mul_monomial' (v : σ) (n : σ →₀ ℕ) (c : K) :
    (X v : MvPolynomial σ K) * monomial n c = monomial (Finsupp.single v 1 + n) c := by
  rw [X, monomial_mul, one_mul]

theorem cmap_X_pderiv (v w : σ) (y : MvPolynomial σ K) :
    cmap f (X v * pderiv w y) = X v * pderiv w (cmap f y) := by
  classical
  induction y using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [pderiv_monomial, cmap_monomial, pderiv_monomial, X_mul_monomial', X_mul_monomial', cmap_monomial]
    congr 1
    rw [mul_comm c, mul_comm (f c)]
    have e1 : ((n w : ℕ) : K) * c = (n w) • c := (nsmul_eq_mul _ _).symm
    have e2 : ((n w : ℕ) : L) * f c = (n w) • f c := (nsmul_eq_mul _ _).symm
    rw [e1, e2, map_nsmul]
  | add p q hp hq =>
    rw [map_add (f := _), mul_add, cmap_add, hp, hq, cmap_add, map_add (f := _), mul_add]

end CMap

section Fun

variable {O : Type} [CommRing O] [IsDomain O] {p : ℕ} [Fact p.Prime] (f : KK O →+ ℚ_[p])

theorem cmap_glAct {N r : ℕ} (LL : ChainLetters N) (j : ℕ) (c d : Fin r) (y : MvPolynomial (Fin N × Fin r) (KK O)) :
    cmap f (glAct (KK O) (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d y) =
      Formalism.GM.M.glAct p (gmL LL) j c d (cmap f y) := by
  unfold Formalism.MainNotions.G.glAct Formalism.GM.M.glAct
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  show cmapHom f _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show cmap f _ = _
  by_cases hi : (i : ℕ) < j
  · have hi' : i ∈ {i : Fin N | (i : ℕ) < j} := hi
    rw [if_pos hi', if_pos hi]
    by_cases hv : LL.vec i = true
    · have hv' : (gmL LL).vec i = true := hv
      have hv'' : (⟨LL.vec⟩ : Letters (Fin N)).vec i = true := hv
      rw [if_pos hv'', if_pos hv']
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply]
      exact cmap_X_pderiv f _ _ y
    · have hv' : ¬ (gmL LL).vec i = true := hv
      have hv'' : ¬ (⟨LL.vec⟩ : Letters (Fin N)).vec i = true := hv
      rw [if_neg hv'', if_neg hv']
      simp only [LinearMap.neg_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply]
      rw [cmap_neg]
      exact congrArg Neg.neg (cmap_X_pderiv f _ _ y)
  · have hi' : i ∉ {i : Fin N | (i : ℕ) < j} := hi
    rw [if_neg hi', if_neg hi]
    simp only [LinearMap.zero_apply]
    exact cmap_zero f

theorem cmap_support_subset {σ : Type} (y : MvPolynomial σ (KK O)) : (cmap f y).support ⊆ y.support := by
  intro m hm
  rw [mem_support_iff] at hm ⊢
  intro h0
  apply hm
  rw [coeff_cmap, h0, map_zero]

theorem sk_ycond_stable {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) (Mt : WithTop ℤ) (c d : Fin r) :
    ∀ x ∈ Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt,
      glAct (KK O) (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d x ∈ Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt := by
  unfold Formalism.MainNotions.G.YCond
  intro x hx
  have : sSup {S : Submodule (KK O) (MvPolynomial (Fin N × Fin r) (KK O)) |
      S ≤ restrictSupport (KK O) {m : Fin N × Fin r →₀ ℕ | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧
        chStable (KK O) LL j S} ≤
      (sSup {S : Submodule (KK O) (MvPolynomial (Fin N × Fin r) (KK O)) |
      S ≤ restrictSupport (KK O) {m : Fin N × Fin r →₀ ℕ | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧
        chStable (KK O) LL j S}).comap (glAct (KK O) (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d) :=
    sSup_le fun S hS x hx => le_sSup hS (hS.2 c d x hx)
  exact this hx

theorem sk_ycond_supp {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) (Mt : WithTop ℤ) :
    Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt ≤
      restrictSupport (KK O) {m : Fin N × Fin r →₀ ℕ | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} :=
  sSup_le fun _ hS => hS.1

theorem cmap_mem_restrictSupport {σ : Type} {s : Set (σ →₀ ℕ)} (y : MvPolynomial σ (KK O))
    (hy : y ∈ restrictSupport (KK O) s) : cmap f y ∈ restrictSupport ℚ_[p] s := by
  rw [mem_restrictSupport_iff] at hy ⊢
  exact (Finset.coe_subset.2 (cmap_support_subset f y)).trans hy

theorem cmap_ycond (ι : ℚ_[p] →+* KK O) (_hf : ∀ (a : ℚ_[p]) (x : KK O), f (ι a * x) = a * f x)
    {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) (Mt : WithTop ℤ)
    (y : MvPolynomial (Fin N × Fin r) (KK O)) (hy : y ∈ Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt) :
    cmap f y ∈ Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt := by
  set S' : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    Submodule.span ℚ_[p] (cmap f '' (Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt : Set _)) with hS'
  have h1 : S' ≤ restrictSupport ℚ_[p] {m | ((Formalism.GM.M.wt (gmL LL) j 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
    rw [hS', Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact cmap_mem_restrictSupport f z (sk_ycond_supp LL j Mt hz)
  have h2 : Formalism.GM.M.GlStable p (gmL LL) j S' := by
    intro c d x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      rw [← cmap_glAct]
      exact Submodule.subset_span ⟨_, sk_ycond_stable LL j Mt c d z hz, rfl⟩
    | zero => rw [map_zero]; exact S'.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact S'.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact S'.smul_mem a hx
  have h3 : S' ≤ Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt := by
    unfold Formalism.GM.M.YCond
    exact le_sSup ⟨h1, h2⟩
  exact h3 (Submodule.subset_span ⟨y, hy, rfl⟩)

end Fun

theorem restFunY_proved : RestFunY := by
  intro O _ _ p _ ι N r _ LL q J M f hf y hy
  obtain ⟨hP, hC⟩ := hy
  refine ⟨cmap_mem_restrictSupport f y hP, ?_⟩
  have hC' : y ∈ ⨅ k, Formalism.MainNotions.G.YCond (KK O) (r := r) LL (J k) (M k) := hC
  show cmap f y ∈ ⨅ k, Formalism.GM.M.YCond p (r := r) (gmL LL) (J k) (M k)
  rw [Submodule.mem_iInf] at hC' ⊢
  exact fun k => cmap_ycond f ι hf LL (J k) (M k) y (hC' k)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.MemLevelsIff
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem mem_levels_iff' {N : ℕ} (G : Formalism.GM.M.BlockData N) (x : (Fin G.T.t → ℕ) × ℕ) :
    x ∈ levels G ↔ G.LevelOK x.1 x.2 := by
  unfold levels
  simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨⟨fun i => ?_, ?_⟩, h⟩⟩
  · have hle := Finset.single_le_sum (s := Finset.univ) (f := fun a => G.LL.deg a)
      (fun a _ => Nat.zero_le _) (Finset.mem_univ (⟨min (G.T.pos i) (N - 1), by
        rcases Nat.eq_zero_or_pos N with h0 | h0
        · exact absurd G.uPos.2 (by omega)
        · omega⟩ : Fin N))
    have h1 := (h.1 i).1
    omega
  · have h2 := h.2
    have h3 := min_le_right (G.LL.deg G.uPos) G.B
    omega

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestBClvl : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b → ∀ l ∈ lv C0 CE1 CE2 X aTop b,
      Module.finrank (KK X.O) (Submodule.span (KK X.O)
        ((blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b).gens X.O (r := X.r) l.1 l.2)) ≤
      Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2)

theorem restBCdim_of (h : RestBClvl C0 CE1 CE2 X) : RestBCdim C0 CE1 CE2 X := by
  intro aTop hT aPlus hP b hk
  rw [finrank_blockLat X.O X.p X.r (Formalism.MainNotions.G.GLWeightTheory.valuation_properties_hold X.std.1.prime X.setting) (X.S C0 CE1 CE2) aTop aPlus X.m b]
  unfold blockRank
  simp only
  set D := blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b with hD
  have hU : Submodule.span (KK X.O) ((D.SSZ X.O (r := X.r) : Submodule X.O _) :
        Set (MvPolynomial (BVar (2 * X.s + 1) X.r D.T.t) (KK X.O))) ≤
      ⨆ l ∈ lv C0 CE1 CE2 X aTop b, Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2) := by
    rw [Submodule.span_le]
    intro x hx
    have hx' : x ∈ Submodule.span X.O (⋃ (j : Fin D.T.t → ℕ) (jp : ℕ) (_ : D.LevelOK j jp), D.gens X.O (r := X.r) j jp) := hx
    refine Submodule.span_induction (p := fun x _ => x ∈ ⨆ l ∈ lv C0 CE1 CE2 X aTop b,
        Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) ?_ ?_ ?_ ?_ hx'
    · intro y hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨j, jp, hl, hy⟩ := hy
      have hmem : ((j, jp) : Lv C0 CE1 CE2 X) ∈ lv C0 CE1 CE2 X aTop b := by
        exact (mem_levels_iff' (gB C0 CE1 CE2 X aTop 0 b) (j, jp)).2 hl
      exact (le_iSup₂ (f := fun (l : Lv C0 CE1 CE2 X) (_ : l ∈ lv C0 CE1 CE2 X aTop b) =>
        Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) (j, jp) hmem) (Submodule.subset_span hy)
    · exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      rw [algebra_compatible_smul (KK X.O) a x]
      exact Submodule.smul_mem _ _ hx
  have := span_SSZ_finite (O := X.O) (r := X.r) D
  have hfd : ∀ l ∈ lv C0 CE1 CE2 X aTop b,
      FiniteDimensional (KK X.O) (Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) := by
    intro l hl
    have hsub : Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2) ≤
        Submodule.span (KK X.O) ((D.SSZ X.O (r := X.r) : Submodule X.O _) :
          Set (MvPolynomial (BVar (2 * X.s + 1) X.r D.T.t) (KK X.O))) := by
      apply Submodule.span_mono
      intro y hy
      apply Submodule.subset_span
      refine Set.mem_iUnion.2 ⟨l.1, Set.mem_iUnion.2 ⟨l.2, Set.mem_iUnion.2 ⟨?_, hy⟩⟩⟩
      exact (mem_levels_iff' (gB C0 CE1 CE2 X aTop 0 b) l).1 hl
    exact Submodule.finiteDimensional_of_le hsub
  obtain ⟨hfd2, hle⟩ := finrank_biSup_le (fun l : Lv C0 CE1 CE2 X =>
    Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) (lv C0 CE1 CE2 X aTop b) hfd
  calc Module.finrank (KK X.O) (Submodule.span (KK X.O) ((D.SSZ X.O (r := X.r) : Submodule X.O _) :
          Set (MvPolynomial (BVar (2 * X.s + 1) X.r D.T.t) (KK X.O))))
      ≤ Module.finrank (KK X.O) (⨆ l ∈ lv C0 CE1 CE2 X aTop b,
          Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2) : Submodule (KK X.O) _) :=
        Submodule.finrank_mono hU
    _ ≤ ∑ l ∈ lv C0 CE1 CE2 X aTop b, Module.finrank (KK X.O) (Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) :=
        hle
    _ ≤ ∑ l ∈ lv C0 CE1 CE2 X aTop b,
          Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2) :=
        Finset.sum_le_sum fun l hl => h aTop hT aPlus hP b hk l hl

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PlusAWICondition
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem mono_mem_xiPolZ (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n) :
    monomial m (1 : ℚ_[p]) ∈ Formalism.GM.M.XiPolZ p N r G.T.t n := by
  classical
  obtain ⟨h1, h2, -⟩ := xiMons_spec (r := r) G n m hm
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff]
    intro m' hm'
    have hm2 : m' = m := Finset.mem_singleton.1 (support_monomial_subset hm')
    subst hm2
    exact ⟨h1, h2⟩
  · exact ⟨monomial m 1, by simp⟩

theorem pderiv_chain_mono (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n)
    (a : Fin N) (c : Fin r) : pderiv (Sum.inl (Fin.castSucc a, c)) (monomial m (1 : ℚ_[p])) = 0 := by
  obtain ⟨h1, -, -⟩ := xiMons_spec (r := r) G n m hm
  rw [pderiv_monomial]
  have : m (Sum.inl (Fin.castSucc a, c)) = 0 := by
    by_contra hne
    obtain ⟨d, hd⟩ := h1 _ (Finsupp.mem_support_iff.2 hne)
    simp only [Formalism.GM.M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at hd
    exact absurd hd.1 (Fin.castSucc_ne_last a)
  rw [this]
  simp

theorem mono_chain_zero (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n)
    (x : Fin N × Fin r) : m (Formalism.GM.M.chainEmb N r G.T.t x) = 0 := by
  obtain ⟨h1, -, -⟩ := xiMons_spec (r := r) G n m hm
  by_contra hne
  obtain ⟨d, hd⟩ := h1 _ (Finsupp.mem_support_iff.2 hne)
  simp only [Formalism.GM.M.chainEmb, Formalism.GM.M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at hd
  exact absurd hd.1 (Fin.castSucc_ne_last x.1)

theorem chainEmb_inj : Function.Injective (Formalism.GM.M.chainEmb N r G.T.t) := by
  intro x y h
  simp only [Formalism.GM.M.chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h
  exact Prod.ext (Fin.castSucc_injective _ h.1) h.2

theorem cf_mul (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n) :
    (((n.factorial / (m.prod fun _ k => k.factorial) : ℕ) : ℚ_[p]) * (mfac m : ℚ_[p])) = (n.factorial : ℚ_[p]) := by
  obtain ⟨-, -, h3⟩ := xiMons_spec (r := r) G n m hm
  have hdvd : (m.prod fun _ k => k.factorial) ∣ n.factorial := by
    have := Nat.prod_factorial_dvd_factorial_sum m.support m
    rw [h3] at this
    exact this
  have e : (mfac m : ℚ_[p]) = ((m.prod fun _ k => k.factorial : ℕ) : ℚ_[p]) := by
    unfold mfac Finsupp.prod
    push_cast
    rfl
  rw [e, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]

theorem plusAW_of_blockOK (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) : RestPlusAW p (r := r) G j jp D := by
  classical
  unfold RestPlusAW
  obtain ⟨x, y, hx, hy, hxy⟩ := goodCount_mem p
    (fun F F' => Formalism.GM.M.fockN p (G.lettersAt j jp) (G.T.phis p (r := r) (G.lettersAt j jp) F) F')
    (Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr) D
  have hcard : (xiMons (r := r) G (G.B - jp)).card = dXi r (G.B - jp) := card_xiMons_eq (r := r) G (G.B - jp)
  let e := Fintype.equivFin (Fin (Formalism.GM.M.goodCount p
    (fun F F' => Formalism.GM.M.fockN p (G.lettersAt j jp) (G.T.phis p (r := r) (G.lettersAt j jp) F) F')
    (Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr) D) × (xiMons (r := r) G (G.B - jp)))
  let cfn : (Formalism.GM.M.BVar N r G.T.t →₀ ℕ) → ℕ := fun m => (G.B - jp).factorial / (m.prod fun _ k => k.factorial)
  have hXm : ∀ k, rename (Formalism.GM.M.chainEmb N r G.T.t) (x (e.symm k).1) * monomial (e.symm k).2.1 (1 : ℚ_[p]) ∈
      Ljj p (r := r) G j jp := fun k =>
    Submodule.subset_span ⟨x (e.symm k).1, hx _, _, mono_mem_xiPolZ p (r := r) G (G.B - jp) _ (e.symm k).2.2, rfl⟩
  have hYm : ∀ k, ((cfn (e.symm k).2.1 : ℕ) : ℚ_[p]) •
      (rename (Formalism.GM.M.chainEmb N r G.T.t) (y (e.symm k).1) * monomial (e.symm k).2.1 (1 : ℚ_[p])) ∈
      Ljj p (r := r) G j jp := by
    intro k
    have h1 : rename (Formalism.GM.M.chainEmb N r G.T.t) (y (e.symm k).1) * monomial (e.symm k).2.1 (1 : ℚ_[p]) ∈
        Ljj p (r := r) G j jp :=
      Submodule.subset_span ⟨y (e.symm k).1, hy _, _, mono_mem_xiPolZ p (r := r) G (G.B - jp) _ (e.symm k).2.2, rfl⟩
    have h2 := Submodule.smul_mem (Ljj p (r := r) G j jp) ((cfn (e.symm k).2.1 : ℕ) : ℤ_[p]) h1
    rw [algebra_compatible_smul ℚ_[p] ((cfn (e.symm k).2.1 : ℕ) : ℤ_[p]), map_natCast] at h2
    exact h2
  have hpair : ∀ k k', bePhi p (r := r) G j jp
      (rename (Formalism.GM.M.chainEmb N r G.T.t) (x (e.symm k).1) * monomial (e.symm k).2.1 (1 : ℚ_[p]))
      (((cfn (e.symm k').2.1 : ℕ) : ℚ_[p]) •
        (rename (Formalism.GM.M.chainEmb N r G.T.t) (y (e.symm k').1) * monomial (e.symm k').2.1 (1 : ℚ_[p]))) =
      if k = k' then (p : ℚ_[p]) ^ D else 0 := by
    intro k k'
    obtain ⟨⟨i, m, hm⟩, hk⟩ : ∃ q, e.symm k = q := ⟨_, rfl⟩
    obtain ⟨⟨i', m', hm'⟩, hk'⟩ : ∃ q, e.symm k' = q := ⟨_, rfl⟩
    have hkk : k = k' ↔ (i = i' ∧ m = m') := by
      constructor
      · rintro rfl
        rw [hk] at hk'
        simp only [Prod.mk.injEq, Subtype.mk.injEq] at hk'
        exact hk'
      · rintro ⟨rfl, rfl⟩
        exact e.symm.injective (hk.trans hk'.symm)
    rw [hk, hk']
    dsimp only
    rw [bePhi_smul_right]
    unfold bePhi
    rw [phisB_rename_mul p (r := r) G hB j jp _ _ (fun a c => pderiv_chain_mono p (r := r) G (G.B - jp) m hm a c),
      fockK_rename_mul _ (chainEmb_inj (r := r) G) _ _ m m' 1 (mono_chain_zero (r := r) G (G.B - jp) m hm)
        (mono_chain_zero (r := r) G (G.B - jp) m' hm')]
    have hxy' : Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
        ∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p]) = if i = i' then (p : ℚ_[p]) ^ D else 0 := hxy i i'
    by_cases hmm : m = m'
    · subst hmm
      rw [if_pos rfl]
      have hcf := cf_mul p (r := r) G (G.B - jp) m hm
      have hdeg : (degFact G j jp : ℚ_[p]) =
          (∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) * ((G.B - jp).factorial : ℚ_[p]) := by
        unfold degFact; push_cast; rfl
      have hF : Formalism.GM.M.fockK (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') =
          Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') := rfl
      have hP : (∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun a _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have hn0 : ((G.B - jp).factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      rw [hdeg, hF]
      have key : ((cfn m : ℕ) : ℚ_[p]) *
          (1 * mfac m * Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
            ((∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) * ((G.B - jp).factorial : ℚ_[p]))) =
          Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
            ∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p]) := by
        rw [show ((cfn m : ℕ) : ℚ_[p]) *
            (1 * mfac m * Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
              ((∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) * ((G.B - jp).factorial : ℚ_[p]))) =
            (((cfn m : ℕ) : ℚ_[p]) * mfac m) * Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
              ((∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) * ((G.B - jp).factorial : ℚ_[p])) by ring]
        rw [hcf]
        field_simp
      rw [key, hxy']
      by_cases hii : i = i'
      · rw [if_pos hii, if_pos (hkk.2 ⟨hii, rfl⟩)]
      · rw [if_neg hii, if_neg (fun h => hii (hkk.1 h).1)]
    · rw [if_neg hmm, if_neg (fun h => hmm (hkk.1 h).2)]
      simp
  have hmem := le_csSup (gcL_bdd p (r := r) G j jp D) ⟨fun k => _, fun k => _, hXm, hYm, hpair⟩
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, hcard] at hmem
  exact hmem

end Level

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem plusAWICondition (CM : ℝ) : RestPlusAWI C0 CE1 CE2 X CM := by
  intro dl _ aTop _ x _
  exact plusAW_of_blockOK X.p (gB C0 CE1 CE2 X aTop 0 x.1) (gB_blockOK C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 _

theorem plusACondition (CM : ℝ) : RestPlusA C0 CE1 CE2 X CM :=
  restPlusA_of C0 CE1 CE2 X CM (plusAWICondition C0 CE1 CE2 X CM)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

