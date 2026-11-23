module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Ex0

def SecEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S₀ : Finset (Pl E)), S₀.card ≤ 1 →
  ∃ Sec : Set (Pl E), IsSection Sec ∧ (∀ w ∈ S₀, w ∈ Sec) ∧ ∀ w, ¬ IsSplitAt w → w ∈ Sec

def MuEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E →
  ∃ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e ∧ (∀ w : Pl E, ¬ IsSplitAt w → μ.UnrAt w) ∧ (∀ᶠ w : Pl E in cofinite, μ.UnrAt w) ∧
    ∀ w : Pl E, IsOpen ((μ.loc w).ker : Set (w.adicCompletion E)ˣ)

def UnifEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ w : Pl E,
  ∃ ϖ : (w.adicCompletion E)ˣ, IsUnifAt ϖ ∧ IsUnifV E w (ϖ : w.adicCompletion E)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsPairLevel {a b : ℕ} {w : Pl E} (L : Subgroup (GLw a w × GLw b w)) : Prop :=
  ∃ L₁ L₂, L = Subgroup.prod L₁ L₂ ∧ GlobalTheory.BCT.IsLevel (thL a w) (KGL w (n := a)) L₁ ∧ GlobalTheory.BCT.IsLevel (thL b w) (KGL w (n := b)) L₂

def SplitEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w →
  ∀ μ : (w.adicCompletion E)ˣ →* ℂˣ, IsOpen (μ.ker : Set (w.adicCompletion E)ˣ) → ∀ m : ℕ, 1 ≤ m → ∀ KB : Subgroup (UL n w), IsCong m KB →
    ∃ (K' : Subgroup (GLw n w)) (X : Finset (GLw n w)) (e : GLw n w → ℂ) (L : ∀ a : ℕ, Subgroup (GLw a w × GLw (n - a) w)),
      K'.subgroupOf (UL n w) = KB ∧ IsOpen (K' : Set (GLw n w)) ∧ K' ≤ KGL w (n := n) ∧
      (∀ k ∈ KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') ∧ (∀ x ∈ X, x ∈ KGL w (n := n)) ∧ (∀ k ∈ KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') ∧
      IsHk K' e ∧ ∀ a (ha : a ≤ n), IsPairLevel (L a) ∧ ∀ y ∈ L a, y ∈ leviOf (Nat.add_sub_of_le ha) w K' ∧
        μ (GeneralLinearGroup.det y.1 ^ (n - a) * GeneralLinearGroup.det y.2 ^ a) = 1

def KEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Sec : Set (Pl E)), IsSection Sec →
  ∀ R : Finset (Pl E), (∀ w ∈ R, w ∈ Sec) → ∀ μ : ∀ w : Pl E, (w.adicCompletion E)ˣ →* ℂˣ,
  (∀ w, IsOpen ((μ w).ker : Set (w.adicCompletion E)ˣ)) → ∀ L : ∀ (a : ℕ) (w : Pl E), Subgroup (GLw a w × GLw (n - a) w),
  (∀ a ≤ n, ∀ w ∈ R, IsPairLevel (L a w)) →
    ∃ K : ∀ w : Pl E, Subgroup (GLw n w), F5.IsLevel K ∧ (∀ w, IsCompact (K w : Set (GLw n w))) ∧
      (∀ w : Pl E, (∀ u ∈ R, u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) → K w = KGL w (n := n)) ∧
      (∀ a (ha : a ≤ n), ∀ w ∈ R, ∀ m X, blk (Nat.add_sub_of_le ha) w m X ∈ K w →
        m ∈ L a w ∧ μ w (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1) ∧
      ∀ a (ha : a ≤ n), ∀ w ∈ R, IsSplitAt w → ∀ u, ConjPl w u → ∀ m X, blk (Nat.add_sub_of_le ha) u m X ∈ K u →
        μ u (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1 ∧
          ∃ m' ∈ L a w, embW a u m.1 = embT a w m'.1 ∧ embW (n - a) u m.2 = embT (n - a) w m'.2

end PositivityTheory.Rg.BcB.F.Ex0

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchB
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.MB

open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcN.F2 (mconv)
open PositivityTheory.Rg.BcB.F.MT (MatchLin)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def congK (m : ℕ) (w : Pl E) (k : ℕ) : Set (GLw m w) :=
  {g | g ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤
    WithZero.exp (-(k : ℤ))}

def pairIndicatorMatch (_n a b : ℕ) (w : Pl E) (k : ℕ) (y : GLw a w × GLw b w) : ℂ :=
  ((-((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (k * a * b))⁻¹ *
    (if y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y.1 ∈ congK a w k ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y.2 ∈ congK b w k then 1
      else 0)

def LponeIdem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (UL n w)),
    IsLevel (MonoidHom.id _) (KL n w) K' → ∀ m : ℕ, lpow K' (lone K') m = lone K'

def FixIdem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (L : Subgroup (GLw a w × GLw b w)),
    IsOpen (L : Set (GLw a w × GLw b w)) → L ≤ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) →
    ∀ φ : GLw a w × GLw b w → ℂ, IsHecke L φ → mconv φ (idem L) = φ ∧ mconv (idem L) φ = φ

def MatchBadS : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a : ℕ) (ha : a ≤ n) (w : Pl E), IsSplitAt w →
    ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ) (K' : Subgroup (UL n w)), IsLevel (MonoidHom.id _) (KL n w) K' → ∀ m : ℕ,
      Match n a (n - a) w μ (lpow K' (lone K') m) (ctMu (Nat.add_sub_cancel' ha) w μ (lone K'))

def MatchBadI : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w → ∀ (n a b k : ℕ), a + b = n →
    1 ≤ k → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → (∀ γ : UL n w, γ ∈ K' ↔ γ.1 ∈ congK n w k) →
      ∀ m : ℕ, Match n a b w 1 (lpow K' (lone K') m) (fun y => ((K'.relIndex (KL n w) : ℕ) : ℂ) * pairIndicatorMatch n a b w k y)

def MatchUnitI : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w → ∀ n a : ℕ, a ≤ n →
    Match n a (n - a) w 1 ((KL n w : Set (UL n w)).indicator 1) (idem (K2 a (n - a) w))

def MatchBadSOf : Prop := M3 → LponeIdem → MatchBadS
def MatchUnitIOf : Prop := M1 → MatchUnitI

end PositivityTheory.Rg.BcB.F.MB

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SeenTr
section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

def LocData.IsLetter {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (d : LocData E n) (a : ℕ) (ha : a ≤ n)
    (L : LM d.kap a (n - a)) : Prop :=
  d.IsGen a ha L ∨ (∃ L', d.IsGen a ha L' ∧ L = L'.adj) ∨ L = d.betaL a ha ∨ L = d.fixL a

def SeenTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → ∀ a (ha : a ≤ n)
  (ls : List (LM d.kap a (n - a))) (N : ∀ w, d.kap w → d.kap w → ℂ), (∀ L ∈ ls, d.IsLetter a ha L) → ∀ w ∈ d.B,
    (ls.foldr LM.mul (d.eL a)).t w = idem (d.lev₂ a w) ∧
    ((w ∈ d.T → ¬ GlobalTheory.UnitaryBC.IsSplitAt w) →
      seen ((ls.foldr LM.mul (d.eL a)).tr d.P N) (ls.foldr LM.mul (d.eL a)).t w = (ls.foldr LM.mul (d.eL a)).tr d.P N w)

end PositivityTheory.Rg.BcB.F

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SplitPlacePowersOfLocalOps
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.MS

section SlopeTestRemainingChoices

variable {H : Type} [Group H]

theorem ms_mem_rStab {u : H → ℂ} {r : H} : r ∈ rStab u ↔ ∀ x, u (x * r) = u x := Iff.rfl

theorem ms_rStab_left (u : H → ℂ) (k : H) : rStab (fun z => u (k * z)) = rStab u := by
  ext r
  rw [ms_mem_rStab, ms_mem_rStab]
  constructor
  · intro h x
    simpa [mul_assoc] using h (k⁻¹ * x)
  · intro h x
    simpa [mul_assoc] using h (k * x)

theorem ms_hint_left (K : Subgroup H) (u : H → ℂ) (k : H) :
    hint K (fun z => u (k * z)) = hint K u := by
  unfold hint
  rw [ms_rStab_left]
  congr 1
  refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm k : H ⧸ (rStab u ⊓ K) ≃ H ⧸ (rStab u ⊓ K)))
  refine finsum_congr fun q => ?_
  have hq : (MulAction.toPerm k : H ⧸ (rStab u ⊓ K) ≃ H ⧸ (rStab u ⊓ K)) q =
      ((k * q.out : H) : H ⧸ (rStab u ⊓ K)) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [hq]
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (rStab u ⊓ K) (k * q.out)
  rw [hh]
  exact (h.2.1 _).symm

theorem ms_exists_of_hint_ne_zero (K : Subgroup H) (u : H → ℂ) (h : hint K u ≠ 0) : ∃ z, u z ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  unfold hint
  simp [hc]

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem isHk_gconv {w : Pl E} (K' : Subgroup (GLw n w)) (f₁ f₂ : GLw n w → ℂ)
    (h₁ : IsHk K' f₁) (h₂ : IsHk K' f₂) : IsHk K' (gconv f₁ f₂) := by
  refine ⟨h₁.1, h₁.2.1, ?_, ?_⟩
  · refine HasCompactSupport.intro (h₁.2.2.1.isCompact.mul h₂.2.2.1.isCompact) fun y hy => ?_
    by_contra hne
    unfold gconv at hne
    obtain ⟨z, hz⟩ := ms_exists_of_hint_ne_zero _ _ hne
    apply hy
    have hz1 : f₁ z ≠ 0 := left_ne_zero_of_mul hz
    have hz2 : f₂ (z⁻¹ * y) ≠ 0 := right_ne_zero_of_mul hz
    have hm := Set.mul_mem_mul (subset_tsupport _ hz1) (subset_tsupport _ hz2)
    simpa using hm
  · intro k₁ hk₁ k₂ hk₂ g
    unfold gconv
    set u : GLw n w → ℂ := fun z => f₁ z * f₂ (z⁻¹ * g) with hu
    have e1 : (fun z => f₁ z * f₂ (z⁻¹ * (k₁ * g * k₂))) = fun z => u (k₁⁻¹ * z) := by
      funext z
      have a1 : f₂ (z⁻¹ * (k₁ * g * k₂)) = f₂ (z⁻¹ * k₁ * g) := by
        rw [show z⁻¹ * (k₁ * g * k₂) = 1 * (z⁻¹ * k₁ * g) * k₂ by group]
        exact h₂.2.2.2 1 (one_mem _) k₂ hk₂ _
      have a2 : f₁ (k₁⁻¹ * z) = f₁ z := by
        have := h₁.2.2.2 k₁⁻¹ (inv_mem hk₁) 1 (one_mem _) z
        rwa [mul_one] at this
      show _ = f₁ (k₁⁻¹ * z) * f₂ ((k₁⁻¹ * z)⁻¹ * g)
      rw [a1, a2, show (k₁⁻¹ * z)⁻¹ * g = z⁻¹ * k₁ * g by group]
    rw [e1]
    exact ms_hint_left _ u k₁⁻¹

theorem isHk_gpow {w : Pl E} (K' : Subgroup (GLw n w)) (f : GLw n w → ℂ) (hf : IsHk K' f) :
    ∀ N, IsHk K' (gpow f N)
  | 0 => hf
  | N + 1 => isHk_gconv K' f (gpow f N) hf (isHk_gpow K' f hf N)

end SlopeTestRemainingChoices

theorem split_place_powers_of_local_ops (hL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], LocOpUniformizer E) : SplitPlaceConstantTermPowers := by
  intro E _ _ _ n a b h w K' hKo hKK hnorm X hX hXu f hf N m
  obtain ⟨-, hct, hprod, -⟩ := hL E n a b h w K' hKo hKK hnorm X hX hXu
  have hpow := isHk_gpow K' f hf
  have key : ∀ N, ∀ x ∈ X, ∀ z ∈ X, phi3 h w (gpow f N) x z = mpow X (phi3 h w f) N x z := by
    intro N
    induction N with
    | zero => intro x _ z _; rfl
    | succ N ih =>
      intro x hx z hz
      funext m
      rw [show gpow f (N + 1) = gconv f (gpow f N) from rfl, hprod f (gpow f N) hf (hpow N) x hx z hz m]
      show _ = ((X.card : ℂ))⁻¹ * ∑ y ∈ X, mconv (phi3 h w f x y) (mpow X (phi3 h w f) N y z) m
      congr 1
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [ih y hy z hz]
  rw [hct _ (hpow N) m]
  congr 1
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [key N x hx x hx]

theorem match_split_place_of_powers (h3 : PositivityTheory.Rg.Bc.ArchbcB.B.M3) (hP : SplitPlaceConstantTermPowers) : MatchSplitPlace := by
  intro E _ _ _ _ n a w hw hUL μ K' hKo hKK hnorm hlev X hX hXu f hf ha N
  have hpow := isHk_gpow K' f hf N
  have hULt : UL n w = ⊤ := eq_top_iff.2 fun g _ => hUL g
  have hcl : IsClosed (UL n w : Set (GLw n w)) := by
    rw [hULt]
    exact isClosed_univ
  have hH : IsHecke (K'.subgroupOf (UL n w)) (fun u : UL n w => gpow f N (u : GLw n w)) := by
    refine ⟨hpow.2.2.1.comp_isClosedEmbedding hcl.isClosedEmbedding_subtypeVal, fun k hk x => ⟨?_, ?_⟩⟩
    · have := hpow.2.2.2 (k : GLw n w) (Subgroup.mem_subgroupOf.1 hk) 1 (one_mem _) (x : GLw n w)
      simpa using this
    · have := hpow.2.2.2 1 (one_mem _) (k : GLw n w) (Subgroup.mem_subgroupOf.1 hk) (x : GLw n w)
      simpa using this
  have hM := h3 E n a ha w hw μ (K'.subgroupOf (UL n w)) hlev _ hH
  have hφ : ctMu (Nat.add_sub_cancel' ha) w μ (fun u : UL n w => gpow f N (u : GLw n w)) =
      splitPlaceMackeyTraceTwist (Nat.add_sub_cancel' ha) w μ X f N := by
    funext m
    unfold ctMu splitPlaceMackeyTraceTwist
    rw [← hP E n a (n - a) (Nat.add_sub_cancel' ha) w K' hKo hKK hnorm X hX hXu f hf N m]
    simp [toSub, hUL]
  rw [← hφ]
  exact hM

end PositivityTheory.Rg.BcB.F.MS

end
end

