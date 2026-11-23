module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsIdealDenominator
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002
public import Formalism.ResultantValuation.ResultantAdjugateProofs.Window
public import Formalism.ResultantValuation.ResultantAdjugateProofs.Laplace
public import Formalism.CyclotomicNorms.Bundle0001
public import Formalism.CyclotomicNorms.IrreducibilityOfGoodTuple
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ClassMapInjectiveBijectiveNorms
section
noncomputable section

namespace Formalism.MainNotions.LocalSituation

open Formalism.BasicNotions Formalism.BasicNotions.Loc

def ClassMapInjectiveBijectiveNorms (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    HerrAat (sit D.loc HW l (D.locA l) K s LL h) ∧ HerrAsat (sit D.loc HW l (D.locA l) K s LL h) ∧
      ((HW l).W K s LL h).ClNat

end Formalism.MainNotions.LocalSituation
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.GaloisEquivariantKeyFunction
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace Formalism.MainNotions.ExistsIdealDenominator

open Formalism.IrreducibleCountingLemmas.TW

section Dense

variable (l : ℕ) [Fact l.Prime]

theorem norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  rw [Padic.norm_p, map_natCast, PadicComplex.coe_natCast] at h
  exact h

theorem exists_norm_btwn (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) : ∃ a : ℂ_[l], x < ‖a‖ ∧ ‖a‖ < y := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := lt_trans one_pos hl1
  have hy : 0 < y := lt_of_le_of_lt hx hxy
  set x' := max x (y / 2) with hx'
  have hx'0 : 0 < x' := lt_of_lt_of_le (half_pos hy) (le_max_right _ _)
  have hx'y : x' < y := max_lt hxy (half_lt_self hy)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ((Real.logb_lt_logb_iff hl1 hx'0 hy).2 hx'y)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (l : ℂ_[l]) q.den_pos
  have hcn : ‖c‖ ^ q.den = (l : ℝ)⁻¹ := by rw [← norm_pow, hc, norm_l]
  have hc' : ‖c‖ = ((l : ℝ)⁻¹) ^ ((q.den : ℝ)⁻¹) := by
    rw [← hcn, Real.pow_rpow_inv_natCast (norm_nonneg _) q.den_ne_zero]
  have hval : ‖c ^ (-q.num)‖ = (l : ℝ) ^ (q : ℝ) := by
    rw [norm_zpow, ← Real.rpow_intCast, hc', ← Real.rpow_mul (inv_nonneg.2 hl0.le),
      Real.inv_rpow hl0.le, ← Real.rpow_neg hl0.le]
    congr 1
    have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den q).symm
    rw [hq]
    push_cast
    field_simp
  refine ⟨c ^ (-q.num), ?_, ?_⟩
  · rw [hval]
    refine lt_of_le_of_lt (le_max_left x (y / 2)) ?_
    rw [← hx']
    calc x' = (l : ℝ) ^ Real.logb l x' := (Real.rpow_logb hl0 hl1.ne' hx'0).symm
      _ < (l : ℝ) ^ (q : ℝ) := (Real.rpow_lt_rpow_left_iff hl1).2 hq1
  · rw [hval]
    calc (l : ℝ) ^ (q : ℝ) < (l : ℝ) ^ Real.logb l y := (Real.rpow_lt_rpow_left_iff hl1).2 hq2
      _ = y := Real.rpow_logb hl0 hl1.ne' hy

@[reducible] def denseC : DenselyNormedField ℂ_[l] where
  __ := (inferInstance : NormedField ℂ_[l])
  lt_norm_lt := exists_norm_btwn l

attribute [local instance] denseC

variable {l}

end Dense

namespace PtGeo

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [AddCommGroup Λ] {σ : Type} (X : PtGeo l Λ σ)

variable {X} {k : ℕ} {ρ : ℝ}

end PtGeo

variable {D : Formalism.BasicNotions.D7}

section Places

section

variable {E L V : Type} [Field E] [NumberField E] [AddCommGroup L] [Module (𝓞 E) L]

end

end Places

section Gal

variable (X : Geo D)

end Gal

section U4

theorem norm_unif {K O : Type} [NormedField K] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra O K] [IsFractionRing O K]
    (hball : ∀ x : K, ‖x‖ ≤ 1 ↔ x ∈ (algebraMap O K).range) {ϖ : O} (hϖ : Irreducible ϖ) :
    0 < ‖algebraMap O K ϖ‖ ∧ ‖algebraMap O K ϖ‖ < 1 := by
  have h0 : algebraMap O K ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]; exact hϖ.ne_zero
  refine ⟨norm_pos_iff.2 h0, lt_of_le_of_ne ((hball _).2 ⟨ϖ, rfl⟩) ?_⟩
  intro h1
  have h2 : ‖(algebraMap O K ϖ)⁻¹‖ ≤ 1 := by rw [norm_inv, h1, inv_one]
  obtain ⟨a, ha⟩ := (hball _).1 h2
  apply hϖ.not_isUnit
  refine IsUnit.of_mul_eq_one a ?_
  apply IsFractionRing.injective O K
  rw [map_mul, ha, map_one, mul_inv_cancel₀ h0]

theorem complete_of_adic {K O : Type} [NormedField K] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra O K] [IsFractionRing O K]
    (hball : ∀ x : K, ‖x‖ ≤ 1 ↔ x ∈ (algebraMap O K).range)
    (hc : IsAdicComplete (IsLocalRing.maximalIdeal O) O) : CompleteSpace K := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hr0, hr1⟩ := norm_unif hball hϖ
  set r := ‖algebraMap O K ϖ‖ with hr
  have hπ0 : algebraMap O K ϖ ≠ 0 := norm_pos_iff.1 hr0
  have hmem : ∀ (a : O) (n : ℕ), ‖algebraMap O K a‖ ≤ r ^ n → a ∈ IsLocalRing.maximalIdeal O ^ n := by
    intro a n h
    have h1 : ‖algebraMap O K a / (algebraMap O K ϖ) ^ n‖ ≤ 1 := by
      rw [norm_div, norm_pow, div_le_one (pow_pos hr0 n)]; exact h
    obtain ⟨c, hc'⟩ := (hball _).1 h1
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨c, ?_⟩
    apply IsFractionRing.injective O K
    rw [map_mul, map_pow, hc', mul_div_cancel₀ _ (pow_ne_zero n hπ0)]
  have hnorm : ∀ (a : O) (n : ℕ), a ∈ IsLocalRing.maximalIdeal O ^ n → ‖algebraMap O K a‖ ≤ r ^ n := by
    intro a n h
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    obtain ⟨c, rfl⟩ := h
    rw [map_mul, map_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg hr0.le n) ((hball _).2 ⟨c, rfl⟩)
  refine Metric.complete_of_convergent_controlled_sequences (fun n => r ^ n) (fun n => pow_pos hr0 n) ?_
  intro u hu
  have h1 : ∀ n, ∃ a : O, algebraMap O K a = u n - u 0 := by
    intro n
    have := hu 0 n 0 (Nat.zero_le _) le_rfl
    rw [pow_zero, dist_eq_norm] at this
    exact (hball _).1 this.le
  choose a ha using h1
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec (f := a) (by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    apply hmem
    rw [map_sub, ha, ha, sub_sub_sub_cancel_right, ← dist_eq_norm]
    exact (hu m m n le_rfl hmn).le)
  refine ⟨u 0 + algebraMap O K L, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1)
  have h2 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h2
  have h3 := hnorm _ n h2
  rw [map_sub, ha] at h3
  rwa [← sub_sub]

end U4

section U4rec

variable {D : Formalism.BasicNotions.D7}

end U4rec

section ConjPlaces

end ConjPlaces

namespace SplitL

variable {R : Ranks} (H : Host R)

end SplitL

section PartC

variable {i : D.ntw.Tw} {j : ℕ} {M : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))}

variable {δ : G D.host.E D.nd.Om →* Multiplicative (DelQM D.host (D.ntw.l i) Q M)}
  {Φ : ↥Q → ZMod (D.ntw.l i ^ M) → D.nth.Lt i j → KK i} {φ : D.nth.Lt i j → KK i}

variable (X : Geo D)

end PartC

section U5

end U5

end Formalism.MainNotions.ExistsIdealDenominator

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.GammaSemisimpleLocalOfConsequences
section
noncomputable section

namespace Formalism.MainNotions.DeltaInvariantLattices

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (W : LocWach PD LL O v n)

def WachLatticeFree : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → wachFree W T

def WachCharacterisationLattice : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → p10 W T

def GammaSemisimpleQuotient : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
    ∀ y : ℕ, 1 ≤ y → SSEig W T (invN W T (W.Q ^ y)) (W.N T)
      {c | ∃ a ∈ Jumps (PD := PD) T, ∃ j : ℕ, 1 ≤ j ∧ j ≤ y ∧ c = (uU W) ^ (-(a + j))}

end Local

section Theory

def wachLatticeFreeLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachLatticeFree ((HW l).W K s LL h)

def wachCharacterisationLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachCharacterisationLattice ((HW l).W K s LL h)

def gammaSemisimpleLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    GammaSemisimpleQuotient ((HW l).W K s LL h)

end Theory

section Design

def WachLatticeFreeGlobal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  wachLatticeFreeLocal D.loc HW D.locA F

def WachCharacterisation (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  wachCharacterisationLocal D.loc HW D.locA F

def gammaSemisimpleQuotientGlobal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  gammaSemisimpleLocal D.loc HW D.locA F

end Design

end Formalism.MainNotions.DeltaInvariantLattices
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.WeaklyAdmissibleFiltrations Module Formalism.MainNotions.N

namespace Formalism.MainNotions.LargeLevelLemmas

open Formalism.BasicNotions Formalism.BasicNotions.Loc

section Lit

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    (LL O : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    [CommRing O] [Algebra O LL]

def bkAAt : Prop :=
  ∀ (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR PD A.ρ → IsDual1 PD A.ρ A'.ρ P →
    (∀ a ∈ continuousCocycles A.ρ, (a ∈ finiteCocycles PD A.ρ ↔ ∀ b ∈ finiteCocycles PD A'.ρ, CobL PD (cupL A'.ρ P a b))) ∧
    (∀ b ∈ continuousCocycles A'.ρ, (b ∈ finiteCocycles PD A'.ρ ↔ ∀ a ∈ finiteCocycles PD A.ρ, CobL PD (cupL A'.ρ P a b)))

def TateH1FinitenessAt (_PD : PeriodData G Qp K₀ K B BdR) : Prop :=
  ∀ (A : GRep G Qp LL O) (LA : Lattice (O := O) A.ρ), Module.Finite O (LatticeCohomology LA)

theorem bkAAt_of_core [TopologicalSpace Qp] (h : bkACore PD) (hO : GoodO (Qp := Qp) LL O) :
    bkAAt PD LL O :=
  h LL O hO

theorem tate_h1_finite_of_all_coefficients [TopologicalSpace Qp] (h : TateFiniteness PD) (hO : GoodO (Qp := Qp) LL O) :
    TateH1FinitenessAt LL O PD :=
  h LL O hO

end Lit

variable {D : D7}

theorem splits_coef {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    Splits (Qp := ℚ_[D.nd.l i]) (K := Br.Kw D.nbr i w hw) ↥C.LL.1 := by
  refine ⟨C.LL.2, ?_⟩
  have hmem : ∀ (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Om (D.nd.l i)) (x : Br.Kw D.nbr i w hw),
      τ x ∈ C.LL.1 := fun τ x => C.le ((D.nbr i w hw).LL_split τ x)
  let e : (Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) ≃
      (Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Om (D.nd.l i)) :=
    { toFun := fun f => C.LL.1.val.comp f
      invFun := fun τ => τ.codRestrict C.LL.1.toSubalgebra (hmem τ)
      left_inv := fun f => by ext x; rfl
      right_inv := fun τ => by ext x; rfl }
  rw [Fintype.card_congr e]
  exact AlgHom.card _ _ _

section Pt

variable (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i)

def adm51 : Prop := π ∈ D.nd.Z i → ∃ S : IdempotentChoiceData D.nd i, GoodCongruenceObjects D.nd r ρ π S

def CharpolyCoeffsLemmaFamily : Prop := CharpolyCoeffsInSubalgebra D.nd i (D.nd.T i) (rO D.nd i r)

def SpanQuotientLemma : Prop := π ∈ D.nd.Z i → ∀ S : IdempotentChoiceData D.nd i, GoodCongruenceObjects D.nd r ρ π S → VanishingLemma D.nd π S

def HomRelationsLemmaAllChoices : Prop := π ∈ D.nd.Z i → ∀ S : IdempotentChoiceData D.nd i, GoodCongruenceObjects D.nd r ρ π S → QuotientHomNonvanishingBound D.nd r π S

def BlochKatoAnnihilators : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw), C.IsGood →
    bkAAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL)

def tateH1FinitenessAtPlacesOver : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw),
    TateH1FinitenessAt ↥C.LL.1 ↥(OL C.LL) (Br.PD D.loc D.nbr i w hw)

end Pt

theorem sum_padicValNat_range (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), padicValNat p k = padicValNat p n.factorial := by
  induction n with
  | zero => simp [Nat.padicValNat_def]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.succ_ne_zero m) (Nat.factorial_ne_zero m), add_comm]

theorem vdel_le (i : D.nd.Loc) :
    D.nd.vdel i ≤ (D.R.t : ℚ) * (D.nd.s0 i : ℚ) + (padicValNat (D.nd.l i) D.R.t.factorial : ℚ) := by
  have h1 : D.nd.vdel i ≤
      ∑ k ∈ Finset.range D.R.t, ((D.nd.s0 i : ℚ) + (padicValNat (D.nd.l i) k : ℚ)) := by
    unfold NData.vdel
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact Finset.mem_range.2 (Finset.mem_Ioo.1 hk).2
    · intro k _ _
      positivity
  have h2 : (∑ k ∈ Finset.range D.R.t, padicValNat (D.nd.l i) k) ≤
      padicValNat (D.nd.l i) D.R.t.factorial := by
    rcases Nat.eq_zero_or_pos D.R.t with h0 | hpos
    · simp [h0]
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      rw [hm, Nat.succ_eq_add_one, sum_padicValNat_range, Nat.factorial_succ,
        (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.succ_ne_zero m) (Nat.factorial_ne_zero m)]
      exact Nat.le_add_left _ _
  have h3 : (∑ k ∈ Finset.range D.R.t, ((D.nd.s0 i : ℚ) + (padicValNat (D.nd.l i) k : ℚ))) =
      (D.R.t : ℚ) * (D.nd.s0 i : ℚ) + ((∑ k ∈ Finset.range D.R.t, padicValNat (D.nd.l i) k : ℕ) : ℚ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sum]
  have h4 : ((∑ k ∈ Finset.range D.R.t, padicValNat (D.nd.l i) k : ℕ) : ℚ) ≤
      (padicValNat (D.nd.l i) D.R.t.factorial : ℚ) := by exact_mod_cast h2
  linarith

theorem zgoodSubsetZ (i : D.nd.Loc) : D.nd.Zgood i ⊆ D.nd.Z i := by
  intro x hx
  rw [D.Z_tie]
  rw [D.Zgood_tie] at hx
  exact hx.1

end Formalism.MainNotions.LargeLevelLemmas
end
end

