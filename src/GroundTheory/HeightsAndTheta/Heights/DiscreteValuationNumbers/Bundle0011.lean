module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutPieces
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem MixedDiffLinear.full : MixedDiffLinear.Statement := MixedDiffLinear.proof

theorem DegLTClosure.full : DegLTClosure.Statement := DegLTClosure.proof MixedDiffLinear.full

theorem DiffStepExpansion.full : DiffStepExpansion.Statement := DiffStepExpansion.proof

theorem DegLTOfUnitSteps.full : DegLTOfUnitSteps.Statement :=
  DegLTOfUnitSteps.proof DiffStepExpansion.full MixedDiffLinear.full DegLTClosure.full

theorem DegLTEventuallyConst.full : DegLTEventuallyConst.Statement :=
  DegLTEventuallyConst.proof MixedDiffLinear.full

theorem EventualValueFacts.full : EventualValueFacts.Statement := EventualValueFacts.proof

theorem HilbFnVanishBlock.full : HilbFnVanishBlock.Statement.{u} := HilbFnVanishBlock.proof

theorem GradedPieceQuot.full : GradedPieceQuot.Statement.{u} := GradedPieceQuot.proof

theorem CutPieces.full : CutPieces.Statement.{u} := CutPieces.proof

theorem HilbFnCut.full : HilbFnCut.Statement.{u} := HilbFnCut.proof GradedPieceQuot.full CutPieces.full

theorem MultiHomogPrimeCriterion.full : MultiHomogPrimeCriterion.Statement.{u} :=
  MultiHomogPrimeCriterion.proof

theorem ColonMultiHomog.full : ColonMultiHomog.Statement.{u} := ColonMultiHomog.proof

theorem AssociatedMultiHomogPrime.full : AssociatedMultiHomogPrime.Statement.{u} :=
  AssociatedMultiHomogPrime.proof MultiHomogPrimeCriterion.full ColonMultiHomog.full

theorem FiltrationStepHilb.full : FiltrationStepHilb.Statement.{u} := FiltrationStepHilb.proof

theorem FiltrationStepLength.full : FiltrationStepLength.Statement.{u} := FiltrationStepLength.proof

theorem PrimeFiltration.full : PrimeFiltration.Statement.{u} :=
  PrimeFiltration.proof AssociatedMultiHomogPrime.full FiltrationStepHilb.full
    FiltrationStepLength.full ColonMultiHomog.full

theorem MultAtPrimeAtMinimal.full : MultAtPrimeAtMinimal.Statement.{u} := MultAtPrimeAtMinimal.proof

theorem DimStrictDrop.full : DimStrictDrop.Statement.{u} := DimStrictDrop.proof

theorem BlockAdjoinPrime.full : BlockAdjoinPrime.Statement.{u} := BlockAdjoinPrime.proof

theorem RelevantDimGe.full : RelevantDimGe.Statement.{u} := RelevantDimGe.proof BlockAdjoinPrime.full

theorem HilbDegBound.full : HilbDegBound.Statement.{u} :=
  HilbDegBound.proof HilbFnVanishBlock.full HilbFnCut.full PrimeFiltration.full DimStrictDrop.full
    RelevantDimGe.full DegLTClosure.full DegLTOfUnitSteps.full

theorem TopDimMinimal.full : TopDimMinimal.Statement.{u} := TopDimMinimal.proof DimStrictDrop.full

theorem IntNumOfFiltration.full : IntNumOfFiltration.Statement.{u} :=
  IntNumOfFiltration.proof MixedDiffLinear.full DegLTEventuallyConst.full EventualValueFacts.full

theorem GradedPieceFree.full : GradedPieceFree.Statement.{u} := GradedPieceFree.proof

theorem SpecialPieceRank.full : SpecialPieceRank.Statement.{u} :=
  SpecialPieceRank.proof GradedPieceFree.full

theorem GenericPieceRank.full : GenericPieceRank.Statement.{u} := GenericPieceRank.proof

theorem SpecialIdealMultiHomog.full : SpecialIdealMultiHomog.Statement.{u} :=
  SpecialIdealMultiHomog.proof

theorem SpecialIdealCorresp.full : SpecialIdealCorresp.Statement.{u} := SpecialIdealCorresp.proof

theorem SpecialIdealSurj.full : SpecialIdealSurj.Statement.{u} := SpecialIdealSurj.proof

theorem SpecialMultAt.full : SpecialMultAt.Statement.{u} := SpecialMultAt.proof

theorem SpecialCycleEval.full : SpecialCycleEval.Statement.{u} :=
  SpecialCycleEval.proof SpecialIdealCorresp.full SpecialIdealSurj.full SpecialMultAt.full

theorem SpecialDimBound.full : SpecialDimBound.Statement.{u} := SpecialDimBound.proof

theorem IntNumVanish.full : IntNumVanish.Statement.{u} :=
  IntNumVanish.proof HilbDegBound.full HilbFnVanishBlock.full DegLTClosure.full EventualValueFacts.full

theorem IntNumAssoc.full : IntNumAssoc.Statement.{u} :=
  IntNumAssoc.proof PrimeFiltration.full IntNumOfFiltration.full MultAtPrimeAtMinimal.full
    IntNumVanish.full TopDimMinimal.full HilbDegBound.full

theorem CutByForm.full : CutByForm.Statement.{u} :=
  CutByForm.proof IntNumAssoc.full HilbFnCut.full MixedDiffLinear.full

theorem ConservationOfNumber.full : ConservationOfNumber.Statement.{u} :=
  ConservationOfNumber.proof IntNumAssoc.full SpecialCycleEval.full SpecialPieceRank.full
    GenericPieceRank.full SpecialIdealMultiHomog.full SpecialDimBound.full

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CycEvalEqAddMulOfCycle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section SlopeTestRemainingChoices

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem cycEval_eq_add_mul_of_cycle (φ : Ideal (MRing ι R) → ℤ) {Z₀ Z₁ Z₂ : Ideal (MRing ι R) → ℤ}
    (k : ℤ) (h₀ : (Function.support Z₀).Finite) (h₂ : (Function.support Z₂).Finite)
    (h : ∀ W, Z₁ W = Z₀ W + k * Z₂ W) :
    cycEval φ Z₁ = cycEval φ Z₀ + k * cycEval φ Z₂ := by
  unfold cycEval
  have f₀ : (Function.support fun W => Z₀ W * φ W).Finite :=
    h₀.subset fun W hW h0 => hW (by simp [h0])
  have f₂ : (Function.support fun W => k * (Z₂ W * φ W)).Finite :=
    h₂.subset fun W hW h0 => hW (by simp [h0])
  rw [mul_finsum, ← finsum_add_distrib f₀ f₂]
  refine finsum_congr fun W => ?_
  rw [h W]
  ring

theorem cycEval_eq_add_mul_of_fun {φ₀ φ₁ φ₂ : Ideal (MRing ι R) → ℤ} {Z : Ideal (MRing ι R) → ℤ}
    (k : ℤ) (hZ : (Function.support Z).Finite) (h : ∀ W, Z W ≠ 0 → φ₁ W = φ₀ W + k * φ₂ W) :
    cycEval φ₁ Z = cycEval φ₀ Z + k * cycEval φ₂ Z := by
  unfold cycEval
  have f₀ : (Function.support fun W => Z W * φ₀ W).Finite :=
    hZ.subset fun W hW h0 => hW (by simp [h0])
  have f₂ : (Function.support fun W => k * (Z W * φ₂ W)).Finite :=
    hZ.subset fun W hW h0 => hW (by simp [h0])
  rw [mul_finsum, ← finsum_add_distrib f₀ f₂]
  refine finsum_congr fun W => ?_
  by_cases hW : Z W = 0
  · simp [hW]
  · rw [h W hW]
    ring

end SlopeTestRemainingChoices

section VNum

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem vNum_vecCons_zero (W : Ideal (MRing ι O)) {d : ℕ} (L : Fin d → K → ℤ) :
    vNum W (Matrix.vecCons (0 : K → ℤ) L) = 0 := by
  unfold vNum intNum
  have hm : mixedDiff (Matrix.vecCons (0 : K → ℤ) L) (hilbFn (specialIdeal W)) = fun _ => 0 := by
    funext m
    simp [mixedDiff, List.ofFn_succ, diffStep]
  rw [hm]
  unfold eventualValue
  have hex : ∃ c, ∀ᶠ m in Filter.atTop, (fun _ : K → ℤ => (0 : ℤ)) m = c :=
    ⟨0, Filter.Eventually.of_forall fun _ => rfl⟩
  rw [dite_eq_left hex]
  obtain ⟨m, hm'⟩ := hex.choose_spec.exists
  exact hm'.symm

end VNum

theorem ShiftByUniformiser.proof (h₁ : DivCycleMul.Statement.{u})
    (h₂ : DivCycleFiniteSupport.Statement.{u}) : ShiftByUniformiser.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s _ hsP hH L n hI₁ hI₂
  have hfin : ∀ (Q : Ideal (MRing ι O)) (x : MRing ι O), (Function.support (divCycle Q x)).Finite :=
    fun Q x => h₂ O K ι Q x
  have hrat : ∀ (Q : Ideal (MRing ι O)) (x y : MRing ι O), (Function.support (ratDiv Q x y)).Finite :=
    fun Q x y => ((hfin Q x).union (hfin Q y)).subset fun W hW => by
      by_contra hc
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
      exact hW (by simp [ratDiv, hc.1, hc.2])

  have hpow : ∀ (Q : Ideal (MRing ι O)), Q.IsPrime → (C ϖ : MRing ι O) ∉ Q → f ∉ Q → ∀ m : ℕ,
      ∀ W, divCycle Q (C ϖ ^ m * f) W = divCycle Q f W + m * divCycle Q (C ϖ) W := by
    intro Q hQ hϖQ hfQ m
    induction m with
    | zero => intro W; simp
    | succ m ih =>
      intro W
      have hm : C ϖ ^ m * f ∉ Q := fun h =>
        (hQ.mem_or_mem h).elim (fun h' => hϖQ (hQ.mem_of_pow_mem _ h')) hfQ
      have e : (C ϖ : MRing ι O) ^ (m + 1) * f = C ϖ * (C ϖ ^ m * f) := by ring
      rw [e, congrFun (h₁ O K ι Q (C ϖ) (C ϖ ^ m * f) hQ hϖQ hm) W, Pi.add_apply, ih W]
      push_cast
      ring
  have hshift : ∀ (Q : Ideal (MRing ι O)), Q.IsPrime → (C ϖ : MRing ι O) ∉ Q → f ∉ Q → ∀ W,
      ratDiv Q (C ϖ ^ n * f) g W = ratDiv Q f g W + (n : ℤ) * ratDiv Q (C ϖ) 1 W := by
    intro Q hQ hϖQ hfQ W
    simp only [ratDiv, divCycle_one, sub_zero]
    rw [hpow Q hQ hϖQ hfQ n W]
    ring
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'
  unfold cutIdentity at hI₁ hI₂ ⊢
  rw [cycEval_eq_add_mul_of_cycle _ (n : ℤ) (hrat P f g) (hrat P (C ϖ) 1)
      (hshift P hPp hϖP hD.num_not_mem)] at hI₁
  classical
  have hR : cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
        else cycEval (fun G => vNum G L) (ratDiv W (C ϖ ^ n * f) g)) (divCycle P s) =
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
        else cycEval (fun G => vNum G L) (ratDiv W f g)) (divCycle P s) +
      (n : ℤ) * cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons (0 : K → ℤ) L)
        else cycEval (fun G => vNum G L) (ratDiv W (C ϖ) 1)) (divCycle P s) := by
    refine cycEval_eq_add_mul_of_fun (n : ℤ) (hfin P s) fun W hW => ?_
    by_cases hϖW : (C ϖ : MRing ι O) ∈ W
    · simp only [if_pos hϖW, vNum_vecCons_zero]
      ring
    · simp only [if_neg hϖW]
      have hV := hH W hW hϖW
      have hWp : W.IsPrime := by
        unfold divCycle at hW
        split_ifs at hW with hm
        · exact hm.1.1.1
        · exact absurd rfl hW
      exact cycEval_eq_add_mul_of_cycle _ (n : ℤ) (hrat W f g) (hrat W (C ϖ) 1)
        (hshift W hWp hϖW hV.num_not_mem)
  rw [hR, hI₂] at hI₁
  linarith

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.MemMinimalPrimesOfDivCycleNeZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem mem_minimalPrimes_of_divCycle_ne_zero {K : Type*} {ι : K → Type*} {R : Type*}
    [CommRing R] {P : Ideal (MRing ι R)} {f : MRing ι R} {W : Ideal (MRing ι R)}
    (h : divCycle P f W ≠ 0) : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact hW
  · exact absurd rfl h

theorem ratDiv_one {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R] (P : Ideal (MRing ι R))
    (f : MRing ι R) : ratDiv P f 1 = divCycle P f := by
  funext W
  rw [ratDiv, divCycle_one, sub_zero]

theorem mixedDiff_cons_zero {K : Type*} {n : ℕ} (L : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) :
    mixedDiff (Matrix.vecCons 0 L) h = 0 := by
  unfold mixedDiff
  rw [List.ofFn_succ, List.foldr_cons, Matrix.cons_val_zero]
  funext m
  simp [diffStep]

theorem eventualValue_zero {K : Type*} : eventualValue (0 : (K → ℤ) → ℤ) = 0 := by
  unfold eventualValue
  split_ifs with hc
  · obtain ⟨m, hm⟩ := hc.choose_spec.exists
    exact hm.symm
  · rfl

theorem vNum_cons_zero {K : Type*} [DecidableEq K] {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (W : Ideal (MRing ι O)) {n : ℕ}
    (L : Fin n → K → ℤ) : vNum W (Matrix.vecCons 0 L) = 0 := by
  rw [vNum, intNum, mixedDiff_cons_zero, eventualValue_zero]

theorem comap_C_eq_bot_of_not_mem {K : Type*} {ι : K → Type*} {O : Type*} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    (H : Ideal (MRing ι O)) [hH : H.IsPrime] (hϖH : (C ϖ : MRing ι O) ∉ H) :
    H.comap (C : O →+* MRing ι O) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun a ha => ?_
  by_contra ha0
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  rw [Ideal.mem_comap, map_mul, map_pow] at ha
  rcases hH.mem_or_mem ha with hv | hp
  · exact hH.ne_top (Ideal.eq_top_of_isUnit_mem _ hv ((Units.isUnit v).map C))
  · exact hϖH (hH.mem_of_pow_mem n hp)

theorem withBot_le_of_add_one_le (x : WithBot ℕ∞) (N : ℕ)
    (hx : x + 1 ≤ ((N + 1 : ℕ) : WithBot ℕ∞)) : x ≤ ((N : ℕ) : WithBot ℕ∞) :=
  by apply _root_.UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ <;> assumption

theorem withBot_lt_of_add_one_le (x : WithBot ℕ∞) (N : ℕ)
    (hx : x + 1 ≤ ((N + 1 : ℕ) : WithBot ℕ∞)) : x < ((N + 1 : ℕ) : WithBot ℕ∞) := by
  refine lt_of_le_of_lt (withBot_le_of_add_one_le x N hx) ?_
  exact_mod_cast Nat.lt_succ_self N

theorem UniformiserCase.proof (h1 : ConservationOfNumberLE.Statement.{u})
    (h2 : GenericDimBound.Statement.{u}) (h3 : GenericFibProps.Statement.{u})
    (h4 : GenericCycleCorresp.Statement.{u}) (h5 : MinimalPrimeMultiHomog.Statement.{u})
    (h6 : SupSpanMultiHomog.Statement.{u}) (h7 : DimStrictDrop.Statement.{u})
    (h8 : CutByForm.Statement.{u}) : UniformiserCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP c s hs hsP L
  have hdim : ringKrullDim (MRing ι O ⧸ P) = ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    hP.dim
  have := hP.multiProj.isPrime

  have hL : cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P (C ϖ) 1) =
      gNum P (Matrix.vecCons (fun k => (c k : ℤ)) L) := by
    rw [ratDiv_one]
    exact h1 O ϖ hϖ K ι P (d + 1) hP.multiProj hP.noTorsion hdim.le _

  obtain ⟨hGprime, hGhom, hGs⟩ := h3 O K ι P hP.multiProj hP.noTorsion
  obtain ⟨hsG, hsG'⟩ := hGs s c hs hsP
  have hGdim : ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) <
      ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    have e : d + 2 + Fintype.card K = (d + 1 + Fintype.card K) + 1 := by omega
    rw [e]
    refine withBot_lt_of_add_one_le _ _ ?_
    have := h2 O K ι P hP.multiProj hP.noTorsion
    rw [hdim] at this
    rwa [show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by omega] at this
  have hcut := h8 (FractionRing O) K ι d (genFib P) hGprime hGhom hGdim _ c hsG hsG' L
  have hcorr := h4 O ϖ hϖ K ι P s hP.multiProj.isPrime hP.noTorsion hsP
    (fun V => intNum (FractionRing O) V L)
  rw [cutIdentity, hL, gNum, hcut, ← hcorr]

  unfold cycEval
  refine finsum_congr fun W => ?_
  by_cases hW : divCycle P s W = 0
  · rw [hW, zero_mul, zero_mul]
  congr 1
  dsimp only
  by_cases hϖW : (C ϖ : MRing ι O) ∈ W
  · rw [if_pos hϖW, if_pos hϖW, vNum_cons_zero]
  rw [if_neg hϖW, if_neg hϖW]
  obtain ⟨hWmin, hWrel⟩ := mem_minimalPrimes_of_divCycle_ne_zero hW
  obtain ⟨hWprime, hPW, -⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  have := hWprime
  have hWhom : IsMultiHomogIdeal W :=
    h5 O K ι (P ⊔ Ideal.span {s}) W (h6 O K ι P s c hP.multiProj.multiHomog hs) hWmin
  have hlt : P < W := lt_of_le_of_ne hPW fun h => hsP (h ▸ hWmin.1.2
    (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  have hWdim : ringKrullDim (MRing ι O ⧸ W) ≤ ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    refine withBot_le_of_add_one_le _ _ ?_
    have := h7 (MRing ι O) P W hlt
    rw [hdim] at this
    rwa [show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by omega] at this
  rw [ratDiv_one]
  exact (h1 O ϖ hϖ K ι W d ⟨hWprime, hWhom, hWrel⟩ (comap_C_eq_bot_of_not_mem hϖ W hϖW) hWdim L).symm

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.MemOfMemSupportDivCycle
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

section Lengths

end Lengths

section Models

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def redMap : MRingOver O ι →+* MRingOver (IsLocalRing.ResidueField O) ι :=
  MvPolynomial.map (IsLocalRing.residue O)

def IsModelOver (P : Ideal (MRingOver O ι)) (d : ℕ) : Prop :=
  IsMultiProjPrime P ∧ P.comap (C : O →+* MRingOver O ι) = ⊥ ∧
    ringKrullDim (MRingOver O ι ⧸ P) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)

def intCyc {R : Type*} [CommRing R] (Z : Ideal (MRingOver R ι) →₀ ℕ) : Ideal (MRingOver R ι) →₀ ℤ :=
  Finsupp.mapRange (fun m : ℕ => (m : ℤ)) Nat.cast_zero Z

def specCyc (ϖ : O) (P : Ideal (MRingOver O ι)) : Ideal (MRingOver O ι) →₀ ℕ :=
  divCycle P (C ϖ)

def divO (P : Ideal (MRingOver O ι)) (f g : MRingOver O ι) : Ideal (MRingOver O ι) →₀ ℤ :=
  intCyc (divCycle P f) - intCyc (divCycle P g)

def redEval (J : Ideal (MRingOver (IsLocalRing.ResidueField O) ι) → ℤ)
    (Z : Ideal (MRingOver O ι) →₀ ℤ) : ℤ :=
  Z.sum fun W m => m * J (W.map redMap)

end Models


section Inhabitants

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]


omit [Fintype K] [IsDomain O] [IsDiscreteValuationRing O] in
theorem isMultiHomog_C (a : O) : IsMultiHomog (C a : MRingOver O ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
  split_ifs at hm with h0
  · subst h0; simp
  · exact absurd rfl hm


end Inhabitants

section LengthInhabitants

open IsLocalRing

end LengthInhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
end
end

