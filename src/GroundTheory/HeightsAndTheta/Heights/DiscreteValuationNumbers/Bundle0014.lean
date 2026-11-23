module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0010

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultAtOfSaturated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

section General

variable {A : Type*} [CommRing A]

theorem mem_minimalPrimes_of_saturated (J Q : Ideal A) [Q.IsPrime] (hJQ : J ≤ Q)
    (hsat : ∀ q ∈ Q, ∃ s ∉ Q, s * q ∈ J) : Q ∈ J.minimalPrimes := by
  refine ⟨⟨‹Q.IsPrime›, hJQ⟩, fun W hW hWQ q hq => ?_⟩
  obtain ⟨s, hs, hsq⟩ := hsat q hq
  exact (hW.1.mem_or_mem (hW.2 hsq)).resolve_left (fun h => hs (hWQ h))

theorem localizedQuot_map_bijective_of_saturated (J Q : Ideal A) [Q.IsPrime] (hJQ : J ≤ Q)
    (hsat : ∀ q ∈ Q, ∃ s ∉ Q, s * q ∈ J) :
    Function.Bijective (LocalizedModule.map Q.primeCompl
      (Submodule.mapQ J Q LinearMap.id (fun _ ha => hJQ ha) : (A ⧸ J) →ₗ[A] A ⧸ Q)) := by
  refine ⟨?_, LocalizedModule.map_surjective _ _ ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    induction x using LocalizedModule.induction_on with | h m s => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
    rw [LinearMap.mem_ker, LocalizedModule.map_mk] at hx
    have haQ : a ∈ Q := localizedQuotient_mk_eq_zero Q a s hx
    obtain ⟨t, ht, hta⟩ := hsat a haQ
    rw [Submodule.mem_bot, ← LocalizedModule.zero_mk (1 : Q.primeCompl), LocalizedModule.mk_eq]
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hta
  · intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk J a, rfl⟩

end General

universe u

theorem MultAtOfSaturated.proof : MultAtOfSaturated.Statement.{u} := by
  intro R _ K ι J Q _ hJQ hsat
  refine ⟨mem_minimalPrimes_of_saturated J Q hJQ hsat, ?_⟩
  unfold multAt
  rw [(LinearEquiv.ofBijective _ (localizedQuot_map_bijective_of_saturated J Q hJQ hsat)).length_eq,
    Module.length_eq_one_iff]
  exact localizedQuotient_isSimpleModule Q

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialQuotDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem SpecialQuotDim.proof : SpecialQuotDim.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ W hW
  let π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O)
  have hsurj : Function.Surjective π :=
    MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π ≤ W := by
    change RingHom.ker (MvPolynomial.map (IsLocalRing.residue O)) ≤ W
    rw [MvPolynomial.ker_map, IsLocalRing.ker_residue,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact hW
  have hcomap : (specialIdeal W).comap π = W := by
    change (W.map π).comap π = W
    rw [Ideal.comap_map_of_surjective' _ hsurj, sup_eq_left.2 hker]
  let f := (Ideal.Quotient.mk (specialIdeal W)).comp π
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hsurj
  have hkf : RingHom.ker f = W := by
    ext x
    change Ideal.Quotient.mk _ (π x) = 0 ↔ x ∈ W
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hcomap]
  exact (ringKrullDim_eq_of_ringEquiv
    ((Ideal.quotEquivOfEq hkf.symm).trans (RingHom.quotientKerEquivOfSurjective hf))).symm

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

attribute [local instance] MvPolynomial.weightedGradedAlgebra


open scoped Classical in
theorem isHomogeneous_of_isMultiHomogIdeal' {K : Type*} [DecidableEq K] {ι : K → Type*}
    {R : Type*} [CommRing R] {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) :
    (by
      classical
      exact I.IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι))) := by
  classical
  have e : I = Ideal.span
      {g | ∃ f ∈ I, ∃ b, g = weightedHomogeneousComponent (blockWeight ι) b f} := by
    apply le_antisymm
    · intro f hf
      rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨f, hf, b, rfl⟩
    · rw [Ideal.span_le]
      rintro g ⟨f, hf, b, rfl⟩
      exact hI f hf b
  rw [e]
  refine Ideal.homogeneous_span _ _ fun x hx => ?_
  obtain ⟨f, -, b, rfl⟩ := hx
  exact ⟨b, weightedHomogeneousComponent_isWeightedHomogeneous b f⟩

theorem SupSpanMultiHomog.proof : SupSpanMultiHomog.Statement := by
  classical
  intro R _ K _ ι I x e hI hx
  have h1 := isHomogeneous_of_isMultiHomogIdeal' hI
  have h2 : (Ideal.span {x}).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) :=
    Ideal.homogeneous_span _ _ (by
      rintro y rfl
      exact ⟨e, hx⟩)
  have h := h1.sup h2
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) h hf b

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalDivisorsCommute
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem ratDiv_support_finite (h4 : DivCycleFiniteSupport.Statement.{u}) {O : Type u} [CommRing O]
    [IsNoetherianRing O] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)) (f g : MRing ι O) : (Function.support (ratDiv P f g)).Finite := by
  refine ((h4 O K ι P f).union (h4 O K ι P g)).subset ?_
  intro W hW
  by_contra h
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
  exact hW (by simp [ratDiv, h.1, h.2])

theorem lt_natCast_of_add_one_le {x : WithBot ℕ∞} {n : ℕ} (h : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by
  induction x with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    have h' : e + 1 ≤ (n : ℕ∞) := by exact_mod_cast h
    have h'' : e < (n : ℕ∞) := (ENat.add_one_le_iff' (ENat.natCast_ne_top n)).mp h'
    exact_mod_cast h''

theorem VerticalDivisorsCommute.proof (h1 : CutByEffectiveDivisor.Statement.{u})
    (h2 : Representative.Statement.{u}) (h3 : IntNumAddFirst.Statement.{u})
    (h4 : DivCycleFiniteSupport.Statement.{u}) (h5 : MinimalPrimeMultiHomog.Statement.{u})
    (h6 : SupSpanMultiHomog.Statement.{u}) (h7 : SpecialQuotDim.Statement.{u})
    (h8 : SpecialIdealCorresp.Statement.{u}) (h9 : SpecialIdealMultiHomog.Statement.{u})
    (h10 : DimStrictDrop.Statement.{u}) : VerticalDivisorsCommute.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b b' f g f' g' hD hD' L
  obtain ⟨c', c'', hc', hc'', hb'⟩ := hD'.degrees
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.degrees
  have hPmh : IsMultiHomogIdeal P := hP.multiProj.multiHomog
  have : P.IsPrime := hP.multiProj.isPrime

  have hmh : ∀ (h : MRing ι O) (e : K → ℕ), IsMultiHomog h e → ∀ W, divCycle P h W ≠ 0 →
      IsMultiHomogIdeal W ∧ W ∈ (P ⊔ Ideal.span {h}).minimalPrimes ∧ IsRelevant W := by
    intro h e he W hW
    unfold divCycle at hW
    split_ifs at hW with hW'
    · exact ⟨h5 O K ι _ W (h6 O K ι P h e hPmh he) hW'.1, hW'.1, hW'.2⟩
    · exact absurd rfl hW
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'

  have hTfin : {H : Ideal (MRing ι O) | (divCycle P f' H ≠ 0 ∨ divCycle P g' H ≠ 0) ∧
      (C ϖ : MRing ι O) ∉ H}.Finite :=
    ((h4 O K ι P f').union (h4 O K ι P g')).subset fun H hH => hH.1
  obtain ⟨f₁, g₁, hV₁, hrat, hT₁⟩ := h2 O ϖ hϖ K ι P b f g hP.multiProj hD hTfin.toFinset (by
    intro H hH
    rw [Set.Finite.mem_toFinset] at hH
    obtain ⟨hne, hϖH⟩ := hH
    rcases hne with hne | hne
    · obtain ⟨hm, hmin, hrel⟩ := hmh f' c' hc' H hne
      exact ⟨⟨hmin.1.1, hm, hrel⟩, le_sup_left.trans hmin.1.2, hϖH, f', hD'.num_not_mem, hmin⟩
    · obtain ⟨hm, hmin, hrel⟩ := hmh g' c'' hc'' H hne
      exact ⟨⟨hmin.1.1, hm, hrel⟩, le_sup_left.trans hmin.1.2, hϖH, g', hD'.den_not_mem, hmin⟩)
  have e1 := h1 O ϖ hϖ K ι P d hP b f₁ g₁ hV₁ c' f' hc' hD'.num_not_mem
    (fun H hH hϖH => hT₁ H (by rw [Set.Finite.mem_toFinset]; exact ⟨Or.inl hH, hϖH⟩)) L
  have e2 := h1 O ϖ hϖ K ι P d hP b f₁ g₁ hV₁ c'' g' hc'' hD'.den_not_mem
    (fun H hH hϖH => hT₁ H (by rw [Set.Finite.mem_toFinset]; exact ⟨Or.inr hH, hϖH⟩)) L
  rw [hrat] at e1 e2

  have hadd : ∀ W, ratDiv P f g W ≠ 0 →
      vNum W (Matrix.vecCons b' L) = vNum W (Matrix.vecCons (fun k => (c' k : ℤ)) L) -
        vNum W (Matrix.vecCons (fun k => (c'' k : ℤ)) L) := by
    intro W hW
    have hϖW : (C ϖ : MRing ι O) ∈ W := hD.vertical W hW
    have hWdata : IsMultiHomogIdeal W ∧ W.IsPrime ∧ P ≤ W := by
      by_cases hWf : divCycle P f W = 0
      · have hWg : divCycle P g W ≠ 0 := by
          intro hWg; apply hW; simp [ratDiv, hWf, hWg]
        obtain ⟨hm, hmin, -⟩ := hmh g bg hbg W hWg
        exact ⟨hm, hmin.1.1, le_sup_left.trans hmin.1.2⟩
      · obtain ⟨hm, hmin, -⟩ := hmh f bf hbf W hWf
        exact ⟨hm, hmin.1.1, le_sup_left.trans hmin.1.2⟩
    obtain ⟨hWm, hWp, hPW⟩ := hWdata
    have := hWp
    have hlt : P < W := lt_of_le_of_ne hPW (fun e => hϖP (e ▸ hϖW))
    have hdrop := h10 (MRing ι O) P W hlt
    rw [hP.dim] at hdrop
    have hdim : ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
        ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [h7 O ϖ hϖ K ι W hϖW]
      have e : d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K := by omega
      rw [e] at hdrop
      exact lt_natCast_of_add_one_le hdrop
    have key := h3 (IsLocalRing.ResidueField O) K ι d (specialIdeal W)
      (h8 O ϖ hϖ K ι P W hWp hϖW).1 (h9 O K ι W hWm) hdim b' (fun k => (c'' k : ℤ)) L
    have hsum : b' + (fun k => (c'' k : ℤ)) = fun k => (c' k : ℤ) := by
      rw [← hb']; funext k; simp
    rw [hsum] at key
    unfold vNum
    rw [key]; ring
  have hZfin := ratDiv_support_finite h4 P f g
  calc cycEval (fun G => vNum G (Matrix.vecCons b' L)) (ratDiv P f g)
      = cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c' k : ℤ)) L)) (ratDiv P f g) -
          cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c'' k : ℤ)) L)) (ratDiv P f g) := by
        unfold cycEval
        rw [← finsum_sub_distrib (hZfin.subset (Function.support_mul_subset_left _ _))
          (hZfin.subset (Function.support_mul_subset_left _ _))]
        refine finsum_congr fun W => ?_
        by_cases hW : ratDiv P f g W = 0
        · simp [hW]
        · beta_reduce
          rw [hadd W hW, mul_sub]
    _ = _ := by rw [e1, e2]
    _ = cycEval (fun G => vNum G (Matrix.vecCons b L)) (ratDiv P f' g') := by
        unfold cycEval
        rw [← finsum_sub_distrib ((h4 O K ι P f').subset (Function.support_mul_subset_left _ _))
          ((h4 O K ι P g').subset (Function.support_mul_subset_left _ _))]
        refine finsum_congr fun W => ?_
        rw [← sub_mul]
        change ratDiv P f' g' W * _ = ratDiv P f' g' W * _
        by_cases hW : ratDiv P f' g' W = 0
        · simp [hW]
        · beta_reduce
          rw [if_pos (hD'.vertical W hW)]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SpanTwoIsPrimeRelevant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Defs

variable {K : Type*} {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def commonExcess (ϖ : O) (P : Ideal (MRing ι O)) (f g s : MRing ι O) : ℕ :=
  ⨆ G : {G : Ideal (MRing ι O) // (C ϖ : MRing ι O) ∈ G}, (divCycle P s G.1 * ratDiv P f g G.1).toNat

end Defs

section Lemmas

def NoCommonComponentCase.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∀ G, (C ϖ : MRing ι O) ∈ G → divCycle P s G ≠ 0 → ratDiv P f g G = 0) →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L

def CommonFactorInduction.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∃ G, (C ϖ : MRing ι O) ∈ G ∧ divCycle P s G ≠ 0 ∧ ratDiv P f g G ≠ 0) →
    (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (P' : Ideal (MRing ι' O)) (d' : ℕ), IsModelOver P' (d' + 1) →
      ∀ (b' : K' → ℤ) (f' g' : MRing ι' O), IsEffectiveVertical P' ϖ b' f' g' →
      ∀ (c' : K' → ℕ) (s' : MRing ι' O), IsMultiHomog s' c' → s' ∉ P' →
      (∀ H, divCycle P' s' H ≠ 0 → (C ϖ : MRing ι' O) ∉ H → IsVerticalDivisor H ϖ b' f' g') →
      commonExcess ϖ P' f' g' s' < commonExcess ϖ P f g s →
      ∀ L' : Fin d' → K' → ℤ, cutIdentity ϖ P' b' f' g' c' s' L') →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBridge
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def VocabMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (s : MRing ι R) (a : K → ℕ),
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a ↔ IsMultiHomog s a

def VocabMultiHomogIdeal.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)),
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P ↔ IsMultiHomogIdeal P

def VocabDivCycle.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)) (s : MRing ι R) (W : Ideal (MRing ι R)),
    ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W : ℕ) : ℤ) = divCycle P s W

def IntNumPoint.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F)) (i : ∀ k, ι k), IsMultiProjPrime V →
    ringKrullDim (MRing ι F ⧸ V) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    (∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V) →
    intNum F V (![] : Fin 0 → K → ℤ) = ReciprocityTheory.ChartRestriction.G.AI.I1.ptDeg V i

def IntNumRatSection.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (V : Ideal (MRing ι F)), IsMultiProjPrime V →
    ringKrullDim (MRing ι F ⧸ V) = ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (L : Fin n → K → ℤ) (A : K → ℤ) (f g : MRing ι F) (α β : K → ℕ),
      IsMultiHomog f α → IsMultiHomog g β → f ∉ V → g ∉ V → (∀ k, (α k : ℤ) - β k = A k) →
      intNum F V (Fin.snoc (α := fun _ => K → ℤ) L A) =
        cycEval (fun W => intNum F W L) (ratDiv V f g)

def IntNumIsFieldIntersection.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)],
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection (F := F) (ι := ι) (fun V _ L => intNum F V L)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairNumberRelabel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def PairNumberRelabel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (K₁ : Type) [Fintype K₁] [DecidableEq K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₂ : Type) [Fintype K₂] [DecidableEq K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)), (∀ v, (σ v).1 = e v.1) →
    ∀ P : Ideal (MRing ι₁ O),
      (∀ d : ℕ, IsModelOver P d → IsModelOver (P.map (rename σ)) d) ∧
      (∀ (b : K₂ → ℤ) (f g : MRing ι₁ O), IsVerticalDivisor P ϖ (b ∘ e) f g →
        IsVerticalDivisor (P.map (rename σ)) ϖ b (rename σ f) (rename σ g)) ∧
      (∀ (n : ℕ) (x x' : Fin n → K₂ → ℤ) (f g : Fin n → MRing ι₁ O)
        (Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ) (Q : List (K₂ → ℤ)),
        pairNum (P.map (rename σ)) x x' (fun i => rename σ (f i)) (fun i => rename σ (g i)) Gs Q =
          pairNum P (fun i => x i ∘ e) (fun i => x' i ∘ e) f g Gs (Q.map (· ∘ e)))

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsVerticalComponentFibre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def VerticalComponentFibre.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
    ∀ (f : MRing ι O) (b : K → ℕ), IsMultiHomog f b → f ∉ P →
    ∀ W ∈ (P ⊔ Ideal.span {f}).minimalPrimes, IsRelevant W → (C ϖ : MRing ι O) ∈ W →
      IsMultiProjPrime (specialIdeal W) ∧
        ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
          ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

