module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterEnvelopingAlgebraDirectSum
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff

noncomputable section

namespace GlobalTheory.UAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isSm_add {f f' : GAd σ J → ℂ} (h : IsSm σ J f) (h' : IsSm σ J f') : IsSm σ J (f + f') :=
  fun k γ hγ g => (h k γ hγ g).add (h' k γ hγ g)

theorem isSm_smul (a : ℂ) {f : GAd σ J → ℂ} (h : IsSm σ J f) : IsSm σ J (a • f) :=
  fun k γ hγ g => (h k γ hγ g).const_smul a

theorem differentiable_of_isSm {f : GAd σ J → ℂ} (h : IsSm σ J f) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ)
    (g : GAd σ J) : Differentiable ℝ fun t : ℝ => f (g * γ t) := by
  have h1 := h 1 (fun _ => γ) (fun _ => hγ) g
  have h2 : ContDiff ℝ ∞ fun t : ℝ => (fun _ : Fin 1 => t) := contDiff_pi.2 fun _ => contDiff_id
  have h3 := (h1.comp h2).differentiable (by simp)
  simpa [Function.comp_def] using h3

theorem lineDer_add {f f' : GAd σ J → ℂ} (h : IsSm σ J f) (h' : IsSm σ J f') {γ : ℝ → GAd σ J}
    (hγ : IsRealLine σ J γ) : lineDer γ (f + f') = lineDer γ f + lineDer γ f' := by
  funext g
  exact deriv_fun_add (differentiable_of_isSm h hγ g 0) (differentiable_of_isSm h' hγ g 0)

omit [NumberField E] in
theorem lineDer_smul (a : ℂ) (f : GAd σ J → ℂ) (γ : ℝ → GAd σ J) : lineDer γ (a • f) = a • lineDer γ f := by
  funext g
  simp only [lineDer, Pi.smul_apply, smul_eq_mul, deriv_const_mul_field']

theorem isSm_lineDer {f : GAd σ J → ℂ} (hf : IsSm σ J f) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) :
    IsSm σ J (lineDer γ f) := by
  intro k γs h g
  have h1 := hf (k + 1) (Fin.snoc (α := fun _ => ℝ → GAd σ J) γs γ)
    (fun i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hγ
      · simpa using h j) g
  have h2 : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simp only [Fin.snoc_castSucc]
      fun_prop
  have h3 : ContDiff ℝ ∞ (Function.uncurry fun (t : Fin k → ℝ) (s : ℝ) =>
      f (g * (List.ofFn fun i => γs i (t i)).prod * γ s)) := by
    convert h1.comp h2 using 1
    funext p
    simp [Function.uncurry, List.ofFn_succ', mul_assoc, -List.ofFn_succ]
  have h4 := ContDiff.fderiv (n := ∞) h3 (contDiff_const (c := (0 : ℝ))) (by simp)
  exact h4.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem isSm_foldr {l : List (ℝ → GAd σ J)} (hl : ∀ γ ∈ l, IsRealLine σ J γ) {f : GAd σ J → ℂ}
    (hf : IsSm σ J f) : IsSm σ J (l.foldr lineDer f) := by
  induction l with
  | nil => exact hf
  | cons γ l ih =>
    exact isSm_lineDer (ih fun δ hδ => hl δ (by simp [hδ])) (hl γ (by simp))

theorem foldr_add {l : List (ℝ → GAd σ J)} (hl : ∀ γ ∈ l, IsRealLine σ J γ) {f f' : GAd σ J → ℂ}
    (hf : IsSm σ J f) (hf' : IsSm σ J f') : l.foldr lineDer (f + f') = l.foldr lineDer f + l.foldr lineDer f' := by
  induction l with
  | nil => rfl
  | cons γ l ih =>
    have hl' : ∀ δ ∈ l, IsRealLine σ J δ := fun δ hδ => hl δ (by simp [hδ])
    simp only [List.foldr_cons]
    rw [ih hl', lineDer_add (isSm_foldr hl' hf) (isSm_foldr hl' hf') (hl γ (by simp))]

omit [NumberField E] in
theorem foldr_smul (l : List (ℝ → GAd σ J)) (a : ℂ) (f : GAd σ J → ℂ) :
    l.foldr lineDer (a • f) = a • l.foldr lineDer f := by
  induction l with
  | nil => rfl
  | cons γ l ih => simp only [List.foldr_cons, ih, lineDer_smul]


end GlobalTheory.UAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowMemSectionsOfMulPowMem
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem Pair.div_pow_mem_H_of_mul_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (N m : ℕ)
    (u : X.functionField), u ∈ P.H N m → u * t ^ N / s ^ m ∈ P.H 0 (b * N) → u / s ^ m ∈ P.H N 0 := by
  intro k _ X _ p D _ P b s t hG N m u hu hut x i j hi hj
  let O : Subring X.functionField := (algebraMap (X.presheaf.stalk x) X.functionField).range
  have hO : ∀ f, RegAt x f ↔ f ∈ O := fun f => Iff.rfl
  have hri : (P.r i : X.functionField) ≠ 0 := (P.r i).ne_zero
  have hrj : (P.r' j : X.functionField) ≠ 0 := (P.r' j).ne_zero
  have hs : P.loc 0 1 s i j ∈ O := (hO _).1 (hG.s_mem.1 x i j hi hj)
  have ht : P.loc (-1) b t i j ∈ O := (hO _).1 (hG.t_mem.1 x i j hi hj)
  have hs0 : P.loc 0 1 s i j ≠ 0 := by
    simp only [loc, zpow_zero, zpow_one, mul_one]
    exact mul_ne_zero hG.s_ne hrj
  have hreg : ∀ g ∈ O, g * P.loc (-1) b t i j / P.loc 0 1 s i j ∈ O → g / P.loc 0 1 s i j ∈ O :=
    fun g hg h => (hO _).1 (hG.reg x i j hi hj g ((hO _).2 hg) ((hO _).2 h))
  have hg : P.loc N m u i j ∈ O := (hO _).1 (hu x i j hi hj)
  have e1 : P.loc N m u i j * P.loc (-1) b t i j ^ N / P.loc 0 1 s i j ^ m =
      P.loc 0 ((b * N : ℕ) : ℤ) (u * t ^ N / s ^ m) i j := by
    simp only [loc, zpow_zero, zpow_one, mul_one, zpow_natCast, zpow_neg, mul_pow, inv_pow]
    push_cast
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast]
    simp only [zpow_natCast]
    field_simp
    ring
  have e2 : P.loc N m u i j / P.loc 0 1 s i j ^ m = P.loc N 0 (u / s ^ m) i j := by
    simp only [loc, zpow_zero, zpow_one, mul_one, zpow_natCast, mul_pow]
    field_simp
  have hgN : P.loc N m u i j * P.loc (-1) b t i j ^ N / P.loc 0 1 s i j ^ m ∈ O := by
    rw [e1]
    have := hut x i j hi hj
    push_cast at this ⊢
    exact (hO _).1 this
  have := regularPair_pow X.functionField O _ _ hs ht hs0 hreg m N _ hg hgN
  rw [e2] at this
  exact (hO _).2 (by exact_mod_cast this)

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowMemSectionsOfMulPowMemTwisted
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.VolBr

theorem Pair.div_pow_mem_H_of_mul_pow_sub : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ,
    ∀ (N m : ℕ) (u : X.functionField), u ∈ P.H N (m - c) → u * t ^ N / s ^ m ∈ P.H 0 (b * N - c) →
    u / s ^ m ∈ P.H N (-c) := by
  intro k _ X _ p D _ P b s t hG c N m u hu hut x i j hi hj
  let O : Subring X.functionField := (algebraMap (X.presheaf.stalk x) X.functionField).range
  have hO : ∀ f, RegAt x f ↔ f ∈ O := fun f => Iff.rfl
  have hri : (P.r i : X.functionField) ≠ 0 := (P.r i).ne_zero
  have hrj : (P.r' j : X.functionField) ≠ 0 := (P.r' j).ne_zero
  have hs : P.loc 0 1 s i j ∈ O := (hO _).1 (hG.s_mem.1 x i j hi hj)
  have ht : P.loc (-1) b t i j ∈ O := (hO _).1 (hG.t_mem.1 x i j hi hj)
  have hs0 : P.loc 0 1 s i j ≠ 0 := by
    simp only [Pair.loc, zpow_zero, zpow_one, mul_one]
    exact mul_ne_zero hG.s_ne hrj
  have hreg : ∀ g ∈ O, g * P.loc (-1) b t i j / P.loc 0 1 s i j ∈ O → g / P.loc 0 1 s i j ∈ O :=
    fun g hg h => (hO _).1 (hG.reg x i j hi hj g ((hO _).2 hg) ((hO _).2 h))
  have hg : P.loc N ((m : ℤ) - c) u i j ∈ O := (hO _).1 (hu x i j hi hj)
  have e1 : P.loc N ((m : ℤ) - c) u i j * P.loc (-1) b t i j ^ N / P.loc 0 1 s i j ^ m =
      P.loc 0 ((b : ℤ) * N - c) (u * t ^ N / s ^ m) i j := by
    simp only [Pair.loc, zpow_zero, zpow_one, mul_one, zpow_sub₀ hrj, zpow_neg, mul_pow, inv_pow, zpow_natCast]
    rw [show ((b : ℤ) * N) = ((b * N : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul]
    field_simp
  have e2 : P.loc N ((m : ℤ) - c) u i j / P.loc 0 1 s i j ^ m = P.loc N (-c) (u / s ^ m) i j := by
    simp only [Pair.loc, zpow_zero, zpow_one, mul_one, zpow_sub₀ hrj, zpow_neg, mul_pow, zpow_natCast]
    field_simp
  have hgN : P.loc N ((m : ℤ) - c) u i j * P.loc (-1) b t i j ^ N / P.loc 0 1 s i j ^ m ∈ O := by
    rw [e1]
    exact (hO _).1 (hut x i j hi hj)
  have := regularPair_pow X.functionField O _ _ hs ht hs0 hreg m N _ hg hgN
  rw [e2] at this
  exact (hO _).2 this

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceDiscKaehlerWedgePermNeg
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair.Place

variable {k K : Type} [Field k] [Field K] {c : k →+* K} (E : Place c) {n : ℕ}

theorem ord_neg (f : K) : E.ord (-f) = E.ord f := by
  by_cases hf : f = 0
  · simp [hf]
  have h1 : ((-1 : E.ring) : K) = -1 := rfl
  have hu : IsUnit (-1 : E.ring) := isUnit_one.neg
  have h0 : E.ord (-1) = 0 := by rw [← h1]; exact E.ord_eq_zero hu
  rw [neg_eq_neg_one_mul, E.ord_mul (by norm_num) hf, h0, zero_add]

theorem isFormOrd_neg_iff (η : Forms c n) (a : ℤ) : E.IsFormOrd (-η) a ↔ E.IsFormOrd η a := by
  have key : ∀ η : Forms c n, E.IsFormOrd η a → E.IsFormOrd (-η) a := by
    rintro η ⟨ω, hω, f, rfl, hf⟩
    refine ⟨ω, hω, -f, ?_, ?_⟩
    · rw [Units.val_neg, neg_smul]
    · rw [Units.val_neg, E.ord_neg, hf]
  exact ⟨fun h => by simpa using key _ h, key η⟩

theorem formOrd_neg (η : Forms c n) : E.formOrd (-η) = E.formOrd η := by
  by_cases h : ∃ a, E.IsFormOrd η a
  · obtain ⟨a, ha⟩ := h
    rw [((E.isFormOrd_neg_iff η a).2 ha).formOrd_eq, ha.formOrd_eq]
  · have h' : ¬ ∃ a, E.IsFormOrd (-η) a := fun ⟨a, ha⟩ => h ⟨a, (E.isFormOrd_neg_iff η a).1 ha⟩
    rw [formOrd, formOrd, dite_eq_right h, dite_eq_right h']

theorem disc_neg (η : Forms c n) (φ : K →₀ ℚ) : E.disc (-η) φ = E.disc η φ := by
  change (E.formOrd (-η) : ℚ) - E.ordQ φ = (E.formOrd η : ℚ) - E.ordQ φ
  rw [E.formOrd_neg]

end GlobalTheory.FieldPair.Place

namespace GlobalTheory.FieldPair

theorem dForm_comp_perm {k K : Type} [Field k] [Field K] (c : k →+* K) {n : ℕ} (x : Fin n → K)
    (σ : Equiv.Perm (Fin n)) : dForm c (x ∘ σ) = Equiv.Perm.sign σ • dForm c x := by
  rw [dForm_eq, dForm_eq]
  exact (exteriorPower.ιMulti K n).map_perm (fun i => dFun c (x i)) σ

theorem disc_dForm_perm_neg {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ)
    (x : Fin n → K) (σ : Equiv.Perm (Fin n)) (E : Place c) (φ : K →₀ ℚ) :
    E.disc (dForm c (x ∘ σ)) φ = E.disc (dForm c x) φ ∧ E.disc (-dForm c x) φ = E.disc (dForm c x) φ := by
  refine ⟨?_, E.disc_neg _ φ⟩
  rw [dForm_comp_perm]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]
  · rw [h, Units.neg_smul, one_smul, E.disc_neg]

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApi
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair


open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in
theorem _root_.GlobalTheory.FieldPair.isFreeGen_dForm_of_trBasis {k K : Type} [Field k] [CharZero k]
    [Field K] (c : k →+* K) {n : ℕ} {x : Fin n → K} (hx : _root_.GlobalTheory.FieldPair.TrBasis c x) :
    _root_.GlobalTheory.TopForm.IsFreeGen K (_root_.GlobalTheory.TopForm.dForm c x) := by
  letI : Algebra k K := c.toAlgebra
  have hb : IsTranscendenceBasis k x := hx
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range x)) K :=
    hb.isAlgebraic_field
  haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨b, hbx⟩ := _root_.GlobalTheory.exists_basis_kaehler_of_algebraicIndependent hb.1
  exact _root_.GlobalTheory.TopForm.isFreeGen_dForm x b (fun i => by rw [hbx i])


open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in
theorem _root_.GlobalTheory.FieldPair.formOrd_api : ∀ {k K : Type} [Field k] [CharZero k] [Field K]
    (c : k →+* K) (n : ℕ) (x : Fin n → K), _root_.GlobalTheory.FieldPair.TrBasis c x →
  _root_.GlobalTheory.TopForm.IsFreeGen K (_root_.GlobalTheory.TopForm.dForm c x) ∧
  ∀ E : _root_.GlobalTheory.FieldPair.Place c,
    (∃ ω : _root_.GlobalTheory.TopForm.Forms E.const n, _root_.GlobalTheory.TopForm.IsFreeGen E.ring ω) ∧
    (∀ η : _root_.GlobalTheory.TopForm.Forms c n, η ≠ 0 → E.IsFormOrd η ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η)) ∧
    (∀ (η : _root_.GlobalTheory.TopForm.Forms c n) (f : K), η ≠ 0 → f ≠ 0 →
      (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (f • η) = E.ord f + (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η) ∧
    (∀ (η : _root_.GlobalTheory.TopForm.Forms c n) (a : ℤ), η ≠ 0 → E.IsFormOrd η a →
      (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η = a) := by
  intro k K _ _ _ c n x hx
  refine ⟨_root_.GlobalTheory.FieldPair.isFreeGen_dForm_of_trBasis c hx, fun E => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact E.exists_isFreeGen hx
  · intro η hη
    exact E.isFormOrd_formOrd hx hη
  · intro η f hη hf
    exact E.formOrd_smul hx hη hf
  · intro η a _ h
    exact h.formOrd_eq

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvRepAllEnvIncl
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}


open Classical in
def lieRep (R : RealPoints θ V) : GlobalTheory.AutFinLit.LieC V →ₗ⁅ℂ⁆ Module.End ℂ (SmF θ V) :=
  DirectSum.toLieAlgebra _ (fun τ => (envRep R τ).toLieHom.comp (UniversalEnvelopingAlgebra.ι ℂ)) fun τ τ' h x y => by
    change (envRep R τ (UniversalEnvelopingAlgebra.ι ℂ x)) * envRep R τ' (UniversalEnvelopingAlgebra.ι ℂ y) -
      envRep R τ' (UniversalEnvelopingAlgebra.ι ℂ y) * envRep R τ (UniversalEnvelopingAlgebra.ι ℂ x) = 0
    rw [(envRep_comm R h _ _).eq, sub_self]

def envRepAll (R : RealPoints θ V) : GlobalTheory.AutFinLit.Env V →ₐ[ℂ] Module.End ℂ (SmF θ V) :=
  UniversalEnvelopingAlgebra.lift ℂ (lieRep R)


open Classical in
def envIncl (V : HSp D) (τ : D.what₂.Tau) : EnvAt V τ →ₐ[ℂ] GlobalTheory.AutFinLit.Env V :=
  UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp
    (DirectSum.lieAlgebraOf ℂ D.what₂.Tau (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ))

open Classical in
theorem envIncl_ι (τ : D.what₂.Tau) (x : ℂ ⊗[ℝ] LieAt V τ) :
    envIncl V τ (UniversalEnvelopingAlgebra.ι ℂ x) =
      UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x) := by
  simp [envIncl]

theorem envRepAll_envIncl (R : RealPoints θ V) (τ : D.what₂.Tau) (u : EnvAt V τ) :
    envRepAll R (envIncl V τ u) = envRep R τ u := by
  classical
  have : (envRepAll R).comp (envIncl V τ) = envRep R τ := by
    apply UniversalEnvelopingAlgebra.hom_ext
    refine LieHom.ext fun x => ?_
    change envRepAll R (envIncl V τ (UniversalEnvelopingAlgebra.ι ℂ x)) = envRep R τ (UniversalEnvelopingAlgebra.ι ℂ x)
    rw [envIncl_ι, envRepAll, UniversalEnvelopingAlgebra.lift_ι_apply, lieRep]
    exact DirectSum.toModule_lof ℂ (M := fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x
  exact congrArg (fun f : EnvAt V τ →ₐ[ℂ] _ => f u) this

end GlobalTheory.CentralOps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharH0H1BoundHigher
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.NefRR

theorem abs_chi_sub_hdim_zero_add_hdim_one_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (n : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (n : ℕ) → ∀ e : ℕ → ℕ, (∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * e m)) → ∃ C : ℕ, ∀ m : ℕ, |chi k (twist F (lbPow L m)) - (hdim k (twist F (lbPow L m)) 0 : ℤ) + (hdim k (twist F (lbPow L m)) 1 : ℤ)| ≤ C * (e m : ℤ) := by
  intro k _ _ X _ hp n L hL F _ hF e he
  choose C hC using fun i : ℕ => he (i + 2) (by omega)
  refine ⟨∑ i ∈ Finset.range n, C i, fun m => ?_⟩
  have hM : (lbPow L m).IsLB := isLB_lbPow hL m
  haveI : IsFiniteQC (twist F (lbPow L m)) := isFiniteQC_twist hM
  have hv : ∀ i, n + 2 ≤ i → Subsingleton (coh (twist F (lbPow L m)) i) := fun i hi =>
    subsingleton_coh_of_isProjOver hp _
      (((suppDim_twist hM).trans_le hF).trans_lt (by exact_mod_cast (by omega : n < i)))
  rw [chi_eq_sum_range k (n + 2) hv, Finset.sum_range_succ', Finset.sum_range_succ']
  have h : ∀ a b c : ℤ, a + (-1 : ℤ) ^ (0 + 1) * b + (-1 : ℤ) ^ 0 * c - c + b = a := by
    intro a b c; ring
  rw [h]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  exact_mod_cast hC i m

end GlobalTheory.NefRR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjugatorsDifferByCentralizerStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integral_conjugators_differ_by_centralizer : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    (minpoly G.F (γ : G.C)).Separable → ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C),
    Function.Injective ι → (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (κ : Type) (b : Module.Basis κ ℚ G.C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ X X' : (v.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X⁻¹) →
      IsIntB v b (↑X' * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X'⁻¹) →
      ∃ m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ↑m * ↑X'⁻¹) ∧
        IsIntB v b (↑X' * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ↑m⁻¹ * ↑X⁻¹) := by
  first | (exact @GlobalTheory.LatStep.lattice_step) | (exact GlobalTheory.LatStep.lattice_step) | (intros; apply GlobalTheory.LatStep.lattice_step  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionNonvanishingAtNotSpecializing
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_sec_mem_not_mem_of_not_specializes :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (N : LB X) (x z : X), IsAmpleLB N → ¬ z ⤳ x →
      ∃ (l : ℕ) (s : (lbPow N l).Sec), 0 < l ∧ x ∈ nonzeroLocus s ∧ z ∉ nonzeroLocus s := by
  intro X _ _ N x z hN hzx
  let U : X.Opens := ⟨(closure ({z} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩
  have hx : x ∈ U := fun h => hzx (specializes_iff_mem_closure.2 h)
  obtain ⟨n, hn, s, hs, hle, -⟩ := hN.exists_affine_le hx
  exact ⟨n, s, hn, hs, fun h => hle h (subset_closure rfl)⟩

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseLevelVectorOfPrincipalLevelFixedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseLevel_vector_of_principalLevel_fixed : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) (π : Formalism.L2.NG.FinTyp D.host.E n) (v : Formalism.AUTREP.GAf D.host.E n → ℂ), v ∈ π.S → v ≠ 0 → principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv)) (fun _ => 1) v → (∀ κ : G → Formalism.AUTREP.GAf D.host.E n, (∀ g, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ (κ g))) → ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (κ g) v = v) → ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 (R.levR F false))) (fun κ => levChi _ (R.βY 0) (R.dat0 (R.levR F false)) (PY.ψ κ)) x := by
  first | exact @GlobalTheory.BaseVec.exists_base_vec | exact GlobalTheory.BaseVec.exists_base_vec | (intros; apply GlobalTheory.BaseVec.exists_base_vec <;> assumption)
end

