module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0476
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryIdempotentInIntegralClosure
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.ConjCompl

def clos (D : D7) (I : Ideal (𝓞 D.host.E)) : AddSubgroup (Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf D.host.F, ∃ x : 𝓞 D.host.E, x ∈ I ∧ y = a ⊗ₜ[D.host.F] (x : D.host.E)}

theorem intAf_mul' {F : Type} [Field F] [NumberField F] {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) :
    a * b ∈ intAf F := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem one_mem_intAf' {F : Type} [Field F] [NumberField F] : (1 : Af F) ∈ intAf F := fun v => by
  rw [map_one]; exact one_mem _

variable {D : D7}

theorem tmul_mem_clos {I : Ideal (𝓞 D.host.E)} {a : Af D.host.F} (ha : a ∈ intAf D.host.F) {x : 𝓞 D.host.E}
    (hx : x ∈ I) : a ⊗ₜ[D.host.F] (x : D.host.E) ∈ clos D I :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

theorem mul_mem_clos {I J : Ideal (𝓞 D.host.E)} {y z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ clos D I) (hz : z ∈ clos D J) : y * z ∈ clos D (I * J) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x', hx', rfl⟩ := hz
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      have e : (x : D.host.E) * (x' : D.host.E) = ((x * x' : 𝓞 D.host.E) : D.host.E) := rfl
      rw [e]
      exact tmul_mem_clos (intAf_mul' ha hb) (Ideal.mul_mem_mul hx hx')
    | zero => rw [zero_mul]; exact zero_mem _
    | add _ _ _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
    | neg _ _ h => rw [neg_mul]; exact neg_mem h
  | zero => rw [mul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg _ _ h => rw [mul_neg]; exact neg_mem h

theorem intAE_eq_clos : intAE D = clos D ⊤ := by
  unfold intAE clos
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, Submodule.mem_top, true_and]

theorem one_mem_clos : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ clos D ⊤ := by
  have h := tmul_mem_clos (D := D) (I := ⊤) one_mem_intAf' (Submodule.mem_top (x := (1 : 𝓞 D.host.E)))
  have e : ((1 : 𝓞 D.host.E) : D.host.E) = 1 := rfl
  rwa [e, ← Algebra.TensorProduct.one_def] at h

theorem prod_mem_clos {ι : Type} (s : Finset ι) (f : ι → Af D.host.F ⊗[D.host.F] D.host.E)
    (I : ι → Ideal (𝓞 D.host.E)) (h : ∀ i ∈ s, f i ∈ clos D (I i)) : ∏ i ∈ s, f i ∈ clos D (∏ i ∈ s, I i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, Ideal.one_eq_top]; exact one_mem_clos
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_mem_clos (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem prod_one_sub {A ι : Type} [CommRing A] (c : ι → A) (s : Finset ι)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → c i * c j = 0) : ∏ i ∈ s, (1 - c i) = 1 - ∑ i ∈ s, c i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ih fun i hi j hj hij => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij]
    have h0 : c a * ∑ i ∈ s, c i = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj =>
        h a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (fun e => ha (e ▸ hj))
    linear_combination h0

theorem exists_pow_eq_span' {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (n : ℕ) (s : 𝓞 F), 0 < n ∧ v.asIdeal ^ n = Ideal.span {s} := by
  classical
  have hv : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  set n := Fintype.card (ClassGroup (𝓞 F)) with hn
  have hvn : v.asIdeal ^ n ∈ nonZeroDivisors (Ideal (𝓞 F)) := pow_mem hv n
  have e : (⟨v.asIdeal ^ n, hvn⟩ : nonZeroDivisors (Ideal (𝓞 F))) = ⟨v.asIdeal, hv⟩ ^ n := Subtype.ext (by simp)
  have h1 : ClassGroup.mk0 ⟨v.asIdeal ^ n, hvn⟩ = 1 := by
    rw [e, map_pow]
    exact pow_card_eq_one
  obtain ⟨s, hs⟩ := ((ClassGroup.mk0_eq_one_iff hvn).1 h1).principal
  exact ⟨n, s, Fintype.card_pos, hs⟩

theorem finPart_es_mem {es : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt es PP)
    (hne : conjI PP.asIdeal ≠ PP.asIdeal) : finPart D es ∈ clos D (conjI PP.asIdeal) := by
  have hmax : (conjI PP.asIdeal).IsMaximal := by
    rw [GlobalTheory.LiftIdeal.conjI_eq_map D]; exact GlobalTheory.LiftIdeal.isMaximal_map D PP
  obtain ⟨s, hs, hsP⟩ : ∃ s ∈ conjI PP.asIdeal, s ∉ PP.asIdeal := by
    by_contra hc
    push_neg at hc
    exact hne (hmax.eq_of_le PP.isPrime.ne_top hc)
  have hs0 : s ≠ 0 := fun e => hsP (e ▸ PP.asIdeal.zero_mem)
  have hsE : (s : D.host.E) ≠ 0 := fun e => hs0 (RingOfIntegers.coe_eq_zero_iff.1 e)
  have hint : finPart D (es * incA D ((s : D.host.E))⁻¹) ∈ intAE D := by
    by_contra hc
    exact hsP ((h.2 s hs0).2 hc)
  rw [intAE_eq_clos] at hint
  have e1 : es = es * incA D ((s : D.host.E))⁻¹ * incA D (s : D.host.E) := by
    rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hsE, map_one, mul_one]
  have hgen : finPart D (incA D (s : D.host.E)) ∈ clos D (conjI PP.asIdeal) := by
    have e2 : finPart D (incA D (s : D.host.E)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (s : D.host.E) := by
      show Algebra.TensorProduct.map _ _ ((1 : AF D.host.F) ⊗ₜ[D.host.F] (s : D.host.E)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
    rw [e2]; exact tmul_mem_clos one_mem_intAf' hs
  rw [e1, map_mul]
  have h3 := mul_mem_clos hint hgen
  rwa [Ideal.top_mul] at h3

theorem one_sub_mem {PP : Formalism.L2.DIV.Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal) {α : Af D.host.F}
    (h1 : evalV D.host.F v α = 1) (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    (1 - α) ⊗ₜ[D.host.F] (1 : D.host.E) ∈ clos D (conjI PP.asIdeal) := by
  obtain ⟨n, t, hn, ht⟩ := exists_pow_eq_span' v
  have htv : t ∈ v.asIdeal := Ideal.pow_le_self hn.ne' (ht ▸ Ideal.mem_span_singleton_self t)
  have htw : ∀ w : HeightOneSpectrum (𝓞 D.host.F), w ≠ v → t ∉ w.asIdeal := fun w hw h => by
    have h2 : v.asIdeal ^ n ≤ w.asIdeal := by rw [ht, Ideal.span_le, Set.singleton_subset_iff]; exact h
    exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top (w.isPrime.le_of_pow_le h2))).symm
  have ht0 : (t : D.host.F) ≠ 0 := by
    intro h0'
    have : t = 0 := by exact_mod_cast h0'
    subst this
    rw [Ideal.span_singleton_eq_bot.2 rfl] at ht
    exact v.ne_bot ((pow_eq_zero_iff hn.ne').1 ht)
  set a : Af D.host.F := algebraMap D.host.F (Af D.host.F) (t : D.host.F)⁻¹ * (1 - α) with ha_def
  have ha : a ∈ intAf D.host.F := by
    intro w
    rw [ha_def, map_mul, AlgHom.commutes, map_sub, map_one]
    by_cases hw : w = v
    · subst hw; rw [h1, sub_self, mul_zero]; exact zero_mem _
    · rw [h0 w hw, sub_zero, mul_one, HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (((((t : D.host.F))⁻¹ : D.host.F) : HeightOneSpectrum.adicCompletion D.host.F w)) ≤ 1
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
        show ((t : D.host.F)) = algebraMap (𝓞 D.host.F) D.host.F t from rfl,
        (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 (htw w hw), inv_one]
  have ecoe : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (t : D.host.F) := rfl
  have hx : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ conjI PP.asIdeal := by
    apply Ideal.subset_span
    refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, ?_, ?_⟩
    · rw [← Ideal.mem_comap, hv]; exact htv
    · rw [ecoe]
      simp [ReciprocityTheory.ChartRestriction.G.FD.cc]
  have h3 := tmul_mem_clos ha hx
  have e : a ⊗ₜ[D.host.F] ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) =
      (1 - α) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [ecoe, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, ha_def, ← mul_assoc,
      ← map_mul, mul_inv_cancel₀ ht0, map_one, one_mul]
  rwa [e] at h3

theorem finPart_one_sub_cA_mem {es : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt es PP)
    (hne : conjI PP.asIdeal ≠ PP.asIdeal) : finPart D (1 - cA D es) ∈ clos D (conjI PP.asIdeal) := by
  obtain ⟨-, -, v, ε, hε, h3⟩ := h.1
  have hsplit := GlobalTheory.LevelPlaces.splitAt_of h.1 hε h3
  obtain ⟨Q, hQ, hQv⟩ := GlobalTheory.IdemPrime.exists_isIdemAt D v es hsplit
  have hQP : Q = PP := GlobalTheory.PlaceVec.isIdemAt_inj hQ h
  subst hQP
  obtain ⟨α, rfl, hα1, hα0⟩ := hε
  have e1 : 1 - cA D es = es + (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) := by
    rw [← h3]; ring
  have e2 : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [e1, map_add (f := _), map_sub, map_one, e2, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul]
  exact add_mem (finPart_es_mem h hne) (one_sub_mem hQv hα1 hα0)

theorem offConj : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) →
    finPart D (1 - cA D e) ∈ AddSubgroup.closure {y | ∃ a ∈ intAf D.host.F, ∃ x : 𝓞 D.host.E,
      x ∈ GlobalTheory.LiftLevel.liftI Pg Q ∧ y = a ⊗ₜ[D.host.F] (x : D.host.E)} := by
  intro D Pg Q e he
  have he' := he
  obtain ⟨⟨es, hes, rfl⟩, h0⟩ := he
  have hz : ∀ i ∈ Pg ∪ Q, ∀ j ∈ Pg ∪ Q, es i * cA D (es j) = 0 := by
    have hsum : ∑ x ∈ (Pg ∪ Q) ×ˢ (Pg ∪ Q), es x.1 * cA D (es x.2) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_product, ← h0, map_sum, Finset.sum_mul_sum]
    have hall := GlobalTheory.PlaceVec.idem_eq_zero_of_sum (A := AE D) GlobalTheory.PlaceVec.natCast_mul_eq_zero
      (fun x : Formalism.L2.DIV.Pl D.host.E × Formalism.L2.DIV.Pl D.host.E => es x.1 * cA D (es x.2)) ((Pg ∪ Q) ×ˢ (Pg ∪ Q))
      (fun x hx => by
        obtain ⟨h1, h2⟩ := Finset.mem_product.1 hx
        show es x.1 * cA D (es x.2) * (es x.1 * cA D (es x.2)) = es x.1 * cA D (es x.2)
        rw [mul_mul_mul_comm, ← map_mul, (hes _ h1).1.1, (hes _ h2).1.1]) hsum
    exact fun i hi j hj => hall (i, j) (Finset.mem_product.2 ⟨hi, hj⟩)
  have horth : ∀ i ∈ Pg ∪ Q, ∀ j ∈ Pg ∪ Q, i ≠ j → cA D (es i) * cA D (es j) = 0 := by
    intro i hi j hj hij
    rcases GlobalTheory.PlaceVec.splitIdem_eq_or (hes i hi).1 (hes j hj).1 (hz i hi j hj) (hz j hj i hi) with e | e
    · exact absurd (GlobalTheory.PlaceVec.isIdemAt_inj (hes i hi) (by rw [e]; exact hes j hj)) hij
    · rw [← map_mul, e, map_zero]
  show finPart D _ ∈ clos D (GlobalTheory.LiftLevel.liftI Pg Q)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← prod_one_sub _ _ horth, map_prod]
  exact prod_mem_clos (Pg ∪ Q) _ (fun PP => conjI PP.asIdeal) fun PP hP =>
    finPart_one_sub_cA_mem (hes PP hP) (by rw [GlobalTheory.LiftIdeal.conjI_eq_map D]; exact GlobalTheory.LiftIdeal.map_ne he' hP hP)

end GlobalTheory.ConjCompl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjFockPureTensorMapNegFormSpaceEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.FockConjNeg

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem dRho_cj_neg {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (S T : HSp D)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO (GlobalTheory.Grid.neg S) T → ℂ) :
    dRho (heisO ψ S T) θ τ z (cj id g) = cj id (dRho (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ z g) := by
  funext x
  show deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (cj id g) x) 0 =
    starRingEnd ℂ (deriv (fun t : ℝ => heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) g x) 0)
  have e : (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (cj id g) x) =
      fun t => star (heisO ψ (GlobalTheory.Grid.neg S) T (lineAt θ τ z t) g x) := by
    funext t
    rw [GlobalTheory.CjNeg.heis_negS' hψ]
    rfl
  rw [e, deriv.star]
  rfl

theorem cplxO_neg_left {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ)
    (u : Matrix (Fin m) (Fin n) ℂ) : cplxO (-sS) sT u = -cplxO sS sT u := by
  simp [cplxO, Matrix.mul_neg, smul_neg]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem aPlus_cj_neg {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S T : HSp D} {g : WO (GlobalTheory.Grid.neg S) T → ℂ} (hg : IsThetaFunO ψ (GlobalTheory.Grid.neg S) T g) (τ : D.what₂.Tau)
    (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    cj id (aPlus (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ (cplxO (-sS) sT) u g) =
      aPlus (heisO ψ S T) θ τ (cplxO sS sT) u (cj id g) := by
  have hn := GlobalTheory.FockAdjoint.dRho_neg' hψ hθ hg τ (cplxO sS sT u)
  unfold aPlus crea
  rw [cplxO_neg_left, hn, dRho_cj_neg hψ, dRho_cj_neg hψ]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul, map_mul, map_sub, map_neg,
    map_inv₀, Complex.conj_ofReal, Complex.conj_I]
  ring

end GlobalTheory.FockConjNeg

namespace GlobalTheory.FockConjNeg

variable {D : D7}

theorem fock_true_eq_ptF (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) (P : GlobalTheory.Grid.Pol S T) :
    GlobalTheory.Grid.fock ψ θ true S T f P = ptF ψ θ (frSgn true (Fr.ofModel S.M)) (Fr.ofModel T.M) f P := by
  have hc : (frSgn true (Fr.ofModel S.M)).cart = GlobalTheory.Grid.cartS true S :=
    funext fun τ => cart_frSgn true (Fr.ofModel S.M) τ
  unfold ptF
  rw [hc]
  rfl

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem cj_ptF_neg {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {V W : HSp D} (A : Fr V) (B : Fr W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ (GlobalTheory.Grid.neg V) W f)
    (P : PolF D W.rank V.rank) :
    cj id (ptF ψ θ (frSgn true A) B f P) = ptF ψ θ A B (cj id f) (MvPolynomial.map (starRingEnd ℂ) P) := by
  have hcf : IsThetaFunO ψ V W (cj id f) := GlobalTheory.CjNeg.theta_negS' hψ hf
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.map_C, ← mul_one (MvPolynomial.C a), ← mul_one (MvPolynomial.C (starRingEnd ℂ a)),
      GlobalTheory.FockAdjoint.ptF_C, GlobalTheory.FockAdjoint.ptF_one, GlobalTheory.FockAdjoint.ptF_C, GlobalTheory.FockAdjoint.ptF_one]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  | add p q hp hq =>
    rw [map_add (f := _), GlobalTheory.FockAdjoint.ptF_add, GlobalTheory.FockAdjoint.ptF_add, ← hp, ← hq]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
  | mul_X p v hp =>
    rw [map_mul, MvPolynomial.map_X, mul_comm, GlobalTheory.FockAdjoint.ptF_X_mul hψ hθ (frSgn true A) B hf, mul_comm,
      GlobalTheory.FockAdjoint.ptF_X_mul hψ hθ A B hcf, ← hp, cart_frSgn]
    exact aPlus_cj_neg hψ hθ (GlobalTheory.FockAdjoint.ptF_theta hψ hθ (frSgn true A) B hf p) v.1 _ _ _

theorem fock_neg_cj : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (f : WO S.V T.V → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → IsThetaFunO ψ (GlobalTheory.Grid.neg S.V) T.V f → ∀ P : GlobalTheory.Grid.Pol S T, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.Grid.fock ψ θ true S T f P) = GlobalTheory.Chain.ptOf ψ θ S.M T.M (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) (MvPolynomial.map (starRingEnd ℂ) P) := by
  intro D S T ψ θ f hψ hθ hf P
  rw [fock_true_eq_ptF, cj_ptF_neg hψ hθ _ _ hf]
  rfl

end GlobalTheory.FockConjNeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateIdempotentChartPlacesInjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.ChartPlaces

variable {D : D7}

theorem mul_eq_zero_of_ne {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ Q ∈ P, Formalism.L2.NTheta.IsIdemAt (es Q) Q) {Q Q' : Formalism.L2.DIV.Pl D.host.E} (hQ : Q ∈ P) (hQ' : Q' ∈ P)
    (hne : Q ≠ Q') : es Q * es Q' = 0 := by
  refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hes Q hQ).1 (hes Q' hQ').1).resolve_left fun h => hne ?_
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [(hes Q hQ).2 x hx, (hes Q' hQ').2 x hx, h]

theorem chart_places_injective : ∀ {D : D7} (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D), (∀ Q ∈ P, Formalism.L2.NTheta.IsIdemAt (es Q) Q) → e = ∑ Q ∈ P, es Q → e * cA D e = 0 → ∀ v : ↥P → HeightOneSpectrum (𝓞 D.host.F), (∀ Q : ↥P, ∃ π : AE D →+* Fv D.host.F (v Q), GlobalTheory.SplitHecke.Chart (cA D (es Q)) (v Q) π) → Function.Injective v := by
  intro D e P es hes hsum hec v hπ
  have hsplit : ∀ Q ∈ P, Formalism.L2.Theta.IsSplitIdem D (es Q) := fun Q hQ => (hes Q hQ).1
  have horth : ∀ Q ∈ P, ∀ Q' ∈ P, Q' ≠ Q → es Q * es Q' = 0 :=
    fun Q hQ Q' hQ' hne => mul_eq_zero_of_ne hes hQ hQ' (Ne.symm hne)

  have habs : ∀ Q ∈ P, es Q * e = es Q := fun Q hQ => by
    rw [hsum]; exact GlobalTheory.PlaceModelSum.mul_sum_orth hsplit horth hQ

  have hcross : ∀ Q ∈ P, ∀ Q' ∈ P, es Q' * cA D (es Q) = 0 := fun Q hQ Q' hQ' => by
    have h1 : cA D (es Q) * cA D e = cA D (es Q) := by rw [← map_mul, habs Q hQ]
    calc es Q' * cA D (es Q) = (es Q' * e) * (cA D e * cA D (es Q)) := by
          rw [habs Q' hQ', mul_comm (cA D e), h1]
      _ = es Q' * (e * cA D e) * cA D (es Q) := by ring
      _ = 0 := by rw [hec, mul_zero, zero_mul]
  intro Q Q' hvv
  by_contra hne
  have hne' : (Q : Formalism.L2.DIV.Pl D.host.E) ≠ Q' := fun h => hne (Subtype.ext h)
  obtain ⟨π, hπc⟩ := hπ Q
  obtain ⟨π', hπc'⟩ := hπ Q'
  have hs' : Formalism.L2.Theta.IsSplitIdem D (cA D (es Q')) := GlobalTheory.PlaceModelSum.isSplitIdem_cA (hsplit Q' Q'.2)
  obtain ⟨hid', hort', v', ε', ⟨α', rfl, hα1, hα0⟩, hsum'⟩ := hs'

  have hπ'1 : π' (cA D (es Q')) = 1 := by
    have := (hπc'.2.1 (1 - cA D (es Q'))).2 (by rw [mul_sub, mul_one, hid', sub_self])
    rwa [map_sub, map_one, sub_eq_zero, eq_comm] at this
  have hπ'0 : π' (cA D (cA D (es Q'))) = 0 := (hπc'.2.1 _).2 hort'
  have hw1 : evalV D.host.F (v Q') α' = 1 := by
    have := hπc'.2.2.1 (pairA D.host.F 0 α')
    rw [← hsum', map_add (f := _), hπ'1, hπ'0, add_zero] at this
    exact this.symm
  have hwv : v Q' = v' := by
    by_contra h
    rw [hα0 _ h] at hw1
    exact zero_ne_one hw1

  have hA : π (cA D (es Q')) = 0 := (hπc.2.1 _).2 (by
    rw [← map_mul, mul_eq_zero_of_ne hes Q.2 Q'.2 hne', map_zero])
  have hB : π (cA D (cA D (es Q'))) = 0 := (hπc.2.1 _).2 (by
    rw [cA_cA, mul_comm]; exact hcross Q Q.2 Q' Q'.2)
  have hC := hπc.2.2.1 (pairA D.host.F 0 α')
  rw [← hsum', map_add (f := _), hA, hB, add_zero] at hC
  have h0 : evalV D.host.F (v Q) α' = 0 := hC.symm
  rw [hvv.trans hwv, hα1] at h0
  exact one_ne_zero h0

end GlobalTheory.ChartPlaces
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecompAtZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.KFinDecomp

variable {D : D7}

def Cls (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) : Set (GA D N.V → ℂ) :=
  {f | GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N f ∧ ∀ k ∈ U, k ∈ GfC N.V → ∀ g, f (g * k) = f g}

structure IsOpAt (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ))
    (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop) (τ : D.what₂.Tau) (A : (GA D N.V → ℂ) → (GA D N.V → ℂ)) : Prop where

  cont : ∀ f, Continuous f → Continuous (A f)

  add : ∀ f f', Continuous f → Continuous f' → A (f + f') = A f + A f'

  smul : ∀ (c : ℂ) f, Continuous f → A (c • f) = c • A f

  maps : ∀ f ∈ 𝒞, A f ∈ 𝒞

  keep : ∀ τ', τ' ≠ τ → ∀ f ∈ 𝒞, Ty τ' f → Ty τ' (A f)

  tr : ∀ τ', τ' ≠ τ → ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ'), ∀ f ∈ 𝒞,
    A (rTr N.V (atTau θ N.V τ' g) f) = rTr N.V (atTau θ N.V τ' g) (A f)

  lie : ∀ τ', τ' ≠ τ → ∀ X ∈ lieAt N.V τ', ∀ f ∈ 𝒞, A (Rder θ N.V τ' X f) = Rder θ N.V τ' X (A f)

def DecompAt (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ))
    (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop) (τ : D.what₂.Tau) : Prop :=
  ∃ (m : ℕ) (a : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ)
    (A : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → (GA D N.V → ℂ) → (GA D N.V → ℂ)),
    (∀ j u, IsOpAt θ N 𝒞 Ty τ (A j u)) ∧
    (∀ j, ∀ f ∈ 𝒞, (∀ u u', A j (u + u') f = A j u f + A j u' f) ∧ (∀ (c : ℂ) u, A j (c • u) f = c • A j u f) ∧
      (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ,
        (w : N.M.H τ) = N.M.rep τ k u → A j w f = rTr N.V (atTau θ N.V τ k) (A j u f)) ∧
      (∀ X ∈ lieAt N.V τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ,
        (w : N.M.H τ) = dRep (N.M.rep τ) X u → A j w f = Rder θ N.V τ X (A j u f))) ∧
    ∀ f ∈ 𝒞, Ty τ f → f = ∑ j, A j (a j) f

theorem isOpAt_id (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ))
    (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop) (τ : D.what₂.Tau) : IsOpAt θ N 𝒞 Ty τ id :=
  ⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => rfl⟩

end GlobalTheory.KFinDecomp

end
end

