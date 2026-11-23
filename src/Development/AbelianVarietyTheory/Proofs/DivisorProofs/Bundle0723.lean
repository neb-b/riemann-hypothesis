module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftQuasiLogarithmAlongPdThickening
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameReflTransGenCyclicChain
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0673
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAdaptedBasisQuasiLogarithmsFrame
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.LiftBasis

theorem exists_lift_isAdapted : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → ∀ (k : ℕ) (e0 : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C), IsBasis c.μ e0 → IsAdapted (RingHom.id O) c.μ e0 → ∃ e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q, (∀ l, map Θ (e l) = e0 l) ∧ IsBasis μ' e ∧ IsAdapted F.θ μ' e := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hμ' hμ Θ hΘ k e0 hB hA
  have hC : IsFrame p C (RingHom.id O) := _root_.GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  have hF : IsFrame p F.Q F.θ := F.frame
  have hμf : (fun i => map F.θ (μ' i)) = c.μ := funext hμ

  have hw : ∀ l, ∃ w : Fin d → F.B, (∀ i, lin (e0 l) i = algebraMap O C (F.θ (w i))) ∧
      ∀ j, l = Sum.inl j → w = Pi.single j 1 := by
    intro l
    cases l with
    | inl j =>
      refine ⟨Pi.single j 1, fun i => ?_, fun j' h => by cases h; rfl⟩
      rw [(hA j).2]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    | inr j =>
      refine ⟨fun i => Classical.choose (hF.surj (Classical.choose ((hB.1 (Sum.inr j)).2.1 i))),
        fun i => ?_, fun j' h => by cases h⟩
      rw [Classical.choose_spec (hF.surj _)]
      exact (Classical.choose_spec ((hB.1 (Sum.inr j)).2.1 i)).2
  choose w hw1 hw2 using hw
  have hlift : ∀ l, ∃ f : MvPowerSeries (Fin d) F.Q, QL μ' ⊤ f ∧ map Θ f = e0 l ∧
      ∀ i, lin f i = algebraMap F.B F.Q (w l i) := by
    intro l
    refine _root_.GlobalTheory.QLog.KLift.lift_quasiLog p F.B O F.Q F.θ hF d μ' hμ' C hC Θ hΘ (e0 l) (w l) ?_ (hw1 l)
    rw [hμf]; exact hB.1 l
  choose e he1 he2 he3 using hlift
  refine ⟨e, he2, ?_, ?_⟩
  · refine _root_.GlobalTheory.basis_lift p F.B O F.Q F.θ hF d μ' hμ' C hC Θ hΘ (Fin d ⊕ Fin k) e he1 ?_
      (_root_.GlobalTheory.BChain.reflTransGen_isStep p C v O hv ε hε F)
    rw [hμf]
    have : (fun i => map Θ (e i)) = e0 := funext he2
    rw [this]; exact hB
  · intro i
    refine ⟨fun α => ?_, ?_⟩
    · obtain ⟨b, -, eb⟩ := (he1 (Sum.inl i)).2.2 α
      refine ⟨b, RingHom.mem_ker.2 ?_, eb⟩
      obtain ⟨b', hb', eb'⟩ := (hA i).1 α
      have hb0 : b' = 0 := RingHom.mem_ker.1 hb'
      have hup : up C c.μ = fun j => map Θ (up F.Q μ' j) :=
        funext (WindowMat.up_map F.θ Θ hΘ hμ)
      have key : algebraMap O C (F.θ b) = 0 := by
        rw [← hΘ, ← eb, ← coeff_map, Window.map_formalGroupLawCoboundaryOne_eq Θ _ (Window.constantCoeff_up hμ'.const),
          ← hup, he2, eb', hb0, map_zero]
      exact hC.inj (by rw [key, map_zero])
    · funext j
      rw [he3, hw2 _ i rfl]
      by_cases hij : j = i
      · subst hij; simp
      · simp [Pi.single_apply, hij]

end GlobalTheory.QLog.LiftBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaxLocLConjBound
section
open Complex ComplexConjugate

noncomputable section

namespace GlobalTheory.JSW.LogPos

theorem prod_inv_one_sub_eq_exp (S : Multiset ℂ) (h : ∀ w ∈ S, ‖w‖ < 1) :
    (S.map fun w => (1 - w)⁻¹).prod = exp (S.map fun w => -log (1 - w)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, exp_add,
      ih fun w hw => h w (Multiset.mem_cons_of_mem hw)]
    congr 1
    have ha : 1 - a ≠ 0 := by
      intro h0
      have e : a = 1 := by linear_combination -h0
      have := h a (Multiset.mem_cons_self a S)
      simp [e] at this
    rw [exp_neg, exp_log ha]

theorem hasSum_log (S : Multiset ℂ) (h : ∀ w ∈ S, ‖w‖ < 1) :
    HasSum (fun n : ℕ => (S.map fun w => w ^ n).sum / n) (S.map fun w => -log (1 - w)).sum := by
  induction S using Multiset.induction_on with
  | empty => simpa using hasSum_zero
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, add_div]
    exact (hasSum_taylorSeries_neg_log (h a (Multiset.mem_cons_self a S))).add
      (ih fun w hw => h w (Multiset.mem_cons_of_mem hw))

theorem sum_pow_product (x : ℂ) (n : ℕ) (s t : Multiset ℂˣ) :
    ((s ×ˢ t).map fun p : ℂˣ × ℂˣ => ((p.1 : ℂ) * p.2 * x) ^ n).sum =
      x ^ n * (s.map fun b : ℂˣ => (b : ℂ) ^ n).sum * (t.map fun b : ℂˣ => (b : ℂ) ^ n).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_product, Multiset.map_add (f := _), Multiset.sum_add, ih, Multiset.map_map]
    simp only [Function.comp_def, mul_pow]
    rw [Multiset.sum_map_mul_right, Multiset.sum_map_mul_left, Multiset.map_cons, Multiset.sum_cons]
    ring

theorem sum_pow_star (n : ℕ) (B : Multiset ℂˣ) :
    ((B.map star).map fun b : ℂˣ => (b : ℂ) ^ n).sum = conj (B.map fun b : ℂˣ => (b : ℂ) ^ n).sum := by
  rw [map_multiset_sum, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun b _ => ?_
  simp [Units.coe_star, star_pow]

theorem cpow_neg_eq (q : ℕ) (σ : ℝ) : (q : ℂ) ^ (-(σ : ℂ)) = (((q : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast, ofReal_neg]

theorem norm_pair_le {B : Multiset ℂˣ} {M : ℝ} (hM : ∀ b ∈ B, ‖(b : ℂ)‖ ^ 2 ≤ M) {p : ℂˣ × ℂˣ}
    (hp : p ∈ B ×ˢ B.map star) : ‖(p.1 : ℂ)‖ * ‖(p.2 : ℂ)‖ ≤ M := by
  rw [Multiset.mem_product] at hp
  obtain ⟨b', hb', hpb⟩ := Multiset.mem_map.1 hp.2
  have h1 := hM _ hp.1
  have h2 := hM _ hb'
  have e2 : ‖(p.2 : ℂ)‖ = ‖(b' : ℂ)‖ := by rw [← hpb, Units.coe_star, norm_star]
  rw [e2]
  nlinarith [sq_nonneg (‖(p.1 : ℂ)‖ - ‖(b' : ℂ)‖)]

theorem locL_conj_eq_exp (q : ℕ) (B : Multiset ℂˣ) (M : ℝ) (hM : ∀ b ∈ B, ‖(b : ℂ)‖ ^ 2 ≤ M) (σ : ℝ)
    (hσ : M * (q : ℝ) ^ (-σ) < 1) :
    ∃ L : ℝ, HasSum (fun n : ℕ => ((q : ℝ) ^ (-σ)) ^ n * normSq (B.map fun b : ℂˣ => (b : ℂ) ^ n).sum / n) L ∧
      locL q B (B.map star) σ = Real.exp L := by
  set x : ℝ := (q : ℝ) ^ (-σ) with hxdef
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set S := (B ×ˢ B.map star).map fun p : ℂˣ × ℂˣ => (p.1 : ℂ) * p.2 * x with hSdef
  have hS : ∀ w ∈ S, ‖w‖ < 1 := by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hw
    have := norm_pair_le hM hp
    rw [norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hx0]
    nlinarith [mul_le_mul_of_nonneg_right this hx0]
  have hloc : locL q B (B.map star) σ = (S.map fun w => (1 - w)⁻¹).prod := by
    simp only [locL, cpow_neg_eq, ← hxdef, hSdef, Multiset.map_map, Function.comp_def]
  have hterm : ∀ n : ℕ, (S.map fun w => w ^ n).sum / n =
      ((x ^ n * normSq (B.map fun b : ℂˣ => (b : ℂ) ^ n).sum / n : ℝ) : ℂ) := by
    intro n
    simp only [hSdef, Multiset.map_map, Function.comp_def]
    rw [sum_pow_product, sum_pow_star, mul_assoc, mul_conj]
    push_cast
    ring
  have hL := hasSum_log S hS
  simp only [hterm] at hL
  have hre := Complex.hasSum_re hL
  have him := Complex.hasSum_im hL
  simp only [ofReal_re, ofReal_im] at hre him
  have hLim := him.unique hasSum_zero
  refine ⟨_, hre, ?_⟩
  rw [hloc, prod_inv_one_sub_eq_exp S hS, ofReal_exp]
  congr 1
  exact Complex.ext (by rw [ofReal_re]) (by rw [ofReal_im, hLim])

end GlobalTheory.JSW.LogPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonicSimpleRootGeneratorResidue
section
open IsLocalRing GlobalTheory.Toroidal Polynomial

namespace GlobalTheory

theorem exists_monic_simple_root_generator_residue : ∀ (O R' Ω : Type) [CommRing O] [IsLocalRing O] [CommRing R']
    [IsLocalRing R'] [Field Ω] (φ' : O →+* R') (u' : R' →+* Ω), IsEtaleCompletion φ' →
    ((residue R').comp φ').FormallyUnramified → RingHom.ker u' = maximalIdeal R' →
    ∃ (G : Polynomial O) (β : Ω), G.Monic ∧ (G.map (u'.comp φ')).eval β = 0 ∧
      (G.map (u'.comp φ')).derivative.eval β ≠ 0 ∧
      ∀ r : R', ∃ q : Polynomial O, u' r = (q.map (u'.comp φ')).eval β := by
  intro O R' Ω _ _ _ _ _ φ u hφ hur hker
  obtain ⟨-, hmax, hfin⟩ := hφ
  haveI : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : φ a ∈ maximalIdeal R' := hmax ▸ Ideal.mem_map_of_mem φ ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 h1 ha
  have hcomp : (ResidueField.map φ).comp (residue O) = (residue R').comp φ :=
    ResidueField.map_comp_residue φ
  have hfin' : (ResidueField.map φ).Finite := by
    rw [← hcomp] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  have hur' : (ResidueField.map φ).FormallyUnramified := by
    rw [← hcomp] at hur
    exact RingHom.FormallyUnramified.of_comp hur
  letI := (ResidueField.map φ).toAlgebra
  haveI : FiniteDimensional (ResidueField O) (ResidueField R') := hfin'
  haveI : Algebra.FormallyUnramified (ResidueField O) (ResidueField R') := hur'
  haveI : Algebra.IsSeparable (ResidueField O) (ResidueField R') :=
    Algebra.FormallyUnramified.isSeparable _ _
  let ι : ResidueField R' →+* Ω := Ideal.Quotient.lift (maximalIdeal R') u
    (fun a ha => by rwa [← RingHom.mem_ker, hker])
  have hι : ∀ r, ι (residue R' r) = u r := fun r => Ideal.Quotient.lift_mk _ _ _
  have hres : ∀ (P : O[X]) (x : ResidueField R'),
      (P.map (u.comp φ)).eval (ι x) = ι (aeval x (P.map (residue O))) := by
    intro P x
    rw [aeval_def, hom_eval₂, eval₂_map, eval_map]
    congr 1
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField O) (ResidueField R')
  have hint : IsIntegral (ResidueField O) α := Algebra.IsIntegral.isIntegral α
  have hpm : (minpoly (ResidueField O) α).Monic := minpoly.monic hint
  have hlift : minpoly (ResidueField O) α ∈ lifts (residue O) :=
    (lifts_iff_coeff_lifts _).2 fun n => residue_surjective _
  obtain ⟨G, hGmap, -, hGm⟩ := lifts_and_degree_eq_and_monic hlift hpm
  refine ⟨G, ι α, hGm, ?_, ?_, ?_⟩
  · rw [hres, hGmap, minpoly.aeval, map_zero]
  · rw [derivative_map, hres, ← derivative_map, hGmap]
    refine (map_ne_zero ι).2 ?_
    exact (Algebra.IsSeparable.isSeparable (ResidueField O) α).aeval_derivative_ne_zero (minpoly.aeval _ _)
  · intro r
    have hr : residue R' r ∈ Algebra.adjoin (ResidueField O) {α} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
        IntermediateField.mem_toSubalgebra, hα]
      exact IntermediateField.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hr
    obtain ⟨pb, hpb⟩ := hr
    obtain ⟨P, hP⟩ := map_surjective (residue O) residue_surjective pb
    refine ⟨P, ?_⟩
    rw [hres, hP, ← hι]
    exact congrArg ι hpb.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormSolutionAdelicFromArchimedean
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

noncomputable section
namespace GlobalTheory
open Classical

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

theorem ainf_single_mul (a b : w.Completion) :
    (show Ainf F from Pi.single w (a * b)) = (show Ainf F from Pi.single w a) * (show Ainf F from Pi.single w b) := by
  funext u
  change (Pi.single w (a*b) : ∀ v : InfinitePlace F, v.Completion) u =
    (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u * (Pi.single w b : ∀ v : InfinitePlace F, v.Completion) u
  by_cases h : u = w
  · subst h; simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne h, mul_zero]

theorem ainf_idem_mul (e : Ainf F) (h1 : e w = 1) (h0 : ∀ u, u ≠ w → e u = 0) (a : w.Completion) :
    e * (show Ainf F from Pi.single w a) = (show Ainf F from Pi.single w a) := by
  funext u
  change (e : ∀ v : InfinitePlace F, v.Completion) u * (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u = (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u
  by_cases h : u = w
  · subst h; rw [h1, one_mul]
  · simp only [Pi.single_eq_of_ne h, mul_zero]

theorem ainf_single_one (e : Ainf F) (h1 : e w = 1) (h0 : ∀ u, u ≠ w → e u = 0) :
    (show Ainf F from Pi.single w 1) = e := by
  funext u
  change (Pi.single w 1 : ∀ v : InfinitePlace F, v.Completion) u = e u
  by_cases h : u = w
  · subst h; rw [h1, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, h0 u h]

theorem af_zero (y : Af F) (h : ∀ v, evalV F v y = 0) : y = 0 := by
  ext v
  exact congrArg _ (h v)

theorem af_ext {p q : AF F} (h1 : fstA F p = fstA F q) (h2 : sndA F p = sndA F q) : p = q :=
  Prod.ext h1 h2

def placeAtInf : w.Completion →ₗ[F] AF F :=
  (LinearMap.inl F (Ainf F) (Af F)).comp (LinearMap.single F (fun u : InfinitePlace F => u.Completion) w)

theorem fstA_placeAtInf (a : w.Completion) : fstA F (placeAtInf F w a) = (show Ainf F from Pi.single w a) := rfl
theorem sndA_placeAtInf (a : w.Completion) : sndA F (placeAtInf F w a) = 0 := rfl

theorem placeAtInf_mul (a b : w.Completion) :
    placeAtInf F w (a * b) = placeAtInf F w a * placeAtInf F w b := by
  apply af_ext
  · have e2 : fstA F (placeAtInf F w a * placeAtInf F w b) =
        fstA F (placeAtInf F w a) * fstA F (placeAtInf F w b) := map_mul (fstA F) _ _
    exact (fstA_placeAtInf F w (a * b)).trans ((ainf_single_mul F w a b).trans
      (e2.trans (congrArg₂ (· * ·) (fstA_placeAtInf F w a) (fstA_placeAtInf F w b))).symm)
  · have e2 : sndA F (placeAtInf F w a * placeAtInf F w b) =
        sndA F (placeAtInf F w a) * sndA F (placeAtInf F w b) := map_mul (sndA F) _ _
    exact (sndA_placeAtInf F w (a * b)).trans ((mul_zero (0 : Af F)).symm.trans
      (e2.trans (congrArg₂ (· * ·) (sndA_placeAtInf F w a) (sndA_placeAtInf F w b))).symm)

variable {F w}

theorem idem_mul_placeAtInf {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (a : w.Completion) :
    ε * placeAtInf F w a = placeAtInf F w a := by
  apply af_ext
  · have e2 : fstA F (ε * placeAtInf F w a) = fstA F ε * fstA F (placeAtInf F w a) := map_mul (fstA F) _ _
    exact e2.trans ((congrArg (fstA F ε * ·) (fstA_placeAtInf F w a)).trans
      ((ainf_idem_mul F w _ (hε.1 w (Finset.mem_singleton_self w))
        (fun u hu => hε.2.1 u (by simpa using hu)) a).trans (fstA_placeAtInf F w a).symm))
  · have e2 : sndA F (ε * placeAtInf F w a) = sndA F ε * sndA F (placeAtInf F w a) := map_mul (sndA F) _ _
    exact e2.trans ((congrArg (sndA F ε * ·) (sndA_placeAtInf F w a)).trans
      ((mul_zero _).trans (sndA_placeAtInf F w a).symm))

theorem placeAtInf_one {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) : placeAtInf F w 1 = ε := by
  apply af_ext
  · refine (fstA_placeAtInf F w 1).trans ?_
    exact ainf_single_one F w _ (hε.1 w (Finset.mem_singleton_self w))
      (fun u hu => hε.2.1 u (by simpa using hu))
  · refine (sndA_placeAtInf F w 1).trans ?_
    exact (af_zero F _ (fun v => hε.2.2.2 v (Finset.notMem_empty v))).symm

variable (F w) (E : Type) [Field E] [Algebra F E]

def placeAtInfE : w.Completion ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  LinearMap.rTensor E (placeAtInf F w)

theorem placeAtInfE_tmul (a : w.Completion) (e : E) :
    placeAtInfE F w E (a ⊗ₜ e) = placeAtInf F w a ⊗ₜ e := rfl

theorem placeAtInfE_mul (x y : w.Completion ⊗[F] E) :
    placeAtInfE F w E (x * y) = placeAtInfE F w E x * placeAtInfE F w E y := by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | add a b ha hb => rw [add_mul, map_add (f := _), map_add (f := _), ha, hb, add_mul]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add c d hc hd => rw [mul_add, map_add (f := _), map_add (f := _), hc, hd, mul_add]
    | tmul b f =>
      unfold placeAtInfE
      rw [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
        LinearMap.rTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul, placeAtInf_mul]

theorem placeAtInfE_sig (σ : E →ₐ[F] E) (x : w.Completion ⊗[F] E) :
    placeAtInfE F w E (sigR w.Completion σ x) = sigR (AF F) σ (placeAtInfE F w E x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]
  | tmul a e =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, placeAtInfE_tmul]

variable {F w E}

theorem idem_mul_placeAtInfE {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (x : w.Completion ⊗[F] E) :
    algebraMap (AF F) (AF F ⊗[F] E) ε * placeAtInfE F w E x = placeAtInfE F w E x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [mul_add, map_add (f := _), h₁, h₂]
  | tmul a e =>
    rw [placeAtInfE_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, Algebra.algebraMap_self, RingHom.id_apply, idem_mul_placeAtInf hε]

theorem placeAtInfE_incl {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (c : E) :
    placeAtInfE F w E (inclR w.Completion c) = algebraMap (AF F) (AF F ⊗[F] E) ε * inclR (AF F) c := by
  simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    placeAtInfE_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_one, Algebra.algebraMap_self, RingHom.id_apply, placeAtInf_one hε]

theorem normEq_inf_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (w : InfinitePlace F) (ε : AF F), IsPlacesIdem {w} ∅ ε → ∀ c : E,
    (∃ t : w.Completion ⊗[F] E, t * sigR w.Completion σ t + inclR w.Completion c = 0) →
    ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  intro F E _ _ _ _ σ w ε hε c ⟨t, ht⟩
  refine ⟨placeAtInfE F w E t, ?_⟩
  rw [← placeAtInfE_sig, ← placeAtInfE_mul, mul_add, idem_mul_placeAtInfE hε, ← placeAtInfE_incl hε,
    ← map_add, ht, map_zero]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsTranslationFamilyChartsThickenings
section
open CategoryTheory TopologicalSpace TensorProduct
open GlobalTheory.AnPer

namespace GlobalTheory.AnPer


set_option maxHeartbeats 1000000 in
theorem exists_points_on_DObj : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →ₐ[ℂ] R) (M : Ideal R) (θ : Hol F.V →+* R) (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k)) (ρ : ∀ k, Hol (K.W (ka k)) →+* R ⊗[ℂ] Hol (K₀.W k)), (∀ k f, ρ k (K.cst (ka k) f) = θ f ⊗ₜ[ℂ] 1) →
    (∀ k a h, ρ k (dw (W := K.W (ka k)) a h) =
      LinearMap.lTensor R (dw (W := K₀.W k) a).toLinearMap (ρ k h)) →
    (∀ l k' k (h : K₀.le l k' k), Close (M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k'))) ((ρ k').comp (Charts.sh (hka h))) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h)).toRingHom.comp (ρ k))) → ∀ (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k)), (∀ k h, ρ k h - 1 ⊗ₜ[ℂ] res k h ∈ M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k))) → ∃ ρ' : ∀ S : K₀.DObj (et : Hol F₀.V →+* R) M, Hol (K.W (ka S.T.k)) →+* S.T.C, (∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f)) ∧ (∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J) ∧ ∀ (S S' : K₀.DObj (et : Hol F₀.V →+* R) M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1)))) ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S)) := by
  intro I _ g Λ _ F F₀ K K₀ R _ _ et M θ ka hka ρ hc hd hs res hr
  choose ψ hψ using _root_.GlobalTheory.AnPer.exists_tensorLift_of_DObj K₀ et M
  have h1 : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M) (d : R), ψ S (d ⊗ₜ[ℂ] 1) = algebraMap R S.T.C d :=
    fun S d ↦ (hψ S d 1).trans (by rw [S.T.ρ.map_one, mul_one])
  have h2 : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M) (h : Hol (K₀.W S.T.k)), ψ S (1 ⊗ₜ[ℂ] h) = S.T.ρ h :=
    fun S h ↦ (hψ S 1 h).trans (by rw [(algebraMap R S.T.C).map_one, one_mul])
  have hJ : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M),
      ∀ c ∈ M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)), ψ S c ∈ S.T.J := by
    intro S c hc
    have : M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)) ≤ S.T.J.comap (ψ S) := by
      refine Ideal.map_le_iff_le_comap.2 fun d hd ↦ ?_
      change ψ S (d ⊗ₜ[ℂ] 1) ∈ S.T.J
      rw [h1]
      exact S.mem d hd
    exact this hc
  refine ⟨fun S ↦ (ψ S).comp (ρ S.T.k), fun S f ↦ ?_, fun S h ↦ ?_, fun S S' f ↦ ?_⟩
  · exact (congrArg (ψ S) (hc _ f)).trans (h1 S _)
  · have := hJ S _ (hr S.T.k h)
    rw [(ψ S).map_sub, h2] at this
    exact this
  · have c1 := (hs _ _ _ (Charts.Hom.le f.1)).map (ψ S') (hJ S')
    have c2 := GlobalTheory.CloseTen.close_tensor
      (W := K.W (ka S.T.k)) (W₀ := K₀.W S.T.k) S'.T.J (ρ S.T.k) (hd S.T.k)
      ((ψ S').comp (Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA (Charts.Hom.le f.1))).toRingHom)
      ((f.1.φ : S.T.C →+* S'.T.C).comp (ψ S))
      (fun d ↦ by
        have e : Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA (Charts.Hom.le f.1)) (d ⊗ₜ[ℂ] 1) = d ⊗ₜ[ℂ] 1 :=
          (Algebra.TensorProduct.map_tmul _ _ _ _).trans
            (congrArg (fun x ↦ d ⊗ₜ[ℂ] x) (Charts.shA (Charts.Hom.le f.1)).map_one)
        exact (congrArg (ψ S') e).trans ((h1 S' d).trans ((f.2 d).symm.trans (congrArg f.1.φ (h1 S d).symm))))
      (by
        have e1 : ((ψ S').comp (Algebra.TensorProduct.map (AlgHom.id ℂ R)
            (Charts.shA (Charts.Hom.le f.1))).toRingHom).comp
            (Algebra.TensorProduct.includeRight : Hol (K₀.W S.T.k) →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)).toRingHom =
            S'.T.ρ.comp (Charts.sh (Charts.Hom.le f.1)) :=
          RingHom.ext fun h ↦ (congrArg (ψ S') (Algebra.TensorProduct.map_tmul (AlgHom.id ℂ R)
            (Charts.shA (Charts.Hom.le f.1)) 1 h)).trans (h2 S' _)
        have e2 : ((f.1.φ : S.T.C →+* S'.T.C).comp (ψ S)).comp
            (Algebra.TensorProduct.includeRight : Hol (K₀.W S.T.k) →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)).toRingHom =
            (f.1.φ : S.T.C →+* S'.T.C).comp S.T.ρ :=
          RingHom.ext fun h ↦ congrArg f.1.φ (h2 S h)
        rw [e1, e2]
        exact f.1.close)
    exact Relation.ReflTransGen.trans c1 c2

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFinGLLeInvAbsDet
section
open NumberField IsDedekindDomain GlobalTheory.HenQ
open GlobalTheory.CuspRep (GA Af finGL)

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.HenQ

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem finGL_apply (k : GL (Fin n) (Af K)) (a b : Fin n) :
    ((finGL K n k : GA K n) : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) a b =
      (1 : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) a b
        - GlobalTheory.CuspRep.sFin K ((1 : Matrix (Fin n) (Fin n) (Af K)) a b)
        + GlobalTheory.CuspRep.sFin K ((k : Matrix (Fin n) (Fin n) (Af K)) a b) := rfl

theorem sFin_fst (x : Af K) : (GlobalTheory.CuspRep.sFin K x).1 = 0 := rfl

end GlobalTheory.HenQ

namespace GlobalTheory.HenQ

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

end GlobalTheory.HenQ
end
end

