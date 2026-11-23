module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRootStalk
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorSumFockHeisenbergISmulSignConjVacuumStatement
section
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piTensorSumFockHeisenberg_I_smul_signConj_vacuum : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (c : ι → Matrix (Ix P Q) (Ix R S) ℂ),
    sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (Complex.I • (Jm P Q * c w * Jm R S)))
      (PiTensorProduct.tprod ℂ fun _ => 1) =
    Complex.I • sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (c w)) (PiTensorProduct.tprod ℂ fun _ => 1) := by
  first | exact @GlobalTheory.FockVac.sumPl_heisOp_vacuum | exact GlobalTheory.FockVac.sumPl_heisOp_vacuum | (intros; apply GlobalTheory.FockVac.sumPl_heisOp_vacuum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.ConjAtPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tendsto_pow_of_lt_one {w : HeightOneSpectrum (𝓞 E)} (x : w.adicCompletion E) (h : Valued.v x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (nhds 0) := by
  rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 _ hne)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_of_continuous {w : HeightOneSpectrum (𝓞 E)} (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : Continuous s) {z : w.adicCompletion E} (hz : Valued.v z < 1) : Valued.v (s z) < 1 := by
  have h1 : Tendsto (fun n : ℕ => s z ^ n) atTop (nhds 0) := by
    have := (hs.tendsto 0).comp (tendsto_pow_of_lt_one z hz)
    simpa [Function.comp_def, map_pow] using this
  have hU : {y : w.adicCompletion E | Valued.v y < 1} ∈ nhds (0 : w.adicCompletion E) :=
    Valued.mem_nhds_zero.2 ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨N, hN⟩ := (h1.eventually hU).exists
  by_contra hc
  rw [not_lt] at hc
  rw [map_pow] at hN
  exact absurd hN (not_lt.2 (one_le_pow₀ hc))

theorem conjSrc_eq_of_cont (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : Continuous s)
    (he : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) :
    conjSrc (GlobalTheory.SplitPts.conjE E) w = w := by
  have hval : ∀ a : 𝓞 E, Valued.v (algebraMap E (w.adicCompletion E) (a : E)) =
      w.valuation E (algebraMap (𝓞 E) E a) := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have hmem : ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ Valued.v (algebraMap E (w.adicCompletion E) (a : E)) < 1 := by
    intro a
    rw [hval, HeightOneSpectrum.valuation_lt_one_iff_mem]
  have hdir : ∀ x y : 𝓞 E, (y : E) = IsCMField.complexConj E (x : E) → x ∈ w.asIdeal → y ∈ w.asIdeal := by
    intro x y hxy hx
    rw [hmem] at hx ⊢
    rw [hxy, ← he]
    exact lt_one_of_continuous s hs hx
  have hc : GlobalTheory.Mem.Chr.ConjPl (GlobalTheory.SplitPts.conjE E) w w := by
    rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    refine ⟨hdir x y hxy, hdir y x ?_⟩
    rw [show (GlobalTheory.SplitPts.conjE E) (x : E) = IsCMField.complexConj E (x : E) from rfl] at hxy
    rw [hxy, IsCMField.complexConj_apply_apply]
  exact (eq_conjSrc hc).symm

theorem conjSrc_eq_iff (w : HeightOneSpectrum (𝓞 E)) :
    conjSrc (GlobalTheory.SplitPts.conjE E) w = w ↔ ¬ IsSplitAt w := by
  refine ⟨fun h hs => (GlobalTheory.SplitPts.over_split hs).1 h, fun h => ?_⟩
  by_contra hne
  apply h
  exact ⟨conjSrc (GlobalTheory.SplitPts.conjE E) w, hne,
    (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2
      (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc w))⟩

theorem ext_of_cont {v w : HeightOneSpectrum (𝓞 E)} (s t : v.adicCompletion E →+* w.adicCompletion E)
    (hs : Continuous s) (ht : Continuous t)
    (hse : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hte : ∀ x : E, t (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) : s = t :=
  RingHom.ext fun y => congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hs ht
    (funext fun k => (hse k).trans (hte k).symm)) y

theorem cont_of_val {w : HeightOneSpectrum (𝓞 E)} (s : w.adicCompletion E →+* w.adicCompletion E)
    (hv : ∀ x, Valued.v (s x) = Valued.v x) : Continuous s :=
  GlobalTheory.Mem.Chr.continuous_of_valued_eq (HeightOneSpectrum.valuedAdicCompletion_surjective E w) s hv

theorem cj_spec (w : Pl E)
    (h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) :
    Continuous (cj w) ∧ ∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
  unfold cj
  rw [dite_eq_left h]
  exact h.choose_spec

theorem cj_of_not (w : Pl E)
    (h : ¬ ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) :
    cj w = RingHom.id _ := by
  unfold cj
  rw [dite_eq_right h]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, Continuous (cj w) ∧ (∀ x, cj w (cj w x) = x) ∧ (∀ x, Valued.v (cj w x) = Valued.v x) ∧ (¬ IsSplitAt w → (∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ (∃ ϖ q, IsUnramInv ϖ (cj w) q ∧ qV E w = q ^ 2) ∧ (∀ x : Af E, pLoc E w (conjFin (IsCMField.complexConj E).toRingEquiv x) = cj w (pLoc E w x)) ∧ ∀ (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x, Valued.v (s x) = Valued.v x) → (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → s = cj w) ∧ ∀ (s : w.adicCompletion E →+* w.adicCompletion E), (∀ x, Valued.v (s x) = Valued.v x) → (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → ¬ IsSplitAt w := by
  intro E _ _ _ hU w
  by_cases hsp : IsSplitAt w
  · have hno : ¬ ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
      rintro ⟨s, hs, he⟩
      exact (GlobalTheory.SplitPts.over_split hsp).1 (conjSrc_eq_of_cont w s hs he)
    have hid := cj_of_not w hno
    refine ⟨by rw [hid]; exact continuous_id, fun x => by rw [hid]; rfl, fun x => by rw [hid]; rfl,
      fun h => absurd hsp h, fun s hv he _ => hno ⟨s, cont_of_val s hv, he⟩⟩
  · obtain ⟨s0, ϖ, q, he0, hU0⟩ := GlobalTheory.InertPlaceConj.exists_conj_isUnramInv E w (hU w) hsp
    have hc0 : Continuous s0 := cont_of_val s0 hU0.2.1
    obtain ⟨hcj, hecj⟩ := cj_spec w ⟨s0, hc0, he0⟩
    have heq : cj w = s0 := ext_of_cont _ _ hcj hc0 hecj he0
    have hsrc : conjSrc (GlobalTheory.SplitPts.conjE E) w = w := (conjSrc_eq_iff w).2 hsp
    refine ⟨hcj, fun x => by rw [heq]; exact hU0.1 x, fun x => by rw [heq]; exact hU0.2.1 x,
      fun _ => ⟨hecj, ⟨ϖ, q, by rw [heq]; exact hU0, ?_⟩, fun x => ?_,
        fun s hv he => ext_of_cont _ _ (cont_of_val s hv) hcj he hecj⟩, fun _ _ _ => hsp⟩
    · exact (Formalism.UG.P.tjcosets_card_residue w).symm.trans hU0.2.2.2.2.2.2
    · rw [pLoc_conjFin]
      have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E),
          Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
          f (pLoc E v x) = cj w (pLoc E w x) := by
        rintro v rfl f hf hfe
        rw [ext_of_cont f (cj v) hf hcj hfe hecj]
      exact key _ hsrc _ (conjLoc_spec _ w).1 (conjLoc_spec _ w).2.1

end GlobalTheory.ConjAtPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSolvabilityTransferAlgClosedFieldsStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_solvability_transfer_algClosed_fields : ∀ (F σ τ : Type) [Field F] [Finite σ] [Finite τ] (P : Ideal (MvPolynomial σ F)) (J : Ideal (MvPolynomial (σ ⊕ τ) F)), (∀ u : σ → AlgebraicClosure F, (∀ g ∈ P, aeval u g = 0) → ∃ y : τ → AlgebraicClosure F, ∀ g ∈ J, aeval (Sum.elim u y) g = 0) → ∀ (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (u : σ → Ω), (∀ g ∈ P, aeval u g = 0) → ∃ y : τ → Ω, ∀ g ∈ J, aeval (Sum.elim u y) g = 0 := by
  first | exact @GlobalTheory.PointTransfer.solvable_transfer | exact GlobalTheory.PointTransfer.solvable_transfer | (intros; apply GlobalTheory.PointTransfer.solvable_transfer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowDvdOfSpecialisations
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.HSShortDiv

variable {F : Type} [Field F] {D N : ℕ}

noncomputable def lastSubst (l₀ : Fin N → F) : Fin (D + 1) × Fin N → MvPolynomial (Fin (D + 1) × Fin N) F :=
  fun p => if p.1 = Fin.last D then C (l₀ p.2) else X p

theorem eval_aeval_lastSubst (l₀ : Fin N → F) (x : Fin (D + 1) × Fin N → F)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    eval x (aeval (lastSubst l₀) f) = eval (fun p => if p.1 = Fin.last D then l₀ p.2 else x p) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p q hp =>
    simp only [map_mul, hp, aeval_X, eval_X, lastSubst]
    split_ifs <;> simp

theorem replace_eq_join (l : Fin N → F) (x : Fin (D + 1) × Fin N → F) :
    (fun p : Fin (D + 1) × Fin N => if p.1 = Fin.last D then l p.2 else x p) =
      join (fun i j => x (i.castSucc, j)) l := by
  funext ⟨i, j⟩
  induction i using Fin.lastCases with
  | last => simp [join]
  | cast i => simp [join, Fin.castSucc_ne_last]

theorem eval_last_zero {δ : ℕ} (hδ : 1 ≤ δ) (f : MvPolynomial (Fin (D + 1) × Fin N) F)
    (hf : IsMultiHomogeneous (fun _ => δ) f) (x : Fin (D + 1) × Fin N → F) :
    eval (fun p => if p.1 = Fin.last D then 0 else x p) f = 0 := by
  rw [eval_eq']
  refine Finset.sum_eq_zero fun d hd => ?_
  have hs := hf d hd (Fin.last D)
  have hne : (∑ j : Fin N, d (Fin.last D, j)) ≠ 0 := by simp only at hs; omega
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := (Fin.last D, j)) (Finset.mem_univ _) ?_)
  simp [zero_pow hj]

theorem pow_dvd_of_specialisations (F : Type) [Field F] [CharZero F] (D N δ b : ℕ) (f G : MvPolynomial (Fin (D + 1) × Fin N) F)
    (Q : MvPolynomial (Fin D × Fin N) F) (hδ : 1 ≤ δ) (hf : IsMultiHomogeneous (fun _ => δ) f)
    (hirr : Irreducible f) (hQ : Q ≠ 0)
    (hG : ∀ s : Fin D → Fin N → F, eval (fun p => s p.1 p.2) Q ≠ 0 → ∃ (E : Type) (_ : Field E)
      (_ : Algebra F E) (γ : E), ∀ l : Fin N → F,
        algebraMap F E (eval (join s l) G) = γ * algebraMap F E (eval (join s l) f) ^ b) :
    f ^ b ∣ G := by
  haveI : Infinite F := Infinite.of_injective Nat.cast Nat.cast_injective
  have hf0 : f ≠ 0 := hirr.ne_zero

  obtain ⟨x₀, hx₀⟩ : ∃ x₀, eval x₀ f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (MvPolynomial.funext fun x => by simp [h x])
  set l₀ : Fin N → F := fun j => x₀ (Fin.last D, j) with hl₀
  set g := aeval (lastSubst l₀) f with hg
  set G₀ := aeval (lastSubst l₀) G with hG₀
  set Q' : MvPolynomial (Fin (D + 1) × Fin N) F :=
    rename (fun p : Fin D × Fin N => (p.1.castSucc, p.2)) Q with hQ'
  have hQ'0 : Q' ≠ 0 := by
    intro h
    apply hQ
    apply rename_injective _ _ (h.trans (map_zero _).symm)
    intro p q hpq
    simp only [Prod.mk.injEq, Fin.castSucc_inj] at hpq
    exact Prod.ext hpq.1 hpq.2

  have key : Q' * (G * g ^ b - f ^ b * G₀) = 0 := by
    apply MvPolynomial.funext
    intro x
    set s : Fin D → Fin N → F := fun i j => x (i.castSucc, j) with hs
    have hx : x = join s (fun j => x (Fin.last D, j)) := by
      rw [← replace_eq_join]
      funext p
      split_ifs with h
      · rw [← h]
      · rfl
    have hQx : eval x Q' = eval (fun p => s p.1 p.2) Q := by
      rw [hQ', eval_rename]; rfl
    simp only [map_mul, map_sub, map_pow, map_zero]
    by_cases hq : eval (fun p => s p.1 p.2) Q = 0
    · rw [hQx, hq, zero_mul]
    · obtain ⟨E, _, _, γ, hγ⟩ := hG s hq
      have h1 := hγ (fun j => x (Fin.last D, j))
      have h2 := hγ l₀
      rw [← hx] at h1
      have hgx : eval x g = eval (join s l₀) f := by rw [hg, eval_aeval_lastSubst, replace_eq_join]
      have hGx : eval x G₀ = eval (join s l₀) G := by rw [hG₀, eval_aeval_lastSubst, replace_eq_join]
      rw [hgx, hGx]
      have : eval x G * eval (join s l₀) f ^ b - eval x f ^ b * eval (join s l₀) G = 0 := by
        apply (algebraMap F E).injective
        simp only [map_sub, map_mul, map_pow, map_zero, h1, h2]
        ring
      rw [this, mul_zero]
  have heq : G * g ^ b = f ^ b * G₀ := by
    have := (mul_eq_zero.mp key).resolve_left hQ'0
    exact sub_eq_zero.mp this
  have hp : Prime f := hirr.prime

  have hndvd : ¬ f ∣ g := by
    rintro ⟨h, hh⟩
    have hg0 : g ≠ 0 := by
      intro h0
      have := congrArg (eval x₀) h0
      rw [hg, eval_aeval_lastSubst, map_zero] at this
      apply hx₀
      have hpt : (fun p : Fin (D + 1) × Fin N => if p.1 = Fin.last D then l₀ p.2 else x₀ p) = x₀ := by
        funext p
        split_ifs with hp1
        · rw [hl₀]; simp only; rw [← hp1]
        · rfl
      rw [hpt] at this
      exact this
    apply hg0
    apply MvPolynomial.funext
    intro x
    have e1 : eval x g = eval (fun p => if p.1 = Fin.last D then 0 else x p) g := by
      rw [hg, eval_aeval_lastSubst, eval_aeval_lastSubst]
      have hpt : (fun p : Fin (D + 1) × Fin N => if p.1 = Fin.last D then l₀ p.2 else x p) =
          (fun p => if p.1 = Fin.last D then l₀ p.2 else if p.1 = Fin.last D then 0 else x p) := by
        funext p
        split_ifs <;> rfl
      rw [hpt]
    rw [e1, hh, map_mul, eval_last_zero hδ f hf, zero_mul, map_zero]
  have hndvd' : ¬ f ∣ g ^ b := fun h => hndvd (hp.dvd_of_dvd_pow h)
  exact hp.pow_dvd_of_dvd_mul_right b hndvd' ⟨G₀, heq⟩

end GlobalTheory.HSShortDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFrameOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaDvr.Scale

open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.ZH.TestVal

theorem odd_level' {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    Odd (S.r * S.N) := by
  obtain ⟨j, -, hj⟩ := ρ.r_eq
  rw [hj, ρ.N_eq]
  exact ρ.n_odd.pow.mul ρ.n_odd.pow.pow

theorem powFrame_one' {B : Scheme.{0}} {A T : Over B} {L : LB A.left} (x : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) :
    powFrame A L x τ 1 = τ :=
  congrArg LB.Gen.mk (funext fun j => zpow_one (τ.s j))


attribute [local instance] gtGroup in
theorem exists_scale : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (yK : S.R →+* FractionRing V) (A : PolAV (Sp (FractionRing V))) (φ : A.A.left ⟶ ρ.P.A.left), IsGrpPullback A.A ρ.P.A (spMap yK) φ → LBIso A.L (ρ.P.L.pull φ) → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), IsSemiAbelian G → (∀ a : o, yK (algebraMap o S.R a) ∈ (algebraMap V (FractionRing V)).range) → ∀ yy : S.Gam →+ D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : D.toPre.X →+ D.toPre.X).range, Function.Surjective yy → (∀ (a : S.Gam) (pk : QkPt D.toPre (AlgebraicClosure (FractionRing V)) (S.r * S.N)) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A), QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) (S.r * S.N) pk x → x.left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) → ∀ (ϖ : V), Irreducible ϖ → ∀ (v : AddValuation (AlgebraicClosure (FractionRing V)) (WithTop ℚ)), ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ (AlgebraicClosure (FractionRing V)) v → ∃ s : WithTop ℚ, (∀ b : S.Gam, s ≤ v (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (yK ⟨S.th b, S.th_mem b⟩)) ∧ (yy b ≠ 0 → yK ⟨S.th b, S.th_mem b⟩ ≠ 0 → s < v (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (yK ⟨S.th b, S.th_mem b⟩)))) ∧ ∀ n : ℕ, 2 ≤ n → n ∣ S.r * S.N → ∀ a : S.Gam, yy a = 0 → ∃ a' : S.Gam, yy a' = 0 ∧ n • (a' - a) = 0 ∧ v (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (yK ⟨S.th a', S.th_mem a'⟩)) = s := by
  intro hL hL₂ o Ω _ _ _ _ S ρ V _ _ _ _ hc yK A φ cart lb G _ _ D U semi hy yy _hyy_onto hyy ϖ hϖ v hv
  obtain ⟨H, h₁, h₂, h₃, h₄⟩ := hyps hL hL₂
  have hm := odd_level' ρ
  have hA : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hB := D.tau_bimult
  choose Q hQ using QForm.exists_QVal hϖ D
  have hu : IsUnit ((S.r * S.N : ℕ) : V) := by
    obtain ⟨b, hb⟩ := S.unit.exists_right_inv
    obtain ⟨c, hc'⟩ := hy b
    refine IsUnit.of_mul_eq_one c (IsFractionRing.injective V (FractionRing V) ?_)
    have := congrArg (fun a => yK (algebraMap o S.R a)) hb
    simp only [map_mul, map_natCast, map_one] at this ⊢
    rw [hc']; simpa using this
  obtain ⟨x, hx, xadd, xinj, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points yK cart
  obtain ⟨rig, e, hrig, he, hsec⟩ := GlobalTheory.ThetaDvr.frames yK cart lb x hx
  obtain ⟨t, ht⟩ := hsec 1 ρ.th₁
  obtain ⟨w₀, hw₀⟩ := EvalZero.exists_normW U.toUnifPre rig hrig
  obtain ⟨th, ϑ, hE, hP, hgen⟩ := exists_prim_generator H h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ _ v hv A G
    semi U w₀ hw₀.1
  have key := val_theta H h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ _ v hv A G semi U w₀ rig hw₀ th ϑ hE hP
    _ hm hu
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq H V _ hA D A G semi U
    (AlgebraicClosure (FractionRing V)) _ hm.pos
  obtain ⟨r, hr⟩ := hgen t
  obtain ⟨sc, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (FractionRing V)))).inv).2 r
  set F := AlgebraicClosure (FractionRing V) with hF
  set y₀ : S.R →+* F := (algebraMap (FractionRing V) F).comp yK with hy₀
  have tv : ∀ a z J, Good A.L z J → cst (R := V) F z sc *
      @id ((TF (R := V) F).left.presheaf.stalk z) (sA th (ptSecT A.A (x a)).left z J) =
      cst (R := V) F z (y₀ ⟨S.th a, S.th_mem a⟩) * @id ((TF (R := V) F).left.presheaf.stalk z)
        (val (powFrame A.A A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ =>
    (ThetaCompare.sval_smul hr (x a) hJ).symm.trans (ht a _ (by
      have b := ρ.th_val a
      rw [← powFrame_one' (ρ.pt a) (ρ.fr a)] at b
      exact b) z J hJ)
  have ex : ∀ a, ∃ q, QkToAkU U.toUnifPre F (S.r * S.N) q (x a) ∧ yy a = QuotientAddGroup.mk q.y :=
    fun a => by
      obtain ⟨q, hq⟩ := f₂ (x a) (he a).1
      exact ⟨q, (f₁ _ _).2 hq.symm, hyy a q _ ((f₁ _ _).2 hq.symm) (hx a)⟩
  by_cases h0 : sc = 0
  · have z0 : ∀ a, y₀ ⟨S.th a, S.th_mem a⟩ = 0 := fun a => by
      obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := F)
      obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := V) F).left) A.isLB z
      have := tv a z J hJ
      rw [h0, CoefBasic.cst_eq, CoefBasic.cst_eq, map_zero, zero_mul] at this
      exact CoefBasic.cstH_inj (R := V) z (((Units.mul_left_eq_zero _).1 this.symm).trans (map_zero _).symm)
    have z1 : ∀ a, algebraMap (FractionRing V) F (yK ⟨S.th a, S.th_mem a⟩) = 0 := fun a => z0 a
    refine ⟨⊤, fun b => ⟨by rw [z1 b, AddValuation.map_zero], fun _ hb => absurd ?_ hb⟩,
      fun n _ _ a ha => ⟨a, ha, by simp, by rw [z1 a, AddValuation.map_zero]⟩⟩
    exact (map_eq_zero_iff _ (algebraMap (FractionRing V) F).injective).1 (z1 b)
  have tv' : ∀ a z J, Good A.L z J → sA th (ptSecT A.A (x a)).left z J =
      @id ((TFK (R := V) F).left.presheaf.stalk z)
        (cst (R := V) F z (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩)) *
        (val (powFrame A.A A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => by
    have b := congrArg (CoefBasic.cstH (R := V) z sc⁻¹ * ·) (tv a z J hJ)
    simp only [CoefBasic.cst_eq, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, _root_.one_mul] at b
    rw [CoefBasic.cst_eq]
    exact b
  have hvs : v sc ≠ ⊤ := v.ne_top_iff.2 h0
  have split : ∀ a, v (y₀ ⟨S.th a, S.th_mem a⟩) = v sc + v (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩) := fun a => by
    rw [← v.map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ h0, _root_.one_mul]
  have nz : ∀ a, v (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩) = 0 ↔ v (y₀ ⟨S.th a, S.th_mem a⟩) = v sc := fun a => by
    rw [split a]
    constructor
    · intro h; rw [h, add_zero]
    · intro h
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hvs
      rw [← hs] at h
      have e1 := congrArg (((-s : ℚ) : WithTop ℚ) + ·) h
      simp only [← add_assoc, ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero, zero_add] at e1
      exact e1
  refine ⟨v sc, fun b => ?_, fun n hn hnm a ha => ?_⟩
  · obtain ⟨q, hq₁, hq₂⟩ := ex b
    have hk := (key q _ hq₁).1 _ _ (he b) (tv' b)
    have lo : (0 : WithTop ℚ) ≤ v (sc⁻¹ * y₀ ⟨S.th b, S.th_mem b⟩) := by
      have := hk.1 0 fun χ => by
        by_cases c : (S.r * S.N) • χ + q.y = 0
        · rw [c, QForm.Q_zero hϖ D hQ]; simp
        · exact div_nonneg (Int.cast_nonneg (zero_le_one.trans (QForm.Q_pos hϖ D hQ c))) (Nat.cast_nonneg _)
      simpa using this
    have le : v sc ≤ v (y₀ ⟨S.th b, S.th_mem b⟩) := by rw [split b]; exact le_add_of_nonneg_right lo
    refine ⟨le, fun hb _ => lt_of_le_of_ne le fun h => hb ?_⟩
    obtain ⟨z, hz⟩ := hk.2 ((nz b).2 h.symm)
    exact hq₂.trans ((QuotientAddGroup.eq_zero_iff _).2 ⟨z, hz.symm⟩)
  · obtain ⟨q, hq₁, hq₂⟩ := ex a
    obtain ⟨z, hz⟩ := (QuotientAddGroup.eq_zero_iff _).1 (hq₂.symm.trans ha)
    have hz' : (S.r * S.N) • z = q.y := hz
    let q₀ : QkPt D.toPre F (S.r * S.N) := qkMk hB 0 (q.g + iota hB _ (-z)) (by
      rw [smul_add, qk_nsmul hB, ← map_nsmul, ← map_add (f := _), smul_neg, hz', add_neg_cancel])
    have e₀ : f q = f q₀ := (f₃ _ _).2 ((equiv_iff hB _ _).2 ⟨-z, by
      rw [smul_neg, hz', add_neg_cancel]; rfl, rfl⟩)
    obtain ⟨q', x', hy', hx', hpow, hval⟩ :=
      (key q₀ (x a) ((f₁ _ _).2 (((f₁ _ _).1 hq₁).trans e₀))).2 n hn hnm (by simp only [q₀, qkMk_y])
    obtain ⟨a', rfl⟩ := xonto x' (hx' w₀ hw₀.1).1
    have := A.isAb.comm
    let X : Multiplicative S.Gam →* (TFK (R := V) F ⟶ A.A) :=
      MonoidHom.mk' (fun a => x a.toAdd) fun a b => xadd _ _
    refine ⟨a', (hyy a' q' _ hx' (hx a')).trans (by rw [hy']; rfl), xinj ?_,
      (nz a').1 (hval _ _ (he a') (tv' a'))⟩
    have b : X ((Multiplicative.ofAdd a' * (Multiplicative.ofAdd a)⁻¹) ^ n) = X 1 := by
      rw [map_pow, map_mul, map_inv, map_one]; exact hpow
    rw [sub_eq_add_neg]
    exact b

end GlobalTheory.ThetaDvr.Scale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMaxOnePowLeOnSiegelTorusConeStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_max_one_pow_le_on_siegelTorusCone : ∀ (r m e : ℕ) (c : ℝ), 0 < c → ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∏ k : Fin r ⊕ Fin r ⊕ Fin m, max 1 (Sum.elim t (Sum.elim (fun i => (t i)⁻¹) (fun _ => (1 : ℝ))) k) ^ e ≤ C * ∏ i, t i ^ e := by
  first | exact @GlobalTheory.ConeMax.prod_max_le_prod | exact GlobalTheory.ConeMax.prod_max_le_prod | (intros; apply GlobalTheory.ConeMax.prod_max_le_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSmoothAdelicFunctionsStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ ψ ∈ Sm E a, smoothing ν α ψ ∈ Sm E a := by
  first | exact @GlobalTheory.AutGrowth.smoothing_mem_Sm | exact GlobalTheory.AutGrowth.smoothing_mem_Sm | (intros; apply GlobalTheory.AutGrowth.smoothing_mem_Sm <;> assumption)
end

