module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFamOfNotMem
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.TrIdem

def normInd {G : Type} [MeasurableSpace G] (μ : Measure G) (H : Set G) : G → ℂ :=
  (μ.real H : ℂ)⁻¹ • H.indicator 1

variable {D : D7} {V : HSp D}

def kerSub (T : TypeDataG V) (v : T.S) : Subgroup (GLoc D.sp.cm.sig V.gram v) :=
  ((T.frame v).red.ker).map (Kv V v).subtype

def levelFam (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : ∀ v, Subgroup (GLoc D.sp.cm.sig V.gram v) :=
  Function.update (fun v => if hv : v ∈ T.S then kerSub T ⟨v, hv⟩ else Kv V v) U.u U.frame.iwahori

def fam (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
    (A : Finset (HeightOneSpectrum (𝓞 D.host.F))) : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ :=
  fun v => if hv : v ∈ T.S ∧ v ∈ A then T.idem μf ⟨v, hv.1⟩ else normInd (μf v) (levelFam T U v : Set _)

variable (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
  (A : Finset (HeightOneSpectrum (𝓞 D.host.F)))

theorem levelFam_u : levelFam T U U.u = U.frame.iwahori := Function.update_self ..

theorem levelFam_of_mem (hu : U.u ∉ T.S) (v : T.S) : levelFam T U v = kerSub T v := by
  have : (v : HeightOneSpectrum (𝓞 D.host.F)) ≠ U.u := fun e => hu (e ▸ v.2)
  rw [levelFam, Function.update_of_ne this, dif_pos v.2]

theorem levelFam_of_notMem {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ T.S) (hu : v ≠ U.u) :
    levelFam T U v = Kv V v := by
  rw [levelFam, Function.update_of_ne hu, dif_neg hv]

theorem fam_of_mem {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ T.S) (hA : v ∈ A) :
    fam T U μf A v = T.idem μf ⟨v, hv⟩ := dif_pos ⟨hv, hA⟩

theorem fam_of_not {v : HeightOneSpectrum (𝓞 D.host.F)} (h : ¬ (v ∈ T.S ∧ v ∈ A)) :
    fam T U μf A v = normInd (μf v) (levelFam T U v : Set _) := dif_neg h

end GlobalTheory.TrIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLocalLatticeCompletionIffCommMem
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

namespace GlobalTheory.TwistLat

theorem comm_symm_mem_intLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {a : E ⊗[F] Fv F v} (ha : a ∈ Formalism.BasicNotions.intV E v) :
    (Algebra.TensorProduct.comm F (Fv F v) E).symm a ∈ GlobalTheory.AdelicU.intLoc F E v := by
  have hle : Formalism.BasicNotions.intV E v ≤ (GlobalTheory.AdelicU.intLoc F E v).comap
      ((Algebra.TensorProduct.comm F (Fv F v) E).symm : E ⊗[F] Fv F v →+* Fv F v ⊗[F] E) := by
    unfold Formalism.BasicNotions.intV Formalism.UG.tensInt
    rw [Subring.closure_le]
    rintro z (⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩)
    · obtain ⟨x, rfl⟩ := RingHom.mem_range.1 (show e ∈ (algebraMap (𝓞 E) E).range from he)
      simp only [SetLike.mem_coe, Subring.mem_comap, RingHom.coe_coe]
      simpa using GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) (v := v) (one_mem _) x
    · simp only [SetLike.mem_coe, Subring.mem_comap, RingHom.coe_coe]
      simpa using GlobalTheory.AdelicU.tmul_mem_intLoc (E := E) (v := v) (a := b) hb 1
  exact hle ha

theorem mem_latLoc_iff_comm_mem_locL : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E), y ∈ GlobalTheory.AdelicU.latLoc F L v ↔ (fun i => Algebra.TensorProduct.comm F (Fv F v) E (y i)) ∈ Formalism.L2.Herm.locL v L := by
  intro F E _ _ _ _ _ n L v y
  constructor
  · intro hy
    refine GlobalTheory.AdelicU.latLoc_induction
      (p := fun y => (fun i => Algebra.TensorProduct.comm F (Fv F v) E (y i)) ∈ Formalism.L2.Herm.locL v L)
      (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy
    · have hmem : ((1 : E) ⊗ₜ[F] a) ∈ Formalism.BasicNotions.intV E v :=
        Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
      have h2 := (Formalism.L2.Herm.locL v L).smul_mem ⟨_, hmem⟩
        (Submodule.subset_span ⟨x, hx, rfl⟩ : (fun i => Formalism.UG.inclE (F := F) (Fv F v) (x i)) ∈ Formalism.L2.Herm.locL v L)
      convert h2 using 1
      funext i
      simp [Formalism.UG.inclE, Subring.smul_def]
    · convert (Formalism.L2.Herm.locL v L).zero_mem using 1
      funext i; simp
    · convert (Formalism.L2.Herm.locL v L).add_mem hy hz using 1
      funext i; simp
    · convert (Formalism.L2.Herm.locL v L).neg_mem hy using 1
      funext i; simp
  · intro hy
    have key : ∀ z : Fin n → E ⊗[F] Fv F v, z ∈ Formalism.L2.Herm.locL v L →
        (fun i => (Algebra.TensorProduct.comm F (Fv F v) E).symm (z i)) ∈ GlobalTheory.AdelicU.latLoc F L v := by
      intro z hz
      unfold Formalism.L2.Herm.locL Formalism.UG.latS at hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        convert GlobalTheory.AdelicU.tmul_mem_latLoc (F := F) (v := v) (one_mem _) hx using 1
        funext i; simp [Formalism.UG.inclE]
      | zero =>
        convert (GlobalTheory.AdelicU.latLoc F L v).zero_mem using 1
        funext i; simp
      | add z w _ _ hz hw =>
        convert (GlobalTheory.AdelicU.latLoc F L v).add_mem hz hw using 1
        funext i; simp
      | smul c z _ hz =>
        have h2 := (GlobalTheory.AdelicU.latLoc F L v).smul_mem ⟨_, comm_symm_mem_intLoc v c.2⟩ hz
        convert h2 using 1
        funext i; simp [Subring.smul_def]
    convert key _ hy using 1
    funext i; simp

end GlobalTheory.TwistLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermBoundedDenominatorsMovedLevel
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTermIntegral

variable {D : D7}

def infLift {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  x.map fun e => (pairA D.host.F 1 0 : AF D.host.F) ⊗ₜ[D.host.F] e

theorem map_incA_eq {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) :
    x.map (incA D) = finLift x + infLift x := by
  ext a b
  simp only [Matrix.map_apply, Matrix.add_apply, finLift, infLift]
  rw [← TensorProduct.add_tmul]
  have : (pairA D.host.F 0 1 + pairA D.host.F 1 0 : AF D.host.F) = 1 := by
    refine Prod.ext ?_ ?_
    · exact zero_add _
    · exact add_zero _
  rw [this]
  rfl

theorem infLift_finPart {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) :
    (infLift x).map (finPart D) = 0 := by
  ext a b
  simp only [Matrix.map_apply, infLift, Matrix.zero_apply]
  show (sndA D.host.F (pairA D.host.F 1 0)) ⊗ₜ[D.host.F] x a b = 0
  have : sndA D.host.F (pairA D.host.F 1 0) = 0 := rfl
  rw [this, TensorProduct.zero_tmul]

theorem compAt_infLift {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ}
    (x : Matrix (Fin m) (Fin n) D.host.E) : compAt θ τ (infLift x) = x.map (tauE D τ) := by
  ext a b
  simp only [compAt, Matrix.map_apply, infLift]
  have : infPart D ((pairA D.host.F 1 0 : AF D.host.F) ⊗ₜ[D.host.F] x a b) =
      (1 : Ainf D.host.F) ⊗ₜ[D.host.F] x a b := rfl
  rw [this]
  exact (hθ τ).1 _

theorem sum_two_re_tauE (D : D7) (e : D.host.E) :
    ∑ τ, 2 * (tauE D τ e).re = ((Algebra.trace ℚ D.host.E e : ℚ) : ℝ) := by
  classical
  have hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => star_star σ
  have hi := GlobalTheory.StdRat.tauE_injective D
  have hcm := GlobalTheory.StdRat.tauE_cm D
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => ComplexEmbedding.conjugate (tauE D t)) := by
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (tauE D b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (tauE D a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, tauE D t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h1 : ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) = ∑ σ : D.host.E →+* ℂ, σ e := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) ℂ (x := e)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom D.host.E ℂ) _ _ fun _ => rfl).symm
  have h4 := hb.sum_comp fun σ : D.host.E →+* ℂ => σ e
  rw [Fintype.sum_sum_type, ← h1] at h4
  simp only [Sum.elim_inl, Sum.elim_inr] at h4
  have h5 := congrArg Complex.re h4
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.add_re, Complex.re_sum, Complex.conj_re,
    Complex.ratCast_re] at h5
  rw [← h5, Finset.sum_congr rfl fun τ _ => two_mul _, Finset.sum_add_distrib]

theorem phase_add (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) {r : ℕ}
    (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (y : Matrix (Fin W.rank) (Fin r) D.host.E)
    (κ κ' : Mx D W.rank r) :
    phase ψ V W C C' y (κ + κ') = phase ψ V W C C' y κ * phase ψ V W C C' y κ' := by
  have h : isoPart V W C (κ + κ') = isoPart V W C κ + isoPart V W C κ' := Matrix.add_mul _ _ _
  unfold phase
  rw [h, (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D V W).2.1, AddChar.map_add_eq_mul]

theorem isoPart_rat (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (y : Matrix (Fin W.rank) (Fin r) D.host.E) :
    isoPart V W C (y.map (incA D)) = ratW W V (y * (adj D C * V.gram)) := by
  show HMul.hMul (y.map (incA D)) ((adj D C * V.gram).map (incA D)) = (y * (adj D C * V.gram)).map (incA D)
  simp only [Matrix.map_mul]

theorem phase_rat (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V W : HSp D) {r : ℕ}
    (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (y x : Matrix (Fin W.rank) (Fin r) D.host.E) :
    phase ψ V W C C' y (x.map (incA D)) = 1 := by
  unfold phase
  rw [isoPart_rat, isoPart_rat]
  obtain ⟨a, ha⟩ := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_rat D V W (y * (adj D C' * V.gram)) (x * (adj D C * V.gram))
  rw [ha]
  exact hψ.2.2.1 a

theorem trace_tau (τ : D.what₂.Tau) {m n : ℕ} (q : Matrix (Fin m) (Fin n) D.host.E)
    (x : Matrix (Fin n) (Fin m) D.host.E) :
    Matrix.trace (q.map (tauE D τ) * x.map (tauE D τ)) = tauE D τ (Matrix.trace (q * x)) := by
  rw [← Matrix.map_mul (f := tauE D τ)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem ratPair_nat_smul (W : HSp D) {r : ℕ} (y x : Matrix (Fin W.rank) (Fin r) D.host.E) (N : ℕ) :
    ((Algebra.trace ℚ D.host.E (Matrix.trace (pairQ W y * ((N : D.host.E) • x))) : ℚ) : ℝ) =
      (N : ℝ) * ratPair W y x := by
  have h : Matrix.trace (pairQ W y * ((N : D.host.E) • x)) = N • Matrix.trace (pairQ W y * x) := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, nsmul_eq_mul]
  rw [h, map_nsmul, nsmul_eq_mul, ratPair]
  push_cast
  rfl

theorem integral : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ e : ℕ, ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ M : ℕ, 0 < M ∧ ∀ (g : GA D V) (h : GA D W), ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ M * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e ∧ ∀ F : WO V W → ℂ, IsThetaFunO ψ V W F → (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ V W (actO V W g h u) F = F) → ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, term ψ V V' W C C' B μ 𝓨 F y ≠ 0 → ∀ x : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ a b, IsIntegral ℤ (x a b)) → ∃ c : ℤ, (N : ℝ) * ratPair W y x = c := by
  intro D V V' W r C C' B hs hCC ψ hψ θ hθ μ 𝓨 hY
  obtain ⟨e, he⟩ := _root_.GlobalTheory.LevelHeight.levelheight D V W r (adj D C * V.gram)
  refine ⟨e, fun U hU => ?_⟩
  obtain ⟨M, hM, hMN⟩ := he U hU
  refine ⟨M, hM, fun g h => ?_⟩
  obtain ⟨N, hN, hNle, hx⟩ := hMN g h
  refine ⟨N, hN, hNle, fun F hF hinv y hy x hxi => ?_⟩
  obtain ⟨u, huU, hufin, hact⟩ := hx x hxi
  have h1 : heisO ψ V W (isoPart V W C (finLift ((N : D.host.E) • x))) F = F := by
    have := hinv u huU hufin
    rw [hact] at this
    exact this
  have h2 := _root_.GlobalTheory.MixedTermTranslate.term_heisO_isoPart D V V' W r C C' B hs ψ hψ μ 𝓨 hY F hF y (finLift ((N : D.host.E) • x))
  rw [h1] at h2
  have hph : phase ψ V W C C' y (finLift ((N : D.host.E) • x)) = 1 :=
    mul_right_cancel₀ hy (by rw [one_mul]; exact h2.symm)
  have hinf : phase ψ V W C C' y (infLift ((N : D.host.E) • x)) = 1 := by
    have := phase_rat ψ hψ.1 V W C C' y ((N : D.host.E) • x)
    rw [map_incA_eq, phase_add, hph, one_mul] at this
    exact this
  rw [_root_.GlobalTheory.PhaseReal.phase_eq D V W r C C' hCC ψ hψ θ hθ y _ (infLift_finPart _)] at hinf
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hinf
  have hsum : (∑ τ, 2 * (Matrix.trace ((pairQ W y).map (tauE D τ) *
      compAt θ τ (infLift ((N : D.host.E) • x)))).re : ℝ) = (N : ℝ) * ratPair W y x := by
    rw [← ratPair_nat_smul, ← sum_two_re_tauE]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [compAt_infLift hθ, trace_tau]
  rw [hsum] at hn
  refine ⟨n, ?_⟩
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have h3 : (((N : ℝ) * ratPair W y x : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by
    apply mul_left_cancel₀ hpi
    rw [hn]
    push_cast
    ring
  exact_mod_cast h3

end GlobalTheory.MixedTermIntegral

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermDerivAlongRationalPairing
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm

namespace GlobalTheory.MixedTerm.DerLaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sum_tauE_add_conj (D : D7) (e : D.host.E) :
    ∑ t, (tauE D t e + starRingEnd ℂ (tauE D t e)) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  classical
  have h1 : ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) = ∑ σ : D.host.E →+* ℂ, σ e := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) ℂ (x := e)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom D.host.E ℂ) _ _ fun _ => rfl).symm
  have hi := GlobalTheory.StdRat.tauE_injective D
  have hcm := GlobalTheory.StdRat.tauE_cm D
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => ComplexEmbedding.conjugate (tauE D t)) := by
    have hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
      fun σ => star_star σ
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (tauE D b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (tauE D a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, tauE D t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h4 := hb.sum_comp fun σ : D.host.E →+* ℂ => σ e
  rw [Fintype.sum_sum_type, ← h1] at h4
  simp only [Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq] at h4
  rw [Finset.sum_add_distrib, h4]

theorem sum_two_re_tauE (D : D7) (e : D.host.E) :
    ∑ t, (((2 * (tauE D t e).re : ℝ)) : ℂ) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  rw [← sum_tauE_add_conj]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Complex.add_conj]

theorem trace_map_mul (D : D7) (τ : D.what₂.Tau) {m n : ℕ} (P : Matrix (Fin m) (Fin n) D.host.E)
    (x : Matrix (Fin n) (Fin m) D.host.E) :
    Matrix.trace (P.map (tauE D τ) * x.map (tauE D τ)) = tauE D τ (Matrix.trace (P * x)) := by
  rw [← Matrix.map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem term_derAlong : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ x y : Matrix (Fin W.rank) (Fin r) D.host.E, term ψ V V' W C C' B μ 𝓨 (derAlong ψ θ V W C x G) y = (2 * Real.pi * Complex.I * (ratPair W y x : ℂ)) * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B hiso hCC ψ hψ θ hθ μ 𝓨 hcov G hG x y
  have hlin := _root_.GlobalTheory.MixedTerm.term_linear D V V' W r C C' B ψ hψ μ 𝓨 hcov y
  have hder := fun τ => _root_.GlobalTheory.MixedTerm.IsoDeriv.term_dRho_dirAt D V V' W r C C' B hiso hCC ψ hψ θ hθ μ 𝓨 hcov G hG τ (x.map (tauE D τ)) y
  set f : D.what₂.Tau → WO V W → ℂ :=
    fun τ => Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ (x.map (tauE D τ))) G with hf
  have hft : ∀ τ, IsThetaFunO ψ V W (f τ) := fun τ => GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ _ hG
  have hsum : ∀ s : Finset D.what₂.Tau,
      term ψ V V' W C C' B μ 𝓨 (∑ τ ∈ s, f τ) y = ∑ τ ∈ s, term ψ V V' W C C' B μ 𝓨 (f τ) y := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
      have h0 := hlin.2 0 G hG
      rw [zero_smul, zero_mul] at h0
      simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        hlin.1 _ _ (hft a) (GlobalTheory.Size.theta_finsetSum s fun i _ => hft i), ih]
  show term ψ V V' W C C' B μ 𝓨 (∑ τ, f τ) y = _
  rw [hsum, Finset.sum_congr rfl fun τ _ => hder τ, ← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  simp only [trace_map_mul, sum_two_re_tauE, ratPair, Complex.ofReal_ratCast]

end GlobalTheory.MixedTerm.DerLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacePointCommuteOfNePlace
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PointAtPlaceComm

open GlobalTheory.PointAtPlace GlobalTheory.PointAtPlaceHom Formalism.MainNotions.StandardLattice

theorem atTau_comm : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ τ' : D.what₂.Tau), τ ≠ τ' → ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), atTau θ V τ g * atTau θ V τ' g' = atTau θ V τ' g' * atTau θ V τ g := by
  intro D θ hθ V τ τ' hne g hg g' hg'
  have ha := atTau_spec hθ V τ hg
  have hb := atTau_spec hθ V τ' hg'
  set a := atTau θ V τ g
  set b := atTau θ V τ' g'
  have k : ∀ (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (x : GA D V),
      infMat D.sp.cm.sig V.gram φ x * infMat D.sp.cm.sig V.gram φ x⁻¹ = 1 := fun φ x => by
    rw [← infMat_mul, mul_inv_cancel, infMat_one]
  have triv : ∀ (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (x : GA D V),
      infMat D.sp.cm.sig V.gram φ x = 1 → infMat D.sp.cm.sig V.gram φ x⁻¹ = 1 := fun φ x h => by
    have := k φ x
    rwa [h, Matrix.one_mul] at this
  have hc : IsAtTau θ V τ 1 (a * b * a⁻¹ * b⁻¹) := by
    have all : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) (a * b * a⁻¹ * b⁻¹) = 1 := fun ρ => by
      simp only [infMat_mul]
      by_cases c : ρ = τ
      · subst c
        have hB : infMat D.sp.cm.sig V.gram (θ ρ) b = 1 := hb.2.2 ρ hne
        rw [hB, triv _ _ hB, Matrix.mul_one, Matrix.mul_one, k]
      · have hA : infMat D.sp.cm.sig V.gram (θ ρ) a = 1 := ha.2.2 ρ c
        rw [hA, triv _ _ hA, Matrix.one_mul, Matrix.mul_one, k]
    exact ⟨mul_mem (mul_mem (mul_mem ha.1 hb.1) (inv_mem ha.1)) (inv_mem hb.1), all τ, fun ρ _ => all ρ⟩
  have h1 : IsAtTau θ V τ 1 (1 : GA D V) := ⟨one_mem _, infMat_one V _, fun _ _ => infMat_one V _⟩
  have e : a * b * a⁻¹ * b⁻¹ = 1 :=
    (existsUnique_isAtTau V τ θ hθ 1 (one_mem_UH _)).unique hc h1
  have e2 : a * b * a⁻¹ = b := mul_inv_eq_one.1 e
  exact mul_inv_eq_iff_eq_mul.1 e2

end GlobalTheory.PointAtPlaceComm

end
end

