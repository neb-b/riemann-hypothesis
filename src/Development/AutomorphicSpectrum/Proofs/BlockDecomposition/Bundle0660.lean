module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnitScalingSelfdualHermMeasures
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0041
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0063

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterBilinearLaws
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {ρ p : ℕ}

theorem trA_add (a b : AE D) : trA (a + b) = trA a + trA b := map_add (Algebra.trace (AF D.host.F) (AE D)) a b

theorem pr_add_left (b₀ : HermE D ρ) (x x' y : Mx D ρ p) : pr b₀ (x + x') y = pr b₀ x y + pr b₀ x' y := by
  have h : adj (x + x') = adj x + adj x' := by
    ext i j
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]
  simp only [pr, h]
  exact Matrix.add_mul _ _ _

theorem pr_add_right (b₀ : HermE D ρ) (x y y' : Mx D ρ p) : pr b₀ x (y + y') = pr b₀ x y + pr b₀ x y' := by
  simp only [pr]
  rw [show (HMul.hMul (b₀.1.map (incA D)) (y + y') : Mx D ρ p) = _ from Matrix.mul_add _ _ _]
  exact Matrix.mul_add _ _ _

theorem chv_add_left (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (x x' y : Mx D ρ p) :
    chv ψ b₀ (x + x') y = chv ψ b₀ x y * chv ψ b₀ x' y := by
  simp only [chv, pr_add_left, Matrix.trace_add, trA_add, AddChar.map_add_eq_mul]

theorem chv_add_right (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (x y y' : Mx D ρ p) :
    chv ψ b₀ x (y + y') = chv ψ b₀ x y * chv ψ b₀ x y' := by
  simp only [chv, pr_add_right, Matrix.trace_add, trA_add, AddChar.map_add_eq_mul]

theorem chv_norm (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (x y : Mx D ρ p) :
    ‖chv ψ b₀ x y‖ = 1 := hψ.2.1 _

theorem chv_zero_right (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (x : Mx D ρ p) : chv ψ b₀ x 0 = 1 := by
  have h : pr b₀ x 0 = 0 := by
    have := pr_add_right b₀ x 0 0
    simpa using this
  simp only [chv, h, Matrix.trace_zero]
  have h0 : trA (0 : AE D) = 0 := map_zero (Algebra.trace (AF D.host.F) (AE D))
  rw [h0, AddChar.map_zero_eq_one]

theorem chv_neg_right (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (x y : Mx D ρ p) :
    chv ψ b₀ x (-y) = conj (chv ψ b₀ x y) := by
  have h1 : chv ψ b₀ x y * chv ψ b₀ x (-y) = 1 := by
    rw [← chv_add_right, add_neg_cancel, chv_zero_right]
  have h2 : chv ψ b₀ x y * conj (chv ψ b₀ x y) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, chv_norm ψ hψ]
    simp
  exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one h1) (h1.trans h2.symm)

theorem trA_incA (t : D.host.E) :
    trA (incA D t) = algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E t) := by
  have h2 : Algebra.lmul (AF D.host.F) (AE D) (incA D t) =
      (Algebra.lmul D.host.F D.host.E t).baseChange (AF D.host.F) := by
    ext x
    simp [incA, inclR]
  show Algebra.trace (AF D.host.F) (AE D) (incA D t) = _
  rw [Algebra.trace_apply, h2, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem pr_rt (b₀ : HermE D ρ) (ξ ξ' : Matrix (Fin ρ) (Fin p) D.host.E) :
    pr b₀ (rt ξ) (rt ξ') = ((ξ.map D.sp.cm.sig)ᵀ * (b₀.1 * ξ')).map (incA D) := by
  have h : adj (rt ξ) = ((ξ.map D.sp.cm.sig)ᵀ).map (incA D) := by
    ext i j
    simp only [adj, rt, Matrix.transpose_apply, Matrix.map_apply]
    rfl
  simp only [pr, h, Matrix.map_mul]

theorem chv_rt (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (ξ ξ' : Matrix (Fin ρ) (Fin p) D.host.E) : chv ψ b₀ (rt ξ) (rt ξ') = 1 := by
  have h : Matrix.trace (pr b₀ (rt ξ) (rt ξ')) = incA D (Matrix.trace ((ξ.map D.sp.cm.sig)ᵀ * (b₀.1 * ξ'))) := by
    rw [pr_rt]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]
  rw [chv, h, trA_incA]
  exact hψ.2.2.1 _

theorem chv_continuous (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) :
    Continuous (fun v : Mx D ρ p × Mx D ρ p => chv ψ b₀ v.1 v.2) := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (trA (D := D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hc : Continuous (cA D) := GlobalTheory.FockCompare.ThetaCont.continuous_conj
  have ha : Continuous fun v : Mx D ρ p × Mx D ρ p => adj v.1 := by
    unfold adj
    exact ((continuous_fst.matrix_map hc)).matrix_transpose
  refine hψ.1.comp (ht.comp ?_)
  exact (ha.matrix_mul (continuous_const.matrix_mul continuous_snd)).matrix_trace

theorem chv_facts : ∀ {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, (∀ x x' y : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ (x + x') y = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x' y) ∧ (∀ x y y' : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (y + y') = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y') ∧ (∀ x y : Mx D ρ p, ‖GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y‖ = 1) ∧ (∀ x y : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (-y) = conj (GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y)) ∧ (∀ ξ ξ' : Matrix (Fin ρ) (Fin p) D.host.E, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ (GlobalTheory.CompanionTheory.FJE.rt ξ) (GlobalTheory.CompanionTheory.FJE.rt ξ') = 1) ∧ Continuous (fun v : Mx D ρ p × Mx D ρ p => GlobalTheory.CompanionTheory.FJE.chv ψ b₀ v.1 v.2) := by
  intro D ρ p ψ hψ b₀
  exact ⟨chv_add_left ψ b₀, chv_add_right ψ b₀, chv_norm ψ hψ b₀, chv_neg_right ψ hψ b₀, chv_rt ψ hψ b₀,
    chv_continuous ψ hψ b₀⟩

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCovolumeFormula
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermSd
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HermCov

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def ratVec {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) [FiniteDimensional F E]
    (A : Matrix (Fin n) (Fin n) E) : Idx n d → F :=
  Sum.elim (fun a => 1 / 2 * Algebra.trace F E (A a a)) fun q => b.repr (A q.1.1.1 q.1.1.2) q.2

def ofVec (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (k : Idx n d → F) :
    Matrix (Fin n) (Fin n) E := fun a c =>
  if h : a < c then ∑ l, k (Sum.inr (⟨(a, c), h⟩, l)) • b l
  else if h' : c < a then σ (∑ l, k (Sum.inr (⟨(c, a), h'⟩, l)) • b l)
  else algebraMap F E (k (Sum.inl a))

theorem ofVec_herm {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (n : ℕ) (k : Idx n d → F) (a c : Fin n) : σ (ofVec σ b n k c a) = ofVec σ b n k a c := by
  rcases lt_trichotomy a c with h | h | h
  · simp only [ofVec, dif_pos h, dif_neg (not_lt_of_gt h), hinv]
  · subst h
    simp only [ofVec, lt_irrefl, dite_false, AlgHom.commutes]
  · simp only [ofVec, dif_pos h, dif_neg (not_lt_of_gt h)]

theorem ratVec_ofVec [FiniteDimensional F E] [CharZero F] (h2 : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (k : Idx n d → F) :
    ratVec b n (ofVec σ b n k) = k := by
  funext i
  cases i with
  | inl a =>
    simp only [ratVec, Sum.elim_inl, ofVec, lt_irrefl, dite_false, Algebra.trace_algebraMap, h2]
    simp
  | inr q =>
    obtain ⟨p, l⟩ := q
    simp only [ratVec, Sum.elim_inr, ofVec, dif_pos p.2]
    rw [b.repr_sum_self]

variable (R : Type) [CommRing R] [Algebra F R]

theorem repr_inclR {d : ℕ} (b : Module.Basis (Fin d) F E) (x : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (inclR R x) k = algebraMap F R (b.repr x k) := by
  change (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] x) k = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

variable [TopologicalSpace R]

theorem hermVec_map [FiniteDimensional F E] (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) E) (S : HermR R σ n)
    (hS : (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = A.map (inclR R)) (i : Idx n d) :
    hermVec R σ b n S i = algebraMap F R (ratVec b n A i) := by
  cases i with
  | inl a =>
    simp only [hermVec, toVec, HaarCoord.hermCoord, Sum.elim_inl, ratVec, hS, Matrix.map_apply]
    change _ * Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] A a a) = _
    rw [trace_tmul, one_mul, map_mul]
  | inr q =>
    simp only [hermVec, toVec, HaarCoord.hermCoord, Sum.elim_inr, ratVec, hS, Matrix.map_apply]
    exact repr_inclR R b _ _

end Alg

section Main

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth PositivityTheory.SiegelWeilFormula.KWhit.MeasP
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_ratHerm_iff {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) (h2 : Module.finrank F E = 2)
    [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (hinj : Function.Injective (hermVec (AF F) σ b n)) (S : HermR (AF F) σ n) :
    S ∈ ratHerm F E σ n ↔ ∃ k : Idx n d → F, ∀ i, hermVec (AF F) σ b n S i = algebraMap F (AF F) (k i) := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨ratVec b n A, hermVec_map (AF F) σ b n A S hA.symm⟩
  · rintro ⟨k, hk⟩
    have hmem : (ofVec σ b n k).map (inclR (AF F)) ∈ HermR (AF F) σ n := by
      intro a c
      simp only [Matrix.map_apply]
      rw [← ofVec_herm hinv b n k a c]
      change sigR (AF F) σ ((1 : AF F) ⊗ₜ[F] _) = (1 : AF F) ⊗ₜ[F] _
      rw [HaarCoord.sigR_tmul]
    have hT : (⟨_, hmem⟩ : HermR (AF F) σ n) = S := by
      apply hinj
      funext i
      rw [hermVec_map (AF F) σ b n (ofVec σ b n k) _ rfl i, ratVec_ofVec h2, hk]
    refine ⟨ofVec σ b n k, ?_⟩
    rw [← hT]
    rfl

theorem existsUnique_sub_mem_pi {ι : Type} (x : ι → AF F) :
    ∃! k : ι → F, (fun i => x i - algebraMap F (AF F) (k i)) ∈
      Set.univ.pi fun _ : ι => fundamentalSet F := by
  choose k hk huniq using fun i => existsUnique_sub_mem_fundamentalSet F (x i)
  refine ⟨k, fun i _ => hk i, fun k' hk' => funext fun i => huniq i _ (hk' i (Set.mem_univ i))⟩

theorem hermCovol : HermCovol := by
  intro F E _ _ _ _ _ σ hCM ψ hψ n ν hν
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts hCM
  have h2 := hCM.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; omega)
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
  let e := (hermVec_isHomeomorph hCM (AF F) b n).homeomorph _
  have he : ∀ S, e S = hermVec (AF F) σ b n S := fun _ => rfl
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hψ.2.2.2
    apply hx
    rw [hξ x, map_zero, zero_mul, AddChar.map_zero_eq_one]
    simp
  have hs : (ξ • formB σ b n).IsSymm := (formB_isSymm hinv b n).smul ξ
  have hdet : (ξ • formB σ b n).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hξ0) (formB_det hinv b n)
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (HermR (AF F) σ n) := inferInstance
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  have hsd : ν.map e = adeleMeasurePi F := by
    refine GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth.selfDual_eq _ hs hdet _
      (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth.selfDual_transport e ?_ _ _ ?_ ν hν)
    · intro x y
      exact hermVec_add (AF F) b n x y
    · intro S T
      have h3 : (ξ • formB σ b n).map (algebraMap F (AF F)) =
          algebraMap F (AF F) ξ • (formB σ b n).map (algebraMap F (AF F)) := by
        ext p q
        exact map_mul (algebraMap F (AF F)) ξ (formB σ b n p q)
      rw [hξ, pair_eq (AF F) hinv h2 hδ hσδ b n S T, chiG, h3, Matrix.smul_mulVec, dotProduct_smul,
        smul_eq_mul]
      rfl
  set D : Set (Idx n 2 → AF F) := Set.univ.pi fun _ => fundamentalSet F with hD
  have hDm : MeasurableSet D := MeasurableSet.univ_pi fun _ => measurableSet_fundamentalSet F
  have hinj : Function.Injective (hermVec (AF F) σ b n) := e.injective
  refine ⟨e ⁻¹' D, IsAddFundamentalDomain.mk' (hDm.preimage e.measurable).nullMeasurableSet ?_, ?_⟩
  · intro S
    obtain ⟨k, hk, huniq⟩ := existsUnique_sub_mem_pi (e S)
    have hg : e.symm (fun i => algebraMap F (AF F) (-k i)) ∈ ratHerm F E σ n :=
      (mem_ratHerm_iff hinv h2 b n hinj _).2 ⟨fun i => -k i, fun i => by
        rw [← he, e.apply_symm_apply]⟩
    refine ⟨⟨_, hg⟩, ?_, ?_⟩
    · change e (e.symm _ + S) ∈ D
      rw [he, hermVec_add, ← he, ← he, e.apply_symm_apply]
      convert hk using 2 with i
      simp [sub_eq_add_neg, add_comm]
    · rintro ⟨g, hgm⟩ hg'
      obtain ⟨k', hk'⟩ := (mem_ratHerm_iff hinv h2 b n hinj _).1 hgm
      change e (g + S) ∈ D at hg'
      rw [he, hermVec_add, ← he] at hg'
      have hkk : (fun i => -k' i) = k := huniq _ (by
        convert hg' using 2 with i
        simp [he, hk', sub_eq_add_neg, add_comm])
      refine Subtype.ext (e.injective ?_)
      rw [e.apply_symm_apply]
      funext i
      rw [he, hk', ← hkk]
      simp
  · rw [← Measure.map_apply e.measurable hDm, hsd, adeleMeasurePi, hD, Measure.pi_pi]
    simp [adeleMeasure_fundamentalSet]

end Main

end GlobalTheory.CompanionTheory.SW.HermCov
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPrimitiveVectorPairing
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreePartner

theorem isReduced_tens (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [IsReduced R] : IsReduced (R ⊗[F] E) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Algebra.FormallyEtale F E := Algebra.FormallyEtale.of_isSeparable F E
  haveI : Algebra.FormallySmooth F E := inferInstance
  haveI : Algebra.FinitePresentation F E := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.Smooth F E := ⟨inferInstance, inferInstance⟩
  haveI : Algebra.Smooth R (R ⊗[F] E) := inferInstance
  exact GlobalTheory.isReduced_algebra_of_smooth_of_isReduced R (R ⊗[F] E)

theorem isUnit_det_JR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (h : J.det ≠ 0) :
    IsUnit (JR (F := F) R J).det := by
  have e : (JR (F := F) R J).det = inclR (F := F) R J.det := by
    rw [RingHom.map_det]
    rfl
  rw [e]
  exact (IsUnit.mk0 _ h).map _

theorem exists_partner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) (fun _ : Fin 1 => x) → ∃ y : Fin M → R ⊗[F] E, hR R σ J x y = 1 := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hloc x hx
  obtain ⟨-, -, -, -, hA, hRed, -, -⟩ := hloc
  haveI := hA
  haveI := hRed
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R _
  haveI : IsReduced (R ⊗[F] E) := isReduced_tens F E R
  have hinv : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z :=
    HermTop.sigR_sigR R (HermTop.sigma_sigma hσ)
  have hlip := FreeOpen.lip_of_artinian_reduced (R ⊗[F] E)
  obtain ⟨P, hP⟩ := hlip (Fin M) (Fin 1)
    (Matrix.of fun i (_ : Fin 1) => sigR R σ (x i)) (by
      intro c hc
      have h1 : ∀ i, sigR R σ (x i) * c 0 = 0 := by
        intro i
        have := congrFun hc i
        simpa [Matrix.mulVec, dotProduct] using this
      have h2 : sigR R σ (c 0) • x = 0 := by
        funext i
        have := congrArg (sigR R σ) (h1 i)
        rw [map_mul, hinv, map_zero] at this
        simpa [mul_comm] using this
      have h3 := Fintype.linearIndependent_iff.mp hx (fun _ => sigR R σ (c 0)) (by simpa using h2) 0
      have h4 : c 0 = 0 := by
        have := congrArg (sigR R σ) h3
        simpa [hinv] using this
      funext j
      rw [Subsingleton.elim j 0]
      simpa using h4)
  have hu := isUnit_det_JR (F := F) R hJ.2
  refine ⟨(JR R J)⁻¹ *ᵥ (fun j => P 0 j), ?_⟩
  have hv : JR R J *ᵥ ((JR R J)⁻¹ *ᵥ (fun j => P 0 j)) = fun j => P 0 j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h00 := congrFun (congrFun hP 0) 0
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply_eq] at h00
  have hform' : hR R σ J x ((JR R J)⁻¹ *ᵥ (fun j => P 0 j)) =
      ∑ i, sigR R σ (x i) * (JR R J *ᵥ ((JR R J)⁻¹ *ᵥ (fun j => P 0 j))) i := by
    simp only [hR, hform, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hform', hv, ← h00]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.CompanionTheory.WeilSiegel.FreePartner
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentExtendByUnitVector
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree

variable {K : Type} [CommRing K] {M n : ℕ}

theorem sum_vec_zero (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) (g : Fin (n + 1) → K) :
    (∑ a, g a • (vec α c X : Fin (n + 1) → Fin (M + 1) → K) a) 0
      = g 0 * α + ∑ j : Fin n, g j.succ * c j := by
  rw [Finset.sum_apply, Fin.sum_univ_succ]
  simp [vec]

theorem sum_vec_succ (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) (g : Fin (n + 1) → K)
    (i : Fin M) :
    (∑ a, g a • (vec α c X : Fin (n + 1) → Fin (M + 1) → K) a) i.succ
      = (∑ j : Fin n, g j.succ • X j) i := by
  rw [Finset.sum_apply, Fin.sum_univ_succ, Finset.sum_apply]
  simp [vec]

theorem linearIndependent_vec_iff (K : Type) [CommRing K] (M n : ℕ) (α : K) (hα : IsUnit α)
    (c : Fin n → K) (X : Fin n → Fin M → K) :
    LinearIndependent K (vec α c X : Fin (n + 1) → Fin (M + 1) → K) ↔ LinearIndependent K X := by
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h w hw j
    obtain ⟨β, hβ⟩ := hα.exists_left_inv
    have key := h (Fin.cons (-(∑ j : Fin n, w j * c j) * β) w) (by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [sum_vec_zero]
        simp only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply]
        rw [mul_assoc, hβ]
        ring
      · rw [sum_vec_succ]
        simp only [Fin.cons_succ, Pi.zero_apply]
        rw [hw]
        rfl) j.succ
    simpa using key
  · intro h w hw
    have hs : ∀ j : Fin n, w j.succ = 0 := by
      refine h (fun j => w j.succ) ?_
      funext i
      have := congrFun hw i.succ
      rwa [sum_vec_succ] at this
    have h0 : w 0 = 0 := by
      have := congrFun hw 0
      rw [sum_vec_zero] at this
      simp only [hs, zero_mul, Finset.sum_const_zero, add_zero, Pi.zero_apply] at this
      exact (hα.mul_left_eq_zero).1 this
    intro a
    refine Fin.cases h0 hs a

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentUnitaryActionIff
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree

theorem linearIndependent_gl_mulVec {K : Type} [CommRing K] {M n : ℕ} (g : GL (Fin M) K)
    (X : Fin n → Fin M → K) (hX : LinearIndependent K X) :
    LinearIndependent K (fun a => (g : Matrix (Fin M) (Fin M) K).mulVec (X a)) := by
  have hinj : Function.Injective (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) K)) := by
    intro x y hxy
    have h2 := congrArg (((g⁻¹ : GL (Fin M) K) : Matrix (Fin M) (Fin M) K).mulVec) hxy
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
    exact h2
  exact hX.map' (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) K)) (LinearMap.ker_eq_bot.2 hinj)

theorem actW_linearIndependent_iff : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), LinearIndependent (R ⊗[F] E) (actW R σ J h X) ↔ LinearIndependent (R ⊗[F] E) X := by
  intro F E _ _ _ R _ _ σ M n J h X
  set g := HA.mat R σ J h with hg
  have hact : actW R σ J h X = fun a => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec (X a) := rfl
  refine ⟨fun hY => ?_, fun hX => ?_⟩
  · have h2 := linearIndependent_gl_mulVec g⁻¹ _ hY
    have h3 : (fun a => ((g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec
        (actW R σ J h X a)) = X := by
      funext a
      rw [hact]
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rwa [h3] at h2
  · rw [hact]
    exact linearIndependent_gl_mulVec g X hX

end GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree
end

