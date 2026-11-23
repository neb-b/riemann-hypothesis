module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceRep
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

section Fields

variable {T : Type} {n : ℕ}


open Classical in
def matDer (τ : T) (X : Matrix (Fin n) (Fin n) ℂ) :
    Derivation ℂ (MvPolynomial (T × Fin n × Fin n) ℂ) (MvPolynomial (T × Fin n × Fin n) ℂ) :=
  MvPolynomial.mkDerivation ℂ fun p =>
    if p.1 = τ then ∑ m, MvPolynomial.X (τ, p.2.1, m) * MvPolynomial.C (X m p.2.2) else 0

open Classical in
theorem matDer_X (τ : T) (X : Matrix (Fin n) (Fin n) ℂ) (p : T × Fin n × Fin n) :
    matDer τ X (MvPolynomial.X p) =
      if p.1 = τ then ∑ m, MvPolynomial.X (τ, p.2.1, m) * MvPolynomial.C (X m p.2.2) else 0 :=
  MvPolynomial.mkDerivation_X _ _ _

theorem matDer_add (τ : T) (X Y : Matrix (Fin n) (Fin n) ℂ) : matDer τ (X + Y) = matDer τ X + matDer τ Y := by
  classical
  refine MvPolynomial.derivation_ext fun p => ?_
  rw [Derivation.add_apply, matDer_X, matDer_X, matDer_X]
  split_ifs
  · simp [mul_add, Finset.sum_add_distrib]
  · simp

theorem matDer_smul (τ : T) (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : matDer τ (c • X) = c • matDer τ X := by
  classical
  refine MvPolynomial.derivation_ext fun p => ?_
  rw [Derivation.smul_apply, matDer_X, matDer_X]
  split_ifs
  · simp only [Matrix.smul_apply, smul_eq_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.C_mul, MvPolynomial.smul_eq_C_mul]; ring
  · simp

theorem matDer_bracket (τ : T) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⁅matDer τ X, matDer τ Y⁆ = matDer τ (X * Y - Y * X) := by
  classical
  refine MvPolynomial.derivation_ext fun p => ?_
  rw [Derivation.commutator_apply, matDer_X, matDer_X, matDer_X]
  split_ifs with h
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, Derivation.leibniz, MvPolynomial.derivation_C, smul_zero, zero_add, matDer_X, if_true,
      smul_eq_mul, Finset.sum_mul, Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, MvPolynomial.C_mul,
      Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, mul_zero, zero_add]
      refine congrArg₂ (· - ·) ?_ ?_ <;> rw [Finset.sum_comm] <;>
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  · simp

theorem matDer_comm {τ τ' : T} (h : τ ≠ τ') (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⁅matDer τ X, matDer τ' Y⁆ = 0 := by
  classical
  refine MvPolynomial.derivation_ext fun p => ?_
  rw [Derivation.commutator_apply, matDer_X, matDer_X, Derivation.zero_apply]
  by_cases h1 : p.1 = τ <;> by_cases h2 : p.1 = τ' <;>
    set_option synthInstance.maxHeartbeats 100000 in
      simp [h1, h2, h, Ne.symm h, map_sum, Derivation.leibniz, MvPolynomial.derivation_C, matDer_X]

theorem matDer_commute {τ τ' : T} (h : τ ≠ τ') (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Commute (matDer τ X : Module.End ℂ (MvPolynomial (T × Fin n × Fin n) ℂ)) (matDer τ' Y) := by
  refine LinearMap.ext fun a => ?_
  have := congrArg (fun D : Derivation ℂ _ _ => D a) (matDer_comm h X Y)
  simp only [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] at this
  exact this

end Fields

section Reps

variable {D : D7}

abbrev PolyE (V : HSp D) : Type := MvPolynomial (D.what₂.Tau × Fin V.rank × Fin V.rank) ℂ

def realEntries (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (g : GA D V) :
    D.what₂.Tau × Fin V.rank × Fin V.rank → ℂ :=
  fun p => infMat D.sp.cm.sig V.gram (θ p.1) g p.2.1 p.2.2

def polyFun (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (P : PolyE V) : GA D V → ℂ :=
  fun g => MvPolynomial.eval (realEntries θ V g) P

theorem exists_placeRep (V : HSp D) (τ : D.what₂.Tau) : ∃ π : EnvAt V τ →ₐ[ℂ] Module.End ℂ (PolyE V),
    ∀ X : LieAt V τ, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = (matDer τ X.1 : Module.End ℂ (PolyE V)) := by
  refine GlobalTheory.EnvelopingExtension.exists_algHom_unitary _ _ _ (fun X : LieAt V τ => (matDer τ X.1 : Module.End ℂ (PolyE V)))
    (fun X Y => LinearMap.ext fun a => ?_) (fun c X => LinearMap.ext fun a => ?_) (fun X Y Z h => LinearMap.ext fun a => ?_)
  · change matDer τ (X.1 + Y.1) a = matDer τ X.1 a + matDer τ Y.1 a
    rw [matDer_add]; rfl
  · have e : ((c • X : LieAt V τ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = (c : ℂ) • X.1 := by
      ext i j; simp [Complex.real_smul]
    change matDer τ ((c • X : LieAt V τ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) a = (c : ℂ) • matDer τ X.1 a
    rw [e, matDer_smul]; rfl
  · change matDer τ Z.1 a = matDer τ X.1 (matDer τ Y.1 a) - matDer τ Y.1 (matDer τ X.1 a)
    rw [h, ← matDer_bracket, Derivation.commutator_apply]

def placeRep (V : HSp D) (τ : D.what₂.Tau) : EnvAt V τ →ₐ[ℂ] Module.End ℂ (PolyE V) := (exists_placeRep V τ).choose

theorem placeRep_ι (V : HSp D) (τ : D.what₂.Tau) (X : LieAt V τ) :
    placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = (matDer τ X.1 : Module.End ℂ (PolyE V)) :=
  (exists_placeRep V τ).choose_spec X

theorem placeRep_tmul (V : HSp D) (τ : D.what₂.Tau) (c : ℂ) (X : LieAt V τ) :
    placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ (c ⊗ₜ[ℝ] X)) = c • (matDer τ X.1 : Module.End ℂ (PolyE V)) := by
  rw [show c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, map_smul,
    placeRep_ι]

theorem placeRep_comm (V : HSp D) {τ τ' : D.what₂.Tau} (h : τ ≠ τ') (x : ℂ ⊗[ℝ] LieAt V τ) (y : ℂ ⊗[ℝ] LieAt V τ') :
    Commute (placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ x)) (placeRep V τ' (UniversalEnvelopingAlgebra.ι ℂ y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _)]; exact hx.add_left hx'
  | tmul c X =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [map_add (f := _), map_add (f := _)]; exact hy.add_right hy'
    | tmul c' Y =>
      rw [placeRep_tmul, placeRep_tmul]
      exact ((matDer_commute h X.1 Y.1).smul_left c).smul_right c'


open Classical in
def polyLie (V : HSp D) : GlobalTheory.AutFinLit.LieC V →ₗ⁅ℂ⁆ Module.End ℂ (PolyE V) :=
  DirectSum.toLieAlgebra _ (fun τ => (placeRep V τ).toLieHom.comp (UniversalEnvelopingAlgebra.ι ℂ)) fun τ τ' h x y => by
    change placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ x) * placeRep V τ' (UniversalEnvelopingAlgebra.ι ℂ y) -
      placeRep V τ' (UniversalEnvelopingAlgebra.ι ℂ y) * placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ x) = 0
    rw [(placeRep_comm V h x y).eq, sub_self]

def polyRep (V : HSp D) : GlobalTheory.AutFinLit.Env V →ₐ[ℂ] Module.End ℂ (PolyE V) :=
  UniversalEnvelopingAlgebra.lift ℂ (polyLie V)

open Classical in
theorem polyRep_ι_of (V : HSp D) (τ : D.what₂.Tau) (x : ℂ ⊗[ℝ] LieAt V τ) :
    polyRep V (UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x)) =
      placeRep V τ (UniversalEnvelopingAlgebra.ι ℂ x) := by
  rw [polyRep, UniversalEnvelopingAlgebra.lift_ι_apply, polyLie]
  exact DirectSum.toModule_lof ℂ (M := fun τ => ℂ ⊗[ℝ] LieAt V τ) τ x

end Reps

end GlobalTheory.CentralOps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPoincareGoodPatchOutsideOpen
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem exists_goodPatch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ}
    (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens)
    (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ),
    IsGood E O H → ∀ y ∉ ptsIn X.str σ O, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := by
  intro F _ σ X m E O H hG y hy
  obtain ⟨e, S, hholo, hys, hy0, hcomp, A, hA, c, N, hev⟩ := hG y hy
  have h1 : ∀ᶠ z in 𝓝 y, z ∈ ptsIn X.str σ O → GoodBound S c N (fun v => H A (e.symm v) ()) (e z) :=
    (eventually_nhdsWithin_iff.1 hev).mono fun z hz hzO => hz hzO ()
  have h2 : ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := GlobalTheory.T.adaptedFrame_eventually_near_complexPoint E hA
  have h3 : ∀ᶠ z in 𝓝 y, z ∈ e.source := e.open_source.mem_nhds hys
  have h4 : ∀ᶠ z in 𝓝 y, ∀ a ∈ S, ‖e z a‖ ≤ 1 / 2 := by
    refine (Filter.eventually_all_finset S).2 fun a ha => ?_
    have hc : ContinuousAt (fun z => e z a) y :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin X.dim => ℂ) a).continuous.comp
        (PiLp.continuous_ofLp 2 _)).continuousAt.comp (e.continuousAt hys)
    have h0 : e y a = 0 := hy0 a ha
    have : ∀ᶠ z in 𝓝 y, e z a ∈ Metric.ball (0 : ℂ) (1 / 2) :=
      hc.preimage_mem_nhds (by rw [h0]; exact Metric.ball_mem_nhds _ (by norm_num))
    exact this.mono fun z hz => le_of_lt (by simpa using hz)
  obtain ⟨W, hW, hWo, hyW⟩ := eventually_nhds_iff.1 (h1.and (h2.and (h3.and h4)))
  refine ⟨e, S, A, W, c, hyW, ?_⟩
  exact
  { holo := hholo
    isOpen := hWo
    sub := fun z hz => (hW z hz).2.2.1
    frame := fun z hz => (hW z hz).2.1
    small := fun z hz => (hW z hz).2.2.2
    mem := fun z hz => by
      have := hcomp z (hW z hz).2.2.1
      constructor
      · intro hzO a ha h
        exact (this.2 ⟨a, ha, h⟩) hzO
      · intro hne
        by_contra hzO
        obtain ⟨a, ha, h⟩ := this.1 hzO
        exact hne a ha h
    form := fun z hz hzO a i j => ((hW z hz).1 hzO).form a i j
    dbar := fun z hz hzO a b i j => ((hW z hz).1 hzO).dbar a b i j }

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResiduePlaceOfTwoDimLocalModelStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residuePlace_of_twoDimLocalModel : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  ∀ (S : Place cL) (ψ : S.ring →+* K), S.IsPrimeOf Q → S.ord (t : L) = 1 →
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) →
  ∃ F : Place cK, (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) ∧
    ∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1 := by
  first | exact @GlobalTheory.FieldPair.residuePlace_of_locModel | exact GlobalTheory.FieldPair.residuePlace_of_locModel | (intros; apply GlobalTheory.FieldPair.residuePlace_of_locModel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallAmpleThroughOff
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem GlobalTheory.PairStep.exists_small_ample_through_off : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (x z : X) (ε : ℚ), IsAmpleLB N → ¬ z ⤳ x → 0 < ε → ∃ (b : ℚ) (A : X → ℚ), 0 ≤ b ∧ b ≤ ε ∧ QNum p N b A ∧ Off A x ∧ ¬ Off A z := by
  intro X _ _ p hp N x z ε hN hzx hε
  obtain ⟨l, s, hl, hx, hz⟩ := _root_.GlobalTheory.PairStep.exists_sec_mem_not_mem_of_not_specializes X N x z hN hzx
  have hs : genericPoint X ∈ nonzeroLocus s :=
    (genericPoint_specializes x).mem_open (nonzeroLocus s).isOpen hx
  obtain ⟨m, hm⟩ := exists_nat_ge ((l : ℚ) / ε)
  have hm0 : 0 < m := by
    have : (0 : ℚ) < (l : ℚ) / ε := div_pos (by exact_mod_cast hl) hε
    exact_mod_cast this.trans_le hm
  obtain ⟨hE, hQ⟩ := _root_.GlobalTheory.PairStep.qNum_divOfSec X p hp N hN.isLB l m s hs hm0
  refine ⟨(l : ℚ) / m, _, by positivity, ?_, hQ, ?_, ?_⟩
  · have hm' : (0 : ℚ) < m := by exact_mod_cast hm0
    rw [div_le_iff₀ hm']
    rw [div_le_iff₀ hε] at hm
    linarith [mul_comm (m : ℚ) ε]
  · exact (_root_.GlobalTheory.PairStep.off_qWeil_iff_notMem_supp X _ m x hE hm0).2 (notMem_supp_divOfSec.2 hx)
  · rw [_root_.GlobalTheory.PairStep.off_qWeil_iff_notMem_supp X _ m z hE hm0, notMem_supp_divOfSec]
    exact hz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialPlaceStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightedMonomialPlace_of_isLocModel : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (r : ℕ) (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ),
    IsNoetherianRing Q → Ideal.span (Set.range z) = IsLocalRing.maximalIdeal Q →
    IsQuasiRegularSeq Q z → wt 0 = 1 → (∀ i, 1 ≤ wt i) →
    ∃ (V : Place c) (hC : V.Contains Q) (u : Fin r → V.ring),
      (∀ i, (u i : L) * (z 0 : L) ^ wt i.succ = z i.succ) ∧
      Irreducible (⟨z 0, hC _ (z 0).2⟩ : V.ring) ∧
      (∀ q ∈ IsLocalRing.maximalIdeal Q,
        (⟨q, hC _ q.2⟩ : V.ring) ∈ IsLocalRing.maximalIdeal V.ring) ∧
      (∀ P : MvPolynomial (Fin r) Q, (∃ α, P.coeff α ∉ IsLocalRing.maximalIdeal Q) →
        IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P)) ∧
      ∀ f : V.ring, ∃ P R : MvPolynomial (Fin r) Q,
        IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R) ∧
        f * MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R =
          MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P := by
  first | exact @GlobalTheory.exists_weightedMonomialPlace | exact GlobalTheory.exists_weightedMonomialPlace | (intros; apply GlobalTheory.exists_weightedMonomialPlace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteBadPlacesPairs
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocTriv

theorem map_starT {A R' C : Type} [CommRing A] [Algebra ℚ A] [CommRing R'] [Algebra ℚ R'] [Ring C] [Algebra ℚ C]
    (σ : C →+* Cᵐᵒᵖ) (f : A →ₐ[ℚ] R') (y : A ⊗[ℚ] C) :
    Algebra.TensorProduct.map f (AlgHom.id ℚ C) (starT σ A y).unop =
      (starT σ R' (Algebra.TensorProduct.map f (AlgHom.id ℚ C) y)).unop := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [starT_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, starT_tmul]; rfl
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

theorem map_conj_ext {p : ℕ} [Fact p.Prime] (G : HTGroup p) (K : Type) [Field K] [Algebra ℚ K] {L : Type} [Field L]
    [Algebra ℚ L] (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L) (β₁ : G.Cˣ)
    (hc : ∀ x, ι (c x) = β₁ * sh G (ι x) * ((β₁⁻¹ : G.Cˣ) : G.C)) (z : K ⊗[ℚ] L) :
    Algebra.TensorProduct.map (AlgHom.id ℚ K) ι (Algebra.TensorProduct.map (AlgHom.id ℚ K) c z) =
      ((1 : K) ⊗ₜ[ℚ] (β₁ : G.C)) * (starT G.star K (Algebra.TensorProduct.map (AlgHom.id ℚ K) ι z)).unop *
        ((1 : K) ⊗ₜ[ℚ] ((β₁⁻¹ : G.Cˣ) : G.C)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, starT_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, AlgHom.id_apply,
      AlgHom.id_apply, hc]
    rfl
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy, mul_add, add_mul]

theorem map_invol {K L : Type} [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L] (c : L →ₐ[ℚ] L)
    (hcc : ∀ x, c (c x) = x) (z : K ⊗[ℚ] L) :
    Algebra.TensorProduct.map (AlgHom.id ℚ K) c (Algebra.TensorProduct.map (AlgHom.id ℚ K) c z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, hcc]; rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem selfDual_conj_eq_one {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [CommRing B] [Algebra R B]
    (ι : B →+* A) (hιR : ∀ r, ι (algebraMap R B r) = algebraMap R A r) (σ : A →+* Aᵐᵒᵖ) (cc : B →+* B) (β₁ : Aˣ)
    (X X₁ : Aˣ) (t t₁ : Rˣ) (a' : B) (m : Bˣ)
    (hc : ι (cc m) = ↑β₁ * (σ (ι m)).unop * ↑β₁⁻¹)
    (h1 : (X : A) * (ι a' * β₁) * (σ X).unop = algebraMap R A t)
    (h2 : (X₁ : A) * β₁ * (σ X₁).unop = algebraMap R A t₁) :
    ((X : A) * ι m * ↑X₁⁻¹) * ((X₁ : A) * ι (algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (↑m⁻¹ * cc ↑m⁻¹)) * ↑X₁⁻¹) *
      (σ ((X : A) * ι m * ↑X₁⁻¹)).unop = 1 := by
  have hs1 : (σ (X₁ : A)).unop * (σ ((X₁⁻¹ : Aˣ) : A)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have ht1 : algebraMap R A ((t₁⁻¹ : Rˣ) : R) * algebraMap R A (t₁ : R) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have k1 : ((X₁⁻¹ : Aˣ) : A) * (σ ((X₁⁻¹ : Aˣ) : A)).unop = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * β₁ := by
    calc ((X₁⁻¹ : Aˣ) : A) * (σ ((X₁⁻¹ : Aˣ) : A)).unop
        = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * (((X₁⁻¹ : Aˣ) : A) * algebraMap R A (t₁ : R) *
            (σ ((X₁⁻¹ : Aˣ) : A)).unop) := by
          rw [← Algebra.commutes (t₁ : R), ← mul_assoc, ← mul_assoc, ht1, one_mul]
      _ = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * ((((X₁⁻¹ : Aˣ) : A) * X₁) * β₁ *
            ((σ X₁).unop * (σ ((X₁⁻¹ : Aˣ) : A)).unop)) := by
          rw [← h2]; simp only [mul_assoc]
      _ = _ := by rw [Units.inv_mul, hs1, one_mul, mul_one]
  have hβ : (β₁ : A) * (σ (ι m)).unop = ι (cc m) * β₁ := by
    rw [hc, mul_assoc, mul_assoc, Units.inv_mul, mul_one]
  have hcm : cc (m : B) * cc ((m⁻¹ : Bˣ) : B) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hmE : (m : B) * (algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (↑m⁻¹ * cc ↑m⁻¹)) * cc m =
      algebraMap R B (↑t⁻¹ * ↑t₁) * a' := by
    calc (m : B) * (algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (↑m⁻¹ * cc ↑m⁻¹)) * cc m
        = algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (((m : B) * ↑m⁻¹) * (cc (m : B) * cc ↑m⁻¹)) := by ring
      _ = _ := by rw [Units.mul_inv, hcm, one_mul, mul_one]
  have hR : ((t₁⁻¹ : Rˣ) : R) * (((t⁻¹ : Rˣ) : R) * (t₁ : R)) * (t : R) = 1 := by
    calc ((t₁⁻¹ : Rˣ) : R) * (((t⁻¹ : Rˣ) : R) * (t₁ : R)) * (t : R)
        = (((t₁⁻¹ : Rˣ) : R) * (t₁ : R)) * (((t⁻¹ : Rˣ) : R) * (t : R)) := by ring
      _ = 1 := by rw [Units.inv_mul, Units.inv_mul, one_mul]
  set E := algebraMap R B (↑t⁻¹ * ↑t₁) * a' * (↑m⁻¹ * cc ↑m⁻¹) with hE
  clear_value E
  have eσ : (σ ((X : A) * ι m * ↑X₁⁻¹)).unop = (σ ((X₁⁻¹ : Aˣ) : A)).unop * (σ (ι m)).unop * (σ X).unop := by
    simp only [map_mul, MulOpposite.unop_mul, mul_assoc]
  rw [eσ]
  calc (X : A) * ι m * ↑X₁⁻¹ * (↑X₁ * ι E * ↑X₁⁻¹) *
        ((σ ((X₁⁻¹ : Aˣ) : A)).unop * (σ (ι m)).unop * (σ X).unop)
      = (X : A) * ι m * (((X₁⁻¹ : Aˣ) : A) * X₁) * ι E * (((X₁⁻¹ : Aˣ) : A) * (σ ((X₁⁻¹ : Aˣ) : A)).unop) *
          (σ (ι m)).unop * (σ X).unop := by simp only [mul_assoc]
    _ = (X : A) * ι m * ι E * (algebraMap R A ((t₁⁻¹ : Rˣ) : R) * (β₁ * (σ (ι m)).unop)) * (σ X).unop := by
          rw [Units.inv_mul, k1, mul_one]; simp only [mul_assoc]
    _ = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * ((X : A) * (ι ((m : B) * E * cc m) * β₁) * (σ X).unop) := by
          rw [hβ, show ι ((m : B) * E * cc m) = ι m * ι E * ι (cc m) by rw [map_mul, map_mul]]
          simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = algebraMap R A ((t₁⁻¹ : Rˣ) : R) * (algebraMap R A (((t⁻¹ : Rˣ) : R) * (t₁ : R)) *
          ((X : A) * (ι a' * β₁) * (σ X).unop)) := by
          rw [hmE, map_mul, hιR]
          simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = 1 := by rw [h1, ← mul_assoc, ← map_mul, ← map_mul, hR, map_one]

theorem exists_finset_of_eventually {p : ℕ} {Q : AwayP p → Prop}
    (h : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), Q v) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v : AwayP p, v.1 ∉ S → Q v := by
  rw [Filter.eventually_cofinite] at h
  refine ⟨(h.image Subtype.val).toFinset, fun v hv => ?_⟩
  by_contra hq
  exact hv ((Set.Finite.mem_toFinset _).2 ⟨v, hq, rfl⟩)

theorem finite_above (p : ℕ) :
    ({v : HeightOneSpectrum ℤ | v.asIdeal = Ideal.span {(p : ℤ)}} : Set (HeightOneSpectrum ℤ)).Finite :=
  Set.Subsingleton.finite fun v hv w hw => HeightOneSpectrum.ext (hv.trans hw.symm)

theorem sh_mul' {p : ℕ} [Fact p.Prime] (G : HTGroup p) (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp [sh]

theorem sh_sh {p : ℕ} [Fact p.Prime] (G : HTGroup p) (x : G.C) : sh G (sh G x) = x := G.star_star x

theorem sh_inv_unit {p : ℕ} [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (hβ : sh G β = β) :
    sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) := by
  have h : sh G β * sh G ((β⁻¹ : G.Cˣ) : G.C) = 1 := by
    rw [← sh_mul', Units.inv_mul, sh_one_eq]
  rw [hβ] at h
  calc sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) * ((β : G.C) * sh G ((β⁻¹ : G.Cˣ) : G.C)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [h, mul_one]


end GlobalTheory.LocTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRationalPointsConjInSupport
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem finite_support_conj_points : ∀ (G H : Type) [Group G] [Group H] (ι : H →* G), Function.Injective ι → ∀ (K' : Subgroup G) (F : G → ℂ), (∀ k ∈ K', ∀ x, F (x * k) = F x) → {q : G ⧸ K' | F q.out ≠ 0}.Finite → ∀ x : G, Finite (ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G) → {h : H | F (x⁻¹ * ι h * x) ≠ 0}.Finite := by
  intro G H _ _ ι hι K' F hF hT x hfin
  have key : ∀ g : G, F ((g : G ⧸ K').out) = F g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K' g
    rw [hk]; exact hF _ k.2 g
  have hL : (ι ⁻¹' ((ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G)).Finite :=
    (Set.finite_coe_iff.mp hfin).preimage hι.injOn
  refine Set.Finite.of_finite_fibers (fun h : H => ((x⁻¹ * ι h * x : G) : G ⧸ K')) (hT.subset ?_) ?_
  · rintro _ ⟨h, hh, rfl⟩
    simp only [Set.mem_setOf_eq] at hh ⊢
    rwa [key]
  · rintro _ ⟨h0, -, rfl⟩
    refine (hL.image (fun k => h0 * k)).subset ?_
    rintro h ⟨-, hh⟩
    refine ⟨h0⁻¹ * h, ?_, by simp⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hh
    have hk : (x⁻¹ * ι h0 * x)⁻¹ * (x⁻¹ * ι h * x) ∈ K' := QuotientGroup.eq.mp hh.symm
    have hk' : x⁻¹ * ι (h0⁻¹ * h) * x ∈ K' := by
      convert hk using 1
      simp [map_mul, map_inv, mul_assoc]
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_inf, MonoidHom.mem_range,
      exists_apply_eq_apply, true_and, Subgroup.mem_map]
    refine ⟨_, hk', ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRestrictedProductEqProdStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_doubleCoset_restrictedProduct_eq_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (T : Subgroup X) (Tv : ∀ v, Subgroup (Y v)), (∀ x, x ∈ T ↔ ∀ v, pf v x ∈ Tv v) → ∀ (F : X → ℂ) (Fv : ∀ v, Y v → ℂ), (∀ x, F x = ∏ᶠ v, Fv v (pf v x)) → (∀ v, ∀ t ∈ Tv v, ∀ y, ∀ k ∈ K v, Fv v (t * y * k) = Fv v y) → (∀ v, {q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)) | Fv v (Quotient.out q) ≠ 0}.Finite) → (∀ᶠ v in cofinite, Fv v 1 = 1 ∧ ∀ y, Fv v y ≠ 0 → ∃ t ∈ Tv v, ∃ k ∈ K v, y = t * k) → ∑ᶠ q : DoubleCoset.Quotient (T : Set X) ((⨅ v, (K v).comap (pf v) : Subgroup X) : Set X), F (Quotient.out q) = ∏ᶠ v, ∑ᶠ q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)), Fv v (Quotient.out q) := by
  first | exact @GlobalTheory.EulerAbs.finsum_doubleCoset_restr | exact GlobalTheory.EulerAbs.finsum_doubleCoset_restr | (intros; apply GlobalTheory.EulerAbs.finsum_doubleCoset_restr <;> assumption)
end

