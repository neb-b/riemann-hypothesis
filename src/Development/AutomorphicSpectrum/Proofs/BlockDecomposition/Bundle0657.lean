module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0652
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.WordSpan
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0012
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0654
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffle
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspShuffle

open Zc.Comb

variable {α β : Type*}

theorem interleave_filter (f : β → α) (q : β → Bool) (P : List β) :
    Interleave ((P.filter q).map f) ((P.filter fun p => !q p).map f) (P.map f) := by
  induction P with
  | nil => exact Zc.Comb.Interleave.nil
  | cons p P ih =>
    cases hq : q p with
    | true =>
      simp only [List.filter_cons, hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        List.map_cons]
      exact Zc.Comb.Interleave.left ih
    | false =>
      simp only [List.filter_cons, hq, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
        List.map_cons]
      exact Zc.Comb.Interleave.right ih

theorem shuffle_range (f : β → α) (c : β → ℕ) (n : ℕ) : ∀ (s : ℕ) (P : List β),
    (∀ p ∈ P, s ≤ c p ∧ c p < s + n) →
      Shuffle ((List.range' s n).map fun i => (P.filter fun p => c p = i).map f) (P.map f) := by
  induction n with
  | zero =>
    intro s P hP
    have hnil : P = [] := List.eq_nil_iff_forall_not_mem.mpr fun p hp => by
      have := hP p hp
      omega
    subst hnil
    exact Zc.Comb.Shuffle.nil
  | succ n ih =>
    intro s P hP
    simp only [List.range'_succ, List.map_cons]
    refine Zc.Comb.Shuffle.cons (v := (P.filter fun p => !decide (c p = s)).map f) ?_
      (GlobalTheory.CompanionTheory.CuspShuffle.interleave_filter f (fun p => decide (c p = s)) P)
    have h := ih (s + 1) (P.filter fun p => !decide (c p = s)) (by
      intro p hp
      rw [List.mem_filter] at hp
      have h1 := hP p hp.1
      have hne : c p ≠ s := by simpa using hp.2
      omega)
    convert h using 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range'_1] at hi
    rw [List.filter_filter]
    congr 1
    apply List.filter_congr
    intro p _
    by_cases hc : c p = i
    · have his : i ≠ s := by omega
      simp [hc, his]
    · simp [hc]

theorem shuffle_of_colouring {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (D : Fin h → List α)
    (hD : ∀ i, Zc.Cos.sub W c i = D i) : Shuffle (List.ofFn D) W := by
  have key := GlobalTheory.CompanionTheory.CuspShuffle.shuffle_range W.get (fun p => (c p : ℕ)) h 0 (List.finRange W.length)
    (fun p _ => ⟨Nat.zero_le _, by simpa using (c p).isLt⟩)
  convert key using 1
  · apply List.ext_getElem
    · simp
    · intro i h1 h2
      rw [List.getElem_ofFn, List.getElem_map, List.getElem_range', ← hD]
      unfold Zc.Cos.sub
      congr 1
      apply List.filter_congr
      intro p _
      simp [Fin.ext_iff]
  · apply List.ext_getElem <;> simp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem decWord_eq_decW (Δ : Segment k) : Zc.Cos.decWord Δ = decW Δ := by
  unfold Zc.Cos.decWord Zc.M.decW
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_reverse, List.getElem_ofFn, List.getElem_ofFn]
    congr 1
    ext
    simp only [Fin.val_rev, List.length_ofFn]
    omega

theorem inShW_of_wd {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hL : LSegJacquet k) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hd : ∑ a, (x a).1 = N) (Δ : Fin h → Segment k) (hΔ : ∀ i, IsLSeg (Δ i) (x i).rep) (w : List (IrrGL (k := k)))
    (hc : ∀ c ∈ w, c.IsCusp) (hw : Wd (prodIrr x hd) w) : InShW (Finset.univ.val.map Δ) w := by
  obtain ⟨hsum, hne⟩ := hw
  have hmult := GlobalTheory.T.segment_product_jacquet_shuffle_count hA hL Δ x hd hΔ w hc
  have hpos : Zc.Cos.jmL w (GlobalTheory.LocGL.prodIrr x hd) ≠ 0 := by
    unfold Zc.Cos.jmL
    rw [dite_eq_left hsum]
    exact hne
  rw [hmult] at hpos
  have hcard : Zc.Cos.shuffleCount w (fun i => Zc.Cos.decWord (Δ i)) ≠ 0 := by exact_mod_cast hpos
  unfold Zc.Cos.shuffleCount at hcard
  obtain ⟨col, hcol⟩ := Finset.card_ne_zero.mp hcard
  have hcol' : ∀ i, Zc.Cos.sub w col i = Zc.Cos.decWord (Δ i) := by simpa using hcol
  unfold Zc.M.InShW
  refine ⟨List.ofFn Δ, ?_, ?_⟩
  · rw [Fin.univ_val_map]
  · rw [List.map_ofFn]
    have e : (Zc.M.decW ∘ Δ) = fun i => Zc.Cos.decWord (Δ i) :=
      funext fun i => (GlobalTheory.CompanionTheory.CuspShuffle.decWord_eq_decW (Δ i)).symm
    rw [e]
    exact GlobalTheory.CompanionTheory.CuspShuffle.shuffle_of_colouring w col _ hcol'

end GlobalTheory.CompanionTheory.CuspShuffle

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SuccAboveCastSuccCastSucc
section
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeSM

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem qminor_restrict {n m t : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (ι : Fin m → Fin n)
    (hι : Function.Injective ι) (a b : Fin t → Fin m) (w : ℂ) :
    qminor (fun a b => E (ι a) (ι b)) a b w = qminor E (ι ∘ a) (ι ∘ b) w := by
  unfold qminor Tm
  simp only [Function.comp, hι.eq_iff]

end GlobalTheory.CompanionTheory.RgHeSM
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralContinuous
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.BigCellJ

theorem integrable_schwartzA {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} {μ : Measure (Mx D m n)}
    {𝓕 : Set (Mx D m n)} (hμ : IsCovolOne (ratMx D m n) μ 𝓕) {φ : Mx D m n → ℂ}
    (hφ : φ ∈ schwartzA θ m n) : Integrable φ μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.TowerRestrict.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := hμ.1
  haveI i6 : DiscreteTopology (ratMx D m n) := i5
  haveI : SecondCountableTopology (ratMx D m n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hc : Continuous φ := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ φ hφ).1
  have hU : GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.UnifSummable (ratMx D m n).subtype φ := fun Q hQ => by
    obtain ⟨b, hb1, hb2⟩ := GlobalTheory.CompanionTheory.ThetaPoisson.translates_bound hθ ⟨φ, hφ⟩ Q hQ
    refine ⟨b, hb1, fun c x hx => ?_⟩
    have h := hb2 x hx c
    rwa [add_comm] at h
  exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs.integrable_of_unif hc hU μ hK fun x => by
    obtain ⟨γ, hγ, h⟩ := hKc x
    refine ⟨⟨-γ, (ratMx D m n).neg_mem hγ⟩, ?_⟩
    simpa [sub_neg_eq_add, add_comm] using h

theorem continuous_halfTr {D : D7} : Continuous (halfTr : AE D → AF D.host.F) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (trA : AE D → AF D.host.F) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  unfold halfTr
  exact continuous_const.mul ht

theorem continuous_integral_twist {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {μ : Measure Y} {φ : Y → ℂ} {g : X → Y → ℂ} (hi : Integrable φ μ)
    (hj : Continuous fun p : X × Y => g p.1 p.2) (hn : ∀ b y, ‖g b y‖ = 1) :
    Continuous fun b => ∫ y, φ y * g b y ∂μ := by
  have hg1 : ∀ b, AEStronglyMeasurable (g b) μ := fun b =>
    (hj.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hg2 : ∀ y, Continuous fun b => g b y := fun y =>
    hj.comp (continuous_id.prodMk continuous_const)
  refine continuous_of_dominated (bound := fun y => ‖φ y‖) (fun b => ?_) (fun b => ?_) hi.norm ?_
  · exact hi.aestronglyMeasurable.mul (hg1 b)
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_mul, hn, mul_one]
  · refine Filter.Eventually.of_forall fun y => ?_
    exact (hg2 y).const_mul (φ y)

theorem continuous_inner_self {D : D7} (V : HSp D) (r : ℕ) :
    Continuous fun y : Mx D V.rank r => (GlobalTheory.StdUnn.inner V y y : Mx D r r) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  unfold GlobalTheory.StdUnn.inner
  exact GlobalTheory.MixModel.continuous_adj.matrix_mul (continuous_const.matrix_mul continuous_id)

theorem continuous_phase {D : D7} (V : HSp D) (r : ℕ) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) :
    Continuous fun p : hermA D r × Mx D V.rank r =>
      ψ (halfTr (Matrix.trace (HMul.hMul p.1.1 (GlobalTheory.StdUnn.inner V p.2 p.2) : Mx D r r))) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact hψ.1.comp (continuous_halfTr.comp
    ((continuous_subtype_val.comp continuous_fst).matrix_mul
      ((continuous_inner_self V r).comp continuous_snd)).matrix_trace)

theorem jt_continuous : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (Mx D V.rank r)) (φ : Mx D V.rank r → ℂ), IsCharAF D.host.F ψ → IsInfFam θ →
    (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → φ ∈ schwartzA θ V.rank r → Continuous (Jt ψ V μ φ) := by
  intro D r V ψ θ μ φ hψ hθ ⟨𝓕, hμ⟩ hφ
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D r r
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D r) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : FirstCountableTopology (hermA D r) :=
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  exact continuous_integral_twist (g := fun (b : hermA D r) (y : Mx D V.rank r) =>
      ψ (halfTr (Matrix.trace (HMul.hMul b.1 (GlobalTheory.StdUnn.inner V y y) : Mx D r r))))
    (integrable_schwartzA hθ hμ hφ) (continuous_phase V r hψ) (fun b y => hψ.2.1 _)

end GlobalTheory.CompanionTheory.BigCellJ

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

abbrev rt (ξ : Matrix (Fin ρ) (Fin p) D.host.E) : Mx D ρ p := ξ.map (incA D)

def chv (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (x y : Mx D ρ p) : ℂ :=
  ψ (trA (Matrix.trace (pr b₀ x y)))

def jc (y x : Mx D ρ p) : hermA D ρ :=
  ⟨(HMul.hMul y (adj x) : Mx D ρ ρ) + (HMul.hMul x (adj y) : Mx D ρ ρ), by
    have key : ∀ a b : Mx D ρ p, adj (HMul.hMul a (adj b) : Mx D ρ ρ) = (HMul.hMul b (adj a) : Mx D ρ ρ) := by
      intro a b
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul,
        Formalism.L2.Theta.cA_cA]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    show adj _ = _
    have : adj ((HMul.hMul y (adj x) : Mx D ρ ρ) + (HMul.hMul x (adj y) : Mx D ρ ρ)) = adj (HMul.hMul y (adj x) : Mx D ρ ρ) + adj (HMul.hMul x (adj y) : Mx D ρ ρ) := by
      ext i j
      simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]
    rw [this, key, key, add_comm]⟩

def dsum (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ : Mx D ρ p → ℂ) (x y : Mx D ρ p) : ℂ :=
  ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, chv ψ b₀ x (rt ξ) * Φ (rt ξ + y)

def Ap (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ φ : Mx D ρ p → ℂ) (v : Mx D ρ p × Mx D ρ p) : ℂ :=
  dsum ψ b₀ Φ v.2 v.1 * conj (dsum ψ b₀ φ v.2 v.1)

theorem th_zero (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (φ : Mx D ρ p → ℂ) (x y : Mx D ρ p) :
    th ψ b₀ φ 0 x y = dsum ψ b₀ φ x y := by
  have h0 : chz ψ b₀ (0 : hermA D ρ) = 1 := by
    have : (Matrix.trace (HMul.hMul (b₀.1.map (incA D)) (0 : hermA D ρ).1 : Mx D ρ ρ)) = 0 := by
      simp
    rw [chz, this]
    simp [halfTr, trA]
  rw [th, h0, one_mul]
  rfl

theorem tsum_meas {ι X : Type} [Countable ι] [MeasurableSpace X] {f : ι → X → ℂ}
    (hf : ∀ i, StronglyMeasurable (f i)) (hs : ∀ a, Summable fun i => f i a) :
    StronglyMeasurable fun a => ∑' i, f i a := by
  refine stronglyMeasurable_of_tendsto (u := (atTop : Filter (Finset ι)))
    (f := fun (s : Finset ι) a => ∑ i ∈ s, f i a) (fun s => ?_) ?_
  · exact Finset.stronglyMeasurable_fun_sum _ fun i _ => hf i
  · exact tendsto_pi_nhds.2 fun a => (hs a).hasSum

end GlobalTheory.CompanionTheory.FJE
end
end

