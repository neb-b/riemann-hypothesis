module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareModelNegSpaceGoodSchroedinger
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FunObj

theorem squareModelW₁_good : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW₁ G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (hJ : X.J = (-1 : D.host.E) • (spW₁ G i j).gram) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∃ co vac dom, Model.IsGood (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co vac ((M.ν (.grid (i : ℕ) (j : ℕ))).map (conjU _ (-1) hJ)) dom) B.ψ := by
  intro D T L sc G μ₀ _hL t i j M hM B hB X Y hJ r s r' s' hX hY
  obtain ⟨co, hco⟩ := GlobalTheory.T.exists_rational_darboux_hermitian_tensor_adeles D.sp.cm.sig B X Y r s r' s' hB hX hY
  have hR : Node.InRange D.R.m (.grid (i : ℕ) (j : ℕ)) := ⟨i.2.le, j.2.le⟩
  have hH := (hM.vtx _ hR).haar_fund
  obtain ⟨dom, hh, hd⟩ := _root_.GlobalTheory.HaarConj.haarConj (spW₁ G i j) (-1) (neg_ne_zero.2 one_ne_zero) hJ _ _ hH.1 hH.2
  let M0 : Model D.sp.cm.sig X Y := ⟨co, fun _ => 0, (M.ν (.grid (i : ℕ) (j : ℕ))).map (conjU _ (-1) hJ), dom⟩
  have hb := GlobalTheory.T.exists_latticeVacuum_finitePlaces_rationalDarboux D.sp.cm.sig B X Y r s r' s' hB hX hY M0 hco
  have hc := _root_.GlobalTheory.StdVacuum.eventually_isVac_indicator D.sp.cm.sig B X Y r s r' s' hB hX hY M0 hco
  refine ⟨co, fun v => if M0.IsVac B.ψ v (Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1)
    then Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1 else (hb v).choose, dom, ?_⟩
  refine ⟨hco, fun v => ?_, ?_, hh, hd⟩
  · change M0.IsVac B.ψ v (if M0.IsVac B.ψ v (Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1)
      then Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1 else (hb v).choose)
    by_cases h : M0.IsVac B.ψ v (Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1)
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact (hb v).choose_spec
  · filter_upwards [hc] with v hv
    exact if_pos hv

end GlobalTheory.FunObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairMembersMemSchwartzBruhat
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.StdPairSB

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_sub_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) k) (hA : ∀ i j, A i j ∈ 𝒪[k])
    (hB : ∀ i j, B i j ∈ 𝒪[k]) (p : 𝒪[k])
    (hAB : ∀ i j, valuation k (B i j - A i j) ≤ valuation k (p : k)) :
    valuation k (B.det - A.det) ≤ valuation k (p : k) := by
  let A' : Matrix (Fin n) (Fin n) 𝒪[k] := Matrix.of fun i j => ⟨A i j, hA i j⟩
  let B' : Matrix (Fin n) (Fin n) 𝒪[k] := Matrix.of fun i j => ⟨B i j, hB i j⟩
  have hA' : A = (algebraMap 𝒪[k] k).mapMatrix A' := by ext i j; rfl
  have hB' : B = (algebraMap 𝒪[k] k).mapMatrix B' := by ext i j; rfl
  have hdvd : ∀ x y : 𝒪[k], valuation k (x : k) ≤ valuation k (y : k) ↔ y ∣ x :=
    fun x y => Valuation.Integers.le_iff_dvd (Valuation.integer.integers (valuation k))
  have key : (Ideal.Quotient.mk (Ideal.span {p})).mapMatrix B' =
      (Ideal.Quotient.mk (Ideal.span {p})).mapMatrix A' := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, ← hdvd]
    simpa [A', B'] using hAB i j
  have h2 : B'.det - A'.det ∈ Ideal.span {p} := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det, key]
  rw [Ideal.mem_span_singleton, ← hdvd] at h2
  rw [hA', hB', ← RingHom.map_det, ← RingHom.map_det]
  exact h2


open Classical in
def gfun (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) {m r : ℕ} (A : Matrix (Fin m) (Fin m) k)
    (B : Matrix (Fin m) (Fin r) k) : ℂ :=
  if h : A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
    (((ν (Units.mk0 _ h.1))⁻¹ : ℂˣ) : ℂ) else 0

theorem prop_of_ne {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c m r : ℕ} {A : Matrix (Fin m) (Fin m) k}
    {B : Matrix (Fin m) (Fin r) k} (h : gfun ν ϖ c A B ≠ 0) :
    A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
  by_contra hP
  exact h (by unfold gfun; rw [dite_eq_right hP])

theorem stable {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ c ν) {m r : ℕ} {A A' : Matrix (Fin m) (Fin m) k}
    {B B' : Matrix (Fin m) (Fin r) k}
    (hP : A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c))
    (hA : ∀ i j, valuation k (A' i j - A i j) ≤ valuation k ((ϖ ^ max c 1 : kˣ) : k))
    (hB : ∀ i j, valuation k (B' i j - B i j) ≤ valuation k ((ϖ ^ max c 1 : kˣ) : k)) :
    (A'.det ≠ 0 ∧ IsGLO A' ∧ ∀ i j, B' i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) ∧
      gfun ν ϖ c A' B' = gfun ν ϖ c A B := by
  obtain ⟨hd0, ⟨hAint, hAdet⟩, hBc⟩ := hP
  have hu : valuation k (ϖ : k) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  have hγc : valuation k ((ϖ ^ max c 1 : kˣ) : k) ≤ valuation k ((ϖ ^ c : kˣ) : k) := by
    simp only [Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_pow_right_of_le_one' hu.le (le_max_left _ _)
  have hγ1 : valuation k ((ϖ ^ max c 1 : kˣ) : k) < 1 := by
    simp only [Units.val_pow_eq_pow_val, map_pow]
    exact pow_lt_one₀ zero_le' hu (by omega)
  have hA'int : ∀ i j, A' i j ∈ 𝒪[k] := by
    intro i j
    have h1 : valuation k (A i j) ≤ 1 := hAint i j
    rw [Valuation.mem_integer_iff, ← sub_add_cancel (A' i j) (A i j)]
    exact Valuation.map_add_le _ ((hA i j).trans hγ1.le) h1
  have hB'c : ∀ i j, B' i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
    intro i j
    rw [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, ← sub_add_cancel (B' i j) (B i j)]
    exact Valuation.map_add_le _ ((hB i j).trans hγc) (hBc i j)
  have hdiff := det_sub_le A A' hAint hA'int ⟨((ϖ ^ max c 1 : kˣ) : k), hγ1.le⟩ hA
  have hdiff1 : valuation k (A'.det - A.det) < valuation k A.det := by
    rw [hAdet]; exact lt_of_le_of_lt hdiff hγ1
  have hdet' : valuation k A'.det = 1 := by
    rw [← sub_add_cancel A'.det A.det, Valuation.map_add_eq_of_lt_right _ hdiff1, hAdet]
  have hd0' : A'.det ≠ 0 := by
    intro h; rw [h, map_zero] at hdet'; exact zero_ne_one hdet'
  refine ⟨⟨hd0', ⟨hA'int, hdet'⟩, hB'c⟩, ?_⟩
  unfold gfun
  rw [dite_eq_left ⟨hd0', ⟨hA'int, hdet'⟩, hB'c⟩, dite_eq_left ⟨hd0, ⟨hAint, hAdet⟩, hBc⟩]
  set u := Units.mk0 A.det hd0
  set u' := Units.mk0 A'.det hd0'
  have hr : ν (u⁻¹ * u') = 1 := by
    apply hν
    refine ⟨?_, ?_⟩
    · simp [u, u', hAdet, hdet']
    · have : ((u⁻¹ * u' : kˣ) : k) - 1 = A.det⁻¹ * (A'.det - A.det) := by
        simp only [u, u', Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
        rw [mul_sub, inv_mul_cancel₀ hd0]
      rw [this, map_mul, map_inv₀, hAdet, inv_one, one_mul]
      exact hdiff.trans hγc
  have hu' : u' = u * (u⁻¹ * u') := by group
  rw [hu', map_mul, hr, mul_one]

theorem isLocallyConstant_gfun {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ c ν) (m r : ℕ) :
    IsLocallyConstant
      (fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k => gfun ν ϖ c q.1 q.2) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨A, B⟩
  have hnh : ∀ x : k, ∀ᶠ y in 𝓝 x, valuation k (y - x) ≤ valuation k ((ϖ ^ max c 1 : kˣ) : k) := by
    intro x
    have ht : Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 0) := by
      simpa using (tendsto_id.sub_const x : Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 (x - x)))
    exact ht (GlobalTheory.SplitWeil.cball_mem_nhds (ϖ ^ max c 1))
  have hev : ∀ᶠ q in 𝓝 (A, B),
      (∀ i j, valuation k ((q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k).1 i j - A i j) ≤
        valuation k ((ϖ ^ max c 1 : kˣ) : k)) ∧
      ∀ i j, valuation k (q.2 i j - B i j) ≤ valuation k ((ϖ ^ max c 1 : kˣ) : k) := by
    refine Filter.Eventually.and ?_ ?_
    · refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
      exact ((continuous_fst.matrix_elem i j).tendsto (A, B)).eventually (hnh (A i j))
    · refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
      exact ((continuous_snd.matrix_elem i j).tendsto (A, B)).eventually (hnh (B i j))
  filter_upwards [hev] with q hq
  by_cases hP : A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)
  · exact (stable hϖ hν hP hq.1 hq.2).2
  · have h0 : gfun ν ϖ c A B = 0 := by unfold gfun; rw [dite_eq_right hP]
    show gfun ν ϖ c q.1 q.2 = gfun ν ϖ c A B
    rw [h0]
    by_contra hne
    refine hP (stable hϖ hν (prop_of_ne hne) (fun i j => ?_) (fun i j => ?_)).1
    · rw [Valuation.map_sub_swap]; exact hq.1 i j
    · rw [Valuation.map_sub_swap]; exact hq.2 i j

theorem integral_of_ne {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) {m r : ℕ}
    {A : Matrix (Fin m) (Fin m) k} {B : Matrix (Fin m) (Fin r) k} (h : gfun ν ϖ c A B ≠ 0) :
    (∀ i j, A i j ∈ 𝒪[k]) ∧ ∀ i j, B i j ∈ 𝒪[k] := by
  obtain ⟨-, ⟨hA, -⟩, hB⟩ := prop_of_ne h
  have hu : valuation k (ϖ : k) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  refine ⟨hA, fun i j => ?_⟩
  rw [Valuation.mem_integer_iff]
  refine (show valuation k (B i j) ≤ valuation k ((ϖ ^ c : kˣ) : k) from hB i j).trans ?_
  simp only [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_one₀ zero_le' hu.le

end Local

end GlobalTheory.StdPairSB

theorem GlobalTheory.StdPairSB.stdPair_mem_SB : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ)
    (c a a' : ℕ), GlobalTheory.SplitFlip.IsUnif ϖ → GlobalTheory.SplitFlip.CondLE ϖ c ν →
      stdA ν ϖ c a a' ∈ SB (Matrix (Fin a) (Fin (a + a')) k) ∧ stdB ν ϖ c a a' ∈ SB (Matrix (Fin a') (Fin (a + a')) k) := by
  intro k _ _ _ _ ν ϖ c a a' hϖ hν
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc1 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₁ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.castAdd a' j)
  have hc2 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₂ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.natAdd a j)
  have hK : ∀ m : ℕ, IsCompact (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin (a + a') => (𝒪[k] : Set k) :
      Set (Matrix (Fin m) (Fin (a + a')) k)) :=
    fun m => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_int k
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : stdA ν ϖ c a a' = (fun q => GlobalTheory.StdPairSB.gfun ν ϖ c q.1 q.2) ∘ fun X => (blk₁ X, blk₂ X) := rfl
    rw [this]
    exact (GlobalTheory.StdPairSB.isLocallyConstant_gfun hϖ hν a a').comp_continuous ((hc1 a).prodMk (hc2 a))
  · refine HasCompactSupport.intro (hK a) fun X hX => ?_
    by_contra hne
    obtain ⟨h1, h2⟩ := GlobalTheory.StdPairSB.integral_of_ne (A := blk₁ X) (B := blk₂ X) hϖ hne
    exact hX fun i _ j _ => Fin.addCases (motive := fun j => X i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
  · have : stdB ν ϖ c a a' = (fun q => GlobalTheory.StdPairSB.gfun ν ϖ c q.1 q.2) ∘ fun Y => (blk₂ Y, blk₁ Y) := rfl
    rw [this]
    exact (GlobalTheory.StdPairSB.isLocallyConstant_gfun hϖ hν a' a).comp_continuous ((hc2 a').prodMk (hc1 a'))
  · refine HasCompactSupport.intro (hK a') fun Y hY => ?_
    by_contra hne
    obtain ⟨h2, h1⟩ := GlobalTheory.StdPairSB.integral_of_ne (A := blk₂ Y) (B := blk₁ Y) hϖ hne
    exact hY fun i _ j _ => Fin.addCases (motive := fun j => Y i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepCharacterUniformiserValueUnitAwayTwist
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

namespace GlobalTheory.TwistStepVal

theorem isAwayUnit_loc {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] (σ : K →+* ℂ)
    (χ : Formalism.L2.Host.HChar L) {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n : I → ℤ} (hinf : χ.HasInf φ n)
    {w : HeightOneSpectrum (𝓞 L)} (hw : χ.UnrAt w) (y : (w.adicCompletion L)ˣ) (hy : Formalism.L2.Host.IsUnifAt w y)
    {m : ℕ} (hm : Ideal.absNorm w.asIdeal ∣ m) {x : K} (hx : σ x = ((χ.loc w y : ℂˣ) : ℂ)) :
    GlobalTheory.Square.IsAwayUnit m x := by
  have hq : 0 < Ideal.absNorm w.asIdeal :=
    Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  refine GlobalTheory.Square.isAwayUnit_of_unitOff_embedding σ x _ m hq hm ?_
  rw [hx, Formalism.L2.Host.HChar.val_eq χ hw y hy]
  exact GlobalTheory.ValUnitLevel.unitOff_val L χ I φ n w _ hinf hw (Ideal.absNorm_mem _)

theorem step_val : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (W : G.Weil) (S : GridChoice W Set.univ) {μ₀ : T},
    Lc.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
      (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      (Lc.C.mu0 j).UnrAt (GlobalTheory.AdelicU.splitPrime τ) → (G.ch.chiH (D.R.m - i)).UnrAt (GlobalTheory.AdelicU.splitPrime τ) →
      GlobalTheory.AdelicU.splitPrime τ ∈ twPl G t →
      ∃ x : D.what₂.LL, D.what₂.embLL x = ((chrW (GlobalTheory.SqStep.chs G i j t).ν τ (unifAt v) : ℂˣ) : ℂ) ∧
        GlobalTheory.Square.IsAwayUnit (Qn G t) x := by
  intro D T Lc sc G W S μ₀ hL hN i j t v τ hμ hχ htw
  rw [GlobalTheory.SqStepArith.chrW_chs G hL]
  have hy : Formalism.L2.Host.IsUnifAt (GlobalTheory.AdelicU.splitPrime τ)
      (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom (unifAt v)) := by
    show Valued.v (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ) ((unifAt v : (Fv D.host.F v)ˣ) : Fv D.host.F v))
      = WithZero.exp (-1 : ℤ)
    rw [GlobalTheory.LFun.SplitTie.valued_complMap τ (GlobalTheory.AdelicU.splitPrime_under τ), GlobalTheory.ChrWUnif.valued_unifAt]
  generalize Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom (unifAt v) = y at hy ⊢
  have hm : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have e : ((nuH G t i j).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) =
      ((Lc.C.mu0 j).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) * ((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ) *
        ((G.ch.chiH (D.R.m - i)).loc (GlobalTheory.AdelicU.splitPrime τ) y : ℂ)⁻¹ := by
    simp [nuH, Formalism.L2.Host.HChar.loc, div_eq_mul_inv]
  obtain ⟨a, ha⟩ := hN.chars.mu0 j (GlobalTheory.AdelicU.splitPrime τ) y
  obtain ⟨b, hb⟩ := hN.chars.xi t (GlobalTheory.AdelicU.splitPrime τ) y
  obtain ⟨c, hc⟩ := hN.chars.chi (D.R.m - i) hm (Nat.sub_le _ _) (GlobalTheory.AdelicU.splitPrime τ) y
  have hQ : 0 < Qn G t := Finset.prod_pos fun w _ =>
    Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hdvd : Ideal.absNorm (GlobalTheory.AdelicU.splitPrime τ).asIdeal ∣ Qn G t :=
    Finset.dvd_prod_of_mem (fun w : HeightOneSpectrum (𝓞 D.host.E) => Ideal.absNorm w.asIdeal) htw
  refine ⟨a * b * c⁻¹, by rw [e, map_mul, map_mul, map_inv₀, ha, hb, hc], ?_⟩
  obtain ⟨n, -, hn⟩ := (Lc.C.isMu0 j).inf
  have ua := isAwayUnit_loc D.what₂.embLL _ hn hμ y hy hdvd ha
  have uc := isAwayUnit_loc D.what₂.embLL _ (G.ch.inf _ hm (Nat.sub_le _ _)) hχ y hy hdvd hc
  obtain ⟨k, hk, hξ⟩ := hL.xi_fin t
  have ub : GlobalTheory.Square.IsAwayUnit (Qn G t) b := by
    refine GlobalTheory.Square.AwayClosure.of_pow_eq_one _ hk (D.what₂.embLL.injective ?_)
    rw [map_pow, hb, map_one, ← Units.val_pow_eq_pow_val]
    have h1 : (Lc.xiH t ^ k).loc (GlobalTheory.AdelicU.splitPrime τ) y = 1 := by
      rw [show Lc.xiH t ^ k = 1 from hξ]; rfl
    rw [← Units.val_one, ← h1]
    simp [Formalism.L2.Host.HChar.loc]
  exact GlobalTheory.Square.AwayClosure.mul (GlobalTheory.Square.AwayClosure.mul ua ub) (GlobalTheory.Square.AwayClosure.inv hQ uc)

end GlobalTheory.TwistStepVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHermitianFormInertPointEqLocalForm
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.InertTens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem quadruple_sum_eq_trace_transpose_mul {L : Type} [CommRing L] {m n : ℕ} (P : Matrix (Fin m) (Fin n) L) (J : Matrix (Fin m) (Fin m) L)
    (K : Matrix (Fin n) (Fin n) L) (Q : Matrix (Fin m) (Fin n) L) :
    ∑ i, ∑ j, ∑ k, ∑ l, P i j * J i k * K j l * Q k l = (Pᵀ * J * Q * Kᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun k _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem trace_orth {L : Type} [Field L] (σL : L →+* L) {m n : ℕ} (J : Matrix (Fin m) (Fin m) L) (K : Matrix (Fin n) (Fin n) L)
    (A : Matrix (Fin m) (Fin m) L) (Bm : Matrix (Fin n) (Fin n) L) (δ : L)
    (hA : Aᵀ * J * A.map σL = 1) (hB : Bmᵀ * K * Bm.map σL = δ • 1) (x y : Matrix (Fin n) (Fin m) L) :
    ((A * xᵀ * Bmᵀ)ᵀ * J * (A * yᵀ * Bmᵀ).map σL * Kᵀ).trace = δ * ((y.map σL)ᵀ * x).trace := by
  have e1 : (A * yᵀ * Bmᵀ).map σL = A.map σL * (y.map σL)ᵀ * (Bm.map σL)ᵀ := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map]
  have e2 : (Bm.map σL)ᵀ * Kᵀ * Bm = δ • 1 := by
    have := congrArg Matrix.transpose hB
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  rw [e1]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have e3 : Bm * (x * Aᵀ) * J * (A.map σL * (y.map σL)ᵀ * (Bm.map σL)ᵀ) * Kᵀ
      = Bm * (x * (Aᵀ * J * A.map σL) * (y.map σL)ᵀ * ((Bm.map σL)ᵀ * Kᵀ)) := by
    simp only [Matrix.mul_assoc]
  rw [e3, hA, Matrix.trace_mul_comm, Matrix.mul_one]
  have e4 : x * (y.map σL)ᵀ * ((Bm.map σL)ᵀ * Kᵀ) * Bm = x * (y.map σL)ᵀ * ((Bm.map σL)ᵀ * Kᵀ * Bm) := by
    simp only [Matrix.mul_assoc]
  rw [e4, e2, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm]

theorem hTens_kap (σ : E →ₐ[F] E) {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (h : w.under (𝓞 F) = v) {σL : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h σL)
    {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E)
    (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (x y : Matrix (Fin n) (Fin m) (w.adicCompletion E)) :
    hTens (cA σ) (incM F JA) (incM F JB) (kap hw h A Bm x) (kap hw h A Bm y) =
      ptAt hw h (∑ i, ∑ j, ∑ k, ∑ l, (A * xᵀ * Bmᵀ) i j * JA.map (algebraMap E (w.adicCompletion E)) i k *
        JB.map (algebraMap E (w.adicCompletion E)) j l * (A * yᵀ * Bmᵀ).map σL k l) := by
  have hr : ∀ (a : E) (z : w.adicCompletion E),
      ptAt hw h z * inclR (F := F) (AF F) a = ptAt hw h (z * algebraMap E (w.adicCompletion E) a) := by
    intro a z
    rw [mul_comm, inclR_mul_ptAt, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hTens, incM, kap_apply, Matrix.map_apply, cA_ptAt hw h σ hc, hr, ← map_mul, map_sum]

end GlobalTheory.InertTens

namespace GlobalTheory.InertTens

theorem hTens_kap_eq_locH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∀ {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin m) (Fin m) (w.adicCompletion E))
      (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (δ : w.adicCompletion E),
      Aᵀ * JA.map (algebraMap E (w.adicCompletion E)) * A.map σL = 1 →
      Bmᵀ * JB.map (algebraMap E (w.adicCompletion E)) * Bm.map σL = δ • 1 →
      ∀ x y, hTens (cA σ) (incM F JA) (incM F JB) (kap hw h A Bm x) (kap hw h A Bm y) =
        ptAt hw h (GlobalTheory.Hk3.locH σL δ (1 : GL (Fin m) (w.adicCompletion E)) (1 : GL (Fin n) (w.adicCompletion E)) x y) := by
  intro F E _ _ _ _ _ σ v w hw h σL hc m n JA JB A Bm δ hA hB x y
  rw [hTens_kap σ hw h hc, quadruple_sum_eq_trace_transpose_mul, trace_orth σL _ _ A Bm δ hA hB x y]
  congr 1
  simp [GlobalTheory.Hk3.locH]

end GlobalTheory.InertTens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftMemMultiplicitySpaceBaseLevel
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaLevelP


set_option maxHeartbeats 1000000 in
theorem thF_mem_conj {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hIs : R.toLevCh.Is A.μ0)
    (hMod : R.IsModels) (hTh : R.IsThP) (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (y : (R.HV i t).H)
    (hy : R.extV i t y ∈ RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i t P))
      (levChi _ (R.βV i) (RecTie.datVP R i t P))) :
    R.thF i t y ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P.conj))
      (levChi _ (R.βW i) (R.datWp i P.conj)) := by
  have hW := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 (hTh.thF_mem i t y)
  refine (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).2 ⟨hW.aut, hW.cusp, fun v k' hk' g => ?_, hW.equiv, hW.cont⟩
  obtain ⟨g0, hl', hc'⟩ := GlobalTheory.LevelRankR.exists_lift_of_mem_level R i P.conj k' hk'
  have hL := (GlobalTheory.StepLifts.lifts_exist R hIs i).1 t
  have hx := hL g0
  clear hL
  rcases hx with ⟨κ, hl⟩
  have h1 := _root_.GlobalTheory.lift_mem_levVP R i t P
  let g1 : P.H := ⟨g0.1, g0.2⟩
  have h3 := h1 g1 κ hl
  clear h1
  have hf0 : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ ≠ 0 := Units.ne_zero _
  have hy' : ∀ k ∈ levS (Vc D i) (R.βV i) (RecTie.datVP R i t P), ∀ h,
      R.extV i t y (h * k) = levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) k • R.extV i t y h := hy
  have e1 := hy' κ h3.1
  have e2 := h3.2
  clear hy' hy h3
  have hnum : (((P.chi g1 : ℂˣ) : ℂ))⁻¹ = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ *
      levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) κ := by
    rw [e2]
    field_simp
  have hsh : ∀ h, R.extV i t ((((P.chi g1 : ℂˣ) : ℂ))⁻¹ • y) h =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ) := by
    intro h
    have e3 : R.extV i t ((((P.chi g1 : ℂˣ) : ℂ))⁻¹ • y) h = (((P.chi g1 : ℂˣ) : ℂ))⁻¹ • R.extV i t y h :=
      congrFun ((R.extV i t).map_smul _ y) h
    refine e3.trans ?_
    refine Eq.trans ?_ (congrArg (fun w => (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • w) (e1 h).symm)
    refine (congrArg (fun a : ℂ => a • R.extV i t y h) hnum).trans ?_
    exact mul_smul _ _ _
  have key := _root_.GlobalTheory.ThetaShiftSmooth.thF_shift_all R hIs hMod hTh i t g0.1 κ k' hl hl' y _ hsh v g
  have hcc : levChi (Wc D i) (R.βW i) (R.datWp i P.conj) k' = (((P.chi g1 : ℂˣ) : ℂ))⁻¹ := by
    rw [hc']
    change (((P.chi⁻¹) g1 : ℂˣ) : ℂ) = _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have e4 : R.thF i t ((((P.chi g1 : ℂˣ) : ℂ))⁻¹ • y) v g = (((P.chi g1 : ℂˣ) : ℂ))⁻¹ * R.thF i t y v g := by
    have e5 := congrFun (congrArg (fun T : MMap (R.MW i (sg0 D A)) => T v) ((R.thF i t).map_smul (((P.chi g1 : ℂˣ) : ℂ))⁻¹ y)) g
    exact e5
  exact key.symm.trans (e4.trans (congrArg (· * R.thF i t y v g) hcc.symm))


set_option maxHeartbeats 1000000 in
theorem thF_mem_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ F : Face D A, R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (b : Bool) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), R.extV i t y ∈ RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i t (R.levR F b))) (levChi _ (R.βV i) (RecTie.datVP R i t (R.levR F b))) → R.thF i t y ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hIs hMod hTh hv b i t y hy
  rw [GlobalTheory.Proof.LevelCharacterConjugate.liftLevel_fixedEmbedding_eq_conj_rowLevel R F b hv]
  exact thF_mem_conj R hIs hMod hTh i t (R.levR F b) y hy

end GlobalTheory.ThetaLevelP
end

