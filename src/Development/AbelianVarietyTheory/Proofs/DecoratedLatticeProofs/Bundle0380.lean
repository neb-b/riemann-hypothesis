module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricDoubleIntegralFiniteCombination

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalSumAndHyperbolicSumSpaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.OrthSumSp

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def col {V W : HSpace E} {k : ℕ} (X : Matrix (Fin V.rank) (Fin k) E) (Y : Matrix (Fin W.rank) (Fin k) E) :
    Matrix (Fin (GlobalTheory.Doubling.hsum V W).rank) (Fin k) E :=
  (Matrix.fromRows X Y).submatrix finSumFinEquiv.symm id

theorem col_gram {V W : HSpace E} {k l : ℕ} (X : Matrix (Fin V.rank) (Fin k) E) (Y : Matrix (Fin W.rank) (Fin k) E)
    (X' : Matrix (Fin V.rank) (Fin l) E) (Y' : Matrix (Fin W.rank) (Fin l) E) :
    (col X Y)ᴴ * (GlobalTheory.Doubling.hsum V W).gram * col X' Y' = Xᴴ * V.gram * X' + Yᴴ * W.gram * Y' := by
  rw [GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat, col, col, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  simp

def orthSumDec (D : D7) (A L : HSp D) : OrthDec (GlobalTheory.Doubling.hsum A L) A L where
  iA := col 1 0
  iB := col 0 1
  isoA := by rw [col_gram]; simp
  isoB := by rw [col_gram]; simp
  orth := by rw [col_gram]; simp
  rank_add := rfl

@[reducible] def posSp (D : D7) (ρ : ℕ) : HSp D where
  V := Fin ρ → D.host.E
  hT := Formalism.BasicNotions.Examples₂.diagForm ρ (fun _ => false)
  herm := Formalism.BasicNotions.Examples₂.diagForm_isSymm ρ _
  nondeg := Formalism.BasicNotions.Examples₂.diagForm_nondeg ρ _
  rank := ρ
  rank_eq := Module.finrank_fin_fun _
  frame := Pi.basisFun _ _
  sig := fun _ => (ρ, 0)
  L0 := Formalism.BasicNotions.Examples₂.stdLat ρ
  standardTuple_isLattice := Formalism.BasicNotions.Examples₂.stdLat_isLattice ρ
  baseLattice_isUnimodular := Formalism.BasicNotions.Examples₂.stdLat_unimod Formalism.BasicNotions.Examples₂.star_isIntegral ρ _

theorem posSp_sigOK (D : D7) (ρ : ℕ) : (posSp D ρ).SigOK :=
  Formalism.BasicNotions.Examples₂.posSpace_sigOK (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral ρ

theorem posSp_gram (D : D7) (ρ : ℕ) : (posSp D ρ).gram = 1 := by
  funext i j
  rw [Matrix.one_apply]
  refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral ρ (fun _ => false) ρ 0 i j).trans ?_
  simp [Formalism.BasicNotions.Examples₂.sgn]

@[reducible] def hypSp (D : D7) (ρ : ℕ) : HSp D :=
  GlobalTheory.Doubling.hdbl (posSp D ρ)

theorem hypSp_sigOK (D : D7) (ρ : ℕ) : (hypSp D ρ).SigOK :=
  GlobalTheory.Doubling.sigOK_hdbl (posSp_sigOK D ρ)

theorem hypSp_sig (D : D7) (ρ : ℕ) (τ) : (hypSp D ρ).sig τ = (ρ, ρ) := by
  show (ρ, 0) + (0, ρ) = (ρ, ρ)
  simp

def hypSumDec (D : D7) (A : HSp D) (ρ : ℕ) : HypDec (GlobalTheory.Doubling.hsum A (hypSp D ρ)) A ρ where
  e := col 0 (col (1 : Matrix (Fin ρ) (Fin ρ) D.host.E) (1 : Matrix (Fin ρ) (Fin ρ) D.host.E))
  e' := col 0 (col ((2 : D.host.E)⁻¹ • (1 : Matrix (Fin ρ) (Fin ρ) D.host.E)) (-((2 : D.host.E)⁻¹ • (1 : Matrix (Fin ρ) (Fin ρ) D.host.E))))
  i₀ := col 1 0
  ee := by
    rw [col_gram, col_gram, GlobalTheory.Doubling.gram_hneg, posSp_gram]; simp
  e'e' := by
    rw [col_gram, col_gram, GlobalTheory.Doubling.gram_hneg, posSp_gram]; simp
  e'e := by
    rw [col_gram, col_gram, GlobalTheory.Doubling.gram_hneg, posSp_gram]
    simp [Matrix.smul_eq_diagonal_mul, ← two_mul]
  iso := by rw [col_gram]; simp
  i₀e := by rw [col_gram]; simp
  i₀e' := by rw [col_gram]; simp
  rank_add := by show A.rank + 2 * ρ = A.rank + (ρ + ρ); omega

theorem exists_orthSum_hypSum : ∀ (D : D7), (∀ A L : HSp D, A.SigOK → L.SigOK → ∃ (S : HSp D) (_ : OrthDec S A L), S.SigOK ∧ ∀ τ, S.sig τ = A.sig τ + L.sig τ) ∧ ∀ (A : HSp D) (ρ : ℕ), A.SigOK → ∃ (S : HSp D) (_ : HypDec S A ρ), S.SigOK ∧ ∀ τ, S.sig τ = A.sig τ + (ρ, ρ) := by
  intro D
  refine ⟨fun A L hA hL => ⟨_, orthSumDec D A L, GlobalTheory.Doubling.sigOK_hsum hA hL, fun τ => rfl⟩,
    fun A ρ hA => ⟨_, hypSumDec D A ρ, GlobalTheory.Doubling.sigOK_hsum hA (hypSp_sigOK D ρ), fun τ => ?_⟩⟩
  show A.sig τ + (hypSp D ρ).sig τ = _
  rw [hypSp_sig]

end GlobalTheory.OrthSumSp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPeriodIdealLocalGeneratorAtSplitPoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open NumberField

noncomputable section

namespace GlobalTheory.FinPl.LocGen

theorem half_diff_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h1 := D.host.𝔟_spec.1
  rw [h, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  have hb0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (half_diff_ne_bot D)
  have hc0 : ((D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
    rw [Host.ccE, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact D.host.ccK_ne_bot
  exact mul_ne_zero hc0 (inv_ne_zero hb0)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_incA_int (q : SplitPt D k) (x : 𝓞 D.host.E) : q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := by
  have h1 : IsIntegral ℤ (q.pr (incA D (x : D.host.E))) := (x.2).map ((q.pr.comp (incA D)).toIntAlgHom)
  have h2 : IsIntegral 𝒪[k] (q.pr (incA D (x : D.host.E))) := h1.tower_top
  exact (Valuation.integer.integers (valuation k)).mem_of_integral h2

theorem exists_gen : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k), ∃ a₀ ∈ (D.host.AA : Set D.host.E), q.pr (incA D a₀) ≠ 0 ∧
      ∀ a ∈ (D.host.AA : Set D.host.E), q.pr (incA D a) / q.pr (incA D a₀) ∈ 𝒪[k] := by
  intro D k _ _ _ _ q
  classical
  set π : D.host.E →+* k := q.pr.comp (incA D) with hπ
  have hinj : Function.Injective π := π.injective
  have hfg : ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E)).FG :=
    FractionalIdeal.fg_unit (Units.mk0 D.host.AA (AA_ne_zero D))
  obtain ⟨s, hs⟩ := hfg
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply AA_ne_zero D
    rw [← FractionalIdeal.coeToSubmodule_eq_bot, ← hs]; simp
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun x => valuation k (π x)) hsne
  have hjmem : j ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) := hs ▸ Submodule.subset_span hj
  have hj0 : π j ≠ 0 := by
    intro h0
    apply AA_ne_zero D
    rw [← FractionalIdeal.coeToSubmodule_eq_bot, ← hs, Submodule.span_eq_bot]
    intro i hi
    have h1 := hmax i hi
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h1
    exact hinj (h1.trans π.map_zero.symm)
  refine ⟨j, hjmem, hj0, ?_⟩
  intro a ha
  have ha' : a ∈ Submodule.span (𝓞 D.host.E) (s : Set D.host.E) := hs.symm ▸ ha
  change π a / π j ∈ 𝒪[k]
  clear ha
  induction ha' using Submodule.span_induction with
  | mem x hx =>
    rw [Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ (hmax x hx) zero_le'
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), add_div]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [Algebra.smul_def, map_mul, mul_div_assoc]
    exact mul_mem (pr_incA_int q r) hx

end GlobalTheory.FinPl.LocGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRatOfSameOrb
section
open NumberField IsDedekindDomain Matrix ValuativeRel Formalism.L2.Col
open scoped Classical

namespace GlobalTheory.QPl.RatOrb
open GlobalTheory.StepData GlobalTheory.SplitWeil GlobalTheory.TwBridge.Lev GlobalTheory.TwBridge.LevOrb

theorem image_val_mem_nhds {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {B : Type} [Fintype B] [DecidableEq B] {S : Set (GL B k)} (hS : IsOpen S) {h : GL B k} (hh : h ∈ S) :
    Units.val '' S ∈ nhds h.val := by
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hS
  have hd : h.val.det ≠ 0 := h.det_ne_zero
  have hc : ContinuousAt (Inv.inv : Matrix B B k → Matrix B B k) h.val := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hd
  have hG : ContinuousAt (fun N : Matrix B B k => (N, MulOpposite.op N⁻¹)) h.val :=
    continuousAt_id.prodMk (MulOpposite.continuous_op.continuousAt.comp hc)
  have key : ∀ u : GL B k, Units.embedProduct _ u = (u.val, MulOpposite.op u.val⁻¹) := fun u => by
    rw [Units.embedProduct_apply, Matrix.coe_units_inv]
  have h1 := hG.preimage_mem_nhds (hW.mem_nhds (by rw [← key]; exact hh))
  have h2 : {N : Matrix B B k | N.det ≠ 0} ∈ nhds h.val :=
    (isOpen_ne.preimage (continuous_id.matrix_det)).mem_nhds hd
  filter_upwards [h1, h2] with N hN1 hN2
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero N hN2, ?_, rfl⟩
  rw [Set.mem_preimage, key]
  exact hN1

theorem exists_rat_of_sameOrb : ∀ {E k : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl P (qOf P) ι ϖ → ∀ {A : Type} [Fintype A] [DecidableEq A] {n : ℕ} (e : A ≃ Fin n) (Jl : Subgroup (GL (A ⊕ Fin 0) k)), IsOpen (Jl : Set (GL (A ⊕ Fin 0) k)) → Jl ≤ GlobalTheory.SplitWeil.KO k (A ⊕ Fin 0) → ∀ (M : ℕ) (c : (A → k) ⧸ GlobalTheory.StepData.box A (ϖ ^ M)) (y₀ : Sp E n), GlobalTheory.QPl.SameOrb Jl (GlobalTheory.StepData.box A (ϖ ^ M)) c (Submodule.Quotient.mk fun a => ι (y₀ (e a))) → ∃ r ∈ GLint E n P, ∃ g ∈ Jl, g.val.toBlocks₁₁ = GlobalTheory.SymBridge.toLoc ι e e r.toLinearMap ∧ ∀ y : Sp E n, ((qOf P : E) ^ M)⁻¹ • (r.symm y - y₀) ∈ stdAt E n P → c = Submodule.Quotient.mk fun a => ι (y (e a)) := by
  intro E k _ _ _ _ _ _ _ P ι ϖ hc A _ _ n e Jl hJo hJ M c y₀
  rintro ⟨g₀, hg₀, y₁, rfl, hy⟩
  rw [Submodule.Quotient.eq] at hy
  let e' : A ⊕ Fin 0 ≃ Fin n := (Equiv.sumEmpty A (Fin 0)).trans e
  have he : ∀ a, e' (.inl a) = e a := fun a => rfl
  have h0 : (g₀⁻¹).val.toBlocks₁₁ *ᵥ (fun a => ι (y₀ (e a))) - y₁ ∈ box A (ϖ ^ M) := by
    have := neg_mem (GlobalTheory.TwBridge.LevOrb.mulVec_mem_box (hJ (inv_mem hg₀)) _ hy)
    rwa [mulVec_sub, mulVec_mulVec, ← CoupStab.toBlocks₁₁_mul, Units.inv_mul, CoupStab.toBlocks₁₁_one, one_mulVec,
      neg_sub] at this
  have hU2 : IsOpen {N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k |
      N.toBlocks₁₁ *ᵥ (fun a => ι (y₀ (e a))) - y₁ ∈ box A (ϖ ^ M)} := by
    refine (CoupStab.isOpen_box (ϖ ^ M)).preimage (f := fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k =>
      N.toBlocks₁₁ *ᵥ (fun a => ι (y₀ (e a))) - y₁) ?_
    have hb : Continuous fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k => N.toBlocks₁₁ :=
      continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (Sum.inl i) (Sum.inl j)
    exact (hb.matrix_mulVec continuous_const).sub continuous_const
  obtain ⟨U, hU, hUo, hUm⟩ := mem_nhds_iff.1 (image_val_mem_nhds hJo (inv_mem hg₀))
  obtain ⟨M₀, ⟨a1, a2⟩, -⟩ := exists_approx ι hc.dense (g₀⁻¹).val (hUo.inter hU2) ⟨hUm, h0⟩
  obtain ⟨g, hg, ev⟩ := hU a1
  obtain ⟨r, hr⟩ := exists_phi ι e' M₀ g ev
  refine ⟨r, (GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO P ι hc.int e' r).2 ?_, g, hg, ?_, fun y hy' => ?_⟩
  · rw [show GlobalTheory.VolBridge.locHom ι e' r = phi ι e' r from Units.ext rfl, hr]
    exact hJ hg
  · rw [← hr]
    rfl
  · have h1 := GlobalTheory.TwBridge.LevOrb.mulVec_mem_box (hJ hg) _ ((mem_box_iff hc e M _).2 hy')
    rw [Set.mem_setOf_eq, ← ev] at a2
    rw [← hr, phi_mulVec e e' he] at h1 a2
    rw [eq_comm, Submodule.Quotient.eq]
    convert add_mem h1 a2 using 1
    ext a
    simp only [Pi.sub_apply, Pi.add_apply, map_sub, LinearEquiv.apply_symm_apply]
    abel

end GlobalTheory.QPl.RatOrb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionIffPattern
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

namespace GlobalTheory.SymRes

theorem exists_red_iff_isPat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {O : Type} [CommRing O] (I : Ideal O) (π : O →+* k) (h : GlobalTheory.FunObj.Comparison₂.IsRed (Ideal.Quotient.mk I) π)
    {s κ r : ℕ} (hr : r = κ + (s + 1)) (S : GlobalTheory.SymChain.SymData k s κ) (g : GL (Fin r) (O ⧸ I)) :
    (∃ x : S.P.J, ∀ (a b : Fin κ ⊕ Fin (s + 1)) (a' b' : Fin r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a →
      b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : O, Ideal.Quotient.mk I z = g.val a' b' →
      valuation k ((x : GL (Fin κ ⊕ Fin (s + 1)) k).val a b - π z) < 1) ↔ IsPat S.ρ κ g := by
  subst hr
  let e : Fin κ ⊕ Fin (s + 1) ≃ Fin (κ + (s + 1)) := finSumFinEquiv
  have he : ∀ a, (e a).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a := by
    rintro (a | a) <;> simp [e, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos]
  have hfree : ∀ a b, FreePos S.ρ κ (e a).val (e b).val ↔ GlobalTheory.SymChain.FreeTop S.ρ a b := by
    intro a b
    rw [he, he]
    rcases a with a | a <;> rcases b with b | b <;>
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos, Sum.elim_inl, Sum.elim_inr, GlobalTheory.SymChain.FreeTop, FreePos, Fin.lt_def] <;>
      have := a.2 <;> have := b.2 <;> omega
  choose l hl using fun a b => Ideal.Quotient.mk_surjective (I := I) (g.val (e a) (e b))
  have key : ∀ a b, g.val (e a) (e b) = (1 : Matrix _ _ (O ⧸ I)) (e a) (e b) ↔
      valuation k (π (l a b) - (1 : Matrix _ _ k) a b) < 1 := by
    intro a b
    have h4 := h.ker (l a b - if a = b then 1 else 0)
    rw [map_sub, map_sub, sub_eq_zero, apply_ite (Ideal.Quotient.mk I), apply_ite π, map_one, map_one, map_zero,
      map_zero, hl] at h4
    rw [Matrix.one_apply, Matrix.one_apply]
    simp only [e.apply_eq_iff_eq]
    convert h4
  constructor
  · rintro ⟨x, hx⟩ i j hij
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    have h1 := hx a b _ _ (he a) (he b) _ (hl a b)
    have h2 := ((GlobalTheory.SymChain.SymData.mem_J_iff_pattern k s κ S x.1).1 x.2).2 a b (fun h' => hij ((hfree a b).2 h'))
    have h3 := (valuation k).map_sub_lt h2 h1
    rw [sub_sub_sub_cancel_left] at h3
    exact (key a b).2 h3
  · intro hg
    have hM : (Matrix.of l).map (Ideal.Quotient.mk I) = g.val.submatrix e e := Matrix.ext hl
    have hu : IsUnit ((Matrix.of l).map (Ideal.Quotient.mk I)).det := by
      rw [hM, det_submatrix_equiv_self]
      convert (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    obtain ⟨x, hx1, hx2⟩ := (h.isUnit_det_iff _).1 hu
    have hx3 : ∀ a b, x.val a b = π (l a b) := fun a b => congrFun (congrFun hx2 a) b
    refine ⟨⟨x, (GlobalTheory.SymChain.SymData.mem_J_iff_pattern k s κ S x).2 ⟨by convert hx1, fun a b hab => ?_⟩⟩, ?_⟩
    · rw [hx3]
      exact (key a b).1 (hg _ _ fun h' => hab ((hfree a b).1 h'))
    · intro a b a' b' ha hb z hz
      obtain rfl : a' = e a := Fin.ext (ha.trans (he a).symm)
      obtain rfl : b' = e b := Fin.ext (hb.trans (he b).symm)
      change valuation k (x.val a b - π z) < 1
      rw [hx3, ← map_sub, ← h.ker, map_sub, hl, hz, sub_self]

end GlobalTheory.SymRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionOfMemLevelZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.SeeSaw.LevRed

open GlobalTheory.LocMod GlobalTheory.StepData GlobalTheory.SymChain

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_mul' (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one' (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem finE_val' (V : HSp D) (g : GA D V) : (Lev.finE V g).val = (mt V g).map (toEAf D) := rfl

theorem exists_lift (z : EAf D) : ∃ w : AE D, toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul b α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩

theorem frGL_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    (Formalism.L2.DIV.frGL β y).val * β.val = β.val * (Formalism.L2.DIV.intGL F E n y).val := by
  have h0 : Formalism.L2.DIV.frGL β y * β = β * Formalism.L2.DIV.intGL F E n y := inv_mul_cancel_right _ _
  rw [← Units.val_mul, h0, Units.val_mul]

theorem eq_map_of_moved {S K n : Type} [CommRing S] [CommRing K] [Fintype n] [DecidableEq n] (π : S →+* K) (β : GL n S)
    (x y : Matrix n n S) (h1 : x * β.val = β.val * y) (T T' H N M : Matrix n n K) (hT : T' * T = 1)
    (hN : T * β.val.map π = N) (hM : H * N = N * M) (hx : T * x.map π = H * T) : M = y.map π := by
  have h2 : x.map π * β.val.map π = β.val.map π * y.map π := by rw [← Matrix.map_mul, h1, Matrix.map_mul]
  have h3 : N * M = N * y.map π := by
    rw [← hM, ← hN, Matrix.mul_assoc _ _ (y.map π), ← h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hx]
  have h4 : ((β⁻¹).val.map π * T') * N = 1 := by
    rw [← hN, Matrix.mul_assoc, ← Matrix.mul_assoc T', hT, Matrix.one_mul, ← Matrix.map_mul,
      Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  calc M = ((β⁻¹).val.map π * T') * (N * M) := by rw [← Matrix.mul_assoc, h4, Matrix.one_mul]
    _ = y.map π := by rw [h3, ← Matrix.mul_assoc, h4, Matrix.one_mul]


set_option maxHeartbeats 1000000 in
theorem red_of_movedTo (q : SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (t h : GA D V) (N M : Matrix (Fin V.rank) (Fin V.rank) k)
    (hN : MovedTo (ofSplit q) V t β N) (hM : (mt V h).map q.pr * N = N * M)
    (hx : Lev.finE V (t⁻¹ * h * t) ∈ Formalism.L2.DIV.St β) (i j : Fin V.rank) (z : 𝓞 D.host.E)
    (hz : Ideal.Quotient.mk PP.asIdeal z = (Formalism.L2.DIV.redFn β PP (Lev.finE V (t⁻¹ * h * t))).val i j) :
    valuation k (M i j - (ofSplit q).pr (z : D.host.E)) < 1 := by
  obtain ⟨π', hπ, hred, -⟩ := _root_.GlobalTheory.FinPl.SplitPt.exists_lift_isRed D k q PP hPP
  obtain ⟨y, hy⟩ := hx
  rw [← hy, Formalism.L2.DIV.redFn_frGL] at hz
  choose l hl using exists_lift (D := D)
  have hπ' : ∀ m : Matrix (Fin V.rank) (Fin V.rank) (AE D), (m.map (toEAf D)).map π' = m.map q.pr := fun m => by
    ext a b; exact hπ _
  have hb : (β.val.map l).map (toEAf D) = β.val := by ext a b; exact hl _
  have hN' : (mt V t).map q.pr * β.val.map π' = N := by
    rw [← hN _ hb, Matrix.map_mul]
    congr 1
    conv_lhs => rw [← hb]
    exact hπ' _
  let ψ := π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype
  have h1 : (Lev.finE V (t⁻¹ * h * t)).val * β.val = β.val * (Formalism.L2.DIV.intGL D.host.F D.host.E _ y).val := by
    have h0 := frGL_mul β y
    rw [hy] at h0
    exact h0
  have hfin : (Lev.finE V (t⁻¹ * h * t)).val.map π' = (mt V (t⁻¹ * h * t)).map q.pr := by
    rw [finE_val', hπ']
  have h5 := eq_map_of_moved π' β _ _ h1 ((mt V t).map q.pr) ((mt V t⁻¹).map q.pr) _ N M
    (by rw [← Matrix.map_mul, ← mt_mul', inv_mul_cancel, mt_one', Matrix.map_one _ (map_zero _) (map_one _)]) hN' hM
    (by
      rw [hfin, ← Matrix.map_mul, ← Matrix.map_mul, ← mt_mul', ← mt_mul', mul_assoc, mul_inv_cancel_left])
  have h7 : M i j = ψ (y.val i j) := congrFun (congrFun h5 i) j
  have h6 : (ofSplit q).pr (z : D.host.E) = ψ (Formalism.L2.DIV.oToS D.host.F D.host.E z) := (hπ _).symm
  rw [h7, h6, ← map_sub, ← hred.ker, map_sub, Formalism.L2.DIV.resS_oToS, hz]
  exact sub_self _

end GlobalTheory.SeeSaw.LevRed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiProductMapHaarFiniteOnCompacts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR

theorem finite_on_compacts_prodRFJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), 1 ≤ ρ → ρ < c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → IsFiniteMeasureOnCompacts (((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)).map (prodRFJ ρ)) := by
  intro k _ _ _ _ _ _ n _ _ c ρ hp hpc ν hν m hm
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  haveI := QuotLinear.finiteOnCompacts_volN (n := n) (c := c) (p := ρ + 1) ν
  haveI : LocallyCompactSpace (N k n c (ρ + 1)) :=
    (QuotLinear.isClosed_N (k := k) (n := n) (c := c) (p := ρ + 1)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c (ρ + 1)) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsLocallyFiniteMeasure (volN ν n c (ρ + 1)) := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite (volN ν n c (ρ + 1)) := sigmaFinite_of_locallyFinite
  haveI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite ν := sigmaFinite_of_locallyFinite
  set M := (m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν) with hM
  haveI : IsFiniteMeasureOnCompacts M := by rw [hM]; infer_instance
  refine ⟨fun K hK => ?_⟩
  obtain ⟨D, hD, hD'⟩ := GlobalTheory.RootEx.ProperTriple.proper_triple k n c ρ hp hpc _ (hK.image continuous_subtype_val)
  have hD2 : IsCompact ((fun w : GL n k × N k n c (ρ + 1) × (n → k) => ((w.1, w.2.1), w.2.2)) '' D) :=
    hD.image (by fun_prop)
  have hsub : prodRFJ ρ ⁻¹' K ⊆ (fun w : GL n k × N k n c (ρ + 1) × (n → k) => ((w.1, w.2.1), w.2.2)) '' D := by
    intro z hz
    exact ⟨(z.1.1, z.1.2, z.2), hD' _ ⟨_, hz, rfl⟩, rfl⟩
  by_cases hf : AEMeasurable (prodRFJ (k := k) (n := n) (c := c) ρ) M
  · rw [Measure.map_apply_of_aemeasurable hf hK.isClosed.measurableSet]
    exact (measure_mono hsub).trans_lt hD2.measure_lt_top
  · by_cases hzero : M = 0
    · simp [hzero]
    · rw [Measure.map_of_not_aemeasurable_of_ne_zero hf hzero]
      exact measure_lt_top _ _

end GlobalTheory.HaarR
end
end

