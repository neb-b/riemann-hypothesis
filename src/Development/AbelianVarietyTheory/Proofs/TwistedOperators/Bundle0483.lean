module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0473
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0467
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexMovedHomLatticeSplitPlaceChart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

namespace GlobalTheory.SplitIdx

theorem half_index : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → (halfLat S T ε).relIndex ((halfLat S T ε).map (actL S T (embV T v (e.symm (k₁ * t * k₂))))) = qV D.host.E w ^ (S.rank * (∑ i, max (-d i) 0).toNat) := by
  intro D S T v w h hs e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂ ε hε
  obtain ⟨φ, hφ, ⟨BS, hBS⟩, BT, hBT, ψ, hψ, hq, κ, hκ, hco⟩ := GlobalTheory.T.splitPlace_chart_frames_conj_maximalCompact D S T v w h hs e he ε hε
  rw [_root_.GlobalTheory.SplitIdx.relIndex_half_act D S T v φ ε hφ BS BT hBS hBT, hco, ← hq]
  have hback : ∀ x : GL (Fin T.rank) (w.adicCompletion D.host.E),
      GlobalTheory.LFun.SplitTie.glEquiv T.rank ψ
        (Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) x) = x := by
    intro x
    ext i j
    simp [GlobalTheory.LFun.SplitTie.glEquiv]
  have hK : ∀ x ∈ KGL w (n := T.rank),
      Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) x ∈ KGL v (n := T.rank) := by
    intro x hx
    rw [GlobalTheory.LFun.SplitTie.mem_KGL_iff hψ, hback]
    exact hx
  have hunif : IsUnifV D.host.F v (ψ.symm ϖ) := by
    have h1 := hψ (ψ.symm ϖ)
    rw [RingEquiv.apply_symm_apply] at h1
    show Valued.v _ = _
    rw [← h1]
    exact hϖ
  have hdiag : (Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) t).1 =
      Matrix.diagonal (fun i => ψ.symm ϖ ^ d i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [ht, map_zpow₀]
    · simp [ht, Matrix.diagonal_apply, hij]
  have hsplit : ∀ a b c : GL (Fin T.rank) (w.adicCompletion D.host.E),
      κ⁻¹ * Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) (a * b * c) * κ =
        (κ⁻¹ * Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) a) *
          Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) b *
          (Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) c * κ) := by
    intro a b c
    simp only [map_mul, mul_assoc]
  rw [hsplit]
  exact GlobalTheory.T.relIndex_integralMatrices_cartanDouble_coset v T.rank S.rank (ψ.symm ϖ) hunif d _ hdiag _ (mul_mem (inv_mem hκ) (hK k₁ hk₁)) _
    (mul_mem (hK k₂ hk₂) hκ)

theorem index_moved_split : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v (e.symm (k₁ * t * k₂))))) = qV D.host.E w ^ (S.rank * (∑ i, |d i|).toNat) := by
  intro D S T v w h hs e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  obtain ⟨τ, hτ⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (GlobalTheory.AdelicU.isCMExt_host D) hs h
  obtain ⟨ε, hε, -⟩ := GlobalTheory.EmbChart.exists_isIdemAt_chart (D := D) τ
  rw [hτ] at hε
  obtain ⟨w', hne, hunder, -⟩ := GlobalTheory.LFun.SplitChart.exists_conj_place (GlobalTheory.AdelicU.isCMExt_host D) h hs
  have h' : w'.under (𝓞 D.host.F) = v := (hunder w').2 (Or.inr rfl)
  obtain ⟨c, hc, hq', -, he'⟩ := GlobalTheory.LFun.ConjPlace.exists_conj_chart (GlobalTheory.AdelicU.isCMExt_host D)
    (GlobalTheory.Mem.VolExists.isHermND D.sp.cm T) (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D T v) hne h h' he
  have hε' := _root_.GlobalTheory.ConjSplitIdem.isIdemAt_cA_of_ne D v w w' hne h h' ε hε
  rw [GlobalTheory.T.relIndex_movedHomLattice_eq_prod_halves_splitPlace D S T ε hε.1 _ (_root_.GlobalTheory.SuppAtPlace.suppAt_embV D T v w h ε hε (e.symm (k₁ * t * k₂))),
    half_index D S T v w h hs e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂ ε hε]
  have hO := GlobalTheory.LFun.ConjPlace.map_mem_Ov_iff c hc
  have hk : ∀ k ∈ KGL w (n := T.rank), GlobalTheory.LFun.ConjPlace.invT c T.rank k ∈ KGL w' (n := T.rank) := fun k hk =>
    (GlobalTheory.LFun.ConjPlace.mem_iff_invT c hO k).1 hk
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    simp [IsUnifV] at hϖ
  have hmul : t.1 * Matrix.diagonal (fun i => ϖ ^ (-d i)) = 1 := by
    rw [ht, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero]
  have hinv : (t⁻¹).1 = Matrix.diagonal (fun i => ϖ ^ (-d i)) := Units.inv_eq_of_mul_eq_one_right hmul
  have hdiag : (GlobalTheory.LFun.ConjPlace.invT c T.rank t).1 = Matrix.diagonal (fun i => c ϖ ^ (-d i)) := by
    ext i j
    rw [GlobalTheory.LFun.ConjPlace.invT_val, hinv]
    by_cases hij : i = j
    · subst hij
      simp [map_zpow₀]
    · simp [Matrix.diagonal_apply, hij, Ne.symm hij]
  have hunif : IsUnifV D.host.E w' (c ϖ) := by
    show Valued.v (c ϖ) = _
    rw [hc]
    exact hϖ
  have hsym : e.symm (k₁ * t * k₂) = (e.trans (GlobalTheory.LFun.ConjPlace.invT c T.rank)).symm
      (GlobalTheory.LFun.ConjPlace.invT c T.rank k₁ * GlobalTheory.LFun.ConjPlace.invT c T.rank t *
        GlobalTheory.LFun.ConjPlace.invT c T.rank k₂) := by
    rw [MulEquiv.symm_trans_apply, ← map_mul, ← map_mul, MulEquiv.symm_apply_apply]
  have hconj := half_index D S T v w' h' hs _ he' (c ϖ) hunif (fun i => -d i) _ hdiag _ (hk k₁ hk₁) _ (hk k₂ hk₂)
    (cA D ε) hε'
  rw [← hsym] at hconj
  rw [hconj, hq']
  simp only [neg_neg]
  rw [← pow_add, ← mul_add]
  have hA : 0 ≤ ∑ i, max (-d i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
  have hB : 0 ≤ ∑ i, max (d i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
  rw [← Int.toNat_add hA hB, ← Finset.sum_add_distrib]
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm]
  exact max_zero_add_max_neg_zero_eq_abs_self (d i)

end GlobalTheory.SplitIdx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfApprox
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ThLiftCusp

theorem isCuspFun_of_approx {D : D7} (V : HSp D) (f : GA D V → ℂ) (hf : Continuous f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) (N : ℕ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ ψ : GA D V → ℂ, Continuous ψ ∧ (∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) ∧ IsCuspFun V ψ ∧
      ∀ g, ‖ψ g - f g‖ ≤ ε * GlobalTheory.Grow.height V g ^ N) : IsCuspFun V f := by
  choose ψ hψ using fun n : ℕ => h (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  refine GlobalTheory.CuspLimit.isCuspFun_of_tendsto D V N ψ f (fun n => ⟨(hψ n).1, (hψ n).2.1, (hψ n).2.2.1⟩) hf hl ?_
  have hb : ∀ n : ℕ, GlobalTheory.Size.growthSize V N (ψ n - f) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    (GlobalTheory.Size.growthSize_le_iff Nat.one_div_pos_of_nat.le).2 fun g => by simpa using (hψ n).2.2.2 g
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le) hb
  simpa using (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat)

end GlobalTheory.ThLiftCusp

namespace GlobalTheory.ThLiftCusp

theorem norm_lift_sub_le {X H : Type} [MeasurableSpace X] (μ : Measure X) (K K' : H → X → ℂ) (φ φ' : X → ℂ)
    (u : H → ℝ) (w : X → ℝ) (C e δ : ℝ) (hC : 0 ≤ C) (he : 0 ≤ e) (hu : ∀ h, 0 ≤ u h)
    (hK : ∀ h x, ‖K h x‖ ≤ C * u h * w x) (hKK : ∀ h x, ‖K' h x - K h x‖ ≤ e * u h * w x)
    (h1 : Integrable (fun x => w x * ‖φ x‖) μ) (h2 : Integrable (fun x => w x * ‖φ' x - φ x‖) μ)
    (hδ : ∫ x, w x * ‖φ' x - φ x‖ ∂μ ≤ δ)
    (hA : ∀ h, Integrable (fun x => K' h x * φ' x) μ) (hB : ∀ h, Integrable (fun x => K h x * φ x) μ) (h : H) :
    ‖∫ x, K' h x * φ' x ∂μ - ∫ x, K h x * φ x ∂μ‖ ≤ u h * (e * ∫ x, w x * ‖φ x‖ ∂μ + (e + C) * δ) := by
  rw [← integral_sub (hA h) (hB h)]
  have hpt : ∀ x, ‖K' h x * φ' x - K h x * φ x‖ ≤
      u h * (e * (w x * ‖φ x‖) + (e + C) * (w x * ‖φ' x - φ x‖)) := fun x => by
    have e1 : K' h x * φ' x - K h x * φ x =
        (K' h x - K h x) * φ x + (K' h x - K h x) * (φ' x - φ x) + K h x * (φ' x - φ x) := by ring
    rw [e1]
    refine (norm_add₃_le).trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    have a1 := mul_le_mul_of_nonneg_right (hKK h x) (norm_nonneg (φ x))
    have a2 := mul_le_mul_of_nonneg_right (hKK h x) (norm_nonneg (φ' x - φ x))
    have a3 := mul_le_mul_of_nonneg_right (hK h x) (norm_nonneg (φ' x - φ x))
    nlinarith
  have hint : Integrable (fun x => u h * (e * (w x * ‖φ x‖) + (e + C) * (w x * ‖φ' x - φ x‖))) μ :=
    ((h1.const_mul e).add (h2.const_mul (e + C))).const_mul (u h)
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hint
    (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul, integral_add (h1.const_mul e) (h2.const_mul (e + C)), integral_const_mul,
    integral_const_mul]
  exact mul_le_mul_of_nonneg_left (by nlinarith) (hu h)

end GlobalTheory.ThLiftCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteDatumOfHomLatticeCosetSelfDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open NumberField
open GlobalTheory.Grid

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Grid

variable {D : D7}

theorem absNorm_mem_idS (I : Ideal (𝓞 D.host.E)) :
    ((Ideal.absNorm I : ℕ) : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ idS D.host.F I := by
  have : oToS D.host.F D.host.E ((Ideal.absNorm I : ℕ) : 𝓞 D.host.E) ∈ idS D.host.F I :=
    Ideal.mem_map_of_mem _ (Ideal.absNorm_mem I)
  simpa using this

theorem mk_eq_of_eq_add {A : Type} [CommRing A] {R : Subring A} (J : Ideal R) {x y w : A} (hx : x ∈ R) (hy : y ∈ R)
    (hw : w ∈ R) {n : ℕ} (hn : (n : R) ∈ J) (h : x = y + n * w) :
    Ideal.Quotient.mk J ⟨x, hx⟩ = Ideal.Quotient.mk J ⟨y, hy⟩ := by
  rw [Ideal.Quotient.eq]
  have e : (⟨x, hx⟩ - ⟨y, hy⟩ : R) = (n : R) * ⟨w, hw⟩ := by
    apply Subtype.ext
    change x - y = ((n : R) : A) * w
    rw [h]
    push_cast
    ring
  rw [e]
  exact J.mul_mem_right _ hn


open Classical in
theorem isFinVec_of_isCosetVec {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {ε : Bool} {S T : GlobalTheory.Grid.Node D} {e : AE D}
    {P : Finset (Pl D.host.E)} {I : Ideal (𝓞 D.host.E)} (c : GlobalTheory.Grid.Coset S T I) {f₀ f : WO S.V T.V → ℂ}
    (hv : GlobalTheory.Grid.IsVac ψ θ ε S T f₀) (hS : IsSelfDualC S.V S.Λ) (hT : IsSelfDualC T.V T.Λ) (he : IsIdemSum e P)
    (hI : I ≠ ⊥) (hc : GlobalTheory.Grid.IsCosetVec ψ ε S T e I c f₀ f) : GlobalTheory.Grid.IsFinVec ψ θ ε S T f := by
  let φ : Matrix (Fin T.V.rank) (Fin S.V.rank) (Datum.EAf D) → ℂ := fun y =>
    if (∀ i j, ∃ h : y i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Ideal.Quotient.mk (idS D.host.F I) ⟨y i j, h⟩ = cmpS D.host.F I (c i j)) then 1 else 0
  have hfun : cosetInd S T e I c = fun x : WO S.V T.V => if IsHalf e x then φ (frMapO S.V T.V S.β T.β x) else 0 := by
    funext x
    unfold cosetInd
    by_cases hx : IsHalf e x
    · rw [if_pos hx]
      by_cases hx' : InCosetOf S T I c x
      · rw [if_pos ⟨hx, hx'⟩]
        exact (if_pos hx').symm
      · rw [if_neg fun h => hx' h.2]
        exact (if_neg hx').symm
    · rw [if_neg hx, if_neg fun h => hx h.1]
  have hS' := GlobalTheory.FlipPath.isSelfDualC_sgn ε hS
  refine GlobalTheory.FlipPath.isFinVec_of_own hv hS hT he (φ := φ) ⟨?_, ?_⟩
  · rw [← hfun]
    obtain ⟨M, hM, hB⟩ := GlobalTheory.PlaceDatum.exists_den_frMapO (S := sgn ε S.V) hS'.1.fg hT.1.fg S.β T.β
    obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := sgn ε S.V)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS')
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) S.β T.β
    have hN : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
    have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
    have hKN : ((K * Ideal.absNorm I : ℕ) : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ idS D.host.F I := by
      rw [Nat.cast_mul]
      exact Ideal.mul_mem_left _ _ (absNorm_mem_idS I)
    refine ⟨fun t ht => ?_, K * (Ideal.absNorm I * M), Nat.mul_pos hK (Nat.mul_pos hN hM), fun u hu hh t => ?_,
      fun t ht => ?_⟩
    · by_contra h
      exact ht (if_neg fun h' => h h'.1)
    · have hH : IsHalf e (t + (K * (Ideal.absNorm I * M)) • u) ↔ IsHalf e t := by
        refine forall_congr' fun i => forall_congr' fun j => ?_
        have e1 : (t + (K * (Ideal.absNorm I * M)) • u) i j = t i j + ((K * (Ideal.absNorm I * M) : ℕ) : AE D) * u i j := by
          change t i j + (K * (Ideal.absNorm I * M)) • u i j = _
          rw [nsmul_eq_mul]
        rw [e1, mul_add, mul_left_comm, hh i j]
        constructor
        · intro h; exact add_right_cancel h
        · intro h; rw [h]
      have hadd : ∀ i j, frMapO S.V T.V S.β T.β (t + (K * (Ideal.absNorm I * M)) • u) i j =
          frMapO S.V T.V S.β T.β t i j +
            ((K * Ideal.absNorm I : ℕ) : EAf D) * ((M : EAf D) * frMapO S.V T.V S.β T.β u i j) := by
        intro i j
        rw [GlobalTheory.PlaceDatum.frMapO_add, show K * (Ideal.absNorm I * M) = K * Ideal.absNorm I * M from (mul_assoc _ _ _).symm,
          Nat.cast_mul (K * Ideal.absNorm I) M, mul_assoc]
      have hC' : InCosetOf S T I c (t + (K * (Ideal.absNorm I * M)) • u) ↔ InCosetOf S T I c t := by
        refine forall_congr' fun i => forall_congr' fun j => ?_
        have hz : (M : EAf D) * frMapO S.V T.V S.β T.β u i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := hB u hu i j
        have hw : ((K * Ideal.absNorm I : ℕ) : EAf D) * ((M : EAf D) * frMapO S.V T.V S.β T.β u i j) ∈
            Formalism.L2.Herm.intAf D.host.F D.host.E := mul_mem (natCast_mem _ _) hz
        have hmem : frMapO S.V T.V S.β T.β (t + (K * (Ideal.absNorm I * M)) • u) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
            frMapO S.V T.V S.β T.β t i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
          rw [hadd]; exact add_mem_cancel_right hw
        constructor
        · rintro ⟨h1, h⟩
          exact ⟨hmem.1 h1, (mk_eq_of_eq_add _ h1 (hmem.1 h1) hz hKN (hadd i j)).symm.trans h⟩
        · rintro ⟨h2, h⟩
          exact ⟨hmem.2 h2, (mk_eq_of_eq_add _ (hmem.2 h2) h2 hz hKN (hadd i j)).trans h⟩
      unfold cosetInd
      by_cases ht : IsHalf e t ∧ InCosetOf S T I c t
      · rw [if_pos ⟨hH.2 ht.1, hC'.2 ht.2⟩, if_pos ht]
      · rw [if_neg fun h => ht ⟨hH.1 h.1, hC'.1 h.2⟩, if_neg ht]
    · have h : IsHalf e t ∧ InCosetOf S T I c t := by
        by_contra h
        exact ht (if_neg h)
      have hK' := hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf h.1) fun i j => (h.2 i j).1
      rw [mul_nsmul]
      exact nsmul_mem hK' _
  · rw [← hfun]
    exact hc

end GlobalTheory.Grid

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFrameInvMul
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

namespace GlobalTheory.SplitPlaceRed

theorem isFrame_inv_mul {D : D7} {n : ℕ} {L Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (β A : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β Λ)
    (hA : A.1.mulVec '' (Formalism.L2.Herm.hatL (F := D.host.F) L : Set (Fin n → Formalism.IndefR.Lev.EAf D)) =
      (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set (Fin n → Formalism.IndefR.Lev.EAf D))) :
    Formalism.L2.DIV.IsFrame (A⁻¹ * β) L := by
  intro x
  have hAm : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) L ↔ A.1.mulVec z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    intro z
    constructor
    · intro hz
      rw [← SetLike.mem_coe, ← hA]
      exact ⟨z, hz, rfl⟩
    · intro hz
      rw [← SetLike.mem_coe, ← hA] at hz
      obtain ⟨z', hz', e⟩ := hz
      have e2 := congrArg (A⁻¹).1.mulVec e
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.one_mulVec] at e2
      exact e2 ▸ hz'
  rw [hAm, hβ]
  have e : ((A⁻¹ * β)⁻¹).1 = (β⁻¹).1 * A.1 := by
    rw [mul_inv_rev, inv_inv]; rfl
  rw [e, ← Matrix.mulVec_mulVec]


set_option maxHeartbeats 1000000 in
theorem map_intGL_eq {D : D7} (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v)
    (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (A : GA D V) (g : Gv V v)
    (y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : Formalism.L2.DIV.frGL β y = finE V (A * embV V v g * A⁻¹)) :
    Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (Formalism.L2.DIV.intGL D.host.F D.host.E V.rank y) =
      (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.frCo φ ((finE V A)⁻¹ * β))⁻¹ * splitHom D.sp.cm.sig V.gram (GlobalTheory.SplitProjChart.emb φ) g *
        GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.frCo φ ((finE V A)⁻¹ * β) := by
  set Φ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) →* GL (Fin V.rank) (Fv D.host.F v) :=
    Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) with hΦ
  have hfin : ∀ h : GA D V, Φ (finE V h) = Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) (Formalism.L2.Theta.matHom V h) := by
    intro h
    apply Units.ext
    apply Matrix.ext
    intro p q
    show GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((finE V h).1 p q) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ ((Formalism.L2.Theta.matHom V h).1 p q)
    rw [GlobalTheory.LevSplit.finE_val]
    exact GlobalTheory.SplitProjChart.rdE_toEAf φ _
  have hk : Φ (finE V (embV V v g)) = splitHom D.sp.cm.sig V.gram (GlobalTheory.SplitProjChart.emb φ) g := by
    rw [hfin]
    exact GlobalTheory.SplitChartLink.rdA_matHom_embV V φ _
  have hyv : Formalism.L2.DIV.intGL D.host.F D.host.E V.rank y = β⁻¹ * Formalism.L2.DIV.frGL β y * β := by
    show _ = β⁻¹ * (β * _ * β⁻¹) * β
    group
  rw [hyv, hy]
  show _ = (Φ ((finE V A)⁻¹ * β))⁻¹ * _ * Φ ((finE V A)⁻¹ * β)
  simp only [map_mul, map_inv, hk]
  group

end GlobalTheory.SplitPlaceRed

namespace GlobalTheory.SplitPlaceRed


set_option maxHeartbeats 1000000 in
theorem splitRed_frame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (a : GfC V), IsBaseFrame V β Λ N → GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsLatIsom V V (frameLat V) Λ (finE V (a : GA D V)).val → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (PP : Pl D.host.E), (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v → ¬ Formalism.IndefR.Lev.IsConjPl PP PP → (∀ k : Kv V v, finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ St β) → ∃ (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) (ρ : ResF v ≃+* kP PP), ∀ (k : Kv V v) (i j : Fin V.rank), (redFn β PP (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V))).1 i j = ρ ((s.red k).1 i j) := by
  intro D V β Λ N a hB hL v PP hv hc hst

  have hcc : Formalism.IndefR.Lev.IsConjPl PP (Formalism.L2.DIV.conjPl PP) := by
    intro c hc'
    refine ⟨Formalism.L2.DIV.starO c, ?_, Formalism.L2.DIV.starO_coe c⟩
    show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO c) ∈ PP.asIdeal
    rw [Formalism.L2.DIV.starO_starO]
    exact hc'
  have hne : PP ≠ Formalism.L2.DIV.conjPl PP := fun e => hc (by
    have := hcc
    rw [← e] at this
    exact this)
  have hv' : (Formalism.L2.DIV.conjPl PP).under (𝓞 D.host.F) = v :=
    (GlobalTheory.LevelPlaces.under_eq_of_isConjPl hcc).symm.trans hv
  obtain ⟨τ, hτ, -⟩ := existsUnique_splitPrime_eq (isCMExt_host D) hne hv hv'
  set φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v := splitProj τ with hφ
  have hemb : GlobalTheory.SplitProjChart.emb φ = τ := by
    ext x; simp [hφ, GlobalTheory.SplitProjChart.emb, splitProj]

  have hfr := isFrame_inv_mul β (finE V (a : GA D V)) hB.1 hL.2
  have hsb := GlobalTheory.ChartStab.isSplitBasis_frCo hfr φ
  let s : SplitAt D.sp.cm.sig V.gram (frameLat V) v :=
    ⟨GlobalTheory.SplitProjChart.emb φ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.frCo φ ((finE V (a : GA D V))⁻¹ * β), isCMExt_host D,
      GlobalTheory.ChartStab.hermND D V, GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat_of_cm D.sp.cm V v, hsb⟩
  have hP : splitPrime (GlobalTheory.SplitProjChart.emb φ) = PP := hemb ▸ hτ
  let ρ : ResF v ≃+* kP PP :=
    (splitResidueEquiv (GlobalTheory.SplitProjChart.emb φ)).symm.trans (Ideal.quotEquivOfEq (congrArg HeightOneSpectrum.asIdeal hP))
  refine ⟨s, ρ, fun k i j => ?_⟩
  obtain ⟨y, hy⟩ := hst k
  have hg0 : ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) = (a : GA D V) * embV V v (k : Gv V v) * (a : GA D V)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_locFin, Subgroup.coe_inv]
  rw [← hy, redFn_frGL]
  rw [hg0] at hy
  show resS D.host.F PP (y.1 i j) = ρ ((s.red k).1 i j)

  have hg : ∀ x : 𝓞 D.host.E, ((ρ : ResF v →+* kP PP).comp ((IsLocalRing.residue _).comp (GlobalTheory.PlaceRed.rdS φ)))
      (oToS D.host.F D.host.E x) = Ideal.Quotient.mk PP.asIdeal x := by
    intro x
    simp only [RingHom.comp_apply, GlobalTheory.PlaceRed.rdS_oToS]
    have e1 : GlobalTheory.PlaceRed.rdO φ x = splitInt (GlobalTheory.SplitProjChart.emb φ) x := Subtype.ext rfl
    rw [e1, ← splitResidueEquiv_mk]
    show Ideal.quotEquivOfEq (congrArg HeightOneSpectrum.asIdeal hP) ((splitResidueEquiv _).symm (splitResidueEquiv _ _)) = _
    rw [RingEquiv.symm_apply_apply, Ideal.quotEquivOfEq_mk]
  rw [← GlobalTheory.PlaceRed.eq_resS PP _ hg]
  show ρ (IsLocalRing.residue _ (GlobalTheory.PlaceRed.rdS φ (y.1 i j))) = ρ ((s.red k).1 i j)
  congr 1
  have hred : (s.red k).1 i j = IsLocalRing.residue _ ((stabLocEquiv (isCMExt_host D) (GlobalTheory.ChartStab.hermND D V)
      (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat_of_cm D.sp.cm V v) hsb k).1 i j) := by
    show (splitRed _ _ _ _ k).1 i j = _
    rw [splitRed_val]; rfl
  rw [hred]
  congr 1
  apply Subtype.ext
  rw [coe_stabLocEquiv, splitEquivIn_apply]
  exact congrArg (fun m : GL (Fin V.rank) (Fv D.host.F v) => m.1 i j) (map_intGL_eq V φ β (a : GA D V) (k : Gv V v) y hy)

end GlobalTheory.SplitPlaceRed
end

