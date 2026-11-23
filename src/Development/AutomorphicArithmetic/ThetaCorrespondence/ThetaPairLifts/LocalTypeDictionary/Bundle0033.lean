module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0555
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TendstoSlopeOfArchimedeanPairing
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0029
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LineDerivativeAdditiveInLines
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open Filter Topology
noncomputable section
open scoped Classical
namespace GlobalTheory.LineAdd
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
section
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
end
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
theorem line_sum_curve_eq_prod (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd)
    (hψ : IsStd ψ) (hG : M.IsGood ψ) (hW : M.IsWeil ψ χX χW om)
    {ι : Type} (γs : ι → (Multiplicative ℝ →* UA σ Y.J)) (hγs : ∀ i, γs i ∈ Lines σ Y)
    (r : (Fin n × Fin d → AF F) → ℂ) (hr00 : r 0 ≠ 0) (hr : ∀ f : SInf F (Fin n × Fin d), Rest (evI F) f r)
    (f : SInf F (Fin n × Fin d)) (g : ι → SInf F (Fin n × Fin d))
    (hg : ∀ i, ∃ c : ℝ → SInf F (Fin n × Fin d),
      (∀ t, om (γs i (Multiplicative.ofAdd t), 1) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c t) r) ∧ c 0 = f ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 (g i))) :
    ∀ l : List ι, ∃ c : ℝ → SInf F (Fin n × Fin d),
      (∀ t, om ((l.map fun i => γs i (Multiplicative.ofAdd t)).prod, 1) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c t) r) ∧
      c 0 = f ∧ Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (𝓝[≠] 0) (𝓝 (l.map g).sum) := by
  have hr0 : ∃ x, r x ≠ 0 := ⟨0, hr00⟩
  have canc := GlobalTheory.ArchCancel.eq_of_tens_eq F r (hr f).1 hr0
  have img : ∀ i (h : SInf F (Fin n × Fin d)) (t : ℝ), ∃ k : SInf F (Fin n × Fin d),
      om (γs i (Multiplicative.ofAdd t), 1) (tens (evI F) ⇑h r) = tens (evI F) ⇑k r := by
    intro i h t
    obtain ⟨c, -, hc, -⟩ := _root_.GlobalTheory.T.archimedean_line_pairing_twist hP M ψ χX χW om hψ hG hW (γs i) (hγs i) h r (hr h)
    exact ⟨c t, hc t⟩
  intro l
  induction l with
  | nil =>
    refine ⟨fun _ => f, fun t => ?_, rfl, ?_⟩
    · simp only [List.map_nil, List.prod_nil]
      exact om_one_one om _
    · simp only [sub_self, smul_zero, List.map_nil, List.sum_nil]
      exact tendsto_const_nhds
  | cons i l' ih =>
    obtain ⟨c', hc', hc'0, hlim'⟩ := ih
    obtain ⟨ci, hci, hci0, hlimi⟩ := hg i
    set S' := (l'.map g).sum with hS'
    let s : ℝ → SInf F (Fin n × Fin d) := fun t => if t = 0 then S' else t⁻¹ • (c' t - f)
    choose k hk using fun t => img i (s t) t
    have hs : Tendsto s (𝓝 0) (𝓝 S') := by
      rw [← nhdsNE_sup_pure (0 : ℝ)]
      refine Tendsto.sup ?_ ?_
      · refine hlim'.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [s, if_neg (show t ≠ 0 from ht)]
      · simp only [tendsto_pure_left, s, if_pos rfl]
        exact fun _ => mem_of_mem_nhds
    have hk' : Tendsto k (𝓝 0) (𝓝 S') :=
      _root_.GlobalTheory.T.jointly_continuous_archimedean_weil_action hP M ψ χX χW om hψ hG hW (γs i) (hγs i) r hr00 hr s k S' hk hs
    have hcs : ∀ t, c' t = f + t • s t := by
      intro t
      by_cases ht : t = 0
      · subst ht; simp [hc'0]
      · simp only [s, if_neg ht, smul_smul, mul_inv_cancel₀ ht, one_smul, add_sub_cancel]
    refine ⟨fun t => ci t + t • k t, fun t => ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.prod_cons]
      rw [om_prod_one, hc' t, hcs t, tens_add_smul, map_add (f := _), map_smul, hci t, hk t, tens_add_smul]
    · simp [hci0]
    · simp only [List.map_cons, List.sum_cons]
      refine (hlimi.add (hk'.mono_left nhdsWithin_le_nhds)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : t ≠ 0 := ht
      rw [add_sub_right_comm, smul_add, smul_smul, inv_mul_cancel₀ ht', one_smul]
end GlobalTheory.LineAdd
open GlobalTheory.LineAdd GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem GlobalTheory.LineAdd.deriv_prod_lines_eq_sum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ {ι : Type} (l : List ι) (γs : ι → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)),
    (∀ i, γs i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X) → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, (∀ t, γ t = (l.map fun i => γs i t).prod) →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ (f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (fs : ι → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γs i (Multiplicative.ofAdd t), 1)) f (fs i)) →
    f₁ = (l.map fs).sum := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om a b a' b' hpair ι l γs hγs γ _ hprod f _ f₁ fs hD hDs
  obtain ⟨r, hr00, hr⟩ := GlobalTheory.ThK.exists_rest_inf F (Fin n × Fin d)
  have hψ := hpair.base.std
  have hG := hpair.good
  have hW := hpair.weil
  have canc := GlobalTheory.ArchCancel.eq_of_tens_eq F r (hr f).1 ⟨0, hr00⟩
  choose cs gs hcs hlims using fun i => _root_.GlobalTheory.T.archimedean_line_pairing_twist hP M B.ψ χX χW om hψ hG hW (γs i) (hγs i) f r (hr f)
  have hcs0 : ∀ i, cs i 0 = f := by
    intro i
    refine canc _ _ ?_
    rw [← hcs i 0]
    simp only [ofAdd_zero, map_one]
    exact om_one_one om _
  have hlims' : ∀ i, Tendsto (fun t : ℝ => t⁻¹ • (cs i t - f)) (𝓝[≠] 0) (𝓝 (gs i)) := by
    intro i; simpa [hcs0 i] using hlims i
  have hfs : ∀ i, fs i = gs i := by
    intro i
    refine canc _ _ (funext fun x => ?_)
    exact (hDs i r (hr f) x).unique (hasDerivAt_of_curve (hcs i) (hcs0 i) (hlims' i) x)
  obtain ⟨c, hc, hc0, hlim⟩ := _root_.GlobalTheory.LineAdd.line_sum_curve_eq_prod hP M B.ψ χX χW om hψ hG hW γs hγs r hr00 hr f gs
    (fun i => ⟨cs i, hcs i, hcs0 i, hlims' i⟩) l
  have hc' : ∀ t, om (γ (Multiplicative.ofAdd t), 1) (tens (evI F) ⇑f r) = tens (evI F) ⇑(c t) r := by
    intro t; rw [hprod]; exact hc t
  have e1 : f₁ = (l.map gs).sum := by
    refine canc _ _ (funext fun x => ?_)
    exact (hD r (hr f) x).unique (hasDerivAt_of_curve hc' hc0 hlim x)
  rw [e1]
  congr 1
  exact List.map_congr_left fun i _ => (hfs i).symm
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_derivative_additive_in_lines : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ {ι : Type} (l : List ι) (γs : ι → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)),
    (∀ i, γs i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X) → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, (∀ t, γ t = (l.map fun i => γs i t).prod) →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ (f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (fs : ι → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γs i (Multiplicative.ofAdd t), 1)) f (fs i)) →
    f₁ = (l.map fs).sum := by
  first | exact @_root_.GlobalTheory.LineAdd.deriv_prod_lines_eq_sum | exact _root_.GlobalTheory.LineAdd.deriv_prod_lines_eq_sum | (intros; apply _root_.GlobalTheory.LineAdd.deriv_prod_lines_eq_sum <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LinePolarizationMatchDerivative
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.LineMatch
open Filter GlobalTheory.WeilM GlobalTheory.AdelicU
theorem polarization_match_deriv : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ Φ', GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' →
    ∀ (Φ₁ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ₁' : (Fin a' × Fin (a + a') → AF F) → ℂ),
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) →
    (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ' x) (Φ₁' x) 0) →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ₁ Φ₁' := by
  intro hP F E _ _ _ _ _ σ a a' B G X om om' R Rf hMt γ hγ Φ Φ' hPM Φ₁ Φ₁' hd hd'
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.OscLie.exists_lie_deriv_pol B G X om om' hMt.triple γ hγ
  obtain ⟨δ', hδ'⟩ := _root_.GlobalTheory.T.twist_lie_derivative_model hP B G X om om' hMt.triple γ hγ
  obtain ⟨T, hT, m, m', f, φ, f', φ', hf, hf', rfl, rfl, heq⟩ := hPM
  have hcof : ∀ {κ : Type} (ψs vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ), (∀ v ∉ T, ψs v = vac v) →
      ∀ᶠ v in cofinite, ψs v = vac v := fun ψs vac h =>
    Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun v hv => by
      by_contra h'
      exact hv (h v h'))
  have hpd : ∀ i x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ (f i)) (φ i) x) 0 := fun i x =>
    (hδ (f i) (hf i).1).2 _ (GlobalTheory.T.restricted_finprod_pure_tensor_adelic_schwartz F _ (φ i) (hf i).2.1
      (((hcof _ _ (hf i).2.2).and hMt.triple.geo.hM.std).mono fun v h => h.1.trans h.2) (f i)) x
  have hpd' : ∀ j x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f' j) (φ' j)) x)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ' (f' j)) (φ' j) x) 0 := fun j x =>
    (hδ' (f' j) (hf' j).1).2 _ (GlobalTheory.T.restricted_finprod_pure_tensor_adelic_schwartz F _ (φ' j) (hf' j).2.1
      (((hcof _ _ (hf' j).2.2).and hMt.triple.geo.hM'.std).mono fun v h => h.1.trans h.2) (f' j)) x
  have hΦ₁ : Φ₁ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ (f i)) (φ i) := by
    funext x
    have hs := HasDerivAt.sum (u := Finset.univ) fun i _ => hpd i x
    have e : (∑ i, fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x) =
        fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x := by
      funext t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_apply, map_sum, Finset.sum_apply]
    rw [e] at hs
    rw [(hd x).unique hs, Finset.sum_apply]
  have hΦ₁' : Φ₁' = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ' (f' j)) (φ' j) := by
    funext x
    have hs := HasDerivAt.sum (u := Finset.univ) fun j _ => hpd' j x
    have e : (∑ j, fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f' j) (φ' j)) x) =
        fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) (∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f' j) (φ' j)) x := by
      funext t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_apply, map_sum, Finset.sum_apply]
    rw [e] at hs
    rw [(hd' x).unique hs, Finset.sum_apply]
  have hR := hMt.real
  set P := G.M.Pol B.ψ B.emb with hPdef
  let pP : P →ₗ[ℂ] R.Pi := R.p ∘ₗ P.subtype
  have hsurj : Function.Surjective pP := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype]
    exact hR.quot.onto
  let g : P →ₗ[ℂ] R.Pi := R.p ∘ₗ δ ∘ₗ P.subtype
  have h0' := hδ' 0 (zero_mem _)
  have hker : LinearMap.ker pP ≤ LinearMap.ker g := by
    intro x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    have := hR.lie γ hγ x.1 x.2 0 (zero_mem _) (δ x.1) (δ' 0) (hδ x.1 x.2).2 h0'.2
      (by simpa [pP] using hx)
    simpa [g] using this
  let L : R.Pi →ₗ[ℂ] R.Pi :=
    (LinearMap.ker pP).liftQ g hker ∘ₗ (pP.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hL : ∀ x ∈ P, L (R.p x) = R.p (δ x) := by
    intro x hx
    have e : (pP.quotKerEquivOfSurjective hsurj).symm (R.p x) = Submodule.Quotient.mk ⟨x, hx⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply]
    rfl
  have hL' : ∀ x ∈ G.M'.Pol B.ψ B.emb, L (R.p' x) = R.p' (δ' x) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := (Submodule.eq_top_iff'.mp hR.quot.onto (R.p' x))
    rw [← hyx, hL y hy]
    exact hR.lie γ hγ y hy x hx (δ y) (δ' x) (hδ y hy).2 (hδ' x hx).2 hyx
  subst hΦ₁ hΦ₁'
  refine ⟨T, hT, m, m', fun i => δ (f i), φ, fun j => δ' (f' j), φ',
    fun i => ⟨(hδ (f i) (hf i).1).1, (hf i).2.1, (hf i).2.2⟩,
    fun j => ⟨(hδ' (f' j) (hf' j).1).1, (hf' j).2.1, (hf' j).2.2⟩, rfl, rfl, ?_⟩
  have := congrArg (LinearMap.rTensor _ L) heq
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.rTensor_tmul] at this
  simpa only [hL _ (hf _).1, hL' _ (hf' _).1] using this
end GlobalTheory.LineMatch
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_polarization_match_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ Φ', GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' →
    ∀ (Φ₁ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ₁' : (Fin a' × Fin (a + a') → AF F) → ℂ),
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) →
    (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ' x) (Φ₁' x) 0) →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ₁ Φ₁' := by
  first | exact @_root_.GlobalTheory.LineMatch.polarization_match_deriv | exact _root_.GlobalTheory.LineMatch.polarization_match_deriv | (intros; apply _root_.GlobalTheory.LineMatch.polarization_match_deriv <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemPolarizationStabilizerOfDualPair
section
section
noncomputable section
open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
namespace GlobalTheory.PolActsPf
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.RealActs
section Swap
variable {P Q R S : ℕ}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end Swap
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
section Graph
variable {κ V : Type} [Fintype κ] [AddCommGroup V] [Module ℂ V] {Φ : V →ₗ[ℂ] SInf F κ}
end Graph
theorem mem_polarizationStabilizer_of_dualPair (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {σ : E →ₐ[F] E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype κ] {P Q R S : ℕ} {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w}
    {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ} {a b : ℂ}
    {A : InfinitePlace F → Matrix α (Ix P Q) ℂ} {C : InfinitePlace F → Matrix β (Ix R S) ℂ}
    {Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ} {om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)}
    {θ : InfinitePlace F → Matrix β β ℂ} (hcm : IsCMExt F E σ) (hψ : IsStd ψ) (fr : Framed τ JA JB a b A C)
    (hΦ : IsFockMap ψ τ d A C Φ) (hs : IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om)
    (hθ : ∀ w, θ w * C w = C w * Jm R S) :
    (∀ γ ∈ RLines (σ := σ) JB, DerOn (LinearMap.range Φ) (fun t => om (γ (Multiplicative.ofAdd t)))) ∧
    ∀ k : UG (cA σ) JB, At (evI F) ((k.1 : Matrix β β (AE F E)) - 1) →
      (∀ w, Commute ((k.1 : Matrix β β (AE F E)).map (piInf (τ w))) (θ w)) → OpOn (LinearMap.range Φ) (om k) := by
  have hder : DerEx := _root_.GlobalTheory.HeisDer.derEx
  have hls : LieScalar := _root_.GlobalTheory.T.weil_lie_algebra_scalar_action hP hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder)
  have hgen : GenEx := _root_.GlobalTheory.RealLiftGen.genEx
  have hkl : KLine := kLine_of_lineEx exists_line_of_upq
  obtain ⟨c, hact⟩ := hls F E σ _ _ _ _ _ _ _ ψ τ _ _ d a b A C Φ om hcm hψ fr hΦ hs
  refine ⟨fun γ hγ => ?_, fun k hk hc => ?_⟩
  · obtain ⟨Y, -, hY⟩ := hgen F E σ β R S τ JB b C hcm fr.2.2 γ hγ
    exact derOn_of_sd hΦ.1 _ _ (fun t => map_zero _) (hact γ hγ Y hY)
  · obtain ⟨γ, hγ, Y, hY, hKC, hγ1⟩ := hkl F E σ β R S τ JB b C θ hcm fr.2.2 hθ k hk hc
    have hloc := locFin_sumPl _ _ _ (fun w => locFin_compact P Q R S (Y w) (hKC w) (c w * (Y w).trace))
    obtain ⟨U, -, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F κ _ Φ _ (om.comp γ) hloc
      (fun t l hl => hs.adm _ l hl) (fun T => hact γ hγ Y hY T)
    change ∀ T, SA (om (γ (Multiplicative.ofAdd 1))) (Φ T) (Φ (U T)) at hSA
    rw [hγ1] at hSA
    exact opOn_of_sa hΦ.1 U _ (map_zero _) hSA
theorem polarization_acts_of_isDualPair : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → GlobalTheory.RealActs.PolActs B M om := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  have hb := h.base
  have hfr : FrameEx := _root_.GlobalTheory.RealLift.frameEx_holds
  have hder : DerEx := _root_.GlobalTheory.HeisDer.derEx
  have hfe : FockEx := _root_.GlobalTheory.FockMapEx.fockEx_of_derEx hder
  have hpr : PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws actsLaws hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder)
  choose A hA hAθ using fun w => hfr _ _ _ _ _ (h.herm.sig w) (h.herm.cartan w)
  choose C hC hCθ using fun w => hfr _ _ _ _ _ (h.skew.sig w) (h.skew.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_real, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_real]; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have fr' : Framed B.emb (incM F W.J) (incM F X.J) Complex.I 1 C A := ⟨mul_one _, hC1, hA1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := h.weil
  obtain ⟨d', hd', hB⟩ := hwp.2.1
  have hr' : LinearMap.range (Φ ∘ₗ (flipT (InfinitePlace F) r s r' s').toLinearMap) = M.Pol B.ψ B.emb := by
    rw [LinearEquiv.range_comp, hr]
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.PolActsPf.mem_polarizationStabilizer_of_dualPair hP hb.cm hb.std fr' (isFockMap_flip hΦ hd') hB.1 hAθ
  obtain ⟨h3, h4⟩ := _root_.GlobalTheory.PolActsPf.mem_polarizationStabilizer_of_dualPair hP hb.cm hb.std fr hΦ hwp.1.1 hCθ
  rw [hr'] at h1 h2
  rw [hr] at h3 h4
  exact ⟨fun γ hγ => h1 γ hγ, fun k hk => h2 k hk.1 hk.2, fun γ hγ => h3 γ hγ, fun k hk => h4 k hk.1 hk.2⟩
end GlobalTheory.PolActsPf
end
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualPair_preserves_polarization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → GlobalTheory.RealActs.PolActs B M om := by
  first | exact @_root_.GlobalTheory.PolActsPf.polarization_acts_of_isDualPair | exact _root_.GlobalTheory.PolActsPf.polarization_acts_of_isDualPair | (intros; apply _root_.GlobalTheory.PolActsPf.polarization_acts_of_isDualPair <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSmoothLinePureWeight
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical
theorem GlobalTheory.Twist.twist_smoothLine_isPure : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    ∃ (c : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      (∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c t) φ) ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - c 0)) (𝓝[≠] 0) (𝓝 g) := by
  intro hP F E _ _ _ _ _ σ n d Y Wd M ψ χX χW om hCM hψ hM hW γ hγ f φ hφ hv
  have h1 := fun t : ℝ => GlobalTheory.T.archimedeanPoint_pureTensor_keeps_finiteFactor M ψ χX χW om hψ hM hW (γ (Multiplicative.ofAdd t)) (hγ.2 _) f φ hφ hv
  choose c hc using h1
  by_cases h : ∃ y : Fin n × Fin d → AF F, ∏ᶠ v, φ v (fun i => evFin F v (y i)) ≠ 0
  · obtain ⟨g, hg⟩ := _root_.GlobalTheory.T.pure_tensor_theta_smooth_along_line hP M ψ χX χW om hCM hψ hM hW γ hγ f φ hφ hv h c hc
    exact ⟨c, g, hc, hg⟩
  · push_neg at h
    have h0 : ∀ c' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure c' φ = 0 := fun c' => by
      funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, h x]
    refine ⟨fun _ => 0, 0, fun t => ?_, ?_⟩
    · rw [h0 f, h0 0, map_zero]
    · simp
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_smoothLine_pure_weight : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    ∃ (c : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      (∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c t) φ) ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - c 0)) (𝓝[≠] 0) (𝓝 g) := by
  first | exact @_root_.GlobalTheory.Twist.twist_smoothLine_isPure | exact _root_.GlobalTheory.Twist.twist_smoothLine_isPure | (intros; apply _root_.GlobalTheory.Twist.twist_smoothLine_isPure <;> assumption)
end
end

