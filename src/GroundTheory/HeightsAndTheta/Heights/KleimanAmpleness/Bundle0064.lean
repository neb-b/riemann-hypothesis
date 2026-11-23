module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Fintype
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0062
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosed
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubringOfInvMem
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0052
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0065

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfIsSubvarAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

theorem exists_ne_zero_of_isSubvar {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} {d : ℕ} (h : Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) d) : ∃ i, x i ≠ 0 := by
  obtain ⟨i, hi⟩ := h.relevant
  refine ⟨i, fun h0 => hi ?_⟩
  change MvPolynomial.X i ∈ RingHom.ker (ReciprocityTheory.ChartRestriction.G.Geo.coneMap F x)
  rw [RingHom.mem_ker]
  simp [ReciprocityTheory.ChartRestriction.G.Geo.coneMap, h0]

theorem VeryAmpleNefPlusAmple.equiv (hBun : BundleOfDeg.Statement) (hNef : ModelNefEq.Statement)
    (hVA : ModelVeryAmpleEq.Statement) (hDim : ModelDimEq.Statement) :
    Kleiman.VeryAmpleNefPlusAmple.Statement.{0, 0} ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmpleNefPlusAmple.Statement := by
  constructor
  · intro hA d F _ K _ _ ι _ Ω _ _ y k₀ hmod hdim μ hnef t ht
    obtain ⟨i₀, -⟩ := hmod.1 k₀
    have hpos : 0 < Fintype.card (ι k₀) := Fintype.card_pos_iff.mpr ⟨i₀⟩
    let e : ι k₀ ≃ Fin (Fintype.card (ι k₀) - 1 + 1) :=
      (Fintype.equivFin _).trans (finCongr (Nat.succ_pred_eq_of_pos hpos).symm)
    obtain ⟨Q, hQ⟩ := hBun F K ι Ω y k₀ _ e hmod μ
    have hs := (hDim F K ι Ω y k₀ _ e hmod d).mpr hdim
    have hn := (hNef F K ι Ω y k₀ _ e hmod μ Q hQ).mpr hnef
    obtain ⟨p, m, hp, hm, hva⟩ := hA F d Ω _ _ Q hs hn t ht
    exact ⟨p, m, hp, hm, (hVA F K ι Ω y k₀ _ e hmod μ Q hQ p m hp).mp hva⟩
  · intro hB k _ d Ω _ _ N x M hs hnef t ht
    have hx := exists_ne_zero_of_isSubvar hs
    obtain ⟨n, hn⟩ := Generated.full.{0, 0} k Ω N x M
    obtain ⟨r, g, -, hg⟩ := GraphClosedAlt.exists_fin_generators
      (M.tensorProd (twistBundle k x n)) (hn n le_rfl)
    have hgen : IsGraphGen M n g := hg
    have hmod := GraphModel.full k N Ω x M n (r + 1) g hx hgen
    have hsec := twist_secs_eq_secOver M n g hgen
    have hdim := (hDim k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock N (Equiv.refl _)
      hmod d).mp hs
    have hnef' := (hNef k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock N (Equiv.refl _)
      hmod (graphDeg n) M hsec).mp hnef
    obtain ⟨a, m, ha, hm, hva⟩ := hB d k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock hmod hdim
      (graphDeg n) hnef' t ht
    exact ⟨a, m, ha, hm, (hVA k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x g) baseBlock N (Equiv.refl _)
      hmod (graphDeg n) M hsec a m ha).mpr hva⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.FoldTensorToSubSystem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

noncomputable section

section Fold

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

def foldTensor {n : ℕ} (L : Fin n → Kleiman.LineBundle S x) (l : List (Fin n)) (Q : Kleiman.LineBundle S x) :
    Kleiman.LineBundle S x :=
  l.foldl (fun P i => P.tensor (L i)) Q

theorem foldTensor_toSubSystem {n : ℕ} (L : Fin n → Kleiman.LineBundle S x) (l : List (Fin n))
    (Q : Kleiman.LineBundle S x) :
    (foldTensor L l Q).toSubSystem = l.foldl (fun P i => P.twist (L i).toSubSystem) Q.toSubSystem := by
  induction l generalizing Q with
  | nil => rfl
  | cons a l ih =>
    rw [foldTensor, List.foldl_cons, List.foldl_cons, ← Kleiman.LineBundle.tensor_toSubSystem]
    exact ih _

end Fold

theorem realises_foldTensor (hT : TensorRealises.Statement)
    {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] [Algebra F Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}
    (hmod : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) {n : ℕ}
    (L : Fin n → Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (δ : Fin n → K → ℤ)
    (hL : ∀ i, BundleRealises y k₀ (L i) (δ i)) (l : List (Fin n)) :
    ∀ (Q : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (β : K → ℤ),
      BundleRealises y k₀ Q β → BundleRealises y k₀ (foldTensor L l Q) (β + (l.map δ).sum) := by
  induction l with
  | nil => intro Q β hQ; simpa [foldTensor] using hQ
  | cons a l ih =>
    intro Q β hQ
    have h := ih (Q.tensor (L a)) (β + δ a) (hT F K ι Ω y k₀ N e hmod Q (L a) β (δ a) hQ (hL a))
    rw [List.map_cons, List.sum_cons, ← add_assoc]
    exact h

theorem TensorRealise.proof (hT : TensorRealises.Statement) : TensorRealise.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod n L δ hL T
  subst hx
  refine Filter.Eventually.of_forall fun c => ?_
  have h0 := BaseRealises.proof F K ι Ω y k₀ N e _ rfl hmod 0
  have h := realises_foldTensor hT hmod L δ hL ((List.finRange n).filter (· ∈ T)) _ _ h0 (c : ℤ)
  rw [foldTensor_toSubSystem, Kleiman.twistBundle_toSubSystem] at h
  have hsum : (((List.finRange n).filter (· ∈ T)).map δ).sum = ∑ i ∈ T, δ i := by
    rw [← List.sum_toFinset δ ((List.nodup_finRange n).filter _)]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp
  rw [hsum, zero_smul, zero_add] at h
  exact h

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelRowExact.proof (hSub : RowSub.Statement) (hZ : CellZeroConst.Statement)
    (hGlue : RowSecGlue.Statement) (hC : CellContract.Statement) (hL : CellLocGlue.Statement)
    (hAct : RowChartAct.Statement) (hCov : RowLocCover.Statement) : ModelRowExact.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM γ J
  refine ⟨fun I hne hI => Submodule.span_le.mpr (hSub F K ι Ω y k₀ N e γ J I hne hI), ?_, ?_⟩
  · intro s hs hd
    choose c₀ hc₀ using hM.1

    let cell : (∀ k, ι k) → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 := fun c =>
      ⟨fun k => {c k}, fun _ => Finset.singleton_nonempty _, by simp⟩
    have hmeet : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → CellMeets y (cell c).1 := by
      intro c hc k i hi
      rw [Finset.mem_singleton.mp hi]
      exact hc k
    refine ⟨s (cell c₀), Submodule.subset_span (hGlue F K ι Ω y k₀ N e γ J _ fun c hc => ?_),
      fun c hc => hZ F K ι Ω y s hd c (cell c₀) hc (hmeet c₀ hc₀)⟩
    rw [← hZ F K ι Ω y s hd (cell c) (cell c₀) (hmeet c hc) (hmeet c₀ hc₀)]
    exact hs (cell c) (Set.mem_univ _)
  · obtain ⟨m, f, u, hf, hu, hsum, hloc⟩ := hCov F K ι Ω y k₀ N e hM γ J
    refine hL F K ι Ω y _ (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J).toSubring m f u hf hu hsum
      (fun I r hr a ha => hAct F K ι Ω y k₀ N e γ J I r a hr ha) fun l => ?_
    obtain ⟨c, hc, h0, hmono, hinv⟩ := hloc l
    exact hC F K ι Ω y _ c hc h0 hmono hinv

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def ModelPoint.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
    ∀ (K' : Type) [Field K'] [Algebra F K'] (y' : (Σ k, ι k) → K'),
      (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → mIdealOver F y ≤ mIdealOver F y' →
      IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

theorem ModelChangeNef.proof (hC : ModelCurves.Statement) (hN : ModelCurveNum.Statement) :
    ModelChangeNef.Statement := by
  have key : ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (N : ℕ)
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
      (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1)),
      IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀' →
      IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm →
      ∀ (β : K → ℤ) (β' : K' → ℤ),
        (∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
            secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) →
        IndefiniteRowSideFullHecke.Kleiman2.IsNef F y β → IndefiniteRowSideFullHecke.Kleiman2.IsNef F y' β' := by
    intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hm hm' hx β β' hs hnef W' hW' hle' hrel'
    obtain ⟨hP, hPle, hPrel⟩ := (hC F K' ι' Ω y' k₀' N e' _ hx hm' 1).1 W' hW' hle' hrel'
    obtain ⟨W, hW, hle, hrel, hWP⟩ := (hC F K ι Ω y k₀ N e _ rfl hm 1).2 _ hP hPle hPrel
    rw [← hN F Ω N K ι y k₀ e K' ι' y' k₀' e' hm hm' hx β β' hs W W' hW hle hrel hW' hle' hrel' hWP]
    exact hnef W hW hle hrel
  intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hm hm' hx β β' hs
  exact ⟨key F Ω N K ι y k₀ e K' ι' y' k₀' e' hm hm' hx β β' hs,
    key F Ω N K' ι' y' k₀' e' K ι y k₀ e hm' hm hx.symm β' β fun c => (hs c).symm⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

def ModelChangeVeryAmple.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (N : ℕ)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀' →
    IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm →
    ∀ (β : K → ℤ) (β' : K' → ℤ),
      (∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
          secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) →
      (IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y β ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y' β')

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

theorem ModelNefEq.proof (hNef : NefEq.Statement) (hCh : ModelChangeNef.Statement) :
    ModelNefEq.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod β Q hQ
  have hx : ∃ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) i ≠ 0 := by
    obtain ⟨i, hi⟩ := hmod.1 k₀
    exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
  obtain ⟨n, hn⟩ := Generated.full.{0, 0} F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Q
  obtain ⟨r, g, -, hg⟩ := GraphClosedAlt.exists_fin_generators
    (Q.tensorProd (twistBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) n)) (hn n le_rfl)
  have hgen : IsGraphGen Q n g := hg
  have hmod' := GraphModel.full F N Ω _ Q n (r + 1) g hx hgen
  have hsec := twist_secs_eq_secOver Q n g hgen
  rw [hNef F N Ω _ Q n (r + 1) g hgen]
  exact (hCh F Ω N K ι y k₀ e (Unit ⊕ Unit) (graphIdx N (r + 1)) _ baseBlock (Equiv.refl _) hmod hmod' rfl
    β (graphDeg n) (fun c => (hQ c).symm.trans (hsec c))).symm

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelCechTwist.proof (hMul : ChartSecMul.Statement) (hBase : BaseRealises.Statement)
    (hLoc : CellLocEval.Statement) (hRef : ModelCechRefine.Statement) : ModelCechTwist.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM β Q hQ p b m c i

  have hbun : ∀ (L : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (δ : K → ℤ),
      BundleRealises y k₀ L δ → ∀ J, (L.sub J : Set Ω) = chartSecOver F y k₀ e δ J := by
    intro L δ hL J
    ext t
    rw [SetLike.mem_coe, mem_sub_iff_gam]
    refine exists_congr fun n => ?_
    rw [Kleiman.SubSystem.gam, hL]
  have hO : ∀ (a : ℤ) J,
      ((Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) a).sub J : Set Ω) =
        chartSecOver F y k₀ e (a • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) J := fun a =>
    hbun (Kleiman.twistBundle F _ a) _ (hBase F K ι Ω y k₀ N e _ rfl hM a)

  have hmul : ∀ (R R' : Kleiman.SubSystem F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Ω) (δ δ' : K → ℤ),
      (∀ J, (R.sub J : Set Ω) = chartSecOver F y k₀ e δ J) →
      (∀ J, (R'.sub J : Set Ω) = chartSecOver F y k₀ e δ' J) →
      ∀ J, ((R.twist R').sub J : Set Ω) = chartSecOver F y k₀ e (δ' + δ) J := by
    intro R R' δ δ' hR hR' J
    rw [twist_sub_eq_mul, Submodule.mul_eq_span_mul_set, hR' J, hR J]
    exact hMul F K ι Ω y k₀ N e hM δ' δ J
  have hpow : ∀ (R : Kleiman.SubSystem F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Ω) (δ : K → ℤ),
      (∀ J, (R.sub J : Set Ω) = chartSecOver F y k₀ e δ J) →
      ∀ (n : ℕ) J, ((R.pow n).sub J : Set Ω) = chartSecOver F y k₀ e (n • δ) J := by
    intro R δ hR n
    induction n with
    | zero =>
      intro J
      have h0 := hO 0 J
      rw [zero_smul] at h0
      rw [zero_smul]
      exact h0
    | succ n ih =>
      intro J
      rw [succ_nsmul']
      exact hmul _ _ _ _ ih hR J
  have hT := hmul _ _ _ _ (hpow _ _ (hmul _ _ _ _ (hpow _ _ (hbun Q β hQ) p) (hO m)) b) (hO c)
  have hγ : c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ + b • (m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ + p • β) =
      b • IndefiniteRowSideFullHecke.Kleiman2.stepL k₀ β p m + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
    simp only [IndefiniteRowSideFullHecke.Kleiman2.stepL]
    module
  rw [hγ] at hT
  obtain ⟨e₁⟩ := hRef F K ι Ω y k₀ N e hM _ _ hT i
  obtain ⟨e₂⟩ := hLoc F K ι Ω y _ i
  exact ⟨e₁.trans e₂⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

theorem ModelCurveNum.proof (hN : CurveNumModel.Statement) : ModelCurveNum.Statement := by
  intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hm hm' hx β β' hs W W' hW hle hrel hW' hle' hrel' hb
  obtain ⟨Q, hQ⟩ := BundleOfDeg.full F K ι Ω y k₀ N e hm β
  have hQ' : BundleRealises y' k₀' Q β' := fun c => (hQ c).trans (hs c)
  have h1 := hN F K ι Ω y k₀ N e _ rfl hm Q β hQ W hW hle hrel
  have h2 := hN F K' ι' Ω y' k₀' N e' _ hx hm' Q β' hQ' W' hW' hle' hrel'
  have hc : W.comap (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) =
      W'.comap (rename fun a : Fin (N + 1) => (⟨k₀', e'.symm a⟩ : Σ k, ι' k)) := by
    ext p
    have := SetLike.ext_iff.mp hb (rename (fun a : Fin (N + 1) => (⟨(), a⟩ : Σ _ : Unit, Fin (N + 1))) p)
    simp only [baseComap, Ideal.mem_comap, rename_rename] at this
    exact this
  rw [h1, h2, hc]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def RealiseRestrict.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω), x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∀ (Q : Kleiman.LineBundle F x) (β : K → ℤ), BundleRealises y k₀ Q β →
      ∀ (K' : Type) [Field K'] [Algebra F K'] (y' : (Σ k, ι k) → K'),
        IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀ → mIdealOver F y ≤ mIdealOver F y' →
        ∀ hxy : (∀ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) i ≠ 0 → x i ≠ 0),
          ∃ (Q' : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm)) (r : Ω → K'),
            Kleiman.RestrictData Q.toSubSystem hxy Q'.toSubSystem r ∧ BundleRealises y' k₀ Q' β

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon IsMGraded quotPart)

def SectionMapInj.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M),
    IsNoetherianRing S → Module.Finite (MRingOver S ι) M → IsMGraded S ι 𝓜 →
    ∃ c₀ : ℤ, ∀ c : K → ℤ, (∀ k, c₀ ≤ c k) → ∀ x ∈ 𝓜 c,
      (∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0, LocalizedModule.mk x (1 : cellMon S I.1) = 0) → x = 0

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OfModelNumEq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelNumEq.proof (hN : NumModel.Statement) : ModelNumEq.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod d βs Qs hsecs hsub
  exact hN F K ι Ω y k₀ N e _ rfl hmod d Qs βs (fun j c => hsecs j c) hsub

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

