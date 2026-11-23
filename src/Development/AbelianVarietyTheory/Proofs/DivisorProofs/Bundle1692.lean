module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1675
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLocalDarbouxCoordinatesBounded
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000

namespace GlobalTheory.LatVacBdd

theorem exists_ne_zero_mul_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (S : Finset (v.adicCompletion F)) :
    ∃ c : v.adicCompletion F, c ≠ 0 ∧ ∀ a ∈ S, c * a ∈ v.adicCompletionIntegers F := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert b S hb ih =>
    obtain ⟨c, hc0, hc⟩ := ih
    by_cases hcb : c * b ∈ v.adicCompletionIntegers F
    · refine ⟨c, hc0, ?_⟩
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hcb
      · exact hc a ha
    · have hinv : (c * b)⁻¹ ∈ v.adicCompletionIntegers F :=
        ((v.adicCompletionIntegers F).mem_or_inv_mem (c * b)).resolve_left hcb
      have hcb0 : c * b ≠ 0 := fun h => hcb (h ▸ zero_mem _)
      refine ⟨c * (c * b)⁻¹, mul_ne_zero hc0 (inv_ne_zero hcb0), ?_⟩
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · rw [mul_assoc, mul_comm _ a, ← mul_assoc, mul_inv_cancel₀ hcb0]; exact one_mem _
      · rw [mul_comm c, mul_assoc]; exact mul_mem hinv (hc a ha)

end GlobalTheory.LatVacBdd

theorem GlobalTheory.LatVacBdd.locCo_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v : Pl (F := F), ∃ c : Fv F v, c ≠ 0 ∧ ∀ γ ∈ latAtV G.V G.W v, ∀ k,
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).1 k ∈ HeightOneSpectrum.adicCompletionIntegers F v ∧
      c * (GlobalTheory.LatVac.locCo G.M.co v γ).2 k ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v
  classical
  choose yf zf hyz using hT.geo.hM.rat
  obtain ⟨sX, hsX⟩ := hT.geo.hV.lat.fg.restrictScalars (R := ℤ)
  obtain ⟨sY, hsY⟩ := hT.geo.hW.lat.fg.restrictScalars (R := ℤ)
  let f : (Fin a → E) →ₗ[ℤ] (Fin (a + a') → E) →ₗ[ℤ] Matrix (Fin a) (Fin (a + a')) E :=
    LinearMap.mk₂ ℤ (fun x y => Matrix.vecMulVec x y)
      (fun x x' y => by ext i j; simp [Matrix.vecMulVec_apply, add_mul])
      (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply, mul_assoc])
      (fun x y y' => by ext i j; simp [Matrix.vecMulVec_apply, mul_add])
      (fun c x y => by ext i j; simp [Matrix.vecMulVec_apply, mul_left_comm])
  let T₀ : Finset (Matrix (Fin a) (Fin (a + a')) E) := Finset.image₂ (fun x y => f x y) sX sY
  have hmem : ∀ x ∈ G.V.L, ∀ y ∈ G.W.L, Matrix.vecMulVec x y ∈ Submodule.span ℤ (T₀ : Set _) := by
    intro x hx y hy
    have hx' : x ∈ Submodule.span ℤ (sX : Set (Fin a → E)) := by
      rw [hsX]; exact hx
    have hy' : y ∈ Submodule.span ℤ (sY : Set (Fin (a + a') → E)) := by
      rw [hsY]; exact hy
    have := Submodule.apply_mem_map₂ f hx' hy'
    rw [Submodule.map₂_span_span] at this
    rw [Finset.coe_image₂]; exact this
  have hgen : latAtV G.V G.W v ≤ AddSubgroup.closure {z | ∃ b : AF F,
      At (evFin F v) b ∧ evFin F v b ∈ v.adicCompletionIntegers F ∧ ∃ t ∈ T₀, z = b • incM F t} := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨b, hb, hbv, x, hx, y, hy, rfl⟩
    let g : Matrix (Fin a) (Fin (a + a')) E →+ Matrix (Fin a) (Fin (a + a')) (AE F E) :=
      (DistribSMul.toAddMonoidHom _ b).comp
        (AddMonoidHom.mapMatrix (inclR (F := F) (E := E) (AF F)).toAddMonoidHom)
    have h1 : Matrix.vecMulVec x y ∈ AddSubgroup.closure (T₀ : Set _) := by
      rw [← Submodule.span_int_eq_addSubgroupClosure]; exact hmem x hx y hy
    have h2 : g (Matrix.vecMulVec x y) ∈ (AddSubgroup.closure (T₀ : Set _)).map g :=
      AddSubgroup.mem_map_of_mem g h1
    rw [AddMonoidHom.map_closure] at h2
    refine AddSubgroup.closure_mono ?_ h2
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨b, hb, hbv, t, ht, rfl⟩
  let S : Finset (Fv F v) :=
    (T₀ ×ˢ (Finset.univ : Finset (Fin a × Fin (a + a')))).image (fun p => algebraMap F (Fv F v) (yf p.1 p.2)) ∪
    (T₀ ×ˢ (Finset.univ : Finset (Fin a × Fin (a + a')))).image (fun p => algebraMap F (Fv F v) (zf p.1 p.2))
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatVacBdd.exists_ne_zero_mul_mem v S
  have hcy : ∀ t ∈ T₀, ∀ k, c * algebraMap F (Fv F v) (yf t k) ∈ v.adicCompletionIntegers F := fun t ht k =>
    hc _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(t, k), Finset.mem_product.2 ⟨ht, Finset.mem_univ _⟩, rfl⟩))
  have hcz : ∀ t ∈ T₀, ∀ k, c * algebraMap F (Fv F v) (zf t k) ∈ v.adicCompletionIntegers F := fun t ht k =>
    hc _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(t, k), Finset.mem_product.2 ⟨ht, Finset.mem_univ _⟩, rfl⟩))
  have hev : ∀ y : F, evFin F v (algebraMap F (AF F) y) = algebraMap F (Fv F v) y := fun y => AlgHom.commutes _ _
  refine ⟨c, hc0, fun γ hγ => ?_⟩
  clear_value T₀
  revert hγ
  intro hγ
  have hγ' := hgen hγ
  clear hγ
  induction hγ' using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, -, hbv, t, ht, rfl⟩ := hz
    intro k
    simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearEquiv.map_smul, hyz,
      Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, hev]
    exact ⟨by rw [mul_left_comm]; exact mul_mem hbv (hcy t ht k),
      by rw [mul_left_comm]; exact mul_mem hbv (hcz t ht k)⟩
  | zero => intro k; simp
  | add x y _ _ hx hy =>
    intro k
    rw [map_add (f := _)]
    exact ⟨by rw [Prod.fst_add, Pi.add_apply, mul_add]; exact add_mem (hx k).1 (hy k).1,
      by rw [Prod.snd_add, Pi.add_apply, mul_add]; exact add_mem (hx k).2 (hy k).2⟩
  | neg x _ hx =>
    intro k
    rw [map_neg]
    exact ⟨by rw [Prod.fst_neg, Pi.neg_apply, mul_neg]; exact neg_mem (hx k).1,
      by rw [Prod.snd_neg, Pi.neg_apply, mul_neg]; exact neg_mem (hx k).2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeavesSupSpanData
section
set_option autoImplicit false

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem lat_span_of_hypC {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j) {large₂ : SizeData₂ D} {H : WeightAlgebra.KHyp}
    {C2 A2 CR Bx CT : ℝ} {S : WeightAlgebra.Scal (recB h.toLawsCore)} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    {nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ}
    (hyp : Formalism.MainNotions.Gaps.EtaleWeightGaps.HypC large₂ (recPJ h j hj) H C2 A2 CR Bx CT S ka wL wF Tn nP nW h0 nus) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h.toLawsCore) j ka ∧ ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ka ∧
      WeightAlgebra.H2 (recPJ h j hj) S ka wL wF := by
  obtain ⟨hA, -, hB, -, hH2, -⟩ := hyp
  obtain ⟨-, -, -, hK, -, po, -, -, PLam, -, -, -, -, hka⟩ := hB
  have sK := GlobalTheory.RunLat.spanAt_of_shortG _ _ _ _ hka
  exact ⟨GlobalTheory.latAt_record D _ h.toLawsCore (GlobalTheory.RunIn.gamAt_of_lawsCore' D _ h.toLawsCore) large₂ H.CA hA j ka _
    (recPJ h j hj) S wL wF hK sK hH2, sK, hH2⟩

theorem ownAt_pos (D : D7) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : 0 < ownAt D v := by
  unfold ownAt
  split_ifs
  · exact D.host.pde'_prime.pos
  · exact D.host.pde_prime.pos


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem leaves_sup_span_data : ∀ CK : ℝ, ∃ x₁ : ℝ, ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → CoreTies L EX J R → OwnPin r → PageNum Tp x₁ → RunsHold Tp hK EX CK r → R.IsGrp F → R.tup_mu_conj → R.tup_mu_off → R.tup_mu_ne → LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O ∧ LeafData O := by
  intro CK
  refine ⟨0, ?_⟩
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hrec _ _ _ hrun hgrp _ _ _
  obtain rfl : κ = fun i : Fin D.R.m => kaR Tp hK ((i : ℕ) + 1) := funext hrec.kap
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hrec.tied
  have hok := hrec.ok
  have h3 : LeafSup O ∧ LeafSpan O ∧ LeafLemmaS O := by
    refine leaves_sup_span_lemmaS_of_formTieK GlobalTheory.chartIndependence_unconditional D L Pm Tp hK hinj EX _ _ _ _ _ c O
      fun v i => ?_
    letI : Algebra (r.used v).full.J.Q.c.F D.what₂.LL := inst
    obtain ⟨a1, a2, a3⟩ := lat_span_of_hypC _ _ (hrun v (hok.laws v).p hinj _ (inR_succ i)).1
    exact ⟨(r.used v).full, (hok.laws v).p, _, inR_succ i, ownAt D v, inst, z i, act i, fun g => r.lev i (mirIncl R g),
      (ht v i).1.toFormTieK, (ht v i).1.act_eq, hok.laws v, hok.xiRat v i, hok.cover v i, ownAt_pos D v, a1, a2, a3⟩
  refine ⟨h3.1, h3.2.1, h3.2.2, ?_⟩
  have hU : ∀ g, g ∈ F.P0 ↔ ∀ PP : R.Pg, R.eG g PP ∈ unip (kP PP.1) D.R.r := fun g => by
    rw [GlobalTheory.OntoChain.mem_base_iff hgrp.levels]
    refine Iff.trans ?_ ((mem_pi_unip_iff R (R.eG g)).symm.trans ⟨fun H PP => H PP (Set.mem_univ _), fun H PP _ => H PP⟩)
    refine exists_congr fun u => and_congr_right fun _ => ?_
    rw [← eG_mirIncl, R.eG.injective.eq_iff]
  have key : ∀ v (i : Fin D.R.m), GlobalTheory.TraceLattice.TiedAt A hinj EX O (mirIncl R) F.P0 F.ψ0⁻¹
      (fun _ _ _ _ _ _ _ _ _ => True) v i := fun v i =>
    ⟨(r.used v).full, inst, R, _, v₀, (hok.laws v).p, fw, ownAt D v, i, _, _, _, z i, act i, r.lev i, 1, y v i,
      (ht v i).1, hok.laws v, hok.xiRat v i, kaWt_n _ _ _ _, GlobalTheory.TraceLattice.kaR_lastPos Tp hK (inR_succ i),
      @GlobalTheory.TraceLattice.detOneOn_of_pins D G _ _ _ _ A (r.used v).full inst R i (hok.laws v) _ (hok.level v i) hok.half _ hU,
      trivial⟩
  exact GlobalTheory.TraceLattice.leafData_of_onTie_of_leafSpan h3.2.1 fun w _ => ⟨key w, key _⟩

end GlobalTheory.BigOn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChrLocal

open scoped TensorProduct
open GlobalTheory.AdelicU

theorem map_eq_zero_of_at {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {B : Type} [CommRing B]
    [Algebra F B] {v : Pl (F := F)} {x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hx : At (evFin F v) x) {a : AF F}
    (ha : evFin F v a = 0) (f : AF F →ₐ[F] B) (hf : f a = 1) :
    Algebra.TensorProduct.map f (AlgHom.id F E) x = 0 := by
  have h := hx a ha
  rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply] at h
  have h2 := congrArg (Algebra.TensorProduct.map f (AlgHom.id F E)) h
  rw [map_mul, Algebra.TensorProduct.map_tmul, map_zero] at h2
  simpa [hf, ← Algebra.TensorProduct.one_def] using h2

theorem eq_locIdele_splitPrime {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (z : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ)
    (hz : At (evFin F v) ((z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) - 1)) (h1 : piW (τ.comp σ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1) :
    z = GlobalTheory.LFun.locIdele F (splitPrime τ)
      (Units.map (GlobalTheory.LFun.complMap (splitPrime_under τ)).toMonoidHom (Units.map (piW τ).toMonoidHom z)) := by
  refine GlobalTheory.LFun.eq_locIdele ?_ (FiniteAdeleRing.ext _ fun u => ?_)
  · have h := map_eq_zero_of_at hz (a := ((1 : Ainf F), (0 : Af F))) (by
      change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v 0 = 0
      exact map_zero _) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) rfl
    change Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA F) (AlgHom.id F E) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1
    rw [map_sub, map_one, sub_eq_zero] at h
    exact h
  · by_cases hu : u.under (𝓞 F) = v
    · rw [GlobalTheory.LFun.finAdEquiv_apply hu]
      have e : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
          (GlobalTheory.LFun.finTens F E (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = compFin F E v (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := by
        change Algebra.TensorProduct.map _ (AlgHom.id F E) (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E) _) = _
        rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
        rfl
      rw [e]
      obtain ⟨τ', rfl⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hσ (GlobalTheory.LFun.SplitChart.isSplit_of_algHom hσ τ) hu
      rw [GlobalTheory.LFun.SplitTie.toCompl_eq_complMap τ' hu]
      change _ = Neutral.B1.finiteSingle E (splitPrime τ) _ (splitPrime τ')
      rcases eq_or_eq_comp_conj hσ τ τ' with rfl | rfl
      · rw [GlobalTheory.LFun.finSingle_self]
        rfl
      · rw [GlobalTheory.LFun.finSingle_ne (splitPrime_comp_ne hσ τ)]
        change GlobalTheory.LFun.complMap hu (piW (τ.comp σ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = 1
        rw [h1, map_one]
    · rw [GlobalTheory.LFun.finAdEquiv_apply rfl]
      have e : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F (u.under (𝓞 F))) (AlgHom.id F E)
          (GlobalTheory.LFun.finTens F E (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = compFin F E (u.under (𝓞 F)) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := by
        change Algebra.TensorProduct.map _ (AlgHom.id F E) (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F) (AlgHom.id F E) _) = _
        rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
        rfl
      have h := map_eq_zero_of_at hz (a := GlobalTheory.LatVac.liftV (u.under (𝓞 F)) 1) (by
        change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (singleFin (u.under (𝓞 F)) 1) = 0
        exact evalV_singleFin_ne (Ne.symm hu) 1) (evFin F (u.under (𝓞 F))) (GlobalTheory.LatVac.evFin_liftV _ 1)
      rw [map_sub, map_one, sub_eq_zero] at h
      have h' : compFin F E (u.under (𝓞 F)) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1 := h
      rw [e, h', map_one]
      change (1 : u.adicCompletion E) = Neutral.B1.finiteSingle E (splitPrime τ) _ u
      exact (GlobalTheory.LFun.finSingle_ne (fun e => hu (by rw [e]; exact splitPrime_under τ)) _).symm

theorem chrW_piW_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (χ : Chr F E) (v : Pl (F := F)) (τ : E →ₐ[F] Fv F v) (z : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ), At (evFin F v) ((z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) - 1) →
    piW (τ.comp σ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1 → chrW χ τ (Units.map (piW τ).toMonoidHom z) = Circle.toUnits (χ z) := by
  intro F E _ _ _ _ _ σ hσ χ v τ z hz h1
  change Circle.toUnits (χ (GlobalTheory.LFun.locIdele F (splitPrime τ) _)) = _
  rw [← eq_locIdele_splitPrime hσ τ z hz h1]

end GlobalTheory.ChrLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormUnramifiedFactorization
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NormLocSplit

theorem norm_at_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : Pl (F := F)) (τ : E →ₐ[F] Fv F v) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) (z - 1) →
    At (evFin F v) (Algebra.norm (AF F) z - 1) ∧ evFin F v (Algebra.norm (AF F) z) = piW τ z * piW (τ.comp σ) z := by
  intro F E _ _ _ _ _ σ h v τ z hz
  have hN : algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (Algebra.norm (AF F) z) = z * cA σ z :=
    GlobalTheory.Doubling.algebraMap_norm_eq h z
  have hinj : Function.Injective (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    Algebra.TensorProduct.includeLeft_injective (S := AF F) (algebraMap F E).injective
  refine ⟨fun u hu => hinj ?_, ?_⟩
  · have h1 : u • (z - 1) = 0 := hz u hu
    have h2 : u • (cA σ z - 1) = 0 := by
      have := congrArg (cA σ) h1
      rwa [map_smul, map_sub, map_one, map_zero] at this
    rw [smul_eq_mul, map_mul, map_sub, map_one, hN, map_zero, ← Algebra.smul_def,
      show z * cA σ z - 1 = (z - 1) * cA σ z + (cA σ z - 1) by ring, smul_add, ← smul_mul_assoc, h1, h2,
      zero_mul, add_zero]
  · have h3 := congrArg (piW τ) hN
    have hc : piW τ (cA σ z) = piW (τ.comp σ) z := by
      change splitProj τ (compFin F E v (sigR (AF F) σ z)) = splitProj (τ.comp σ) (compFin F E v z)
      have hs : ∀ y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), compFin F E v (sigR (AF F) σ y) = sigR (Fv F v) σ (compFin F E v y) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a x => rfl
        | add x y hx hy => simp only [map_add (f := _), hx, hy]
      rw [hs, splitProj_comp]
    have ha : piW τ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (Algebra.norm (AF F) z)) = evFin F v (Algebra.norm (AF F) z) := by
      change splitProj τ (compFin F E v (Algebra.norm (AF F) z ⊗ₜ[F] 1)) = _
      simp [compFin]
    rw [map_mul, hc, ha] at h3
    exact h3

end GlobalTheory.NormLocSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalProductActsOfAdelicProductActsFirst
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BoxAct

theorem tens_boxFun {F : Type} [Field F] [NumberField F] {R κ κ' : Type} (ev : AF F → R)
    (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) (r₁ : (κ → AF F) → ℂ) (r₂ : (κ' → AF F) → ℂ) :
    tens ev (boxFun φ₁ φ₂) (boxFun r₁ r₂) = boxFun (tens ev φ₁ r₁) (tens ev φ₂ r₂) := by
  funext x
  simp only [tens, boxFun, Function.comp_def]
  ring

theorem boxFun_acts : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (Td : ((κ ⊕ κ' → AF F) → ℂ) → (κ ⊕ κ' → AF F) → ℂ),
    (∀ Φ₁ ∈ schA F κ, ∀ Φ₂ ∈ schA F κ', Td (boxFun Φ₁ Φ₂) = boxFun (T Φ₁) Φ₂) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), ∀ (φ₁' : (κ → Fv F v) → ℂ) (Φ' : (κ ⊕ κ' → Fv F v) → ℂ),
      Acts (evFin F v) T φ₁ φ₁' → Acts (evFin F v) Td (boxFun φ₁ φ₂) Φ' → Φ' = boxFun φ₁' φ₂ := by
  intro F _ _ v κ κ' _ _ T Td hT φ₁ hφ₁ φ₂ hφ₂ φ₁' Φ' h₁ hd
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  obtain ⟨R', hR0', hR'⟩ := GlobalTheory.RestWitness.exists_rest κ' v
  have r₁ := hR φ₁ hφ₁
  have r₂ := hR' φ₂ hφ₂
  have hRest : Rest (evFin F v) (boxFun φ₁ φ₂) (boxFun R R') := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · have hz₁ : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inl i)
      have hz₂ : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inr i)
      have e₁ := r₁.1 (x ∘ Sum.inl) (z ∘ Sum.inl) hz₁
      have e₂ := r₂.1 (x ∘ Sum.inr) (z ∘ Sum.inr) hz₂
      simp only [boxFun]
      have a₁ : (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl := rfl
      have a₂ : (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr := rfl
      rw [a₁, a₂, e₁, e₂]
    · rw [tens_boxFun]
      exact GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ' _ r₁.2 _ r₂.2
  have key : tens (evFin F v) Φ' (boxFun R R') = tens (evFin F v) (boxFun φ₁' φ₂) (boxFun R R') := by
    rw [← hd _ hRest, tens_boxFun, hT _ r₁.2 _ r₂.2, h₁ R r₁, tens_boxFun]
  funext y
  let z : κ ⊕ κ' → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hz : ∀ (ι : Type) (w : ι → κ ⊕ κ'), At (evFin F v) (z ∘ w) := by
    intro ι w u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v (y (w i)) u hu
  have hRz : boxFun R R' z = R 0 * R' 0 := by
    have e₁ := (hR φ₁ hφ₁).1 0 (z ∘ Sum.inl) (hz κ Sum.inl)
    have e₂ := (hR' φ₂ hφ₂).1 0 (z ∘ Sum.inr) (hz κ' Sum.inr)
    rw [zero_add] at e₁ e₂
    simp only [boxFun]
    rw [e₁, e₂]
  have hev : (fun i => evFin F v (z i)) = y := by
    funext i; exact GlobalTheory.LatVac.evFin_liftV v (y i)
  have e := congrFun key z
  simp only [tens, hev, hRz] at e
  exact mul_right_cancel₀ (mul_ne_zero hR0 hR0') e

end GlobalTheory.BoxAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorIsometrySchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LocalIsom

theorem lintegral_sq_eq_of_acts : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J), x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F v) →
    ∀ φ φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, φ ∈ GlobalTheory.WeilM.SB _ → φ₁ ∈ GlobalTheory.WeilM.SB _ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om' (x, 1)) φ φ₁ →
      ∀ μ : @Measure (Fin a' × Fin (a + a') → Fv F v) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∫⁻ y, ‖φ₁ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hTr v x _ φ φ₁ hφ hφ₁ hact μ hμ
  obtain ⟨r, K, hrm, hinv, hsch, hK, hKi, hint⟩ := GlobalTheory.T.exists_periodic_measurable_schwartz_bound (κ := Fin a' × Fin (a + a')) v
  letI mA : MeasurableSpace (Fin a' × Fin (a + a') → AF F) := borel _
  haveI : BorelSpace (Fin a' × Fin (a + a') → AF F) := ⟨rfl⟩
  have hμA : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (Fin a' × Fin (a + a') → AF F)) := inferInstance
  obtain ⟨C, hC0, hCt, hC⟩ := GlobalTheory.T.lintegral_normSq_componentTensor_eq_const_mul v r hrm hinv _ hμA μ hμ K hK hKi (hint _ hμA).1 (hint _ hμA).2
  have hU := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil').unit
  have e := hU _ hμA (x, 1) _ (hsch φ hφ)
  rw [hact r ⟨hinv, hsch φ hφ⟩, hC φ₁ hφ₁.1.continuous hφ₁.2, hC φ hφ.1.continuous hφ.2] at e
  exact (ENNReal.mul_right_inj hC0 hCt).mp e

end GlobalTheory.LocalIsom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEqStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modification_globalSectionsDim_pull_eq : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp k) (U : Y.Opens) (D : ℕ), SmoothOfRelativeDimension D p → IsProjOver p → ∀ (M : Modif p U D) [IsIntegral M.X] (B : LB Y), B.IsLB → letI := algebraΓOfHom p; letI := algebraΓOfHom M.str; lbH0 k (B.pull M.σ) = lbH0 k B := by
  first | exact @GlobalTheory.ModifSections.modification_lineBundleGlobalSectionsDim_pull_eq | exact GlobalTheory.ModifSections.modification_lineBundleGlobalSectionsDim_pull_eq | (intros; apply GlobalTheory.ModifSections.modification_lineBundleGlobalSectionsDim_pull_eq <;> assumption)
end

