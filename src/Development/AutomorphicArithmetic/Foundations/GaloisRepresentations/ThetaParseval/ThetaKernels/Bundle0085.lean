module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.Decomp
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0027
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGDecomp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0011
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0078
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGTail
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TP
private theorem abs_tail_pk {G D C : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [MeasurableSpace D] [BorelSpace D]
    [LocallyCompactSpace D] [SecondCountableTopology D]
    [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [MeasurableSpace C] [BorelSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    (j : D × C ≃ₜ* G) (μ : Measure G) [μ.IsHaarMeasure] (μC : Measure C) [μC.IsHaarMeasure]
    {U W : Set G} {K : Set C} (hU : IsOpen U) (hUc : IsCompact U) (h1 : (1 : G) ∈ U)
    (hK : MeasurableSet K) (f : G → ENNReal) (F : C → ENNReal) (hF : Measurable F)
    (hc : ∀ d c, j (d, c) ∈ U → j (d, 1) ∈ U ∧ c ∈ K)
    (hm : ∀ d c, j (d, 1) ∈ U → c ∉ K → j (d, c) ∈ W ∧ f (j (d, c)) = F c)
    (hlt : ∫⁻ g in W, f g ∂μ < μ U) : ∫⁻ c in Kᶜ, F c ∂μC < μC K := by
  let μD : Measure D := Measure.haar
  let T : Set D := {d | j (d, 1) ∈ U}
  have cj : Continuous fun d : D => j (d, 1) := j.continuous.comp (by fun_prop)
  have oT : IsOpen T := hU.preimage cj
  have m1 : (1 : D) ∈ T := by
    show j ((1 : D), (1 : C)) ∈ U
    rw [show ((1 : D), (1 : C)) = 1 from rfl, map_one]; exact h1
  have t0 : μD T ≠ 0 := (oT.measure_pos μD ⟨1, m1⟩).ne'
  have tt : μD T ≠ ⊤ := by
    have cpt : IsCompact (Prod.fst '' (j.symm '' U)) := (hUc.image j.symm.continuous).image continuous_fst
    refine ((measure_mono ?_).trans_lt cpt.measure_lt_top).ne
    intro d hd
    exact ⟨(d, 1), ⟨j (d, 1), hd, j.symm_apply_apply _⟩, rfl⟩
  let P : Measure (D × C) := μD.prod μC
  have me : MeasurableEmbedding j := j.toHomeomorph.measurableEmbedding
  have hH : (P.map j).IsHaarMeasure := j.toMulEquiv.isHaarMeasure_map P j.continuous j.symm.continuous
  have hν : P.map j = Measure.haarScalarFactor (P.map j) μ • μ := Measure.isMulLeftInvariant_eq_smul (P.map j) μ
  have k0 : Measure.haarScalarFactor (P.map j) μ ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  have a1 : μD T * ∫⁻ c in Kᶜ, F c ∂μC = ∫⁻ y in T ×ˢ Kᶜ, F y.2 ∂P := by
    rw [← Measure.prod_restrict, lintegral_prod (fun y : D × C => F y.2) (hF.comp measurable_snd).aemeasurable]
    simp [lintegral_const, mul_comm]
  have a2 : ∫⁻ y in T ×ˢ Kᶜ, F y.2 ∂P ≤ ∫⁻ g in W, f g ∂(P.map j) := by
    rw [me.restrict_map, me.lintegral_map]
    calc _ = ∫⁻ y in T ×ˢ Kᶜ, f (j y) ∂P :=
          setLIntegral_congr_fun (oT.measurableSet.prod hK.compl) fun y hy => (hm y.1 y.2 hy.1 hy.2).2.symm
      _ ≤ _ := lintegral_mono_set fun y hy => (hm _ _ hy.1 hy.2).1
  have a3 : (P.map j) U ≤ μD T * μC K := by
    rw [me.map_apply, ← Measure.prod_prod]
    exact measure_mono fun y hy => hc y.1 y.2 hy
  have a4 : ∫⁻ g in W, f g ∂(P.map j) < (P.map j) U := by
    rw [hν, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply]
    have hk : ((Measure.haarScalarFactor (P.map j) μ : ℝ≥0) : ENNReal) ≠ 0 := by exact_mod_cast k0
    simp only [ENNReal.smul_def, smul_eq_mul]
    exact (ENNReal.mul_lt_mul_iff_right hk ENNReal.coe_ne_top).2 hlt
  have := (a1.le.trans a2).trans_lt (a4.trans_le a3)
  exact (ENNReal.mul_lt_mul_iff_right t0 tt).1 this
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n} {v : Pl F}
private theorem fix_off_pk {g : UA σ X.J} (hg : OffAt v g) {z : Fin n → AE F E} (hz : At (evFin F v) z) : mat g *ᵥ z = z := by
  have h : PositivityTheory.ThKG.Loc.idem F v • (mat g - 1) = 0 := Matrix.ext fun i j => Bad.idem_off (by
    have := congrFun₂ hg i j
    rw [Matrix.map_apply] at this
    simp [this, Matrix.one_apply, apply_ite (compFin F E v)])
  have e : (mat g - 1) *ᵥ z = 0 := by
    rw [← Bad.idem_smul hz, Matrix.mulVec_smul, ← Matrix.smul_mulVec, h, Matrix.zero_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at e
  exact e
private theorem int_of_off_pk {g : UA σ X.J} (hg : OffAt v g) : IntAt v g := fun z hz h => by
  have e := fix_off_pk hg h
  have e' : mat g⁻¹ *ᵥ z = z := by
    conv_lhs => rw [← e]
    rw [Matrix.mulVec_mulVec, ← Euler.mm, inv_mul_cancel]
    exact Matrix.one_mulVec z
  exact ⟨e.symm ▸ hz, e'.symm ▸ hz⟩
private theorem int_gOff_pk {S : Finset (Pl F)} {c : UA σ X.J} (hc : c ∈ gOff σ X S) (hv : v ∈ S) : IntAt v c :=
  (show gOff σ X S ≤ Euler.intGrp σ X v from
    (Subgroup.closure_le _).2 (fun _ hg => int_of_off_pk (hg.2 v hv))) hc
private theorem int_gAt_pk {S : Finset (Pl F)} {b : UA σ X.J} (hb : b ∈ gAt σ X S) (hv : v ∉ S) : IntAt v b := by
  have : gAt σ X S ≤ Euler.intGrp σ X v := iSup₂_le fun w hw x hx => by
    have hvw : v ≠ w := fun e => hv (e ▸ hw)
    have := (Euler.int_mul_ne hvw hx 1).2 (Euler.intGrp σ X v).one_mem
    rwa [mul_one] at this
  exact this hb
private theorem hgt_right_pk {K : Subgroup (G2 σ X)} {a : G2 σ X → ℝ} (ha : IsHgt K a) (x : G2 σ X) {k : G2 σ X} (hk : k ∈ K) :
    a (x * k) = a x := by
  obtain ⟨p, t, hp, k', hk', rfl⟩ := ha.iwa x
  rw [mul_assoc, ha.val p t hp _ (K.mul_mem hk' hk), ha.val p t hp k' hk']
end
end UpperTheory.TP
open UpperTheory.TP in
theorem UpperTheory.TP.tail_k :
    _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.Tail_k := by
  intro T F E _ _ _ _ _ σ B n X hB hX K a e hK ha he μ t hμ hi S₀
  classical
  have := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  obtain ⟨a1, a2, a3⟩ := Euler.lcsc_UA σ X.J
  have hL := hX.lat
  have dec := _root_.UpperTheory.TP.decomp_k T F E σ B n X hB hX
  let U : Set (UA σ X.J) := {g | IntAll g}
  have Um : ∀ {x y : UA σ X.J}, IntAll x → IntAll y → IntAll (x * y) := fun hx hy v => (Euler.intGrp σ X v).mul_mem (hx v) (hy v)
  have Ui : ∀ {x : UA σ X.J}, IntAll x → IntAll x⁻¹ := fun hx v => (Euler.intGrp σ X v).inv_mem (hx v)
  have U1 : IntAll (1 : UA σ X.J) := fun v => (Euler.intGrp σ X v).one_mem
  obtain ⟨-, -, -, -, cU, oU, -, -, -⟩ := dec ∅
  have hr : ∀ g u : UA σ X.J, IntAll u → a (e (g * u, 1)) = a (e (g, 1)) := fun g u hu => by
    have : e (g * u, 1) = e (g, 1) * e (u, 1) := by rw [← map_mul, Prod.mk_mul_mk, mul_one]
    rw [this, hgt_right_pk ha _ (_root_.GlobalTheory.ThK.Dbl.Bad.emb_mem_k hB hX (by simp) hK he hu)]
  have lc : IsLocallyConstant fun g : UA σ X.J => a (e (g, 1)) := (IsLocallyConstant.iff_exists_open _).2 fun g =>
    ⟨{x | g⁻¹ * x ∈ U}, oU.preimage (by fun_prop), by show g⁻¹ * g ∈ U; rw [inv_mul_cancel]; exact U1, fun x hx => by
      have := hr g _ hx
      rwa [mul_inv_cancel_left] at this⟩
  let f : UA σ X.J → ENNReal := fun g => ENNReal.ofReal (a (e (g, 1)) ^ t)
  have cf : Continuous f := (lc.comp fun r => ENNReal.ofReal (r ^ t)).continuous
  let m : Measure (UA σ X.J) := μ.withDensity f
  have mfin : m Set.univ ≠ ⊤ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hi.lintegral_lt_top.ne
  let A : Finset (Pl F) → Set (UA σ X.J) := fun S => {g | ∀ v ∈ S, IntAt v g} \ U
  have mA : ∀ S, MeasurableSet (A S) := fun S => by
    refine MeasurableSet.diff ?_ oU.measurableSet
    simp only [Set.setOf_forall]
    exact (isClosed_iInter fun u => isClosed_iInter fun _ => Euler.isClosed_int hL.toIsLattice u).measurableSet
  have anti : Antitone A := fun S S' hS g hg => ⟨fun v hv => hg.1 v (hS hv), hg.2⟩
  have emp : ⋂ S, A S = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun g hg => ?_
    have hg' := Set.mem_iInter.1 hg
    exact (hg' ∅).2 fun v => (hg' {v}).1 v (Finset.mem_singleton_self v)
  have ten := tendsto_measure_iInter_atTop (μ := m) (fun S => (mA S).nullMeasurableSet) anti
    ⟨∅, ne_top_of_le_ne_top mfin (measure_mono (Set.subset_univ _))⟩
  rw [emp, measure_empty] at ten
  have pos : 0 < μ U := oU.measure_pos μ ⟨1, U1⟩
  obtain ⟨S, hlt, hS⟩ := ((ten.eventually (gt_mem_nhds pos)).and (eventually_ge_atTop S₀)).exists
  refine ⟨S, hS, fun μC hC => ?_⟩
  obtain ⟨⟨j, hj⟩, cI, cA, cO, -, -, iI, -, -⟩ := dec S
  have : LocallyCompactSpace (gInf σ X) := cI.isClosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace (gAt σ X S) := cA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace (gOff σ X S) := cO.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (gInf σ X) := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology (gAt σ X S) := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology (gOff σ X S) := IsEmbedding.subtypeVal.secondCountableTopology
  let j' : (gInf σ X × gAt σ X S) × gOff σ X S ≃ₜ* UA σ X.J :=
    { toMulEquiv := MulEquiv.prodAssoc.trans j.toMulEquiv
      continuous_toFun := j.continuous.comp ((continuous_fst.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
      continuous_invFun := by
        have := j.symm.continuous
        exact ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd)).comp this }
  have hj' : ∀ d c, j' (d, c) = d.1.1 * d.2.1 * c.1 := fun d c => hj (d.1, d.2, c)
  have hj1 : ∀ d, j' (d, 1) = d.1.1 * d.2.1 := fun d => by rw [hj']; simp
  have hcm : ∀ d c, j' (d, c) = c.1 * (d.1.1 * d.2.1) := fun d c => by
    have := map_mul j' ((1 : gInf σ X × gAt σ X S), c) (d, (1 : gOff σ X S))
    rw [Prod.mk_mul_mk, one_mul, mul_one, hj1] at this
    rw [this, hj']
    simp
  have res := abs_tail_pk j' μ μC (U := U) (W := A S) (K := {c | IntAll c.1}) oU cU U1
    (oU.preimage continuous_subtype_val).measurableSet f (fun c => f c.1) (cf.measurable.comp measurable_subtype_coe)
    (fun d c hg => by
      have hx : IntAll d.1.1 := iI _ d.1.2
      have hg' : IntAll (d.1.1 * d.2.1 * c.1) := hj' d c ▸ hg
      have hb : IntAll d.2.1 := fun v => by
        by_cases hv : v ∈ S
        · have e1 : d.2.1 = d.1.1⁻¹ * (d.1.1 * d.2.1 * c.1) * c.1⁻¹ := by group
          rw [e1]
          exact (Euler.intGrp σ X v).mul_mem ((Euler.intGrp σ X v).mul_mem ((Euler.intGrp σ X v).inv_mem (hx v)) (hg' v))
            ((Euler.intGrp σ X v).inv_mem (int_gOff_pk c.2 hv))
        · exact int_gAt_pk d.2.2 hv
      have hxb := Um hx hb
      refine ⟨by rw [hj1]; exact hxb, ?_⟩
      show IntAll c.1
      have e2 : c.1 = (d.1.1 * d.2.1)⁻¹ * (d.1.1 * d.2.1 * c.1) := by group
      rw [e2]
      exact Um (Ui hxb) hg')
    (fun d c hd hcK => by
      have hd' : IntAll (d.1.1 * d.2.1) := hj1 d ▸ hd
      refine ⟨⟨fun v hv => ?_, fun hg => hcK ?_⟩, ?_⟩
      · rw [hj']
        exact (Euler.intGrp σ X v).mul_mem (hd' v) (int_gOff_pk c.2 hv)
      · have hg' : IntAll (d.1.1 * d.2.1 * c.1) := hj' d c ▸ hg
        show IntAll c.1
        have e2 : c.1 = (d.1.1 * d.2.1)⁻¹ * (d.1.1 * d.2.1 * c.1) := by group
        rw [e2]
        exact Um (Ui hd') hg'
      · show ENNReal.ofReal (a (e (j' (d, c), 1)) ^ t) = ENNReal.ofReal (a (e (c.1, 1)) ^ t)
        rw [hcm, hr _ _ hd'])
    (by
      rw [← withDensity_apply _ (mA S)]
      exact hlt)
  exact res
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeylBaseColumn
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
namespace N
theorem fix_of_col_k {w x : d.G}
    (hc : ∀ r, inFrame d.b x r (Sum.inl L.i₀) = inFrame d.b w r (Sum.inl L.i₀)) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (w⁻¹ * x) := by
  intro k
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply]
  simp_rw [hc]
  rw [← Matrix.mul_apply, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
theorem weyl_base_column (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) : ∃ b₀ : E, b₀ ≠ 0 ∧ ∀ r, inFrame d.b w₁ r (Sum.inl L.i₀) =
    inclR (F := F) (AF F) ((Pi.single (Sum.inr L.i₀) b₀ : Fin d.n ⊕ Fin d.n → E) r) := by
  obtain ⟨a, b, -, hb, hw⟩ := h.wf
  refine ⟨b, hb, fun r => ?_⟩
  rw [hw]
  rcases r with i | i <;> by_cases hi : i = L.i₀
  · subst hi; simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply]
  · simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply, hi, Ne.symm hi]
  · subst hi; simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply]
  · simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply, hi, Ne.symm hi]
theorem normalize_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {γ : d.G} (hγ : γ ∈ rat2 σ d.Y) (hn : ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L γ) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (w₁⁻¹ * (p * γ)) := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) γ hγ
  have hform := Bq.form_E hε γ hG0
  obtain ⟨b₀, hb₀, hw1⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.N.weyl_base_column h
  have hy : (fun k => G0 (Sum.inr k) (Sum.inl L.i₀)) ≠ 0 := by
    intro h0
    apply hn
    intro i
    rw [hG0]
    show inclR (F := F) (AF F) (G0 (Sum.inr i) (Sum.inl L.i₀)) = 0
    rw [congrFun h0 i, Pi.zero_apply, map_zero]
  obtain ⟨A, β0, hβ, hcol⟩ := exists_E L.i₀ hσ ε hform hb₀ hy
  obtain ⟨pm, hpmr, hpm⟩ := Afc.levi_ex hσ d.ok.frame A
  have hpmP : pm ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame pm).2 (by rw [hpm, Matrix.toBlocks_fromBlocks₂₁])
  have hβA : incM F β0 ∈ nA σ d.Y d.b := (kfour.mem_nA_iff hσ hε _).2 (nCond_of_E ε hβ)
  set pn := nb ⟨incM F β0, hβA⟩ with hpn_def
  have hpn : inFrame d.b pn = Matrix.fromBlocks 1 (incM F β0) 0 1 := h.nb _
  have hpnP : pn ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame pn).2 (by rw [hpn, Matrix.toBlocks_fromBlocks₂₁])
  have hpnr : pn ∈ rat2 σ d.Y :=
    kunf.rat_of_inFrame (M := Matrix.fromBlocks 1 β0 0 1) (by rw [hpn, kfour.incM_nM]; rfl)
  refine ⟨pn * pm, mul_mem hpnP hpmP, mul_mem hpnr hpmr, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.N.fix_of_col_k fun r => ?_⟩
  have hF : inFrame d.b (pn * pm * γ) =
      incM F (Matrix.fromBlocks 1 β0 0 1 * Matrix.fromBlocks A.1 0 0 (((A⁻¹).1)ᵀ.map σ) * G0) := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hpn, hpm, hG0, kfour.incM_mul', kfour.incM_mul',
      kfour.incM_nM, Afc.incM_fromBlocks, kfour.incM_zero]
    rfl
  rw [hF, hw1 r]
  show inclR (F := F) (AF F) _ = _
  rw [hcol r]
end N
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end

