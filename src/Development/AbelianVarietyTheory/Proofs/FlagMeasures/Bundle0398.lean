module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0190
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0147
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0151
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0030
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0029
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0076

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroFlagProbabilityBoundOfVolumeRatioInductio
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.NonzeroFlag

theorem telescope : ∀ (a : ℕ) (r : Fin (a + 1) → ℕ) (j : Fin a → ℕ),
    (∀ i : Fin a, r i.succ = r i.castSucc + j i) → r (Fin.last a) = r 0 + ∑ i, j i := by
  intro a
  induction a with
  | zero => intro r j _; simp
  | succ a ih =>
    intro r j h
    have h1 := ih (fun i => r i.castSucc) (fun i => j i.castSucc) (fun i => h i.castSucc)
    have h2 := h (Fin.last a)
    rw [Fin.sum_univ_castSucc]
    have h3 : r (Fin.last (a + 1)) = r (Fin.last a).castSucc + j (Fin.last a) := h2
    have h4 : r (Fin.last a).castSucc = r 0 + ∑ i : Fin a, j i.castSucc := h1
    omega

theorem exists_composition (a : ℕ) (j : Fin a → ℕ) (hj : ∀ i, 1 ≤ j i) (J : ℕ) (hJ : ∑ i, j i = J)
    (P : ∀ a : ℕ, (Fin a → ℕ) → Prop) (h : P a j) :
    ∃ c : Composition J, P c.length c.blocksFun := by
  have key : ∀ (b : ℕ) (e : b = a) (j' : Fin b → ℕ), (∀ i, j' i = j (Fin.cast e i)) → P b j' := by
    intro b e j' hh
    subst e
    have : j' = j := funext hh
    rw [this]; exact h
  refine ⟨⟨List.ofFn j, ?_, ?_⟩, key _ (by simp [Composition.length]) _ ?_⟩
  · intro i hi
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hi
    exact hj k
  · rw [List.sum_ofFn, hJ]
  · intro i
    simp [Composition.blocksFun]
    rfl

theorem measurableSet_simplexH (a : ℕ) : MeasurableSet (simplexH a) := by
  have : simplexH a = (⋂ i : Fin a, ⋂ k : Fin a, ⋂ _ : i < k, {τ : Fin a → ℝ | τ i < τ k}) ∩
      ⋂ i : Fin a, ({τ : Fin a → ℝ | 0 < τ i} ∩ {τ : Fin a → ℝ | τ i < 1 / 2}) := by
    ext τ
    simp [simplexH, StrictMono]
  rw [this]
  refine MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply k)
  · exact MeasurableSet.iInter fun i => (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const)

theorem mem_typeSet (I : AutInst) (p q : ℕ) (hs : HasSig I p q) (x : I.GA) (hx : stepLt I x (1 / 2) ≠ ⊥) :
    ∃ J ∈ Finset.Icc 1 q, ∃ c : Composition J, x ∈ typeSet I c.blocksFun (simplexH c.length) := by
  obtain ⟨⟨a, S, τ, hF⟩, -, h3⟩ := GlobalTheory.PointFlag.flag_spec I x
  have h3 := (h3 a S τ hF).1
  set j : Fin a → ℕ := fun i => Formalism.HN.rkK (S i.succ) - Formalism.HN.rkK (S i.castSucc) with hjdef
  have hj1 : ∀ i, 1 ≤ j i := fun i => by have := (h3 i).2.1; simp only [hjdef]; omega
  have hj2 : ∀ i, Formalism.HN.rkK (S i.succ) = Formalism.HN.rkK (S i.castSucc) + j i := fun i => by
    have := (h3 i).2.1; simp only [hjdef]; omega
  have htel := telescope a (fun i => Formalism.HN.rkK (S i)) j hj2
  obtain ⟨v⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  have hr := (_root_.GlobalTheory.FlagIso.flag_isotropic I x).2.1 v
  have hq : rkR (I.ε v) ≤ q := by
    rw [← (hs v).2]; exact min_le_right _ _
  have hle : ∑ i, j i ≤ q := by
    simp only [hF.2.2.1] at htel
    omega
  have ha : a ≠ 0 := by
    rintro rfl
    apply hx
    rw [← hF.2.2.1, ← hF.1]; rfl
  have hge : 1 ≤ ∑ i, j i :=
    (hj1 ⟨0, Nat.pos_of_ne_zero ha⟩).trans (Finset.single_le_sum (fun i _ => Nat.zero_le (j i)) (mem_univ _))
  refine ⟨∑ i, j i, Finset.mem_Icc.mpr ⟨hge, hle⟩, ?_⟩
  refine exists_composition a j hj1 _ rfl (fun a j => x ∈ typeSet I j (simplexH a)) ?_
  exact ⟨τ, ⟨hF.2.2.2.1, fun i => ⟨(hF.2.2.2.2.1 i).1, (hF.2.2.2.2.1 i).2.1⟩⟩, S, hF, hj2⟩

theorem nonzeroFlagBound : VolumeStep → NonzeroFlagBound := by
  intro hV I μf _ _ fund hfund p q hs hn hq hrd hf
  obtain ⟨hfd, hv, -, hf1, -, hpq⟩ := _root_.GlobalTheory.FlagMeas.instance_numbers I
  have hpq := hpq p q hs
  have hn16 : 16 ≤ I.n := by
    have hpos : (0 : ℝ) < I.n := by
      rcases Nat.eq_zero_or_pos I.n with h | h
      · rw [h] at hn; simp at hn; linarith
      · exact_mod_cast h
    have := Real.log_le_sub_one_of_pos hpos
    have : (16 : ℝ) ≤ I.n := by linarith
    exact_mod_cast this
  have h2q : 2 * q + 2 ≤ I.n := by nlinarith
  set X : ℝ := I.n * I.f * Real.log I.n with hX
  have hX15 : 15 ≤ X := by
    have h1 : (1 : ℝ) ≤ I.n := by exact_mod_cast (by omega : 1 ≤ I.n)
    have h2 : (1 : ℝ) ≤ I.f := by exact_mod_cast hf1
    have h3 : (1 : ℝ) ≤ I.n * I.f := one_le_mul_of_one_le_of_one_le h1 h2
    rw [hX]; nlinarith
  have hone : ∀ J ∈ Finset.Icc 1 q, ∀ c : Composition J,
      I.muA μf (typeSet I c.blocksFun (simplexH c.length) ∩ fund) / I.muA μf fund ≤
        ENNReal.ofReal (Real.exp (-(1 / 2 * J * X))) := by
    intro J hJ c
    obtain ⟨hJ1, hJq⟩ := Finset.mem_Icc.mp hJ
    have hsum := c.sum_blocksFun
    have hT := (_root_.GlobalTheory.FlagMeas.Bound.flagMeasureBound hV I μf fund hfund p q hs h2q c.length c.blocksFun
      (c.length_pos_of_pos hJ1) c.one_le_blocksFun (by omega) _ (measurableSet_simplexH _) subset_rfl).2.2.2
    have hD := _root_.GlobalTheory.DensityIntegral.lintegral_dens_le_one I.n I.f c.length c.blocksFun hf1 c.one_le_blocksFun (by omega)
    have hK := _root_.GlobalTheory.FlagMeas.constantBound I.E I.cm.cmUnram p q c.length c.blocksFun c.one_le_blocksFun (by omega)
      (by rw [hpq]; exact hn) (by rw [hpq]; exact hq) (by rw [hpq, hv]; exact hrd) (by rw [hpq, hfd]; exact hf)
    rw [hpq, hfd, hsum] at hK
    refine hT.trans ((mul_le_mul_right hD _).trans ?_)
    rw [mul_one]
    refine ENNReal.ofReal_le_ofReal (hK.trans (le_of_eq ?_))
    rw [hX]; congr 1; ring
  have hsub : {x | stepLt I x (1 / 2) ≠ ⊥} ∩ fund ⊆
      ⋃ J ∈ Finset.Icc 1 q, ⋃ c ∈ (Finset.univ : Finset (Composition J)),
        typeSet I c.blocksFun (simplexH c.length) ∩ fund := by
    rintro x ⟨hx, hxf⟩
    obtain ⟨J, hJ, c, hc⟩ := mem_typeSet I p q hs x hx
    simp only [Set.mem_iUnion]
    exact ⟨J, hJ, c, mem_univ _, hc, hxf⟩
  have hμ : I.muA μf ({x | stepLt I x (1 / 2) ≠ ⊥} ∩ fund) ≤
      ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J,
        I.muA μf (typeSet I c.blocksFun (simplexH c.length) ∩ fund) :=
    (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
      (Finset.sum_le_sum fun J _ => measure_biUnion_finset_le _ _))
  calc I.muA μf ({x | stepLt I x (1 / 2) ≠ ⊥} ∩ fund) / I.muA μf fund
      ≤ (∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J,
        I.muA μf (typeSet I c.blocksFun (simplexH c.length) ∩ fund)) / I.muA μf fund :=
        ENNReal.div_le_div_right hμ _
    _ = ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J,
        I.muA μf (typeSet I c.blocksFun (simplexH c.length) ∩ fund) / I.muA μf fund := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∑ _c : Composition J, ENNReal.ofReal (Real.exp (-(1 / 2 * J * X))) :=
        Finset.sum_le_sum fun J hJ => Finset.sum_le_sum fun c _ => hone J hJ c
    _ = ENNReal.ofReal (∑ J ∈ Finset.Icc 1 q, (2 : ℝ) ^ (J - 1) * Real.exp (-(1 / 2 * J * X))) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun J _ => by positivity)]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.sum_const, Finset.card_univ, composition_card, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ((_root_.GlobalTheory.sum_two_pow_pred_mul_exp_neg_le q X hX15).trans (le_of_eq ?_))
        rw [hX]; congr 1; ring

end GlobalTheory.NonzeroFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormsInvariantsGenericRationalFramePair
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenMass.Norms

theorem sqrt_norm_eq (D : D7) (x : D.host.E) :
    Real.sqrt |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ w : InfinitePlace D.host.E, w x := by
  have := Formalism.MainNotions.InterlacingSignCuts.host_totallyComplex D
  have h1 := InfinitePlace.prod_eq_abs_norm x
  have h2 : ∏ w : InfinitePlace D.host.E, w x ^ w.mult = (∏ w : InfinitePlace D.host.E, w x) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun w _ => by rw [(IsTotallyComplex.isComplex w).mult_eq_two]
  rw [← Rat.cast_abs, ← h1, h2]
  exact Real.sqrt_sq (Finset.prod_nonneg fun w _ => w.1.nonneg _)

theorem prod_natPow (D : D7) (g m : ℕ) :
    ∏ w : InfinitePlace D.host.E, w ((g : D.host.E) ^ m) = ((g : ℝ) ^ m) ^ D.R.f := by
  rw [← Formalism.MainNotions.LatticeGluingRadicals.d_card D, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_congr rfl fun w _ => by rw [map_pow, InfinitePlace.map_natCast]

theorem localInvariantNorm_eq_prod_infinitePlaces_div (D : D7) (T T' : D.host.E) (Z : Formalism.L2.SG.CntLocal.MatZ D) :
    Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram T T' Z =
      (∏ w : InfinitePlace D.host.E, w (Formalism.L2.SG.CntLocal.GZ T T' Z)) / (((gS D : ℕ) : ℝ) ^ D.R.m) ^ D.R.f := by
  unfold Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram
  rw [sqrt_norm_eq, ← prod_natPow, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun w _ => by rw [map_div₀]

theorem rd_pow_f (D : D7) : D.host.rdE ^ D.R.f = |(NumberField.discr D.host.F : ℝ)| := by
  have h := Formalism.MainNotions.BridgeLemma.szf_rd_pow D
  rw [Formalism.L2.SG.NGCut.LeadingMinorIntegrality.discr_sq] at h
  have hrd := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.rd_pos (D := D)
  refine (pow_left_inj₀ (by positivity) (abs_nonneg _) two_ne_zero).1 ?_
  rw [h]; push_cast; rw [abs_pow]

theorem one_le_tprod_real {ι : Type} (a : ι → ℝ) (ha : ∀ i, 1 ≤ a i) : 1 ≤ ∏' i, a i := by
  by_cases h : Multipliable a
  · refine ge_of_tendsto' h.hasProd fun s => ?_
    exact Finset.one_le_prod₀ (fun i _ => ha i)
  · rw [tprod_eq_one_of_not_multipliable h]

theorem one_le_nM {K V : Type} [Field K] [NumberField K] [StarRing K] (F : Type) [Field F] [NumberField F]
    [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (M : Submodule (𝓞 K) V) :
    1 ≤ Formalism.L2.SG.Pf.Cnt.nM F h U M := by
  unfold Formalism.L2.SG.Pf.Cnt.nM
  refine one_le_tprod_real _ fun p => one_le_pow₀ ?_
  have h0 : p.1 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField F)
  have h1 : Ideal.absNorm p.1 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  exact_mod_cast Nat.one_le_iff_ne_zero.2 h1

theorem m_eq (D : D7) : D.R.m = 2 * D.R.rS + 2 := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  unfold Ranks.rS
  omega

theorem norms_generic : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ (G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Λ : LV D) (w : Point D.host.E (D.R.rS + 1)), G'.zt = G'.fl.z → TotPos (Gval (lf D (X.Fu u)) G') → IsRowLat D (X.Fu u) Λ → G' ∈ Formalism.L2.SG.CntLocal.EZ ((Tu D u' : ℕ) : D.host.E) (X.Fu u) Λ (ZhatL (lf D (X.Fu u)) G') → IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) G')) w → (∀ a, 1 ≤ ∏ v : InfinitePlace D.host.E, (D.host.rdE ^ (2 * (endIdx (toPts w) a * (2 * D.R.rS + 1 - endIdx (toPts w) a))))⁻¹ * v (endMin (toPts w) a) ^ 2) ∧ ((gS D : ℝ)) ^ ((2 * D.R.rS + 2) * Fintype.card (InfinitePlace D.host.E)) ≤ NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) ∧ Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1) * Formalism.L2.SG.MassDataConc.ngFac D = PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) ^ (D.R.k - 1) := by
  intro D X Y u u' hT G' Λ w hzt hP hrow hE hcell
  have hun := hrow.2.1.2.1
  have hz := hrow.2.1.2.2.1.1
  have hX := hrow.2.2
  have hz' : G'.fl.z ∈ Λ := hE.1.1.1
  have hX' := hE.2.2.2.1.2
  have hF : ∀ b, frame (lf D (X.Fu u)) b ∈ Λ := PtPf.frame_mem _ hz hX
  have hF' : ∀ b, frame G' b ∈ Λ := PtPf.frame_mem _ hz' hX'
  have hrd := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.rd_pos (D := D)
  have hg : (0 : ℝ) < (gS D : ℕ) := by exact_mod_cast Formalism.MainNotions.LatticeGluingRadicals.z_gS_pos D
  have hGeq := LeadingMinorIntegrality.gpt_eq (T := Tu D u) (T' := Tu D u') (lf D (X.Fu u)) G' _ hcell
  set P : ℝ := ∏ v : InfinitePlace D.host.E, v (Gval (lf D (X.Fu u)) G') with hPdef
  have hNG : NGPt D.host.rdE (Tu D u * Tu D u') (toPts w) =
      ((D.host.rdE ^ D.R.f) ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ * P := by
    unfold NGPt
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Formalism.MainNotions.LatticeGluingRadicals.d_card D, hGeq, inv_pow,
      ← pow_mul, ← pow_mul, mul_comm D.R.f]
    rfl
  have hN0 : Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
      (ZhatL (lf D (X.Fu u)) G') = P / (((gS D : ℕ) : ℝ) ^ D.R.m) ^ D.R.f := localInvariantNorm_eq_prod_infinitePlaces_div D _ _ _
  refine ⟨fun a => ?_, ?_, ?_⟩
  · have hj : endIdx (toPts w) a ≤ D.R.rS + 1 := (toPts w).1.sizeUpTo_le _
    obtain ⟨o, ho, e⟩ := LeadingMinorIntegrality.lead_mem hun (lf D (X.Fu u)) G' hz hX hz' hX' _ hj
    rw [← LeadingMinorIntegrality.lead_cell _ _ hcell, ← LeadingMinorIntegrality.endMin_eq] at e
    have hE5 := PtPf.blockEndMinors_of_cell _ (PtPf.zhatOM_isIntegral _ _ hun hF hF') _ hcell
    have h0 : endMin (toPts w) a ≠ 0 := (hE5 a).2
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Formalism.MainNotions.LatticeGluingRadicals.d_card D]
    have hsq := LeadingMinorIntegrality.prod_sq_ge _ o ho (by rw [e]; exact h0)
    rw [e] at hsq
    rw [inv_pow, ← div_eq_inv_mul, one_le_div (by positivity), ← pow_mul, mul_comm _ D.R.f, pow_mul]
    exact hsq
  · have hI := Formalism.L2.SG.Pf.Cnt.mmInt_of_EZ hT (Y.rowsOK u) hzt rfl hP hrow hE
    have hn := PI.UnitaryGroupMassFormula.CntFormula.R6.norm_mass_of_jordan D u u' hT (X.Fu u) (Y.what₂ u) (Y.rowsOK u) _ G' hzt rfl hP hI
    have h1 := one_le_nM D.host.F (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D (X.Fu u) G')
      (Formalism.L2.SG.Pf.Cnt.MMof D (X.Fu u) G')
    replace h1 := h1.trans_eq hn
    rw [zpow_neg, zpow_natCast, ← rd_pow_f] at h1
    replace h1 : 1 ≤ ((D.host.rdE ^ D.R.f) ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ *
        (P / (((gS D : ℕ) : ℝ) ^ D.R.m) ^ D.R.f) := hN0 ▸ h1
    rw [← mul_div_assoc, one_le_div (by positivity)] at h1
    rw [hNG, Formalism.MainNotions.LatticeGluingRadicals.d_card D, ← m_eq, pow_mul]
    exact h1
  · have hv : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
    rw [hN0, hNG, hv]
    unfold Formalism.L2.SG.MassDataConc.ngFac PN.abelian₂
    rw [sqrt_norm_eq, prod_natPow, ← mul_pow, div_mul_cancel₀ _ (by positivity)]
    have e : D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1) * (D.R.k - 1) * D.R.f) =
        ((D.host.rdE ^ D.R.f) ^ (2 * D.R.rS * (D.R.rS + 1))) ^ (D.R.k - 1) := by
      rw [← pow_mul, ← pow_mul]; congr 1; ring
    rw [e, ← mul_pow, mul_inv_cancel_left₀ (by positivity)]

end GlobalTheory.GenMass.Norms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbMassStabilizerLe
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimMeanOne

open GlobalTheory.Mass.FixedSub GlobalTheory.Mass.PrimMean

theorem orbMass_stabilizer_le (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hK : IsCMUnram K) (hs : h.IsSymm) (hp : PD h) (U : Submodule K V) (n N₀ : ℕ) (T : 𝓞 K) (hT : T ≠ 0)
    (dW : Module.finrank K (perp h U) = 1) :
    orbMass (MulAction.stabilizer (isom h) U) {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧
      (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧
      (∀ x ∈ dual h L, T • x ∈ L) ∧ discN (hRes h U) (latIn U L) = n} ≤
    orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) n) *
      (∑ n' ∈ Finset.Icc 1 (n * N₀), orbMass (isom (hRes h (perp h U)))
        (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n')) *
      ((Ideal.absNorm (Ideal.span {T}) * n : ℕ) : ℝ≥0∞) := by
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.definite_unitary_stabilizer_subspace_prod K V h hK hs hp U
  have hs1 := hRes_symm h hs U
  have hp1 := hRes_pd h hp U
  have hs2 := hRes_symm h hs (perp h U)
  have hp2 := hRes_pd h hp (perp h U)
  letI act : MulAction (MulAction.stabilizer (isom h) U)
      (Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U)) :=
    { smul := fun γ p => ((φ γ).1 • p.1, (φ γ).2 • p.2)
      one_smul := fun p => by
        change ((φ 1).1 • p.1, (φ 1).2 • p.2) = p
        simp
      mul_smul := fun a b p => by
        change ((φ (a * b)).1 • p.1, (φ (a * b)).2 • p.2) =
          ((φ a).1 • ((φ b).1 • p.1), (φ a).2 • ((φ b).2 • p.2))
        simp [mul_smul] }
  have hact : ∀ (γ : MulAction.stabilizer (isom h) U)
      (p : Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U)),
      γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2) := fun _ _ => rfl
  set X : Set (Submodule (𝓞 K) V) := {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧
    (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧
    (∀ x ∈ dual h L, T • x ∈ L) ∧ discN (hRes h U) (latIn U L) = n} with hX
  set A : Set (Submodule (𝓞 K) U) := latsDisc (R := 𝓞 K) (hRes h U) n with hA
  set B : Set (Submodule (𝓞 K) (perp h U)) :=
    ⋃ n' ∈ Finset.Icc 1 (n * N₀), latsDisc (R := 𝓞 K) (hRes h (perp h U)) n' with hB
  have memB : ∀ M, M ∈ B ↔ IsIntLat (hRes h (perp h U)) M ∧
      1 ≤ discN (hRes h (perp h U)) M ∧ discN (hRes h (perp h U)) M ≤ n * N₀ := by
    intro M
    simp only [hB, Set.mem_iUnion, Finset.mem_Icc, latsDisc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, h1, rfl⟩
      exact ⟨h1, hi⟩
    · rintro ⟨h1, hi⟩
      exact ⟨_, hi, h1, rfl⟩
  have sA : Stable (isom (hRes h U)) A := stable_latsDisc _ n
  have sB : Stable (isom (hRes h (perp h U))) B := by
    intro g M hM
    rw [memB] at hM ⊢
    rw [discN_smul]
    exact ⟨isIntLat_smul _ g M hM.1, hM.2⟩
  have fA : ∀ M ∈ A, Finite (MulAction.stabilizer (isom (hRes h U)) M) := fun M hM =>
    (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K U (hRes h U) hK hs1 hp1 M hM.1.1).2.2.2.1 M hM.1.1
  have fB : ∀ M ∈ B, Finite (MulAction.stabilizer (isom (hRes h (perp h U))) M) := fun M hM =>
    (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K (perp h U) (hRes h (perp h U)) hK hs2 hp2 M ((memB M).1 hM).1.1).2.2.2.1 M
      ((memB M).1 hM).1.1
  have sX : Stable (MulAction.stabilizer (isom h) U) X := by
    rintro γ L ⟨h1, h2, h3, h5, h4⟩
    refine ⟨isIntLat_smul h γ.1 L h1, (discN_smul h γ.1 L).trans h2, gens_smul h γ.1 L 1 h3, ?_, ?_⟩
    · intro x hx
      have hx' : x ∈ γ.1 • dual h L := dual_smul h γ.1 L ▸ hx
      change T • x ∈ γ.1 • L
      rw [smul_def'] at hx' ⊢
      unfold gmap at hx' ⊢
      obtain ⟨y, hy, rfl⟩ := hx'
      exact ⟨T • y, h5 y hy, map_smul _ _ _⟩
    · rw [(hφ γ L).1, discN_smul, h4]
  have sY : Stable (MulAction.stabilizer (isom h) U) (A ×ˢ B) := by
    rintro γ p ⟨h1, h2⟩
    exact ⟨sA _ _ h1, sB _ _ h2⟩
  have mp : Set.MapsTo (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) X (A ×ˢ B) := by
    rintro L ⟨h1, h2, h3, -, h4⟩
    obtain ⟨k1, k2, k3, -⟩ := _root_.GlobalTheory.Mass.PrimDisc.main K V h hK hs hp L U 1 h1 h3
    refine ⟨⟨k1, h4⟩, (memB _).2 ⟨k2, ?_, ?_⟩⟩
    · exact Nat.one_le_iff_ne_zero.2
        (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K (perp h U) _ hK hs2 (pd_nondeg _ hp2) _ k2).1
    · rw [h2, h4] at k3
      exact k3
  have fY : ∀ p ∈ A ×ˢ B, Finite (MulAction.stabilizer (MulAction.stabilizer (isom h) U) p) := by
    rintro p ⟨h1, h2⟩
    haveI := fA _ h1
    haveI := fB _ h2
    refine Finite.of_injective
      (β := MulAction.stabilizer (isom (hRes h U)) p.1 ×
        MulAction.stabilizer (isom (hRes h (perp h U))) p.2)
      (fun γ => (⟨(φ γ.1).1, congrArg Prod.fst γ.2⟩, ⟨(φ γ.1).2, congrArg Prod.snd γ.2⟩)) ?_
    intro a b e
    apply Subtype.ext
    apply φ.injective
    exact Prod.ext (congrArg (fun q => q.1.1) e) (congrArg (fun q => q.2.1) e)
  have e1 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (MulAction.stabilizer (isom h) U) _ _ X (A ×ˢ B)
    (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L))
    (fun γ L => Prod.ext (hφ γ L).1 (hφ γ L).2) sX sY mp fY
  have e2 := _root_.GlobalTheory.Mass.ProdMass.orbMass_prod (MulAction.stabilizer (isom h) U) _ _ _ _ φ A B hact sA sB fA fB
  have e3 : orbMass (isom (hRes h (perp h U))) B ≤ ∑ n' ∈ Finset.Icc 1 (n * N₀),
      orbMass (isom (hRes h (perp h U))) (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n') :=
    (_root_.GlobalTheory.Mass.OrbMono.main (isom (hRes h (perp h U))) (Submodule (𝓞 K) (perp h U))).2.2.1 ℕ _ B _ _ subset_rfl
  obtain ⟨m1, m2, -⟩ := _root_.GlobalTheory.Mass.OrbMono.main (MulAction.stabilizer (isom h) U)
    (Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U))
  rw [e1]
  refine (m1 _ (A ×ˢ B) _
    (fun _ => ((Ideal.absNorm (Ideal.span {T}) * n : ℕ) : ℝ≥0∞))
    subset_rfl ?_).trans ?_
  · rintro ⟨M, M'⟩ ⟨h1, h2⟩
    obtain ⟨b1, -, -⟩ := (memB M').1 h2
    have cnt := _root_.GlobalTheory.Mass.LineGlue.main K V h hK hs hp U M M' T hT dW h1.1 b1
    have sub : X ∩ (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) ⁻¹' {(M, M')} ⊆
        {L : Submodule (𝓞 K) V | IsIntLat h L ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧ latIn U L = M ∧
          latIn (perp h U) L = M'} :=
      fun N hN => ⟨hN.1.1, hN.1.2.2.2.1, congrArg Prod.fst hN.2, congrArg Prod.snd hN.2⟩
    have e : discN (hRes h U) M = n := h1.2
    rw [e] at cnt
    have := ENat.toENNReal_le.2 ((Set.encard_le_encard sub).trans cnt)
    rwa [ENat.toENNReal_coe] at this
  · rw [m2, e2, mul_comm]
    gcongr

theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ j : ℕ, 1 ≤ j → j + 1 = Module.finrank K V → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ j → ∀ (V₂ : Type) [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂] [Module (𝓞 K) V₂] [IsScalarTower (𝓞 K) K V₂] (h₂ : V₂ →ₗ⋆[K] V₂ →ₗ[K] K) (I₂ : Submodule (𝓞 K) V₂), h₂.IsSymm → IsOrthoLattice h₂ I₂ 1 → ∀ (de t : ℕ) (T : 𝓞 K), 1 ≤ de → 1 ≤ t → T ≠ 0 → Ideal.absNorm (Ideal.span {T}) = t ^ 2 → ∀ 𝒢 : Set (Submodule (𝓞 K) V), Stable (isom h) 𝒢 → (∀ L ∈ 𝒢, IsIntLat h L ∧ discN h L = t ^ 2 ∧ (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V)) ∧ ∀ x ∈ dual h L, T • x ∈ L) → orbSum (isom h) 𝒢 (fun L => (((primSp h L j (de ^ 2)).encard : ℕ∞) : ℝ≥0∞)) ≤ ENNReal.ofReal (mass h₁ I₁ * mass h₂ I₂ * (de : ℝ) ^ j * ((de : ℝ) ^ (4 + Real.logb 2 (fDeg K)) * (t : ℝ) ^ 2 * ((de : ℝ) * t) ^ (2 + Real.logb 2 (fDeg K)))) := by
  intro hM K V _ _ _ _ _ _ _ _ h hK hs hp hLand j hj hjs V₁ _ _ _ _ _ h₁ I₁ hs₁ hI₁ V₂ _ _ _ _ _ h₂ I₂ hs₂ hI₂
    de t T hde ht hT hN 𝒢 hst h𝒢
  obtain ⟨S, hdim, hcov, hsum⟩ := GlobalTheory.T.exists_subspaceReps_sum_orbitMass_le hM K V h hK hs hp hLand j hj V₁ h₁ I₁ hs₁ hI₁ de hde
  have hnd := pd_nondeg h hp
  set l : ℝ := Real.logb 2 (fDeg K) with hl
  have m1 := mass_nonneg h₁ I₁
  have m2 := mass_nonneg h₂ I₂
  have h1 := orbSum_encard_le (isom h) (Submodule (𝓞 K) V) (Submodule K V) 𝒢
    (fun L => primSp h L j (de ^ 2))
    (fun g L U => (_root_.GlobalTheory.Mass.PrimMove.main K V h hK hs hnd g L U j (de ^ 2)).1) hst
    (fun L hL => (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp L (h𝒢 L hL).1.1).2.2.2.1 L (h𝒢 L hL).1.1) S
    (fun L hL U hU => hcov U hU.1 ⟨latIn U L, isIntLat_latIn h (h𝒢 L hL).1 U, hU.2⟩)
  refine h1.trans ?_
  have d0 : (0 : ℝ) < de := by exact_mod_cast hde
  have t0 : (0 : ℝ) < t := by exact_mod_cast ht
  set C : ℝ := mass h₂ I₂ * ((de : ℝ) * t) ^ (2 + l) * ((t : ℝ) ^ 2 * (de : ℝ) ^ 2) with hC
  have h2 : ∀ U ∈ S, orbMass (MulAction.stabilizer (isom h) U) {L | L ∈ 𝒢 ∧ U ∈ primSp h L j (de ^ 2)} ≤
      orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) (de ^ 2)) * ENNReal.ofReal C := by
    intro U hU
    have dU := hdim U hU
    obtain ⟨hc, -, -, -⟩ := (_root_.GlobalTheory.Mass.Witt.witt_definite K V h hK hs hp).2 U
    have dW : Module.finrank K (perp h U) = 1 := by
      have := Submodule.finrank_add_eq_of_isCompl hc
      omega
    have a1 := (_root_.GlobalTheory.Mass.OrbMono.main (MulAction.stabilizer (isom h) U) (Submodule (𝓞 K) V)).1
      {L | L ∈ 𝒢 ∧ U ∈ primSp h L j (de ^ 2)}
      {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = t ^ 2 ∧ (∃ t : Finset V, t.card ≤ 1 ∧
        dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧
        discN (hRes h U) (latIn U L) = de ^ 2}
      (fun _ => 1) (fun _ => 1)
      (fun L hL => ⟨(h𝒢 L hL.1).1, (h𝒢 L hL.1).2.1, (h𝒢 L hL.1).2.2.1, (h𝒢 L hL.1).2.2.2, hL.2.2⟩)
      (fun _ _ => le_rfl)
    refine a1.trans ((orbMass_stabilizer_le K V h hK hs hp U (de ^ 2) (t ^ 2) T hT dW).trans ?_)
    have a3 := GlobalTheory.T.totalMass_integralLattices_bounded_det_line hM K (perp h U) (hRes h (perp h U)) hK (hRes_symm h hs _) (hRes_pd h hp _) dW
      V₂ h₂ I₂ hs₂ hI₂ (de * t) (Nat.mul_pos hde ht)
    rw [mul_pow, Nat.cast_mul] at a3
    rw [mul_assoc, hC, ENNReal.ofReal_mul (by positivity), hN]
    refine mul_le_mul' le_rfl (mul_le_mul' a3 (le_of_eq ?_))
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.sum_mul]
  refine (mul_le_mul' hsum le_rfl).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have e : (de : ℝ) ^ (4 + l) = (de : ℝ) ^ (2 + l) * (de : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add d0]
    congr 1
    push_cast
    ring
  rw [e, hC]
  ring

end GlobalTheory.Mass.PrimMeanOne
end

