module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PackageTie
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHasFlag
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0030
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0085

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearAbsMeasurableAndSplit
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff ENNReal

namespace GlobalTheory.NearMeas

theorem tsum_sub_eq {G : Type} (S T : Set G) (h : S ⊆ T) (f : G → ℝ≥0∞) :
    ∑' γ : S, f γ.1 = ∑' γ : T, S.indicator f γ.1 := by
  rw [tsum_subtype S f, tsum_subtype T (S.indicator f), Set.indicator_indicator,
    Set.inter_eq_right.mpr h]

private theorem continuous_ph' (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : IsDSData B d) :
    Continuous (ph B d) := by
  show Continuous fun g : B.I.Ginf =>
    ((∏ v, d v : ℝ) : ℂ) * star (∏ v, ⟪B.w v, B.σ v (uMat (g v)) (B.w v)⟫_ℂ)
  refine continuous_const.mul (continuous_star.comp (continuous_finsetProd _ fun v _ => ?_))
  obtain ⟨-, ⟨-, -, ⟨-, -, hcont⟩, -⟩, -⟩ := h v
  have hmat : Continuous fun g : B.I.Ginf => uMat (g v) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v))
  have hc : Continuous fun g : B.I.Ginf => B.σ v (uMat (g v)) (B.w v) :=
    (hcont (B.w v)).comp_continuous hmat fun g => (g v).2
  exact continuous_const.inner hc

theorem continuous_phe (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : IsDSData B d) :
    Continuous (phe B d) := by
  obtain ⟨hlc, -⟩ := B.e_adm
  show Continuous fun x : B.I.GA => ph B d x.1 * B.e x.2
  exact ((continuous_ph' B d h).comp continuous_fst).mul (hlc.continuous.comp continuous_snd)

private theorem continuous_conj_by_inv (B : RowsAut) (γ : B.I.GA) :
    Continuous fun x : B.I.GA => x⁻¹ * γ * x :=
  (continuous_inv.mul continuous_const).mul continuous_id

private theorem measurable_indicator_nearNe_phe (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : IsDSData B d)
    (γ : B.I.GA) :
    Measurable fun x : B.I.GA =>
      {x : B.I.GA | γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x}.indicator
        (fun x => ‖phe B d (x⁻¹ * γ * x)‖ₑ) x := by
  have hc : Continuous fun x : B.I.GA => phe B d (x⁻¹ * γ * x) :=
    (continuous_phe B d h).comp (continuous_conj_by_inv B γ)
  have hd : ∀ v, Continuous fun x : B.I.GA => dHS (uMat ((x⁻¹ * γ * x).1 v)) := fun v =>
    (GlobalTheory.Count.CartanSize.cartan_size _ (B.I.ε v)).1.comp
      ((continuous_apply v).comp (continuous_fst.comp (continuous_conj_by_inv B γ)))
  have hcl : IsClosed {x : B.I.GA | ∀ v, dHS (uMat ((x⁻¹ * γ * x).1 v)) ≤ epN B} := by
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_le (hd v) continuous_const
  have hne : MeasurableSet {x : B.I.GA | phe B d (x⁻¹ * γ * x) ≠ 0} :=
    hc.measurable (measurableSet_singleton 0).compl
  have hset : MeasurableSet {x : B.I.GA | γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x} := by
    have heq : {x : B.I.GA | γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x} =
        ({x : B.I.GA | γ ∈ B.I.GFset} ∩ ({x : B.I.GA | phe B d (x⁻¹ * γ * x) ≠ 0} ∩
          {x : B.I.GA | ∀ v, dHS (uMat ((x⁻¹ * γ * x).1 v)) ≤ epN B})) ∩ {x : B.I.GA | γ ≠ 1} := by
      ext x
      rfl
    rw [heq]
    exact ((MeasurableSet.const _).inter (hne.inter hcl.measurableSet)).inter (MeasurableSet.const _)
  exact Measurable.indicator hc.enorm.measurable hset

theorem nearAbs_measurable_and_split : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → Measurable (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) ∧ ∀ x : B.I.GA, Summable (fun γ : B.I.GFset => ‖phe B d (x⁻¹ * γ.1 * x)‖) → ENNReal.ofReal ‖kern B.I (phe B d) x x - phe B d 1‖ ≤ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x + GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x := by
  intro B d h
  classical
  refine ⟨?_, ?_⟩
  · have hcount : Countable B.I.GFset := (GlobalTheory.RatDiscrete.countable_GFset B.I).to_subtype
    have heq : GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d = fun x => ∑' γ : B.I.GFset,
        {x : B.I.GA | γ.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x}.indicator
          (fun x => ‖phe B d (x⁻¹ * γ.1 * x)‖ₑ) x := by
      funext x
      exact tsum_sub_eq (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x) B.I.GFset (fun γ hγ => hγ.1.1)
        (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ)
    rw [heq]
    exact Measurable.tsum fun γ => measurable_indicator_nearNe_phe B d h γ.1
  · intro x hsum
    have hone : (1 : B.I.GA) ∈ B.I.GFset := (GlobalTheory.RatDiscrete.ratSub B.I).one_mem
    let o : B.I.GFset := ⟨1, hone⟩
    have hs : Summable fun γ : B.I.GFset => phe B d (x⁻¹ * γ.1 * x) := hsum.of_norm
    have hk : kern B.I (phe B d) x x = ∑' γ : B.I.GFset, phe B d (x⁻¹ * γ.1 * x) := rfl
    have h1 : phe B d 1 = phe B d (x⁻¹ * o.1 * x) := by simp [o]
    rw [hk, h1, hs.tsum_eq_add_tsum_ite o, add_sub_cancel_left]
    have hgn : Summable fun γ : B.I.GFset =>
        ‖if γ = o then (0 : ℂ) else phe B d (x⁻¹ * γ.1 * x)‖ := by
      refine hsum.of_nonneg_of_le (fun _ => norm_nonneg _) fun γ => ?_
      by_cases hγ : γ = o <;> simp [hγ]
    have hsub1 : GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x ⊆ B.I.GFset := fun γ hγ => hγ.1.1
    have hsub2 : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSet B d x ⊆ B.I.GFset := fun γ hγ => hγ.1
    calc ENNReal.ofReal ‖∑' γ : B.I.GFset, if γ = o then (0 : ℂ) else phe B d (x⁻¹ * γ.1 * x)‖
        ≤ ENNReal.ofReal (∑' γ : B.I.GFset,
            ‖if γ = o then (0 : ℂ) else phe B d (x⁻¹ * γ.1 * x)‖) :=
          ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hgn)
      _ = ∑' γ : B.I.GFset, ‖if γ = o then (0 : ℂ) else phe B d (x⁻¹ * γ.1 * x)‖ₑ := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hgn]
          simp only [ofReal_norm]
      _ ≤ ∑' γ : B.I.GFset,
            ((GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x).indicator (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ) γ.1 +
              (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSet B d x).indicator
                (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ) γ.1) := by
          refine ENNReal.tsum_le_tsum fun γ => ?_
          by_cases hγ : γ = o
          · simp [hγ]
          have hγ1 : γ.1 ≠ 1 := fun h' => hγ (Subtype.ext h')
          rw [if_neg hγ]
          by_cases hn : IsNear B d (epN B) x γ.1
          · have hm : γ.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearNe B d x := ⟨hn, hγ1⟩
            rw [Set.indicator_of_mem hm]
            exact le_self_add
          · have hm : γ.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSet B d x := ⟨γ.2, hn⟩
            rw [Set.indicator_of_mem hm]
            exact le_add_self
      _ = GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x + GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x := by
          rw [ENNReal.tsum_add]
          exact congrArg₂ (· + ·)
            (tsum_sub_eq _ _ hsub1 (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ)).symm
            (tsum_sub_eq _ _ hsub2 (fun γ => ‖phe B d (x⁻¹ * γ * x)‖ₑ)).symm

end GlobalTheory.NearMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalIntegralTensorBoundHypProof
section
noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Formalism.BasicNotions

namespace GlobalTheory.TensHS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hsNormSq_eq_sum_std {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) :
    Formalism.MainNotions.S.hsNormSq A = Formalism.L2.SG.RealObj.hs2 A := by
  unfold Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner Formalism.L2.SG.RealObj.hs2
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hsNormSq_of_tens {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (A : X.Vpi u' →L[ℂ] X.Vpi u) (J : ∀ v, X.Vloc u' v →L[ℂ] X.Vloc u v)
    (hA : ∀ y, A (X.tensU u' y) = X.tensU u (fun v => J v (y v))) :
    Formalism.MainNotions.S.hsNormSq A = ∏ v, Formalism.MainNotions.S.hsNormSq (J v) := by
  obtain ⟨hon, hsp⟩ := Formalism.L2.SG.RealObj.EnergyCut.tens_onb X u'
  let B := OrthonormalBasis.mk hon hsp
  have hB : ∀ i, B i = X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v)) := fun i => by simp [B]
  rw [hsNormSq_eq_sum_std]
  simp only [hsNormSq_eq_sum_std]
  unfold Formalism.L2.SG.RealObj.hs2
  rw [Formalism.L2.SG.RealObj.InfCut.hsb_indep (stdOrthonormalBasis ℂ (X.Vpi u')) B]
  simp only [hB, hA, Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u) (X.tensU_inner u), ← Finset.prod_pow]
  rw [Fintype.prod_sum]

theorem hsNormSq_nonneg {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) : 0 ≤ Formalism.MainNotions.S.hsNormSq A := by
  rw [hsNormSq_eq_sum_std]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem tensC_holds : GlobalTheory.TypeAsm.TensC := by
  intro D X u γ νl hσ
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  haveI : ∀ v, CompleteSpace (X.Vloc u v) := fun v => FiniteDimensional.complete ℂ (X.Vloc u v)
  haveI := hσ
  have hWc : Continuous (X.Wu u) := (X.Wu_spec u).2.2.1
  have hfac : ∀ y, (Formalism.L2.SG.TermOp.OO (Measure.pi νl) Set.univ (X.Wu u) (X.Wu u) γ) (X.tensU u y) =
      X.tensU u (fun v => (Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (γ v)) (y v)) := by
    intro y
    have h := Formalism.L2.SG.RealObj.RankOneTensors.oo_factor νl (X.tensU u) (X.tensU u) (X.tensU_inner u)
      (X.tensU_inner u) (X.tensU_span u) (X.Wloc u) (X.Wloc u) (X.Wloc_cont u) (X.Wloc_cont u)
      (X.Wu u) (X.Wu u) hWc hWc (X.Wu_tens u) (X.Wu_tens u) γ y
    simpa only [Formalism.L2.SG.RealObj.Jv, Formalism.L2.SG.TermOp.OO, Measure.restrict_univ] using h
  have hhs := hsNormSq_of_tens X u u _ _ hfac
  have hn := Formalism.L2.SG.PackageTie.norm_hsEmb_sq
    (Formalism.L2.SG.TermOp.OO (Measure.pi νl) Set.univ (X.Wu u) (X.Wu u) γ)
  refine le_of_eq ?_
  rw [← Real.sqrt_sq (norm_nonneg _), hn, hhs]
  have hprod : ∏ v, Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (γ v)) =
      (∏ v, Real.sqrt (Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (γ v)))) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun v _ => (Real.sq_sqrt (hsNormSq_nonneg _)).symm
  rw [hprod, Real.sqrt_sq (Finset.prod_nonneg fun v _ => Real.sqrt_nonneg _)]

end GlobalTheory.TensHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalDecompositionLocalNondegenerate
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DecompOrth

variable {D : D7}

theorem mem_orth_of_basis {n : ℕ} (U : Submodule D.host.E (VS D).V)
    (b : Module.Basis (Fin n) D.host.E U) (y : (VS D).V)
    (hy : ∀ i, (VS D).hT (b i : (VS D).V) y = 0) : y ∈ orth (VS D) U := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro u hu
  have hu' : u = ∑ i, b.repr ⟨u, hu⟩ i • (b i : (VS D).V) := by
    have := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    exact this.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hu', map_sum]
  simp [hy]

theorem exists_decomp (U : Submodule D.host.E (VS D).V) (hU : U ⊓ orth (VS D) U = ⊥)
    (x : (VS D).V) : ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b := by
  let b := Module.finBasis D.host.E U
  let L : U →ₗ[D.host.E] (Fin (Module.finrank D.host.E U) → D.host.E) :=
    LinearMap.pi (fun i => ((VS D).hT (b i : (VS D).V)).comp U.subtype)
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have hy' : ∀ i, (VS D).hT (b i : (VS D).V) y = 0 := fun i => congrFun hy i
    have hmem : (y : (VS D).V) ∈ U ⊓ orth (VS D) U := ⟨y.2, mem_orth_of_basis U b y hy'⟩
    rw [hU] at hmem
    exact Subtype.ext ((Submodule.mem_bot _).1 hmem)
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨y, hy⟩ := hsurj (fun i => (VS D).hT (b i : (VS D).V) x)
  refine ⟨x - y, mem_orth_of_basis U b _ (fun i => ?_), y, y.2, by abel⟩
  have := congrFun hy i
  simp only [L, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [map_sub, this, sub_self]

theorem gram_det_ne_zero {n : ℕ} (U : Submodule D.host.E (VS D).V) (hU : U ⊓ orth (VS D) U = ⊥)
    (b : Module.Basis (Fin n) D.host.E U) :
    (Matrix.of fun i j => (VS D).hT (b i : (VS D).V) (b j : (VS D).V)).det ≠ 0 := by
  intro h
  obtain ⟨α, hα0, hα⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hα0
  have hy : ∀ i, (VS D).hT (b i : (VS D).V) (((∑ j, α j • b j : U)) : (VS D).V) = 0 := by
    intro i
    have := congrFun hα i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Submodule.coe_sum, map_sum]
    simpa [mul_comm] using this
  have hmem : ((∑ j, α j • b j : U) : (VS D).V) ∈ U ⊓ orth (VS D) U :=
    ⟨Subtype.prop _, mem_orth_of_basis U b _ hy⟩
  rw [hU, Submodule.mem_bot] at hmem
  have h0 : ∑ j, α j • b j = 0 := Subtype.ext hmem
  funext j
  exact Fintype.linearIndependent_iff.1 b.linearIndependent α h0 j

end GlobalTheory.DecompOrth

namespace GlobalTheory.DecompOrth

variable {D : D7}

noncomputable def formLeft (Z : LocDat D) (p : PlF D) (w : Vp D p) : Vp D p →ₗ[(D.s.atP p).Ep] (D.s.atP p).Ep where
  toFun v := LocFacts₂ Z.M p v w
  map_add' x y := (locH Z p).h_add_left x y w
  map_smul' a x := (locH Z p).h_smul_left a x w

theorem formLeft_apply (Z : LocDat D) (p : PlF D) (w v : Vp D p) :
    formLeft Z p w v = LocFacts₂ Z.M p v w := rfl

theorem eq_zero_of_local_orth (U : Submodule D.host.E (VS D).V) (hU : U ⊓ orth (VS D) U = ⊥)
    (Z : LocDat D) (p : PlF D) (v : Vp D p)
    (hv : v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)))
    (horth : ∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) : v = 0 := by
  let b := Module.finBasis D.host.E U
  have hspan : Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) ≤
      Submodule.span (D.s.atP p).Ep (Set.range fun j => baseChange₂ D p (b j : (VS D).V)) := by
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    have hu' : u = ∑ i, b.repr ⟨u, hu⟩ i • (b i : (VS D).V) := by
      have := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hu', map_sum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [baseChange_smul₂]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hspan hv)
  set G := Matrix.of fun i j => (VS D).hT (b i : (VS D).V) (b j : (VS D).V) with hGdef
  set A := G.map (D.s.atP p).ιE with hA
  have hAβ : Matrix.mulVec A β = 0 := by
    funext i
    have h1 := horth (b i) (b i).2
    have h2 : LocFacts₂ Z.M p (∑ j, β j • baseChange₂ D p (b j : (VS D).V)) (baseChange₂ D p (b i : (VS D).V)) =
        formLeft Z p (baseChange₂ D p (b i : (VS D).V)) (∑ j, β j • baseChange₂ D p (b j : (VS D).V)) := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum] at h1
    simp only [map_smul, smul_eq_mul] at h1
    simp only [formLeft_apply, baseChangeAt_form Z.M p (Z.hcj p), brS] at h1
    simp only [Matrix.mulVec, dotProduct, hA, hGdef, Matrix.map_apply, Matrix.of_apply, Pi.zero_apply]
    simpa [mul_comm] using h1
  have hdet : IsUnit A.det := by
    rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 (gram_det_ne_zero U hU b)).map _
  have hβ : β = 0 := by
    have := congrArg (fun w => Matrix.mulVec A⁻¹ w) hAβ
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  simp [hβ]

end GlobalTheory.DecompOrth

theorem GlobalTheory.decomp_orth_complement : ∀ (D : D7) (U : Submodule D.host.E (VS D).V), U ⊓ orth (VS D) U = ⊥ → (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) ∧ ∀ (Z : LocDat D) (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) → (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0 :=
  fun _ U hU => ⟨GlobalTheory.DecompOrth.exists_decomp U hU,
    fun Z p v hv horth => GlobalTheory.DecompOrth.eq_zero_of_local_orth U hU Z p v hv horth⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PointsOfFlagTypeSetMeasurableAndInvariant
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagMeas

theorem typeSet_measurable_invariant : ∀ (I : AutInst) (a : ℕ) (j : Fin a → ℕ) (B : Set (Fin a → ℝ)), MeasurableSet B → MeasurableSet (typeSet I j B) ∧ (∀ γ ∈ I.GFset, ∀ x ∈ typeSet I j B, γ * x ∈ typeSet I j B) ∧ ∀ x ∈ typeSet I j B, ∀ k ∈ I.Kset, (x.1, x.2 * k) ∈ typeSet I j B := by
  intro I a j B hB
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨s, hs, hm, he⟩ := type_measurable I a j
    have : typeSet I j B = {x : I.GA | ∃ τ, HasType I x j τ} ∩ s ⁻¹' B := by
      ext x
      constructor
      · rintro ⟨τ, h1, h2⟩
        exact ⟨⟨τ, h2⟩, by rw [Set.mem_preimage, he x τ h2]; exact h1⟩
      · rintro ⟨⟨τ, h2⟩, h1⟩
        rw [Set.mem_preimage, he x τ h2] at h1
        exact ⟨τ, h1, h2⟩
    rw [this]
    exact hm.inter (hs hB)
  · rintro γ ⟨g, hg, h1, h2⟩ x ⟨τ, hτ, h⟩
    exact ⟨τ, hτ, ((GlobalTheory.PointEquivariance.equivariance I x g γ hg h1 h2).2.2.2.2.1 a j τ).2 h⟩
  · rintro x ⟨τ, hτ, h⟩ k hk
    refine ⟨τ, hτ, GlobalTheory.PointEquivariance.hasType_of I x (x.1, x.2 * k) (OrderIso.refl _) ?_
      (fun _ => rfl) (fun _ => rfl) j τ h⟩
    have e : ((x.1, x.2 * k) : I.GA) = x * (1, k) := Prod.ext (mul_one _).symm rfl
    rw [e]
    exact (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I x (1, k)).1 hk

end GlobalTheory.FlagMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalAutomorphismLocalExtensionMovesLattices
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatLocMove

variable {D : D7}

theorem isLattice_gmap' (g : GV D) (A : LV D) (hA : Submodule.IsLattice D.host.E A) :
    Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g A) := by
  exact Submodule.IsLattice.of_fg _ (hA.fg.map _)

theorem finrank_Vp_eq (p : PlF D) : Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.r, Ranks.rS]
  omega

end GlobalTheory.RatLocMove

namespace GlobalTheory.RatLocMove

open GlobalTheory.LocExt

variable {D : D7}

theorem localExtension_isometryFixingFrames_mem_localUnitary {u u' : D.what₂.Word}
    (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS)
    (hB : Based Z FP (Tu D u) (Tu D u') F F') (h : GV D) (hh : h ∈ H0 F F') (p : PlF D)
    (g' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hg : Ext p h g') : g' ∈ (FP p).UW0 := by
  obtain ⟨hiso, hF, hF'⟩ := hh
  obtain rfl := locEquiv_unique p h g' hg
  refine Subgroup.subset_closure ⟨locEquiv_unitary Z p h hiso, fun b => ⟨?_, ?_⟩⟩
  · rw [(hB p).1]
    show locEquiv p h (frFac Z.δ p b • baseChange₂ D p (frame F b)) = _
    rw [map_smul, locEquiv_ext p h, hF b]
    rfl
  · rw [(hB p).2.1]
    show locEquiv p h (frFac Z.δ p b • baseChange₂ D p (frame F' b)) = _
    rw [map_smul, locEquiv_ext p h, hF' b]
    rfl

theorem rat_ext_moves : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → (∀ (g : GV D) (p : PlF D), ∃! g', Ext p g g') ∧ (∀ h ∈ H0 F F', ∀ p g', Ext p h g' → g' ∈ (FP p).UW0) ∧ (∀ (g : GV D) p g' (Λ : LV D), Ext p g g' → lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap g Λ) = LocNG.img g' (lattice₂ D Z.M p Λ)) ∧ ∀ h ∈ H0 F F', ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∃ y', LocOver (Formalism.HermitianLatticesTheory.gmap h Λ) y' ∧ RMoves h y y' := by
  intro D X Y u u' F F' w _ _ Z FP hB hRel
  refine ⟨fun g p => ⟨locEquiv p g, locEquiv_ext p g, fun g' h => locEquiv_unique p g g' h⟩,
    fun h hh p g' hg => localExtension_isometryFixingFrames_mem_localUnitary F F' Z FP hB h hh p g' hg, ?_, ?_⟩
  · intro g p g' Λ hg
    obtain rfl := locEquiv_unique p g g' hg
    exact (locEquiv_img Z p g Λ).symm
  · intro h hh Λ y hov
    have hmem : ∀ p, locEquiv p h ∈ (FP p).UW0 := fun p =>
      localExtension_isometryFixingFrames_mem_localUnitary F F' Z FP hB h hh p _ (locEquiv_ext p h)
    have hact := fun p => _root_.GlobalTheory.InnerDatumAct.exists_mulAction (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
      (finrank_Vp_eq p) (hRel p)
    choose act hmv _ using hact
    let y' : Dat Z FP := fun p => (act p).smul ⟨locEquiv p h, hmem p⟩ (y p)
    have hmoves : ∀ p, LocNG.Datum.Moves (locEquiv p h) (y p) (y' p) := fun p =>
      ((hmv p) ⟨locEquiv p h, hmem p⟩ (y p) (y' p)).2 rfl
    refine ⟨y', ⟨isLattice_gmap' h Λ hov.1, fun p => ?_⟩, fun p => ⟨locEquiv p h, locEquiv_ext p h, hmoves p⟩⟩
    obtain ⟨τ, hτ, hL⟩ := hov.2 p
    have hm := (GlobalTheory.T.unitaryComplement_moves_local_terms_with_data (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
      (finrank_Vp_eq p) (hRel p) (locEquiv p h) (hmem p) (y p) (y' p) τ hτ (hmoves p)).1
    refine ⟨_, hm, ?_⟩
    show LocNG.img (locEquiv p h) τ.abelian₂ = _
    rw [hL, locEquiv_img Z p h Λ]

end GlobalTheory.RatLocMove
end
end

