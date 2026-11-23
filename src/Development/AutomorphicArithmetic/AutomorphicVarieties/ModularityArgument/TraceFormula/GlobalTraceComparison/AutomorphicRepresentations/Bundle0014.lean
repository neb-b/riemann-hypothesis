module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0007
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0008
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA
public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0066
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0046
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitCentreMulTor

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPSupp
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PS

open MeasureTheory

section Abs

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private theorem fix_proj (S : Submodule ℂ K) [S.HasOrthogonalProjection] (m : K →L[ℂ] K)
    (hs : ∀ x y, inner ℂ (m x) y = inner ℂ x (m y)) (hS : ∀ x ∈ S, m x ∈ S) (w : K) (hw : m w = w) :
    m (S.starProjection w) = S.starProjection w := by
  set p := S.starProjection w with hp
  have hpS : p ∈ S := Submodule.starProjection_apply_mem S w
  have hq : w - p ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal w
  have hmq : m (w - p) ∈ Sᗮ := by
    rw [Submodule.mem_orthogonal] at hq ⊢
    intro u hu
    rw [← hs]
    exact hq _ (hS u hu)
  have h1 : m p - p ∈ S := S.sub_mem (hS p hpS) hpS
  have h2 : m p - p ∈ Sᗮ := by
    have e : m p - p = (w - p) - m (w - p) := by
      rw [map_sub, hw]; abel
    rw [e]
    exact Sᗮ.sub_mem hq hmq
  have h3 : m p - p = 0 := by
    have := (Submodule.mem_orthogonal S _).1 h2 _ h1
    exact inner_self_eq_zero.1 this
  exact sub_eq_zero.1 h3

end Abs

section Mul

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} (c : X → ℝ)

private noncomputable def mulL (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  by apply _root_.UpperTheory.Reformulated.B.MultiplicationNormBound.mulL <;> assumption

private theorem mulL_ae (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) (f : Lp ℂ 2 ν) :
    (mulL c hc hb f : X → ℂ) =ᵐ[ν] fun x => (c x : ℂ) * (f : X → ℂ) x :=
  by apply _root_.UpperTheory.Reformulated.B.MulLinearAe.mulL_ae <;> assumption

private theorem mulL_inner (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) (f g : Lp ℂ 2 ν) :
    inner ℂ (mulL c hc hb f) g = inner ℂ f (mulL c hc hb g) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulL_ae c hc hb f, mulL_ae c hc hb g] with x h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

private def mulS (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) :
    PiLp 2 (fun _ : Unit => Lp ℂ 2 ν) →L[ℂ] PiLp 2 (fun _ : Unit => Lp ℂ 2 ν) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Unit => Lp ℂ 2 ν)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun i : Unit => (mulL c hc hb).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Unit => Lp ℂ 2 ν) i)).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Unit => Lp ℂ 2 ν)).toContinuousLinearMap)

private theorem mulS_apply (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1)
    (f : PiLp 2 (fun _ : Unit => Lp ℂ 2 ν)) (i : Unit) : mulS c hc hb f i = mulL c hc hb (f i) := rfl

private theorem mulS_inner (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1)
    (f g : PiLp 2 (fun _ : Unit => Lp ℂ 2 ν)) :
    inner ℂ (mulS c hc hb f) g = inner ℂ f (mulS c hc hb g) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulS_apply, mulS_apply, mulL_inner]

end Mul

section Cut

private def chi (a b s : ℝ) : ℝ := max 0 (1 - (max (a - s) 0 + max (s - b) 0))

private theorem chi_cont (a b : ℝ) : Continuous (chi a b) := by
  unfold chi
  fun_prop

private theorem chi_abs (a b s : ℝ) : |chi a b s| ≤ 1 := by
  have h1 : 0 ≤ max (a - s) 0 := le_max_right _ _
  have h2 : 0 ≤ max (s - b) 0 := le_max_right _ _
  have h3 : 0 ≤ chi a b s := le_max_left _ _
  rw [abs_of_nonneg h3]
  exact max_le zero_le_one (by linarith)

private theorem chi_eq_one {a b s : ℝ} (h : s ∈ Set.Icc a b) : chi a b s = 1 := by
  have h1 : max (a - s) 0 = 0 := max_eq_right (by linarith [h.1])
  have h2 : max (s - b) 0 = 0 := max_eq_right (by linarith [h.2])
  simp [chi, h1, h2]

private theorem chi_ne_one {a b s : ℝ} (h : s ∉ Set.Icc a b) : chi a b s ≠ 1 := by
  intro e
  have h1 : 0 ≤ max (a - s) 0 := le_max_right _ _
  have h2 : 0 ≤ max (s - b) 0 := le_max_right _ _
  have h3 : 1 ≤ 1 - (max (a - s) 0 + max (s - b) 0) := by
    unfold chi at e
    rcases max_choice (0 : ℝ) (1 - (max (a - s) 0 + max (s - b) 0)) with h | h
    · rw [h] at e; norm_num at e
    · rw [h] at e; exact e.ge
  have h4 : a - s ≤ 0 := by linarith [le_max_left (a - s) 0]
  have h5 : s - b ≤ 0 := by linarith [le_max_left (s - b) 0]
  exact h ⟨by linarith, by linarith⟩

end Cut

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PS

end

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.PS PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc MeasureTheory in
attribute [local instance] PositivityTheory.Rg.BcB.E.borelH in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pSupp_pf :
    PSupp := by
  intro E _ _ _ n D π a b v hv
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  have hl : Continuous (ldet : H E n 0 → ℝ) := continuous_ldet
  set c : H E n 0 → ℝ := fun x => chi a b (ldet x) with hcdef
  have hc : Measurable c := ((chi_cont a b).comp hl).measurable
  have hb : ∀ x, |c x| ≤ 1 := fun x => chi_abs a b _
  have hgen : ∀ f : Hs (ι := Unit) D, IsPiVec D π f → IsPiVec D π (mulS c hc hb f) := by
    intro f hf i
    obtain ⟨ψ, hψ, u, hu, hus, he⟩ := hf i
    refine ⟨ψ, hψ, fun s => (chi a b s : ℂ) * u s,
      (Complex.continuous_ofReal.comp (chi_cont a b)).mul hu, hus.mul_left, ?_⟩
    rw [mulS_apply]
    filter_upwards [mulL_ae c hc hb (f i), he] with x h1 h2
    rw [h1, h2]
    simp only [hcdef]
    ring
  have hS : ∀ f ∈ piSp D π Unit, mulS c hc hb f ∈ piSp D π Unit := by
    have hle : Submodule.span ℂ {f | IsPiVec D π f} ≤
        (piSp D π Unit).comap (mulS (ν := D.ν) c hc hb).toLinearMap := by
      refine Submodule.span_le.2 fun f hf => ?_
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span (hgen f hf))
    have hcl : IsClosed (((piSp D π Unit).comap
        (mulS (ν := D.ν) c hc hb).toLinearMap : Submodule ℂ _) : Set (Hs (ι := Unit) D)) :=
      (show IsClosed (piSp D π Unit : Set (Hs (ι := Unit) D)) from
        Submodule.isClosed_topologicalClosure _).preimage (mulS c hc hb).continuous
    exact fun f hf => Submodule.topologicalClosure_minimal _ hle hcl hf
  have hv1 : mulL c hc hb v = v := by
    refine Lp.ext ?_
    filter_upwards [mulL_ae c hc hb v, hv] with x h1 h2
    rw [h1]
    by_cases hx : ldet x ∈ Set.Icc a b
    · simp [hcdef, chi_eq_one hx]
    · simp [h2 hx]
  have hw : mulS c hc hb (vecM v fun _ : Unit => 1) = vecM v fun _ : Unit => 1 := by
    ext1 i
    rw [mulS_apply]
    show mulL c hc hb ((1 : ℂ) • v) = (1 : ℂ) • v
    rw [one_smul, hv1]
  have key := fix_proj (piSp D π Unit) (mulS c hc hb) (mulS_inner c hc hb) hS _ hw
  have h2 : mulL c hc hb (P0 D π v) = P0 D π v := by
    have := congrArg (fun f : Hs (ι := Unit) D => f ()) key
    exact this
  have h3 := mulL_ae c hc hb (P0 D π v)
  rw [h2] at h3
  filter_upwards [h3] with x h4 hx
  have h5 : ((c x : ℂ) - 1) * (P0 D π v : H E n 0 → ℂ) x = 0 := by
    rw [sub_mul, one_mul, ← h4, sub_self]
  rcases mul_eq_zero.1 h5 with h6 | h6
  · exfalso
    have h7 : (c x : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [sub_eq_zero.1 h6]; simp
    exact chi_ne_one hx (Complex.ofReal_injective h7)
  · exact h6
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PRangeW
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem ac_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : ac E n 0 = 1 := by
  unfold ac
  rw [zero_div, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_zero]
  rfl

private theorem test_trM {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]
    {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) (M : Matrix ι ι ℂ) :
    Continuous (trM Φ M) ∧ HasCompactSupport (trM Φ M) := by
  have e : trM Φ M = ∑ i, ∑ j, fun y => Φ i j y * M j i := by
    funext y
    simp [trM, Finset.sum_apply]
  constructor
  · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hΦ i j).1.mul continuous_const
  · rw [e]
    exact HasCompactSupport.finset_sum fun i _ => HasCompactSupport.finset_sum fun j _ => (hΦ i j).2.mul_right

private theorem ldet_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {φ : H E n 0 → ℂ}
    (hc : HasCompactSupport φ) : ∃ N : ℕ, ∀ z, φ z ≠ 0 → |ldet z| ≤ N := by
  obtain ⟨R, hR⟩ := (hc.isCompact.image (continuous_abs.comp (continuous_ldet (E := E) (n := n)))).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_ge R
  exact ⟨N, fun z hz => (hR ⟨z, subset_tsupport _ hz, rfl⟩).trans hN⟩

private theorem cut_cont (N : ℕ) : Continuous fun t : ℝ => ((Dcy.chi N t : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp (Dcy.continuous_chi N)

private theorem cut_supp (N : ℕ) : HasCompactSupport fun t : ℝ => ((Dcy.chi N t : ℝ) : ℂ) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ((N : ℝ) + 1)) fun t ht => by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at ht
    rw [Dcy.chi_eq_zero ht.le, Complex.ofReal_zero]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.rangeW_pf :
    Rep → RangeW := by
  intro hR E _ _ _ n ι _ s p hF m ψ hψ x₀ h₀
  obtain ⟨N, hN⟩ := ldet_bound (test_trM m.t s.M).2
  set u : ℝ → ℂ := fun t => ((Dcy.chi N t : ℝ) : ℂ) with hu
  have rep := fun y => hR E n ι s m ψ hψ u (cut_cont N) (cut_supp N) y
  have key : ∀ y : H E n 0, ldet y = 0 →
      ∫ x, ψ.1 x.1 * m.G y x * u (ldet x) ∂s.D.ν = ∫ z, m.φ z * ψ.1 (thetaA E n (y.1 * z.1)) ∂s.D.μ := by
    intro y hy
    rw [(rep y).2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : m.φ z = 0
    · simp [hz]
    · have h1 : |(-(ldet y + ldet z))| ≤ N := by
        rw [hy, zero_add, abs_neg]
        exact hN z hz
      simp only [hu, Dcy.chi_eq_one h1, Complex.ofReal_one, mul_one]
  rw [← key x₀ h₀]
  have hG : ∀ x, ψ.1 x.1 * m.G x₀ x * u (ldet x) =
      ∑ b, (p.w b).1 x₀.1 * (ψ.1 x.1 * m.G (p.x b) x * u (ldet x)) := by
    intro x
    rw [hF m x₀ x, h₀, ac_zero, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [one_mul]
    ring
  simp_rw [hG]
  rw [integral_finsetSum _ fun b _ => ((rep (p.x b)).1).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, key (p.x b) (p.zero b)]

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PSatAll
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

noncomputable section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem twist_loc (w : Pl E) (g : GLw n (GlobalTheory.EulerTw.cPl E w)) :
    thF E n (locGL E n (GlobalTheory.EulerTw.cPl E w) g) = locGL E n w (thetaGL n (RingHom.id _)
      (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g)) := by
  refine GlobalTheory.EulerTwU.gl_ext fun v => ?_
  rw [GlobalTheory.EulerTwU.pc_thF]
  by_cases h : v = w
  · subst h
    rw [pLoc_locGL, pLoc_locGL]
  · have h' : GlobalTheory.EulerTw.cPl E v ≠ GlobalTheory.EulerTw.cPl E w := fun e =>
      h (by rw [← GlobalTheory.EulerTwU.cPl_cPl v, e, GlobalTheory.EulerTwU.cPl_cPl])
    rw [pLoc_locGL_of_ne h', pLoc_locGL_of_ne h]
    exact (congrArg (thetaGL n (RingHom.id _)) (map_one _)).trans (map_one _)

private theorem twist_conj (w : Pl E) (g : GLw n (GlobalTheory.ThetaSatake.cw w)) :
    thF E n (locGL E n w (PhiU n (w.adicCompletion E) * GlobalTheory.CompanionTheory.ConjSat.flipGL w g * (PhiU n (w.adicCompletion E))⁻¹)) =
      locGL E n (GlobalTheory.ThetaSatake.cw w) g := by
  have e : thetaGL n (RingHom.id _) (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g) =
      PhiU n (w.adicCompletion E) * GlobalTheory.CompanionTheory.ConjSat.flipGL w g * (PhiU n (w.adicCompletion E))⁻¹ := by
    rw [GlobalTheory.CompanionTheory.ConjSat.flipGL_eq]
    rfl
  rw [← e, ← twist_loc w g, GlobalTheory.EulerTwU.thF_thF]
  rfl

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.satAll_pf :
    SatAll := by
  intro E _ _ _ n π w B y hy h0
  have hne : (⟨y, hy⟩ : π.V) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  refine ⟨fun hB hf => ?_, fun hB hf => ?_⟩
  · rw [CG.hasSat_mk] at hB
    have hx : (⟨y, hy⟩ : π.V) ∈ fixed (π.locRep w) (KGL w (n := n)) :=
      GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hf k hk)
    exact (hB.2 _ hx hne).map (ρ' := rw' n w false) π.V.subtype (fun _ _ => rfl) h0
  · rw [CG.hasSat_mk] at hB
    let σ : Representation ℂ (GLw n w) π.V := π.finPart.comp (jw n w true)
    let k := PhiU n (w.adicCompletion E)
    let T : π.V ≃ₗ[ℂ] π.V := LinearEquiv.ofLinear (σ k⁻¹) (σ k)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    have hs : HasSatGL w σ (B.map (·⁻¹)) :=
      GlobalTheory.ThetaSatake.hasSatGL_of_invT (GlobalTheory.ThetaSatake.cloc w) (conjLoc_spec _ w).2.2
        (GlobalTheory.ThetaSatake.absNorm_cw w).symm T (fun g x => ?_) hB
    · have hx : (⟨y, hy⟩ : π.V) ∈ fixed σ (KGL w (n := n)) :=
        GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hf k hk)
      exact (hs.2 _ hx hne).map (ρ' := rw' n w true) π.V.subtype (fun _ _ => rfl) h0
    · have e : π.locRep (GlobalTheory.ThetaSatake.cw w) g = σ (k * GlobalTheory.CompanionTheory.ConjSat.flipGL w g * k⁻¹) := by
        change π.finPart (locGL E n (GlobalTheory.ThetaSatake.cw w) g) = π.finPart (thF E n (locGL E n w _))
        rw [twist_conj]
      change σ (GlobalTheory.CompanionTheory.ConjSat.flipGL w g) (σ k⁻¹ x) = σ k⁻¹ (π.locRep (GlobalTheory.ThetaSatake.cw w) g x)
      rw [e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PSizes
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open PositivityTheory.Rg.Rs
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem centre_eq (τ : ℝ) : splitCentre E n τ = (An.tor E (fun _ : Fin n => τ) : GA E n) := by
  have h := GlobalTheory.CuspBoundSiegel.diagUnits_posIdele (E := E) n (Real.exp_pos τ)
  rw [Real.log_exp] at h
  rw [← h, DiscreteGroups.T1.G.Dcy.tor_eq]

private theorem logSize_centre (τ : ℝ) :
    logSize (splitCentre E n τ) ≤ 2 * Module.finrank ℚ E * |τ| := by
  rw [centre_eq]
  refine ((torNorm_holds E).2 n _).2.trans ?_
  have h : ‖(fun _ : Fin n => τ)‖ ≤ |τ| :=
    (pi_norm_le_iff_of_nonneg (abs_nonneg τ)).2 fun _ => by simp
  gcongr

private theorem logSize_inv' (g : GA E n) : logSize (g⁻¹) = logSize g := by
  unfold logSize
  rw [inv_inv, add_comm]

private theorem deg_top (g : GA E n) : deg g ⊤ = deg (1 : GA E n) ⊤ + logAbs g.val.det := by
  have e : (((1 : Matrix (Fin n) (Fin n) E)ᵀ : Matrix (Fin n) (Fin n) E) : Fin n → Fin n → E) =
      ⇑(Pi.basisFun E (Fin n)) := by
    ext i j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have hli : LinearIndependent E ((1 : Matrix (Fin n) (Fin n) E)ᵀ) := by
    rw [e]; exact (Pi.basisFun E (Fin n)).linearIndependent
  have hsp : Submodule.span E (Set.range ((1 : Matrix (Fin n) (Fin n) E)ᵀ)) = ⊤ := by
    rw [e]; exact (Pi.basisFun E (Fin n)).span_eq
  have h1 := D1.degBasis E n n g 1 hli
  have h2 := D1.degBasis E n n 1 1 hli
  have h3 := D1.degAdelic E n n 1 g g 1 hli (by simp)
  rw [mul_one] at h3
  rw [hsp] at h1 h2
  rw [← h1, ← h2, h3]

private theorem abs_logAbs_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA E n,
    |logAbs g.val.det| ≤ C * (1 + logSize g) := by
  obtain ⟨C, hC, h⟩ := degRight E n
  refine ⟨C, hC, fun g => abs_le.2 ⟨?_, ?_⟩⟩
  · have h1 := h g g⁻¹ ⊤
    rw [mul_inv_cancel, logSize_inv', deg_top g] at h1
    linarith
  · have h1 := h 1 g ⊤
    rw [one_mul, deg_top g] at h1
    linarith

private theorem sizes' : Sizes := by
  intro E _ _ _ n hn
  obtain ⟨C, hC, hdet⟩ := abs_logAbs_le (E := E) (n := n)
  obtain ⟨-, -, -, c₀, hc₀⟩ := D1.sizeBasic E n
  have hc : 0 ≤ 2 + |c₀| + C := by positivity
  refine ⟨2 + |c₀| + C, hc, fun x => ⟨?_, ?_, DiscreteGroups.T1.G.Dcy.redSize_nonneg _⟩⟩
  · set l := ldet x with hl
    set d : ℝ := (Module.finrank ℚ E : ℝ) with hd
    have hd0 : 0 < d := by
      rw [hd]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := E)
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set τ : ℝ := l / (n * d) with hτ
    set y : GA E n := splitCentre E n (-l / (n * d)) * x.1 with hy
    have hr : r0 x = redSize y := rfl
    have hx : x.1 = splitCentre E n τ * y := by
      rw [hy, ← mul_assoc, ← CuspidalL2GL.splitCentre_add]
      have : τ + -l / (n * d) = 0 := by rw [hτ]; ring
      rw [this, CuspidalL2GL.splitCentre_zero, one_mul]
    have hτle : 2 * d * |τ| ≤ 2 * |l| := by
      have hpos : 0 < (n : ℝ) * d := by positivity
      rw [hτ, abs_div, abs_of_pos hpos]
      have e : 2 * d * (|l| / (n * d)) = 2 * |l| / n := by field_simp
      rw [e]
      exact div_le_self (by positivity) hn0
    have hK : 2 * |l| + c₀ ≤ (2 + |c₀| + C) * (1 + |l|) := by
      have h1 := le_abs_self c₀
      have h2 := abs_nonneg l
      have h3 := abs_nonneg c₀
      nlinarith [mul_nonneg h3 h2, mul_nonneg hC h2]
    have key : redSize x.1 - (2 + |c₀| + C) * (1 + |l|) ≤ redSize y := by
      refine le_ciInf fun γ => ?_
      have h1 := DiscreteGroups.T1.G.Dcy.redSize_le x.1 γ
      have h2 : ratGL E n γ * x.1 = splitCentre E n τ * (ratGL E n γ * y) := by
        rw [hx, ← mul_assoc, ← CuspidalL2GL.splitCentre_comm, mul_assoc]
      rw [h2] at h1
      have h3 := hc₀ (splitCentre E n τ) (ratGL E n γ * y)
      have h4 : logSize (splitCentre E n τ) ≤ 2 * d * |τ| := logSize_centre τ
      linarith
    rw [hr]
    linarith
  · have h1 : |ldet x| ≤ C * (1 + logSize x.1) := hdet x.1
    have h2 := DiscreteGroups.T1.G.Dcy.logSize_nonneg x.1
    have h3 := abs_nonneg c₀
    nlinarith [mul_nonneg h3 h2]

theorem sizes_of_basic : Basic → Sizes := fun _ => sizes'

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

