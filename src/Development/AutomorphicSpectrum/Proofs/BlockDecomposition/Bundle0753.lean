module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0575
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0574
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0555
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0750
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0556
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0404

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionExistsAlt
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

namespace GlobalTheory.CompanionTheory.SecThrough

theorem secEx : SecEx := by
  intro E _ _ _ S₀ hS₀
  let f : Pl E → HeightOneSpectrum (𝓞 (maximalRealSubfield E)) := fun w => w.under (𝓞 (maximalRealSubfield E))
  have hex : ∀ y : Set.range f, ∃ u : Pl E, f u = y.1 ∧ ∀ w ∈ S₀, f w = y.1 → u = w := by
    rintro ⟨_, w₀, rfl⟩
    by_cases h : ∃ w ∈ S₀, f w = f w₀
    · obtain ⟨w, hw, hfw⟩ := h
      exact ⟨w, hfw, fun w' hw' _ => Finset.card_le_one.1 hS₀ w hw w' hw'⟩
    · exact ⟨w₀, rfl, fun w hw hfw => absurd ⟨w, hw, hfw⟩ h⟩
  let g : Set.range f → Pl E := fun y => (hex y).choose
  have hg : ∀ y, f (g y) = y.1 := fun y => (hex y).choose_spec.1
  have hg₀ : ∀ y, ∀ w ∈ S₀, f w = y.1 → g y = w := fun y => (hex y).choose_spec.2
  refine ⟨Set.range g, fun w => ⟨g ⟨f w, w, rfl⟩, ⟨⟨_, rfl⟩, hg _⟩, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨⟨y, rfl⟩, hy⟩
    exact congrArg g (Subtype.ext ((hg y).symm.trans hy))
  · intro w hw
    exact ⟨⟨f w, w, rfl⟩, hg₀ _ w hw rfl⟩
  · intro w hw
    refine ⟨⟨f w, w, rfl⟩, ?_⟩
    by_contra hne
    exact hw ⟨_, hne, hg _⟩

end GlobalTheory.CompanionTheory.SecThrough

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightsIntegralPullbackFormula
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
open Set Filter Topology

namespace GlobalTheory.CompanionTheory.MixZ

theorem lintegral_logNorm_locDens_lt_top : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B C : LB X} (φ : GlobalTheory.Weight q σ B) (_ : φ.IsCInf) (ψ : GlobalTheory.Weight q σ C) (_ : ψ.IsCInf)
      (g : GlobalTheory.CxPts q σ → ℝ) (S Z : Set (GlobalTheory.CxPts q σ)) {N : ℕ} (W : Fin N → X.Opens) (b : Fin N → C.ι)
      (a d : ∀ l, Γ(X, W l)),
    (∀ y : GlobalTheory.CxPts q σ, ∃ l, y ∈ ptsIn q σ (W l)) → (∀ l, W l ≤ C.U (b l)) →
    (∀ l, ∀ y ∈ ptsIn q σ (W l), y ∈ S → y ∉ Z →
      g y = Real.log ‖ev q σ (W l) (a l) y‖ - Real.log ‖ev q σ (W l) (d l) y‖ - ψ.φ (b l) y / 2) →
    IsOpen S → ContinuousOn g S → MeasurableSet Z →
    ∀ (j : Fin A.n) (K : Set (Fin D → ℂ)), K ⊆ (A.chart j).target → IsCompact K →
      ∫⁻ u in K \ (F ∘ (A.chart j).symm) ⁻¹' Z, S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| < ⊤ := by
  intro k _ X q σ D T _ A F hF hol B C φ hφ ψ hψ g S Z N W b a d hcov hWb hg hSo hgc hZ j K hKt hKc
  have hGc : ContinuousOn (F ∘ (A.chart j).symm) (A.chart j).target :=
    hF.comp_continuousOn (A.chart j).continuousOn_symm
  have hdc : ContinuousOn (locDens A (fun _ => φ.locPot.pullback F hF) j) (A.chart j).target :=
    locDensCont A _ (fun _ => isPotential_pullback_locPot A F hF hol φ hφ) j
  refine hKc.induction_on (p := fun s => ∫⁻ u in s \ (F ∘ (A.chart j).symm) ⁻¹' Z,
      S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| < ⊤) ?_ ?_ ?_ ?_
  · simp
  · intro s t hst ht
    exact (lintegral_mono_set (diff_subset_diff_left hst)).trans_lt ht
  · intro s t hs ht
    rw [union_diff_distrib]
    exact (lintegral_union_le _ _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hs, ht⟩)
  intro u0 hu0
  obtain ⟨l, hl⟩ := hcov (F ((A.chart j).symm u0))
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (F ⁻¹' ptsIn q σ (W l))) :=
    (A.chart j).isOpen_inter_preimage_symm ((isOpen_ptsIn _).preimage hF)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 ⟨hKt hu0, hl⟩
  set V := (A.chart j).target ∩ (A.chart j).symm ⁻¹' (F ⁻¹' ptsIn q σ (W l)) with hV
  set Bl := Metric.closedBall u0 (r / 2) with hBl
  have hBV : Bl ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBc : IsCompact Bl := isCompact_closedBall _ _
  have hBm : MeasurableSet Bl := Metric.isClosed_closedBall.measurableSet
  have hBt : Bl ⊆ (A.chart j).target := hBV.trans inter_subset_left
  refine ⟨Bl, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ (by linarith)), ?_⟩
  have hla : IntegrableOn (fun u => Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖) Bl :=
    (ReciprocityTheory.ChartRestriction.G.Geo.logAbsLocInt D V (fun u => ev q σ (W l) (a l) (F ((A.chart j).symm u))) hO
      (fun u hu => hol (W l) (a l) j u hu)).integrableOn_compact_subset hBV hBc
  have hld : IntegrableOn (fun u => Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖) Bl :=
    (ReciprocityTheory.ChartRestriction.G.Geo.logAbsLocInt D V (fun u => ev q σ (W l) (d l) (F ((A.chart j).symm u))) hO
      (fun u hu => hol (W l) (d l) j u hu)).integrableOn_compact_subset hBV hBc
  have hψc : ContinuousOn (fun u => ψ.φ (b l) (F ((A.chart j).symm u))) Bl := by
    intro u hu
    have hc : ContinuousAt (ψ.φ (b l)) (F ((A.chart j).symm u)) :=
      (hψ (b l) _ (ptsIn_mono (hWb l) (hBV hu).2)).continuousAt
    exact ContinuousAt.comp_continuousWithinAt (f := F ∘ (A.chart j).symm) hc
      ((hGc u (hBt hu)).mono hBt)
  have hlψ : IntegrableOn (fun u => |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) Bl :=
    (hψc.abs.div_const 2).integrableOn_compact hBc
  have hh : IntegrableOn (fun u => |Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
      |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
      |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) Bl :=
    (hla.abs.add hld.abs).add hlψ
  obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn (hdc.mono hBt)
  have hYm : MeasurableSet (Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z) := by
    have hc : Continuous (fun u : Bl => (F ∘ (A.chart j).symm) u.1) :=
      continuousOn_iff_continuous_restrict.1 (hGc.mono hBt)
    have h1 : MeasurableSet (Subtype.val '' ((fun u : Bl => (F ∘ (A.chart j).symm) u.1) ⁻¹' Z)) :=
      hBm.subtype_image (hc.measurable hZ)
    have h2 : Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z =
        Bl \ (Subtype.val '' ((fun u : Bl => (F ∘ (A.chart j).symm) u.1) ⁻¹' Z)) := by
      ext u
      constructor
      · rintro ⟨hu, hn⟩
        refine ⟨hu, ?_⟩
        rintro ⟨v, hv, rfl⟩
        exact hn hv
      · rintro ⟨hu, hn⟩
        exact ⟨hu, fun hz => hn ⟨⟨u, hu⟩, hz, rfl⟩⟩
    rw [h2]
    exact hBm.diff h1
  have hpt : ∀ u ∈ Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z,
      S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| ≤
      ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
        |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
        |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) * ENNReal.ofReal M := by
    rintro u ⟨huB, huZ⟩
    by_cases hS : F ((A.chart j).symm u) ∈ S
    · rw [indicator_of_mem hS]
      refine mul_le_mul' ?_ (ENNReal.ofReal_le_ofReal ?_)
      · rw [← ofReal_norm_eq_enorm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hg l _ (hBV huB).2 hS huZ, Real.norm_eq_abs]
        have h1 := abs_sub (Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖ -
          Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖)
          (ψ.φ (b l) (F ((A.chart j).symm u)) / 2)
        have h2 := abs_sub (Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖)
          (Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖)
        rw [abs_div, abs_two] at h1
        linarith
      · simpa using hM u huB
    · rw [indicator_of_notMem hS, zero_mul]
      exact zero_le
  calc ∫⁻ u in Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z,
        S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
          ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u|
      ≤ ∫⁻ u in Bl \ (F ∘ (A.chart j).symm) ⁻¹' Z,
        ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
          |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
          |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) * ENNReal.ofReal M :=
        setLIntegral_mono' hYm hpt
    _ ≤ ∫⁻ u in Bl,
        ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
          |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
          |ψ.φ (b l) (F ((A.chart j).symm u))| / 2) * ENNReal.ofReal M :=
        lintegral_mono_set diff_subset
    _ = (∫⁻ u in Bl,
        ENNReal.ofReal (|Real.log ‖ev q σ (W l) (a l) (F ((A.chart j).symm u))‖| +
          |Real.log ‖ev q σ (W l) (d l) (F ((A.chart j).symm u))‖| +
          |ψ.φ (b l) (F ((A.chart j).symm u))| / 2)) * ENNReal.ofReal M :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top hh.lintegral_lt_top ENNReal.ofReal_lt_top

end GlobalTheory.CompanionTheory.MixZ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceExists
section
open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitLevel

theorem exists_reps {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K K' : Subgroup G)
    (hc : IsCompact (K : Set G)) (ho : IsOpen (K' : Set G)) :
    ∃ X : Finset G, (∀ x ∈ X, x ∈ K) ∧ ∀ k ∈ K, ∃! x ∈ X, x⁻¹ * k ∈ K' := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  have hop : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.coe_subgroupOf]
    exact ho.preimage continuous_subtype_val
  haveI : Finite (K ⧸ K'.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hop
  haveI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)
  refine ⟨Finset.univ.image fun q : K ⧸ K'.subgroupOf K => ((q.out : K) : G), ?_, ?_⟩
  · intro x hx
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    exact q.out.2
  · intro k hk
    let q₀ : K ⧸ K'.subgroupOf K := QuotientGroup.mk ⟨k, hk⟩
    refine ⟨((q₀.out : K) : G), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have h : (q₀.out)⁻¹ * ⟨k, hk⟩ ∈ K'.subgroupOf K := QuotientGroup.eq.1 (QuotientGroup.out_eq' q₀)
      exact Subgroup.mem_subgroupOf.1 h
    · rintro x ⟨hx, hxk⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
      have h : q = q₀ := by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hxk)
      rw [h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem congSub_conj (w : Pl E) (n m : ℕ) : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ GlobalTheory.PrincCong.congSub w n m,
    k * k' * k⁻¹ ∈ GlobalTheory.PrincCong.congSub w n m := by
  rintro _ ⟨h, rfl⟩ _ ⟨h', hh', rfl⟩
  refine ⟨h * h' * h⁻¹, ?_, by simp⟩
  exact Subgroup.Normal.conj_mem h' hh' h

def lev (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (m b : ℕ) : Subgroup (GLw b w) :=
  GlobalTheory.PrincCong.congSub w b m ⊓ μ.ker.comap GeneralLinearGroup.det

theorem continuous_det (w : Pl E) (b : ℕ) :
    Continuous (GeneralLinearGroup.det : GLw b w → (w.adicCompletion E)ˣ) :=
  Units.continuous_iff.2 ⟨Continuous.matrix_det Units.continuous_val,
    Continuous.matrix_det (Units.continuous_val.comp continuous_inv)⟩

theorem isLevel_lev (w : Pl E) (hw : IsSplitAt w) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : IsOpen (μ.ker : Set (w.adicCompletion E)ˣ)) (m b : ℕ) :
    GlobalTheory.BCT.IsLevel (thL b w) (GlobalTheory.LFun.KGL w (n := b)) (lev w μ m b) := by
  refine ⟨?_, fun g hg => ((GlobalTheory.PrincCong.mem_congSub_iff w b m g).1 hg.1).1, fun k hk => ?_⟩
  · exact (GlobalTheory.PrincCong.isOpen_congSub w b m).inter (hμ.preimage (continuous_det w b))
  · have ht : thL b w = MonoidHom.id _ := by unfold thL; rw [if_pos hw]
    rw [ht]
    exact hk

theorem blk_mem {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : ℕ) (y : GLw a w × GLw b w)
    (h1 : y.1 ∈ GlobalTheory.PrincCong.congSub w a m) (h2 : y.2 ∈ GlobalTheory.PrincCong.congSub w b m) :
    blk h w y 0 ∈ GlobalTheory.PrincCong.congSub w n m := by
  rw [GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.blk_zero_eq, GlobalTheory.PrincCong.mem_congSub_iff]
  obtain ⟨k1, e1⟩ := (GlobalTheory.PrincCong.mem_congSub_iff w a m _).1 h1
  obtain ⟨k2, e2⟩ := (GlobalTheory.PrincCong.mem_congSub_iff w b m _).1 h2
  have hI1 := GlobalTheory.AdelicU.mem_GLint_iff.1 k1
  have hI2 := GlobalTheory.AdelicU.mem_GLint_iff.1 k2
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [CtLevel.dgM_val]
    exact CtLevel.blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ hI1.1 hI2.1 i j
  · rw [← map_inv, CtLevel.dgM_val]
    exact CtLevel.blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ hI1.2 hI2.2 i j
  · obtain ⟨i', rfl⟩ := (CtLevel.blkEq h).surjective i
    obtain ⟨j', rfl⟩ := (CtLevel.blkEq h).surjective j
    have hone : ∀ p q, (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (CtLevel.blkEq h p) (CtLevel.blkEq h q) =
        (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) (w.adicCompletion E)) p q := by
      intro p q
      simp [Matrix.one_apply, (CtLevel.blkEq h).injective.eq_iff]
    rw [hone]
    rcases i' with i' | i' <;> rcases j' with j' | j'
    · rw [(GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.dgM_entries h w y).1]
      simpa [Matrix.one_apply] using e1 i' j'
    · rw [CtLevel.dgM_val, CtLevel.dgMat, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply]
      simp
    · rw [CtLevel.dgM_val, CtLevel.dgMat, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply]
      simp
    · rw [(GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.dgM_entries h w y).2]
      simpa [Matrix.one_apply] using e2 i' j'

theorem splitEx : SplitEx := by
  intro E _ _ _ n w hw μ hμ m hm KB hKB
  have hKc := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2
  have ho := GlobalTheory.PrincCong.isOpen_congSub w n m
  have hle : GlobalTheory.PrincCong.congSub w n m ≤ GlobalTheory.LFun.KGL w (n := n) :=
    fun g hg => ((GlobalTheory.PrincCong.mem_congSub_iff w n m g).1 hg).1
  have hcl : IsClosed (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) := Subgroup.isClosed_of_isOpen _ ho
  have hc : IsCompact (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) := hKc.of_isClosed_subset hcl hle
  obtain ⟨X, hX, hXu⟩ := exists_reps (GlobalTheory.LFun.KGL w (n := n)) (GlobalTheory.PrincCong.congSub w n m) hKc ho
  refine ⟨GlobalTheory.PrincCong.congSub w n m, X, (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)).indicator 1,
    fun a => (lev w μ m a).prod (lev w μ m (n - a)), ?_, ho, hle, congSub_conj w n m, hX, hXu, ?_, ?_⟩
  · ext k
    rw [Subgroup.mem_subgroupOf, GlobalTheory.PrincCong.mem_congSub_iff, hKB k]
    exact Iff.rfl
  · refine ⟨ho, hc, ?_, fun k₁ hk₁ k₂ hk₂ g => ?_⟩
    · refine HasCompactSupport.of_support_subset_isCompact hc ?_
      intro g hg
      by_contra h
      exact hg (Set.indicator_of_notMem h _)
    · have hiff : k₁ * g * k₂ ∈ GlobalTheory.PrincCong.congSub w n m ↔ g ∈ GlobalTheory.PrincCong.congSub w n m := by
        rw [Subgroup.mul_mem_cancel_right _ hk₂, Subgroup.mul_mem_cancel_left _ hk₁]
      by_cases hg : g ∈ GlobalTheory.PrincCong.congSub w n m
      · rw [Set.indicator_of_mem (show _ ∈ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from hiff.2 hg),
          Set.indicator_of_mem (show _ ∈ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from hg)]
        rfl
      · rw [Set.indicator_of_notMem (show _ ∉ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from fun h => hg (hiff.1 h)),
          Set.indicator_of_notMem (show _ ∉ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from hg)]
  · intro a ha
    refine ⟨⟨_, _, rfl, isLevel_lev w hw μ hμ m a, isLevel_lev w hw μ hμ m (n - a)⟩, fun y hy => ⟨?_, ?_⟩⟩
    · exact blk_mem (Nat.add_sub_of_le ha) w m y hy.1.1 hy.2.1
    · have d1 : μ (GeneralLinearGroup.det y.1) = 1 := hy.1.2
      have d2 : μ (GeneralLinearGroup.det y.2) = 1 := hy.2.2
      rw [map_mul, map_pow, map_pow, d1, d2, one_pow, one_pow, one_mul]

end GlobalTheory.CompanionTheory.SplitLevel

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerExists
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.BCT Formalism.L2.Host PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B

namespace GlobalTheory.CompanionTheory.UnifFix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem conj_real (x : maximalRealSubfield E) :
    IsCMField.complexConj E (algebraMap (maximalRealSubfield E) E x) = algebraMap (maximalRealSubfield E) E x := by
  exact (IsCMField.complexConj E).commutes x

theorem cj_real (w : Pl E) (x : maximalRealSubfield E) :
    GlobalTheory.BCT.cj w (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E x)) =
      algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E x) := by
  unfold GlobalTheory.BCT.cj
  split_ifs with h
  · rw [h.choose_spec.2, conj_real]
  · rfl

theorem valuation_up (hU : GlobalTheory.BCT.Unr E) (w : Pl E) (x : maximalRealSubfield E) :
    w.valuation E (algebraMap (maximalRealSubfield E) E x) =
      (w.under (𝓞 (maximalRealSubfield E))).valuation (maximalRealSubfield E) x := by
  have := hU w
  have h1 := HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 (maximalRealSubfield E))) w x
  have he : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  rw [← h1, he, pow_one]

theorem neg_toAdd_unzero (a : WithZero (Multiplicative ℤ)) (h : a ≠ 0) (ha : a = WithZero.exp (-1 : ℤ)) :
    -Multiplicative.toAdd (WithZero.unzero h) = 1 := by
  subst ha
  rfl

theorem unifEx : UnifEx := by
  intro E _ _ _ hU w
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (maximalRealSubfield E)
    (w.under (𝓞 (maximalRealSubfield E)))
  have hy : w.valuation E (algebraMap (maximalRealSubfield E) E π) = WithZero.exp (-1) := by
    rw [valuation_up hU w π, hπ]
  have hy0 : algebraMap (maximalRealSubfield E) E π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hy
    exact WithZero.zero_ne_coe hy
  have hne : algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π) ≠ 0 :=
    (map_ne_zero _).2 hy0
  have hv : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) =
      WithZero.exp (-1) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion (𝓞 E) E w, Function.comp_apply, Algebra.algebraMap_self,
      RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hy]
  have hv0 : Valued.v (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) ≠ 0 := by
    rw [hv]
    exact WithZero.coe_ne_zero
  refine ⟨Units.mk0 _ hne, ⟨?_, ?_⟩, ?_⟩
  · show Formalism.UG.ordL (algebraMap E (w.adicCompletion E) (algebraMap (maximalRealSubfield E) E π)) = 1
    unfold Formalism.UG.ordL
    rw [dite_eq_right hv0]
    exact neg_toAdd_unzero _ hv0 hv
  · exact cj_real w π
  · exact hv

end GlobalTheory.CompanionTheory.UnifFix
end
end

