module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.WeilBound.CoreStatements.MeasureExistence.ExistsMeas
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AutomorphicSpectrum.Definitions.TwistedFlags.OneMemOffK
public import Formalism.LocalToGlobal.IndefiniteReal.GvPairOfOrbitDerivCont
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NelsonExistsWordGrowthConstant
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieBasisCoordinateGrowthBound

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticSectionIsAlgebraic
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Gaga

theorem holomorphicSections_algebraic_of_isProper : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → IsProper p → ∀ (R : AnRead p (RingHom.id ℂ) D) (B : LB Y), B.IsLB → ∀ s ∈ R.holSec B, ∃ t : B.Sec, secVal p (RingHom.id ℂ) t = s := by
  intro Y p D hs hp R B hB s hsec
  have hcont (j : B.ι) : ContinuousOn (s j) (ptsIn p (RingHom.id ℂ) (B.U j)) :=
    (hsec.2 j).continuousOn (isOpen_ptsIn _)
  have loc (i : B.ι) (x : B.U i) : ∃ V : Y.Opens, x.1 ∈ V ∧ V ≤ B.U i ∧ ∃ c : Γ(Y, V),
      ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ev p (RingHom.id ℂ) V c y = s i y := by
    obtain ⟨U, hxU, hU⟩ := GlobalTheory.exists_open_isDomain_of_smooth_complex Y p D hs x
    obtain ⟨V, hVa, hx, hV⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (U := U ⊓ B.U i) (x := x.1) ⟨hxU, x.2⟩
    have ha : IsAffineOpen V := hVa
    have hi := hV.trans inf_le_right
    have hd := hU V (hV.trans inf_le_left) hx
    have hh := (hsec.2 i).mono (ptsIn_mono hi)
    obtain ⟨n, u, C, m, hC⟩ := _root_.GlobalTheory.CompanionTheory.Gaga.continuous_section_polynomial_growth_of_isProper Y p hp B hB s hsec.1 hcont i V ha hi
    obtain ⟨a, b, hb, e⟩ := SerreSections.exists_mul_eq_of_polynomial_growth Y p D hs R V ha hd _ hh n u C m hC
    exact ⟨V, hx, hi, GlobalTheory.exists_ev_eq_of_continuousOn_quotient Y p D hs V ha hd _ (hh.continuousOn (isOpen_ptsIn _)) a b hb e⟩
  choose V hx hV c hc using loc
  have glue (i : B.ι) : ∃ f : Γ(Y, B.U i), ∀ y ∈ ptsIn p (RingHom.id ℂ) (B.U i),
      ev p (RingHom.id ℂ) _ f y = s i y := by
    obtain ⟨f, hf, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf (V i) (B.U i)
      (fun x => homOfLE (hV i x)) (fun x h => Opens.mem_iSup.2 ⟨⟨x, h⟩, hx i _⟩) (c i) fun x x' =>
        GlobalTheory.eq_of_ev_eq_of_smoothOfRelativeDimension Y p D hs (V i x ⊓ V i x') _ _ fun y hy =>
          ((ev_res inf_le_left hy _).trans (hc i x y (mem_ptsIn_inf.1 hy).1)).trans
            ((ev_res inf_le_right hy _).trans (hc i x' y (mem_ptsIn_inf.1 hy).2)).symm
    refine ⟨f, fun y hy => ?_⟩
    have hy' : y ∈ ptsIn p (RingHom.id ℂ) (V i ⟨_, mem_ptsIn.1 hy⟩) := mem_ptsIn.2 (hx i _)
    rw [← hc i _ y hy', ← hf]
    exact (ev_res _ hy' _).symm
  choose f hf using glue
  refine ⟨⟨f, fun i j => GlobalTheory.eq_of_ev_eq_of_smoothOfRelativeDimension Y p D hs _ _ _ fun y hy => ?_⟩, funext₂ fun i y => ?_⟩
  · have h := mem_ptsIn_inf.1 hy
    refine (ev_res inf_le_left hy _).trans (Eq.trans ?_ (ev_mul _ _ _).symm)
    rw [hf i y h.1, hsec.1.1 i j y h.1 h.2, ← hf j y h.2]
    exact congrArg _ (ev_res inf_le_right hy _).symm
  · by_cases h : y ∈ ptsIn p (RingHom.id ℂ) (B.U i)
    · exact hf i y h
    · exact (ev_of_notMem h _).trans (hsec.1.2 i y h).symm

end GlobalTheory.CompanionTheory.Gaga
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIdeleCircle
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps

namespace GlobalTheory.CompanionTheory.HeckeBridge

variable {E : Type} [Field E] [NumberField E]

def ideleCircle (χ : HChar E) (hu : IsUnitary χ) : GroundTheory.Global.IdeleGroup E →* Circle where
  toFun x := ⟨((χ.1 x : ℂˣ) : ℂ), by simp [Submonoid.unitSphere, hu x]⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [map_mul, Units.val_mul]
    rfl

theorem continuous_ideleCircle (χ : HChar E) (hu : IsUnitary χ) : Continuous (ideleCircle χ hu) :=
  Continuous.subtype_mk (Units.continuous_val.comp χ.2.1) _

def toHecke (χ : HChar E) (hu : IsUnitary χ) : GroundTheory.Global.HeckeCharacter E where
  toMonoidHom := QuotientGroup.lift (GroundTheory.Global.IdeleGroup.diagonal E).range (ideleCircle χ hu) (by
    rintro _ ⟨k, rfl⟩
    rw [MonoidHom.mem_ker]
    ext
    have := χ.2.2 k
    show ((χ.1 (Neutral.B1.diagUnits E k) : ℂˣ) : ℂ) = 1
    rw [this]; rfl)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk (GroundTheory.Global.IdeleGroup.diagonal E).range).continuous_iff.2
    (continuous_ideleCircle χ hu)

theorem coe_toIdele (χ : HChar E) (hu : IsUnitary χ) (x : GroundTheory.Global.IdeleGroup E) :
    (((toHecke χ hu).toIdele x : Circle) : ℂ) = ((χ.1 x : ℂˣ) : ℂ) := rfl

theorem coe_localComponent (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    (((toHecke χ hu).localComponent v x : Circle) : ℂ) = ((χ.loc v x : ℂˣ) : ℂ) := rfl

theorem toHecke_inv (χ : HChar E) (hu : IsUnitary χ) (hu' : IsUnitary χ⁻¹) : toHecke χ⁻¹ hu' = (toHecke χ hu)⁻¹ := by
  ext c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  show (((toHecke χ⁻¹ hu').toIdele x : Circle) : ℂ) = ((((toHecke χ hu).toIdele x)⁻¹ : Circle) : ℂ)
  rw [coe_toIdele, Circle.coe_inv, coe_toIdele]
  exact Units.val_inv_eq_inv_val (χ.1 x)

end GlobalTheory.CompanionTheory.HeckeBridge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory NumberField Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspFin

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.AutMult GlobalTheory.DiscreteSum GlobalTheory.Orb GlobalTheory.AdelicU GlobalTheory.SplitWeil

theorem le_re_inner_of_isRepOp {G H : Type} [Group G] [MeasurableSpace G] [TopologicalSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : G →* (H →L[ℂ] H)} {μ : Measure G} {φ : G → ℝ} {T : H →L[ℂ] H}
    (hT : IsRepOp π μ (fun g => (φ g : ℂ)) T) (hφ : Integrable φ μ) (h0 : 0 ≤ φ) {N : Set G}
    (hs : Function.support φ ⊆ N) (u : H) (c : ℝ) (hc : ∀ g ∈ N, c ≤ (⟪u, π g u⟫_ℂ).re) :
    c * ∫ g, φ g ∂μ ≤ (⟪u, T u⟫_ℂ).re := by
  have hi := (hT u).1
  have hin : Integrable (fun g => ⟪u, (φ g : ℂ) • π g u⟫_ℂ) μ := hi.const_inner u
  have e : (⟪u, T u⟫_ℂ).re = ∫ g, (⟪u, (φ g : ℂ) • π g u⟫_ℂ).re ∂μ := by
    rw [(hT u).2, ← integral_inner hi u]
    exact (integral_re hin).symm
  rw [e, ← integral_const_mul]
  refine integral_mono (hφ.const_mul c) hin.re fun g => ?_
  simp only [inner_smul_right, Complex.re_ofReal_mul]
  by_cases hg : φ g = 0
  · simp [hg]
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hc g (hs hg)) (h0 g)

variable {D : D7} {V : HSp D}

theorem exists_bump (μ : Measure (GA D V)) [μ.IsHaarMeasure] {N : Set (GA D V)} (hN : N ∈ 𝓝 (1 : GA D V)) :
    ∃ φ : GA D V → ℝ, (fun g => (φ g : ℂ)) ∈ CcGA V ∧ 0 ≤ φ ∧ Function.support φ ⊆ N ∧ Integrable φ μ ∧
      0 < ∫ g, φ g ∂μ := by
  obtain ⟨φ, hφ, h0, h1, hs⟩ : ∃ φ : GA D V → ℝ, (fun g => (φ g : ℂ)) ∈ CcGA V ∧ 0 ≤ φ ∧ φ 1 = 1 ∧
      Function.support φ ⊆ N := GlobalTheory.CuspSpectrum.exists_bump_ccAd (isCMExt_host D) hN
  have hc := continuous_of_mem_ccAd hφ
  have hφc : Continuous φ := Complex.continuous_re.comp hc.1
  have hφs : HasCompactSupport φ := hc.2.comp_left (g := Complex.re) rfl
  exact ⟨φ, hφ, h0, hs, hφc.integrable_of_hasCompactSupport hφs,
    hφc.integral_pos_of_hasCompactSupport_nonneg_nonzero hφs h0 (x := 1) (by rw [h1]; exact one_ne_zero)⟩

theorem finiteDimensional_of_coercive (hP : GlobalTheory.Published.CuspDecayBound) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (Sb : Submodule ℂ (L2cusp V μ)) {N : Set (GA D V)} (hN : N ∈ 𝓝 (1 : GA D V))
    (h : ∀ g ∈ N, ∀ u ∈ Sb, (1 / 2 : ℝ) * ‖u‖ ^ 2 ≤ (⟪u, Rcusp V μ g u⟫_ℂ).re) : FiniteDimensional ℂ Sb := by
  obtain ⟨φ, hf, h0, hs, hi, hpos⟩ := exists_bump μ hN
  have hrep := GlobalTheory.CuspSpectrum.isRepOp_RcuspOp (μ := μ) hf
  refine _root_.GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive (L2cusp V μ) (RcuspOp V μ _)
    (isCompactOperator_of_isHilbertSchmidt (GlobalTheory.CuspHS.isHilbertSchmidt_RcuspOp hP hf)) Sb
    ((1 / 2) * ∫ g, φ g ∂μ) (by positivity) fun u hu => ?_
  have := le_re_inner_of_isRepOp hrep hi h0 hs u ((1 / 2 : ℝ) * ‖u‖ ^ 2) fun g hg => h g hg u hu
  calc _ = (1 / 2 : ℝ) * ‖u‖ ^ 2 * ∫ g, φ g ∂μ := by ring
    _ ≤ _ := this

end GlobalTheory.CompanionTheory.CuspFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HilbertClassFieldJ
section
namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem hilbertClassFieldJ : GlobalTheory.Published.HilbertClassFieldJ :=
  GlobalTheory.Published.ComplexMultiplicationJSt.hilbertClassFieldJ GlobalTheory.CompanionTheory.Published.complexMultiplicationJ

end GlobalTheory.CompanionTheory.Hypotheses₂
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IdealInvariantsOneOrbit
section
namespace GlobalTheory.CompanionTheory.CM

theorem idealInvariantsOneOrbit : GlobalTheory.Published.IdealInvariantsOneOrbitSt :=
  GlobalTheory.Published.ComplexMultiplicationJSt.oneOrbit _root_.GlobalTheory.CompanionTheory.Published.complexMultiplicationJ

end GlobalTheory.CompanionTheory.CM
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.WordBoundOfDelta
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordDelta

theorem dRep_real_smul {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (r : ℝ) :
    dRep π (r • X) v = (r : ℂ) • dRep π X v := by
  have hrX : r • X ∈ HCSS.lieOf G := (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra hG).2.1 r X hX
  have h1 := (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec hG hrep hv hX).1
  have h2 := (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec hG hrep hv hrX).1
  have h3 : HasDerivAt (fun t : ℝ => r * t) r 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul r
  have h4 : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((r * t) • X)) v) (r • dRep π X v) 0 := by
    have h1' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) (r * 0) := by
      simpa using h1
    exact HasDerivAt.scomp (0 : ℝ) h1' h3
  have h5 : (fun t : ℝ => π (NormedSpace.exp (t • (r • X))) v) = fun t : ℝ => π (NormedSpace.exp ((r * t) • X)) v := by
    funext t
    rw [smul_smul, mul_comm]
  rw [h5] at h2
  rw [h2.unique h4]
  exact (Complex.coe_smul r _).symm

theorem dRep_sum {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) (r : Fin d → ℝ) {w : H} (hw : IsSmoothVec G π w) :
    dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w := by
  have hl := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra hG
  have key : ∀ s : Finset (Fin d), (∑ i ∈ s, r i • b i ∈ HCSS.lieOf G) ∧
      dRep π (∑ i ∈ s, r i • b i) w = ∑ i ∈ s, (r i : ℂ) • dRep π (b i) w := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨?_, ?_⟩
      · intro t
        simpa using hG.one_mem
      · simp [dRep]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hri := hl.2.1 (r i) _ (hb i)
      refine ⟨hl.1 _ _ hri ih.1, ?_⟩
      rw [(_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear hG hrep hw hw hri ih.1).1, ih.2, dRep_real_smul hG hrep hw (hb i)]
  exact (key Finset.univ).2

theorem word_bound_of_delta : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) (hQ : AlmostIsom G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) (hli : LinearIndependent ℝ b) (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] (hYs : ∀ y ∈ Y, IsSmoothVec G π y) (hYd : ∀ y ∈ Y, ∑ i, dRep π (b i) (dRep π (b i) y) ∈ Y), ∀ v ∈ Y, WordBound G π v := by
  intro n G H _ _ _ π hG hrep _ hQ d b hb hli hsp Y _ hYs hYd v hv
  obtain ⟨Q, m, Mb, a, hm, hMb, ha, hadd, hsmul, hconj, hpos, hbd, hgrow⟩ := hQ
  obtain ⟨hsadd, hssmul, -⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.smooth_closed hG hrep
  have hvs := hYs v hv
  let S : Submodule ℂ H :=
    { carrier := {x | IsSmoothVec G π x}
      add_mem' := fun {x y} hx hy => hsadd x y hx hy
      zero_mem' := by simpa using hssmul 0 v hvs
      smul_mem' := fun c x hx => hssmul c x hx }
  let Xf : Fin d → Module.End ℂ S := fun i =>
    { toFun := fun x => ⟨dRep π (b i) x, (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec hG hrep x.2 (hb i)).2⟩
      map_add' := fun x y => Subtype.ext (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear hG hrep x.2 y.2 (hb i) (hb i)).2.1
      map_smul' := fun c x => Subtype.ext ((_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear hG hrep x.2 x.2 (hb i) (hb i)).2.2 c) }
  have hXc : ∀ i (x : S), ((Xf i x : S) : H) = dRep π (b i) x := fun _ _ => rfl
  have hlie := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra hG
  choose r hr using fun (p : Fin d × Fin d) => hsp _ (hlie.2.2.1 (b p.1) (b p.2) (hb p.1) (hb p.2))
  have hcomm : ∀ i j, Xf i * Xf j - Xf j * Xf i = ∑ l, ((r (i, j) l : ℝ) : ℂ) • Xf l := by
    intro i j
    ext u
    have h1 := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket.smooth_bracket hG hrep u.2 (hb i) (hb j)
    rw [show b i * b j - b j * b i = _ from hr (i, j), dRep_sum hG hrep b hb _ u.2] at h1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, hXc]
    exact h1.symm
  have hQnn : ∀ x : H, 0 ≤ (Q x x).re := fun x =>
    le_trans (by positivity) (hpos x)
  let A : ℝ := a * ∑ i, mnorm (b i)
  have hmn : ∀ X : Matrix (Fin n) (Fin n) ℂ, 0 ≤ mnorm X := fun X =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hA : 0 ≤ A := mul_nonneg ha (Finset.sum_nonneg fun i _ => hmn _)
  have hs : ∀ i (x : S), |2 * (Q (Xf i x) x).re| ≤ A * (Q x x).re := by
    intro i x
    refine (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.abs_two_re_form_dRep_le hG hrep Q Mb a hadd hsmul hconj hbd hgrow (hb i) x.2).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (hQnn x)
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun i => mnorm (b i)) (fun i _ => hmn _) (Finset.mem_univ i)) ha
  let V : Submodule ℂ S := Y.comap S.subtype
  have hinj : Function.Injective (fun u : V => (⟨(u : S), u.2⟩ : Y)) := by
    intro u w h
    exact Subtype.ext (Subtype.ext (congrArg (fun y : Y => (y : H)) h))
  let f : V →ₗ[ℂ] Y :=
    { toFun := fun u => ⟨(u : S), u.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : FiniteDimensional ℂ V := FiniteDimensional.of_injective f hinj
  have hV : ∀ u ∈ V, (∑ i, Xf i * Xf i) u ∈ V := by
    intro u hu
    have h1 := hYd (u : H) hu
    change (((∑ i, Xf i * Xf i) u : S) : H) ∈ Y
    simpa only [LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, hXc] using h1
  obtain ⟨C, hC, hN⟩ := _root_.GlobalTheory.CompanionTheory.HCForm.nelson_form (fun x y : S => Q x y)
    (fun x y z => hadd x y z) (fun c x y => hsmul c x y) (fun x y => hconj x y)
    (fun x hx => lt_of_lt_of_le (by
      have : (x : H) ≠ 0 := fun h => hx (Subtype.ext h)
      positivity) (hpos x))
    Xf (fun i j l => ((r (i, j) l : ℝ) : ℂ)) hcomm A hA hs V hV
  have hword : ∀ (l : List (Fin d)) (u : S),
      (((l.map Xf).prod u : S) : H) = l.foldr (fun i w => dRep π (b i) w) (u : H) := by
    intro l u
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, hXc, List.foldr_cons, ih]
  let vS : S := ⟨v, hvs⟩
  have hvV : vS ∈ V := hv
  let K : ℝ := Real.sqrt (Q v v).re / Real.sqrt m
  have hK : 0 ≤ K := by positivity
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  refine _root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand.wordBound_of_basis hG hrep b hb hsp _ (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord.sum_abs_coord_le_mnorm b hli).choose_spec.1 (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord.sum_abs_coord_le_mnorm b hli).choose_spec.2
    (fun r w hw => dRep_sum hG hrep b hb r hw) hvs (C * (K + 1)) (by positivity) ?_
  intro l
  have h1 := hN l vS hvV
  rw [show ((l.map Xf).prod vS : S) = ((l.map Xf).prod vS : S) from rfl] at h1
  set w : S := (l.map Xf).prod vS with hw
  have hwv : (w : H) = l.foldr (fun i w => dRep π (b i) w) v := hword l vS
  rw [← hwv]
  have h2 : Real.sqrt m * ‖(w : H)‖ ≤ Real.sqrt (Q w w).re := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, Real.sq_sqrt hm.le]
    exact hpos w
  have h3 : ‖(w : H)‖ ≤ C ^ (l.length + 1) * l.length.factorial * K := by
    have h4 : Real.sqrt m * ‖(w : H)‖ ≤ C ^ (l.length + 1) * l.length.factorial * Real.sqrt (Q v v).re := h2.trans h1
    have h5 : C ^ (l.length + 1) * l.length.factorial * K = (C ^ (l.length + 1) * l.length.factorial * Real.sqrt (Q v v).re) / Real.sqrt m := by
      simp only [K]; ring
    rw [h5, le_div_iff₀ hsm]
    linarith
  refine h3.trans ?_
  have h6 : K ≤ (K + 1) ^ (l.length + 1) := by
    have h7 : (K + 1) ^ 1 ≤ (K + 1) ^ (l.length + 1) := pow_le_pow_right₀ (by linarith) (by omega)
    linarith
  rw [mul_pow]
  have h8 : 0 ≤ C ^ (l.length + 1) * (l.length.factorial : ℝ) := by positivity
  calc C ^ (l.length + 1) * l.length.factorial * K ≤ C ^ (l.length + 1) * l.length.factorial * (K + 1) ^ (l.length + 1) :=
        mul_le_mul_of_nonneg_left h6 h8
    _ = C ^ (l.length + 1) * (K + 1) ^ (l.length + 1) * l.length.factorial := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordDelta

end
end

