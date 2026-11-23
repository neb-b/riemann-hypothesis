module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumCentralCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelSobolevBoundWeilCompact
section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

noncomputable section

namespace GlobalTheory.ThetaDens.WeilCompact

variable {D : D7}

theorem mt_mul_eq (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one_eq (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem continuous_mt_eq (V : HSp D) : Continuous (Formalism.L2.Theta.mt V) :=
  Units.continuous_val.comp continuous_subtype_val

theorem actO_actO_inv {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    Formalism.IndefR.Datum.actO S T g h (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ x) = x := by
  unfold Formalism.IndefR.Datum.actO
  rw [inv_inv]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.Theta.mt T h), ← mt_mul_eq, ← mt_mul_eq, mul_inv_cancel, mul_inv_cancel,
    mt_one_eq, mt_one_eq, Matrix.one_mul, Matrix.mul_one]


open GlobalTheory.Size in
theorem dRho_om {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (g : GA D S) (h : GA D T) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (om (g, h) f) =
      om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ
        (compAt θ τ (Formalism.L2.Theta.mt T h⁻¹) * z * compAt θ τ (Formalism.L2.Theta.mt S g)) f) := by
  rw [GlobalTheory.OrientedHeis.om_dRho hom hθ g h τ _ hf]
  congr 1
  have e1 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ h
  have e2 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ g
  simp only [Matrix.mul_assoc]
  rw [e2, Matrix.mul_one, ← Matrix.mul_assoc, e1, Matrix.one_mul]

def dirSize (θ : InfFam D) (S T : HSp D) (x : GA D S × GA D T) : ℝ :=
  ∑ a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool, ∑ i, ∑ j,
    (|((compAt θ a.1 (Formalism.L2.Theta.mt T x.2⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
      compAt θ a.1 (Formalism.L2.Theta.mt S x.1)) i j).re| +
     |((compAt θ a.1 (Formalism.L2.Theta.mt T x.2⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
      compAt θ a.1 (Formalism.L2.Theta.mt S x.1)) i j).im|)

theorem continuous_dirSize {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) : Continuous (dirSize θ S T) := by
  unfold dirSize
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  have h1 : Continuous fun x : GA D S × GA D T => compAt θ a.1 (Formalism.L2.Theta.mt T x.2⁻¹) :=
    (GlobalTheory.RealWeil.continuous_compAt hθ a.1 _ _).comp ((continuous_mt_eq T).comp continuous_snd.inv)
  have h2 : Continuous fun x : GA D S × GA D T => compAt θ a.1 (Formalism.L2.Theta.mt S x.1) :=
    (GlobalTheory.RealWeil.continuous_compAt hθ a.1 _ _).comp ((continuous_mt_eq S).comp continuous_fst)
  have h3 := ((h1.matrix_mul (continuous_const (y := Matrix.single a.2.1 a.2.2.1
    (if a.2.2.2 then Complex.I else 1)))).matrix_mul h2).matrix_elem i j
  exact (continuous_abs.comp (Complex.continuous_re.comp h3)).add (continuous_abs.comp (Complex.continuous_im.comp h3))

theorem actO_add' {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    Formalism.IndefR.Datum.actO S T g h (x + y) = Formalism.IndefR.Datum.actO S T g h x + Formalism.IndefR.Datum.actO S T g h y := by
  unfold Formalism.IndefR.Datum.actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem actO_zero' {S T : HSp D} (g : GA D S) (h : GA D T) : Formalism.IndefR.Datum.actO S T g h 0 = 0 := by
  unfold Formalism.IndefR.Datum.actO
  rw [Matrix.mul_zero, Matrix.zero_mul]

theorem actO_neg' {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    Formalism.IndefR.Datum.actO S T g h (-x) = -Formalism.IndefR.Datum.actO S T g h x := by
  unfold Formalism.IndefR.Datum.actO
  rw [Matrix.mul_neg, Matrix.neg_mul]


open GlobalTheory.Size in
theorem word_om_le {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕) {K : Set (GA D S × GA D T)}
    (B : ℝ≥0) (hB : ∀ x ∈ K, dirSize θ S T x ≤ B) (k : ℕ) :
    ∃ C : ℝ≥0, ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), l.length = k → ∀ x ∈ K,
      ∀ g, IsThetaFunO ψ S T g → l2O μ 𝓕 (wordAct (heisDer ψ θ) l (om x g)) ≤ C * sobO ψ θ μ 𝓕 k g := by
  induction k with
  | zero =>
    refine ⟨1, fun l hl x _ g hg => ?_⟩
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero hl
    rw [wordAct_nil, l2O_om_apply_eq_of_isThetaFunO hom hμ.1 hμ.2.1 hg, sobO_zero, ENNReal.coe_one, one_mul]
  | succ k ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C * B, fun l hl x hx g hg => ?_⟩
    obtain ⟨g1, h1⟩ := x
    have hne : l ≠ [] := by rintro rfl; simp at hl
    rw [← List.dropLast_append_getLast hne, wordAct_append, wordAct_cons, wordAct_nil]
    set a := l.getLast hne
    have e := dRho_om hom hθ g1 h1 a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) hg
    have e' : heisDer ψ θ a (om (g1, h1) g) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ a.1
        (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) (om (g1, h1) g) := rfl
    rw [e', e]
    have hg' := GlobalTheory.OrientedHeis.theta_dRho hθ hom.std a.1 (compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
      Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) hg
    have hs : ENNReal.ofReal (∑ i, ∑ j, (|((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
        Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).re| +
        |((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) *
        Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).im|))
        ≤ B := by
      rw [← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal (le_trans ?_ (hB _ hx))
      unfold dirSize
      exact Finset.single_le_sum (f := fun a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool => ∑ i, ∑ j,
        (|((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
          compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).re| +
         |((compAt θ a.1 (Formalism.L2.Theta.mt T h1⁻¹) * Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) *
          compAt θ a.1 (Formalism.L2.Theta.mt S g1)) i j).im|))
        (fun b _ => by positivity) (Finset.mem_univ a)
    calc _ ≤ (C : ℝ≥0∞) * sobO ψ θ μ 𝓕 k _ := hC _ (by simp [hl]) _ hx _ hg'
      _ ≤ C * (ENNReal.ofReal _ * sobO ψ θ μ 𝓕 (k + 1) g) := by
          gcongr
          exact sobO_dRho_le hom.std hθ hg a.1 _ k
      _ ≤ C * (B * sobO ψ θ μ 𝓕 (k + 1) g) := by gcongr
      _ = ((C * B : ℝ≥0) : ℝ≥0∞) * sobO ψ θ μ 𝓕 (k + 1) g := by push_cast; ring

end GlobalTheory.ThetaDens.WeilCompact


open GlobalTheory.ThetaDens.WeilCompact GlobalTheory.Size in
theorem GlobalTheory.ThetaDens.om_compact_sobCont : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ K : Set (GA D S × GA D T), IsCompact K → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ U' : AddSubgroup (WO S T), IsOpen (U' : Set (WO S T)) ∧ (∀ f ∈ thetaLevel ψ S T U, ∀ x ∈ K, om x f ∈ thetaLevel ψ S T U') ∧ ∀ d : ℕ, ∃ (d' : ℕ) (C : ℝ≥0), ∀ f ∈ thetaLevel ψ S T U, ∀ x ∈ K, sobO ψ θ μ 𝓕 d (om x f) ≤ C * sobO ψ θ μ 𝓕 d' f := by
  intro D ψ S T χS χT om hom θ hθ μ 𝓕 hμ K hK U hU
  let U' : AddSubgroup (WO S T) :=
    { carrier := {u | ∀ x ∈ K, Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ u ∈ U}
      add_mem' := fun {a b} ha hb x hx => by
        rw [Set.mem_setOf_eq] at ha hb
        show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ (a + b) ∈ U
        rw [actO_add']; exact U.add_mem (ha x hx) (hb x hx)
      zero_mem' := fun x _ => by
        show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ 0 ∈ U
        rw [actO_zero']; exact U.zero_mem
      neg_mem' := fun {a} ha x hx => by
        show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ (-a) ∈ U
        rw [actO_neg']; exact U.neg_mem (ha x hx) }
  have hU' : IsOpen (U' : Set (WO S T)) := by
    refine U'.isOpen_of_mem_nhds (g := 0) ?_
    refine hK.eventually_forall_of_forall_eventually (x₀ := (0 : WO S T))
      (P := fun u x => Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ u ∈ U) fun x _ => ?_
    have hc : Continuous fun p : WO S T × (GA D S × GA D T) => Formalism.IndefR.Datum.actO S T p.2.1⁻¹ p.2.2⁻¹ p.1 := by
      unfold Formalism.IndefR.Datum.actO
      exact (((continuous_mt_eq T).comp continuous_snd.snd.inv).matrix_mul continuous_fst).matrix_mul
        ((continuous_mt_eq S).comp continuous_snd.fst.inv.inv)
    refine (hU.preimage hc).mem_nhds ?_
    show Formalism.IndefR.Datum.actO S T x.1⁻¹ x.2⁻¹ 0 ∈ U
    rw [actO_zero']; exact U.zero_mem
  obtain ⟨B0, hB0⟩ := hK.bddAbove_image (continuous_dirSize hθ S T).continuousOn
  have hB : ∀ x ∈ K, dirSize θ S T x ≤ (B0.toNNReal : ℝ) := fun x hx =>
    (hB0 ⟨x, hx, rfl⟩).trans (Real.le_coe_toNNReal B0)
  refine ⟨U', hU', fun f hf x hx => ⟨hom.om_pres x f hf.1, fun u hu h0 => ?_⟩, fun d => ?_⟩
  · obtain ⟨g, h⟩ := x
    have hv : Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u ∈ U := hu (g, h) hx
    have hv0 : (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u).map (infPart D) = 0 := by
      unfold Formalism.IndefR.Datum.actO
      rw [Matrix.map_mul, Matrix.map_mul, h0]; simp
    calc heisO ψ S T u (om (g, h) f)
        = heisO ψ S T (Formalism.IndefR.Datum.actO S T g h (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u)) (om (g, h) f) := by
          rw [actO_actO_inv]
      _ = om (g, h) (heisO ψ S T (Formalism.IndefR.Datum.actO S T g⁻¹ h⁻¹ u) f) := (hom.om_heis g h _ f hf.1).symm
      _ = om (g, h) f := by rw [hf.2 _ hv hv0]
  · choose C hC using word_om_le hom hθ hμ _ hB
    refine ⟨d, ∑ k ∈ Finset.range (d + 1), ∑ _a : Fin k → D.what₂.Tau × Fin T.rank × Fin S.rank × Bool, C k,
      fun f hf x hx => ?_⟩
    show wordSum (heisDer ψ θ) (l2O μ 𝓕) d (om x f) ≤ _
    unfold wordSum
    rw [ENNReal.ofNNReal_finsetSum, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [ENNReal.ofNNReal_finsetSum, Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => ?_
    calc _ ≤ (C k : ℝ≥0∞) * sobO ψ θ μ 𝓕 k f := hC k _ (List.length_ofFn) x hx f hf.1
      _ ≤ C k * sobO ψ θ μ 𝓕 d f := by
          gcongr
          exact sobO_mono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSiegelParabolicConjDoubledCompact
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.ConjElt

theorem compInf_sigR_comm {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (w : NumberField.InfinitePlace F) (x : AF F ⊗[F] E) :
    compInf F E w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ (compInf F E w x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => simp [compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem compInf_inclR_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (w : NumberField.InfinitePlace F) (y : E) :
    compInf F E w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) y) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR w.Completion y := by
  simp [compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem sq_real_of_majorant {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (a b : GL (Fin n) (AF F ⊗[F] E)) (ha : IsMajorantFrame σ J a)
    (hbw : ∀ w, Formalism.UG.bc (compInf F E w) b = Formalism.UG.bc (compInf F E w) a) (w : NumberField.InfinitePlace F) :
    (((b.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ))ᵀ * J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F)) * b.1) *
      ((b.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ))ᵀ * J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F)) * b.1)).map
        (compInf F E w) = 1 := by
  obtain ⟨s, hs⟩ := ha w
  rw [← hbw w] at hs
  have h1 : ((b.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ))ᵀ).map (compInf F E w) =
      Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (Formalism.UG.bc (compInf F E w) b).1 :=
    Matrix.ext fun i j => compInf_sigR_comm σ w _
  have h2 : (J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))).map (compInf F E w) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F := F) w.Completion J :=
    Matrix.ext fun i j => compInf_inclR_eq w _
  have hH : ((b.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ))ᵀ * J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F)) * b.1).map
      (compInf F E w) = Matrix.diagonal fun i => if s i = true then 1 else -1 := by
    rw [← hs, Matrix.map_mul, Matrix.map_mul, h1, h2]
    rfl
  rw [Matrix.map_mul, hH, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

theorem gram_blk_mul {R : Type} [CommRing R] (c : R →+* R) {n : ℕ} (b J : Matrix (Fin n) (Fin n) R)
    (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    Formalism.UG.cT c (blkMat finSumFinEquiv b b * M) * dblGram finSumFinEquiv J * (blkMat finSumFinEquiv b b * M) =
      Formalism.UG.cT c M * dblGram finSumFinEquiv (Formalism.UG.cT c b * J * b) * M := by
  have h : Formalism.UG.cT c (blkMat finSumFinEquiv b b * M) =
      Formalism.UG.cT c M * Formalism.UG.cT c (blkMat finSumFinEquiv b b) := by
    rw [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]; rfl
  have h2 : Formalism.UG.cT c (blkMat finSumFinEquiv b b) * dblGram finSumFinEquiv J * blkMat finSumFinEquiv b b =
      dblGram finSumFinEquiv (Formalism.UG.cT c b * J * b) := by
    rw [cT_blkMat, dblGram, dblGram, blkMat_mul, blkMat_mul, Matrix.mul_neg, Matrix.neg_mul]
  rw [h, ← h2]
  simp only [Matrix.mul_assoc]

theorem diag_blk_mul {R : Type} [CommRing R] {n : ℕ} (b : Matrix (Fin n) (Fin n) R)
    (M : Matrix (Fin (n + n)) (Fin (n + n)) R) (l : Fin (n + n))
    (h : ∀ i : Fin n, M (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) l = M (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) l)
    (i : Fin n) :
    (blkMat finSumFinEquiv b b * M) (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) l =
      (blkMat finSumFinEquiv b b * M) (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) l := by
  simp only [Matrix.mul_apply, ← (finSumFinEquiv (m := n) (n := n)).sum_comp, Fintype.sum_sum_type, blkMat,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add, h]

theorem gA_dblSp {D : D7} (A : HSp D) : gA (dblSp A) = dblGram finSumFinEquiv (gA A) :=
  (congrArg (fun x => x.map (incA D)) (gram_hdbl A)).trans ((blkMat_map _ _ (map_zero _) _ _).trans
    (congrArg (blkMat finSumFinEquiv (gA A)) (Matrix.map_neg _ (map_neg _) _)))

theorem gram_frame {D : D7} (A : HSp D) (b : GL (Fin A.rank) (AE D)) (M : GL (Fin (A.rank + A.rank)) (AE D)) :
    adj (blkGL finSumFinEquiv (b, b) * M).1 * gA (dblSp A) * (blkGL finSumFinEquiv (b, b) * M).1 =
      adj M.1 * dblGram finSumFinEquiv (adj b.1 * gA A * b.1) * M.1 :=
  (congrArg (fun X : Mx D (A.rank + A.rank) (A.rank + A.rank) =>
    adj (blkGL finSumFinEquiv (b, b) * M).1 * X * (blkGL finSumFinEquiv (b, b) * M).1) (gA_dblSp A)).trans
    (gram_blk_mul (cA D) b.1 (gA A) M.1)

theorem exists_siegel_frame {D : D7} (A : HSp D) (μ : D.host.E) (hμ : IsSkew μ) (b : GL (Fin A.rank) (AE D))
    (M : GL (Fin (A.rank + A.rank)) (AE D))
    (hMg : adj M.1 * dblGram finSumFinEquiv (adj b.1 * gA A * b.1) * M.1 = incA D μ • rat (Jst D A.rank))
    (hMc : ∀ i j : Fin A.rank,
      M.1 (finSumFinEquiv (Sum.inr i : Fin A.rank ⊕ Fin A.rank)) (finSumFinEquiv (Sum.inl j : Fin A.rank ⊕ Fin A.rank)) =
      M.1 (finSumFinEquiv (Sum.inl i : Fin A.rank ⊕ Fin A.rank)) (finSumFinEquiv (Sum.inl j : Fin A.rank ⊕ Fin A.rank))) :
    ∃ p : siegel A, mt (dblSp A) p * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) =
      (blkGL finSumFinEquiv (b, b) * M).1 :=
  GlobalTheory.StdUnn.exists_siegel_mul_Tm D A μ hμ (blkGL finSumFinEquiv (b, b) * M) ((gram_frame A b M).trans hMg)
    fun i j => diag_blk_mul b.1 M.1 _ (fun k => hMc k j) i

theorem adj_gram {D : D7} (A : HSp D) (b : Mx D A.rank A.rank) : adj (adj b * gA A * b) = adj b * gA A * b := by
  rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

theorem sq_real {D : D7} (A : HSp D) (a b : GL (Fin A.rank) (AE D)) (ha : IsMaj A a)
    (hbw : ∀ w, Formalism.UG.bc (compInf D.host.F D.host.E w) b = Formalism.UG.bc (compInf D.host.F D.host.E w) a)
    (w : NumberField.InfinitePlace D.host.F) :
    ((adj b.1 * gA A * b.1) * (adj b.1 * gA A * b.1)).map (compInf D.host.F D.host.E w) = 1 :=
  sq_real_of_majorant _ _ a b ha hbw w

theorem exists_isConj : ∀ D : D7, ∃ μ : D.host.E, IsSkew μ ∧ ∀ (A : HSp D) (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∃ p : siegel A, IsConj A a κ p := by
  intro D
  obtain ⟨μ, hμ, u, ε, hue⟩ := GlobalTheory.StdUnn.scalData_exists D
  obtain ⟨t, ht⟩ := GlobalTheory.StdUnn.exists_halfData D
  refine ⟨μ, hμ, fun A a ha κ hκ => ?_⟩
  obtain ⟨b, hbL, hbw⟩ := GlobalTheory.StdUnn.exists_isLatticeFrame_bc_eq D A a
  obtain ⟨Hm, hHm, hHmI⟩ := GlobalTheory.StdUnn.Unimod.gram_unimodular D A b hbL
  have hherm : adj Hm.1 = Hm.1 := by rw [hHm]; exact adj_gram A b.1
  have hsq : ∀ w, (Hm.1 * Hm.1).map (compInf D.host.F D.host.E w) = 1 := fun w => by
    rw [hHm]; exact sq_real A a b ha hbw w
  obtain ⟨M, M', hMg, hMc, hM'I, hMu, hMw⟩ := GlobalTheory.StdUnn.Frame.exists_frame D A.rank Hm hherm hHmI hsq μ u ε t hμ hue ht
  rw [hHm] at hMg
  obtain ⟨p, hp⟩ := exists_siegel_frame A μ hμ b M hMg hMc
  exact ⟨p, GlobalTheory.StdUnn.Conj.isConj_of_frame D A μ hμ κ hκ a b hbL hbw M M' u hM'I hMu hMw p hp⟩

end GlobalTheory.StdUnn.ConjElt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniformIsotypicAverageRealCentre
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AvgMidUnif

open GlobalTheory.AvgMid

theorem exists_isotypic_uniform : ∀ (D : D7), BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k₀ : KerDat A S) (k₀' : KerDat S A'), k₀.Is ψ θ x y → k₀'.Is ψ θ y z → ∀ (χ₁ : GA D A → ℂ) (χ₃ : GA D S → ℂ) (C₁ : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C₁ → IsBiSmooth C₁ → (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k₀.om (a, 1) (fun u => C₁ u v) = χ₁ a • fun u => C₁ u v) → (∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ v, k₀.om (1, b) (fun u => C₁ u v) = χ₃ b • fun u => C₁ u v) → ∃ (C₂ : WO A S → WO S A' → ℂ) (χ₂ : GA D S → ℂ), IsBiVac ψ A S A' x.L y.L z.L C₂ ∧ (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k₀.om (a, 1) (fun u => C₂ u v) = χ₁ a • fun u => C₂ u v) ∧ (∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ u, k₀'.om (b, 1) (C₂ u) = χ₂ b • C₂ u) ∧ ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → (∀ a ∈ GinfC A, ∀ b ∈ GinfC S, ∀ f, IsThetaFunO ψ A S f → k.om (a, b) f = k₀.om (a, b) f) → (∀ a ∈ GinfC S, ∀ b ∈ GinfC A', ∀ f, IsThetaFunO ψ S A' f → k'.om (a, b) f = k₀'.om (a, b) f) → ∀ φ, IsContAut A φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C₁) = biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C₂) := by
  intro D _ hF _ ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ₁ χ₃ C₁ hC₁ _ h1 h3
  obtain ⟨χA, χS, hwa⟩ := hk₀.weil
  obtain ⟨χS', χA', hwb⟩ := hk₀'.weil
  by_cases h0 : ∀ u v, C₁ u v = 0
  · refine ⟨C₁, fun _ => 1, hC₁, h1, fun b _ _ u => ?_, fun _ _ _ _ _ _ _ _ => rfl⟩
    rw [show C₁ u = 0 from funext (h0 u), map_zero, smul_zero]
  push_neg at h0
  obtain ⟨u₀, v₀, h0⟩ := h0
  have hv : ∀ b : ↥(GinfC S ⊓ Subgroup.center (GA D S)), k₀.om (1, b.1) (fun u => C₁ u v₀) u₀ = χ₃ b.1 * C₁ u₀ v₀ :=
    fun b => congrFun (h3 b.1 b.2.1 b.2.2 v₀) u₀
  have hχ : Continuous fun b : ↥(GinfC S ⊓ Subgroup.center (GA D S)) => χ₃ b.1 := by
    have : (fun b : ↥(GinfC S ⊓ Subgroup.center (GA D S)) => χ₃ b.1) =
        fun b => k₀.om (1, b.1) (fun u => C₁ u v₀) u₀ / C₁ u₀ v₀ := funext fun b => by rw [hv, mul_div_cancel_right₀ _ h0]
    rw [this]
    exact ((hwa.om_cont _ (hC₁.left v₀).1 u₀).comp (continuous_const.prodMk continuous_subtype_val)).div_const _
  have hm : ∀ b b' : ↥(GinfC S ⊓ Subgroup.center (GA D S)), χ₃ (b.1 * b'.1) = χ₃ b.1 * χ₃ b'.1 := fun b b' => by
    have e := hv (b * b')
    have e' : ((1, (b * b').1) : GA D A × GA D S) = (1, b.1) * (1, b'.1) := by simp
    rw [e', map_mul, Module.End.mul_apply, h3 b'.1 b'.2.1 b'.2.2, map_smul, Pi.smul_apply, hv, smul_eq_mul] at e
    refine mul_right_cancel₀ h0 ?_
    rw [← Subgroup.coe_mul, ← e]
    ring
  obtain ⟨hcpt, ν, hν, hν'⟩ := exists_haar hy
  obtain ⟨W, hW, hWf⟩ := hF ψ θ hθ A S x y hx hy k₀ hk₀ χ₁
  let E : Submodule ℂ (WO A S → ℂ) := Submodule.span ℂ (Set.range fun v u => C₁ u v)
  haveI : FiniteDimensional ℂ E := by
    refine Submodule.finiteDimensional_of_le (S₂ := W.map (pureTensorO ψ θ A S x.s y.s x.B y.B k₀.vac))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨v, rfl⟩
    obtain ⟨P, hP, e⟩ := hWf _ (hC₁.left v).1 (hC₁.left v).2 (fun a ha hc => h1 a ha hc v)
    exact Submodule.mem_map.2 ⟨P, hP, e.symm⟩
  have hEv : E ≤ vacSub ψ A S (latO A S x.L y.L fun _ => True) := Submodule.span_le.2 (by
    rintro _ ⟨v, rfl⟩; exact hC₁.left v)
  have hEe : ∀ (p : GA D A × GA D S) (c : ℂ), (∀ v, k₀.om p (fun u => C₁ u v) = c • fun u => C₁ u v) →
      ∀ f ∈ E, k₀.om p f = c • f := fun p c h f hf => by
    have : E ≤ LinearMap.eqLocus (k₀.om p) (c • LinearMap.id) := Submodule.span_le.2 (by rintro _ ⟨v, rfl⟩; exact h v)
    exact this hf
  obtain ⟨n, e, g, he, hg, hs⟩ := GlobalTheory.SeeSaw.FinRank.sum_prod_of_slices C₁ E
    (vacSub ψ S A' (latO S A' y.L z.L fun _ => True)) (fun v => Submodule.subset_span ⟨v, rfl⟩) hC₁.right
  have hg' : ∀ i, mean k₀'.om ν χ₃ (g i) ∈ vacSub ψ S A' (latO S A' y.L z.L fun _ => True) := fun i =>
    vac_mean hwb hθ hχ (hg i)
  have hl : ∀ v, (fun u => ∑ i, e i u * mean k₀'.om ν χ₃ (g i) v) ∈ E := fun v => by
    have : (fun u => ∑ i, e i u * mean k₀'.om ν χ₃ (g i) v) = ∑ i, mean k₀'.om ν χ₃ (g i) v • e i := by
      funext u; simp [Finset.sum_apply, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (he i)
  have hr : ∀ u, (fun v => ∑ i, e i u * mean k₀'.om ν χ₃ (g i) v) = ∑ i, e i u • mean k₀'.om ν χ₃ (g i) := fun u => by
    funext v; simp [Finset.sum_apply]
  refine ⟨fun u v => ∑ i, e i u * mean k₀'.om ν χ₃ (g i) v, fun b => χ₃ b⁻¹, ⟨?_, fun v => hEv (hl v), fun u => ?_⟩,
    fun a ha hc v => hEe _ _ (h1 a ha hc) _ (hl v), fun b hb hc u => ?_, fun k k' hk hk' hag hag' φ hφ => ?_⟩
  · exact continuous_finsetSum _ fun i _ => ((hEv (he i)).1.cont.comp continuous_fst).mul
      ((hg' i).1.cont.comp continuous_snd)
  · rw [hr]
    exact (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hg' i) :
      _ ∈ vacSub ψ S A' (latO S A' y.L z.L fun _ => True))
  · simp only []
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hr, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_comm]
    exact congrArg _ (eigen_mean hwb hθ hχ hm (hg i).1 ⟨b, hb, hc⟩)
  · obtain ⟨χA₁, χS₁, hwa₁⟩ := hk.weil
    obtain ⟨χS₁', χA₁', hwb₁⟩ := hk'.weil

    have hmean : ∀ i, mean k₀'.om ν χ₃ (g i) = mean k'.om ν χ₃ (g i) := fun i => by
      funext w
      simp only [mean]
      congr 1
      funext b
      rw [hag' b.1 b.2.1 1 (GinfC A').one_mem (g i) (hg i).1]
    have hEk : ∀ b : ↥(GinfC S ⊓ Subgroup.center (GA D S)), ∀ f ∈ E, k.om (1, b.1) f = χ₃ b.1 • f :=
      fun b f hf => by
        rw [hag 1 (GinfC A).one_mem b.1 b.2.1 f (hEv hf).1]
        exact hEe _ _ (h3 b.1 b.2.1 b.2.2) f hf
    have hg'' : ∀ i, mean k'.om ν χ₃ (g i) ∈ vacSub ψ S A' (latO S A' y.L z.L fun _ => True) := fun i =>
      vac_mean hwb₁ hθ hχ (hg i)
    simp only [hmean]
    funext h₂
    have hX : ∀ i, IsThetaFunO ψ A S (comb ψ A S k.c (e i)) := fun i => theta_comb hwa₁.std hk.fin (hEv (he i)).1
    rw [show C₁ = fun u v => ∑ i, e i u * g i v from funext fun u => funext (hs u), biComb_sum, biComb_sum,
      biLift_sum hwa₁ hwb₁ hx.cpt hy.cpt _ _ hX (fun i => theta_comb hwb₁.std hk'.fin (hg i).1) hφ,
      biLift_sum hwa₁ hwb₁ hx.cpt hy.cpt _ _ hX (fun i => theta_comb hwb₁.std hk'.fin (hg'' i).1) hφ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [comb_mean hwb₁ hχ hk'.fin (hg i).1]
    refine (lift_mean hwb₁ hθ hy.cpt y.vol hχ (theta_comb hwb₁.std hk'.fin (hg i).1)
      (contAut_lift hwa₁ hx.cpt x.vol (hX i) hφ) (fun b h => ?_) h₂).symm
    rw [← integral_const_mul]
    congr 1
    funext a
    have e' : ((a, h * b.1) : GA D A × GA D S) = (a, h) * (1, b.1) := by simp
    rw [e', map_mul, Module.End.mul_apply, GlobalTheory.FrComb.om_comb hwa₁ (GinfC A).one_mem b.2.1 hk.fin (hEv (he i)).1,
      hEk b _ (he i), comb_smul, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.AvgMidUnif

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroLeftMemCoreLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ContrComb

theorem extL_mem_latO : ∀ (D : D7) (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (P : Pl D → Prop) (LA : Lat A) (LS : Lat S) (M : Lat V₀), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC V₀ M → (∀ v, P v → ∃ LL, OrthAt o M LA LL v) → ∀ u ∈ latO A S (LA : Set _) (LS : Set _) P, (o.resS S).symm (u, 0) ∈ latO V₀ S (M : Set _) (LS : Set _) P := by
  intro D V₀ A L S o P LA LS M hA hS hM hO u hu
  rw [_root_.GlobalTheory.FinPl.LatMem.mem_latO_iff D A S LA LS hA hS P u] at hu
  obtain ⟨huP, huL⟩ := hu
  rw [_root_.GlobalTheory.FinPl.LatMem.mem_latO_iff D V₀ S M LS hM hS P, OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
  have hloc := (_root_.GlobalTheory.FinPl.localComponents D P).2
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (huP i k)
  · have hy' := ((hloc V₀).2.2.2 M y hM.1).1 hy
    have hp : o.pA *ᵥ y ∈ latV A LA P := by
      refine ((hloc A).2.2.2 LA (o.pA *ᵥ y) hA.1).2 ⟨fun i => ?_, fun v hv e he => ?_⟩
      · rw [Matrix.mulVec, dotProduct]
        exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hy'.1 k)
      · obtain ⟨LL, hLL⟩ := hO v hv
        have h1 := ((hLL (e • y)).1 (hy'.2 v hv e he)).1
        rwa [Matrix.mulVec_smul] at h1
    have h2 := huL _ hp
    change (u * o.pA) *ᵥ y ∈ latA S LS P
    rwa [← Matrix.mulVec_mulVec]

end GlobalTheory.ContrComb
end

