module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0710
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0088
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvSmulMemOfRedL
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevelPrimePointModelRealisation
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0141
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteNotIsUnitOneAddSmul
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompactSpaceDefiniteUnitaryInfinitePoints
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

noncomputable section

open Formalism.UG

namespace GlobalTheory.InfUCompact

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem compactSpace_UJ (E : Type) [Field E] (n : ℕ) :
    CompactSpace (UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E))) := by
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) (Cinf E)) := GlobalTheory.KinfCompactness.compactSpace_Kinf E n
  let f : Matrix.unitaryGroup (Fin n) (Cinf E) → GL (Fin n) (Cinf E) := fun u =>
    ⟨u.1, star u.1, Matrix.mem_unitaryGroup_iff.1 u.2, Matrix.mem_unitaryGroup_iff'.1 u.2⟩
  have hf : Continuous f :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩
  have hr : Set.range f =
      (UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E)) : Set (GL (Fin n) (Cinf E))) := by
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      change cT (starRingEnd (Cinf E)) u.1 * 1 * u.1 = 1
      rw [mul_one]
      exact Matrix.mem_unitaryGroup_iff'.1 u.2
    · intro hg
      have h : cT (starRingEnd (Cinf E)) (g : Matrix (Fin n) (Fin n) (Cinf E)) * 1 * g = 1 := hg
      rw [mul_one] at h
      exact ⟨⟨g.1, Matrix.mem_unitaryGroup_iff'.2 h⟩, Units.ext rfl⟩
  exact isCompact_iff_compactSpace.1 (hr ▸ isCompact_range hf)

theorem range_infPt : Set.range (GlobalTheory.DefiniteDense.infPt (E := E) (n := n)) = (infU E n : Set (UA E n)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact pFin_infGL _
  · intro hx
    have hp : ∀ a : Ad E, pInf E (conjAd E a) = starRingEnd (Cinf E) (pInf E a) :=
      fun a => (infEq E).symm_apply_apply _
    have hM : GeneralLinearGroup.map (pInf E) x.1 ∈
        UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E)) := by
      have h0 : cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * x.1 = 1 := x.2
      rw [mul_one] at h0
      have e : cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) =
          (cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E))).map (pInf E) := by
        ext i j
        simp [Formalism.UG.cT, hp]
      change cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) * 1 *
        (x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) = 1
      rw [e, mul_one, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]
    refine ⟨⟨_, hM⟩, Subtype.ext (ga_ext ?_ ?_)⟩
    · exact pInf_infGL _
    · exact (pFin_infGL _).trans (Eq.symm hx)

theorem compactSpace_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
    CompactSpace (infU E n) := by
  intro E _ _ _ n
  haveI := compactSpace_UJ E n
  have h : IsCompact (infU E n : Set (UA E n)) :=
    range_infPt (E := E) (n := n) ▸ isCompact_range GlobalTheory.DefiniteDense.continuous_infPt
  exact isCompact_iff_compactSpace.1 h

end GlobalTheory.InfUCompact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvaluationMapTrueChainFormsToForms
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PerQ.ptT_forms_built : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), (∀ φ ∈ ((I.tw l l0 Z).fm u a).Fi B.R.m, GlobalTheory.PerQ.PtT (I.rec7 l Z) u a φ ∈ ((I.tw l l0 Z).fm u a).ptC) ∧ ((I.rec7 l Z).fm u).SgInterlace := by
  intro B X I hI l Z l0 u a
  have hW := fun τ => _root_.GlobalTheory.PerQ.trueWeights_built I hI l Z u a τ
  refine ⟨?_, ?_⟩
  swap
  · have ⟨τ⟩ : Nonempty B.fields.Tau := inferInstance
    exact (hW τ).2.2.2.2
  intro φ hφ
  set M := I.fm l u a with hM
  have key : ∀ x ∈ (M.lat B.R.m).L, ∃ y, M.ptEmb y =
      (I.per l u a).lowerMap ((I.per l u a).evz (M.emb B.R.m x)) := by
    intro x hx
    obtain ⟨y, -, hy⟩ := GlobalTheory.LvT.BuiltChain.exists_image (Q := I.perIn u a) B.fields.emb B.embLL (B.hcW u)
      GlobalTheory.LvT.BuiltChain.branching_ok (l.ch u a) (l.per u a)
      (fun τ => (hW τ).2.2.1) (fun τ => (hW τ).2.2.2.1) ((l.fmL u a).fam B.R.m) (l.fmL u a).famP x hx
    exact ⟨y, hy⟩
  have rat : ∀ x, ∃ y, M.ptEmb y = (I.per l u a).lowerMap ((I.per l u a).evz (M.emb B.R.m x)) := by
    intro x
    have hx : x ∈ Submodule.span B.LL ((M.lat B.R.m).L : Set (M.lat B.R.m).V) := by
      rw [(M.lat_good B.R.m).2.2]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact key x hx
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨y, e⟩ := ha
      obtain ⟨z, e'⟩ := hb
      exact ⟨y + z, by rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), e, e']⟩
    | smul r a _ ha =>
      obtain ⟨y, e⟩ := ha
      refine ⟨r • y, ?_⟩
      rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, e, LinearMap.map_smul, LinearMap.map_smul]
  have ptMem : ∀ y, M.ptEmb y ∈ M.ptC := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← M.ptEmb_basis.2, ← M.ptLat.b.sum_repr y, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hφ' : φ ∈ M.Fi B.R.m := hφ
  rw [← (M.emb_basis B.R.m).2] at hφ'
  have hle : Submodule.span ℂ (Set.range fun a => M.emb B.R.m ((M.lat B.R.m).b a)) ≤
      M.ptC.comap ((I.per l u a).lowerMap ∘ₗ (I.per l u a).evz) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    obtain ⟨y, e⟩ := rat ((M.lat B.R.m).b b)
    show (I.per l u a).lowerMap ((I.per l u a).evz _) ∈ M.ptC
    rw [← e]
    exact ptMem y
  exact hle hφ'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalBasisRepLatticeIntegralCoordsSpec
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ.Co

theorem usage₉ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl), Formalism.L2.Forms.IsLocBasis (B.places.resChar w) ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c) : Set _) (GlobalTheory.PerQ.Co.bP I u a w c) ∧ (∀ x, iniH (N_m_succ B.R) (((GlobalTheory.PerQ.Co.bM I u a w c : GL (Fin (B.R.N B.R.m)) B.fields.E) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) = ((GlobalTheory.PerQ.Co.bP I u a w c : GL (Fin (B.R.N B.R.m - 1)) B.fields.E) : Matrix _ _ B.fields.E) *ᵥ iniH (N_m_succ B.R) x) ∧ (∀ x, (I.perIn u a).tz * (((GlobalTheory.PerQ.Co.bM I u a w c : GL (Fin (B.R.N B.R.m)) B.fields.E) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) (Br.iL (N_m_succ B.R)) = x (Br.iL (N_m_succ B.R))) ∧ Formalism.L2.Forms.IsLocBasis (B.places.resChar w) (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c) : Set _) (GlobalTheory.PerQ.Co.bM I u a w c) := by
  intro B X I _hI l u a w c
  haveI : Fact (B.places.resChar w).Prime := ⟨B.places.resChar_prime w⟩
  have hlat := (l.per u a).step.lsh_lat c.1 ((I.perIn u a).S'.rep c)
  have hP : Formalism.L2.Forms.IsLocBasis (B.places.resChar w) ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c) : Set _)
      (GlobalTheory.PerQ.Co.bP I u a w c) := by
    let d := ((I.stX a).rep c).1.1.deco
    have hN := GlobalTheory.LvT.Pts.span_eq_top_of_unimodular d.1.N d.2.lat d.2.uni
    have hspan : Submodule.span B.fields.E
        ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c) : Set _) = ⊤ :=
      top_unique (hN.ge.trans (Submodule.span_mono d.2.N_le_Lsh))
    obtain ⟨g, hg⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis
      (B.places.resChar w) B.fields.E _ hlat.fg hspan
    exact Classical.epsilon_spec (p := fun g : GL (Fin (B.R.N B.R.m - 1)) B.fields.E =>
      Formalism.L2.Forms.IsLocBasis (B.places.resChar w) ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c) : Set _) g) ⟨g, hg⟩
  refine ⟨hP, ?_⟩
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.isLocBasis_snoc (N_m_succ B.R) (I.perIn u a).tz (l.per u a).tz_ne
    (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c))
    ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c))
    (fun x => (l.per u a).Lsh_til c.1 ((I.perIn u a).S'.rep c) x) (B.places.resChar w) (GlobalTheory.PerQ.Co.bP I u a w c)
    (B.places.resChar_prime w) hP
  exact Classical.epsilon_spec (p := fun g : GL (Fin (B.R.N B.R.m)) B.fields.E =>
    (∀ x, iniH (N_m_succ B.R) ((g : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) =
        ((GlobalTheory.PerQ.Co.bP I u a w c : GL (Fin (B.R.N B.R.m - 1)) B.fields.E) : Matrix _ _ B.fields.E) *ᵥ iniH (N_m_succ B.R) x) ∧
      (∀ x, (I.perIn u a).tz * ((g : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E) *ᵥ x) (Br.iL (N_m_succ B.R)) =
        x (Br.iL (N_m_succ B.R))) ∧
      Formalism.L2.Forms.IsLocBasis (B.places.resChar w)
        (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c) : Set _) g) ⟨g, hg⟩

end GlobalTheory.PerQ.Co
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SharpBoundStabilityLatticeColumnChain
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

namespace GlobalTheory.LvT.Built.Assemble

theorem sharpBound_stability_latticeColumnChain : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u),
    (∀ i, i ≤ D.R.m → Nonempty (Split (B.J.A i) B.J.T)) → B.Sees →
    (∀ i, i < D.R.m → ∃ k : B.Ker i, Built.Dat.KerEq k ∧ Built.Dat.KerDil k ∧ Built.Dat.KerUK k ∧ Built.Dat.KerBar k ∧
      Built.Dat.KerP k) →
    Module.finrank ℚ B.E * D.R.N D.R.m + 1 < B.J.T → TwColumn.WtSigns B.ch → Conclusion5Sharp B.ch ∧ FormsStable B.ch := by
  intro D u B hsp hsee hker hT hW

  have hM : ∀ i (h : i ≤ D.R.m), ∃ M : PtModel B.ch i, Nonempty (B.Real i (hsp i h).some M) :=
    fun i h => _root_.GlobalTheory.LvT.Built.RealM.exists_real D u B i (hsp i h).some
  let Lv : LevTie B.ch := fun i h => (hM i h).choose
  have hR : ∀ i (h : i ≤ D.R.m), B.Real i (hsp i h).some (Lv i h) := fun i h => (hM i h).choose_spec.some

  have hC : ∀ i (h : i ≤ D.R.m), ∃ Co : (Lv i h).Coord, Co.Ok ∧ (hR i h).ValIs Co :=
    fun i h => GlobalTheory.T.exists_coordinates_valueLattices_eq_weylLattices D u B i (hsp i h).some (Lv i h) (hR i h) h hsee
  let Vt : ValTie Lv := fun i h => ⟨(hC i h).choose, (hC i h).choose_spec.1⟩

  have hk : ∀ i (h : i < D.R.m), ∃ k : B.Ker i, Built.Dat.KerEq k ∧ Built.Dat.KerDil k ∧ Built.Dat.KerUK k ∧
      Built.Dat.KerBar k ∧ Built.Dat.KerP k := hker

  have hK : ∀ i (h : i < D.R.m), ∃ K : KerPt (Lv i h.le) (Lv (i + 1) h),
      K.TgtEq ∧ Built.Dat.KerIs (hR i h.le) (hR (i + 1) h) K (hk i h).choose :=
    fun i h => _root_.GlobalTheory.LvT.Built.KerExt.exists_kerPt D u B i (hsp i h.le).some (hsp (i + 1) h).some (Lv i h.le) (Lv (i + 1) h)
      (hR i h.le) (hR (i + 1) h) _ (hk i h).choose_spec.1
  let Kt : KerTie Lv := fun i h => (hK i h).choose
  have laws : KerLaws Vt Kt :=
    { tgt := fun i h => (hK i h).choose_spec.1
      dil := fun i h => _root_.GlobalTheory.LvT.Built.DilPass.dilLaw_of_kerDil D u B i _ _ _ _ (hR i h.le) (hR (i + 1) h) _ _
        (hK i h).choose_spec.1 (hK i h).choose_spec.2 (hk i h).choose_spec.2.1
      uk := fun i h => GlobalTheory.T.heckeLaw_pointKernel_of_coefficientKernel D u B i _ _ _ _ (hR i h.le) (hR (i + 1) h) _ _
        (hK i h).choose_spec.1 (hK i h).choose_spec.2 (hk i h).choose_spec.2.2.1
      bar := fun i h => _root_.GlobalTheory.LvT.Built.BarPass.intBar_of_kerBar D u B i _ _ _ _ (hR i h.le) (hR (i + 1) h) _ _ _ _
        (hK i h).choose_spec.1 (hK i h).choose_spec.2 (hC i h.le).choose_spec.1 (hC (i + 1) h).choose_spec.1
        (hC i h.le).choose_spec.2 (hC (i + 1) h).choose_spec.2 (hk i h).choose_spec.2.2.2.1
      intP := fun i h => IntPPass.intP_of_kerP D u B i _ _ _ _ (hR i h.le) (hR (i + 1) h) _ _ _ _
        (hK i h).choose_spec.1 (hK i h).choose_spec.2 (hC i h.le).choose_spec.1 (hC (i + 1) h).choose_spec.1
        (hC i h.le).choose_spec.2 (hC (i + 1) h).choose_spec.2 (hk i h).choose_spec.2.2.2.2 }
  have hF : FormsStable B.ch := formsStable_of_tgtEq D u B.ch Lv Kt laws.tgt
  have h4 : LevelChainUOperatorCommutation B.ch := levelChainUOperatorCommutation_of_pointPairLaw D u B.ch Lv Kt laws.tgt laws.uk
  have hst : StabUnit B.ch := StabOrder.stabUnit_of_chainIn B.ch B.I B.emb D.what₂.embLL B.hI rfl hT
  have hWb : WtBounds B.ch := wtBounds_of_nonneg D u B.ch hW.1 hW.2
  exact ⟨levelChainSharpColumnValuation_of_stability D u B.ch hF h4 (UKS.ukSharp D u B.ch Lv Vt Kt laws hst hWb) hWb, hF⟩

end GlobalTheory.LvT.Built.Assemble
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedOfIsCMUnram
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped Matrix

namespace GlobalTheory.DefiniteMass
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.LocalConjugacy

theorem mass_eq_of_sameGenus {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hh : h.IsSymm)
    (hst : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K))
    {L M : Submodule (𝓞 K) V} (hLM : Formalism.HermitianLatticesTheory.SameGenus h L M) :
    Formalism.HermitianLatticesTheory.mass h L = Formalism.HermitianLatticesTheory.mass h M := by
  have he := (Formalism.HermitianLatticesTheory.final_genusBasic (𝓞 K) K V h hh hst).1
  have hg : Formalism.HermitianLatticesTheory.genus h L = Formalism.HermitianLatticesTheory.genus h M :=
    Set.ext fun N => and_congr_right fun _ => ⟨he.trans (he.symm hLM), he.trans hLM⟩
  have hc : Formalism.ThetaLiftIndependence.IsClassReps h L = Formalism.ThetaLiftIndependence.IsClassReps h M := by
    funext s
    unfold Formalism.ThetaLiftIndependence.IsClassReps
    rw [hg]
  unfold Formalism.HermitianLatticesTheory.mass
  rw [hc]

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem unramified_of_isCMUnram (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
  Formalism.L2.Pj.unramBridge_holds E fun P hP => by
    obtain ⟨θ, t, e1, e2⟩ := hc.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) θ = t :=
      RingOfIntegers.ext e1.symm
    rwa [this]

theorem exists_isometry (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W : Formalism.BasicNotions.HSpace E) (hs : W.SigOK)
    (hp : ∀ τ : E →+* ℂ, W.sig τ = (W.rank, 0)) :
    ∃ e : W.V ≃ₗ[E] (Fin W.rank → E), ∀ x y, stdForm E W.rank (e x) (e y) = W.hT x y := by
  haveI := unramified_of_isCMUnram hc
  have hG : ∀ a b, cc (W.gramᵀ a b) = W.gramᵀ b a := fun a b => W.herm.eq (W.frame b) (W.frame a)
  have hd : W.gramᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W).ne_zero
  obtain ⟨P, hP0, hP⟩ := congr_signMatrix (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt)
    GlobalTheory.QNorm.hasseNormSt hG hd (isLattice_coordLat W W.L0 W.standardTuple_isLattice W.baseLattice_isUnimodular) (selfDual_coordLat W W.L0 W.baseLattice_isUnimodular)
    Set.univ (fun _ => Or.inl trivial) W.rank fun τ _ => by
      have h0 := hs τ
      rw [hp τ] at h0
      obtain ⟨e, Q, hQ⟩ := h0
      have hJ : Formalism.UG.Jpq W.rank 0 = 1 := by
        ext i j
        rcases i with i | i
        · rcases j with j | j
          · simp [Formalism.UG.Jpq, Matrix.one_apply]
          · exact j.elim0
        · exact i.elim0
      rw [hJ] at hQ
      refine ⟨Q.1.submatrix e e, ?_, ?_⟩
      · rw [Matrix.det_submatrix_equiv_self]
        exact (Matrix.isUnit_iff_isUnit_det _ |>.1 Q.isUnit).ne_zero
      · have h1 := congrArg (fun M => (Matrix.submatrix M e e)ᵀ) hQ
        simp only [Matrix.submatrix_one_equiv, Matrix.transpose_one] at h1
        rw [← Matrix.submatrix_mul_equiv _ _ e e e, ← Matrix.submatrix_mul_equiv _ _ e e e,
          Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc] at h1
        rw [Published.gram_eq]
        convert h1 using 1
        · congr 2
          ext i j
          simp
        · ext i j
          simp [Matrix.diagonal_apply, Matrix.one_apply, sgn]
  have h1 : signMatrix E W.rank W.rank = 1 := by
    ext i j
    simp [signMatrix, Matrix.diagonal_apply, Matrix.one_apply]
  rw [h1, Matrix.mul_one] at hP
  refine ⟨W.frame.equivFun.trans (Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP0.isUnit)), fun x y => ?_⟩
  rw [← herm_coord, hP]
  change ∑ i, cc ((P *ᵥ W.frame.equivFun x) i) * (P *ᵥ W.frame.equivFun y) i = _
  generalize W.frame.equivFun x = u
  generalize W.frame.equivFun y = v
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [herm, cc, Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring

theorem stdLat_eq (n : ℕ) : stdLat E n = GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdMod E n := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun x hx => ?_
  · rintro _ ⟨j, rfl⟩
    exact GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.single_mem_stdMod j
  · choose a ha using GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.mem_stdMod.1 hx
    rw [pi_eq_sum_univ' x]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← ha j]
    exact Submodule.smul_mem _ (a j) (Submodule.subset_span ⟨j, rfl⟩)

theorem mem_dual_iff {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (L : Submodule (𝓞 E) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, ∃ a : 𝓞 E, (a : E) = h y x := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_one]

theorem loc_le_of_nsmul {V : Type} [AddCommGroup V] [Module (𝓞 E) V] {p : ℕ} (hp : p.Prime)
    {P : Ideal (𝓞 E)} (hP : P.IsMaximal) (hpP : (p : 𝓞 E) ∈ P) {L M : Submodule (𝓞 E) V}
    (h : ∀ x ∈ L, ∃ k : ℕ, ¬ p ∣ k ∧ k • x ∈ M) :
    Formalism.HermitianLatticesTheory.loc (K := E) P L ≤ Formalism.HermitianLatticesTheory.loc (K := E) P M := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨k, hk, hkx⟩ := h _ hx
  have hkP : (k : 𝓞 E) ∉ P := fun hkP => by
    obtain ⟨a, b, hab⟩ := ((Nat.Prime.coprime_iff_not_dvd hp).2 hk).cast (R := 𝓞 E)
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (P.mul_mem_left a hpP) (P.mul_mem_left b hkP)))
  have hc : (k : 𝓞 E) ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) P := by
    refine Submonoid.subset_closure ⟨hkP, fun t ht => ?_⟩
    have : t = (k : 𝓞 E) := RingOfIntegers.coe_injective (by rw [ht, map_natCast, star_natCast])
    rwa [this]
  exact ⟨_, mul_mem hc hs, by rwa [mul_smul, Nat.cast_smul_eq_nsmul]⟩

theorem sameGenus_stdLat (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.IsLattice E L) (hsd : ∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ a : 𝓞 E, (a : E) = stdForm E n y x) :
    Formalism.HermitianLatticesTheory.SameGenus (stdForm E n) (stdLat E n) L := by
  haveI := unramified_of_isCMUnram hc
  have hf : ∀ x y : Fin n → E, GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm x y = stdForm E n y x := fun x y =>
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤ := by
    by_contra h
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr h)
    let w : Fin n → E := fun i => star (f (Pi.single i 1))
    have hw : ∀ y ∈ L, stdForm E n y w = 0 := by
      intro y hy
      have hyf : f y = 0 := LinearMap.mem_ker.mp (hle (Submodule.subset_span hy))
      have hrepr := f.pi_apply_eq_sum_univ y
      have hsingle : ∀ i : Fin n, (fun j => if i = j then (1 : E) else 0) = Pi.single i 1 := by
        intro i
        ext j
        simp [Pi.single_apply, eq_comm]
      simp only [hsingle] at hrepr
      change (∑ i, star (y i) * star (f (Pi.single i 1))) = 0
      calc
        _ = star (∑ i, y i * f (Pi.single i 1)) := by simp
        _ = star (f y) := by rw [hrepr]; simp [smul_eq_mul]
        _ = 0 := by rw [hyf, star_zero]
    have hline : ∀ c : E, c • w ∈ L := by
      intro c
      apply (hsd _).2
      intro y hy
      refine ⟨0, ?_⟩
      simp only [map_zero, LinearMap.map_smul, hw y hy, smul_zero]
    have hw0 : w = 0 := by
      by_contra hw0
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hw0
      have htop : L.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin n => E) j) = ⊤ := by
        refine eq_top_iff.mpr fun x _ => ⟨(x / w j) • w, hline _, ?_⟩
        simp [div_mul_cancel₀ _ hj]
      have : Module.Finite (𝓞 E) E := ⟨by rw [← htop]; exact hL.fg.map _⟩
      have := Algebra.IsIntegral.of_finite (𝓞 E) E
      exact RingOfIntegers.not_isField E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
    apply hf0
    apply LinearMap.ext
    intro y
    rw [f.pi_apply_eq_sum_univ y]
    apply Finset.sum_eq_zero
    intro i _
    have hi : star (f (Pi.single i 1)) = 0 := congrFun hw0 i
    have : f (Pi.single i 1) = 0 := by simpa using congrArg star hi
    have hsingle : (fun j => if i = j then (1 : E) else 0) = Pi.single i 1 := by
      ext j
      simp [Pi.single_apply, eq_comm]
    rw [hsingle, this, smul_zero]
  have hgen := GlobalTheory.GenusSelfDual.inGenus_of_selfDual (Λ := ⟨L, hL.fg, hspan⟩) fun x => by
    simpa only [hf] using hsd x
  intro P hP
  haveI : P.IsPrime := hP.isPrime
  obtain ⟨p, hp, hpP⟩ : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 E) ∈ P := by
    haveI : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P
      (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E))
    obtain ⟨p, hp⟩ := CharP.exists (𝓞 E ⧸ P)
    refine ⟨p, (CharP.char_is_prime_or_zero (𝓞 E ⧸ P) p).resolve_right (CharP.char_ne_zero_of_finite (𝓞 E ⧸ P) p), ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero]
  obtain ⟨γ, hγ, h1, h2⟩ := hgen p hp
  refine ⟨γ, fun x y => by rw [← hf, ← hf]; exact hγ y x, ?_⟩
  rw [gmap_eq_tMap, tMap_loc, stdLat_eq]
  exact le_antisymm (loc_le_of_nsmul hp hP hpP h2) (loc_le_of_nsmul hp hP hpP h1)

theorem mass_eq_std (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W : Formalism.BasicNotions.HSpace E) (hs : W.SigOK)
    (hp : ∀ τ : E →+* ℂ, W.sig τ = (W.rank, 0)) :
    Formalism.HermitianLatticesTheory.mass W.hT W.L0 = Formalism.HermitianLatticesTheory.mass (stdForm E W.rank) (stdLat E W.rank) := by
  obtain ⟨e, he⟩ := exists_isometry hc W hs hp
  have hL : Submodule.IsFullLattice E W.L0 :=
    { toIsLattice := W.standardTuple_isLattice
      span_eq_top := GlobalTheory.LocalConjugacy.span_eq_top_of_unimodular W W.L0
        W.standardTuple_isLattice W.baseLattice_isUnimodular }
  obtain ⟨h1, h2, -⟩ := Formalism.HermitianLatticesTheory.massBasic _ _ W.hT W.herm
    (GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.trace_pos hc.2.1 W hs hp) W.L0 hL
  have h3 := mass_transport e.symm (isoSymm e he) (tMap e W.L0) (by rwa [tMap_symm]) (by rwa [tMap_symm])
  rw [tMap_symm] at h3
  rw [← h3]
  refine (mass_eq_of_sameGenus _ (stdForm_symm E _) (fun r => ?_)
    (sameGenus_stdLat hc (tMap e W.L0) (Submodule.IsLattice.of_fg E (W.standardTuple_isLattice.fg.map _)) fun x => ?_)).symm
  · exact ⟨IsCMField.ringOfIntegersComplexConj E r, rfl⟩
  · obtain ⟨x, rfl⟩ := e.surjective x
    rw [mem_tMap, e.symm_apply_apply]
    conv_lhs => rw [← show Formalism.HermitianLatticesTheory.dual W.hT W.L0 = W.L0 from W.baseLattice_isUnimodular, mem_dual_iff]
    constructor
    · rintro H _ ⟨y, hy, rfl⟩
      exact (he y x).symm ▸ H y hy
    · intro H y hy
      exact he y x ▸ H _ ⟨y, hy, rfl⟩

end

theorem mass_eq_massI (D : D7) : letI := D.host.cmStar
    ∀ W : Formalism.BasicNotions.HSpace D.host.E, W.SigOK → (∀ τ : D.host.E →+* ℂ, W.sig τ = (W.rank, 0)) →
      Formalism.HermitianLatticesTheory.mass W.hT W.L0 = massI D W.rank :=
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  fun W hs hp => mass_eq_std (E := D.host.E) D.sp.cm.cmUnram W hs hp

end GlobalTheory.DefiniteMass
end
end

