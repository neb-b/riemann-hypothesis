module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralUnramifiedOutsideOpenSubsetInsertPlace
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.HaarStep


set_option maxHeartbeats 1000000 in
theorem integral_openOff_insert : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (Sf : Finset (FinPl D)) (v : FinPl D), v ∉ Sf → ∀ μ : Measure (Gv A v), μ.IsHaarMeasure → μ (stabLoc D.sp.cm.sig A.gram L v) = 1 → ∀ (S' : Finset (FinPl D)), (∀ u, u ∈ S' ↔ u = v ∨ u ∈ Sf) → ∀ F : GA D A → ℂ, IntegrableOn F (openOff A L S') m → ∫ g in openOff A L S', F g ∂m = ∫ x in openOff A L Sf, (∫ y, F (x * (emb D.sp.cm.sig A.gram v (proj D.sp.cm.sig A.gram v x))⁻¹ * emb D.sp.cm.sig A.gram v y) ∂μ) ∂m := by
  intro D A L hL m hm Sf v hv μ hμ hK S' hS' F hF
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.AdIsom.selfDual_isFullLattice hL
  have hne : ∀ u, u ∉ S' → u ≠ v := fun u hu h => hu ((hS' u).2 (Or.inl h))
  have memU : ∀ x, x ∈ openOff A L Sf ↔ x ∈ openOff A L S' ∧
      proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram L v := by
    intro x
    constructor
    · intro h
      exact ⟨fun u hu => h u (fun hu' => hu ((hS' u).2 (Or.inr hu'))), h v hv⟩
    · rintro ⟨h1, h2⟩ u hu
      by_cases e : u = v
      · subst e; exact h2
      · exact h1 u (fun h => by rcases (hS' u).1 h with h | h; exact e h; exact hu h)
  have memV : ∀ (y : Gv A v) (x : GA D A), emb D.sp.cm.sig A.gram v y * x ∈ openOff A L S' ↔ x ∈ openOff A L S' := by
    intro y x
    refine forall_congr' fun u => imp_congr_right fun hu => ?_
    rw [map_mul, proj_emb_ne _ _ (hne u hu), one_mul]
  have isOpen_off : ∀ S : Finset (FinPl D), IsOpen (openOff A L S) := by
    intro S
    let H : Subgroup (GA D A) :=
      ⨅ u, ⨅ (_ : u ∉ S), (stabLoc D.sp.cm.sig A.gram L u).comap (proj D.sp.cm.sig A.gram u)
    have eH : (H : Set (GA D A)) = openOff A L S := by
      ext g; simp [H, openOff, Subgroup.mem_iInf]
    rw [← eH]
    refine Subgroup.isOpen_mono (H₁ := levelOpen D.sp.cm.sig A.gram L) ?_ (isOpen_levelOpen _ _ L)
    intro g hg
    simp only [H, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro u _
    exact (mem_levelOpen.1 hg) u
  have hUm : MeasurableSet (openOff A L Sf) := (isOpen_off Sf).measurableSet
  have hVm : MeasurableSet (openOff A L S') := (isOpen_off S').measurableSet
  have hKo : IsOpen (stabLoc D.sp.cm.sig A.gram L v : Set (Gv A v)) := isOpen_stabLoc _ _ L v
  have hright : ∀ k ∈ stabLoc D.sp.cm.sig A.gram L v, μ.map (fun y => y * k) = μ := by
    intro k hk
    rw [GlobalTheory.AdelicUnimod.map_mul_right_eq,
      GlobalTheory.AdelicUnimod.modular_compact _ hKo (isCompact_stabLoc _ _ L v) hk, one_smul]
  have step1 : ∀ x ∈ openOff A L Sf,
      ∫ y, F (x * (emb D.sp.cm.sig A.gram v (proj D.sp.cm.sig A.gram v x))⁻¹ * emb D.sp.cm.sig A.gram v y) ∂μ =
        ∫ y, F (emb D.sp.cm.sig A.gram v y * x) ∂μ := by
    intro x hx
    have hkK : proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram L v := hx v hv
    set k := proj D.sp.cm.sig A.gram v x with hk
    set x' := x * (emb D.sp.cm.sig A.gram v k)⁻¹ with hx'
    have hx'1 : proj D.sp.cm.sig A.gram v x' = 1 := by
      rw [hx', map_mul, map_inv, proj_emb_self, mul_inv_cancel]
    have hxx : x = x' * emb D.sp.cm.sig A.gram v k := by rw [hx', inv_mul_cancel_right]
    have e : ∀ y, emb D.sp.cm.sig A.gram v y * x = x' * emb D.sp.cm.sig A.gram v (y * k) := by
      intro y
      have hc := (commute_emb D.sp.cm.sig A.gram y hx'1).eq
      calc emb D.sp.cm.sig A.gram v y * x = emb D.sp.cm.sig A.gram v y * x' * emb D.sp.cm.sig A.gram v k := by
            rw [mul_assoc, ← hxx]
        _ = x' * emb D.sp.cm.sig A.gram v y * emb D.sp.cm.sig A.gram v k := by rw [hc]
        _ = x' * emb D.sp.cm.sig A.gram v (y * k) := by rw [map_mul, mul_assoc]
    simp_rw [e]
    have h := integral_map_equiv (μ := μ) (MeasurableEquiv.mulRight k)
      (fun y => F (x' * emb D.sp.cm.sig A.gram v y))
    have hm' : Measure.map (MeasurableEquiv.mulRight k) μ = μ := hright k hkK
    rw [hm'] at h
    exact h
  rw [setIntegral_congr_fun hUm step1]

  have hec : Continuous (emb D.sp.cm.sig A.gram v) := continuous_emb _ _ v
  have hpc : Continuous (proj D.sp.cm.sig A.gram v) := continuous_proj _ _ v
  let Q : Set (GA D A × Gv A v) :=
    {q | (proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ stabLoc D.sp.cm.sig A.gram L v}
  have hQo : IsOpen Q := hKo.preimage (((hpc.comp continuous_fst).inv).mul continuous_snd)
  let f₂ : GA D A × Gv A v → ℂ := Q.indicator (fun q => (openOff A L S').indicator F q.1)
  let T : GA D A × Gv A v → GA D A × Gv A v := fun p => (emb D.sp.cm.sig A.gram v p.2 * p.1, p.2)
  have hT : MeasurePreserving T (m.prod μ) (m.prod μ) := by
    have h1 : MeasurePreserving (fun p : Gv A v × GA D A => (p.1, emb D.sp.cm.sig A.gram v p.1 * p.2))
        (μ.prod m) (μ.prod m) :=
      MeasurePreserving.skew_product (MeasurePreserving.id μ)
        ((hec.comp continuous_fst).mul continuous_snd).measurable
        (Filter.Eventually.of_forall fun y => map_mul_left_eq_self m (emb D.sp.cm.sig A.gram v y))
    have h2 : MeasurePreserving (Prod.swap : GA D A × Gv A v → Gv A v × GA D A) (m.prod μ) (μ.prod m) :=
      Measure.measurePreserving_swap
    have h3 : MeasurePreserving (Prod.swap : Gv A v × GA D A → GA D A × Gv A v) (μ.prod m) (m.prod μ) :=
      Measure.measurePreserving_swap
    have h4 := (h3.comp h1).comp h2
    have e : T = (Prod.swap ∘ (fun p : Gv A v × GA D A => (p.1, emb D.sp.cm.sig A.gram v p.1 * p.2))) ∘ Prod.swap := by
      funext p; rfl
    rw [e]; exact h4
  have hCm : ∀ a : Gv A v, MeasurableSet {y : Gv A v | a⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v} :=
    fun a => (hKo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμC : ∀ a : Gv A v, μ {y : Gv A v | a⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v} = 1 := by
    intro a
    rw [← hK]
    exact measure_preimage_mul μ a⁻¹ _
  have slice : ∀ w, (fun y => f₂ (w, y)) =
      {y : Gv A v | (proj D.sp.cm.sig A.gram v w)⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v}.indicator
        (fun _ => (openOff A L S').indicator F w) := by
    intro w; funext y
    rfl
  have hFV : Integrable ((openOff A L S').indicator F) m := (integrable_indicator_iff hVm).2 hF
  have hf₂m : AEStronglyMeasurable f₂ (m.prod μ) :=
    (hFV.aestronglyMeasurable.comp_fst).indicator hQo.measurableSet
  have inner : ∀ w, ∫ y, f₂ (w, y) ∂μ = (openOff A L S').indicator F w := by
    intro w
    rw [slice w, integral_indicator_const _ (hCm _), Measure.real, hμC, ENNReal.toReal_one, one_smul]
  have innerN : ∀ w, ∫ y, ‖f₂ (w, y)‖ ∂μ = ‖(openOff A L S').indicator F w‖ := by
    intro w
    have : (fun y => ‖f₂ (w, y)‖) =
        {y : Gv A v | (proj D.sp.cm.sig A.gram v w)⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v}.indicator
          (fun _ => ‖(openOff A L S').indicator F w‖) := by
      rw [show (fun y => ‖f₂ (w, y)‖) = fun y => ‖(fun y => f₂ (w, y)) y‖ from rfl, slice w]
      funext y
      exact norm_indicator_eq_indicator_norm _ y
    rw [this, integral_indicator_const _ (hCm _), Measure.real, hμC, ENNReal.toReal_one, one_smul]
  have hf₂ : Integrable f₂ (m.prod μ) := by
    refine (integrable_prod_iff hf₂m).2 ⟨Filter.Eventually.of_forall fun w => ?_, ?_⟩
    · rw [slice w]
      refine (integrable_indicator_iff (hCm _)).2 ?_
      haveI : IsFiniteMeasure (μ.restrict
          {y : Gv A v | (proj D.sp.cm.sig A.gram v w)⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v}) :=
        isFiniteMeasure_restrict.2 (by rw [hμC]; exact ENNReal.one_ne_top)
      exact integrable_const _
    · simp_rw [innerN]
      exact hFV.norm
  have hf₁ : Integrable (f₂ ∘ T) (m.prod μ) := (hT.integrable_comp hf₂m).2 hf₂
  have hI : ∫ p, f₂ (T p) ∂(m.prod μ) = ∫ p, f₂ p ∂(m.prod μ) := by
    rw [← integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hf₂m), hT.map_eq]
  have hT1 : ∀ x y, f₂ (T (x, y)) = (openOff A L Sf).indicator (fun x => F (emb D.sp.cm.sig A.gram v y * x)) x := by
    intro x y
    have hp : (proj D.sp.cm.sig A.gram v (emb D.sp.cm.sig A.gram v y * x))⁻¹ * y =
        (proj D.sp.cm.sig A.gram v x)⁻¹ := by
      rw [map_mul, proj_emb_self, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    have hmem : T (x, y) ∈ Q ↔ proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram L v := by
      show (proj D.sp.cm.sig A.gram v (emb D.sp.cm.sig A.gram v y * x))⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v ↔ _
      rw [hp, inv_mem_iff]
    by_cases h2 : proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram L v
    · rw [show f₂ (T (x, y)) = (openOff A L S').indicator F (emb D.sp.cm.sig A.gram v y * x) from
        Set.indicator_of_mem (hmem.2 h2) _]
      by_cases h1 : x ∈ openOff A L S'
      · rw [Set.indicator_of_mem ((memV y x).2 h1), Set.indicator_of_mem ((memU x).2 ⟨h1, h2⟩)]
      · rw [Set.indicator_of_notMem (mt (memV y x).1 h1), Set.indicator_of_notMem (fun h => h1 ((memU x).1 h).1)]
    · rw [show f₂ (T (x, y)) = 0 from Set.indicator_of_notMem (mt hmem.1 h2) _,
        Set.indicator_of_notMem (fun h => h2 ((memU x).1 h).2)]
  calc ∫ g in openOff A L S', F g ∂m = ∫ w, (openOff A L S').indicator F w ∂m := (integral_indicator hVm).symm
    _ = ∫ p, f₂ p ∂(m.prod μ) := by rw [integral_prod f₂ hf₂]; simp_rw [inner]
    _ = ∫ p, f₂ (T p) ∂(m.prod μ) := hI.symm
    _ = ∫ x, ∫ y, f₂ (T (x, y)) ∂μ ∂m := integral_prod (f₂ ∘ T) hf₁
    _ = ∫ x, (openOff A L Sf).indicator (fun x => ∫ y, F (emb D.sp.cm.sig A.gram v y * x) ∂μ) x ∂m := by
      congr 1; funext x
      simp_rw [hT1]
      by_cases h : x ∈ openOff A L Sf <;> simp [h]
    _ = ∫ x in openOff A L Sf, ∫ y, F (emb D.sp.cm.sig A.gram v y * x) ∂μ ∂m := integral_indicator hUm

end GlobalTheory.Core.Rk.HaarStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPointOfGenericCorankOne
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna
  Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One

namespace GlobalTheory.Core.One.NormalsProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.NGCut.NormalVectorPairings Formalism.L2.SG.Pf.MainEqNml

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

def IsGenericCorankOneTerm (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS) (t : TauC Y u u) : Prop :=
  t ∈ (Y.tO u u).genSet ∧ (Y.tO u u).vec t ≠ 0 ∧ cls1 Y u t = c ∧ ptPN t = γ

theorem occurs_iff_generic_corank_one (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
    (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :
    PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν ↔ ∃ t, IsGenericCorankOneTerm Y u c γ t ∧ nmlOf Y u u t = ν := by
  constructor
  · rintro ⟨t, h1, h2, h3, h4, h5⟩
    rw [genT_ngSet] at h1
    exact ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
  · rintro ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
    refine ⟨t, ?_, h2, h3, h4, h5⟩
    rw [genT_ngSet]
    exact h1

variable {Y u}

theorem related_of_generic_corank_one (hE : CorankOneIsEquivalenceOnRow) (hT : ConcTie X Y) {c : Set (TauC Y u u)} {γ : PN.Pts D.host.E D.R.rS}
    {t0 t : TauC Y u u} (h0 : IsGenericCorankOneTerm Y u c γ t0) (h : IsGenericCorankOneTerm Y u c γ t) : RelC Y u u t0 t := by
  have hrefl : (Y.tO u u).s0 t t = 1 := (hE D X Y u u hT).1 t h.1.1
  have ht : t ∈ cls1 Y u t := ⟨h.1, rfl, hrefl⟩
  rw [h.2.2.1, ← h0.2.2.1] at ht
  exact ⟨ht.2.1, ht.2.2⟩

theorem isPoint_of_generic_corank_one {νL νB : X.B.I.Ginf → Measure X.B.I.Ginf} {ng : PN.Pts D.host.E D.R.rS → ℝ}
    {c : Set (TauC Y u u)} {γ : PN.Pts D.host.E D.R.rS} {t : TauC Y u u} (h : IsGenericCorankOneTerm Y u c γ t) :
    PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ :=
  ⟨clsG Y u t, nmlOf Y u u t, (occ_iffG Y u νL νB ng _ γ _).2 ⟨t, ⟨h.1, h.2.1, rfl, h.2.2.2⟩, rfl⟩⟩

end GlobalTheory.Core.One.NormalsProof

namespace GlobalTheory.Core.One.NormalsProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.NGCut.NormalVectorPairings Formalism.L2.SG.Pf.MainEqNml Formalism.L2.SG.NGCut.NormalInvariants

def NmlInvOne : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
        (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS),
        (∃ ν, PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν) →
        1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ →
        ∃ (J J' : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (m m' : D.host.E)
          (κ : NuC D → D.host.E × D.host.E),
          J ≠ 0 ∧ J' ≠ 0 ∧ m ≠ 0 ∧ m' ≠ 0 ∧
          (∀ ν, PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν →
            (κ ν).1 ∈ J ∧ (κ ν).1 * star (κ ν).1 = m ∧ (κ ν).2 ∈ J' ∧ (κ ν).2 * star (κ ν).2 = m') ∧
          (∀ ν₁ ν₂, PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν₁ →
            PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν₂ → κ ν₁ = κ ν₂ → ν₁ = ν₂) ∧
          |((Algebra.norm ℚ m : ℚ) : ℝ)| ≤ ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 *
            ((Tu D u : ℕ) : ℝ) ^ (2 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 2 ∧
          |((Algebra.norm ℚ m' : ℚ) : ℝ)| ≤ ((FractionalIdeal.absNorm J' : ℚ) : ℝ) ^ 2 *
            ((Tu D u : ℕ) : ℝ) ^ (2 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 2

theorem nmlInvOne_of (hE : CorankOneIsEquivalenceOnRow) (hL : NmlLine) (hI : NmlInt) (hS : NmlSep) : NmlInvOne := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a1, b1, H1⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨a2, b2, H2⟩ := hI Cg cb Cw cT CT C0
  obtain ⟨a3, b3, H3⟩ := hS Cg cb Cw cT CT C0
  refine ⟨max a1 (max a2 a3), max b1 (max b2 b3), fun C' Cl hC hCl D large₂ X Y u hctx νL νB ng c γ hocc hNG => ?_⟩
  have hC1 : a1 ≤ C' := le_trans (le_max_left _ _) hC
  have hC2 : a2 ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hC3 : a3 ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hl1 : b1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hl2 : b2 ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hl3 : b3 ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCl
  have hT : ConcTie X Y := hctx.2.2
  obtain ⟨ν0, hν0⟩ := hocc
  obtain ⟨t0, ht0, -⟩ := (occurs_iff_generic_corank_one Y u νL νB ng c γ ν0).1 hν0
  have hG0 : Gt t0 ≠ 0 := ht0.1.1
  obtain ⟨J, J', hJ, hJ', hmem, hb, hb'⟩ := H2 C' Cl hC2 hl2 D large₂ X Y u u hctx γ hNG t0 hG0 ht0.2.2.2
  set pick : NuC D → TauC Y u u := fun ν =>
    if h : ∃ t, IsGenericCorankOneTerm Y u c γ t ∧ nmlOf Y u u t = ν then h.choose else t0 with hpick
  have hpick_spec : ∀ ν, PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν →
      IsGenericCorankOneTerm Y u c γ (pick ν) ∧ nmlOf Y u u (pick ν) = ν := by
    intro ν hν
    have h := (occurs_iff_generic_corank_one Y u νL νB ng c γ ν).1 hν
    simp only [hpick, dif_pos h]
    exact h.choose_spec
  refine ⟨J, J', 1, 1, fun ν => (coefA Y u u t0 (pick ν), coefA' Y u u t0 (pick ν)), hJ, hJ', one_ne_zero,
    one_ne_zero, fun ν hν => ?_, fun ν₁ ν₂ h₁ h₂ hκ => ?_, ?_, ?_⟩
  · obtain ⟨hp, -⟩ := hpick_spec ν hν
    obtain ⟨m1, m2⟩ := hmem _ hp.1.1 hp.2.2.2 (related_of_generic_corank_one hE hT ht0 hp)
    obtain ⟨n1, n2⟩ := H1 C' Cl hC1 hl1 D large₂ X Y u u hctx γ hNG t0 _ hG0 hp.1.1 ht0.2.2.2 hp.2.2.2
      (related_of_generic_corank_one hE hT ht0 hp)
    exact ⟨m1, n1, m2, n2⟩
  · obtain ⟨hp1, he1⟩ := hpick_spec ν₁ h₁
    obtain ⟨hp2, he2⟩ := hpick_spec ν₂ h₂
    have hk1 := congrArg Prod.fst hκ
    have hk2 := congrArg Prod.snd hκ
    simp only at hk1 hk2
    rw [← he1, ← he2]
    exact H3 C' Cl hC3 hl3 D large₂ X Y u u hctx γ hNG t0 _ _ hG0 hp1.1.1 hp2.1.1 ht0.2.2.2 hp1.2.2.2 hp2.2.2.2
      (related_of_generic_corank_one hE hT ht0 hp1) (related_of_generic_corank_one hE hT ht0 hp2) hk1 hk2
  · rw [map_one]
    simpa using hb
  · rw [map_one]
    simpa using hb'

end GlobalTheory.Core.One.NormalsProof

namespace GlobalTheory.Core.One

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.NGCut.NormalVectorPairings Formalism.L2.SG.Pf.MainEqNml Formalism.L2.SG.NGCut.NormalInvariants GlobalTheory.Core.One.NormalsProof

theorem stepNormals1_of : CorankOneIsEquivalenceOnRow → Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine → Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInt →
    Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep → Formalism.L2.SG.NGCut.NormalInvariants.NormCount → StepNormOneG → StepNormals1 := by
  intro hE hL hI hS hB hO
  have hA := nmlInvOne_of hE hL hI hS
  intro Cg cb Cw cT CT C0
  obtain ⟨a₀, b₀, hA2⟩ := hA Cg cb Cw cT CT C0
  obtain ⟨o₀, p₀, hO2⟩ := hO Cg cb Cw cT CT C0
  refine ⟨max a₀ o₀, max b₀ p₀, fun C' Cl h1 h2 D large₂ X Y u hc νL νB ng => ?_⟩
  intro cl γ S hS
  have hrd := rd_one_le D
  have hv : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
  have hstand := hc.2.1
  show (S.card : ℝ) ≤ ((2 * D.host.v) ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
    (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f)) *
    NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6
  have eR : (D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
      (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f)) *
      ((((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ) ^ 6 =
      (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6 := by
    have hR := rd_cancel D
    calc _ = (D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
          (((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) ^ 6) *
          ((((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6) := by
          ring
      _ = _ := by rw [hR, one_mul]
  rw [hv, ngPt_eq, eR]
  have hT1 : (3 : ℝ) ≤ ((Tu D u : ℕ) : ℝ) := by exact_mod_cast hstand.2.2.2.1
  have hT2 : (3 : ℝ) ≤ ((Tu D u : ℕ) : ℝ) := by exact_mod_cast hstand.2.2.2.2.1
  rcases S.eq_empty_or_nonempty with hSe | ⟨ν0, hν0⟩
  · rw [hSe]
    simp only [Finset.card_empty, Nat.cast_zero]
    refine mul_nonneg (pow_nonneg (by nlinarith) _) ?_
    rw [show PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 6 = (PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ^ 3) ^ 2 by ring]
    exact sq_nonneg _
  have hocc : ∃ ν, PN.Occ (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) cl γ ν := ⟨ν0, hS ν0 hν0⟩
  obtain ⟨t0, ht0, -⟩ := (occurs_iff_generic_corank_one Y u νL νB ng cl γ ν0).1 (hS ν0 hν0)
  have hIsPt : PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ := isPoint_of_generic_corank_one ht0
  have hNG0 := (hO2 C' Cl (le_trans (le_max_right _ _) h1) (le_trans (le_max_right _ _) h2) D large₂ X Y u hc
    νL νB ng γ hIsPt).1
  obtain ⟨J, J', m, m', κ, hJ, hJ', hm, hm', hmem, hinj, hN, hN'⟩ :=
    hA2 C' Cl (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h2) D large₂ X Y u hc νL νB ng cl γ hocc hNG0
  have hNG := hNG0
  rw [ngPt_eq] at hNG
  have hP1 : 1 ≤ PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ := by
    have hX : 1 ≤ (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f := one_le_pow₀ (one_le_pow₀ hrd)
    have hpos : 0 < (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f := lt_of_lt_of_le one_pos hX
    rw [inv_mul_eq_div, le_div_iff₀ hpos, one_mul] at hNG
    linarith
  let T1 := S.image (fun ν => (κ ν).1)
  let T2 := S.image (fun ν => (κ ν).2)
  have hcard : S.card ≤ T1.card * T2.card := by
    calc S.card = (S.image κ).card :=
          (Finset.card_image_of_injOn fun a ha b hb h => hinj a b (hS a ha) (hS b hb) h).symm
      _ ≤ (T1 ×ˢ T2).card := Finset.card_le_card (by
          intro p hp
          obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
          exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hν, Finset.mem_image_of_mem _ hν⟩)
      _ = T1.card * T2.card := Finset.card_product _ _
  have hB1 := hB D J m hJ hm T1 (by
    intro x hx
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨(hmem ν (hS ν hν)).1, (hmem ν (hS ν hν)).2.1⟩)
  have hB2 := hB D J' m' hJ' hm' T2 (by
    intro x hx
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨(hmem ν (hS ν hν)).2.2.1, (hmem ν (hS ν hν)).2.2.2⟩)
  have hJp : 0 < ((FractionalIdeal.absNorm J : ℚ) : ℝ) := by
    have h0 : FractionalIdeal.absNorm J ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    have := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J) (Ne.symm h0)
    exact_mod_cast this
  have hJp' : 0 < ((FractionalIdeal.absNorm J' : ℚ) : ℝ) := by
    have h0 : FractionalIdeal.absNorm J' ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    have := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J') (Ne.symm h0)
    exact_mod_cast this
  generalize PG ((Tu D u : ℕ) * (Tu D u : ℕ)) γ = P at hN hN' hP1 ⊢
  generalize ((Tu D u : ℕ) : ℝ) = T at hN hN' hT1 hT2 ⊢
  generalize ((FractionalIdeal.absNorm J : ℚ) : ℝ) = nJ at hB1 hN hJp
  generalize ((FractionalIdeal.absNorm J' : ℚ) : ℝ) = nJ' at hB2 hN' hJp'
  generalize |((Algebra.norm ℚ m : ℚ) : ℝ)| = nm at hB1 hN
  generalize |((Algebra.norm ℚ m' : ℚ) : ℝ)| = nm' at hB2 hN'
  have hc1 : (T1.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2) := by
    have h := hB1.trans (mul_le_mul_of_nonneg_left hN (by positivity))
    have h' : (T1.card : ℝ) * nJ ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2)) * nJ ^ 2 := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_right h' (by positivity)
  have hc2 : (T2.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2) := by
    have h := hB2.trans (mul_le_mul_of_nonneg_left hN' (by positivity))
    have h' : (T2.card : ℝ) * nJ' ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2)) * nJ' ^ 2 := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_right h' (by positivity)
  calc (S.card : ℝ) ≤ (T1.card : ℝ) * T2.card := by exact_mod_cast hcard
    _ ≤ _ := count_bound D.R.f T T P _ _ hT1 hT2 hP1 hc1 hc2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end GlobalTheory.Core.One
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAAScaledEqAtUnitSplitPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.UnitPlaces

variable {D : D7}

theorem pairA_sum {κ : Type} (s : Finset κ) (f : κ → Af D.host.F) :
    pairA D.host.F 0 (∑ i ∈ s, f i) = ∑ i ∈ s, pairA D.host.F 0 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact GlobalTheory.FinPlLoc.pairA_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.FinPlLoc.pairA_add, ih]

theorem latMul_mono (S : HSp D) (𝔞 : Set D.host.E) (L : Lat S) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) :
    latMul S 𝔞 L P ≤ latMul S 𝔞 L P' := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨α, hαi, hα, a, ha, x, hx, rfl⟩
  exact AddSubgroup.subset_closure ⟨α, hαi, fun v hv => hα v fun h' => hv (h v h'), a, ha, x, hx, rfl⟩

theorem latMul_le_of_parts (S : HSp D) (𝔞 : Set D.host.E) (L : Lat S) (M : AddSubgroup (Fin S.rank → AE D))
    {P : Pl D → Prop} (s : Finset (Pl D)) (hs : ∀ w, P w → w ∈ s) (h : ∀ w ∈ s, latMul S 𝔞 L (· = w) ≤ M) :
    latMul S 𝔞 L P ≤ M := by
  classical
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨α, hαi, hα, a, ha, x, hx, rfl⟩
  have hdec : α = ∑ w ∈ s, GlobalTheory.FinPlLoc.ePl D (· = w) * α := by
    refine RestrictedProduct.ext _ _ fun u => ?_
    change evalV D.host.F u α = evalV D.host.F u (∑ w ∈ s, GlobalTheory.FinPlLoc.ePl D (· = w) * α)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul, GlobalTheory.FinPlLoc.evalV_ePl]
    by_cases hu : u ∈ s
    · simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq, if_pos hu]
    · have h0 : evalV D.host.F u α = 0 := hα u fun h' => hu (hs u h')
      simp [h0]
  have hsum : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) =
      ∑ w ∈ s, fun i => pairA D.host.F 0 (GlobalTheory.FinPlLoc.ePl D (· = w) * α) ⊗ₜ[D.host.F] (a * x i) := by
    funext i
    rw [Finset.sum_apply, ← TensorProduct.sum_tmul, ← pairA_sum, ← hdec]
  show _ ∈ M
  rw [hsum]
  refine AddSubgroup.sum_mem _ fun w hw => h w hw (AddSubgroup.subset_closure
    ⟨GlobalTheory.FinPlLoc.ePl D (· = w) * α, fun u => ?_, fun u hu => ?_, a, ha, x, hx, rfl⟩)
  · rw [map_mul]; exact mul_mem (GlobalTheory.FinPlLoc.ePl_int _ u) (hαi u)
  · rw [map_mul, GlobalTheory.FinPlLoc.evalV_ePl, if_neg hu, zero_mul]

theorem latA_eq_latV : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (S : HSp D) (L : Lat S), latA S L P = latV S L P := by
  intro D k _ _ _ _ ι p I P hP S L
  classical
  let s : Finset (Pl D) := (I.map fun i => (p i).v).toFinset
  have hs : ∀ w, P w → w ∈ s := by
    intro w hw
    obtain ⟨i, rfl⟩ := (hP.mem w).1 hw
    exact List.mem_toFinset.2 (List.mem_map.2 ⟨i, hP.all i, rfl⟩)
  have hsi : ∀ w ∈ s, ∃ i, w = (p i).v := by
    intro w hw
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hw)
    exact ⟨i, rfl⟩
  have hsP : ∀ w ∈ s, P w := fun w hw => (hP.mem w).2 (hsi w hw)
  have hloc : ∀ w ∈ s, latA S L (· = w) = latV S L (· = w) := by
    intro w hw
    obtain ⟨i, rfl⟩ := hsi w hw
    exact (hP.unit i).2 S L
  apply le_antisymm
  · refine latMul_le_of_parts S _ L _ s hs fun w hw => ?_
    exact (hloc w hw).le.trans (latMul_mono S {1} L fun u (hu : u = w) => hu ▸ hsP w hw)
  · refine latMul_le_of_parts S _ L _ s hs fun w hw => ?_
    exact (hloc w hw).ge.trans (latMul_mono S {a | a ∈ D.host.AA} L fun u (hu : u = w) => hu ▸ hsP w hw)

end GlobalTheory.FinPl.UnitPlaces

end
end

