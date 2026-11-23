module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0642
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrivOutsideListProd
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftStandardGroup

open ReciprocityTheory.Aut

def bz (r n p : ℕ) (γ : GL (Fin r) (ZMod p)) : Matrix (Fin n) (Fin n) ℤ := fun a b =>
  if hab : a.val < r ∧ b.val < r then
    ((((γ : Matrix (Fin r) (Fin r) (ZMod p)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val : ℕ) : ℤ)
  else if a = b then 1 else 0

theorem bz_map_zmod (r t p : ℕ) [Fact p.Prime] (γ : GL (Fin r) (ZMod p)) :
    (bz r (r + t) p γ).map (Int.cast : ℤ → ZMod p) = GlobalTheory.SerSys.BlockLift.bm r t γ := by
  ext a b
  rw [GlobalTheory.SerSys.BlockLift.bm_apply]
  simp only [Matrix.map_apply, bz]
  split_ifs <;> simp [ZMod.natCast_zmod_val]

theorem bz_det_ne (r t p : ℕ) [Fact p.Prime] (γ : GL (Fin r) (ZMod p)) :
    (((bz r (r + t) p γ).det : ℤ) : ZMod p) ≠ 0 := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.SerSys.BlockLift.bm_isUnit r t γ)
  intro h0
  have e : (((bz r (r + t) p γ).det : ℤ) : ZMod p) = (GlobalTheory.SerSys.BlockLift.bm r t γ).det := by
    rw [← bz_map_zmod]
    exact RingHom.map_det (Int.castRingHom (ZMod p)) _
  rw [e] at h0
  exact hu.ne_zero h0

section Local

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem val_intCast_le_one (s : SplitPlace L) (m : ℤ) :
    Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L))) ≤ 1 := by
  have h := s.split_le_one (m : 𝓞 L)
  simpa using h

theorem val_intCast_eq_one (s : SplitPlace L) {p : ℕ} [Fact p.Prime]
    (hp : Valued.v ((p : s.v.adicCompletion (maximalRealSubfield L))) < 1) (m : ℤ) (hm : (m : ZMod p) ≠ 0) :
    Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L))) = 1 := by
  set u : ℤ := (((m : ZMod p)⁻¹).val : ℤ) with hu
  have h1 : (((m * u - 1 : ℤ)) : ZMod p) = 0 := by
    rw [hu]
    push_cast
    rw [ZMod.natCast_zmod_val, mul_inv_cancel₀ hm, sub_self]
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h1
  have e : ((m : s.v.adicCompletion (maximalRealSubfield L)) * (u : s.v.adicCompletion (maximalRealSubfield L))) =
      1 + (p : s.v.adicCompletion (maximalRealSubfield L)) * (c : s.v.adicCompletion (maximalRealSubfield L)) := by
    have : (m * u : ℤ) = 1 + (p : ℤ) * c := by linarith
    exact_mod_cast this
  have h2 : Valued.v ((p : s.v.adicCompletion (maximalRealSubfield L)) * (c : s.v.adicCompletion (maximalRealSubfield L))) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le hp (val_intCast_le_one s c)
  have h3 : Valued.v ((m : s.v.adicCompletion (maximalRealSubfield L)) * (u : s.v.adicCompletion (maximalRealSubfield L))) = 1 := by
    rw [e]
    exact Valuation.map_one_add_of_lt _ h2
  apply le_antisymm (val_intCast_le_one s m)
  by_contra hlt
  push_neg at hlt
  have h4 := mul_lt_one_of_lt_of_le hlt (val_intCast_le_one s u)
  rw [← map_mul, h3] at h4
  exact lt_irrefl _ h4

end Local

end GlobalTheory.LiftStandardGroup

end

namespace GlobalTheory.LiftStandardGroup

open ReciprocityTheory.Aut

section Local2

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem loc_eq_one_of_ne {n : ℕ} (s' : SplitPlace L) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (h : s'.v ≠ v)
    {x : Formalism.AUTREP.GAf L n} (hx : TrivOutside {v} x) : s'.loc n x = 1 := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  have hc : compAt L s'.v (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b - (1 : Matrix (Fin n) (Fin n) (AL L)) a b) = 0 := by
    have := congrFun (congrFun (hx s'.v (by simpa using h)) a) b
    rw [Matrix.map_apply] at this
    rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h0 := GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero L s' _ hc
  rw [map_sub, sub_eq_zero] at h0
  show s'.proj (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b) =
    (1 : Matrix (Fin n) (Fin n) (s'.v.adicCompletion (maximalRealSubfield L))) a b
  rw [h0, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem exists_local (s : SplitPlace L) (r t p : ℕ) [Fact p.Prime]
    (hp : Valued.v ((p : s.v.adicCompletion (maximalRealSubfield L))) < 1) (γ : GL (Fin r) (ZMod p)) :
    ∃ x : Formalism.AUTREP.GAf L (r + t), TrivOutside {s.v} x ∧ x ∈ Umax L (r + t) ∧
      GlobalTheory.PendOf.IsLiftAt s r p γ (s.loc (r + t) x) := by
  set M : Matrix (Fin (r + t)) (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)) :=
    (bz r (r + t) p γ).map (Int.cast : ℤ → s.v.adicCompletion (maximalRealSubfield L)) with hM
  have hdetM : M.det = (((bz r (r + t) p γ).det : ℤ) : s.v.adicCompletion (maximalRealSubfield L)) :=
    (RingHom.map_det (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))) _).symm
  have hv : Valued.v M.det = 1 := by
    rw [hdetM]; exact val_intCast_eq_one s hp _ (bz_det_ne r t p γ)
  have hne : M.det ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
  set h : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)) :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero M hne with hh
  have hval : (h : Matrix (Fin (r + t)) (Fin (r + t)) _) = M := rfl
  obtain ⟨x, hx1, hx2⟩ := GlobalTheory.SplitSec.exists_trivOutside_loc L (r + t) s h
  have hint : ∀ a b, Valued.v (M a b) ≤ 1 := fun a b => by
    rw [hM, Matrix.map_apply]; exact val_intCast_le_one s _
  have hinvint : ∀ a b, Valued.v ((M⁻¹ : Matrix (Fin (r + t)) (Fin (r + t)) _) a b) ≤ 1 := by
    intro a b
    have hadj : M.adjugate = ((bz r (r + t) p γ).adjugate).map (Int.cast : ℤ → s.v.adicCompletion (maximalRealSubfield L)) :=
      (RingHom.map_adjugate (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))) _).symm
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, hadj, Matrix.map_apply, smul_eq_mul, map_mul, map_inv₀, hv,
      inv_one, one_mul]
    exact val_intCast_le_one s _
  refine ⟨x, hx1, ?_, ?_⟩
  · refine GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s x hx1 ?_ ?_
    · intro a b; rw [hx2, hval]; exact hint a b
    · intro a b; rw [map_inv, hx2, Matrix.coe_units_inv, hval]; exact hinvint a b
  · intro a b
    rw [hx2, hval, hM]
    by_cases hab : a.val < r ∧ b.val < r
    · rw [dif_pos hab, Matrix.map_apply]
      simp [bz, dif_pos hab]
    · rw [dif_neg hab, Matrix.map_apply]
      simp only [bz, dif_neg hab]
      split_ifs <;> simp

end Local2

end GlobalTheory.LiftStandardGroup

namespace GlobalTheory.LiftStandardGroup

open ReciprocityTheory.Aut

theorem list_prod_map_eq {ι G : Type} [Monoid G] (f : ι → G) (a : ι) :
    ∀ l : List ι, l.Nodup → a ∈ l → (∀ b ∈ l, b ≠ a → f b = 1) → (l.map f).prod = f a := by
  classical
  intro l hnd hm h1
  rw [List.prod_map_eq_pow_single a f (fun b hne hb => h1 b hb hne), hnd.count_of_mem hm, pow_one]

theorem trivOutside_list_prod {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} :
    ∀ l : List (Formalism.AUTREP.GAf L n), (∀ x ∈ l, TrivOutside T x) → TrivOutside T l.prod
  | [], _ => by
    rw [List.prod_nil]
    intro w _
    exact Matrix.map_one _ (map_zero _) (map_one _)
  | x :: l, h => by
    rw [List.prod_cons]
    have hx := h x List.mem_cons_self
    have hl := trivOutside_list_prod l fun y hy => h y (List.mem_cons_of_mem _ hy)
    intro w hw
    have hmul : ((x * l.prod).1 : Matrix (Fin n) (Fin n) (AL L)) =
        (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (l.prod.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
    rw [hmul, Matrix.map_mul, hx w hw, hl w hw, mul_one]

theorem main : ∀ (D : D7) (n : ℕ), D.R.r ≤ n → ∃ Lf : G0g D.nd → Formalism.AUTREP.GAf D.host.E n,
    GlobalTheory.PendOf.IsTypeGroupBlockLift D n Lf ∧ ∀ g, Lf g ∈ ReciprocityTheory.Aut.Umax D.host.E n := by
  intro D n hn
  classical
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  choose s hs using fun kv : (Σ k : Fin 2, D.nd.PlG k) => GlobalTheory.FixedPlaceOverType.exists_splitPlace_w_plGw D kv.1 kv.2
  have hp : ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
      Valued.v (((D.host.g kv.1 : ℕ) : (s kv).v.adicCompletion (maximalRealSubfield D.host.E))) < 1 := by
    intro kv
    have h0 : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := D.naut.plGw_over kv.1 kv.2
    rw [← hs kv] at h0
    have h1 := ((s kv).split_mem_ideal _).1 h0
    simpa using h1
  have hloc : ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (γ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))),
      ∃ x : Formalism.AUTREP.GAf D.host.E (D.R.r + t), TrivOutside {(s kv).v} x ∧ x ∈ Umax D.host.E (D.R.r + t) ∧
        GlobalTheory.PendOf.IsLiftAt (s kv) D.R.r (D.host.g kv.1) γ ((s kv).loc (D.R.r + t) x) := by
    intro kv γ
    haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
    exact exists_local (s kv) D.R.r t (D.host.g kv.1) (hp kv) γ
  choose x hx1 hx2 hx3 using hloc
  have hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv).v) :=
    GlobalTheory.PlaceInj.splitPlace_v_injective D (fun k v => s ⟨k, v⟩) (fun k v => hs ⟨k, v⟩)
  have hgPl : ∀ kv, (s kv).v ∈ GlobalTheory.PendOf.gPl D := by
    intro kv
    refine ⟨kv, ?_⟩
    show _ = _
    rw [← hs kv]
    exact (s kv).w_under
  refine ⟨fun g => ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map (fun kv => x kv (g kv))).prod,
    fun g => ⟨?_, ?_⟩, fun g => ?_⟩
  · apply trivOutside_list_prod
    intro y hy
    obtain ⟨kv, -, rfl⟩ := List.mem_map.1 hy
    intro w hw
    exact hx1 kv (g kv) w (fun e => hw (by rw [Set.mem_singleton_iff.1 e]; exact hgPl kv))
  · intro kv s' hs'
    have e : s' = s kv := GlobalTheory.SplitPlaceExt.eq_of_w_eq D.host.E (s kv) s' (hs'.trans (hs kv).symm)
    subst e
    rw [map_list_prod, List.map_map]
    rw [list_prod_map_eq _ kv _ (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ _))]
    · exact hx3 kv (g kv)
    · intro kv' _ hne
      exact loc_eq_one_of_ne (s kv) (fun e => hne (hinj e.symm)) (hx1 kv' (g kv'))
  · apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨kv, -, rfl⟩ := List.mem_map.1 hy
    exact hx2 kv (g kv)

end GlobalTheory.LiftStandardGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationNullSetsToPointClassNull
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

open scoped Matrix ComplexOrder

namespace GlobalTheory.UnifNull


open Set in
theorem iSup_apply_eq_zero {Z : Type*} [MeasurableSpace Z] {ι : Type*} (μ : ι → Measure Z) {T : Set Z}
    (hT : MeasurableSet T) (h : ∀ i, μ i T = 0) : (⨆ i, μ i) T = 0 := by
  have hle : (⨆ i, μ i) ≤ (⨆ i, μ i).restrict Tᶜ := iSup_le fun i => Measure.le_iff.2 fun B hB => by
    rw [Measure.restrict_apply hB, ← measure_inter_add_diff B hT, diff_eq,
      measure_mono_null inter_subset_right (h i), zero_add]
    exact Measure.le_iff'.1 (le_iSup μ i) _
  refine le_antisymm ((Measure.le_iff'.1 hle T).trans ?_) (zero_le)
  rw [Measure.restrict_apply hT, inter_compl_self, measure_empty]


open Set in
theorem glueNull : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) [SecondCountableTopology (CxPts p σ)] (ρ : AlgChart p σ D → CxPts p σ → ENNReal) (S : Set (CxPts p σ)), (∀ c : AlgChart p σ D, volume (c.e '' (c.e.source ∩ S)) = 0) → glueMeas (fun c : AlgChart p σ D => c.e) ρ S = 0 := by
  intro k _ Y p σ D _ ρ S hS
  classical
  obtain ⟨I, hIc, hI⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun c : AlgChart p σ D => c.e.source) fun c => c.e.open_source
  let Z : AlgChart p σ D → Set (ReciprocityTheory.L2DbarEstimates.V D) := fun c => toMeasurable volume (c.e '' (c.e.source ∩ S))
  have hZ : ∀ c, volume (Z c) = 0 := fun c => (measure_toMeasurable _).trans (hS c)
  have hTm : ∀ c : AlgChart p σ D, MeasurableSet (c.e.source ∩ c.e ⁻¹' Z c) := by
    intro c
    have hm := (c.e.continuousOn.measurable_piecewise (continuousOn_const (c := (0 : ReciprocityTheory.L2DbarEstimates.V D)))
      c.e.open_source.measurableSet) (measurableSet_toMeasurable volume (c.e '' (c.e.source ∩ S)))
    convert c.e.open_source.measurableSet.inter hm using 1
    ext y
    simp only [mem_inter_iff, mem_preimage]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> simpa [Set.piecewise_eq_of_mem _ _ _ h1] using h2
  let T : Set (CxPts p σ) := (⋃ c : AlgChart p σ D, c.e.source)ᶜ ∪ ⋃ c ∈ I, (c.e.source ∩ c.e ⁻¹' Z c)
  have hT : MeasurableSet T :=
    (isOpen_iUnion fun c : AlgChart p σ D => c.e.open_source).measurableSet.compl.union
      (MeasurableSet.biUnion hIc fun c _ => hTm c)
  have hST : S ⊆ T := by
    intro y hy
    by_cases hO : y ∈ ⋃ c : AlgChart p σ D, c.e.source
    · right
      rw [← hI] at hO
      obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.1 hO
      exact mem_biUnion hc ⟨hyc, subset_toMeasurable _ _ ⟨y, ⟨hyc, hy⟩, rfl⟩⟩
    · exact Or.inl hO
  have hc0 : ∀ c : AlgChart p σ D, chartMeas c.e (ρ c) T = 0 := by
    intro c
    rw [chartMeas_apply _ _ hT]
    refine setLIntegral_measure_zero _ _ ?_
    have hsub : c.e '' (c.e.source ∩ T) ⊆ ⋃ c' ∈ I, (c.e ∘ c'.e.symm) ''
        (Z c' ∩ (c'.e.target ∩ c'.e.symm ⁻¹' c.e.source)) := by
      rintro _ ⟨y, ⟨hy, hyT⟩, rfl⟩
      rcases hyT with hyO | hyT
      · exact (hyO (mem_iUnion.2 ⟨c, hy⟩)).elim
      obtain ⟨c', hc', hy1, hy2⟩ := mem_iUnion₂.1 hyT
      refine mem_biUnion hc' ⟨c'.e y, ⟨hy2, c'.e.map_source hy1, ?_⟩, ?_⟩
      · simp only [mem_preimage, c'.e.left_inv hy1]; exact hy
      · simp only [Function.comp_apply, c'.e.left_inv hy1]
    refine measure_mono_null hsub ((measure_biUnion_null_iff hIc).2 fun c' _ => ?_)
    exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (((AlgChart.holo_trans c' c).restrictScalars ℝ).mono inter_subset_right)
      (measure_mono_null inter_subset_left (hZ c'))
  exact measure_mono_null hST (iSup_apply_eq_zero _ hT hc0)


open Set in
theorem volume_null_of_muD {ι : Type} [Fintype ι] {p q : ℕ} {N : Set (ι × Fin p × Fin q → ℂ)}
    (hN : N ⊆ DomFlat ι p q) (h0 : muD ι p q N = 0) : volume N = 0 := by
  have hc : ∀ i : ι, Continuous fun v : ι × Fin p × Fin q → ℂ => (hQ (unflat v i)).det.re := by
    intro i
    refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
    have hu : Continuous fun v : ι × Fin p × Fin q → ℂ => unflat v i :=
      continuous_pi fun a => continuous_pi fun b => continuous_apply (i, a, b)
    unfold hQ
    exact continuous_const.sub (Continuous.matrix_mul (Continuous.matrix_conjTranspose hu) hu)
  have hm : Measurable fun v : ι × Fin p × Fin q → ℂ =>
      ENNReal.ofReal (∏ i, ((hQ (unflat v i)).det.re) ^ (-((p + q : ℕ) : ℤ))) := by
    refine ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ => ?_)
    simp only [zpow_neg, zpow_natCast]
    exact ((hc i).measurable.pow_const _).inv
  have hpos : ∀ v ∈ DomFlat ι p q,
      ENNReal.ofReal (∏ i, ((hQ (unflat v i)).det.re) ^ (-((p + q : ℕ) : ℤ))) ≠ 0 := by
    intro v hv
    refine (ENNReal.ofReal_pos.2 (Finset.prod_pos fun i _ => zpow_pos ?_ _)).ne'
    have h := (hv i : (1 - (unflat v i)ᴴ * unflat v i).PosDef).det_pos
    exact (Complex.pos_iff.1 h).1
  rw [muD, withDensity_apply_eq_zero' hm.aemeasurable,
    Measure.restrict_apply' GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat.measurableSet] at h0
  refine measure_mono_null ?_ h0
  intro v hv
  exact ⟨⟨hpos v (hN hv), hv⟩, hN hv⟩


open Set in
theorem chart_image_null {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {ι : Type} [Fintype ι] (c : AlgChart p σ D) (ψ : (ι → ℂ) → CxPts p σ) {s : Set (ι → ℂ)}
    (hD : D = Fintype.card ι) (hs : volume s = 0)
    (hψ : ∀ a, DifferentiableOn ℂ (ev p σ c.U (c.x a) ∘ ψ) (s ∩ ψ ⁻¹' ptsIn p σ c.U)) :
    volume (c.e '' (c.e.source ∩ ψ '' s)) = 0 := by
  set t := s ∩ ψ ⁻¹' c.e.source with ht
  have e1 : c.e '' (c.e.source ∩ ψ '' s) = (c.e ∘ ψ) '' t := by
    ext y; constructor
    · rintro ⟨_, ⟨h1, w, hw, rfl⟩, rfl⟩; exact ⟨w, ⟨hw, h1⟩, rfl⟩
    · rintro ⟨w, ⟨hw, h1⟩, rfl⟩; exact ⟨ψ w, ⟨h1, w, hw, rfl⟩, rfl⟩
  have hd : DifferentiableOn ℂ (c.e ∘ ψ) t := by
    apply differentiableOn_euclidean.2
    intro a
    have hsub : t ⊆ s ∩ ψ ⁻¹' ptsIn p σ c.U :=
      fun _ hw => ⟨hw.1, c.source_subset hw.2⟩
    exact ((hψ a).mono hsub).congr fun w hw => c.apply_eq _ hw.2 a
  have hfin : Module.finrank ℝ (ι → ℂ) = Module.finrank ℝ (ReciprocityTheory.L2DbarEstimates.V D) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (ι → ℂ), ← Module.finrank_mul_finrank ℝ ℂ (ReciprocityTheory.L2DbarEstimates.V D)]
    simp [hD]
  let L : (ι → ℂ) ≃L[ℝ] ReciprocityTheory.L2DbarEstimates.V D := ContinuousLinearEquiv.ofFinrankEq hfin
  have h1 : volume ((L.symm ∘ (c.e ∘ ψ)) '' t) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (L.symm.differentiable.comp_differentiableOn (hd.restrictScalars ℝ))
      (measure_mono_null inter_subset_left hs)
  have e2 : (c.e ∘ ψ) '' t = L.symm ⁻¹' ((L.symm ∘ (c.e ∘ ψ)) '' t) := by
    rw [← L.image_eq_preimage_symm, image_image]; simp
  haveI : (Measure.map L.symm (volume : Measure (ReciprocityTheory.L2DbarEstimates.V D))).IsAddHaarMeasure :=
    L.symm.isAddHaarMeasure_map volume
  have hac := Measure.absolutelyContinuous_isAddHaarMeasure
    (Measure.map L.symm (volume : Measure (ReciprocityTheory.L2DbarEstimates.V D))) volume
  rw [e1, e2]
  calc volume (L.symm ⁻¹' ((L.symm ∘ (c.e ∘ ψ)) '' t))
      = Measure.map L.symm volume ((L.symm ∘ (c.e ∘ ψ)) '' t) :=
        (L.symm.toHomeomorph.toMeasurableEquiv.map_apply _).symm
    _ = 0 := hac h1

theorem image_null : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ N ⊆ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) N = 0 → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ψ '' N) = 0 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ N hN h0
  have hH := _root_.GlobalTheory.UnifHolo.holo E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hv := volume_null_of_muD hN h0
  have hdim : X.dim = Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) := by
    rw [(GlobalTheory.FlagBaseDim.dims E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL).2]
    have h1 := ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.two_card_Psi (U.X k)
    have h2 : Fintype.card (GlobalTheory.AllWt.Psi H) = Module.finrank ℚ E / 2 := by
      rw [← Nat.card_eq_fintype_card]; exact GlobalTheory.PeriodCoord.card_cmType H
    have h3 : Fintype.card (GlobalTheory.AllWt.Psi H) = Fintype.card (U.X k).Ψ := by omega
    simp only [Fintype.card_prod, Fintype.card_fin, h3, Nat.add_sub_cancel_left]
  unfold chernTopPart
  exact glueNull X.str (σ.comp e.toRingHom) X.dim _ _ fun ch =>
    chart_image_null ch ψ hdim hv fun a => (hH ch.U (ch.x a)).mono fun w hw => ⟨hN hw.1, hw.2⟩

end GlobalTheory.UnifNull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WitnessesPassAlongSetDivision
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr


set_option maxHeartbeats 16000000 in
theorem witMv_of_positionMv : ∀ 𝒮 : Slots, PositionMv 𝒮 → WitMv 𝒮 := by
  intro 𝒮 hS K B f T w Z O x N h hE
  have hR := _root_.GlobalTheory.Mem.Top.Bl.WitTr.isRecG_setDiv K.s (w.D Z) x.col.Gt x.col.cmp x.col.g.herm x.col.g.forms N h x.col.isRec
  let col := columnLocalDataTransportDivision w Z N h x.col hR
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.Mem.Top.Bl.WitTr.kerT_entC_setDiv w Z x.col.toColT O.X O.Gy x.ker0 x.ker N h hE
  let n := nchTTr w Z N h x.n
  obtain ⟨dv⟩ := GlobalTheory.T.divisionLocalData_preserved_divisionLatticeChange w Z x.n O.X N h x.div
  obtain ⟨th⟩ := GlobalTheory.T.thetaAutomorphicWeilData_preserved_divisionLatticeChange w Z x.n O.th N h x.th
  obtain ⟨t, hobj, ⟨rx⟩, ⟨nx⟩, ⟨sx⟩, ⟨ox⟩⟩ := hS K B f T w Z O x N h (O.tr N h) rfl col n
  have hker : (⟨(O.tr N h).gatT, (O.tr N h).cmp, (O.tr N h).tw, (O.tr N h).ker⟩ : Σ (Gt : GatTies (w.D (setDivZ Z N h)))
      (cmp : LatCmp (w.D (setDivZ Z N h))) (tw : TwForms (w.D (setDivZ Z N h))), KerFam (w.D (setDivZ Z N h)) Gt cmp tw (O.tr N h).Gy) =
      ⟨col.Gt, col.cmp, w.tw (setDivZ Z N h), kerTr w Z N h x.ker0⟩ := by
    have e := congrArg (fun s : Σ (Gt : GatTies (w.D Z)) (cmp : LatCmp (w.D Z)) (tw : TwForms (w.D Z)), KerFam (w.D Z) Gt cmp tw O.Gy =>
      (⟨gatTr (D := w.D Z) N h s.1, cmpTr (D := w.D Z) N h s.2.1, twTr (D := w.D Z) N h s.2.2.1,
        fun u v g => { s.2.2.2 u v g with }⟩ : Σ (Gt : GatTies (w.D (setDivZ Z N h))) (cmp : LatCmp (w.D (setDivZ Z N h)))
          (tw : TwForms (w.D (setDivZ Z N h))), KerFam (w.D (setDivZ Z N h)) Gt cmp tw (O.tr N h).Gy)) x.ker_eq
    exact e
  have herr : (O.tr N h).errX = Formalism.L2.Herm.toErrXS col.full.1 := by
    show errTr (D := w.D Z) N h O.errX = _
    rw [x.errX]; rfl
  refine ⟨{
      isOver := x.isOver
      forced := x.forced
      Wt := x.Wt
      pin := x.pin
      coh := x.coh
      vol := x.vol
      col := col
      what₂ := t
      rx := rx
      lev := x.lev
      errX := herr
      n := n
      nx := nx
      sx := sx
      ker0 := kerTr w Z N h x.ker0
      ker_eq := hker
      ker := k
      div := dv
      th := th
      obj := hobj
      ox := ox
      real := { x.real with }
      dsig_eq := x.dsig_eq
      gauge := x.gauge
      good := _root_.GlobalTheory.Mem.Top.Bl.WitTr.goodO_setDiv (w.D Z) O.nch O.xd N h x.good }, hk⟩

end GlobalTheory.Mem.Top.Bl

end
end

