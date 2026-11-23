module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0083

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LvTwDivDvSplit
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LocValSplit
open GlobalTheory.LFun (LvTw_eq eulerFac_eq_prod etaU locL etaFam_of_unram eulerFac_singleton mem_aboveF)

theorem LvTw_div_dv_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (v : HeightOneSpectrum (𝓞 F)) (w w' : HeightOneSpectrum (𝓞 E)) (r b : ℕ) (s : ℂ), IsSplit (E := E) v → Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v → w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') → Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal → Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal → B w' = (B w).map (·⁻¹) → m w * m w' = 1 → LvTw B m v (s + 1 / 2) / dv E r b v s = eulerFac ((B w).map ((m w)⁻¹ * ·)) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) * eulerFac ((B w).map fun β => ((m w)⁻¹ * β)⁻¹) (GlobalTheory.LFun.npow w (-(s + 1 / 2))) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i))) := by
  intro F E _ _ _ _ _ B m v w w' r b s hsplit hunr hne hv hqw hqw' hB' hm1
  classical
  set X : ℂ := GlobalTheory.LFun.npow w (-(s + 1 / 2)) with hXdef
  set μ : ℂ := (m w : ℂ) with hμ
  have hX' : GlobalTheory.LFun.npow w' (-(s + 1 / 2)) = X := by rw [hXdef, GlobalTheory.LFun.npow, GlobalTheory.LFun.npow, hqw, hqw']
  have hinv : ((m w' : ℂ))⁻¹ = μ := inv_eq_of_mul_eq_one_left (by rw [hμ, ← Units.val_mul, hm1, Units.val_one])
  have e : Formalism.L2.Host.aboveF (L := E) F v = {w, w'} := by ext u; simp [mem_aboveF, hv]
  have hL : LvTw B m v (s + 1 / 2) = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod *
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [LvTw_eq, e, Finset.prod_pair hne, hB', Multiset.map_map, hX', hinv]
    simp only [Function.comp_def, Units.val_inv_eq_inv_val]
    rfl
  have hr1 : eulerFac ((B w).map ((m w)⁻¹ * ·)) X = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_mul, Units.val_inv_eq_inv_val, hμ]
    ring
  have hr2 : eulerFac ((B w).map fun β => ((m w)⁻¹ * β)⁻¹) X =
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_inv_eq_inv_val, Units.val_mul, mul_inv, inv_inv, hμ]
    ring
  have hd : dv E r b v s = (∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ (-(2 * s + r - i))))⁻¹ := by
    rw [← Finset.prod_inv_distrib, dv]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hu : etaU E v = 1 := by unfold etaU; rw [if_pos hsplit]
    rw [locL, etaFam_of_unram hunr, hu, one_pow, eulerFac_singleton, Units.val_one, one_mul, GlobalTheory.LFun.npow, qV, hqw]
  rw [hd, div_inv_eq_mul, hL, hr1, hr2]

end GlobalTheory.LocValSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrdLEqNegLog
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.AbsInert

theorem ordL_eq_neg_log {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {y : L}
    (hy : Valued.v y ≠ (0 : WithZero (Multiplicative ℤ))) : ordL y = -WithZero.log (Valued.v y) := by
  unfold ordL
  rw [dite_eq_right hy, WithZero.toAdd_unzero_eq_log]

theorem absEv_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ x : (Fv F v ⊗[F] E)ˣ, (absEv F E v x : ℝ) = (qV F v : ℝ) ^ (-(2 * ordL (toCompl h x.1))) := by
  intro F E _ _ _ _ _ σ hσ v w h hw x

  set N : Fv F v := Algebra.norm (Fv F v) x.1 with hNdef
  set z : w.adicCompletion E := toCompl h x.1 with hzdef
  have hN0 : N ≠ 0 := ((x.isUnit.map (Algebra.norm (Fv F v))).ne_zero)
  have hz0 : z ≠ 0 := (x.isUnit.map (toCompl h)).ne_zero

  have key := GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := Fv F v) x.1
  have key' := congrArg (toCompl h) key
  rw [map_mul] at key'
  have hl : toCompl h (algebraMap (Fv F v) (Fv F v ⊗[F] E) N) = GlobalTheory.LFun.complMap h N := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [hl] at key'

  let c : w.adicCompletion E →+* w.adicCompletion E :=
    (GlobalTheory.LFun.InertChart.complEquiv hw h).toRingHom.comp
      (((sigR (Fv F v) σ : Fv F v ⊗[F] E →+* Fv F v ⊗[F] E)).comp (GlobalTheory.LFun.InertChart.complEquiv hw h).symm.toRingHom)
  have he : ∀ t, GlobalTheory.LFun.InertChart.complEquiv hw h t = toCompl h t := fun _ => rfl
  have hs : (GlobalTheory.LFun.InertChart.complEquiv hw h).symm z = x.1 := by
    rw [RingEquiv.symm_apply_eq, he]
  have hcz : c z = toCompl h (sigR (Fv F v) σ x.1) := by
    show GlobalTheory.LFun.InertChart.complEquiv hw h (sigR (Fv F v) σ ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z)) = _
    rw [hs, he]
  have hc : GlobalTheory.LFun.IsConjAt σ h c := by
    unfold GlobalTheory.LFun.IsConjAt
    intro t
    show GlobalTheory.LFun.InertChart.complEquiv hw h (sigR (Fv F v) σ ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm (toCompl h t))) = _
    rw [← he t, RingEquiv.symm_apply_apply, he]

  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv hσ hw hc
  have hvc : Valued.v (toCompl h (sigR (Fv F v) σ x.1)) = Valued.v z := by
    rw [← hcz]
    exact hU.2.1 z

  have he1 : w.asIdeal.ramificationIdx (𝓞 F) = 1 :=
    GlobalTheory.LFun.isUnram_iff.mp (GlobalTheory.LFun.isUnram_of_isInertAt hw) w h
  have hvN : Valued.v N = Valued.v z ^ 2 := by
    have hv := GlobalTheory.LFun.valued_complMap h hN0
    rw [he1, pow_one, key', map_mul, hvc] at hv
    rw [sq]
    exact hv.symm
  have hz' : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz0
  have hN' : Valued.v N ≠ 0 := (Valuation.ne_zero_iff _).mpr hN0

  rw [GlobalTheory.Doubling.absEv_apply, coe_nnnorm]
  show ‖N‖ = _
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hN',
    hvN, WithZero.log_pow, ordL_eq_neg_log (y := toCompl h x.1) hz']
  have hq : ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ) = (qV F v : ℝ) := by simp [qV]
  rw [NNReal.coe_zpow, hq]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.AbsInert

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
open GlobalTheory.SWC

noncomputable section

namespace GlobalTheory.HermSD

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

theorem eq_of_test_haar {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] {κ P : Measure V} {χ : V → V → ℂ}
    (hκ : SelfDual κ χ) (hP : P.IsAddHaarMeasure) (Φ : V → ℂ) (hc : Continuous Φ)
    (hs : HasCompactSupport Φ) (hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂P) P) (z : V)
    (h1 : ∫ y, (∫ x, Φ x * χ x y ∂P) * χ y z ∂P = Φ (-z)) (hz : Φ (-z) ≠ 0) : κ = P := by
  have := hκ.1
  have e : κ = Measure.addHaarScalarFactor κ P • P := Measure.isAddLeftInvariant_eq_smul κ P
  set c : NNReal := Measure.addHaarScalarFactor κ P with hcdef
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂κ = (c : ℂ) * ∫ x, Φ x * χ x y ∂P := by
    intro y
    rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hI' : Integrable (fun y => ∫ x, Φ x * χ x y ∂κ) κ := by
    simp only [hT]
    rw [e]
    exact (hI.const_mul (c : ℂ)).smul_measure_nnreal
  have h2 := hκ.2 Φ hc hs hI' z
  simp only [hT] at h2
  rw [e, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at h2
  have h3 : ∫ y, ((c : ℂ) * ∫ x, Φ x * χ x y ∂P) * χ y z ∂P =
      (c : ℂ) * ∫ y, (∫ x, Φ x * χ x y ∂P) * χ y z ∂P := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y => by ring)
  rw [h3, h1, ← mul_assoc] at h2
  have h4 : ((c : ℂ)) * (c : ℂ) = 1 := mul_right_cancel₀ hz (by rw [h2, one_mul])
  have h5 : c * c = 1 := by exact_mod_cast h4
  have h6 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast h5
    have h7 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
    exact_mod_cast h7
  rw [e, h6, one_smul]

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

end GlobalTheory.HermSD

namespace GlobalTheory.HermSD

end GlobalTheory.HermSD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupConjugateTransposeMatrix
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GramFrame

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem integral_adelic_lattice_mul_mem {z w : GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E))
    (hw : w ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E)) :
    z * w ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) := by
  exact GlobalTheory.AdelicLatticeClosure.adelic_hat_one_mul_mem hz hw

theorem one_int_af : ∀ v : HeightOneSpectrum (𝓞 F),
    (1 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := fun v => by
  show (1 : v.adicCompletion F) ∈ _
  exact one_mem _

theorem mem_integral_adelic_lattice_iff (z : GlobalTheory.AdLat.RA F E) :
    z ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) ↔
      GlobalTheory.LevSplit.swp F E z ∈ Formalism.L2.Herm.intAf F E := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      obtain ⟨x', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      rw [GlobalTheory.LevSplit.swp_tmul]
      have e : (algebraMap (𝓞 E) E x') ⊗ₜ[F] a =
          ((algebraMap (𝓞 E) E x') ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * ((1 : E) ⊗ₜ[F] a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [e]
      refine mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, x', rfl⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
    | zero => rw [map_zero]; exact zero_mem _
    | add u u' _ _ hu hu' => rw [map_add]; exact add_mem hu hu'
    | neg u _ hu => rw [map_neg]; exact neg_mem hu
  · intro hz
    have key : ∀ s ∈ Formalism.L2.Herm.intAf F E, ∃ t ∈ GlobalTheory.AdLat.hat1 F
        ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E), GlobalTheory.LevSplit.swp F E t = s := by
      intro s hs
      induction hs using Subring.closure_induction with
      | mem s hs =>
        rcases hs with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
        · exact ⟨(1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (algebraMap (𝓞 E) E c),
            AddSubgroup.subset_closure ⟨1, one_int_af, _, (FractionalIdeal.mem_one_iff _).2 ⟨c, rfl⟩, rfl⟩, rfl⟩
        · exact ⟨b ⊗ₜ[F] (1 : E), AddSubgroup.subset_closure ⟨b, hb, 1,
            (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, rfl⟩, rfl⟩
      | zero => exact ⟨0, zero_mem _, map_zero _⟩
      | one => exact ⟨1, AddSubgroup.subset_closure ⟨1, one_int_af, 1,
            (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, rfl⟩, map_one _⟩
      | add a b _ _ ha hb =>
        obtain ⟨t, ht, rfl⟩ := ha
        obtain ⟨t', ht', rfl⟩ := hb
        exact ⟨t + t', add_mem ht ht', map_add _ _ _⟩
      | neg a _ ha =>
        obtain ⟨t, ht, rfl⟩ := ha
        exact ⟨-t, neg_mem ht, map_neg _ _⟩
      | mul a b _ _ ha hb =>
        obtain ⟨t, ht, rfl⟩ := ha
        obtain ⟨t', ht', rfl⟩ := hb
        exact ⟨t * t', integral_adelic_lattice_mul_mem ht ht', map_mul _ _ _⟩
    obtain ⟨t, ht, e⟩ := key _ hz
    rwa [GlobalTheory.LevSplit.swp_bij.1 e] at ht

end Gen
end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

def conjEquiv (I : AutInst) : Gal(I.E/I.F) :=
  AlgEquiv.ofAlgHom I.cm.sig I.cm.sig
    (AlgHom.ext fun x => by show star (star x) = x; exact star_star x)
    (AlgHom.ext fun x => by show star (star x) = x; exact star_star x)

theorem conjEquiv_apply (I : AutInst) (x : I.E) : conjEquiv I x = I.cm.sig x := rfl

theorem hatL_selfDual (I : AutInst) : GlobalTheory.ParahoricLift.HatSelfDual I.cm.sig I.J I.L := by
  have hJ : ∀ a b, I.cm.sig (I.J b a) = I.J a b := fun a b => by
    have := congrFun (congrFun I.J_herm a) b
    exact (by simpa [Formalism.UG.cT] using this : starRingEnd I.E (I.J b a) = I.J a b)
  refine GlobalTheory.ParahoricLift.hatL_selfDual_gen (conjEquiv I) I.cm.sig (fun _ => rfl) I.J I.L I.L_fg I.L_span
    (fun x => by show star (star x) = x; exact star_star x) (fun a b => ?_) (by rw [Matrix.det_transpose]; exact I.J_det)
    (fun v => ?_) (fun s hs => Formalism.UG.P.csDual_sig_mem I.cm.sig hs) mem_integral_adelic_lattice_iff
  · simp only [Matrix.transpose_apply, conjEquiv_apply]
    exact hJ a b
  · rw [I.L_dual v]
    refine forall₂_congr fun y _ => ?_
    rw [FractionalIdeal.mem_one_iff]
    have e : (∑ a, ∑ b, v a * I.Jᵀ a b * conjEquiv I (y b)) =
        Formalism.UG.hform (starRingEnd I.E) I.J y v := by
      unfold Formalism.UG.hform
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Matrix.transpose_apply, conjEquiv_apply]
      show _ = star (y a) * _ * _
      have : I.cm.sig (y a) = star (y a) := rfl
      rw [this]; ring
    rw [e]
    rfl

end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

theorem gram_frame_int : ∀ (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), IsFrame β I.L → ∃ G : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E), ((Formalism.UG.bc (Formalism.L2.Herm.intAf I.F I.E).subtype G : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) = Formalism.UG.cT (sigA I) (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) := by
  intro I β hβ
  set σ := sigA I with hσ
  set JA : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :=
    I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) with hJA
  set B : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) := (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) with hB
  set Gm := Formalism.UG.cT σ B * JA * B with hGm
  have hSD := hatL_selfDual I

  have hmem : ∀ a : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F, (∀ i, a i ∈ Formalism.L2.Herm.intAf I.F I.E) →
      B *ᵥ a ∈ Formalism.L2.Herm.hatL (F := I.F) I.L := fun a ha => by
    refine (hβ _).2 fun i => ?_
    rw [Matrix.mulVec_mulVec, hB, Units.inv_mul, Matrix.one_mulVec]
    exact ha i
  have hsingle : ∀ k, ∀ i, (Pi.single k (1 : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) : Fin I.n → _) i ∈
      Formalism.L2.Herm.intAf I.F I.E := fun k i => by
    rw [Pi.single_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _

  have hG : ∀ i j, Gm i j ∈ Formalism.L2.Herm.intAf I.F I.E := fun i j => by
    rw [← Formalism.UG.P.hform_single σ Gm i j, hGm, ← Formalism.UG.P.hform_mulVec]
    exact (hSD _).1 (hmem _ (hsingle j)) _ (hmem _ (hsingle i))

  have hdet : IsUnit Gm.det := by
    have h1 : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 β.isUnit
    have h2 : IsUnit (Formalism.UG.cT σ B).det := by
      rw [Formalism.UG.cT, Matrix.det_transpose, show B.map σ = σ.mapMatrix B from rfl, ← RingHom.map_det]
      exact h1.map σ
    have h3 : IsUnit JA.det := by
      rw [hJA, show I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) = (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)).mapMatrix I.J from rfl, ← RingHom.map_det]
      exact (isUnit_iff_ne_zero.2 I.J_det).map _
    rw [hGm, Matrix.det_mul, Matrix.det_mul]
    exact (h2.mul h3).mul h1
  have hGi : Gm * Gm⁻¹ = 1 := Matrix.mul_nonsing_inv Gm hdet
  have hiG : Gm⁻¹ * Gm = 1 := Matrix.nonsing_inv_mul Gm hdet

  have hG' : ∀ i j, (Gm⁻¹) i j ∈ Formalism.L2.Herm.intAf I.F I.E := fun i j => by
    set c : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F := fun l => (Gm⁻¹) l j with hc
    have hx : B *ᵥ c ∈ Formalism.L2.Herm.hatL (F := I.F) I.L := by
      refine (hSD _).2 fun z hz => ?_
      have hz' := (hβ z).1 hz
      set a := ((β⁻¹ : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) *ᵥ z with ha
      have hza : z = B *ᵥ a := by
        rw [ha, Matrix.mulVec_mulVec, hB, Units.mul_inv, Matrix.one_mulVec]
      rw [hza, Formalism.UG.P.hform_mulVec, ← hGm, Formalism.UG.P.hform_eq_dot]
      have e : Gm *ᵥ c = Pi.single j 1 := by
        funext k
        have := congrFun (congrFun hGi k) j
        rw [Matrix.mul_apply] at this
        simp only [Matrix.mulVec, dotProduct, hc, this, Pi.single_apply, Matrix.one_apply]
      rw [e]
      simp only [dotProduct, Function.comp_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact Formalism.L2.SG.Pf.unitaryCongruence.sigA_mem I (hz' j)
    have := (hβ _).1 hx i
    rwa [Matrix.mulVec_mulVec, hB, Units.inv_mul, Matrix.one_mulVec] at this

  let S := Formalism.L2.Herm.intAf I.F I.E
  have inj : Function.Injective fun M : Matrix (Fin I.n) (Fin I.n) S => M.map S.subtype :=
    Matrix.map_injective S.subtype_injective
  refine ⟨⟨Matrix.of fun i j => ⟨Gm i j, hG i j⟩, Matrix.of fun i j => ⟨(Gm⁻¹) i j, hG' i j⟩, inj ?_, inj ?_⟩, ?_⟩
  · show Matrix.map _ S.subtype = Matrix.map _ S.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hGi
  · show Matrix.map _ S.subtype = Matrix.map _ S.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hiG
  · rfl

end GlobalTheory.GramFrame
end

