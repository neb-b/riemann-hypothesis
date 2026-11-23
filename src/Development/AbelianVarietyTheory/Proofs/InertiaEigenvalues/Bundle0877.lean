module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActionHermitianInvariantsTransitive
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0864
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageTopOfVanishingBlockAverStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMirabolicWhittakerStage_top_of_vanishing_blockAverages : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (ψ : AddChar (Ad E) ℂ) (f : GA E (m + 1) → ℂ),
    Continuous f → (∀ γ g, f (ratGL E (m + 1) γ * g) = f g) →
    (∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => f (blkU x * g)) = 0) → Good ψ m f := by
  first | (exact @GlobalTheory.CuspGeneric.good_top) | (exact GlobalTheory.CuspGeneric.good_top) | (intros; apply GlobalTheory.CuspGeneric.good_top  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitHeckePrimeOffLevelOfHeckeIndexPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false

namespace GlobalTheory.HeckeIndexPrime

theorem isHeckePrime_of_hkIdx : ∀ (D : D7) (T0 : CoreJ D), LawsJ T0 → ∀ (i : D.ntw.Tw) (k : ℕ) (P : PlE D.host),
    Formalism.MainNotions.IntegralHeckeForms.HkIdx (X := D.ntw) i k P →
    GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime T0.Q.H T0.Q.l P.asIdeal (charAt P) ∧ charAt P ≠ D.ntw.l i := by
  intro D T0 hL i k P hk
  obtain ⟨_, _, hsp, hS⟩ := hk
  refine ⟨⟨P.isMaximal, GlobalTheory.HeckeSup.split_of_ne ((GlobalTheory.HeckeTieCompare.isSplitPl_iff P).1 hsp), charAt_prime P,
    charAt_mem P, GlobalTheory.HeckeSup.not_dvd_level hL (charAt_mem P) (GlobalTheory.HeckeTieCompare.level_notMem ⟨i, hS⟩)⟩, ?_⟩
  intro he
  apply hS
  have hm : P ∈ Formalism.BasicNotions.placesOver D.host.E (D.ntw.l i) := by
    show ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
    rw [← he]
    exact charAt_mem P
  exact D.ntw.twistExcludedPlaces_contains_residueChar i hm

end GlobalTheory.HeckeIndexPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitSubCharValuesOfCyclotomicGenerator
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing

namespace GlobalTheory.CharacterUnits

theorem unit_pow_sub_isUnit {l : ℕ} [Fact l.Prime] (u : ℤ_[l]ˣ)
    (hu : orderOf (PadicInt.toZMod (u : ℤ_[l])) = l - 1)
    (a b : ℕ) (ha : a < l - 1) (hb : b < l - 1) (hab : a ≠ b) :
    IsUnit ((u : ℤ_[l]) ^ a - (u : ℤ_[l]) ^ b) := by
  by_contra h
  have h1 : (u : ℤ_[l]) ^ a - (u : ℤ_[l]) ^ b ∈ IsLocalRing.maximalIdeal ℤ_[l] := h
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow, map_pow, sub_eq_zero] at h1
  exact hab (pow_injOn_Iio_orderOf (by rw [hu]; exact ha) (by rw [hu]; exact hb) h1)

theorem chi_sub_isUnit : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (g0 : G H.E N.Om), orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) = N.l i - 1 → R.t + 1 < N.l i → ∀ a ∈ Finset.Icc 1 R.t, ∀ b ∈ Finset.Icc 1 R.t, a ≠ b → IsUnit (((N.chi i a g0 : (N.O i)ˣ) : N.O i) - ((N.chi i b g0 : (N.O i)ˣ) : N.O i)) := by
  intro R H what₂ N i g0 hε hl a ha b hb hab
  rw [Finset.mem_Icc] at ha hb
  set e : (N.O i)ˣ := Units.map (algebraMap ℤ_[N.l i] (N.O i)).toMonoidHom
    (cycZ (F := H.E) (Ω := N.Om) (N.l i) g0) with he_def
  have h3 : ∀ c, 1 ≤ c → c ≤ R.t → N.chi i c g0 = N.chi i 1 g0 * (e⁻¹ ^ (c - 1)) := by
    intro c h1 h2
    rw [N.chi_def i c h1 h2, MonoidHom.mul_apply]
    congr 1
    have h4 : (-(((c : ℕ) : ℤ) - 1)) = -(((c - 1 : ℕ) : ℤ)) := by omega
    rw [h4, _root_.zpow_neg, zpow_natCast, MonoidHom.inv_apply, MonoidHom.pow_apply, inv_pow]
    rfl
  have hu := (unit_pow_sub_isUnit _ hε (b - 1) (a - 1) (by omega) (by omega)
    (by omega)).map (algebraMap ℤ_[N.l i] (N.O i))
  rw [map_sub, map_pow, map_pow] at hu
  have he : algebraMap ℤ_[N.l i] (N.O i) ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
      ((e : (N.O i)ˣ) : N.O i) := rfl
  rw [he] at hu
  rw [h3 a ha.1 ha.2, h3 b hb.1 hb.2]
  set x := N.chi i 1 g0
  have a1 : ((e⁻¹ : (N.O i)ˣ) : N.O i) ^ (a - 1) * (e : N.O i) ^ (a - 1) = 1 := by rw [← mul_pow]; simp
  have a2 : ((e⁻¹ : (N.O i)ˣ) : N.O i) ^ (b - 1) * (e : N.O i) ^ (b - 1) = 1 := by rw [← mul_pow]; simp
  have key : ((x * e⁻¹ ^ (a - 1) : (N.O i)ˣ) : N.O i) - ((x * e⁻¹ ^ (b - 1) : (N.O i)ˣ) : N.O i) =
      ((x * e⁻¹ ^ (a - 1) * e⁻¹ ^ (b - 1) : (N.O i)ˣ) : N.O i) *
        ((e : N.O i) ^ (b - 1) - (e : N.O i) ^ (a - 1)) := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination (-((x : N.O i) * ((e⁻¹ : (N.O i)ˣ) : N.O i) ^ (a - 1))) * a2 +
      ((x : N.O i) * ((e⁻¹ : (N.O i)ˣ) : N.O i) ^ (b - 1)) * a1
  rw [key]
  exact (Units.isUnit _).mul hu

end GlobalTheory.CharacterUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegralsInvariantLocallyCon
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.OrbLC

theorem eventually_eq_fun {A G β : Type} [TopologicalSpace A] [TopologicalSpace G] (Φ : A → G → β) (a₀ : A)
    (K : Set G) (hK : IsCompact K) (hloc : ∀ g ∈ K, ∀ᶠ z in 𝓝 (a₀, g), Φ z.1 z.2 = Φ a₀ g)
    (hout : ∀ᶠ a in 𝓝 a₀, ∀ g ∉ K, Φ a g = Φ a₀ g) : ∀ᶠ a in 𝓝 a₀, Φ a = Φ a₀ := by
  have h := hK.eventually_forall_of_forall_eventually (x₀ := a₀) (P := fun a g => Φ a g = Φ a₀ g) (by
    intro g hg
    have h1 := hloc g hg
    have hT : Tendsto (fun z : A × G => (a₀, z.2)) (𝓝 (a₀, g)) (𝓝 (a₀, g)) := by
      have : Continuous (fun z : A × G => (a₀, z.2)) := by fun_prop
      simpa using this.tendsto (a₀, g)
    have h2 := hT.eventually h1
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2])
  filter_upwards [h, hout] with a h1 h2
  funext g
  by_cases hg : g ∈ K
  · exact h1 g hg
  · exact h2 g hg

theorem act_mul {r : ℕ} {k : Type} [CommRing k] (g h : GL (Fin r) k) (Y : Gl r k) :
    act (g * h) Y = act g (act h Y) := by
  simp only [act, Units.val_mul, _root_.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem actU_mul {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    (g h : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : actU (g * h) X = actU g (actU h X) := by
  simp only [actU]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · apply Subtype.ext
    simp only [Submonoid.coe_mul, star_mul, Matrix.mul_assoc]
  · simp only [Submonoid.coe_mul, Matrix.mulVec_mulVec]

theorem part1 (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (r : ℕ) (M : Meas r F E) (f' : Gl r F → ℂ) (g : GL (Fin r) F) (Y : Gl r F) :
    orbG M f' (act g Y) = orbG M f' Y := by
  letI := M.mG
  haveI := M.bG
  haveI := GlobalTheory.T.generalLinear_haar_isMulRightInvariant_unramified F E r M
  unfold orbG
  simp only [← act_mul]
  exact integral_mul_right_eq_self (fun h => f' (act h Y) * omega (act h Y)) g

theorem part2 (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (r : ℕ) (M : Meas r F E) (f : Hn r F E → ℂ) (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) :
    orbU M f (actU g X) = orbU M f X := by
  letI := M.mU
  haveI := M.bU
  haveI := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E r).2 M
  unfold orbU
  simp only [← actU_mul]
  exact integral_mul_right_eq_self (fun h => f (actU h X)) g

end GlobalTheory.JR.OrbLC

namespace GlobalTheory.JR.OrbLC

theorem companion_pow_mulVec {r : ℕ} {k : Type} [CommRing k] (p : Fin r → k) :
    ∀ (j : ℕ) (hj : j < r), (companion p) ^ j *ᵥ (fun i : Fin r => if (i : ℕ) = 0 then (1 : k) else 0) =
      Pi.single (⟨j, hj⟩ : Fin r) 1 := by
  intro j
  induction j with
  | zero =>
    intro hj
    funext i
    simp only [pow_zero, Matrix.one_mulVec, Pi.single_apply, Fin.ext_iff]
  | succ j ih =>
    intro hj
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih (by omega)]
    funext i
    rw [Matrix.mulVec_single]
    simp only [companion, Matrix.of_apply, mul_one, Pi.single_apply, Fin.ext_iff]
    have : j + 1 ≠ r := by omega
    simp [this]

theorem Cm_sec {r : ℕ} {k : Type} [CommRing k] (a : Inv r k) : Cm (sec a) = hankel a := by
  ext i j
  simp only [Cm, hankel, mom, Matrix.of_apply]
  rw [pow_add, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have h := companion_pow_mulVec a.1 j j.2
  simp only [sec] at h ⊢
  rw [h, Fin.eta, dotProduct_single, mul_one]

theorem lastDet_act_sec {r : ℕ} {k : Type} [CommRing k] (g : GL (Fin r) k) (a : Inv r k) :
    lastDet (act g (sec a)) = (-1) ^ r * (Delta a * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).det) := by
  rw [(_root_.GlobalTheory.JR.transfer_factor_lemma k r).1, (_root_.GlobalTheory.JR.transfer_factor_lemma k r).2, Matrix.det_mul, Cm_sec]
  rfl

theorem eta_eventually {F : Type} [NormedField F] [IsUltrametricDist F] (x : F) (hx : x ≠ 0) :
    ∀ᶠ y in 𝓝 x, eta y = eta x := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  filter_upwards [Metric.ball_mem_nhds x hpos] with y hy
  have hn : ‖y‖ = ‖x‖ := by
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := y - x) (y := x) hy.ne
    rw [sub_add_cancel] at this
    rw [this, max_eq_right hy.le]
  unfold eta
  rw [hn]

end GlobalTheory.JR.OrbLC

namespace GlobalTheory.JR.OrbLC

theorem part3 (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (r : ℕ) (M : Meas r F E) (f' : Gl r F → ℂ) (hf : IsTest f') (a₀ : Inv r F) (hΔ : Delta a₀ ≠ 0) :
    ∀ᶠ a in 𝓝 a₀, orbG M f' (sec a) = orbG M f' (sec a₀) := by
  haveI : LocallyCompactSpace F := Unram.lcF (E := E)
  haveI : IsUltrametricDist F := Unram.ultraF (E := E)
  obtain ⟨hcont, -, hDc, hprop⟩ := _root_.GlobalTheory.JR.OrbitProper.main F E r
  have hopen : IsOpen {a : Inv r F | Delta a ≠ 0} := isOpen_ne_fun hDc continuous_const
  obtain ⟨Ω, hΩn, hΩsub, hΩc⟩ := local_compact_nhds (hopen.mem_nhds hΔ)
  set K : Set (GL (Fin r) F) :=
    Prod.fst '' {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ tsupport f'} with hKdef
  have hK : IsCompact K := (hprop (tsupport f') Ω hf.2 hΩc (fun a ha => hΩsub ha)).image continuous_fst
  have hzero : ∀ a ∈ Ω, ∀ g ∉ K, f' (act g (sec a)) = 0 := by
    intro a ha g hg
    by_contra h
    exact hg ⟨(g, a), ⟨ha, subset_tsupport _ h⟩, rfl⟩
  set Φ : Inv r F → GL (Fin r) F → ℂ := fun a g => f' (act g (sec a)) * omega (act g (sec a)) with hΦ
  have ha₀ : a₀ ∈ Ω := mem_of_mem_nhds hΩn
  have hc2 : Continuous (fun z : Inv r F × GL (Fin r) F => act z.2 (sec z.1)) :=
    hcont.comp continuous_swap
  have hdet : Continuous (fun z : Inv r F × GL (Fin r) F =>
      (-1 : F) ^ r * (Delta z.1 * ((z.2⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det)) := by
    have h1 : Continuous (fun z : Inv r F × GL (Fin r) F => ((z.2⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) :=
      Units.continuous_val.comp (continuous_inv.comp continuous_snd)
    exact continuous_const.mul ((hDc.comp continuous_fst).mul h1.matrix_det)
  have hloc : ∀ g ∈ K, ∀ᶠ z in 𝓝 (a₀, g), Φ z.1 z.2 = Φ a₀ g := by
    intro g _
    have h1 : ∀ᶠ z in 𝓝 (a₀, g), f' (act z.2 (sec z.1)) = f' (act g (sec a₀)) :=
      (hc2.tendsto (a₀, g)).eventually ((IsLocallyConstant.iff_eventually_eq f').1 hf.1 _)
    have hne : (-1 : F) ^ r * (Delta a₀ * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (mul_ne_zero hΔ ?_)
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (g⁻¹ : GL (Fin r) F))).ne_zero
    have h2 := (hdet.tendsto (a₀, g)).eventually (eta_eventually _ hne)
    filter_upwards [h1, h2] with z hz1 hz2
    simp only [hΦ, omega, lastDet_act_sec]
    rw [hz1]
    rw [hz2]
  have hout : ∀ᶠ a in 𝓝 a₀, ∀ g ∉ K, Φ a g = Φ a₀ g := by
    filter_upwards [hΩn] with a ha g hg
    simp only [hΦ, hzero a ha g hg, hzero a₀ ha₀ g hg, zero_mul]
  filter_upwards [eventually_eq_fun Φ a₀ K hK hloc hout] with a h
  have h' : ∀ g, f' (act g (sec a)) * omega (act g (sec a)) = f' (act g (sec a₀)) * omega (act g (sec a₀)) :=
    fun g => congrFun h g
  simp only [orbG, h']

end GlobalTheory.JR.OrbLC

namespace GlobalTheory.JR.OrbLC

theorem continuous_star_of_unram (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] : Continuous (star : E → E) :=
  (AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := E)) (fun x => Unram.norm_star (F := F) x)).continuous

theorem continuous_actU (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) :
    Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => actU p.1 p.2) := by
  haveI : ContinuousStar E := ⟨continuous_star_of_unram F E⟩
  have hg : Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => (p.1 : Matrix (Fin r) (Fin r) E)) :=
    continuous_subtype_val.comp continuous_fst
  have hA : Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => (p.2.1 : Matrix (Fin r) (Fin r) E)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hb : Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => p.2.2.1) :=
    continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hl : Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => p.2.2.2) :=
    continuous_snd.comp (continuous_snd.comp continuous_snd)
  refine Continuous.prodMk ?_ (Continuous.prodMk (hg.matrix_mulVec hb) hl)
  exact Continuous.subtype_mk ((hg.mul hA).mul hg.star) _

theorem part4 (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (r : ℕ) (M : Meas r F E) (f : Hn r F E → ℂ) (hf : IsTest f) (a₀ : Inv r F) (X₀ : Hn r F E)
    (hΔ : Delta a₀ ≠ 0) (hX₀ : HasInv X₀ a₀) :
    ∀ᶠ a in 𝓝 a₀, (∃ X : Hn r F E, HasInv X a) ∧ ∀ X : Hn r F E, HasInv X a → orbU M f X = orbU M f X₀ := by
  obtain ⟨Ω, s, hΩc, hΩo, ha₀, hs, hsinv, hprop⟩ := (_root_.GlobalTheory.JR.image_openClosed_section F E r a₀ hΔ).2 ⟨X₀, hX₀⟩
  have huniq := (_root_.GlobalTheory.JR.HermInv.herm_invariants F E r).2.2.1
  set K : Set (Matrix.unitaryGroup (Fin r) E) :=
    Prod.fst '' {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ tsupport f} with hKdef
  have hK : IsCompact K := (hprop (tsupport f) hf.2).image continuous_fst
  have hzero : ∀ a ∈ Ω, ∀ g ∉ K, f (actU g (s a)) = 0 := by
    intro a ha g hg
    by_contra h
    exact hg ⟨(g, a), ⟨ha, subset_tsupport _ h⟩, rfl⟩
  set Φ : Inv r F → Matrix.unitaryGroup (Fin r) E → ℂ := fun a g => f (actU g (s a)) with hΦ
  have hloc : ∀ g ∈ K, ∀ᶠ z in 𝓝 (a₀, g), Φ z.1 z.2 = Φ a₀ g := by
    intro g _
    have hsa : ContinuousAt s a₀ := hs.continuousAt (hΩo.mem_nhds ha₀)
    have h1 : ContinuousAt (fun z : Inv r F × Matrix.unitaryGroup (Fin r) E => (z.2, s z.1)) (a₀, g) :=
      continuousAt_snd.prodMk (hsa.comp continuousAt_fst)
    have hT : ContinuousAt (fun z : Inv r F × Matrix.unitaryGroup (Fin r) E => actU z.2 (s z.1)) (a₀, g) :=
      ContinuousAt.comp (g := fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => actU p.1 p.2)
        (f := fun z : Inv r F × Matrix.unitaryGroup (Fin r) E => (z.2, s z.1))
        ((continuous_actU F E r).continuousAt) h1
    exact hT.tendsto.eventually ((IsLocallyConstant.iff_eventually_eq f).1 hf.1 _)
  have hout : ∀ᶠ a in 𝓝 a₀, ∀ g ∉ K, Φ a g = Φ a₀ g := by
    filter_upwards [hΩo.mem_nhds ha₀] with a ha g hg
    simp only [hΦ, hzero a ha g hg, hzero a₀ ha₀ g hg]
  have horb : ∀ a ∈ Ω, ∀ X : Hn r F E, HasInv X a → orbU M f X = orbU M f (s a) := by
    intro a ha X hX
    obtain ⟨g, hg, -⟩ := huniq (s a) X a (hsinv a ha).1 (hsinv a ha).2 hX
    rw [← hg, part2]
  filter_upwards [eventually_eq_fun Φ a₀ K hK hloc hout, hΩo.mem_nhds ha₀] with a h ha
  refine ⟨⟨s a, (hsinv a ha).2⟩, fun X hX => ?_⟩
  have h' : ∀ g, f (actU g (s a)) = f (actU g (s a₀)) := fun g => congrFun h g
  rw [horb a ha X hX, horb a₀ ha₀ X₀ hX₀]
  simp only [orbU, h']

theorem orbital_integrals_invariant_locally_constant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (∀ (f' : Gl r F → ℂ) (g : GL (Fin r) F) (Y : Gl r F), orbG M f' (act g Y) = orbG M f' Y) ∧ (∀ (f : Hn r F E → ℂ) (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E), orbU M f (actU g X) = orbU M f X) ∧ (∀ (f' : Gl r F → ℂ), IsTest f' → ∀ a₀ : Inv r F, Delta a₀ ≠ 0 → ∀ᶠ a in 𝓝 a₀, orbG M f' (sec a) = orbG M f' (sec a₀)) ∧ ∀ (f : Hn r F E → ℂ), IsTest f → ∀ (a₀ : Inv r F) (X₀ : Hn r F E), Delta a₀ ≠ 0 → HasInv X₀ a₀ → ∀ᶠ a in 𝓝 a₀, (∃ X : Hn r F E, HasInv X a) ∧ ∀ X : Hn r F E, HasInv X a → orbU M f X = orbU M f X₀ := by
  intro F E _ _ _ _ _ r M
  exact ⟨part1 F E r M, part2 F E r M, fun f' hf a₀ hΔ => part3 F E r M f' hf a₀ hΔ,
    fun f hf a₀ X₀ hΔ hX₀ => part4 F E r M f hf a₀ X₀ hΔ hX₀⟩

end GlobalTheory.JR.OrbLC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointConditionOfEigenCentralSeries
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.PassOp

open Formalism.MainNotions.N.PlaceLabelTeichmuller

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

theorem prod_plc (a : ∀ i, MonoidAlgebra ℂ (G i)) (L : List ι) (hL : L.Nodup) :
    (L.map fun i => plc i (a i)).prod = tens (fun j => if j ∈ L then a j else 1) := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.not_mem_nil, if_false]
    exact tens_one.symm
  | cons i L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, ih hL.2, plc, tens_mul]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp [hL.1]
    · simp [Function.update_of_ne hj, hj]

end Tensor

local instance factGk (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroGk (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

theorem tw_eta (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut)
    (hAN : ∀ Pa Pa' : List (Part D.naut.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w) → Pa.Perm Pa')
    {a : ℕ} (ha : 1 ≤ a) (π : D.naut.CG a) : D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv = π := by
  have hsing : ∀ (π' : D.naut.CG a) w, isoLoc D.nd D.naut [⟨a, π', 1⟩] w = D.naut.locG π' w := by
    intro π' w
    show D.naut.lpSum (spehLoc D.nd D.naut ⟨a, π', 1⟩ w) (D.naut.lpZero w) = _
    rw [D.naut.lpSum_zero]
    unfold spehLoc
    simp [D.naut.lpSum_zero, D.naut.lpTw_zero]
  have h := hAN [⟨a, D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv, 1⟩] [⟨a, π, 1⟩]
    (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by
      rw [hsing, hsing, D.naut.locG_tw, D.naut.locG_tw]
      exact (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hT _).1)
  rw [List.singleton_perm_singleton] at h
  injection h with _ h2

theorem twistIso_eta (D : D7) (hT : SumRepresentations.At.TieLP D.nd D.naut)
    (hAN : ∀ Pa Pa' : List (Part D.naut.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w) → Pa.Perm Pa')
    (L : List (Part D.naut.CG)) (hL : ∀ p ∈ L, 1 ≤ p.a) :
    twistIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) D.naut.etaTinv = L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    show (⟨p.a, D.naut.tw (D.naut.tw p.π D.naut.etaT) D.naut.etaTinv, p.d⟩ : Part D.naut.CG) ::
      twistIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) D.naut.etaTinv = p :: L
    rw [ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)), tw_eta D hT hAN (hL p List.mem_cons_self)]

theorem goodPar_iff_goodSig (D : D7) (Sig : List (Part D.naut.CG)) (σ' : D.ntypes.Par)
    (h1 : ∀ w, isoLoc D.nd D.naut Sig w = D.ntypes.locPar σ' w) :
    D.ntypes.goodPar σ' ↔ goodSig D.nd D.naut Sig := by
  unfold NTypes.goodPar NTypes.goodTuple goodSig
  simp only [D.ntypes.labPar_def, h1]

end GlobalTheory.PassOp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaBelowDetOne
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_theta_below_det_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (π' : CuspSub E (m + 1)), π'.IsUnitary →
    ∀ φ' ∈ GlobalTheory.JSW.mspanR π', ∀ G ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → ∀ x : ℝ, 1 < x →
      ∫⁻ g in 𝓕 ∩ {g | GlobalTheory.RSnm.detAbs g ≤ 1}, ‖φ' g‖ₑ ^ 2 * (∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0}, ‖G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ.1 j)) g.val)‖ₑ) * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) ∂μ ≠ ⊤ := by
  intro E _ _ _ m π' hπ φ' hφ G hG μ _ 𝓕 h𝓕 x hx
  have hbound := GlobalTheory.ThetaSqLow.exists_bound hπ hφ hG
  obtain ⟨C, hC⟩ := hbound
  have hi : IntegrableOn (fun g : GA E (m + 1) => GlobalTheory.RSnm.detAbs g ^ (x - 1))
      (𝓕 ∩ {g | GlobalTheory.RSnm.detAbs g ≤ 1}) μ :=
    _root_.GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low
      E (m + 1) m.succ_pos μ 𝓕 h𝓕 (x - 1) (by linarith)
  refine ne_top_of_le_ne_top (hi.const_mul C).2.ne (lintegral_mono fun g => ?_)
  have hδ := GlobalTheory.RSnm.detAbs_pos g
  refine (mul_le_mul_left (hC g) _).trans ?_
  rw [mul_comm, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), Real.eNorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) (le_abs_self _))
  beta_reduce
  rw [Real.rpow_sub_one hδ.ne']
  ring
end

