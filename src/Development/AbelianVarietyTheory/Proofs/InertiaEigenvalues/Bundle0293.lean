module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0187
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0271
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0272
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExactFunctorPhiGammaOfFrames
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOnGaussNormAcrisRadiusIco
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
open Filter Topology

noncomputable section

namespace GlobalTheory.PMon.Gauss

theorem gC_zero_of_lt_one (l : ℕ) [Fact l.Prime] {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    gC l ρ (0 : Formalism.Per.Acris l) = 0 := by
  unfold gC
  split_ifs with h
  · have hN := Classical.choose_spec h
    set N := Classical.choose h
    have hm := hN.2.2.2.1 ((l : Formalism.Per.Acris l)) 0
    have hl : N (l : Formalism.Per.Acris l) = ρ := by
      have := hN.2.2.2.2 (l : Formalism.Per.Ainf l)
      rw [map_natCast] at this
      rw [this]
      exact GlobalTheory.GaussSlope.gauss_l l h0
    rw [mul_zero, hl] at hm
    have : (1 - ρ) * N 0 = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact h'
  · rfl

theorem continuousOn_gC (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) :
    ContinuousOn (fun ρ => gC l ρ x) (Set.Ico (l : ℝ)⁻¹ 1) := by
  have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := by
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  by_cases hx : x = 0
  · subst hx
    refine (continuousOn_const (c := (0 : ℝ))).congr fun ρ hρ => ?_
    exact gC_zero_of_lt_one l (hl0.le.trans hρ.1) hρ.2
  intro ρ₀ hρ₀
  have hpos : 0 < ρ₀ := hl0.trans_le hρ₀.1
  obtain ⟨⟨c, k, ρ₂, -, h02, -, hR⟩, hL⟩ := _root_.GlobalTheory.PMon.Gauss.gC_monomial_near l x hx ρ₀ hρ₀.1 hρ₀.2
  have hS : Set.Ico (l : ℝ)⁻¹ 1 = (Set.Ico (l : ℝ)⁻¹ 1 ∩ Set.Iic ρ₀) ∪ (Set.Ico (l : ℝ)⁻¹ 1 ∩ Set.Ici ρ₀) := by
    ext y
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici]
    constructor
    · intro hy
      rcases le_total y ρ₀ with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    · rintro (h | h) <;> exact h.1
  rw [ContinuousWithinAt, hS, ← ContinuousWithinAt, continuousWithinAt_union]
  constructor
  · rcases eq_or_lt_of_le hρ₀.1 with heq | hlt
    · refine (continuousWithinAt_singleton (f := fun ρ => gC l ρ x) (x := ρ₀)).mono ?_
      rintro y ⟨hy1, hy2⟩
      exact le_antisymm hy2 (heq ▸ hy1.1)
    · obtain ⟨c', k', ρ₁, -, -, h10, hL'⟩ := hL hlt
      have hg : ContinuousWithinAt (fun ρ : ℝ => c' * ρ ^ k') (Set.Iic ρ₀) ρ₀ :=
        (continuousAt_const.mul (continuousAt_zpow₀ ρ₀ k' (Or.inl hpos.ne'))).continuousWithinAt
      have hg' : ContinuousWithinAt (fun ρ => gC l ρ x) (Set.Icc ρ₁ ρ₀) ρ₀ :=
        (hg.mono Set.Icc_subset_Iic_self).congr (fun y hy => hL' y hy) (hL' ρ₀ ⟨h10.le, le_rfl⟩)
      exact (hg'.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE h10)).mono Set.inter_subset_right
  · have hg : ContinuousWithinAt (fun ρ : ℝ => c * ρ ^ k) (Set.Ici ρ₀) ρ₀ :=
      (continuousAt_const.mul (continuousAt_zpow₀ ρ₀ k (Or.inl hpos.ne'))).continuousWithinAt
    have hg' : ContinuousWithinAt (fun ρ => gC l ρ x) (Set.Icc ρ₀ ρ₂) ρ₀ :=
      (hg.mono Set.Icc_subset_Ici_self).congr (fun y hy => hR y hy) (hR ρ₀ ⟨le_rfl, h02.le⟩)
    exact (hg'.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE h02)).mono Set.inter_subset_right

theorem continuousOn_gC_target :
    ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), ContinuousOn (fun ρ => gC l ρ x) (Set.Ico (l : ℝ)⁻¹ 1) :=
  fun l _ x => continuousOn_gC l x

end GlobalTheory.PMon.Gauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOneTmul
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.WeakClosed

theorem continuous_one_tmul : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ}
    (b : LatB T d), letI := twTop T b; Continuous fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t := by
  intro l _ K LL T d b
  haveI := LL.2
  haveI : Module.Free ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.1
  haveI : Module.Finite ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.2.1
  have hc : ∀ c : ℤ_[l], algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) c) =
      algebraMap ℚ_[l] ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] c) := fun c =>
    (IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL) ↥LL.1 c).symm.trans
      (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1 c)
  letI := zlMod T
  haveI := zlTower T
  letI := twTop T b
  letI tC : TopologicalSpace (Cb l) := cbTop l
  letI tW : TopologicalSpace (WCb l) := wTop l
  have hemb : Topology.IsInducing (algebraMap ℤ_[l] ℚ_[l]) := Topology.IsInducing.subtypeVal
  have hb : ∀ i, Continuous fun t : ↥T.L.T => b.repr t i := by
    intro i
    obtain ⟨φ, hφ⟩ := GlobalTheory.Cyc.exists_form_lat hc T b i
    have h1 : Continuous φ := GlobalTheory.Cyc.continuous_form_of_moduleTopology (L := ↥LL.1) φ
    exact hemb.continuous_iff.2 ((h1.comp continuous_subtype_val).congr hφ)
  have hW : Continuous (algebraMap ℤ_[l] (WCb l)) := GlobalTheory.WeakTop.continuous_padicInt_witt _
  have h1 : ∀ (t : ↥T.L.T) i, GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b
      ((1 : RW LL) ⊗ₜ[↥(OL LL)] t) i = algebraMap ℤ_[l] (WCb l) (b.repr t i) := by
    intro t i
    rw [Algebra.TensorProduct.one_def, GlobalTheory.WeakTop.coords_tmul, one_smul,
      Algebra.algebraMap_eq_smul_one]
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  simp only [Function.comp_apply, h1]
  exact hW.comp (hb i)

end GlobalTheory.WeakClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousZlSmul
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.WeakTop

theorem coords_algebraMap_smul {R O W T ι : Type} [CommRing R] [CommRing O] [Algebra R O]
    [CommRing W] [Algebra R W] [AddCommGroup T] [Module O T] [Module R T] [IsScalarTower R O T]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R T) (c : R) (x : (O ⊗[R] W) ⊗[O] T) (i : ι) :
    coords W O b (algebraMap R O c • x) i = algebraMap R W c * coords W O b x i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add (f := _), Pi.add_apply, hx, hy, mul_add]
  | tmul r t =>
    induction r using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_tmul, smul_add, map_add (f := _), Pi.add_apply, hx, hy, mul_add]
    | tmul a w =>
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', coords_tmul, coords_tmul, smul_eq_mul,
        mul_smul, algebraMap_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_smul,
        Algebra.smul_def]

end GlobalTheory.WeakTop

theorem GlobalTheory.WeakClosed.continuous_zl_smul : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (m : TW (RW LL) T), letI := twTop T b; Continuous fun c : ℤ_[l] => algebraMap ℤ_[l] ↥(OL LL) c • m := by
  intro l _ K LL T d b m
  letI := twTop T b
  letI := zlMod T
  haveI := zlTower T
  letI := cbTop l
  letI := cbValued l
  letI := wTop l
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  have hW : Continuous (algebraMap ℤ_[l] (WCb l)) := GlobalTheory.WeakTop.continuous_padicInt_witt _
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  simp only [Function.comp_apply, GlobalTheory.WeakTop.coords_algebraMap_smul]
  exact hW.mul continuous_const
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordsOneTmulSmul
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.WeakTop

theorem coords_one_tmul_smul {R O W T ι : Type} [CommRing R] [CommRing O] [Algebra R O] [CommRing W] [Algebra R W] [AddCommGroup T] [Module O T] [Module R T] [IsScalarTower R O T] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R T) (w : W) (z : (O ⊗[R] W) ⊗[O] T) (i : ι) :
    GlobalTheory.WeakTop.coords W O b (((1 : O) ⊗ₜ[R] w) • z) i = w * GlobalTheory.WeakTop.coords W O b z i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add (f := _), Pi.add_apply, hx, hy, mul_add]
  | tmul r t =>
    induction r using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [add_tmul, smul_add, map_add (f := _), Pi.add_apply, hx, hy, mul_add]
    | tmul a w' =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        coords_tmul, coords_tmul]
      simp only [Algebra.smul_def]
      ring

end GlobalTheory.WeakTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycEqImage
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

noncomputable section

namespace GlobalTheory.CycImage

theorem cyc_eq_image : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G], PadicCoeff p O → ∀ (φ : ℤ_[p] →+* O) (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ g : G, ((ε g : Oˣ) : O) = φ ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) : ℤ_[p]ˣ) : ℤ_[p]) := by
  intro p _ K O _ _ _ _ G _ _ hO φ i ε hε g
  set c : ℤ_[p] := ((cyclotomicCharacter (PadicAlgCl p) p
    (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) : ℤ_[p]ˣ) : ℤ_[p]) with hcdef
  have key : ∀ n : ℕ, ((ε g : Oˣ) : O) - φ c ∈ Ideal.span {(p : O) ^ n} := by
    intro n
    obtain ⟨ζ, hζ⟩ : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ (p ^ n) :=
      HasEnoughRootsOfUnity.exists_primitiveRoot _ _
    obtain ⟨a, ha, hmem⟩ := hε (i g) n ζ hζ.pow_eq_one
    have hcar : ((carry i ε (i g) : Oˣ) : O) = ((ε g : Oˣ) : O) := by
      simp only [carry, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
      congr 2
      exact i.symm_apply_apply g
    rw [hcar] at hmem
    have hsp := cyclotomicCharacter.spec (L := PadicAlgCl p) p (n := n)
      (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) ζ hζ.pow_eq_one
    have h1 : (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) ζ = (i g) ζ := rfl
    rw [h1, ha] at hsp
    set v : ℕ := (PadicInt.toZModPow n c).val with hv
    have hmod : a ≡ v [MOD p ^ n] := by
      have hne : ζ ≠ 0 := hζ.ne_zero (NeZero.ne _)
      have hz : ζ ^ ((a : ℤ) - (v : ℤ)) = 1 := by
        rw [zpow_sub₀ hne, zpow_natCast, zpow_natCast, hsp, div_self (pow_ne_zero _ hne)]
      have hd := (hζ.zpow_eq_one_iff_dvd _).1 hz
      exact (Nat.modEq_iff_dvd.2 (by
        have : ((p ^ n : ℕ) : ℤ) ∣ -((a : ℤ) - (v : ℤ)) := (dvd_neg).2 (by exact_mod_cast hd)
        simpa using this))
    have hc : c - (v : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, hv,
        ZMod.natCast_zmod_val, sub_self]
    have hφ : φ c - (v : O) ∈ Ideal.span {(p : O) ^ n} := by
      have := Ideal.mem_map_of_mem φ hc
      rw [Ideal.map_span, Set.image_singleton] at this
      simpa using this
    have hav : (a : O) - (v : O) ∈ Ideal.span {(p : O) ^ n} := by
      rw [Ideal.mem_span_singleton]
      have hd : ((p ^ n : ℕ) : ℤ) ∣ (v : ℤ) - (a : ℤ) := (Nat.modEq_iff_dvd.1 hmod)
      obtain ⟨k, hk⟩ := hd
      refine ⟨-(k : O), ?_⟩
      have hk' : ((v : ℤ) : O) - ((a : ℤ) : O) = (((p ^ n : ℕ) : ℤ) : O) * (k : O) := by
        rw [← Int.cast_sub, hk, Int.cast_mul]
      push_cast at hk'
      linear_combination -hk'
    have hsum : ((ε g : Oˣ) : O) - φ c =
        ((((ε g : Oˣ) : O) - a) + ((a : O) - v)) - (φ c - v) := by ring
    rw [hsum]
    exact Ideal.sub_mem _ (Ideal.add_mem _ hmem hav) hφ
  have hbot : ((ε g : Oˣ) : O) - φ c ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal O) ^ n := by
    refine Ideal.mem_iInf.2 fun n => ?_
    have h := key n
    have hle : Ideal.span {(p : O) ^ n} ≤ (IsLocalRing.maximalIdeal O) ^ n := by
      rw [← Ideal.span_singleton_pow]
      exact Ideal.pow_right_mono ((Ideal.span_singleton_le_iff_mem _).2 hO.p_mem) n
    exact hle h
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top, Ideal.mem_bot] at hbot
  exact sub_eq_zero.1 hbot

end GlobalTheory.CycImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicIntegersEqWittZetaSubOne
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS Polynomial
open scoped IntermediateField

namespace GlobalTheory.PrismS.Poly

variable {l : ℕ} [Fact l.Prime]

theorem mem_OL_of_norm_le (K : FinExt l) (y : ↥K.1) (h : ‖(y : Om l)‖ ≤ 1) : y ∈ OL K := by
  have hi : IsIntegral ℚ_[l] (y : Om l) := Algebra.IsIntegral.isIntegral _
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hi)] at h
  have hl : minpoly ℚ_[l] (y : Om l) ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hm⟩ := lifts_and_degree_eq_and_monic hl (minpoly.monic hi)
  have h1 : IsIntegral ℤ_[l] (y : Om l) := ⟨q, hm, by
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩
  exact (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).1 h1

theorem norm_coeff_le (K : FinExt l) (N : ℕ) (π : Om l)
    (hπ : ‖π‖ = (l : ℝ) ^ (-(1 : ℝ) / (N : ℝ))) (p : (↥(K0 K))[X])
    (hd : p.natDegree < N) (h1 : ‖aeval π p‖ ≤ 1) (j : ℕ) :
    ‖((p.coeff j : ↥(K0 K)) : Om l)‖ ≤ 1 := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_le _).trans_lt hd
  have key : ∀ i ∈ p.support, ∃ n : ℤ, ‖((p.coeff i : ↥(K0 K)) : Om l)‖ = (l : ℝ) ^ n ∧
      ‖p.coeff i • π ^ i‖ = (l : ℝ) ^ ((n : ℝ) - (i : ℝ) / N) := by
    intro i hi
    have h0 : ((p.coeff i : ↥(K0 K)) : Om l) ≠ 0 := by
      have := mem_support_iff.1 hi
      exact fun h => this (Subtype.ext h)
    obtain ⟨n, hn⟩ := GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K _ (p.coeff i).2 h0
    refine ⟨n, hn, ?_⟩
    change ‖((p.coeff i : ↥(K0 K)) : Om l) * π ^ i‖ = _
    rw [norm_mul, norm_pow, hn, hπ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le,
      ← Real.rpow_intCast, ← Real.rpow_add hl0]
    congr 1
    ring
  have hpw : Set.Pairwise (p.support : Set ℕ)
      (fun i k => ‖p.coeff i • π ^ i‖₊ ≠ ‖p.coeff k • π ^ k‖₊) := by
    intro i hi k hk hik h
    obtain ⟨n, -, hn⟩ := key i hi
    obtain ⟨m, -, hm⟩ := key k hk
    have h' : ‖p.coeff i • π ^ i‖ = ‖p.coeff k • π ^ k‖ := congrArg NNReal.toReal h
    rw [hn, hm] at h'
    have h2 := (Real.rpow_right_inj hl0 hl1.ne').1 h'
    have h3 : ((n - m) * N : ℝ) = i - k := by
      field_simp at h2
      linarith
    have h4 : ((n - m) * N : ℤ) = i - k := by exact_mod_cast h3
    have hi' : i < N := (le_natDegree_of_mem_supp i hi).trans_lt hd
    have hk' : k < N := (le_natDegree_of_mem_supp k hk).trans_lt hd
    have h5 : (i : ℤ) - k = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd (m := N) ⟨n - m, by rw [← h4]; ring⟩
      rw [abs_lt]; constructor <;> omega
    omega
  by_cases hj : j ∈ p.support
  swap
  · rw [notMem_support_iff.1 hj]; simp
  have hs : ∑ i ∈ p.support, p.coeff i • π ^ i = aeval π p := by
    rw [aeval_eq_sum_range' (Nat.lt_succ_self _)]
    apply Finset.sum_subset supp_subset_range_natDegree_succ
    intro i _ hi
    rw [notMem_support_iff.1 hi, zero_smul]
  have h6 := IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpw
  rw [hs] at h6
  have h7 := Finset.le_sup (f := fun i => ‖p.coeff i • π ^ i‖₊) hj
  rw [← h6] at h7
  obtain ⟨n, hn, hn'⟩ := key _ hj
  have h8 : ‖p.coeff j • π ^ j‖ ≤ ‖aeval π p‖ := h7
  replace h8 := (h8.trans h1).trans (Real.rpow_zero (l : ℝ)).ge
  rw [hn', Real.rpow_le_rpow_left_iff hl1] at h8
  have hj' : (j : ℝ) < N := by exact_mod_cast (le_natDegree_of_mem_supp j hj).trans_lt hd
  have h9 : (j : ℝ) / N < 1 := (div_lt_one hN).2 hj'
  have h10 : n < 1 := by
    have : (n : ℝ) < 1 := by linarith
    exact_mod_cast this
  rw [hn]
  exact zpow_le_one_of_nonpos₀ hl1.le (by omega)

theorem coe_eval₂ (K : FinExt l) (π : Om l) (t : OC l) (ht : (t : ℂ_[l]) = (π : ℂ_[l]))
    (r : (WK K)[X]) : ((r.eval₂ (intToOC (unr K)) t : OC l) : ℂ_[l]) =
      algebraMap (Om l) ℂ_[l] (aeval π (r.map ((OL (unr K)).val.toRingHom : WK K →+* ↥(K0 K)))) := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [eval₂_add, Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), ← hp, ← hq]; rfl
  | monomial n a =>
    rw [eval₂_monomial, Polynomial.map_monomial, aeval_monomial, map_mul, map_pow]
    push_cast
    rw [ht]
    rfl

theorem exists_poly (K : FinExt l) (s : ℕ) (hs : 1 ≤ s) (ζ : Om l) (hζ : IsPrimitiveRoot ζ (l ^ s))
    (x : Om l) (hx : x ∈ Ks K s) :
    ∃ p : (↥(K0 K))[X], p.natDegree < l ^ (s - 1) * (l - 1) ∧ aeval (ζ - 1) p = x := by
  have hlp : l.Prime := Fact.out
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  rw [GlobalTheory.Cyc.Ks_eq_restrictScalars K s ζ hζ] at hx
  have hx' : x ∈ ((↥(K0 K))⟮ζ⟯).toSubalgebra := hx
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hx'
  obtain ⟨q, rfl⟩ := hx'
  refine ⟨taylor 1 (q %ₘ minpoly ↥(K0 K) ζ), ?_, ?_⟩
  · rw [natDegree_taylor, ← Nat.totient_prime_pow hlp hs,
      ← natDegree_cyclotomic (l ^ s) ↥(K0 K), ← GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s hs ζ hζ]
    exact natDegree_modByMonic_lt _ (minpoly.monic hint) (minpoly.ne_one _ _)
  · rw [taylor_apply, aeval_comp]
    simp only [map_add (f := _), aeval_X, aeval_C, map_one, sub_add_cancel]
    exact aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), 1 ≤ s → ∀ ζ : Om l, IsPrimitiveRoot ζ (l ^ s) → ∀ t : OC l, (t : ℂ_[l]) = ((ζ - 1 : Om l) : ℂ_[l]) → (∀ r : Polynomial (WK K), r.natDegree < l ^ (s - 1) * (l - 1) → r.eval₂ (intToOC (unr K)) t = 0 → r = 0) ∧ (K.1 ≤ Ks K s → ∀ x : ↥(OL K), ∃ r : Polynomial (WK K), r.eval₂ (intToOC (unr K)) t = intToOC K x) := by
  intro l _ K s hs ζ hζ t ht
  have hlp : l.Prime := Fact.out
  have hnorm : ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l ^ (s - 1) * (l - 1) : ℕ) : ℝ)) := by
    have h1 := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l s hs (ζ : PadicComplex l)
      (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))
    push_cast [Nat.cast_sub hlp.one_le]
    rw [← h1, ← PadicComplex.norm_extends]
    congr 1
    exact (map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)
  have hinj : Function.Injective ((OL (unr K)).val.toRingHom : WK K →+* ↥(K0 K)) :=
    Subtype.val_injective
  refine ⟨fun r hr h0 => ?_, fun hK x => ?_⟩
  · by_contra hne
    have h1 := coe_eval₂ K (ζ - 1) t ht r
    rw [h0] at h1
    refine GlobalTheory.Cyc.aeval_ne_zero_of_norm_eq K _ (ζ - 1) hnorm _
      ((Polynomial.map_ne_zero_iff hinj).2 hne) (natDegree_map_le.trans_lt hr) ?_
    exact (algebraMap (Om l) ℂ_[l]).injective (h1.symm.trans (map_zero _).symm)
  · obtain ⟨p, hp, hpx⟩ := exists_poly K s hs ζ hζ _ (hK (x : ↥K.1).2)
    have hc := norm_coeff_le K _ _ hnorm p hp (hpx ▸ norm_le_one_of_mem_OL K x)
    have hl : p ∈ Polynomial.lifts ((OL (unr K)).val.toRingHom : WK K →+* ↥(K0 K)) := by
      rw [lifts_iff_coeff_lifts]
      exact fun n => ⟨⟨_, mem_OL_of_norm_le (unr K) _ (hc n)⟩, rfl⟩
    obtain ⟨r, rfl⟩ := (mem_lifts _).1 hl
    refine ⟨r, Subtype.ext ?_⟩
    rw [coe_eval₂ K (ζ - 1) t ht r, hpx]
    rfl

end GlobalTheory.PrismS.Poly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfTensorLatticeSpecialisationStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ainf_tensor_lattice_specialisation : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f n : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (θ : Ainf l →ₐ[ℤ_[l]] OC l), IsMat K LL T M A → IsThetaShift AI n θ → ∃ Φ : TW (RA LL) T →+ (Fin d → PadicComplex l), (∀ (r : RA LL) (z : TW (RA LL) T), Φ (r • z) = (lam o A (thR LL θ r)).mulVec (Φ z)) ∧ (∀ z i, ‖Φ z i‖ ≤ 1) ∧ (∀ (g : ↥(GK K)) (z : TW (RA LL) T), Φ (TWact (gRA AI LL (g : GQ l)) T g z) = (M (g : GQ l)).mulVec (fun i => AI.actC (g : GQ l) (Φ z i))) ∧ ∀ j, ∃ t : ↥T.L.T, Φ ((1 : RA LL) ⊗ₜ[↥(OL LL)] t) = Pi.single j 1 := by
  exact @GlobalTheory.Cyc.Decomp.exists_specPhi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicFrobeniusTwistedValueEqStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomicFrobeniusTwistedValue_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e j n : ℕ), 1 ≤ j → j ≤ s → ¬ l ∣ n → ∀ c : Om l, c ∈ K0 K → ‖c‖ ≤ 1 → ∃ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) ∧ ‖(d : Om l)‖ ≤ 1 ∧ d - (l : ↥(K0 K)) ^ e * frK P K d = (frK P K ^ s) (∑ a ∈ primeTo l s, lam a) ∧ cycVal P K s e lam d = (l : Om l) ^ ((e + 1) * (s - 1)) * (c * P.ζQ j ^ n) := by
  first | exact @GlobalTheory.ExpImage.Values.exists_cycVal_eq | exact GlobalTheory.ExpImage.Values.exists_cycVal_eq | (intros; apply GlobalTheory.ExpImage.Values.exists_cycVal_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExactFunctorPhiGammaOfFramesStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exact_functor_phiGamma_of_frames : ∀ {k G : Type} [Field k] [Group G] {Rk : Type} [CommRing Rk] [Algebra k Rk] {l n : ℕ} [NeZero n] (R : RingPG k l) (κ : k⸨X⸩ →+* Rk) (φ : Rk →ₐ[k] Rk) (a : G → (Rk →ₐ[k] Rk)) (g₀ : G) (ε : ZMod n → Rk) (Obj : Ob k G → Prop) (β : ∀ A : Ob k G, ZMod n → (Vc k A.m →+ Rk ⊗[k] (Fin A.m → k))), IsFrames R κ φ a g₀ ε Obj β → ∃ F : DFun R n G, F.Obj = Obj ∧ (∀ A, Obj A → ∀ i x, β A i ((F.D A).φ i x) = Phi φ A.m (β A (i - 1) x)) ∧ (∀ A, Obj A → ∀ i x, β A i ((F.D A).γ i x) = Act a A g₀ (β A i x)) ∧ (∀ A B f, Obj A → Obj B → IsHom A B f → ∀ i x, β B i (F.map A B f i x) = f.baseChange Rk (β A i x)) ∧ ∀ i, β (chr 1) i (F.unit i) = ε i ⊗ₜ[k] (fun _ => 1) := by
  first | exact @GlobalTheory.RedFun.exists_dfun_of_frames | exact GlobalTheory.RedFun.exists_dfun_of_frames | (intros; apply GlobalTheory.RedFun.exists_dfun_of_frames <;> assumption)
end

