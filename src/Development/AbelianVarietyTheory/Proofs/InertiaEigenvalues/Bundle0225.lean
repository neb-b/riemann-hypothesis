module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerGeneratorMatrixPerturbation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0186
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanCyclotomicTwoCocyclesFiniteExtension
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem span_cocycles_ext {G F E : Type} [Group G] [TopologicalSpace G] [Field F]
    [TopologicalSpace F] [IsTopologicalRing F] [Field E] [Algebra F E] [TopologicalSpace E]
    [FiniteDimensional F E] [IsModuleTopology F E] [IsTopologicalRing E] (χ : G → F)
    (H : ∃ z0 : G × G → F, (Continuous z0 ∧ ∀ g h k,
        χ g * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧
      ∀ z : G × G → F, Continuous z →
        (∀ g h k, χ g * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) →
        ∃ x : F, ∃ f : G → F, Continuous f ∧
          ∀ g h, χ g * f h - f (g * h) + f g = z (g, h) - x * z0 (g, h)) :
    ∃ z0 : G × G → E, (Continuous z0 ∧ ∀ g h k,
        algebraMap F E (χ g) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧
      ∀ z : G × G → E, Continuous z →
        (∀ g h k, algebraMap F E (χ g) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) →
        ∃ x : E, ∃ f : G → E, Continuous f ∧
          ∀ g h, algebraMap F E (χ g) * f h - f (g * h) + f g = z (g, h) - x * z0 (g, h) := by
  obtain ⟨z0, ⟨hc0, hz0⟩, H⟩ := H
  haveI : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
  have hA : Continuous (algebraMap F E) := by
    have : (algebraMap F E : F → E) = fun a => a • (1 : E) := by
      funext a; rw [Algebra.algebraMap_eq_smul_one]
    rw [this]; fun_prop
  refine ⟨fun p => algebraMap F E (z0 p), ⟨hA.comp hc0, fun g h k => ?_⟩, fun z hc hz => ?_⟩
  · have := congrArg (algebraMap F E) (hz0 g h k)
    simpa using this
  · let b := Module.finBasis F E
    have hb : ∀ i, Continuous (b.coord i) := fun i =>
      IsModuleTopology.continuous_of_linearMap (b.coord i)
    have key : ∀ i, ∃ x : F, ∃ f : G → F, Continuous f ∧
        ∀ g h, χ g * f h - f (g * h) + f g = b.coord i (z (g, h)) - x * z0 (g, h) := by
      intro i
      refine H (fun p => b.coord i (z p)) ((hb i).comp hc) (fun g h k => ?_)
      have := congrArg (b.coord i) (hz g h k)
      rw [← Algebra.smul_def, map_sub, map_add (f := _), map_sub, map_smul, map_zero, smul_eq_mul] at this
      exact this
    choose x f hf hxf using key
    refine ⟨∑ i, x i • b i, fun g => ∑ i, f i g • b i, ?_, fun g h => ?_⟩
    · exact continuous_finsetSum _ (fun i _ => (hf i).smul continuous_const)
    · have hs : z (g, h) = ∑ i, b.coord i (z (g, h)) • b i := by
        simp [b.sum_repr]
      rw [hs, ← Algebra.smul_def, mul_comm, ← Algebra.smul_def, Finset.smul_sum, Finset.smul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_smul, smul_smul, ← sub_smul, ← add_smul, ← sub_smul, hxf i g h, mul_comm (x i)]

theorem span_cocycles_cyc_ext : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∃ z0 : ↥(GK K) × ↥(GK K) → ℚ_[l], (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → ℚ_[l], Continuous z → (∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : ℚ_[l], CobL (P.PD K) (z - x • z0)) → ∃ z0 : ↥(GK K) × ↥(GK K) → LL, (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → LL, Continuous z → (∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : LL, CobL (P.PD K) (z - x • z0) := by
  intro l _ P K LL _ _ _ O _ _ hO H
  obtain ⟨-, hfd, hmt, htr, -⟩ := hO
  obtain ⟨z0, hz0, H⟩ := H
  have := span_cocycles_ext (F := ℚ_[l]) (E := LL)
    (fun g : ↥(GK K) => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l])) ⟨z0, hz0, fun z hc hz => by
      obtain ⟨x, f, hf, hd⟩ := H z hc hz
      refine ⟨x, f, hf, fun g h => ?_⟩
      have := congrFun hd (g, h)
      simpa [ReciprocityTheory.Def.d1, Formalism.WeaklyAdmissibleFiltrations.charRep] using this⟩
  have e : ∀ g : ↥(GK K), algebraMap ℚ_[l] LL ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l])
      = ((cycLL (P.PD K) LL g : LLˣ) : LL) := fun g => by simp [cycLL]
  simp only [e] at this
  obtain ⟨w0, hw0, H'⟩ := this
  refine ⟨w0, hw0, fun z hc hz => ?_⟩
  obtain ⟨x, f, hf, hd⟩ := H' z hc hz
  refine ⟨x, f, hf, ?_⟩
  funext ⟨g, h⟩
  simpa [ReciprocityTheory.Def.d1, Formalism.WeaklyAdmissibleFiltrations.charRep] using hd g h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateInvariantsCyclotomicTwist
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.CyclotomicTowerSubgroupInclusions

variable {l : ℕ} [Fact l.Prime]

theorem unramified_subfield_le_Ks (K : FinExt l) (j : ℕ) : K0 K ≤ Ks K j := le_sup_left

theorem Ks_le_Kinf (K : FinExt l) (j : ℕ) : Ks K j ≤ Kinf K :=
  sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ (fun _ hx => Exists.intro j hx)) _

theorem cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified (K : FinExt l) (j : ℕ) : Gj K j ≤ (K0 K).fixingSubgroup :=
  fun _ hg x => hg ⟨x.1, unramified_subfield_le_Ks K j x.2⟩

theorem Hinf_le_Gj (K : FinExt l) (j : ℕ) : Hinf K ≤ Gj K j :=
  fun _ hg x => hg ⟨x.1, Ks_le_Kinf K j x.2⟩

theorem mem_inC_iff (F : IntermediateField ℚ_[l] (Om l)) (y : PadicComplex l) :
    y ∈ inC F ↔ y ∈ F.toSubfield.map (algebraMap (Om l) (PadicComplex l)) := Iff.rfl

theorem algebraMap_mem_inC (F : IntermediateField ℚ_[l] (Om l)) (u : ℚ_[l]) :
    algebraMap ℚ_[l] (PadicComplex l) u ∈ inC F :=
  ⟨algebraMap ℚ_[l] (Om l) u, F.algebraMap_mem u, rfl⟩

theorem act_fix {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {g : GQ l} (hg : g ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ inC F) : act g y = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  have := hg ⟨x, hx⟩
  change g x = x at this
  simp only [ha.1, this]

theorem exists_scale (y : PadicComplex l) : ∃ n : ℕ, ‖(l : PadicComplex l) ^ n * y‖ ≤ 1 := by
  have hl : ‖(l : PadicComplex l)‖ < 1 := by
    have h1 : ‖algebraMap ℚ_[l] (PadicComplex l) (l : ℚ_[l])‖ = ‖(l : ℚ_[l])‖ := norm_algebraMap' _ _
    rw [map_natCast] at h1
    rw [h1]
    exact Padic.norm_p_lt_one
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const ‖y‖
  rw [zero_mul] at h
  obtain ⟨n, hn⟩ := (h.eventually (ge_mem_nhds (zero_lt_one' ℝ))).exists
  exact ⟨n, by rwa [norm_mul, norm_pow]⟩

theorem invariants_twist : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ Gj K j, chiC χ i g * act g y = y) → (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC (Ks K j)) := by
  intro l _ act χ ha hχ K j hj i y hy
  obtain ⟨hnorm, -, hker⟩ := _root_.GlobalTheory.Cyc.cyc_basic l χ hχ
  obtain ⟨⟨g, hg⟩, -⟩ := _root_.GlobalTheory.Cyc.gen_dense l act χ ha hχ K j hj
  obtain ⟨hdec, hdir, -, hmul, hact, -⟩ := _root_.GlobalTheory.TateDecomp.tate_decomposition l act χ ha hχ K j hj.1
  obtain ⟨n, hn⟩ := exists_scale y
  have hl0 : (l : PadicComplex l) ^ n ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  set z := (l : PadicComplex l) ^ n * y with hz
  have hzinv : ∀ σ ∈ Gj K j, chiC χ i σ * act σ z = z := by
    intro σ hσ
    rw [hz, map_mul, map_pow, map_natCast, mul_left_comm, hy σ hσ]
  have hzO : z ∈ Ohat K := by
    refine (_root_.GlobalTheory.CycInvariants.fixed_iff_mem_Ohat l act ha K z hn).mp fun h hh => ?_
    have h1 : χ h = 1 := (hker K h (cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified K j (Hinf_le_Gj K j hh))).2.mp hh
    have h2 := hzinv h (Hinf_le_Gj K j hh)
    simpa [chiC, h1] using h2
  obtain ⟨a, haK, x, hx, hax⟩ := hdec z hzO
  set c := chiC χ i g with hc
  have hcK : c ∈ inC (Ks K j) := algebraMap_mem_inC _ _
  have hc1 : ‖c‖ = 1 := by
    rw [hc, chiC, norm_algebraMap', Units.val_zpow_eq_zpow_val, norm_zpow, hnorm, one_zpow]
  have hga : act g a = a := act_fix ha hg.1 haK.1
  have heq : c * (a + act g x) = a + x := by
    have := hzinv g hg.1
    rwa [hax, map_add, hga] at this
  have hX : x - c * act g x ∈ Xj K j :=
    (Xj K j).sub_mem hx (hmul c ⟨hcK, hc1.le⟩ _ (hact g (cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified K j hg.1) x hx))
  have hK : (c - 1) * a ∈ inC (Ks K j) := by
    rw [mem_inC_iff]
    exact Subfield.mul_mem _ (Subfield.sub_mem _ hcK (Subfield.one_mem _)) haK.1
  have h0 : (c - 1) * a = 0 := hdir _ hK _ hX 0 (by linear_combination heq)
  have hrho : 0 < rho1 l :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos) _
  have hx0 : x = 0 := by
    have h := (_root_.GlobalTheory.CycPerturb.perturbation l act χ ha hχ K j hj g hg 1 (fun _ => 1) (by
      intro a b
      rw [Subsingleton.elim a b, Matrix.one_apply_eq]
      refine ⟨?_, by simp⟩
      rw [mem_inC_iff]
      exact Subfield.one_mem _) (by intro a b; simpa using hrho) i).1 (fun _ => x) (fun _ => hx) (by
      funext b
      simp only [twAct, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
      linear_combination heq - h0)
    exact congrFun h 0
  rw [hx0, add_zero] at hax
  refine ⟨fun hi => ?_, fun _ => ?_⟩
  · have hv := _root_.GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one l j hj (χ g : ℚ_[l]) hg.2 i hi
    have hne : c - 1 ≠ 0 := by
      intro h
      have h2 : c - 1 = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ i - 1) := by
        rw [hc, chiC, Units.val_zpow_eq_zpow_val, map_sub, map_one]
      rw [h2, map_eq_zero] at h
      rw [h, norm_zero] at hv
      exact (zpow_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos : (0 : ℝ) < l) _).ne hv
    have ha0 : a = 0 := (mul_eq_zero.mp h0).resolve_left hne
    rw [ha0, hz] at hax
    exact (mul_eq_zero.mp hax).resolve_left hl0
  · have : y = ((l : PadicComplex l) ^ n)⁻¹ * a := by
      rw [← hax, hz, inv_mul_cancel_left₀ hl0]
    rw [this, mem_inC_iff]
    exact Subfield.mul_mem _ (Subfield.inv_mem _ (Subfield.pow_mem _ (natCast_mem _ l) n)) haK.1

end GlobalTheory.CyclotomicTowerSubgroupInclusions
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUnitTeichmullerPrincipalUnitSplit
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LogU.TeichSplit

variable {l : ℕ} [Fact l.Prime]

def nrm (y : Per.Fl l) : ℝ := ‖((y.untilt : Per.OC l) : ℂ_[l])‖

lemma nrm_mul (y z : Per.Fl l) : nrm (y * z) = nrm y * nrm z := by
  simp only [nrm, map_mul]
  push_cast
  exact norm_mul _ _

lemma nrm_one : nrm (1 : Per.Fl l) = 1 := by
  simp [nrm]

lemma nrm_pow (y : Per.Fl l) (n : ℕ) : nrm (y ^ n) = nrm y ^ n := by
  simp only [nrm, map_pow]
  push_cast
  exact norm_pow _ _

lemma nrm_nonneg (y : Per.Fl l) : 0 ≤ nrm y := norm_nonneg _

lemma nrm_le_one (y : Per.Fl l) : nrm y ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 (y.untilt).2

lemma nrm_add (y z : Per.Fl l) : nrm (y + z) ≤ max (nrm y) (nrm z) :=
  (GlobalTheory.TiltAbs.untilt_ultrametric_definite l y z).1

lemma eq_zero_of_nrm (y : Per.Fl l) (h : nrm y = 0) : y = 0 := by
  refine (GlobalTheory.TiltAbs.untilt_ultrametric_definite l y y).2 ?_
  have : ((y.untilt : Per.OC l) : ℂ_[l]) = 0 := norm_eq_zero.1 h
  exact Subtype.ext this

lemma nrm_neg_one : nrm (-1 : Per.Fl l) = 1 := by
  have h : nrm (-1 : Per.Fl l) ^ 2 = 1 := by
    rw [← nrm_pow]; simp [nrm_one]
  exact (pow_eq_one_iff_of_nonneg (nrm_nonneg _) (by norm_num)).1 h

lemma nrm_neg (y : Per.Fl l) : nrm (-y) = nrm y := by
  rw [neg_eq_neg_one_mul, nrm_mul, nrm_neg_one, one_mul]

lemma nrm_sub_tri (a b c : Per.Fl l) : nrm (a - c) ≤ max (nrm (a - b)) (nrm (b - c)) := by
  have : a - c = (a - b) + (b - c) := by ring
  rw [this]; exact nrm_add _ _

lemma norm_l_pos : 0 < ‖((l : ℕ) : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero

lemma nrm_sub_le (y z : Per.Fl l) :
    nrm (y - z) ≤ max ‖((y.untilt : Per.OC l) : ℂ_[l]) - ((z.untilt : Per.OC l) : ℂ_[l])‖
      ‖((l : ℕ) : ℂ_[l])‖ := by
  obtain ⟨t, ht⟩ := GlobalTheory.TiltAbs.untilt_add (y - z) z
  rw [sub_add_cancel] at ht
  have h : (((y - z).untilt : Per.OC l) : ℂ_[l]) =
      (((y.untilt : Per.OC l) : ℂ_[l]) - ((z.untilt : Per.OC l) : ℂ_[l])) +
        (-((l : ℕ) : ℂ_[l]) * ((t : Per.OC l) : ℂ_[l])) := by
    rw [ht]; push_cast; ring
  unfold nrm
  rw [h]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max le_rfl ?_)
  rw [norm_mul, norm_neg]
  exact mul_le_of_le_one_right (norm_nonneg _) (GlobalTheory.TiltAbs.norm_le_one t)

private lemma exists_pow_between_pt {r s c : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hs : s ≤ 1) (hc0 : 0 < c)
    (hc1 : c < 1) : ∃ n k : ℕ, r ^ n < c ^ k ∧ c ^ k < s ^ n := by
  have hs0 : 0 < s := lt_of_le_of_lt hr hrs
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc0 ((div_lt_one hs0).2 hrs)
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one (pow_pos hs0 n) (pow_le_one₀ hs0.le hs) hc0 hc1
  refine ⟨n, k + 1, ?_, hk1⟩
  rw [div_pow, div_lt_iff₀ (pow_pos hs0 n)] at hn
  calc r ^ n < c * s ^ n := hn
    _ ≤ c * c ^ k := mul_le_mul_of_nonneg_left hk2 hc0.le
    _ = c ^ (k + 1) := by ring

private lemma norm_map_mono_pt (f : Per.OC l →+* Per.OC l) (a b : Per.OC l)
    (h : ‖(a : ℂ_[l])‖ ≤ ‖(b : ℂ_[l])‖) : ‖((f a : Per.OC l) : ℂ_[l])‖ ≤ ‖((f b : Per.OC l) : ℂ_[l])‖ := by
  have hd : ∃ t : Per.OC l, a = b * t := by
    by_cases hb : (b : ℂ_[l]) = 0
    · rw [hb, norm_zero] at h
      have ha : (a : ℂ_[l]) = 0 := norm_le_zero_iff.1 h
      exact ⟨0, by rw [mul_zero]; exact Subtype.ext ha⟩
    · refine ⟨⟨(a : ℂ_[l]) / (b : ℂ_[l]), (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
      · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
      · push_cast
        rw [mul_div_cancel₀ _ hb]
  obtain ⟨t, rfl⟩ := hd
  rw [map_mul]
  push_cast
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (GlobalTheory.TiltAbs.norm_le_one _)

private lemma norm_map_pt (f : Per.OC l →+* Per.OC l) (y : Per.OC l) :
    ‖((f y : Per.OC l) : ℂ_[l])‖ = ‖(y : ℂ_[l])‖ := by
  have hlt := GlobalTheory.TiltAbs.norm_l_lt (l := l)
  have e (z : Per.OC l) (n : ℕ) : ‖((z ^ n : Per.OC l) : ℂ_[l])‖ = ‖(z : ℂ_[l])‖ ^ n := by
    push_cast; exact norm_pow _ _
  have el : ‖((((l : ℕ) : Per.OC l)) : ℂ_[l])‖ = ‖((l : ℕ) : ℂ_[l])‖ := by
    push_cast; rfl
  rcases lt_trichotomy ‖((f y : Per.OC l) : ℂ_[l])‖ ‖(y : ℂ_[l])‖ with h | h | h
  · obtain ⟨n, k, h1, h2⟩ := exists_pow_between_pt (norm_nonneg _) h (GlobalTheory.TiltAbs.norm_le_one y)
      (norm_l_pos (l := l)) hlt
    have h3 := norm_map_mono_pt f (((l : ℕ) : Per.OC l) ^ k) (y ^ n) (by rw [e, e, el]; exact h2.le)
    rw [map_pow, map_pow, map_natCast, e, e, el] at h3
    exact absurd h1 (not_lt.2 h3)
  · exact h
  · obtain ⟨n, k, h1, h2⟩ := exists_pow_between_pt (norm_nonneg _) h (GlobalTheory.TiltAbs.norm_le_one (f y))
      (norm_l_pos (l := l)) hlt
    have h3 := norm_map_mono_pt f (y ^ n) (((l : ℕ) : Per.OC l) ^ k) (by rw [e, e, el]; exact h1.le)
    rw [map_pow, map_pow, map_natCast, e, e, el] at h3
    exact absurd h2 (not_lt.2 h3)

lemma nrm_σF (g : Per.Gq l) (y : Per.Fl l) : nrm (Per.σF g y) = nrm y := by
  unfold nrm
  rw [GlobalTheory.RingBasics.untilt_σF]
  exact norm_map_pt (Per.σO g) _

end GlobalTheory.LogU.TeichSplit

namespace GlobalTheory.LogU.TeichSplit
variable {l : ℕ} [Fact l.Prime]

lemma nrm_eq_one_of_isUnit {x : Per.Fl l} (hx : IsUnit x) : nrm x = 1 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h := congrArg nrm hy
  rw [nrm_mul, nrm_one] at h
  nlinarith [nrm_le_one x, nrm_le_one y, nrm_nonneg x, nrm_nonneg y]

lemma eq_zero_of_pow_eq_self {d : Per.Fl l} {q : ℕ} (hq : 2 ≤ q) (hd : d ^ q = d) (h : nrm d < 1) :
    d = 0 := by
  refine eq_zero_of_nrm d ?_
  have h1 : nrm d ^ q = nrm d := by rw [← nrm_pow, hd]
  by_contra hne
  have hpos : 0 < nrm d := lt_of_le_of_ne (nrm_nonneg d) (Ne.symm hne)
  have h2 : nrm d ^ (q - 1) = 1 := by
    have : nrm d ^ (q - 1) * nrm d = 1 * nrm d := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), h1, one_mul]
    exact mul_right_cancel₀ hpos.ne' this
  have := (pow_eq_one_iff_of_nonneg (nrm_nonneg d) (by omega)).1 h2
  linarith

lemma inJ_of_nrm {y : Per.Fl l} (h : nrm (y - 1) ≤ ‖((l : ℕ) : ℂ_[l])‖) : InJ (Per.tm y - 1) := by
  obtain ⟨t, ht⟩ := GlobalTheory.TiltAbs.untilt_add (y - 1) 1
  rw [sub_add_cancel, map_one] at ht
  have hmem : (y - 1).untilt ∈ (Ideal.span {((l : ℕ) : Per.OC l)}) ^ 1 := by
    rw [GlobalTheory.RingBasics.mem_span_pow_OC, pow_one]; exact h
  rw [pow_one, Ideal.mem_span_singleton'] at hmem
  obtain ⟨s, hs⟩ := hmem
  refine ⟨s + t, ?_⟩
  rw [map_sub, map_one, WittVector.fontaineTheta_teichmuller, ht, ← hs]
  ring

end GlobalTheory.LogU.TeichSplit


open GlobalTheory.LogU.TeichSplit in
theorem GlobalTheory.LogU.teich_split : ∀ (l : ℕ) [Fact l.Prime] (x : Per.Fl l), IsUnit x → ∃ (ω x₁ : Per.Fl l) (N : ℕ), x = ω * x₁ ∧ GlobalTheory.LogU.InJ (Per.tm (x₁ ^ (l ^ N)) - 1) ∧ ∀ (g : Per.Gq l) (e : Per.Fl l), e.untilt = 1 → Per.σF g x = x * e → Per.σF g ω = ω := by
  intro l _ x hx
  have hl : l.Prime := Fact.out
  have hlt := GlobalTheory.TiltAbs.norm_l_lt (l := l)
  have hN1 : nrm x = 1 := nrm_eq_one_of_isUnit hx

  obtain ⟨α, hα⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt
    (((x.untilt : Per.OC l) : ℂ_[l])) one_pos
  rw [dist_eq_norm] at hα
  have hαn : ‖α‖ = 1 := by
    rw [← PadicComplex.norm_extends]
    have hx1 : ‖((x.untilt : Per.OC l) : ℂ_[l])‖ = 1 := hN1
    have a1 : ‖((α : PadicAlgCl l) : ℂ_[l])‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (((x.untilt : Per.OC l) : ℂ_[l]))
        (((α : PadicAlgCl l) : ℂ_[l]) - ((x.untilt : Per.OC l) : ℂ_[l]))
      rw [add_sub_cancel, norm_sub_rev] at this
      exact this.trans (max_le hx1.le hα.le)
    have a2 := IsUltrametricDist.norm_add_le_max (((α : PadicAlgCl l) : ℂ_[l]))
        (((x.untilt : Per.OC l) : ℂ_[l]) - ((α : PadicAlgCl l) : ℂ_[l]))
    rw [add_sub_cancel, hx1] at a2
    refine le_antisymm a1 ?_
    rcases le_max_iff.1 a2 with h | h
    · exact h
    · exact absurd h (not_le.2 hα)
  obtain ⟨ζ, m, hm, hζ, hαζ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_teichmuller_bar α hαn
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
  obtain ⟨ω, hωm, hωζ⟩ := GlobalTheory.MemLoc.exists_tilt_root_of_unity l ζ m hm0 hm hζ

  have hxω : nrm (x - ω) < 1 := by
    refine lt_of_le_of_lt (nrm_sub_le x ω) (max_lt ?_ hlt)
    rw [hωζ]
    have e1 : ((x.untilt : Per.OC l) : ℂ_[l]) - ((ζ : Om l) : ℂ_[l]) =
        (((x.untilt : Per.OC l) : ℂ_[l]) - ((α : PadicAlgCl l) : ℂ_[l])) +
          (((α - ζ : PadicAlgCl l)) : ℂ_[l]) := by
      rw [UniformSpace.Completion.coe_sub]; ring
    rw [e1]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hα ?_)
    rw [PadicComplex.norm_extends]; exact hαζ
  set x₁ := x * ω ^ (m - 1) with hx₁
  have hωω : ω * ω ^ (m - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hm0, hωm]
  have hx1 : nrm (x₁ - 1) < 1 := by
    have : x₁ - 1 = ω ^ (m - 1) * (x - ω) := by
      rw [hx₁, ← hωω]; ring
    rw [this, nrm_mul]
    calc nrm (ω ^ (m - 1)) * nrm (x - ω) ≤ 1 * nrm (x - ω) :=
          mul_le_mul_of_nonneg_right (nrm_le_one _) (nrm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hxω

  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (norm_l_pos (l := l)) hx1
  refine ⟨ω, x₁, k, ?_, ?_, ?_⟩
  · rw [hx₁, ← mul_assoc, mul_comm ω x, mul_assoc, hωω, mul_one]
  · refine inJ_of_nrm ?_
    have e2 : x₁ ^ l ^ k - 1 = (x₁ - 1) ^ l ^ k := by
      rw [sub_pow_char_pow, one_pow]
    rw [e2, nrm_pow]
    refine le_trans (pow_le_pow_of_le_one (nrm_nonneg _) (nrm_le_one _)
      (Nat.lt_pow_self hl.one_lt).le) hk.le
  · intro g e he hgx
    have f0 : 0 < Nat.totient m := Nat.totient_pos.2 hm0
    have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hm
    have hmod : l ^ Nat.totient m ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop
    have hq1 : 1 ≤ l ^ Nat.totient m := Nat.one_le_pow _ _ hl.pos
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hq1).1 hmod.symm
    have hωq : ω ^ l ^ Nat.totient m = ω := by
      rw [← Nat.sub_add_cancel hq1, pow_succ, hc, pow_mul, hωm, one_pow, one_mul]
    have hq2 : 2 ≤ l ^ Nat.totient m :=
      le_trans hl.two_le (Nat.le_self_pow f0.ne' l)
    rw [← sub_eq_zero]
    refine eq_zero_of_pow_eq_self hq2 ?_ ?_
    · rw [sub_pow_char_pow, ← map_pow, hωq]
    · have he1 : nrm (e - 1) < 1 := by
        refine lt_of_le_of_lt (nrm_sub_le e 1) (max_lt ?_ hlt)
        rw [he, map_one, sub_self, norm_zero]; exact zero_lt_one
      have h1 : nrm (Per.σF g ω - Per.σF g x) < 1 := by
        rw [← map_sub, nrm_σF, ← neg_sub, nrm_neg]; exact hxω
      have h2 : nrm (Per.σF g x - x) < 1 := by
        have : Per.σF g x - x = x * (e - 1) := by rw [hgx]; ring
        rw [this, nrm_mul, hN1, one_mul]; exact he1
      refine lt_of_le_of_lt (nrm_sub_tri _ (Per.σF g x) _) (max_lt h1 ?_)
      exact lt_of_le_of_lt (nrm_sub_tri _ x _) (max_lt h2 hxω)
end
end

