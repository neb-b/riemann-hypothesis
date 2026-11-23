module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0577
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0584

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedSemistablePeriodsNullFamily
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem exists_bounded_periods_wseed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∃ (ι : Type) (TB : TopBasis bk.ev bk.J ι) (k : ℕ) (v : ι → Matrix (Fin d) (Fin d) (Ainf l)) (Z : ι → Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), (∀ (n : ℕ) (a b : Fin d), {i | v i a b ∉ (bk.J ^ n).map bk.ev}.Finite) ∧ (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → ∀ i, s.W * (Z i).map j = (v i).map bk.iA) ∧ ∀ a b : Fin d, HasSum (fun i => bk.iA (v i a b * TB.b i)) (bk.iA ((l : Ainf l) ^ k * τ ^ (2 * s.N) * if a = b then 1 else 0)) := by
  intro l _ K bk τ hτ d ρ hρ s
  obtain ⟨ι, ⟨TB⟩⟩ := _root_.GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hρ0 := bk.ρ₀_pos'
  have hρ1 := bk.ρ₀_lt_one'
  have hj0 : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  let j0 : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ :=
    Disc.map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := bk.ev X) (ρ' := bk.ρ₀) bk.ev hj0
  have hj0d : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j0 := isDiscMap_map _ _
  have hΦ0 : ‖toDisc l (bk.ev X) bk.ρ₀ (WittVector.frobenius (bk.ev X))‖ ≤ bk.ρ₀ := by
    rw [frobenius_ev_X_eq]
    refine (norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) l hρ0).trans ?_
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρ1.le) (Fact.out : l.Prime).ne_zero
  let Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀ :=
    Disc.map (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (u' := bk.ev X) (ρ' := bk.ρ₀) WittVector.frobenius hΦ0
  have hΦ : IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ := isDiscMap_map _ _
  obtain ⟨cD, hc1, hc2, hc3, hc4, hc5, -, -, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j0 hj0d
  have hrec := GlobalTheory.T.semistable_disc_coefficient_recurrence l K bk τ hτ d ρ hρ s ι TB j0 hj0d cD hc1 hc2 hc5 hc3 Φ hΦ
  let V : ι → Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀) := fun i => s.W * (s.W'.map (cD i)).map j0
  let Vκ : ι × (Fin d × Fin d) → bk.DA bk.ρ₀ := fun p => V p.1 p.2.1 p.2.2
  let c : ι × (Fin d × Fin d) → ι × (Fin d × Fin d) → Ainf l := fun p q =>
    if p.2 = q.2 then bk.ev (TB.c q.1 (WittVector.frobenius (TB.b p.1))) else 0
  have hcfin : ∀ p (n : ℕ), {q | c p q ∉ (bk.J ^ n).map bk.ev}.Finite := by
    rintro ⟨i, ab⟩ n
    refine ((TB.fin (WittVector.frobenius (TB.b i)) n).image fun i₁ => (i₁, ab)).subset ?_
    rintro ⟨i₁, ab'⟩ hq
    by_cases e : ab = ab'
    · subst e
      refine ⟨i₁, fun hm => hq ?_, rfl⟩
      simp only [c, if_pos rfl]
      exact Ideal.mem_map_of_mem _ hm
    · exact (hq (by simp [c, e])).elim
  have hj0c : Continuous j0 :=
    AddMonoidHomClass.continuous_of_bound j0 1 fun y => (hj0d.norm_le y).trans (one_mul _).ge
  have hV : Filter.Tendsto Vκ Filter.cofinite (nhds 0) := by
    refine tendsto_cofinite_prod_of_finite Vκ fun ab => ?_
    have := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun m _ =>
      (tendsto_const_nhds (x := s.W ab.1 m)).mul ((hj0c.tendsto 0).comp (hc4 (s.W' m ab.2)))
    simpa [Vκ, V, Matrix.mul_apply] using this
  have hrecκ : ∀ q, HasSum (fun p => Φ (Vκ p) * toDisc l (bk.ev X) bk.ρ₀ (c p q))
      (toDisc l (bk.ev X) bk.ρ₀ (bk.ev bk.E) ^ (2 * s.N) * Vκ q) := by
    rintro ⟨i₁, a, b⟩
    have hg : Function.Injective (fun i : ι => (i, (a, b))) := fun x y h => (Prod.mk.inj h).1
    refine (hg.hasSum_iff ?_).1 ?_
    · rintro ⟨i, a', b'⟩ hx
      have hne : (a', b') ≠ (a, b) := fun e => hx ⟨i, by simp [e]⟩
      simp [c, hne]
    · convert hrec i₁ a b using 1
      · funext i
        simp [c, Vκ, V]
  obtain ⟨k, v, hv1, hv2⟩ := GlobalTheory.T.exists_bounded_of_phi_equation_disc l K bk (Ainf l) bk.ev ι TB WittVector.frobenius (frobenius_ev_X_eq bk)
    Φ hΦ _ c hcfin (2 * s.N) Vκ hV hrecκ
  refine ⟨ι, TB, k, fun i => Matrix.of fun a b => v (i, (a, b)),
    fun i => (l : bk.DS bk.ρ₀) ^ k • s.W'.map (cD i), ?_, ?_, ?_⟩
  · intro n a b
    have hg : Function.Injective (fun i : ι => (i, (a, b))) := fun x y h => (Prod.mk.inj h).1
    exact (hv2 n).preimage hg.injOn
  · intro j hj i
    have e := IsDiscMap.unique hj hj0d
    subst e
    ext a b
    show (s.W * ((l : bk.DS bk.ρ₀) ^ k • s.W'.map (cD i)).map j0) a b = bk.iA (v (i, (a, b)))
    rw [hv1]
    simp only [Vκ, V, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow,
      map_natCast, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  · intro a b
    have hs := (hasSum_sum (s := (Finset.univ : Finset (Fin d))) fun m _ =>
      (hc5 (s.W' m b)).mul_left (s.W a m)).mul_left ((l : bk.DA bk.ρ₀) ^ k)
    have hW := congrFun (congrFun s.W_mul a) b
    rw [Matrix.mul_apply] at hW
    rw [hW] at hs
    have hf : (fun i => bk.iA ((Matrix.of fun a b => v (i, (a, b))) a b * TB.b i)) =
        fun i => (l : bk.DA bk.ρ₀) ^ k * ∑ m, s.W a m * (j0 (cD i (s.W' m b)) * toDisc l (bk.ev X) bk.ρ₀ (TB.b i)) := by
      funext i
      rw [map_mul, Matrix.of_apply, hv1]
      simp only [Vκ, V, Matrix.mul_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hval : bk.iA ((l : Ainf l) ^ k * τ ^ (2 * s.N) * if a = b then 1 else 0) =
        (l : bk.DA bk.ρ₀) ^ k * (bk.iA τ ^ (2 * s.N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))) a b := by
      rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [hf, hval]
    exact hs

end GlobalTheory.BKLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactLatticeGL
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele

namespace GlobalTheory.IdeleCovolume


open NumberField.Units NumberField.Units.dirichletUnitTheorem in
theorem exists_bound_log (E : Type) [Field E] [NumberField E] :
    ∃ R : ℝ, ∀ t : InfinitePlace E → ℝ, ∃ (u : (𝓞 E)ˣ) (n : ℤ), ∀ w : InfinitePlace E,
      |t w + Real.log (w (u : E)) + n| ≤ R := by
  first
  | exact @_root_.GlobalTheory.IntegerUnitBound.exists_unit_int_abs_le
  | exact _root_.GlobalTheory.IntegerUnitBound.exists_unit_int_abs_le
  | (apply _root_.GlobalTheory.IntegerUnitBound.exists_unit_int_abs_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegerUnitBound.exists_unit_int_abs_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegerUnitBound.exists_unit_int_abs_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegerUnitBound.exists_unit_int_abs_le ..)

theorem isCompact_units {A : Type} [Monoid A] [TopologicalSpace A] [ContinuousMul A] [T1Space A] {C : Set A}
    (hC : IsCompact C) : IsCompact {x : Aˣ | (x : A) ∈ C ∧ ((x⁻¹ : Aˣ) : A) ∈ C} := by
  have h2 := (Units.isClosedEmbedding_embedProduct (α := A)).isCompact_preimage
    (hC.prod (hC.image MulOpposite.continuous_op))
  convert h2 using 1
  ext g
  constructor
  · rintro ⟨h1, h1'⟩
    exact ⟨h1, _, h1', rfl⟩
  · rintro ⟨h1, m, hm, hm'⟩
    refine ⟨h1, ?_⟩
    have : m = ((g⁻¹ : Aˣ) : A) := MulOpposite.op_injective hm'
    rw [← this]; exact hm

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

abbrev diag : Eˣ →* (Ad E)ˣ := Units.map (algebraMap E (Ad E)).toMonoidHom

def eIdele : (Ad E)ˣ := infId E (expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ))

theorem pInf_eIdele (w : InfinitePlace E) : pInf E (eIdele E : Ad E) w = Complex.exp 1 := by
  have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
  change pInf E (1 - sInf E 1 + sInf E _) w = _
  simp only [map_add (f := _), map_sub, map_one, h, sub_self, zero_add]
  rfl

theorem pFin_eIdele : pFin E (eIdele E : Ad E) = 1 := by
  change (1 : Af E) - 0 + 0 = 1
  simp

theorem isCompact_box (r : ℝ) :
    IsCompact {x : Ad E | (∀ w, ‖pInf E x w‖ ≤ r) ∧ ∀ v, pFin E x v ∈ v.adicCompletionIntegers E} := by
  have h1 : IsCompact (Set.pi Set.univ fun _ : InfinitePlace E => Metric.closedBall (0 : ℂ) r) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have h2 := (h1.image (continuous_infEq E)).prod (GlobalTheory.AdeleCocompact.isCompact_integral E)
  have h3 : IsCompact (X := Ad E) _ := h2
  refine Eq.mpr (congrArg IsCompact (Set.ext fun x => ?_)) h3
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨⟨pInf E x, fun w _ => mem_closedBall_zero_iff.2 (h w), (infEq E).apply_symm_apply _⟩, h'⟩
  · rintro ⟨⟨y, hy, e⟩, h'⟩
    refine ⟨fun w => ?_, h'⟩
    have : pInf E x = y := (infEq E).symm_apply_eq.2 e.symm
    rw [this]
    exact mem_closedBall_zero_iff.1 (hy w trivial)

theorem exists_compact_unit : ∃ K : Set (Ad E)ˣ, IsCompact K ∧ ∀ a ∈ GlobalTheory.Mem.Chr.unitIdl E,
    ∃ (k : Eˣ) (n : ℤ), diag E k * eIdele E ^ n * a ∈ K := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  obtain ⟨R, hR⟩ := exists_bound_log E
  refine ⟨_, isCompact_units (isCompact_box E (Real.exp R)), fun a ha => ?_⟩
  obtain ⟨u, n, hu⟩ := hR fun w => Real.log ‖pInf E (a : Ad E) w‖
  let k : Eˣ := Units.map (algebraMap (𝓞 E) E).toMonoidHom u
  refine ⟨k, n, ?_⟩
  have hk : diag E k ∈ GlobalTheory.Mem.Chr.unitIdl E := fun v => by
    have h1 : ∀ z : (𝓞 E)ˣ, Valued.v (pFin E (diag E (Units.map (algebraMap (𝓞 E) E).toMonoidHom z) : Ad E) v) ≤ 1 :=
      fun z => HeightOneSpectrum.coe_mem_adicCompletionIntegers v (z : 𝓞 E)
    have h2 := h1 u⁻¹
    rw [map_inv, map_inv] at h2
    have e : pFin E (diag E k : Ad E) v * pFin E (((diag E k)⁻¹ : (Ad E)ˣ) : Ad E) v = 1 :=
      congrArg (fun a : Ad E => a.2 v) (diag E k).mul_inv
    have e' := congrArg Valued.v e
    rw [map_mul, map_one] at e'
    exact eq_one_of_one_le_mul_left (h1 u) h2 e'.ge
  have he : eIdele E ∈ GlobalTheory.Mem.Chr.unitIdl E := fun v => by
    change Valued.v (pFin E (eIdele E : Ad E) v) = 1
    rw [pFin_eIdele]
    exact map_one _
  have hmem : diag E k * eIdele E ^ n * a ∈ GlobalTheory.Mem.Chr.unitIdl E := mul_mem (mul_mem hk (zpow_mem he n)) ha
  let N : InfinitePlace E → ((Ad E)ˣ →* ℝ) := fun w =>
    ((normHom (α := ℂ)).toMonoidHom.comp
      (((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).comp (pInf E)).toMonoidHom)).comp (Units.coeHom _)
  have hN : ∀ w x, N w x = ‖pInf E (x : Ad E) w‖ := fun _ _ => rfl
  have hpos : ∀ w x, 0 < N w x := fun w x =>
    lt_of_le_of_ne (hN w x ▸ norm_nonneg _) ((Group.isUnit x).map (N w)).ne_zero.symm
  have hlog : ∀ w, |Real.log (N w (diag E k * eIdele E ^ n * a))| ≤ R := fun w => by
    have h1 : N w (diag E k) = w (u : E) := by
      rw [hN]
      change ‖pInf E (algebraMap E (Ad E) (u : E)) w‖ = _
      rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq]
    have h2 : Real.log (N w (eIdele E)) = 1 := by
      rw [hN, pInf_eIdele, Complex.norm_exp, Real.log_exp, Complex.one_re]
    rw [map_mul, map_mul, Real.log_mul (mul_pos (hpos _ _) (hpos _ _)).ne' (hpos _ _).ne',
      Real.log_mul (hpos _ _).ne' (hpos _ _).ne', map_zpow, Real.log_zpow, h2, h1, hN]
    convert hu w using 2
    ring
  refine ⟨⟨fun w => ?_, fun v => (hmem v).le⟩, fun w => ?_, fun v => (inv_mem hmem v).le⟩
  · rw [← hN, ← Real.log_le_iff_le_exp (hpos _ _)]
    exact (abs_le.1 (hlog w)).2
  · rw [← hN, ← Real.log_le_iff_le_exp (hpos _ _), map_inv, Real.log_inv]
    linarith [(abs_le.1 (hlog w)).1]

theorem exists_compact_idele : ∃ K : Set (Ad E)ˣ, IsCompact K ∧ ∀ x : (Ad E)ˣ,
    ∃ (k : Eˣ) (n : ℤ), diag E k * eIdele E ^ n * x ∈ K := by
  obtain ⟨K, hK, h⟩ := exists_compact_unit E
  let S : Subgroup (Ad E)ˣ := GlobalTheory.Mem.Chr.unitIdl E ⊔ (diag E).range
  haveI : S.FiniteIndex := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup E
  refine ⟨⋃ q : (Ad E)ˣ ⧸ S, (· * q.out) '' K,
    isCompact_iUnion fun q => hK.image (continuous_id.mul continuous_const), fun x => ?_⟩
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S x
  obtain ⟨a, ha, _, ⟨k, rfl⟩, e⟩ := Subgroup.mem_sup.1 (inv_mem s.2)
  obtain ⟨k', n, hk⟩ := h a ha
  refine ⟨k' * k⁻¹, n, Set.mem_iUnion.2 ⟨(x : (Ad E)ˣ ⧸ S), _, hk, ?_⟩⟩
  have : a = (s : (Ad E)ˣ)⁻¹ * (diag E k)⁻¹ := eq_mul_inv_of_mul_eq e
  simp only [hs, map_mul, map_inv, this]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem one_lt_ideleNorm_eIdele : 1 < ideleNorm (E := E) (eIdele E) := by
  have h1 : ∀ v : InfinitePlace E, ‖(eIdele E : Ad E).1 v‖ = Real.exp 1 := fun v => by
    have := pInf_eIdele E v
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)]
    refine (congrArg norm this).trans ?_
    rw [Complex.norm_exp, Complex.one_re]
  have h2 : ∀ v : HeightOneSpectrum (𝓞 E), ‖(eIdele E : Ad E).2 v‖ = 1 := fun v => by
    change ‖pFin E (eIdele E : Ad E) v‖ = 1
    rw [pFin_eIdele]
    exact norm_one
  change 1 < (∏ v : InfinitePlace E, ‖(eIdele E : Ad E).1 v‖ ^ v.mult) *
    (∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖(eIdele E : Ad E).2 v‖)
  simp only [h1, h2, finprod_one, mul_one]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  exact one_lt_pow₀ (Real.one_lt_exp_iff.2 one_pos) Module.finrank_pos.ne'

theorem exists_nhds_idele : ∃ W ∈ 𝓝 (1 : (Ad E)ˣ), ∀ (k : Eˣ) (n : ℤ), diag E k * eIdele E ^ n ∈ W →
    diag E k * eIdele E ^ n = 1 := by
  obtain ⟨U, hU, h⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero E
  have hL : 0 < Real.log (ideleNorm (E := E) (eIdele E)) := Real.log_pos (one_lt_ideleNorm_eIdele E)
  have h1 : (fun x : (Ad E)ˣ => (x : Ad E) - 1) ⁻¹' U ∈ 𝓝 (1 : (Ad E)ˣ) :=
    (Units.continuous_val.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using hU)
  have h2 : {x : (Ad E)ˣ | |Real.log (ideleNorm (E := E) x)| < Real.log (ideleNorm (E := E) (eIdele E))} ∈
      𝓝 (1 : (Ad E)ˣ) :=
    (isOpen_lt (continuous_ideleNorm.log ideleNorm_ne_zero).abs continuous_const).mem_nhds (by simpa using hL)
  refine ⟨_, Filter.inter_mem h1 h2, fun k n ⟨h3, h4⟩ => ?_⟩
  have h5 : ideleNorm (E := E) (diag E k) = 1 := ideleNorm_principalIdele k
  rw [Set.mem_setOf_eq, map_mul, h5, one_mul, map_zpow, Real.log_zpow, abs_mul, abs_of_pos hL,
    mul_lt_iff_lt_one_left hL] at h4
  have hn : n = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast h4)
  subst hn
  rw [zpow_zero, mul_one] at h3 ⊢
  have h6 := h ((k : E) - 1) (by rw [map_sub, map_one]; exact h3)
  rw [show k = 1 from Units.ext (sub_eq_zero.1 h6), map_one]

abbrev toGL : (Ad E)ˣ →* GA E 1 := GeneralLinearGroup.scalar (Fin 1)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem det_toGL (x : (Ad E)ˣ) : GeneralLinearGroup.det (toGL E x) = x :=
  Units.ext (by
    change (Matrix.scalar (Fin 1) (x : Ad E)).det = x
    simp)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem toGL_det (g : GA E 1) : toGL E (GeneralLinearGroup.det g) = g := by
  ext i j
  change Matrix.scalar (Fin 1) (g : Matrix (Fin 1) (Fin 1) (Ad E)).det i j = _
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0, Matrix.det_fin_one]
  simp

omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_toGL : Continuous (toGL E) :=
  Continuous.units_map _ (by
    change Continuous fun x : Ad E => Matrix.diagonal fun _ : Fin 1 => x
    exact (continuous_pi fun _ => continuous_id).matrix_diagonal)

theorem det_splitCentre : GeneralLinearGroup.det (splitCentre E 1 1) = eIdele E := by
  rw [splitCentre, det_infGL, eIdele]
  congr 1
  refine Units.ext ?_
  change (Matrix.scalar (Fin 1) _).det = _
  simp

omit [_root_.NumberField.IsTotallyComplex E] in
theorem det_ratGL (g : GL (Fin 1) E) : GeneralLinearGroup.det (ratGL E 1 g) = diag E (GeneralLinearGroup.det g) :=
  Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)

theorem mem_latticeGL (g : GA E 1) :
    g ∈ latticeGL E 1 ↔ ∃ (k : Eˣ) (n : ℤ), diag E k * eIdele E ^ n = GeneralLinearGroup.det g := by
  constructor
  · intro hg
    have : latticeGL E 1 ≤ ((diag E).range ⊔ Subgroup.zpowers (eIdele E)).comap GeneralLinearGroup.det := by
      refine sup_le ?_ ?_
      · rintro _ ⟨g, rfl⟩
        exact Subgroup.mem_sup_left ⟨_, (det_ratGL E g).symm⟩
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap, det_splitCentre]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    obtain ⟨_, ⟨k, rfl⟩, _, ⟨n, rfl⟩, e⟩ := Subgroup.mem_sup.1 (this hg)
    exact ⟨k, n, e⟩
  · rintro ⟨k, n, e⟩
    have h1 : toGL E (diag E k) = ratGL E 1 (GeneralLinearGroup.scalar (Fin 1) k) := by
      rw [← toGL_det E (ratGL E 1 _), det_ratGL]
      congr 2
      refine Units.ext ?_
      change _ = (Matrix.scalar (Fin 1) (k : E)).det
      simp
    rw [← toGL_det E g, ← e, map_mul, map_zpow, ← det_splitCentre, toGL_det, h1]
    exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨n, rfl⟩

theorem exists_compact_latticeGL :
    ∃ K : Set (GA E 1), IsCompact K ∧ ∀ g, ∃ γ ∈ latticeGL E 1, γ * g ∈ K := by
  obtain ⟨K, hK, h⟩ := exists_compact_idele E
  refine ⟨toGL E '' K, hK.image (continuous_toGL E), fun g => ?_⟩
  obtain ⟨k, n, hk⟩ := h (GeneralLinearGroup.det g)
  exact ⟨toGL E (diag E k * eIdele E ^ n), (mem_latticeGL E _).2 ⟨k, n, (det_toGL E _).symm⟩,
    _, hk, by rw [map_mul (toGL E), toGL_det]⟩

end GlobalTheory.IdeleCovolume

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallinePrismsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crystalline_prisms : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∃ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (j₀ : ZMod a → S₀.A →+* K⟦X⟧), PP.I = Ideal.span {(l : PP.A)} ∧ δ.comp p₀ = δ.comp p₁ ∧ (∀ τ y, j₀ τ (δ.f y) = PowerSeries.constantCoeff (j τ y)) ∧ (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) ∧ (∀ τ y, j τ (PP.D.φ y) = φ₂ (j (τ - 1) y)) ∧ ∃ hS : ∀ τ y (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (j τ y)) ∈ S O K e, (∀ τ y (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (j τ y) ∈ S O K e) ∧ ∀ (Cr : Obj l ↥(OL (ϖ.field a))) (eC : Cr.A ≃+* Per.Acris l) (h : GlobalTheory.Prism.Hom (ainfObj (ϖ.field a)) Cr), Cr.I = Ideal.span {(l : Cr.A)} → (∀ x, eC (Cr.D.φ x) = frobC l (eC x)) → (∀ x : Ainf l, eC (h.f x) = ainfToAcris l (WittVector.frobenius x)) → ∀ g : ↥(GK (ϖ.field a)), ∃ ev : GlobalTheory.Prism.Hom PP Cr, ev.comp p₀ = h.comp (ϖ.toAinf a) ∧ ev.comp p₁ = (h.comp (ainfHom (ϖ.field a) g)).comp (ϖ.toAinf a) ∧ ∀ (y : PP.A) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] eC (ev.f y) - ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K fun τ => ⟨_, hS τ y i⟩ := by
  first | exact @GlobalTheory.CrysPrism.exists_crys_prisms | exact GlobalTheory.CrysPrism.exists_crys_prisms | (intros; apply GlobalTheory.CrysPrism.exists_crys_prisms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqTmulOneOfMonodromyFrobeniusFiltrationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_tmul_one_of_monodromy_frobenius_filtration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (z : V ⊗[ℚ_[l]] Bst P), monV P ℚ_[l] V z = 0 → phiV P ℚ_[l] V z = z → LinearMap.lTensor V ι.toLinearMap z ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 → ∃ v : V, z = v ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
  first | exact @GlobalTheory.PMon.exists_eq_tmul_one_of_mon_phi_fil | exact GlobalTheory.PMon.exists_eq_tmul_one_of_mon_phi_fil | (intros; apply GlobalTheory.PMon.exists_eq_tmul_one_of_mon_phi_fil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantLogSemistableToDeRham
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BstLog

theorem iota_exists : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ ι : Bst P →ₐ[ℚ_[l]] P.R.BdR, (∀ b, ι (Polynomial.C b) = P.ιB b) ∧
      (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) := by
  intro l _ P AI T
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.PMon.exists_log_tilt_BdR l P AI T
  have hcomm : ∀ (g : GQ l) (z : P.R.B), P.ιB (P.actQ g z) = P.actQdR g (P.ιB z) := by
    intro g z
    have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ z
    rwa [P.PD_ι, P.PD_actB, P.PD_ι, P.PD_actdR] at this
  let ι : Bst P →ₐ[ℚ_[l]] P.R.BdR := Polynomial.eval₂AlgHom P.ιB u (fun _ => Commute.all _ _)
  refine ⟨ι, fun b => Polynomial.eval₂_C _ _, fun g x => ?_⟩
  have h : ι.comp (actSt P g) = ((P.actQdR g : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →ₐ[ℚ_[l]] P.R.BdR).comp ι := by
    apply Polynomial.algHom_ext'
    · ext b
      show Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (actSt P g (Polynomial.C b)) =
        P.actQdR g (Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (Polynomial.C b))
      rw [actSt_C, Polynomial.eval₂_C, Polynomial.eval₂_C]
      exact hcomm g b
    · show Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u (actSt P g Polynomial.X) =
        P.actQdR g (Polynomial.eval₂ (P.ιB : P.R.B →+* P.R.BdR) u Polynomial.X)
      rw [actSt_X, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, hu]
      rfl
  exact congrArg (fun F : Bst P →ₐ[ℚ_[l]] P.R.BdR => F x) h

end GlobalTheory.BstLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFCrystalHomOfStratifiedPhiModuleHom
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} {S : Strat bk d} {M : FCrys l ↥(OL K)}
  {e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)}

theorem IsCoord.v_eq_of_sum {B Q : Obj l ↥(OL K)} {V : Eval S B (M.M B)} (hV : IsCoord e V) (a : Hom B Q)
    (g : Hom bk.prism Q) (x : M.M B) (z : Fin d → Q.A) (hz : M.tr a x = ∑ i, z i • M.tr g (e i)) :
    V.v a g x = z := by
  obtain ⟨b, hb⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ g.f _ _ (M.tr g) (M.tr_bc g) _ e
  have h := (hV a g x).symm.trans hz
  simp only [← hb] at h
  funext i
  have := congrArg (fun y => b.repr y i) h
  simpa [Finsupp.single_apply, Module.Basis.repr_self] using this

theorem IsCoord.v_tr {B B' Q : Obj l ↥(OL K)} {V : Eval S B (M.M B)} {V' : Eval S B' (M.M B')}
    (hV : IsCoord e V) (hV' : IsCoord e V') (k : Hom B B') (a : Hom B' Q) (g : Hom bk.prism Q) (x : M.M B) :
    V'.v a g (M.tr k x) = V.v (a.comp k) g x :=
  hV'.v_eq_of_sum a g _ _ (by rw [← M.tr_comp]; exact hV _ g x)

theorem exists_fHom_of_isStratHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ)
    (S : Strat bk d) (S' : Strat bk d') (M M' : FCrys l ↥(OL K))
    (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (e' : Module.Basis (Fin d') bk.prism.A (M'.M bk.prism)),
    Framed S M e → Framed S' M' e' → ∀ Y : Matrix (Fin d') (Fin d) bk.S, IsStratHom S S' Y →
    ∃ u : FHom M M', ∀ j, u.u bk.prism (e j) = ∑ i, bk.toP (Y i j) • e' i := by
  intro l _ K bk d d' S S' M M' e e' hF hF' Y hY
  choose V hV using _root_.GlobalTheory.BSP.CoordEx.main l K bk d S M e hF
  choose V' hV' using _root_.GlobalTheory.BSP.CoordEx.main l K bk d' S' M' e' hF'
  choose w hw using fun B => _root_.GlobalTheory.BSP.evalHom l K bk d d' S S' Y hY B (M.M B) (M'.M B) (V B) (V' B)
  refine ⟨⟨w, fun {P P'} k x => ?_, fun P t x m k h =>
    GlobalTheory.T.stratifiedCrystalValueMap_comm_frobenius l K bk d d' S S' M e M' e' hF hF' Y hY P (V P) (V' P) (hV P) (hV' P) (w P) (hw P) t x m k h⟩,
    fun j => ?_⟩
  · obtain ⟨C, h, ⟨f⟩, hc⟩ := _root_.GlobalTheory.BSP.exists_cover_receiving_bk l K bk P'
    apply (_root_.GlobalTheory.BSP.Eval.effective_of_cover l K bk d' S' P' C (M'.M P') (V' P') h f hc).1
    rw [hw, IsCoord.v_tr (hV P) (hV P'), IsCoord.v_tr (hV' P) (hV' P'), hw]
  · have h1 := hV' bk.prism (Hom.id _) (Hom.id _) (w bk.prism (e j))
    have h2 : (V bk.prism).v (Hom.id _) (Hom.id _) (e j) = Pi.single j 1 :=
      IsCoord.v_eq_of_sum (hV _) _ _ _ _ (by simp [M.tr_id, Pi.single_apply])
    have h3 := ((hw bk.prism _ (Hom.id _) (Hom.id _) (e j)).trans (congrArg _ h2)).trans
      (Matrix.mulVec_single_one _ j)
    rw [h3] at h1
    simp only [M'.tr_id] at h1
    refine h1.trans (Finset.sum_congr rfl fun i _ => ?_)
    exact congrArg (fun c : bk.prism.A => c • e' i) (show ((Y.map (BK.hf (Hom.id bk.prism))).col j) i = bk.toP (Y i j) from rfl)

end GlobalTheory.BSP
end

