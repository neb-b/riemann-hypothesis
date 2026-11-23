module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompComplexifiedMaxCompact
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestWeightMatrixCoefficientDependsOnWeight
section
open Matrix Formalism.MainNotions.S GlobalTheory.JointHarm

noncomputable section

namespace GlobalTheory.JointHarm.Sph

variable {n : ℕ} {ε : Fin n → Bool} {μ : Fin n → ℝ}

theorem entire_eq_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h : ∀ t : ℝ, f t = 0) (z : ℂ) : f z = 0 := by
  have ha : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  refine ha.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ 0) ?_
    (Set.mem_univ z)
  have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := Complex.continuous_ofReal.tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  exact ht.frequently (Filter.Eventually.of_forall h).frequently

theorem diag_mem {d : Fin n → ℂ} (hd : ∀ a, d a ≠ 0) : Matrix.diagonal d ∈ GlobalTheory.Dec.KC ε := by
  refine ⟨?_, by simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  exact fun a _ => hd a

theorem mul_mem {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ GlobalTheory.Dec.KC ε) (hb : b ∈ GlobalTheory.Dec.KC ε) :
    a * b ∈ GlobalTheory.Dec.KC ε :=
  ⟨ha.1.mul hb.1, by rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]⟩

theorem ct_mem {a : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ GlobalTheory.Dec.KC ε) : aᴴ ∈ GlobalTheory.Dec.KC ε := by
  refine ⟨by simpa [Matrix.star_eq_conjTranspose] using ha.1.star, ?_⟩
  have := congrArg Matrix.conjTranspose ha.2
  simp only [Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose] at this
  exact this.symm

section One

variable {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
  {π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P}

theorem diff_curve (h : IsHolRep ε B π) {c : ℂ → Matrix (Fin n) (Fin n) ℂ}
    (hc : ∀ i j, Differentiable ℂ fun z => c z i j) (hm : ∀ z, c z ∈ GlobalTheory.Dec.KC ε) (x y : P) :
    Differentiable ℂ fun z => B x (π (c z) y) := by
  have h1 : Differentiable ℂ fun z => (fun i j => c z i j : Fin n → Fin n → ℂ) :=
    differentiable_pi.2 fun i => differentiable_pi.2 fun j => hc i j
  have := (h.2.2.2.2 x y).comp (s := Set.univ) h1.differentiableOn (fun z _ => hm z)
  exact differentiableOn_univ.1 this

theorem real_torus (h : IsHolRep ε B π) {x : P} (hx : IsBottom ε π μ x) (s : Fin n → ℝ) :
    π (Matrix.diagonal fun a => Complex.exp (s a : ℂ)) x = Complex.exp ((∑ a, μ a * s a : ℝ) : ℂ) • x := by
  rw [← sub_eq_zero]
  apply h.1
  generalize hw : π (Matrix.diagonal fun a => Complex.exp (s a : ℂ)) x -
    Complex.exp ((∑ a, μ a * s a : ℝ) : ℂ) • x = w
  have hd := diff_curve h (c := fun z => Matrix.diagonal fun a => Complex.exp (z * s a * Complex.I))
    (fun i j => by
      by_cases e : i = j
      · subst e; simp only [Matrix.diagonal_apply_eq]; fun_prop
      · simp only [Matrix.diagonal_apply_ne _ e]; fun_prop)
    (fun z => diag_mem fun a => Complex.exp_ne_zero _) w x
  have h0 := entire_eq_zero (f := fun z => B w (π (Matrix.diagonal fun a => Complex.exp (z * s a * Complex.I)) x) -
      Complex.exp (z * ((∑ a, μ a * s a : ℝ) : ℂ) * Complex.I) * B w x) (hd.sub (by fun_prop))
    (fun t => by
      have := hx.2 (fun a => t * s a)
      have e : (∑ a, μ a * (t * s a)) = t * ∑ a, μ a * s a := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
      rw [e] at this
      simp only [Complex.ofReal_mul] at this
      simp only [this, map_smul, smul_eq_mul, sub_self]) (-Complex.I)
  have e : ∀ u : ℂ, -Complex.I * u * Complex.I = u := fun u => by
    linear_combination (-u) * Complex.I_mul_I
  simp only [e] at h0
  conv_lhs => enter [2]; rw [← hw]
  rw [map_sub, map_smul, smul_eq_mul, h0]

theorem borel {b : Matrix (Fin n) (Fin n) ℂ} (hb : b ∈ GlobalTheory.Dec.KC ε) (hl : GlobalTheory.Dec.IsLo b)
    (hp : ∀ i, b i i = Complex.exp (Real.log (b i i).re : ℝ))
    (h : IsHolRep ε B π) {x : P} (hx : IsBottom ε π μ x) :
    π b x = Complex.exp ((∑ a, μ a * Real.log (b a a).re : ℝ) : ℂ) • x := by
  have hne : ∀ i, b i i ≠ 0 := fun i => by rw [hp i]; exact Complex.exp_ne_zero _
  have hu : Matrix.diagonal (fun a => (b a a)⁻¹) * b ∈ GlobalTheory.Dec.KC ε :=
    mul_mem (diag_mem fun a => inv_ne_zero (hne a)) hb
  have hlu : IsLoUni (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := fun i j =>
    ⟨fun hij => by rw [Matrix.diagonal_mul, hl i j hij, mul_zero],
      fun hij => by subst hij; rw [Matrix.diagonal_mul, inv_mul_cancel₀ (hne i)]⟩
  have e : b = Matrix.diagonal (fun a => Complex.exp (Real.log (b a a).re : ℝ)) *
      (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.diagonal_mul, ← hp i, mul_inv_cancel_left₀ (hne i)]
  conv_lhs => rw [e]
  rw [h.2.2.1 _ (diag_mem fun a => Complex.exp_ne_zero _) _ hu, Module.End.mul_apply, hx.1 _ hu hlu,
    real_torus h hx]

end One


open scoped ComplexOrder in
theorem gram {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ GlobalTheory.Dec.KC ε) (μ : Fin n → ℝ) :
    ∃ c : ℂ, ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ)
      (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) (x y : P), IsHolRep ε B π → IsBottom ε π μ x →
      IsBottom ε π μ y → B x (π (gᴴ * g) y) = c * B x y := by
  obtain ⟨k, b, hk, hb, hl, hp, rfl⟩ := GlobalTheory.Dec.IwKC.exists_decomp ε hg
  have hp' : ∀ i, b i i = Complex.exp (Real.log (b i i).re : ℝ) := fun i => by
    have := Complex.pos_iff.1 (hp i)
    rw [← Complex.ofReal_exp, Real.exp_log this.1]
    exact Complex.ext rfl (by simpa using this.2.symm)
  refine ⟨star (Complex.exp ((∑ a, μ a * Real.log (b a a).re : ℝ) : ℂ)) *
    Complex.exp ((∑ a, μ a * Real.log (b a a).re : ℝ) : ℂ), fun P _ _ B π x y h hx hy => ?_⟩
  rw [GlobalTheory.Dec.IwKC.gram_unitary_mul hk.1, h.2.2.1 _ (ct_mem hb) _ hb, Module.End.mul_apply,
    ← h.2.2.2.1 _ hb, borel hb hl hp' h hx, borel hb hl hp' h hy]
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply]
  ring

section Exp

open scoped Matrix.Norms.Operator

theorem exp_mem {H : Matrix (Fin n) (Fin n) ℂ} (hJ : H * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * H) (z : ℂ) :
    NormedSpace.exp (z • H) ∈ GlobalTheory.Dec.KC ε := by
  refine ⟨Matrix.isUnit_exp _, ?_⟩
  have : Commute (z • H) (Formalism.REAL.Jm ε) := Commute.smul_left hJ z
  exact this.exp_left.eq

theorem exp_diff (H : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    Differentiable ℂ fun z : ℂ => NormedSpace.exp (z • H) i j := by
  have h1 : Differentiable ℂ fun z : ℂ => NormedSpace.exp (z • H) :=
    fun z => (hasDerivAt_exp_smul_const H z).differentiableAt
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)).differentiable.comp h1

theorem exp_gram {H : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ = H) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • H) =
      (NormedSpace.exp (((t : ℂ) / 2) • H))ᴴ * NormedSpace.exp (((t : ℂ) / 2) • H) := by
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH]
  have e : star ((t : ℂ) / 2) = (t : ℂ) / 2 := by simp
  rw [e, ← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul, add_halves]

end Exp

theorem coeff_eq (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (P : Type) [AddCommGroup P] [Module ℂ P]
    (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) (P' : Type) [AddCommGroup P']
    [Module ℂ P'] (B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ) (π' : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P') (x y : P)
    (x' y' : P') (h : IsHolRep ε B π) (h' : IsHolRep ε B' π') (hx : IsBottom ε π μ x) (hy : IsBottom ε π μ y)
    (hx' : IsBottom ε π' μ x') (hy' : IsBottom ε π' μ y') :
    ∀ k ∈ Formalism.REAL.Kset ε, B x (π k y) * B' x' y' = B x y * B' x' (π' k y') := by
  intro k hk
  obtain ⟨Y, ⟨hG, hY⟩, rfl, -⟩ := Formalism.REAL.compact_exists_log_bounded ε k hk
  have hs : Yᴴ = -Y := by
    have h1 : (Yᴴ + Y) * Formalism.REAL.Jm ε = 0 := by
      rw [Matrix.add_mul, hY]; exact hG
    have h2 := congrArg (· * Formalism.REAL.Jm ε) h1
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one, Matrix.zero_mul] at h2
    exact eq_neg_of_add_eq_zero_left h2
  have hH : ((-Complex.I) • Y)ᴴ = (-Complex.I) • Y := by
    rw [Matrix.conjTranspose_smul, hs]; simp
  have hJ : ((-Complex.I) • Y) * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * ((-Complex.I) • Y) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hY]
  have h0 := entire_eq_zero (f := fun z => B x (π (NormedSpace.exp (z • (-Complex.I) • Y)) y) * B' x' y' -
      B x y * B' x' (π' (NormedSpace.exp (z • (-Complex.I) • Y)) y'))
    (((diff_curve h (exp_diff _) (exp_mem hJ) x y).mul_const _).sub
      ((diff_curve h' (exp_diff _) (exp_mem hJ) x' y').const_mul _))
    (fun t => by
      obtain ⟨c, hc⟩ := gram (exp_mem hJ ((t : ℂ) / 2)) μ
      simp only [exp_gram hH t, hc P B π x y h hx hy, hc P' B' π' x' y' h' hx' hy']
      ring) Complex.I
  have e : Complex.I • (-Complex.I) • Y = Y := by rw [smul_smul]; simp
  simp only [e] at h0
  exact sub_eq_zero.1 h0

end GlobalTheory.JointHarm.Sph

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NEqAndIsClosed
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselClosed

open GlobalTheory.BesselCompare (mt_mul mt_one hA_coeff closure_prop spanA)

variable {D : D7}

def spanLt (B : HSp D) {ρ : ℕ} (e : Fin ρ → B.V) (k : ℕ) : Submodule (AE D) (Fin B.rank → AE D) where
  carrier := {v | ∃ c : Fin ρ → AE D, (∀ l : Fin ρ, k ≤ l.1 → c l = 0) ∧ v = ∑ l, c l • vecA B (e l)}
  zero_mem' := ⟨0, fun _ _ => rfl, by simp⟩
  add_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    exact ⟨c + c', fun l hl => by simp [hc l hl, hc' l hl], by simp [add_smul, Finset.sum_add_distrib]⟩
  smul_mem' := by
    rintro a _ ⟨c, hc, rfl⟩
    exact ⟨a • c, fun l hl => by simp [hc l hl], by simp [Finset.smul_sum, smul_smul]⟩

variable {B : HSp D} {ρ : ℕ} {e : Fin ρ → B.V}

theorem spanLt_mono {k k' : ℕ} (h : k ≤ k') : spanLt B e k ≤ spanLt B e k' := by
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨c, fun l hl => hc l (h.trans hl), rfl⟩

theorem vec_mem_spanLt {k : ℕ} {l : Fin ρ} (h : l.1 < k) : vecA B (e l) ∈ spanLt B e k := by
  classical
  refine ⟨Pi.single l 1, fun j hj => Pi.single_eq_of_ne (fun e => by subst e; omega) _, ?_⟩
  rw [Finset.sum_eq_single l] <;> simp +contextual

theorem mulVec_mem_spanLt {k : ℕ} (M : Matrix (Fin B.rank) (Fin B.rank) (AE D))
    (hM : ∀ l : Fin ρ, l.1 < k → M.mulVec (vecA B (e l)) - vecA B (e l) ∈ spanLt B e l.1)
    {v} (hv : v ∈ spanLt B e k) : M.mulVec v ∈ spanLt B e k := by
  obtain ⟨c, hc, rfl⟩ := hv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Matrix.mulVecLin_apply, map_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  rcases lt_or_ge l.1 k with hl | hl
  · rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    have := add_mem (spanLt_mono hl.le (hM l hl)) (vec_mem_spanLt (B := B) (e := e) hl)
    rwa [sub_add_cancel] at this
  · simp [hc l hl]

theorem mem_NS_iff {n : GA D B} : n ∈ GlobalTheory.BesselCompare.NS B e ↔
    (∀ i : Fin ρ, actV B n (e i) - vecA B (e i) ∈ spanLt B e i.1) ∧
      ∀ x : B.V, (∀ i, B.hD x (e i) = 0) → actV B n x - vecA B x ∈ spanLt B e ρ := by
  refine and_congr (forall_congr' fun i => exists_congr fun c => and_congr Iff.rfl sub_eq_iff_eq_add'.symm)
    (forall_congr' fun x => forall_congr' fun _ => exists_congr fun c => ?_)
  rw [sub_eq_iff_eq_add']
  exact ⟨fun h => ⟨fun l hl => absurd l.2 (by omega), h⟩, fun h => h.2⟩

theorem closure_flag (n : GA D B) (hn : n ∈ Subgroup.closure (GlobalTheory.BesselCompare.NS B e)) :
    ∀ i : Fin ρ, actV B n (e i) - vecA B (e i) ∈ spanLt B e i.1 := by
  induction hn using Subgroup.closure_induction'' with
  | one => intro i; simp [actV, mt_one]
  | mem g hg => exact (mem_NS_iff.1 hg).1
  | inv_mem g hg =>
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      have h := mulVec_mem_spanLt (mt B g⁻¹) (fun l hl => ih l hl) ((mem_NS_iff.1 hg).1 i)
      rw [Matrix.mulVec_sub, actV, mulVec_inv_cancel] at h
      have := neg_mem h
      rwa [neg_sub] at this
  | mul g h _ _ ihg ihh =>
    intro i
    have := add_mem (mulVec_mem_spanLt (mt B g) (fun l _ => ihg l) (ihh i)) (ihg i)
    rwa [Matrix.mulVec_sub, actV, ← mulVec_mul, actV, sub_add_sub_cancel] at this

theorem closure_NS : (Subgroup.closure (GlobalTheory.BesselCompare.NS B e) : Set (GA D B)) = GlobalTheory.BesselCompare.NS B e := by
  refine subset_antisymm (fun n hn => mem_NS_iff.2 ⟨closure_flag n hn, fun x hx => ?_⟩) Subgroup.subset_closure
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 ((closure_prop B e n hn).2 x hx)
  exact ⟨a, fun l hl => absurd l.2 (by omega), ha.symm⟩

theorem mem_spanLt_iff {f : Fin ρ → B.V} (ef : ∀ i j, B.hD (e i) (f j) = if i = j then 1 else 0) {k : ℕ} {v} :
    v ∈ spanLt B e k ↔ (∀ l : Fin ρ, k ≤ l.1 → hA B v (vecA B (f l)) = 0) ∧
      v = ∑ l, hA B v (vecA B (f l)) • vecA B (e l) := by
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  rintro ⟨c, hc, rfl⟩
  simp only [hA_coeff B e f ef]
  exact ⟨hc, trivial⟩

theorem isClosed_NS {f : Fin ρ → B.V} (ef : ∀ i j, B.hD (e i) (f j) = if i = j then 1 else 0) :
    IsClosed (GlobalTheory.BesselCompare.NS B e) := by
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  have : T2Space (AE D) := e0.isEmbedding.t2Space
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  have hm : Continuous (fun k : GA D B => mt B k) := Units.continuous_val.comp continuous_subtype_val
  have hh : ∀ y, Continuous fun v => hA B v y := fun y =>
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  have hc : ∀ k, IsClosed (spanLt B e k : Set (Fin B.rank → AE D)) := fun k => by
    have : (spanLt B e k : Set (Fin B.rank → AE D)) =
        (⋂ l : Fin ρ, ⋂ _ : k ≤ l.1, {v | hA B v (vecA B (f l)) = 0}) ∩
          {v | v = ∑ l, hA B v (vecA B (f l)) • vecA B (e l)} := by
      ext v
      simp only [SetLike.mem_coe, mem_spanLt_iff ef, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact (isClosed_iInter fun l => isClosed_iInter fun _ => isClosed_eq (hh _) continuous_const).inter
      (isClosed_eq continuous_id (continuous_finsetSum _ fun l _ => (hh _).smul continuous_const))
  have : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  have : ContinuousSub (AE D) := IsTopologicalAddGroup.to_continuousSub
  have ha : ∀ x, Continuous fun n : GA D B => actV B n x - vecA B x := fun x =>
    continuous_pi fun j => ((continuous_apply j).comp (hm.matrix_mulVec continuous_const)).sub continuous_const
  have : GlobalTheory.BesselCompare.NS B e =
      (⋂ i : Fin ρ, (fun n => actV B n (e i) - vecA B (e i)) ⁻¹' spanLt B e i.1) ∩
        ⋂ x : B.V, ⋂ _ : ∀ i, B.hD x (e i) = 0, (fun n => actV B n x - vecA B x) ⁻¹' spanLt B e ρ := by
    ext n
    simp only [mem_NS_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [this]
  exact (isClosed_iInter fun i => (hc _).preimage (ha _)).inter
    (isClosed_iInter fun x => isClosed_iInter fun _ => (hc _).preimage (ha _))

theorem N_eq_and_isClosed : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι), (d.N : Set (GA D B)) = d.NSet ∧ IsClosed (d.N : Set (GA D B)) := by
  intro D A B ι d
  have h : (d.N : Set (GA D B)) = GlobalTheory.BesselCompare.NS B d.e := closure_NS
  exact ⟨h, h ▸ isClosed_NS d.ef⟩

end GlobalTheory.BesselClosed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelic
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.FinTranslate

open GlobalTheory.PointAtPlaceHom

variable {D : D7} {θ : InfF D} {V : HSp D}

theorem Rder_rTr {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (φ : GA D V → ℂ) : Rder θ V τ X (rTr V k φ) = rTr V k (Rder θ V τ X φ) := by
  funext g
  unfold Rder rTr
  congr 1
  funext t
  rw [mul_assoc, mul_assoc, oneP, comm_of_mem V (atTau_mem V τ _) hk]

theorem foldr_rTr {α : Type} (k : GA D V) (F : α → (GA D V → ℂ) → (GA D V → ℂ)) (l : List α)
    (h : ∀ a ∈ l, ∀ φ, F a (rTr V k φ) = rTr V k (F a φ)) (φ : GA D V → ℂ) :
    l.foldr F (rTr V k φ) = rTr V k (l.foldr F φ) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih fun b hb => h b (List.mem_cons_of_mem _ hb), h a List.mem_cons_self]

theorem gelf_rTr {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) (n : ℕ) (φ : GA D V → ℂ) :
    gelf θ V τ n (rTr V k φ) = rTr V k (gelf θ V τ n φ) := by
  unfold gelf
  rw [Finset.sum_congr rfl fun idx _ => foldr_rTr k _ _ (fun a ha ψ => ?_) φ]
  · funext g
    simp only [rTr, Finset.sum_apply]
  · obtain ⟨b, rfl⟩ := List.mem_ofFn.1 ha
    unfold RderC
    rw [Rder_rTr hk, Rder_rTr hk]
    rfl

theorem isAutFunSm_rTr_fin : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ),
    IsAutFunSm θ V φ → ∀ k ∈ GfC V, IsAutFunSm θ V (rTr V k φ) := by
  intro D θ _ V φ h k hk
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine { left := fun γ hγ g => ?_, level := ?_, cont := h.cont.comp (continuous_mul_const k),
           smooth := fun n τs Xs hX g => ?_, zfin := ?_, growth := ?_ }
  · unfold rTr
    rw [mul_assoc, h.left γ hγ]
  · obtain ⟨U, hU, e⟩ := h.level
    refine ⟨U.comap (MulAut.conj k⁻¹).toMonoidHom, hU.preimage ?_, fun u hu hf g => ?_⟩
    · show Continuous fun u : GA D V => k⁻¹ * u * k⁻¹⁻¹
      fun_prop
    · have hu' : k⁻¹ * u * k⁻¹⁻¹ ∈ U := hu
      have := e _ hu' (mul_mem (mul_mem (inv_mem hk) hf) (inv_mem (inv_mem hk))) (g * k)
      unfold rTr
      rw [← this]
      congr 1
      group
  · have := h.smooth n τs Xs hX (g * k)
    convert this using 2 with t
    unfold rTr
    rw [mul_assoc, mul_assoc, comm_of_mem V (list_prod_mem fun a ha => ?_) hk]
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 ha
    exact atTau_mem V _ _
  · obtain ⟨W, hW, m, s⟩ := h.zfin
    refine ⟨W.map (LinearMap.funLeft ℂ ℂ fun g => g * k), inferInstance, ⟨φ, m, rfl⟩, ?_⟩
    rintro τ n _ ⟨f, hf, rfl⟩
    exact ⟨_, s τ n f hf, (gelf_rTr hk τ n f).symm⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl (x * k)
    refine ⟨C, fun g hg => ?_⟩
    rw [foldr_rTr k _ l (fun a _ ψ => Rder_rTr hk _ _ ψ) φ]
    unfold rTr
    rw [mul_assoc, comm_of_mem V hg hk, ← mul_assoc]
    exact hC g hg

end GlobalTheory.Mem.FinTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceAnnihilatorRelativelyCompact
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct RestrictedProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitAnnihilator

open GlobalTheory.IdemModTwo


open Classical in
theorem continuous_singleV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (singleV F v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem trace_split {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} (he : SplitAt D v e)
    (x y : Fv D.host.F v) :
    Algebra.trace (AF D.host.F) (AE D) (fj D (singleV D.host.F v x) * e * (fj D (singleV D.host.F v y) * e)) =
      pairA D.host.F 0 (singleV D.host.F v (x * y)) := by
  have h1 : fj D (singleV D.host.F v x) * e * (fj D (singleV D.host.F v y) * e) =
      fj D (singleV D.host.F v (x * y)) * e := by
    rw [mul_mul_mul_comm, he.1, ← map_mul, singleV_mul, GlobalTheory.SplitIdem.evalV_singleV_same]
  have h2 := GlobalTheory.FockCompare.SymplVal.trace_AE D (fj D (singleV D.host.F v (x * y)) * e)
  rw [map_mul (cA D), cA_fj, ← mul_add, he.2.2, ← map_mul (fj D), singleV_mul, GlobalTheory.SplitIdem.evalV_singleV_same, mul_one] at h2
  rw [h1]
  exact tmul_one_inj (F := D.host.F) (E := D.host.E) h2

theorem annihilator_subset_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1) → ∀ ε : AE D, IsSplitIdem D ε → ∀ V ∈ nhds (0 : AE D), ∃ C : Set (AE D), IsCompact C ∧ ∀ a, ε * a = a → (∀ s ∈ V, ε * s = s → ψ (Algebra.trace (AF D.host.F) (AE D) (a * s)) = 1) → a ∈ C := by
  intro D ψ hψ e hε V hV
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 hε
  obtain ⟨y, hy⟩ := hψ v
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have : ProperSpace (Fv D.host.F v) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion D.host.F v
  let j : Fv D.host.F v → AE D := fun x => fj D (singleV D.host.F v x) * e
  have hj : Continuous j := by
    have h1 : Continuous (algebraMap (AF D.host.F) (AE D)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF D.host.F) (AE D))
    have h2 : Continuous fun x : Fv D.host.F v => pairA D.host.F 0 (singleV D.host.F v x) :=
      Continuous.prodMk continuous_const (continuous_singleV D.host.F v)
    exact (h1.comp h2).mul continuous_const
  have hj0 : j 0 = 0 := by
    have h0 : singleV D.host.F v 0 = 0 := by
      rw [← sub_self (0 : Fv D.host.F v), singleV_sub, sub_self]
    simp only [j, h0, map_zero, zero_mul]
  have hV' : j ⁻¹' V ∈ nhds (0 : Fv D.host.F v) := hj.continuousAt.preimage_mem_nhds (by rwa [hj0])
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hV'
  refine ⟨j '' Metric.closedBall 0 (‖y‖ / r), (isCompact_closedBall _ _).image hj, fun a ha hs => ?_⟩
  obtain ⟨x, hx⟩ := he.exists_scalar a
  rw [ha] at hx
  refine ⟨x, ?_, hx.symm⟩
  by_contra hn
  rw [mem_closedBall_zero_iff, not_le] at hn
  have hxpos : 0 < ‖x‖ := lt_of_le_of_lt (div_nonneg (norm_nonneg _) hr.le) hn
  have hx0 : x ≠ 0 := norm_pos_iff.1 hxpos
  have hmem : y / x ∈ Metric.ball (0 : Fv D.host.F v) r := by
    rw [mem_ball_zero_iff, norm_div, div_lt_iff₀ hxpos]
    rw [div_lt_iff₀ hr] at hn
    linarith
  have h := hs (j (y / x)) (hball hmem) (by
    show e * (_ * e) = _ * e
    rw [mul_left_comm, he.1])
  rw [hx] at h
  change ψ (Algebra.trace _ _ (_ * (_ * e))) = 1 at h
  rw [trace_split he, mul_div_cancel₀ _ hx0] at h
  exact hy h

end GlobalTheory.SplitAnnihilator

end
end

