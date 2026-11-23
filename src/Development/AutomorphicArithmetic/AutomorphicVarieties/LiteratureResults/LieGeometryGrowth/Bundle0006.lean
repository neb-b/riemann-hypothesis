module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfCsTens
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem cmp_lT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j ((Matrix.toLin' Q).lTensor W y) = ∑ k, Q j k • cmp k y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add, Finset.sum_add_distrib]
  | tmul φ v =>
    simp only [LinearMap.lTensor_tmul, cmp_tmul, smul_smul, ← Finset.sum_smul]
    rfl

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (S : Module.End ℂ W)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j (S.rTensor (Fin d → ℂ) y) = S (cmp j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]


variable (E a) in
private def csSub : Submodule ℂ (Sm E a) where
  carrier := {φ | Pf.Cs φ.1}
  zero_mem' := ⟨0, fun _ _ => rfl⟩
  add_mem' := by
    rintro φ ψ ⟨R, hR⟩ ⟨S, hS⟩
    refine ⟨max R S, fun g hg => ?_⟩
    have h1 := hR g (lt_of_le_of_lt (le_max_left _ _) hg)
    have h2 := hS g (lt_of_le_of_lt (le_max_right _ _) hg)
    show φ.1 g + ψ.1 g = 0
    rw [h1, h2, add_zero]
  smul_mem' := by
    rintro c φ ⟨R, hR⟩
    refine ⟨R, fun g hg => ?_⟩
    show c • φ.1 g = 0
    rw [hR g hg, smul_zero]

private theorem cs_iff {d : ℕ} (x : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Pf.Cs (ev x) ↔ x ∈ tens d (csSub E a) := by
  rw [mem_tens]
  constructor
  · rintro ⟨R, hR⟩ j
    exact ⟨R, fun g hg => by rw [Pf.cmp_ev, hR g hg]; rfl⟩
  · intro h
    choose R hR using h
    refine ⟨∑ j, |R j|, fun g hg => funext fun j => ?_⟩
    rw [← Pf.cmp_ev]
    refine hR j g (lt_of_le_of_lt ?_ hg)
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |R j|) (fun i _ => abs_nonneg _) (Finset.mem_univ j))

end

theorem UpperTheory.V.Lit.Geo.Pf.csTens :
    UpperTheory.V.Lit.Geo.Pf.CsTens := by
  intro E _ _ _ a Ξ r X x hx
  rw [cs_iff] at hx
  rw [cs_iff, cs_iff]
  have hA : smA Ξ X x ∈ tens Ξ.d (csSub E a) := mem_tens.2 fun j => by
    rw [smA_apply, cmp_rT]
    exact Pf.csLie E a _ X (mem_tens.1 hx j)
  have hB : smB Ξ X x ∈ tens Ξ.d (csSub E a) := mem_tens.2 fun j => by
    rw [smB_apply, cmp_lT]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (mem_tens.1 hx k)
  constructor
  · have : smLie Ξ X x = smA Ξ X x + smB Ξ X x := by
      simp only [smB, LinearMap.sub_apply, add_sub_cancel]
    rw [this]
    exact Submodule.add_mem _ hA hB
  · rw [smAdj, adj_apply]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ hB hA) ?_
    exact Submodule.smul_of_tower_mem _ _ hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfPtInv
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo
open scoped TensorProduct

private theorem open_stab {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) {S : Set G} (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ g ∈ S, ρ g v = v) :
    IsOpen {g | ρ g v = v} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' S, fun x hx => ?_, hS.preimage (by fun_prop), by simpa using h1⟩
  have e : x = g * (g⁻¹ * x) := by group
  have hg' : ρ g v = v := hg
  show ρ x v = v
  rw [e, map_mul, Module.End.mul_apply, h _ hx, hg']

theorem UpperTheory.V.Lit.Geo.Pf.ptInv :
    UpperTheory.V.Lit.Geo.Pf.PtInv := by
  intro E _ _ _ a χ d G x y
  have h : ∀ g, Pf.pt χ G x y g = ∑ i, ∑ j, G i j *
      (starRingEnd ℂ ((mulChi a χ (cmp i x)).1 g) * (mulChi a χ (cmp j y)).1 g) := by
    intro g
    have hn : ((‖((chiDet a χ g : ℂˣ) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
        starRingEnd ℂ ((chiDet a χ g : ℂˣ) : ℂ) * ((chiDet a χ g : ℂˣ) : ℂ) := by
      rw [Complex.conj_mul']; push_cast; rfl
    simp only [Pf.pt, hn, mulChi_apply, Pf.cmp_ev, dotProduct, Matrix.mulVec, Finset.mul_sum, map_mul, Pi.star_apply,
      Complex.star_def]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hc : Pf.TwInv χ x → Pf.TwInv χ y → Pf.CInv (Pf.pt χ G x y) := by
    intro hx hy
    rw [show Pf.pt χ G x y = _ from funext h]
    refine Pf.CInv.sum _ fun i => Pf.CInv.sum _ fun j => ⟨?_, fun γ g => ?_, fun t g => ?_⟩
    · exact continuous_const.mul ((Complex.continuous_conj.comp (Pf.invLie E a _ (hx i)).1.cont).mul
        (Pf.invLie E a _ (hy j)).1.cont)
    · rw [(hx i).left, (hy j).left]
    · rw [(hx i).centre, (hy j).centre]
  refine ⟨h, hc, fun θ hθ hx hy => ⟨fun γ g => ?_, fun t g => ?_, ?_⟩⟩
  · rw [hθ, hθ, (hc hx hy).left]
  · rw [hθ, hθ, (hc hx hy).centre]
  · change IsOpen {k | finRep E a k θ = θ}
    have ox : IsOpen (⋂ i, {k | finRep E a k (mulChi a χ (cmp i x)) = mulChi a χ (cmp i x)}) :=
      isOpen_iInter_of_finite fun i => (hx i).level
    have oy : IsOpen (⋂ i, {k | finRep E a k (mulChi a χ (cmp i y)) = mulChi a χ (cmp i y)}) :=
      isOpen_iInter_of_finite fun i => (hy i).level
    refine open_stab (finRep E a) θ (ox.inter oy) ⟨by simp, by simp⟩ ?_
    rintro k ⟨h1, h2⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at h1 h2
    have e : ∀ φ : Sm E a, finRep E a k φ = φ → ∀ g, φ.1 (g * finGL E a k) = φ.1 g := fun φ hφ g =>
      congrFun (congrArg Subtype.val hφ) g
    refine Subtype.ext (funext fun g => ?_)
    change θ.1 (g * finGL E a k) = θ.1 g
    rw [hθ, hθ, h, h]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [e _ (h1 i), e _ (h2 j)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfStokesFn
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep UpperTheory.V.Af GlobalTheory.UnitaryBC
open scoped GlobalTheory.CuspRep.CuspidalL2GL

private theorem one_mem {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} :
    (fun _ => (1 : ℂ)) ∈ Sm E a := fun g =>
  (contDiffOn_const (c := (1 : ℂ))).congr fun x hx => by
    have hx' : IsUnit (Matrix.of x) := hx
    simp [chart, hx']

private theorem lie_one {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (X : Lie E a) :
    lie E a X ⟨fun _ => (1 : ℂ), one_mem⟩ = 0 := by
  obtain ⟨c, c0, -, -, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  refine Subtype.ext (funext fun g => ?_)
  exact (hasDerivAt_curve (⟨fun _ => (1 : ℂ), one_mem⟩ : Sm E a) g c X c0 cder).unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))

theorem UpperTheory.V.Lit.Geo.Pf.stokesFn :
    UpperTheory.V.Lit.Geo.Pf.StokesFn := by
  intro E _ _ _ a μ _ θ X hθ hc
  let u : Sm E a := ⟨fun _ => (1 : ℂ), one_mem⟩
  have hu : IsOpen {k | act (.fin k) u = u} := by
    have e : {k | act (.fin k) u = u} = Set.univ := Set.eq_univ_of_forall fun k => rfl
    rw [e]
    exact isOpen_univ
  obtain ⟨h1, h2⟩ := Pf.invLie E a θ hθ
  have h3 := (Pf.invLie E a _ (h2 X)).1
  have m1 := (Pf.bddInt E a μ _ h1 (Pf.csBdd E a _ h1 (.inl hc))).2
  have m2 := (Pf.bddInt E a μ _ h3 (Pf.csBdd E a _ h3 (.inl (Pf.csLie E a θ X hc)))).2
  have m3 := (Pf.bddInt E a μ u.1 ⟨continuous_const, fun _ _ => rfl, fun _ _ => rfl⟩ ⟨1, fun _ => norm_one.le⟩).2
  have e0 : (lie E a X u).1 = fun _ => 0 := congrArg Subtype.val (lie_one X)
  have m4 : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (latticeGL E a) μ (lie E a X u).1 := by
    rw [e0]
    exact (Pf.bddInt E a μ _ ⟨continuous_const, fun _ _ => rfl, fun _ _ => rfl⟩ ⟨0, fun _ => norm_zero.le⟩).2
  have h := UpperTheory.V.Lit.Bor.skew_lie_action_L2 E a μ X u θ hu hθ.level m3 m1 m4 m2
  rw [GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.inner_toL2_eq_theta_pairing, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.inner_toL2_eq_theta_pairing, e0] at h
  simpa [GlobalTheory.AutomorphicL2Unitary.pet, GlobalTheory.AutomorphicL2Unitary.descend, Pf.qint, u] using h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullCentreVal
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo
open scoped TensorProduct

private theorem span_val {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a d : ℕ} (P : Sm E a → Prop)
    (x y : GA E a) (c : ℂ) (h : ∀ φ, P φ → φ.1 x = c * φ.1 y) (m : Sm E a ⊗[ℂ] (Fin d → ℂ))
    (hm : m ∈ Submodule.span ℂ {z : Sm E a ⊗[ℂ] (Fin d → ℂ) | ∃ φ v, P φ ∧ z = φ ⊗ₜ[ℂ] v}) : ev m x = c • ev m y := by
  induction hm using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨φ, v, hφ, rfl⟩ := hz
    rw [ev_tmul, ev_tmul, h φ hφ, mul_smul]
  | zero => simp
  | add z w _ _ hz hw => simp only [map_add (f := _), Pi.add_apply, hz, hw, smul_add]
  | smul s z _ hz => simp only [map_smul, Pi.smul_apply, hz, smul_comm s c]

theorem UpperTheory.V.Lit.Geo.centreVal :
    CentreVal := by
  intro E _ _ _ a U Ξ r hr q α hα X γ t g
  refine span_val (IsLevelFn U Ξ) _ _ _ (fun φ hφ => ?_) _ (hα.3 X)
  rw [mul_assoc, hφ.1, aInv E a φ _ (hφ.2.2 r hr), neg_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldDef
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem sand_comp (g h : GL (Fin a) (Cinf E)) (v : HV E a) : sand g (sand h v) = sand (g * h) v := by
  rw [map_mul]; rfl

private theorem unitary_of_eq {g h : GL (Fin a) (Cinf E)} (e : sand g (hOne E a) = sand h (hOne E a)) :
    ∃ k : Kinf E a, h = g * Unitary.toUnits k := by
  have h1 : sand (g⁻¹ * h) (hOne E a) = hOne E a := by
    rw [← sand_comp, ← e, sand_comp, inv_mul_cancel, map_one]; rfl
  have h2 : (g⁻¹ * h).val * star (g⁻¹ * h).val = 1 := by
    have h3 := sand_val (g⁻¹ * h) (hOne E a)
    rw [h1, hOne_val, mul_one] at h3
    exact h3.symm
  refine ⟨⟨(g⁻¹ * h).val, Matrix.mem_unitaryGroup_iff.2 h2⟩, ?_⟩
  rw [← inv_mul_eq_iff_eq_mul]
  exact Units.ext rfl

private theorem hv_adHerm (k : Kinf E a) (X : Herm E a) : hv (adHerm k X) = sand (Unitary.toUnits k) (hv X) := rfl

end

theorem UpperTheory.V.Lit.Geo.fieldDef :
    FieldDef := by
  classical
  intro E _ _ _ a U Y C hY
  refine ⟨fun s p => if h : p ∈ cone E a then
    sand h.choose (hv (Y (infGL E a h.choose * finGL E a s.out))) else 0, fun g x => ?_⟩
  have hp : sand g (hOne E a) ∈ cone E a := ⟨g, rfl⟩
  obtain ⟨k, hk⟩ := unitary_of_eq hp.choose_spec.symm
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U x
  beta_reduce
  rw [dite_eq_left hp, hk, hu, map_mul (finGL E a), ← mul_assoc, hY.lev _ u.2, ← sand_comp, ← hv_adHerm,
    map_mul (infGL E a), mul_assoc, infGL_comm, ← mul_assoc, hY.cpt]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldDer
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem lie_bound {φ : Sm E a} (h : BddDer φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (X : Lie E a) (g : GA E a), ‖(lie E a X φ).1 g‖ ≤ B * ‖X‖ := by
  let b := Module.finBasis ℝ (Lie E a)
  choose c hc using fun k => h (b k) []
  have hc' : ∀ k g, ‖(lie E a (b k) φ).1 g‖ ≤ c k := fun k g => by simpa using hc k g
  have h0 : ∀ k, 0 ≤ c k := fun k => (norm_nonneg _).trans (hc' k 1)
  refine ⟨∑ k, ‖LinearMap.toContinuousLinearMap (b.coord k)‖ * c k,
    Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (h0 k), fun X g => ?_⟩
  let L : Lie E a →ₗ[ℝ] ℂ :=
    { toFun := fun X => (lie E a X φ).1 g
      map_add' := fun X X' => by rw [map_add (f := _)]; rfl
      map_smul' := fun r X => by rw [map_smul]; rfl }
  have e : L X = ∑ k, b.repr X k • L (b k) := by
    conv_lhs => rw [← b.sum_repr X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  change ‖L X‖ ≤ _
  rw [e, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_smul, mul_right_comm]
  exact mul_le_mul ((LinearMap.toContinuousLinearMap (b.coord k)).le_opNorm X) (hc' k g) (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

private theorem val_bound {U : Subgroup (GL (Fin a) (Af E))} {Y : GA E a → Herm E a} {C : ℝ} (h : IsFld U Y C)
    (g : GA E a) : ‖hv (Y g)‖ ≤ a * C ^ 2 + 1 := by
  obtain ⟨x, h1, h2, -⟩ := h.root g 1 (by simp)
  have hC : 0 ≤ C := (norm_nonneg _).trans h2
  have hp : (0 : ℝ) ≤ a * C ^ 2 + 1 := by positivity
  have e : (Y g).1 = x.val * star x.val - 1 := by rw [h1, one_smul, add_sub_cancel_left]
  have hx : ∀ i j, ‖x.val i j‖ ≤ C := fun i j =>
    ((norm_le_pi_norm (toL x.val i) j).trans (norm_le_pi_norm (toL x.val) i)).trans h2
  change ‖toL (Y g).1‖ ≤ _
  refine (pi_norm_le_iff_of_nonneg hp).2 fun i => (pi_norm_le_iff_of_nonneg hp).2 fun j => ?_
  change ‖(Y g).1 i j‖ ≤ _
  rw [e, Matrix.sub_apply, Matrix.mul_apply]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_sum_le _ _).trans ?_) ?_)
  · calc ∑ k, ‖x.val i k * star x.val k j‖ ≤ ∑ _k : Fin a, C ^ 2 := Finset.sum_le_sum fun k _ => by
          refine (norm_mul_le _ _).trans ?_
          rw [Matrix.star_apply, norm_star, sq]
          exact mul_le_mul (hx i k) (hx j k) (norm_nonneg _) hC
      _ = a * C ^ 2 := by simp
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => ?_
    rw [Matrix.one_apply]
    split_ifs <;> simp

theorem fieldDer : FieldDer := by
  intro E _ _ _ a U Y C h
  choose φ hφ hb using h.sm
  choose B hB0 hB using fun i j w => lie_bound (hb i j w)
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective (HV E a).subtype (Submodule.ker_subtype _)
  have hP' : ∀ v : HV E a, LinearMap.toContinuousLinearMap P v.1 = v := fun v => LinearMap.congr_fun hP v
  let B' : Lie E a := fun i j w => (B i j w : ℂ)
  have hle : ∀ i j w, B i j w ≤ ‖B'‖ := fun i j w =>
    calc B i j w ≤ ‖B' i j w‖ := by simpa [B'] using le_abs_self _
      _ ≤ ‖B'‖ := ((norm_le_pi_norm (B' i j) w).trans (norm_le_pi_norm (B' i) j)).trans (norm_le_pi_norm B' i)
  refine ⟨max (a * C ^ 2 + 1) (‖LinearMap.toContinuousLinearMap P‖ * ‖B'‖), le_max_of_le_left (by positivity),
    fun g => ⟨le_max_of_le_left (val_bound h g), fun c X h0 hX => ?_⟩⟩
  let D : Lie E a := fun i j w => (lie E a X (φ i j w)).1 g
  have hD : HasDerivAt (fun t => (hv (Y (g * infGL E a (c t)))).1) D 0 :=
    hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w =>
      (hasDerivAt_curve (φ i j w) g c X h0 hX).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => (hφ i j w _).symm)
  have hn : ‖D‖ ≤ ‖B'‖ * ‖X‖ := by
    have hp : 0 ≤ ‖B'‖ * ‖X‖ := by positivity
    exact (pi_norm_le_iff_of_nonneg hp).2 fun i => (pi_norm_le_iff_of_nonneg hp).2 fun j =>
      (pi_norm_le_iff_of_nonneg hp).2 fun w =>
        (hB i j w X g).trans (mul_le_mul_of_nonneg_right (hle i j w) (norm_nonneg _))
  refine ⟨LinearMap.toContinuousLinearMap P D, ?_, ?_⟩
  · refine ((LinearMap.toContinuousLinearMap P).le_opNorm_of_le hn).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · exact ((LinearMap.toContinuousLinearMap P).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => (hP' _).symm)

end UpperTheory.V.Lit.Geo
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldSm
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open scoped ContDiff

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem sub_smooth {f : X → HV E a} {x : X} (h : ContDiffAt ℝ ∞ (fun y => (f y).1) x) :
    ContDiffAt ℝ ∞ f x := by
  obtain ⟨r, hr⟩ := (HV E a).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  have e : f = fun y => LinearMap.toContinuousLinearMap r (f y).1 :=
    funext fun y => (LinearMap.congr_fun hr (f y)).symm
  rw [e]
  exact (LinearMap.toContinuousLinearMap r).contDiff.contDiffAt.comp x h

private theorem sand_smooth {σ : X → GL (Fin a) (Cinf E)} {v : X → HV E a} {x : X}
    (h : ∀ i j, ContDiffAt ℝ ∞ (fun y => (σ y).val i j) x) (hv : ∀ i j, ContDiffAt ℝ ∞ (fun y => (v y).1 i j) x) :
    ContDiffAt ℝ ∞ (fun y => sand (σ y) (v y)) x := by
  refine sub_smooth (contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_)
  have e : (fun y => (sand (σ y) (v y)).1 i j) =
      fun y => ∑ l, (∑ k, (σ y).val i k * (v y).1 k l) * star ((σ y).val j l) := by
    funext y
    change ((σ y).val * Matrix.of (v y).1 * star (σ y).val) i j = _
    simp [Matrix.mul_apply]
  rw [e]
  refine ContDiffAt.sum fun l _ => (ContDiffAt.sum fun k _ => (h i k).mul (hv k l)).mul ?_
  exact (starL' ℝ : Cinf E ≃L[ℝ] Cinf E).contDiff.contDiffAt.comp x (h j l)

end UpperTheory.V.Lit.Geo

open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.fieldSm :
    FieldSm := by
  intro E _ _ _ a U Y C hY W hW s p₀ hp₀
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨τ, hτ, hs⟩ := locSec E a p₀ hp₀
  refine ContDiffAt.contDiffWithinAt ?_
  have h1 : ContDiffAt ℝ ∞ (fun p => sand (τ p) (hv (Y (infGL E a (τ p) * finGL E a x)))) p₀ := by
    refine sand_smooth (fun i j => contDiffAt_pi.1 (contDiffAt_pi.1 hτ i) j) fun i j => contDiffAt_pi.2 fun w => ?_
    obtain ⟨φ, hφ, -⟩ := hY.sm i j w
    have := (contDiffAt_chart φ.2 (finGL E a x) (val_mem_invSet (τ p₀))).comp p₀ hτ
    simp only [Function.comp_def, chart_val, hφ] at this
    simp only [infGL_comm]
    exact this
  refine h1.congr_of_eventuallyEq (hs.mono fun p hp => ?_)
  have := hW (τ p) x
  rwa [hp] at this
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHkSmooth
section
noncomputable section

open scoped ContDiff Topology

namespace UpperTheory.V.Lit.Geo

theorem hkSmooth : HkSmooth := by
  intro V F _ _ _ _ _ _ Y hY W hW q w hw
  have hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    exact_mod_cast le_top
  have hWat : ∀ p ∈ Y, ContDiffAt ℝ ∞ W p := fun p hp => hW.1.contDiffAt (hY.mem_nhds hp)
  have hwat : ∀ p ∈ Y, ContDiffAt ℝ ∞ w p := fun p hp => hw.contDiffAt (hY.mem_nhds hp)
  have hfd : ∀ p ∈ Y, ∀ t : ℝ, fderiv ℝ (flow W t) p = ContinuousLinearMap.id ℝ V + t • fderiv ℝ W p := by
    intro p hp t
    have hd : DifferentiableAt ℝ W p := (hWat p hp).differentiableAt (by simp)
    exact ((hasFDerivAt_id p).add (hd.hasFDerivAt.const_smul t)).fderiv
  have hflowc : ∀ z : V × ℝ, z.1 ∈ Y → ContDiffAt ℝ ∞ (fun y : V × ℝ => flow W y.2 y.1) z := by
    intro z hz
    exact contDiffAt_fst.add (contDiffAt_snd.smul ((hWat z.1 hz).comp z contDiffAt_fst))
  have hSo : IsOpen {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y} := by
    have h := ContinuousOn.isOpen_inter_preimage (f := fun y : V × ℝ => flow W y.2 y.1)
      (s := Prod.fst ⁻¹' Y) (t := Y) ?_ (hY.preimage continuous_fst) hY
    · exact h
    · intro z hz
      exact (hflowc z hz).continuousAt.continuousWithinAt
  have hsm : ContDiffOn ℝ ∞ (fun z : V × ℝ => hk W z.2 w z.1) {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y} := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    apply UpperTheory.V.Lit.Dr.altSmooth (V × ℝ) V F q
    intro v
    have hf : ContDiffAt ℝ ∞ (fun y : V × ℝ => w (flow W y.2 y.1)) z := (hwat _ hz.2).comp z (hflowc z hz.1)
    have hu : ∀ i : Fin (q + 1), ContDiffAt ℝ ∞ ((Fin.cons (fun y : V × ℝ => W y.1)
        (fun (j : Fin q) (y : V × ℝ) => v j + y.2 • fderiv ℝ W y.1 (v j)) : Fin (q + 1) → V × ℝ → V) i) z := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        exact (hWat z.1 hz.1).comp z contDiffAt_fst
      · simp only [Fin.cons_succ]
        exact contDiffAt_const.add (contDiffAt_snd.smul
          ((((hWat z.1 hz.1).fderiv_right hinf).comp z contDiffAt_fst).clm_apply contDiffAt_const))
    have h3 := UpperTheory.V.Lit.Dr.applySmooth (V × ℝ) V F (q + 1) (fun y : V × ℝ => w (flow W y.2 y.1))
      (Fin.cons (fun y : V × ℝ => W y.1)
        (fun (j : Fin q) (y : V × ℝ) => v j + y.2 • fderiv ℝ W y.1 (v j)) : Fin (q + 1) → V × ℝ → V) z hf hu
    apply h3.congr_of_eventuallyEq
    have hnb : {y : V × ℝ | y.1 ∈ Y} ∈ 𝓝 z := (hY.preimage continuous_fst).mem_nhds hz.1
    filter_upwards [hnb] with y hy
    simp only [hk, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply, hfd y.1 hy y.2]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  have hmaps : ∀ p ∈ Y, ∀ t ∈ Set.Icc (0 : ℝ) 1, (p, t) ∈ {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y} :=
    fun p hp t ht => ⟨hp, hW.2 p hp t ht⟩
  refine ⟨hSo, hsm, ?_, ?_⟩
  · intro p hp
    have hc : ContinuousOn ((fun z : V × ℝ => hk W z.2 w z.1) ∘ (fun t : ℝ => (p, t))) (Set.Icc 0 1) :=
      hsm.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => hmaps p hp t ht)
    simpa [Function.comp_def] using hc
  · have h4 := UpperTheory.V.Lit.Dr.paramSmooth V (V [⋀^Fin q]→L[ℝ] F) Y {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y}
      (fun z => hk W z.2 w z.1) hY hSo (fun z hz => hmaps z.1 hz.1 z.2 hz.2) hsm
    exact h4

end UpperTheory.V.Lit.Geo
end
end

