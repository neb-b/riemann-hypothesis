module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0714
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRegularSequenceOfCommonZeros
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.HSCore GlobalTheory.QCoh RingTheory.Sequence

namespace GlobalTheory.RegBasis

section General

variable {X : Scheme.{0}} {L : LB X} {k : Type} [Field k] [Algebra k Γ(X, ⊤)] {V : Type} [AddCommGroup V]
  [Module k V] (φ : V →ₛₗ[algebraMap k Γ(X, ⊤)] L.Sec)

def vanishAt (x : X) : Submodule k V where
  carrier := {w | x ∉ nonzeroLocus (φ w)}
  add_mem' := fun {a b} ha hb hx => by
    rw [map_add (f := _)] at hx
    exact (nonzeroLocus_add_le _ _ hx).elim ha hb
  zero_mem' := fun hx => by
    rw [map_zero] at hx
    exact nonzeroLocus_secZero.le hx
  smul_mem' := fun c a ha hx => by
    rw [φ.map_smulₛₗ] at hx
    exact ha ((nonzeroLocus_secScale _ _).le hx).2

theorem vanishAt_eq_top {ι : Type} {v : ι → V} (hv : Submodule.span k (Set.range v) = ⊤) {x : X}
    (hx : ∀ i, x ∉ nonzeroLocus (φ (v i))) : vanishAt φ x = ⊤ :=
  top_le_iff.1 (hv.ge.trans (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hx i)))

theorem exists_regSeq [Infinite k] [Module.Finite k V] [AlgebraicGeometry.IsNoetherian X] (hL : L.IsLB)
    (c : X → L.ι) (hc : ∀ x, x ∈ L.U (c x)) (m : ℕ) (F : X.Modules) [IsFiniteQC F] (W : Submodule k V)
    (hW : Module.finrank k W + m = Module.finrank k V)
    (h : ∀ v : Fin m → V, W ⊔ Submodule.span k (Set.range v) = ⊤ → ∀ x, vanishAt φ x = ⊤ →
      IsWeaklyRegular (F.presheaf.stalk x :) (List.ofFn fun i => X.presheaf.germ _ x (hc x) ((φ (v i)).f (c x)))) :
    ∃ v : Fin m → V, W ⊔ Submodule.span k (Set.range v) = ⊤ ∧ RegSeq hL F (List.ofFn fun i => φ (v i)) := by
  induction m generalizing F W with
  | zero =>
    refine ⟨Fin.elim0, ?_, by rw [List.ofFn_zero]; trivial⟩
    rw [Submodule.eq_top_of_finrank_eq hW, top_sup_eq]
  | succ m ih =>
    have hne : W ≠ ⊤ := fun e => by
      rw [e, finrank_top] at hW
      omega
    have : Finite {x : X // x ∈ assPoints F ∧ vanishAt φ x ≠ ⊤} :=
      ((finite_assPoints F).subset (t := {x : X | x ∈ assPoints F ∧ vanishAt φ x ≠ ⊤})
        (fun _ hx => hx.1)).to_subtype
    obtain ⟨w, hw⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
      (fun o : Option {x : X // x ∈ assPoints F ∧ vanishAt φ x ≠ ⊤} => o.elim W fun x => vanishAt φ x.1)
      (by
        rintro (_ | x)
        exacts [hne, x.2.2])
    have hsup : ∀ v : Fin m → V, W ⊔ Submodule.span k {w} ⊔ Submodule.span k (Set.range v) =
        W ⊔ Submodule.span k (Set.range (Fin.cons w v : Fin (m + 1) → V)) := fun v => by
      rw [Fin.range_cons, Submodule.span_insert, sup_assoc]
    have key : ∀ v : Fin m → V, W ⊔ Submodule.span k {w} ⊔ Submodule.span k (Set.range v) = ⊤ →
        ∀ x, vanishAt φ x = ⊤ → IsWeaklyRegular (F.presheaf.stalk x :)
          (X.presheaf.germ _ x (hc x) ((φ w).f (c x)) ::
            List.ofFn fun i => X.presheaf.germ _ x (hc x) ((φ (v i)).f (c x))) := fun v hv x hx => by
      have := h (Fin.cons w v) ((hsup v).symm.trans hv) x hx
      rwa [List.ofFn_succ] at this
    obtain ⟨v, hv, hr⟩ := ih (cut F hL (φ w)) (W ⊔ Submodule.span k {w})
      (by rw [Submodule.finrank_sup_span_singleton (p := W) (hw none)]; omega) fun v hv x hx => by
        obtain ⟨q⟩ := CutDegree.nonempty_stalk_cut_equiv F hL (φ w) (c x) (hc x)
        exact (q.isWeaklyRegular_congr _).1 ((isWeaklyRegular_cons_iff _ _ _).1 (key v hv x hx)).2
    refine ⟨Fin.cons w v, (hsup v).symm.trans hv, ?_⟩
    rw [List.ofFn_succ]
    refine (regSeq_cons hL F _ _).2 ⟨(mono_cutHom_iff F hL _).2 fun x hx => ?_, hr⟩
    by_cases e : vanishAt φ x = ⊤
    · have hreg := ((isWeaklyRegular_cons_iff _ _ _).1 (key v hv x e)).1
      obtain ⟨t, ht⟩ := mem_assPoints_iff_exists.1 hx
      refine (Cartier.mem_nonzeroLocus_iff (φ w) (c x) (hc x)).2 ((X.mem_basicOpen _ x (hc x)).2 ?_)
      by_contra hu
      have h0 : t = 0 := hreg (((ht _).2 hu).trans (smul_zero _).symm)
      exact (ht 1).1 (by rw [h0, smul_zero]) isUnit_one
    · exact not_not.1 (hw (some ⟨x, hx, e⟩))

theorem nonempty_stalk_toMod {B : LB X} (hB : B.IsLB) (x : X) :
    Nonempty (((LB.toMod B).presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x) := by
  obtain ⟨e⟩ := Twist.nonempty_stalkEquiv (F := structureModule X) hB x
  let i : twist (structureModule X) B ≅ LB.toMod B := Twist.unitTwistIso B
  exact ⟨(LinearEquiv.ofBijective (stalkLinear i.hom x)
    ⟨stalkLinear_injective _ x, stalkLinear_surjective _ x⟩).symm ≪≫ₗ e ≪≫ₗ structureModuleStalkEquiv x⟩

end General

def combMap {k : Type} [Field k] (S : LinSys k) {D : ℕ} (s : Fin D → Fin S.N → k) :
    (Fin D → k) →ₛₗ[algebraMap k Γ(S.Y, ⊤)] S.L.Sec where
  toFun c := S.comb (∑ j, c j • s j)
  map_add' a b := by
    simp only [LinSys.comb, Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add (f := _)]
  map_smul' a b := by
    simp only [LinSys.comb, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_mul]

theorem exists_regular_basis : ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (s : Fin G.D → Fin G.N → K),
    G.IsGood s → ∀ B : LB G.Y, B.IsLB → ∃ g : Matrix (Fin G.D) (Fin G.D) K, IsUnit g.det ∧
      RegSeq G.isLB (GlobalTheory.LB.toMod B) (List.ofFn fun i => G.comb (∑ j, g i j • s j)) := by
  intro K _ _ G s hs B hB
  have hp := G.geom.alg.variety.proj
  have := isNoetherian_of_isProjOver hp
  have : IsFiniteQC (LB.toMod B) := isFiniteQC_iff_isFiniteType.2 ⟨LB.isQuasicoherent_toMod hB, LB.isFiniteType_toMod hB⟩
  have hfin : ((G.ideal s).support : Set G.Y).Finite := by
    have := hs.finite
    have h := ((G.ideal s).subschemeι ≫ G.str).finite_preimage_singleton (IsLocalRing.closedPoint K)
    rw [← Scheme.IdealSheafData.range_subschemeι, ← Set.image_univ]
    exact (h.subset fun z _ => Subsingleton.elim (α := PrimeSpectrum K) _ _).image _
  obtain ⟨v, hv, hr⟩ := exists_regSeq (combMap G.toLinSys s) G.isLB G.chartAt G.mem_chartAt G.D (LB.toMod B) ⊥
    (by simp) fun v hv x hx => by
      rw [bot_sup_eq] at hv
      obtain ⟨q⟩ := nonempty_stalk_toMod hB x
      refine (q.isWeaklyRegular_congr _).2 ((ProperCut.topSelf_eq_length_of_smooth G.str G.smooth hp G.isLB
        (fun i => combMap G.toLinSys s (v i)) (hfin.subset fun y hy => ?_)).2.1 x ?_ _ _).toIsWeaklyRegular
      · have e := vanishAt_eq_top _ hv ((mem_support_cutIdeal _ _ y).1 hy)
        refine (mem_support_cutIdeal _ _ y).2 fun i => ?_
        have h : y ∉ nonzeroLocus (G.comb (∑ j, (Pi.single i 1 : Fin G.D → K) j • s j)) :=
          e.ge (Submodule.mem_top (x := Pi.single i 1))
        simpa [Pi.single_apply] using h
      · exact (mem_support_cutIdeal _ _ x).2 fun i => hx.ge (Submodule.mem_top (x := v i))
  rw [bot_sup_eq] at hv
  refine ⟨Matrix.of v, (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1
    (linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simp))), hr⟩

end GlobalTheory.RegBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenSubgroupSubsetNhdsOne
section
open NumberField MeasureTheory Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.GLFin

namespace GlobalTheory.GLFinSmall

open Set Filter Pointwise Topology

theorem exists_nhds_mul_subset {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {W : Set G} (hWc : IsCompact W) (hWo : IsOpen W) : ∃ T ∈ 𝓝 (1 : G), W * T ⊆ W := by
  apply hWc.induction_on (p := fun S ↦ ∃ T ∈ 𝓝 (1 : G), S * T ⊆ W)
    ⟨Set.univ, by simp only [univ_mem, Set.empty_mul, empty_subset, and_self]⟩
    (fun _ _ huv ⟨T, hT, mem⟩ ↦ ⟨T, hT, (mul_subset_mul_right huv).trans mem⟩)
    fun U V ⟨T₁, hT₁, mem1⟩ ⟨T₂, hT₂, mem2⟩ ↦ ⟨T₁ ∩ T₂, inter_mem hT₁ hT₂, by
      rw [union_mul]
      exact union_subset (mul_subset_mul_left inter_subset_left |>.trans mem1)
        (mul_subset_mul_left inter_subset_right |>.trans mem2)⟩
  intro x memW
  have : (x, 1) ∈ (fun p : G × G ↦ p.1 * p.2) ⁻¹' W := by simp [memW]
  rcases isOpen_prod_iff.mp (continuous_mul.isOpen_preimage W hWo) x 1 this with
    ⟨U, V, Uopen, Vopen, xmemU, onememV, prodsub⟩
  have h6 : U * V ⊆ W := mul_subset_iff.mpr (fun _ hx _ hy ↦ prodsub (mk_mem_prod hx hy))
  exact ⟨U ∩ W, ⟨U, Uopen.mem_nhds xmemU, W, fun _ a ↦ a, rfl⟩,
    V, IsOpen.mem_nhds Vopen onememV, fun _ a ↦ h6 ((mul_subset_mul_right inter_subset_left) a)⟩

def rightStab {G : Type} [Group G] (W : Set G) : Subgroup G where
  carrier := {g | ∀ w, w ∈ W ↔ w * g ∈ W}
  one_mem' := by intro w; simp
  mul_mem' := by
    intro g h hg hh w
    rw [hg w, hh (w * g), mul_assoc]
  inv_mem' := by
    intro g hg w
    rw [hg (w * g⁻¹), inv_mul_cancel_right]

theorem exists_compact_open_subgroup_subset {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {W : Set G} (hWc : IsCompact W) (hWo : IsOpen W) (h1 : (1 : G) ∈ W) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ IsCompact (U : Set G) ∧ (U : Set G) ⊆ W := by
  obtain ⟨T, hT, hTW⟩ := exists_nhds_mul_subset hWc hWo
  have hsub : T ∩ T⁻¹ ⊆ (rightStab W : Set G) := by
    intro v hv w
    constructor
    · intro hw; exact hTW (Set.mul_mem_mul hw hv.1)
    · intro hw
      have : w * v * v⁻¹ ∈ W := hTW (Set.mul_mem_mul hw (Set.mem_inv.mp hv.2))
      simpa using this
  have hnhds : (rightStab W : Set G) ∈ 𝓝 (1 : G) :=
    Filter.mem_of_superset (inter_mem hT (inv_mem_nhds_one G hT)) hsub
  have hopen : IsOpen (rightStab W : Set G) := Subgroup.isOpen_of_mem_nhds _ hnhds
  have hW : (rightStab W : Set G) ⊆ W := by
    intro g hg
    have := (hg 1).mp h1
    simpa using this
  refine ⟨rightStab W, hopen, ?_, hW⟩
  exact hWc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hopen) hW

end GlobalTheory.GLFinSmall

theorem GlobalTheory.GLFin.exists_compact_open_subgroup_subset_nhds_one :
    ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (B : Set (GL (Fin a) (Af E))),
      B ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ U : Subgroup (GL (Fin a) (Af E)),
        IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧
          (U : Set (GL (Fin a) (Af E))) ⊆ B := by
  intro E _ _ a B hB
  obtain ⟨W, hWo, hWc, -, h1, hWB⟩ := GlobalTheory.T.exists_compact_clopen_nhds_one_GL_finiteAdeles E a B hB
  obtain ⟨U, hUo, hUc, hUW⟩ := GlobalTheory.GLFinSmall.exists_compact_open_subgroup_subset hWc hWo h1
  exact ⟨U, hUo, hUc, hUW.trans hWB⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothin
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory.AutGrowth.ApproxId

theorem tendsto_integral_of_concentrate {V : Type} [NormedAddCommGroup V] [MeasurableSpace V] {ν : Measure V}
    {f : V → ℂ} {x₀ : V} (hf : ContinuousAt f x₀) (β : ℕ → V → ℝ) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (h0 : ∀ n x, 0 ≤ β n x) (h1 : ∀ n, ∫ x, β n x ∂ν = 1) (hs : ∀ n x, β n x ≠ 0 → dist x x₀ < r n)
    (hi : ∀ n, Integrable (β n) ν) (hfi : ∀ n, Integrable (fun x => (β n x : ℂ) * f x) ν) :
    Tendsto (fun n => ∫ x, (β n x : ℂ) * f x ∂ν) atTop (𝓝 (f x₀)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.1 hf (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hr) δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have hrn : r n < δ := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have e1 : ∫ x, (β n x : ℂ) * f x₀ ∂ν = f x₀ := by
    rw [integral_mul_const, integral_complex_ofReal, h1 n]; simp
  have e2 : ∫ x, (β n x : ℂ) * f x ∂ν - f x₀ = ∫ x, (β n x : ℂ) * (f x - f x₀) ∂ν := by
    conv_lhs => rw [← e1]
    refine (integral_sub (hfi n) ((hi n).ofReal.mul_const (f x₀))).symm.trans ?_
    congr 1; funext x; rw [mul_sub]; rfl
  rw [dist_eq_norm, e2]
  calc ‖∫ x, (β n x : ℂ) * (f x - f x₀) ∂ν‖ ≤ ∫ x, β n x * (ε / 2) ∂ν := by
        refine norm_integral_le_of_norm_le ((hi n).mul_const _) (.of_forall fun x => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 n x)]
        by_cases hx : β n x = 0
        · simp [hx]
        · exact mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact (hfδ ((hs n x hx).trans hrn)).le) (h0 n x)
    _ = ε / 2 := by rw [integral_mul_const, h1 n, one_mul]
    _ < ε := half_lt_self hε

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem sum_norm_sq_eq (N : Matrix (Fin a) (Fin a) (Cinf E)) (w : InfinitePlace E) :
    ∑ i, ∑ j, ‖N i j w‖ ^ 2 = (Matrix.trace (star N * N) w).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, Finset.sum_apply, Pi.mul_apply,
    Pi.star_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem trace_star_mul_conj (k : Kinf E a) (N : Matrix (Fin a) (Fin a) (Cinf E)) :
    Matrix.trace (star ((k : Matrix (Fin a) (Fin a) (Cinf E)) * N * star (k : Matrix (Fin a) (Fin a) (Cinf E))) *
      ((k : Matrix (Fin a) (Fin a) (Cinf E)) * N * star (k : Matrix (Fin a) (Fin a) (Cinf E)))) =
      Matrix.trace (star N * N) := by
  have h1 : star (k : Matrix (Fin a) (Fin a) (Cinf E)) * k = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
  set K : Matrix (Fin a) (Fin a) (Cinf E) := ↑k
  have e : star (K * N * star K) * (K * N * star K) = K * (star N * N * star K) := by
    rw [star_mul, star_mul, star_star]
    calc K * (star N * star K) * (K * N * star K) = K * star N * (star K * K) * N * star K := by
          simp only [mul_assoc]
      _ = K * (star N * N * star K) := by rw [h1, mul_one]; simp only [mul_assoc]
  rw [e, Matrix.trace_mul_comm, mul_assoc, h1, mul_one]


variable (E a) in
def frobSq (x : Lie E a) : ℝ := ∑ w, ∑ i, ∑ j, ‖x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2

omit [_root_.NumberField.IsTotallyComplex E] in
theorem frobSq_eq (x : Lie E a) :
    frobSq E a x = ∑ w, ((Matrix.trace (star (Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) *
      (Matrix.of x - 1)) : Cinf E) w).re := by
  rw [frobSq]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← sum_norm_sq_eq]
  rfl


omit [_root_.NumberField.IsTotallyComplex E] in
theorem frobSq_conj (k : Kinf E a) (x : Lie E a) :
    frobSq E a (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x *
      ((star k : Kinf E a) : Matrix (Fin a) (Fin a) (Cinf E)))) = frobSq E a x := by
  have h2 : (k : Matrix (Fin a) (Fin a) (Cinf E)) * star (k : Matrix (Fin a) (Fin a) (Cinf E)) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 k.2
  have e : Matrix.of (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x *
      ((star k : Kinf E a) : Matrix (Fin a) (Fin a) (Cinf E)))) - 1 =
      (k : Matrix (Fin a) (Fin a) (Cinf E)) * (Matrix.of x - 1) * star (k : Matrix (Fin a) (Fin a) (Cinf E)) := by
    rw [Unitary.coe_star, mul_sub, sub_mul, mul_one, h2]
    rfl
  rw [frobSq_eq, frobSq_eq, e, trace_star_mul_conj]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem contDiff_frobSq : ContDiff ℝ ∞ (frobSq E a) := by
  unfold frobSq
  refine ContDiff.sum fun w _ => ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact (contDiff_norm_sq ℝ).comp
    (((contDiff_apply ℝ (fun _ => ℂ) w).comp ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ i))).sub contDiff_const)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem frobSq_one : frobSq E a (oneL E a) = 0 := by
  simp [frobSq]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_sq_le_frobSq (x : Lie E a) (i j : Fin a) (w : InfinitePlace E) :
    ‖x i j w - oneL E a i j w‖ ^ 2 ≤ frobSq E a x := by
  unfold frobSq
  refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ i, ∑ j,
    ‖x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2) (fun w _ => by positivity) (Finset.mem_univ w))
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j,
    ‖x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ‖x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ j)


variable (E a) in
def bumpR (m : ℝ) (x : Lie E a) : ℝ := Real.smoothTransition (1 - m ^ 2 * frobSq E a x)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem contDiff_bumpR (m : ℝ) : ContDiff ℝ ∞ (bumpR E a m) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_frobSq))

omit [_root_.NumberField.IsTotallyComplex E] in
theorem bumpR_nonneg (m : ℝ) (x : Lie E a) : 0 ≤ bumpR E a m x := Real.smoothTransition.nonneg _

omit [_root_.NumberField.IsTotallyComplex E] in
theorem bumpR_one (m : ℝ) : bumpR E a m (oneL E a) = 1 := by
  simp [bumpR, frobSq_one]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem dist_lt_of_bumpR_ne_zero {m : ℝ} (hm : 0 < m) {x : Lie E a} (h : bumpR E a m x ≠ 0) :
    dist x (oneL E a) < 1 / m := by
  have h1 : m ^ 2 * frobSq E a x < 1 := by
    by_contra hc
    exact h (Real.smoothTransition.zero_of_nonpos (by linarith))
  have hr : 0 < 1 / m := one_div_pos.2 hm
  rw [dist_pi_lt_iff hr]; intro i
  rw [dist_pi_lt_iff hr]; intro j
  rw [dist_pi_lt_iff hr]; intro w
  rw [Complex.dist_eq]
  have h2 := norm_sq_le_frobSq x i j w
  have h3 : (m * ‖x i j w - oneL E a i j w‖) ^ 2 < 1 := by
    rw [mul_pow]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h2 (by positivity)) h1
  have h4 : m * ‖x i j w - oneL E a i j w‖ < 1 := by
    have := abs_lt_of_sq_lt_sq' (h3.trans_eq (one_pow 2).symm) zero_le_one
    exact this.2
  rw [lt_div_iff₀ hm]
  linarith

omit [_root_.NumberField.IsTotallyComplex E] in
theorem bumpR_conj (m : ℝ) (k : Kinf E a) (x : Lie E a) :
    bumpR E a m (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x *
      ((star k : Kinf E a) : Matrix (Fin a) (Fin a) (Cinf E)))) = bumpR E a m x := by
  simp only [bumpR, frobSq_conj]

end GlobalTheory.AutGrowth.ApproxId

namespace GlobalTheory.AutGrowth.ApproxId

theorem exists_approx_identity : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure], ∃ α : ℕ → Lie E a → ℂ,
      (∀ n, IsTest (invSet E a) (α n) ∧ KInv (α n)) ∧
      ∀ ψ ∈ Sm E a, ∀ g, Tendsto (fun n => smoothing ν (α n) ψ g) atTop (𝓝 (ψ g)) := by
  intro E _ _ _ a ν _
  have : ProperSpace (Lie E a) := FiniteDimensional.proper ℝ _
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_invSet (E := E) (a := a)) (oneL E a) isUnit_one
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  let m : ℕ → ℝ := fun n => (n : ℝ) + N + 1
  have hm : ∀ n, 0 < m n := fun n => by positivity
  have hmN : ∀ n, 1 / m n < ε := fun n =>
    lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by simp [m])) hN
  have hsub : ∀ n, Metric.closedBall (oneL E a) (1 / m n) ⊆ invSet E a := fun n =>
    (Metric.closedBall_subset_ball (hmN n)).trans hball
  have hsupp : ∀ n, Function.support (bumpR E a (m n)) ⊆ Metric.closedBall (oneL E a) (1 / m n) :=
    fun n x hx => Metric.mem_closedBall.2 (dist_lt_of_bumpR_ne_zero (hm n) hx).le
  have hcs : ∀ n, HasCompactSupport (bumpR E a (m n)) := fun n =>
    HasCompactSupport.intro (isCompact_closedBall (oneL E a) (1 / m n)) fun x hx => by
      by_contra h; exact hx (hsupp n h)
  have hpos : ∀ n, 0 < ∫ x, bumpR E a (m n) x ∂ν := fun n =>
    (contDiff_bumpR (m n)).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (hcs n)
      (fun x => bumpR_nonneg _ x) (x := oneL E a) (by rw [bumpR_one]; norm_num)
  let β : ℕ → Lie E a → ℝ := fun n x => (∫ y, bumpR E a (m n) y ∂ν)⁻¹ * bumpR E a (m n) x
  have hβs : ∀ n x, β n x ≠ 0 → dist x (oneL E a) < 1 / m n := fun n x h =>
    dist_lt_of_bumpR_ne_zero (hm n) (right_ne_zero_of_mul h)
  have hβc : ∀ n, ContDiff ℝ ∞ (β n) := fun n => contDiff_const.mul (contDiff_bumpR _)
  have hβcs : ∀ n, HasCompactSupport (β n) := fun n => (hcs n).mul_left
  have hT : ∀ n, IsTest (invSet E a) (fun x => (β n x : ℂ)) := fun n => by
    refine ⟨Complex.ofRealCLM.contDiff.comp (hβc n), ?_, ?_⟩
    · exact HasCompactSupport.intro (isCompact_closedBall (oneL E a) (1 / m n)) fun x hx => by
        by_contra h
        exact hx (Metric.mem_closedBall.2 (hβs n x (fun h' => h (by simp [h']))).le)
    · refine (closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall).trans (hsub n)
      exact Metric.mem_closedBall.2 (hβs n x (fun h' => hx (by simp [h']))).le
  refine ⟨fun n x => (β n x : ℂ), fun n => ⟨hT n, fun k x => ?_⟩, fun ψ hψ g => ?_⟩
  · simp only [β, bumpR_conj]
  · have hv : chart ψ g (oneL E a) = ψ g := by
      have := chart_val ψ g 1
      simpa using this
    have hf : ContinuousAt (chart ψ g) (oneL E a) := (contDiffAt_chart hψ g isUnit_one).continuousAt
    have hr : Tendsto (fun n => 1 / m n) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (one_div_pos.2 (hm n)).le) (fun n => ?_)
      exact one_div_le_one_div_of_le (by positivity) (by simp [m])
    have h1 : ∀ n, ∫ x, β n x ∂ν = 1 := fun n => by
      simp only [β]
      rw [integral_const_mul, inv_mul_cancel₀ (hpos n).ne']
    have key := tendsto_integral_of_concentrate hf β (fun n => 1 / m n) hr
      (fun n x => mul_nonneg (inv_nonneg.2 (hpos n).le) (bumpR_nonneg _ x)) h1 hβs
      (fun n => (hβc n).continuous.integrable_of_hasCompactSupport (hβcs n))
      (fun n => (hT n).integrable_mul ν isOpen_invSet (hψ g).continuousOn)
    rw [hv] at key
    exact key

end GlobalTheory.AutGrowth.ApproxId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainRationalBlockUnipotentGL
section
noncomputable section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open Topology

namespace GlobalTheory.CuspRep

theorem discreteTopology_ratN (E : Type) [Field E] [NumberField E] (a s : ℕ) :
    DiscreteTopology (ratN E a s) := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have hU : IsOpen (Set.univ.pi fun _ : BlockIx a s => Formalism.IndefR.Eqv.G5.adlNbhd (F := E)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => Formalism.IndefR.Eqv.G5.adl_isOpen_nbhd
  have h : ({0} : Set (ratN E a s)) =
      Subtype.val ⁻¹' (Set.univ.pi fun _ : BlockIx a s => Formalism.IndefR.Eqv.G5.adlNbhd (F := E)) := by
    ext ⟨x, q, hq⟩
    constructor
    · intro hx p _
      have : x = 0 := congrArg Subtype.val hx
      subst this
      exact Formalism.IndefR.Eqv.G5.adl_zero_mem_nbhd
    · intro hx
      subst hq
      apply Subtype.ext
      funext p
      have h0 : q p = 0 := Formalism.IndefR.Eqv.G5.adl_eq_zero_of_mem_nbhd (q p) (hx p (Set.mem_univ _))
      show algebraMap E (Ad E) (q p) = 0
      rw [h0, map_zero]
  rw [h]
  exact hU.preimage continuous_subtype_val

theorem exists_isAddFundamentalDomain_ratN : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (s : ℕ) [MeasurableSpace (BlockIx a s → Ad E)] [BorelSpace (BlockIx a s → Ad E)] (μ : Measure (BlockIx a s → Ad E)) [μ.IsAddHaarMeasure], ∃ 𝓕 : Set (BlockIx a s → Ad E), IsAddFundamentalDomain (ratN E a s) 𝓕 μ ∧ μ 𝓕 ≠ 0 ∧ μ 𝓕 < ⊤ := by
  intro E _ _ _ a s _ _ μ _
  haveI : SecondCountableTopology (Ad E) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := discreteTopology_ratN E a s
  haveI := countable_ratN (E := E) (a := a) s
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isAddFundamentalDomain_addSubgroup (ratN E a s)
  haveI : MeasurableConstVAdd (ratN E a s) (BlockIx a s → Ad E) :=
    ⟨fun γ => (continuous_const.add continuous_id :
      Continuous fun x : BlockIx a s → Ad E => (γ : BlockIx a s → Ad E) + x).measurable⟩
  haveI : VAddInvariantMeasure (ratN E a s) (BlockIx a s → Ad E) μ :=
    ⟨fun γ t _ => measure_preimage_add μ (γ : BlockIx a s → Ad E) t⟩
  have hμ : μ ≠ 0 := fun h => by
    have := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
    rw [h] at this
    exact this rfl
  exact ⟨D, hD μ, (hD μ).measure_ne_zero hμ, covol_lt_top μ D (hD μ)⟩

end GlobalTheory.CuspRep
end
end

