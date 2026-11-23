module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.GrpEqMemArchCompact
public import GroundTheory.AutomorphicForms.AdelicDixmierMalliavinProduct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0329
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.DelLev
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem lie_left (X : Lie E a) (φ : Sm E a) (h g : GA E a) (hφ : ∀ g, φ.1 (h * g) = φ.1 g) :
    (lie E a X φ).1 (h * g) = (lie E a X φ).1 g := by
  have e : chart φ.1 (h * g) =ᶠ[nhds (oneL E a)] chart φ.1 g := by
    filter_upwards [isOpen_invSet.mem_nhds (val_mem_invSet (1 : GL (Fin a) (Cinf E)))] with x hx
    obtain ⟨u, hu⟩ := hx
    obtain rfl : x = toL u.val := hu.symm
    rw [chart_val, chart_val, mul_assoc, hφ]
  change fderiv ℝ (chart φ.1 (h * g)) (oneL E a) X = fderiv ℝ (chart φ.1 g) (oneL E a) X
  rw [e.fderiv_eq]

private theorem lie_one_comm (X : Lie E a) (φ : Sm E a) :
    lie E a (oneL E a) (lie E a X φ) = lie E a X (lie E a (oneL E a) φ) := by
  have h := lie_comm (oneL E a) X
  have e : Matrix.of (oneL E a) * Matrix.of X = Matrix.of X * Matrix.of (oneL E a) :=
    (one_mul (Matrix.of X)).trans (mul_one (Matrix.of X)).symm
  rw [e, sub_self, sub_eq_zero] at h
  exact LinearMap.congr_fun h φ

private theorem level_lie {U : Subgroup (GL (Fin a) (Af E))} {Ξ : AlgRep E a} (X : Lie E a) (φ : Sm E a)
    (h : IsLevelFn U Ξ φ) : IsLevelFn U Ξ (lie E a X φ) := by
  refine ⟨fun γ g => lie_left X φ _ g (h.1 γ), fun u hu => ?_, fun m hm => ?_⟩
  · exact (LinearMap.congr_fun (lie_rt_fin X u) φ).symm.trans (congrArg (lie E a X) (h.2.1 u hu))
  · rw [lie_one_comm, h.2.2 m hm, map_smul]

private theorem adj_span (Ξ : AlgRep E a) (r : ℝ) (P : Sm E a → Prop) (hP : ∀ X φ, P φ → P (lie E a X φ)) (X : Lie E a)
    (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) (hm : m ∈ Submodule.span ℂ {x | ∃ φ v, P φ ∧ x = φ ⊗ₜ[ℂ] v}) :
    smAdj Ξ r X m ∈ Submodule.span ℂ {x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) | ∃ φ v, P φ ∧ x = φ ⊗ₜ[ℂ] v} := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, v, hφ, rfl⟩ := hx
    rw [smAdj, adj_apply, smA_apply, smB_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.subset_span ⟨_, _, hφ, rfl⟩)
      (Submodule.subset_span ⟨_, _, hP X φ hφ, rfl⟩))
      (Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨_, _, hφ, rfl⟩))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

private theorem k_adj (Ξ : AlgRep E a) (r : ℝ) (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    smK Ξ k * smAdj Ξ r (toL X) = smAdj Ξ r (toL (k.1 * X * star k.1)) * smK Ξ k := by
  obtain ⟨-, -, -, hA, hB, -⟩ := smAB E a Ξ
  refine LinearMap.ext fun m => ?_
  have h1 := LinearMap.congr_fun (hA k X) m
  have h2 := LinearMap.congr_fun (hB k X) m
  simp only [Module.End.mul_apply] at h1 h2 ⊢
  rw [smAdj, adj_apply, adj_apply, map_sub, map_sub, h1, h2, (ellFacts E a).2.2.1 k X, LinearMap.map_smul_of_tower]

end

theorem UpperTheory.V.Cj.H.delLev :
    UpperTheory.V.Cj.H.DelLev := by
  intro E _ _ _ a n e he U Ξ r q ω
  refine ⟨fun h => ⟨delCochain E a n e he _ _ _ (fun k X => k_adj Ξ r k X.1) q ω h.equiv, fun X i hi => ?_, fun X => ?_⟩,
    fun h X => ?_⟩
  · rw [del_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [h.basic (Matrix.vecCons (e j) X) i.succ hi, map_zero]
  · rw [del_apply]
    exact Submodule.sum_mem _ fun j _ => adj_span Ξ r _ level_lie _ _ (h.val _)
  · refine mem_tens.1 (span_le_tens (P := fun φ => φ ∈ sqSub E a r) (fun _ h => h) ?_)
    rw [del_apply]
    exact Submodule.sum_mem _ fun j _ => adj_span Ξ r _ ((sqLie E a r).2) _ _ (mem_span_of_cmp (h _))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.DmTest
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

variable (E a) in
private noncomputable def spl : GA E a ≃ₜ* archGroup E a × GL (Fin a) (Af E) where
  toMulEquiv := (AdelicGLn.prodEquiv E a).toMulEquiv.trans
    (MulEquiv.prodCongr (archEquiv E a).toMulEquiv (MulEquiv.refl _))
  continuous_toFun := ((archEquiv E a).continuous.prodMap continuous_id).comp (AdelicGLn.prodEquiv E a).continuous
  continuous_invFun := (AdelicGLn.prodEquiv E a).symm.continuous.comp
    ((archEquiv E a).symm.continuous.prodMap continuous_id)

private theorem spl_symm (x : archGroup E a) (b : GL (Fin a) (Af E)) :
    (spl E a).symm (x, b) = finEmb E a b * infEmb E a x := by
  refine (AdelicGLn.prodEquiv E a).injective ?_
  rw [map_mul, prodEquiv_infEmb, prodEquiv_finEmb, Prod.mk_mul_mk, one_mul, mul_one]
  exact (AdelicGLn.prodEquiv E a).apply_symm_apply _

private theorem spl_fin (b : GL (Fin a) (Af E)) : (spl E a).symm (1, b) = finGL E a b := by
  rw [spl_symm, map_one, mul_one, UpperTheory.V.Fb.finEmb_eq]

private theorem arch_iff (φ : GA E a → ℂ) :
    IsArchSmooth φ ↔ ∀ b, (isExpLieAlgebra E a).IsSmoothFun fun x => φ ((spl E a).symm (x, b)) := by
  simp only [spl_symm]
  refine ⟨fun h b => h (finEmb E a b), fun h g => ?_⟩
  rw [← infEmb_mul_finEmb g, infEmb_mul_finEmb_comm, archSlice_mul]
  exact ((isExpLieAlgebra E a).leftTranslateEnd _ ⟨_, h _⟩).2

variable [_root_.NumberField.IsTotallyComplex E]

private def stab (φ : Sm E a) : Subgroup (GL (Fin a) (Af E)) where
  carrier := {k | ∀ g, φ.1 (g * finGL E a k) = φ.1 g}
  one_mem' := fun g => by rw [map_one, mul_one]
  mul_mem' := fun {k l} hk hl g => by rw [map_mul, ← mul_assoc, hl, hk]
  inv_mem' := fun {k} hk g => by
    rw [← hk (g * finGL E a k⁻¹), mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

private theorem lev_iff (φ : Sm E a) : HasLev φ ↔ IsOpen (stab φ : Set (GL (Fin a) (Af E))) := by
  have : {k | act (.fin k) φ = φ} = (stab φ : Set (GL (Fin a) (Af E))) := by
    ext k
    exact ⟨fun h g => congrFun (congrArg Subtype.val h) g, fun h => Subtype.ext (funext h)⟩
  rw [HasLev, this]

private theorem smooth_of (φ : Sm E a) (h : HasLev φ) :
    ProdSmooth.IsSmooth (isExpLieAlgebra E a) (spl E a) φ.1 := by
  have ho : IsOpen ((stab φ ⊓ AdelicGLn.integralFiniteGL E a : Subgroup (GL (Fin a) (Af E))) :
      Set (GL (Fin a) (Af E))) := ((lev_iff φ).1 h).inter (AdelicGLn.isOpen_integralFiniteGL E a)
  refine ⟨(arch_iff φ.1).1 (UpperTheory.V.Cm.isArchSmooth_of_mem φ.2), _, ho,
    (AdelicGLn.isCompact_integralFiniteGL E a).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun _ h => h.2,
    fun x v hv => ?_⟩
  rw [spl_fin]
  exact hv.1 x

private theorem test_of (φ : CompactlySupportedContinuousMap (GA E a) ℂ)
    (h : ProdSmooth.IsSmooth (isExpLieAlgebra E a) (spl E a) φ) : ∃ u : Sm E a, IsTest u ∧ u.1 = φ := by
  obtain ⟨h1, V, hV, -, h2⟩ := h
  refine ⟨⟨φ, UpperTheory.V.Cm.mem_Sm_of ((arch_iff _).2 h1)⟩, ⟨φ.hasCompactSupport, ?_⟩, rfl⟩
  rw [lev_iff]
  refine Subgroup.isOpen_mono (H₁ := V) (fun v hv g => ?_) hV
  rw [← spl_fin]
  exact h2 g v hv

end

theorem UpperTheory.V.Cj.H.dmTest :
    UpperTheory.V.Cj.H.DmTest := by
  intro E _ _ _ a μ _ f hf
  let F : CompactlySupportedContinuousMap (GA E a) ℂ := ⟨⟨f.1, ((testOps E a f).1 hf.2).1⟩, hf.1⟩
  obtain ⟨n, φ, ψ, h, e⟩ := GroundTheory.Automorphic.ProdSmooth.exists_sum_conv _ (spl E a) μ F (smooth_of f hf.2)
  choose u hu eu using fun i => test_of (φ i) (h i).1
  choose v hv ev using fun i => test_of (ψ i) (h i).2
  refine ⟨n, u, v, fun i => ⟨hu i, hv i⟩, funext fun x => ?_⟩
  have := congrArg (fun G : CompactlySupportedContinuousMap (GA E a) ℂ => G x) e
  simp only [CompactlySupportedContinuousMap.sum_apply, GroundTheory.Automorphic.conv_apply] at this
  rw [Finset.sum_apply]
  simp only [eu, ev]
  exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HCobLim
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private def Fty {I : Type} (f : (I → ℂ) → ℂ) : Prop :=
  ∃ L : I →₀ ℂ, ∀ b : I → ℂ, Finsupp.linearCombination ℂ b L = f b

private theorem fty_ev {I : Type} (a : ℂ) (i : I) : Fty fun b : I → ℂ => a * b i :=
  ⟨Finsupp.single i a, fun b => by rw [Finsupp.linearCombination_single, smul_eq_mul]⟩

private theorem fty_sub {I : Type} {f g : (I → ℂ) → ℂ} (hf : Fty f) (hg : Fty g) : Fty fun b => f b - g b := by
  obtain ⟨L, hL⟩ := hf
  obtain ⟨M, hM⟩ := hg
  exact ⟨L - M, fun b => by rw [map_sub, hL, hM]⟩

private theorem fty_sum {I K : Type} (t : Finset K) (f : K → (I → ℂ) → ℂ) (hf : ∀ k, Fty (f k)) :
    Fty fun b => ∑ k ∈ t, f k b := by
  choose L hL using hf
  exact ⟨∑ k ∈ t, L k, fun b => by rw [map_sum]; exact Finset.sum_congr rfl fun k _ => hL k b⟩

private theorem fty_solve {I J : Type} (f : J → (I → ℂ) → ℂ) (hf : ∀ j, Fty (f j)) (c : J → ℂ) (cn : ℕ → J → ℂ)
    (h : ∀ k, ∃ b, ∀ j, f j b = cn k j) (hl : ∀ j, Tendsto (fun k => cn k j) atTop (𝓝 (c j))) :
    ∃ b, ∀ j, f j b = c j := by
  choose L hL using hf
  have hs : ∀ (b : I → ℂ) j, (L j).sum (fun i x => x * b i) = f j b := by
    intro b j
    rw [← hL, Finsupp.linearCombination_apply]
    rfl
  obtain ⟨b, hb⟩ := absSolve I J L c cn (fun k => by
    obtain ⟨b, hb⟩ := h k
    exact ⟨b, fun j => by rw [hs, hb]⟩) hl
  exact ⟨b, fun j => by rw [← hs, hb]⟩

theorem UpperTheory.V.Cj.H.hCobLim :
    UpperTheory.V.Cj.H.HCobLim := by
  intro Γ S _ d ρ hρ q c cn h hl
  have hlim : ∀ x : List Γ, x.length = q + 1 → ∀ s i,
      Tendsto (fun k => (c - cn k) x s i) atTop (𝓝 (c x s i)) := by
    intro x hx s i
    have h1 : Tendsto (fun k => cn k x s i) atTop (𝓝 0) := tendsto_pi_nhds.1 (hl x hx s) i
    simpa using (tendsto_const_nhds (x := c x s i)).sub h1
  cases q with
  | zero =>
    intro x hx
    funext s i
    have h1 := hlim x hx s i
    have h2 : (fun k => (c - cn k) x s i) = fun _ => (0 : ℂ) := by
      funext k
      rw [h k x hx]
      rfl
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  | succ q =>
    let cur : (List Γ × S × Fin d → ℂ) → List Γ → S → Fin d → ℂ := fun b x s i => b (x, s, i)
    let f : (Γ × {x : List Γ // x.length = q + 1} × S × Fin d) ⊕ ({x : List Γ // x.length = q + 2} × S × Fin d) →
        (List Γ × S × Fin d → ℂ) → ℂ :=
      Sum.elim (fun p b => cur b (p.2.1.1.map (p.1 * ·)) p.2.2.1 p.2.2.2 - ρ p.1 (cur b p.2.1.1) p.2.2.1 p.2.2.2)
        (fun p b => hd (cur b) p.1.1 p.2.1 p.2.2)
    have hf : ∀ j, Fty (f j) := by
      rintro (⟨γ, x, s, i⟩ | ⟨x, s, i⟩)
      · obtain ⟨s', B, hB⟩ := hρ γ s
        have e : f (Sum.inl (γ, x, s, i)) =
            fun b => 1 * b (x.1.map (γ * ·), s, i) - ∑ j, B i j * b (x.1, s', j) := by
          funext b
          simp only [f, Sum.elim_inl, hB, one_mul]
          rfl
        rw [e]
        exact fty_sub (fty_ev _ _) (fty_sum _ _ fun j => fty_ev _ _)
      · have e : f (Sum.inr (x, s, i)) =
            fun b => ∑ j ∈ Finset.range x.1.length, ((-1 : ℂ) ^ j) * b (x.1.eraseIdx j, s, i) := by
          funext b
          simp [f, cur, hd, Finset.sum_apply]
        rw [e]
        exact fty_sum _ _ fun j => fty_ev _ _
    obtain ⟨b, hb⟩ := fty_solve f hf (Sum.elim (fun _ => 0) fun p => c p.1.1 p.2.1 p.2.2)
      (fun k => Sum.elim (fun _ => 0) fun p => (c - cn k) p.1.1 p.2.1 p.2.2) (fun k => by
        obtain ⟨b, h1, h2⟩ := h k
        refine ⟨fun p => b p.1 p.2.1 p.2.2, ?_⟩
        rintro (⟨γ, x, s, i⟩ | ⟨x, s, i⟩)
        · change b (x.1.map (γ * ·)) s i - ρ γ (b x.1) s i = 0
          rw [h1 γ x.1 x.2, sub_self]
        · change hd b x.1 s i = (c - cn k) x.1 s i
          rw [h2 x.1 x.2]) (by
        rintro (p | ⟨x, s, i⟩)
        · exact tendsto_const_nhds
        · exact hlim x.1 x.2 s i)
    refine ⟨cur b, fun γ x hx => ?_, fun x hx => ?_⟩
    · funext s i
      exact sub_eq_zero.1 (hb (Sum.inl (γ, ⟨x, hx⟩, s, i)))
    · funext s i
      exact (hb (Sum.inr (⟨x, hx⟩, s, i))).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.IsOpenMapVal
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped ContDiff

section General

variable {P Q α : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [TopologicalSpace α]

private def Loc (Q : Type) [NormedAddCommGroup Q] [NormedSpace ℝ Q] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (H : P → α → V) (x : P) (y : α) : Prop :=
  ∃ (h : P × Q → V) (A : α → Q), ContinuousAt A y ∧ ContDiffAt ℝ ∞ h (x, A y) ∧
    ∀ᶠ p : P × α in 𝓝 (x, y), H p.1 p.2 = h (p.1, A p.2)

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {H : P → α → V} {x : P} {y : α}

private theorem Loc.cont (h : Loc Q H x y) : ContinuousAt (fun p : P × α => H p.1 p.2) (x, y) := by
  obtain ⟨h, A, hA, hh, e⟩ := h
  refine ContinuousAt.congr ?_ (EventuallyEq.symm e)
  exact ContinuousAt.comp (f := fun p : P × α => (p.1, A p.2)) hh.continuousAt
    (continuousAt_fst.prodMk (ContinuousAt.comp (f := Prod.snd) hA continuousAt_snd))

private theorem Loc.diff (h : Loc Q H x y) : DifferentiableAt ℝ (fun x => H x y) x := by
  obtain ⟨h, A, -, hh, e⟩ := h
  have e' : (fun x => H x y) =ᶠ[𝓝 x] fun x => h (x, A y) :=
    (Continuous.prodMk_left y).continuousAt.eventually e
  exact DifferentiableAt.congr_of_eventuallyEq
    ((hh.differentiableAt (by simp)).comp x (differentiableAt_id.prodMk (differentiableAt_const _))) e'

private theorem Loc.fderiv (h : Loc Q H x y) : Loc Q (fun x y => fderiv ℝ (fun x => H x y) x) x y := by
  obtain ⟨h, A, hA, hh, e⟩ := h
  refine ⟨fun q => (_root_.fderiv ℝ h q).comp (ContinuousLinearMap.inl ℝ P Q), A, hA,
    (hh.fderiv_right (by simp)).clm_comp contDiffAt_const, ?_⟩
  have hc : ContinuousAt (fun p : P × α => (p.1, A p.2)) (x, y) :=
    continuousAt_fst.prodMk (ContinuousAt.comp (f := Prod.snd) hA continuousAt_snd)
  have hd : ∀ᶠ q in 𝓝 (x, A y), ContDiffAt ℝ 1 h q := (hh.of_le (by simp)).eventually (by simp)
  filter_upwards [e.eventually_nhds, hc.eventually hd] with p hp hq
  have e' : (fun x => H x p.2) =ᶠ[𝓝 p.1] fun x => h (x, A p.2) :=
    (Continuous.prodMk_left p.2).continuousAt.eventually hp
  rw [e'.fderiv_eq]
  exact ((hq.differentiableAt (by simp)).hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left p.1 (A p.2))).fderiv

variable [FiniteDimensional ℝ P] [T2Space α] [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
  {μ : Measure α} {f : α → ℂ} {S : Set P}

omit [FiniteDimensional ℝ P] [T2Space α] [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α] in
private theorem supp_fderiv (hs : ∃ C : Set α, IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, H x' y = 0) :
    ∃ C : Set α, IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, fderiv ℝ (fun x => H x y) x' = 0 := by
  obtain ⟨C, hC, h⟩ := hs
  refine ⟨C, hC, h.eventually_nhds.mono fun x' hx' y hy => ?_⟩
  have e : (fun x => H x y) =ᶠ[𝓝 x'] fun _ => 0 := hx'.mono fun z hz => hz y hy
  rw [e.fderiv_eq, fderiv_fun_const]
  rfl

private theorem dom [NormedSpace ℂ V] (hf : LocallyIntegrable f μ) (hS : IsOpen S) (hx : x ∈ S)
    (hH : ∀ x ∈ S, ∀ y, Loc Q H x y) (hs : ∃ C : Set α, IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, H x' y = 0) :
    ∃ b : α → ℝ, Integrable b μ ∧ ∀ᶠ x' in 𝓝 x, AEStronglyMeasurable (fun y => f y • H x' y) μ ∧
      ∀ y, ‖f y • H x' y‖ ≤ b y := by
  obtain ⟨C, hC, h⟩ := hs
  obtain ⟨K, hK, hKS, hKc⟩ := local_compact_nhds (hS.mem_nhds hx)
  obtain ⟨M, hM⟩ := (hKc.prod hC).exists_bound_of_continuousOn (f := fun p : P × α => H p.1 p.2)
    fun p hp => (hH p.1 (hKS hp.1) p.2).cont.continuousWithinAt
  refine ⟨C.indicator fun y => ‖f y‖ * M,
    (integrable_indicator_iff hC.measurableSet).2 ((hf.integrableOn_isCompact hC).norm.mul_const M), ?_⟩
  filter_upwards [h, hK] with x' h1 h2
  refine ⟨hf.aestronglyMeasurable.smul (Continuous.aestronglyMeasurable (continuous_iff_continuousAt.2 fun y => ?_)),
    fun y => ?_⟩
  · exact ContinuousAt.comp (f := fun y => (x', y)) (hH x' (hKS h2) y).cont (Continuous.prodMk_right x').continuousAt
  · by_cases hy : y ∈ C
    · rw [Set.indicator_of_mem hy, norm_smul]
      exact mul_le_mul_of_nonneg_left (hM (x', y) ⟨h2, hy⟩) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hy, h1 y hy, smul_zero, norm_zero]

private theorem hasFD [NormedSpace ℂ V] [SMulCommClass ℝ ℂ V] (hf : LocallyIntegrable f μ) (hS : IsOpen S) (hx : x ∈ S)
    (hH : ∀ x ∈ S, ∀ y, Loc Q H x y) (hs : ∃ C : Set α, IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, H x' y = 0) :
    HasFDerivAt (fun x => ∫ y, f y • H x y ∂μ) (∫ y, f y • fderiv ℝ (fun x => H x y) x ∂μ) x := by
  obtain ⟨b, hb, h⟩ := dom hf hS hx hH hs
  obtain ⟨b', hb', h'⟩ := dom hf hS hx (fun x hx y => (hH x hx y).fderiv) (supp_fderiv hs)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := b')
    (F' := fun x y => f y • fderiv ℝ (fun x => H x y) x) (h'.and (hS.eventually_mem hx)) (h.mono fun _ h => h.1)
    (hb.mono' h.self_of_nhds.1 (.of_forall h.self_of_nhds.2)) h'.self_of_nhds.1
    (.of_forall fun y x' hx' => hx'.1.2 y) hb' (.of_forall fun y x' hx' => ?_)
  exact (hH x' hx'.2 y).diff.hasFDerivAt.const_smul (f y)

private theorem smooth_nat (hf : LocallyIntegrable f μ) (hS : IsOpen S) (n : ℕ) :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V] [SMulCommClass ℝ ℂ V] (H : P → α → V),
      (∀ x ∈ S, ∀ y, Loc Q H x y) → (∀ x ∈ S, ∃ C : Set α, IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, H x' y = 0) →
      ContDiffOn ℝ n (fun x => ∫ y, f y • H x y ∂μ) S := by
  induction n with
  | zero =>
    intro V _ _ _ _ H hH hs
    exact contDiffOn_zero.2 fun x hx => (hasFD hf hS hx hH (hs x hx)).continuousAt.continuousWithinAt
  | succ n ih =>
    intro V _ _ _ _ H hH hs
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hS]
    refine ⟨fun x hx => (hasFD hf hS hx hH (hs x hx)).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (ih _ _ (fun x hx y => (hH x hx y).fderiv) fun x hx => supp_fderiv (hs x hx)).congr
      fun x hx => (hasFD hf hS hx hH (hs x hx)).fderiv

end General

section Adelic

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

omit [_root_.NumberField.IsTotallyComplex E] in
private theorem contDiff_mulL :
    ContDiff ℝ ∞ fun q : Lie E a × Lie E a => toL (Matrix.of q.2 * Matrix.of q.1) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  change ContDiff ℝ ∞ fun q : Lie E a × Lie E a => ∑ k, q.2 i k * q.1 k j
  refine ContDiff.sum fun k _ => ContDiff.mul ?_ ?_
  · exact contDiff_pi.1 (contDiff_pi.1 contDiff_snd i) k
  · exact contDiff_pi.1 (contDiff_pi.1 contDiff_fst k) j

private theorem loc_chart {ψ : Sm E a} (hψ : HasLev ψ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) (y : GA E a) :
    Loc (Lie E a) (fun x y => chart ψ.1 (y⁻¹ * g) x) x y := by
  have hc : Continuous fun w : GA E a => (y⁻¹ * g)⁻¹ * (w⁻¹ * g) :=
    continuous_const.mul (continuous_inv.mul continuous_const)
  have hA : Continuous fun w : GA E a => (GeneralLinearGroup.map (pInf E) ((y⁻¹ * g)⁻¹ * (w⁻¹ * g))).val :=
    Units.continuous_val.comp (GlobalTheory.CompanionTheory.AffglAssembly.continuous_mapInf.comp hc)
  refine ⟨fun q => chart ψ.1 (y⁻¹ * g) (toL (Matrix.of q.2 * Matrix.of q.1)),
    fun w => toL (GeneralLinearGroup.map (pInf E) ((y⁻¹ * g)⁻¹ * (w⁻¹ * g))).val, hA.continuousAt, ?_, ?_⟩
  · refine ContDiffAt.comp _ (contDiffAt_chart ψ.2 _ ?_) contDiff_mulL.contDiffAt
    exact IsUnit.mul (Units.isUnit _) hx
  · have h1 : ∀ᶠ w in 𝓝 y, act (.fin (GeneralLinearGroup.map (pFin E) ((y⁻¹ * g)⁻¹ * (w⁻¹ * g)))) ψ = ψ :=
      (GlobalTheory.CompanionTheory.AffglAssembly.continuous_mapFin.comp hc).continuousAt.eventually_mem (hψ.mem_nhds (by
        change finRep E a _ ψ = ψ
        simp))
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod (isOpen_invSet.mem_nhds hx) h1]
    rintro ⟨x', w⟩ ⟨⟨u, hu⟩, hw⟩
    obtain rfl : x' = toL u.val := hu.symm
    set t := (y⁻¹ * g)⁻¹ * (w⁻¹ * g) with ht
    have e1 := congrFun (congrArg Subtype.val hw) (y⁻¹ * g * infGL E a (GeneralLinearGroup.map (pInf E) t * u))
    change ψ.1 (_ * finGL E a _) = _ at e1
    change chart ψ.1 (w⁻¹ * g) (toL u.val) = chart ψ.1 (y⁻¹ * g) (toL (GeneralLinearGroup.map (pInf E) t * u).val)
    rw [chart_val, chart_val, ← e1, map_mul, mul_assoc (y⁻¹ * g), mul_assoc (infGL E a _), infGL_comm u,
      ← mul_assoc (infGL E a _), infGL_mul_finGL, ← mul_assoc (y⁻¹ * g), ht, mul_inv_cancel_left]

open scoped Matrix.Norms.Operator in
omit [_root_.NumberField.IsTotallyComplex E] in
private theorem isOpenMap_val : IsOpenMap fun u : GL (Fin a) (Cinf E) => toL u.val :=
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  (Units.isOpenEmbedding_val (R := Matrix (Fin a) (Fin a) (Cinf E))).isOpenMap

open scoped Matrix.Norms.Operator in
omit [_root_.NumberField.IsTotallyComplex E] in
private theorem locCpt : LocallyCompactSpace (GL (Fin a) (Cinf E)) :=
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  haveI : ProperSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.proper ℝ _
  (Units.isOpenEmbedding_val (R := Matrix (Fin a) (Fin a) (Cinf E))).locallyCompactSpace

private theorem supp_chart {ψ : GA E a → ℂ} (hψ : HasCompactSupport ψ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    ∃ C : Set (GA E a), IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, chart ψ (y⁻¹ * g) x' = 0 := by
  obtain ⟨u, hu⟩ := hx
  obtain rfl : x = toL u.val := hu.symm
  haveI := locCpt (E := E) (a := a)
  obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds u
  have hc : Continuous fun p : GL (Fin a) (Cinf E) × GA E a => g * infGL E a p.1 * p.2⁻¹ :=
    (continuous_const.mul ((GlobalTheory.CompanionTheory.LieSkew.continuous_infGL_map E a).comp continuous_fst)).mul continuous_snd.inv
  refine ⟨_, (hKc.prod hψ.isCompact).image hc, ?_⟩
  filter_upwards [isOpenMap_val.image_mem_nhds hK]
  rintro _ ⟨v, hv, rfl⟩ y hy
  rw [chart_val]
  by_contra h
  exact hy ⟨(v, y⁻¹ * g * infGL E a v), ⟨hv, subset_tsupport _ h⟩, by simp only; group⟩

end Adelic

theorem UpperTheory.V.Cj.H.cvSm :
    UpperTheory.V.Cj.H.CvSm := by
  intro E _ _ _ a μ _ _ ψ hψ F g
  have hf := (UpperTheory.V.Cj.H.locInt (GA E a) (latticeGL E a) μ).1 F
  have h : ContDiffOn ℝ ∞ (fun x => ∫ y, GlobalTheory.AutomorphicL2Unitary.lift _ F y • chart ψ.1 (y⁻¹ * g) x ∂μ) (invSet E a) :=
    contDiffOn_infty.2 fun n => smooth_nat hf isOpen_invSet n ℂ _ (fun _ hx y => loc_chart hψ.2 g hx y)
      fun _ hx => supp_chart hψ.1 g hx
  refine h.congr ?_
  rintro x ⟨u, hu⟩
  obtain rfl : x = toL u.val := hu.symm
  simp only [chart_val, cv, mul_assoc, smul_eq_mul]
end

