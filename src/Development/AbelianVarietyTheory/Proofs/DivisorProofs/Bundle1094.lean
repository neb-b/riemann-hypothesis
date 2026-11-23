module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjAverageUnipotentLocallyConstantCompactSuppor
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.UnipMean

section Generic

variable {G : Type} [Group G]

def core (K K' : Subgroup G) : Subgroup G where
  carrier := {c | ∀ k ∈ K, k⁻¹ * c * k ∈ K'}
  one_mem' := by intro k _; simp
  mul_mem' := by
    intro a b ha hb k hk
    have : k⁻¹ * (a * b) * k = (k⁻¹ * a * k) * (k⁻¹ * b * k) := by group
    rw [this]; exact K'.mul_mem (ha k hk) (hb k hk)
  inv_mem' := by
    intro a ha k hk
    have : k⁻¹ * a⁻¹ * k = (k⁻¹ * a * k)⁻¹ := by group
    rw [this]; exact K'.inv_mem (ha k hk)

theorem isOpen_core [TopologicalSpace G] [IsTopologicalGroup G] (K K' : Subgroup G) (hK : IsCompact (K : Set G))
    (hK' : IsOpen (K' : Set G)) : IsOpen (core K K' : Set G) := by
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have h := hK.eventually_forall_of_forall_eventually (x₀ := (1 : G)) (P := fun c k => k⁻¹ * c * k ∈ K') ?_
  · exact h
  intro k _
  have hc : Continuous fun p : G × G => p.2⁻¹ * p.1 * p.2 := by fun_prop
  have h1 : (fun p : G × G => p.2⁻¹ * p.1 * p.2) (1, k) ∈ (K' : Set G) := by simp [K'.one_mem]
  exact hc.continuousAt.preimage_mem_nhds (hK'.mem_nhds h1)

theorem cavg_mul_core (K K' : Subgroup G) (f : G → ℂ) (hf : ∀ k ∈ K', ∀ x, f (x * k) = f x) (x c : G)
    (hc : c ∈ core K K') : cavg K f (x * c) = cavg K f x := by
  unfold cavg
  congr 1
  funext k
  have := hf _ (hc k k.2) ((k : G)⁻¹ * x * k)
  rw [← this]
  congr 1
  group

theorem exists_of_cavg_ne_zero (K : Subgroup G) (f : G → ℂ) (x : G) (h : cavg K f x ≠ 0) :
    ∃ k ∈ K, f (k⁻¹ * x * k) ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply h
  unfold cavg avg
  have : (fun k : K => f ((k : G)⁻¹ * x * k)) = fun _ => 0 := funext fun k => hn k k.2
  rw [this]
  simp

end Generic

section Block

variable {E : Type} [Field E] [NumberField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)

theorem isUnit_blkMat (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 m.2.isUnit)

theorem blk_val (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X).val = Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
  unfold blk
  simp only
  rw [dite_eq_left (isUnit_blkMat h w m X)]
  rfl

theorem blk_add (m : GLw a w × GLw b w) (x y : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    blk h w m (x + y) = blk h w m x * blk h w 1 y := by
  ext1
  rw [Units.val_mul, blk_val, blk_val, blk_val]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Prod.fst_one,
    Prod.snd_one, Units.val_one, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_add]
  congr 2
  exact add_comm _ _

theorem blk_one_zero : blk h w (1 : GLw a w × GLw b w) 0 = 1 := by
  ext1
  rw [blk_val]
  simp only [Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.mul_zero, Matrix.fromBlocks_one, Units.val_one]
  exact Matrix.submatrix_one_equiv _

theorem blk_one_neg (y : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w 1 y)⁻¹ = blk h w 1 (-y) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← blk_add, add_neg_cancel, blk_one_zero]

theorem continuous_blk_one : Continuous fun y : Matrix (Fin a) (Fin b) (w.adicCompletion E) => blk h w 1 y := by
  have hv : Continuous fun y : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (blk h w 1 y).val := by
    simp only [blk_val, Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.one_mul]
    exact (continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const).matrix_reindex _ _
  refine Units.continuous_iff.2 ⟨hv, ?_⟩
  simp only [blk_one_neg]
  exact hv.comp continuous_neg

def corner (m : GLw a w × GLw b w) (g : GLw n w) : Matrix (Fin a) (Fin b) (w.adicCompletion E) :=
  (m.1⁻¹).val * (Matrix.reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm
    g.val).toBlocks₁₂

theorem corner_blk (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    corner h w m (blk h w m X) = X := by
  rw [corner, blk_val, ← Matrix.reindex_symm, Equiv.symm_apply_apply, Matrix.toBlocks_fromBlocks₁₂,
    ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem continuous_corner (m : GLw a w × GLw b w) : Continuous (corner h w m) := by
  unfold corner
  refine continuous_const.matrix_mul ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact (Units.continuous_val.matrix_elem _ _)

end Block

theorem cavg_blk_locConst_compactSupport : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw b w, (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m (x + y)) = GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m x)) ∧ HasCompactSupport (fun X => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (blk h w m X)) := by
  intro E _ _ n a b h w f ⟨K', hK'o, hf⟩ m
  obtain ⟨_, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hCo : IsOpen (core (GlobalTheory.LFun.KGL w (n := n)) K' : Set (GLw n w)) := isOpen_core _ _ hKc hK'o
  let U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) :=
    { carrier := {y | blk h w 1 y ∈ core (GlobalTheory.LFun.KGL w (n := n)) K'}
      zero_mem' := by
        simp only [Set.mem_setOf_eq, blk_one_zero]
        exact Subgroup.one_mem _
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at *
        rw [blk_add]
        exact Subgroup.mul_mem _ hx hy
      neg_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        rw [← blk_one_neg]
        exact Subgroup.inv_mem _ hx }
  refine ⟨⟨U, hCo.preimage (continuous_blk_one h w), fun x y hy => ?_⟩, ?_⟩
  · rw [blk_add]
    exact cavg_mul_core _ _ f (fun k hk x => (hf.2 k hk x).2) _ _ hy
  · let S : Set (GLw n w) := (fun p : GLw n w × GLw n w × GLw n w => p.1 * p.2.1 * p.2.2) ''
      ((GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ×ˢ (tsupport f ×ˢ (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w))))
    have hS : IsCompact S := (hKc.prod (hf.1.isCompact.prod hKc)).image (by fun_prop)
    refine HasCompactSupport.intro (hS.image (continuous_corner h w m)) fun X hX => ?_
    by_contra hne
    obtain ⟨k, hk, hfk⟩ := exists_of_cavg_ne_zero _ f _ hne
    refine hX ⟨blk h w m X, ⟨(k, k⁻¹ * blk h w m X * k, k⁻¹),
      ⟨hk, subset_tsupport _ hfk, Subgroup.inv_mem _ hk⟩, by group⟩, corner_blk h w m X⟩

end GlobalTheory.LeviDesc.UnipMean
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAt
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem contDiffAt_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {f : CxPts X.str σ → ℝ} {y : CxPts X.str σ}, y ∈ e.source → CInfAt f y → ContDiffAt ℝ ∞ (fun v => f (e.symm v)) (e y) := by
  intro F _ σ X e he f y hy hf
  obtain ⟨W, ι, hι, g, Φ, O, hyW, hO, hgO, hΦ, hfeq⟩ := hf

  have hU : IsOpen (e.target ∩ e.symm ⁻¹' ptsIn X.str σ W) :=
    e.isOpen_inter_preimage_symm (GlobalTheory.CxPts.isOpen_ptsIn W)
  have hyU : e y ∈ e.target ∩ e.symm ⁻¹' ptsIn X.str σ W :=
    ⟨e.map_source hy, by rw [Set.mem_preimage, e.left_inv hy]; exact hyW⟩

  have hGc : ContDiffAt ℂ ∞ (fun v a => GlobalTheory.CxPts.ev X.str σ W (g a) (e.symm v)) (e y) := by
    rw [contDiffAt_pi]
    intro a
    exact (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ _ hU (he W (g a))).contDiffAt
      (hU.mem_nhds hyU)

  have hΦc : ContDiffAt ℝ ∞ Φ (fun a => GlobalTheory.CxPts.ev X.str σ W (g a) (e.symm (e y))) := by
    rw [e.left_inv hy]
    exact hΦ.contDiffAt (hO.mem_nhds hgO)
  have hcomp : ContDiffAt ℝ ∞ (fun v => Φ fun a => GlobalTheory.CxPts.ev X.str σ W (g a) (e.symm v)) (e y) :=
    hΦc.comp (e y) (hGc.restrict_scalars ℝ)
  refine hcomp.congr_of_eventuallyEq ?_

  have ht : Filter.Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
    have h := e.continuousAt_symm (e.map_source hy)
    rw [ContinuousAt, e.left_inv hy] at h
    exact h
  exact ht.eventually hfeq

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPolarisedTopChernCoeff
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop


set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
theorem _root_.GlobalTheory.GoodTop.continuousAt_mixTop :
    ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]
      {K : _root_.ReciprocityTheory.L2DbarEstimates.V n → Fin n → _root_.GlobalTheory.GoodTop.EndValuedForm11Coeffs n r} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n},
      (∀ i a b p q, ContinuousAt (fun x => K x i a b p q) v) →
        ContinuousAt (fun x => _root_.GlobalTheory.GoodTop.mixTop (K x)) v := by
  intro n r _ _ K v hK
  unfold _root_.GlobalTheory.GoodTop.mixTop
  simp only [Matrix.det_apply, Matrix.of_apply]
  fun_prop

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMapGLSpl
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

theorem continuous_sLoc_spl (v : Pl E) : Continuous (sLoc E v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (Pl E)) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion E → RestrictedProduct (fun u : Pl E => u.adicCompletion E)
      (fun u => (u.adicCompletionIntegers E : Set (u.adicCompletion E))) (Filter.principal {v}ᶜ) :=
    fun a => ⟨Pi.single v a, fun u hu => by
      rw [Set.mem_setOf_eq, Pi.single_eq_of_ne hu]; exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem continuous_locGL_spl (w : Pl E) : Continuous (locGL E n w) :=
  Continuous.units_map _ (continuous_const.add (Continuous.matrix_map continuous_id (continuous_sLoc_spl E w)))

variable {E n}

end GlobalTheory.EulerTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOneAddLowRankEmbeddingQuaternionMatrix
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory

theorem emb_qm_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (a b : F) (M : ℕ) (A : Matrix (Fin M) (Fin 2) (AF F ⊗[F] E)) (B : Matrix (Fin 2) (Fin M) (AF F ⊗[F] E)) (θ : AF F ⊗[F] E), Continuous fun x : DA F a b => emb A B (qm (algebraMap (AF F) (AF F ⊗[F] E)) θ x) := by
  intro F E _ _ _ _ a b M A B θ
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := IsModuleTopology.topologicalAddGroup (AF F) _
  have hL : ∀ c : AF F ⊗[F] E, Continuous (fun y : AF F ⊗[F] E => c * y) := fun c =>
    IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft (AF F) c)
  have hR : ∀ c : AF F ⊗[F] E, Continuous (fun y : AF F ⊗[F] E => y * c) := fun c =>
    IsModuleTopology.continuous_of_linearMap (LinearMap.mulRight (AF F) c)
  have hι : Continuous (algebraMap (AF F) (AF F ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
  have hc : ∀ i, Continuous fun x : DA F a b => coords x i := fun i =>
    (continuous_apply i).comp continuous_induced_dom
  have h0 : Continuous fun x : DA F a b => x.re := by simpa [coords] using hc 0
  have h1 : Continuous fun x : DA F a b => x.imI := by simpa [coords] using hc 1
  have h2 : Continuous fun x : DA F a b => x.imJ := by simpa [coords] using hc 2
  have h3 : Continuous fun x : DA F a b => x.imK := by simpa [coords] using hc 3
  have hq : ∀ k l, Continuous fun x : DA F a b => qm (algebraMap (AF F) (AF F ⊗[F] E)) θ x k l := by
    intro k l
    fin_cases k <;> fin_cases l <;> simp [qm]
    · exact (hι.comp h0).add ((hR θ).comp (hι.comp h1))
    · exact (hL _).comp ((hι.comp h2).add ((hR θ).comp (hι.comp h3)))
    · exact (hι.comp h2).sub ((hR θ).comp (hι.comp h3))
    · exact (hι.comp h0).sub ((hR θ).comp (hι.comp h1))
  apply continuous_matrix
  intro i j
  simp only [emb, Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply]
  refine continuous_const.add (continuous_finsetSum _ fun l _ => (hR _).comp
    (continuous_finsetSum _ fun k _ => (hL _).comp ((hq k l).sub continuous_const)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPlaceAt
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.PlaceCoordsF

variable {F : Type} [Field F] [NumberField F]

def placeAt (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) : AF F := pairA F 0 (GlobalTheory.AdelicU.singleFin v x)

theorem placeAt_add (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    placeAt v (x + y) = placeAt v x + placeAt v y := by
  unfold placeAt pairA
  rw [map_add (f := _)]
  exact Prod.ext (add_zero 0).symm rfl

theorem placeAt_injective (v : HeightOneSpectrum (𝓞 F)) : Function.Injective (placeAt v) := by
  intro x y h
  have h2 := congrArg (fun c : AF F => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v c.2) h
  simpa only [placeAt, pairA, GlobalTheory.AdelicU.evalV_singleFin_self] using h2

theorem continuous_placeAt (v : HeightOneSpectrum (𝓞 F)) : Continuous (placeAt v) := by
  unfold placeAt pairA
  exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)

theorem eq_placeAt_of_mul {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (hα1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v α = 1)
    (hα0 : ∀ v', v' ≠ v → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v' α = 0) {c : AF F} (hc : pairA F 0 α * c = c) :
    c = placeAt v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v c.2) := by
  have h1 : c.1 = 0 := by
    have := congrArg Prod.fst hc
    rw [← this]
    exact zero_mul _
  have h2 : α * c.2 = c.2 := congrArg Prod.snd hc
  refine Prod.ext h1 ?_
  show c.2 = GlobalTheory.AdelicU.singleFin v _
  refine GlobalTheory.AdelicU.af_ext fun u => ?_
  by_cases hu : u = v
  · subst hu
    rw [GlobalTheory.AdelicU.evalV_singleFin_self]
  · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hu, ← h2, map_mul, hα0 u hu, zero_mul]

end GlobalTheory.PlaceCoordsF

namespace GlobalTheory.PlaceCoordsF

theorem coords_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (ε : AF F), IsPlaceIdemF F v ε → ∀ nS nT : ℕ,
      ∃ (N : ℕ) (Φ : (Fin N → v.adicCompletion F) →+ WOF F E nS nT), Continuous Φ ∧ Function.Injective Φ ∧
        ∀ y : WOF F E nS nT, (∀ i j, algebraMap (AF F) (AEF F E) ε * y i j = y i j) → y ∈ Set.range Φ := by
  intro F E _ _ _ _ _ v ε hε nS nT
  obtain ⟨α, rfl, hα1, hα0⟩ := hε
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  let B : Module.Basis (Fin (Module.finrank F E)) (AF F) (AEF F E) :=
    Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  let e := Fintype.equivFin (Fin nT × Fin nS × Fin (Module.finrank F E))
  let f : (Fin (Fintype.card (Fin nT × Fin nS × Fin (Module.finrank F E))) → v.adicCompletion F) → WOF F E nS nT :=
    fun t i j => B.equivFun.symm (fun l => placeAt v (t (e (i, j, l))))
  have hadd : ∀ s t, f (s + t) = f s + f t := by
    intro s t
    funext i j
    show B.equivFun.symm _ = B.equivFun.symm _ + B.equivFun.symm _
    rw [← map_add (f := _)]
    congr 1
    funext l
    exact placeAt_add v _ _
  let Φ := AddMonoidHom.mk' f hadd
  refine ⟨_, Φ, ?_, ?_, ?_⟩
  · have hB : Continuous B.equivFun.symm := IsModuleTopology.continuous_of_linearMap B.equivFun.symm.toLinearMap
    exact continuous_pi fun i => continuous_pi fun j =>
      hB.comp (continuous_pi fun l => (continuous_placeAt v).comp (continuous_apply _))
  · intro s t hst
    have key : ∀ i j l, s (e (i, j, l)) = t (e (i, j, l)) := by
      intro i j l
      have h1 : f s i j = f t i j := congrFun (congrFun hst i) j
      have h2 := congrFun (B.equivFun.symm.injective h1) l
      exact placeAt_injective v h2
    funext k
    have := key (e.symm k).1 (e.symm k).2.1 (e.symm k).2.2
    simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using this
  · intro y hy
    have hc : ∀ i j l, B.equivFun (y i j) l =
        placeAt v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (B.equivFun (y i j) l).2) := by
      intro i j l
      refine eq_placeAt_of_mul hα1 hα0 ?_
      have h1 : pairA F 0 α • y i j = y i j := by rw [Algebra.smul_def]; exact hy i j
      have h2 := congrFun (congrArg B.equivFun h1) l
      rw [map_smul, Pi.smul_apply, smul_eq_mul] at h2
      exact h2
    refine ⟨fun k => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (B.equivFun (y (e.symm k).1 (e.symm k).2.1) (e.symm k).2.2).2, ?_⟩
    funext i j
    show B.equivFun.symm _ = y i j
    simp only [Equiv.symm_apply_apply]
    rw [← B.equivFun.symm_apply_apply (y i j)]
    congr 1
    funext l
    rw [B.equivFun.symm_apply_apply]
    exact (hc i j l).symm

end GlobalTheory.PlaceCoordsF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
section
noncomputable section

open MeasureTheory

namespace GlobalTheory

namespace WeylCell

def partnerU {n : ℕ} (k : Fin (n / 2)) : Fin n :=
  if h : k.val + 1 < n / 2 then lo (⟨k.val + 1, h⟩ : Fin (n / 2)) else (lo k).rev

def simpleU {n : ℕ} (k : Fin (n / 2)) : Equiv.Perm (Fin n) :=
  if k.val + 1 < n / 2 then Equiv.swap (lo k) (partnerU k) * Equiv.swap (lo k).rev (partnerU k).rev
  else Equiv.swap (lo k) (lo k).rev

def actU {n : ℕ} (k : Fin (n / 2)) (α : Fin (n / 2) → ℂˣ) : Fin (n / 2) → ℂˣ :=
  if h : k.val + 1 < n / 2 then α ∘ Equiv.swap k ⟨k.val + 1, h⟩ else Function.update α k (α k)⁻¹

def cSimpleU (q : ℕ) {n : ℕ} (k : Fin (n / 2)) (α : Fin (n / 2) → ℂˣ) : ℂ :=
  if h : k.val + 1 < n / 2 then cSL ((q : ℂ) ^ 2) ((α k : ℂ) / α ⟨k.val + 1, h⟩)
  else if Even n then cSL q (α k) else cSU q (α k)

theorem IsWeylRep.inv {R : Type} [CommRing R] {n : ℕ} {v : Equiv.Perm (Fin n)} {y : GL (Fin n) R}
    (hy : IsWeylRep v y) : IsWeylRep v⁻¹ y⁻¹ := by
  have key : ∀ i j, ((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i (v j) *
      (y : Matrix (Fin n) (Fin n) R) (v j) j = if i = j then 1 else 0 := by
    intro i j
    have h := congrFun (congrFun (Units.inv_mul y) i) j
    rw [Matrix.mul_apply, Finset.sum_eq_single (v j)] at h
    · rw [h, Matrix.one_apply]
    · intro b _ hb; rw [hy b j hb, mul_zero]
    · simp
  have hv : ∀ j, v (v⁻¹ j) = j := fun j => by simp
  intro i j hij
  have hu : IsUnit ((y : Matrix (Fin n) (Fin n) R) j (v⁻¹ j)) := by
    have h := key (v⁻¹ j) (v⁻¹ j)
    rw [hv, if_pos rfl] at h
    exact IsUnit.of_mul_eq_one_right _ h
  have h := key i (v⁻¹ j)
  rw [hv, if_neg hij] at h
  exact hu.mul_left_eq_zero.1 h

end WeylCell

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryCharacterTrivialOfSiegelStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledUnitary_character_trivial_of_siegel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 → ∀ c : UG (cA σ) (dbl (incM F J)) →* ℂˣ, Continuous c → (∀ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), (p.1.1 : Matrix _ _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * diagCols (Fin n) = diagCols (Fin n) * t.1 → c p = 1) → c = 1 := by
  first | exact @GlobalTheory.SiegelChar.eq_one_of_siegel | exact GlobalTheory.SiegelChar.eq_one_of_siegel | (intros; apply GlobalTheory.SiegelChar.eq_one_of_siegel <;> assumption)
end

