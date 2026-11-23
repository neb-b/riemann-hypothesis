module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsDense
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.absDense :
    UpperTheory.V.Cj.H.AbsDense := by
  intro G H _ _ _ _ R D A hD hR hA hsym hirr s hs w hw
  set u : D → H := fun v => (A v : H) + (Complex.I * s) • (v : H) with hu
  have hinner : ∀ (g : G) (x y : H), inner ℂ (R g x) (R g y) = inner ℂ x y := fun g x y =>
    (LinearIsometry.mk (R g).toLinearMap (hR g)).inner_map_map x y
  have hinv : ∀ (g : G) (y : H), R g (R g⁻¹ y) = y := by
    intro g y
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  let W : Submodule ℂ H :=
    { carrier := {x | ∀ v : D, inner ℂ x (u v) = 0}
      add_mem' := by
        intro a b ha hb v
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [inner_add_left, ha v, hb v, add_zero]
      zero_mem' := by
        intro v
        simp only [Set.mem_setOf_eq, inner_zero_left]
      smul_mem' := by
        intro c a ha v
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [inner_smul_left, ha v, mul_zero] }
  have hW : GlobalTheory.AutomorphicL2Unitary.IsSubrep R W := by
    refine ⟨?_, ?_⟩
    · have hset : (W : Set H) = ⋂ v : D, {x | inner ℂ x (u v) = 0} := by
        ext x
        simp [W]
      rw [hset]
      exact isClosed_iInter fun v => isClosed_eq (continuous_id.inner continuous_const) continuous_const
    · intro g x hx v
      show inner ℂ (R g x) (u v) = 0
      have key : R g⁻¹ (u v) = u ⟨R g⁻¹ v, hD g⁻¹ v v.2⟩ := by
        simp only [hu, map_add (f := _), map_smul]
        rw [hA g⁻¹ v]
      rw [← hinv g (u v), hinner, key]
      exact hx _
  have hWD : W ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxD⟩ := Submodule.mem_inf.mp hx
    have h0 : inner ℂ x (u ⟨x, hxD⟩) = 0 := hxW ⟨x, hxD⟩
    have hre : (inner ℂ x (A ⟨x, hxD⟩ : H)).im = 0 := by
      have hs' := hsym ⟨x, hxD⟩ ⟨x, hxD⟩
      rw [← inner_conj_symm] at hs'
      exact Complex.conj_eq_iff_im.mp hs'
    simp only [hu] at h0
    rw [inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K] at h0
    have him := congrArg Complex.im h0
    simp [hre, hs] at him
    rw [← Complex.ofReal_pow, Complex.ofReal_re] at him
    rw [Submodule.mem_bot]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp him)
  have hwW : w ∈ W := hw
  rw [hirr W hW hWD] at hwW
  exact (Submodule.mem_bot ℂ).mp hwW
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsInv
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem UpperTheory.V.Cj.H.absInv_low {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x v : H) (s : ℝ)
    (h : inner ℂ x v = inner ℂ v x) : |s| * ‖v‖ ≤ ‖x + (Complex.I * s) • v‖ := by
  have hre : (inner ℂ x v).im = 0 := by
    have e := congrArg Complex.im h
    rw [← inner_conj_symm v x, Complex.conj_im] at e
    linarith
  have hsq : ‖x + (Complex.I * s) • v‖ ^ 2 = ‖x‖ ^ 2 + (|s| * ‖v‖) ^ 2 := by
    rw [@norm_add_sq ℂ, inner_smul_right, norm_smul]
    have hn : ‖Complex.I * (s : ℂ)‖ = |s| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hn]
    simp [Complex.mul_re, hre]
  have h0 : 0 ≤ |s| * ‖v‖ := mul_nonneg (abs_nonneg s) (norm_nonneg v)
  nlinarith [norm_nonneg (x + (Complex.I * s) • v), sq_nonneg ‖x‖]

theorem UpperTheory.V.Cj.H.absInv :
    UpperTheory.V.Cj.H.AbsInv := by
  intro H _ _ _ D A hA s hs hd
  let L : D →ₗ[ℂ] H := D.subtype.comp A + (Complex.I * s) • D.subtype
  have hL : ∀ v, L v = ↑(A v) + (Complex.I * s) • (v : H) := fun v => rfl
  have hs' : 0 < |s| := abs_pos.mpr hs
  have hlow : ∀ v : D, |s| * ‖(v : H)‖ ≤ ‖L v‖ := by
    intro v
    rw [hL]
    exact UpperTheory.V.Cj.H.absInv_low _ _ s (hA v v)
  have hinj : Function.Injective L := by
    intro a b hab
    have h1 := hlow (a - b)
    rw [map_sub, hab, sub_self, norm_zero] at h1
    have h2 : ‖((a - b : D) : H)‖ = 0 :=
      le_antisymm (le_of_mul_le_mul_left (by simpa using h1) hs') (norm_nonneg _)
    rw [norm_eq_zero, Submodule.coe_sub, sub_eq_zero] at h2
    exact Subtype.ext h2
  let R := LinearMap.range L
  let e := LinearEquiv.ofInjective L hinj
  have he : ∀ x : D, ((e x : R) : H) = L x := fun x => LinearEquiv.ofInjective_apply L (h := hinj) x
  let g : R →ₗ[ℂ] H := D.subtype.comp e.symm.toLinearMap
  have hg : ∀ y : R, |s| * ‖g y‖ ≤ ‖(y : H)‖ := by
    intro y
    have h1 : L (e.symm y) = y := by
      have h2 := he (e.symm y)
      rw [LinearEquiv.apply_symm_apply] at h2
      exact h2.symm
    have h3 := hlow (e.symm y)
    rw [h1] at h3
    exact h3
  let gc : R →L[ℂ] H := g.mkContinuous (|s|⁻¹) (fun y => by
    rw [inv_mul_eq_div, le_div_iff₀ hs']
    have := hg y
    change ‖g y‖ * |s| ≤ ‖(y : H)‖
    linarith)
  have hdense : Dense (R : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, ← Submodule.orthogonal_orthogonal_eq_closure]
    have hb : Rᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro w hw
      apply hd w
      intro v
      exact (Submodule.mem_orthogonal' R w).1 hw _ (LinearMap.mem_range_self L v)
    rw [hb, Submodule.bot_orthogonal_eq_top]
  have hdr : DenseRange (R.subtypeL : R → H) := hdense.denseRange_val
  have hui : IsUniformInducing (R.subtypeL : R → H) := isUniformEmbedding_subtype_val.isUniformInducing
  refine ⟨gc.extend R.subtypeL, ?_, ?_⟩
  · intro v
    have h1 := ContinuousLinearMap.extend_eq gc hdr hui ⟨L v, LinearMap.mem_range_self L v⟩
    have h2 : e.symm ⟨L v, LinearMap.mem_range_self L v⟩ = v := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext (he v).symm
    calc gc.extend R.subtypeL (↑(A v) + (Complex.I * ↑s) • ↑v)
        = gc ⟨L v, LinearMap.mem_range_self L v⟩ := h1
      _ = ↑v := by
        show ((e.symm ⟨L v, LinearMap.mem_range_self L v⟩ : D) : H) = v
        rw [h2]
  · intro w
    refine hdense.induction (P := fun w => |s| * ‖gc.extend R.subtypeL w‖ ≤ ‖w‖) ?_ ?_ w
    · intro y hy
      have h1 : gc.extend R.subtypeL y = gc ⟨y, hy⟩ :=
        ContinuousLinearMap.extend_eq gc hdr hui ⟨y, hy⟩
      show |s| * ‖gc.extend R.subtypeL y‖ ≤ ‖y‖
      rw [h1]
      exact hg ⟨y, hy⟩
    · exact isClosed_le (continuous_const.mul (continuous_norm.comp (gc.extend R.subtypeL).continuous))
        continuous_norm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsLim
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem tendsto_zero_on_closure_of_lipschitz_family {H : Type} [NormedAddCommGroup H] (Q : ℕ → H → H)
    (hQ : ∀ k x y, ‖Q k x‖ ≤ ‖Q k y‖ + ‖x - y‖) (S : Set H)
    (hS : ∀ x ∈ S, Filter.Tendsto (fun k => Q k x) Filter.atTop (nhds 0)) (x : H)
    (hx : x ∈ closure S) :
    Filter.Tendsto (fun k => Q k x) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hyS, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hS y hyS) (ε / 2) (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  have h1 := hN k hk
  rw [dist_zero_right] at h1 ⊢
  rw [dist_eq_norm] at hxy
  calc ‖Q k x‖ ≤ ‖Q k y‖ + ‖x - y‖ := hQ k x y
    _ < ε / 2 + ε / 2 := add_lt_add h1 hxy
    _ = ε := by ring

theorem UpperTheory.V.Cj.H.absLim :
    UpperTheory.V.Cj.H.AbsLim := by
  intro H _ _ _ D A hA s hs hplus hminus T hT hTb P hP hPr w
  have hc : ∀ k, ‖(Complex.I * (s k : ℂ))‖ = |s k| := by
    intro k
    simp
  have hadj : ∀ k (v' : D), ContinuousLinearMap.adjoint (T k)
      ((A v' : H) - (Complex.I * (s k : ℂ)) • (v' : H)) = (v' : H) := by
    intro k v'
    apply sub_eq_zero.mp
    apply hplus k
    intro v
    rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left, hT k v]
    rw [inner_sub_left, inner_smul_left, inner_add_right, inner_smul_right, hA v' v]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hPfix : ∀ k, (Complex.I * (s k : ℂ)) • T k (P w) = P w := by
    intro k
    apply sub_eq_zero.mp
    apply hminus k
    intro v
    have h1 : inner ℂ (T k (P w)) ((A v : H) - (Complex.I * (s k : ℂ)) • (v : H))
        = inner ℂ (P w) (v : H) := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hadj k v]
    rw [inner_sub_left, inner_smul_left, h1, inner_sub_right, inner_smul_right, hP w v]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hr : Filter.Tendsto (fun k => (Complex.I * (s k : ℂ)) • T k (w - P w)) Filter.atTop
      (nhds 0) := by
    refine tendsto_zero_on_closure_of_lipschitz_family (fun k x => (Complex.I * (s k : ℂ)) • T k x) ?_
      (Set.range fun v : D => (A v : H)) ?_ (w - P w) ?_
    · intro k x y
      have e : (Complex.I * (s k : ℂ)) • T k x = (Complex.I * (s k : ℂ)) • T k y
          + (Complex.I * (s k : ℂ)) • T k (x - y) := by
        rw [map_sub, smul_sub]
        abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_smul, hc]
      exact hTb k (x - y)
    · rintro _ ⟨v, rfl⟩
      have e : ∀ k, (Complex.I * (s k : ℂ)) • T k (A v : H) = (Complex.I * (s k : ℂ)) • (v : H)
          - (Complex.I * (s k : ℂ)) • ((Complex.I * (s k : ℂ)) • T k (v : H)) := by
        intro k
        have h := hT k v
        rw [map_add (f := _), map_smul] at h
        rw [eq_sub_iff_add_eq, ← smul_add, h]
      apply squeeze_zero_norm (a := fun k => 2 * |s k| * ‖(v : H)‖)
      · intro k
        rw [e k]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, norm_smul, norm_smul, hc]
        have h2 := mul_le_mul_of_nonneg_left (hTb k (v : H)) (abs_nonneg (s k))
        linarith
      · have h3 : Filter.Tendsto (fun k => |s k|) Filter.atTop (nhds 0) := by
          simpa using hs.abs
        have h4 := (h3.const_mul 2).mul_const ‖(v : H)‖
        rwa [mul_zero, zero_mul] at h4
    · have h := hPr w
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range] at h
      exact h
  have hsum : ∀ k, (Complex.I * (s k : ℂ)) • T k w
      = P w + (Complex.I * (s k : ℂ)) • T k (w - P w) := by
    intro k
    rw [map_sub, smul_sub, hPfix k]
    abel
  have h5 := (tendsto_const_nhds (x := P w) (f := Filter.atTop)).add hr
  rw [add_zero] at h5
  exact h5.congr (fun k => (hsum k).symm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsSSProj
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem exists_orthogonal_decomposition_of_isPos {W : Type} [AddCommGroup W] [Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (M : Submodule ℂ W) (hB : IsPos B M) (F K : Submodule ℂ W) (hF : F ≤ M) (hK : K ≤ F)
    [FiniteDimensional ℂ F] (v : W) (hv : v ∈ F) :
    ∃ a ∈ K, ∃ b ∈ F, v = a + b ∧ ∀ x ∈ K, B x b = 0 := by
  letI core : InnerProductSpace.Core ℂ F :=
    { inner := fun x y => B x y
      conj_inner_symm := fun x y => by
        show (starRingEnd ℂ) (B y x) = B x y
        rw [hB.herm]; simp
      re_inner_nonneg := fun x => hB.nonneg x (hF x.2)
      add_left := fun x y z => by
        show B (x + y : F) z = B x z + B y z
        simp
      smul_left := fun x y r => by
        show B (r • x : F) y = (starRingEnd ℂ) r * B x y
        simp
      definite := fun x hx => Subtype.ext (hB.definite x (hF x.2) hx) }
  letI : NormedAddCommGroup F := InnerProductSpace.Core.toNormedAddCommGroup (cd := core)
  letI : InnerProductSpace ℂ F := InnerProductSpace.ofCore (𝕜 := ℂ) (F := F) inferInstance
  let K' : Submodule ℂ F := K.comap F.subtype
  haveI : CompleteSpace K' := FiniteDimensional.complete ℂ K'
  obtain ⟨y, hy, z, hz, hyz⟩ := K'.exists_add_mem_mem_orthogonal ⟨v, hv⟩
  refine ⟨y, hy, z, z.2, congrArg Subtype.val hyz, fun x hx => ?_⟩
  have := (Submodule.mem_orthogonal K' z).1 hz ⟨x, hK hx⟩ hx
  exact this

private theorem orbit_of_compact_finite_of_open_stabilizer {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (n : W) (U V : Subgroup G)
    (hUc : IsCompact (U : Set G)) (hVo : IsOpen (V : Set G)) (hVn : ∀ u ∈ V, ρ u n = n) :
    ((fun u => ρ u n) '' (U : Set G)).Finite := by
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover (fun u : U => (fun g => (u : G)⁻¹ * g) ⁻¹' (V : Set G))
    (fun u => hVo.preimage (continuous_const.mul continuous_id))
    (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp [V.one_mem]⟩)
  apply ((t : Set U).toFinite.image (fun u : U => ρ (u : G) n)).subset
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨u, hu, hgu⟩ := Set.mem_iUnion₂.1 (ht hg)
  refine ⟨u, hu, ?_⟩
  have hg' : g = (u : G) * ((u : G)⁻¹ * g) := by group
  show ρ (u : G) n = ρ g n
  rw [hg', map_mul, Module.End.mul_apply, hVn _ hgu]

theorem UpperTheory.V.Cj.H.absSS :
    UpperTheory.V.Cj.H.AbsSS := by
  intro G W _ _ _ _ _ ρ M B hB hM hc hsm hfd N hNM hN
  have hρ : ∀ (g h : G) (x : W), ρ g (ρ h x) = ρ (g * h) x := by
    intro g h x
    rw [map_mul, Module.End.mul_apply]
  let N' : Submodule ℂ W :=
    { carrier := {w | w ∈ M ∧ ∀ n ∈ N, B n w = 0}
      add_mem' := fun {a b} ha hb => ⟨M.add_mem ha.1 hb.1, fun n hn => by simp [ha.2 n hn, hb.2 n hn]⟩
      zero_mem' := ⟨M.zero_mem, fun n _ => by simp⟩
      smul_mem' := fun r w hw => ⟨M.smul_mem r hw.1, fun n hn => by simp [hw.2 n hn]⟩ }
  have memN' : ∀ w, w ∈ N' ↔ w ∈ M ∧ ∀ n ∈ N, B n w = 0 := fun w => Iff.rfl
  refine ⟨N', fun w hw => ((memN' w).1 hw).1, ?_, ?_, ?_⟩
  · intro g w hw
    rw [memN'] at hw ⊢
    refine ⟨hM g w hw.1, fun n hn => ?_⟩
    obtain ⟨c, hcg⟩ := hc g
    have hn' : ρ g⁻¹ n ∈ N := hN _ _ hn
    have h1 : ρ g (ρ g⁻¹ n) = n := by rw [hρ, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← h1, hcg _ (hNM hn') _ hw.1, hw.2 _ hn', mul_zero]
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxN, hxN'⟩ := Submodule.mem_inf.1 hx
    rw [memN'] at hxN'
    exact (Submodule.mem_bot ℂ).2 (hB.definite x (hNM hxN) (hxN'.2 x hxN))
  · refine le_antisymm (sup_le hNM fun w hw => ((memN' w).1 hw).1) ?_
    intro v hv
    obtain ⟨U, hUo, hUc, hUv⟩ := hsm v hv
    haveI := hfd U hUo
    have hFM : Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x} ≤ M :=
      Submodule.span_le.2 fun x hx => hx.1
    have hFfix : ∀ x ∈ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x}, ∀ u ∈ U, ρ u x = x := by
      intro x hx u hu
      induction hx using Submodule.span_induction with
      | mem y hy => exact hy.2 u hu
      | zero => simp
      | add y z _ _ hy hz => simp [hy, hz]
      | smul r y _ hy => simp [hy]
    have hvF : v ∈ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x} :=
      Submodule.subset_span ⟨hv, hUv⟩
    obtain ⟨a, haK, b, hbF, hvab, hb⟩ :=
      exists_orthogonal_decomposition_of_isPos B M hB _ (N ⊓ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x}) hFM inf_le_right v hvF
    rw [hvab]
    refine Submodule.add_mem_sup (Submodule.mem_inf.1 haK).1 ((memN' b).2 ⟨hFM hbF, fun n hn => ?_⟩)
    have hinv : ∀ u ∈ U, ∀ x ∈ M, B (ρ u x) b = B x b := by
      intro u hu x hx
      obtain ⟨c, hcu⟩ := hc u
      have h1 := hcu x hx b (hFM hbF)
      rw [hFfix b hbF u hu] at h1
      by_cases hb0 : b = 0
      · simp [hb0]
      have h2 := hcu b (hFM hbF) b (hFM hbF)
      rw [hFfix b hbF u hu] at h2
      have hbb : B b b ≠ 0 := fun h => hb0 (hB.definite b (hFM hbF) h)
      have hc1 : c = 1 := by
        have h3 : (c - 1) * B b b = 0 := by rw [sub_mul, ← h2]; ring
        rcases mul_eq_zero.1 h3 with h | h
        · exact sub_eq_zero.1 h
        · exact absurd h hbb
      rw [h1, hc1, one_mul]
    obtain ⟨V, hVo, -, hVn⟩ := hsm n (hNM hn)
    have hfin := orbit_of_compact_finite_of_open_stabilizer ρ n U V hUc hVo hVn
    have hmemS : ∀ x, x ∈ hfin.toFinset ↔ ∃ g ∈ U, ρ g n = x := by
      intro x
      rw [Set.Finite.mem_toFinset]
      rfl
    have hSN : ∀ x ∈ hfin.toFinset, x ∈ N ∧ B x b = B n b := by
      intro x hx
      obtain ⟨g, hg, rfl⟩ := (hmemS x).1 hx
      exact ⟨hN g n hn, hinv g hg n (hNM hn)⟩
    have hsN : (∑ x ∈ hfin.toFinset, x) ∈ N := Submodule.sum_mem _ fun x hx => (hSN x hx).1
    have hsfix : ∀ u ∈ U, ρ u (∑ x ∈ hfin.toFinset, x) = ∑ x ∈ hfin.toFinset, x := by
      intro u hu
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_nbij' (fun x => ρ u x) (fun x => ρ u⁻¹ x) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
      · intro x hx
        obtain ⟨g, hg, rfl⟩ := (hmemS x).1 hx
        exact (hmemS _).2 ⟨u * g, U.mul_mem hu hg, (hρ u g n).symm⟩
      · intro x hx
        obtain ⟨g, hg, rfl⟩ := (hmemS x).1 hx
        exact (hmemS _).2 ⟨u⁻¹ * g, U.mul_mem (U.inv_mem hu) hg, (hρ u⁻¹ g n).symm⟩
      · intro x _
        rw [hρ, inv_mul_cancel, map_one, Module.End.one_apply]
      · intro x _
        rw [hρ, mul_inv_cancel, map_one, Module.End.one_apply]
    have hsF : (∑ x ∈ hfin.toFinset, x) ∈ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x} :=
      Submodule.subset_span ⟨hNM hsN, hsfix⟩
    have hzero := hb _ (Submodule.mem_inf.2 ⟨hsN, hsF⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply, Finset.sum_congr rfl fun x hx => (hSN x hx).2,
      Finset.sum_const, nsmul_eq_mul] at hzero
    have hcard : (hfin.toFinset.card : ℂ) ≠ 0 := by
      have : n ∈ hfin.toFinset := (hmemS n).2 ⟨1, U.one_mem, by simp⟩
      exact_mod_cast (Finset.card_pos.2 ⟨n, this⟩).ne'
    exact (mul_eq_zero.1 hzero).resolve_left hcard
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsSolve
section
noncomputable section

open Filter Topology

namespace UpperTheory.V.Cj.H

set_option maxHeartbeats 400000 in
theorem absSolve : AbsSolve := by
  intro I J L c cn hcn hlim
  classical
  let ψ : (J →₀ ℂ) →ₗ[ℂ] (I →₀ ℂ) := Finsupp.linearCombination ℂ L
  let φ : (J →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ c
  have hsum : ∀ (b : I → ℂ) (v : I →₀ ℂ),
      (v.sum fun i x => x * b i) = Finsupp.linearCombination ℂ b v := by
    intro b v
    rw [Finsupp.linearCombination_apply]
    rfl
  have hcomp : ∀ (b : I → ℂ), (Finsupp.linearCombination ℂ b) ∘ₗ ψ
      = Finsupp.linearCombination ℂ (fun j => Finsupp.linearCombination ℂ b (L j)) := by
    intro b
    apply Finsupp.lhom_ext
    intro j x
    simp [ψ, Finsupp.linearCombination_single]
  have hker : LinearMap.ker ψ ≤ LinearMap.ker φ := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    have h0 : ∀ k, Finsupp.linearCombination ℂ (cn k) a = 0 := by
      intro k
      obtain ⟨b, hb⟩ := hcn k
      have h1 := congrArg (fun m => m a) (hcomp b)
      simp only [LinearMap.comp_apply, ha, map_zero] at h1
      rw [show cn k = fun j => Finsupp.linearCombination ℂ b (L j) from
        funext fun j => ((hsum b (L j)).symm.trans (hb j)).symm]
      exact h1.symm
    have hT : Tendsto (fun k => Finsupp.linearCombination ℂ (cn k) a) atTop (𝓝 (φ a)) := by
      simp only [φ, Finsupp.linearCombination_apply, Finsupp.sum]
      apply tendsto_finsetSum
      intro j _
      exact (hlim j).const_smul (a j)
    simp only [h0] at hT
    exact tendsto_nhds_unique hT tendsto_const_nhds
  let f0 : LinearMap.range ψ →ₗ[ℂ] ℂ :=
    ((LinearMap.ker ψ).liftQ φ hker) ∘ₗ
      (ψ.quotKerEquivRange.symm : LinearMap.range ψ →ₗ[ℂ] (J →₀ ℂ) ⧸ LinearMap.ker ψ)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f0
  have hgψ : ∀ a, g (ψ a) = φ a := by
    intro a
    have h2 := congrArg (fun m => m ⟨ψ a, LinearMap.mem_range_self ψ a⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h2]
    simp [f0, LinearMap.quotKerEquivRange_symm_apply_image]
  have hgb : Finsupp.linearCombination ℂ (fun i => g (Finsupp.single i 1)) = g := by
    apply Finsupp.lhom_ext
    intro i x
    rw [Finsupp.linearCombination_single, ← map_smul, Finsupp.smul_single_one]
  refine ⟨fun i => g (Finsupp.single i 1), fun j => ?_⟩
  refine (hsum (fun i => g (Finsupp.single i 1)) (L j)).trans ?_
  rw [hgb]
  have h3 := hgψ (Finsupp.single j 1)
  simpa [ψ, φ, Finsupp.linearCombination_single] using h3

end UpperTheory.V.Cj.H
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ConeCpt
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.coneCpt :
    UpperTheory.V.Cj.H.ConeCpt := by
  intro E _ _ a K hK hKc
  refine ⟨_, (UpperTheory.V.Cj.A.sandCpt E a).2 K hK hKc, fun p hp => ?_⟩
  obtain ⟨g, rfl⟩ := hK hp
  exact ⟨g, hp, rfl⟩
end

