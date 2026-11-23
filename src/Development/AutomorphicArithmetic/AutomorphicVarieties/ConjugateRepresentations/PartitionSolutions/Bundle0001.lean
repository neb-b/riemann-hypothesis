module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.HdFacts
section
open UpperTheory.V.Cj.A UpperTheory.V.Lit.Geo

private theorem hd_cons' {I M : Type} [AddCommGroup M] (c : List I → M) (i : I) (x : List I) :
    hd c (i :: x) = c x - hd (fun y => c (i :: y)) x := by
  unfold hd
  rw [List.length_cons, Finset.sum_range_succ', sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp [pow_succ]

private theorem hd_sub' {I M : Type} [AddCommGroup M] (c c' : List I → M) (x : List I) :
    hd (fun y => c y - c' y) x = hd c x - hd c' x := by
  unfold hd
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => smul_sub _ _ _

private theorem hd_hd' {I M : Type} [AddCommGroup M] (x : List I) :
    ∀ c : List I → M, hd (hd c) x = 0 := by
  induction x with
  | nil => intro c; simp [hd]
  | cons i x ih =>
    intro c
    rw [hd_cons']
    have h : (fun y => hd c (i :: y)) = fun y => c y - hd (fun z => c (i :: z)) y :=
      funext fun y => hd_cons' c i y
    rw [h, hd_sub', ih]
    simp

private theorem hd_map' {I J M : Type} [AddCommGroup M] (f : J → I) (c : List I → M) (x : List J) :
    hd (fun y => c (y.map f)) x = hd c (x.map f) := by
  unfold hd
  rw [List.length_map]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [List.eraseIdx_map]

private theorem hd_hom' {I M N : Type} [AddCommGroup M] [AddCommGroup N] (f : M →+ N) (c : List I → M)
    (x : List I) : hd (fun y => f (c y)) x = f (hd c x) := by
  unfold hd
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => (map_zsmul f _ _).symm

private theorem hd_congr' {I M : Type} [AddCommGroup M] (c c' : List I → M) (x : List I)
    (h : ∀ y : List I, y.length + 1 = x.length → (∀ i ∈ y, i ∈ x) → c y = c' y) : hd c x = hd c' x := by
  unfold hd
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < x.length := Finset.mem_range.1 hj
  rw [h (x.eraseIdx j) (by rw [List.length_eraseIdx_of_lt hj']; omega)
    (fun i hi => List.mem_of_mem_eraseIdx hi)]

theorem UpperTheory.V.Cj.A.hdFacts :
    HdFacts := by
  refine ⟨fun I M _ c x => hd_hd' x c, fun I M _ c i x => hd_cons' c i x,
    fun I J M _ f c x => hd_map' f c x, fun I M N _ _ f c x => hd_hom' f c x,
    fun I M _ c c' x h => hd_congr' c c' x h, ?_⟩
  intro Γ I M _ _ _ _ ρ k c hc γ x hx
  rw [← hd_map']
  refine Eq.trans (hd_congr' _ (fun y => (ρ γ).toAddMonoidHom (c y)) x fun y hy _ => ?_)
    (hd_hom' (ρ γ).toAddMonoidHom c x)
  exact hc γ y (by omega)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.OrbClosed
section
open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.orbClosed :
    OrbClosed := by
  intro Γ V S _ _ _ _ d G hG K hKY hK s s'
  unfold UpperTheory.V.Lit.Dr.Geo.Proper at hG
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨hpY, hpA⟩
  obtain ⟨L, hLn, hLY, hL⟩ := local_compact_nhds (G.isOpen.mem_nhds hpY)
  have hFfin : {γ | (G.σ γ) s = s' ∧ ∃ q ∈ L ∪ K, (G.ρ γ) q ∈ L ∪ K}.Finite :=
    hG (L ∪ K) (Set.union_subset hLY hKY) (hL.union hK) s s'
  set F := {γ | (G.σ γ) s = s' ∧ ∃ q ∈ L ∪ K, (G.ρ γ) q ∈ L ∪ K} with hF
  have hBc : IsClosed (⋃ γ ∈ F, (G.ρ γ) ⁻¹' K) :=
    hFfin.isClosed_biUnion fun γ _ => hK.isClosed.preimage (G.ρ γ).continuous
  have hpB : p ∉ ⋃ γ ∈ F, (G.ρ γ) ⁻¹' K := by
    simp only [Set.mem_iUnion, Set.mem_preimage, not_exists]
    intro γ hγF hγ
    exact hpA ⟨γ, hγF.1, hγ⟩
  have hnb : (⋃ γ ∈ F, (G.ρ γ) ⁻¹' K)ᶜ ∈ nhds p := hBc.isOpen_compl.mem_nhds hpB
  filter_upwards [hLn, hnb] with q hqL hqB
  refine ⟨hLY hqL, ?_⟩
  rintro ⟨γ, hσ, hγ⟩
  apply hqB
  simp only [Set.mem_iUnion, Set.mem_preimage]
  exact ⟨γ, ⟨hσ, q, Or.inl hqL, Or.inr hγ⟩, hγ⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PartBase
section
noncomputable section

open scoped ContDiff Manifold Topology

namespace UpperTheory.V.Cj.A

theorem partBase : PartBase := by
  intro V _ _ _ Y hY D hD hDp
  let Y' : TopologicalSpace.Opens V := ⟨Y, hY⟩
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  haveI : LocallyCompactSpace Y' := Y'.isOpen.locallyCompactSpace
  haveI : SecondCountableTopology V := inferInstance
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, V) (M := Y') isClosed_univ
    (fun j => ((↑) : Y' → V) ⁻¹' D j) (fun j => (hD j).preimage continuous_subtype_val)
    (fun x _ => Set.mem_iUnion.2 ⟨(x : V), hDp x x.2⟩)
  classical
  refine ⟨fun j p => if h : p ∈ Y then f j ⟨p, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    let g : V → ℝ := fun p => if h : p ∈ Y then f j ⟨p, h⟩ else 0
    have h1 : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ) ∞ (fun y : Y' => g (y : V)) ⟨x, hx⟩ := by
      have e : (fun y : Y' => g (y : V)) = f j := by
        funext y
        exact dif_pos y.2
      rw [e]
      exact (f j).contMDiff.contMDiffAt
    have h2 : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ) ∞ g x :=
      (contMDiffAt_subtype_iff (U := Y') (f := g) (x := ⟨x, hx⟩)).1 h1
    exact (contMDiffAt_iff_contDiffAt.1 h2).contDiffWithinAt
  · intro p hp
    obtain ⟨t, ht, htf⟩ := f.locallyFinite ⟨p, hp⟩
    obtain ⟨N, hN, hNt⟩ := (mem_nhds_subtype _ _ _).1 ht
    refine ⟨N, hN, htf.subset ?_⟩
    rintro j ⟨x, hxN, hne⟩
    by_cases hxY : x ∈ Y
    · have h : f j ⟨x, hxY⟩ ≠ 0 := by simpa [hxY] using hne
      exact ⟨⟨x, hxY⟩, h, hNt hxN⟩
    · exact (hne (dif_neg hxY)).elim
  · intro p hp
    refine Eq.trans ?_ (f.sum_eq_one (x := ⟨p, hp⟩) (Set.mem_univ _))
    exact finsum_congr fun j => dif_pos hp
  · intro j p hne
    by_cases hpY : p ∈ Y
    · have h : f j ⟨p, hpY⟩ ≠ 0 := by simpa [hpY] using hne
      exact hf j (subset_tsupport _ h)
    · exact (hne (dif_neg hpY)).elim

end UpperTheory.V.Cj.A
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PartMem
section
open UpperTheory.V.Cj.A UpperTheory.V.Lit
open scoped ContDiff

theorem UpperTheory.V.Cj.A.partMem :
    PartMem := by
  intro Γ V S I _ _ _ _ d G φ hφ q c
  rw [Dr.Geo.mem_Om]
  intro s
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨N, hN, hfin⟩ := hφ.locFin s p hp
    have hsum : ContDiffAt ℝ ∞ (fun x => ∑ i ∈ hfin.toFinset, φ i s x • (c i).1 s x) p :=
      ContDiffAt.sum fun i _ =>
        ((hφ.smooth i s).contDiffAt (G.isOpen.mem_nhds hp)).smul (Dr.Geo.contDiffAt_Om (c i) s hp)
    refine (hsum.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hN] with x hx
    refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
    rw [Set.Finite.coe_toFinset]
    refine ⟨x, hx, fun h => hi ?_⟩
    simp only [h, zero_smul]
  · have h : ∀ i : I, φ i s p • (c i).1 s p = 0 := fun i => by
      rw [((c i).2 s).2 p hp, smul_zero]
    simp only [h, finsum_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PartProd
section
open UpperTheory.V.Cj.A UpperTheory.V.Lit UpperTheory.V.Lit.Dr
open scoped ContDiff

private def UpperTheory.V.Cj.A.idxEquiv (Γ J : Type) : Γ × J ≃ Idx Γ J where
  toFun x := ⟨x.1, x.2⟩
  invFun i := (i.g, i.j)
  left_inv _ := rfl
  right_inv _ := rfl

theorem UpperTheory.V.Cj.A.partProd :
    PartProd := by
  intro Γ V S J _ _ _ d G u hu ψ hψs hψf hψ1
  obtain ⟨hus, huf, hu1⟩ := hu
  have hlf : ∀ s, ∀ p ∈ G.Y, ∃ N ∈ nhds p, {i : Idx Γ J | ∃ x ∈ N,
      u ((G.σ i.g⁻¹) s) ((G.ρ i.g⁻¹) x) * ψ ((G.σ i.g⁻¹) s) i.j ((G.ρ i.g⁻¹) x) ≠ 0}.Finite := by
    intro s p hp
    obtain ⟨N₁, hN₁, hF⟩ := huf s p hp
    have key : ∀ γ : Γ, ∃ M ∈ nhds p,
        {j | ∃ x ∈ M, ψ ((G.σ γ⁻¹) s) j ((G.ρ γ⁻¹) x) ≠ 0}.Finite := by
      intro γ
      obtain ⟨M, hM, hMf⟩ := hψf ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) p) (G.maps _ p hp)
      refine ⟨(G.ρ γ⁻¹) ⁻¹' M, (G.ρ γ⁻¹).continuous.continuousAt.preimage_mem_nhds hM, ?_⟩
      refine hMf.subset ?_
      rintro j ⟨x, hx, hne⟩
      exact ⟨_, hx, hne⟩
    choose M hM hMf using key
    refine ⟨N₁ ∩ ⋂ γ ∈ hF.toFinset, M γ, ?_, ?_⟩
    · exact Filter.inter_mem hN₁ ((Filter.biInter_finset_mem _).2 fun γ _ => hM γ)
    · refine ((hF.toFinset.finite_toSet.biUnion fun γ _ =>
        (Set.finite_singleton γ).prod (hMf γ)).image (idxEquiv Γ J)).subset ?_
      rintro ⟨g, j⟩ ⟨x, ⟨hx1, hx2⟩, hne⟩
      have hu0 : u ((G.σ g⁻¹) s) ((G.ρ g⁻¹) x) ≠ 0 := left_ne_zero_of_mul hne
      have hψ0 : ψ ((G.σ g⁻¹) s) j ((G.ρ g⁻¹) x) ≠ 0 := right_ne_zero_of_mul hne
      have hgF : g ∈ hF.toFinset := hF.mem_toFinset.2 ⟨x, hx1, hu0⟩
      refine ⟨(g, j), Set.mem_biUnion (x := g) hgF ⟨Set.mem_singleton _, x, ?_, hψ0⟩, rfl⟩
      exact Set.mem_iInter₂.1 hx2 g hgF
  refine ⟨?_, hlf, ?_, ?_⟩
  · intro i s
    have hmap : Set.MapsTo (G.ρ i.g⁻¹) G.Y G.Y := fun p hp => G.maps _ p hp
    exact ((hus _).comp (G.ρ i.g⁻¹).contDiff.contDiffOn hmap).mul
      ((hψs _ _).comp (G.ρ i.g⁻¹).contDiff.contDiffOn hmap)
  · intro s p hp
    have hfin : (Function.support fun x : Γ × J =>
        u ((G.σ x.1⁻¹) s) ((G.ρ x.1⁻¹) p) * ψ ((G.σ x.1⁻¹) s) x.2 ((G.ρ x.1⁻¹) p)).Finite := by
      obtain ⟨N, hN, hNf⟩ := hlf s p hp
      refine (hNf.preimage (idxEquiv Γ J).injective.injOn).subset ?_
      intro x hx
      exact ⟨p, mem_of_mem_nhds hN, hx⟩
    rw [← finsum_comp_equiv (idxEquiv Γ J)]
    show ∑ᶠ x : Γ × J, u ((G.σ x.1⁻¹) s) ((G.ρ x.1⁻¹) p) *
      ψ ((G.σ x.1⁻¹) s) x.2 ((G.ρ x.1⁻¹) p) = 1
    rw [finsum_curry _ (by exact hfin)]
    have hin : ∀ a : Γ, ∑ᶠ b : J, u ((G.σ a⁻¹) s) ((G.ρ a⁻¹) p) * ψ ((G.σ a⁻¹) s) b ((G.ρ a⁻¹) p) =
        u ((G.σ a⁻¹) s) ((G.ρ a⁻¹) p) := by
      intro a
      rw [← mul_finsum, hψ1 _ _ (G.maps _ _ hp), mul_one]
    rw [finsum_congr hin]
    exact hu1 s p hp
  · intro γ i s p
    have h1 : (G.σ γ⁻¹) ((G.σ γ) s) = s := by
      rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply]
    have h2 : (G.ρ γ⁻¹) ((G.ρ γ) p) = p := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
    show u ((G.σ (γ * i.g)⁻¹) ((G.σ γ) s)) ((G.ρ (γ * i.g)⁻¹) ((G.ρ γ) p)) *
      ψ ((G.σ (γ * i.g)⁻¹) ((G.σ γ) s)) i.j ((G.ρ (γ * i.g)⁻¹) ((G.ρ γ) p)) = _
    rw [mul_inv_rev, map_mul, map_mul, Equiv.Perm.mul_apply, ContinuousLinearMap.mul_apply, h1, h2]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PullAct
section
open UpperTheory.V.Cj.A UpperTheory.V.Lit.Dr Matrix

theorem UpperTheory.V.Cj.A.pullAct :
    PullAct := by
  intro Γ V S _ _ _ d G _hcone l hl q P hP γ w
  have hinv : ∀ x : V, G.ρ γ (G.ρ γ⁻¹ x) = x := by
    intro x
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
  have hinv' : ∀ x : V, G.ρ γ⁻¹ (G.ρ γ x) = x := by
    intro x
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
  have hinvS : ∀ s : S, G.σ γ (G.σ γ⁻¹ s) = s := by
    intro s
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  apply Subtype.ext
  funext s p
  by_cases hp : p ∈ G.Y
  · have hp' : G.ρ γ⁻¹ p ∈ G.Y := G.maps _ _ hp
    have hleq : l (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) = l s p := by
      have := hl.2 γ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) hp'
      rw [hinvS, hinv] at this
      exact this.symm
    have hdiff : DifferentiableAt ℝ (l s) p :=
      ((hl.1 s).1.contDiffAt (G.isOpen.mem_nhds hp)).differentiableAt (by simp)
    have hf : HasFDerivAt (fun x => l s x • x) (fderiv ℝ (fun x => l s x • x) p) (G.ρ γ (G.ρ γ⁻¹ p)) := by
      rw [hinv]
      exact (hdiff.smul differentiableAt_id).hasFDerivAt
    have hcomp := (G.ρ γ⁻¹).hasFDerivAt.comp (G.ρ γ⁻¹ p) (hf.comp (G.ρ γ⁻¹ p) (G.ρ γ).hasFDerivAt)
    have heq : (fun x => l (G.σ γ⁻¹ s) x • x) =ᶠ[nhds (G.ρ γ⁻¹ p)]
        (⇑(G.ρ γ⁻¹) ∘ ((fun x => l s x • x) ∘ ⇑(G.ρ γ))) := by
      filter_upwards [G.isOpen.mem_nhds hp'] with x hx
      have := hl.2 γ (G.σ γ⁻¹ s) x hx
      rw [hinvS] at this
      simp only [Function.comp_apply, map_smul, hinv', this]
    have hder : ∀ u : V, fderiv ℝ (fun x => l (G.σ γ⁻¹ s) x • x) (G.ρ γ⁻¹ p) (G.ρ γ⁻¹ u)
        = G.ρ γ⁻¹ (fderiv ℝ (fun x => l s x • x) p u) := by
      intro u
      rw [(hcomp.congr_of_eventuallyEq heq).fderiv]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, hinv]
    ext v
    rw [G.act_apply, hP w _ _ hp', hP _ s p hp]
    simp only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply, G.act_apply]
    rw [hleq, map_smul]
    simp only [Function.comp_def, hder]
  · have hnot : G.ρ γ⁻¹ p ∉ G.Y := by
      intro h
      exact hp (hinv p ▸ G.maps γ _ h)
    have h1 := ((P w).2 (G.σ γ⁻¹ s)).2 _ hnot
    have h2 := ((P (G.act q γ w)).2 s).2 p hp
    rw [h2]
    ext v
    rw [G.act_apply, h1]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PullOp
section
open UpperTheory.V.Cj.A UpperTheory.V.Lit.Dr
open scoped ContDiff

theorem UpperTheory.V.Cj.A.pullOp :
    PullOp := by
  intro Γ V S _ _ _ _ d G hC l hl
  have hY : IsOpen G.Y := G.isOpen
  have hpos : ∀ s, ∀ p ∈ G.Y, l s p • p ∈ G.Y := fun s p hp => hC _ ((hl.1 s).2.1 p hp) p hp
  have hw : ∀ q (w : G.Om q) (s : S),
      ContDiffOn ℝ ∞ ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
        ∀ p ∉ G.Y, (w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0 := fun q w => w.2
  have mem : ∀ q (w : G.Om q), (fun s => G.Y.indicator
      (pull (l s) ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s))) ∈ G.Om q := by
    intro q w s
    refine ⟨?_, fun p hp => Set.indicator_apply_eq_zero.2 fun h => absurd h hp⟩
    exact (pullB V (Fin d → ℂ) G.Y hY hC (l s) (hl.1 s) q _ (hw q w s).1).1.congr
      fun p hp => Set.indicator_of_mem hp _
  have padd : ∀ q (s : S) (a b : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (p : V),
      pull (l s) (a + b) p = pull (l s) a p + pull (l s) b p := by
    intro q s a b p
    ext v
    simp [pull]
  have psmul : ∀ q (s : S) (c : ℂ) (a : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (p : V),
      pull (l s) (c • a) p = c • pull (l s) a p := by
    intro q s c a p
    ext v
    simp [pull]
  have ext_ind : ∀ q (om : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) p, p ∈ G.Y →
      extDeriv (G.Y.indicator om) p = extDeriv om p := by
    intro q om p hp
    simp only [extDeriv]
    rw [Filter.EventuallyEq.fderiv_eq
      (Filter.eventuallyEq_of_mem (hY.mem_nhds hp) fun x hx => Set.indicator_of_mem hx om)]
  let P : ∀ q, G.Om q →ₗ[ℂ] G.Om q := fun q =>
    { toFun := fun w => ⟨_, mem q w⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        funext s p
        simp only [Submodule.coe_add, Pi.add_apply]
        by_cases hp : p ∈ G.Y
        · simp only [Set.indicator_of_mem hp]
          exact padd q s _ _ p
        · simp [Set.indicator, hp]
      map_smul' := by
        intro c a
        apply Subtype.ext
        funext s p
        simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
        by_cases hp : p ∈ G.Y
        · simp only [Set.indicator_of_mem hp]
          exact psmul q s c _ p
        · simp [Set.indicator, hp] }
  refine ⟨P, ?_, ?_, ?_⟩
  · intro q w s p hp
    exact Set.indicator_of_mem hp _
  · intro q w
    apply Subtype.ext
    funext s p
    by_cases hp : p ∈ G.Y
    · rw [Geo.dOm_apply G _ s hp]
      change extDeriv (G.Y.indicator _) p = G.Y.indicator _ p
      rw [ext_ind _ _ _ hp, Set.indicator_of_mem hp,
        (pullB V (Fin d → ℂ) G.Y hY hC (l s) (hl.1 s) q _ (hw q w s).1).2 p hp]
      simp only [pull]
      rw [Geo.dOm_apply G w s (hpos s p hp)]
    · exact ((hw _ _ s).2 p hp).trans ((hw _ _ s).2 p hp).symm
  · intro f
    apply Subtype.ext
    funext s p
    by_cases hp : p ∈ G.Y
    · change G.Y.indicator _ p = _
      rw [Set.indicator_of_mem hp]
      ext v
      simp only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply]
      rw [Geo.incl_apply G f s (hpos s p hp), Geo.incl_apply G f s hp]
    · exact ((hw _ _ s).2 p hp).trans ((hw _ _ s).2 p hp).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.RelPoin
section
open UpperTheory.V.Cj.A UpperTheory.V.Lit.Dr
open Set ContinuousAlternatingMap
open scoped ContDiff

theorem UpperTheory.V.Cj.A.relPoin :
    RelPoin := by
  intro V F _ _ _ _ _ _ Y C hY hconv hC hCY q w hw hd hwC
  rcases C.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀C⟩
  · obtain ⟨η, h1, h2⟩ := poincare V F Y hY hconv q w hw hd
    exact ⟨η, h1, h2, fun p hp => hp.elim⟩
  have hp₀ : p₀ ∈ Y := hCY hp₀C
  have hseg : ContDiff ℝ ∞ (fun z : V × ℝ => p₀ + z.2 • (z.1 - p₀)) := by fun_prop
  set U : Set (V × ℝ) := (fun z : V × ℝ => p₀ + z.2 • (z.1 - p₀)) ⁻¹' Y with hU
  have hUo : IsOpen U := hY.preimage hseg.continuous
  have hmem : ∀ p ∈ Y, ∀ t ∈ Icc (0 : ℝ) 1, p₀ + t • (p - p₀) ∈ Y :=
    fun p hp t ht => hconv.add_smul_sub_mem hp₀ hp ht
  let Φ : V × ℝ → V [⋀^Fin q]→L[ℝ] F :=
    fun z => z.2 ^ q • (w (p₀ + z.2 • (z.1 - p₀))).curryLeft (z.1 - p₀)
  have hΦ : ContDiffOn ℝ ∞ Φ U := by
    have h1 : ContDiffOn ℝ ∞ (fun z : V × ℝ => w (p₀ + z.2 • (z.1 - p₀))) U :=
      hw.comp hseg.contDiffOn fun z hz => hz
    have h2 : ContDiffOn ℝ ∞ (fun z : V × ℝ => (w (p₀ + z.2 • (z.1 - p₀))).curryLeft) U :=
      (curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap.contDiff.comp_contDiffOn h1
    exact (contDiff_snd.pow q).contDiffOn.smul
      (h2.clm_apply (contDiff_fst.sub contDiff_const).contDiffOn)
  refine ⟨fun p => ∫ t in (0 : ℝ)..1, Φ (p, t),
    paramSmooth V _ Y U Φ hY hUo (fun z hz => hmem z.1 hz.1 z.2 hz.2) hΦ, fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨hc, hD⟩ := paramDeriv V _ p U Φ hUo (hmem p hp) hΦ
    have hI := hc.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) zero_le_one
    have hI' := ((alternatizeUncurryFinCLM ℝ V F).continuous.comp_continuousOn hc).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) zero_le_one
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r : ℝ => r ^ (q + 1) • w (p₀ + r • (p - p₀)))
        (alternatizeUncurryFinCLM ℝ V F (fderiv ℝ (fun x => Φ (x, t)) p)) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hm := hmem p hp t ht
      exact poinPt V F q w p₀ p t
        ((hw.contDiffAt (hY.mem_nhds hm)).differentiableAt (by simp)) (hd _ hm)
    have h3 := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hI'
    rw [(alternatizeUncurryFinCLM ℝ V F).intervalIntegral_comp_comm hI, ← hD.fderiv] at h3
    refine Eq.trans h3 ?_
    simp
  · have h0 : ∀ t ∈ uIcc (0 : ℝ) 1, Φ (p, t) = (fun _ => 0) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hz : w (p₀ + t • (p - p₀)) = 0 := hwC _ (hC.add_smul_sub_mem hp₀C hp ht)
      show t ^ q • (w (p₀ + t • (p - p₀))).curryLeft (p - p₀) = 0
      rw [hz]
      ext v
      simp
    show ∫ t in (0 : ℝ)..1, Φ (p, t) = 0
    rw [intervalIntegral.integral_congr h0]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SandCpt
section
open UpperTheory.V.Cj.A
open Matrix NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Cj.A.sandCpt :
    SandCpt := by
  intro E _ _ a
  have hcont : Continuous (fun g : GL (Fin a) (Cinf E) => sand g (hOne E a)) := by
    refine Continuous.subtype_mk (f := fun g : GL (Fin a) (Cinf E) => (sand g (hOne E a)).1) ?_ _
    change Continuous fun g : GL (Fin a) (Cinf E) =>
      (g.val * Matrix.of (hOne E a).1 * star g.val : Matrix (Fin a) (Fin a) (Cinf E))
    exact (Units.continuous_val.mul continuous_const).mul Units.continuous_val.star
  refine ⟨hcont, fun K hK hKc => ?_⟩
  obtain ⟨C, hC⟩ := boundInf E a (insert (hOne E a) K) (Set.insert_subset hOne_mem_cone hK) (hKc.insert _)
  have hB : IsCompact {m : Matrix (Fin a) (Fin a) (Cinf E) | ‖toL m‖ ≤ C} := by
    have h : IsCompact (Metric.closedBall (0 : Fin a → Fin a → Cinf E) C) := isCompact_closedBall _ _
    have e : Metric.closedBall (0 : Fin a → Fin a → Cinf E) C = {m | ‖m‖ ≤ C} := by
      ext m; simp
    rw [e] at h
    exact h
  have hT := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin a) (Fin a) (Cinf E))).isCompact_preimage
    (hB.prod (hB.image MulOpposite.continuous_op))
  refine hT.of_isClosed_subset (hKc.isClosed.preimage hcont) fun g hg => ⟨?_, (g⁻¹).val, ?_, rfl⟩
  · exact hC g _ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ hg)
  · refine hC g⁻¹ _ (Set.mem_insert_of_mem _ hg) ?_
    have e : sand g⁻¹ (sand g (hOne E a)) = hOne E a := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [e]
    exact Set.mem_insert _ _
end

