module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Acyclic
section
noncomputable section

open CategoryTheory

namespace UpperTheory.V.Lit.Dr

theorem acyclic : Acyclic := by
  intro Γ Ω _ _ _ ρ hP n
  obtain ⟨P, hconst, hequi⟩ := hP
  let S : Subgroup Γ := ⊥
  haveI : Subsingleton S := ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)⟩
  let A : Rep ℂ S := Rep.of (Representation.trivial ℂ S Ω)
  let C : Rep ℂ Γ := Rep.coind S.subtype A
  have hC : Subsingleton (groupCohomology C (n + 1)) := by
    have hz : Limits.IsZero (groupCohomology C (n + 1)) :=
      (isZero_groupCohomology_succ_of_subsingleton A n).of_iso (groupCohomology.coindIso A (n + 1))
    have h0 : 𝟙 (groupCohomology C (n + 1)) = 0 := hz.eq_of_src _ _
    refine ⟨fun a b => ?_⟩
    have ha := congrArg (fun f => f.hom a) h0
    have hb := congrArg (fun f => f.hom b) h0
    simp only [ModuleCat.hom_id, ModuleCat.hom_zero, LinearMap.id_apply, LinearMap.zero_apply] at ha hb
    rw [ha, hb]
  let L : Ω →ₗ[ℂ] (Γ → Ω) := LinearMap.pi fun h => ρ h
  have hL : ∀ x, L x ∈ Representation.coindV S.subtype A.ρ := by
    intro x g h
    have hg : (g : Γ) = 1 := Subgroup.mem_bot.1 g.2
    simp [L, hg, A]
  let iL : Ω →ₗ[ℂ] Representation.coindV S.subtype A.ρ := LinearMap.codRestrict _ L hL
  let M : Representation.coindV S.subtype A.ρ →ₗ[ℂ] (Γ → Ω) :=
    LinearMap.pi fun g => ρ g ∘ₗ LinearMap.proj g⁻¹ ∘ₗ Submodule.subtype _
  let rL : Representation.coindV S.subtype A.ρ →ₗ[ℂ] Ω := P ∘ₗ M
  let i : Rep.of ρ ⟶ C := Rep.ofHom ⟨iL, fun γ => by
    refine LinearMap.ext fun x => Subtype.ext (funext fun h => ?_)
    simp only [iL, L, LinearMap.comp_apply]
    show (ρ h) ((ρ γ) x) = (ρ (h * γ)) x
    rw [map_mul, Module.End.mul_apply]⟩
  let r : C ⟶ Rep.of ρ := Rep.ofHom ⟨rL, fun γ => by
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.comp_apply, rL, M]
    rw [hequi]
    congr 1
    funext g
    simp [mul_inv_rev, ← Module.End.mul_apply, ← map_mul]
    rfl⟩
  have hri : i ≫ r = 𝟙 _ := by
    ext x
    simp [i, r, rL, M, iL, L, ← Module.End.mul_apply, ← map_mul, hconst]
    show P (fun g => ρ g (ρ g⁻¹ x)) = x
    rw [show (fun g => ρ g (ρ g⁻¹ x)) = fun _ => x from
      funext fun g => by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply], hconst]
  let F := groupCohomology.functor ℂ Γ (n + 1)
  have hinj : Function.Injective (F.map i).hom := by
    intro a b hab
    have key : ∀ z, (F.map r).hom ((F.map i).hom z) = z := by
      intro z
      rw [← ModuleCat.comp_apply, ← F.map_comp, hri, F.map_id]
      rfl
    rw [← key a, ← key b, hab]
  haveI : Subsingleton (F.obj C) := hC
  exact hinj.subsingleton

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AltAddRadial
section
noncomputable section

open scoped ContDiff Topology

namespace UpperTheory.V.Lit.Dr

section

variable {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

end

private theorem multilinear_apply_add_smul_of_vanishing {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {q : ℕ} (A : V [⋀^Fin q]→L[ℝ] F) (z : V)
    (hA : ∀ (u : Fin q → V) (i : Fin q), u i = z → A u = 0) (u : Fin q → V) (a : Fin q → ℝ) :
    A (fun i => u i + a i • z) = A u := by
  classical
  suffices key : ∀ s : Finset (Fin q),
      A (fun i => if i ∈ s then u i + a i • z else u i) = A u by
    simpa using key Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have e1 : (fun i => if i ∈ insert j s then u i + a i • z else u i) =
        Function.update (fun i => if i ∈ s then u i + a i • z else u i) j (u j + a j • z) := by
      ext i
      by_cases h : i = j
      · subst h
        simp
      · simp [h]
    have e2 : Function.update (fun i => if i ∈ s then u i + a i • z else u i) j (u j) =
        fun i => if i ∈ s then u i + a i • z else u i := by
      ext i
      by_cases h : i = j
      · subst h
        simp [hj]
      · simp [h]
    rw [e1, ContinuousAlternatingMap.map_update_add, ContinuousAlternatingMap.map_update_smul,
      hA (Function.update (fun i => if i ∈ s then u i + a i • z else u i) j z) j (by simp),
      smul_zero, add_zero, e2, ih]

theorem pullA : PullTranslates := by
  intro V F _ _ _ _ Y hY hC l hl q w
  obtain ⟨hlc, hlpos, hlh⟩ := hl
  have hld : ∀ p ∈ Y, DifferentiableAt ℝ l p := fun p hp =>
    (hlc.contDiffAt (hY.mem_nhds hp)).differentiableAt (by simp)
  have hDr : ∀ p ∈ Y, ∀ h, fderiv ℝ (fun x => l x • x) p h = fderiv ℝ l p h • p + l p • h := by
    intro p hp h
    have hd : HasFDerivAt (fun x => l x • x) _ p := (hld p hp).hasFDerivAt.smul (hasFDerivAt_id p)
    rw [hd.fderiv]
    simp [add_comm]
  have heul : ∀ p ∈ Y, fderiv ℝ l p p = -l p := by
    intro p hp
    have hc : HasDerivAt (fun t : ℝ => t • p) p 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const p
    have h' : HasFDerivAt l (fderiv ℝ l p) ((1 : ℝ) • p) := by
      simpa using (hld p hp).hasFDerivAt
    have h1 : HasDerivAt (fun t : ℝ => l (t • p)) (fderiv ℝ l p p) 1 := h'.comp_hasDerivAt 1 hc
    have h2 : HasDerivAt (fun t : ℝ => t⁻¹ * l p) (-l p) 1 := by
      simpa using (hasDerivAt_inv (one_ne_zero (α := ℝ))).mul_const (l p)
    have heq : (fun t : ℝ => l (t • p)) =ᶠ[𝓝 1] fun t => t⁻¹ * l p := by
      filter_upwards [lt_mem_nhds one_pos] with t ht using hlh t ht p hp
    exact h1.unique (h2.congr_of_eventuallyEq heq)
  have hDrp : ∀ p ∈ Y, fderiv ℝ (fun x => l x • x) p p = 0 := by
    intro p hp
    rw [hDr p hp, heul p hp, neg_smul, neg_add_cancel]
  refine ⟨?_, ?_⟩
  · intro p hp v i hvi
    simp only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    apply ContinuousAlternatingMap.map_coord_zero _ i
    simp [hvi, hDrp p hp]
  · intro hR hH p hp
    ext v
    simp only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have hc := hlpos p hp
    have hcp : l p • p ∈ Y := hC _ hc p hp
    have e1 : (fun i => fderiv ℝ (fun x => l x • x) p (v i)) =
        fun i => l p • v i + (fderiv ℝ l p (v i) / l p) • (l p • p) := by
      ext i
      rw [hDr p hp, smul_smul, div_mul_cancel₀ _ hc.ne', add_comm]
    change w (l p • p) (fun i => fderiv ℝ (fun x => l x • x) p (v i)) = w p v
    rw [e1, multilinear_apply_add_smul_of_vanishing (w (l p • p)) (l p • p) (fun u i hu => hR _ hcp u i hu)]
    exact hH _ hc p hp v

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AltSmooth
section
noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem altSmooth : AltSmooth := by
  intro X _ _ V F _ _ _ _ _ _ q f x hf
  let b := Module.finBasis ℝ V
  let E : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] ((Fin q → Fin (Module.finrank ℝ V)) → F) :=
    { toFun := fun a k => a fun i => b (k i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hE : Function.Injective E := by
    intro a a' h
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    refine Module.Basis.ext_alternating b fun k _ => ?_
    exact congrFun h k
  obtain ⟨g, hg⟩ := E.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hE)
  have h1 : ContDiffAt ℝ ∞ (fun y => E (f y)) x := contDiffAt_pi.2 fun k => hf _
  have h2 := (LinearMap.toContinuousLinearMap g).contDiff.contDiffAt.comp x h1
  have h3 : (LinearMap.toContinuousLinearMap g) ∘ (fun y => E (f y)) = f := by
    funext y
    exact LinearMap.congr_fun hg (f y)
  rwa [h3] at h2

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AltSym
section
noncomputable section

namespace UpperTheory.V.Lit.Dr

theorem altSym : AltSym := by
  intro V F _ _ _ _ q w p L γ u D hw hL hγ hu hD
  have hA : HasFDerivAt w (fderiv ℝ w p) p := hw.hasFDerivAt
  have hDi : ∀ i, D i = fderiv ℝ w p (L i p) (fun j => L (i.succAbove j) p) +
      ∑ j : Fin q, w p (Function.update (fun j' => L (i.succAbove j') p) j
        (L (i.succAbove j) (L i p))) := by
    intro i
    have hg : ∀ j : Fin q, HasFDerivAt (fun t => u i (i.succAbove j) t)
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (L (i.succAbove j) (L i p))) 0 :=
      fun j => ((hu i (i.succAbove j)).2).hasFDerivAt
    have hA' : HasFDerivAt w (fderiv ℝ w p) (γ i 0) := by
      rw [(hγ i).1]
      exact hA
    have hf : HasFDerivAt (fun t => w (γ i t))
        ((fderiv ℝ w p).comp (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (L i p))) 0 :=
      hA'.comp 0 (hγ i).2.hasFDerivAt
    have H := (hf.continuousAlternatingMap_apply hg).hasDerivAt
    rw [(hD i).unique H]
    have hu0 : ∀ j, u i j 0 = L j p := fun j => (hu i j).1
    simp [hu0, (hγ i).1]
  have hrm : ∀ i : Fin (q + 1), Fin.removeNth i (fun k => L k p) = fun j => L (i.succAbove j) p :=
    fun i => rfl
  rw [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  simp only [hDi, smul_add, Finset.sum_add_distrib, hrm]
  suffices hS : ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • ∑ j : Fin q,
      w p (Function.update (fun j' => L (i.succAbove j') p) j (L (i.succAbove j) (L i p))) = 0 by
    rw [hS, add_zero]
  set M : Fin (q + 1) → Fin (q + 1) → V := fun i k => L k (L i p) with hM
  have hMs : ∀ i k, M i k = M k i := fun i k => hL k i
  set Y : Fin (q + 1) → Fin (q + 1) → Fin (q + 1) → V :=
    fun i k m => if m = i ∨ m = k then M i k else L m p with hYdef
  set c : Fin (q + 1) → Fin (q + 1) → F :=
    fun i k => if i = k then 0 else (-1 : ℤ) ^ (i : ℕ) • w p (Fin.removeNth i (Y i k)) with hcdef
  have hc : ∀ i k, c i k + c k i = 0 := by
    intro i k
    by_cases hik : i = k
    · subst hik
      simp [c]
    · have hY : Y k i = Y i k := by
        funext m
        simp only [Y, hMs k i, or_comm]
      simp only [c, hik, Ne.symm hik, if_false, hY]
      exact (w p).neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq (v := Y i k) (by simp [Y]) hik
  have hsum : ∑ i, ∑ k, c i k = 0 := by
    have h1 : ∑ i, ∑ k, c i k = -∑ i, ∑ k, c i k := by
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact eq_neg_iff_add_eq_zero.mpr (hc k i)
    have h2 : (2 : ℝ) • ∑ i, ∑ k, c i k = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h1]
      exact add_neg_cancel _
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hne : ∀ (i : Fin (q + 1)) (j : Fin q), i ≠ i.succAbove j := fun i j => (Fin.succAbove_ne i j).symm
  have hrow : ∀ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • ∑ j : Fin q, w p (Function.update
      (fun j' => L (i.succAbove j') p) j (L (i.succAbove j) (L i p))) = ∑ k, c i k := by
    intro i
    rw [Fin.sum_univ_succAbove _ i, Finset.smul_sum]
    simp only [c, if_pos rfl, zero_add, hne, if_false]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    funext j'
    by_cases hj : j' = j
    · subst hj
      simp [Fin.removeNth_apply, Y, M]
    · simp [Fin.removeNth_apply, Y, M, Function.update_of_ne hj, Fin.succAbove_ne i j', hj]
  rw [← hsum]
  exact Finset.sum_congr rfl fun i _ => hrow i

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ApplySmooth
section
noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem applySmooth : ApplySmooth := by
  intro X _ _ V F _ _ _ _ q f v x hf hv
  let B : (V [⋀^Fin q]→L[ℝ] F) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin q => V) F :=
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ
  have hB : ContDiffAt ℝ ∞ (fun p : (V [⋀^Fin q]→L[ℝ] F) × (Fin q → V) => B p.1 p.2)
      (f x, fun i => v i x) :=
    (B.cpolynomialAt_uncurry_of_multilinear).contDiffAt
  have hin : ContDiffAt ℝ ∞ (fun y => (f y, fun i => v i y)) x :=
    hf.prodMk (contDiffAt_pi.mpr hv)
  exact hB.comp x hin

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AvgMem
section
noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem avgMem : AvgMem := by
  intro Γ V S _ _ _ d G u hu q c
  obtain ⟨hsm, hfin, -⟩ := hu
  have hc : ∀ γ s, ContDiffOn ℝ ∞ ((c γ : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
      ∀ p ∉ G.Y, (c γ : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0 :=
    fun γ s => (c γ).2 s
  simp only [Geo.Om, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  intro s
  refine ⟨?_, ?_⟩
  · apply contDiffOn_of_locally_contDiffOn
    intro p hp
    obtain ⟨N, hN, hF⟩ := hfin s p hp
    obtain ⟨O, hON, hO, hpO⟩ := mem_nhds_iff.mp hN
    refine ⟨O, hO, hpO, ?_⟩
    have hsum : ContDiffOn ℝ ∞ (fun x => ∑ γ ∈ hF.toFinset,
        u ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x) • (c γ : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) (G.Y ∩ O) := by
      apply ContDiffOn.sum
      intro γ _
      have h1 : ContDiffOn ℝ ∞ (fun x => u ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x)) (G.Y ∩ O) :=
        ((hsm _).comp (G.ρ γ⁻¹).contDiff.contDiffOn
          (fun x hx => G.maps γ⁻¹ x hx.1))
      exact h1.smul ((hc γ s).1.mono Set.inter_subset_left)
    refine hsum.congr ?_
    intro x hx
    apply finsum_eq_sum_of_support_subset
    intro γ hγ
    rw [Set.Finite.coe_toFinset]
    refine ⟨x, hON hx.2, ?_⟩
    intro h0
    rw [Function.mem_support] at hγ
    exact hγ (by rw [h0, zero_smul])
  · intro p hp
    apply finsum_eq_zero_of_forall_eq_zero
    intro γ
    simp [(hc γ s).2 p hp]

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.BasicDeriv
section
noncomputable section

open scoped ContDiff Topology

namespace UpperTheory.V.Lit.Dr

section

variable {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

end

private theorem hasDerivAt_apply_comp_of_differentiableAt {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {q : ℕ} {w : V → V [⋀^Fin q]→L[ℝ] F}
    {c : ℝ → V} {c' : V} {s : ℝ} (m : Fin q → V) (hw : DifferentiableAt ℝ w (c s))
    (hc : HasDerivAt c c' s) :
    HasDerivAt (fun r => w (c r) m) (fderiv ℝ w (c s) c' m) s := by
  have h1 := (ContinuousAlternatingMap.apply ℝ V F m).hasFDerivAt.comp (c s) hw.hasFDerivAt
  exact h1.comp_hasDerivAt s hc

private theorem fderiv_update_add_eq_zero_of_radBasic {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Y : Set V} (hY : IsOpen Y) {q : ℕ}
    {w : V → V [⋀^Fin q]→L[ℝ] F} (hR : RadBasic Y w) {x : V} (hx : x ∈ Y)
    (hw : DifferentiableAt ℝ w x) (v : Fin q → V) (j : Fin q) :
    fderiv ℝ w x (v j) (Function.update v j x) + w x v = 0 := by
  have hc : HasDerivAt (fun s : ℝ => x + s • v j) (v j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (v j)).const_add x
  have hw0 : DifferentiableAt ℝ w (x + (0 : ℝ) • v j) := by simpa using hw
  have d1 := hasDerivAt_apply_comp_of_differentiableAt (Function.update v j x) hw0 hc
  have d2 := hasDerivAt_apply_comp_of_differentiableAt v hw0 hc
  have d3 := (hasDerivAt_id (0 : ℝ)).smul d2
  have dg := d1.add d3
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), x + s • v j ∈ Y := by
    have hcont : Continuous fun s : ℝ => x + s • v j := by fun_prop
    exact hcont.continuousAt (x := 0) |>.preimage_mem_nhds (by simpa using hY.mem_nhds hx)
  have heq : (fun s : ℝ => w (x + s • v j) (Function.update v j x) + id s • w (x + s • v j) v)
      =ᶠ[𝓝 0] fun _ => (0 : F) := by
    filter_upwards [hev] with s hs
    have h0 := hR (x + s • v j) hs (Function.update v j (x + s • v j)) j (by simp)
    rw [ContinuousAlternatingMap.map_update_add, ContinuousAlternatingMap.map_update_smul,
      Function.update_eq_self] at h0
    simpa using h0
  have := dg.unique ((hasDerivAt_const (0 : ℝ) (0 : F)).congr_of_eventuallyEq heq)
  simpa using this

private theorem fderiv_self_add_smul_eq_zero_of_radBasic_closed {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Y : Set V} (hY : IsOpen Y) {q : ℕ}
    {w : V → V [⋀^Fin q]→L[ℝ] F} (hR : RadBasic Y w) {x : V} (hx : x ∈ Y)
    (hw : DifferentiableAt ℝ w x) (hd : extDeriv w x = 0) (v : Fin q → V) :
    fderiv ℝ w x x v + (q : ℝ) • w x v = 0 := by
  have h0 := congrArg (fun f => f (Fin.cons x v)) hd
  simp only [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ] at h0
  cases q with
  | zero => simpa using h0
  | succ n =>
    have hterm : ∀ j : Fin (n + 1), (-1 : ℤ) ^ ((j.succ : Fin (n + 2)) : ℕ) •
        fderiv ℝ w x ((Fin.cons x v : Fin (n + 2) → V) j.succ)
          (Fin.removeNth j.succ (Fin.cons x v : Fin (n + 2) → V)) = w x v := by
      intro j
      have hr : Fin.removeNth j.succ (Fin.cons x v : Fin (n + 2) → V) =
          Matrix.vecCons x (Fin.removeNth j v) := by
        ext i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp [Fin.removeNth]
        · simp [Fin.removeNth, Fin.succ_succAbove_succ]
      rw [hr, ← ContinuousAlternatingMap.neg_one_pow_smul_map_insertNth, Fin.insertNth_removeNth,
        Fin.cons_succ, smul_smul]
      have := fderiv_update_add_eq_zero_of_radBasic hY hR hx hw v j
      rw [Fin.val_succ, pow_succ, mul_comm, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩,
        one_mul, neg_one_smul, neg_eq_iff_eq_neg, eq_neg_iff_add_eq_zero]
      exact this
    rw [Finset.sum_congr rfl (fun j _ => hterm j)] at h0
    rw [Nat.cast_smul_eq_nsmul]
    simpa [add_comm] using h0

theorem homog : Homog := by
  intro V F _ _ _ _ Y hY hC q w hw hR hd t ht p hp v
  have hdiff : ∀ x ∈ Y, DifferentiableAt ℝ w x := fun x hx =>
    (hw.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)
  set k : ℝ → F := fun s => s ^ q • w (s • p) v with hkdef
  have hscale : ∀ s : ℝ, w (s • p) (fun i => s • v i) = k s := by
    intro s
    rw [ContinuousAlternatingMap.map_smul_univ]
    simp [k, Finset.prod_const]
  have hk : ∀ s ∈ Set.Ioi (0 : ℝ), HasDerivAt k 0 s := by
    intro s hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hsp : s • p ∈ Y := hC s hs p hp
    have hc : HasDerivAt (fun r : ℝ => r • p) p s := by
      simpa using (hasDerivAt_id s).smul_const p
    have dg := hasDerivAt_apply_comp_of_differentiableAt v (c := fun r : ℝ => r • p) (hdiff _ hsp) hc
    have dk : HasDerivAt k _ s := (hasDerivAt_pow q s).smul dg
    have key := fderiv_self_add_smul_eq_zero_of_radBasic_closed hY hR hsp (hdiff _ hsp) (hd _ hsp) v
    have hA : s • fderiv ℝ w (s • p) p v = -((q : ℝ) • w (s • p) v) := by
      rw [eq_neg_iff_add_eq_zero, ← key]
      simp [map_smul]
    have hpow : s * ((q : ℝ) * s ^ (q - 1)) = q * s ^ q := by
      cases q with
      | zero => simp
      | succ n => simp [pow_succ]; ring
    convert dk using 1
    apply smul_right_injective F hs0
    simp only [smul_zero, smul_add]
    rw [smul_comm s (s ^ q), hA, smul_smul, hpow, smul_neg, smul_smul, mul_comm, neg_add_cancel]
  have hconst := isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun s hs => (hk s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hk s hs).deriv) (Set.mem_Ioi.mpr ht) (Set.mem_Ioi.mpr one_pos)
  rw [hscale, hconst]
  simp [k]

end UpperTheory.V.Lit.Dr
end
end

