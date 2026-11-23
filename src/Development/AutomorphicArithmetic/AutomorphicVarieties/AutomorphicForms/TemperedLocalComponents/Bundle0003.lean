module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalTwists.ZeroComplOfFb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.CoeSmEqSymm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.MemArchMaxCompactIffOrthogonalAtInfinitePlaces
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsKFiniteTotallyRealModelOfIsKFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ModerateGrowthTotallyRealModelOfModerateGrowth

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistsContRep
section
open NumberField GlobalTheory.CuspRep UpperTheory.V


open Matrix in
private theorem exists_contRep {K I : Type} [Group K] [TopologicalSpace K] {d : ℕ} (ξ : K →* Matrix (Fin d) (Fin d) ℂ)
    (ev : I → Module.Dual ℂ (Fin d → ℂ)) (hc : ∀ i v, Continuous fun k => ev i (ξ k *ᵥ v))
    (hs : ∀ k v, (∀ i, ev i v = 0) → ∀ i, ev i (ξ k *ᵥ v) = 0) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W) (ρ : Representation ℂ K W),
      GlobalTheory.Published.AutFin.IsContRep ρ ∧ ∀ i v, (fun k => ev i (ξ k *ᵥ v)) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  let N : Submodule ℂ (Fin d → ℂ) := ⨅ i, LinearMap.ker (ev i)
  have hN : ∀ v, v ∈ N ↔ ∀ i, ev i v = 0 := fun v => by simp [N, Submodule.mem_iInf]
  let σ : Representation ℂ K (Fin d → ℂ) := (Matrix.toLinAlgEquiv' : _ ≃ₐ[ℂ] _).toMonoidHom.comp ξ
  have hσ : ∀ k v, σ k v = ξ k *ᵥ v := fun k v => Matrix.toLinAlgEquiv'_apply _ _
  have hle : ∀ k, N ≤ N.comap (σ k) := fun k v hv => (hN _).2 (hσ k v ▸ hs k v ((hN v).1 hv))
  have hq : ∀ k v, σ.quotient N hle k (N.mkQ v) = N.mkQ (ξ k *ᵥ v) := fun k v => by rw [← hσ]; rfl
  refine ⟨(Fin d → ℂ) ⧸ N, inferInstance, inferInstance, inferInstance, σ.quotient N hle, fun ℓ w => ?_, fun i v => ?_⟩
  · obtain ⟨v, rfl⟩ := N.mkQ_surjective w
    simp only [hq]
    have hl : ℓ ∘ₗ N.mkQ ∈ Submodule.span ℂ (Set.range ev) :=
      FiniteDimensional.mem_span_of_iInf_ker_le_ker fun x hx => by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, (Submodule.Quotient.mk_eq_zero N).2 hx |> fun h => show N.mkQ x = 0 from h,
          map_zero]
    change Continuous fun k => (ℓ ∘ₗ N.mkQ) (ξ k *ᵥ v)
    generalize ℓ ∘ₗ N.mkQ = m at hl
    induction hl using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hc i v
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  · refine Submodule.subset_span ⟨N.liftQ (ev i) (iInf_le _ i), N.mkQ v, funext fun k => ?_⟩
    rw [hq]
    rfl

open Matrix in
theorem UpperTheory.V.Af.admissibleReal :
    UpperTheory.V.Published.AdmissibleReal := by
  intro F _ _ _ a π U hU d ξ
  obtain ⟨c, hc⟩ := TR.Cen.exists_cap_scalar π
  let I : Type := {f : (Fin d → ℂ) →ₗ[ℂ] π.V // ∀ k v, f (ξ k *ᵥ v) = π.op (.cpt k) (f v)} × GA F a
  let ev : I → Module.Dual ℂ (Fin d → ℂ) := fun i =>
    (LinearMap.proj i.2).comp ((TR.Sm F a).subtype.comp (π.V.subtype.comp i.1.1))
  have hev : ∀ (i : I) k v, ev i (ξ k *ᵥ v) = (TR.cptRep F a k (i.1.1 v).1).1 i.2 := fun i k v =>
    congrArg (fun x : π.V => x.1.1 i.2) (i.1.2 k v)
  obtain ⟨W, _, _, _, ρ, hρ, hco⟩ := exists_contRep ξ ev
    (fun i v => by simp only [hev]; exact TR.Cen.continuous_cptRep _ _)
    (fun k v h i => by rw [hev]; exact h (i.1, i.2 * TR.infGL F a (Unitary.toUnits k)))
  have hfin := UpperTheory.V.Af.cuspFormsFiniteReal F a U hU W ρ hρ c
  set S := Submodule.span ℂ {φ : TR.Sm F a | TR.IsCuspForm φ ∧ (∀ k ∈ U, TR.finRep F a k φ = φ) ∧
    (∀ g : GA F a, (fun k : TR.Kinf F a => (TR.cptRep F a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
    ∀ v u, TR.cap v u φ = c v u • φ}
  refine ⟨S.comap π.V.subtype, FiniteDimensional.of_injective
    ((π.V.subtype ∘ₗ (S.comap π.V.subtype).subtype).codRestrict S fun x => x.2) (fun x y e => ?_), ?_⟩
  · exact Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
  · rintro f hf hfix _ ⟨v, rfl⟩
    refine Submodule.subset_span ⟨π.cusp _ (f v).2, fun k hk => congrArg Subtype.val (hfix k hk v), fun g => ?_,
      fun w u => hc w u _ (f v).2⟩
    have h := hco (⟨f, hf⟩, g) v
    simp only [hev] at h
    exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PCuspSS
section
open NumberField GlobalTheory.CuspRep UpperTheory.V

section
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

private theorem cusp_to (φ : TR.Sm F a) (h : TR.IsCuspForm φ) : φ.1 ∈ cuspForms F a := by
  have hs : IsSmooth φ.1 := ⟨UpperTheory.isArchSmooth_of_contDiff_chart F a _ φ.2, fun g => by
    filter_upwards [h.1.level.mem_nhds (show TR.finRep F a 1 φ = φ by simp)] with y hy
    rw [Fb.finEmb_eq]
    exact congrFun (congrArg Subtype.val hy) g⟩
  have hA : IsAutomorphicForm φ.1 := ⟨h.1.left, hs, UpperTheory.isKFinite_totallyRealModel_of_isKFinite F a φ h.1.level h.1.kfin,
    (Fb.zfin_iff φ).1 h.1.zfin, UpperTheory.moderateGrowth_totallyRealModel_of_moderateGrowth F a φ h.1.left h.1.level h.1.growth⟩
  exact ⟨hA, UpperTheory.constantTerm_eq_zero_of_isCuspidal F a _ hA.isLeftInvariant hA.continuous h.2⟩

private theorem cusp_of (f : GA F a → ℂ) (hf : f ∈ cuspForms F a) : ∃ h : f ∈ TR.Sm F a, TR.IsCuspForm ⟨f, h⟩ := by
  have hA := hf.1
  have h := UpperTheory.contDiff_chart_of_isArchSmooth F a f hA.isSmooth.1
  refine ⟨h, ⟨hA.isLeftInvariant, ?_, ?_, (Fb.zfin_iff _).2 hA.isZFinite, fun g => ?_⟩,
    UpperTheory.isCuspidal_of_constantTerm_eq_zero F a f hA.isLeftInvariant hA.continuous hf.2⟩
  · obtain ⟨W, -, hW⟩ := exists_openSubgroup_rightInvariant hA.isSmooth hA.isKFinite
    refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (W.isOpen.mem_nhds W.one_mem) fun k hk => ?_)
    refine Subtype.ext (funext fun g => ?_)
    have := hW g k hk
    rwa [Fb.finEmb_eq] at this
  · have := hA.isKFinite
    unfold IsKFinite at this
    refine UnitaryAdmissible.finiteDimensional_of_map_subtype_le _ (S := Submodule.span ℂ
      (Set.range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL F a)) =>
        rightTranslate (k : AdelicGLn.AdelicGL F a) f)) ?_
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    have hk : infEmb F a (Fb.grpEq F a (Unitary.toUnits k)) ∈ Reduction.maxCompact := (UpperTheory.mem_archMaxCompact_iff_orthogonal_at_infinitePlaces F a _).2 k.2
    rw [Fb.infEmb_grpEq] at hk
    exact Submodule.subset_span ⟨⟨_, hk⟩, rfl⟩
  · obtain ⟨C, N, hC⟩ := hA.hasModerateGrowth
    obtain ⟨M, hM⟩ := UpperTheory.adelicHeight_infGL_le_opNorm F a
    have h0 : 0 ≤ C := by
      have := (norm_nonneg _).trans (hC 1)
      rwa [height_one, one_pow, mul_one] at this
    have h1 := (one_le_heightConst (K := F) (n := a))
    have h2 := height_pos g
    refine ⟨C * (heightConst F a * height g) ^ N, M * N, fun y => (hC _).trans ?_⟩
    rw [mul_assoc, pow_mul, ← mul_pow]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le ((height_mul_le _ _).trans ?_) N) h0
    exact mul_le_mul_of_nonneg_left (hM y) (by positivity)

end

theorem UpperTheory.V.Af.cuspSemisimpleReal :
    UpperTheory.V.Published.CuspSemisimpleReal :=
  TR.SS.cuspSemisimple_of fun _ _ _ _ _ => TR.SS.zeroCompl_of_fb cusp_to cusp_of
    (fun X φ _ => (congrArg Subtype.val (Fb.uAction_ι_smEq X φ)).symm) UpperTheory.mem_archMaxCompact_iff_orthogonal_at_infinitePlaces
end

