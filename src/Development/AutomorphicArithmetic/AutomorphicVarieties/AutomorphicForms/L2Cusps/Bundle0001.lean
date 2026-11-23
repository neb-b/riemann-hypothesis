module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
public import GroundTheory.AutomorphicForms.TensorProductTheorem.KProjApplyEqSelfIff
public import GroundTheory.AutomorphicForms.L2LocalComponents.NonEmpty
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.InfEmbGrpEq

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsApprox
section
private theorem starProjection_apply_comm_of_invariant_adjoint {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (Y : Submodule ℂ H) [Y.HasOrthogonalProjection] (B C : H →L[ℂ] H)
    (hB : ∀ y ∈ Y, B y ∈ Y) (hC : ∀ y ∈ Y, C y ∈ Y)
    (hBC : ContinuousLinearMap.adjoint B = C) (x : H) :
    Y.starProjection (B x) = B (Y.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal' (z := B (x - Y.starProjection x))
    (hB _ (Y.starProjection_apply_mem x))
  · rw [Submodule.mem_orthogonal]
    intro y hy
    rw [← ContinuousLinearMap.adjoint_inner_left, hBC]
    exact Submodule.inner_right_of_mem_orthogonal (hC y hy)
      (Submodule.sub_starProjection_mem_orthogonal (K := Y) x)
  · rw [← map_add (f := _), add_sub_cancel]

private theorem exists_finiteDimensional_invariant_le_of_fg {ι H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : ι → H →L[ℂ] H) (W M : Submodule ℂ H) (hM : M.FG) (hMW : M ≤ W)
    (hW : ∀ w ∈ W, ∃ Y ≤ W, FiniteDimensional ℂ Y ∧ w ∈ Y ∧ ∀ i, ∀ y ∈ Y, A i y ∈ Y) :
    ∃ Y ≤ W, FiniteDimensional ℂ Y ∧ M ≤ Y ∧ ∀ i, ∀ y ∈ Y, A i y ∈ Y := by
  classical
  obtain ⟨s, rfl⟩ := hM
  have key : ∀ t : Finset H, (↑t : Set H) ⊆ W → ∃ Y ≤ W, FiniteDimensional ℂ Y ∧
      (↑t : Set H) ⊆ Y ∧ ∀ i, ∀ y ∈ Y, A i y ∈ Y := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨⊥, bot_le, inferInstance, by simp, fun i y hy => ?_⟩
      rw [(Submodule.mem_bot ℂ).1 hy, map_zero]
      exact Submodule.zero_mem _
    | insert a t ha ih =>
      intro hsub
      rw [Finset.coe_insert, Set.insert_subset_iff] at hsub
      obtain ⟨Y1, h1W, h1f, h1t, h1A⟩ := ih hsub.2
      obtain ⟨Y2, h2W, h2f, h2a, h2A⟩ := hW a hsub.1
      haveI := h1f
      haveI := h2f
      refine ⟨Y1 ⊔ Y2, sup_le h1W h2W, inferInstance, ?_, ?_⟩
      · rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨Submodule.mem_sup_right h2a, h1t.trans (SetLike.coe_subset_coe.2 le_sup_left)⟩
      · intro i y hy
        obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add (f := _)]
        exact Submodule.add_mem_sup (h1A i y1 hy1) (h2A i y2 hy2)
  obtain ⟨Y, hYW, hYf, hsY, hYA⟩ := key s (Submodule.span_le.1 hMW)
  exact ⟨Y, hYW, hYf, Submodule.span_le.2 hsY, hYA⟩

theorem UpperTheory.V.KernelIndexFullLattice.absApprox_holds :
    UpperTheory.V.KernelIndexFullLattice.AbsApprox := by
  intro ι H _ _ _ A hA W N hN hW v hv hP
  classical
  haveI := hN
  have hfg : (N ⊓ W).FG := by
    haveI : FiniteDimensional ℂ ↥(N ⊓ W) := Submodule.finiteDimensional_of_le inf_le_left
    exact (Submodule.fg_iff_finiteDimensional _).2 inferInstance
  obtain ⟨Y0, hY0W, hY0f, hNY0, hY0A⟩ := exists_finiteDimensional_invariant_le_of_fg A W (N ⊓ W) hfg inf_le_right hW
  haveI := hY0f
  have hproj : ∀ (Y : Submodule ℂ H) [FiniteDimensional ℂ Y], Y ≤ W →
      (∀ i, ∀ y ∈ Y, A i y ∈ Y) → Y0 ≤ Y → Y0.starProjection v = Y.starProjection v := by
    intro Y _ hYW hYA hY0Y
    have h1 : Y.starProjection v ∈ N := by
      apply hP
      · intro i x
        obtain ⟨j, hj⟩ := hA i
        exact starProjection_apply_comm_of_invariant_adjoint Y (A i) (A j) (hYA i) (hYA j) hj x
      · intro x
        exact hYW (Y.starProjection_apply_mem x)
    have h2 : Y.starProjection v ∈ Y0 := hNY0 ⟨h1, hYW (Y.starProjection_apply_mem v)⟩
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero h2
    intro w hw
    exact Submodule.starProjection_inner_eq_zero v w (hY0Y hw)
  have horth : ∀ w ∈ W, inner ℂ w (v - Y0.starProjection v) = 0 := by
    intro w hw
    obtain ⟨Y1, h1W, h1f, hw1, h1A⟩ := hW w hw
    haveI := h1f
    have hY := hproj (Y0 ⊔ Y1) (sup_le hY0W h1W) (fun i y hy => by
      obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hY0A i y1 hy1) (h1A i y2 hy2)) le_sup_left
    rw [hY, inner_eq_zero_symm]
    exact Submodule.starProjection_inner_eq_zero v w (Submodule.mem_sup_right hw1)
  have hcl : v - Y0.starProjection v ∈ W.topologicalClosure :=
    W.topologicalClosure.sub_mem hv
      (W.le_topologicalClosure (hY0W (Y0.starProjection_apply_mem v)))
  have hsub : closure (W : Set H) ⊆ {x | inner ℂ x (v - Y0.starProjection v) = 0} :=
    closure_minimal horth (isClosed_eq (continuous_id.inner continuous_const) continuous_const)
  have hzero : inner ℂ (v - Y0.starProjection v) (v - Y0.starProjection v) = 0 := by
    apply hsub
    rw [← Submodule.topologicalClosure_coe]
    exact hcl
  rw [inner_self_eq_zero, sub_eq_zero] at hzero
  rw [hzero]
  exact hY0W (Y0.starProjection_apply_mem v)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompact
section
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.AutMult GroundTheory.Automorphic

theorem UpperTheory.V.KernelIndexFullLattice.absCompact_holds :
    UpperTheory.V.KernelIndexFullLattice.AbsCompact := by
  intro G G₁ H L _ _ _ _ _ _ _ _ _ _ _ _ _ π ν _ _ ρ W hW J r hr hρ hJ hcpt
  have hmem : ∀ h, J h ∈ W := by
    intro h
    rw [← hJ]
    exact ⟨h, rfl⟩
  let Φ : H →ₗᵢ[ℂ] W :=
    { toLinearMap := (J.toLinearMap).codRestrict W hmem
      norm_map' := fun h => J.norm_map h }
  have hΦsurj : Function.Surjective Φ := by
    intro w
    have hw : (w : L) ∈ J.range := by
      rw [hJ]
      exact w.2
    obtain ⟨h, hh⟩ := hw
    exact ⟨h, Subtype.ext hh⟩
  let Ψ : H ≃ₗᵢ[ℂ] W := LinearIsometryEquiv.ofSurjective Φ hΦsurj
  let Ψc : H →L[ℂ] W := (Ψ.toContinuousLinearEquiv : H →L[ℂ] W)
  let Ψi : W →L[ℂ] H := (Ψ.symm.toContinuousLinearEquiv : W →L[ℂ] H)
  have hΨc : ∀ h, Ψc h = Ψ h := fun h => rfl
  have hΨi : ∀ w, Ψi w = Ψ.symm w := fun w => rfl
  have hrep : ∀ g h, hW.rep g (Ψ h) = Ψ (π (r g) h) := by
    intro g h
    apply Subtype.ext
    exact hρ g h
  intro w hw0
  have hne : Ψ.symm w ≠ 0 := by
    intro h0
    apply hw0
    simpa using congrArg Ψ h0
  obtain ⟨f, hf⟩ := π.exists_integrated_ne_zero ν hne
  refine ⟨Ψc ∘L (π.integrated ν (UnitaryRep.ccToL1 ν f)) ∘L Ψi, ?_, ?_, ?_⟩
  · exact ((hcpt f).comp_clm Ψi).clm_comp Ψc
  · intro S hS x
    rw [mem_homIn_top] at hS
    let T : H →L[ℂ] H := Ψi ∘L S ∘L Ψc
    have hT : T ∈ π.intertwiners π := by
      intro g₁ h
      obtain ⟨g, rfl⟩ := hr g₁
      show Ψ.symm (S (Ψ (π (r g) h))) = π (r g) (Ψ.symm (S (Ψ h)))
      have e1 : S (Ψ h) = Ψ (Ψ.symm (S (Ψ h))) := (Ψ.apply_symm_apply _).symm
      calc Ψ.symm (S (Ψ (π (r g) h))) = Ψ.symm (S (hW.rep g (Ψ h))) := by rw [hrep]
        _ = Ψ.symm (hW.rep g (S (Ψ h))) := by rw [hS]
        _ = Ψ.symm (hW.rep g (Ψ (Ψ.symm (S (Ψ h))))) := by rw [← e1]
        _ = π (r g) (Ψ.symm (S (Ψ h))) := by rw [hrep, LinearIsometryEquiv.symm_apply_apply]
    have hc := UnitaryRep.comp_integrated_of_mem_intertwiners π ν hT (UnitaryRep.ccToL1 ν f)
    have hc' := congrArg (fun Q => Q (Ψ.symm x)) hc
    simp only [T, ContinuousLinearMap.comp_apply, hΨc, hΨi,
      LinearIsometryEquiv.apply_symm_apply] at hc' ⊢
    rw [← hc', LinearIsometryEquiv.apply_symm_apply]
  · simpa [hΨc, hΨi] using hf
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsIrr
section
theorem UpperTheory.V.KernelIndexFullLattice.absIrr_holds :
    UpperTheory.V.KernelIndexFullLattice.AbsIrr := by
  intro G G₁ H L _ _ _ _ _ _ _ _ π ρ J r hr hρ X hXJ hX
  obtain ⟨⟨hXc, hXinv⟩, hXne, hXmin⟩ := hX
  have hVc : IsClosed ((Submodule.comap J.toLinearMap X : Submodule ℂ H) : Set H) :=
    hXc.preimage J.continuous
  haveI hVcomp : CompleteSpace (Submodule.comap J.toLinearMap X) := hVc.completeSpace_coe
  have hinv : π.IsInvariant (Submodule.comap J.toLinearMap X) := by
    intro g₁ v hv
    obtain ⟨g, rfl⟩ := hr g₁
    show J (π (r g) v) ∈ X
    rw [← hρ]
    exact hXinv g _ hv
  refine ⟨hVcomp, hinv, ?_, ?_⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hXne
    obtain ⟨h, rfl⟩ := hXJ hx
    refine nontrivial_of_ne (⟨h, hx⟩ : Submodule.comap J.toLinearMap X) 0 ?_
    intro e
    apply hx0
    have e' : h = 0 := congrArg Subtype.val e
    rw [e', map_zero]
  · intro U' hU'c hU'inv
    let V := Submodule.comap J.toLinearMap X
    let U : Submodule ℂ L := (U'.map V.subtype).map J.toLinearMap
    have hUX : U ≤ X := by
      rintro _ ⟨_, ⟨u, _, rfl⟩, rfl⟩
      exact u.2
    have hU'H : IsClosed ((U'.map V.subtype : Submodule ℂ H) : Set H) := by
      rw [Submodule.map_coe]
      exact hVc.isClosedEmbedding_subtypeVal.isClosedMap _ hU'c
    have hUc : IsClosed (U : Set L) := by
      rw [Submodule.map_coe]
      exact J.isometry.isClosedEmbedding.isClosedMap _ hU'H
    have hUinv : ∀ g, ∀ v ∈ U, ρ g v ∈ U := by
      rintro g _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨_, ⟨⟨π (r g) u, hinv _ _ u.2⟩, hU'inv (r g) u hu, rfl⟩, ?_⟩
      exact (hρ g u).symm
    rcases hXmin U hUX ⟨hUc, hUinv⟩ with h | h
    · left
      rw [eq_bot_iff]
      intro u hu
      have hJu : J u ∈ U := ⟨u, ⟨u, hu, rfl⟩, rfl⟩
      rw [h, Submodule.mem_bot] at hJu
      rw [Submodule.mem_bot]
      apply Subtype.ext
      have hn : ‖(u : H)‖ = 0 := by rw [← J.norm_map, hJu, norm_zero]
      simpa using hn
    · right
      rw [eq_top_iff]
      intro u _
      have hJu : J u ∈ U := by
        rw [h]
        exact u.2
      obtain ⟨_, ⟨u', hu', rfl⟩, he⟩ := hJu
      have : u' = u := Subtype.ext (J.injective he)
      rw [← this]
      exact hu'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Assemble
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_split (h : SplitEq) (s : {r : ℝ // 0 < r}) :
    ∃ t : ℝ, Reduction.centralSection E a s = splitCentre E a t := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨0, Subsingleton.elim _ _⟩
  · have h0 : ((a : ℝ) * Module.finrank ℚ E) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.2 ha.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
    refine ⟨Real.log s.1 / (a * Module.finrank ℚ E), ?_⟩
    rw [h]
    congr 1
    refine Subtype.ext ?_
    change s.1 = Real.exp _
    rw [mul_div_cancel₀ _ h0, Real.exp_log s.2]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem retractOne_surjective : Function.Surjective (retractOne : GA E a → G1 E a) :=
  fun x => ⟨x, retractOne_coe x⟩

theorem range_cmp (h1 : RangeLe) (h2 : ContMem) {μ : Measure (GA E a)} [μ.IsHaarMeasure]
    {μ₁ : Measure (G1 E a)} [μ₁.IsHaarMeasure] (hp : Pres μ μ₁) :
    LinearMap.range (cmp hp).toLinearMap = L2cusp μ := by
  refine le_antisymm ?_ (L2cusp_le ?_ fun φ hφ h => h2 E a μ μ₁ hp φ hφ h)
  · rintro _ ⟨v, rfl⟩
    exact h1 E a μ μ₁ hp v
  · exact (cmp hp).isometry.isClosedEmbedding.isClosed_range

theorem partA (hH : MuHaar) (hP : QuotPres) (hE : CmpEquiv) (h1 : RangeLe) (h2 : ContMem) (hC : AbsCompact) :
    GlobalTheory.Published.CuspDiscreteDecompositionGL := by
  intro E _ _ _ a μ _ _
  have := hH E a μ
  have hp := hP E a μ
  exact EnoughCompact.isDiscreteSum (isUnitaryRep_Rcusp μ)
    (hC _ _ _ _ (cuspRepT (muOne μ)) (muOne μ) _ _ (isSubrep_L2cusp μ) (cmp hp) retractOne retractOne_surjective
      (hE E a μ _ hp) (range_cmp h1 h2 hp) fun f => isCompactOperator_cuspRep (muOne μ) f)

theorem partC (hS : SplitEq) (hB : BrCusp) : GlobalTheory.Published.CuspFormsBoundedGL := by
  intro E _ _ _ a φ hφ hn
  obtain ⟨C, hC⟩ := exists_norm_le_of_mem_cuspForms (hB E a φ hφ)
  refine ⟨C, fun g => ?_⟩
  obtain ⟨s, y, hy, rfl⟩ := exists_centralSection_mul_mem_normOneGL g
  obtain ⟨t, ht⟩ := exists_split (E := E) (a := a) hS s
  rw [ht, hn]
  exact hC y hy

theorem partB (hS : SplitEq) (hH : MuHaar) (hP : QuotPres) (hE : CmpEquiv) (hF : CmpForm) (h1 : RangeLe) (h2 : ContMem)
    (hI : AbsIrr) (hN : NeBot) (hK : KFinTr) (hM : KFinMem) (hR : BrRep) : GlobalTheory.Published.CuspFiniteVectorsGL := by
  intro E _ _ _ a μ _ _ H hH' hirr
  have := hH E a μ
  have hp := hP E a μ
  have hle : H ≤ LinearMap.range (cmp hp).toLinearMap := (range_cmp h1 h2 hp).symm ▸ hH'
  obtain ⟨_, hV, hVi⟩ := hI _ _ _ _ (cuspRepT (muOne μ)) _ (cmp hp) retractOne retractOne_surjective
    (hE E a μ _ hp) H hle hirr
  have hne := hN E a _ _ hV hVi
  have hcl := CuspidalAutomorphicRepresentation.topologicalClosure_map_ofSummand _ hV hVi hne
  generalize CuspidalAutomorphicRepresentation.ofSummand _ hV hVi hne = π₀ at hcl
  obtain ⟨π, hπ⟩ := hR E a π₀
  have hto : ∀ φ ∈ π.V, ∃ ψ ∈ π₀.carrier, ψ.1 = φ.1 := fun φ hφ => hπ.le ⟨φ, hφ, rfl⟩
  have hof : ∀ ψ ∈ π₀.carrier, ∃ φ ∈ π.V, φ.1 = ψ.1 := fun ψ hψ => hπ.ge ⟨ψ, hψ, rfl⟩
  have hnorm : IsNormalised π := fun φ hφ t g => by
    obtain ⟨ψ, hψ, e⟩ := hto φ hφ
    rw [← e, hS]
    exact π₀.le_central hψ _ g
  have hcls : classes π.V μ = (π₀.carrier.map (cuspVecL (muOne μ))).map (cmp hp).toLinearMap := by
    ext F
    constructor
    · rintro ⟨φ, hφ, e⟩
      obtain ⟨ψ, hψ, e'⟩ := hto φ hφ
      exact ⟨_, ⟨ψ, hψ, rfl⟩, l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ((hF E a μ _ hp ψ (π₀.le_central hψ)).trans (e' ▸ e.symm))⟩
    · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩
      obtain ⟨φ, hφ, e⟩ := hof ψ hψ
      exact ⟨φ, hφ, e ▸ hF E a μ _ hp ψ (π₀.le_central hψ)⟩
  refine ⟨π, hnorm, fun φ hφ => ?_, ?_, fun F hFH hk => ?_⟩
  · obtain ⟨ψ, hψ, e⟩ := hto φ hφ
    exact memL2_of_ae_eq (leftInv_latticeGL (π.cusp φ hφ).1.left (hnorm φ hφ))
      (e ▸ hF E a μ _ hp ψ (π₀.le_central hψ))
  · rw [hcls, ← Submodule.map_comap_eq_self hle, ← hcl]
    refine SetLike.coe_injective ?_
    simp only [Submodule.topologicalClosure_coe, Submodule.map_coe]
    exact (cmp hp).isometry.isClosedEmbedding.closure_image_eq _
  · obtain ⟨v, rfl⟩ := hle hFH
    obtain ⟨k1, k2⟩ := hK E a μ _ hp v hk
    rw [hcls]
    exact ⟨v, hM E a _ π₀ v (hcl.symm ▸ hFH) k1 k2, rfl⟩

end UpperTheory.V.KernelIndexFullLattice
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.HomFin
section
open GroundTheory.Automorphic

private theorem UpperTheory.V.KernelIndexFullLattice.homFin_comp {R B S : Type} [Ring R] [AddCommGroup B] [Module R B]
    [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    isotypicComponent R B S = ⊥ ∨ isotypicComponent R B S ∈ isotypicComponents R B := by
  by_cases h : isotypicComponent R B S = ⊥
  · exact Or.inl h
  · right
    obtain ⟨m, ⟨e⟩, -⟩ : ∃ m ∈ {m : Submodule R B | Nonempty (m ≃ₗ[R] S)}, m ≠ ⊥ := by
      by_contra hc
      push_neg at hc
      exact h (sSup_eq_bot.mpr hc)
    haveI : IsSimpleModule R m := IsSimpleModule.congr e
    exact ⟨m, inferInstance, e.isotypicComponent_eq.symm⟩

theorem UpperTheory.V.KernelIndexFullLattice.homFin_holds :
    UpperTheory.V.KernelIndexFullLattice.HomFin := by
  intro C M X _ _ _ _ _ _ _ _ _ _ σ hσ τ hτ F hF
  have hτK : CompactRep.IsKFinite τ := ⟨fun _ => inferInstance, hτ⟩
  haveI : IsSemisimpleModule (MonoidAlgebra ℂ C) τ.asModule := CompactRep.isSemisimpleModule_asModule hτK
  haveI : IsNoetherian ℂ τ.asModule := inferInstanceAs (IsNoetherian ℂ X)
  haveI hτT : IsScalarTower ℂ (MonoidAlgebra ℂ C) τ.asModule := by
    refine ⟨fun c a v => ?_⟩
    show τ.asAlgebraHom (c • a) _ = c • τ.asAlgebraHom a _
    rw [map_smul]
    rfl
  haveI hσT : IsScalarTower ℂ (MonoidAlgebra ℂ C) σ.asModule := by
    refine ⟨fun c a v => ?_⟩
    show σ.asAlgebraHom (c • a) _ = c • σ.asAlgebraHom a _
    rw [map_smul]
    rfl
  haveI : IsNoetherian (MonoidAlgebra ℂ C) τ.asModule := isNoetherian_of_tower ℂ inferInstance
  obtain ⟨t, ht, htop⟩ := WellFoundedGT.isSupFiniteCompact (α := Submodule (MonoidAlgebra ℂ C) τ.asModule) {m | IsSimpleModule (MonoidAlgebra ℂ C) m}
  rw [IsSemisimpleModule.sSup_simples_eq_top] at htop
  let W : Submodule (MonoidAlgebra ℂ C) τ.asModule → Submodule ℂ M := fun m =>
    F ⊓ ((isotypicComponent (MonoidAlgebra ℂ C) σ.asModule m).restrictScalars ℂ : Submodule ℂ σ.asModule)
  refine ⟨t.sup W, ?_, ?_⟩
  · refine Finset.sup_induction (p := fun N : Submodule ℂ M => FiniteDimensional ℂ N) ?_ ?_ ?_
    · exact inferInstance
    · intro a ha b hb
      exact Submodule.finiteDimensional_sup a b
    · intro m hm
      haveI : IsSimpleModule (MonoidAlgebra ℂ C) m := ht hm
      rcases UpperTheory.V.KernelIndexFullLattice.homFin_comp (R := MonoidAlgebra ℂ C) (B := σ.asModule) (S := m) with h | hc
      · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) ?_
        intro v hv
        have hv2 : (show σ.asModule from v) ∈ isotypicComponent (MonoidAlgebra ℂ C) σ.asModule m := hv.2
        rw [h] at hv2
        have hv0 : (show σ.asModule from v) = 0 := (Submodule.mem_bot (MonoidAlgebra ℂ C)).1 hv2
        exact (Submodule.mem_bot ℂ).2 hv0
      · haveI := hF _ hc
        refine Submodule.finiteDimensional_of_le
          (S₂ := LinearMap.range (CompactRep.kProj hσ hc ∘ₗ F.subtype)) ?_
        intro v hv
        exact ⟨⟨v, hv.1⟩, (CompactRep.kProj_apply_eq_self_iff hσ hc).2 hv.2⟩
  · intro f hf hFf x
    let f' : τ.asModule →ₗ[ℂ] σ.asModule :=
      σ.asModuleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ τ.asModuleEquiv.toLinearMap
    let g : τ.asModule →ₗ[MonoidAlgebra ℂ C] σ.asModule :=
      MonoidAlgebra.equivariantOfLinearOfComm f'
        (fun k v => by
          simp [f']
          exact hf k v)
    have hg : ∀ y : τ.asModule, g y = f y := fun y => rfl
    have one : ∀ m ∈ t, ∀ y ∈ m, g y ∈ t.sup W := by
      intro m hm y hy
      haveI : IsSimpleModule (MonoidAlgebra ℂ C) m := ht hm
      refine Finset.le_sup (f := W) hm ⟨?_, ?_⟩
      · rw [hg]
        exact hFf y
      show g y ∈ isotypicComponent (MonoidAlgebra ℂ C) σ.asModule m
      rcases (g.domRestrict m).injective_or_eq_zero with hi | h0
      · have hle : LinearMap.range (g.domRestrict m) ≤ isotypicComponent (MonoidAlgebra ℂ C) σ.asModule m :=
          le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
        exact hle ⟨⟨y, hy⟩, rfl⟩
      · have h1 : g y = 0 := by simpa using LinearMap.congr_fun h0 ⟨y, hy⟩
        rw [h1]
        exact zero_mem _
    have key : ∀ s : Finset (Submodule (MonoidAlgebra ℂ C) τ.asModule), s ⊆ t →
        ∀ y ∈ s.sup id, g y ∈ t.sup W := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro _ y hy
        have hy0 : y = 0 := by simpa using hy
        rw [hy0, map_zero]
        exact zero_mem _
      | insert a s ha ih =>
        intro hs y hy
        rw [Finset.sup_insert] at hy
        obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add (f := _)]
        exact add_mem (one a (hs (Finset.mem_insert_self a s)) y1 hy1)
          (ih ((Finset.subset_insert a s).trans hs) y2 hy2)
    have hx : (show τ.asModule from x) ∈ t.sup id := htop ▸ Submodule.mem_top
    have := key t subset_rfl _ hx
    rw [hg] at this
    exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.KernelIndexFullLatticeNeBot
section
theorem UpperTheory.V.KernelIndexFullLattice.kernelIndexFullLattice_neBot :
    UpperTheory.V.KernelIndexFullLattice.NeBot :=
  @GroundTheory.Automorphic.CuspidalSpectrum.summandCuspForms_ne_bot
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq
section
open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global.IdeleGroup

private theorem posIdele_inf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (s : ℝ) (hs : 0 < s)
    (w : InfinitePlace E) :
    ((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).1 w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (s : ℂ) := by
  have hw : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
  rw [← coe_infiniteProj, infiniteProj_posIdele]
  change GroundTheory.Global.posRealElem w _ = _
  unfold GroundTheory.Global.posRealElem
  rw [dite_eq_right hw]
  simp [InfinitePlace.mult, hw, Real.sqrt_sq hs.le]

theorem UpperTheory.V.KernelIndexFullLattice.splitEq_holds :
    UpperTheory.V.KernelIndexFullLattice.SplitEq := by
  intro E _ _ _ a t
  refine Units.ext (Matrix.ext fun i j => ?_)
  have ha : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 i.pos.ne'
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have e : rpowHom ((a * Module.finrank ℚ E : ℝ))⁻¹ ⟨Real.exp (a * Module.finrank ℚ E * t), Real.exp_pos _⟩ =
      ⟨Real.exp t, Real.exp_pos t⟩ := by
    refine Subtype.ext ?_
    change Real.exp (a * Module.finrank ℚ E * t) ^ ((a * Module.finrank ℚ E : ℝ))⁻¹ = Real.exp t
    rw [← Real.exp_mul]
    congr 1
    field_simp
  rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, e, posIdeleHom_apply, scalarUnits_apply,
    coe_diagUnits, splitCentre]
  set y : GL (Fin a) (Cinf E) :=
    Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ)) with hy
  have h2 : ((infGL E a y).val i j).2 =
      (1 : Matrix (Fin a) (Fin a) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E)) i j :=
    congrArg (fun g : GL (Fin a) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) => g.val i j) (pFin_infGL y)
  have h1 : ∀ w, ((infGL E a y).val i j).1 w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (y.val i j w) :=
    fun w => congrFun (UpperTheory.V.Cm.infGL_entry y i j) w
  have hyv : y.val = Matrix.diagonal fun _ => (fun _ : InfinitePlace E => Complex.exp (t : ℂ)) := rfl
  refine Prod.ext (funext fun w => ?_) ?_
  · rw [h1, hyv]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, posIdele_inf, Complex.ofReal_exp]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]
      exact map_zero _
  · rw [h2]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact IsDedekindDomain.FiniteAdeleRing.ext E fun v => (posIdele_finite _ _ v).symm
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
      rfl
end

