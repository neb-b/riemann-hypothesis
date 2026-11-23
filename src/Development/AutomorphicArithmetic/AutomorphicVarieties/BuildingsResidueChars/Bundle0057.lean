module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SemisimpleModuleRestrictionToNormalSubgroup
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem UpperTheory.semisimple_restriction_normal_subgroup {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : G → V →ₗ[K] V)
    (hmul : ∀ (a b : G) (v : V), ρ a (ρ b v) = ρ (a * b) v) (hone : ∀ v, ρ 1 v = v)
    (N : Subgroup G) (hN : N.Normal)
    (hss : ∀ W : Submodule K V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) →
      ∃ W' : Submodule K V, (∀ g, ∀ v ∈ W', ρ g v ∈ W') ∧ IsCompl W W')
    (W : Submodule K V) (hW : ∀ g ∈ N, ∀ v ∈ W, ρ g v ∈ W) :
    ∃ W' : Submodule K V, (∀ g ∈ N, ∀ v ∈ W', ρ g v ∈ W') ∧ IsCompl W W' := by
  obtain ⟨W', ⟨hW's, hW'd⟩, hmax⟩ := exists_maximal_of_wellFoundedGT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ Disjoint W U)
    ⟨⊥, by intro g _ v hv; rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], disjoint_bot_right⟩
  refine ⟨W', hW's, hW'd, ?_⟩
  rw [codisjoint_iff]
  obtain ⟨C, hC, hUC⟩ := hss (⨅ g : G, (W ⊔ W').comap (ρ g)) (by
    intro g v hv
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv ⊢
    intro h
    rw [hmul]; exact hv _)
  by_cases htriv : C = ⊥
  · have hU := hUC.sup_eq_top
    rw [htriv, sup_bot_eq] at hU
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ (⨅ g : G, (W ⊔ W').comap (ρ g)) := hU ▸ Submodule.mem_top
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv
    have := hv 1
    rwa [hone] at this
  exfalso
  obtain ⟨S, ⟨hSs, hS0, hSC⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun U : Submodule K V => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ U ≠ ⊥ ∧ U ≤ C)
    ⟨C, fun g _ v hv => hC g v hv, htriv, le_rfl⟩
  have hsup : ∀ n ∈ N, ∀ v ∈ W ⊔ W', ρ n v ∈ W ⊔ W' := by
    intro n hn v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hW n hn a ha) (hW's n hn b hb)
  have key : ∀ g : G, ∀ s ∈ S, ρ g s ∈ W ⊔ W' := by
    intro g
    by_cases hA : S ⊓ (W ⊔ W').comap (ρ g) = ⊥
    · have hle : W' ⊔ S.map (ρ g) ≤ W' := by
        refine hmax ⟨?_, ?_⟩ le_sup_left
        · intro n hn v hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          rw [map_add (f := _)]
          refine Submodule.add_mem_sup (hW's n hn a ha) ?_
          refine Submodule.mem_map.mpr ⟨ρ (g⁻¹ * n * g) s, hSs _ (hN.conj_mem' n hn g) s hs, ?_⟩
          rw [hmul, hmul]; congr 2; group
        · rw [Submodule.disjoint_def]
          intro v hvW hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hb
          have h1 : ρ g s ∈ W ⊔ W' := by
            have := (W ⊔ W').sub_mem (Submodule.mem_sup_left hvW) (Submodule.mem_sup_right ha)
            simpa using this
          have h2 : s ∈ S ⊓ (W ⊔ W').comap (ρ g) := ⟨hs, h1⟩
          rw [hA, Submodule.mem_bot] at h2
          subst h2
          rw [map_zero, add_zero] at hvW ⊢
          exact Submodule.disjoint_def.mp hW'd a hvW ha
      intro s hs
      exact Submodule.mem_sup_right (hle (Submodule.mem_sup_right (Submodule.mem_map_of_mem hs)))
    · have hle : S ≤ S ⊓ (W ⊔ W').comap (ρ g) := by
        refine hmin ⟨?_, hA, inf_le_left.trans hSC⟩ inf_le_left
        intro n hn v hv
        refine ⟨hSs n hn v hv.1, ?_⟩
        have h1 : ρ g v ∈ W ⊔ W' := hv.2
        have h2 := hsup _ (hN.conj_mem n hn g) _ h1
        show ρ g (ρ n v) ∈ W ⊔ W'
        rw [hmul] at h2 ⊢
        have : g * n * g⁻¹ * g = g * n := by group
        rwa [this] at h2
      intro s hs
      exact (hle hs).2
  apply hS0
  rw [eq_bot_iff, ← hUC.inf_eq_bot]
  intro s hs
  refine ⟨?_, hSC hs⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap]
  exact fun g => key g s hs

theorem UpperTheory.semisimpleModule_restriction_to_normal_subgroup :
    UpperTheory.V.Af.Sol.SsRes := by
  intro Γ Γ' k _ _ _ n r φ hN hss W hW
  obtain ⟨W', h1, h2⟩ := UpperTheory.semisimple_restriction_normal_subgroup
    (fun g : Γ => Matrix.mulVecLin (r g : Matrix (Fin n) (Fin n) k))
    (by
      intro a b v
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, map_mul, Units.val_mul])
    (by
      intro v
      simp only [Matrix.mulVecLin_apply, map_one, Units.val_one, Matrix.one_mulVec])
    φ.range hN hss W (by
      rintro _ ⟨g, rfl⟩ v hv
      exact hW g v hv)
  exact ⟨W', fun g v hv => h1 (φ g) ⟨g, rfl⟩ v hv, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SignAtInfinityOfParallelWeight
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

open ReciprocityTheory.Neutral.Bridge.HCFR

private theorem UpperTheory.infPow_infIdele_neg_one_of_const_of_isReal {F : Type} [Field F] [NumberField F] (a : (F →+* ℂ) → ℤ)
    (a0 : ℤ) (ha : ∀ φ, a φ = a0) (w : InfinitePlace F) (hw : w.IsReal) :
    infPow a (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F w (-1)) = (-1) ^ a0 := by
  have hcont : Continuous (Complex.ofRealHom.comp
      (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw)) :=
    Complex.continuous_ofReal.comp
      (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous
  let i0 : {i : w.Completion →+* ℂ // Continuous i} := ⟨_, hcont⟩
  have huniq : ∀ i : {i : w.Completion →+* ℂ // Continuous i}, i = i0 := by
    intro i
    apply Subtype.ext
    ext x
    let E := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw
    let g : ℝ →+* ℂ := (i : w.Completion →+* ℂ).comp
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
    have hg : Continuous g := i.2.comp E.symm.continuous
    have hg' := Complex.ringHom_eq_ofReal_of_continuous hg
    have hx : (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
        (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x) = x :=
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm_apply_apply x
    have := congrArg (fun f : ℝ →+* ℂ => f
      (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x)) hg'
    simp only [g, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hx] at this
    simpa [i0] using this
  unfold infPow
  rw [Finset.prod_eq_single w]
  · rw [finprod_eq_single _ i0 (fun j hj => absurd (huniq j) hj)]
    rw [ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_self, ha]
    simp
  · intro w' _ hne
    simp [ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_ne F w w' hne]
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem UpperTheory.sign_at_infinity_of_parallel_weight :
    UpperTheory.V.Af.Sol.Parallel → UpperTheory.V.Af.Sol.SignOf := by
  intro hP F Ω _ _ _ _ _ _ l _ ι χ μ hμ hs v v'
  obtain ⟨-, art, a, hart, halg, hlad⟩ := hμ
  have hpar := hP F χ a halg
  have key : ∀ w : InfinitePlace F, ∃ c : G F Ω, IsConjEl c ∧
      ((χ.locInf w (-1) : ℂˣ) : ℂ) = ι (μ c) * (-1) ^ (a v.embedding) := by
    intro w
    obtain ⟨j, c, hc, hw⟩ := GlobalTheory.HilbertFromArtin.exists_conj (Ω := Ω) w
      (NumberField.IsTotallyReal.isReal w)
    refine ⟨c, ⟨j, hc⟩, ?_⟩
    have hart' := GlobalTheory.HilbertFromArtin.art_sign_eq hart j c hc
    rw [hw] at hart'
    have h := hlad _ c hart'
    have hl : lPow ι a (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F w (-1)) = 1 := by
      simp [GlobalTheory.HeckeGal.lPow, ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_snd, GlobalTheory.HeckeGal.locPow_one]
    rw [hl, mul_one, UpperTheory.infPow_infIdele_neg_one_of_const_of_isReal a (a v.embedding) (fun φ => hpar φ v.embedding) w
      (NumberField.IsTotallyReal.isReal w)] at h
    have h2 := congrArg ι h
    rw [RingEquiv.apply_symm_apply] at h2
    rw [h2]
    have hne : ((-1 : ℂ) ^ (a v.embedding)) ≠ 0 := zpow_ne_zero _ (by norm_num)
    rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
    rfl
  obtain ⟨c, hc, hcv⟩ := key v
  obtain ⟨c', hc', hcv'⟩ := key v'
  apply Units.ext
  rw [hcv, hcv', hs c c' hc hc']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvableAuxiliaryGaloisExtension
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.solvable_auxiliary_galois_extension :
    UpperTheory.V.Af.Sol.ExistsCompositumWithPrimeDegreeGalois := by
  intro M Ω _ _ _ _ _ L _ _ _ hp hlt
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed M
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap M Ω).injective
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ L
  have hαi : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  set P := minpoly ℚ α with hPdef
  have hPdeg : P.natDegree = Module.finrank ℚ L := by
    rw [← IntermediateField.adjoin.finrank hαi, hα, IntermediateField.finrank_top']
  let φ : L →ₐ[ℚ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  set β := φ α with hβdef
  have hβP : minpoly ℚ β = P := minpoly.algHom_eq φ φ.injective α
  set Q : Polynomial M := P.map (algebraMap ℚ M) with hQdef
  have hQ0 : Q ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hαi)
  have hsplit : (Q.map (algebraMap M Ω)).Splits := IsAlgClosed.splits _
  have hSF := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have hsep : Q.Separable := Polynomial.Separable.map (Algebra.IsSeparable.isSeparable ℚ α)
  have hroot : ∀ y : Ω, y ∈ Q.rootSet Ω ↔ y ∈ P.rootSet Ω := by
    intro y
    rw [Polynomial.mem_rootSet, Polynomial.mem_rootSet, hQdef, Polynomial.aeval_map_algebraMap]
    exact and_congr_left fun _ => ⟨fun _ => minpoly.ne_zero hαi, fun _ => hQ0⟩
  have hβroot : β ∈ P.rootSet Ω := by
    rw [Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero hαi, hβP ▸ minpoly.aeval ℚ β⟩
  have hrange : ∀ x : L, φ x ∈ IntermediateField.adjoin M {β} := by
    intro x
    have h1 : φ x ∈ (⊤ : IntermediateField ℚ L).map φ := ⟨x, trivial, rfl⟩
    rw [← hα, IntermediateField.adjoin_map, Set.image_singleton] at h1
    have h2 : IntermediateField.adjoin ℚ {φ α} ≤ (IntermediateField.adjoin M {β}).restrictScalars ℚ :=
      IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self M β)
    exact h2 h1
  have hPs : (P.map (algebraMap ℚ L)).Splits := Normal.splits inferInstance α
  have hroots : ∀ y ∈ P.rootSet Ω, y ∈ Set.range φ := by
    intro y hy
    rw [← hPs.image_rootSet φ] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have heq : IntermediateField.adjoin M (Q.rootSet Ω) = IntermediateField.adjoin M {β} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := hroots y ((hroot y).1 hy)
      exact hrange x
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.subset_adjoin M _ ((hroot β).2 hβroot)
  have hgal0 : IsGalois M (IntermediateField.adjoin M (Q.rootSet Ω)) := by
    haveI := hSF
    exact IsGalois.of_separable_splitting_field hsep
  have hgal : IsGalois M (IntermediateField.adjoin M {β}) := heq ▸ hgal0
  have hβQ : IsIntegral ℚ β := hαi.map φ
  have hβM : IsIntegral M β := hβQ.tower_top
  haveI hfdM : FiniteDimensional M (IntermediateField.adjoin M {β}) :=
    IntermediateField.adjoin.finiteDimensional hβM
  haveI hfdQ : FiniteDimensional ℚ (IntermediateField.adjoin M {β}) :=
    Module.Finite.trans M (IntermediateField.adjoin M {β})
  haveI hnf : NumberField (IntermediateField.adjoin M {β}) := {}
  let f : L →+* IntermediateField.adjoin M {β} := (φ : L →+* Ω).codRestrict _ hrange
  have hfin : Module.finrank M (IntermediateField.adjoin M {β}) = (minpoly M β).natDegree :=
    IntermediateField.adjoin.finrank hβM
  have hle : (minpoly M β).natDegree ≤ Module.finrank ℚ L := by
    rw [← hPdeg, ← Polynomial.natDegree_map (algebraMap ℚ M) (p := P)]
    refine Polynomial.natDegree_le_of_dvd ?_ hQ0
    have h4 := minpoly.dvd_map_of_isScalarTower ℚ M β
    rwa [hβP] at h4
  have hx : minpoly ℚ (⟨β, IntermediateField.mem_adjoin_simple_self M β⟩ : IntermediateField.adjoin M {β}) = P := by
    rw [← minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ (IntermediateField.adjoin M {β}) Ω)
      (algebraMap (IntermediateField.adjoin M {β}) Ω).injective]
    exact hβP
  have hdvd : Module.finrank ℚ L ∣ Module.finrank ℚ (IntermediateField.adjoin M {β}) := by
    have h5 := minpoly.degree_dvd (Algebra.IsIntegral.isIntegral (R := ℚ)
      (⟨β, IntermediateField.mem_adjoin_simple_self M β⟩ : IntermediateField.adjoin M {β}))
    rwa [hx, hPdeg] at h5
  have hMpos : 0 < Module.finrank ℚ M := Module.finrank_pos
  have hEpos : 0 < Module.finrank M (IntermediateField.adjoin M {β}) := Module.finrank_pos
  have hdeg : Module.finrank M (IntermediateField.adjoin M {β}) = Module.finrank ℚ L := by
    rw [← Module.finrank_mul_finrank ℚ M (IntermediateField.adjoin M {β})] at hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h3 | h3
    · exact absurd h3 (Nat.not_dvd_of_pos_of_lt hMpos hlt)
    · exact le_antisymm (hfin ▸ hle) (Nat.le_of_dvd hEpos h3)
  have htop : Algebra.adjoin M (Set.range f) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have hz : (z : Ω) ∈ Algebra.adjoin M {β} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβM.isAlgebraic]
      exact z.2
    have hsub : Algebra.adjoin M {β} ≤
        (Algebra.adjoin M (Set.range f)).map (IntermediateField.adjoin M {β}).val := by
      rw [AlgHom.map_adjoin]
      apply Algebra.adjoin_mono
      rintro _ rfl
      exact ⟨f α, ⟨α, rfl⟩, rfl⟩
    obtain ⟨w, hw, hwz⟩ := hsub hz
    have hwz' : w = z := Subtype.ext hwz
    exact hwz' ▸ hw
  exact ⟨IntermediateField.adjoin M {β}, inferInstance, hnf, inferInstance, inferInstance,
    inferInstance, f, hgal, hdeg, htop⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvableCmCompositumMaximalRealSubfield
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem rcsup_mem_real {L M' : Type} [Field L] [Field M'] (f : L →+* M') (hL : IsTotallyReal L) (x : L) :
    f x ∈ maximalRealSubfield M' := by
  intro φ
  have h : x ∈ maximalRealSubfield L := by
    rw [IsTotallyReal.maximalRealSubfield_eq_top]; trivial
  exact h (φ.comp f)

private theorem rcsup_map_real {M M' : Type} [Field M] [Field M'] (g : M →+* M') {x : M}
    (hx : x ∈ maximalRealSubfield M) : g x ∈ maximalRealSubfield M' :=
  fun φ => hx (φ.comp g)

private theorem rcsup_cm_of_pair {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (d : K) (hd0 : d ≠ 0)
    (hd : ∀ φ : K →+* ℂ, star (φ d) = - φ d)
    (hspan : ∀ y : K, ∃ a ∈ maximalRealSubfield K, ∃ b ∈ maximalRealSubfield K, y = a + b * d) :
    IsCMField K := by
  have hli : LinearIndependent (maximalRealSubfield K) ![(1 : K), d] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have h0 : (s : K) + (t : K) * d = 0 := by
      simpa [Subfield.smul_def] using hst
    have h1 : φ s + φ t * φ d = 0 := by
      rw [← map_mul, ← map_add (f := _), h0, map_zero]
    have h2 : φ s - φ t * φ d = 0 := by
      have := congrArg star h1
      rw [star_add, star_mul', s.2 φ, t.2 φ, hd φ, star_zero] at this
      linear_combination this
    have h3 : φ s = 0 := by linear_combination (h1 + h2) / 2
    have hs : (s : K) = 0 := (map_eq_zero φ).mp h3
    have ht : (t : K) = 0 := by
      rw [hs, zero_add] at h0
      exact (mul_eq_zero.mp h0).resolve_right hd0
    exact ⟨Subtype.ext hs, Subtype.ext ht⟩
  have hsp : ⊤ ≤ Submodule.span (maximalRealSubfield K) (Set.range ![(1 : K), d]) := by
    intro y _
    obtain ⟨a, ha, b, hb, rfl⟩ := hspan y
    have e : a + b * d = (⟨a, ha⟩ : maximalRealSubfield K) • (1 : K) + (⟨b, hb⟩ : maximalRealSubfield K) • d := by
      simp [Subfield.smul_def]
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have hrk : Module.finrank (maximalRealSubfield K) K = 2 := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)]
    simp
  haveI : Algebra.IsQuadraticExtension (maximalRealSubfield K) K := { finrank_eq_two' := hrk }
  exact {}

theorem UpperTheory.solvable_cm_compositum_maximalRealSubfield :
    UpperTheory.V.Af.Sol.RCSup := by
  intro L M M' _ _ _ _ _ _ _ f hL htop hM
  rcases hM with hM | hM
  · left
    rw [← maximalRealSubfield_eq_top_iff_isTotallyReal, eq_top_iff]
    intro y _
    have hy : y ∈ Algebra.adjoin M (Set.range f) := htop ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact rcsup_mem_real f hL z
    | algebraMap r => exact rcsup_mem_real _ hM r
    | add x y _ _ hx hy => exact add_mem (hx trivial) (hy trivial)
    | mul x y _ _ hx hy => exact mul_mem (hx trivial) (hy trivial)
  · right
    haveI : IsTotallyComplex M' := isTotallyComplex_of_algebra M M'
    obtain ⟨x, hx⟩ : ∃ x : M, IsCMField.complexConj M x ≠ x := by
      by_contra h
      apply IsCMField.complexConj_ne_one M
      ext x
      by_contra h'
      exact h ⟨x, h'⟩
    set δ : M := x - IsCMField.complexConj M x with hδ
    have hδ0 : δ ≠ 0 := sub_ne_zero.mpr hx.symm
    have hcδ : IsCMField.complexConj M δ = -δ := by
      rw [hδ, map_sub, IsCMField.complexConj_apply_apply]; ring
    have hd : ∀ φ : M' →+* ℂ, star (φ (algebraMap M M' δ)) = - φ (algebraMap M M' δ) := by
      intro φ
      have := IsCMField.complexEmbedding_complexConj M (φ.comp (algebraMap M M')) δ
      rw [hcδ, map_neg] at this
      exact this.symm
    have hsq : algebraMap M M' δ * algebraMap M M' δ ∈ maximalRealSubfield M' := by
      intro φ
      rw [map_mul, star_mul', hd φ]; ring
    refine rcsup_cm_of_pair (algebraMap M M' δ) ((_root_.map_ne_zero _).mpr hδ0) hd ?_
    intro y
    have hy : y ∈ Algebra.adjoin M (Set.range f) := htop ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      exact ⟨f z, rcsup_mem_real f hL z, 0, zero_mem _, by simp⟩
    | algebraMap r =>
      refine ⟨algebraMap M M' ((r + IsCMField.complexConj M r) / 2), rcsup_map_real _ ?_,
        algebraMap M M' ((r - IsCMField.complexConj M r) / (2 * δ)), rcsup_map_real _ ?_, ?_⟩
      · rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add (f := _), IsCMField.complexConj_apply_apply, map_ofNat, add_comm]
      · rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, IsCMField.complexConj_apply_apply, map_ofNat, hcδ]
        field_simp
        ring
      · rw [← map_mul, ← map_add (f := _)]
        congr 1
        field_simp
        ring
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      obtain ⟨a', ha', b', hb', rfl⟩ := hy
      exact ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', by ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      obtain ⟨a', ha', b', hb', rfl⟩ := hy
      exact ⟨a * a' + b * b' * (algebraMap M M' δ * algebraMap M M' δ),
        add_mem (mul_mem ha ha') (mul_mem (mul_mem hb hb') hsq),
        a * b' + b * a', add_mem (mul_mem ha hb') (mul_mem hb ha'), by ring⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvablePolarizedRestriction
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.solvable_polarized_restriction :
    UpperTheory.V.Af.Sol.PolRes := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι n r h
  obtain ⟨F₀, i1, i2, i3, i4, i5, i6, hF, μ, c, P, hμ, hs, hc, hp⟩ := h
  letI : Algebra F₀ M := ((algebraMap K M).comp (algebraMap F₀ K)).toAlgebra
  haveI : IsScalarTower F₀ K M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower F₀ M Ω := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply F₀ K Ω,
      IsScalarTower.algebraMap_apply K M Ω]
  refine ⟨F₀, i1, i2, inferInstance, inferInstance, this, i6, hF, μ, c, P, hμ, hs, hc, ?_⟩
  unfold IsPairing at hp ⊢
  intro t t' ht
  have e1 : ∀ u : G M Ω,
      AlgEquiv.restrictScalars F₀ (resG K M Ω u) = AlgEquiv.restrictScalars F₀ u := by
    intro u; ext x; rfl
  have e2 : ∀ u : G M Ω, resG F₀ M Ω u = resG F₀ K Ω (resG K M Ω u) := by
    intro u; ext x; rfl
  have key := hp (resG K M Ω t) (resG K M Ω t') (by rw [e1, e1]; exact ht)
  simpa [e2] using key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SumFamilyOfReductions
section
open UpperTheory.V.Af UpperTheory.V.Af.Gu
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.sum_family_of_reductions :
    SumTwo → SumRed → SumFam := by
  intro h2 hred E Ω _ _ _ _ _ l _ ι c hc
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  clear hc
  induction c with
  | zero =>
    intro N hN n hn r p HT H
    have hn' : N 0 = n := by simpa using hn
    subst hn'
    refine ⟨r 0, ⟨(H 0).cont, (H 0).ss, ?_, fun w => ((H 0).par w).congr fun A h rc _ => ?_⟩, fun hi => ⟨rfl, fun i => ?_⟩⟩
    · have e : (fun τ => ∑ i, HT i τ) = HT 0 := by
        funext τ
        simp
      rw [e]
      exact (H 0).ht
    · simp [sumList, WD.lpSum_zero]
    · obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
      exact hi
  | succ c ih =>
    intro N hN n hn r p HT H
    rw [Fin.sum_univ_succ] at hn
    subst hn
    obtain ⟨R, hR, -⟩ := ih (fun i => N i.succ) (fun i => hN i.succ) _ rfl (fun i => r i.succ) (fun i => p i.succ)
      (fun i => HT i.succ) (fun i => H i.succ)
    have hS := h2 E Ω l ι _ _ (r 0) R _ _ _ _ (H 0) hR
    refine ⟨Formalism.MainNotions.SumRepresentations.At.sumRep (r 0) R, ⟨hS.cont, hS.ss, ?_, fun w => (hS.par w).congr fun A h rc _ => ?_⟩, fun hi => ?_⟩
    · have e : (fun τ => ∑ i, HT i τ) = fun τ => HT 0 τ + ∑ i : Fin (c + 1), HT i.succ τ := by
        funext τ
        rw [Fin.sum_univ_succ]
      rw [e]
      exact hS.ht
    · rw [List.ofFn_succ (f := fun i => p i w A h rc)]
      rfl
    · refine absurd hi (hred _ _ _ _ _ _ (hN 0) ?_)
      exact le_trans (hN (Fin.succ 0)) (Finset.single_le_sum (f := fun i : Fin (c + 1) => N i.succ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
end

