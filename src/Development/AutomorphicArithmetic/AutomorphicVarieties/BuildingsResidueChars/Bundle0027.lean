module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0057
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsIrreducibleSubrepHeckeEigenOfInvariantForm

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCompactFundamentalSetUnitary
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU

theorem UpperTheory.exists_compact_fundamental_set_unitary :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ C : Set (UA E n), IsCompact C ∧ ∀ g, ∃ γ ∈ ratU E n, ∃ c ∈ C, g = γ * c := by
  intro E _ _ _ n
  classical
  obtain ⟨K, hKo, hKc⟩ := UpperTheory.exists_isOpen_isCompact_subgroup_finiteAdelicUnitary E n
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n K hKo
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  haveI : ∀ v : InfinitePlace E, CompactSpace (embU n v.embedding) := fun v => by
    obtain ⟨e, -⟩ := _root_.GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n v.embedding
    exact e.toHomeomorph.symm.compactSpace
  let P : (∀ v : InfinitePlace E, embU n v.embedding) → UA E n :=
    fun y => (Finset.univ.toList.map fun v => (y v : UA E n)).prod
  have hP : Continuous P :=
    continuous_list_prod _ fun v _ => continuous_subtype_val.comp (continuous_apply v)
  have hPc : IsCompact (Set.range P) := isCompact_range hP
  have hKc' : IsCompact (Subtype.val '' (K : Set (finU (E := E) (n := n)))) := hKc.image continuous_subtype_val
  refine ⟨_, (S.finite_toSet.isCompact.mul hPc).mul hKc', fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, e⟩ := hS g
  obtain ⟨y, hy, -, hyx⟩ := _root_.GlobalTheory.DefU.infU_eq_list_prod_embU E n x hx
  refine ⟨γ, hγ, s * x * k, Set.mul_mem_mul (Set.mul_mem_mul hs ⟨fun v => ⟨y v, hy v⟩, hyx⟩) ⟨k, hk, rfl⟩, ?_⟩
  rw [e, mul_assoc, mul_assoc, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemISupIrreducibleOfAdmissibleUnitary
section
theorem UpperTheory.mem_iSup_irreducible_of_admissible_unitary :
    ∀ (H W : Type) [Group H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ v, B v v = 0 → v = 0) → (∀ g u v, B (ρ g u) (ρ g v) = B u v) → (∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧ ∀ w, (Set.range fun k : K => ρ k w).Finite) → ∀ x : W, x ∈ ⨆ U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1 := by
  intro H W _ _ _ ρ B hdef hinv hadm x
  classical
  set S : Submodule ℂ W := ⨆ U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1 with hS
  have hSle : ∀ U : Submodule ℂ W, U ≠ ⊥ → (∀ g, ∀ u ∈ U, ρ g u ∈ U) →
      (∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U) → U ≤ S := by
    intro U h1 h2 h3
    exact le_iSup (fun U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U} => U.1) ⟨U, h1, h2, h3⟩
  have hSinv : ∀ g, ∀ u ∈ S, ρ g u ∈ S := by
    intro g u hu
    have hle : S ≤ S.comap (ρ g) := by
      refine iSup_le ?_
      rintro ⟨U, h1, h2, h3⟩ v hv
      exact hSle U h1 h2 h3 (h2 g v hv)
    exact hle hu
  let Z : Subrepresentation ρ := ⟨S, fun g v hv => hSinv g v hv⟩
  let O : Submodule ℂ W := ⨅ z : S, LinearMap.ker (B (z : W))
  have memO : ∀ w, w ∈ O ↔ ∀ z ∈ S, B z w = 0 := by
    intro w
    simp [O, Submodule.mem_iInf]
  let Y : Subrepresentation ρ := ⟨O, fun g v hv =>
    (memO _).2 (GlobalTheory.UnitarySemisimple.orth_stable ρ B hinv Z v ((memO _).1 hv) g)⟩
  obtain ⟨t, htS, ht⟩ := GlobalTheory.UnitarySemisimple.exists_compl_proj ρ B hdef hinv hadm Z x
  by_cases h0 : x - t = 0
  · rw [sub_eq_zero.1 h0]
    exact htS
  exfalso
  let σ : Representation ℂ H O := Y.toRepresentation
  have hσ : ∀ g (v : O), ((σ g v : O) : W) = ρ g v := fun _ _ => rfl
  let B' : O →ₗ⋆[ℂ] O →ₗ[ℂ] ℂ := (B.comp O.subtype).compl₂ O.subtype
  have hB' : ∀ u v : O, B' u v = B u v := fun _ _ => rfl
  have hadm' : ∀ v : O, ∃ K : Subgroup H, (∀ k ∈ K, σ k v = v) ∧
      FiniteDimensional ℂ (GlobalTheory.PRep.fixed σ K) ∧ ∀ w, (Set.range fun k : K => σ k w).Finite := by
    intro v
    obtain ⟨K, h1, h2, h3⟩ := hadm v
    refine ⟨K, fun k hk => Subtype.ext (h1 k hk), ?_, fun w => ?_⟩
    · let f : GlobalTheory.PRep.fixed σ K →ₗ[ℂ] GlobalTheory.PRep.fixed ρ K :=
        (O.subtype.comp (GlobalTheory.PRep.fixed σ K).subtype).codRestrict _ (by
          intro u k
          exact congrArg Subtype.val (u.2 k))
      refine Module.Finite.of_injective f ?_
      intro a b hab
      have hab' : ((f a : GlobalTheory.PRep.fixed ρ K) : W) = ((f b : GlobalTheory.PRep.fixed ρ K) : W) := by rw [hab]
      exact Subtype.ext (Subtype.ext hab')
    · refine Set.Finite.of_finite_image (f := Subtype.val) ((h3 w).subset ?_) Subtype.val_injective.injOn
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
  obtain ⟨U, hU, hirr, f, hfU, hf0, -⟩ := UpperTheory.exists_irreducible_subrep_hecke_eigen_of_invariant_form H O σ B'
    (fun v hv => Subtype.ext (hdef _ hv)) (fun g u v => hinv g u v) hadm'
    ⟨x - t, (memO _).2 ht⟩ (fun h => h0 (congrArg Subtype.val h))
  have hf0' : (f : W) ≠ 0 := fun h => hf0 (Subtype.ext h)
  have hfU' : (f : W) ∈ U.map O.subtype := ⟨f, hfU, rfl⟩
  have hle : U.map O.subtype ≤ S := by
    refine hSle _ (fun h => hf0' (by simpa [h] using hfU')) ?_ ?_
    · rintro g _ ⟨u, hu, rfl⟩
      exact ⟨σ g u, hU g u hu, rfl⟩
    · intro N hN hNinv
      have hNO : N ≤ O := hN.trans (Submodule.map_subtype_le _ _)
      have hmc : (N.comap O.subtype).map O.subtype = N := by
        rw [Submodule.map_comap_subtype, inf_eq_right.2 hNO]
      have hle' : N.comap O.subtype ≤ U := by
        intro u hu
        obtain ⟨w, hw, hwu⟩ := hN hu
        have : w = u := Subtype.ext hwu
        exact this ▸ hw
      rcases hirr _ hle' (fun g u hu => hNinv g u hu) with h | h
      · left
        rw [← hmc, h, Submodule.map_bot]
      · right
        rw [← hmc, h]
  exact hf0' (hdef _ ((memO _).1 f.2 _ (hle hfU')))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnitaryAdelicGroupTopology
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU

theorem UpperTheory.unitary_adelic_t2_locallyCompact_secondCountable :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), T2Space (UA E n) ∧ LocallyCompactSpace (UA E n) ∧ SecondCountableTopology (UA E n) ∧ DiscreteTopology (ratU E n) := by
  intro E _ _ _ n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL (E := E) (a := n)
  refine ⟨inferInstance, (GlobalTheory.DefU.LocAdm.isClosed_UA (E := E) (n := n)).isClosedEmbedding_subtypeVal.locallyCompactSpace,
    (Topology.IsEmbedding.subtypeVal (p := fun g : GA E n => g ∈ UA E n)).secondCountableTopology, ?_⟩
  have hm : ∀ x : ratU E n, ((x : UA E n) : GA E n) ∈ latticeGL E n := fun x => by
    obtain ⟨δ, hδ⟩ := x.2
    have h := GlobalTheory.CuspRep.CuspidalL2GL.ratGL_mem_latticeGL (E := E) δ
    rw [hδ] at h
    exact h
  let f : ratU E n → latticeGL E n := fun x => ⟨_, hm x⟩
  have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hi : Function.Injective f := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : latticeGL E n => (z : GA E n)) h))
  exact DiscreteTopology.of_continuous_injective hf hi
end

