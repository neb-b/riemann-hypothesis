module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.ProjectionComponents.CompOfProj
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem comp_of_proj {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {π σ : Submodule ℂ (UA L n → ℂ)} (hπ : IsAutRepU π)
    (P : GlobalTheory.DefU.autU L n →ₗ[ℂ] GlobalTheory.DefU.autU L n) (hP : ∀ φ, (P φ).1 ∈ σ)
    (he : ∀ x φ, P (GlobalTheory.DefU.autRep L n x φ) = GlobalTheory.DefU.autRep L n x (P φ))
    (ψ : GlobalTheory.DefU.autU L n) (hψ : ψ.1 ∈ π) (h0 : P ψ ≠ 0) (w : Plc L) (τ : SmIrr (GL (Fin n) (Kw w)))
    (h : Comp π w τ) : Comp σ w τ := by
  have hle : π ≤ GlobalTheory.DefU.autU L n := hπ.aut
  have hK : π ⊓ (LinearMap.ker P).map (GlobalTheory.DefU.autU L n).subtype = ⊥ := by
    refine (hπ.irred _ inf_le_left ?_).resolve_right fun e => h0 ?_
    · rintro x _ ⟨h1, φ, h2, rfl⟩
      refine ⟨hπ.stable x _ h1, GlobalTheory.DefU.autRep L n x φ, ?_, rfl⟩
      have h2' : P φ = 0 := h2
      change P _ = 0
      rw [he, h2', map_zero]
    · obtain ⟨-, φ, h2, h3⟩ := e.ge hψ
      obtain rfl : φ = ψ := Subtype.ext h3
      exact h2
  obtain ⟨h1, f, hf0, hf, h2⟩ := h
  let g := f.codRestrict (GlobalTheory.DefU.autU L n) fun v => hle (hf v)
  refine ⟨h1, (GlobalTheory.DefU.autU L n).subtype ∘ₗ P ∘ₗ g, fun e => hf0 (LinearMap.ext fun v => ?_), fun v => hP _,
    fun x v => ?_⟩
  · have h3 : P (g v) = 0 := Subtype.ext (LinearMap.congr_fun e v)
    exact hK.le ⟨hf v, g v, h3, rfl⟩
  · have h3 : g (τ.ρ (((cLoc w).comp (locU n w).subtype) x) v) = GlobalTheory.DefU.autRep L n x (g v) :=
      Subtype.ext (h2 x v)
    exact congrArg Subtype.val ((congrArg P h3).trans (he x _))

theorem UpperTheory.V.Z.Sym.U.finFamU :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V), ContCoef R → ∀ U, IsLevel U →
        ∃ A : Set (Submodule ℂ (UA L n → ℂ)), A.Finite ∧ (∀ σ ∈ A, IsAutRepU σ ∧ (∃ φ ∈ σ, φ ≠ 0 ∧ ∀ u ∈ U, RU L n u φ = φ)) ∧
          ∀ π, IsAutRepU π → ∀ φ : UA L n → V, φ ≠ 0 → IsAF R U φ → CoefIn φ π → ∃ σ ∈ A, ∀ w τ, Comp π w τ → Comp σ w τ := by
  intro L _ _ _ n V _ _ _ R hR U hU
  have := afFin L n V R U hU
  let b := Module.finBasis ℂ V
  let T : Fin (Module.finrank ℂ V) → AF R U →ₗ[ℂ] GlobalTheory.DefU.autU L n := fun i =>
    (((b.coord i).compLeft (UA L n)) ∘ₗ (AF R U).subtype).codRestrict _ fun φ =>
      coefAut L n V R hR U hU φ.1 φ.2 (b.coord i)
  obtain ⟨κ, _, σ, P, h1, h2, h3, h4⟩ := autProj L n (⨆ i, LinearMap.range (T i)) inferInstance
  refine ⟨{s ∈ Set.range σ | ∃ φ ∈ s, φ ≠ 0 ∧ ∀ u ∈ U, RU L n u φ = φ}, (Set.finite_range σ).subset fun _ h => h.1, ?_,
    fun π hπ φ h0 hφ hc => ?_⟩
  · rintro _ ⟨⟨i, rfl⟩, h⟩
    exact ⟨h1 i, h⟩
  obtain ⟨i, hi⟩ : ∃ i, T i ⟨φ, hφ⟩ ≠ 0 := by
    by_contra! h
    refine h0 (funext fun g => b.ext_elem fun i => ?_)
    have h5 : b.coord i (φ g) = 0 := congrFun (congrArg Subtype.val (h i)) g
    simpa using h5
  obtain ⟨k, hk⟩ : ∃ k, P k (T i ⟨φ, hφ⟩) ≠ 0 := by
    by_contra! h
    refine hi ?_
    rw [← h4 (T i ⟨φ, hφ⟩) (Submodule.mem_iSup_of_mem i ⟨_, rfl⟩)]
    simp [h]
  refine ⟨σ k, ⟨⟨k, rfl⟩, (P k (T i ⟨φ, hφ⟩)).1, h2 k _, fun e => hk (Subtype.ext e), fun u hu => ?_⟩,
    comp_of_proj hπ (P k) (h2 k) (h3 k) _ (hc (b.coord i)) hk⟩
  have e : GlobalTheory.DefU.autRep L n u (T i ⟨φ, hφ⟩) = T i ⟨φ, hφ⟩ :=
    Subtype.ext (funext fun g => congrArg (b.coord i) (hφ.level u hu g))
  have := h3 k u (T i ⟨φ, hφ⟩)
  rw [e] at this
  exact congrArg Subtype.val this.symm

private theorem mem_lev {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {U : Subgroup (UA L n)} {S : Finset (Plc L)}
    (hS : Places (S : Set (Plc L))) (hK : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U) {w : Plc L} (hw : w ∈ S) {x : UA L n}
    (hx : x ∈ locU n w) (hJ : cLoc w x ∈ (iw w).J n) : x ∈ lev U S iw := by
  have hk : x ∈ Kall L n := by
    refine ((factor L n w).2.2.2.2.1 x hx).2 ?_
    rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL]
    exact ((Sig.finFacts _ (iw w)).2.2.2.2.2 n).2.2.2 hJ
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨hK w hw ⟨hx, hk⟩, fun w' hw' => ?_⟩
  by_cases e : w' = w
  · subst e; exact hJ
  · have hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L)) := fun h => e (hS.inj hw' hw h.symm)
    have := (factor L n w').2.2.1 w hne hx
    simp only [away, Subgroup.mem_iInf] at this
    rw [Subgroup.mem_comap, (MonoidHom.mem_ker.1 (this w' rfl))]
    exact one_mem _

private theorem unram_of {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (σ : Submodule ℂ (UA L n → ℂ)) (S : Finset (Plc L))
    (V : ∀ w : Plc L, Sig.Lev (Kw w)) (h : ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ u ∈ lev (Kall L n) S V, RU L n u φ = φ) (w : Plc L)
    (hw : ∀ w' ∈ S, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) : IsUnramU σ w := by
  obtain ⟨φ, h1, h2, h3⟩ := h
  refine ⟨φ, h1, h2, fun x hx hK => h3 x ?_⟩
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨((factor L n w).2.2.2.2.1 x hx).2 hK, fun w' hw' => ?_⟩
  have := (factor L n w').2.2.1 w (hw w' hw').symm hx
  simp only [away, Subgroup.mem_iInf] at this
  rw [Subgroup.mem_comap, (MonoidHom.mem_ker.1 (this w' rfl))]
  exact one_mem _

private theorem pigeon {X I : Type} (A : Set X) (hA : A.Finite) (P : X → I → Prop)
    (h : ∀ S : Finset I, ∃ x ∈ A, ∀ i ∈ S, P x i) : ∃ x ∈ A, ∀ i, P x i := by
  classical
  by_contra hn
  push Not at hn
  choose f hf using fun x : A => hn x.1 x.2
  haveI := hA.fintype
  obtain ⟨x, hx, h1⟩ := h (Finset.univ.image f)
  exact hf ⟨x, hx⟩ (h1 _ (Finset.mem_image_of_mem f (Finset.mem_univ _)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.ProjectionComponents.UfDg
section
noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym

namespace UpperTheory.V.Z.Sym.U

private def dg {Γ k : Type} [Group Γ] [Field k] (χ : Γ →* kˣ) : Γ →* GL (Fin 2) k where
  toFun g := Matrix.GeneralLinearGroup.mkOfDetNeZero !![(χ g : k), 0; 0, 1] (by simp)
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
  map_mul' g h := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]

private theorem uf_dg {Γ k : Type} [Group Γ] [Field k] (χ : Γ →* kˣ) (g : Γ) : Ga.uf (dg χ g) = (χ g : k) + (χ g : k)⁻¹ := by
  have h0 : (χ g : k) ≠ 0 := (χ g).ne_zero
  simp only [Ga.uf, Ga.tr, dg, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.trace_fin_two, Matrix.det_fin_two]
  simp
  field_simp
  ring

theorem xiOne (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime]
    (r : G L Ω →* GL (Fin 2) (Qbar l)) (hc : Continuous r) (h4 : IrrOpen (Ga.sym4 r)) (ξ : G L Ω →* (Qbar l)ˣ)
    (hξ : IsOpen (ξ.ker : Set (G L Ω))) (h : ∀ g ∉ Ga.Bad r, (ξ g : Qbar l) * (Ga.uf (r g) + 1) = Ga.uf (r g) + 1) : ξ = 1 := by
  by_contra hne
  obtain ⟨g0, hg0⟩ : ∃ g0, ξ g0 ≠ 1 := by
    by_contra hall
    push_neg at hall
    exact hne (MonoidHom.ext hall)
  obtain ⟨huf, hep, hbad⟩ := Ga.badClosed L Ω l r hc
  set U : Set (G L Ω) := (fun g => g0⁻¹ * g) ⁻¹' (ξ.ker : Set (G L Ω)) with hU
  have hUo : IsOpen U := hξ.preimage (continuous_const.mul continuous_id)
  have hg0U : g0 ∈ U := by
    show g0⁻¹ * g0 ∈ ξ.ker
    rw [inv_mul_cancel]
    exact ξ.ker.one_mem
  have hUξ : ∀ g ∈ U, ξ g = ξ g0 := by
    intro g hg
    have h1 : ξ (g0⁻¹ * g) = 1 := MonoidHom.mem_ker.mp hg
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  by_cases hcase : (U ∩ (Ga.Bad r)ᶜ).Nonempty
  · apply Ga.noKappa l (G L Ω) r r h4 (U ∩ (Ga.Bad r)ᶜ) (hUo.inter hbad.isOpen_compl) hcase
    intro g hg
    have h1 := h g hg.2
    rw [hUξ g hg.1] at h1
    have h2 : Ga.uf (r g) + 1 = 0 := by
      have h3 : ((ξ g0 : Qbar l) - 1) * (Ga.uf (r g) + 1) = 0 := by
        rw [sub_mul, h1]
        ring
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd (Units.val_eq_one.mp (sub_eq_zero.mp h4)) hg0
      · exact h4
    have h5 : Ga.uf (r g) = -1 := by linear_combination h2
    rw [h5]
    norm_num
  · have hsub : U ⊆ Ga.Bad r := by
      intro g hg
      by_contra hgb
      exact hcase ⟨g, hg, hgb⟩
    set B : ℤ → Set (G L Ω) := fun m =>
      {g | Ga.uf (r g) ^ 2 - 2 = Ga.ep l (g ^ m) + Ga.ep l (g ^ (-m))} with hB
    have hBc : ∀ m, IsClosed (B m) := fun m =>
      isClosed_eq ((huf.pow 2).sub continuous_const)
        ((hep.comp (continuous_zpow m)).add (hep.comp (continuous_zpow (-m))))
    have hepz : ∀ g : G L Ω, ∀ m : ℤ, Ga.ep l (g ^ m) = Ga.ep l g ^ m := by
      intro g m
      simp only [Ga.ep, map_zpow, Units.val_zpow_eq_zpow_val]
    have hBad : Ga.Bad r ⊆ ⋃ m ∈ Finset.Icc (-2 : ℤ) 2, B m := by
      intro g hg
      obtain ⟨m, hm, he⟩ := hg
      simp only [Set.mem_iUnion, Finset.mem_Icc]
      refine ⟨m, ⟨(abs_le.mp hm).1, (abs_le.mp hm).2⟩, ?_⟩
      show _ = _
      rw [hepz, hepz]
      exact he
    have claim : ∀ (s : Finset ℤ) (W : Set (G L Ω)), IsOpen W → W.Nonempty → W ⊆ ⋃ m ∈ s, B m →
        ∃ m, ∃ V : Set (G L Ω), IsOpen V ∧ V.Nonempty ∧ V ⊆ B m := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · intro W _ hW hsW
        obtain ⟨w, hw⟩ := hW
        simpa using hsW hw
      · intro a s _ ih W hWo hW hsW
        by_cases hd : (W ∩ (B a)ᶜ).Nonempty
        · refine ih _ (hWo.inter (hBc a).isOpen_compl) hd ?_
          intro g hg
          have h6 := hsW hg.1
          simp only [Finset.set_biUnion_insert, Set.mem_union] at h6
          exact h6.resolve_left hg.2
        · refine ⟨a, W, hWo, hW, fun g hg => ?_⟩
          by_contra hga
          exact hd ⟨g, hg, hga⟩
    obtain ⟨m, V, hVo, hVn, hVB⟩ := claim _ U hUo ⟨g0, hg0U⟩ (hsub.trans hBad)
    apply Ga.noKappa l (G L Ω) r (dg ((cycBar L Ω l) ^ m)) h4 V hVo hVn
    intro g hg
    have h7 : Ga.uf (r g) ^ 2 - 2 = Ga.ep l (g ^ m) + Ga.ep l (g ^ (-m)) := hVB hg
    rw [uf_dg, h7, hepz, hepz]
    simp [Ga.ep, zpow_neg]

end UpperTheory.V.Z.Sym.U
end
end

