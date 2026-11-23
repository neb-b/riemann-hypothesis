module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0011
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsotypicOfJointlyInjectiveIntoIsotypic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsMultilinearIntertwinerOfCommutingSubgroups
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsDualSchurModuleIsoDualWeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceAutomorphicProperties
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTermSpace_automorphic_properties :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (S : Submodule ℂ (archSmooth K (r + s))), Bdd S → Sat S → ctSp r S ≤ NInv K (r + s) r ∧ Growth (ctSp r S) ∧ Level (ctSp r S) ∧ Sat (ctSp r S) ∧ ∀ ψ ∈ ctSp r S, ∀ (γ₁ : GL (Fin r) K) (γ₂ : GL (Fin s) K) g, ψ.1 (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * g) = ψ.1 g := by
  intro K _ _ r s S hB hS
  have hrt : ∀ (φ φ' : AdelicGLn.AdelicGL K (r + s) → ℂ) (k : AdelicGLn.AdelicGL K (r + s)),
      (∀ x, φ' x = φ (x * k)) → ∀ g, constantTerm r φ (g * k) = constantTerm r φ' g := by
    intro φ φ' k h g
    unfold constantTerm
    simp only [h, mul_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro ψ ⟨φ, hφ, e⟩ X g
    rw [e]
    exact UpperTheory.constantTerm_unipotent_left_invariant K _ r φ.1 (hB.left φ hφ) X g
  · intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h =>
      obtain ⟨φ, hφ, e⟩ := h
      rw [e]
      exact UpperTheory.hasModerateGrowth_constantTerm K _ r φ.1 (hB.growth φ hφ)
    | zero => exact hasModerateGrowth_zero
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx => exact hx.smul c
  · obtain ⟨L, hL, h⟩ := hB.level
    refine ⟨L, hL, fun ψ hψ u hu g => ?_⟩
    induction hψ using Submodule.span_induction with
    | mem ψ h' =>
      obtain ⟨φ, hφ, e⟩ := h'
      rw [e]
      exact hrt φ.1 φ.1 _ (fun x => (h φ hφ u hu x).symm) g
    | zero => rfl
    | add x y _ _ hx hy => exact congrArg₂ (· + ·) hx hy
    | smul c x _ hx => exact congrArg (c • ·) hx
  · intro k hk ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h' =>
      obtain ⟨φ, hφ, e⟩ := h'
      refine Submodule.subset_span ⟨rt k φ, hS k hk φ hφ, funext fun g => ?_⟩
      rw [rt_apply, e]
      exact hrt φ.1 _ k (rt_apply k φ) g
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  · intro ψ hψ γ₁ γ₂ g
    induction hψ using Submodule.span_induction with
    | mem ψ h' =>
      obtain ⟨φ, hφ, e⟩ := h'
      rw [e]
      exact UpperTheory.constantTerm_levi_rational_left_invariant K r s φ.1 (hB.left φ hφ) γ₁ γ₂ g
    | zero => rfl
    | add x y _ _ hx hy => exact congrArg₂ (· + ·) hx hy
    | smul c x _ hx => exact congrArg (c • ·) hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DdRLeFilAndInfFilEqBotOfHodgeTateMult
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

private theorem step_of_mult [CharZero Qp] (PD : PeriodData G Qp K₀ K B BdR)
    [Fintype (K →ₐ[Qp] LL)] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (ρ : Representation LL G V) (hfin : FiniteDimensional LL ↥(DdR PD ρ)) (c : ℤ)
    (h : ∀ τ : K →ₐ[Qp] LL, multV PD ρ τ c = 0) :
    DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) (c + 1) = DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) c := by
  rw [JsetEmb.de_rham_filtration_eq_iSup_embeddings PD hcard ρ (c + 1), JsetEmb.de_rham_filtration_eq_iSup_embeddings PD hcard ρ c]
  refine iSup_congr fun τ => ?_
  have hle : FildR PD ρ τ c ≤ DdR PD ρ := fun x hx => hx.1.1
  have : FiniteDimensional LL ↥(FildR PD ρ τ c) := Submodule.finiteDimensional_of_le hle
  have h0 := h τ
  unfold multV at h0
  refine Submodule.eq_of_le_of_finrank_eq (Ln03.Pf.jb_FildR_anti PD ρ τ (by omega)) ?_
  omega

private theorem gen_fil [CharZero Qp] (PD : PeriodData G Qp K₀ K B BdR)
    [Fintype (K →ₐ[Qp] LL)] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (ρ : Representation LL G V) (hfin : FiniteDimensional LL ↥(DdR PD ρ)) :
    (∀ a : ℤ, (∀ (τ : K →ₐ[Qp] LL) (c : ℤ), c < a → multV PD ρ τ c = 0) →
      DdR PD ρ ≤ FilV PD (LL := LL) (V := V) a) ∧
    ∀ b : ℤ, (∀ (τ : K →ₐ[Qp] LL) (c : ℤ), b < c → multV PD ρ τ c = 0) →
      DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) (b + 1) = ⊥ := by
  refine ⟨fun a ha x hx => ?_, fun b hb => ?_⟩
  · obtain ⟨c, hc⟩ := Ln03.Pf.jb_FilV_exh PD (LL := LL) (V := V) x
    rcases le_total a c with h | h
    · exact Ln03.Pf.jb_FilV_anti PD (LL := LL) (V := V) h hc
    · have key : ∀ d, c ≤ d → d ≤ a → x ∈ FilV PD (LL := LL) (V := V) d := by
        intro d hd
        induction d, hd using Int.leInduction with
        | base => exact fun _ => hc
        | succ d hd ih =>
          intro hda
          have hm : x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) d := ⟨hx, ih (by omega)⟩
          rw [← step_of_mult PD hcard ρ hfin d fun τ => ha τ d (by omega)] at hm
          exact hm.2
      exact key a h le_rfl
  · rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    refine Ln03.Pf.jb_FilV_sep PD (LL := LL) (V := V) x fun d => ?_
    rcases le_total d (b + 1) with h | h
    · exact Ln03.Pf.jb_FilV_anti PD (LL := LL) (V := V) h hx.2
    · induction d, h using Int.leInduction with
      | base => exact hx.2
      | succ d hd ih =>
        have hm : x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) d := ⟨hx.1, ih⟩
        rw [← step_of_mult PD hcard ρ hfin d fun τ => hb τ d (by omega)] at hm
        exact hm.2

end Gen

theorem UpperTheory.ddR_le_fil_and_inf_fil_eq_bot_of_hodgeTate_mult :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ LL.1) → ∀ {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) ρ) → (∀ a : ℤ, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ℤ), c < a → multV (P.PD K) ρ τ c = 0) → DdR (P.PD K) ρ ≤ FilV (P.PD K) (LL := ↥LL.1) (V := V) a) ∧ ∀ b : ℤ, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ℤ), b < c → multV (P.PD K) ρ τ c = 0) → DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V) (b + 1) = ⊥ := by
  intro l _ P K LL key V _ _ _ _ _ ρ hfin
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hc : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := by
    let e : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) ≃ (↥K.1 →ₐ[ℚ_[l]] Om l) :=
      { toFun := fun f => LL.1.val.comp f
        invFun := fun g => g.codRestrict LL.1.toSubalgebra (key g)
        left_inv := fun f => by ext; rfl
        right_inv := fun g => by ext; rfl }
    rw [Nat.card_congr e]
    exact AlgHom.natCard_of_splits _ _ _ (fun _ => IsAlgClosed.splits _)
  have : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Module.finrank_pos.ne')
  letI := Fintype.ofFinite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
  exact gen_fil (P.PD K) (by rw [Fintype.card_eq_nat_card, hc]) ρ hfin
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsConstantTermLinearMapEquivariantUniversalE
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ), ∃ f : automorphicForms K n →ₗ[ℂ] archSmooth K n, (∀ φ, (f φ).1 = constantTerm r φ.1) ∧ ∀ u φ, f (uActionAF K n u φ) = uAction u (f φ) := by
  intro K _ _ n r
  have h := fun φ : automorphicForms K n =>
    UpperTheory.constantTerm_archSmooth K n r ⟨φ.1, automorphicForms_le_archSmooth φ.2⟩ φ.2
  choose hs hX using h
  let f : automorphicForms K n →ₗ[ℂ] archSmooth K n :=
    { toFun := fun φ => ⟨constantTerm r φ.1, hs φ⟩
      map_add' := fun φ ψ => Subtype.ext (funext fun g =>
        constantTerm_add (IsAutomorphicForm.continuous φ.2) (IsAutomorphicForm.continuous ψ.2) g)
      map_smul' := fun c φ => Subtype.ext (funext fun g => constantTerm_smul c φ.1 g) }
  refine ⟨f, fun _ => rfl, fun u => ?_⟩
  induction u using UEnv.induction with
  | halg c =>
    intro φ
    have e : uActionAF K n (algebraMap ℝ (UEnv K n) c) φ = (c : ℂ) • φ :=
      Subtype.ext (coe_uAction_algebraMap c ⟨φ.1, automorphicForms_le_archSmooth φ.2⟩)
    rw [e, map_smul]
    exact Subtype.ext (coe_uAction_algebraMap c (f φ)).symm
  | hι X => exact fun φ => Subtype.ext (hX φ X).symm
  | hmul a b ha hb =>
    intro φ
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  | hadd a b ha hb =>
    intro φ
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), ha, hb]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsTensorDualEmbeddingOfHasWeightAt
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

section
open GlobalTheory.DefU GlobalTheory.Branching
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem irr_emb (τ : E →+* ℂ) (lam : DomWeight n) :
    Representation.IsIrreducible ((sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype)) := by
  obtain ⟨e, he⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n τ
  have heq : (sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype) =
      (smallRep (unitaryIncl n) lam).comp e.toMulEquiv.toMonoidHom := by
    ext x : 1
    change sqRep ℂ n lam (cEmb τ (x : UA E n)) = sqRep ℂ n lam (unitaryIncl n (e x))
    rw [he]
  rw [heq]
  exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv _ e.toMulEquiv (isIrreducible_smallRep_unitary n lam)

private noncomputable def locRep (τ : E →+* ℂ) (lam : DomWeight n) :
    Representation ℂ ((embU n τ).subgroupOf (infU E n)) (nablaSq ℂ n lam) :=
  (sqRep ℂ n lam).comp ((cEmb τ).comp ((infU E n).subtype.comp (Subgroup.subtype _)))

private theorem irr_locRep (τ : E →+* ℂ) (lam : DomWeight n) : (locRep τ lam).IsIrreducible :=
  GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv _ (Subgroup.subgroupOfEquivOfLe (embU_le_infU τ)) (irr_emb τ lam)

private noncomputable def repN {m : ℕ} (N : Submodule ℂ (Fin m → UA E n → ℂ))
    (hN : ∀ x ∈ infU E n, ∀ F ∈ N, (fun k => RU E n x (F k)) ∈ N) : Representation ℂ (infU E n) N where
  toFun x :=
    { toFun := fun F => ⟨fun k => RU E n x (F.1 k), hN x x.2 F.1 F.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext F k g
    simp
  map_mul' x y := by
    ext F k : 3
    exact (RU_RU x.1 y.1 (F.1 k)).symm

private theorem isoN {m : ℕ} (N : Submodule ℂ (Fin m → UA E n → ℂ))
    (hN : ∀ x ∈ infU E n, ∀ F ∈ N, (fun k => RU E n x (F k)) ∈ N) (σ : Submodule ℂ (UA E n → ℂ))
    (hσ : IsAutRepU σ) (hNσ : ∀ F ∈ N, ∀ k, F k ∈ σ) (τ : E →+* ℂ) (lam : DomWeight n) (h : HasWeightAt σ τ lam) :
    (⨆ f : {f : nablaSq ℂ n lam →ₗ[ℂ] N // ∀ (g : (embU n τ).subgroupOf (infU E n)) v,
      f (locRep τ lam g v) = repN N hN g (f v)}, LinearMap.range f.1) = ⊤ := by
  let π : AutSub E n := ⟨σ, hσ⟩
  have h1 := iSup_range_weight_eq_top E n π τ lam h
  refine UpperTheory.isotypic_of_jointly_injective_into_isotypic _ _ π.V (locRep τ lam) (π.rep.comp ((infU E n).subtype.comp (Subgroup.subtype _)))
    (irr_locRep τ lam) ?_ N ((repN N hN).comp (Subgroup.subtype _)) (Fin m)
    (fun k => ((LinearMap.proj k).comp N.subtype).codRestrict σ fun F => hNσ F.1 F.2 k) (fun _ _ _ => rfl)
    (fun y hy => Subtype.ext (funext fun k => congrArg Subtype.val (hy k)))
  refine top_le_iff.1 (h1.ge.trans (iSup_le fun f => ?_))
  exact le_iSup_of_le ⟨f.toLinearMap, fun g v => LinearMap.congr_fun (f.isIntertwining' ⟨g.1.1, g.2⟩) v⟩ le_rfl

private theorem exists_multi {I : Type} [Finite I] (emb : I → (E →+* ℂ))
    (hb : Function.Bijective (fun i => InfinitePlace.mk (emb i))) (lam : I → DomWeight n)
    (σ : Submodule ℂ (UA E n → ℂ)) (hσ : IsAutRepU σ) (hw : ∀ i, HasWeightAt σ (emb i) (lam i)) {m : ℕ}
    (N : Submodule ℂ (Fin m → UA E n → ℂ)) (h0 : N ≠ ⊥) (hNσ : ∀ F ∈ N, ∀ k, F k ∈ σ)
    (hN : ∀ x ∈ infU E n, ∀ F ∈ N, (fun k => RU E n x (F k)) ∈ N) :
    ∃ μ : MultilinearMap (RingHom.id ℂ) (fun i => nablaSq ℂ n (lam i)) N, μ ≠ 0 ∧ ∀ x ∈ infU E n, ∀ v k,
      RU E n x ((μ v).1 k) = (μ fun i => sqRep ℂ n (lam i) (cEmb (emb i) x) (v i)).1 k := by
  classical
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 h0
  obtain ⟨hgen, hcomm⟩ := UpperTheory.archimedeanUnitary_le_iSup_embU_and_commute E n
  obtain ⟨μ, hμ0, hμ⟩ := UpperTheory.exists_multilinear_intertwiner_of_commuting_subgroups (infU E n) I (fun i => (embU n (emb i)).subgroupOf (infU E n))
    (fun i j hij a ha b hb' => Subtype.ext (hcomm (emb i) (emb j) (fun e => hij (hb.1 e)) a.1 ha b.1 hb'))
    (fun i => nablaSq ℂ n (lam i)) (fun i => locRep (emb i) (lam i)) (fun i => irr_locRep _ _) N (repN N hN)
    (fun i => isoN N hN σ hσ hNσ (emb i) (lam i) (hw i))
  refine ⟨μ, hμ0, fun x hx => ?_⟩
  refine Subgroup.iSup_induction _ (C := fun x => ∀ v k,
      RU E n x ((μ v).1 k) = (μ fun i => sqRep ℂ n (lam i) (cEmb (emb i) x) (v i)).1 k) (hgen hx) ?_ ?_ ?_
  · intro τ y hy v k
    obtain ⟨i, hi⟩ := hb.2 (InfinitePlace.mk τ)
    have hi' : InfinitePlace.mk (emb i) = InfinitePlace.mk τ := hi
    have hy' : y ∈ embU n (emb i) := by
      unfold embU at hy ⊢
      rwa [hi']
    have h2 := hμ i ⟨⟨y, embU_le_infU _ hy'⟩, hy'⟩ v
    have h3 : (fun j => sqRep ℂ n (lam j) (cEmb (emb j) y) (v j)) =
        Function.update v i (locRep (emb i) (lam i) ⟨⟨y, embU_le_infU _ hy'⟩, hy'⟩ (v i)) := by
      funext j
      by_cases e : j = i
      · subst e
        rw [Function.update_self]
        rfl
      · have h4 := (Subgroup.mem_inf.1 hy').2
        rw [Subgroup.mem_iInf] at h4
        have h5 := h4 (emb j)
        rw [Subgroup.mem_iInf] at h5
        have h6 : cEmb (emb j) y = 1 := h5 fun e' => e (hb.1 e')
        rw [Function.update_of_ne e, h6, map_one, Module.End.one_apply]
    rw [h3, h2]
    rfl
  · intro v k
    simp only [map_one, Module.End.one_apply]
  · intro a b ha hb v k
    rw [← RU_RU, hb, ha]
    simp only [map_mul, Module.End.mul_apply]

end

private theorem dualDistrib_comp_map {I : Type} [Finite I] {M : I → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (f : ∀ i, Module.Dual ℂ (M i)) (g : ∀ i, M i →ₗ[ℂ] M i) :
    PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ f) ∘ₗ PiTensorProduct.map g =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ fun i => f i ∘ₗ g i) := by
  have := Fintype.ofFinite I
  ext v
  simp [PiTensorProduct.dualDistrib_apply]

theorem UpperTheory.exists_tensor_dual_embedding_of_hasWeightAt :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (I : Type) [Finite I] (emb : I → (E →+* ℂ)), Function.Bijective (fun i => InfinitePlace.mk (emb i)) → ∀ (lam : I → DomWeight n) (σ : Submodule ℂ (UA E n → ℂ)), IsAutRepU σ → (∀ i, HasWeightAt σ (emb i) (lam i).dual) → ∀ (m : ℕ) (N : Submodule ℂ (Fin m → UA E n → ℂ)), N ≠ ⊥ → (∀ F ∈ N, ∀ k, F k ∈ σ) → (∀ x ∈ infU E n, ∀ F ∈ N, (fun k => RU E n x (F k)) ∈ N) → ∃ Φ : Module.Dual ℂ (⨂[ℂ] i : I, nablaSq ℂ n (lam i)) →ₗ[ℂ] (Fin m → UA E n → ℂ), Φ ≠ 0 ∧ (∀ ℓ, Φ ℓ ∈ N) ∧ ∀ ℓ, ∀ x ∈ infU E n, ∀ k, RU E n x (Φ ℓ k) = Φ (ℓ ∘ₗ PiTensorProduct.map fun i => GlobalTheory.Branching.sqRep ℂ n (lam i) (cEmb (emb i) x⁻¹)) k := by
  intro E _ _ _ n hn I _ emb hb lam σ hσ hw m N h0 hNσ hN
  obtain ⟨μ, hμ0, hμ⟩ := exists_multi emb hb (fun i => (lam i).dual) σ hσ hw N h0 hNσ hN
  choose κ hκ using fun i => UpperTheory.exists_dual_schur_module_iso_dual_weight n hn (lam i)
  let D := PiTensorProduct.dualDistribEquiv (R := ℂ) (M := fun i => nablaSq ℂ n (lam i))
  have hD : ∀ t, D t = PiTensorProduct.dualDistrib t := fun _ => rfl
  let Ψ := PiTensorProduct.lift (μ.compLinearMap fun i => (κ i).toLinearMap)
  have hΦ : ∀ f, (N.subtype ∘ₗ Ψ ∘ₗ D.symm.toLinearMap) (D (PiTensorProduct.tprod ℂ f)) =
      (μ fun i => κ i (f i)).1 := by
    intro f
    change (Ψ (D.symm (D _))).1 = _
    rw [D.symm_apply_apply, PiTensorProduct.lift.tprod]
    rfl
  refine ⟨N.subtype ∘ₗ Ψ ∘ₗ D.symm.toLinearMap, fun h => hμ0 ?_, fun ℓ => (Ψ (D.symm ℓ)).2, fun ℓ x hx k => ?_⟩
  · ext v : 1
    have := hΦ fun i => (κ i).symm (v i)
    rw [h] at this
    simp only [LinearEquiv.apply_symm_apply] at this
    exact Subtype.ext this.symm
  · obtain ⟨t, rfl⟩ := D.surjective ℓ
    generalize (N.subtype ∘ₗ Ψ ∘ₗ D.symm.toLinearMap) = Φ at hΦ
    induction t using PiTensorProduct.induction_on with
    | smul_tprod c f =>
      rw [map_smul, LinearMap.smul_comp, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, map_smul]
      congr 1
      rw [hΦ, hμ x hx, hD, dualDistrib_comp_map, ← hD, hΦ]
      simp only [map_inv (cEmb _), hκ]
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_comp, Pi.add_apply, ha, hb]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalOfFiniteDimensionalLeviSlices
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.finiteDimensional_of_finiteDimensional_levi_slices :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (S : Submodule ℂ (archSmooth K (r + s))), S ≤ NInv K (r + s) r → Sat S → Level S → Types S → FiniteDimensional ℂ (slSp (e1 r s) (Set.range (emb (e2 r s))) S) → FiniteDimensional ℂ (slSp (e2 r s) (Set.range (emb (e1 r s))) S) → FiniteDimensional ℂ S := by
  intro K _ _ r s S hN hsat hlev htyp h1 h2
  obtain ⟨V, hVfd, hV⟩ := UpperTheory.exists_finiteDimensional_compact_translates_of_level_types K (r + s) S hlev htyp
  let Φ₀ : archSmooth K (r + s) →ₗ[ℂ] (AdelicGLn.AdelicGL K r × AdelicGLn.AdelicGL K s → ℂ) :=
    { toFun := fun m p => (m : AdelicGLn.AdelicGL K (r + s) → ℂ) (emb (e1 r s) p.1 * emb (e2 r s) p.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Φ : archSmooth K (r + s) →ₗ[ℂ]
      ((AdelicGLn.AdelicGL K r × AdelicGLn.AdelicGL K s) × (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K (r + s))) → ℂ) :=
    { toFun := fun m p => (m : AdelicGLn.AdelicGL K (r + s) → ℂ) (emb (e1 r s) p.1.1 * emb (e2 r s) p.1.2 * (p.2 : AdelicGLn.AdelicGL K (r + s)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hfd0 : FiniteDimensional ℂ (Submodule.map Φ₀ S) := by
    refine UpperTheory.finiteDimensional_map_of_separately_finite _ _ _ S Φ₀ ((slSp (e1 r s) (Set.range (emb (e2 r s))) S).map (archSmooth K r).subtype)
      ((slSp (e2 r s) (Set.range (emb (e1 r s))) S).map (archSmooth K s).subtype) inferInstance inferInstance ?_ ?_
    · intro m hm y
      obtain ⟨f, hf, -⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K r (r + s) (e1 r s) (emb (e2 r s) y)
      refine Submodule.mem_map.mpr ⟨f m, Submodule.subset_span ⟨m, hm, emb (e2 r s) y, ⟨y, rfl⟩, fun x => hf m x⟩, ?_⟩
      funext x
      change (f m : AdelicGLn.AdelicGL K r → ℂ) x = _
      rw [hf, ← emb_comm]
      rfl
    · intro m hm x
      obtain ⟨f, hf, -⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K s (r + s) (e2 r s) (emb (e1 r s) x)
      refine Submodule.mem_map.mpr ⟨f m, Submodule.subset_span ⟨m, hm, emb (e1 r s) x, ⟨x, rfl⟩, fun y => hf m y⟩, ?_⟩
      funext y
      change (f m : AdelicGLn.AdelicGL K s → ℂ) y = _
      rw [hf]
      rfl
  have hfd : FiniteDimensional ℂ (Submodule.map Φ S) := by
    refine UpperTheory.finiteDimensional_map_of_separately_finite _ _ _ S Φ (Submodule.map Φ₀ S) V hfd0 hVfd ?_ ?_
    · intro m hm k
      refine Submodule.mem_map.mpr ⟨rt (k : AdelicGLn.AdelicGL K (r + s)) m, hsat _ k.2 m hm, ?_⟩
      funext x
      change ((rt (k : AdelicGLn.AdelicGL K (r + s)) m : archSmooth K (r + s)) : AdelicGLn.AdelicGL K (r + s) → ℂ) _ = _
      rw [rt_apply]
      rfl
    · intro m hm x
      exact hV m hm (emb (e1 r s) x.1 * emb (e2 r s) x.2)
  refine FiniteDimensional.of_injective (Φ.submoduleMap S) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hx' : ∀ p, Φ x p = 0 := fun p => congrFun (congrArg Subtype.val hx) p
  apply Subtype.ext
  apply Subtype.ext
  funext g
  obtain ⟨b, hb, k, hk, rfl⟩ := Reduction.exists_adelicBorel_mul_maxCompact g
  obtain ⟨X, m₁, m₂, rfl⟩ := UpperTheory.upperTriangular_eq_unipotent_mul_levi _ r s b (Reduction.mem_adelicBorel.mp hb)
  have hxN := hN x.2
  change ((x : archSmooth K (r + s)) : AdelicGLn.AdelicGL K (r + s) → ℂ) (unipGL X * blk m₁ m₂ * k) = 0
  rw [mul_assoc]
  change (∀ (X : UPos (r + s) r → AdeleRing (𝓞 K) K) g, ((x : archSmooth K (r + s)) : AdelicGLn.AdelicGL K (r + s) → ℂ) (unipGL X * g) = _) at hxN
  rw [hxN]
  exact hx' ((m₁, m₂), ⟨k, hk⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixedCongruenceNeBotOfJacquetTorusFixed
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.fixed_congruence_ne_bot_of_jacquet_torus_fixed :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1),
    IsAdmissible π → ∀ y : Jacquet π (unipB k (Fin N)), y ≠ 0 →
    (∀ t : Fin N → kˣ, (∀ i, valuation k ((t i : k) - 1) < γ) → jacBU π t y = y) →
    fixed π (GlobalTheory.CentralExponent.cong (Fin N) γ hγ) ≠ ⊥ := by
  intro k _ _ _ _ N V _ _ π γ hγ hπ y hy0 hy hbot
  have hmem : ∀ d : Fin N → kˣ, diagT k (Fin N) d ∈ GlobalTheory.CentralExponent.cong (Fin N) γ hγ ↔
      ∀ i, valuation k ((d i : k) - 1) < γ := by
    intro d
    constructor
    · intro h i
      have := h i i
      simpa [val_diagT] using this
    · intro h i j
      by_cases hij : i = j
      · subst hij
        simpa [val_diagT] using h i
      · simp [val_diagT, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  obtain ⟨v, hv, e⟩ := GlobalTheory.SmGL.IwahoriOnto.exists_fixed_mk_eq hπ
    (GlobalTheory.CentralExponent.isOpen_cong γ hγ) (GlobalTheory.CentralExponent.isCompact_cong γ hγ) (diagT k (Fin N))
    (N := unipB k (Fin N)) (fun _ => leviEmb_mem_normalizer k (points (Fin N)) _)
    ((GlobalTheory.CentralExponent.cong (Fin N) γ hγ).comap (diagT k (Fin N)))
    (fun _ h => h) (GlobalTheory.SmGL.IwahoriOnto.lowerInt k (Fin N))
    (fun g hg => by
      obtain ⟨d, hd, x, hx, c, hc, e⟩ := UpperTheory.congruence_subgroup_eq_diagonal_unipotent_lower_iwahori k N γ hγ g hg
      exact ⟨d, (hmem d).2 hd, x, hx, c, hc, e⟩)
    (GlobalTheory.SmGL.IwahoriOnto.lowerInt_contract k (Fin N)) y
    (fun d => by
      have := hy d ((hmem d).1 d.2)
      rw [MonoidHom.one_apply, Units.val_one, one_smul]
      exact this)
  rw [hbot, Submodule.mem_bot] at hv
  exact hy0 (by rw [← e, hv, map_zero])
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalCrystallineOfInduced
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

theorem UpperTheory.local_crystalline_of_induced :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] (σ : ↥(Weil h)), deg σ = -1 → ∀ (x : V ⊗[ℚ_[l]] P.R.B) (y : ↥(Dpst P ρ)), x ∈ Dcris (P.PD Bw.Kw) ρ → (y : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V x → ((weilD Bw h P ρ σ y : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V (((φVB (P.PD Bw.Kw) (LL := ↥LL.1) (V := V) : Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.B)) ^ resDeg l w) x) := by
  intro l _ P E Ω _ _ _ _ _ A w O _ _ _ Bw h hj LL V _ _ _ _ _ ρ _ σ hσ x y hx hy
  have hφ : ∀ z : V ⊗[ℚ_[l]] P.R.B, phiV P ↥LL.1 V (crisIncl P ↥LL.1 V z) =
      crisIncl P ↥LL.1 V (φVB (P.PD Bw.Kw) (LL := ↥LL.1) (V := V) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [φVB, P.PD_φ]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hpow : ∀ n : ℕ, (((phiD P ρ ^ n) y : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) =
      crisIncl P ↥LL.1 V (((φVB (P.PD Bw.Kw) (LL := ↥LL.1) (V := V) :
        Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.B)) ^ n) x) := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih => rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply, coe_phiD, ih, hφ]
  have hfix : actD P ρ (weilToGK Bw h σ) y = y := by
    refine Subtype.ext ?_
    rw [coe_actD, hy, stRep_crisIncl]
    congr 1
    have h1 := (Submodule.mem_iInf _).mp hx (weilToGK Bw h σ)
    simpa [sub_eq_zero] using h1
  have ha : -GlobalTheory.Pst.alpha l σ = ((resDeg l w : ℕ) : ℤ) := by simp [GlobalTheory.Pst.alpha, hσ]
  rw [weilD_apply, (commute_actD_phiU P ρ _ _).eq, End.mul_apply, hfix, ha, zpow_natCast,
    Units.val_pow_eq_pow_val, coe_phiU, hpow]
end

