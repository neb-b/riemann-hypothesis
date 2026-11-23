module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNondegenerateRightInvariantFormOfCompactQu
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0062
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0042
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.EqOnTors
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.HeckePolCoeff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.TypeConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.TypeLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PiFamilyProdHomBijectiveCharacterization
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ExistsIrreducibleTypeCharacters

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DecompU
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

open GlobalTheory.DefU in
private theorem autProj (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (M : Submodule ℂ (autU E n))
    (hM : FiniteDimensional ℂ M) :
    ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Submodule ℂ (UA E n → ℂ)) (P : κ → autU E n →ₗ[ℂ] autU E n),
      (∀ i, IsAutRepU (σ i)) ∧ (∀ i φ, (P i φ).1 ∈ σ i) ∧ (∀ i x φ, P i (autRep E n x φ) = autRep E n x (P i φ)) ∧
      ∀ φ ∈ M, ∑ i, P i φ = φ := by
  obtain ⟨h1, h2, h3, h4⟩ := UpperTheory.unitary_adelic_t2_locallyCompact_secondCountable E n
  obtain ⟨C, hC, hcov⟩ := UpperTheory.exists_compact_fundamental_set_unitary E n
  obtain ⟨B, hdef, hinv⟩ := UpperTheory.exists_nondegenerate_right_invariant_form_of_compact_quotient (UA E n) (ratU E n) C hC hcov
  have hsum := UpperTheory.mem_iSup_automorphicReps_of_invariant_form E n B (fun φ h => hdef φ h.cont h.left)
    (fun x φ ψ h h' => hinv x φ ψ h.cont h.left h'.cont h'.left)
  have hi := Submodule.map_injective_of_injective (autU E n).injective_subtype
  obtain ⟨κ, _, U, P, hU, hP, hPe, hPs⟩ := UpperTheory.exists_equivariant_projections_of_sum_irreducible (UA E n) (autU E n) (autRep E n) (fun x => by
    have key : ∀ (Z : Submodule ℂ (autU E n)), (∀ σ, IsAutRepU σ → σ.comap (autU E n).subtype ≤ Z) → x ∈ Z := by
      intro Z hZ
      have hle : (⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1) ≤ Z.map (autU E n).subtype :=
        iSup_le fun σ φ hφ => ⟨⟨φ, σ.2.aut φ hφ⟩, hZ σ.1 σ.2 hφ, rfl⟩
      obtain ⟨y, hy, e⟩ := hle (hsum x.1 x.2)
      exact Subtype.ext e ▸ hy
    refine key _ fun σ hσ => ?_
    have hm : (σ.comap (autU E n).subtype).map (autU E n).subtype = σ := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 hσ.aut
    refine le_iSup_of_le ⟨σ.comap (autU E n).subtype, fun h => hσ.ne_bot ?_, fun g u hu => hσ.stable g u.1 hu,
      fun N hN hst => ?_⟩ le_rfl
    · rw [← hm, h, Submodule.map_bot]
    · refine (hσ.irred (N.map (autU E n).subtype) (hm ▸ Submodule.map_mono hN) ?_).imp
        (fun h => hi (h.trans (Submodule.map_bot _).symm)) fun h => hi (h.trans hm.symm)
      rintro g _ ⟨u, hu, rfl⟩
      exact ⟨_, hst g u hu, rfl⟩) M hM
  refine ⟨κ, inferInstance, fun i => (U i).map (autU E n).subtype, P, fun i => ⟨?_, ?_, ?_, fun N hN hst => ?_⟩,
    fun i φ => ⟨_, hP i φ, rfl⟩, hPe, hPs⟩
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · rintro g _ ⟨u, hu, rfl⟩
    exact ⟨_, (hU i).2.1 g u hu, rfl⟩
  · exact fun h => (hU i).1 (hi (h.trans (Submodule.map_bot _).symm))
  · have hm : (N.comap (autU E n).subtype).map (autU E n).subtype = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hN.trans (Submodule.map_subtype_le _ _))
    rcases (hU i).2.2 (N.comap (autU E n).subtype) (fun u hu => by
      obtain ⟨w, hw, e⟩ := hN hu
      exact Subtype.ext e ▸ hw) (fun g u hu => hst g u.1 hu) with h | h
    · left; rw [← hm, h, Submodule.map_bot]
    · right; rw [← hm, h]

open GlobalTheory.DefU in
private theorem core {E : Type} [Field E] [NumberField E] [IsCMField E] {n m : ℕ} {Y D I : Type} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D] (A : Submodule ℂ Y) (tf : Y →ₗ[ℂ] D →ₗ[ℂ] (UA E n → ℂ))
    (r : UA E n → D → D) (hinj : ∀ F ∈ A, (∀ ℓ, tf F ℓ = 0) → F = 0)
    (hsur : ∀ Φ : D →ₗ[ℂ] (UA E n → ℂ), (∀ ℓ, IsAutFormU (Φ ℓ)) → (∀ ℓ, ∀ x ∈ infU E n, RU E n x (Φ ℓ) = Φ (r x ℓ)) →
      ∃ F ∈ A, ∀ ℓ, tf F ℓ = Φ ℓ)
    (T : I → Y → Y) (k : I → UA E n) (a : I → Fin m → Fin m → ℂ) (hTA : ∀ u, ∀ F ∈ A, T u F ∈ A)
    (hT : ∀ u F ℓ, tf (T u F) ℓ = RU E n (k u) (tf F ℓ)) (F : Fin m → Y) (hFA : ∀ i, F i ∈ A)
    (haut : ∀ i ℓ, IsAutFormU (tf (F i) ℓ)) (heq : ∀ i ℓ, ∀ x ∈ infU E n, RU E n x (tf (F i) ℓ) = tf (F i) (r x ℓ))
    (hF : ∀ u i, ∑ j, a u i j • T u (F j) = F i) :
    ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Submodule ℂ (UA E n → ℂ)) (G : κ → Fin m → Y),
      (∀ t, IsAutRepU (σ t)) ∧ (∀ t i, G t i ∈ A) ∧ (∀ t i ℓ, tf (G t i) ℓ ∈ σ t) ∧
      (∀ t u i, ∑ j, a u i j • T u (G t j) = G t i) ∧ ∑ t, G t = F := by
  let Φ : Fin m → D →ₗ[ℂ] autU E n := fun i => (tf (F i)).codRestrict (autU E n) (haut i)
  obtain ⟨κ, _, σ, P, hσ, hP, hPe, hPs⟩ := autProj E n (⨆ i, LinearMap.range (Φ i)) inferInstance
  have hex : ∀ t i, ∃ G ∈ A, ∀ ℓ, tf G ℓ = (P t (Φ i ℓ)).1 := fun t i =>
    hsur ((autU E n).subtype ∘ₗ P t ∘ₗ Φ i) (fun ℓ => (P t (Φ i ℓ)).2) fun ℓ x hx => by
      have e : autRep E n x (Φ i ℓ) = Φ i (r x ℓ) := Subtype.ext (heq i ℓ x hx)
      exact (congrArg Subtype.val (hPe t x (Φ i ℓ))).symm.trans (by rw [e]; rfl)
  choose G hGA hG using hex
  refine ⟨κ, inferInstance, σ, G, hσ, hGA, fun t i ℓ => hG t i ℓ ▸ hP t _, fun t u i => ?_, funext fun i => ?_⟩
  · refine sub_eq_zero.1 (hinj _ (sub_mem (Submodule.sum_mem _ fun j _ => A.smul_mem _ (hTA u _ (hGA t j))) (hGA t i))
      fun ℓ => ?_)
    have e : ∑ j, a u i j • autRep E n (k u) (Φ j ℓ) = Φ i ℓ := by
      apply Subtype.ext
      have := congrArg (fun y => tf y ℓ) (hF u i)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hT] at this
      rw [Submodule.coe_sum]
      exact this
    have e2 := congrArg (fun y => (P t y).1) e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hPe, Submodule.coe_sum] at e2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, hT, hG]
    exact sub_eq_zero.2 e2
  · rw [Finset.sum_apply]
    refine sub_eq_zero.1 (hinj _ (sub_mem (Submodule.sum_mem _ fun t _ => hGA t i) (hFA i)) fun ℓ => ?_)
    have e := congrArg Subtype.val (hPs (Φ i ℓ) (Submodule.mem_iSup_of_mem i ⟨ℓ, rfl⟩))
    rw [Submodule.coe_sum] at e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, hG]
    exact sub_eq_zero.2 e

private theorem core2 {E : Type} [Field E] [NumberField E] [IsCMField E] {n m d : ℕ} {Γ Ga Gp D : Type} [Group Γ] [Group Ga]
    [Group Gp] [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D] (X : Frame Γ Ga Gp) (ξ : Gp →* GL (Fin d) ℂ)
    (τ : X.Ub →* GL (Fin m) ℂ) (U₀ U : Subgroup X.Ub) (I : Subgroup Gp) (J : UA E n →* Ga × Gp)
    (tf : (Ga × Gp → Fin d → ℂ) →ₗ[ℂ] D →ₗ[ℂ] (UA E n → ℂ)) (r : UA E n → D → D)
    (hJinf : ∀ x ∈ infU E n, J x = 1) (hRfin : ∀ k ∈ finU (E := E) (n := n), ∀ ℓ, r k ℓ = ℓ)
    (hinj : ∀ F ∈ X.AF ξ, (∀ ℓ, tf F ℓ = 0) → F = 0)
    (haut : ∀ F ∈ X.AF ξ, IsOpen {k : finU (E := E) (n := n) | ∀ g, F (g * J k) = F g} → ∀ ℓ, IsAutFormU (tf F ℓ))
    (htr : ∀ F ℓ x, RU E n x (tf F ℓ) = tf (fun g => F (g * J x)) (r x ℓ))
    (hsurj : Function.Surjective fun k : finU (E := E) (n := n) => J k)
    (hsur : ∀ Φ : D →ₗ[ℂ] (UA E n → ℂ), (∀ ℓ, IsAutFormU (Φ ℓ)) → (∀ ℓ, ∀ x ∈ infU E n, RU E n x (Φ ℓ) = Φ (r x ℓ)) →
      ∃ F ∈ X.AF ξ, ∀ ℓ, tf F ℓ = Φ ℓ)
    (hev : ∀ᶠ k : finU (E := E) (n := n) in nhds 1, (∃ u ∈ U, (u : Ga) = (J k).1 ∧ τ u = 1) ∧ (J k).2 ∈ I)
    (F : Fin m → X.Fn ℂ d) (hF : F ∈ Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U₀)
    (hK : F ∈ fixd (X.raF d τ) U) (hb : F ∈ fixd (X.rpF ℂ d m) I) :
    F ∈ ⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ},
      (Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U₀) ⊓ Submodule.span ℂ {F | ∀ i ℓ, tf (F i) ℓ ∈ σ.1} := by
  have hra : ∀ (u : X.Ub) (G : Fin m → Ga × Gp → Fin d → ℂ) (i : Fin m),
      X.raF d τ u G i = ∑ j, (τ u).val i j • fun g => G j (g * ((u : Ga), 1)) := fun u G i => by
    funext g t
    rw [Finset.sum_apply, Finset.sum_apply]
    rfl
  have hFA : ∀ i, F i ∈ X.AF ξ := fun i => hF.1 i trivial
  have hopen : ∀ i, IsOpen {k : finU (E := E) (n := n) | ∀ g, F i (g * J k) = F i g} := fun i => by
    let S : Subgroup (finU (E := E) (n := n)) :=
      { carrier := {k | ∀ g, F i (g * J k) = F i g}
        one_mem' := fun g => by rw [OneMemClass.coe_one, map_one, mul_one]
        mul_mem' := fun {x y} hx hy g => by rw [Subgroup.coe_mul, map_mul, ← mul_assoc, hy, hx]
        inv_mem' := fun {x} hx g => by rw [← hx, Subgroup.coe_inv, map_inv, inv_mul_cancel_right] }
    refine S.isOpen_of_mem_nhds (g := 1) ?_
    filter_upwards [hev] with k ⟨⟨u, hu, huk, h1⟩, hk⟩ g
    have h2 := (hra u F i).symm.trans (congrFun (hK u hu) i)
    rw [h1] at h2
    have h3 : ∀ g, F i (g * ((u : Ga), 1)) = F i g := fun g => by
      have h4 := congrFun h2 g
      rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj => by
        rw [Units.val_one, Matrix.one_apply_ne hj.symm, zero_smul]; rfl) (fun h => (h (Finset.mem_univ _)).elim),
        Units.val_one, Matrix.one_apply_eq, one_smul] at h4
      exact h4
    have h5 : ∀ g, F i (g * (1, (J k).2)) = F i g := fun g => congrFun (congrFun (hb _ hk) i) g
    have h6 : J k = ((u : Ga), 1) * (1, (J k).2) := Prod.ext (huk.symm.trans (mul_one _).symm) (one_mul _).symm
    rw [h6, ← mul_assoc, h5, h3]
  choose k hk using fun u : U₀ => hsurj (((u : X.Ub) : Ga), 1)
  obtain ⟨κ, _, σ, G, hσ, hGA, hG, hGu, hsum⟩ := core (X.AF ξ) tf r hinj hsur
    (fun (u : U₀) G g => G (g * (((u : X.Ub) : Ga), 1))) (fun u => (k u : UA E n)) (fun u => (τ u.1).val)
    (fun u G hG γ g => by
      have := hG γ (g * (((u : X.Ub) : Ga), 1))
      rw [← mul_assoc] at this
      exact this)
    (fun u G ℓ => by
      have h1 := htr G ℓ (k u)
      rw [hRfin _ (k u).2, show J (k u) = _ from hk u] at h1
      exact h1.symm)
    F hFA (fun i => haut (F i) (hFA i) (hopen i))
    (fun i ℓ x hx => by
      have h1 := htr (F i) ℓ x
      simp only [hJinf x hx, mul_one] at h1
      exact h1)
    (fun u i => (hra u.1 F i).symm.trans (congrFun (hF.2 u.1 u.2) i))
  rw [← hsum]
  refine Submodule.sum_mem _ fun t _ => Submodule.mem_iSup_of_mem ⟨σ t, hσ t⟩ ⟨⟨fun i _ => hGA t i, fun u hu => ?_⟩,
    Submodule.subset_span (hG t)⟩
  exact funext fun i => (hra u (G t) i).trans (hGu t ⟨u, hu⟩ i)

theorem UpperTheory.V.Hi.decompU :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), ∀ ι : Qbar l ≃+* ℂ, IsOpen (τ₀.ker : Set (KT n (wt s))) → ∀ (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ F ∈ (hset Q τ₀).Big ι ξ, (∃ K, F ∈ fixd ((hset Q τ₀).X.raF d ((hset Q τ₀).τC ι)) ((hset Q τ₀).lev K)) → (∃ b, F ∈ fixd ((hset Q τ₀).X.rpF ℂ d m) ((hset Q τ₀).X.I.I1 b)) → F ∈ ⨆ σ : {σ : Submodule ℂ (UA L n → ℂ) // IsAutRepU σ}, YOf Q ι τ₀ e ξ σ.1 := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ ι hτ lam d e ξ hξ F hF ⟨K, hK⟩ ⟨b, hb⟩
  let J : UA L n →* Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) :=
    MonoidHom.prod (away l L n).rangeRestrict (Pi.monoidHom fun v : V.frame.Vl => cLoc (s.w v.1))
  obtain ⟨hinj, haut, htr, hsurj, hsur⟩ := UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ J (fun _ => rfl)
  haveI := e.finiteDimensional
  let tf : (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ]
      Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
    LinearMap.mk₂ ℂ (toForm ι e)
      (fun F F' ℓ => funext fun g => by simp only [toForm, Pi.add_apply, map_add (f := _)])
      (fun a F ℓ => funext fun g => by simp only [toForm, Pi.smul_apply, map_smul])
      (fun F ℓ ℓ' => funext fun g => by simp only [toForm, Pi.add_apply, LinearMap.add_apply])
      (fun a F ℓ => funext fun g => by simp only [toForm, Pi.smul_apply, LinearMap.smul_apply])
  have hJinf : ∀ x ∈ infU L n, J x = 1 := fun x hx => by
    have h1 : ∀ w, cLoc w x = 1 := fun w => by
      have h2 : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := hx
      change Matrix.GeneralLinearGroup.map (pLoc L w) (Matrix.GeneralLinearGroup.map (pFin L) x.1) = 1
      rw [h2, map_one]
    exact Prod.ext (Subtype.ext (funext fun w => h1 _)) (funext fun v => h1 _)
  have hRfin : ∀ k ∈ finU (E := L) (n := n), infRep (V := V) ι lam k = 1 := fun k hk => by
    have h1 : ∀ τ, cEmb τ k = 1 := fun τ => by
      change Matrix.GeneralLinearGroup.map (coord τ) (cInf k) = 1
      rw [MonoidHom.mem_ker.1 hk, map_one]
    have h2 : (Pi.monoidHom fun e : Emb l (fun v : V.frame.Vl => s.w v.1) =>
        (GlobalTheory.Branching.sqRep ℂ n (lam e.res)).comp (cEmb (E := L) (n := n) (ι.toRingHom.comp e.res))) k = 1 :=
      funext fun y => by
        change GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb _ k) = 1
        rw [h1, map_one]
    unfold infRep
    rw [MonoidHom.comp_apply, h2, map_one]
  refine core2 (hset Q τ₀).X ξ ((hset Q τ₀).τC ι) (hset Q τ₀).UQ ((hset Q τ₀).lev K) ((hset Q τ₀).X.I.I1 b) J tf
    (fun x ℓ => ℓ ∘ₗ infRep ι lam x⁻¹) hJinf (fun k hk ℓ => ?_) hinj haut htr hsurj hsur ?_ F hF hK hb
  · rw [hRfin _ ((finU (E := L) (n := n)).inv_mem hk)]
    rfl
  · filter_upwards [UpperTheory.eventually_mem_heckeLevel_and_iwahoriCongruence l L Ω s n hn V Q c m τ₀ hτ K b] with k ⟨⟨u, hu, huk, hu1⟩, hk⟩
    refine ⟨⟨u, hu, huk, ?_⟩, hk⟩
    change Matrix.GeneralLinearGroup.map _ (τ₀ (toKT n s u)) = 1
    rw [hu1, map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2BaseEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem cu_ext {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) [IsHausdorff I R] {S : Set Γ}
    (hS : Dense S) {f g : Γ → R} (hf : Alg.AdicCont I f) (hg : Alg.AdicCont I g) (h : ∀ x ∈ S, f x = g x) : f = g := by
  funext x
  refine IsHausdorff.eq_iff_smodEq (I := I).2 fun N => ?_
  rw [smul_eq_mul, Ideal.mul_top]
  letI : TopologicalSpace (R ⧸ I ^ N) := ⊥
  haveI : DiscreteTopology (R ⧸ I ^ N) := ⟨rfl⟩
  exact congrFun (Continuous.ext_on hS (hf N).continuous (hg N).continuous fun y hy => by simp only [h y hy]) x

private theorem cu_prod {n : ℕ} {M : Type} [CommGroup M] (f g : Fin n → M)
    (h : ∀ j, ∏ i with i ≤ j, f i = ∏ i with i ≤ j, g i) : ∀ j, f j = g j := by
  intro j
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have hj : j ∈ Finset.univ.filter fun i => i ≤ j := by simp
    have e := h j
    rw [← Finset.mul_prod_erase _ _ hj, ← Finset.mul_prod_erase _ g hj,
      Finset.prod_congr rfl (g := g) fun i hi => ih i (by
        rw [Finset.mem_erase, Finset.mem_filter] at hi
        exact lt_of_le_of_ne hi.2.2 hi.1)] at e
    exact mul_right_cancel e

private theorem cu_gen {W M k : Type} [Group W] [Group M] [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a : W →* kˣ) (ha : Function.Surjective a) (f g : W →* M)
    (h1 : ∀ s (y : Uo k), a s = y → f s = g s) (h2 : ∀ s, a s = Hi.unif k → f s = g s) (s : W) : f s = g s := by
  obtain ⟨p, hp⟩ := ha (Hi.unif k)
  have e := h1 (s * (p ^ ord k (a s))⁻¹) ⟨_, GlAx.val_div_ord (a s)⟩ (by
    rw [map_mul, map_inv, map_zpow, hp]
    exact (div_eq_mul_inv _ _).symm)
  rw [map_mul, map_mul, map_inv, map_inv, map_zpow, map_zpow, h2 p hp] at e
  exact mul_right_cancel e

private theorem push_cont {Γ O T T₀ : Type} [TopologicalSpace Γ] [CommRing O] [IsLocalRing O] [CommRing T] [Algebra O T]
    [Alg.IsCO O T] [CommRing T₀] [Algebra O T₀] [Alg.IsCO O T₀] (φ : T →ₐ[O] T₀) {f : Γ → T}
    (hf : Alg.AdicCont (maximalIdeal T) f) : Alg.AdicCont (maximalIdeal T₀) fun g => φ (f g) := fun N => by
  have hle : maximalIdeal T ^ N ≤ (maximalIdeal T₀ ^ N).comap (φ : T →+* T₀) := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show φ y ∈ maximalIdeal T₀
    rw [← Alg.res_eq_zero_iff O, Alg.res_map, Alg.res_eq_zero_iff]
    exact hy
  exact (hf N).comp (Ideal.quotientMap _ (φ : T →+* T₀) hle)

private theorem abs_det {n : ℕ} {G G₀ O T T₀ : Type} [Group G] [TopologicalSpace G] [Group G₀] [TopologicalSpace G₀]
    [CommRing O] [IsLocalRing O] [CommRing T] [Algebra O T] [Alg.IsCO O T] [CommRing T₀] [Algebra O T₀] [Alg.IsCO O T₀]
    (φ : T →ₐ[O] T₀) (p : G →* G₀) (hp : Continuous p) (D : W.GDet n T G) (D₀ : W.GDet n T₀ G₀)
    (hD : D.IsCont (maximalIdeal T)) (hD₀ : D₀.IsCont (maximalIdeal T₀)) {S : Set G} (hS : Dense S)
    (h : ∀ g ∈ S, (D.chi (MonoidAlgebra.single g 1)).map φ.toRingHom = D₀.chi (MonoidAlgebra.single (p g) 1)) :
    D.map φ.toRingHom = D₀.comap p := by
  have e : ∀ g, (D.map φ.toRingHom).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map φ.toRingHom :=
    fun g => by
      rw [← (AlgebraTools.Det.mapApi D _).1]
      simp
  refine UpperTheory.V.CA.d_gext _ _ fun g i _ _ => ?_
  have h1 := congrFun (cu_ext _ hS (push_cont φ (hD i)) (fun N => (hD₀ i N).comp_continuous hp) fun g hg => by
    simp only [W.GDet.lam, ← h g hg, coeff_map, map_mul, map_pow, map_neg, map_one]
    rfl) g
  simp only [W.GDet.lam, map_mul, map_pow, map_neg, map_one] at h1
  simp only [W.GDet.lam, e, LvR.chi_comap, coeff_map]
  exact h1

private theorem abs_chr {n : ℕ} {Wl Dc O T T₀ k : Type} [Group Wl] [Group Dc] [TopologicalSpace Dc] [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [CommRing O] [IsLocalRing O] [CommRing T] [Algebra O T] [Alg.IsCO O T] [CommRing T₀] [Algebra O T₀] [Alg.IsCO O T₀]
    (φ : T →ₐ[O] T₀) (inc : Wl →* Dc) (hd : DenseRange inc) (art : Wl →* kˣ) (ha : Function.Surjective art)
    (ψ : Fin n → Dc →* Tˣ) (ψ₀ : Fin n → Dc →* T₀ˣ) (c1 : ∀ i, Alg.AdicCont (maximalIdeal T) fun g => (ψ i g : T))
    (c0 : ∀ i, Alg.AdicCont (maximalIdeal T₀) fun g => (ψ₀ i g : T₀)) (ε : Dc → Tˣ) (ε₀ : Dc → T₀ˣ)
    (hε : ∀ g, φ (ε g) = ε₀ g) (u : Fin n → Uo k → T) (u₀ : Fin n → Uo k → T₀) (hu : ∀ i y, φ (u i y) = u₀ i y)
    (γ : Fin n → T) (γ₀ : Fin n → T₀) (hγ : ∀ i, φ (γ i) = γ₀ i)
    (a1 : ∀ i s (y : Uo k), art s = y → (ψ i (inc s) * ε (inc s) ^ (i : ℕ) : Tˣ) * u i y = 1)
    (a0 : ∀ i s (y : Uo k), art s = y → (ψ₀ i (inc s) * ε₀ (inc s) ^ (i : ℕ) : T₀ˣ) * u₀ i y = 1)
    (b1 : ∀ j s, art s = Hi.unif k → ((∏ i with i ≤ j, ψ i (inc s) * ε (inc s) ^ (i : ℕ) : Tˣ) : T) = γ j)
    (b0 : ∀ j s, art s = Hi.unif k → ((∏ i with i ≤ j, ψ₀ i (inc s) * ε₀ (inc s) ^ (i : ℕ) : T₀ˣ) : T₀) = γ₀ j) (i : Fin n) :
    W.pushCh φ.toRingHom (ψ i) = ψ₀ i := by
  have hm : ∀ i g, φ ((ψ i g * ε g ^ (i : ℕ) : Tˣ) : T) = ((W.pushCh φ.toRingHom (ψ i) g * ε₀ g ^ (i : ℕ) : T₀ˣ) : T₀) :=
    fun i g => by
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hε]
      rfl
  refine MonoidHom.ext fun g => Units.ext (congrFun (cu_ext _ hd (push_cont φ (c1 i)) (c0 i) ?_) g)
  rintro _ ⟨s, rfl⟩
  refine congrArg Units.val (cu_gen art ha ((W.pushCh φ.toRingHom (ψ i)).comp inc) ((ψ₀ i).comp inc)
    (fun s y hy => ?_) (fun s hs => ?_) s)
  · have e := congrArg φ (a1 i s y hy)
    rw [map_mul, hm, hu, map_one] at e
    have e' := a0 i s y hy
    exact mul_right_cancel (inv_injective (Units.ext
      ((Units.eq_inv_of_mul_eq_one_left e).symm.trans (Units.eq_inv_of_mul_eq_one_left e'))))
  · refine mul_right_cancel (cu_prod (fun i => W.pushCh φ.toRingHom (ψ i) (inc s) * ε₀ (inc s) ^ (i : ℕ))
      (fun i => ψ₀ i (inc s) * ε₀ (inc s) ^ (i : ℕ)) (fun j => Units.ext ?_) i)
    have e := congrArg φ (b1 j s hs)
    rw [Units.coe_prod, map_prod, hγ] at e
    rw [b0 j s hs, ← e, Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => (hm i _).symm

private theorem heckePol_map' {T T₀ : Type} [CommRing T] [CommRing T₀] (f : T →+* T₀) (n q : ℕ) (g : ℕ → T) :
    (heckePol n q g).map f = heckePol n q fun j => f (g j) := JEx.heckePol_map _ _ _ _

set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Hi.levelUR2BaseEq :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V₀ V : s.Lev) (Q₀ : QData V₀) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q₀ τ₀).X.I.T →* Aˣ), (hset Q₀ τ₀).IsWt θ → ∀ (a : (hset Q₀ τ₀).Op → c.O) (K₀ : (hset Q₀ τ₀).Lev) (K : (hset Q τ₀).Lev), ∀ (p : V.frame.G₀ →* V₀.frame.G₀), Continuous p → Function.Surjective p → (∀ g, p (V.pr g) = V₀.pr g) → ∀ j : (hset Q τ₀).Op → (hset Q₀ τ₀).Op, (∀ x : Vl l L × Fin n, j (.inr x) = .inr x) → (∀ (w : (hset Q τ₀).Wp) (k : Fin n), ∃ hw, j (.inl (w, k)) = .inl (⟨w.1, hw⟩, k)) → ∀ (θ' : (hset Q τ₀).X.I.T →* Aˣ) (a' : (hset Q τ₀).Op → c.O), (hset Q τ₀).IsWt θ' → @Eq ((hset Q τ₀).X.I.T →* Aˣ) θ' θ → (∀ i, a' i = a (j i)) → ∀ [Fact (CommOn ((hset Q₀ τ₀).MK θ a K₀) ((hset Q₀ τ₀).op A))] [Alg.IsCO c.O ((hset Q₀ τ₀).TK θ a K₀)] [Fact (CommOn ((hset Q τ₀).MK θ' a' K) ((hset Q τ₀).op A))] [Alg.IsCO c.O ((hset Q τ₀).TK θ' a' K)] (D₀ : W.GDet n ((hset Q₀ τ₀).TK θ a K₀) V₀.frame.G₀) (ψ₀ : ∀ v : Vl l L, Fin n → Dec (F := L) (s.A v.1) →* ((hset Q₀ τ₀).TK θ a K₀)ˣ), (hset Q₀ τ₀).IsUniv θ a K₀ (maximalIdeal _) D₀ ψ₀ → ∀ (D : W.GDet n ((hset Q τ₀).TK θ' a' K) V.frame.G₀) (ψ : ∀ v : Vl l L, Fin n → Dec (F := L) (s.A v.1) →* ((hset Q τ₀).TK θ' a' K)ˣ), (hset Q τ₀).IsUniv θ' a' K (maximalIdeal _) D ψ → ∀ φ : (hset Q τ₀).TK θ' a' K →ₐ[A] (hset Q₀ τ₀).TK θ a K₀, (∀ i, φ ((hset Q τ₀).gen θ' a' K i) = (hset Q₀ τ₀).gen θ a K₀ (j i)) → D.map φ.toRingHom = D₀.comap p ∧ ∀ v i, W.pushCh φ.toRingHom (ψ v i) = ψ₀ v i := by
  intro hN l _ L Ω _ _ _ _ _ _ s n hn V₀ V Q₀ Q c m τ₀ A _ _ _ θ _ a K₀ K p hp _ hpr j hj hjw θ' a' _ hθ _ _ _ _ _ D₀ ψ₀ hU₀ D ψ hU φ hφ
  have hAx := axU hN l L Ω s n hn V Q c m τ₀
  refine ⟨abs_det (φ.restrictScalars c.O) p hp D D₀ hU.cont hU₀.cont hAx.dense ?_, fun v i => ?_⟩
  · rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    obtain ⟨hw₀, -⟩ := hjw ⟨w, hw⟩ ⟨0, hn⟩
    have e1 := hU.frob ⟨w, hw⟩ B σ hB hσ
    have e0 := hU₀.frob ⟨w, hw₀⟩ B σ hB hσ
    refine ((congrArg (Polynomial.map _) e1).trans ((heckePol_map' _ _ _ _).trans ?_)).trans
      (e0.symm.trans (congrArg (fun g => D₀.chi (MonoidAlgebra.single g 1)) (hpr σ⁻¹).symm))
    refine congrArg (heckePol n (normV w)) (funext fun k => ?_)
    unfold HSet.genW
    split_ifs with h
    · obtain ⟨_, e⟩ := hjw ⟨w, hw⟩ ⟨k - 1, h.2⟩
      exact (hφ _).trans (congrArg ((hset Q₀ τ₀).gen θ a K₀) e)
    · exact map_one _
  · exact abs_chr (k := ((hset Q τ₀).Sl v).adicCompletion L) (φ.restrictScalars c.O) (Subgroup.inclusion (Weil_le_Dec (s.hw v.1))) (UpperTheory.weil_group_dense_in_galois_group L Ω _ _ (s.hw v.1))
      ((hset Q τ₀).art v) (hAx.art_spec v).surj (ψ v) (ψ₀ v) (hU.ψ_cont v) (hU₀.ψ_cont v)
      ((hset Q τ₀).epsV _ v) ((hset Q₀ τ₀).epsV _ v) (fun g => (φ.restrictScalars c.O).commutes _)
      (fun i y => algebraMap A _ (θ' (eV n (hset Q τ₀).Sl v i y))) (fun i y => algebraMap A _ (θ (eV n (hset Q₀ τ₀).Sl v i y)))
      (fun i y => (φ.commutes _).trans (congrArg (fun u : Aˣ => algebraMap A _ (u : A))
        (congrArg (fun t : (hset Q τ₀).X.I.T →* Aˣ => t (eV n (hset Q τ₀).Sl v i y)) hθ)))
      _ _ (fun k => (hφ _).trans (congrArg ((hset Q₀ τ₀).gen θ a K₀) (hj (v, k))))
      (fun i x y h => hU.ψ_unit v i x _ y rfl h) (fun i x y h => hU₀.ψ_unit v i x _ y rfl h)
      (fun k x h => hU.ψ_unif v k x _ rfl h) (fun k x h => hU₀.ψ_unif v k x _ rfl h) i
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.TypeEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.typeEx :
    Af.HypothesesH → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∃ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), TypeFor r ι τ₀ :=
  fun P => UpperTheory.NonzeroTypeTheory.exists_type_for_residual_rep P.litN
end

