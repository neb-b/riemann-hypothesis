module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.ProjectionComponents.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.LevUnion
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.LocSubD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ROrdAway
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.OrdPlain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0242

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.MemLevelOfLocalDepth
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem compD :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ n : ℕ, 1 ≤ n → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π → ∀ w, IsSplitAt w → ∀ W : Sig.Lev (Kw w),
                 ∀ φ : UA L n → V, φ ≠ 0 → CoefIn φ π → (∀ x ∈ locU n w, cLoc w x ∈ W.J n → ∀ g, φ (g * x) = φ g) →
                 ∀ ψ : Fin n → (Kw w)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) → EigT φ w W ψ → CompSub π w ψ := by
  intro H L _ _ _ unr n hn V _ _ π hπ w hw W φ h0 hc hJ ψ hψ he
  obtain ⟨s1, s2, -⟩ := secSpec L n w hw
  obtain ⟨τ, hτ⟩ := compEx H L unr n hn π hπ w hw
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[ℂ] ℂ, f ∘ φ ≠ 0 := by
    obtain ⟨g, hg⟩ := Function.ne_iff.1 h0
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ hg
    exact ⟨f, Function.ne_iff.2 ⟨g, hf⟩⟩
  obtain ⟨p, hp, hp0⟩ := (isoCopy _ _ _ τ.ρ _ τ.irred (isoTypic L n π hπ w hw τ hτ)).1 ⟨f ∘ φ, hc f⟩ fun h => hf (congrArg Subtype.val h)
  refine ⟨hψ, τ, hτ, UpperTheory.V.Z.Sym.W.locSubD H _ n W ψ hψ _ τ.ρ τ.smooth τ.irred _ hp0 (fun u hu => ?_) fun d hd => ?_⟩
  · rw [← hp]
    congr 1
    exact Subtype.ext (funext fun g => congrArg f (hJ _ (s1 u) (by rwa [s2]) g))
  · rw [← dcMap W _ τ.ρ p hp, ← map_smul]
    congr 1
    apply Subtype.ext
    have a := dcMap W ((repOn hπ).comp (secW n w)) ((RU L n).comp (secW n w)) π.subtype (fun _ _ => rfl) (Sig.dg d) ⟨f ∘ φ, hc f⟩
    have b := dcMap W ((rightReg ℂ (UA L n) V).comp (secW n w)) ((RU L n).comp (secW n w)) (f.compLeft (UA L n))
      (fun _ _ => rfl) (Sig.dg d) φ
    rw [show UpperTheory.V.Hi.dc _ _ _ _ φ = _ • φ from he d hd, map_smul] at b
    exact a.trans b.symm

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

private theorem mem_level_of_local_depth {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {S₀ S : Finset (Plc L)} {c : ℕ}
    (hS : Places ((S₀ : Set (Plc L)) ∪ S)) (hd : Disjoint S₀ S) {w : Plc L} (hw : w ∈ S₀) {x : UA L n}
    (hx : x ∈ locU n w) (hJ : cLoc w x ∈ (deep c w).J n) : x ∈ lev (lev (Kall L n) S₀ (deep c)) S iw := by
  have hk : x ∈ Kall L n := by
    refine ((factor L n w).2.2.2.2.1 x hx).2 ?_
    rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL]
    exact ((Sig.finFacts _ (deep c w)).2.2.2.2.2 n).2.2.2 hJ
  have key : ∀ w' ∈ (S₀ : Set (Plc L)) ∪ S, w' ≠ w → cLoc w' x = 1 := fun w' hw' e => by
    have hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L)) := fun h => e (hS.inj hw' (Or.inl hw) h.symm)
    have := (factor L n w').2.2.1 w hne hx
    simp only [away, Subgroup.mem_iInf] at this
    exact MonoidHom.mem_ker.1 (this w' rfl)
  simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine ⟨⟨hk, fun w' hw' => ?_⟩, fun w' hw' => ?_⟩
  · by_cases e : w' = w
    · subst e; exact hJ
    · rw [Subgroup.mem_comap, key w' (Or.inl hw') e]
      exact one_mem _
  · rw [Subgroup.mem_comap, key w' (Or.inr hw') fun e => Finset.disjoint_left.1 hd hw (e ▸ hw')]
    exact one_mem _

private theorem outW :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ n : ℕ, 1 ≤ n → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V), ContCoef R → ∀ (S₀ : Finset (Plc L)) (c : ℕ) (U : Subgroup (UA L n)), U = lev (Kall L n) S₀ (deep c) → IsLevel U →
                 ∃ A : Set (Submodule ℂ (UA L n → ℂ)), A.Finite ∧ (∀ σ ∈ A, IsAutRepU σ ∧ (∃ φ ∈ σ, φ ≠ 0 ∧ ∀ u ∈ U, RU L n u φ = φ)) ∧
                   ∀ S : Finset (Plc L), Places ((S₀ : Set (Plc L)) ∪ S) → Disjoint S₀ S → Places (S : Set (Plc L)) → (∀ w ∈ S, locU n w ⊓ Kall L n ≤ U) →
                   ∀ (ψ : ∀ w : Plc L, Fin n → (Kw w)ˣ →* ℂˣ) (φ : UA L n → V), φ ≠ 0 → IsAF R (lev U S iw) φ →
                   (∀ w ∈ S, (∀ i, ∀ u ∈ UpperTheory.V.Hi.Uo (Kw w), ψ w i u = 1) ∧ (∀ i i', i ≠ i' → ψ w i ≠ ψ w i' ∧ ψ w i ≠ ψ w i' * absPow (Kw w) 1) ∧
                     EigT φ w (iw w) (ψ w)) → (∀ w ∈ S₀, (∀ i, IsSmoothChar (ψ w i)) ∧ EigT φ w (deep c w) (ψ w)) →
                   ∃ σ ∈ A, (∀ w ∈ S₀, CompSub σ w (ψ w)) ∧ ∀ w ∈ S, CompSub σ w (ψ w) := by
  intro H L _ _ _ unr n hn V _ _ _ R hR S₀ c U eU hU
  obtain ⟨A, hA, hA', h⟩ := UpperTheory.V.Z.Sym.U.finFamU L n V R hR U hU
  refine ⟨A, hA, hA', fun S hP hd hS hK ψ φ h0 hφ hψ hψ0 => ?_⟩
  obtain ⟨π, φ₁, hπ, h1, hφ₁, hc, he⟩ := proj L n V R hR _ ((cof L n).2.2.1 U hU S iw) φ h0 hφ
  have hcs : ∀ w ∈ S, CompSub π w (ψ w) := fun w hw =>
    compOfEig H L unr n hn V π hπ w (hS.split w hw) φ₁ h1 hc (fun x hx hJ => hφ₁.level x (mem_lev hS hK hw hx hJ)) (ψ w)
      (fun i => (unrSmooth _).1 _ ((hψ w hw).1 i)) fun d hd => he _ _ _ _ ((hψ w hw).2.2 d hd)
  have hc0 : ∀ w ∈ S₀, CompSub π w (ψ w) := fun w hw =>
    compD H L unr n hn V π hπ w (hP.split w (Or.inl hw)) (deep c w) φ₁ h1 hc
      (fun x hx hJ => hφ₁.level x (eU ▸ mem_level_of_local_depth hP hd hw hx hJ)) (ψ w) (hψ0 w hw).1 fun d hd => he _ _ _ _ ((hψ0 w hw).2 d hd)
  obtain ⟨φ₂, h2, hc2, hφ₂⟩ := raise L n V R π hπ U hU.1 S hS
    (fun w hw => ⟨hK w hw, sph H L n π w (ψ w) (hS.split w hw) (hcs w hw) (hψ w hw).1 (hψ w hw).2.1⟩) iw φ₁ h1 hc hφ₁
  obtain ⟨σ, hσ, ht⟩ := h π hπ φ₂ h2 hφ₂ hc2
  refine ⟨σ, hσ, fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨a, τ, b, c⟩ := hc0 w hw
    exact ⟨a, τ, ht w τ b, c⟩
  · obtain ⟨a, τ, b, c⟩ := hcs w hw
    exact ⟨a, τ, ht w τ b, c⟩

private theorem smo {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ψ : Fin 2 → kˣ →* ℂˣ}
    (h : ∀ i, IsSmoothChar (ψ i)) : ∀ i, IsSmoothChar ((![ψ 0 / ψ 1, 1, (ψ 0 / ψ 1)⁻¹] : Fin 3 → kˣ →* ℂˣ) i) := by
  have h1 : IsSmoothChar (ψ 0 / ψ 1) := by
    rw [div_eq_mul_inv]
    exact (h 0).mul (h 1).inv
  intro i
  fin_cases i
  · exact h1
  · have := h1.mul h1.inv
    rwa [mul_inv_cancel] at this
  · exact h1.inv

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

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.NeZeroRep
section
noncomputable section

namespace UpperTheory.V.Z.Sym.W.RetractionModules

section Rep

private theorem mod_retr {R S M : Type} [Ring R] [AddCommGroup S] [Module R S] [AddCommGroup M] [Module R M]
    [IsSimpleModule R S] (h : ⨆ f : S →ₗ[R] M, LinearMap.range f = ⊤) (x : M) (hx : x ≠ 0) :
    ∃ T : M →ₗ[R] S, T x ≠ 0 := by
  have htop : isotypicComponent R M S = ⊤ := top_le_iff.1 (h ▸ iSup_le fun f => by
    rcases f.injective_or_eq_zero with hi | rfl
    · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
    · simp)
  haveI : IsSemisimpleModule R M :=
    IsSemisimpleModule.congr (M := isotypicComponent R M S) (LinearEquiv.ofTop _ htop).symm
  have hiso := IsIsotypicOfType.of_isotypicComponent_eq_top htop
  obtain ⟨m, hm, hxm⟩ : ∃ m : Submodule R M, IsCoatom m ∧ x ∉ m := by
    by_contra hn
    push Not at hn
    refine hx ((Submodule.mem_bot R).1 ?_)
    rw [← IsSemisimpleModule.jacobson_eq_bot R M]
    exact Submodule.mem_sInf.2 hn
  obtain ⟨W, hc⟩ := exists_isCompl m
  haveI : IsSimpleModule R W := isSimpleModule_iff_isAtom.2 (hc.isCoatom_iff_isAtom.1 hm)
  obtain ⟨e⟩ := hiso W
  refine ⟨e.toLinearMap ∘ₗ W.projectionOnto m hc.symm, fun h0 => hxm ?_⟩
  simpa using h0

variable {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]

private theorem rep_retr (σ : Representation ℂ Γ X) (hσ : σ.IsIrreducible) (τ : Representation ℂ Γ V)
    (h : ⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1 = ⊤) (x : V) (hx : x ≠ 0) :
    ∃ T : V →ₗ[ℂ] X, (∀ g v, T (τ g v) = σ g (T v)) ∧ T x ≠ 0 := by
  have key := mod_retr (R := MonoidAlgebra ℂ Γ) (S := σ.asModule) (M := τ.asModule) (by
      refine top_le_iff.1 fun y _ => ?_
      have hy : τ.asModuleEquiv y ∈ (⊤ : Submodule ℂ V) := trivial
      rw [← h] at hy
      rw [← τ.asModuleEquiv.symm_apply_apply y]
      refine Submodule.iSup_induction _ (motive := fun z => τ.asModuleEquiv.symm z ∈ _) hy ?_ ?_ ?_
      · rintro f _ ⟨v, rfl⟩
        exact Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ τ
          ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩) ⟨v, rfl⟩
      · simp
      · intro a b ha hb
        rw [map_add (f := _)]
        exact add_mem ha hb)
  obtain ⟨T, h2⟩ := key x hx
  let T' := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ).symm T
  exact ⟨T'.toLinearMap, fun g v => LinearMap.congr_fun (T'.2 g) v, h2⟩

private theorem ne_zero_rep (τ : Representation ℂ Γ V) {x : V} (hx : x ≠ 0) (g : Γ) : τ g ≠ 0 := fun h => hx (by
  have : τ g⁻¹ (τ g x) = x := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h, LinearMap.zero_apply, map_zero])

private theorem map_dc (σ : Representation ℂ Γ X) (τ : Representation ℂ Γ V) (T : V →ₗ[ℂ] X)
    (hT : ∀ g v, T (τ g v) = σ g (T v)) {x : V} (hx : T x ≠ 0) (K : Subgroup Γ) (a : Γ) :
    T (Hi.dc τ K K a x) = Hi.dc σ K K a (T x) := by
  have hx0 : x ≠ 0 := fun e => hx (by rw [e, map_zero])
  rcases finite_or_infinite (MulAction.orbit K (a : Γ ⧸ K)) with hf | hf
  · haveI := Fintype.ofFinite (MulAction.orbit K (a : Γ ⧸ K))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum, hT]
  · rw [Hi.dc, Hi.dc, finsum_of_infinite_support, finsum_of_infinite_support]
    · simp
    · rw [Function.support_eq_univ fun _ => ne_zero_rep σ hx _]
      exact Set.infinite_univ
    · rw [Function.support_eq_univ fun _ => ne_zero_rep τ hx0 _]
      exact Set.infinite_univ

end Rep

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V.Af UpperTheory.V.Sd

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_ps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin 2) k) V} (hπ : GlobalTheory.PRep.IsSmooth π)
    (hi : π.IsIrreducible) (μ₁ μ₂ : kˣ →* ℂˣ) (L : V →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    (H : ∀ (a d : kˣ) (x : k) v, L (π (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) =
      ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) :
    ∃ ψ : Fin 2 → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ IsSubquotient π (prinSeries ψ) ∧
      ∀ x : kˣ, ψ 0 x = μ₁ x * (absPow k (1 / 2) x)⁻¹ := by
  set δ : (Fin 2 → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin 2 => Unit).comp (leviTorus k (Fin 2)).toMonoidHom with hδ
  let χ : (Fin 2 → kˣ) →* ℂˣ := torusChar ![μ₁, μ₂] * δ⁻¹
  have hU : GlobalTheory.PRep.twKer π (unipB k (Fin 2)) 1 ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    obtain ⟨u1, u2⟩ := (mem_unipB k).1 u.2
    have e : (u : GL (Fin 2) k) = Matrix.GeneralLinearGroup.scalar (Fin 2) 1 * aff (1 / 1) (u.1.val 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [aff, u2, u1 1 0]
    have := H 1 1 (u.1.val 0 1) v
    rw [← e] at this
    simp [this]
  let l : GlobalTheory.PRep.Jacquet π (unipB k (Fin 2)) →ₗ[ℂ] ℂ := Submodule.liftQ _ L hU
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hL (LinearMap.ext hn)
  have hle : ∀ t x, l (jacB π t x) = (χ t : ℂ) * l x := fun t x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e : diagT k (Fin 2) t = Matrix.GeneralLinearGroup.scalar (Fin 2) (t 1) * aff (t 0 / t 1) 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [aff, val_diagT, Matrix.GeneralLinearGroup.scalar, mul_div_cancel₀]
    rw [UnramFixed.jacB_apply, jacBU_mk, map_smul, e]
    change _ * L _ = _ * L y
    rw [H, ← mul_assoc, ← Units.val_mul, mul_comm _ (μ₁ _ * _)]
    simp [χ, torusChar_apply, hδ]
  have hs : IsSmoothChar χ := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      ((isSmooth_jacB hπ (Submodule.Quotient.mk v)).mem_nhds (by simp)) ?_)
    intro g hg
    have hg' : jacB π g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := hg
    have h := hle g (Submodule.Quotient.mk v)
    rw [hg'] at h
    exact Units.ext (mul_right_cancel₀ (show l (Submodule.Quotient.mk v) ≠ 0 from hv) (h.symm.trans (one_mul _).symm))
  have htc : torusChar (fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i)) = χ :=
    MonoidHom.ext fun t => by
      rw [torusChar_apply]
      conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
      rfl
  refine ⟨fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
    fun i => hs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), ?_, fun x => ?_⟩
  · have key := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hi χ l
      (fun e => hv (LinearMap.congr_fun e (Submodule.Quotient.mk v))) hle
    rw [← htc] at key
    exact key
  · have hd : ∀ (t : Fin 2 → kˣ) i, Matrix.GeneralLinearGroup.det (leviTorus k (Fin 2) t i) = t i := fun t =>
      congrFun ((leviTorus k (Fin 2)).left_inv t)
    have e0 : modExp (fun _ : Fin 2 => Unit) 0 = 1 := by decide
    have e1 : modExp (fun _ : Fin 2 => Unit) 1 = -1 := by decide
    have h1 : δ (Pi.mulSingle 0 x) = absPow k (1 / 2) x := by
      rw [hδ, MonoidHom.comp_apply]
      change deltaHalf k (fun _ : Fin 2 => Unit) (leviTorus k (Fin 2) (Pi.mulSingle 0 x)) = _
      rw [deltaHalf_apply, Fin.prod_univ_two, hd, hd, e0, e1]
      simp
    change torusChar ![μ₁, μ₂] (Pi.mulSingle 0 x) * (δ (Pi.mulSingle 0 x))⁻¹ = _
    rw [h1]
    simp [torusChar_apply]

section Gal

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w}

end Gal

end UpperTheory.V.Z.Sym.W.RetractionModules

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V.Af
open UpperTheory.V.Sd UpperTheory.V.Z.Sym.W.RetractionModules

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem plainAll {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} {ξ : G F Ω →* (Qbar l)ˣ} {s c m a π r} (H : OrdForm ι ξ s c m a π r) {wt HT} (hG : UpperTheory.Gal.SV.IsGalRS π ι r wt HT) (w) :
    UpperTheory.V.Z.Win.PlainAtR π w := fun σ hσ =>
  (UpperTheory.V.Z.Win.Birth.ordPlain F Ω l ι ξ s c m a π r H w σ hσ).elim id fun ⟨B, hB⟩ => hG.plain w B hB σ hσ
end
end

