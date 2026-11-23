module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0056
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2IsoL
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem frame_stab {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {d m : ℕ}
    (ξ : Gp →* GL (Fin d) ℂ) (τ : X.Ub →* GL (Fin m) ℂ) (U : Subgroup X.Ub) (b : Gp) (F : Fin m → X.Fn ℂ d)
    (hF : F ∈ Submodule.pi Set.univ (fun _ : Fin m => X.AF ξ) ⊓ fixd (X.raF d τ) U) :
    X.rpF ℂ d m b F ∈ Submodule.pi Set.univ (fun _ : Fin m => X.AF ξ) ⊓ fixd (X.raF d τ) U := by
  refine ⟨fun i hi γ g => ?_, fun u hu => ?_⟩
  · have h := hF.1 i hi γ (g * (1, b))
    rw [← mul_assoc] at h
    exact h
  · funext i g k
    have h := congrFun (congrFun (congrFun (hF.2 u hu) i) (g * (1, b))) k
    have e : g * (1, b) * ((u : Ga), 1) = g * ((u : Ga), 1) * (1, b) := by
      rw [mul_assoc, mul_assoc]
      simp
    change (Matrix.mulVec (τ u : Matrix (Fin m) (Fin m) ℂ) fun j => F j (g * (1, b) * ((u : Ga), 1)) k) i = F i (g * (1, b)) k at h
    rw [e] at h
    exact h

private theorem big_stab {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) (v : H.V)
    (g : GLw n (H.Sl v)) (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ H.Big ι ξ) : H.atV d v g F ∈ H.Big ι ξ :=
  frame_stab H.X ξ (H.τC ι) H.UQ _ F hF

private theorem iso_of {H P N W : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup N] [Module ℂ N]
    [AddCommGroup W] [Module ℂ W] {m d : ℕ} (e : (Fin d → ℂ) ≃ₗ[ℂ] W)
    (T : (P → Fin d → ℂ) →ₗ[ℂ] Module.Dual ℂ W →ₗ[ℂ] N) (ρ : Representation ℂ H (Fin m → P → Fin d → ℂ))
    (ρ' : Representation ℂ H N) (Y : Submodule ℂ (Fin m → P → Fin d → ℂ)) (Z : Submodule ℂ N) (τ : SmIrr H)
    (hZ : IsoSum ρ' Z τ) (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hm : ∀ y ∈ Y, ∀ i ℓ, T (y i) ℓ ∈ Z)
    (he : ∀ y g i ℓ, T (ρ g y i) ℓ = ρ' g (T (y i) ℓ)) (hi : ∀ y ∈ Y, ∀ i, (∀ ℓ, T (y i) ℓ = 0) → y i = 0) :
    IsoSum ρ Y τ := by
  let b := (Pi.basisFun ℂ (Fin d)).map e
  refine UpperTheory.isoSum_of_injective_equivariant_family H _ N ρ ρ' Y Z τ (Fin m × Fin d)
    (fun x => T.flip (b.coord x.2) ∘ₗ LinearMap.proj x.1) hZ hY (fun x y hy => hm y hy x.1 _)
    (fun x g y _ => he y g x.1 _) fun y hy h => funext fun i => hi y hy i fun ℓ => ?_
  have h0 : T (y i) = 0 := b.dualBasis.ext fun k => by
    rw [Module.Basis.coe_dualBasis]
    exact h (i, k)
  rw [h0]
  rfl

private noncomputable def formLin {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) :
    (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ]
      Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
  LinearMap.mk₂ ℂ (toForm ι e)
    (fun F F' ℓ => funext fun g => by
      simp only [toForm, Pi.add_apply, map_add (f := _)])
    (fun a F ℓ => funext fun g => by
      simp only [toForm, Pi.smul_apply, map_smul])
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)

theorem UpperTheory.V.Hi.partUR2IsoL :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    ∀ (v : V.frame.Vl) (τ : SmIrr (GLw n (s.w v.1))), IsCompAlong σ (locU n (s.w v.1)) ((cLoc (s.w v.1)).comp (locU n (s.w v.1)).subtype) τ.ρ → IsoSum (H := GLw n (s.w v.1)) ((hset Q τ₀).atV d v) (YOf Q ι τ₀ e ξ σ) τ := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ v τ hτ
  have hsp : IsSplitAt (s.w v.1) :=
    UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω (s.A v.1) v.1 (s.hA v.1) (s.split v.1 (Or.inl v.2)) _ (w_under s v.1)
  obtain ⟨j, hj1, hj2, -, hj3⟩ := (secU l L Ω s n hn (s.w v.1) hsp).1
  have hZ := UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ (s.w v.1) j hj1 hj2 hj3 τ hτ
  have hM := partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ
  have hA := partUR2AtV l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ v j hj1 hj2
  have hI := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).1
  have hY : ∀ g, ∀ y ∈ YOf Q ι τ₀ e ξ σ, (hset Q τ₀).atV d v g y ∈ YOf Q ι τ₀ e ξ σ := fun g y hy =>
    (hM _).2 ⟨big_stab (hset Q τ₀) ι ξ v g y ((hM y).1 hy).1, fun i ℓ =>
      (hA y g i ℓ).symm ▸ hσ.stable (j g) _ (((hM y).1 hy).2 i ℓ)⟩
  exact iso_of (H := GLw n (s.w v.1)) (m := m) e (formLin ι e) ((hset Q τ₀).atV d v) ((RU L n).comp j) (YOf Q ι τ₀ e ξ σ) σ τ hZ hY
    (fun y hy => ((hM y).1 hy).2) hA fun y hy i h => hI (y i) (((hM y).1 hy).1.1 i trivial) h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2IsoQ
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem raF_big {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {d m : ℕ}
    (τ : X.Ub →* GL (Fin m) ℂ) (ξ : Gp →* GL (Fin d) ℂ) (U : Subgroup X.Ub) (x : X.Ub) (hx : ∀ u ∈ U, Commute u x)
    (F : Fin m → X.Fn ℂ d) (hF : F ∈ Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U) :
    X.raF d τ x F ∈ Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U := by
  refine ⟨fun i _ => ?_, fun u hu => ?_⟩
  · have h : X.raF d τ x F i = ∑ j, (τ x : Matrix (Fin m) (Fin m) ℂ) i j • fun g => F j (g * ((x : Ga), 1)) := by
      funext g k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    change X.raF d τ x F i ∈ X.AF ξ
    rw [h]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ fun γ g => ?_
    have := hF.1 j trivial γ (g * ((x : Ga), 1))
    simpa only [mul_assoc] using this
  · rw [← Module.End.mul_apply, ← map_mul, (hx u hu).eq, map_mul, Module.End.mul_apply, hF.2 u hu]

private theorem big_atW {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hA : H.Ax) (ι : Qbar l ≃+* ℂ) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ)
    (q : H.Q) (g : GLw n (H.wq q)) (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ H.Big ι ξ) : H.atW ι d (H.wq q) g F ∈ H.Big ι ξ :=
  raF_big H.X (H.τC ι) ξ H.UQ (H.sec (H.wq q) g) (fun u hu => hA.Q_UQ q u hu g) F hF

private noncomputable def formL {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) :
    (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ]
      Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
  LinearMap.mk₂ ℂ (toForm ι e)
    (fun F F' ℓ => funext fun g => by simp only [toForm, Pi.add_apply, map_add (f := _)])
    (fun a F ℓ => funext fun g => by simp only [toForm, Pi.smul_apply, map_smul])
    (fun F ℓ ℓ' => rfl) (fun a F ℓ => rfl)

theorem UpperTheory.V.Hi.partUR2IsoQ :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    (hset Q τ₀).Ax → ∀ (q : Q.Q) (τ : SmIrr (GLw n (Q.wq q))), IsCompAlong σ (locU n (Q.wq q)) ((cLoc (Q.wq q)).comp (locU n (Q.wq q)).subtype) τ.ρ → IsoSum ((hset Q τ₀).atW ι d (Q.wq q)) (YOf Q ι τ₀ e ξ σ) τ := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ hA q τ hτ
  have hS' : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
    rw [Q.range]
    exact Or.inr ⟨q, rfl⟩
  have hsp : IsSplitAt (Q.wq q) := UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ hS') _ rfl
  obtain ⟨j, hj1, hj2, -, hj3⟩ := (secU l L Ω s n hn _ hsp).1
  have hiso := UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ _ j hj1 hj2 hj3 τ hτ
  have hmem := partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ
  have hat := partUR2AtW l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ _ hsp (Q.notS q) j hj1 hj2
  have hinj := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).1
  let b := ((Pi.basisFun ℂ (Fin d)).map e).dualBasis
  let φ : Fin m × Fin d → (Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ] (UA L n → ℂ) :=
    fun x => ((formL ι e).flip (b x.2)).comp (LinearMap.proj x.1)
  refine UpperTheory.isoSum_of_injective_equivariant_family _ _ _ _ ((RU L n).comp j) _ σ τ (Fin m × Fin d) φ hiso (fun g F hF => ?_) (fun x F hF => ?_)
    (fun x g F _ => ?_) (fun F hF h0 => ?_)
  · obtain ⟨h1, h2⟩ := (hmem F).1 hF
    refine (hmem _).2 ⟨big_atW (hset Q τ₀) hA ι ξ q g F h1, fun i ℓ => ?_⟩
    refine (hat F g i ℓ).symm ▸ ?_
    exact hσ.stable _ _ (h2 i ℓ)
  · exact ((hmem F).1 hF).2 x.1 (b x.2)
  · exact hat F g x.1 (b x.2)
  · refine funext fun i => hinj (F i) (((hmem F).1 hF).1.1 i trivial) fun ℓ => ?_
    have h : formL ι e (F i) = 0 := b.ext fun k => h0 (i, k)
    exact LinearMap.congr_fun h ℓ
end

