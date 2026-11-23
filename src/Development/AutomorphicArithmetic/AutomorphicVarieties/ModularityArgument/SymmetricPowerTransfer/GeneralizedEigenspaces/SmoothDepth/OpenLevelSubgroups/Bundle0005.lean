module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SecSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.AbsPow
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.sph :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : Submodule ℂ (UA L n → ℂ)) (w : Plc L) (ψ : Fin n → (Kw w)ˣ →* ℂˣ), IsSplitAt w → CompSub π w ψ →
                 (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ i u = 1) → (∀ i i', i ≠ i' → ψ i ≠ ψ i' ∧ ψ i ≠ ψ i' * absPow (Kw w) 1) → IsUnramU π w := by
  intro H L _ _ _ n π w ψ hw hc hu hne
  obtain ⟨hsm, τ, ⟨-, f, hf0, hfπ, hf⟩, hsq⟩ := hc
  obtain ⟨hs1, hs2, -, -⟩ := secSpec L n w hw

  have hker : ∀ x, f x = 0 → x = 0 := by
    let S : Subrepresentation τ.ρ := ⟨LinearMap.ker f, by
      intro g x hx
      have h := hf ⟨secW n w g, hs1 g⟩ x
      have h' : f (τ.ρ g x) = RU L n (secW n w g) (f x) := by
        rw [← h]
        show f (τ.ρ g x) = f (τ.ρ (cLoc w (secW n w g)) x)
        rw [hs2 g]
      rw [LinearMap.mem_ker] at hx ⊢
      rw [h', hx, map_zero]⟩
    have hS : S = ⊥ := by
      rcases (τ.irred.eq_bot_or_eq_top S) with h | h
      · exact h
      · refine absurd (LinearMap.ext fun x => ?_) hf0
        have : x ∈ S.toSubmodule := by rw [h]; trivial
        exact this
    intro x hx
    have : x ∈ S.toSubmodule := hx
    rw [hS] at this
    exact this

  obtain ⟨ω, rfl, hω⟩ : ∃ ω : Fin n → (Kw w)ˣ →* ℂˣ,
      ψ = (fun i => ω i * absPow (Kw w) (((n : ℂ) - 1) / 2)) ∧ ∀ i, IsSmoothChar (ω i) := by
    refine ⟨fun i => ψ i * absPow (Kw w) (-(((n : ℂ) - 1) / 2)), funext fun i => ?_,
      fun i => (hsm i).mul (isSmoothChar_of_isUnram (isUnram_absPow _ _))⟩
    have h0 : absPow (Kw w) 0 = 1 := by
      ext x
      simp [absPow]
    rw [mul_assoc, ← absPow_add, neg_add_cancel, h0, mul_one]
  have hneω : ∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * absPow (Kw w) 1 := fun i j hij =>
    ⟨fun h => (hne i j hij).1 (by simp only [h]), fun h => (hne i j hij).2 (by
      simp only []
      rw [h, mul_right_comm])⟩
  obtain ⟨E⟩ := (Hi.psIrr H (Kw w) n ω hω hneω).2 _ τ.ρ τ.irred hsq
  obtain ⟨v₀, hv₀, hfix⟩ := locSph (Kw w) n _ hu
  obtain ⟨v, rfl⟩ := E.surjective v₀
  have hv : v ≠ 0 := by
    rintro rfl
    exact hv₀ (map_zero E)
  have hτ : ∀ u ∈ KO (Kw w) (Fin n), τ.ρ u v = v := fun u hu' => by
    apply E.injective
    have h1 := LinearMap.congr_fun (E.isIntertwining' u) v
    exact h1.trans (hfix u hu')
  refine ⟨f v, hfπ v, fun h => hv (hker v h), fun x hx hK => ?_⟩
  have h := hf ⟨x, hx⟩ v
  rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL] at hK
  rw [← h]
  show f (τ.ρ (cLoc w x) v) = f v
  rw [hτ _ hK]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.IsoTypic
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.isoTypic :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : Submodule ℂ (UA L n → ℂ)) (hπ : IsAutRepU π) (w : Plc L), IsSplitAt w → ∀ τ, Comp π w τ →
        (⨆ f : {f : τ.V →ₗ[ℂ] π // ∀ h x, f (τ.ρ h x) = (repOn hπ).comp (secW n w) h (f x)}, LinearMap.range f.1) = ⊤ := by
  intro L _ _ _ n π hπ w hw τ ⟨_, f, f0, fm, fe⟩
  obtain ⟨f1, f2, -⟩ := factor L n w
  obtain ⟨s1, s2, s3, -⟩ := secSpec L n w hw
  set N := ⨆ f : {f : τ.V →ₗ[ℂ] π // ∀ h x, f (τ.ρ h x) = (repOn hπ).comp (secW n w) h (f x)}, LinearMap.range f.1 with hN
  have hst : ∀ g, ∀ v ∈ N, repOn hπ g v ∈ N := by
    intro g v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := f2 g
    refine Submodule.iSup_induction _ (motive := fun v => repOn hπ (x * y) v ∈ N) hv ?_ (by simp) fun a b ha hb => by
      rw [map_add (f := _)]; exact N.add_mem ha hb
    rintro ⟨p, hp⟩ _ ⟨t, rfl⟩
    refine Submodule.mem_iSup_of_mem ⟨repOn hπ y ∘ₗ p, fun h t => ?_⟩ ⟨τ.ρ (cLoc w x) t, ?_⟩
    · rw [LinearMap.comp_apply, hp, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, ← f1 _ (s1 h) y hy, map_mul]; rfl
    · rw [LinearMap.comp_apply, hp, MonoidHom.comp_apply, s3 x hx, ← Module.End.mul_apply, ← map_mul, f1 x hx y hy]
  rcases hπ.irred (N.map π.subtype) (Submodule.map_subtype_le _ _) (by
    rintro x _ ⟨v, hv, rfl⟩
    exact ⟨_, hst x v hv, rfl⟩) with h | h
  · refine absurd (LinearMap.ext fun t => ?_) f0
    have : f t ∈ N.map π.subtype := ⟨⟨f t, fm t⟩, Submodule.mem_iSup_of_mem ⟨f.codRestrict π fm, fun h t => Subtype.ext (by
      have := fe ⟨secW n w h, s1 h⟩ t
      rw [MonoidHom.comp_apply, Subgroup.subtype_apply, s2] at this
      exact this)⟩ ⟨t, rfl⟩, rfl⟩
    rwa [h] at this
  · exact Submodule.map_injective_of_injective π.injective_subtype (by rw [h, Submodule.map_subtype_top])
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SpanKeep
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem dc_conj {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K K' : Subgroup H) (x : H) (T : M ≃ₗ[A] M)
    (hT : ∀ h m, T (ρ h m) = ρ h (T m)) (m : M) :
    T (UpperTheory.V.Hi.dc ρ K K' x m) = UpperTheory.V.Hi.dc ρ K K' x (T m) := by
  have hc : ∀ h, T.conj (ρ h) = ρ h := fun h => by
    ext v
    simp [LinearEquiv.conj_apply, hT]
  have key : T.conj (UpperTheory.V.Hi.dc ρ K K' x) = UpperTheory.V.Hi.dc ρ K K' x := by
    unfold UpperTheory.V.Hi.dc
    have := AddEquiv.map_finsum (T.conj.toAddEquiv)
      (fun q : MulAction.orbit K (x : H ⧸ K') => ρ (q : H ⧸ K').out)
    simpa [hc] using this
  have := congrArg (fun E : Module.End A M => E (T m)) key
  simpa [LinearEquiv.conj_apply] using this

theorem UpperTheory.V.Z.Sym.Al.spanKeep :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (w : Plc L) (φ φ' : UA L n → V), InSpan w φ φ' →
        (∀ π, IsAutRepU π → CoefIn φ π → CoefIn φ' π) ∧
        (∀ (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (A : Subgroup (UA L n)), A ≤ away n w → IsAF R A φ → IsAF R A φ') ∧
        ∀ w' : Plc L, IsSplitAt w' → w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) → ∀ W d c, EigAt φ w' W d c → EigAt φ' w' W d c := by
  intro L _ _ _ n V _ _ w φ φ' h
  obtain ⟨h1, -, h3, h4, -, -⟩ := UpperTheory.V.Z.Sym.Al.factor L n w
  refine ⟨fun π hπ hc => ?_, fun R A hA hf => ?_, fun w' hs hne W d c he => ?_⟩
  · refine Submodule.span_induction (p := fun ψ _ => CoefIn ψ π) ?_ ?_ ?_ ?_ h
    · rintro _ ⟨x, hx, rfl⟩ f
      exact hπ.stable x _ (hc f)
    · intro f
      have e : f ∘ (0 : UA L n → V) = 0 := by ext; simp
      rw [e]
      exact π.zero_mem
    · intro a b _ _ ha hb f
      have e : f ∘ (a + b) = f ∘ a + f ∘ b := by ext; simp
      rw [e]
      exact π.add_mem (ha f) (hb f)
    · intro t a _ ha f
      have e : f ∘ (t • a) = t • (f ∘ a) := by ext; simp
      rw [e]
      exact π.smul_mem t (ha f)
  · have hle : Submodule.span ℂ {ψ | ∃ x ∈ locU n w, ψ = fun g => φ (g * x)} ≤ AF R A := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨fun γ hγ g => ?_, fun y hy g => ?_, fun u hu g => ?_⟩
      · show φ (γ * g * x) = φ (g * x)
        rw [mul_assoc]
        exact hf.left γ hγ _
      · show φ (g * y * x) = R (infC L n y⁻¹) (φ (g * x))
        rw [mul_assoc, ← h1 x hx y (h4 hy), ← mul_assoc]
        exact hf.inf y hy _
      · show φ (g * u * x) = φ (g * x)
        rw [mul_assoc, ← h1 x hx u (hA hu), ← mul_assoc]
        exact hf.level u hu _
    exact hle h
  · have hsec := (UpperTheory.V.Z.Sym.Al.secSpec L n w' hs).1
    refine Submodule.span_induction (p := fun ψ _ => EigAt ψ w' W d c) ?_ ?_ ?_ ?_ h
    · rintro _ ⟨x, hx, rfl⟩
      let T : (UA L n → V) ≃ₗ[ℂ] (UA L n → V) :=
        { toFun := fun ψ g => ψ (g * x)
          invFun := fun ψ g => ψ (g * x⁻¹)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          left_inv := fun ψ => by ext g; simp
          right_inv := fun ψ => by ext g; simp }
      have hT : ∀ (y : GL (Fin n) (Kw w')) (m : UA L n → V),
          T (((rightReg ℂ (UA L n) V).comp (secW n w')) y m) =
            ((rightReg ℂ (UA L n) V).comp (secW n w')) y (T m) := by
        intro y m
        funext g
        show m (g * x * secW n w' y) = m (g * secW n w' y * x)
        rw [mul_assoc, mul_assoc, h1 x hx _ (h3 w' hne (hsec y))]
      have e := dc_conj _ (W.J n) (W.J n) (Sig.dg d) T hT φ
      show UpperTheory.V.Hi.dc _ _ _ _ (T φ) = c • T φ
      rw [← e]
      unfold EigAt at he
      rw [he, map_smul]
    · unfold EigAt
      rw [map_zero, smul_zero]
    · intro a b _ _ ha hb
      unfold EigAt at ha hb ⊢
      rw [map_add (f := _), ha, hb, smul_add]
    · intro t a _ ha
      unfold EigAt at ha ⊢
      rw [map_smul, ha, smul_comm]
end

