module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CuspOrTwoAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree

@[expose] public section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

section

open Formalism.L2.Host Matrix

private theorem isotypic {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (π : CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (hσ : π.IsLocComp w σ) :
    UpperTheory.V.Af.LocIsotypic π.finPart w σ := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩
  obtain ⟨f, h0, hf⟩ := hσ
  change ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 = ⊤
  have preserves_isotypic (T : Module.End ℂ π.V)
      (hT : ∀ g y, T (π.locRep w g y) = π.locRep w g (T y)) {x : π.V}
      (hx : x ∈ ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)},
        LinearMap.range f.1) :
      T x ∈ ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)},
        LinearMap.range f.1 := by
    refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap T _) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem
      ⟨T ∘ₗ f.1, fun g v => by simp only [LinearMap.comp_apply, f.2, hT]⟩ ⟨v, rfl⟩
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ (o : Op E a) (x : π.V),
      x ∈ (⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1) →
      π.op o x ∈ ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 := by
    intro o x hx
    cases o with
    | fin k =>
      have h1 := preserves_isotypic
        (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k)) (fun g' y => by
        simp only [CuspSub.locRep, MonoidHom.comp_apply]
        rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul,
          LocUniq.comm_locGL w (LocEx.map_pLoc_inv_mul w k)]) hx
      have e : π.locRep w (GeneralLinearGroup.map (pLoc E w) k)
          (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) x) = π.op (.fin k) x := by
        rw [CuspSub.locRep, MonoidHom.comp_apply, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]
        rfl
      rw [← e]
      refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) :
        _ ≤ Submodule.comap (π.locRep w (GeneralLinearGroup.map (pLoc E w) k)) _) h1)
      rintro _ ⟨v, rfl⟩
      exact Submodule.mem_iSup_of_mem f ⟨σ.ρ (GeneralLinearGroup.map (pLoc E w) k) v, f.2 _ _⟩
    | cpt k =>
      refine preserves_isotypic _ (fun g y => Subtype.ext ?_) hx
      change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
        (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, infGL_comm]
    | lie X =>
      refine preserves_isotypic _ (fun g y => Subtype.ext ?_) hx
      exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1
  rcases π.irred (Submodule.map π.V.subtype _) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h1 | h1
  · have h2 := hi (h1.trans (Submodule.map_bot _).symm)
    exact absurd (LinearMap.range_eq_bot.1 (le_bot_iff.1 (h2 ▸ le_iSup
      (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)} => LinearMap.range f.1) ⟨f, hf⟩))) h0
  · exact hi (h1.trans (Submodule.map_subtype_top _).symm)

end

open GlobalTheory.LFun in
private theorem sat_part {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ} (e : N = n)
    (V : Submodule ℂ (Sm E N)) (π : CuspSub E n) (he : e ▸ V = π.V) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin N) (w.adicCompletion E))) (h : IsLocCompGL V w σ) (B : Multiset ℂˣ) :
    (CG.mk π).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w σ.ρ B := by
  subst e
  subst he
  obtain ⟨f, h0, hm, hf⟩ := h
  have hσ : π.IsLocComp w σ := by
    refine ⟨f.codRestrict _ hm, fun e => h0 ?_, fun g v => Subtype.ext (hf g v)⟩
    exact LinearMap.ext fun v => congrArg Subtype.val (LinearMap.congr_fun e v)
  have htop := (isotypic π w σ hσ).2
  have up {B : Multiset ℂˣ} : HasSatGL w σ.ρ B → HasSatGL w (π.locRep w) B :=
    GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ
  change HasSatGL w (π.locRep w) B ↔ HasSatGL w σ.ρ B
  refine ⟨fun h => ?_, up⟩
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 h.1
  obtain ⟨y, hy0, hy⟩ := LocSph.exists_fixed_of_mem_iSup (π.locRep w) σ.ρ σ.irred
    (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)} => f.1) (fun f => f.2)
    (KGL w (n := N) : Set _) x hx0 (fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx k hk) (htop ▸ Submodule.mem_top)
  obtain ⟨B', hB'⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred
    ((Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩)
  exact (up hB').unique h ▸ hB'

theorem UpperTheory.V.Z.Tf.GOne.oneSat :
    OneSat := by
  intro E _ _ _ n _ π D hD w B
  obtain ⟨c, N, h, V, σ, m, pos, disc, loc, inf⟩ := D
  obtain ⟨hc, hV⟩ := hD
  obtain rfl : c = 1 := hc
  obtain ⟨e, he⟩ := hV 0
  have key := sat_part e (V 0) π he w (σ 0 w) (loc 0 w) B
  constructor
  · intro hs
    have h1 := key.1 hs
    refine ⟨fun _ => B, fun i => ?_, by simp⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact ⟨h1.1, h1⟩
  · rintro ⟨b, hb, rfl⟩
    have h1 := (hb 0).2
    simpa using (sat_part e (V 0) π he w (σ 0 w) (loc 0 w) (b 0)).2 h1
