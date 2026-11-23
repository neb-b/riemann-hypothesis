module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.MuConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RUEval
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.RFamMatch
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.EvaluationCombinedTestFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.USide
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0969
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.ChoiceM
section
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Af.Bc (cPl)

theorem UpperTheory.V.Z.Mult.choiceM :
    UpperTheory.V.Z.Mult.ChoiceM := by
  classical
  intro E _ _ _ n hn π hns μ e hμ S hS K' hK' hKn
  obtain ⟨-, hc, hInf, hSec⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E
  have hF := UpperTheory.V.Af.formsFiniteGL
  have hbad : {w : Pl E | ¬ (((∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w) ∧ K' w = KL n w)}.Finite :=
    Filter.eventually_cofinite.1 (((GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E n π).and
      (GlobalTheory.Mem.UnrAe.unr_ae_and_level E μ).1).and hK'.2)
  obtain ⟨Bd, hBd⟩ : ∃ Bd : Finset (Pl E), ∀ w, w ∈ Bd ↔
      ¬ (((∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w) ∧ K' w = KL n w) :=
    ⟨hbad.toFinset, fun w => by simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]⟩
  have hgood : ∀ w, w ∉ Bd → ((∃ B, (CG.mk π).HasSat w B) ∧ μ.UnrAt w) ∧ K' w = KL n w := fun w hw => by
    by_contra h
    exact hw ((hBd w).2 h)
  have hsplit : ∀ w ∈ Bd, IsSplitAt w := fun w hw => by
    by_contra hs
    exact (hBd w).1 hw ⟨⟨hns w hs, fun x hx => by
      rw [hμ.2.2.1 w hs]
      exact GlobalTheory.CompanionTheory.MuOpen.unrChar_apply_of_isUnitAt w _ x hx⟩, hKn w hs⟩
  have hcs : ∀ w, IsSplitAt w → IsSplitAt (cPl w) := fun w hw =>
    (hc (cPl w)).2.2 (by rw [(hc w).1]; exact ((hc w).2.1 hw).symm)
  obtain ⟨m, hm, hmS⟩ : ∃ m : Pl E → Pl E, (∀ w, m w ∈ S ∧ (m w = w ∨ m w = cPl w)) ∧ ∀ w ∈ S, m w = w :=
    ⟨fun w => if w ∈ S then w else cPl w, fun w => by
      by_cases h : w ∈ S
      · simp [h]
      · simpa [h] using ((hSec S hS w).1.resolve_left h), fun w h => by simp [h]⟩
  have hms : ∀ w, IsSplitAt w → IsSplitAt (m w) := fun w hw => by
    rcases (hm w).2 with e | e
    · rwa [e]
    · rw [e]; exact hcs w hw
  obtain ⟨w₀, hw₀, hw₀'⟩ := (hInf.diff (Bd ∪ Bd.image cPl).finite_toSet).nonempty
  have hn₀ : w₀ ∉ Bd := fun h => hw₀' (by simp [h])
  have hn₁ : cPl w₀ ∉ Bd := fun h => hw₀' (by
    refine Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, h, (hc w₀).1⟩)))
  obtain ⟨w₁, hw₁, hw₁S, hw₁s⟩ : ∃ w₁, w₁ ∉ Bd ∧ w₁ ∈ S ∧ IsSplitAt w₁ := by
    refine ⟨m w₀, ?_, (hm w₀).1, hms w₀ hw₀⟩
    rcases (hm w₀).2 with e | e <;> rwa [e]
  choose! B hB using fun w (h : ∃ B, (CG.mk π).HasSat w B) => h
  choose τ hτ using fun w => GlobalTheory.CuspRep.LocEx.exists_isLocComp hF E n π w
  obtain ⟨b, hb⟩ := (hgood w₁ hw₁).1.1
  obtain ⟨g, h1, h2, h3⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.regFn E n w₁ (τ w₁) b
    (((GlobalTheory.Cong.satake_locComp E n π w₁ (τ w₁) (hτ w₁).1).1 b).1 hb)
  refine ⟨insert w₁ (Bd.image m), B, τ, w₁, g, fun w hw => ?_, fun w hw hwZ => ?_, fun w hw => ?_,
    fun w _ => (hτ w).1, Finset.mem_insert_self _ _, h1, h2, h3⟩
  · rcases Finset.mem_insert.1 hw with rfl | h
    · exact ⟨hw₁S, hw₁s⟩
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
      exact ⟨(hm u).1, hms u (hsplit u hu)⟩
  · refine (hgood w fun h => hwZ ?_).2
    have hi : m w ∈ insert w₁ (Bd.image m) := Finset.mem_insert_of_mem (Finset.mem_image_of_mem m h)
    rwa [hmS w hw] at hi
  · have hw' : w ∉ Bd := fun h => by
      have hi : m w ∈ insert w₁ (Bd.image m) := Finset.mem_insert_of_mem (Finset.mem_image_of_mem m h)
      rcases (hm w).2 with e | e
      · exact hw.1 (e ▸ hi)
      · exact hw.2 (e ▸ hi)
    exact ⟨hB w (hgood w hw').1.1, (hgood w hw').1.2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.CpUniq
section
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun

private theorem trc_of_equiv {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} (e : ρ.Equiv ρ') (K : Subgroup G) (f : G → ℂ) :
    trc ρ K f = trc ρ' K f := by
  have hid : e.toLinearEquiv.toLinearMap ∘ₗ LinearMap.id ∘ₗ e.toLinearEquiv.symm.toLinearMap = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    exact e.toLinearEquiv.apply_symm_apply v
  have h := GlobalTheory.BCT.twTr_conj_equiv G V V' ρ ρ' e K (K ⊓ GlobalTheory.BCT.rStab f ⊓ GlobalTheory.BCT.rStab fun y => f y⁻¹) f LinearMap.id
  rw [hid] at h
  exact h.symm

section Split

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}

private theorem mem_UL (hw : IsSplitAt w) (g : GLw n w) : g ∈ UL n w := by
  rw [UL, if_pos hw]
  trivial

private noncomputable def toUL (hw : IsSplitAt w) (τ : SmIrr (GLw n w)) : SmIrr (UL n w) where
  V := τ.V
  ρ := τ.ρ.comp (UL n w).subtype
  smooth v := (τ.smooth v).preimage continuous_subtype_val
  irred := by
    obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 τ.irred
    exact (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g x hx => hW ⟨g, mem_UL hw g⟩ x hx⟩

private theorem isCompU_toUL (hw : IsSplitAt w) {σ : Submodule ℂ (UA E n → ℂ)} {τ : SmIrr (GLw n w)} (h : Cp σ w τ) :
    IsCompU σ w (toUL hw τ) := by
  obtain ⟨-, F, hF0, hFσ, hF⟩ := h
  refine ⟨{ toFun := fun x => ⟨cLoc w x.1, mem_UL hw _⟩
            map_one' := Subtype.ext (by simp)
            map_mul' := fun a b => Subtype.ext (by simp) }, fun _ => rfl, (toUL hw τ).irred, F, hF0, hFσ, fun x v => hF x v⟩

private noncomputable def equivOfUL (hw : IsSplitAt w) {τ τ' : SmIrr (GLw n w)} (e : (toUL hw τ).ρ.Equiv (toUL hw τ').ρ) : τ.ρ.Equiv τ'.ρ :=
  Representation.Equiv.mk e.toLinearEquiv fun g => e.isIntertwining' ⟨g, mem_UL hw g⟩

end Split

theorem UpperTheory.V.Z.Mult.cpUniq :
    UpperTheory.V.Z.Mult.CpUniq := by
  intro E _ _ _ hU n hn σ hσ w hw τ τ' h h'
  obtain ⟨e⟩ := (_root_.GlobalTheory.BCT.LocCompU.exists_unique_locComp E hU n hn σ hσ w).2 (toUL hw τ) (toUL hw τ') (isCompU_toUL hw h) (isCompU_toUL hw h')
  have e' := equivOfUL hw e
  exact ⟨fun B hB => GlobalTheory.PrinSat.hasSatGL_of_equiv e'.symm hB, fun f => trc_of_equiv e' _ f⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.GeomTr
section
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical

theorem UpperTheory.V.Z.Mult.geomTr :
    UpperTheory.V.Z.Mult.GeomTr := by
  intro E _ _ _ hU n hn S hS lam K' hK'
  refine ⟨dimW_ne_zero lam, fun f hf hsep => ?_⟩
  have hOrb : geomURat lam (fun γ => twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f)) =
      geomURat lam (fun γ => ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w)) := by
    unfold geomURat
    refine finsum_congr fun c => ?_
    split_ifs with hc
    · exact congrArg (_ * ·) (_root_.GlobalTheory.BCT.twOrb_globFn_eq_finprod E hU n hn S hS K' hK' f hf c.rep hc)
    · rfl
  rw [_root_.GlobalTheory.BCT.trOn_forms_hop_eq_geom E hU n hn S hS lam K' hK' f hf hsep, hOrb,
    GlobalTheory.PreStabU.geomURat_eq_geomU E hU n hn S hS lam K' hK' f hf hsep]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.IsDecOfGlobLev
section
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Mult

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem isDec_of_globLev {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n}
    {K₁ K₂ : ∀ w : Pl E, Subgroup (UL n w)} (h : globLev S K₁ = globLev S K₂) {ι : Type}
    {σ : ι → Submodule ℂ (UA E n → ℂ)} (hd : IsDec S lam K₁ σ) : IsDec S lam K₂ σ := by
  have hf : forms S lam K₁ = forms S lam K₂ := by
    unfold forms
    rw [h]
  unfold IsDec at hd ⊢
  rw [← hf, ← h]
  exact hd

private theorem isHecke_mono {G : Type} [Group G] [TopologicalSpace G] {K₁ K₂ : Subgroup G} (hle : K₁ ≤ K₂) {f : G → ℂ}
    (h : IsHecke K₂ f) : IsHecke K₁ f :=
  ⟨h.1, fun k hk x => h.2 k (hle hk) x⟩

private theorem fixed_equiv {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} (e : ρ.Equiv ρ') (φ : H →* G) (K : Subgroup H)
    (h : fixed (ρ.comp φ) K ≠ ⊥) : fixed (ρ'.comp φ) K ≠ ⊥ := by
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨e x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, fun h1 => h0 ?_⟩
  · have h2 := GlobalTheory.LGrp.mem_fixed.1 hx k hk
    have h3 : e (ρ (φ k) x) = ρ' (φ k) (e x) := LinearMap.congr_fun (e.isIntertwining' (φ k)) x
    have h2' : ρ (φ k) x = x := h2
    change ρ' (φ k) (e x) = e x
    rw [← h3, h2']
  · exact e.toLinearEquiv.map_eq_zero_iff.1 h1

end UpperTheory.V.Z.Mult

theorem UpperTheory.V.Z.Mult.rMult :
    UpperTheory.V.Z.Mult.RMult := by
  intro hId hCA hLT hGT hLI hLc hCh hOS hMu E _ _ _ hU n hn hn4 lam
  obtain ⟨a, ha, hA⟩ := hId E hU n hn hn4 lam
  obtain ⟨μ, e, hμ⟩ := hMu E hU
  have key : ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π →
      (∀ v, π.HasInfChar v.embedding (infOfWeight (lam v))) → (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
      ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w),
      IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → (∀ w, ¬ IsSplitAt w → K' w = KL n w) →
      (∀ w ∈ S, IsSplitAt w → ∃ τ, π.IsLocComp w τ ∧ fixed (τ.ρ.comp (UL n w).subtype) (K' w) ≠ ⊥) →
      ∀ (ι : Type) [Fintype ι] (σ : ι → Submodule ℂ (UA E n → ℂ)), IsDec S lam K' σ →
      (Nat.card {i // At π (σ i)} : ℝ) = a := by
    intro π hreg hdual hinf hunr S hS K' hK' hKn hfix ι _ σ hDec
    obtain ⟨Z, B, τ, w₀, f₀, hZ, hZK, hoff, hτ, hw₀, hf₀, htr₀, hsep⟩ := hCh E n hn π hunr μ e hμ S hS K' hK' hKn
    have hKLo : ∀ w, IsOpen (KL n w : Set (UL n w)) := fun w => (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).1
    obtain ⟨K₀, hK₀o, hK₀le, hK₀⟩ := hLc E n w₀ (hZ w₀ hw₀).2 f₀ hf₀
    obtain ⟨K₁, hK₁Z, hK₁o⟩ : ∃ K₁ : ∀ w : Pl E, Subgroup (UL n w), (∀ w ∈ Z, K₁ w = K' w) ∧ ∀ w, w ∉ Z → K₁ w = KL n w :=
      ⟨fun w => if w ∈ Z then K' w else KL n w, fun w h => if_pos h, fun w h => if_neg h⟩
    have hK₁ : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K₁ := by
      refine ⟨fun w => ?_, ?_⟩
      · by_cases h : w ∈ Z
        · rw [hK₁Z w h]
          exact hK'.1 w
        · rw [hK₁o w h]
          exact ⟨hKLo w, le_rfl, fun k hk => hk⟩
      · refine eventually_cofinite.2 (Z.finite_toSet.subset fun w hw => ?_)
        by_contra h
        exact hw (hK₁o w h)
    obtain ⟨K₂, hK₂w, hK₂⟩ : ∃ K₂ : ∀ w : Pl E, Subgroup (UL n w), K₂ w₀ = K₁ w₀ ⊓ K₀ ∧ ∀ w, w ≠ w₀ → K₂ w = K₁ w :=
      ⟨Function.update K₁ w₀ (K₁ w₀ ⊓ K₀), Function.update_self _ _ _, fun w h => Function.update_of_ne h _ _⟩
    have hle : ∀ w, K₂ w ≤ K₁ w := fun w => by
      by_cases h : w = w₀
      · subst h
        rw [hK₂w]
        exact inf_le_left
      · rw [hK₂ w h]
    have hK₂o : ∀ w, w ∉ Z → K₂ w = KL n w := fun w h => by
      rw [hK₂ w (fun e => h (e ▸ hw₀)), hK₁o w h]
    have hK₂L : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K₂ := by
      refine ⟨fun w => ?_, ?_⟩
      · by_cases h : w = w₀
        · subst h
          rw [hK₂w]
          refine ⟨?_, inf_le_left.trans (hK₁.1 w).2.1, fun k hk => hk⟩
          rw [Subgroup.coe_inf]
          exact (hK₁.1 w).1.inter hK₀o
        · rw [hK₂ w h]
          exact hK₁.1 w
      · refine eventually_cofinite.2 (Z.finite_toSet.subset fun w hw => ?_)
        by_contra h
        exact hw (hK₂o w h)
    have hg1 : globLev S K' = globLev S K₁ := hOS E n S K' K₁ fun w hw => by
      by_cases h : w ∈ Z
      · exact (hK₁Z w h).symm
      · rw [hK₁o w h]
        exact hZK w hw h
    have hDec₁ : IsDec S lam K₁ σ := isDec_of_globLev hg1 hDec
    obtain ⟨-, ι₂, _, σ₂, d1, d2, d3, -⟩ := _root_.GlobalTheory.BCT.forms_decomp E hU n hn S hS lam K₂ hK₂L
    have hDec₂ : IsDec S lam K₂ σ₂ := ⟨d1, d2, d3⟩
    have hfx : ∀ w ∈ Z, fixed ((τ w).ρ.comp (UL n w).subtype) (K₁ w) ≠ ⊥ := fun w hw => by
      obtain ⟨t, ht, hne⟩ := hfix w (hZ w hw).1 (hZ w hw).2
      obtain ⟨eq⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique π w t (τ w) ht (hτ w hw)
      rw [hK₁Z w hw]
      exact fixed_equiv eq _ _ hne
    have hg : ∀ w : Pl E, ∃ g : GLw n w → ℂ, w ∈ Z → Lc (KGL w (n := n)) g ∧
        (∀ K ≤ K₁ w, IsHecke K fun x : UL n w => g x.1) ∧ trc (τ w).ρ (KGL w (n := n)) g ≠ 0 := fun w => by
      by_cases hw : w ∈ Z
      · obtain ⟨g, h1, h2, h3⟩ := hLI E n w (hZ w hw).2 (K₁ w) (hK₁.1 w).1 (hK₁.1 w).2.1
        exact ⟨g, fun _ => ⟨h1, h2, h3 _ (hfx w hw)⟩⟩
      · exact ⟨0, fun h => absurd h hw⟩
    choose g hg using hg
    have hc₂ : (Nat.card {i // At π (σ₂ i)} : ℝ) = a := by
      refine hA π hreg hdual hinf μ e hμ S hS Z hZ B τ (Function.update g w₀ f₀) hoff
        (fun w hw => ⟨hτ w hw, ?_⟩) ⟨w₀, hw₀, ?_⟩ K₂ hK₂L hK₂o (fun w hw => ?_) ι₂ σ₂ hDec₂
      · by_cases h : w = w₀
        · subst h
          rw [Function.update_self]
          exact ⟨hf₀, htr₀⟩
        · rw [Function.update_of_ne h]
          exact ⟨(hg w hw).1, (hg w hw).2.2⟩
      · rw [Function.update_self]
        exact hsep
      · by_cases h : w = w₀
        · subst h
          rw [Function.update_self, hK₂w]
          exact isHecke_mono inf_le_right hK₀
        · rw [Function.update_of_ne h, hK₂ w h]
          exact (hg w hw).2.1 _ le_rfl
    obtain ⟨J, _, C, hC, hF⟩ := hCA E hU n hn hn4 π hreg hdual S hS lam Z hZ B τ (fun w h => (hoff w h).1) hτ
      K₁ hK₁ hK₁o ι σ hDec₁
    obtain ⟨J', _, C', hC', hF'⟩ := hCA E hU n hn hn4 π hreg hdual S hS lam Z hZ B τ (fun w h => (hoff w h).1) hτ
      K₂ hK₂L hK₂o ι₂ σ₂ hDec₂
    obtain ⟨T, e₁, e₂, hT, hd, h1, h0⟩ := rSep places E n S hS Z (J ⊕ J') B (Sum.elim C C')
      (by rintro (j | j); exacts [hC j, hC' j])
    have hh₁ : ∀ w ∈ Z, IsHecke (K₁ w) fun x : UL n w => g w x.1 := fun w hw => (hg w hw).2.1 _ le_rfl
    have hh₂ : ∀ w ∈ Z, IsHecke (K₂ w) fun x : UL n w => g w x.1 := fun w hw => (hg w hw).2.1 _ (hle w)
    obtain ⟨t₁, r₁⟩ := hF g hh₁ T hT hd e₁ e₂ h1 (fun j => h0 (Sum.inl j)) 1
    obtain ⟨-, r₂⟩ := hF' g hh₂ T hT hd e₁ e₂ h1 (fun j => h0 (Sum.inr j)) 1
    have hlt := hLT E hU n hn S hS lam K₁ K₂ hK₁ hK₂L hle _ t₁
    have hd0 := (hGT E hU n hn S hS lam K₁ hK₁).1
    have hP : ∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) (g w) ≠ 0 := Finset.prod_ne_zero_iff.2 fun w hw => (hg w hw).2.2
    have heq := (r₂ le_rfl).symm.trans (hlt.trans (r₁ le_rfl))
    have hcc := mul_right_cancel₀ hP (mul_left_cancel₀ hd0 heq)
    have hc : Nat.card {i // At π (σ i)} = Nat.card {i // At π (σ₂ i)} := by exact_mod_cast hcc.symm
    rw [hc]
    exact hc₂
  by_cases hN : ∃ m : ℕ, (m : ℝ) = a
  · obtain ⟨m, rfl⟩ := hN
    refine ⟨m, by exact_mod_cast ha, fun π h1 h2 h3 h4 S hS K' hK h5 h6 ι _ σ hd => ?_⟩
    exact_mod_cast key π h1 h2 h3 h4 S hS K' hK h5 h6 ι σ hd
  · exact ⟨1, one_pos, fun π h1 h2 h3 h4 S hS K' hK h5 h6 ι _ σ hd =>
      absurd ⟨_, key π h1 h2 h3 h4 S hS K' hK h5 h6 ι σ hd⟩ hN⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.LcLev
section
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryBC GlobalTheory.LFun Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.PRep

theorem UpperTheory.V.Z.Mult.lcLev :
    UpperTheory.V.Z.Mult.LcLev := by
  intro E _ _ _ n w hw f hf
  obtain ⟨K', hKo, hKle, hK⟩ := hf
  have hU : UL n w = ⊤ := if_pos hw
  have hcl : IsClosed ((UL n w : Subgroup (GLw n w)) : Set (GLw n w)) := by
    rw [hU]
    exact isClosed_univ
  refine ⟨K'.subgroupOf (UL n w), hKo.preimage continuous_subtype_val, ?_, ?_, ?_⟩
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hKle (Subgroup.mem_subgroupOf.mp hx))
  · exact hK.1.comp_isClosedEmbedding hcl.isClosedEmbedding_subtypeVal
  · intro k hk x
    exact hK.2 k.1 (Subgroup.mem_subgroupOf.mp hk) x.1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.OffSec
section
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem UpperTheory.V.Z.Mult.offSec :
    UpperTheory.V.Z.Mult.OffSec := by
  intro E _ _ _ n S K' K'' h
  unfold GlobalTheory.BCT.globLev
  refine iInf_congr fun w => iInf_congr fun hw => ?_
  rw [h w hw]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.GeometricTraces.RCountAt
section
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open NumberField IsDedekindDomain Filter GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Af.Bc (cPl)

theorem UpperTheory.V.Z.Mult.rCountAt :
    UpperTheory.V.Z.Mult.RCountAt := by
  classical
  intro hC hEv hCp hP E _ _ _ hU n hn1 hn4 π hreg hd S hS lam Z hZ B τ hB hτ K' hK' hKZ ι _ σ hdec
  obtain ⟨t, Bi, hi, hev⟩ := hEv E hU n hn1 S hS lam Z hZ K' hK' hKZ ι σ hdec
  obtain ⟨-, hc, -, hSec⟩ := hP E
  have hF := UpperTheory.V.Af.formsFiniteGL
  have hsat : ∀ w, Off Z w → ∃ τ₀ : SmIrr (GLw n w), π.IsLocComp w τ₀ ∧ HasSatGL w τ₀.ρ (B w) := fun w hw => by
    obtain ⟨τ₀, h₀⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp hF E n π w
    exact ⟨τ₀, h₀.1, ((GlobalTheory.Cong.satake_locComp E n π w τ₀ h₀.1).1 _).1 (hB w hw)⟩
  have hAt : ∀ i, (∀ w, Off Z w → IsSplitAt w → Bi i w = B w) → At π (σ i) := fun i h => by
    filter_upwards [off_cofinite hP Z] with w hw hs
    obtain ⟨τ', h1, h2⟩ := (hi i).2.2 w hw hs
    exact ⟨τ', B w, h1, h w hw hs ▸ h2, hB w hw⟩
  have hCo : ∀ i, At π (σ i) → ∀ w, IsSplitAt w → ∀ τ₀, π.IsLocComp w τ₀ → Cp (σ i) w τ₀ := fun i h =>
    hC E hU n hn1 hn4 π hreg hd (σ i) (hdec.1 i).1 (hi i).1 h
  have hEq : ∀ i, At π (σ i) → ∀ w, Off Z w → IsSplitAt w → Bi i w = B w := fun i h w hw hs => by
    obtain ⟨τ', h1, h2⟩ := (hi i).2.2 w hw hs
    obtain ⟨τ₀, h₀, s₀⟩ := hsat w hw
    exact HasSatGL.unique h2 ((hCp E hU n hn1 (σ i) (hdec.1 i).1 w hs τ₀ τ' (hCo i h w hs τ₀ h₀) h1).1 _ s₀)
  refine ⟨{i // ¬ At π (σ i)}, inferInstance, fun j => Bi j.1, fun j => ?_, ?_⟩
  · by_contra hno
    refine j.2 (hAt j.1 fun w hw hs => ?_)
    by_contra hne
    obtain ⟨τ', -, h2⟩ := (hi j.1).2.2 w hw hs
    obtain ⟨τ₀, -, s₀⟩ := hsat w hw
    exact hno ⟨w, hw, hs, HasSatGL.card s₀, HasSatGL.card h2, hne⟩
  · intro f hf T hT hTZ e₁ e₂ h1 h0 k
    obtain ⟨htest, htr⟩ := hev f hf T hT hTZ e₁ e₂ k
    refine ⟨htest, fun hk => ?_⟩
    have hoffT : ∀ w ∈ T, Off Z w ∧ IsSplitAt w := fun w hw => by
      have hnZ : ∀ {u}, u ∈ T → u ∉ Z := fun hu hu' => Finset.disjoint_left.1 hTZ hu hu'
      refine ⟨⟨hnZ hw, fun h => ?_⟩, (hT w hw).2⟩
      exact ((hc w).2.1 (hT w hw).2) ((hSec S hS w).2 (hT w hw).1 (hZ _ h).1)
    have hval : ∀ i, At π (σ i) → val1 T e₁ e₂ (Bi i) = 1 := fun i h => by
      rw [← h1]
      refine Finset.prod_congr rfl fun w hw => ?_
      obtain ⟨⟨ha, hb⟩, hs⟩ := hoffT w hw
      have hcs : IsSplitAt (cPl w) := (hc (cPl w)).2.2 (by rw [(hc w).1]; exact ((hc w).2.1 hs).symm)
      have ho : Off Z (cPl w) := ⟨hb, by rwa [(hc w).1]⟩
      rw [hEq i h w ⟨ha, hb⟩ hs, hEq i h _ ho hcs]
    have hterm : ∀ i, (∏ w ∈ Z, trc (t i w).ρ (KGL w (n := n)) (f w)) * val1 T e₁ e₂ (Bi i) ^ k =
        (if At π (σ i) then 1 else 0) * ∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) (f w) := fun i => by
      by_cases h : At π (σ i)
      · rw [if_pos h, hval i h, one_pow, mul_one, one_mul]
        refine Finset.prod_congr rfl fun w hw => ?_
        exact ((hCp E hU n hn1 (σ i) (hdec.1 i).1 w (hZ w hw).2 (τ w) (t i w)
          (hCo i h w (hZ w hw).2 _ (hτ w hw)) ((hi i).2.1 w hw)).2 (f w)).symm
      · rw [if_neg h, h0 ⟨i, h⟩, zero_pow (by omega), mul_zero, zero_mul]
    rw [htr, Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_mul, Finset.sum_boole, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
end

