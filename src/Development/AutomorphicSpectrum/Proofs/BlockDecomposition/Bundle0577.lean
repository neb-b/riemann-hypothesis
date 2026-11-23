module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0552
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0459
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0208
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0475
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriOrbitalSupport
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.DiagCoset

theorem v_eq_of_ne {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L} (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ordL
  rw [dite_eq_right h0]
  simp

theorem diagT_mem_iwGL {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ)
    (τ : Fin n → (w.adicCompletion E)ˣ) (hτ : ∀ i, Valued.v (τ i : w.adicCompletion E) = 1) :
    GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ ∈ iwGL n w := by
  have hinv : ∀ i, Valued.v ((τ⁻¹) i : w.adicCompletion E) = 1 := by
    intro i
    have : (((τ⁻¹) i : (w.adicCompletion E)ˣ) : w.adicCompletion E) = (τ i : w.adicCompletion E)⁻¹ := by
      simp
    rw [this, map_inv₀, hτ, inv_one]
  have hle : ∀ (ρ : Fin n → (w.adicCompletion E)ˣ), (∀ i, Valued.v (ρ i : w.adicCompletion E) = 1) →
      ∀ i j, Valued.v ((GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) ρ).val i j) ≤ 1 := by
    intro ρ hρ i j
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, hρ]
    · rw [Matrix.diagonal_apply_ne _ h, map_zero]
      exact zero_le'
  refine ((GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1).2 ⟨hle τ hτ, ?_, ?_⟩
  · rw [← map_inv]
    exact hle _ hinv
  · intro i j hij
    rw [GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_ne _ (ne_of_gt hij), map_zero]
    exact zero_lt_one

theorem fU_diag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ → ∀ (l : Fin (n / 2) → ℤ), Cone l → ∀ (γ : UL n w) (u : Fin n → (w.adicCompletion E)ˣ), (∀ i, ordL (u i : w.adicCompletion E) = wexp n l i) → γ.1 = b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ → ∀ x ∈ iwU n w b, ∀ z ∈ iwU n w b, fU n w b ϖ l (x * γ * z) = 1 := by
  intro E _ _ _ hU w hw n b hb ϖ hϖ l hl γ u hu hγ x hx z hz
  obtain ⟨hUL, hiw, -, hdiag⟩ := GlobalTheory.CompanionTheory.UnitaryWitt.unitary_hyperbolic_basis E hU w hw n b hb
  have hrev := (GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev n l hl).2

  set τ : Fin n → (w.adicCompletion E)ˣ := fun i => u i * (ϖ ^ wexp n l i)⁻¹ with hτdef
  have hvϖ : Valued.v (ϖ : w.adicCompletion E) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [v_eq_of_ne ϖ.ne_zero, hϖ.1]
  have hvpow : ∀ d : ℤ, Valued.v (((ϖ ^ d : (w.adicCompletion E)ˣ)) : w.adicCompletion E) =
      ((Multiplicative.ofAdd (-d) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro d
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hvϖ, ← WithZero.coe_zpow, ← ofAdd_zsmul]
    simp
  have hτ : ∀ i, Valued.v (τ i : w.adicCompletion E) = 1 := by
    intro i
    have e : ((τ i : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        (u i : w.adicCompletion E) * (((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E)⁻¹ := by
      simp [hτdef]
    rw [e, map_mul, map_inv₀, hvpow, v_eq_of_ne (u i).ne_zero, hu i]
    exact mul_inv_cancel₀ WithZero.coe_ne_zero
  have hfac : GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u =
      tdiag ϖ (wexp n l) * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ := by
    rw [tdiag, ← map_mul]
    congr 1
    funext i
    simp [hτdef]

  have hu1 : ∀ i, cj w (u i : w.adicCompletion E) * (u (Fin.rev i) : w.adicCompletion E) = 1 := by
    have h1 : b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u * b⁻¹ ∈ UL n w := hγ ▸ γ.2
    exact (hdiag u).1 ((hUL _).1 h1)
  have hcjϖ : ∀ d : ℤ, cj w (((ϖ ^ d : (w.adicCompletion E)ˣ)) : w.adicCompletion E) =
      ((ϖ ^ d : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    intro d
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ.2]
  have hτ1 : ∀ i, cj w (τ i : w.adicCompletion E) * (τ (Fin.rev i) : w.adicCompletion E) = 1 := by
    intro i
    have e : ∀ j, ((τ j : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        (u j : w.adicCompletion E) * (((ϖ ^ wexp n l j : (w.adicCompletion E)ˣ)) : w.adicCompletion E)⁻¹ := by
      intro j
      simp [hτdef]
    rw [e, e, map_mul, map_inv₀, hcjϖ, hrev i, _root_.zpow_neg]
    have h2 := hu1 i
    have hp : (((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E) ≠ 0 := Units.ne_zero _
    simp only [Units.val_inv_eq_inv_val, inv_inv]
    calc _ = (cj w (u i : w.adicCompletion E) * (u (Fin.rev i) : w.adicCompletion E)) *
          ((((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E)⁻¹ *
            (((ϖ ^ wexp n l i : (w.adicCompletion E)ˣ)) : w.adicCompletion E)) := by ring
      _ = 1 := by rw [h2, inv_mul_cancel₀ hp, one_mul]
  have hκU : b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ * b⁻¹ ∈ UL n w :=
    (hUL _).2 ((hdiag τ).2 hτ1)
  let κ : UL n w := ⟨_, hκU⟩
  have hκ : κ ∈ iwU n w b := by
    rw [hiw]
    have : b⁻¹ * κ.1 * b = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ := by
      change b⁻¹ * (b * _ * b⁻¹) * b = _
      group
    rw [this]
    exact diagT_mem_iwGL w n τ hτ
  unfold fU
  refine if_pos ⟨x, hx, κ * z, mul_mem hκ hz, ?_⟩
  change x.1 * γ.1 * z.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * ((b * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) τ * b⁻¹) * z.1)
  rw [hγ, hfac]
  group

end GlobalTheory.CompanionTheory.DiagCoset
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwLevels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem KGL_eq_KO (w : Pl E) (n : ℕ) :
    GlobalTheory.LFun.KGL w (n := n) = GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) := by
  ext g
  rw [GlobalTheory.CompanionTheory.IwEntries.mem_KGL_iff, GlobalTheory.CompanionTheory.IwEntries.mem_KO_iff]

theorem isCompact_KGL (w : Pl E) (n : ℕ) : IsCompact (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) := by
  rw [KGL_eq_KO]
  exact GlobalTheory.SplitFlip.isCompact_KO

theorem iwGL_le_KGL (w : Pl E) (n : ℕ) : iwGL n w ≤ GlobalTheory.LFun.KGL w (n := n) := by
  rw [KGL_eq_KO]
  exact GlobalTheory.SmGL.iwahori_le_KO _ _

theorem isClosed_UL {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (hc : Continuous (cj w)) :
    IsClosed (UL n w : Set (GLw n w)) := by
  rw [GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]
  exact GlobalTheory.CompanionTheory.UnitaryWitt.isClosed_UJ_one n hc

theorem isOpen_KL (n : ℕ) (w : Pl E) : IsOpen (KL n w : Set (UL n w)) := by
  have h : IsOpen (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) := by
    rw [KGL_eq_KO]
    exact GlobalTheory.SplitFlip.isOpen_KO
  exact h.preimage (continuous_subtype_val (p := (· ∈ UL n w)))

theorem isCompact_KL {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (hc : Continuous (cj w)) :
    IsCompact (KL n w : Set (UL n w)) :=
  (isClosed_UL hw n hc).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_KGL w n)

theorem isOpen_iwU (n : ℕ) (w : Pl E) (b : GLw n w) : IsOpen (iwU n w b : Set (UL n w)) := by
  have ho : IsOpen (iwGL n w : Set (GLw n w)) :=
    GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin n)
  have hcont : Continuous fun γ : UL n w => b⁻¹ * γ.1 * b :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  have e : (iwU n w b : Set (UL n w)) = (fun γ : UL n w => b⁻¹ * γ.1 * b) ⁻¹' (iwGL n w : Set (GLw n w)) := by
    ext γ
    exact GlobalTheory.CompanionTheory.UnitaryWitt.mem_iwU_iff n w b γ
  rw [e]
  exact ho.preimage hcont

theorem iwU_le_KL (n : ℕ) (w : Pl E) (b : GLw n w) (hb : b ∈ GlobalTheory.LFun.KGL w (n := n)) :
    iwU n w b ≤ KL n w := by
  intro γ hγ
  have h1 := iwGL_le_KGL w n ((GlobalTheory.CompanionTheory.UnitaryWitt.mem_iwU_iff n w b γ).1 hγ)
  have h2 : γ.1 = b * (b⁻¹ * γ.1 * b) * b⁻¹ := by group
  rw [KL, Subgroup.mem_subgroupOf, h2]
  exact mul_mem (mul_mem hb h1) (inv_mem hb)

theorem relIndex_ne_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H K : Subgroup G}
    (hH : IsOpen (H : Set G)) (hK : IsCompact (K : Set G)) : H.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let U : OpenSubgroup K := ⟨H.subgroupOf K, hH.preimage continuous_subtype_val⟩
  haveI : Finite (K ⧸ (U : Subgroup K)) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
  exact Subgroup.index_ne_zero_of_finite

theorem isCompact_support_fU {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w)
    (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ) (hc : Continuous (cj w)) :
    IsCompact {g : UL n w | fU n w b ϖ l g ≠ 0} := by
  set t : GLw n w := b * tdiag ϖ (wexp n l) * b⁻¹ with ht
  have hI : IsCompact (iwU n w b : Set (UL n w)) :=
    GlobalTheory.CompanionTheory.UnitaryWitt.isCompact_iwU hw n b hc
  have hS : IsCompact ((fun p : UL n w × UL n w => p.1.1 * t * p.2.1) ''
      ((iwU n w b : Set (UL n w)) ×ˢ (iwU n w b : Set (UL n w)))) :=
    (hI.prod hI).image (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
      (continuous_subtype_val.comp continuous_snd))
  have e : {g : UL n w | fU n w b ϖ l g ≠ 0} = Subtype.val ⁻¹'
      ((fun p : UL n w × UL n w => p.1.1 * t * p.2.1) ''
        ((iwU n w b : Set (UL n w)) ×ˢ (iwU n w b : Set (UL n w)))) := by
    ext γ
    simp only [Set.mem_setOf_eq, fU, Set.mem_preimage, Set.mem_image, Set.mem_prod, SetLike.mem_coe]
    constructor
    · intro h
      by_contra hn
      refine h (if_neg ?_)
      rintro ⟨x, hx, z, hz, e⟩
      exact hn ⟨(x, z), ⟨hx, hz⟩, e.symm⟩
    · rintro ⟨⟨x, z⟩, ⟨hx, hz⟩, e⟩
      rw [if_pos ⟨x, hx, z, hz, e.symm⟩]
      exact one_ne_zero
  rw [e]
  exact (isClosed_UL hw n hc).isClosedEmbedding_subtypeVal.isCompact_preimage hS

theorem levels_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ), IsUnifAt ϖ → Cone l → IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧ IsLevel (MonoidHom.id _) (KL n w) (iwU n w b) ∧ (iwU n w b).relIndex (KL n w) ≠ 0 ∧ IsCompact {g : UL n w | fU n w b ϖ l g ≠ 0} := by
  intro E _ _ _ hU w hw n b hb ϖ l _ _
  have hc : Continuous (cj w) := (_root_.GlobalTheory.ConjAtPlace.main E hU w).1
  exact ⟨isOpen_KL n w, isCompact_KL hw n hc,
    ⟨isOpen_iwU n w b, iwU_le_KL n w b hb.1, fun k hk => hk⟩,
    relIndex_ne_zero (isOpen_iwU n w b) (isCompact_KL hw n hc),
    isCompact_support_fU hw n b ϖ l hc⟩

end GlobalTheory.CompanionTheory.IwLevels
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockInjectiveIrreducible
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

namespace GlobalTheory.CompanionTheory.BZNuPair.WhitSub

theorem exists_injective_of_subQuot_bot {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} (hσ : σ.IsIrreducible) {ρ : Representation ℂ G V}
    (A B : Subrepresentation ρ) (hB : B = ⊥) (f : σ.IntertwiningMap (subQuot A B))
    (hf : f.toLinearMap ≠ 0) : ∃ g : σ.IntertwiningMap ρ, Function.Injective g := by
  subst hB
  have hle : (⊥ : Subrepresentation ρ).toSubmodule.comap A.toSubmodule.subtype ≤
      LinearMap.ker A.toSubmodule.subtype := fun v hv => by
    have : (v : V) ∈ (⊥ : Subrepresentation ρ).toSubmodule := hv
    exact this
  let p : (subQuot A ⊥).IntertwiningMap ρ :=
    .mk (Submodule.liftQ _ A.toSubmodule.subtype hle) (fun g => by
      ext v
      rfl)
  have hp : Function.Injective p := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).2 hx
  have hi : Function.Injective (p.comp f) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    rcases eq_bot_or_eq_top (p.comp f).ker with h | h
    · have : x ∈ (p.comp f).ker := hx
      rw [h] at this
      exact this
    · exfalso
      refine hf (LinearMap.ext fun y => ?_)
      have hy : y ∈ (p.comp f).ker := by rw [h]; trivial
      exact hp (by simpa using hy)
  exact ⟨p.comp f, hi⟩

theorem exists_irr_sub : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (d : Fin 2 → ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) X), IsSmooth J → HasFiniteLength J → Nontrivial (X ⧸ whitKer ψ d J) →
    ∃ (S : IrrRep (GL (Fin (d 0)) k)) (f : S.ρ.IntertwiningMap (whit2 ψ d J)), Function.Injective f := by
  intro k _ _ _ _ ψ _ d X _ _ J hs hfl hnt
  obtain ⟨hgt, hlt⟩ := (hasFiniteLength_iff_wellFounded J).1 hfl
  have hbotImg : whitImg ψ d J ⊥ = ⊥ := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.map_bot _
  have htop : whitImg ψ d J ⊤ ≠ ⊥ := by
    intro h
    have h1 : (whitImg ψ d J ⊤).toSubmodule = ⊤ := by
      show (⊤ : Subrepresentation J).toSubmodule.map (whitKer ψ d J).mkQ = ⊤
      exact (Submodule.map_top _).trans (Submodule.range_mkQ _)
    rw [h] at h1
    obtain ⟨x, hx⟩ := exists_ne (0 : X ⧸ whitKer ψ d J)
    have : x ∈ (⊥ : Subrepresentation (whit2 ψ d J)).toSubmodule := by rw [h1]; trivial
    exact hx this
  obtain ⟨T, hT, hmin⟩ := (wellFounded_lt (α := Subrepresentation J)).has_min
    {T | whitImg ψ d J T ≠ ⊥} ⟨⊤, htop⟩
  have hbot : (⊥ : Subrepresentation J) < T := by
    refine bot_lt_iff_ne_bot.2 fun h => hT ?_
    rw [h]
    exact hbotImg
  obtain ⟨T', hT', hmax⟩ := (wellFounded_gt (α := Subrepresentation J)).has_min
    {B | B < T} ⟨⊥, hbot⟩
  have hcov : T' ⋖ T := ⟨hT', fun C hBC hCA => hmax C hCA hBC⟩
  have hImg' : whitImg ψ d J T' = ⊥ := by
    by_contra h
    exact hmin T' h hT'
  let τ : IrrRep (Levi k fun a => Fin (d a)) :=
    ⟨_, subQuot T T', IsSubquotient.isSmooth ⟨T, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩ hs, isIrreducible_subQuot hcov⟩
  obtain ⟨s, ⟨Φ⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
    k (Fin 2) (fun a => Fin (d a)) τ
  have hspan := _root_.GlobalTheory.CompanionTheory.BZNuPair.WhitCover.main k ψ d X J T T' (fun a => (s a).V) (fun a => (s a).ρ) hT'.le Φ
  have hQ : Nontrivial ((whitImg ψ d J T).toSubmodule ⧸
      (whitImg ψ d J T').toSubmodule.comap (whitImg ψ d J T).toSubmodule.subtype) := by
    refine Submodule.Quotient.nontrivial_iff.2 fun h => hT ?_
    apply Subrepresentation.toSubmodule_injective
    refine le_antisymm (fun x hx => ?_) bot_le
    have hx' : (⟨x, hx⟩ : (whitImg ψ d J T).toSubmodule) ∈
        (whitImg ψ d J T').toSubmodule.comap (whitImg ψ d J T).toSubmodule.subtype := by
      rw [h]; trivial
    rw [Submodule.mem_comap, hImg'] at hx'
    exact hx'
  obtain ⟨f, hf⟩ : ∃ f : (s 0).ρ.IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')),
      f.toLinearMap ≠ 0 := by
    by_contra hno
    push_neg at hno
    have : (⨆ f : (s 0).ρ.IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')),
        LinearMap.range f.toLinearMap) = ⊥ := by
      refine le_antisymm (iSup_le fun f => ?_) bot_le
      rw [hno f, LinearMap.range_zero]
    rw [this] at hspan
    exact bot_ne_top hspan
  obtain ⟨g, hg⟩ := exists_injective_of_subQuot_bot (s 0).irr _ _ hImg' f hf
  exact ⟨s 0, g, hg⟩

end GlobalTheory.CompanionTheory.BZNuPair.WhitSub

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockSubquotientTensor
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

namespace GlobalTheory.CompanionTheory.BZNuPair

theorem whit2_isSubquotient_whitImg_top {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Type} [AddCommGroup X]
    [Module ℂ X] (J : Representation ℂ (Levi k fun a => Fin (d a)) X) :
    IsSubquotient (whit2 ψ d J) (whitImg ψ d J ⊤).toRepresentation := by
  let f : (whitImg ψ d J ⊤).toRepresentation.IntertwiningMap (whit2 ψ d J) :=
    ⟨(whitImg ψ d J ⊤).toSubmodule.subtype, fun _ => rfl⟩
  refine .of_surjective f fun w => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact ⟨⟨Submodule.Quotient.mk x, x, trivial, rfl⟩, rfl⟩

theorem not_isSubquotient_whitImg_bot {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X W : Type} [AddCommGroup X]
    [Module ℂ X] [AddCommGroup W] [Module ℂ W] (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    {σ : Representation ℂ (GL (Fin (d 0)) k) W} (hσ : σ.IsIrreducible) :
    ¬ IsSubquotient σ (whitImg ψ d J ⊥).toRepresentation := by
  rintro ⟨R, f, hf⟩
  have := nontrivial_of_irreducible hσ
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf w
  have hv : v = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨t, ht, h⟩ := v.1.2
    have ht0 : t = 0 := ht
    rw [← h, ht0]
    simp
  exact hw (by rw [hv, map_zero])

theorem exists_constituent_of_whit2 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (d : Fin 2 → ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) X), IsSmooth J → HasFiniteLength J → ∀ S : IrrRep (GL (Fin (d 0)) k),
    IsSubquotient S.ρ (whit2 ψ d J) → ∃ s : ∀ a, IrrRep (GL (Fin (d a)) k),
      IsSubquotient (piTensor fun a => (s a).ρ) J ∧ Nonempty ((s 0).ρ.Equiv S.ρ) := by
  intro k _ _ _ _ ψ _ d X _ _ J hs hfl S hS
  obtain ⟨hgt, hlt⟩ := (hasFiniteLength_iff_wellFounded J).1 hfl
  obtain ⟨T, hT, hmin⟩ := WellFounded.has_min hlt
    {T : Subrepresentation J | IsSubquotient S.ρ (whitImg ψ d J T).toRepresentation}
    ⟨⊤, hS.trans (whit2_isSubquotient_whitImg_top ψ d J)⟩
  have hne : T ≠ ⊥ := by
    rintro rfl
    exact not_isSubquotient_whitImg_bot ψ d J S.irr hT
  obtain ⟨T', hT'lt, hmax⟩ := WellFounded.has_min hgt {U : Subrepresentation J | U < T}
    ⟨⊥, bot_lt_iff_ne_bot.2 hne⟩
  have hcov : T' ⋖ T := ⟨hT'lt, fun c h1 h2 => hmax c h2 h1⟩
  have hq : IsSubquotient (subQuot T T') J :=
    ⟨T, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩
  let τ : IrrRep (Levi k fun a => Fin (d a)) :=
    ⟨_, subQuot T T', hq.isSmooth hs, isIrreducible_subQuot hcov⟩
  obtain ⟨s, ⟨Φ⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k (Fin 2)
    (fun a => Fin (d a)) τ
  have hspan := _root_.GlobalTheory.CompanionTheory.BZNuPair.WhitCover.main k ψ d X J T T' (fun a => (s a).V) (fun a => (s a).ρ) hT'lt.le Φ
  refine ⟨s, (IsSubquotient.of_surjective Φ.toIntertwiningMap Φ.surjective).trans hq, ?_⟩
  rcases _root_.GlobalTheory.CompanionTheory.SubquotExt.isSubquotient_sub_or_quot _ _ _ (whit2 ψ d J) S.ρ _ _ (whitImg_mono ψ d J hT'lt.le) S.irr hT with h | h
  · exact absurd hT'lt (hmin T' h)
  · obtain ⟨e⟩ := GlobalTheory.T.subquotient_equiv_of_irreducible_image _ _ _ _ (s 0).ρ _ S.ρ (s 0).irr S.irr hspan h
    exact ⟨e.symm⟩

end GlobalTheory.CompanionTheory.BZNuPair

end
end

