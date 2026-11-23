module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TsubValInjective
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.MemTensorFockOfCoeffs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0271
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberSheafEqSumLengthMulCycle
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SheafCycle

theorem dim_add_one_le {T : Type} [TopologicalSpace T] {A B : Set T} (hA : IsClosed A)
    (hAi : IsIrreducible A) (hBi : IsIrreducible B) (h : A ⊂ B) :
    topologicalKrullDim A + 1 ≤ topologicalKrullDim B :=
  GlobalTheory.T.topologicalKrullDim_add_one_le_of_irreducible_ssubset T A B hA hAi hBi h

theorem length_stalk_ne_top {X : Scheme.{0}} [IsLocallyNoetherian X] (F : X.Modules)
    [QCoh.IsFiniteQC F] (w : X) (h : ∀ y ∈ QCoh.support F, w ∈ closure {y} → y = w) :
    Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) ≠ ⊤ :=
  GlobalTheory.T.length_stalk_ne_infty_of_no_generization X F w h

theorem length_stalk_pushforward_generic {X : Scheme.{0}} (Z : Closeds X)
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme]
    (G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules) [QCoh.IsFiniteQC G] :
    Module.length (X.presheaf.stalk (redι Z (genericPoint _)))
      (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk (redι Z (genericPoint _)) :) =
      (GlobalTheory.VB.genRank G : ℕ∞) :=
  _root_.GlobalTheory.StalkLength.length_stalk_pushforward_genericPoint X Z G

theorem lt_of_add_one_le_natCast {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ n) : a < n := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have e : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) := rfl
      rw [e, top_add] at h
      have : ((⊤ : ℕ∞)) ≤ (n : ℕ∞) := by exact_mod_cast h
      exact ENat.natCast_ne_top n (top_le_iff.1 this)
    | coe m =>
      have : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ n := by exact_mod_cast h
      have : m + 1 ≤ n := by exact_mod_cast this
      exact_mod_cast (by omega : m < n)

open QCoh

variable {κ : Type} [Field κ] {X : Scheme.{0}} [Algebra κ Γ(X, ⊤)]

theorem length_stalk_eq_zero_of_notMem {F : X.Modules} {w : X} (h : w ∉ support F) :
    Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) = 0 := by
  haveI := notMem_support_iff.1 h
  exact Module.length_eq_zero

theorem dim_closure_le_suppDim {F : X.Modules} [IsFiniteQC F] {w : X} (h : w ∈ support F) :
    topologicalKrullDim (closure {w} : Set X) ≤ suppDim F := by
  rw [suppDim_eq_iSup_closure F]
  exact le_iSup₂ (f := fun x (_ : x ∈ support F) ↦ topologicalKrullDim (closure {x} : Set X)) w h

theorem eq_of_mem_closure {F : X.Modules} [IsFiniteQC F] {n : ℕ} (hd : suppDim F ≤ n) {w : X}
    (hw : topologicalKrullDim (closure {w} : Set X) = n) :
    ∀ y ∈ support F, w ∈ closure {y} → y = w := by
  intro y hy hwy
  have hsub : closure {w} ⊆ closure {y} :=
    isClosed_closure.closure_subset_iff.2 (Set.singleton_subset_iff.2 hwy)
  by_cases he : closure ({w} : Set X) = closure {y}
  · exact (inseparable_iff_closure_eq.2 he.symm).eq
  · have h1 := dim_add_one_le isClosed_closure isIrreducible_singleton.closure
      isIrreducible_singleton.closure (ssubset_of_subset_of_ne hsub he)
    have h2 := (dim_closure_le_suppDim hy).trans hd
    rw [hw] at h1
    have h3 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ n := by push_cast; exact h1.trans h2
    exact absurd (by exact_mod_cast h3 : n + 1 ≤ n) (by omega)


variable (κ) in
theorem interNumRed_eq_zero (hp : IsProjOver (strHom κ (X := X))) {ι : Type} [Fintype ι]
    {P : ι → LB X} (hP : ∀ i, (P i).IsLB) (C : Closeds X)
    (hC : topologicalKrullDim (C : Set X) < (Fintype.card ι : ℕ)) : interNumRed κ C P = 0 := by
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  have : IsLocallyNoetherian X := (isNoetherian_of_isProjOver hp).toIsLocallyNoetherian
  have hAV : IsAmpleLB (A.pull (redι C)) := hA.pull_of_isClosedImmersion _
  haveI : IsFiniteQC ((Scheme.Modules.pushforward (redι C)).obj (structureModule _)) :=
    ProperFinite.isFiniteQC_pushforward (redι C) hAV _
  refine interNum_eq_zero_of_isProjOver (algebraMap_eq_strHom κ X) _ hp ?_ hP
  refine lt_of_le_of_lt (topologicalKrullDim_mono ?_) hC
  exact (support_pushforward_subset_image_of_isClosedImmersion (redι C) _).trans
    ((Set.image_subset_range _ _).trans (range_redι C).le)

theorem interNum_eq_sum_length_mul_interNumRed : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ (X := X)) → ∀ (ι : Type) [Fintype ι] (P : ι → LB X), (∀ i, (P i).IsLB) → ∀ (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F], GlobalTheory.QCoh.suppDim F ≤ (Fintype.card ι : ℕ) → ∀ S : Finset X, (∀ w ∈ GlobalTheory.QCoh.support F, topologicalKrullDim (closure ({w} : Set X)) = (Fintype.card ι : ℕ) → w ∈ S) → interNum κ F P = ∑ w ∈ S, ((Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :)).toNat : ℤ) * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  intro κ _ X _ hp ι _ P hP F hF
  have hf := algebraMap_eq_strHom κ X
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  set n := Fintype.card ι with hn
  let term : X.Modules → X → ℤ := fun E w ↦
    ((Module.length (X.presheaf.stalk w) (E.presheaf.stalk w :)).toNat : ℤ) *
      interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P

  have hsmall : ∀ (E : X.Modules) (w : X), topologicalKrullDim (closure ({w} : Set X)) < n →
      term E w = 0 := fun E w h ↦ by
    simp only [term, interNumRed_eq_zero κ hp hP ⟨closure {w}, isClosed_closure⟩ h, mul_zero]
  have hout : ∀ (E : X.Modules) (w : X), w ∉ support E → term E w = 0 := fun E w h ↦ by
    simp only [term, length_stalk_eq_zero_of_notMem h, ENat.toNat_zero, Nat.cast_zero, zero_mul]
  let Q : X.Modules → Prop := fun E ↦ suppDim E ≤ n → ∀ S : Finset X,
    (∀ w ∈ support E, topologicalKrullDim (closure ({w} : Set X)) = n → w ∈ S) →
      interNum κ E P = ∑ w ∈ S, term E w
  suffices H : Q F from H
  refine GlobalTheory.QCoh.devissage X Q ?_ ?_ ?_ F hF
  · intro E hE _ S _
    rw [interNum_eq_zero_of_isZero κ hE hP]
    refine (Finset.sum_eq_zero fun w _ ↦ hout E w ?_).symm
    rw [support_eq_empty_iff.2 hE]
    exact Set.notMem_empty w
  · intro C hC h₁ h₃ Q₁ Q₃ hd S hS
    haveI := h₁
    haveI := h₃
    haveI := hC.mono_f
    haveI := hC.epi_g
    have hd₁ : suppDim C.X₁ ≤ n := (suppDim_le_of_mono C.f).trans hd
    have hd₃ : suppDim C.X₃ ≤ n := (suppDim_le_of_epi C.g).trans hd
    rw [interNum_shortExact hC hP (finiteCohTwists_of_isProjOver hf _ hp)
        (finiteCohTwists_of_isProjOver hf _ hp),
      Q₁ hd₁ S (fun w hw ↦ hS w (support_subset_of_mono C.f hw)),
      Q₃ hd₃ S (fun w hw ↦ hS w (support_subset_of_epi C.g hw)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    by_cases hw : topologicalKrullDim (closure ({w} : Set X)) < n
    · rw [hsmall _ _ hw, hsmall _ _ hw, hsmall _ _ hw, add_zero]
    have hfin : ∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ n →
        Module.length (X.presheaf.stalk w) (E.presheaf.stalk w :) ≠ ⊤ := fun E _ hE ↦ by
      by_cases hm : w ∈ support E
      · have he : topologicalKrullDim (closure ({w} : Set X)) = n :=
          le_antisymm ((dim_closure_le_suppDim hm).trans hE) (not_lt.1 hw)
        exact length_stalk_ne_top E w (eq_of_mem_closure hE he)
      · rw [length_stalk_eq_zero_of_notMem hm]; exact ENat.zero_ne_top
    have hex := Module.length_eq_add_of_exact (stalkLinear C.f w) (stalkLinear C.g w)
      (stalkLinear_injective C.f w) (stalkLinear_surjective C.g w)
      ((exact_iff_stalkLinear C).1 hC.exact w)
    simp only [term]
    rw [hex, ENat.toNat_add (hfin C.X₁ hd₁) (hfin C.X₃ hd₃)]
    push_cast
    ring
  · intro Z hZ hsm G hG hd S hS
    haveI := hG
    haveI := isIntegral_red hZ
    have hAV : IsAmpleLB (A.pull (redι Z)) := hA.pull_of_isClosedImmersion _
    haveI hFq : IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj G) :=
      ProperFinite.isFiniteQC_pushforward (redι Z) hAV G
    have hsupp : support ((Scheme.Modules.pushforward (redι Z)).obj G) ⊆ (Z : Set X) :=
      (support_pushforward_subset_image_of_isClosedImmersion (redι Z) G).trans
        ((Set.image_subset_range _ _).trans (range_redι Z).le)
    by_cases hss : support ((Scheme.Modules.pushforward (redι Z)).obj G) = (Z : Set X)
    swap
    · exact hsm _ hFq (ssubset_of_subset_of_ne hsupp hss) hd S hS
    have hdZ : topologicalKrullDim (Z : Set X) ≤ n := by
      rw [← hss]; exact hd

    have hlt : ∀ w ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G),
        closure ({w} : Set X) ≠ Z → topologicalKrullDim (closure ({w} : Set X)) < n := by
      intro w hw hne
      have hwZ : closure ({w} : Set X) ⊆ Z :=
        Z.isClosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 (hsupp hw))
      have h1 := dim_add_one_le isClosed_closure isIrreducible_singleton.closure hZ
        (ssubset_of_subset_of_ne hwZ hne)
      exact lt_of_add_one_le_natCast (h1.trans hdZ)
    rcases lt_or_eq_of_le hdZ with hZlt | hZeq
    · rw [interNum_eq_zero_of_isProjOver hf _ hp (by rw [suppDim, hss]; exact hZlt) hP]
      refine (Finset.sum_eq_zero fun w _ ↦ ?_).symm
      by_cases hw : w ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G)
      · refine hsmall _ _ (lt_of_le_of_lt (topologicalKrullDim_mono ?_) hZlt)
        exact Z.isClosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 (hsupp hw))
      · exact hout _ _ hw
    set η := redι Z (genericPoint (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) with hη
    have hcl : closure ({η} : Set X) = Z := by
      rw [hη, ← Set.image_singleton, (redι Z).isClosedEmbedding.closure_image_eq,
        (genericPoint_spec _).def, Set.image_univ, range_redι]
    have hηs : η ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G) := by
      rw [hss]; exact (range_redι Z).le ⟨_, rfl⟩
    rw [Finset.sum_eq_single_of_mem η (hS η hηs (by rw [hcl]; exact hZeq)) fun w _ hne ↦ ?_]
    swap
    · by_cases hw : w ∈ support ((Scheme.Modules.pushforward (redι Z)).obj G)
      · refine hsmall _ _ (hlt w hw fun e ↦ hne ?_)
        exact (inseparable_iff_closure_eq.2 (e.trans hcl.symm)).eq
      · exact hout _ _ hw
    simp only [term]
    rw [length_stalk_pushforward_generic Z G, ENat.toNat_natCast]
    have hC : (⟨closure {η}, isClosed_closure⟩ : Closeds X) = Z := Closeds.ext hcl
    rw [hC]
    letI : Algebra κ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
      algebraΓOfHom (redι Z ≫ strHom κ X)
    have hfZ : ∀ r : κ, (redι Z).appTop (algebraMap κ Γ(X, ⊤) r) =
        algebraMap κ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r := fun r ↦ by
      rw [hf r]; rfl
    have hstr : strHom κ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = redι Z ≫ strHom κ X :=
      strHom_eq fun _ ↦ rfl
    have hpZ : IsProjOver (strHom κ (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
      rw [hstr]; exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
    have hdimZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤
        (Fintype.card ι : ℕ) := by
      rw [topologicalKrullDim_red]; exact hdZ
    rw [interNum_pushforward_of_isClosedImmersion hfZ G hP,
      GlobalTheory.T.lineBundleIntersectionNumber_eq_genericRank_mul κ _ hpZ ι hdimZ G _ (fun i ↦ pull_isLB (hP i) _), interNumRed_def, interNumSub_def,
      interNumOn_def, interNum_pushforward_of_isClosedImmersion hfZ _ hP]

end GlobalTheory.SheafCycle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerPreservesHighestWeight
section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open GlobalTheory.PsCo.Pc1 (Mat)

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem intertwiner_preserves_highestWeight : HWVec := by
  intro n ε H _ _ σ D E hσ hD Z _ hZK γ W _ _ _ T hT Φ hΦ hint
  obtain ⟨-, -, hTy⟩ := hT
  obtain ⟨-, -, hirr, ⟨v, -, hv0, hvw⟩, hdom⟩ := hTy

  have hker : LinearMap.ker Φ = ⊥ := by
    rcases hirr (LinearMap.ker Φ) le_top (fun g hg w hw => by
      rw [LinearMap.mem_ker] at hw ⊢
      rw [hint g hg w, hw, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hΦ
  have hinj : Function.Injective Φ := LinearMap.ker_eq_bot.1 hker
  let ι : W →ₗ[ℂ] TensorProduct ℂ D (Fock n) := tsubVal Z ∘ₗ Φ
  have hιinj : Function.Injective ι := tsubVal_injective.comp hinj
  have hιK : ∀ (k : Mat n) (hk : k ∈ Kset ε) (w : W), wK hD hk (ι w) = ι (T k w) := by
    intro k hk w
    show wK hD hk (tsubVal Z (Φ w)) = tsubVal Z (Φ (T k w))
    rw [hint k (by rw [mir_Kset_eq]; exact hk) w, tOp_apply hD hZK hk]
  let S' : Submodule ℂ (TensorProduct ℂ D (Fock n)) := LinearMap.range ι
  have hS'fin : FiniteDimensional ℂ S' := LinearMap.finiteDimensional_range ι
  have hS'K : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ S', wK hD hk y ∈ S' := by
    rintro k hk _ ⟨w, rfl⟩
    exact ⟨T k w, (hιK k hk w).symm⟩

  have hwt : ∀ (μ : Fin n → ℝ) (w : W), Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T μ w →
      ∀ θ : Fin n → ℝ, wK hD (diag_mem_Kset' ε θ) (ι w) = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • ι w := by
    intro μ w hw θ
    rw [hιK _ _ w, hw θ (by rw [mir_Kset_eq]; exact diag_mem_Kset' ε θ), map_smul]
  have hwt' : ∀ (μ : Fin n → ℝ) (w : W),
      (∀ θ : Fin n → ℝ, wK hD (diag_mem_Kset' ε θ) (ι w) = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • ι w) →
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T μ w := by
    intro μ w hw θ _
    apply hιinj
    rw [map_smul, ← hιK _ (diag_mem_Kset' ε θ) w, hw θ]
  set z := ι v with hz
  have hz0 : z ≠ 0 := fun h => hv0 (hιinj (h.trans (map_zero ι).symm))
  have hzd : ∀ a, diagE ε (eT E) cpT cmT a a z = ((γ a : ℝ) : ℂ) • z :=
    diagE_wt_of_wK hσ hD (hwt γ v hvw)
  refine ⟨z, tsubVal_mem (Φ v), hz0, hzd, fun a b hab hε => ?_⟩
  set y := diagE ε (eT E) cpT cmT a b z with hy
  have hyS : y ∈ S' := diagE_mem_of_wK hσ hD S' hS'fin hS'K hε ⟨v, rfl⟩
  obtain ⟨w', hw'⟩ := hyS
  have hyd : ∀ c, diagE ε (eT E) cpT cmT c c y = (((γ + root a b) c : ℝ) : ℂ) • y := by
    intro c
    have hc := congrArg (fun F => F z)
      (diagAction_commutator (eT_isGlRep hD.glRep) cpT_cmT_isCAR (eT_commutesCAR E) ε c c a b rfl hε)
    simp only [Module.End.mul_apply, LinearMap.sub_apply] at hc
    rw [hzd c, map_smul] at hc
    have e1 : diagE ε (eT E) cpT cmT c c y =
        ((γ c : ℝ) : ℂ) • y + ((if c = a then diagE ε (eT E) cpT cmT c b else 0) -
          (if b = c then diagE ε (eT E) cpT cmT a c else 0)) z := by
      rw [hy, LinearMap.sub_apply, ← hc]; abel
    rw [e1]
    by_cases hca : c = a
    · subst hca
      have hcb : ¬ b = c := fun h => (ne_of_lt hab) h.symm
      simp only [if_neg hcb, sub_zero, Pi.add_apply, root, Pi.sub_apply, Pi.single_eq_same, ↓reduceIte]
      rw [Pi.single_eq_of_ne (ne_of_lt hab)]
      simp only [sub_zero, Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]
      rfl
    · by_cases hcb : b = c
      · subst hcb
        simp only [if_neg hca, zero_sub, Pi.add_apply, root, Pi.sub_apply, Pi.single_eq_same,
          LinearMap.neg_apply, ↓reduceIte]
        rw [Pi.single_eq_of_ne hca]
        simp only [zero_sub, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_one, add_smul, neg_smul,
          one_smul]
        rfl
      · simp only [if_neg hca, if_neg hcb, sub_zero, LinearMap.zero_apply, add_zero, Pi.add_apply, root,
          Pi.sub_apply]
        rw [Pi.single_eq_of_ne hca, Pi.single_eq_of_ne (Ne.symm hcb)]
        simp
  have hw'w : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T (γ + root a b) w' := by
    apply hwt'
    intro θ
    rw [hw']
    exact wK_diag_wt hσ hD hyd θ
  by_contra hne
  have hw'0 : w' ≠ 0 := by
    intro h; apply hne; rw [← hw', h, map_zero]
  exact not_cdom_add_root ε γ hab (hdom _ w' (Submodule.mem_top) hw'0 hw'w)

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicAppLE
section
open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace GlobalTheory.GenDegAlg

theorem isAlgebraic_appLE : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ {U : X.Opens} {V : Y.Opens}, IsAffineOpen U → (V : Set Y).Nonempty → ∀ h : V ≤ π ⁻¹ᵁ U, (letI := (π.appLE U V h).hom.toAlgebra; Algebra.IsAlgebraic Γ(X, U) Γ(Y, V)) := by
  intro X Y _ _ π hgen hdeg U V hU hV h
  have hη : genericPoint Y ∈ V :=
    ((genericPoint_spec Y).mem_open_set_iff V.isOpen).2 (by simpa using hV)
  have hx : π (genericPoint Y) ∈ U := h hη
  letI : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V h).hom.toAlgebra
  letI : Algebra Γ(X, U) (X.residueField (π (genericPoint Y))) :=
    (X.evaluation U _ hx).hom.toAlgebra
  letI : Algebra (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) :=
    (π.residueFieldMap (genericPoint Y)).hom.toAlgebra
  letI : Algebra Γ(Y, V) (Y.residueField (genericPoint Y)) :=
    (Y.evaluation V _ hη).hom.toAlgebra
  letI : Algebra Γ(X, U) (Y.residueField (genericPoint Y)) :=
    (X.evaluation U _ hx ≫ π.residueFieldMap (genericPoint Y)).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U) (X.residueField (π (genericPoint Y)))
      (Y.residueField (genericPoint Y)) := IsScalarTower.of_algebraMap_eq' rfl
  have hnat : π.appLE U V h ≫ Y.evaluation V _ hη =
      X.evaluation U _ hx ≫ π.residueFieldMap (genericPoint Y) := by
    rw [Scheme.evaluation_naturality, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp [Scheme.evaluation]
  haveI : IsScalarTower Γ(X, U) Γ(Y, V) (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' congr($(hnat).hom).symm
  haveI := GlobalTheory.ProjFin.isFractionRing_evaluation X hU hgen hx
  haveI : Nonempty U := ⟨⟨_, hx⟩⟩
  haveI : Module.Finite (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hdeg)
  haveI : Algebra.IsAlgebraic (X.residueField (π (genericPoint Y)))
      (Y.residueField (genericPoint Y)) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic Γ(X, U) (Y.residueField (genericPoint Y)) :=
    (IsFractionRing.comap_isAlgebraic_iff (K := X.residueField (π (genericPoint Y)))).2 inferInstance
  have hinj : Function.Injective (Y.evaluation V _ hη).hom := by
    have h1 := germ_injective_of_isIntegral Y (genericPoint Y) hη
    have h2 : Function.Injective (Y.residue (genericPoint Y)).hom :=
      RingHom.injective (show Y.functionField →+* Y.residueField (genericPoint Y) from
        (Y.residue (genericPoint Y)).hom)
    exact h2.comp h1
  exact Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom Γ(X, U) Γ(Y, V)
    (Y.residueField (genericPoint Y))) hinj

end GlobalTheory.GenDegAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOverMvPolynomialRangeEtaleTower
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem isAlgebraic_range_eval₂Hom_of_isEtTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T),
  IsEtTower cK R cL T ι ψ τ → Function.Injective (MvPolynomial.eval₂Hom ι τ) →
  ∀ z : L, IsAlgebraic (T.subtype.comp (MvPolynomial.eval₂Hom ι τ)).range z := by
  intro K L _ _ cK cL r R T ι ψ τ h hinj z
  classical
  let A := MvPolynomial (Fin r) R
  let φ : A →+* T := MvPolynomial.eval₂Hom ι τ
  let φL : A →+* L := T.subtype.comp φ
  have hφL : Function.Injective φL := Subtype.val_injective.comp hinj

  letI : Algebra A T := φ.toAlgebra
  letI : Algebra A L := φL.toAlgebra
  haveI : IsScalarTower A T L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FormallyEtale A T := h.etale

  haveI : IsFractionRing T L := IsFractionRing.of_field T L fun f => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h.top.frac f
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change f = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  haveI : Algebra.FormallyUnramified T L :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors T)
  haveI : Algebra.FormallyUnramified A L := Algebra.FormallyUnramified.comp A T L

  let c0 : ℂ →+* R := cK.codRestrict R h.base.const_mem
  let cT : ℂ →+* T := cL.codRestrict T h.top.const_mem
  letI : Algebra ℂ R := c0.toAlgebra
  letI : Algebra ℂ T := cT.toAlgebra
  letI : Algebra ℂ L := cL.toAlgebra
  haveI : IsScalarTower ℂ T L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℂ A L := IsScalarTower.of_algebraMap_eq fun a => by
    change cL a = T.subtype (MvPolynomial.eval₂Hom ι τ (MvPolynomial.C (c0 a)))
    rw [MvPolynomial.eval₂Hom_C]
    exact (h.const a).symm
  haveI : Algebra.EssFiniteType ℂ T := RingHom.essFiniteType_algebraMap.1 h.top.essFiniteType
  haveI : Algebra.EssFiniteType T L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors T)
  haveI : Algebra.EssFiniteType ℂ L := Algebra.EssFiniteType.comp ℂ T L
  haveI : Algebra.EssFiniteType A L := Algebra.EssFiniteType.of_comp ℂ A L

  let F := FractionRing A
  letI : Algebra F L := (IsFractionRing.lift hφL : F →+* L).toAlgebra
  haveI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap hφL a).symm
  haveI : Algebra.FormallyUnramified F L := Algebra.FormallyUnramified.of_restrictScalars A F L
  haveI : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp A F L
  haveI : Algebra.IsSeparable F L := Algebra.FormallyUnramified.isSeparable F L
  have hA : IsAlgebraic A z :=
    (IsFractionRing.isAlgebraic_iff A F L).2 (Algebra.IsAlgebraic.isAlgebraic z)

  obtain ⟨p, hp, hpz⟩ := hA
  refine ⟨p.map φL.rangeRestrict, (Polynomial.map_ne_zero_iff
    (RingHom.injective_codRestrict.2 hφL)).2 hp, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  exact hpz

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCartierLocalEquationDiagonalOfAdaptedFrame
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem isEqn_diag_of_frame : ∀ (F : Type) [Field F] (Y : Var F) (ι : Type) (m : ι → ℕ) (E' : Fr (ratOf Y) m m) (gr : Root m → Y.Dv), ∀ B ∈ E'.S (genericPoint Y.X), (∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t) → ∀ (y : Y.X), ∀ A ∈ E'.S y, Par m ⊤ (B * A⁻¹) ∧ ∀ x : Root m, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t := by
  intro F _ Y ι m E' gr B hB H y A hA
  have par : ∀ {z : Y.X} {A : Mat m Y.Fn}, A ∈ E'.S z → Par m ⊤ (B * A⁻¹) := fun {z A} h =>
    ((Fr.mem_iff (Fr.mem_genericPoint h)).1 hB).mono le_rfl le_top
  refine ⟨par hA, fun x => ?_⟩
  obtain ⟨A', hA', t', ht', heq⟩ := H y x
  have hP : Par m ((ratOf Y).O y).toSubring (A' * A⁻¹) := (Fr.mem_iff hA).1 hA'
  have e : B * A⁻¹ = (B * A'⁻¹) * (A' * A⁻¹) := by
    rw [← mul_assoc, mul_assoc B, Mat.inv_mul (Fr.det_ne hA'), mul_one]
  obtain ⟨hu0, hui, -, -⟩ := _root_.GlobalTheory.FlagPush.diag_of_par ι m Y.Fn _ (A' * A⁻¹) hP x
  obtain ⟨-, -, -, hmul⟩ := _root_.GlobalTheory.FlagPush.diag_of_par ι m Y.Fn ⊤ (B * A'⁻¹) (par hA') x
  obtain ⟨ht0, -⟩ := _root_.GlobalTheory.FlagPush.diag_of_par ι m Y.Fn ⊤ (B * A⁻¹) (par hA) x
  have hd : (B * A⁻¹) x.1 x.2 x.2 = t' * (A' * A⁻¹) x.1 x.2 x.2 := by
    rw [e, hmul _ (hP.mono le_rfl le_top), ht']
  refine ⟨Units.mk0 _ ht0, rfl, heq.iff_unitAt.2 ?_⟩
  have hu : UnitAt y ((A' * A⁻¹) x.1 x.2 x.2) := (unitAt_iff hu0).2
    ⟨mem_O_ratOf.1 ((hP x.1).1 x.2 x.2), mem_O_ratOf.1 hui⟩
  convert hu using 1
  rw [Units.val_mk0, hd]
  exact mul_div_cancel_left₀ _ t'.ne_zero

end GlobalTheory.FlagPush
end

