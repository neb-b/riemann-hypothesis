module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InfinitelyManyRealQuadraticSteps
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0343
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CoreAtQIffRowQ
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0235

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.BadFinite
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

namespace UpperTheory.Gal.Int.Core

section

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]

private def bad (l : ℕ) {a : ℕ} (π : CuspSub E a) (w₀ : HeightOneSpectrum (𝓞 E)) : Set (HeightOneSpectrum (𝓞 E)) :=
  {w | w = w₀ ∨ ((l : ℕ) : 𝓞 E) ∈ w.asIdeal ∨ ¬ ∃ B, (CG.mk π).HasSat w B}

private theorem bad_finite {a : ℕ} (π : CuspSub E a) (w₀ : HeightOneSpectrum (𝓞 E)) : (bad l π w₀).Finite := by
  have h1 := Filter.eventually_cofinite.1 (GlobalTheory.CongEx.eventually_not_mem_l E l)
  have h2 := Filter.eventually_cofinite.1 (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep GlobalTheory.automorphicFormsFiniteGL E a π)
  refine ((Set.finite_singleton w₀).union (h1.union h2)).subset ?_
  rintro w (h | h | h)
  · exact Or.inl h
  · exact Or.inr (Or.inl (not_not.2 h))
  · exact Or.inr (Or.inr h)

private theorem serves (hR : RamUnr) {a : ℕ} (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (w₀ : HeightOneSpectrum (𝓞 E)) (Q : QCM E Ω)
    (h1 : ∀ t ∈ bad l π w₀, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := E) A, Fixes ↥Q.K g)
    (h2 : RamOff (bad l π w₀) Q)
    (h3 : ∀ P : CuspSub ↥Q.K a, IsLift π P → ∃ p : HeightOneSpectrum (𝓞 ↥Q.K) → Prop, RowP Ω p P ι ∧
      (∀ᶠ w : HeightOneSpectrum (𝓞 ↥Q.K) in Filter.cofinite, (normV w).Prime → p w) ∧ ∀ w, w.under (𝓞 E) = w₀ → p w) :
    Serves π ι w₀ Q := by
  refine ⟨fun A hA g hg => ?_, ?_, h3⟩
  · rw [GlobalTheory.ExSplitCM.mem_range_res_iff]
    exact fun x hx => h1 w₀ (Or.inl rfl) A hA g hg ⟨x, hx⟩
  · obtain ⟨w, hw, hT⟩ := hR E Ω _ Q h2
    exact ⟨w, hw, not_not.1 fun h => hT (Or.inr (Or.inr h))⟩

end

theorem joinUp_of' (hS : StepDown) (hC : CsdLift) (hR : RamUnr) (hO : OneUs) (hQ : Quad2Ex) : JoinUp := by
  intro hJ hG hL hcore
  have top : ∀ (E Y Ω : Type) [Field E] [NumberField E] [Field Y] [NumberField Y] [IsCMField Y] [Field Ω] [Algebra E Y]
      [Algebra Y Ω] [IsAlgClosure Y Ω] (δ : Y), RealStep E Ω δ → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
      (∀ (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra Y M], ∃ w : Fin 3 → HeightOneSpectrum (𝓞 M),
        (∀ i, ((l : ℕ) : 𝓞 M) ∈ (w i).asIdeal) ∧ ∀ i j, i ≠ j → Apart (w i) (w j)) →
      ∀ a : ℕ, 1 ≤ a → ∀ π : CuspSub Y a, InScope .all l π (quadChar Y ^ a) → RowP Ω (fun _ => True) π ι := by
    intro E Y Ω _ _ _ _ _ _ _ _ _ δ hδ l _ ι h3 a ha π hπ
    refine hS hL Y Ω l ι a ha π fun w₀ => ?_
    have hinf : {Q : QCM Y Ω | Step2 (bad l π w₀) Q}.Infinite := by
      refine infOf Y Ω _ fun S hS => ?_
      obtain ⟨Q, ⟨a1, a2, a3, a4, u, hu, a5⟩, hI, d, hd, hU⟩ := hQ E Y Ω δ hδ (bad l π w₀ ∪ S) ((bad_finite π w₀).union hS)
      exact ⟨Q, ⟨⟨a1, a2, fun t ht => a3 t (Or.inl ht), fun w hw => ⟨fun h => (a4 w hw).1 (Or.inl h), (a4 w hw).2⟩, u,
        fun h => hu (Or.inl h), a5⟩, hI, d, hd, fun w hw => hU w (Or.inl hw)⟩, u, fun h => hu (Or.inr h), a5⟩
    refine hinf.mono ?_
    rintro Q ⟨h1, hI, d, hd, hU⟩
    refine serves hR π ι w₀ Q h1.2.2.1 h1.2.2.2.2 fun P hP => ?_
    have hl : ∀ w : HeightOneSpectrum (𝓞 ↥Q.K), ((l : ℕ) : 𝓞 ↥Q.K) ∈ w.asIdeal → w.under (𝓞 Y) ∈ bad l π w₀ :=
      fun w hw => Or.inr (Or.inl ((GlobalTheory.CMFam.natCast_mem_under w l).2 hw))
    obtain ⟨w, hw, hap⟩ := h3 ↥Q.K
    have hF : GlobalTheory.Row9.FieldOK l ↥Q.K := ⟨h1.1, h1.2.1, allUnr_holds Y Ω _ Q h1, fun u hu => (hU u (hl u hu)).1,
      w 0, w 1, w 2, hw 0, hw 1, hw 2, hap 0 1 (by decide), hap 0 2 (by decide), hap 1 2 (by decide)⟩
    have hsq : SqAt d l := (hU _ (hl _ (hw 0))).2 l Fact.out (hw 0)
    have hPs := hC hJ hG Y ↥Q.K l a ha π P hP hπ
    have hgood : Good l P := by
      refine ⟨h1.1, h1.2.1, fun u hu => ?_⟩
      obtain ⟨b1, b2, -⟩ := h1.2.2.2.1 u hu
      refine ⟨fun h => b1 (hl u h), b2, ?_⟩
      obtain ⟨B, hB⟩ : ∃ B, (CG.mk π).HasSat (u.under (𝓞 Y)) B := not_not.1 fun h => b1 (Or.inr (Or.inr h))
      exact ⟨_, hP.sat u _ B (GlobalTheory.RealGal.AttRes.normV_eq_pow u) hB⟩
    exact ⟨UsPl d, hcore ↥Q.K Ω l ι hF hI d hd hsq a ha P ⟨hPs.1, hPs.2.1, hgood, rfl⟩, hO ↥Q.K d hd,
      fun u hu => hU u (Or.inl hu)⟩
  intro E Ω _ _ _ _ _ _ l _ ι a ha π hπ
  obtain ⟨t, ht⟩ := GlobalTheory.CongEx.exists_place_over E l
  refine hS hL E Ω l ι a ha π fun w₀ => (infinitely_many_real_quadratic_steps E Ω _ (bad_finite (l := l) π w₀)).mono fun Q₁ s₁ => ?_
  refine serves hR π ι w₀ Q₁ s₁.2.1 s₁.2.2 fun P₁ hP₁ => ⟨fun _ => True, ?_, by simp, fun _ _ => trivial⟩
  have h₁ := hC hJ hG E ↥Q₁.K l a ha π P₁ hP₁ hπ
  refine hS hL ↥Q₁.K Ω l ι a ha P₁ fun w₁ => (infinitely_many_real_quadratic_steps ↥Q₁.K Ω _ (bad_finite (l := l) P₁ w₁)).mono fun Q₂ s₂ => ?_
  refine serves hR P₁ ι w₁ Q₂ s₂.2.1 s₂.2.2 fun P₂ hP₂ => ⟨fun _ => True, ?_, by simp, fun _ _ => trivial⟩
  have h₂ := hC hJ hG ↥Q₁.K ↥Q₂.K l a ha P₁ P₂ hP₂ h₁
  obtain ⟨δ, hδ, -⟩ := s₂.1
  refine top ↥Q₁.K ↥Q₂.K Ω δ hδ l ι (fun M _ _ _ _ => ?_) a ha P₂ h₂
  obtain ⟨w, hw, hap⟩ := threeApart_holds E Ω _ Q₁ s₁ _ Q₂ s₂ t (Or.inr (Or.inl ht))
    (fun u hu => Or.inr (Or.inl ((GlobalTheory.CMFam.natCast_mem_under (E := E) u l).1 (hu ▸ ht)))) M
  refine ⟨w, fun i => ?_, hap⟩
  rw [← GlobalTheory.CMFam.natCast_mem_under (E := ↥Q₂.K), ← GlobalTheory.CMFam.natCast_mem_under (E := ↥Q₁.K),
    ← GlobalTheory.CMFam.natCast_mem_under (E := E), hw i]
  exact ht

end UpperTheory.Gal.Int.Core
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.JoinAll
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core
open UpperTheory.Gal.TP

namespace UpperTheory.Gal.Int.Core

theorem goodGuard_usPl (h1 : OneUs) (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (d : ℕ) (hd : ImQ E d) : GoodGuard Ω l (UsPl (E := E) d) := by
  refine ⟨fun _ h => h.1, fun S hS => ?_⟩
  have hT := hS.union (Filter.eventually_cofinite.1 ((h1 E d hd).and (GlobalTheory.CongEx.eventually_not_mem_l E l)))
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hT
  refine (hD.preimage (Homeomorph.inv (G E Ω)).isOpenMap).mono ?_
  rintro g ⟨v, hv, hdeg, A, hA, hσ⟩
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
  have hp : (normV v).Prime := by
    simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
      (((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hdeg)
  exact ⟨v, hv.1, hv.2.1 hp, hv.2.2, A, hA, hσ⟩

theorem joinAll_of (h1 : OneUs) (hS : SubtractQ) : JoinAll := by
  intro hT hU E Ω _ _ _ _ _ _ l _ ι hF hI d hd hsq n hn
  exact allCoreQ_of hS hT E Ω l ι hF hI _ (goodGuard_usPl h1 E Ω l d hd) (fun m hm => hU m hm E Ω l ι hF d hd hsq) n hn

end UpperTheory.Gal.Int.Core
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.JoinEndHolds
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core
open UpperTheory.Gal.TP

namespace UpperTheory.Gal.Int.Core

theorem joinU_of (h1 : OneUs) (h2 : IsoOne) (h3 : PhiPol) (h4 : AutT) (hA : Sub.SatAE) (hC : Sub.ClConj) (hS : Sub.SatPol)
    (hW : Sub.ClAway) : JoinU := by
  intro hL m hm E Ω _ _ _ _ _ _ l _ ι hF d hd hsq U hU lam hl
  obtain ⟨T, hT, hAT⟩ := h4 E m U hU
  have hsp := hF.2.2.2.1
  have hFO : FieldOK E l d := ⟨hd, hsq, hF.2.1, fun w hw => ⟨fun h => hw (hsp w h), hF.2.2.1 w⟩⟩
  have key : ∀ u v : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ u.asIdeal → ((l : ℕ) : 𝓞 E) ∈ v.asIdeal → Apart v u →
      ∃ r : G E Ω →* GL (Fin m) (Qbar l), Continuous r ∧ IsSSRep r ∧
        (∀ w, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, SatU U w B → FrobEig ι r w (algSat m (normV w) B)) ∧
        ∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w u → Apart w v → ∀ B, SatU U w B →
          Sub.Cl ι r w (algSat m (normV w) B) (GlobalTheory.GalDef.jumpsOf ι lam) := by
    intro u v hu hv huv
    obtain ⟨r, hc, hs, f1, f2, f3⟩ := hL E Ω l ι m hm d hFO T hT U hAT u v hu (hsp u hu) hv (hsp v hv) huv
    refine ⟨r, hc, hs, f1, fun w hw a1 a2 B hB => (sphG_iff_cl hS ι r w B lam).1 fun c => ?_⟩
    have hD := f2 w hw a1 a2 ⟨B, hB⟩
    cases c with
    | unr => exact fun h => absurd hw h
    | dR =>
      intro P AI ht A hA O _ _ _ Bw hj
      exact ⟨(hD P AI ht A hA O Bw hj).2.1, fun τ LL' τ' hi J hJ =>
        (hD P AI ht A hA O Bw hj).2.2 τ LL' τ' hi (lam _) J (hl _) hJ⟩
    | crys => exact fun P AI ht A hA O _ _ _ Bw hj => (hD P AI ht A hA O Bw hj).1
    | phi =>
      intro P AI ht A hA O _ _ _ Bw hj g
      exact h3 E Ω A w hA _ _ g (f3 w hw a1 a2 B hB P AI ht A hA O Bw hj g)
  obtain ⟨w₁, w₂, w₃, l1, l2, l3, a12, a13, a23⟩ := hF.2.2.2.2
  obtain ⟨r, hc, hs, f1, -⟩ := key w₂ w₁ l2 l1 a12
  refine ⟨r, hc, hs, fun w B hw hB => (sphG_iff_cl hS ι r w B lam).2 ?_⟩
  by_cases hwl : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal
  · have pick : ∃ u v : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ u.asIdeal ∧ ((l : ℕ) : 𝓞 E) ∈ v.asIdeal ∧ Apart v u ∧
        Apart w u ∧ Apart w v := by
      unfold Apart at a12 a13 a23 ⊢
      by_cases e1 : w.under (𝓞 (maximalRealSubfield E)) = w₁.under (𝓞 (maximalRealSubfield E))
      · exact ⟨w₃, w₂, l3, l2, a23, e1 ▸ a13, e1 ▸ a12⟩
      · by_cases e2 : w.under (𝓞 (maximalRealSubfield E)) = w₂.under (𝓞 (maximalRealSubfield E))
        · exact ⟨w₃, w₁, l3, l1, a13, e2 ▸ a23, e1⟩
        · exact ⟨w₂, w₁, l2, l1, a12, e2, e1⟩
    obtain ⟨u, v, hu, hv, huv, hwu, hwv⟩ := pick
    obtain ⟨s, sc, ss, g1, g2⟩ := key u v hu hv huv
    refine hC E Ω l ι m s r sc (h2 E Ω l ι m s r sc hc ss hs ?_) w _ _ (g2 w hwl hwu hwv B hB.2)
    filter_upwards [h1 E d hd, hA E m U hU, GlobalTheory.CongEx.eventually_not_mem_l E l] with x x1 x2 x3 hp
    obtain ⟨B', hB'⟩ := x2 (x1 hp).1
    exact ⟨_, g1 x (x1 hp) x3 B' hB', f1 x (x1 hp) x3 B' hB'⟩
  · exact (hW E Ω l ι m r w hwl _ _).2 (f1 w hw hwl B hB.2)

theorem joinGL_holds : JoinGL := by
  intro hD hU E Ω _ _ _ _ _ _ l _ ι hF hI d hd hsq a ha π hπ
  obtain ⟨T, hT, -, U, hM⟩ := hD E l a (Fact.out) ha π hπ ∅
  obtain ⟨lam, hlam⟩ := GlobalTheory.Cong.exists_weight_of_isAutRepU E a U hM.aut
  obtain ⟨r, hc, hs, hr⟩ := hU E Ω l ι hF hI d hd hsq a ha U hM.aut lam hlam
  refine ⟨r, hc, hs, fun w B hw hB c => ?_⟩
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL E a π w
  have h := hr w B hw ⟨hw.1, σ, hM.split w hw.1 σ hσ, ((GlobalTheory.Cong.satake_locComp E a π w σ hσ).1 B).1 hB⟩ c
  cases c with
  | unr => exact h
  | dR =>
    intro P AI ht A hA O _ _ _ Bw hj
    refine ⟨(h P AI ht A hA O Bw hj).1, fun τ LL' τ' hi J hJ => (h P AI ht A hA O Bw hj).2 τ LL' τ' hi J ?_⟩
    rw [hM.inf _ _ (hlam _)] at hJ
    exact hJ
  | crys => exact fun P AI ht A hA O _ _ _ Bw hj _ _ _ => h P AI ht A hA O Bw hj
  | phi => exact h

theorem joinEnd_holds : JoinEnd := by
  intro h E Ω _ _ _ _ _ _ l _ ι a ha π hπ
  obtain ⟨r, hc, hs, hr⟩ := h E Ω l ι a ha π hπ.all
  refine ⟨r, ⟨hc, hs, ?_⟩, fun w B hB =>
    ⟨hr w B trivial hB .unr, hr w B trivial hB .dR, hr w B trivial hB .crys, hr w B trivial hB .phi⟩⟩
  filter_upwards [GlobalTheory.CongEx.eventually_not_mem_l E l,
    GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep GlobalTheory.automorphicFormsFiniteGL E a π] with w hl hB
  obtain ⟨B, hB⟩ := hB
  exact ⟨B, hB, hr w B trivial hB .unr hl⟩

theorem stepDown_of (h2 : IsoOne) (hP : PatchOne) (hD : ∀ c, SphDown c) : StepDown := by
  intro hQL E Ω _ _ _ _ _ _ l _ ι a ha π fam
  have hsat := GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep GlobalTheory.automorphicFormsFiniteGL E a π
  let S : Set (QCM E Ω) := {Q | ∃ r : G ↥Q.K Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧ AttOne (CG.mk π).HasSat ι ↥Q.K r}
  have serve : ∀ w₀ (Q : QCM E Ω), Serves π ι w₀ Q → ∃ (P : CuspSub ↥Q.K a) (r : G ↥Q.K Ω →* GL (Fin a) (Qbar l)), IsLift π P ∧
      Continuous r ∧ IsSSRep r ∧ AttOne (CG.mk π).HasSat ι ↥Q.K r ∧
      ∀ w B, w.under (𝓞 E) = w₀ → (CG.mk P).HasSat w B → ∀ c, GlobalTheory.RoadU.SphAt c P ι r w B := by
    intro w₀ Q hQ
    obtain ⟨P, hPl⟩ := hQL E ↥Q.K Q.two a ha π hQ.2.1
    obtain ⟨p, ⟨r, hc, hs, hr⟩, hp1, hp2⟩ := hQ.2.2 P hPl
    refine ⟨P, r, hPl, hc, hs, ?_, fun w B hw => hr w B (hp2 w hw)⟩
    unfold AttOne
    filter_upwards [hp1, GlobalTheory.CongEx.eventually_not_mem_l (↥Q.K) l,
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under (K := E) (L := ↥Q.K)).eventually hsat] with w x1 x2 x3 hp
    obtain ⟨B, hB⟩ := x3
    have hq := GlobalTheory.RealGal.AttRes.normV_eq_pow (F := E) w
    have hf : w.asIdeal.inertiaDeg (𝓞 E) = 1 := Nat.Prime.eq_one_of_pow (hq ▸ hp)
    have hB' : (CG.mk P).HasSat w B := by simpa [hf] using hPl.sat w _ B hq hB
    exact ⟨B, hB, hr w B (x1 hp) hB' .unr x2⟩
  have famS : ∀ w₀ Q, Serves π ι w₀ Q → Q ∈ S := fun w₀ Q hQ => by
    obtain ⟨_, r, -, a1, a2, a3, -⟩ := serve w₀ Q hQ
    exact ⟨r, a1, a2, a3⟩
  obtain ⟨v0, -⟩ := GlobalTheory.CongEx.exists_place_over E l
  have hS : S.Infinite := (fam v0).mono fun Q hQ => famS v0 Q hQ
  choose r hr using fun Q : ↥S => Q.2
  obtain ⟨ρ, hρc, hρs, hev⟩ := hP E Ω l ι a (CG.mk π).HasSat (fun v B B' h h' => h.unique h') S hS r hr
  refine ⟨ρ, hρc, hρs, fun w B _ hB c => ?_⟩
  have hfin := (Filter.eventually_cofinite.1 hev).image Subtype.val
  obtain ⟨Q, hQ, hQn⟩ := ((fam w).diff hfin).nonempty
  have hiso : RepIso (r ⟨Q, famS w Q hQ⟩) (ρ.comp (res E Ω ↥Q.K)) := by
    by_contra hc
    exact hQn ⟨⟨Q, famS w Q hQ⟩, hc, rfl⟩
  obtain ⟨P, s, hPl, sc, ss, sa, hs⟩ := serve w Q hQ
  obtain ⟨rc, rs, ra⟩ := hr ⟨Q, famS w Q hQ⟩
  have e : RepIso s (r ⟨Q, famS w Q hQ⟩) := by
    refine h2 (↥Q.K) Ω l ι a s _ sc rc ss rs ?_
    filter_upwards [sa, ra] with x x1 x2 hp
    obtain ⟨B1, b1, c1⟩ := x1 hp
    obtain ⟨B2, b2, c2⟩ := x2 hp
    obtain rfl := b1.unique b2
    exact ⟨_, c1, c2⟩
  refine hD c E Ω l ι a π Q P hPl ρ w B hB hQ.1 fun w' hw' hB' => ?_
  exact GlobalTheory.RoadW.sphAt_of_repIso ι P rc hiso c w' B (GlobalTheory.RoadW.sphAt_of_repIso ι P sc e c w' B (hs w' B hw' hB' c))

end UpperTheory.Gal.Int.Core
end

