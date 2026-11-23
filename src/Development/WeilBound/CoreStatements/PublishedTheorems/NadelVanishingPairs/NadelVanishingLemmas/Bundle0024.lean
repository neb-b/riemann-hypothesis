module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0017
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0023
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CohomologyVanishingSpecializes
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0010
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.BlowupAmpleRelative
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.AmpleUpstairs


open GlobalTheory.Cartier.CartierDiv in
theorem supp_neg_le {X : Scheme.{0}} [IsIntegral X] (D : GlobalTheory.Cartier.CartierDiv X) : (-D).supp ≤ D.supp := by
  intro x hx
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  rw [hg.neg.mem_supp_iff] at hx
  rw [hg.mem_supp_iff]
  intro hu
  apply hx
  rw [Units.val_inv_eq_inv_val]
  exact hu.inv


open GlobalTheory.Cartier.CartierDiv in
theorem supp_nsmul_le {X : Scheme.{0}} [IsIntegral X] (D : GlobalTheory.Cartier.CartierDiv X) (m : ℕ) :
    (m • D).supp ≤ D.supp := by
  intro x hx
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  rw [(hg.nsmul m).mem_supp_iff] at hx
  rw [hg.mem_supp_iff]
  intro hu
  apply hx
  rw [Units.val_pow_eq_pow_val]
  have key : ∀ j : ℕ, UnitAt x ((g : X.functionField) ^ j) := by
    intro j
    induction j with
    | zero => simpa using unitAt_one x
    | succ j ih => rw [pow_succ]; exact ih.mul hu
  exact key m

end GlobalTheory.AmpleUpstairs

namespace GlobalTheory


open GlobalTheory.AmpleUpstairs in
theorem exists_ample_pull_sub_eff : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver q → IsProjOver (t ≫ q) → ∀ I : Y₀.IdealSheafData, IsIso (t ∣_ I.support.compl) → FinalTheorems.EffCartier (I.comap t) → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ (c : ℕ) (E : CartierDiv Y₁) (A₁ : LB Y₁) (hA₁ : IsAmpleLB A₁), 0 < c ∧ E.Eff ∧ E.supp ≤ (I.comap t).support ∧ c • CechPic.pull t (cls A hA.isLB) = cls A₁ hA₁.isLB + toPic E := by
  intro k _ _ Y₀ Y₁ _ _ _ _ q n t _ _ _ hq ht I hiso hI A hA
  obtain ⟨-, L₁, hL₁⟩ := isProper_and_exists_isAmpleLB_of_isProjOver ht
  haveI : CompactSpace Y₁ := hL₁.compactSpace
  haveI : CompactSpace Y₀ := hA.compactSpace
  haveI : IsNoetherian Y₀ := {}
  haveI : Smooth (t ≫ q) := SmoothOfRelativeDimension.smooth n _
  haveI : GlobalTheory.IsNormalScheme Y₁ := GlobalTheory.ModifSections.isNormalScheme_of_smooth (t ≫ q)
  obtain ⟨H, hH⟩ := toPic_surjective (cls L₁ hL₁.isLB)
  obtain ⟨H₀, hH₀⟩ := GlobalTheory.T.divisor_agreement_on_isomorphism k Y₀ Y₁ q n t ht I.support.compl hiso H
  obtain ⟨E₀, hE₀, hsE₀, hgen⟩ := GlobalTheory.T.blowup_ample_minus_exceptional Y₀ Y₁ t I hI A hA
  have hD : (H - pullCart t H₀).supp ≤ E₀.supp := by
    intro y hy
    rw [hsE₀, Scheme.IdealSheafData.support_comap]
    by_contra h
    exact hH₀ y h hy
  obtain ⟨e, he⟩ := GlobalTheory.T.effective_multiple_dominates Y₁ (H - pullCart t H₀) E₀ hE₀ hD
  obtain ⟨c₁, hc₁, hc₁'⟩ :=
    ((hA.eventually_isGenerated_tens_lbPow (isLB_toLB (-H₀))).and (eventually_ge_atTop 1)).exists
  obtain ⟨c₂, hc₂⟩ := hgen.exists
  obtain ⟨P, hP, hPc⟩ := cls_surj (c₂ • CechPic.pull t (cls A hA.isLB) - toPic E₀)
  have gP := hc₂ P hP hPc
  have g₁ := hc₁.pull t
  have gM := AmpleModelPos.isGenerated_tens g₁ (gP.pow e)
  have hA₁L := isLB_tens hL₁.isLB gM.isLB
  have hA₁ : IsAmpleLB (tens L₁ (tens ((tens (toLB (-H₀)) (lbPow A c₁)).pull t) (lbPow P e))) := by
    refine hL₁.tensor_isGenerated gM hA₁L ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hA₁L hL₁.isLB) gM.isLB)).1 ?_)
    rw [cls_div (LB.isLB_div hA₁L hL₁.isLB) gM.isLB, cls_div hA₁L hL₁.isLB, cls_tens hL₁.isLB gM.isLB]
    abel
  refine ⟨c₁ + e * c₂, e • E₀ - (H - pullCart t H₀), _, hA₁, by omega, he, ?_, ?_⟩
  · rw [sub_eq_add_neg]
    refine (GlobalTheory.Cartier.CartierDiv.supp_add_le _ _).trans (sup_le ((supp_nsmul_le _ _).trans hsE₀.le) ?_)
    exact (supp_neg_le _).trans (hD.trans hsE₀.le)
  · rw [cls_tens hL₁.isLB gM.isLB, cls_tens g₁.isLB (gP.pow e).isLB,
      cls_lbPow hP e, hPc, cls_pull (isLB_tens (isLB_toLB (-H₀)) (isLB_lbPow hA.isLB c₁)) t,
      cls_tens (isLB_toLB (-H₀)) (isLB_lbPow hA.isLB c₁), cls_lbPow hA.isLB c₁, ← toPic_apply,
      map_sub, map_nsmul, map_sub, toPic_pullCart, hH, map_add, map_neg, map_nsmul, add_smul, mul_smul]
    simp only [map_neg, smul_sub]
    abel

end GlobalTheory
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegSpreading
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem vanishing_charZero_fibre_of_finiteType : ∀ (R k : Type) [CommRing R] [Field k] [CharZero k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f], Algebra.FiniteType ℤ R → Function.Injective φ → IsPullback π f' f (spMap φ) → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : A.IsLB) (r : ℕ) (b : Fin s → ℕ), IsAmpleLB (A.pull π) → 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • cls (L i) (h.isLB i) + cls A hA → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod (M.pull π)) q) := by
  intro R k _ _ _ φ X X' f f' π d _ _ hR hφ hpb s L σ h K M A hM hA r b hAmp hr hb hrel q hq
  haveI : IsDomain R := Function.Injective.isDomain φ hφ
  haveI : CharZero R := (RingHom.charZero_iff hφ).mpr inferInstance
  haveI := hR
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  haveI hstab := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  haveI : Smooth f := SmoothOfRelativeDimension.smooth d f
  haveI : Flat f := inferInstance
  let KR := FractionRing R
  let ι : KR →+* k := IsFractionRing.lift hφ
  have hφι : φ = ι.comp (algebraMap R KR) := by
    ext x
    simp [ι, IsFractionRing.lift_algebraMap]
  have hsp : spMap φ = spMap ι ≫ spMap (algebraMap R KR) := by
    rw [hφι]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) hpb ‹IsProper f›
  have hAπ : (A.pull π).IsLB := LB.isLB_pull hA π
  have hrelK' : Out.RelAmple (Over.mk f') (A.pull π) :=
    haveI : IsProper (Over.mk f').hom := (inferInstance : IsProper f')
    (relAmple_iff_isAmpleLB_of_isAffine (Over.mk f') hAπ).mpr hAmp
  have hgenPb := IsPullback.of_hasPullback f (spMap (algebraMap R KR))
  have hA1 : (A.pull (pullback.fst f (spMap (algebraMap R KR)))).IsLB := LB.isLB_pull hA _
  have hgen : Out.RelAmple (Over.mk (pullback.snd f (spMap (algebraMap R KR))))
      (A.pull (pullback.fst f (spMap (algebraMap R KR)))) :=
    FibreAmple.relAmple_of_fieldExtension hA ι hgenPb (hsp ▸ hpb) hA1 ((cls_eq_iff hA1 hA1).mp rfl) hrelK'
  obtain ⟨a, ha, hspread⟩ := AmpleSpread.relAmple_spread R KR (Over.mk f) A ‹IsProper f› hA hgen
  obtain ⟨p, hp, hdp, χ, hχ⟩ := exists_ringHom_zmod_prime_sq_isUnit_of_finiteType R hR a ha d
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  let c : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
  have hY := IsPullback.of_hasPullback f (spMap χ)
  haveI : SmoothOfRelativeDimension d (pullback.snd f (spMap χ)) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) hY inferInstance
  have h1 := IsPullback.of_hasPullback (pullback.snd f (spMap χ)) (spMap c)
  haveI : SmoothOfRelativeDimension d (pullback.snd (pullback.snd f (spMap χ)) (spMap c)) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) h1 inferInstance
  haveI : IsProper (pullback.snd (pullback.snd f (spMap χ)) (spMap c)) := inferInstance
  have hsp2 : spMap c ≫ spMap χ = spMap (c.comp χ) := by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hρ : IsPullback (pullback.fst (pullback.snd f (spMap χ)) (spMap c) ≫ pullback.fst f (spMap χ))
      (pullback.snd (pullback.snd f (spMap χ)) (spMap c)) f (spMap (c.comp χ)) :=
    hsp2 ▸ h1.paste_horiz hY
  set ρ := pullback.fst (pullback.snd f (spMap χ)) (spMap c) ≫ pullback.fst f (spMap χ) with hρdef
  set f₁ := pullback.snd (pullback.snd f (spMap χ)) (spMap c) with hf₁
  have hspec := hspread (ZMod p) (c.comp χ) (hχ.map c)
  have hid : spMap (RingHom.id (ZMod p)) ≫ spMap (c.comp χ) = spMap (c.comp χ) := by
    simp [spMap]
  have hAρ : (A.pull ρ).IsLB := LB.isLB_pull hA ρ
  have hamp1 : Out.RelAmple (Over.mk f₁) (A.pull ρ) :=
    FibreAmple.relAmple_of_fieldExtension hA (RingHom.id (ZMod p)) hρ
      (hid.symm ▸ IsPullback.of_hasPullback f (spMap (c.comp χ))) hAρ ((cls_eq_iff hAρ hAρ).mp rfl) hspec
  haveI : IsProper (Over.mk f₁).hom := (inferInstance : IsProper f₁)
  have hampX : IsAmpleLB (A.pull ρ) := (relAmple_iff_isAmpleLB_of_isAffine (Over.mk f₁) hAρ).mp hamp1
  have hproj : IsProjOver f₁ := (isProjOver_iff_isProper_and_exists_isAmpleLB f₁).mpr ⟨inferInstance, _, hampX⟩
  have hL := LogPair.relSnc_baseChange R (ZMod (p ^ 2)) χ X _ f _ _ d s L σ hY h
  let K₁ : CanonLB f₁ d := CanonLB.baseChange hρ K
  have hMρ : (M.pull ρ).IsLB := LB.isLB_pull hM ρ
  have hrel1 : r • cls (M.pull ρ) hMρ = r • cls K₁.bundle K₁.isLB +
      ∑ i, b i • pull (pullback.fst (pullback.snd f (spMap χ)) (spMap c))
        (cls ((L i).pull (pullback.fst f (spMap χ))) (LB.isLB_pull (h.isLB i) _)) + cls (A.pull ρ) hAρ := by
    have e := congrArg (pull ρ) hrel
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_nsmul, map_sum] at e
    have eK : cls K₁.bundle K₁.isLB = pull ρ (cls K.bundle K.isLB) := cls_pull K.isLB ρ K₁.isLB
    rw [cls_pull hM ρ, eK, cls_pull hA ρ]
    convert e using 4
    rw [cls_pull (h.isLB _) _, ← pull_comp]
  have hvan := charp_vanishing_liftable p _ _ (pullback.snd f (spMap χ)) f₁
    (pullback.fst (pullback.snd f (spMap χ)) (spMap c)) d h1 hproj hdp s
    (fun i => (L i).pull (pullback.fst f (spMap χ))) (fun i => Cartier.secPull (σ i) _) hL K₁
    (M.pull ρ) (A.pull ρ) hMρ hampX r b hr hb hrel1 q hq
  have hker : RingHom.ker φ ≤ RingHom.ker (c.comp χ) := by
    rw [(RingHom.injective_iff_ker_eq_bot φ).mp hφ]
    exact bot_le
  exact SemicontLB.subsingleton_coh_pull_of_ker_le R X f M hM (ZMod p) k (c.comp χ) φ _ X' f₁ f' ρ π hρ hpb hker q hvan

end GlobalTheory
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogResolutionMultiplierOpen
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
namespace GlobalTheory.Discrepancy

theorem isOpen_setOf_forall_specializes_of_finite {X Y : Type} [TopologicalSpace X] (s : Y → X)
    (P : Y → Prop) (hP : {w | ¬ P w}.Finite) :
    IsOpen {x : X | ∀ w : Y, s w ⤳ x → P w} := by
  have h : {x : X | ∀ w : Y, s w ⤳ x → P w} = (⋃ w ∈ {w | ¬ P w}, closure {s w})ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists,
      ← specializes_iff_mem_closure]
    exact ⟨fun h w hw hx => hw (h w hx), fun h w hx => by_contra fun hw => h w hw hx⟩
  rw [h]
  exact (hP.isClosed_biUnion fun w _ => isClosed_closure).isOpen_compl

theorem isOpen_kltAt_and_lcAt_of_isLogRes : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y), IsLogMult p n Δ η m G → IsLogRes p n η m G s K B → IsOpen {x : X | KltAt p n Δ x} ∧ IsOpen {x : X | LcAt p n Δ x} := by
  intro k _ _ X _ _ _ p n hproj hn Δ η m G Y _ _ s _ K B hlm hres
  obtain ⟨N, i, hi, hpi⟩ := hres.proj
  haveI : QuasiCompact (s ≫ p) := hpi ▸ inferInstance
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (s ≫ p)
  have hfin := (pullCart s G - m • K).finite_support_mult
  have hm : (0 : ℤ) < m := by exact_mod_cast hlm.pos
  have hiff := kltAt_lcAt_iff_of_isLogRes k X p n hproj hn Δ η m G Y s K B hlm hres
  constructor
  · have : {x : X | KltAt p n Δ x} =
        {x : X | ∀ w : Y, s w ⤳ x → (pullCart s G - m • K).mult w < m} := by
      ext x
      exact (hiff x).1
    rw [this]
    refine isOpen_setOf_forall_specializes_of_finite _ _ (hfin.subset fun w hw => ?_)
    simp only [Set.mem_setOf_eq, not_lt] at hw
    simp only [Function.mem_support]
    omega
  · have : {x : X | LcAt p n Δ x} =
        {x : X | ∀ w : Y, s w ⤳ x → (pullCart s G - m • K).mult w ≤ m} := by
      ext x
      exact (hiff x).2
    rw [this]
    refine isOpen_setOf_forall_specializes_of_finite _ _ (hfin.subset fun w hw => ?_)
    simp only [Set.mem_setOf_eq, not_le] at hw
    simp only [Function.mem_support]
    omega

end GlobalTheory.Discrepancy
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierIdealIndependentStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.multiplier_ideal_independent : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → ∀ J : X.IdealSheafData, IsMultIdeal p n η m G J ↔ (∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), (-F).RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) := by
  first | exact @_root_.GlobalTheory.Discrepancy.isMultIdeal_iff_regularAt | exact _root_.GlobalTheory.Discrepancy.isMultIdeal_iff_regularAt | (intros; apply _root_.GlobalTheory.Discrepancy.isMultIdeal_iff_regularAt <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutRelativeSncStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.spread_out_relative_snc : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ), IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : RelSnc f₁ d L₁ σ₁) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h.isLB i) = CechPic.pull π (cls (L₁ i) (h₁.isLB i))) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  first | exact @_root_.GlobalTheory.ModelSnc.exists_model_relSnc | exact _root_.GlobalTheory.ModelSnc.exists_model_relSnc | (intros; apply _root_.GlobalTheory.ModelSnc.exists_model_relSnc <;> assumption)
end

