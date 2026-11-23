module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0663
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2203
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberBaseChangeInjectiveLocalCompleteNormal
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0203
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLatticesIsoFormsProportionalRamification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.TraitUniq

theorem form_of_assoc {V V' W : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [CommRing W] [IsDomain W]
    {Dg : DegPre V} {Dg' : DegPre V'} {ϖ : V} {ϖ' : V'} {β : LinearMap.BilinForm ℤ Dg.X}
    {β' : LinearMap.BilinForm ℤ Dg'.X} (hβ : ∀ a b, β a b = β b a) (hβ' : ∀ a b, β' a b = β' b a)
    (hm : IsMonomial Dg ![ϖ] ![β]) (hm' : IsMonomial Dg' ![ϖ'] ![β']) (f : V →+* W) (f' : V' →+* W)
    (ε : Dg.X ≃+ Dg'.X) {w : W} (hw : Irreducible w) {m m' : ℕ} (h : Associated (f ϖ) (w ^ m))
    (h' : Associated (f' ϖ') (w ^ m'))
    (hε : ∀ y r r', PsiCoord Dg y r → PsiCoord Dg' (ε y) r' → Associated (f r ^ 2) (f' r' ^ 2)) :
    ∀ a b, (m : ℤ) * β a b = m' * β' (ε a) (ε b) := by
  have key : ∀ a, (m : ℤ) * β a a = m' * β' (ε a) (ε a) := by
    intro a
    obtain ⟨u₁, n₁, hn₁, c₁⟩ := hm a
    obtain ⟨u₂, n₂, hn₂, c₂⟩ := hm' (ε a)
    have a₁ : Associated (f (u₁ * ∏ i, ![ϖ] i ^ n₁ i)) (w ^ (m * n₁ 0)) := by
      rw [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow, pow_mul]
      exact (associated_unit_mul_left _ _ (u₁.isUnit.map f)).trans h.pow_pow
    have a₂ : Associated (f' (u₂ * ∏ i, ![ϖ'] i ^ n₂ i)) (w ^ (m' * n₂ 0)) := by
      rw [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow, pow_mul]
      exact (associated_unit_mul_left _ _ (u₂.isUnit.map f')).trans h'.pow_pow
    have a₃ := (a₁.pow_pow (n := 2)).symm.trans ((hε a _ _ c₁ c₂).trans (a₂.pow_pow (n := 2)))
    rw [← pow_mul, ← pow_mul] at a₃
    have e := GlobalTheory.SiegLoc.TraitOrd.eq_of_associated_pow hw a₃
    have h₀ : β a a = 2 * n₁ 0 := by simpa using hn₁ 0
    have h₀' : β' (ε a) (ε a) = 2 * n₂ 0 := by simpa using hn₂ 0
    rw [h₀, h₀']
    have e' := congrArg (fun x : ℕ => (x : ℤ)) e
    push_cast at e'
    linarith
  intro a b
  have k := key (a + b)
  have ka := key a
  have kb := key b
  simp only [map_add (f := _), LinearMap.add_apply] at k
  rw [hβ b a, hβ' (ε b) (ε a)] at k
  simp only [mul_add] at k
  linarith

theorem extIso {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {G₁ G₂ : Over (Sp W)} [GrpObj G₁]
    [GrpObj G₂] (h₁ : IsSemiAbelian G₁) (h₂ : IsSemiAbelian G₂)
    (e : (Over.pullback (jK W)).obj G₁ ≅ (Over.pullback (jK W)).obj G₂) (he : IsMonHom e.hom) :
    ∃ E : G₁ ≅ G₂, IsMonHom E.hom ∧ (Over.pullback (jK W)).map E.hom = e.hom := by
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W (FractionRing W) G₁ G₂ h₁ h₂ e.hom he
  obtain ⟨F₁, ⟨hF₁, hF₁'⟩, -⟩ :=
    GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W (FractionRing W) G₂ G₁ h₂ h₁ e.inv inferInstance
  refine ⟨⟨F, F₁, ?_, ?_⟩, hF, hF'⟩
  · exact (GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W (FractionRing W) G₁ G₁ h₁ h₁ (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, hF', hF₁', e.hom_inv_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
  · exact (GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W (FractionRing W) G₂ G₂ h₂ h₂ (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, hF₁', hF', e.inv_hom_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩

end GlobalTheory.Poinc.TraitUniq

namespace GlobalTheory.Poinc.TraitUniq

variable {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ}

theorem genFib (T : Trait F) {W : Type} [CommRing W] [IsDomain W] (f : T.V →+* W)
    (fK : FractionRing T.V →+* FractionRing W) (hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) :
    ∃ κ : ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).left ⟶ T.A.A.left,
      IsGrpPullback ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)) T.A.A (spMap fK) κ ∧
      κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) =
        pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f) :=
  _root_.GlobalTheory.Poinc.GenFibre.exists_generic_pullback g n o ζ F T W f fK hfK

theorem lamPull (T : Trait F) {W : Type} [CommRing W] [IsDomain W] (fK : FractionRing T.V →+* FractionRing W)
    (G'' : Over (Sp W)) [GrpObj G''] (β : G''.left ⟶ T.G.left)
    (κ : ((Over.pullback (jK W)).obj G'').left ⟶ T.A.A.left)
    (hκ : IsGrpPullback ((Over.pullback (jK W)).obj G'') T.A.A (spMap fK) κ)
    (hκβ : κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst G''.hom (jK W) ≫ β)
    (α₂ : (G2 ((Over.pullback (jK W)).obj G'')).left ⟶ (G2 F.univ.A).left) (hα₂ : IsSquare (κ ≫ T.α) α₂) :
    LBIso (abelian₂ ((Over.pullback (jK W)).obj G'') (T.U.LG.L.pull (pullback.fst G''.hom (jK W) ≫ β)))
      (F.univ.P.pull α₂) :=
  _root_.GlobalTheory.Poinc.lam_trait_fibre_eq_univ g n o ζ F T W fK G'' β κ hκ hκβ α₂ hα₂

end GlobalTheory.Poinc.TraitUniq

namespace GlobalTheory.Poinc.TraitUniq

variable {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ}

theorem isCN (T : Trait F) : GlobalTheory.TorRef.IsCN T.V := ⟨inferInstance, inferInstance, T.complete, T.char⟩

theorem isCN_of_base {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (h : GlobalTheory.Mum.Base W) : GlobalTheory.TorRef.IsCN W :=
  ⟨h.1.1, h.1.2.2.1, h.1.2.2.2, h.2⟩

theorem pull (T : Trait F) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.TorRef.IsCN W) (f : T.V →+* W)
    (hf : Function.Injective f) (hl : IsLocalHom f) (fK : FractionRing T.V →+* FractionRing W)
    (G'' : Over (Sp W)) [GrpObj G''] [IsCommMonObj G''] (β : G''.left ⟶ T.G.left)
    (hβ : IsGrpPullback G'' T.G (spMap f) β) (κ : ((Over.pullback (jK W)).obj G'').left ⟶ T.A.A.left)
    (hκ : IsGrpPullback ((Over.pullback (jK W)).obj G'') T.A.A (spMap fK) κ)
    (hκβ : κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst G''.hom (jK W) ≫ β)
    (α₂ : (G2 ((Over.pullback (jK W)).obj G'')).left ⟶ (G2 F.univ.A).left) (hα₂ : IsSquare (κ ≫ T.α) α₂) :
    ∃ (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G'')
      (ε : D'.toPre.X ≃+ T.D.toPre.X) (L : LB ((Over.pullback (jK W)).obj G'').left), L.IsLB ∧
      LBIso L (U'.LG.L.pull (pullback.fst G''.hom (jK W))) ∧
      LBIso (abelian₂ ((Over.pullback (jK W)).obj G'') L) (F.univ.P.pull α₂) ∧
      ∀ y r, PsiCoord T.D.toPre (ε y) r → ∃ u : Wˣ, PsiCoord D'.toPre y (u * f r) := by
  have pull_isLB {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) : (L.pull F).IsLB := by
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  have hΛ := lamPull T fK G'' β κ hκ hκβ α₂ hα₂
  have gB := (isGrpPullback_pullback G'' (jK W)).comp hβ
  obtain ⟨hr, hs⟩ := GlobalTheory.T.rigidified_symmetric_lineBundle_groupPullback _ _ _ T.G _ _ gB T.U.LG T.U.symG T.U.symG_gen
  have hα := hκ.comp T.cart
  obtain ⟨ha, hamp, hkt⟩ := _root_.GlobalTheory.SiegFibrePol.polAV_of_lam_univ o ζ g n F _ (spMap fK ≫ T.y) _ (κ ≫ T.α) α₂ hα hα₂ _
    (pull_isLB T.U.LG.isLB _) hr hs hΛ
  have hϖ : f T.ϖ ≠ 0 := fun h => T.irr.ne_zero (hf (h.trans (map_zero f).symm))
  obtain ⟨D', A', U', ε, hL, hc⟩ := _root_.GlobalTheory.UnifCoordPull.exists_unif_psiCoord T.V W (isCN T) hW f hl T.G T.semi T.D T.A T.U
    {p | T.ϖ ∉ p.asIdeal} (PrimeSpectrum.isOpen_basicOpen (a := T.ϖ))
    (fun y => T.mono.psiUnitOn y fun p hp => by simpa using hp) (fun h => hϖ (RingHom.mem_ker.1 h)) G'' β hβ ha hr hs
    hamp hkt
  exact ⟨D', A', U', ε, _, pull_isLB T.U.LG.isLB _, hL, hΛ, hc⟩

end GlobalTheory.Poinc.TraitUniq

namespace GlobalTheory.Poinc.TraitUniq

theorem traitUniq : TraitUniqSt := by
  intro g n o _ ζ F T T' W _ _ _ f f' fK fK' hW hdvr hf hf' hl hl' hK hK' hy w m m' hw hm hm'
  have pull_isLB {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) : (L.pull F).IsLB := by
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  have semiPull {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G]
      (h : IsSemiAbelian G) : IsSemiAbelian ((Over.pullback f).obj G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := h.comm; infer_instance
    · have := h.smooth; change Smooth (pullback.snd G.hom f); infer_instance
    · have := h.separated; change IsSeparated (pullback.snd G.hom f); infer_instance
    · have := h.quasiCompact; change QuasiCompact (pullback.snd G.hom f); infer_instance
    · have := h.geomConnected; change GeometricallyConnected (pullback.snd G.hom f); infer_instance
    · intro Ω _ _ q
      obtain ⟨E⟩ := h.fibres Ω (q ≫ f)
      exact ⟨torusExtOfIso (pullCompIso q f G) E⟩
  haveI := hdvr
  have hWC := isCN_of_base hW
  have hs₁ : IsSemiAbelian ((Over.pullback (spMap f)).obj T.G) := semiPull (spMap f) T.G T.semi
  have hs₂ : IsSemiAbelian ((Over.pullback (spMap f')).obj T'.G) := semiPull (spMap f') T'.G T'.semi
  obtain ⟨κ₁, hκ₁, hκβ₁⟩ := genFib T f fK hK
  obtain ⟨κ₂, hκ₂, hκβ₂⟩ := genFib T' f' fK' hK'
  have hα₁ := hκ₁.comp T.cart
  have hα₂ := (hκ₂.comp T'.cart).congr hy.symm rfl
  obtain ⟨e, he, heα⟩ := grpPullback_iso hα₁ hα₂
  obtain ⟨E, hE, hEe⟩ := extIso hs₁ hs₂ e he
  have w₁ := hα₁.1.w
  let α₂ := pullback.map ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).hom
    ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).hom F.univ.A.hom F.univ.A.hom
    (κ₁ ≫ T.α) (κ₁ ≫ T.α) (spMap fK ≫ T.y) w₁.symm w₁.symm
  have hsq : IsSquare (κ₁ ≫ T.α) α₂ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hβ' : IsGrpPullback ((Over.pullback (spMap f)).obj T.G) T'.G (spMap f')
      (E.hom.left ≫ pullback.fst T'.G.hom (spMap f')) :=
    ((isGrpPullback_of_iso E).comp (isGrpPullback_pullback T'.G (spMap f'))).congr (Category.id_comp _) rfl
  have hκ' := ((isGrpPullback_of_iso e).comp hκ₂).congr (Category.id_comp _) rfl
  have hκβ' : (e.hom.left ≫ κ₂) ≫ T'.U.gen.inv.left ≫ pullback.fst T'.G.hom (jK T'.V) =
      pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ E.hom.left ≫ pullback.fst T'.G.hom (spMap f') := by
    rw [Category.assoc, hκβ₂, ← Category.assoc, ← Category.assoc, ← hEe]
    congr 1
    exact pullback.lift_fst _ _ _
  have hsq' : IsSquare ((e.hom.left ≫ κ₂) ≫ T'.α) α₂ := by rw [Category.assoc, heα]; exact hsq
  obtain ⟨E₁, A₁, U₁, ε₁, L₁, l₁, i₁, m₁, c₁⟩ := pull T hWC f hf hl fK _ _ (isGrpPullback_pullback T.G (spMap f))
    κ₁ hκ₁ hκβ₁ α₂ hsq
  obtain ⟨E₂, A₂, U₂, ε₂, L₂, l₂, i₂, m₂, c₂⟩ := pull T' hWC f' hf' hl' fK' _ _ hβ' _ hκ' hκβ' α₂ hsq'
  have hΛ : LBIso (abelian₂ _ L₂) (abelian₂ _ L₁) :=
    LBIso.trans (DVR.linComb_isLB _ l₂ _ _) (pull_isLB F.univ.isLB _) (DVR.linComb_isLB _ l₁ _ _) m₂ m₁.symm
  obtain ⟨ε, hε⟩ := GlobalTheory.SqUnifCoord.main W hWC _ hs₁ E₂ E₁ A₂ A₁ U₂ U₁
    (GlobalTheory.squares_iso_of_lam_generic W hWC _ hs₁ E₂ E₁ A₂ A₁ U₂ U₁ L₂ L₁ l₂ l₁ i₂ i₁ hΛ)
  let ε₀ : T.D.toPre.X ≃+ T'.D.toPre.X := (ε₁.symm.trans ε).trans ε₂
  have hε₀ : ∀ z r₁ r₂, PsiCoord T.D.toPre z r₁ → PsiCoord T'.D.toPre (ε₀ z) r₂ →
      Associated (f r₁ ^ 2) (f' r₂ ^ 2) := by
    intro z r₁ r₂ h₁ h₂
    obtain ⟨u₁, k₁⟩ := c₁ (ε₁.symm z) r₁ (by rwa [AddEquiv.apply_symm_apply])
    obtain ⟨u₂, k₂⟩ := c₂ (ε (ε₁.symm z)) r₂ h₂
    have := hε _ _ _ k₂ k₁
    rw [mul_pow, mul_pow] at this
    exact ((associated_unit_mul_left _ _ (u₁.isUnit.pow 2)).symm.trans this.symm).trans
      (associated_unit_mul_left _ _ (u₂.isUnit.pow 2))
  exact ⟨ε₀, form_of_assoc T.symm T'.symm T.mono T'.mono f f' ε₀ hw hm hm' hε₀⟩

end GlobalTheory.Poinc.TraitUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelFiniteFlatSurjectiveOverBase
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TwistKernel

theorem twisted_kernel : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∃ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd A T).left ∧ Flat (h ≫ snd A T).left ∧ Surjective (h ≫ snd A T).left ∧ ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t := by
  intro R _ _ A _ hA L hL ha T _ hT N hN
  have := hA.proper
  have : LocallyOfFiniteType (A ⊗ T).hom := by
    have := hT
    first
    | infer_instance
    | (show LocallyOfFiniteType (pullback.fst A.hom T.hom ≫ A.hom); infer_instance)
    | (show LocallyOfFiniteType (pullback.snd A.hom T.hom ≫ T.hom); infer_instance)
  have : IsLocallyNoetherian (A ⊗ T).left := LocallyOfFiniteType.isLocallyNoetherian (A ⊗ T).hom
  have hΛ : Fam A (abelian₂ A L) := ⟨LB.isLB_linComb hL _ _,
    (GlobalTheory.CubeDual.isAdditive_lam GlobalTheory.CubeTop.cubeTheorem hA hL (LB.isLB_linComb hL _ _)).1⟩
  obtain ⟨H, h, hh, hH⟩ := GlobalTheory.DualLocus.exists_closed_same (Sp R) A (A ⊗ T) hA
    (ev (abelian₂ A L) (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ fst A T)) (ev N (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T))
    (hΛ.ev (fst A T)) (hN.ev (snd A T))
  have rep : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T),
      Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t := by
    intro Y a t
    rw [← hH Y (lift a t), same_iff hΛ.isLB hN.isLB, same_iff (hΛ.ev (fst A T)).isLB (hN.ev (snd A T)).isLB,
      evc_ev hΛ.isLB, evc_ev hN.isLB]
    simp
  exact ⟨H, h, hh, _root_.GlobalTheory.TwistKerFinite.isFinite_twisted_kernel R A hA L hL ha T hT N hN H h hh rep,
    _root_.GlobalTheory.TwistFlat.flat_twisted_kernel R A hA L hL ha T hT N hN H h hh rep (_root_.GlobalTheory.TwistKerFinite.isFinite_twisted_kernel R A hA L hL ha T hT N hN H h hh rep),
    _root_.GlobalTheory.TwistKerSurj.surjective_twist_kernel R A hA L hL ha T hT N hN H h hh rep, rep⟩

end GlobalTheory.TwistKernel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UMemBaseChangeValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.MemBC
open GlobalTheory.ArcPull

theorem uMem_baseChange_values : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (j : V →+* V') (k : FractionRing V →+* FractionRing V'), IsCN V' → Function.Injective j → IsLocalHom j → (∀ v : V, k (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (j v)) → ∃ 𝔫 : UMem X₁ z₁ act V' (j.comp ev) X (fun i => j (t i)) δ, (∀ r, 𝔫.yK r = k (𝔪.yK r)) ∧ ∀ a mu, 𝔪.YY a mu → 𝔫.YY a mu := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 V' _ _ _ j k hV' hj hl hkv
  have hkj : k = fracMap hj := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors V) (RingHom.ext fun v => ?_)
    exact (hkv v).trans (fracMap_algebraMap hj v).symm
  have hV := 𝔪.cn
  have hAd : AdmBase V (maximalIdeal V) := ⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩
  have hAd' : AdmBase V' (maximalIdeal V') := ⟨hV'.1, inferInstance, hV'.2.1, hV'.2.2.1⟩
  have hI : (maximalIdeal V).map j ≤ maximalIdeal V' := map_maximalIdeal_le j
  obtain ⟨D', hD, A', gA, U', hPU, hgA, htA, hrel⟩ := exists_pull_gen hAd hAd' j hj hI 𝔪.semi 𝔪.U
  have hwl : LBIso A'.L (X₁.ρ.P.L.pull (gA ≫ 𝔪.φ)) :=
    LBIso.trans A'.isLB (pull_isLB 𝔪.A.isLB _) (pull_isLB X₁.ρ.P.isLB _) htA (lbIso_pull_comp ⟨𝔪.wl, 𝔪.wl_gen⟩ gA)
  obtain ⟨wl, hwl⟩ := hwl
  haveI := 𝔪.loc
  have hk : 1 ≤ X₁.S.r * X₁.S.N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))
  refine ⟨{
    cn := hV'
    loc := inferInstance
    reg := regAt_comp X₁ z₁ ev j hj 𝔪.reg
    yK := (fracMap hj).comp 𝔪.yK
    yK_eq := yK_comp X₁ z₁ ev j hj 𝔪.yK 𝔪.yK_eq
    D := D'
    e₈ := 𝔪.e₈.trans hD.xe.symm
    G := (Over.pullback (specOf j)).obj 𝔪.G
    semi := IsSemiAbelian.pullback _ _ 𝔪.semi
    A := A'
    U := U'
    φ := gA ≫ 𝔪.φ
    cart := (hgA.comp 𝔪.cart).congr (by rw [spMap_comp]) rfl
    wl := wl
    wl_gen := hwl
    equiv := fun a a' ha => ?_
    psi := fun mu => ?_ }, fun r => ?_, ?_⟩
  · obtain ⟨E, hE1, hE2⟩ := 𝔪.equiv a a' ha
    have := E.homG
    obtain ⟨E', h1, h2, -⟩ := EndBaseChange.exists_end hD hPU E ((Over.pullback (specOf j)).map E.aG)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    refine ⟨E', ?_, fun mu => ?_⟩
    · rw [← Category.assoc, aA_comm j hj 𝔪.U.toUnifPre U'.toUnifPre gA hgA hrel E E' h1, Category.assoc, hE1,
        Category.assoc]
    · apply hD.xe.injective
      simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply, h2, hE2]
  · obtain ⟨u, hu⟩ := 𝔪.psi mu
    have hr : Formalism.L2.Pj.PsiCoord 𝔪.D.toPre (hD.xe (hD.xe.symm (𝔪.e₈ mu))) (u * mono W t δ mu) := by
      rw [AddEquiv.apply_symm_apply]; exact hu
    obtain ⟨u', hu'⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD _ _ hr
    refine ⟨u' * Units.map j.toMonoidHom u, ?_⟩
    have hm : mono W (fun i => j (t i)) δ mu = j (mono W t δ mu) := by simp [mono, map_prod, map_pow]
    convert hu' using 1
    · exact AddEquiv.trans_apply _ _ _
    · rw [hm, map_mul]
      simp [_root_.mul_assoc]
  · show fracMap hj (𝔪.yK r) = k (𝔪.yK r)
    rw [hkj]
  · rintro a mu ⟨p, x, hpy, hqx, hxφ⟩
    obtain ⟨p', x', σ, hσ, hp'y, hq', hx'⟩ := yy_pull' hV hV' j hj hl 𝔪.semi 𝔪.U D' hD A' gA U' hPU hgA hrel _ hk p x hqx
    refine ⟨p', x', ?_, hq', ?_⟩
    · show p'.y = (𝔪.e₈.trans hD.xe.symm) mu
      rw [AddEquiv.trans_apply, hp'y, hpy]
    · show x'.left ≫ gA ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V') (AlgebraicClosure (FractionRing V'))).comp
          ((fracMap hj).comp 𝔪.yK)) ≫ (X₁.ρ.pt a).left
      rw [← Category.assoc, hx', Category.assoc, hxφ, ← Category.assoc, ← spMap_comp]
      congr 2
      rw [← RingHom.comp_assoc, hσ, RingHom.comp_assoc]

end GlobalTheory.Poinc.Sep.MemBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationMovesAlongDvrInjectionGivenFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.UnifMoveGiven


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear GlobalTheory.UnifMove in
theorem exists_pull_given {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R}
    {I' : Ideal R'} (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g)
    (hI : I.map g ≤ I') (gK : FractionRing R →+* FractionRing R') (sq : spMap gK ≫ jK R = jK R' ≫ spMap g)
    {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G)
    (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (gA : A'.A.left ⟶ A.A.left)
    (gpA : IsGrpPullback A'.A A.A (spMap gK) gA) (hL : LBIso A'.L (A.L.pull gA)) (dA : A'.g = A.g) :
    ∃ (D' : DegData R' I') (hD : IsPullDeg g D.toPre D'.toPre)
      (U' : Unif I' D' A' ((Over.pullback (specOf g)).obj G)),
      IsPullUnif g hD (Iso.refl _) U U' ∧
      U'.gen.hom.left ≫ gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
        pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g) := by
  have hU : UnifBaseChangeSt := GlobalTheory.UnifPullGuards.unifBaseChange_holds
  have hψ : PsiOnExistsSt := psiOnExists
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap gK ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = pullback.fst G.hom (spMap g) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      (hL.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec ((Over.pullback (specOf g)).obj G))
      (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) := ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
    rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := hψ R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -, hgenU, hPU⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨D', hD, U', hPU, by rw [hgenU]; exact heA⟩


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear GlobalTheory.UnifMove in
theorem move_given : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'], IsAdicComplete (maximalIdeal V) V → IsAdicComplete (maximalIdeal V') V' → ∀ (φ : V →+* V') (φK : FractionRing V →+* FractionRing V'), φK.comp (algebraMap V _) = (algebraMap V' _).comp φ → (maximalIdeal V).map φ ≤ maximalIdeal V' → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (A' : PolAV (Sp (FractionRing V'))) (ψ : A'.A.left ⟶ A.A.left), IsGrpPullback A'.A A.A (spMap φK) ψ → LBIso A'.L (A.L.pull ψ) → A'.g = A.g → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra (FractionRing V') F], (algebraMap (FractionRing V') F).comp φK = algebraMap (FractionRing V) F → ∃ (D' : DegData V' (maximalIdeal V')) (hD : IsPullDeg φ D.toPre D'.toPre) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal V') D' A' G'), IsSemiAbelian G' ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (q : QkPt D.toPre F k) (x : TFK (R := V) F ⟶ A.A), QkToAkU U.toUnifPre F k q x → ∃ (q' : QkPt D'.toPre F k) (x' : TFK (R := V') F ⟶ A'.A), hD.xe q'.y = q.y ∧ x'.left ≫ ψ = x.left ∧ QkToAkU U'.toUnifPre F k q' x' := by
  intro V V' _ _ _ _ _ _ hV hV' φ φK hK hI D A G _ _ U A' ψ gp hL hg F _ _ _ hF
  have aV : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  have aV' : AdmBase V' (IsLocalRing.maximalIdeal V') := ⟨inferInstance, inferInstance, inferInstance, hV'⟩
  have hK' : ∀ r, φK (algebraMap V _ r) = algebraMap V' _ (φ r) := fun r => RingHom.congr_fun hK r
  have hφ : Function.Injective φ := fun a b h =>
    IsFractionRing.injective V (FractionRing V) (φK.injective (by rw [hK', hK', h]))
  have sq : spMap φK ≫ jK V = jK V' ≫ spMap φ := by
    refine (Spec.map_comp _ _).symm.trans (Eq.trans ?_ (Spec.map_comp _ _))
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hK
  have hFc : ∀ r : V, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) r) =
      algebraMap (FractionRing V') F (algebraMap V' (FractionRing V') (φ r)) := fun r => by
    rw [← hK', ← hF]; rfl
  have sF : jFK (R := V') F ≫ spMap φK = jFK (R := V) F := by
    refine (Spec.map_comp _ _).symm.trans ?_
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hF
  obtain ⟨D', hD, U', hU, hgen⟩ := exists_pull_given aV aV' φ hφ hI φK sq
    (isSemiAbelian_of_unifPre_dvr V D A G U.toUnifPre) U A' ψ gp hL hg
  refine ⟨D', hD, _, inferInstance, inferInstance, U',
    isSemiAbelian_of_unifPre_dvr V' D' A' _ U'.toUnifPre, fun k hk q x H => ?_⟩
  obtain ⟨τ, hτ, -⟩ := exists_qk_pull_equiv abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 V V' φ D.toPre D'.toPre hD
    D.tau_bimult D'.tau_bimult F hFc k
  obtain ⟨hy, hg'⟩ := (hτ q _).1 rfl
  have w : x.left ≫ A.A.hom = jFK (R := V') F ≫ spMap φK := (Over.w x).trans sF.symm
  let x' : TFK (R := V') F ⟶ A'.A := Over.homMk (gp.1.lift x.left (jFK (R := V') F) w) (gp.1.lift_snd _ _ _)
  have hx : x'.left ≫ ψ = x.left := gp.1.lift_fst _ _ _
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  refine ⟨τ q, x', by rw [hy]; exact hD.xe.apply_symm_apply _, hx,
    qkToAk_baseChange abelianSchemeLaws_all.1.globalFns abelianSchemeLaws_all.1.secBaseChange V V' _ _ aV aV' φ D A G U
      _ (Iso.refl _) mR A' D' hD U' hU F hFc k hk q x (τ q) x' hy hg' ?_ H⟩
  have n : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf φ) =
      pullback.fst G.hom (spMap φ) := Category.id_comp _
  rw [hbc, ← hgen, ← Category.assoc U'.gen.inv.left, n, Category.id_comp, ← Category.assoc, hx]

end GlobalTheory.UnifMoveGiven

end
end

