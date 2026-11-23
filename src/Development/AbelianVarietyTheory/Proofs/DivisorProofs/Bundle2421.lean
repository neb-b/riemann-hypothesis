module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2338
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFibreIsoSharpTorsionGivesFactorIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

theorem GlobalTheory.Poinc.Sep.conj_fibre_eighth_root : ∀ (l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ j, 1 ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsUnit (l : V₁) → ∀ (Q : Data V) (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (σ : K ≃+* K), ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) → (∀ mu (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left), q ≫ pullback.fst D.P.A.hom (spMap ev) = spMap ev ≫ (D.c (e mu)).left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst D.P.A.hom (spMap ev)) → ∀ (a : Q.X) (p : Sp K ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = spMap (ev.comp ρ) ≫ (Q.c a).left → p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = 𝟙 _ → ∃ (f : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left) (f₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left), IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f ∧ IsSquare f f₂ ∧ (∀ (ψ₀ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 Q.B).left) (ψσ : (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left ⟶ (G2 Q.B).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ))) ψ₀ → IsSquare (pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) ψσ → LBIso ((abelian₂ Q.B Q.M.L).pull ψ₀) ((abelian₂ Q.B Q.M.L).pull (f₂ ≫ ψσ))) ∧ p ≫ f ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) = spMap σ.toRingHom ≫ p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) := by
  intro l hl hlo W hW j hj V V₁ _ _ _ _ _ hlu Q ρ hρ D e hSh K _ _ ev σ f hf hL ht hc a p hpf hps
  obtain ⟨pr, w, hmon, huniv, hwgen, hc4, -⟩ := hSh
  obtain ⟨f₁, hf₁, hcomp⟩ := GlobalTheory.T.eighth_power_fibre_iso_eq_coordinatewise_power l hl hlo W hW j hj V V₁ hlu Q ρ hρ D pr w hmon huniv hwgen K ev σ f hf hL ht
  have hw : f₁ ≫ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).hom = ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).hom := by
    simpa using hf₁.1.w
  let f' : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) := Over.homMk f₁ hw
  have hsq : IsSquare f₁ (f' ⊗ₘ f').left := by
    constructor
    · rw [← Over.comp_left, tensorHom_fst]; rfl
    · rw [← Over.comp_left, tensorHom_snd]; rfl
  refine ⟨f₁, (f' ⊗ₘ f').left, hf₁, hsq, ?_, ?_⟩
  · intro ψ₀ ψσ h0 hσ
    exact GlobalTheory.T.exists_e8_weighted_bundle_iso_pullback W hW V V₁ Q ρ D pr w hmon huniv hwgen K ev σ f hf hL f₁ hf₁ hcomp _ hsq ψ₀ ψσ h0 hσ
  · let mu0 : Fin 8 → Q.X := Pi.single 0 a
    have hsec : (spMap ev ≫ (D.c (e mu0)).left) ≫ D.P.A.hom = 𝟙 _ ≫ spMap ev := by
      rw [Category.assoc, Over.w]; simp
    let q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left := pullback.lift (spMap ev ≫ (D.c (e mu0)).left) (𝟙 _) hsec
    have hq1 : q ≫ pullback.fst D.P.A.hom (spMap ev) = spMap ev ≫ (D.c (e mu0)).left := pullback.lift_fst _ _ _
    have hq2 : q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ := pullback.lift_snd _ _ _
    have hspc : spMap (ev.comp ρ) = spMap ev ≫ spMap ρ := by
      simp [spMap]
    have e1 : p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = q ≫ pullback.fst D.P.A.hom (spMap ev) ≫ (pr 0).left ≫ pullback.fst Q.B.hom (spMap ρ) := by
      rw [hpf, reassoc_of% hq1, ← Over.comp_left_assoc, hc4, hspc, Category.assoc]
      simp [mu0]
    have e2 : p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = q ≫ pullback.snd D.P.A.hom (spMap ev) := by
      rw [hps, hq2]
    have h1 := hcomp 0 _ q p e1 e2
    have h2 := hc mu0 q hq1 hq2
    rw [← h1, reassoc_of% h2, e1]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerPresentationEndomorphismsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc

theorem sharpOver_pullback_end : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left) (c : SiegPre g n ζ (u ≫ F.s)), SiegPB c F.univ u → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T₁ : Over T) (y : Fin 8 → (T₁ ⟶ c.A)), ∃! x : T₁ ⟶ P.A, ∀ a, x ≫ pr a = y a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → ∃ c' : SiegPre g n ζ ((f ≫ u) ≫ F.s), SiegPB c' F.univ (f ≫ u) ∧ ∃ pr' : Fin 8 → (P'.A ⟶ c'.A), (∀ a, IsMonHom (pr' a)) ∧ (∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ c'.A)), ∃! x : T₁ ⟶ P'.A, ∀ a, x ≫ pr' a = y a) ∧ LBIso P'.L (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2)) ∧ ∀ (b : P.A ⟶ P.A) (k : Fin 8 → Fin 8 → ℤ), (∀ a, b ≫ pr a = (List.ofFn fun v => pr v ^ k a v).prod) → ∃ b' : P'.A ⟶ P'.A, (∀ a, b' ≫ pr' a = (List.ofFn fun v => pr' v ^ k a v).prod) ∧ b'.left ≫ φ = φ ≫ b.left := by
  intro g n o _ ζ F W T T' P P' u f φ c hc pr hpr huniv hbun hφ hL
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback g n o ζ T T' (u ≫ F.s) ((f ≫ u) ≫ F.s) f c (by rw [Category.assoc])
  have hc'u : SiegPB c' F.univ (f ≫ u) := GlobalTheory.SiegelPullComp.pb_comp hc hc'
  obtain ⟨ψ, ψ₂, hψ, hsq, hw, -⟩ := hc'
  have hp := hψ.1
  have hφp := hφ.1
  have wa : ∀ a, (φ ≫ (pr a).left) ≫ c.A.hom = P'.A.hom ≫ f := fun a => by
    rw [Category.assoc, Over.w, hφp.w]
  let pr' : Fin 8 → (P'.A ⟶ c'.A) := fun a =>
    Over.homMk (hp.lift (φ ≫ (pr a).left) P'.A.hom (wa a)) (hp.lift_snd _ _ _)
  have hpr'ψ : ∀ a, (pr' a).left ≫ ψ = φ ≫ (pr a).left := fun a => hp.lift_fst _ _ _
  have push_comp : ∀ {T₁ : Over T'} (x : T₁ ⟶ P'.A) a, pushPt hψ.1.w (x ≫ pr' a) = pushPt hφ.1.w x ≫ pr a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ (pr' a).left) ≫ ψ = (x.left ≫ φ) ≫ (pr a).left
      rw [Category.assoc, hpr'ψ, Category.assoc])
  have pmψ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ c'.A), pushPt hψ.1.w (x * y) = pushPt hψ.1.w x * pushPt hψ.1.w y :=
    fun x y => map_mul (pushHom hψ _) x y
  have pmφ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ P'.A), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have injψ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ c'.A}, pushPt hψ.1.w x = pushPt hψ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hψ _ e
  have injφ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ P'.A}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hφ _ e
  have hmon : ∀ a, IsMonHom (pr' a) := fun a => by
    haveI := hpr a
    refine isMonHom_of_mul _ fun T₁ x y => injψ ?_
    rw [push_comp, pmψ, push_comp, push_comp, pmφ]
    exact MonObj.mul_comp _ _ _
  have huniv' : ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ c'.A)), ∃! x : T₁ ⟶ P'.A, ∀ a, x ≫ pr' a = y a := by
    intro T₁ y
    obtain ⟨x₀, hx₀, hu₀⟩ := huniv (Over.mk (T₁.hom ≫ f)) (fun a => pushPt hψ.1.w (y a))
    let x : T₁ ⟶ P'.A := Over.homMk (hφp.lift x₀.left T₁.hom (Over.w x₀)) (hφp.lift_snd _ _ _)
    have hx : pushPt hφ.1.w x = x₀ := Over.OverMorphism.ext (hφp.lift_fst _ _ _)
    have key : ∀ z : T₁ ⟶ P'.A, (∀ a, z ≫ pr' a = y a) ↔ ∀ a, pushPt hφ.1.w z ≫ pr a = pushPt hψ.1.w (y a) :=
      fun z => forall_congr' fun a => ⟨fun h => by rw [← push_comp, h], fun h => injψ (by rw [push_comp, h])⟩
    refine ⟨x, (key x).2 (by rw [hx]; exact hx₀), fun z hz => injφ ?_⟩
    exact (hu₀ _ ((key z).1 hz)).trans hx.symm
  have hq : ∀ ab : Fin 8 × Fin 8, (lift (pr' ab.1) (pr' ab.2)).left ≫ ψ₂ = φ ≫ (lift (pr ab.1) (pr ab.2)).left :=
    fun ab => (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq hsq (T := Over.mk (φ ≫ P.A.hom)) (T' := P'.A)
      (𝟙 P'.A.left) (pr' ab.1) (pr' ab.2) (Z := P.A) φ (pr ab.1) (pr ab.2)
      ((Category.id_comp _).trans (hpr'ψ ab.1)) ((Category.id_comp _).trans (hpr'ψ ab.2)))
  have hbun' : LBIso P'.L (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left)
      (fun ab => W ab.1 ab.2)) := by
    let ε : Fin 8 × Fin 8 → ℤ := fun ab => W ab.1 ab.2
    let q := fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left
    let q' := fun ab : Fin 8 × Fin 8 => (lift (pr' ab.1) (pr' ab.2)).left
    have l0 : (LB.LinComb c.P q ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB q ε
    have l1 : (LB.LinComb c.P (fun ab => φ ≫ q ab) ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB _ ε
    have l2 : (LB.LinComb (c.P.pull ψ₂) q' ε).IsLB :=
      ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB (c.P.pull ψ₂) (pull_isLB c.isLB ψ₂) q' ε
    have l3 : (LB.LinComb c'.P q' ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB q' ε
    have refl1 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) :=
      ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ l1
    have i2 : LBIso (P.L.pull φ) ((LB.LinComb c.P q ε).pull φ) := GlobalTheory.SiegelPullComp.iso_pull φ hbun
    have i3 : LBIso ((LB.LinComb c.P q ε).pull φ) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) :=
      LBIso.chartPull (chartPullOut c.P q ε φ _ fun _ => rfl) (chartPullId _) refl1
    have i4 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) (LB.LinComb (c.P.pull ψ₂) q' ε) :=
      LBIso.chartPull (chartPullId _)
        (chartPullLinComb c.P ψ₂ q' (fun ab => φ ≫ q ab) ε (𝟙 _) fun ab => (hq ab).trans (Category.id_comp _).symm) refl1
    have i5 : LBIso (LB.LinComb (c.P.pull ψ₂) q' ε) (LB.LinComb c'.P q' ε) :=
      GlobalTheory.PowPrimitive.lbIso_linComb hw.symm q' ε
    have h1 := pull_isLB P.isLB φ
    have h2 := pull_isLB l0 φ
    exact LBIso.trans P'.isLB h1 l3 hL (LBIso.trans h1 h2 l3 i2 (LBIso.trans h2 l1 l3 i3 (LBIso.trans l1 l2 l3 i4 i5)))
  refine ⟨c', hc'u, pr', hmon, huniv', hbun', ?_⟩
  intro b k hb
  obtain ⟨b', hb', -⟩ := huniv' P'.A (fun a => (List.ofFn fun v => pr' v ^ k a v).prod)
  refine ⟨b', hb', ?_⟩
  let U : Over.mk (P'.A.hom ≫ f) ⟶ P.A := pushPt hφ.1.w (𝟙 P'.A)
  have hU : ∀ v, pushPt hψ.1.w (pr' v) = U ≫ pr v := fun v => by
    rw [← push_comp, Category.id_comp]
  have e : ∀ a, pushPt hφ.1.w b' ≫ pr a = (U ≫ b) ≫ pr a := fun a => by
    rw [← push_comp, hb' a, Category.assoc U b (pr a), hb a]
    have h1 : pushPt hψ.1.w (List.ofFn fun v => pr' v ^ k a v).prod
        = pushHom hψ P'.A (List.ofFn fun v => pr' v ^ k a v).prod := rfl
    have h2 : U ≫ (List.ofFn fun v => pr v ^ k a v).prod = preHom U (List.ofFn fun v => pr v ^ k a v).prod := rfl
    rw [h1, h2, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 1
    apply List.ofFn_inj.mpr
    funext v
    simp only [Function.comp_apply, map_zpow]
    congr 1
    exact hU v
  obtain ⟨x₀, -, hu₀⟩ := huniv (Over.mk (P'.A.hom ≫ f)) (fun a => pushPt hφ.1.w b' ≫ pr a)
  have := (hu₀ _ fun a => rfl).trans (hu₀ _ fun a => (e a).symm).symm
  have := congrArg (fun z => z.left) this
  simpa [U, pushPt] using this

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndUOfOLinear
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.UT.OLinEnd

noncomputable section

namespace GlobalTheory.Mum.EFix

section Pts
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
variable {O : Type} [Ring O] [StarRing O] [Module O D.X]

theorem exists_gtPtAct (hG : GlobalFnsSt) (oa : D.OAct O) {k : ℕ} (a : O) (p : QkPt D F k) :
    ∃ q : QkPt D F k, q.y = a • p.y ∧ GtPtAct oa a p.g q.g := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hr := oa.onB.rosati (star a)
  have hbal := oa.tau_bal (star a)
  rw [star_star] at hr hbal
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ hr
  have cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x := fun T x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  have ra := fun {y : (TF (R := R) F).left} {J} (hJ : Good D.P.L y J) =>
    ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := TF (R := R) F) hJ
  have vu : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ x w : TF (R := R) F ⟶ D.P.A,
      val (LB.pullGen D.P.L _ _ u (lift x w).left) (𝟙 _) y J = val₂ u y J x w := fun hJ x w => by
    rw [val_pull hJ, Category.id_comp]; rfl
  have u₁ : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ w, val₂ u y J 1 w = 1 := fun {y J} hJ w => by
    have C : IsCub (cubV D.cub y J) := isCub_cubV D.cub hJ
    have e := (ra hJ 1 1 w).1
    rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have u₂ : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ w, val₂ u y J w 1 = 1 := fun {y J} hJ w => by
    have C : IsCub (cubV D.cub y J) := isCub_cubV D.cub hJ
    have e := (ra hJ 1 1 w).2
    rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have ex : ∀ g : GtPtF D F, ∃ g' : GtPtF D F, g'.b = g.b ≫ oa.onB.act a ∧ ∀ χ y J, Good D.P.L y J →
      val (g'.s χ) (𝟙 _) y J = val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := by
    intro g
    have vv : ∀ χ y J, Good D.P.L y J → val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 _) y J =
        val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := fun χ y J hJ =>
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (vu hJ _ _))
    obtain ⟨g', hb, hv⟩ := exists_gt (g.b ≫ oa.onB.act a) (fun χ => LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left))
      (fun χ => mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ hu _)) (fun χ U _ h => by
        refine (prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _ (prod_gt g.b (star a • χ) h)
          (prod_ros _ _ (cP D _ χ) g.b h)).trans ?_
        rw [prod_gt, cf]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) (fun y J hJ => by
        rw [vv 0 y J hJ, smul_zero, cPoint_zero, u₁ hJ, _root_.mul_one]
        exact (val_corr hJ g.s_zero _).trans (val_one _)) (fun χ χ' y J hJ => by
        have e₁ := (ra hJ (cP D _ χ) (cP D _ χ') g.b).1
        have e₂ := gt_mul (𝟙 (TF (R := R) F)) hJ g (star a • χ) (star a • χ')
        rw [Category.id_comp, cf, cf, Over.id_left] at e₂
        rw [vv _ y J hJ, vv _ y J hJ, vv _ y J hJ, smul_add, cPoint_add, _root_.mul_assoc]
        refine (congrArg _ e₁).trans ?_
        rw [← _root_.mul_assoc]
        exact (congrArg (· * _) e₂).trans (mul_mul_mul_comm _ _ _ _))
    exact ⟨g', hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩
  choose act hb hv using ex
  have add : ∀ g g' g'' : GtPtF D F, g.IsAdd g' g'' → (act g).IsAdd (act g') (act g'') := fun g g' g'' h => by
    obtain ⟨b₁, v₁⟩ := (isAdd_iff _ _ _).1 h
    refine (isAdd_iff _ _ _).2 ⟨by rw [hb, hb, hb, b₁, MonObj.mul_comp], fun χ y J hJ => ?_⟩
    have e₁ := (ra hJ g.b g'.b (cP D _ χ)).2
    have e₂ := v₁ (star a • χ) y J hJ
    rw [cf] at e₂
    rw [← b₁] at e₁
    rw [hv _ _ y J hJ, hv _ _ y J hJ, hv _ _ y J hJ, hb, hb, _root_.mul_assoc]
    refine (congrArg _ e₁).trans ?_
    rw [← _root_.mul_assoc]
    exact (congrArg (· * _) e₂).trans (mul_mul_mul_comm _ _ _ _)
  obtain ⟨h, ⟨gs, g₀, gst, gl⟩, hι⟩ := p.eq
  obtain ⟨ιb, ιv⟩ := (isIota_iff _ _).1 hι
  let q : QkPt D F k := ⟨a • p.y, act p.g, act h, ⟨fun i => act (gs i), by
      obtain ⟨z₁, z₂⟩ := (isZero_iff _).1 g₀
      exact (isZero_iff _).2 ⟨by rw [hb, z₁, MonObj.one_comp], fun χ y J hJ => by
        rw [hv _ _ y J hJ, z₂ _ y J hJ, z₁, u₂ hJ, _root_.mul_one]⟩,
      fun i => add _ _ _ (gst i), congrArg act gl⟩, (isIota_iff _ _).2 ⟨by rw [hb, ιb, cf], fun χ y J hJ => by
      let κ : TF (R := R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by
        rw [Category.id_comp]; rfl)
      have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal u hu u₀ χ p.y) κ.left)
      have e' : val (LB.pullGen D.P.L _ _ u (D.pt2 χ p.y)) κ.left y J = val₂ u y J (cP D _ χ) (cP D _ p.y) := by
        rw [val_pull hJ, val₂, ← comp_cP D κ, ← comp_cP D κ p.y, ← comp_lift]; rfl
      rw [hv _ _ y J hJ, ιv _ y J hJ, ιb, ← e']
      exact (congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) rfl).trans
        (e.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))⟩⟩
  refine ⟨q, rfl, hb _, fun u' hu' u₀' χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) rfl ?_) (hv p.g χ y J hJ).symm)
  rw [val_pull hJ, Category.id_comp]
  have z2 : zero2 D.P.A ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D.P.A] η[D.P.A])
  exact gen_unique D.P.isLB _ (zero2 D.P.A) z2 (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2) hu' hu
    (fun y I hI => by
      have a₁ := val_corr hI u₀' (𝟙 _)
      have a₂ := val_corr hI u₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a₁ a₂
      exact a₁.trans a₂.symm) _ _ y J hJ

end Pts

section End
variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_u (hG : GlobalFnsSt) (D : DegPre R) {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O)
    (a : O) (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) (hu : u.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) (χ : D.X) :
    ∃ v : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) (star a • χ)) (D.Oφ (oa.onB.act a) χ)) (Sum.elim Oε Oinvε)),
      Normd v ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
        Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x := fun T x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) (star a • χ)) (D.Oφ (oa.onB.act a) χ)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (prod_ros _ _ (cP D _ χ) (𝟙 D.P.A) h).trans (Eq.symm ?_)
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_Oφ D (𝟙 _) (star a • χ) h)
        (prod_Oφ_inv D (oa.onB.act a) χ h)).trans ?_
      rw [cf, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.pullGen D.P.L _ _ u (lift (cP D D.P.A χ) (𝟙 D.P.A)).left) (pullGen_isGen _ _ _ _ hu _)
  have key : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
      Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := fun T x Z r z J hJ => by
    rw [vv Z _ z J hJ, val_pull hJ, Category.assoc, ← Over.comp_left, comp_lift, comp_cP, Category.comp_id]
  refine ⟨v, ⟨hv, corr_of_val D.P.isLB fun y J hJ => ?_⟩, key⟩
  have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) hJ 1 1 (cP D _ χ)).2
  rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J (cP D _ χ) 1 = 1 := mul_eq_left.1 e.symm
  have k := key (𝟙_ (Over (Spec (CommRingCat.of R)))) 1 _ (𝟙 _) y J hJ
  have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  rw [o] at k
  refine (val_pull hJ _ _ _).trans (k.trans (Eq.trans ?_ (val_one _).symm))
  rw [Category.id_comp]
  exact e'

theorem endU_of_oLinear : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → ∀ a : O, ∃ E : EndU U.toUnifPre, E.aG = ιG.act a ∧ E.aA = ιA.act a ∧ E.aB = ιD.onB.act a ∧ (∀ χ, E.h χ = star a • χ) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (g g' : GtPtF D.toPre F), E.Act g g' ↔ GtPtAct ιD a g g' := by
  intro hL R _ _ _ I _ D A G _ _ _ U O _ _ _ ιD ιA ιG hO a
  have hG := hL.1.globalFns
  have := ιD.onB.hom a
  have := ιD.onB.hom (star a)
  have hr := ιD.onB.rosati (star a)
  rw [star_star] at hr
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hr
  choose v hv vv using exists_u hG D.toPre ιD a u hu u₀
  refine ⟨{ aG := ιG.act a, aA := ιA.act a, aB := ιD.onB.act a, homG := ιG.hom a, homA := ιA.hom a,
            homB := ιD.onB.hom a, h := DistribSMul.toAddMonoidHom D.toPre.X (star a), ext := hO.ext a,
            q_lin := fun e => hO.q_lin e a, i_lin := fun e => hO.i_lin e a, u := v, u_norm := hv,
            t_lin := fun e χ Z x z J hJ => ?_ }, rfl, rfl, rfl, fun _ => rfl, fun F _ _ g g' => ?_⟩
  · have e₁ := val_corr hJ (hL.2.2.2.1.tLin R I O D A G U.toUnifPre ιD ιA ιG hO e a u hu u₀ χ) x
    refine ((val_pull hJ _ _ _).symm.trans e₁.symm).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_))
    exact (val_pull hJ _ _ _).trans (vv χ _ (U.gt e).pG Z x z J hJ).symm
  · have k : ∀ χ z J, Good D.toPre.P.L z J →
        val (v χ) g.b.left z J = val u (𝟙 _ ≫ (lift (cP D.toPre _ χ) g.b).left) z J := fun χ z J hJ =>
      (congrArg (fun q => val (v χ) q z J) (Category.id_comp g.b.left).symm).trans (vv χ _ g.b _ (𝟙 _) z J hJ)
    refine and_congr Iff.rfl ⟨fun H u' hu' u₀' χ => corr_of_val D.toPre.P.isLB fun z J hJ => ?_, fun H χ z J hJ => ?_⟩
    · refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) rfl ?_) (H χ z J hJ).symm)
      exact (val_pull hJ _ _ _).trans ((ros_unique hG D.toPre hu hu' u₀ u₀' _ _ z J hJ).trans (k χ z J hJ).symm)
    · refine (val_corr hJ (H u hu u₀ χ) (𝟙 _)).symm.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_))
      exact (val_pull hJ _ _ _).trans (k χ z J hJ).symm

end End

end GlobalTheory.Mum.EFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSameExpansionThickeningOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumMult

theorem map_map_homOfLE {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom x) =
      (X.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem map_res_homOfLE {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (u : Γ(X, U)ˣ) :
    (X.presheaf.map (homOfLE h2).op).hom (res h1 u).val = (res (h2.trans h1) u).val :=
  map_map_homOfLE h1 h2 u.val

theorem sum_attach_eq_sum_of_subset {β M : Type*} [AddCommMonoid M] {S S' : Finset β} (hS : S ⊆ S') (F : β → M)
    (T : S → M) (hT : ∀ x, T x = F x) (hz : ∀ α ∈ S', α ∉ S → F α = 0) :
    ∑ x ∈ S.attach, T x = ∑ α ∈ S', F α := by
  rw [← Finset.sum_subset hS hz, ← Finset.sum_attach S F]
  exact Finset.sum_congr rfl fun x _ => hT x

theorem eq_of_expandsAt_of_chartExpOn : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R I e G).left.Opens) (hW : W ≤ (fstG I e G).left ⁻¹ᵁ secChart U.LG.L i') (g : Γ((thickObj R I e G).left, W)), U.ExpandsAt e k σ f → GlobalTheory.MumMult.ChartExpOn U e k i' W g f → ((thickObj R I e G).left.presheaf.map (homOfLE hW).op).hom (((fstG I e G).left.app (secChart U.LG.L i')).hom (σ.f i')) = g := by
  intro R _ _ I D A G _ _ U e k σ f i' W hW g hE hC
  classical
  obtain ⟨S₁, h1v, E1⟩ := hE
  obtain ⟨S₂, h2v, E2⟩ := hC
  have hex : ∀ x : D.toPre.P.A.left, ∃ i, x ∈ D.toPre.P.L.U i := fun x => by
    have hx : x ∈ (⨆ i, D.toPre.P.L.U i) := by rw [D.toPre.P.isLB.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  choose idx0 hidx0 using hex
  have key : ∀ y ∈ W, ∃ (V : (thickObj R I e G).left.Opens) (hV : V ≤ W), y ∈ V ∧
      ((thickObj R I e G).left.presheaf.map (homOfLE hV).op).hom
        (((thickObj R I e G).left.presheaf.map (homOfLE hW).op).hom
          (((fstG I e G).left.app (secChart U.LG.L i')).hom (σ.f i'))) =
      ((thickObj R I e G).left.presheaf.map (homOfLE hV).op).hom g := by
    intro y hy
    let idx : ((thickObj R I e G).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι := fun φ => idx0 (φ.base y)
    have hidx : ∀ φ, φ.base y ∈ D.toPre.P.L.U (idx φ) := fun φ => hidx0 _
    let p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι) :=
      (fun _ => idx (U.gt e).pG.left, fun _ => i' 0)
    let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun α κ => idx ((U.gt e).pG.left ≫ D.toPre.famφB α κ)
    let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun α κ => idx (D.toPre.Oφ (U.gt e).pG α κ)
    have hcoh : ∀ S : Finset D.toPre.X, CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
      intro S a b hab
      rcases a with a | a | a <;> rcases b with b | b | b <;> exact congrArg idx hab
    have hmem : ∀ S, y ∈ U.expW e p i' S jf jt := by
      intro S
      refine ⟨⟨⟨Set.mem_iInter.2 fun _ => hidx _, Set.mem_iInter.2 fun _ => ?_⟩, hW hy⟩, ?_⟩
      · exact Set.mem_iInter.1 (hW hy) 0
      · refine Finset.inf_induction (p := fun O : (thickObj R I e G).left.Opens => y ∈ O) trivial
          (fun a ha b hb => ⟨ha, hb⟩) ?_
        intro α _
        exact ⟨Set.mem_iInter.2 fun κ => hidx ((U.gt e).pG.left ≫ D.toPre.famφB α κ),
          Set.mem_iInter.2 fun κ => hidx _⟩

    have hV1 : U.expW e p i' (S₁ ∪ S₂) jf jt ⊓ W ≤ U.expW e p i' S₁ jf jt :=
      inf_le_left.trans (inf_le_inf_left _ (Finset.inf_mono Finset.subset_union_left))
    have hV2 : U.expW e p i' (S₁ ∪ S₂) jf jt ⊓ W ≤ U.expW e p i' S₂ jf jt ⊓ W :=
      inf_le_inf_right _ (inf_le_inf_left _ (Finset.inf_mono Finset.subset_union_right))
    have E1V := congrArg ((thickObj R I e G).left.presheaf.map (homOfLE hV1).op).hom
      (E1 p i' jf jt rfl (hcoh S₁))
    have E2V := congrArg ((thickObj R I e G).left.presheaf.map (homOfLE hV2).op).hom
      (E2 p jf jt rfl (hcoh S₂))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_pow, map_sum, map_res_homOfLE, map_map_homOfLE] at E1V E2V
    let tV : ∀ α, α ∈ S₁ ∪ S₂ → Γ((thickObj R I e G).left, U.expW e p i' (S₁ ∪ S₂) jf jt ⊓ W) :=
      fun α h => ((thickObj R I e G).left.presheaf.map
          (homOfLE (inf_le_left.trans (U.expW_le_f e p i' jf jt h))).op).hom
          (((U.gt e).pG.left.app _).hom ((f α).f (jf α))) *
        (res (inf_le_left.trans (U.expWeight_le_chart_weight e p i' jf jt h)) (((U.gt e).t α).s (jt α))).val
    let F : D.toPre.X → Γ((thickObj R I e G).left, U.expW e p i' (S₁ ∪ S₂) jf jt ⊓ W) :=
      fun α => if h : α ∈ S₁ ∪ S₂ then tV α h else 0
    have hz1 : ∀ α ∈ S₁ ∪ S₂, α ∉ S₁ → F α = 0 := by
      intro α h hn
      have h0 : ((U.gt e).pG.left.app (LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α))).hom
          ((f α).f (jf α)) = 0 := h1v α hn (jf α)
      simp only [F, dif_pos h, tV]
      rw [h0, map_zero, zero_mul]
    have hz2 : ∀ α ∈ S₁ ∪ S₂, α ∉ S₂ → F α = 0 := by
      intro α h hn
      have h0 : ((U.gt e).pG.left.app (LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α))).hom
          ((f α).f (jf α)) = 0 := h2v α hn (jf α)
      simp only [F, dif_pos h, tV]
      rw [h0, map_zero, zero_mul]
    rw [sum_attach_eq_sum_of_subset Finset.subset_union_left F _ (fun x => ?_) hz1] at E1V
    rw [sum_attach_eq_sum_of_subset Finset.subset_union_right F _ (fun x => ?_) hz2] at E2V
    rotate_left
    · simp only [F, dif_pos (Finset.mem_union_right S₁ x.2), tV]
      congr 1 <;> first | rfl | exact map_res_homOfLE _ _ _ | exact map_map_homOfLE _ _ _
    · simp only [F, dif_pos (Finset.mem_union_left S₂ x.2), tV]
      congr 1 <;> first | rfl | exact map_res_homOfLE _ _ _ | exact map_map_homOfLE _ _ _
    refine ⟨U.expW e p i' (S₁ ∪ S₂) jf jt ⊓ W, inf_le_right, ⟨hmem _, hy⟩, ?_⟩
    rw [map_map_homOfLE]
    exact ((Units.isUnit _).pow k).mul_left_cancel (E1V.trans E2V.symm)
  choose V hVW hyV hEq using key
  refine TopCat.Sheaf.eq_of_locally_eq' (thickObj R I e G).left.sheaf (fun y : W => V y.1 y.2) W
    (fun y => homOfLE (hVW y.1 y.2)) ?_ _ _ fun y => hEq y.1 y.2
  intro y hy
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyV y hy⟩

end GlobalTheory.MumMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleAddEffectiveOfNefBigStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ample_add_effective_of_nef_big : GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (N : LB X) (hN : N.IsLB), IsNef ℂ N → IsBig ℂ N → ∃ (a : ℕ) (A : LB X) (hA : A.IsLB) (E₀ : CartierDiv X), 0 < a ∧ IsAmpleLB A ∧ E₀.Eff ∧ a • cls N hN = cls A hA + cls (toLB E₀) (isLB_toLB E₀) := by
  first | exact @GlobalTheory.exists_ample_add_eff_of_isNef_isBig | exact GlobalTheory.exists_ample_add_eff_of_isNef_isBig | (intros; apply GlobalTheory.exists_ample_add_eff_of_isNef_isBig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOfTheoremOfCubeTenPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_of_theoremOfCube_ten_points : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G) (θ : P.L.L.Sec) (T : Over S) (x a b c : T ⟶ G) (W : T.left.Opens), (∀ f ∈ cubeTen x a b c, W ≤ f.left ⁻¹ᵁ secNz θ) → ∃ t : LB.Gen (P.L.L.pull (W.ι ≫ x.left)), t.IsGen := by
  first | exact @GlobalTheory.Mum.exists_gen_of_cubeTen | exact GlobalTheory.Mum.exists_gen_of_cubeTen | (intros; apply GlobalTheory.Mum.exists_gen_of_cubeTen <;> assumption)
end

