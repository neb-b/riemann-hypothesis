module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0139
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2143
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeTwoObstructionClassNatural
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem extHom_coefHom_restrict {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁]
    {C₂ C' : Type} [Category.{0} C₂] [Category.{0} C'] (F₂ : C₂ ⥤ CommAlgCat.{0} R₀) (G : C' ⥤ C₂) (T : C')
    (y : R₁ ⊗[R₀] F₂.obj ((CoefMap.restrict F₂ G).G.obj T)) :
    extHom R₁ (coefHom (CoefMap.restrict F₂ G) T) y = y := by
  change Algebra.TensorProduct.map (AlgHom.id R₁ R₁) (AlgHom.id R₀ _) y = y
  rw [Algebra.TensorProduct.map_id]; rfl

theorem isOb2_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C₂ : Type) [Category.{0} C₂] (F₂ : C₂ ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (G : C' ⥤ C₂) (n : CoefMap (RingHom.id R₀) F (G ⋙ F₂)) (L : Pre I π F) (L₂ : Pre I π F₂) (w : Glob1 F) (w₂ : Glob1 F₂) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)) (c₂ : GlobalTheory.CatCoh.H2 (ext R₁ F₂)), (∀ T, q1 n T (w.1 _) = w₂.1 (G.obj T)) → L.IsOb2 α w c → L₂.IsOb2 α w₂ c₂ → (extMap R₁ n).pull2 c = (extMap R₁ (CoefMap.restrict F₂ G)).pull2 c₂ := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F C₂ _ F₂ C' _ G n L L₂ w w₂ c c₂ hw h1 h2
  obtain ⟨θ, σ, z, hθ, hσ, rfl, hz⟩ := h1
  obtain ⟨θ₂, σ₂, z₂, hθ₂, hσ₂, rfl, hz₂⟩ := h2
  have hl0 : ∀ T : C', ∃ l : L.B (n.G.obj T) →ₐ[R] L₂.B (G.obj T),
      ∀ b, L₂.p (G.obj T) (l b) = coefHom n T (L.p _ b) := by
    intro T
    haveI := L.smooth (n.G.obj T)
    exact homLift R R₀ I hI π hπ hk _ _ (L.p _) (L.semi _) (L.surj _) (L.ker _) _ _ (L₂.p (G.obj T))
      (L₂.semi _) (L₂.surj _) (L₂.ker _) (coefHom n T)
  choose l hl using hl0
  have hd : ∀ (T T' : C') (a : T ⟶ T') (b : L.B (n.G.obj T)),
      ((L₂.ρ (G.map a)).comp (l T)) b - ((l T').comp (L.ρ (n.G.map a))) b ∈
        I.map (algebraMap R (L₂.B (G.obj T'))) := by
    intro T T' a b
    refine (L₂.ker _ _).1 ?_
    rw [map_sub, sub_eq_zero]
    simp only [AlgHom.comp_apply]
    rw [L₂.nat, hl, hl, L.nat]
    exact (n.naturality a (L.p _ b)).symm
  choose κ hκ using fun (T T' : C') (a : T ⟶ T') ↦ ((theta_classify R R₀ (L.B (n.G.obj T)) (F.obj (n.G.obj T))
    (L₂.B (G.obj T')) I hI π hπ (L.p _) (L.semi _) (L.surj _) (L.ker _)
    ((L₂.ρ (G.map a)).comp (l T))).1 _ (hd T T' a)).exists
  have key : ∀ (T T' T'' : C') (a : T ⟶ T') (b : T' ⟶ T'') (ω : Ω[F.obj (n.G.obj T)⁄R₀]),
      θ₂ _ _ _ (G.map a) (G.map b) (q1 n T ω) + κ T T'' (a ≫ b) ω =
        L₂.ρ (G.map b) (κ T T' a ω) + κ T' T'' b (p1 F (n.G.map a) ω) +
          l T'' (θ _ _ _ (n.G.map a) (n.G.map b) ω) := by
    intro T T' T'' a b ω
    have e1 := (_root_.GlobalTheory.Obs.isTheta_comp R R₀ I hI π hπ hk _ _ (L₂.p (G.obj T)) (L₂.semi _) (L₂.surj _) (L₂.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L₂.B (G.obj T'')) (L₂.B (G.obj T'')) _ _ _ (hθ₂ _ _ _ (G.map a) (G.map b))).2
      (l T) (coefHom n T) (hl T)
    have e2 := hκ T T'' (a ≫ b)
    rw [Functor.map_comp, Functor.map_comp] at e2
    have s1 := (isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ _ _ _
      e1).2.1 e2
    have f1 := (_root_.GlobalTheory.Obs.isTheta_comp R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L₂.B (G.obj T')) (L₂.B (G.obj T'')) _ _ _ (hκ T T' a)).1 (L₂.ρ (G.map b))
    have f2 := (_root_.GlobalTheory.Obs.isTheta_comp R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T')) (L.semi _) (L.surj _) (L.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L₂.B (G.obj T'')) (L₂.B (G.obj T'')) _ _ _ (hκ T' T'' b)).2
      (L.ρ (n.G.map a)) (mp F (n.G.map a)) (L.nat (n.G.map a))
    have f3 := (_root_.GlobalTheory.Obs.isTheta_comp R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj T'')) (L₂.B (G.obj T'')) _ _ _ (hθ _ _ _ (n.G.map a) (n.G.map b))).1 (l T'')
    have s2 := (isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ _ _ _
      ((isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ _ _ _
        f1).2.1 f2)).2.1 f3
    have e := congrArg (fun t : Ω[F.obj (n.G.obj T)⁄R₀] →+ L₂.B (G.obj T'') ↦ t ω)
      ((isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ (l T'' |>.comp (L.ρ (n.G.map (a ≫ b)))) _ _
        s1).2.2.1 s2)
    exact e
  choose g hgK hg using fun (T T' : C') (a : T ⟶ T') ↦ (sig_basic R R₀ I hI π hπ hk R₁ α _ _
    (L₂.p (G.obj T')) (L₂.semi _) (L₂.surj _) (L₂.ker _) (σ₂ _) (hσ₂ _)).2.2.2 (κ T T' a (w.1 _))
    ((hκ T T' a).mem _)
  have kadd : ∀ {X : C₂} (y y' : R₁ ⊗[R₀] F₂.obj X), α.KerQ y → α.KerQ y' → α.KerQ (y + y') :=
    fun y y' h h' ↦ by unfold Aug.KerQ at *; rw [map_add (f := _), h, h', add_zero]
  have kneg : ∀ {X : C₂} (y : R₁ ⊗[R₀] F₂.obj X), α.KerQ y → α.KerQ (-y) :=
    fun y h ↦ by unfold Aug.KerQ at *; rw [map_neg, h, neg_zero]
  have ksub : ∀ {X : C₂} (y y' : R₁ ⊗[R₀] F₂.obj X), α.KerQ y → α.KerQ y' → α.KerQ (y - y') :=
    fun y y' h h' ↦ by rw [sub_eq_add_neg]; exact kadd _ _ h (kneg _ h')
  rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk]
  refine ⟨fun T T' a ↦ -g T T' a, ?_⟩
  funext T T' T'' a b
  haveI := L₂.smooth (G.obj T'')
  have nb := sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L₂.p (G.obj T')) (L₂.semi _) (L₂.surj _) (L₂.ker _) _ _
    (L₂.p (G.obj T'')) (L₂.semi _) (L₂.surj _) (L₂.ker _) (L₂.ρ (G.map b)) (mp F₂ (G.map b)) (L₂.nat (G.map b))
    (σ₂ _) (σ₂ _) (hσ₂ _) (hσ₂ _)
  have nl := sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L.p (n.G.obj T'')) (L.semi _) (L.surj _) (L.ker _) _ _
    (L₂.p (G.obj T'')) (L₂.semi _) (L₂.surj _) (L₂.ker _) (l T'') (coefHom n T'') (hl T'')
    (σ _) (σ₂ _) (hσ _) (hσ₂ _)
  change extHom R₁ (mp F₂ (G.map b)) (-g T T' a) - -g T T'' (a ≫ b) + -g T' T'' b =
    extHom R₁ (coefHom n T'') (z.1 _ _ _ (n.G.map a) (n.G.map b)) -
      extHom R₁ (coefHom (CoefMap.restrict F₂ G) T'') (z₂.1 _ _ _ (G.map a) (G.map b))
  rw [extHom_coefHom_restrict, ← sub_eq_zero]
  refine _root_.GlobalTheory.Obs.sig_inj_of_flat R R₀ I hI π hπ hk R₁ α _ _ (L₂.p (G.obj T'')) (L₂.semi _) (L₂.surj _) (L₂.ker _)
    (σ₂ _) (hσ₂ _) _ ?_ ?_
  · refine ksub _ _ (kadd _ _ (ksub _ _ ?_ (kneg _ (hgK _ _ _))) (kneg _ (hgK _ _ _)))
      (ksub _ _ (nl.2 _ (hz _ _ _ _ _).1) (hz₂ _ _ _ _ _).1)
    rw [map_neg]; exact kneg _ (nb.2 _ (hgK _ _ _))
  · change σ₂ (G.obj T'') ((_ : R₁ ⊗[R₀] F₂.obj (G.obj T'')) -
      (_ - z₂.1 (G.obj T) (G.obj T') (G.obj T'') (G.map a) (G.map b))) = 0
    simp only [map_sub, map_add (f := _), map_neg]
    rw [← nb.1, ← nl.1, hg, hg, hg, (hz _ _ _ _ _).2, (hz₂ _ _ _ _ _).2, ← hw, w.2 (n.G.map a)]
    linear_combination key T T' T'' a b (w.1 _)

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationHomotopyOperatorFiltrationProperties
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.HotFil

theorem hot_fil : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (v : Derivation R B B) (e : ℕ → B) (N : ℕ), (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) → (∀ k, e k ∈ fil δ k) → (∀ x y, hot v e N (x + y) = hot v e N x + hot v e N y) ∧ (∀ b, hot v e N (algebraMap B (DR R B) b) = 0) ∧ (∀ (j : ℕ), ∀ x ∈ ⋀[B]^(j + 1) Ω[B⁄R], hot v e N x ∈ ⋀[B]^j Ω[B⁄R]) ∧ (∀ x ∈ rel R δ, hot v e N x ∈ rel R δ) ∧ ∀ n, ∀ x ∈ filDR R δ n, hot v e N x ∈ filDR R δ (n + 1) := by
  intro R B _ _ _ J δ v e N hv he
  obtain ⟨hc0, -, -, -, -, hcdeg⟩ := (_root_.GlobalTheory.PDForm.ctr_lie_rules).1 R B v
  obtain ⟨-, -, -, -, -, hldeg⟩ := (_root_.GlobalTheory.PDForm.ctr_lie_rules).2 R B v
  have hrel := (_root_.GlobalTheory.PDForm.ctr_lie_rel_filDR).1
  have hfil := (_root_.GlobalTheory.PDForm.ctr_lie_rel_filDR).2
  obtain ⟨-, -, -, -, hfil0, hanti, hsmul⟩ := (_root_.GlobalTheory.PDForm.rel_two_sided_and_bot).1 R B J δ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [hot, map_add (f := _), smul_add, Finset.sum_add_distrib]
  · intro b
    simp only [hot, hc0, map_zero, smul_zero, Finset.sum_const_zero]
  · intro j x hx
    have hc := hcdeg j x hx
    have hk : ∀ k, (lie v ^ k) (ctr v x) ∈ ⋀[B]^j Ω[B⁄R] := by
      intro k
      induction k with
      | zero => simpa using hc
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact hldeg j _ ih
    exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (hk k)
  · intro x hx
    have hc := (hrel R B J δ v hv x hx).1
    have hk : ∀ k, (lie v ^ k) (ctr v x) ∈ rel R δ := by
      intro k
      induction k with
      | zero => simpa using hc
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact (hrel R B J δ v hv _ ih).2
    refine Ideal.sum_mem _ fun k _ ↦ ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (hk k)
  · intro n x hx
    have hc := (hfil R B J δ v hv n).1 x hx
    have hk : ∀ k, (lie v ^ k) (ctr v x) ∈ filDR R δ (n - k) := by
      intro k
      induction k with
      | zero => simpa using hc
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        rcases Nat.eq_zero_or_pos (n - k) with h0 | hpos
        · have : n - (k + 1) = 0 := by omega
          rw [this, hfil0]
          exact Submodule.mem_top
        · have h1 : n - k = (n - (k + 1)) + 1 := by omega
          rw [h1] at ih
          exact (hfil R B J δ v hv (n - (k + 1))).2.2 _ ih
    refine Ideal.sum_mem _ fun k _ ↦ ?_
    have hek : (-1) ^ k * e (k + 1) ∈ fil δ (k + 1) := Ideal.mul_mem_left _ _ (he (k + 1))
    exact hanti (n + 1) ((k + 1) + (n - k)) (by omega) (hsmul (k + 1) (n - k) _ hek _ (hk k))

end GlobalTheory.PDForm.HotFil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentCocycleDefectIsTripleCocycle
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm

namespace GlobalTheory.PolRoot

private theorem gm_charPullTop {X T : Scheme.{0}} (r : T ⟶ X) (t : T) (a : Γ(X, ⊤)ˣ) :
    gm (𝟙 T) t ⊤ (GlobalTheory.CharKer.pullTop r a) = gm r t ⊤ a :=
  (gm_pull (𝟙 T) r t ⊤ trivial a).trans (by rw [Category.id_comp])

theorem defect_tri {X Y T : Scheme.{0}} {f : X ⟶ Y} {M : LB X} {φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ}
    {D : Γ(Triple f, ⊤)ˣ} (h : Defect f M φ D) (a b c : T ⟶ X) (h₁ : a ≫ f = b ≫ f) (h₂ : b ≫ f = c ≫ f)
    (t : T) (i j k : M.ι) (hi : a t ∈ M.U i) (hj : b t ∈ M.U j) (hk : c t ∈ M.U k) :
    gm (tri f a b c h₁ h₂) t ⊤ D * gm (pullback.lift a c (h₁.trans h₂)) t _ (φ i k) =
      gm (pullback.lift a b h₁) t _ (φ i j) * gm (pullback.lift b c h₂) t _ (φ j k) := by
  have e₁ : tri f a b c h₁ h₂ ≫ pullback.fst (pullback.snd f f) (pullback.fst f f) = pullback.lift a b h₁ :=
    pullback.lift_fst _ _ _
  have e₂ : tri f a b c h₁ h₂ ≫ pullback.snd (pullback.snd f f) (pullback.fst f f) = pullback.lift b c h₂ :=
    pullback.lift_snd _ _ _
  have e₃ : tri f a b c h₁ h₂ ≫ pr13 f = pullback.lift a c (h₁.trans h₂) := by
    apply pullback.hom_ext
    · rw [pr13, Category.assoc, pullback.lift_fst, reassoc_of% e₁, pullback.lift_fst]
      try rw [pullback.lift_fst]
    · rw [pr13, Category.assoc, pullback.lift_snd, reassoc_of% e₂, pullback.lift_snd]
      try rw [pullback.lift_snd]
  have := h T (tri f a b c h₁ h₂) t i j k
    (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, reassoc_of% e₁, pullback.lift_fst]; exact hi)
    (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, reassoc_of% e₁, pullback.lift_snd]; exact hj)
    (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, reassoc_of% e₂, pullback.lift_snd]; exact hk)
  rwa [e₁, e₂, e₃] at this

theorem triCocycle_of_defect : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ), Defect f M φ D → TriCocycle f D := by
  intro X Y f M hM φ D h T a b c d h₁ h₂ h₃
  refine unit_ext fun t _ => ?_
  obtain ⟨i, hi⟩ := exists_chart hM (a t)
  obtain ⟨j, hj⟩ := exists_chart hM (b t)
  obtain ⟨k, hk⟩ := exists_chart hM (c t)
  obtain ⟨l, hl⟩ := exists_chart hM (d t)
  have e₁ := defect_tri h a b c h₁ h₂ t i j k hi hj hk
  have e₂ := defect_tri h a c d (h₁.trans h₂) h₃ t i k l hi hk hl
  have e₃ := defect_tri h b c d h₂ h₃ t j k l hj hk hl
  have e₄ := defect_tri h a b d h₁ (h₂.trans h₃) t i j l hi hj hl
  rw [map_mul, map_mul, gm_charPullTop, gm_charPullTop, gm_charPullTop, gm_charPullTop]
  apply mul_right_cancel (b := gm (pullback.lift a d ((h₁.trans h₂).trans h₃)) t _ (φ i l))
  rw [_root_.mul_assoc, _root_.mul_assoc, e₂, e₄, ← _root_.mul_assoc, e₁, _root_.mul_left_comm, e₃, _root_.mul_assoc]

end GlobalTheory.PolRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagSumPullTwo
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem diagSum_pullTwo : ∀ (R : Type) [CommRing R] (D D' : Type) [CommRing D] [Bialgebra R D]
    [Coalgebra.IsCocomm R D] [CommRing D'] [Bialgebra R D'] [Coalgebra.IsCocomm R D'] (f : D →ₐc[R] D')
    (m : ℕ) (c : D ⊗[R] D), f (diagSum R D m c) = diagSum R D' m (pullbackTwo f c) := by
  intro R _ D D' _ _ _ _ _ _ f m c
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [diagSum_tmul, pullbackTwo, TensorProduct.map_tmul, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mulBy]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.CUniq

theorem map_max {R V : Type} [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] (θ : R →+* V) [IsLocalHom θ]
    {x : R} (hx : x ∈ maximalIdeal R) : θ x ∈ maximalIdeal V := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  exact fun h => hx (isUnit_of_map_unit θ x h)

theorem diff_pow {A R V : Type} [CommRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V]
    (ψ : A →+* R) (hψ : IsComplAt ψ) (θ₁ θ₂ : R →+* V) [IsLocalHom θ₁] [IsLocalHom θ₂]
    (h : θ₁.comp ψ = θ₂.comp ψ) (k : ℕ) : ∀ r : R, θ₁ r - θ₂ r ∈ maximalIdeal V ^ k := by
  have hc : ∀ a, θ₁ (ψ a) = θ₂ (ψ a) := fun a => congrArg (fun f => f a) h
  induction k with
  | zero => intro r; simp
  | succ k ih =>
    have hm : ∀ x ∈ maximalIdeal R, θ₁ x - θ₂ x ∈ maximalIdeal V ^ (k + 1) := by
      intro x hx
      rw [← hψ.2.2.2.1] at hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨p, -, rfl⟩ := hy
        simp [hc]
      | zero => simp
      | add y z _ _ hy hz =>
        have := add_mem hy hz
        simpa [map_add (f := _), sub_add_sub_comm] using this
      | smul a y hy' hy =>
        have hyM : y ∈ maximalIdeal R := hψ.2.2.2.1 ▸ hy'
        have e : θ₁ (a • y) - θ₂ (a • y) = θ₁ a * (θ₁ y - θ₂ y) + (θ₁ a - θ₂ a) * θ₂ y := by
          simp only [smul_eq_mul, map_mul]; ring
        rw [e]
        refine add_mem (Ideal.mul_mem_left _ _ hy) ?_
        rw [pow_succ]
        exact Ideal.mul_mem_mul (ih a) (map_max θ₂ hyM)
    intro r
    obtain ⟨a, b, hb, hx⟩ := hψ.2.2.2.2 r
    have e := hm _ hx
    have hu : IsUnit (θ₁ (ψ b)) := hb.map θ₁
    have e2 : θ₁ (r * ψ b - ψ a) - θ₂ (r * ψ b - ψ a) = (θ₁ r - θ₂ r) * θ₁ (ψ b) := by
      simp only [map_sub, map_mul, hc]; ring
    rw [e2] at e
    obtain ⟨u, hu'⟩ := hu
    have : θ₁ r - θ₂ r = (θ₁ r - θ₂ r) * θ₁ (ψ b) * ↑u⁻¹ := by
      rw [← hu', _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ e

end GlobalTheory.TChart.CUniq

theorem GlobalTheory.TChart.cuniq : ∀ (A R V : Type) [CommRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (ψ : A →+* R), IsComplAt ψ → ∀ θ₁ θ₂ : R →+* V, IsLocalHom θ₁ → IsLocalHom θ₂ → θ₁.comp ψ = θ₂.comp ψ → θ₁ = θ₂ := by
  intro A R V _ _ _ _ _ _ ψ hψ θ₁ θ₂ h₁ h₂ h
  ext r
  have hk := fun k => GlobalTheory.TChart.CUniq.diff_pow ψ hψ θ₁ θ₂ h k r
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal V) (maximalIdeal.isMaximal V).ne_top
  have : θ₁ r - θ₂ r ∈ ⨅ k : ℕ, maximalIdeal V ^ k := Ideal.mem_iInf.mpr hk
  rw [hbot, Ideal.mem_bot, sub_eq_zero] at this
  exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimAddRank
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem Trait.dim_add_rank : ∀ {g n : ℕ}, 2 ≤ n → ∀ (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F),
    T.D.toPre.P.g + Module.finrank ℤ T.D.toPre.X = g := by
  intro g n hn F T
  have hn0 : n ≠ 0 := by omega
  have hζ : IsUnit (zetaAway n) := by rw [← cycBase_ζ hn0]; exact Units.isUnit _
  have hd : SmoothOfRelativeDimension g F.univ.A.hom :=
    GlobalTheory.SiegSharpCover.smoothDim F.univ hn hζ (isUnit_natCast hn0)
  have hA : SmoothOfRelativeDimension g T.A.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback T.cart.1 hd
  have e : T.A.g = g :=
    H1.dim_unique _ T.A.smoothDim hA ((η[T.A.A]).left (IsLocalRing.closedPoint _))
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have h := GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U
  omega

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyFormulaDivisor
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem discrep_isAt_eq_neg_mult : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ (K G : CartierDiv Y) (m : ℕ), 0 < m → IsDivOfForm K η → ∀ (E : DivOver q) (w : Y) (g : Y.functionFieldˣ), E.IsAt w → G.IsEqn w g → discrep E η m g = -((G - m • K).mult w : ℚ) / m := by
  intro k _ _ Y _ _ q n _ η hη K G m hm hK E w g hE hg
  obtain ⟨c, hc⟩ := K.exists_isEqn w
  have h1 := (hg.sub (hc.nsmul m)).mult_eq
  rw [← hE.ord_eq, div_eq_mul_inv, E.ord_mul, E.ord_inv, E.ord_pow] at h1
  have h2 := _root_.GlobalTheory.Discrepancy.DivOver.formOrd_eq_mult_of_isDivOfForm k Y q n η hη K hK E w hE
  rw [hc.mult_eq, ← hE.ord_eq] at h2
  change E.formOrd η = E.ord c at h2
  have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [discrep, h1, h2]
  push_cast
  field_simp
  ring

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerLiftCompProjection
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.Pow8

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

abbrev G8 : Over S := powObj G 8

abbrev pr8 (i : Fin 8) : G8 G ⟶ G := powPr G i

def mk8 {T : Over S} (x : Fin 8 → (T ⟶ G)) : T ⟶ G8 G := (powIsLimit G 8).lift (Fan.mk T x)

theorem eighthPowerLift_comp_projection {T : Over S} (x : Fin 8 → (T ⟶ G)) (i : Fin 8) : mk8 G x ≫ pr8 G i = x i :=
  (powIsLimit G 8).fac (Fan.mk T x) ⟨i⟩

theorem eighthPowerGroupObj_hom_ext {T : Over S} {x y : T ⟶ G8 G} (h : ∀ i, x ≫ pr8 G i = y ≫ pr8 G i) : x = y :=
  (powIsLimit G 8).hom_ext fun ⟨i⟩ => h i

def matAct (a : Matrix (Fin 8) (Fin 8) ℤ) : G8 G ⟶ G8 G := mk8 G fun i => ∏ j, pr8 G j ^ a i j

theorem matAct_pr (a : Matrix (Fin 8) (Fin 8) ℤ) (i : Fin 8) : matAct G a ≫ pr8 G i = ∏ j, pr8 G j ^ a i j :=
  eighthPowerLift_comp_projection G _ i

theorem matAct_hom (a : Matrix (Fin 8) (Fin 8) ℤ) : IsMonHom (matAct G a) :=
  Serre.isMonHom_of_mul_comp _ fun T x y => eighthPowerGroupObj_hom_ext G fun k => by
    have hc : IsMonHom (∏ j, pr8 G j ^ a k j) :=
      PowQuotient.isMonHom_prod _ fun j => Serre.isMonHom_zpow _ _
    rw [MonObj.mul_comp _ _ (pr8 G k), Category.assoc, Category.assoc, Category.assoc, matAct_pr,
      MonObj.mul_comp _ _ (∏ j, pr8 G j ^ a k j)]

theorem matAct_one : matAct G 1 = 𝟙 (G8 G) := eighthPowerGroupObj_hom_ext G fun i => by
  rw [matAct_pr, Category.id_comp, Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [Matrix.one_apply_ne' hj]
  · simp

end GlobalTheory.Mum.Pow8
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfCompEtaleSameRelativeDimensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_of_comp_etale_sameRelativeDimension : ∀ (X Y Z S : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z) (sX : X ⟶ S) (sY : Y ⟶ S) (d : ℕ), h ≫ sY = sX → SmoothOfRelativeDimension d sX → SmoothOfRelativeDimension d sY → Etale (h ≫ f) → Etale h := by
  first | (exact @GlobalTheory.etale_of_comp_etale_of_smoothOfRelativeDimension) | (exact GlobalTheory.etale_of_comp_etale_of_smoothOfRelativeDimension) | (intros; apply GlobalTheory.etale_of_comp_etale_of_smoothOfRelativeDimension  <;> assumption)
end

