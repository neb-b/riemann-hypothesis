module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorMatchIdOneMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

attribute [local instance] GlobalTheory.TorusExt.gtGroup

namespace GlobalTheory.Poinc.Eq8.TorMatchLaws

theorem alg_eq {R F : Type} [CommRing R] [IsDomain R] [Field F] (i₁ i₂ : Algebra (FractionRing R) F)
    (h : ∀ r, @algebraMap _ _ _ _ i₁ (algebraMap R (FractionRing R) r) =
      @algebraMap _ _ _ _ i₂ (algebraMap R (FractionRing R) r)) : i₁ = i₂ := by
  apply Algebra.algebra_ext
  intro x
  have e := IsLocalization.ringHom_ext (M := nonZeroDivisors R) (S := FractionRing R)
    (j := @algebraMap _ _ _ _ i₁) (k := @algebraMap _ _ _ _ i₂) (RingHom.ext h)
  exact RingHom.congr_fun e x

theorem qk_eq {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {k : ℕ} {q q' : QkPt D F k} (hy : q.y = q'.y) (hg : q.g = q'.g) : q = q' := by
  cases q; cases q'; cases hy; cases hg; rfl

theorem tor_eq {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {τ : Multiplicative D.X →* Fˣ} {g : GtPtF D F} (h : GlobalTheory.UT.IsTor τ g) :
    g = GlobalTheory.TorusExt.torusPt D F (Additive.ofMul τ) :=
  (GlobalTheory.TorusExt.isTorusPtF_iff_eq g τ).1 ((GlobalTheory.UT.isTor_iff τ g).1 h)

theorem one_le_of_isUnit {R : Type} [CommRing R] [IsDomain R] {k : ℕ} (hk : IsUnit (k : R)) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp at hk
  · exact h

end GlobalTheory.Poinc.Eq8.TorMatchLaws

namespace GlobalTheory.Poinc.Eq8.TorMatchLaws

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem tors_fun (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] {k : ℕ} (hk : IsUnit (k : R)) :
    ∃ f : QkPt D.toPre F k → (TFK (R := R) F ⟶ A.A), (∀ p x, QkToAkU U.toUnifPre F k p x ↔ x = f p) ∧
      (∀ p p', f p = f p' ↔ QkPt.Equiv D.toPre F p p') ∧ (∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') := by
  haveI := hR.2
  obtain ⟨f, ⟨h1, -, h3, h4, -⟩, -⟩ :=
    GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR.1 D A G hG U F k (one_le_of_isUnit hk)
  exact ⟨f, h1, h3, h4⟩

theorem push {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))}
    (U : Unif (maximalIdeal R) D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    ∃ e : (TFK (R := R) F ⟶ A.A) ≃* (Over.mk (jFK (R := R) F ≫ jK R) ⟶ G), ∀ x, (e x).left = x.left ≫ genMap U :=
  GlobalTheory.LiePull.exists_pushEquiv (GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre) (TFK (R := R) F) _ rfl

end GlobalTheory.Poinc.Eq8.TorMatchLaws

namespace GlobalTheory.Poinc.Eq8.TorMatchLaws

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem torMatch_id (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G) :
    TorMatch U U (RingHom.id R) (𝟙 G.left) (AddMonoidHom.id _) := by
  intro F _ _ i₁ i₂ hF
  obtain rfl : i₁ = i₂ := alg_eq i₁ i₂ hF
  intro k hk τ τ' q q' a a' _ hρ hy hτ hy' hτ' hq hq'
  obtain ⟨f, h1, -, -⟩ := tors_fun hR hG U F hk
  have e : τ = τ' := MonoidHom.ext fun x => hρ (Multiplicative.toAdd x)
  subst e
  have hqq : q = q' := qk_eq (hy.trans hy'.symm) ((tor_eq hτ).trans (tor_eq hτ').symm)
  subst hqq
  rw [(h1 q a).1 hq, (h1 q a').1 hq', Category.comp_id]

theorem torMatch_one (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G)
    {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))}
    (U' : Unif (maximalIdeal R) D' A' G') :
    TorMatch U U' (RingHom.id R) (1 : G' ⟶ G).left 0 := by
  intro F _ _ i₁ i₂ hF
  obtain rfl : i₁ = i₂ := alg_eq i₁ i₂ hF
  intro k hk τ τ' q q' a a' _ hρ hy hτ _ _ hq _
  obtain ⟨f, h1, h3, h4⟩ := tors_fun hR hG U F hk
  have e : τ = 1 := MonoidHom.ext fun x => by
    rw [MonoidHom.one_apply]
    refine (hρ (Multiplicative.toAdd x)).trans ?_
    rw [AddMonoidHom.zero_apply, ofAdd_zero, map_one]
  subst e
  have hg : q.g = 0 := by rw [tor_eq hτ, ofMul_one, map_zero]
  have hadd : QkAdd q q q := ⟨q, by rw [hy, add_zero], (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (by rw [hg, add_zero]),
    (h3 q q).1 rfl⟩
  have ha : a = 1 := by
    rw [(h1 q a).1 hq]
    exact mul_eq_left.1 (h4 q q q hadd).symm
  obtain ⟨eU, heU⟩ := push U F
  obtain ⟨eU', heU'⟩ := push U' F
  have key : eU a = eU' a' ≫ (1 : G' ⟶ G) := by rw [comp_one, ha, map_one]
  rw [← heU, key, Over.comp_left, heU', Category.assoc]

theorem torMatch_mul (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G)
    {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))}
    (U' : Unif (maximalIdeal R) D' A' G') (p p' : G' ⟶ G) (ρ ρ' : D.toPre.X →+ D'.toPre.X)
    (hp : TorMatch U U' (RingHom.id R) p.left ρ) (hp' : TorMatch U U' (RingHom.id R) p'.left ρ') :
    TorMatch U U' (RingHom.id R) (p * p').left (ρ + ρ') := by
  intro F _ _ i₁ i₂ hF
  obtain rfl : i₁ = i₂ := alg_eq i₁ i₂ hF
  intro k hk τ τ' q q' a a' hτk hρ hy hτ hy' hτ' hq hq'
  obtain ⟨f, h1, h3, h4⟩ := tors_fun hR hG U F hk
  let τ₁ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ)
  let τ₂ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ')
  have pw : ∀ σ : D.toPre.X →+ D'.toPre.X, (τ'.comp (AddMonoidHom.toMultiplicative σ)) ^ k = 1 := fun σ =>
    MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hτk, MonoidHom.one_apply,
        MonoidHom.one_apply]
  obtain ⟨q₁, hy₁, hτ₁⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult τ₁ (pw ρ)
  obtain ⟨q₂, hy₂, hτ₂⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult τ₂ (pw ρ')
  have e₁ := hp F hF k hk τ₁ τ' q₁ q' (f q₁) a' hτk (fun _ => rfl) hy₁ hτ₁ hy' hτ' ((h1 q₁ _).2 rfl) hq'
  have e₂ := hp' F hF k hk τ₂ τ' q₂ q' (f q₂) a' hτk (fun _ => rfl) hy₂ hτ₂ hy' hτ' ((h1 q₂ _).2 rfl) hq'
  have hτe : τ = τ₁ * τ₂ := MonoidHom.ext fun x => by
    rw [MonoidHom.mul_apply]
    refine (hρ (Multiplicative.toAdd x)).trans ?_
    rw [AddMonoidHom.add_apply, ofAdd_add, map_mul]
    rfl
  have hg : q.g = q₁.g + q₂.g := by
    rw [tor_eq hτ, tor_eq hτ₁, tor_eq hτ₂, hτe, ofMul_mul, map_add (f := _)]
  have hadd : QkAdd q₁ q₂ q := ⟨q, by rw [hy, hy₁, hy₂, add_zero], (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 hg,
    (h3 q q).1 rfl⟩
  have ha : a = f q₁ * f q₂ := by rw [(h1 q a).1 hq]; exact h4 q₁ q₂ q hadd
  obtain ⟨eU, heU⟩ := push U F
  obtain ⟨eU', heU'⟩ := push U' F
  have k₁ : eU (f q₁) = eU' a' ≫ p := Over.OverMorphism.ext (by rw [heU, e₁, Over.comp_left, heU', Category.assoc])
  have k₂ : eU (f q₂) = eU' a' ≫ p' := Over.OverMorphism.ext (by rw [heU, e₂, Over.comp_left, heU', Category.assoc])
  have key : eU a = eU' a' ≫ (p * p') := by rw [comp_mul, ha, map_mul, k₁, k₂]
  rw [← heU, key, Over.comp_left, heU', Category.assoc]

end GlobalTheory.Poinc.Eq8.TorMatchLaws

namespace GlobalTheory.Poinc.Eq8


open TorMatchLaws in
theorem torMatch_id_one_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G'), TorMatch U U (RingHom.id R) (𝟙 G.left) (AddMonoidHom.id _) ∧ TorMatch U U' (RingHom.id R) (1 : G' ⟶ G).left 0 ∧ ∀ (p p' : G' ⟶ G) ρ ρ', TorMatch U U' (RingHom.id R) p.left ρ → TorMatch U U' (RingHom.id R) p'.left ρ' → TorMatch U U' (RingHom.id R) (p * p').left (ρ + ρ') := by
  intro R _ _ _ hR G _ _ hG D A U G' _ _ _ D' A' U'
  exact ⟨torMatch_id hR hG U, torMatch_one hR hG U U', fun p p' ρ ρ' hp hp' => torMatch_mul hR hG U U' p p' ρ ρ' hp hp'⟩

end GlobalTheory.Poinc.Eq8
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibreInjectsLevelModule
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
set_option autoImplicit false
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

theorem one_left {X' : Scheme.{0}} {G : Over X'} [GrpObj G] {Y : Scheme.{0}} (t : Y ⟶ X') :
    (1 : Over.mk t ⟶ G).left = t ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

end GlobalTheory.TorsSpec

namespace GlobalTheory.EqvAct


open GlobalTheory.TorsSpec in
theorem torsLevel_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) → ∀ m : Γ → ((GlobalTheory.EqvAct.pullG TF Z φ).left ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left), GlobalTheory.EqvAct.IsEqvAct ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m → GlobalTheory.EqvAct.MovesEta TF Z ι ρ ℓ (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullψ TF Z φ) m → GlobalTheory.EqvAct.TorsLevel I ι ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ I g _ hMb Γ _ _ ι ρ _ X' _ φ ℓ ρ' hX _ hℓo hℓ hρ m hm hmv
  haveI := hX
  haveI := hℓo
  have hsemi : IsSemiAbelian (pullG TF Z φ) := IsSemiAbelian.pullback _ _ TF.Y.t.semi
  haveI := hsemi.smooth
  haveI := hsemi.separated
  haveI := hsemi.comm
  haveI : Nonempty (V₀ TF.Y Z) := by
    obtain ⟨z, hz⟩ := Z.2.1.nonempty
    exact ⟨⟨z, (j_mem_barComp Z z).2 hz⟩⟩
  have hn : IsUnit ((l.M : ℕ) : Γ(X', ⊤)) := by
    have h0 : IsUnit ((l.M : ℕ) : c.F) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (by have := l.three_le; omega))
    have := h0.map (((φ ≫ s₀ TF.Y Z).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom)
    simpa using this
  have hnI : ((l.M : ℕ) : 𝓞 E) ∈ I := by
    have h0 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]
      exact Ideal.mem_span_singleton_self _
    exact hMb ((Ideal.mul_le_inf.trans inf_le_left) h0)
  have hmv' : ∀ γ x, etaSecL TF Z φ ℓ hℓ x ≫ m γ = (ρ γ).asIso.hom ≫ etaSecL TF Z φ ℓ hℓ (ι γ x) := by
    intro γ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (ι γ (Submodule.Quotient.mk b))
    rw [← ha]
    refine hmv γ a b ?_ _ _ (etaSecL_w TF Z φ ℓ hℓ _) (etaSecL_w TF Z φ ℓ hℓ _) (etaSecL_ψ TF Z φ ℓ hℓ b)
      (etaSecL_ψ TF Z φ ℓ hℓ a)
    rw [ha]
    exact ((ι γ).symm_apply_apply _).symm
  intro K _ _ t
  classical
  have hlift : ∀ P : Over.mk t ⟶ pullG TF Z φ, IsTorsI I (pullAct TF Z φ) P →
      ∃ PT : Sp K ⟶ (torsion (pullG TF Z φ) l.M).left, PT ≫ (torsion.ι (pullG TF Z φ) l.M).left = P.left ∧
        ∃ x, ValAt (pullG TF Z φ) l.M ℓ (etaSecL TF Z φ ℓ hℓ) (PT (IsLocalRing.closedPoint K)) x := by
    intro P hP
    have h1 : P ≫ mulN (pullG TF Z φ) l.M = 1 := by rw [← act_natCast (pullAct TF Z φ)]; exact hP _ hnI
    obtain ⟨PT, hPT⟩ := exists_lift_torsion l.M P h1
    have hPT' : PT.left ≫ (torsion.ι (pullG TF Z φ) l.M).left = P.left := by rw [← Over.comp_left, hPT]
    refine ⟨PT.left, hPT', _root_.GlobalTheory.TorsSpec.exists_valAt (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ)
      (pullAct TF Z φ) I (_root_.GlobalTheory.TorsSpec.exists_etaSecL_of_torsI TF Z φ ℓ hℓ I hMb) K PT.left (fun a ha => ?_) _⟩
    have e1 := congrArg Over.Hom.left (hP a ha)
    rw [Over.comp_left, one_left] at e1
    rw [reassoc_of% hPT', e1, ← Category.assoc, Over.w PT]
    rfl
  let PT : ∀ P, IsTorsI I (pullAct TF Z φ) P → (Sp K ⟶ (torsion (pullG TF Z φ) l.M).left) :=
    fun P h => Classical.choose (hlift P h)
  have hPT : ∀ P h, PT P h ≫ (torsion.ι (pullG TF Z φ) l.M).left = P.left :=
    fun P h => (Classical.choose_spec (hlift P h)).1
  let cl : ∀ P, IsTorsI I (pullAct TF Z φ) P → LevelMod Dw l :=
    fun P h => Classical.choose (Classical.choose_spec (hlift P h)).2
  have hcl : ∀ P h, ValAt (pullG TF Z φ) l.M ℓ (etaSecL TF Z φ ℓ hℓ) (PT P h (IsLocalRing.closedPoint K)) (cl P h) :=
    fun P h => Classical.choose_spec (Classical.choose_spec (hlift P h)).2
  have hun := GlobalTheory.T.levelSection_injective_at_geometricPoint TF Z φ ℓ hℓ
  refine ⟨fun P => if h : IsTorsI I (pullAct TF Z φ) P then cl P h else 0, ?_, ?_, ?_, ?_⟩
  · intro P Q hP hQ
    have hPQ : IsTorsI I (pullAct TF Z φ) (P * Q) := fun a ha => by
      haveI := (pullAct TF Z φ).hom a
      rw [MonObj.mul_comp, hP a ha, hQ a ha, _root_.mul_one]
    simp only [dif_pos hP, dif_pos hQ, dif_pos hPQ]
    exact _root_.GlobalTheory.TorsSpec.valAt_mul (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ) hun
      (_root_.GlobalTheory.TorsSpec.etaSecL_add_geom TF Z φ ℓ hℓ) K t P Q _ _ _ (hPT P hP) (hPT Q hQ) (hPT _ hPQ) _ _ _ _ (hcl P hP) (hcl Q hQ)
      (hcl _ hPQ)
  · intro P a hP
    have hPa : IsTorsI I (pullAct TF Z φ) (P ≫ (pullAct TF Z φ).act a) := fun r hr => by
      rw [Category.assoc, ← (pullAct TF Z φ).mul]
      exact hP _ (I.mul_mem_left a hr)
    simp only [dif_pos hP, dif_pos hPa]
    exact _root_.GlobalTheory.TorsSpec.class_act (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ) hun (pullAct TF Z φ)
      (_root_.GlobalTheory.TorsSpec.etaSecL_smul_geom TF Z φ ℓ hℓ) K t P a _ _ (hPT P hP) (hPT _ hPa) _ _ _ (hcl P hP) (hcl _ hPa)
  · intro P Q hP hQ he
    simp only [dif_pos hP, dif_pos hQ] at he
    exact _root_.GlobalTheory.TorsSpec.eq_of_valAt_eq (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ) K t P Q _ _
      (hPT P hP) (hPT Q hQ) _ _ (hcl P hP) (he ▸ hcl Q hQ)
  · intro γ ht P Q hP hQP
    have hQ : IsTorsI I (pullAct TF Z φ) Q := fun a ha => by
      refine Over.OverMorphism.ext ?_
      have e1 := congrArg Over.Hom.left (hP a ha)
      rw [one_left] at e1
      rw [Over.comp_left, one_left, hQP, Category.assoc, ← hm.2.1 γ a, ← Category.assoc, ← Over.comp_left, e1,
        Category.assoc, eta_comp_of_isGrpPullback (hm.1 γ), ← Category.assoc, ht]
    simp only [dif_pos hP, dif_pos hQ]
    exact _root_.GlobalTheory.TorsSpec.class_move (pullG TF Z φ) l.M hn ℓ (etaSecL TF Z φ ℓ hℓ) (etaSecL_w TF Z φ ℓ hℓ) hun (pullAct TF Z φ)
      ρ' ρ hρ ι m hm hmv' K t γ P Q _ _ (hPT P hP) (hPT Q hQ) hQP _ _ _ (hcl P hP) (hcl Q hQ)

end GlobalTheory.EqvAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsGaloisAllLevelsOfSquares
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalSquares

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_div {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (D : DegData R (maximalIdeal R))
    {k : ℕ} (l N : ℕ) (hl : 1 ≤ l) (hN : N = k * l) (p : QkPt D.toPre (Kb R) k) :
    ∃ q : QkPt D.toPre (Kb R) N, q.y = p.y ∧ l • q.g = p.g := by
  obtain ⟨g, hg⟩ := GlobalTheory.TorusExt.exists_nsmul_eq (F := Kb R) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1.1)
    (n := l) (by omega) p.g
  refine ⟨GlobalTheory.TorusExt.qkMk D.tau_bimult p.y g ?_, rfl, hg⟩
  rw [hN, mul_nsmul', hg]
  exact GlobalTheory.TorusExt.qk_nsmul D.tau_bimult p

theorem qkExt_nsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) {F F' : Type} [Field F]
    [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') {k N : ℕ}
    (l : ℕ) {p : QkPt D F k} {p' : QkPt D F' k} {q : QkPt D F N} (hp : QkExt σ.toRingHom p p') (hy : q.y = p.y)
    (hg : l • q.g = p.g) : ∃ q' : QkPt D F' N, QkExt σ.toRingHom q q' ∧ q'.y = p'.y ∧ l • q'.g = p'.g := by
  have hσ : σ.toRingHom.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := RingHom.ext σ.commutes
  refine ⟨GlobalTheory.TorusExt.qkExt hB σ.toRingHom hσ q, (GlobalTheory.TorusExt.qkExt_iff hB _ hσ _ _).2 rfl, ?_, ?_⟩
  · rw [(GlobalTheory.TorusExt.qkExt_iff hB _ hσ _ _).1 hp]
    exact hy
  · rw [(GlobalTheory.TorusExt.qkExt_iff hB _ hσ _ _).1 hp]
    show l • GlobalTheory.TorusExt.gtExt D σ.toRingHom hσ q.g = GlobalTheory.TorusExt.gtExt D σ.toRingHom hσ p.g
    rw [← map_nsmul, hg]

theorem pow_left_of_comp {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Sp (FractionRing R))}
    (σ : Kb R →ₐ[FractionRing R] Kb R) (x y : TFK (R := R) (Kb R) ⟶ A.A) (h : y.left = spMap σ.toRingHom ≫ x.left)
    (l : ℕ) : (y ^ l).left = spMap σ.toRingHom ≫ (x ^ l).left := by
  let s : TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R) := Over.homMk (spMap σ.toRingHom) (by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (RingHom.ext σ.commutes))
  have hy : y = s ≫ x := Over.OverMorphism.ext h
  have hp : ∀ m : ℕ, s ≫ x ^ m = (s ≫ x) ^ m := fun m => by
    induction m with
    | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
    | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  rw [hy, ← hp]
  rfl

theorem compPow {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (ρ : T' ⟶ T) (x : T ⟶ A) (m : ℕ) :
    (ρ ≫ x) ^ m = ρ ≫ x ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem lab_level {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A) (hO : OneTrait D.toPre A lab) (k l N : ℕ) (hk : 1 ≤ k)
    (hl : 1 ≤ l) (hN : N = k * l) (p : QkPt D.toPre (Kb R) k) (q : QkPt D.toPre (Kb R) N) (hy : q.y = p.y)
    (hg : GtPtF.IsNsmul l q.g p.g) : (lab k p).left = ((lab N q) ^ l).left := by
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em, hW, -, -, hG', ⟨ga, hga, hcart, -⟩, hc, hind⟩ := hO
  have := hW.1
  haveI : CharZero W := hW.2.2
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have hG := GlobalTheory.globalFns_holds
  have hL := GlobalTheory.firstFiveLaws
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hl
  have hem : em.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb W) :=
    RingHom.ext em.commutes
  have hsq : spMap em.toRingHom ≫ jFK (R := R) (Kb R) = (TFK (R := W) (Kb W)).hom ≫ spMap ga := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hem]
    refine congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_))
    simp only [RingHom.comp_apply]
    rw [hga r]
    exact hc r
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv hcart (TFK (R := W) (Kb W)) _ hsq
  let s : Over.mk (spMap em.toRingHom ≫ jFK (R := R) (Kb R)) ⟶ TFK (R := R) (Kb R) :=
    Over.homMk (spMap em.toRingHom) rfl
  have hcomp : ∀ {m : ℕ} (r : QkPt D.toPre (Kb R) m), 1 ≤ m →
      QkToAkU U'.toUnifPre (Kb W) m (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem r))
        (e.symm (s ≫ lab m r)) := by
    intro m r hm
    refine hind m hm r _ _ _ ((GlobalTheory.TorusExt.qkExt_iff hB _ hem _ _).2 rfl) rfl
      ((GlobalTheory.ArcPull.eq_pullQk_iff hD hG hc hB hB' _ _).1 rfl).2 ?_
    rw [← he, e.apply_symm_apply]
    rfl
  have h₁ := hcomp p hk
  have h₂ := (GlobalTheory.LevelCompat.qkToAkU_level hL W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k l N hk hl hN
    (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem p))
    (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem q)) (e.symm (s ≫ lab N q))).2
    (by show hD.xe.symm p.y = hD.xe.symm q.y; rw [hy])
    ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 (by
      show GlobalTheory.ArcPull.pullGt hD hG hc (GlobalTheory.TorusExt.gtExt D.toPre em.toRingHom hem p.g) =
        l • GlobalTheory.ArcPull.pullGt hD hG hc (GlobalTheory.TorusExt.gtExt D.toPre em.toRingHom hem q.g)
      rw [(GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hg, map_nsmul, map_nsmul])) (hcomp q hN1)
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k hk
  have hx := ((hf _ _).1 h₁).trans ((hf _ _).1 h₂).symm
  have hs : s ≫ lab k p = s ≫ lab N q ^ l := by
    have := congrArg e hx
    rw [e.apply_symm_apply, map_pow, e.apply_symm_apply] at this
    rw [this, compPow]
  have : Epi (spMap em.toRingHom) := Flat.epi_of_flat_of_surjective _
  exact (cancel_epi (spMap em.toRingHom)).1 (congrArg (fun z => z.left) hs)

end GlobalTheory.Mum.GalSquares


open GlobalTheory.Mum.GalSquares in
theorem GlobalTheory.Mum.galEqN_of_squares : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime →
    Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R)))
    (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i →
      ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' →
        (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left) → GalEqN n lab := by
  intro R _ _ _ hR n hn _ _ D A lab hO ⟨i₀, H⟩ σ j p p' hpp'
  letI := GlobalTheory.TorusExt.gtGroup D.toPre (Kb R)
  have hi : i₀ ≤ max i₀ j := le_max_left _ _
  have hj : j ≤ max i₀ j := le_max_right _ _
  have hN : (n ^ max i₀ j) ^ 2 = n ^ j * n ^ (2 * max i₀ j - j) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hl : 1 ≤ n ^ (2 * max i₀ j - j) := Nat.one_le_pow _ _ hn.pos
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  obtain ⟨q, hqy, hqg⟩ := exists_div hR D _ _ hl hN p
  obtain ⟨q', hq', hq'y, hq'g⟩ := qkExt_nsmul D.toPre D.tau_bimult σ _ hpp' hqy hqg
  have e₁ := lab_level D A lab hO _ _ _ hk hl hN p q hqy ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 hqg.symm)
  have e₂ := lab_level D A lab hO _ _ _ hk hl hN p' q' hq'y ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 hq'g.symm)
  rw [e₂, pow_left_of_comp σ _ _ (H _ hi σ q q' hq'), ← e₁]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointExtendsOverNormalDomain
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Tors

theorem torsion_extend : Laws → ∀ (R : Type) [CommRing R] [IsDomain R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (P : PolAV (Spec (CommRingCat.of R))) (N : ℕ), 1 ≤ N → ∀ x : TF (R := R) (FractionRing R) ⟶ P.A, x ^ N = 1 → ∃ b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A, b ^ N = 1 ∧ x = toUnit _ ≫ b := by
  intro hL R _ _ hR hIC P N hN x hx
  have hfin : IsFinite (mulA P.A N).left := (hL.mulN _ P N hN).1
  have hj : jFK (R := R) (FractionRing R) = 𝟙 _ := by
    simp [jFK]
  have hTF : (TF (R := R) (FractionRing R)).hom = jK R := by
    simp [TF, hj]
  have e1 : x ≫ mulA P.A N = toUnit _ ≫ η[P.A] := by
    rw [mulA, MonObj.comp_pow, Category.comp_id, hx]; rfl
  have h : x.left ≫ (mulA P.A N).left = jK R ≫ η[P.A].left := by
    have := congrArg CommaMorphism.left e1
    simp only [Over.comp_left] at this
    rw [this]
    congr 1
  obtain ⟨l, hl1, hl2⟩ := GlobalTheory.FiniteLift.exists_lift (mulA P.A N).left η[P.A].left x.left h
  have hl3 : l ≫ P.A.hom = 𝟙 _ := by
    rw [← Over.w (mulA P.A N), ← Category.assoc, hl1, Over.w η[P.A]]
    simp
  let b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A := Over.homMk l (by simpa using hl3)
  refine ⟨b, ?_, ?_⟩
  · have e2 : b ^ N = b ≫ mulA P.A N := by rw [mulA, MonObj.comp_pow, Category.comp_id]
    rw [e2]
    ext1
    simp only [Over.comp_left, b, Over.homMk_left, hl1]
    show _ = (toUnit _ ≫ η[P.A]).left
    rw [toUnit_unit, Category.id_comp]
  · ext1
    simp only [Over.comp_left, b, Over.homMk_left]
    have w := Over.w (toUnit (TF (R := R) (FractionRing R)))
    have w' : (toUnit (TF (R := R) (FractionRing R))).left = jK R := by
      rw [← hTF, ← w]
      first | rfl | simp | (erw [Category.comp_id])
    rw [w', hl2]

end GlobalTheory.Poinc.Tors
end
end

