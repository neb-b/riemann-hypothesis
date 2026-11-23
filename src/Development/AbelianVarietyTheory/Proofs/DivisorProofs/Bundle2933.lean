module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2914
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2249
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedComplexFibreMarkedLatticeClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1358
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2745
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2762
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2886
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1106

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalTraitSystemAtClosedPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_classicalTrait_system_at_closedPoint : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z), IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁), Φ.Matches ∧ Φ.abelian₂ ∧ (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) := by
  first | exact @GlobalTheory.Poinc.PreSys.main | exact GlobalTheory.Poinc.PreSys.main | (intros; apply GlobalTheory.Poinc.PreSys.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonSemiAbelianPullbackTwoUnitaryTraits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.TraitUniq

theorem jK_comp_spMap {V W : Type} [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] (f : V →+* W)
    (fK : FractionRing V →+* FractionRing W) (hK : ∀ a, fK (algebraMap V _ a) = algebraMap W _ (f a)) :
    spMap fK ≫ jK V = jK W ≫ spMap f := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact hK a

theorem exists_common_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (T T' : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (f : T.V →+* W)
    (f' : T'.V →+* W) (fK : FractionRing T.V →+* FractionRing W) (fK' : FractionRing T'.V →+* FractionRing W),
    GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → Function.Injective f → Function.Injective f' → IsLocalHom f →
    IsLocalHom f' → (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) →
    (∀ a, fK' (algebraMap T'.V _ a) = algebraMap W _ (f' a)) → spMap fK ≫ T.y = spMap fK' ≫ T'.y →
    ∃ tW : SAB H (Sp W), Nonempty (SABMap tW T.t (spMap f)) ∧ Nonempty (SABMap tW T'.t (spMap f')) := by
  intro E _ _ _ H Dw l Xo c T T' W _ _ _ f f' fK fK' _ hdvr _ _ _ _ hK hK' hy
  obtain ⟨tW, ⟨mW⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap f) T.t
  obtain ⟨tW', ⟨mW'⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap f') T'.t
  obtain ⟨tK, ⟨a⟩, ⟨b⟩⟩ := T.gen
  obtain ⟨tK', ⟨a'⟩, ⟨b'⟩⟩ := T'.gen
  obtain ⟨uK, ⟨n⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap fK ≫ T.y ≫ pullback.fst _ _) Xo.univ.t
  obtain ⟨c₁⟩ := GlobalTheory.TraitOrder.cancel rfl b n
  have e' : spMap fK' ≫ T'.y ≫ pullback.fst _ _ = spMap fK ≫ T.y ≫ pullback.fst _ _ := by
    rw [← Category.assoc, ← hy, Category.assoc]
  obtain ⟨c₂⟩ := GlobalTheory.TraitOrder.cancel e' b' n
  obtain ⟨d₁⟩ := GlobalTheory.TraitOrder.comp (jK_comp_spMap f fK hK) a c₁
  obtain ⟨d₂⟩ := GlobalTheory.TraitOrder.comp (jK_comp_spMap f' fK' hK') a' c₂
  obtain ⟨x₁⟩ := GlobalTheory.TraitOrder.cancel rfl mW d₁
  obtain ⟨x₂⟩ := GlobalTheory.TraitOrder.cancel rfl mW' d₂
  obtain ⟨ψ, -⟩ := GlobalTheory.ModelUniqueChecks.existsUnique_map W (FractionRing W) tW tW' uK x₁ x₂
  exact ⟨tW, ⟨mW⟩, GlobalTheory.TraitOrder.comp (Category.id_comp _) mW' ψ⟩

end GlobalTheory.UPoinc.TraitUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexUniformisationHarrisTaylor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Unif

theorem eta_points {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {g : ℕ} {y : Sp ℂ ⟶ S}
    {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} {Λ' : Type} [AddCommGroup Λ'] {lv : Λ' → (𝟙_ (Over S) ⟶ G)} {N : ℕ}
    (hN : 0 < N) (hadd : ∀ z w, e (z + w) = e z * e w) (hsurj : Function.Surjective e)
    (hlv : ∀ x y, lv (x + y) = lv x * lv y) (hker : ∀ x, lv (N • x) = 1) (a : Λ') :
    ∃ z, e z = 1 ∧ toUnit _ ≫ lv a = e ((N : ℂ)⁻¹ • z) := by
  obtain ⟨w, hw⟩ := hsurj (toUnit _ ≫ lv a)
  have hepow : ∀ n : ℕ, e (n • w) = e w ^ n := by
    intro n
    induction n with
    | zero =>
      have h0 := hadd 0 0
      rw [add_zero] at h0
      simpa using (mul_eq_left.mp h0.symm)
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hlvpow : ∀ n : ℕ, lv (n • a) = lv a ^ n := by
    intro n
    induction n with
    | zero =>
      have h0 := hlv 0 0
      rw [add_zero] at h0
      simpa using (mul_eq_left.mp h0.symm)
    | succ n ih => rw [succ_nsmul, hlv, ih, pow_succ]
  refine ⟨N • w, ?_, ?_⟩
  · rw [hepow, hw, ← comp_pow, ← hlvpow, hker, comp_one]
  · have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [← hw, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN', one_smul]

end GlobalTheory.UPel.HT.Unif

namespace GlobalTheory.UPel.HT.Unif

theorem unifAt_change {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ ρ₂ : O →+* Matrix (Fin g) (Fin g) ℂ} {R : Type}
    [CommRing R] {σ : R →+* ℂ} {Λ : Type} {F : Fam R O Λ g} {N : ℕ} {D' : PLat O bar} {t : Λ → D'.La}
    {P : D'.La →+ (Fin g → ℂ)} {y : Sp ℂ ⟶ F.X} {e : (Fin g → ℂ) → (Over.mk y ⟶ F.A)}
    (hU : UnifAt F σ ρ N D' t P y e) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hc : ∀ a z, h (ρ a *ᵥ z) = ρ₂ a *ᵥ h z) :
    UnifAt F σ ρ₂ N D' t (h.toLinearMap.toAddMonoidHom.comp P) y (fun z => e (h.symm z)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hU
  have hc' : ∀ a z, h.symm (ρ₂ a *ᵥ z) = ρ a *ᵥ h.symm z := fun a z => by
    rw [LinearEquiv.symm_apply_eq, hc, LinearEquiv.apply_symm_apply]
  have hs : ∀ (k : ℂ) x, h.symm (k • h (P x)) = k • P x := fun k x => by simp
  refine ⟨h1, GlobalTheory.T.comp_linearEquiv_intertwining O bar D' g ρ ρ₂ P h h2 hc, ?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.LocLift.IsExp.comp h3 (LinearEquiv.toContinuousLinearEquiv h.symm)
  · intro z
    rw [h4]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by simp [hx]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, by simp⟩
  · intro a z
    simp only [hc']
    exact h5 a _
  · intro k a b c hk hcc
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, hs]
    exact h6 k a b c hk hcc
  · intro a
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, hs]
    exact h7 a

end GlobalTheory.UPel.HT.Unif

namespace GlobalTheory.UPel.HT.Unif

variable {p : ℕ} [Fact p.Prime]

theorem exists_unifAt_of_exp (D : Datum p) {R : Type} [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ)
    (o : Obj b N (spMap σ)) (h : SmoothOfRelativeDimension D.g o.A.hom)
    (hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB) (hN : 0 < N)
    (ρ' : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ o.A))
    (Λ : Submodule ℤ (Fin D.g → ℂ)) (he : IsExp (𝟙 _) e) (hd : DiscreteTopology Λ)
    (hs : Submodule.span ℝ (Λ : Set (Fin D.g → ℂ)) = ⊤) (hk : ∀ z, e z = 1 ↔ z ∈ Λ)
    (hρ : ∀ a z, e (ρ' a *ᵥ z) = e z ≫ o.act.act a) :
    ∃ (D' : PLat D.O D.inv) (t : D.La → D'.La) (Q : D'.La →+ (Fin D.g → ℂ)), UnifAt (o.fam h hL) σ ρ' N D' t Q (𝟙 _) e := by
  have hst : ∀ a z, z ∈ Λ → ρ' a *ᵥ z ∈ Λ := fun a z hz => by
    haveI := o.act.hom a
    rw [← hk, hρ, (hk z).2 hz]
    exact one_comp _
  let φ : D.O →+* Module.End ℤ Λ :=
    { toFun := fun a =>
        { toFun := fun x => ⟨ρ' a *ᵥ (x : Fin D.g → ℂ), hst a x x.2⟩
          map_add' := fun x y => Subtype.ext (by simp [Matrix.mulVec_add])
          map_smul' := fun n x => Subtype.ext (by
            show ρ' a *ᵥ (n • (x : Fin D.g → ℂ)) = n • (ρ' a *ᵥ (x : Fin D.g → ℂ))
            exact map_zsmul (Matrix.mulVecLin (ρ' a)) n (x : Fin D.g → ℂ)) }
      map_one' := by ext x i; simp
      map_mul' := fun a b => by ext x i; simp [Matrix.mulVec_mulVec]
      map_zero' := by ext x i; simp
      map_add' := fun a b => by ext x i; simp [Matrix.add_mulVec] }
  letI : Module D.O Λ := Module.compHom Λ φ
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let Q : Λ →+ (Fin D.g → ℂ) := Λ.subtype.toAddMonoidHom
  have hQi : Function.Injective Q := Subtype.val_injective
  have hQk : ∀ z, e z = 1 ↔ z ∈ Q.range := fun z => by
    rw [hk]; simp [Q]
  have hQs : Submodule.span ℝ (Set.range Q) = ⊤ := by
    simpa [Q] using hs
  obtain ⟨Hm, EF, hH, hpos, him, hweil⟩ := _root_.GlobalTheory.exists_riemannForm_of_relAmple (Sp ℂ) o.A D.g o.ab h
    (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) hL o.ample (𝟙 _) e Λ Q he hQi hQk
  obtain ⟨halt, hnd⟩ := GlobalTheory.T.im_hermForm_alternating_nondegenerate_on_lattice Λ D.g Q Hm EF hQi hQs hH hpos him
  have hmv : ∀ (a : D.O) (k : ℂ) (z : Fin D.g → ℂ), k • (ρ' a *ᵥ z) = ρ' a *ᵥ (k • z) := fun a k z => by
    rw [Matrix.mulVec_smul]
  have hadj : ∀ (a : D.O) x y, EF (φ a x) y = EF x (φ (D.inv a) y) := by
    intro a
    have hu : ∀ (c : D.O) (k : ℕ) (x : Λ), 0 < k →
        e ((k : ℂ)⁻¹ • Q ((φ c).toAddMonoidHom x)) = e ((k : ℂ)⁻¹ • Q x) ≫ o.act.act c := fun c k x _ => by
      show e ((k : ℂ)⁻¹ • (ρ' c *ᵥ (x : Fin D.g → ℂ))) = _
      rw [hmv, hρ]
      rfl
    have key := GlobalTheory.T.rosati_adjoint_iff_biextension_pullbacks_isomorphic o.A D.g o.ab h o.P o.isLB o.rig₁ o.rig₂ o.symm o.ample e Λ Q EF he hQi hQk hweil
      (o.act.act a) (o.act.act (D.star a).unop) (φ a).toAddMonoidHom (φ (D.inv a)).toAddMonoidHom (o.act.hom a)
      (o.act.hom _) (hu a) (hu (D.inv a))
    exact key.1 (o.rosati a)
  have het : ∀ a : D.La, ∃ z, e z = 1 ∧ toUnit _ ≫ o.eta a = e ((N : ℂ)⁻¹ • z) :=
    eta_points hN he.1 he.2.1 o.eta_add o.eta_ker
  choose tz htz using het
  let D' : PLat D.O D.inv :=
    { La := Λ
      fin := ZLattice.module_finite ℝ Λ
      free := ZLattice.module_free ℝ Λ
      EF := EF
      alt := halt
      nondeg := hnd
      adj := fun a x y => hadj a x y }
  refine ⟨D', fun a => (⟨tz a, (hk _).1 (htz a).1⟩ : Λ), Q, Category.id_comp _,
    ⟨fun a x => rfl, hQi, ?_, hQs, Hm, hH, hpos, him⟩, he, hQk, hρ, hweil, fun a => (htz a).2⟩
  have : Q.range = Λ.toAddSubgroup := by ext; simp [Q]
  rw [this]
  exact hd

end GlobalTheory.UPel.HT.Unif

namespace GlobalTheory.UPel.HT.Unif

theorem exists_unifAt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL, 0 < N → N.Coprime p → b.IsType σ ρ → ∃ D' t Q e, D.Cls N D' t ∧ UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e := by
  intro p _ D R _ b N σ ρ o h hL hN hNp hty
  obtain ⟨e₀, Λ, hexp, hdisc, hspan, hker⟩ := _root_.GlobalTheory.FibreExp.exists_exp_lattice (Sp ℂ) o.A D.g o.ab h (𝟙 _)
  obtain ⟨ρ', hρ'⟩ := _root_.GlobalTheory.ExpLin.exists_ringHom_matrix_lift (Sp ℂ) o.A D.g D.O o.act.act o.ab h o.act.hom o.act.one o.act.mul o.act.add (𝟙 _) e₀ hexp
  obtain ⟨D', t, Q, hU⟩ := exists_unifAt_of_exp D b N σ o h hL hN ρ' e₀ Λ hexp hdisc hspan hker hρ'
  have hty' := _root_.GlobalTheory.UPel.HT.LieType.lie_isType p D R b N σ ρ' o h hL D' t Q e₀ hU
  obtain ⟨M, hMu, hM⟩ := _root_.GlobalTheory.UPel.HT.rep_conj_of_trace_eq p D D.g ρ ρ' (fun c => by rw [hty c, hty' c])
  set u := hMu.unit with hu
  have hM' : ∀ a, ρ' a * (u : Matrix (Fin D.g) (Fin D.g) ℂ) = u * ρ a := fun a => by
    rw [hu, IsUnit.unit_spec]; exact hM a
  let Mi : Matrix (Fin D.g) (Fin D.g) ℂ := ((u⁻¹ : (Matrix (Fin D.g) (Fin D.g) ℂ)ˣ) : Matrix (Fin D.g) (Fin D.g) ℂ)
  have hinv : ∀ a, Mi * ρ' a = ρ a * Mi := fun a => by
    calc Mi * ρ' a = Mi * ρ' a * ((u : Matrix (Fin D.g) (Fin D.g) ℂ) * Mi) := by
          rw [Units.mul_inv, _root_.mul_one]
      _ = Mi * (ρ' a * u) * Mi := by simp only [_root_.mul_assoc]
      _ = Mi * (u * ρ a) * Mi := by rw [hM']
      _ = ρ a * Mi := by rw [← _root_.mul_assoc Mi, Units.inv_mul, _root_.one_mul]
  let hl : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ) := Matrix.toLinearEquiv' Mi (Units.invertible u⁻¹)
  have hc : ∀ a z, hl (ρ' a *ᵥ z) = ρ a *ᵥ hl z := fun a z => by
    show Mi *ᵥ (ρ' a *ᵥ z) = ρ a *ᵥ (Mi *ᵥ z)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hinv]
  have hU2 := unifAt_change hU hl hc
  obtain ⟨t', hcls, ht'⟩ := _root_.GlobalTheory.UPel.HT.unifAt_cls p D R b N σ ρ o h hL D' t _ _ hN hNp hU2
  have hmk : IsMarkedIsom N D' D' t t' (LinearEquiv.refl D.O D'.La) := by
    refine ⟨fun x y => rfl, fun a => ?_⟩
    obtain ⟨x, hx⟩ := ht' a
    exact ⟨-x, by rw [hx]; simp⟩
  exact ⟨D', t', _, _, hcls, _root_.GlobalTheory.PELU.unifAt_transport D.O D.inv D.g ρ R σ D.La (o.fam h hL) N D' D' t t' _ _ (𝟙 _) _
    (LinearEquiv.refl D.O D'.La) (LinearEquiv.refl ℂ (Fin D.g → ℂ)) hN hU2 hmk (fun x => rfl) hU2.2.1⟩

end GlobalTheory.UPel.HT.Unif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionAtBoundary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BdLocalExt

theorem exists_extension_of_smooth {A : CommRingCat.{0}} [IsRegularRing A] {X Y : Scheme.{0}} (p : X ⟶ Spec A) [Smooth p]
    [QuasiCompact p] (u : Y ⟶ X) [IsOpenImmersion u] (L : LB Y) (hL : L.IsLB) :
    ∃ M : LB X, M.IsLB ∧ LBIso (M.pull u) L := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have h : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ UniqueFactorizationMonoid (X.presheaf.stalk x) := fun x => by
    haveI : Smooth (show X ⟶ Spec (CommRingCat.of A) from p) := ‹Smooth p›
    haveI : IsRegularRing (X.presheaf.stalk x) :=
      GlobalTheory.ExtendRig.isRegularRing_stalk GlobalTheory.isRegularRing_of_smooth A p x
    haveI : IsRegularLocalRing (X.presheaf.stalk x) := IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
    haveI : IsDomain (X.presheaf.stalk x) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
    exact ⟨inferInstance, GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
      GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE _⟩
  exact GlobalTheory.exists_lineBundle_extension_of_isDomain X Y u inferInstance (fun x => (h x).1) (fun x => (h x).2) L hL

theorem exists_extension_stalk {S X Y : Scheme.{0}} (g : X ⟶ S) [Smooth g] [QuasiCompact g] (e : Y ⟶ X)
    [IsOpenImmersion e] (x : S) [IsRegularLocalRing (S.presheaf.stalk x)] (L : LB Y) (hL : L.IsLB) :
    ∃ M : LB (pullback g (S.fromSpecStalk x)), M.IsLB ∧
      LBIso (M.pull (pullback.map (e ≫ g) (S.fromSpecStalk x) g (S.fromSpecStalk x) e (𝟙 _) (𝟙 _) (by simp) (by simp)))
        (L.pull (pullback.fst (e ≫ g) (S.fromSpecStalk x))) := by
  haveI : IsRegularRing (S.presheaf.stalk x) := GlobalTheory.isRegularRing_of_isRegularLocalRing _
  exact exists_extension_of_smooth (pullback.snd g (S.fromSpecStalk x)) _ _ (pull_isLB hL _)

end GlobalTheory.BdLocalExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfDieudonneRangeLe
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

theorem omega_finite_of_theory (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G : PDivGroup p k) : Module.Finite k G.omega := by
  classical
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials p T k
  obtain ⟨-, hs, -, hsm, -⟩ := hθ G
  haveI := T.base.finite G trivial
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule (WittVector p k) (T.M G)).FG)
  refine ⟨⟨S.image (θ G), ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro y -
  obtain ⟨m, rfl⟩ := hs y
  have hm : m ∈ Submodule.span (WittVector p k) (S : Set (T.M G)) := hS ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [(θ G).map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨b, rfl⟩ : ∃ b, WittVector.frobenius b = a :=
      ⟨(WittVector.frobeniusEquiv p k).symm a, (WittVector.frobeniusEquiv p k).apply_symm_apply a⟩
    rw [hsm]
    exact Submodule.smul_mem _ _ hx

theorem range_omegaMap_le_of_range_map_le (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] {G Q H : PDivGroup p k} (q : G ⟶ Q) (f : G ⟶ H)
    (h : LinearMap.range (T.map f) ≤ LinearMap.range (T.map q)) :
    LinearMap.range (omegaMap G H f) ≤ LinearMap.range (omegaMap G Q q) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials p T k
  rintro _ ⟨v, rfl⟩
  obtain ⟨m, rfl⟩ := (hθ H).2.1 v
  obtain ⟨m', hm'⟩ := h ⟨m, rfl⟩
  refine ⟨θ Q m', ?_⟩
  rw [← (hθ G).2.2.2.2 Q q m', ← (hθ G).2.2.2.2 H f m, hm']

theorem exists_comp_eq_of_colength (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (n : ℕ) : ∀ (G Q H : PDivGroup p k) (q : G ⟶ Q) (f : G ⟶ H),
    G.IsConn → IsIsog q →
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = n →
    LinearMap.range (T.map f) ≤ LinearMap.range (T.map q) → ∃ g : Q ⟶ H, q ≫ g = f := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G Q H q f hG hq hn hfq
  have hω := range_omegaMap_le_of_range_map_le p T k q f hfq
  by_cases hsurj : Function.Surjective (omegaMap G Q q)
  · have hs := _root_.GlobalTheory.PDivGroup.app_surjective_of_omegaMap_surjective p k G Q q hG hsurj
    obtain ⟨m, q', h1, h2⟩ := hq
    refine _root_.GlobalTheory.Dieu.exists_comp_eq_of_kerIdeal_le p k G Q H m q q' f h1 h2 ?_
    rw [kerIdeal_of_surjective (hs m)]
    exact (kerIdeal_le_ker_iff _ _).2 fun c => by simp
  obtain ⟨C, i1, i2, i3, i4, π, hπs, hker, hnil, hfrob⟩ := _root_.GlobalTheory.PDiv.FrobKerInter.exists_quotient_kerIdeal_sup_frobKerIdeal p k G Q q
  obtain ⟨Q₁, q₁, q₁', e1, e2, hk1⟩ := _root_.GlobalTheory.HTPair.exists_quot_field p k G C π hπs
  have hqπ : kerIdeal (q.app 1) ≤ RingHom.ker π := hker ▸ le_sup_left
  have hcq := _root_.GlobalTheory.PDivGroup.cot_kernel_eq_coker_omegaMap p k G Q q C π hπs
  have hcq₁ := _root_.GlobalTheory.PDivGroup.cot_kernel_eq_coker_omegaMap p k G Q₁ q₁ C π hπs
  have hcotf : cotMap (π.comp (f.app 1)) = 0 :=
    hcq.2.2 H f fun w hw => hcq.1 hqπ w (hω hw)
  have htriv := GlobalTheory.T.eq_counit_of_heightOne_cotangentPullback_zero p k C (H.A 1) (π.comp (f.app 1)) hnil hcotf
  have hfπ : kerIdeal (f.app 1) ≤ RingHom.ker π :=
    (kerIdeal_le_ker_iff (f.app 1) (π : G.A 1 →ₐ[k] C)).2 htriv
  have e1' : q₁ ≫ q₁' = (p : ℤ_[p]) ^ 1 • 𝟙 G := by rw [pow_one]; exact e1
  have e2' : q₁' ≫ q₁ = (p : ℤ_[p]) ^ 1 • 𝟙 Q₁ := by rw [pow_one]; exact e2
  obtain ⟨f', hf'⟩ := _root_.GlobalTheory.Dieu.exists_comp_eq_of_kerIdeal_le p k G Q₁ H 1 q₁ q₁' f e1' e2' (hk1 ▸ hfπ)
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.Dieu.exists_comp_eq_of_kerIdeal_le p k G Q₁ Q 1 q₁ q₁' q e1' e2' (hk1 ▸ hqπ)
  have hq₁ : IsIsog q₁ := ⟨1, q₁', e1', e2'⟩
  have hr' : IsIsog r := (_root_.GlobalTheory.Dieu.isog_basics p k G).2.2.1 Q₁ Q q₁ r hq₁ (hr ▸ hq)
  have hG₁ : Q₁.IsConn := _root_.GlobalTheory.Dieu.isConn_of_isIsog p k G Q₁ q₁ hq₁ hG
  have hfun := _root_.GlobalTheory.Dieu.base_functor_props p _ T.base k G Q₁ Q trivial trivial trivial
  have hfun' := _root_.GlobalTheory.Dieu.base_functor_props p _ T.base k G Q₁ H trivial trivial trivial
  have hmq : T.map q = T.map q₁ ∘ₗ T.map r := by rw [← hr]; exact hfun.2.1 q₁ r
  have hmf : T.map f = T.map q₁ ∘ₗ T.map f' := by rw [← hf']; exact hfun'.2.1 q₁ f'
  have hinj := (_root_.GlobalTheory.Dieu.isog_finrank_omega p T k G Q₁ q₁ hq₁).1
  have hfr : LinearMap.range (T.map f') ≤ LinearMap.range (T.map r) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hfq ⟨y, rfl⟩
    refine ⟨z, hinj ?_⟩
    rw [← LinearMap.comp_apply, ← hmq, hz, hmf, LinearMap.comp_apply]

  haveI := omega_finite_of_theory p T k G
  have hCq : Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G Q q)) = Module.finrank k (Cot k C) :=
    hcq.2.1 (hker ▸ sup_le_sup_left hfrob _) hqπ
  have hCq₁ : Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G Q₁ q₁)) =
      Module.finrank k (Cot k C) := hcq₁.2.1 (hk1 ▸ le_sup_left) hk1.le
  have hpos : 0 < Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G Q q)) := by
    haveI : Nontrivial (G.omega ⧸ LinearMap.range (omegaMap G Q q)) :=
      Submodule.Quotient.nontrivial_iff.2 fun h => hsurj (LinearMap.range_eq_top.1 h)
    exact Module.finrank_pos
  have h1 : (1 : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q₁)) := by
    refine le_trans ?_ (GlobalTheory.T.finrank_quot_range_le_length_quot_range_map p T k G Q₁ q₁).1
    rw [hCq₁, ← hCq]
    exact_mod_cast hpos
  have hadd := (_root_.GlobalTheory.Dieu.colength_add_and_pow_and_eq p k (T.M G) (T.M Q₁) (T.M Q)).1 (T.map q₁) (T.map r) hinj
  rw [← hmq, hn] at hadd
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (show Module.length (WittVector p k)
      (T.M G ⧸ LinearMap.range (T.map q₁)) ≠ ⊤ from fun h => by simp [h] at hadd)
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (show Module.length (WittVector p k)
      (T.M Q₁ ⧸ LinearMap.range (T.map r)) ≠ ⊤ from fun h => by simp [h] at hadd)
  rw [← ha, ← hb] at hadd
  rw [← ha] at h1
  have hab : n = a + b := by exact_mod_cast hadd
  have ha1 : 1 ≤ a := by exact_mod_cast h1
  obtain ⟨g, hg⟩ := ih b (by omega) Q₁ Q H r f' hG₁ hr' hb.symm hfr
  exact ⟨g, by rw [← hr, Category.assoc, hg, hf']⟩

theorem exists_comp_eq_of_range_map_le : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G Q H : PDivGroup p k) (q : G ⟶ Q) (f : G ⟶ H), G.IsConn →
    IsIsog q → LinearMap.range (T.map f) ≤ LinearMap.range (T.map q) → ∃ g : Q ⟶ H, q ≫ g = f := by
  intro p _ T k _ _ _ G Q H q f hG hq hfq
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (_root_.GlobalTheory.Dieu.isog_finrank_omega p T k G Q q hq).2.1
  exact exists_comp_eq_of_colength p T k n G Q H q f hG hq hn.symm hfq

end GlobalTheory.Dieu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeSchemeRepresentingPolarizedHoms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomFixAff

theorem exists_homFixRep_finiteType : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro Rg _ _ A B _ _ _ _ L M hA hB hL hM rL rM aL aM
  have h := fun p => GlobalTheory.T.exists_local_representing_scheme_homFixedPullback Rg A B L M hA hB hL hM rL rM aL aM p
  choose U hpU hdat using h
  exact _root_.GlobalTheory.homFixRep_glue_opens (Sp Rg) A B L M hA hB hL hM rL rM (Sp Rg) U (fun p => ⟨p, hpU p⟩) hdat

end GlobalTheory.HomFixAff
end

