module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0178
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0172
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PrimitiveExpansionThetaPullbackHeisenbergTransla
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuationSubring
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.GoodTrait
set_option linter.style.haveILetI false

theorem exists_unit_prime (O : Type) [CommRing O] [IsLocalRing O] : ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : O) := by
  have h : IsUnit (((3 : ℕ) : O) * 2 + -((5 : ℕ) : O)) := by
    have : ((3 : ℕ) : O) * 2 + -((5 : ℕ) : O) = 1 := by push_cast; norm_num
    rw [this]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  · exact ⟨3, by norm_num, by decide, isUnit_of_mul_isUnit_left h⟩
  · exact ⟨5, by norm_num, by decide, (IsUnit.neg_iff _).1 h⟩

theorem norm_eq_one_of_isUnit {W C : Type} [CommRing W] [NormedField C] (f : W →+* C) (hf : ∀ r, ‖f r‖ ≤ 1) {x : W}
    (hx : IsUnit x) : ‖f x‖ = 1 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h : ‖f x‖ * ‖f y‖ = 1 := by rw [← norm_mul, ← map_mul, hy, map_one, norm_one]
  have h₁ := hf x
  have h₂ := hf y
  have h₃ := norm_nonneg (f x)
  nlinarith

theorem exists_valuationSubring {K C : Type} [Field K] [NormedField C] [IsUltrametricDist C] (f : K →+* C) :
    ∃ S : ValuationSubring K, (∀ x, x ∈ S ↔ ‖f x‖ ≤ 1) ∧ ∀ x, S.valuation x = 1 ↔ ‖f x‖ = 1 := by
  let v := (NormedField.valuation (K := C)).comap f
  refine ⟨v.valuationSubring, fun x => ?_, fun x => ?_⟩
  · rw [Valuation.mem_valuationSubring_iff]
    exact Iff.rfl
  · rw [← (Valuation.isEquiv_valuation_valuationSubring v).eq_one_iff_eq_one]
    exact NNReal.coe_inj.symm

theorem isDominant_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    IsDominant (spMap f) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap f)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot f).1 hf]
  exact bot_le


set_option maxHeartbeats 1000000 in
theorem range_subset_abLocus : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), Function.Injective g → g.Finite → IsIntegrallyClosed R₁ → ThetaInt Y g y₁ → y₁ ≫ Y.j ≫ Y.s = jK R₁ ≫ spMap g ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₁ →+* W) (gam : FractionRing R₁ →+* FractionRing W), (∀ r, gam (algebraMap R₁ _ r) = algebraMap W _ (φ r)) → ∀ χ : Sp W ⟶ Y.X, spMap gam ≫ y₁ ≫ Y.j = jK W ≫ χ → IsUnit (φ (g PowerSeries.X)) → Set.range χ ⊆ abLocus Y.t.G := by
  intro h₁ h₂ h₃ h₄ h₅ h₆ h₇ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hO R₁ _ _ g y₁ _ _ _ hT hy W _ _ _ hW φ gam hgam χ hχ hu
  haveI : IsLocalRing O' := by
    rcases hO with ⟨h, -⟩ | ⟨h, -⟩
    · letI := h.toField
      exact inferInstance
    · exact inferInstance
  obtain ⟨n, hn, hodd, hnu⟩ := exists_unit_prime O'
  obtain ⟨hdvr, -, hch⟩ := id hW
  obtain ⟨C, _, _, _, _, alg, -, -, hC⟩ := GlobalTheory.Ex.exists_complete_isAlgClosed_cExt W (FractionRing W)
  let iC : W →+* C := (algebraMap (FractionRing W) C).comp (algebraMap W _)
  have hiC : Function.Injective iC := (algebraMap (FractionRing W) C).injective.comp (IsFractionRing.injective W _)
  haveI : CharZero C := charZero_of_injective_ringHom hiC
  obtain ⟨o, ho, hθ⟩ := hT
  haveI := o.charZero
  let Γ : AlgebraicClosure (FractionRing R₁) →+* C :=
    letI : Algebra (FractionRing R₁) C := ((algebraMap (FractionRing W) C).comp gam).toAlgebra
    (IsAlgClosed.lift (R := FractionRing R₁) (S := AlgebraicClosure (FractionRing R₁)) (M := C)).toRingHom
  have hΓ : Γ.comp (algebraMap (FractionRing R₁) _) = (algebraMap (FractionRing W) C).comp gam := by
    letI : Algebra (FractionRing R₁) C := ((algebraMap (FractionRing W) C).comp gam).toAlgebra
    exact RingHom.ext fun x => (IsAlgClosed.lift (R := FractionRing R₁) (S := AlgebraicClosure (FractionRing R₁)) (M := C)).commutes x
  have hΓ' : ∀ r, Γ (((algebraMap (FractionRing R₁) _).comp (algebraMap R₁ _)) r) = iC (φ r) := fun r => by
    have := DFunLike.congr_fun hΓ (algebraMap R₁ _ r)
    simp only [RingHom.comp_apply, hgam] at this
    exact this
  obtain ⟨o', hext, hth, -⟩ := GlobalTheory.FullExtend.main h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D _ C Γ o
  have e₀ : spMap Γ ≫ spMap (algebraMap (FractionRing R₁) (AlgebraicClosure (FractionRing R₁))) ≫ y₁ =
      spMap (algebraMap (FractionRing W) C) ≫ spMap gam ≫ y₁ := by
    rw [← Category.assoc, ← spMap_comp', hΓ, spMap_comp', Category.assoc]
  have bF : c.F →+* AlgebraicClosure (FractionRing R₁) :=
    ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫
      ((spMap (algebraMap (FractionRing R₁) (AlgebraicClosure (FractionRing R₁))) ≫ y₁) ≫ pullback.snd _ _).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (FractionRing R₁)))).hom).hom
  have ho' := (GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y _ bF).2.2 C Γ _ o o' ho hext
  rw [e₀] at ho'
  have e₁ : spMap gam ≫ jK R₁ = jK W ≫ spMap φ :=
    (spMap_comp' (algebraMap R₁ _) gam).symm.trans ((congrArg spMap (RingHom.ext hgam)).trans (spMap_comp' φ (algebraMap W _)))
  have e₂ : spMap (algebraMap (FractionRing W) (FractionRing W)) = 𝟙 _ := Spec.map_id _
  obtain ⟨M, f, χ', mp, hf, hfC, hχ', -⟩ := GlobalTheory.Ex.UnifModel.exists_mdl h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D l Xo c W₀ Y C W hW hC
    (FractionRing W) (algebraMap (FractionRing W) C) (fun _ => rfl) (spMap gam ≫ y₁)
    (φ.comp (g.comp ((PowerSeries.C (R := O')).comp b))) (by
      rw [e₂, Category.id_comp, Category.assoc, hy, spMap_comp', spMap_comp', spMap_comp', ← Category.assoc, e₁,
        Category.assoc]) o' ho'
  obtain ⟨v, hv, hint⟩ := hθ n 2 hn hodd hnu one_le_two
  obtain ⟨S, hS, hS'⟩ := exists_valuationSubring Γ
  obtain ⟨a₁, -, a₃⟩ := hint S fun r => by rw [hS, hΓ']; exact hC.1 _
  have a₄ := a₃ (by rw [hS', hΓ']; exact norm_eq_one_of_isUnit iC hC.1 hu)
  have hnC : ‖(n : C)‖ = 1 := by
    have := norm_eq_one_of_isUnit iC hC.1 (hnu.map (φ.comp (g.comp (PowerSeries.C (R := O')))))
    rwa [map_natCast, map_natCast] at this
  have hprop : IsProper M.t.G.hom := _root_.GlobalTheory.CosetGood.isProper_of_unit_in_cosets h₁ h₂ h₃ h₄ h₅ h₆ h₇ E H D C o' M n 2 hn hodd hnC le_rfl _ (hth _ _ hv)
    (fun x => (hS _).1 (a₁ x)) fun x => (a₄ x).imp fun h hh => (hS' _).1 hh
  let jC : M.W →+* C := (algebraMap (FractionRing M.W) C).comp (algebraMap M.W _)
  have hjC : Function.Injective jC := (algebraMap (FractionRing M.W) C).injective.comp (IsFractionRing.injective M.W _)
  have hjf : jC.comp f = iC := RingHom.ext hfC
  have hfi : Function.Injective f := Function.Injective.of_comp (f := jC) (by rw [← RingHom.coe_comp, hjf]; exact hiC)
  have := projProper _ _ _ Y.proj
  have : Y.X.IsSeparated := ⟨by rw [← terminal.comp_from Y.s]; infer_instance⟩
  have := isDominant_spMap jC hjC
  have e₃ : χ' = spMap f ≫ χ := by
    refine ext_of_isDominant (spMap jC) ?_
    have e₄ : spMap jC = jFK (R := M.W) C ≫ jK M.W := spMap_comp' _ _
    have e₅ : spMap iC = spMap (algebraMap (FractionRing W) C) ≫ jK W := spMap_comp' _ _
    rw [← Category.assoc, ← spMap_comp', hjf, e₅, e₄, Category.assoc, hχ', Category.assoc, Category.assoc, hχ]
  rintro _ ⟨x, rfl⟩
  obtain ⟨x', rfl⟩ := hf.to_isIntegral.comap_surjective hfi x
  have h := (abLocus_pullback abLocusOne Y.t.semi mp.cart.1 x').2 fun K _ _ t _ => inferInstance
  rw [e₃] at h
  exact h

end GlobalTheory.Ex.GoodTrait
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TestFibre

section
variable {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
  {F : Type} [Field F] [Algebra (FractionRing R) F]

abbrev cF (R : Type) [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] (c : F) :
    Γ((TFK (R := R) F).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c

def IsComb {k : ℕ} {J : Type} [Fintype J] (s : J → SecA A F k) (b : J → F) (t : SecA A F k) : Prop :=
  ∀ j, t.f j = ∑ l, liftFun A.A _ (cF R (b l)) * (s l).f j

abbrev FrameAt (x : TFK (R := R) F ⟶ A.A) : Type :=
  LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))

def ValIs {k : ℕ} (t : SecA A F k) (x : TFK (R := R) F ⟶ A.A) (e : FrameAt A x) (c : F) : Prop :=
  ∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J =
    @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val

def IsNormPull (ρ : LB.Gen (A.L.pull (eSec A.A))) (m N : ℕ) (th : SecA A F 1) (s : SecA A F N) : Prop :=
  ∃ α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, (snd (TFK (R := R) F) A.A ^ m).left]
      ![(N : ℤ), -((1 : ℕ) : ℤ)]),
    α.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left)
      (rigT A.A A.L ρ (TFK (R := R) F) ((N : ℤ) - 1)) ∧
    IsTwistPull A.A A.L (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _) (N : ℤ) ((1 : ℕ) : ℤ) α th s

end

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

def PtsOver (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) : Prop :=
  ∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left

def SecsOver (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A)))
    (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N) : Prop :=
  rig.IsGen ∧ (∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a)) ∧
  (∀ a, ValIs u.A th (x a) (e a) (y₀ ⟨S.th a, S.th_mem a⟩)) ∧
  (∀ i a, ValIs u.A (s i) (x a) (e a) (y₀ ⟨S.ev a i, S.ev_mem a i⟩)) ∧
  IsNormPull u.A rig (ρ.n ^ ρ.k) S.N th (s ρ.i₀) ∧
  ∀ a, ∃ θ : ThetaGrp u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p)),
    SymLift u.A.A u.A.L S.N S.N (x (S.r • a)) θ ∧ ∀ i σ, IsActOf u.A.A u.A.L S.N θ (s i) σ →
      IsComb u.A s (fun j => y₀ (algebraMap o S.R (S.ρ a j i))) σ

def NormIs (l : u.Lab) (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ) : Prop :=
  0 < lam ∧ QForm.IsQ u.D.toPre ϖ Q ∧ (∀ χ, l.q χ = lam * Q χ) ∧
  (∀ (c : PadicAlgCl p) (r : ℚ), (r : WithTop ℚ) ≤ v c ↔ ‖c‖ ≤ Real.exp (-(lam * r))) ∧
  ∀ (c : PadicAlgCl p) (r : ℚ), v c = (r : WithTop ℚ) ↔ ‖c‖ = Real.exp (-(lam * r))

theorem laws_all (h : Laws) (h₂ : Laws2) :
    LL ∧ TwistBCSpanStatement ∧ TWM.VRatioGtStatement ∧ TWStatement ∧ UUStatement := by
  have hS : SecBaseChangeSt := h.secBaseChange
  have hT : TwistBCSpanStatement := twistBCSpan_of twistBaseChange
  exact ⟨⟨h, h₂, laws3, uniformisationLaws_of_baseChange_laws polBaseChange_holds globalFns_holds hS twistBaseChange,
      laws5 globalFns_holds hS⟩, hT, RatioVal.main, TWM.tw_of globalFns_holds hT RatioVal.main,
    UnitBallFree.main globalFns_holds twistBaseChange⟩

end GlobalTheory.TestFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemThetaPointsOfClosureCosetCondition
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.ClosurePoint

theorem exists_full_of_closure_of_cosets :
    HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (n j : ℕ) (ρ z : K) (v : D.La → K), n.Prime → Odd n → 2 ≤ j → Compat H ((n ^ j) ^ 2) z ρ → (∀ G, VanishC D (n ^ j) G → MvPolynomial.eval₂ (cf z ρ) v G = 0) → (∀ x, ∃ h, v (x + n ^ (j - 1) • h) ≠ 0) → ∃ o : Full D K, o.ρ = ρ ∧ (o.I.ζ ((n ^ j) ^ 2) : K) = z ∧ o.Theta (n ^ j) v := by
  intro h1 h2 h3 h4 h5 h6 h7 E _ _ _ H D l Xo c W₀ Y K _ _ _ n j ρ z v hn hodd hj hc hvan hcos
  have hm : Odd (n ^ j) := hodd.pow
  have hn3 : 3 ≤ n := by
    have := hn.two_le
    rcases hodd with ⟨k, hk⟩
    omega
  have hm3 : 3 ≤ n ^ j := hn3.trans (Nat.le_self_pow (by omega) n)
  have hv0 : v ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := hcos 0
    exact hx (by rw [h]; rfl)
  obtain ⟨C, _, _, _, _, _, S, κ, _, _, res, i, o, M, v', r', z', hnorm, hS, hres, hth, hv', hr', hρ,
    hz', hz⟩ := _root_.GlobalTheory.ThetaClosure.exists_trait h1 h2 h3 h4 h5 h6 h7 E H D l Xo c W₀ Y K (n ^ j) ρ z v hm hc hv0 hvan
  have hunit : ∀ x, v x ≠ 0 → ‖(v' x : C)‖ = 1 := by
    intro x hx
    have hle : ‖(v' x : C)‖ ≤ 1 := (hS _).1 (v' x).2
    by_contra hne
    have h0 := hres (v' x) (lt_of_le_of_ne hle hne)
    rw [hv' x] at h0
    exact hx (i.injective (by rw [h0, map_zero]))
  have hprop : IsProper M.t.G.hom :=
    _root_.GlobalTheory.CosetGood.isProper_of_unit_in_cosets h1 h2 h3 h4 h5 h6 h7 E H D C o M n j hn hodd (hnorm n hn.pos) hj
      (fun x => v' x) hth (fun x => (hS _).1 (v' x).2)
      (fun x => (hcos x).imp fun h hh => hunit _ hh)
  obtain ⟨o', hρ', hζ', hth'⟩ := _root_.GlobalTheory.Ex.Specialise.exists_specialisation h1 h2 h3 h4 h5 h6 h7 E H D C hnorm o M hprop S hS κ res
    hres (n ^ j) v' hm hm3 hth (by
      obtain ⟨x, hx⟩ := hcos 0
      exact ⟨_, by rw [hv']; exact (map_ne_zero i).2 hx⟩)
  refine _root_.GlobalTheory.Ex.ThetaDescent.exists_full_of_theta_in_subfield h1 h2 h3 h4 h5 h6 h7 E H D l Xo c W₀ Y K κ i (n ^ j) ρ z v o' hm hc
    ((hρ' r' hr').trans hρ) ((hζ' _ (by positivity) z' hz').trans hz) ?_
  have : (fun x => res (v' x)) = fun x => i (v x) := funext hv'
  rwa [this] at hth'

end GlobalTheory.Ex.ClosurePoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelUniformisationOfAbelianLocusDirectImage
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory

theorem isAdmissibleCompleteLocalDomainPrime_maximalIdeal (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (h₁ : IsNoetherianRing R) (h₂ : IsIntegrallyClosed R) (h₃ : IsAdicComplete (IsLocalRing.maximalIdeal R) R) :
    admitted R (IsLocalRing.maximalIdeal R) := by
  refine ⟨⟨h₁, inferInstance, h₂, h₃⟩, h₃, inferInstance, (IsLocalRing.maximalIdeal.isMaximal R).isPrime, ?_⟩
  let _ : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  infer_instance

theorem model_uniformisation_of_clauses : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Ega → USt → PelSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → Y.N3 := by
  intro hL hL2 hL3 hL4 hL5 hE hU hP E _ _ _ H D l Xo c W₀ Y p hN R _ _ _ _ hR₁ hR₂ hR₃ ξ t ht hne hsp
  obtain ⟨-, hpol, hloc⟩ := _root_.GlobalTheory.LN.generic_point_of_meets_abLocus hL hL2 E H D l Xo c W₀ Y p hN R ξ t ht hne
  have hθ : ThetaNZ t.G t.PP.L := _root_.GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible E H Y.X Y.t hN.2.2.1 R ξ t ht
  have hadm : admitted R (IsLocalRing.maximalIdeal R) := isAdmissibleCompleteLocalDomainPrime_maximalIdeal R hR₁ hR₂ hR₃
  let _ : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  have hpid : IsPrincipalIdealRing (R ⧸ IsLocalRing.maximalIdeal R) := inferInstance
  have hsplit : SplitOver t.G (IsLocalRing.maximalIdeal R) := hsp
  obtain ⟨P, hP'⟩ := _root_.GlobalTheory.LN.UnifPrime.exists_pelUnif hL hL2 hL3 hL4 hL5 hE hU hP E H R _ hadm hpid t hpol hsplit hθ
  have hopen : IsOpen (abLocus t.G) := by
    obtain ⟨U, hU', -⟩ := hN.2.2.2.1
    rw [← hloc, ← hU']
    exact U.isOpen.preimage ξ.continuous
  refine ⟨P, ?_, hP'⟩
  rw [hloc]
  exact _root_.GlobalTheory.psiUnitOn_abLocus_pel hL hL2 hL3 hL4 hL5 E H R _ hadm t P hP' hopen

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLevelOfIsAlgClosed
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem GlobalTheory.nonempty_level_of_isAlgClosed : ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (M : ℕ) (ze : kˣ), (M : k) ≠ 0 → IsPrimitiveRoot ze M → Nonempty (Out.Level P M (unitOn ze)) := by
  intro k _ _ P M ze hM hz
  have hz0 : IsPrimitiveRoot (ze : k) M := IsPrimitiveRoot.coe_units_iff.mpr hz

  have hinj : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ Sp k),
      Function.Injective ((Scheme.Hom.appTop s).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) := by
    intro K _ s
    exact Function.Injective.of_comp
      ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp
        ((Scheme.Hom.appTop s).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).injective
  have hinv : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    fun a b h => hinj k (𝟙 _) (by rw [RingHom.comp_apply, RingHom.comp_apply, h])

  have hu : IsPrimitiveRoot (unitOn ze) M := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    exact hz0.map_of_injective hinv
  obtain ⟨hL, -⟩ := GlobalTheory.abelianSchemeLaws_all

  obtain ⟨x, hx1, hx2⟩ := GlobalTheory.ConstThetaLevel.exists_symplectic_points hL k P rfl M hM (unitOn ze) hu

  obtain ⟨lev, -⟩ := GlobalTheory.exists_level_of_pairing GlobalTheory.globalFns_holds hL.weil hL.mulN (Sp k) P M (unitOn ze) hu
    (fun K _ s => by
      refine ⟨fun h0 => hM ?_, ?_⟩
      · have hf := ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp
          ((Scheme.Hom.appTop s).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).injective
        exact hf (by rw [map_natCast, map_zero]; exact h0)
      · rw [← IsPrimitiveRoot.coe_units_iff]
        exact hz0.map_of_injective (hinj K s))
    x hx1 hx2
  exact ⟨lev⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NuGeTranslatePullSmul
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

namespace GlobalTheory.ZH

theorem eq_mul_of_isTwistPull {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    {m : T ⊗ A ⟶ A} {a b : ℤ} {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    {s s₀ : LB.Sec (LPow A L b T)} {t t₀ : LB.Sec (LPow A L a T)} {c : Γ(T.left, ⊤)}
    (e : ∀ j, s.f j = liftFun A _ c * s₀.f j)
    (h : IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α s t)
    (h₀ : IsTwistPull A L (lift (fst T A) m) m (lift_snd _ _) a b α s₀ t₀) (j) :
    t.f j = liftFun A _ c * t₀.f j := by
  have f₁ : (lift (fst T A) m).left ≫ (fst T A).left = (fst T A).left := by
    rw [← Over.comp_left, lift_fst]
  have key : (SecM.ofSec A t : SecM A L a T) = SecM.ofSec A (SecM.toSec A (c • SecM.ofSec A t₀)) :=
    VVRank.ofSec_ext A hL fun y J hJ => by
      rw [ThetaPtMove.sv_of_eq_mul (s := SecM.toSec A (c • SecM.ofSec A t₀)) (t := t₀) (c := c) (fun j => rfl) _ y hJ,
        VVRank.sv_of_isTwistPull A h _ y hJ, VVRank.sv_of_isTwistPull A h₀ _ y hJ,
        ThetaPtMove.sv_of_eq_mul e _ y hJ]
      simp only [Category.assoc, f₁]
      ring
  exact congrArg (fun q => q.1 j) key

theorem nuGe_translate_pull_smul : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th₀ : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th₀ ϑ → Prim D Q v ϑ → ∀ (m N : ℕ), N = m ^ 2 → Odd m → IsUnit (m : V) → ∀ (c : F) (r : ℚ) (th : SecA A F 1), (r : WithTop ℚ) ≤ v c → (∀ j, th.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * th₀.f j) → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := V) F) A.A).left, (snd (TFK (R := V) F) A.A ^ m).left] ![(N : ℤ), -((1 : ℕ) : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := V) F) ((N : ℤ) - 1)) → ∀ (s₁ t : SecA A F N) (x : TFK (R := V) F ⟶ A.A) (θ : ThetaGrp A.A A.L N (TFK (R := V) F)) (s : Fam D.toPre F N), IsTwistPull A.A A.L (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _) (N : ℤ) ((1 : ℕ) : ℤ) α th s₁ → x ^ N = 1 → SymLift A.A A.L N N x θ → IsActOf A.A A.L N θ s₁ t → U.ExpandsF F N w₀ t s → NuGe D Q F v N s r := by
  intro hLL hBC hVR hTW hUU V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th₀ ϑ hth hprim m N hNm hm hmu
    c r th hr eth α hα hn s₁ t x θ s hs₁ hx hθ ht hs
  subst hNm
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hN1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  obtain ⟨hB, hlin⟩ := expBijF_and_expandsF_lin hLL V _ hA D A G hG U
  obtain ⟨hB₁, -⟩ := hB F (m ^ 2) hN1 w₀ hN.1
  let T := TFK (R := V) F
  let κ : F ≃+* Γ(T.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv
  obtain ⟨u₁, hu₁⟩ := VVRank.exists_isTwistPull A.A (ψ := mulT A.A T m) (hm := lift_snd _ _) A.isLB hα th₀
  obtain ⟨t₀, ht₀⟩ := VVRank.exists_isTwistPull A.A (ψ := translT A.A θ.pt) (hm := lift_snd _ _) A.isLB θ.isGen u₁
  obtain ⟨c₀, hc₀⟩ := NormTheta.exists_value A.isLB hN.2.1 _ t₀
  obtain ⟨c', rfl⟩ := κ.surjective c₀
  obtain ⟨s₀, hs₀, -⟩ := hB₁ t₀
  have hP := _root_.GlobalTheory.UT.PrimPull.main hLL hBC hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th₀ ϑ hth hprim m hm hmu
    x t₀ c' s₀ hx ⟨α, u₁, θ, hα, hn, hu₁, hθ, ht₀, hc₀⟩ hs₀
  have e₁ := eq_mul_of_isTwistPull (c := κ c) A.isLB eth hs₁ hu₁
  have e₂ := eq_mul_of_isTwistPull (c := κ c) A.isLB e₁ ht ht₀
  have h₁ := hlin F (m ^ 2) w₀ t₀ t₀ t s₀ s₀ (c - 1) hs₀ hs₀ fun j => by
    refine (e₂ j).trans ?_
    have : κ c • SecM.ofSec A.A t₀ = κ (c - 1) • SecM.ofSec A.A t₀ + SecM.ofSec A.A t₀ := by
      rw [map_sub, map_one, sub_smul, one_smul, sub_add_cancel]
    exact congrArg (fun q => q.1 j) this
  rw [sub_smul, one_smul, sub_add_cancel] at h₁
  have := NuGe.smul Q hr ((isSmul_iff c s₀ s).2 ((hB₁ t).unique hs h₁)) hP.1
  rwa [zero_add] at this

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionTorsionMemUnitThetaConstantGroupStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_torsion_mem_unitThetaConstantGroup : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ n j : ℕ, n.Prime → Odd n → IsUnit (n : V) → 2 ≤ j → ∀ x : TFK (R := V) F ⟶ A.A, FromGt U.toUnifPre (n ^ j) x → x ∈ unitGrp v ρ th (n ^ j) := by
  first | exact @GlobalTheory.OneBasis.UnitGen.fromGt_mem_unitGrp | exact GlobalTheory.OneBasis.UnitGen.fromGt_mem_unitGrp | (intros; apply GlobalTheory.OneBasis.UnitGen.fromGt_mem_unitGrp <;> assumption)
end

