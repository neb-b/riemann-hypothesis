module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0180
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0114
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelValuationData
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionPointsGroupPairingStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0189
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleAdaptedBasisLinkMatrix
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsPolarisedAbelianVarietyGalois
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EgaBundleFromLaws
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem GlobalTheory.LN.ega_of_laws : Laws → Laws2 → Ega := fun h₁ h₂ =>
  ⟨_root_.GlobalTheory.FormalAlgebraise.algebraisation h₁ h₂, _root_.GlobalTheory.LocalMorAlg.existsUnique_hom_of_thickenings h₁ h₂, GlobalTheory.SecAlg.existsUnique_sec, GlobalTheory.T.exists_section_primitiveBundle_translate_localRing h₁ h₂⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralBasisCombinationOfIntegralFamily
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory.TestFibre

theorem exists_nsmul_of_nsmul_eq_zero {K : Type} {r N : ℕ} (hr : 0 < r) (hN : 0 < N) (a₀ : K → ZMod (r * N))
    (h : N • a₀ = 0) : ∃ a : K → ZMod (r * N), r • a = a₀ := by
  haveI : NeZero (r * N) := ⟨(Nat.mul_pos hr hN).ne'⟩
  have key : ∀ i, ∃ b : ZMod (r * N), r • b = a₀ i := by
    intro i
    have h1 : ((N * (a₀ i).val : ℕ) : ZMod (r * N)) = 0 := by
      have := congrFun h i
      simpa [nsmul_eq_mul] using this
    rw [ZMod.natCast_eq_zero_iff, _root_.mul_comm N] at h1
    obtain ⟨d, hd⟩ := Nat.dvd_of_mul_dvd_mul_right hN h1
    refine ⟨(d : ZMod (r * N)), ?_⟩
    rw [nsmul_eq_mul, ← Nat.cast_mul, ← hd, ZMod.natCast_zmod_val]
  choose a ha using key
  exact ⟨a, funext ha⟩

theorem exists_span_translates_of_eq_sq (h : Laws) (h₂ : Laws2) {V : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CharZero V] (hc : IsAdicComplete (IsLocalRing.maximalIdeal V) V) {ϖ : V}
    (hϖ : Irreducible ϖ) {D : DegData V (IsLocalRing.maximalIdeal V)} {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif (IsLocalRing.maximalIdeal V) D A G)
    (w₀ : W0 U.toUnifPre) (rig : LB.Gen (A.L.pull (eSec A.A))) (hw : NormW U.toUnifPre w₀ rig)
    (th th' : SecA A F 1) (ϑ : Fam D.toPre F 1) (hϑ : U.ExpandsF F 1 w₀ th' ϑ) (hP : Prim D Q v ϑ) (c : F)
    (hth : ∀ j, th.f j = liftFun A.A _ (cF V c) * th'.f j) (m : ℕ) (hm : Odd m) (hu : IsUnit (m : V)) (h3 : 3 ≤ m)
    (N : ℕ) (hN : N = m ^ 2) (Φ : Fam D.toPre F N) (hΦ : NuGe D Q F v N Φ 0) :
    ∃ (n : ℕ) (a : Fin n → F) (z : Fin n → (TFK (R := V) F ⟶ A.A)) (t : Fin n → SecA A F N)
      (r : Fin n → Fam D.toPre F N),
      (∀ i, 0 ≤ v (a i) ∧ z i ^ N = 1 ∧ U.ExpandsF F N w₀ (t i) (r i) ∧
        ∀ (s₁ σ : SecA A F N) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := V) F)), IsNormPull A rig m N th s₁ →
          SymLift A.A A.L (N : ℤ) N (z i) θ → IsActOf A.A A.L (N : ℤ) θ s₁ σ →
          ∀ j, σ.f j = liftFun A.A _ (cF V c) * (t i).f j) ∧ Φ = ∑ i, a i • r i := by
  subst hN
  obtain ⟨hL, h1, h2, h3', h4⟩ := laws_all h h₂
  obtain ⟨n, a, z, t, c', r, H, hs⟩ :=
    (GlobalTheory.T.valuation_nonneg_iff_span_multiplicationTranslates hL h1 h2 h3' h4 V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ rig hw th' ϑ hϑ hP m hm hu h3 Φ).1 hΦ
  refine ⟨n, a, z, t, r, fun i => ?_, hs⟩
  obtain ⟨ha, hz, hT, hE⟩ := H i
  exact ⟨ha, hz, hE, fun s₁ σ θ hs₁ hθ hσ =>
    GlobalTheory.T.symmetricLift_normalisedPullback_theta_smul hL V A F rig hw.2.1 m hm th th' c hth s₁ σ (t i) (z i) θ (c' i) hz hs₁ hθ hσ hT⟩

theorem IsComb.of_eq_mul {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} {J : Type} [Fintype J] {s : J → SecA A F k} {b : J → F}
    {σ t : SecA A F k} (hσ : IsComb A s b σ) {c : F} (hc : c ≠ 0)
    (ht : ∀ j, σ.f j = liftFun A.A _ (cF R c) * t.f j) : IsComb A s (fun l => c⁻¹ * b l) t := by
  intro j
  have hmul : ∀ x y : F, (liftFun A.A _ (cF R (x * y)) : Γ((TFK (R := R) F ⊗ A.A).left, (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U j)) = liftFun A.A _ (cF R x) * liftFun A.A _ (cF R y) := by
    intro x y
    simp only [liftFun, cF, map_mul]
  have hone : (liftFun A.A _ (cF R (1 : F)) : Γ((TFK (R := R) F ⊗ A.A).left, (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U j)) = 1 := by
    simp only [liftFun, cF, map_one]
  have h1 : t.f j = liftFun A.A _ (cF R c⁻¹) * σ.f j := by
    rw [ht j, ← _root_.mul_assoc, ← hmul, inv_mul_cancel₀ hc, hone, _root_.one_mul]
  rw [h1, hσ j, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [hmul, _root_.mul_assoc]

theorem exists_isComb_expands_of_nuGe_zero : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ → ValOver ϖ (PadicAlgCl p) v → NormIs u l ϖ Q v lam → ∀ (w₀ : W0 u.U.toUnifPre) (th' : SecA u.A (PadicAlgCl p) 1) (ϑ : Fam u.D.toPre (PadicAlgCl p) 1) (c : PadicAlgCl p), NormW u.U.toUnifPre w₀ rig → u.U.ExpandsF (PadicAlgCl p) 1 w₀ th' ϑ → Prim u.D Q v ϑ → (∀ j, th.f j = liftFun u.A.A _ (cF u.V c) * th'.f j) → c ≠ 0 → ∀ Φ : Fam u.D.toPre (PadicAlgCl p) S.N, NuGe u.D Q (PadicAlgCl p) v S.N Φ 0 → ∃ (b : S.J → PadicAlgCl p) (σ : SecA u.A (PadicAlgCl p) S.N), (∀ j, ‖c * b j‖ ≤ 1) ∧ IsComb u.A s b σ ∧ u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ Φ := by
  intro h h₂ _ o Ω _ _ _ _ S ρ p _ y₀ u l hy x rig e th s hx hs ϖ Q v lam hϖ hv hNorm w₀ th' ϑ c hw hϑ hP hth hc Φ hΦ
  obtain ⟨hchar, hun, hadm, -⟩ := _root_.GlobalTheory.TestValuation.main o Ω S ρ p y₀ u l hy
  obtain ⟨hadd, -, hbij, -⟩ := (GlobalTheory.T.uniformisedModel_torsionPoints_group_pairing h o Ω S ρ p y₀ u).2 x hx
  obtain ⟨-, -, -, -, hpull, hact⟩ := hs
  obtain ⟨-, hQ, -, hle, -⟩ := hNorm
  have hN0 : 0 < S.N := lt_of_lt_of_le (by norm_num) S.N_ge
  have hn3 : 3 ≤ ρ.n := by
    have h2 := ρ.n_prime.two_le
    obtain ⟨d, hd⟩ := ρ.n_odd
    omega
  have hm3 : 3 ≤ ρ.n ^ ρ.k :=
    hn3.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  have hmu : IsUnit ((ρ.n ^ ρ.k : ℕ) : u.V) := by
    rw [Nat.cast_pow]; exact hun.pow _
  obtain ⟨n, a, z, t, r, H, hΦs⟩ := exists_span_translates_of_eq_sq h h₂ u.complete hϖ hQ hv u.semi u.U w₀ rig hw
    th th' ϑ hϑ hP c hth (ρ.n ^ ρ.k) ρ.n_odd.pow hmu hm3 S.N ρ.N_eq Φ hΦ
  have hx0 : x 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hxs : ∀ (k : ℕ) (b : S.Gam), x (k • b) = x b ^ k := by
    intro k b
    induction k with
    | zero => rw [zero_nsmul, hx0, pow_zero]
    | succ k ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hpt : ∀ i, ∃ g : S.Gam, x (S.r • g) = z i := by
    intro i
    obtain ⟨a₀, ha₀, -⟩ := hbij (z i) (by rw [_root_.mul_comm S.r, pow_mul, (H i).2.1, one_pow])
    obtain ⟨a₁, -, hu₁⟩ := hbij 1 (one_pow _)
    have h0 : S.N • a₀ = 0 :=
      (hu₁ _ (by show x _ = 1; rw [hxs, ha₀, (H i).2.1])).trans (hu₁ 0 hx0).symm
    obtain ⟨g, hg⟩ := exists_nsmul_of_nsmul_eq_zero S.r_pos hN0 a₀ h0
    exact ⟨g, by rw [← ha₀, ← hg]⟩
  choose g hg using hpt
  have ht : ∀ i, IsComb u.A s (fun j => c⁻¹ * y₀ (algebraMap o S.R (S.ρ (g i) j ρ.i₀))) (t i) := by
    intro i
    obtain ⟨θ, hθ, hθa⟩ := hact (g i)
    obtain ⟨σ, hσ, -⟩ := (GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N S.J s (fun _ => 0)).2.2.2.1 θ (s ρ.i₀)
    rw [hg] at hθ
    exact IsComb.of_eq_mul (hθa _ _ hσ) hc ((H i).2.2.2 _ σ θ hpull hθ hσ)
  obtain ⟨σ, hσ⟩ := (GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N (Fin n) t a).1
  refine ⟨_, σ, fun j => ?_,
    (GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N S.J s (fun _ => 0)).2.2.2.2 (Fin n) _ t a σ ht hσ, ?_⟩
  · rw [Finset.mul_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [← _root_.mul_assoc, mul_inv_cancel_left₀ hc, norm_mul]
    have h1 : ‖a i‖ ≤ 1 := by
      have := (hle (a i) 0).1 (by simpa using (H i).1)
      simpa using this
    exact mul_le_one₀ (hy _) (norm_nonneg _) h1
  · rw [hΦs]
    exact (_root_.GlobalTheory.TestFibre.isComb_iff_expandsF_sum (laws_all h h₂).1 u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hN0 w₀ hw.1
      (Fin n) t r a σ fun i => (H i).2.2.1).1 hσ

end GlobalTheory.TestFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsogenousRetractPolarisedFiniteExtStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isogenous_retract_polarised_finiteExt : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (B : Over (Sp L)) (_ : GrpObj B) (Q : Out.PolAV (Sp L)) (g m : ℕ) (i : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ B) (r : B ⟶ (Over.pullback (spMap (algebraMap K L))).obj A) (i' : B ⟶ Q.A) (r' : Q.A ⟶ B), GlobalTheory.AbLaw.IsProjBy ((Over.pullback (spMap (algebraMap K L))).obj A).hom ∧ SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K L))).obj A).hom ∧ SmoothOfRelativeDimension g B.hom ∧ IsMonHom i ∧ IsMonHom r ∧ 1 ≤ m ∧ r ≫ i = 𝟙 _ ^ m ∧ IsMonHom i' ∧ IsMonHom r' ∧ i' ≫ r' = 𝟙 B ∧ (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) := by
  first | exact @GlobalTheory.FiniteData.exists_isogenous_retract | exact GlobalTheory.FiniteData.exists_isogenous_retract | (intros; apply GlobalTheory.FiniteData.exists_isogenous_retract <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointUnitValuePrimitiveIntegralFamiStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionPoint_unit_value_primitive_integral_family : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ k n : ℕ, 4 ≤ k → n.Prime → IsUnit (n : V) → ∀ (t : SecA A F k) (s : Fam D.toPre F k) (α : D.toPre.X), U.ExpandsF F k w₀ t s → IntGe D v s 0 → (∀ q : ℚ, 0 < q → ¬ VGe D F v k α (s.s α) q) → ∃ (j : ℕ) (x : TFK (R := V) F ⟶ A.A), 2 ≤ j ∧ FromGt U.toUnifPre (n ^ j) x ∧ ∀ e (c : F), IsTorsFrame A ρ (n ^ j) x e → ValAt t x e c → v c = 0 := by
  first | exact @GlobalTheory.OneBasis.UnitValue.exists_unit_value | exact GlobalTheory.OneBasis.UnitValue.exists_unit_value | (intros; apply GlobalTheory.OneBasis.UnitValue.exists_unit_value <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasGeometricTestOfHasUniformisedTest
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.GeoExist

theorem link_smul {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ}
    [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (σ : S.J → (u.H S.N).Sec)
    (b : Matrix S.J S.J (FractionRing u.V)) (h : u.Link σ b) (c : FractionRing u.V) (hc : c ≠ 0) :
    u.Link σ (c • b) := by
  intro a v hv
  have hc' : algebraMap (FractionRing u.V) (PadicAlgCl p) c ≠ 0 := (map_ne_zero _).2 hc
  have h₁ := CrdCalc.crd_smul (Units.mk0 _ hc') (h a v hv)
  convert h₁ using 1
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, _root_.mul_assoc]

theorem hasGeo_of_hasU : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → ρ.HasU → ρ.HasGeo := by
  intro hL hT o Ω _ _ _ _ S ρ hB hU p _ y₀ hy Fs
  obtain ⟨u, l, τ, hm, hF⟩ := hU p y₀ hy Fs
  obtain ⟨σ, cls, f, hb⟩ := _root_.GlobalTheory.AdaptedBasis.main hL o Ω S ρ p y₀ u l S.N (le_trans one_le_two S.N_ge) S.J ρ.card
  obtain ⟨md⟩ := _root_.GlobalTheory.ZH.utest_nonempty_mod hL hT o Ω S ρ p y₀ u l σ cls f hb
  obtain ⟨b, hd, hl⟩ := _root_.GlobalTheory.ZH.LinkMatrix.exists_link hL o Ω S ρ p y₀ u l σ cls f hb
  obtain ⟨c, hc, hs⟩ := _root_.GlobalTheory.ZH.testLattice_eq_span_sections hL o Ω S ρ p y₀ u l τ σ cls md b hB hy hm hl hd
  have hl' := link_smul u σ b hl c hc
  exact ⟨⟨u, l, τ, hm, σ, cls, md, c • b, hl', hs,
    _root_.GlobalTheory.ZH.ClassWeight.row_weight hL hT o Ω S ρ p y₀ u l σ cls f hb (c • b) hl'⟩, hF⟩

end GlobalTheory.ZH.GeoExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralFamilyValuesTorsionTorusExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_family_values_torsion_torusExtension : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → ∀ (x : TFK (R := V) F ⟶ A.A) e (t : SecA A F k) (s : Fam D.toPre F k) (c : F), FromGt U.toUnifPre n x → IsTorsFrame A ρ n x e → U.ExpandsF F k w₀ t s → IntGe D v s 0 → ValAt t x e c → 0 ≤ v c := by
  first | exact @GlobalTheory.OneBasis.integral_value_at_torsion | exact GlobalTheory.OneBasis.integral_value_at_torsion | (intros; apply GlobalTheory.OneBasis.integral_value_at_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormThetaConstantLePrimitiveGeneratorScaleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_thetaConstant_le_primitiveGenerator_scale : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ → ValOver ϖ (PadicAlgCl p) v → NormIs u l ϖ Q v lam → ∀ (w₀ : W0 u.U.toUnifPre) (th' : SecA u.A (PadicAlgCl p) 1) (ϑ : Fam u.D.toPre (PadicAlgCl p) 1) (c : PadicAlgCl p), NormW u.U.toUnifPre w₀ rig → u.U.ExpandsF (PadicAlgCl p) 1 w₀ th' ϑ → Prim u.D Q v ϑ → (∀ j, th.f j = liftFun u.A.A _ (cF u.V c) * th'.f j) → ∀ a, ‖y₀ ⟨S.th a, S.th_mem a⟩‖ ≤ ‖c‖ := by
  first | exact @GlobalTheory.ThetaBound.norm_theta_le | exact GlobalTheory.ThetaBound.norm_theta_le | (intros; apply GlobalTheory.ThetaBound.norm_theta_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PrincipallyPolarizedAbelianVarietyPotentialSemiA
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SemiPol

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem exists_prime_unit (V : Type) [CommRing V] [IsLocalRing V] :
    ∃ l : ℕ, l.Prime ∧ 3 ≤ l ∧ IsUnit (l : V) := by
  have h : IsUnit ((2 : V) * ((3 : ℕ) : V) + -((5 : ℕ) : V)) := by
    have : (2 : V) * ((3 : ℕ) : V) + -((5 : ℕ) : V) = 1 := by push_cast; ring
    rw [this]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  · exact ⟨3, Nat.prime_three, le_rfl, isUnit_of_mul_isUnit_right h⟩
  · exact ⟨5, Nat.prime_five, by norm_num, by simpa using h⟩

theorem exists_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (P : Out.PolAV S) :
    ∃ (P' : Out.PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ := by
  obtain ⟨P', φ, hφ, -, mul, -⟩ :=
    polBaseChange_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally S S' f P
  refine ⟨P', φ, hφ, fun T x y x₀ y₀ hx hy => ?_⟩
  have e₁ : x₀ = Out.toBase hφ.w x := Over.OverMorphism.ext hx
  have e₂ : y₀ = Out.toBase hφ.w y := Over.OverMorphism.ext hy
  rw [e₁, e₂, ← mul]
  rfl

theorem fixed_of_rational {K K₁ Ω Ω₁ : Type} [Field K] [Field K₁] [Field Ω] [Field Ω₁] [Algebra K K₁] [Algebra K Ω]
    [Algebra K₁ Ω] [IsScalarTower K K₁ Ω] [Algebra K₁ Ω₁] (j : Ω ≃ₐ[K₁] Ω₁)
    {A : Over (Sp K)} [GrpObj A] {A₁ : Over (Sp K₁)} [GrpObj A₁] {φ : A₁.left ⟶ A.left}
    (h : IsGrpPullback A₁ A (spMap (algebraMap K K₁)) φ) (l : ℕ)
    (hr : ∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ A, x ^ l = 1 →
      ∃ y : Sp K₁ ⟶ A.left, spMap (algebraMap K₁ Ω) ≫ y = x.left)
    (τ : Ω₁ ≃ₐ[K₁] Ω₁) (x : Over.mk (spMap (algebraMap K₁ Ω₁)) ⟶ A₁) (hx : x ^ l = 1) :
    spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback h (spMap (algebraMap K₁ Ω₁))
    (spMap (algebraMap K₁ Ω₁) ≫ spMap (algebraMap K K₁)) rfl
  let u : Over.mk (spMap (algebraMap K Ω)) ⟶ Over.mk (spMap (algebraMap K₁ Ω₁) ≫ spMap (algebraMap K K₁)) :=
    Over.homMk (spMap j.symm.toRingEquiv.toRingHom) (by
      show spMap _ ≫ spMap _ ≫ spMap _ = spMap _
      rw [sp_comp, sp_comp]
      congr 1
      ext c
      simp [← IsScalarTower.algebraMap_apply])
  obtain ⟨y, hy⟩ := hr (u ≫ e x) (by rw [← MonObj.comp_pow, ← map_pow, hx, map_one, MonObj.comp_one])
  have hy' : spMap (algebraMap K₁ Ω) ≫ y = spMap j.symm.toRingEquiv.toRingHom ≫ x.left ≫ φ := by
    rw [hy, ← he]; rfl
  have h₁ : spMap (algebraMap K₁ Ω₁) ≫ y = x.left ≫ φ := by
    have e₁ : spMap j.toRingEquiv.toRingHom ≫ spMap (algebraMap K₁ Ω) = spMap (algebraMap K₁ Ω₁) := by
      rw [sp_comp]; congr 1; ext c; simp
    have e₂ : spMap j.toRingEquiv.toRingHom ≫ spMap j.symm.toRingEquiv.toRingHom = 𝟙 _ := by
      rw [sp_comp, ← Spec.map_id]; congr 1; ext c; simp
    refine (congrArg (· ≫ y) e₁.symm).trans ((Category.assoc _ _ _).trans ?_)
    rw [hy', ← Category.assoc, e₂]
    exact Category.id_comp _
  have hτ : spMap τ.toRingEquiv.toRingHom ≫ spMap (algebraMap K₁ Ω₁) = spMap (algebraMap K₁ Ω₁) := by
    rw [sp_comp]; congr 1; ext c; simp
  refine h.1.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) h₁.symm).trans ?_
    rw [← Category.assoc, hτ, h₁]
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (Over.w x)).trans ?_
    exact hτ.trans (Over.w x).symm

theorem exists_finset (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (l : ℕ) (hl : l.Prime) :
    ∃ s : Finset Ω, ∀ (K₁ : Type) [Field K₁] [Algebra K K₁] [Algebra K₁ Ω] [IsScalarTower K K₁ Ω],
      (∀ c ∈ s, c ∈ (algebraMap K₁ Ω).fieldRange) →
      ∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A, x ^ l = 1 →
        ∃ y : Sp K₁ ⟶ P.A.left, spMap (algebraMap K₁ Ω) ≫ y = x.left := by
  classical
  have hc := (_root_.GlobalTheory.torsion_points_galois_module K P Ω l hl).1 1
  rw [pow_one] at hc
  have hfin : Finite {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hl.ne_zero)
  have hsm := P.smoothDim
  have hsm' : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g _
  have hft : LocallyOfFiniteType P.A.hom := inferInstance
  have key : ∀ x : {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l = 1}, ∃ s : Finset Ω,
      ∀ (K₁ : Type) [Field K₁] [Algebra K K₁] [Algebra K₁ Ω] [IsScalarTower K K₁ Ω],
      (∀ c ∈ s, c ∈ (algebraMap K₁ Ω).fieldRange) →
        ∃ y : Sp K₁ ⟶ P.A.left, spMap (algebraMap K₁ Ω) ≫ y = x.1.left := by
    intro x
    obtain ⟨E, -, h₂, h₃⟩ := GlobalTheory.SS.exists_fieldOfValues P.A.left Ω x.1.left
    obtain ⟨L, hL, rfl⟩ := h₃ K P.A.hom hft (Over.w x.1) inferInstance
    obtain ⟨s, hs⟩ : (Subalgebra.toSubmodule L.toSubalgebra).FG :=
      (Submodule.fg_iff_finiteDimensional _).2 hL
    refine ⟨s, fun K₁ _ _ _ _ hK => (h₂ K₁ _).1 fun c hc => ?_⟩
    have : Subalgebra.toSubmodule L.toSubalgebra ≤
        Subalgebra.toSubmodule (IsScalarTower.toAlgHom K K₁ Ω).range := by
      rw [← hs, Submodule.span_le]
      exact fun d hd => hK d hd
    exact this hc
  choose s hs using key
  have := Fintype.ofFinite {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l = 1}
  exact ⟨Finset.univ.biUnion s, fun K₁ _ _ _ _ hK x hx => hs ⟨x, hx⟩ K₁ fun c hc =>
    hK c (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, hc⟩)⟩

theorem potModel_semiAbelian : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ P : Out.PolAV (Sp K), PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ hres P
  obtain ⟨l, hl, h3, hu⟩ := exists_prime_unit V
  let Ω := AlgebraicClosure K
  obtain ⟨s, hs⟩ := exists_finset K P Ω l hl
  have hV : CharZero V := (algebraMap V K).charZero
  have hinj : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  have hf : FaithfulSMul V Ω := (faithfulSMul_iff_algebraMap_injective V Ω).2 hinj
  have ha : Algebra.IsAlgebraic V Ω :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := K) (C := Ω)).2 inferInstance
  obtain ⟨W, hW, hWc, -, hWf, -, hWl, hWs, -⟩ := exists_complete_dvr_finite_subalgebra V Ω s
  let K₁ := FractionRing W
  have hinj₁ : Function.Injective ((algebraMap W K₁).comp (algebraMap V W)) :=
    (IsFractionRing.injective W K₁).comp fun a b h => hinj (congrArg Subtype.val h)
  let _ : Algebra K K₁ := (IsFractionRing.lift hinj₁ : K →+* K₁).toAlgebra
  let _ : Algebra K₁ Ω := (IsFractionRing.lift (g := algebraMap W Ω) Subtype.val_injective : K₁ →+* Ω).toAlgebra
  have c₁ : ∀ a, algebraMap K K₁ (algebraMap V K a) = algebraMap W K₁ (algebraMap V W a) := fun a =>
    IsFractionRing.lift_algebraMap hinj₁ a
  have c₂ : ∀ a : W, algebraMap K₁ Ω (algebraMap W K₁ a) = a := fun a =>
    IsFractionRing.lift_algebraMap (g := algebraMap W Ω) Subtype.val_injective a
  have hT : IsScalarTower K K₁ Ω := IsScalarTower.of_algebraMap_eq' (by
    refine IsLocalization.ringHom_ext (nonZeroDivisors V) (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply]
    rw [c₁, c₂, ← IsScalarTower.algebraMap_apply]
    rfl)
  have hK₁ : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap K K₁).injective
  have hal : Algebra.IsAlgebraic K₁ Ω := Algebra.IsAlgebraic.tower_top (K := K) K₁
  have hac : IsAlgClosure K₁ Ω := ⟨inferInstance, hal⟩
  have hres₁ : Finite (IsLocalRing.ResidueField W) :=
    Module.finite_of_finite (IsLocalRing.ResidueField V)
  obtain ⟨P₁, φ, hφ⟩ := exists_pullback (spMap (algebraMap K K₁)) P
  refine GlobalTheory.SS.potModel_trans V K W K₁ (RingHom.ext fun a => (c₁ a).symm) hWf hWl P.A P₁.A φ hφ _ ?_
  refine _root_.GlobalTheory.SS.potModel_of_rational_torsion W K₁ hres₁ l hl h3 (by simpa using hu.map (algebraMap V W)) P₁ ?_
  refine fixed_of_rational (IsAlgClosure.equiv K₁ Ω (AlgebraicClosure K₁)) hφ l (hs K₁ fun c hc => ?_)
  obtain ⟨a, ha, b, hb, hb0, h⟩ := hWs c hc
  refine ⟨algebraMap W K₁ ⟨a, ha⟩ / algebraMap W K₁ ⟨b, hb⟩, ?_⟩
  rw [map_div₀, c₂, c₂]
  exact (div_eq_iff hb0).2 h.symm

end GlobalTheory.SemiPol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsAtUniformisedTraitStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_constants_at_uniformised_trait : HV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)) (_ : SABMap t' t χ) (_ : PELUnif (maximalIdeal V) t') (σ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ))), NZ t.G t.PP.L χ σ → IsGenSec t.G t.PP.L ((1 : ℕ) : ℤ) σ ∧ ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → ∀ (x' : Sp F ⟶ S) (ξ : Over.mk x' ⟶ Over.mk χ), ξ.left = jFK (R := V) F ≫ jK V → (∀ x (c : F), ThG t.G t.PP.L t.PP.rig m (VVRank.pullS t.G _ ξ σ) x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG t.G t.PP.L t.PP.rig m (VVRank.pullS t.G _ ξ σ) x (fnOf c) ∧ v c = 0 := by
  first | exact @GlobalTheory.Ex.OneGen.theta_at_trait | exact GlobalTheory.Ex.OneGen.theta_at_trait | (intros; apply GlobalTheory.Ex.OneGen.theta_at_trait <;> assumption)
end

