module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0200
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0249
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0167
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0070
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionPositive
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0154
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeVectorBundleOfSmooth
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteNormZeroOutsideDenom
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0126
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0151
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0061
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0233
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicEmbeddingDiscreteValuationRing

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeSpreadsOutFiniteTypeSubring
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem prop_snd_of_isPullback (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange]
    {X Y S' S : Scheme.{0}} {φ : X ⟶ Y} {a : X ⟶ S'} {b : Y ⟶ S} {f : S' ⟶ S}
    (h : IsPullback φ a b f) (ha : P a) : P (pullback.snd b f) := by
  have sq : IsPullback h.isoPullback.inv (pullback.snd b f) a (𝟙 S') :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  exact P.of_isPullback sq ha

theorem isCommMonObj_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    [IsCommMonObj G] {b : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G b φ) : IsCommMonObj G' := by
  have key : ∀ {T : Over S'} (x y : T ⟶ G'), x * y = y * x := by
    intro T x y
    let x₀ : Over.mk (T.hom ≫ b) ⟶ G := Over.homMk (x.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])
    let y₀ : Over.mk (T.hom ≫ b) ⟶ G := Over.homMk (y.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])
    have e₁ := h.2 T x y x₀ y₀ rfl rfl
    have e₂ := h.2 T y x y₀ x₀ rfl rfl
    have c : x₀ * y₀ = y₀ * x₀ := mul_comm _ _
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [← e₁, ← e₂, c]
    · rw [Over.w, Over.w]
  refine ⟨?_⟩
  rw [mul_eq_mul, comp_mul, key]
  simp

theorem abelianScheme_descends_to_fg_subring : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  intro R _ A _ F hA
  haveI : IsCommMonObj A := hA.comm
  haveI : IsProper A.hom := hA.proper
  obtain ⟨k, A₀, i₀, c₀, φ, hFk, hk, s₀, sep₀, qc₀, hφ⟩ :=
    GlobalTheory.smooth_grpScheme_descends_to_fg_subring R A F hA.smooth inferInstance inferInstance
  haveI : IsNoetherianRing k := Algebra.FiniteType.isNoetherianRing ℤ k
  have hφ' : IsGrpPullback A A₀ (spMap (algebraMap k R)) φ := hφ
  obtain ⟨R₁, hR₁, pr₁⟩ := GlobalTheory.T.separated_properness_fg_subalgebra k R A₀.left A₀.hom sep₀ inferInstance qc₀
    (prop_snd_of_isPullback @IsProper hφ.1 hA.proper)
  obtain ⟨i₁, φ₁, h₁₀, h₁, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Approx.model_passes_to_subalgebra k R A A₀ φ hφ' R₁
  haveI : Algebra.FiniteType k R₁ := (Subalgebra.fg_iff_finiteType R₁).1 hR₁
  haveI : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing k R₁
  haveI : IsCommMonObj (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R₁)))) :=
    isCommMonObj_of_isGrpPullback h₁₀
  have hk₁ : Algebra.FiniteType ℤ R₁ := Algebra.FiniteType.trans hk inferInstance
  have h₁' : IsGrpPullback A (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R₁))))
      (spMap (algebraMap R₁ R)) φ₁ := h₁
  have sm₁ : Smooth (pullback.snd A₀.hom (spMap (algebraMap k R₁))) :=
    by haveI := s₀; infer_instance
  obtain ⟨R₂, hR₂, gc₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_descends_to_fg R₁ R (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R₁))))
    sm₁ pr₁ (prop_snd_of_isPullback @GeometricallyConnected h₁.1 hA.geomConnected)
  obtain ⟨i₂, φ₂, h₂₁, h₂, -⟩ := @_root_.GlobalTheory.CompanionTheory.Ar.Approx.model_passes_to_subalgebra R₁ R _ _ _ A _
    (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R₁)))) i₁ φ₁ h₁' R₂
  haveI : Algebra.FiniteType R₁ R₂ := (Subalgebra.fg_iff_finiteType R₂).1 hR₂
  have hk₂ : Algebra.FiniteType ℤ R₂ := Algebra.FiniteType.trans hk₁ inferInstance
  refine ⟨R₂.toSubring, Over.mk (pullback.snd (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R₁)))).hom
    (spMap (algebraMap R₁ R₂))), i₂, φ₂, ?_, hk₂, ?_, h₂⟩
  · intro x hx
    have hx₁ : x ∈ R₁ := R₁.algebraMap_mem (⟨x, hFk hx⟩ : k)
    exact R₂.algebraMap_mem (⟨x, hx₁⟩ : R₁)
  · haveI := sm₁
    haveI := pr₁
    exact ⟨isCommMonObj_of_isGrpPullback h₂₁, by dsimp only [Over.mk_hom]; infer_instance,
      by dsimp only [Over.mk_hom]; infer_instance, gc₂⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeGlobalRelayStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_prime_global_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∃ (AA : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)) (AW : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (Fin (D.p + D.q) → F)), AA.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) ∧ AW.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC) ∧ AW.carrier.toAddSubgroup = ((chartD e b pq sc w P i).bc RC).M ∧ (∀ h ∈ AA.carrier, (fun x => h ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.toNAdd sc) ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.fromNAdd pq) x))) ∈ AA.carrier) ∧ GlobalTheory.CompanionTheory.Ar.GR.FStable F AW.carrier := by
  first | exact @GlobalTheory.CompanionTheory.Relay.arith_variety_prime_global_relay | exact GlobalTheory.CompanionTheory.Relay.arith_variety_prime_global_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.arith_variety_prime_global_relay <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionPositiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_intersection_positive : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (U : ((Σ k, J k) → ℂ) → ℝ), Or.𝔐.IsCuspWeight Or.sm U → ChartPsh Dc (phMu Hd) ∧ ChartCont Dc (phMu Hd) ∧ ChartPsh Dc (corrW Hd U) ∧ ChartCont Dc (corrW Hd U) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cusp_intersection_positive | exact GlobalTheory.CompanionTheory.Relay.cusp_intersection_positive | (intros; apply GlobalTheory.CompanionTheory.Relay.cusp_intersection_positive <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFree
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich

theorem inFibre_unique : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) (p r : ℕ), p.Prime → r.Prime → InFibre ξ p q → InFibre ξ r q → r = p := by
  intro X Ω _ _ ξ q p r hp hr hpq hrq
  have key : ∀ n : ℕ, n.Prime → InFibre ξ n q →
      (n : X.presheaf.stalk q.1) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk q.1) := by
    intro n hn hf
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    apply hf
    have hn0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.2 hn.ne_zero
    have h1 : genMap ξ q (↑u⁻¹ : X.presheaf.stalk q.1) * (n : Ω) = 1 := by
      rw [← map_natCast (genMap ξ q) n, ← map_mul, ← hu, Units.inv_mul, map_one]
    exact ⟨hn0, ⟨(n : X.presheaf.stalk q.1), map_natCast _ n⟩,
      ⟨(↑u⁻¹ : X.presheaf.stalk q.1), eq_inv_of_mul_eq_one_left h1⟩⟩
  by_contra hne
  have hcop : Nat.Coprime p r := (Nat.coprime_primes hp hr).2 (Ne.symm hne)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have h1 : (1 : X.presheaf.stalk q.1) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk q.1) := by
    have : ((a * p + b * r : ℤ) : X.presheaf.stalk q.1) = 1 := by rw [hab]; simp
    rw [← this]
    push_cast
    exact add_mem (Ideal.mul_mem_left _ _ (key p hp hpq)) (Ideal.mul_mem_left _ _ (key r hr hrq))
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem div_mem_regAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) (p : ℕ), p.Prime → (∀ r : ℕ, r.Prime → InFibre ξ r q → r = p) → ∀ (a : ℤ) (b : ℕ), ¬ p ∣ b → (a : Ω) / (b : Ω) ∈ regAt ξ q := by
  intro X Ω _ _ ξ q p hp hover a b hb
  have hinv : ∀ b : ℕ, ¬ p ∣ b → ((b : Ω))⁻¹ ∈ regAt ξ q := by
    refine Nat.recOnMul (motive := fun b => ¬ p ∣ b → ((b : Ω))⁻¹ ∈ regAt ξ q) ?_ ?_ ?_ ?_
    · intro h
      exact absurd (dvd_zero p) h
    · intro _
      simp
    · intro r hr h
      have hne : r ≠ p := fun e => h (e ▸ dvd_rfl)
      have hnf : ¬ InFibre ξ r q := fun hf => hne (hover r hr hf)
      exact (not_not.1 hnf).2.2
    · intro m n hm hn h
      rw [Nat.cast_mul, mul_inv]
      exact mul_mem (hm fun h' => h (dvd_mul_of_dvd_left h' _)) (hn fun h' => h (dvd_mul_of_dvd_right h' _))
  rw [div_eq_mul_inv]
  exact mul_mem (intCast_mem _ a) (hinv b hb)

theorem isCp_dvd : ∀ (Ω : Type) [Field Ω] (A : Subring Ω) (p : ℕ) [Fact p.Prime] (κ : Ω), κ ∈ A → IsCp p κ → ∃ u ∈ A, (p : Ω) ^ 2 = κ * u := by
  intro Ω _ A p hp κ hκA hκ
  unfold IsCp at hκ
  split_ifs at hκ with h2
  · exact ⟨1, A.one_mem, by rw [hκ, h2]; norm_num⟩
  · obtain ⟨ζ, hζ, rfl⟩ := hκ
    have hζA : ζ ∈ A := by simpa using A.add_mem hκA A.one_mem
    have hsum : ∑ i ∈ Finset.range p, ζ ^ i = 0 := hζ.geom_sum_eq_zero hp.out.one_lt
    have hp' : (p : Ω) = ∑ i ∈ Finset.range p, (1 - ζ ^ i) := by
      rw [Finset.sum_sub_distrib, hsum]
      simp
    have hterm : ∀ i, (1 : Ω) - ζ ^ i = (1 - ζ) * ∑ j ∈ Finset.range i, ζ ^ j := fun i => by
      rw [mul_comm, geom_sum_mul_neg]
    have hv : (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j) ∈ A :=
      A.sum_mem fun i _ => A.sum_mem fun j _ => A.pow_mem hζA j
    have hpv : (p : Ω) = -(ζ - 1) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j := by
      rw [hp', Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hterm]
      ring
    refine ⟨-(p : Ω) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j,
      A.mul_mem (A.neg_mem (natCast_mem A p)) hv, ?_⟩
    calc (p : Ω) ^ 2 = p * p := sq _
      _ = p * (-(ζ - 1) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j) := by rw [← hpv]
      _ = _ := by ring

theorem smul_htDual_mem : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : ReciprocityTheory.ChartRestriction.G.Semi.LB G.left) (n : ℕ) (O : Type) [CommRing O] (ρ : O →+* Module.End Ω Li) (σ : O →+* Ω) (g : ℕ), IsCptGen ξ → SmoothOfRelativeDimension g G.hom → ∀ (q : Cpt ξ) (κ : Ω), (∀ w ∈ M.omLat q, κ • w ∈ M.htOm L n q) → ∀ e ∈ M.htDual L n ρ σ q, κ • e ∈ M.eigLat ρ σ q := by
  intro X Ω _ ξ G _ _ Li _ _ M L n O _ ρ σ g hgen hsm q κ hκ e he
  obtain ⟨hvb, -⟩ := GlobalTheory.CompanionTheory.Ar.lieLat_isVB X G g Ω ξ Li M hgen hsm
  have hbi := (Lat.isVBOn_dual_and_bidual X Ω ξ Li M.lat Set.univ _ hvb).2 q trivial
  rw [M.mem_htDual_iff L n ρ σ q e] at he
  refine ⟨(hbi (κ • e)).2 fun w hw => ?_, Submodule.smul_mem _ κ he.1⟩
  have := he.2 (κ • w) (hκ w hw)
  simpa [map_smul, smul_eq_mul, LinearMap.smul_apply] using this

end GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich

namespace GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich

theorem exists_zp (Ω : Type) [Field Ω] (p : ℕ) [hp : Fact p.Prime] :
    ∃ o : Subalgebra ℤ Ω, ∀ x : Ω, x ∈ o ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω) := by
  refine ⟨{ carrier := {x | ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)}
            mul_mem' := ?_, add_mem' := ?_, algebraMap_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h <;> contradiction
    · push_cast; rw [div_mul_div_comm]
  · rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    by_cases h0 : (b : Ω) = 0
    · exact ⟨a', b', hb', by simp [h0]⟩
    by_cases h0' : (b' : Ω) = 0
    · exact ⟨a, b, hb, by simp [h0']⟩
    refine ⟨a * b' + a' * b, b * b', fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h <;> contradiction
    · push_cast; rw [div_add_div _ _ h0 h0']; ring
  · intro n
    exact ⟨n, 1, hp.out.not_dvd_one, by simp⟩

theorem sandwich_of_htFree : FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q), HTFree 𝔐 p → ∃ κ : Ω, IsCp p κ ∧ Sandwich 𝔐 p κ := by
  intro hF E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ hpS hpq hfree
  obtain ⟨o, ho⟩ := exists_zp Ω p
  have ho' : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω) := by
    intro x
    rw [← ho x]
    exact ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  obtain ⟨hchar, -, -, -, -, -, hch⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.hcpt_generic_point E H D l Xo c O β Y S Ω K J y 𝔐 p hpS o ho'
  letI := hchar
  have hPT : PointHT := GlobalTheory.T.pointHT_of_fargues_hodge_tate hF
  obtain ⟨Dc, hfam, htest⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.hodgeTate_family_exists E H D l Xo c O β Y S Ω K J y 𝔐 p hpS hpq o ho'
  obtain ⟨hproj, -, κ, hκ, hκA⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.family_proj E H D l Xo c O β Y S Ω K J y 𝔐 p hpS hpq o ho' Dc hfam hfree
  refine ⟨κ, hκ, fun q hq => ?_⟩
  have hover : OverZp 𝔐 p q := fun r hr hrq => inFibre_unique _ Ω 𝔐.ξ q p r Fact.out hr hq hrq
  obtain ⟨c', hc'⟩ := 𝔐.tie.cover q
  let s : {s : ∀ k, J k // mseg y s ≠ 0} := ⟨c', hc'.1⟩
  have hin : InChart 𝔐.ξ (mseg y) s.1 q := hc'
  have hreg : ∀ x ∈ chartRing o (mseg y) s.1, x ∈ regAt 𝔐.ξ q := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hin.2 j
    | algebraMap r =>
      obtain ⟨a, b, hb, h⟩ := (ho r).1 r.2
      rw [show algebraMap o Ω r = (r : Ω) from rfl, h]
      exact div_mem_regAt _ Ω 𝔐.ξ q p Fact.out hover a b hb
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have hκq : κ ∈ regAt 𝔐.ξ q := hreg κ (hκA s)
  obtain ⟨hN, hIC, hFR, -⟩ := hch s.1 s.2
  let κA : chartRing o (mseg y) s.1 := ⟨κ, hκA s⟩
  obtain ⟨u, hu, hpu⟩ := isCp_dvd Ω (chartRing o (mseg y) s.1).toSubring p κ (hκA s) hκ
  have hdiv : κA * (p : chartRing o (mseg y) s.1) ^ (𝔐.R p - 2) ∣ (p : chartRing o (mseg y) s.1) ^ (𝔐.R p) := by
    refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, 𝔐.R p = k + 2 := ⟨𝔐.R p - 2, by have := 𝔐.R_ge p hpS; omega⟩
    rw [hk, Nat.add_sub_cancel]
    push_cast
    rw [pow_add, hpu]
    show _ = κ * _ * u
    ring
  have hinv : ∀ x : E, cmConj E (cmConj E x) = x := fun x => by simp [cmConj]
  obtain ⟨⟨-, hsm⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence.chartSequence (chartRing o (mseg y) s.1) Ω E (cmConj E) hinv p (𝔐.R p) (D.p + D.q)
    (Module.Dual Ω 𝔐.Li) (Dc s) κA (𝔐.R p - 2) hdiv (htest s κA hPT hκ) (hproj s).1
  have hκω : ∀ w ∈ 𝔐.M.omLat q, κ • w ∈ omP 𝔐 p q := by
    intro w hw
    rw [hfam.om_loc s q hin hover] at hw
    rw [hfam.om'_loc s q hin hq]
    induction hw using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ?_
      have := hsm x hx
      rwa [← algebraMap_smul Ω κA x] at this
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul r x _ hx =>
      have : κ • (r • x) = r • (κ • x) := by
        rw [Subring.smul_def, Subring.smul_def, smul_smul, smul_smul, mul_comm]
      rw [this]
      exact Submodule.smul_mem _ r hx
  refine ⟨hκq, 𝔐.M.htOm_le 𝔐.t.PP.L _ q, hκω, fun s' => ⟨𝔐.M.eigLat_le_htDual 𝔐.t.PP.L _ 𝔐.ρ (𝔐.emb s') q,
    fun e he => ?_⟩⟩
  have hirr : IrreducibleSpace 𝔐.X := by
    rw [irreducibleSpace_def]
    have hcl : closure ({genPt 𝔐.ξ} : Set 𝔐.X) = (⊤ : Set 𝔐.X) :=
      Set.eq_univ_of_forall fun x => specializes_iff_mem_closure.1 (𝔐.all x)
    rw [← hcl]
    exact isIrreducible_singleton.closure
  obtain ⟨d, hd⟩ := GlobalTheory.Models.InhabZOn.exists_dim_triple 𝔐.t
  exact smul_htDual_mem 𝔐.X Ω 𝔐.ξ 𝔐.t.G 𝔐.Li 𝔐.M 𝔐.t.PP.L (p ^ 𝔐.R p) (𝓞 E) 𝔐.ρ (𝔐.emb s') d
    𝔐.tie.gen hd q κ hκω e he

end GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfParts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.TopA

theorem exists_padic_emb (F : IntermediateField ℚ ℂ) [NumberField F] (p : Nat.Primes) :
    Nonempty (F →+* ℂ_[p]) :=
  ⟨(IsAlgClosed.lift (M := ℂ_[p]) (R := ℚ) (S := F)).toRingHom⟩

theorem eq_of_clopen_irred {X : Type*} [TopologicalSpace X] {U U' : Set X} (hU : IsClopen U)
    (hUi : IsIrreducible U) (hU' : IsClopen U') (hUi' : IsIrreducible U') {u : X} (hu : u ∈ U) (hu' : u ∈ U') :
    U = U' :=
  (hUi.isConnected.isPreconnected.subset_isClopen hU' ⟨u, hu, hu'⟩).antisymm
    (hUi'.isConnected.isPreconnected.subset_isClopen hU ⟨u, hu', hu⟩)

theorem finite_primes_dvd {n : ℕ} (hn : n ≠ 0) : {p : Nat.Primes | (p : ℕ) ∣ n}.Finite :=
  ((Set.finite_Iic n).preimage Subtype.val_injective.injOn).subset fun p hp =>
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hp

theorem model_hyp {K : Type} [Field K] (V : ValuationSubring K) [IsDiscreteValuationRing V] :
    Function.Injective V.subtype ∧ IsNoetherianRing V ∧
      ∀ x : K, ∃ a b : V, V.subtype b ≠ 0 ∧ x * V.subtype b = V.subtype a := by
  refine ⟨Subtype.val_injective, inferInstance, fun x => ?_⟩
  rcases V.mem_or_inv_mem x with h | h
  · exact ⟨⟨x, h⟩, 1, by simp, by simp⟩
  · by_cases hx : x = 0
    · exact ⟨0, 1, by simp, by simp [hx]⟩
    · exact ⟨1, ⟨x⁻¹, h⟩, by simpa using hx, by simp [hx]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_place {l : Level H} (c : Coeff l) [NumberField c.F] (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) :
    ∃ W : ValuationSubring ℂ, ((p : ℕ) : ℂ) ∈ W.nonunits ∧ IsDiscreteValuationRing (c.V W) ∧
      ∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ c.V W := by
  obtain ⟨W, hp, hW⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_valuationSubring_of_padicEmbedding c.F p κ
  obtain ⟨V, hV, hκ, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.ValRing.exists_dvr_of_padic_embedding c.F p κ
  have hmem : ∀ x : c.F, x ∈ c.V W ↔ ‖κ x‖ ≤ 1 := fun x => (hW x).symm
  have heq : c.V W = V := by ext x; rw [hmem, hκ]
  refine ⟨W, hp, ?_, fun x => (hmem x).symm⟩
  rw [heq]; exact hV

theorem exists_cpt {D : Datum H} {l : Level H} (Xo : Moduli D l) (c : Coeff l) {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β)
    (hβ : Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    {U : Set (Xo.XF c)} (hU : IsClopen U) (hUi : IsIrreducible U) : Nonempty (CptOver Y U) := by
  obtain ⟨u, hu⟩ := hUi.nonempty
  obtain ⟨U', Z, hu', hc, hi⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_cptOver_mem_isClopen_isIrreducible E H D l Xo c O β Y u hβ
  rw [eq_of_clopen_irred hU hUi hc hi hu hu']
  exact ⟨Z⟩

theorem local_gen (hA0 : FlatLineGenerator) (hA1 : FlatLineGeneratorComponent) (hC : FinConstAll) {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} (U : Set (Xo.XF c)) (τ : E →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (hpq : 1 ≤ D.p + D.q)
    (hτ : τ (H.rt : E) = H.rt0) (hty : IsTypeFn H D.p D.q ty) (hU : IsClopen U) (hUi : IsIrreducible U)
    (hP : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      (Set.range y ⊆ U ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P))
    (W : ValuationSubring ℂ) [IsDiscreteValuationRing (c.V W)] (Y : Model Xo c (c.V W).subtype)
    (hSF : Y.SplitFibres) (hN3 : Y.N3) (p : Nat.Primes) (κ : c.F →+* ℂ_[p])
    (hκ : ∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ c.V W) :
    ∃ φ : FrameFn Xo c, IsFlatGen U τ φ FU i ∧ (∀ s : c.F →+* ℂ, ∃ t, HasInfNorm U τ φ s t) ∧
      ∃ t, HasFinNorm U τ φ p κ t := by
  obtain ⟨Z⟩ := exists_cpt Xo c Y (model_hyp (c.V W)) hU hUi
  have hG : Z.IsGeom := _root_.GlobalTheory.CompanionTheory.Ar.Flat.isGeom_of_period E H D l Xo c _ _ Y U Z g ty FU i hty (fun y hy hr => (hP y hy).1 hr)
  obtain ⟨φ, hl, hf, -⟩ := hA0 E H D l Xo c _ _ Y U Z τ (model_hyp (c.V W)) hpq hτ hG
  obtain ⟨hinf, hfg⟩ := hA1 E H D l Xo c _ _ Y U Z τ φ (model_hyp (c.V W)) hpq hτ hG hl hf
  refine ⟨φ, hfg g ty FU i hty (fun P y hPer hu hy => (hP y hy).2 ⟨P, hPer, hu⟩), fun s => ?_, ?_⟩
  · obtain ⟨t, ht, -⟩ := hinf s
    exact ⟨t, ht⟩
  · refine hC E H D l Xo c _ _ Y U Z τ p κ φ hτ Subtype.val_injective (fun x => (hκ x).trans ?_) hSF hN3 hG hf hl
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩

theorem hasFinNorm_of_eq {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {U : Set (Xo.XF c)}
    {τ : E →+* ℂ} {φ φ' : FrameFn Xo c} (hl : IsLineFn U τ φ) {a : c.F} (ha : a ≠ 0)
    (he : ∀ (F : Type) [Field F] (β : c.F →+* F) y v w, IsFramed U τ β y v w → φ' F y v w = β a * φ F y v w)
    {p : Nat.Primes} {κ : c.F →+* ℂ_[p]} {t : ℝ} (ht : HasFinNorm U τ φ' p κ t) :
    HasFinNorm U τ φ p κ (t - Real.log ‖κ a‖) := by
  intro V K _ _ _ _ _ _ j β y v w T tK m m' hj hjβ hfr hv hw
  have h1 := ht V K j β y v w T tK m m' hj hjβ hfr hv hw
  have hja : j (β a) = κ a := by rw [← hjβ]; rfl
  have h2 : ‖κ a‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero κ).mpr ha)
  have h3 : ‖j (φ K y v w)‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero j).mpr (hl.ne K β y v w hfr))
  rw [he K β y v w hfr, map_mul, hja, norm_mul, Real.log_mul h2 h3] at h1
  linarith

end GlobalTheory.CompanionTheory.Ar.Flat.TopA

namespace GlobalTheory.CompanionTheory.Ar.Flat


open GlobalTheory.CompanionTheory.Ar.Flat.TopA in
theorem thmFlatA_of_parts : PartI → FlatLineGenerator → FlatLineGeneratorComponent → FinConst → ThmFlatA := by
  intro hI hA0 hA1 _ E _ _ _ H D Xo l c _ U τ g ty FU i hpq hτ hg hty hU hUi hP
  have hC : FinConstAll := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FinAll.finConstAll
  obtain ⟨-, hI'⟩ := hI
  obtain ⟨Ys, hYs, -⟩ := hI' E H D hpq Xo
  have key : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ φ : FrameFn (Xo l) c, IsFlatGen U τ φ FU i ∧
      (∀ s : c.F →+* ℂ, ∃ t, HasInfNorm U τ φ s t) ∧ ∃ t, HasFinNorm U τ φ p κ t := by
    intro p κ
    obtain ⟨W, hpW, hdvr, hκ⟩ := exists_place c p κ
    haveI := hdvr
    obtain ⟨-, hYi⟩ := hYs p W p.2 hpW
    obtain ⟨hSF, hN3, -⟩ := hYi ⟨l, c, hg p p.2⟩
    exact local_gen hA0 hA1 hC U τ FU i hpq hτ hty hU hUi hP W (Ys p W p.2 hpW ⟨l, c, hg p p.2⟩) hSF hN3 p κ hκ
  obtain ⟨κ₀⟩ := exists_padic_emb c.F ⟨2, Nat.prime_two⟩
  obtain ⟨φ, hφ, hinf, -⟩ := key _ κ₀
  have hfin : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t := by
    intro p κ
    obtain ⟨φ', hφ', -, t, ht⟩ := key p κ
    obtain ⟨a, ha, he⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.flatGen_unique E H D l (Xo l) c U τ φ' φ g ty FU i hty hφ' hφ
      (fun y hy hr => (hP y hy).1 hr)
    exact ⟨_, hasFinNorm_of_eq hφ.line ha he ht⟩
  let N : LogNorms c.F := ⟨fun s => (hinf s).choose, fun p κ => (hfin p κ).choose -
    D.q * (logIdeal (κ.comp (tauIn c τ)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((H.d : ℕ) : ℂ_[p])‖)⟩
  have hN : HasNorms U τ φ N := ⟨fun s => (hinf s).choose_spec, fun p κ => by
    simp only [N, sub_add_cancel]
    exact (hfin p κ).choose_spec⟩
  refine ⟨φ, N, hφ, hN, ?_⟩
  obtain ⟨n, hn, hn0⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.line_function_norm_zero_away E H D l (Xo l) c U τ φ hτ hU.isOpen hUi.nonempty hφ.line
  have hS := _root_.GlobalTheory.CompanionTheory.Ar.Fl.finite_logIdeal_ne_zero E (differentIdeal ℤ (𝓞 E)) differentIdeal_ne_bot
  refine (((finite_primes_dvd hn.ne').union (finite_primes_dvd H.d_prime.ne_zero)).union hS).subset ?_
  rintro p ⟨ι₀, hι⟩
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_not] at hcon
  obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
  obtain ⟨-, -, -, -, hd⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.ValRing.exists_dvr_of_padic_embedding c.F p ι₀
  have hd' : ‖((H.d : ℕ) : ℂ_[p])‖ = 1 := by simpa using hd H.d h2
  have h0 := hn0 p ι₀ _ h1 (hN.2 p ι₀)
  rw [h3 (ι₀.comp (tauIn c τ)), hd', Real.log_one] at h0
  simp only [sub_zero, mul_zero, add_zero] at h0
  exact hι h0

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

