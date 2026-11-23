module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstMemberEqProdLocalGridBases
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairSecondMemberEqProdLocalGridBases
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnitarySelfDualLatticeGridDoubling
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEqSmulArrowVacuaProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2873
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineReadingAdelicNormEqTorusMeanSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankFormMinimalTuplesAtClosedPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TanBasisPull
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BasisPull

theorem tanBasis_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (T : SAB H X) (t : SAB H X') (g : X' ⟶ X) (φ : SABMap t T g) (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ T.G.left)) (v' : Fin n → (Sp (DualNumber Γ(X', U'.1)) ⟶ t.G.left)), (∀ i, IsTanAtG T (chart U) (v i)) → (∀ w, IsTanAtG T (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG T (chart U) v cf w) → (∀ i, IsTanAtG t (chart U') (v' i)) → (∀ i, v' i ≫ φ.φ = spMap (dualMap (g.appLE U.1 U'.1 hU).hom) ≫ v i) → ∀ w, IsTanAtG t (chart U') w → ∃! cf : Fin n → Γ(X', U'.1), IsCombAtG t (chart U') v' cf w := by
  intro E _ _ _ H X X' T t g φ U U' hU n v v' hv hvb hv' hvv' w hw
  have hx : chart U' ≫ g = spMap (g.appLE U.1 U'.1 hU).hom ≫ chart U :=
    (IsAffineOpen.SpecMap_appLE_fromSpec g U.2 U'.2 hU).symm
  obtain ⟨v'', hv''φ, hv''t, hv''b⟩ :=
    GlobalTheory.SabTan.tanBasis_sabMap E H X X' T t g φ _ _ (g.appLE U.1 U'.1 hU).hom (chart U) (chart U')
      hx n v hv hvb
  have heq : v'' = v' := by
    funext i
    apply φ.cart.1.hom_ext
    · rw [hv''φ, hvv']
    · rw [(hv''t i).1, (hv' i).1]
  rw [← heq]
  exact hv''b w hw

end GlobalTheory.BasisPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisActionMatricesRingHom
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BalProj

theorem actMat_ringHom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X : Scheme.{0}} (t : SAB H X) (S : Type) [CommRing S] (x0 : Spec (CommRingCat.of S) ⟶ X) (n : ℕ) (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) S), (∀ i, IsTanAtG t x0 (v i)) → (∀ w, IsTanAtG t x0 w → ∃! cf : Fin n → S, IsCombAtG t x0 v cf w) → (∀ a i, IsCombAtG t x0 v (A a i) (v i ≫ (t.act.act a).left)) → A 1 = 1 ∧ (∀ a b, A (a + b) = A a + A b) ∧ (∀ a b, A (a * b) = A a * A b) := by
  intro E _ _ _ H X t S _ x0 n v A hv hb hA
  classical
  let T : Fin n → TanM x0 t.G := fun i => GlobalTheory.LieMet.tanOf (hv i)
  have uniq : ∀ c c' : Fin n → S, ∑ j, c j • T j = ∑ j, c' j • T j → c = c' := by
    intro c c' h
    obtain ⟨cf, _, hcf⟩ := hb _ (GlobalTheory.LieMet.isTan_tv (∑ j, c j • T j))
    have h1 : IsCombAtG t x0 v c (tv (∑ j, c j • T j)).left := (GlobalTheory.LieMet.isComb_iff T c _).2 rfl
    have h2 : IsCombAtG t x0 v c' (tv (∑ j, c j • T j)).left := (GlobalTheory.LieMet.isComb_iff T c' _).2 h
    exact (hcf _ h1).trans (hcf _ h2).symm
  have hact : ∀ a i, ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (T i) = ∑ j, A a i j • T j := fun a i =>
    (GlobalTheory.LieMet.isComb_iff T (A a i) (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (T i))).1 (hA a i)
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have e : ∑ k, A 1 i k • T k = ∑ k, (1 : Matrix (Fin n) (Fin n) S) i k • T k := by
      rw [← hact, map_one, Module.End.one_apply]
      simp [Matrix.one_apply]
    exact congrFun (uniq _ _ e) j
  · intro a b
    ext i j
    have e : ∑ k, A (a + b) i k • T k = ∑ k, (A a + A b) i k • T k := by
      rw [← hact, map_add (f := _), LinearMap.add_apply, hact, hact]
      simp [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
    exact congrFun (uniq _ _ e) j
  · intro a b
    ext i j
    have e : ∑ k, A (a * b) i k • T k = ∑ k, (A a * A b) i k • T k := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hact, mul_comm a b, map_mul, Module.End.mul_apply, hact, map_sum]
      simp only [map_smul, hact, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      exact Finset.sum_comm
    exact congrFun (uniq _ _ e) j

end GlobalTheory.BalProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisUniformisedGroupOfRaynaudExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TanRayBasis

theorem vBasis_of_isPointOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∃ b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G), ⇑b = v' := by
  intro E _ _ _ H R _ _ _ _ _ _ t P
  letI := H.starRing
  intro Y n vH v' hv
  obtain ⟨b, hb⟩ := GlobalTheory.TanRay.tanBasis_of_isPointOf E H R t P Y n vH v' hv
  exact ⟨b, funext hb⟩

end GlobalTheory.TanRayBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyGenericFibreHenselLineSubsing
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.LocAcycDegOne

open scoped TensorProduct

theorem unitsL : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → (∀ a : A, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] A), a ∈ φ.range) → ∀ u : (TensorProduct T (FractionRing T) A)ˣ, ∃ v : (TensorProduct T (FractionRing T) A)ˣ, v ^ q = u := by
  intro q _ T _ _ _ hT hq A _ _ _ _ hSH hA
  obtain ⟨O, _, _, _, _, _, _, π, hπ, hO⟩ := GlobalTheory.T.surj_of_strictHenselisation_polynomial_alt T A hSH hA
  exact GlobalTheory.T.henselian_directed_union_subalgebras q T hT hq O hO A π hπ

theorem picL : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → (∀ a : A, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] A), a ∈ φ.range) → ∀ c : CommRing.Pic (TensorProduct T (FractionRing T) A), c ^ q = 1 → c = 1 := by
  intro q _ T _ _ _ hT hq A _ _ _ _ hSH hA
  obtain ⟨O, _, _, _, _, _, _, π, hπ, hO⟩ := GlobalTheory.T.surj_of_strictHenselisation_polynomial_alt T A hSH hA
  exact GlobalTheory.T.pic_generic_fibre_quotient_strictHenselisation_no_torsion_alt q T hT hq O hO A π hπ

theorem exists_cyclotomic_root (q : ℕ) [NeZero q] (T B : Type) [CommRing T] [Nontrivial T] [CommRing B] [Algebra T B] (hT : AIC T) :
    ∃ ζ : B, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  have hcyc : (Polynomial.cyclotomic q T).Monic := Polynomial.cyclotomic.monic q T
  have hdeg : 0 < (Polynomial.cyclotomic q T).natDegree := by
    rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
  obtain ⟨ζ, hζ⟩ := hT _ hcyc hdeg
  refine ⟨algebraMap T B ζ, ?_⟩
  have h0 := congrArg (algebraMap T B) hζ
  rw [← Polynomial.map_cyclotomic_int, Polynomial.eval_map, Polynomial.hom_eval₂, map_zero] at h0
  rw [Polynomial.aeval_def, algebraMap_int_eq]
  rwa [show (algebraMap T B).comp (Int.castRingHom T) = Int.castRingHom B from RingHom.ext_int _ _] at h0

theorem tateTwistCohomology_genericFibre_henselLine_subsingleton : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → (∀ a : A, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] A), a ∈ φ.range) → ∀ i : ℤ, Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) A)) 1 i) := by
  intro q _ T _ _ _ hT hq A _ _ _ _ hSH hA i
  have hqB : IsUnit (q : TensorProduct T (FractionRing T) A) := by
    simpa using hq.map (algebraMap T (TensorProduct T (FractionRing T) A))
  have hz := exists_cyclotomic_root q T (TensorProduct T (FractionRing T) A) hT
  obtain ⟨e⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q (TensorProduct T (FractionRing T) A) hqB hz 1 i 1
  have h1 : Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) A)) 1 1) :=
    GlobalTheory.T.kummer_etale_vanishing q _ hqB (fun u => (unitsL q T hT hq A hSH hA u).imp fun _ h => h.symm) (picL q T hT hq A hSH hA)
  refine ⟨fun x y => e.injective ?_⟩
  exact Subsingleton.elim _ _

end GlobalTheory.LocAcycDegOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaAtMove
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.TopFlip

variable {D : D7}

theorem om_fockF {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {ε : Bool} {M X : HSp D} (A : Fr M) (B : Fr X)
    {χ χ' : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep M X} (hω : GlobalTheory.Grid.IsWeil ψ ε M X χ χ' ω) {h : GA D X} (hh : h ∈ GfC X)
    {f : WO M X → ℂ} (hf : IsFinF ψ θ ε A B f) (c : ℂ) (P) :
    fockF ψ θ ε A B (c • ω (1, h) f) P = c • ω (1, h) (fockF ψ θ ε A B f P) := by
  have e : ω.toSgn ε (1, h) = ω (1, h) := by simp [GlobalTheory.Grid.WRep.toSgn]
  have h1 := GlobalTheory.FiniteFock.compAt_mt_of_finite θ (S := GlobalTheory.Grid.sgn ε M) (hk := one_mem _)
  have h2 := GlobalTheory.FiniteFock.compAt_mt_of_finite θ (hk := hh)
  have := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ _ X χ χ' _ hω hθ (frSgn ε A).cart _ A.onb _ B.cart _ B.onb _ 1 h
    (fun τ => by rw [h1, Matrix.mul_one, Matrix.one_mul]) (fun τ => by rw [h2, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [h1, Matrix.one_mul]) (fun τ => by rw [h2, Matrix.one_mul]) f hf.1 P).2
  rw [e] at this
  exact (GlobalTheory.FiniteFock.pureTensorO_smul _ _ _ _ _ _ _ _ _ _ _).trans (congrArg (c • ·) this.symm)

theorem om_compare {ψ : AddChar (AF D.host.F) ℂ} {S X : HSp D} {χ χ' χ₁ χ₁' : (AE D)ˣ →* Circle} {ω ω₁}
    (hω : IsWeilDatumO ψ S X χ χ' ω) (hω₁ : IsWeilDatumO ψ S X χ₁ χ₁' ω₁) {h : GA D X} {y : (AE D)ˣ} (hy : IsDetRoot X h y)
    {f} (hf : IsThetaFunO ψ S X f) : ω₁ (1, h) f = ((χ₁ y : ℂ) * (χ y : ℂ)⁻¹) • ω (1, h) f := by
  rw [GlobalTheory.WeilChange.weilData_differ_by_splitFac D ψ S X χ χ' χ₁ χ₁' ω ω₁ hω hω₁ 1 h 1 y (by simp [IsDetRoot]) hy f hf]
  simp [splitFacO]

theorem thetaAt_move {ψ : AddChar (AF D.host.F) ℂ} {S X : HSp D} {χ χ' : (AE D)ˣ →* Circle} {ω}
    (hω : IsWeilDatumO ψ S X χ χ' ω) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)} (hS : Submodule.IsFullLattice D.host.E ΛS) (hX : Submodule.IsFullLattice D.host.E ΛX)
    {a : AE D} (ha : a * a = a) (hc : a * cA D a = 0) (hinf : infPart D a = 0) {b b' Φ f : WO S X → ℂ} (hb : IsThetaFunO ψ S X b)
    {h : GA D X} (hfx : ∀ x : WO S X, IsHalf a x ∨ IsHalf (cA D a) x → actO S X 1 h x = x) {c : ℂ} (hc0 : c ≠ 0)
    (e : ω (1, h) b = c • b')
    (hf : IsThetaAt ψ (symplO S X) (heisO ψ S X) a (latO S X ΛS ΛX fun _ => True) 1 b Φ f) :
    IsThetaAt ψ (symplO S X) (heisO ψ S X) a (latO S X ΛS ΛX fun _ => True) 1 b' Φ (c⁻¹ • ω (1, h) f) := by
  letI := hS
  letI := hX
  have := GlobalTheory.ThetaBaseMove.isThetaAt_move hω
    (fun f₀ h₀ Tm hTm Ψ hΨ => GlobalTheory.DiagLiftFix.isTheta_placeModel hω.std inferInstance inferInstance ha hc hinf h₀ Tm hTm Ψ hΨ) hb 1 h
    (inv_ne_zero hc0) hfx hf
  rwa [e, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}


set_option maxHeartbeats 1000000 in
theorem exists_move (hL : L.Is μ₀) (hst : ∀ t, SquareStanding G t) {W : G.Weil} (B : Frames G) (ρ : RealMatch W) {i j : Fin D.R.m}
    {X : TriG G i j} (hX : TopGrid W i j X) {νH}
    (hI : X.Is W.ψ W.θ (fun t => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (fun _ => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) νH (locPl G))
    {AV : Fr (spV G i j)} {AV₁ : Fr (spV₁ G i j)} (hV : IsGridFr W _ AV) (hV₁ : IsGridFr W _ AV₁) :
    ∃ h ∈ GfC (spX G i j), ∃ (cA cB : ℂ) (y : (AE D)ˣ), cA ≠ 0 ∧ cB ≠ 0 ∧ ∀ t,
      IsLinA B t i j ρ (X.e t) (locFst B t X) (cA⁻¹ • X.ω t (1, h) (X.f t)) ∧
      IsLinB B t i j ρ (X.e t) (locSnd B t X) ((cB * (L.xi t y : ℂ))⁻¹ • X.ω' t (1, h) (X.f' t)) := by
  obtain ⟨h, hh, Λ, hΛ, hfx, hmv, tA, tB⟩ := _root_.GlobalTheory.TopFlip.exists_twistElt (G := G) hL i j
  obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hX
  have x7 := x6 AV AV₁ hV hV₁
  have sW := (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).sd
  have sW₁ := (node_isV G hL (X := .grid i j) ⟨i.2.le, j.2.le⟩).sd
  have sX : IsSelfDualC (spX G i j) (latX G i j) := by have := hI.rigW.1; rwa [x3] at this
  have vA := hI.isVac
  have vB := hI.isVac'
  rw [x1, x3, x4, x7] at vA
  rw [x2, x3, x5, x7] at vB
  have eA : ∀ t, (X.ω t).toSgn true (1, h) = X.ω t (1, h) := fun t => by simp [GlobalTheory.Grid.WRep.toSgn]
  have h2 := GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ (hk := hh)
  have mA := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ (hI.weil μ₀) W.θ_is _ _ _ _ _ _ _ _ 1 h
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [h2, Matrix.mul_one, Matrix.one_mul]) (hmv _ _ (isSelfDualC_neg sW)) _ vA
  have mB := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ _ (hI.weil' μ₀) W.θ_is _ _ _ _ _ _ _ _ 1 h
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite W.θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [h2, Matrix.mul_one, Matrix.one_mul]) (hmv _ _ sW₁) _ vB
  obtain ⟨cA', hcA, kA⟩ := _root_.GlobalTheory.TopFlip.VacRouteBig.vac_eq_smul_vacA hL W ρ i j AV AV₁ hV hV₁ Λ hΛ tA _ mA
  obtain ⟨cB, hcB, kB⟩ := _root_.GlobalTheory.TopFlipVacB.vac_eq_smul_vacB hL W ρ i j AV AV₁ hV hV₁ Λ hΛ tB _ mB
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D _ h
  refine ⟨h, hh, cA', cB * (L.xi μ₀ y : ℂ)⁻¹, y, hcA, mul_ne_zero hcB (inv_ne_zero (Circle.coe_ne_zero _)), fun t => ⟨?_, ?_⟩⟩
  · have he := hI.idem t
    have f1 := hI.fst t
    rw [x1, x3, _root_.GlobalTheory.TopFlip.stdFst_eq_prodA hL B t i j X _ he] at f1
    have k : (X.ω t).toSgn true (1, h) X.vac = cA' • vacA ρ i j := by
      rw [om_compare (hI.weil μ₀) (hI.weil t) hy vA.2.theta, mul_inv_cancel₀ (Circle.coe_ne_zero _), one_smul, kA]
    have := thetaAt_move (ΛS := G.Λ (.grid (i + 1) (j + 1))) (ΛX := latX G i j)
      (hI.weil t) (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sW)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sX) (GlobalTheory.PlaceVec.idemSum_mul_self he) he.2 (GlobalTheory.PlaceVec.idemSum_infPart he)
      vA.2.theta (hfx t (hst t) _ he _) hcA k f1
    rwa [eA] at this
  · have he := hI.idem t
    have f1 := hI.snd t
    rw [x2, x3, _root_.GlobalTheory.TopFlip.StdSnd.stdSnd_eq_prodB hL B t i j X _ he] at f1
    have k : X.ω' t (1, h) X.vac' = (cB * (L.xi μ₀ y : ℂ)⁻¹ * (L.xi t y : ℂ)) • vacB ρ i j := by
      refine (om_compare (hI.weil' μ₀) (hI.weil' t) hy vB.2.theta).trans ?_
      rw [kB, smul_smul]
      congr 1
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha, LevCh.mu, Lift.tup, MonoidHom.mul_apply, Circle.coe_mul]
      field_simp
    exact thetaAt_move (S := spW₁ G i j) (ΛS := G.Λ (.grid i j)) (ΛX := latX G i j)
      (hI.weil' t) (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sW₁)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sX) (by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he])
      (by rw [← map_mul, he.2, map_zero]) (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he))
      vB.2.theta (fun x hx => hfx t (hst t) _ he _ x (by rwa [GlobalTheory.LatVac.cA_cA, or_comm] at hx))
      (mul_ne_zero (mul_ne_zero hcB (inv_ne_zero (Circle.coe_ne_zero _))) (Circle.coe_ne_zero _)) k f1

end GlobalTheory.TopFlip

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingNormSqEqVacuumStatement
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCosetIndicatorReading_normSq_eq_absNorm_inv_mul_vacuum : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) (o : ℕ), GoodMod D 𝔪 Sf →
  ∀ LB : Lat X.B, IsSelfDualC X.B LB →
    (∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True) →
  ∀ f₀ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ → IsSphOff X.ψ X.A X.B (stdLat X.A) LB ∅ f₀ →
    Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ →
  ∀ (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), IsCovolOne (ratL X.B X.A) ν 𝓕 →
    ip X.A X.B ν 𝓕 φ φ = ((Ideal.absNorm 𝔪 : ℂ) ^ (P.a * P.d))⁻¹ * ip X.A X.B ν 𝓕 f₀ f₀ := by
  first | exact @GlobalTheory.NormRatio.CosetNorm.ip_cosetVec | exact GlobalTheory.NormRatio.CosetNorm.ip_cosetVec | (intros; apply GlobalTheory.NormRatio.CosetNorm.ip_cosetVec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineReadingAdelicNormEqTorusMeanSquareStatement
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLineReading_adelicNorm_eq_torusMeanSquare : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (δ : ℂ) (r : D.host.E), Setup ψ θ S T ⊤ δ r →
  ∀ LT : Lat T, IsSelfDualC T LT →
    (∀ z : Matrix (Fin d) (Fin a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) ↔
      finPt hS hT r z ∈ latO S T (stdLat S) LT fun _ => True) →
  ∀ e0 ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D ⊤ δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d), ∀ f₀,
    Reads ψ θ hS hT ⊤ δ r e0 f₀ → IsSphOff ψ S T (stdLat S) LT ∅ f₀ →
  ∀ (ν : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) ν 𝓕 →
    ip S T ν 𝓕 f₀ f₀ = (Formalism.MainNotions.TaylorLogMetric.normSq D (Formalism.MainNotions.TaylorLogMetric.tor0 D ⊤ δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D ⊤ δ) a d) e0 : ℝ) := by
  first | exact @GlobalTheory.VacNormMean.ip_eq_normSq | exact GlobalTheory.VacNormMean.ip_eq_normSq | (intros; apply GlobalTheory.VacNormMean.ip_eq_normSq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelLocalLatticeFourierPartsOrders
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem local_lattice_orders : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), S.Big → SharpOver F W ρ.P u → (∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X) → ∀ (_ : NeZero S.N) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, ∃ (r : ℕ) (b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ)) (μ : (Fin 8 → Fin r → ZMod S.N) → (Fin 8 → Fin r → ℤ)) (e : (Fin 8 → Fin r → ZMod S.N) → Ω), r ≤ g ∧ (∀ x y, b₀ x y = b₀ y x) ∧ (∀ x, x ≠ 0 → 0 < b₀ x x) ∧ (∀ c u i, ((μ c u i : ℤ) : ZMod S.N) = c u i) ∧ (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod S.N) = c u i) → qW W b₀ (μ c) ≤ qW W b₀ α) ∧ (∀ c, e c ≠ 0 ∧ ∃ (T₀ : AddSubgroup S.Gam) (c' : T₀ →+ ZMod S.N) (κ : S.J × (T₀ → ZMod ((S.r * S.N) ^ 2))) (x₀ : S.Gam), S.IsoFree T₀ ∧ e c = S.FF T₀ c' κ / S.th x₀) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ π : (Fin r → ℤ) →+ T.D.toPre.X, Function.Surjective π ∧ (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod S.N) = c u i) → qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c) ≤ qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) α) ∧ ∀ c, 0 ≤ qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c) ∧ OrdEq M T ξ (e c ^ S.N) (qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c)).toNat := by
  intro g n hg hn hodd F W hW o' Ω _ _ _ _ S ρ u hS hsh hgen hN M U₀ EE FinalForm hadm hEE x
  have hc : CompactSpace M.Z := by
    have := M.qc
    exact QuasiCompact.compactSpace_of_compactSpace M.s
  obtain ⟨y, hy, hyc⟩ := (isClosed_closure (s := ({x} : Set M.Z))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  have hxy : x ⤳ y := specializes_iff_mem_closure.2 hy
  obtain ⟨r, b₀, μ, e, h1, h2, h3, h4, h5, h6, h7⟩ :=
    _root_.GlobalTheory.Poinc.Clocx.exists_at_closedPoint g n hg hn hodd F W hW o' Ω S ρ u hS hsh hgen hN M U₀ EE FinalForm hadm hEE y hyc
  exact ⟨r, b₀, μ, e, h1, h2, h3, h4, h5, h6, fun T ξ hT hξ => h7 T ξ hT (hξ.trans hxy)⟩

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaShiftFunctionalEqSubConstFnSmul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HeatMod

section Values

variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}

def germConstHom (q : Z ⟶ Sp R) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_id_scal_eq_germConstHom (q : Z ⟶ Sp R) (z : Z) (a : R) :
    gs (𝟙 Z) z ⊤ (scal q a) = germConstHom q z a := by
  rw [gs_eq (𝟙 Z) z ⊤ trivial]; rfl

theorem gs_constFn_eq_germConstHom (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (a : R) :
    gs r z ⊤ (constFn p ⊤ a) = germConstHom (r ≫ p) z a := by
  have : constFn p ⊤ a = (p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) := by
    unfold constFn
    rw [← Scheme.Hom.appLE_eq_app]; rfl
  exact (congrArg (gs r z ⊤) this).trans ((gs_eq r z ⊤ trivial _).trans rfl)

theorem sval_sub_constFn_smul {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ Sp R)
    (s s' : LB.Sec (LB.LinComb L φ ε)) (a : R) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (s' - constFn p ⊤ a • s) r z J = sval s' r z J - germConstHom (r ≫ p) z a * sval s r z J := by
  have hm := hJ.mem φ r
  have h₁ : sval (s' - constFn p ⊤ a • s) r z J + sval (constFn p ⊤ a • s) r z J = sval s' r z J :=
    (gs_add r z _ hm _ _).symm.trans (congrArg (gs r z _) (sub_add_cancel _ _))
  have h₂ : sval (constFn p ⊤ a • s) r z J = germConstHom (r ≫ p) z a * sval s r z J :=
    (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·)
      ((gs_res r z le_top hm _).trans (gs_constFn_eq_germConstHom p r z a)) rfl)
  rw [← h₁, h₂, add_sub_cancel_right]

end Values

theorem shiftEq_of_sub_constFn_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (mu α : Q.X) (σ σ' : Q.SecB k α) (σ₁ σ₁' : Q.SecB k (α + k • mu)) (c e e₁ : R), ShiftEq Q k mu α σ σ₁ 0 σ₁ → ShiftEq Q k mu α (σ' - constFn Q.P.A.hom ⊤ e • σ) (σ₁' - constFn Q.P.A.hom ⊤ e₁ • σ₁) c σ₁ → ShiftEq Q k mu α σ' σ₁' (c + e₁ - e) σ₁ := by
  intro R _ _ Q k mu α σ σ' σ₁ σ₁' c e e₁ h₀ h₁ u hu hc z J hJ
  have a₀ := h₀ u hu hc z J hJ
  have a₁ := h₁ u hu hc z J hJ
  rw [sval_sub_constFn_smul _ _ _ _ _ _ hJ, sval_sub_constFn_smul _ _ _ _ _ _ hJ, Over.w, Over.w,
    gs_id_scal_eq_germConstHom] at a₁
  rw [gs_id_scal_eq_germConstHom, map_zero, zero_mul, add_zero] at a₀
  rw [gs_id_scal_eq_germConstHom, map_sub, map_add (f := _)]
  linear_combination a₁ + germConstHom (DegPre.BF Q (FractionRing R)).hom z e * a₀

end GlobalTheory.HeatMod
end
end

