module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2160
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2878
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2915
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigThetaKernelIntegrable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.SquareConv

theorem natCast_not_mem {Rg : Type*} [CommRing Rg] {P : Ideal Rg} (hP : P ≠ ⊤) {p n : ℕ} (hpn : Nat.Coprime p n)
    (hp : (p : Rg) ∈ P) : (n : Rg) ∉ P :=
  _root_.GlobalTheory.CoprimeNatNotMem.natCast_not_mem_of_coprime hP hpn hp

theorem standing {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {large₂ : SizeData₂ D}
    (hS : HidaSetting large₂ R F) (hx : 11 ≤ D.host.splitBound) {sc : Consts} (G : GridData R.toLevCh sc) (t : T) :
    SquareStanding G t := by
  classical
  obtain ⟨hq, hd, -⟩ := D.host.hyp
  have hcc : D.host.ccK = ⊤ := hS.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨P, -, -⟩, -⟩ := hS.size
  have lev : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_condN_of_splitK D.host hpp (P.level_split p hp)
  refine ⟨hx, fun w hw => ?_⟩
  have e1 : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) = ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) := by
    rw [hcc, Ideal.absNorm_top, mul_one]
  rw [e1]
  rcases Finset.mem_union.1 hw with hw | hw
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨p, hpv, hcop⟩ : ∃ p : ℕ, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∧ Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := by
      rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1
      · refine ⟨q0 D, G.pl.basePlace_over_qZero, ?_⟩
        have hs := (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
        have hM : Nat.Coprime (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) (q0 D) := by
          rw [Nat.Coprime, Nat.gcd_rec, hs, Nat.gcd_one_left]
        have hdv : D.host.QS * D.host.q * D.host.d ∣ Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D := by
          unfold LevelStarExponents.condE
          exact Dvd.dvd.mul_left dvd_rfl _
        exact (hM.coprime_dvd_left hdv).symm
      · rcases (S1_mem_OmF D).1 hv1 with h | h | h | h
        · exact ⟨_, h, lev _ (D.host.g_level 0) (D.host.g_prime 0)⟩
        · exact ⟨_, h, lev _ (D.host.g_level 1) (D.host.g_prime 1)⟩
        · exact ⟨_, h, lev _ D.host.pde_level.1 D.host.pde_prime⟩
        · exact ⟨_, h, lev _ D.host.pde_level.2 D.host.pde'_prime⟩
    have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal := by
      rw [← G.pl.under_w hv, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hpv
      exact hpv
    exact natCast_not_mem (G.pl.w v).isPrime.ne_top hcop hpw
  · intro hmem
    apply (hS.core.lev.Q_off t w hw).1
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem

theorem splitBound_ge {D : D7} {large₂ : SizeData₂ D} {ε : ℝ} (_he : large₂.sc.eps = ε) (_hx : (12 : ℝ) ^ (5 / ε) ≤ large₂.sc.x)
    {Γ : Type} {_ : Group Γ} {_ : Fintype Γ} {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} {_ : Field Ks} {_ : NumberField Ks} {_ : Algebra Ks D.what₂.LL} {R : RealDat D A Ks} {F : Face D A}
    (hS : HidaSetting large₂ R F := by assumption) : 11 ≤ D.host.splitBound :=
  hS.size.2.1.eleven_le

end GlobalTheory.SquareConv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CPtEqOfNormValLtOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UPoinc.cPt_eq_of_norm_val_lt_one : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ z₁ : M₁.Z, letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra; ∀ (𝔷 : Ideal (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂)), 𝔷.IsMaximal → ∀ z₂ : M₂.Z, q z₂ = z₁ → (∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ 𝔷 ↔ ((b : Ω₂) = 0 ∨ (b : Ω₂)⁻¹ ∉ M₂.O z₂)) → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M₂.Z), q (y (cPt p)) = z₁ → (∀ b ∈ 𝔷, ‖M₂.val (gPt p ≫ y) (b : Ω₂)‖ < 1) → y (cPt p) = z₂ := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q hN hF hg z₁
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
  intro 𝔷 h𝔷 z₂ hz₂ hmem p _ y hy hsmall
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Poinc.integralClosure_stalk_fibre o₁ Ω₁ o₂ Ω₂ M₁ M₂ q hN hF hg z₁
  have hO : ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, (b : Ω₂) ∈ M₂.O (y (cPt p)) :=
    fun b => (h1 b).1 b.2 _ hy
  let ι : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ →+* M₂.O (y (cPt p)) :=
    (RingHom.id Ω₂).restrict _ _ fun c hc => hO ⟨c, hc⟩
  have hle : 𝔷 ≤ (IsLocalRing.maximalIdeal (M₂.O (y (cPt p)))).comap ι := by
    intro b hb
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (RatModel.norm_val_lt_one_iff rfl (hO b)).1 (hsmall b hb)
  have heq := h𝔷.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top) hle
  have key : ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂,
      ((b : Ω₂) = 0 ∨ (b : Ω₂)⁻¹ ∉ M₂.O z₂) ↔ ((b : Ω₂) = 0 ∨ (b : Ω₂)⁻¹ ∉ M₂.O (y (cPt p))) := by
    intro b
    rw [← hmem b, heq, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, RatModel.isUnit_O_iff]
    show ¬ ((b : Ω₂) ≠ 0 ∧ (b : Ω₂)⁻¹ ∈ M₂.O (y (cPt p))) ↔ _
    tauto
  refine (h3 z₂ (y (cPt p)) hz₂ hy fun b => ?_).symm
  by_cases hb0 : (b : Ω₂) = 0
  · rw [hb0, inv_zero]
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  · have := key b
    simp only [hb0, false_or] at this
    exact not_iff_not.1 this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfClassEqZeroStatement
section
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechCocycle_isCoboundary_of_class_eq_zero : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) → (∀ i i', IsAffineOpen (W i ⊓ W i')) → ∀ (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c → GlobalTheory.CechCmp.cmp s W hW c = 0 → ∃ h : ∀ i : J, Γ(Z, W i), ∀ i i', c i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') := by
  first | exact @GlobalTheory.CechCmp.exists_coboundary_of_cmp_eq_zero | exact GlobalTheory.CechCmp.exists_coboundary_of_cmp_eq_zero | (intros; apply GlobalTheory.CechCmp.exists_coboundary_of_cmp_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfIsCoboundarySubcoverStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechCocycle_isCoboundary_of_isCoboundary_subcover : ∀ (Z : Scheme.{0}) (J : Type) (W : J → Z.Opens) (S : Set J), (∀ i, W i ≤ ⨆ a ∈ S, W a) → ∀ d : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W d → ∀ h₀ : ∀ i, Γ(Z, W i), (∀ a ∈ S, ∀ b ∈ S, d a b = resG Z inf_le_left (h₀ a) - resG Z inf_le_right (h₀ b)) → ∃ h : ∀ i, Γ(Z, W i), ∀ i i', d i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') := by
  first | exact @GlobalTheory.CechFin.isCob_of_isCob_subcover | exact GlobalTheory.CechFin.isCob_of_isCob_subcover | (intros; apply GlobalTheory.CechFin.isCob_of_isCob_subcover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFiniteGenerationOfAffineBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_finite_generation_of_affine_base_change : ∀ (G X : Scheme.{0}) (p : G ⟶ X) (U : X.affineOpens) (J : Type) (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1), CechFG (fun i => pullback.fst p U.2.fromSpec ⁻¹ᵁ W i) Γ(X, U.1) (fun i i' => (secMap (R := Γ(X, U.1)) (pullback.snd p U.2.fromSpec) _).hom) → CechFG W Γ(X, U.1) (fun i i' => (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) := by
  first | exact @GlobalTheory.CechTr.cechFG_of_baseChange_affine | exact GlobalTheory.CechTr.cechFG_of_baseChange_affine | (intros; apply GlobalTheory.CechTr.cechFG_of_baseChange_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1ClassEqOfCocycleAffineCoverStatement
section
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_h1_class_eq_of_cocycle_affine_cover : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) → (∀ i i', IsAffineOpen (W i ⊓ W i')) → (∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'')) → ∀ x : GlobalTheory.CechDR.HO1 s, ∃ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), GlobalTheory.CechCmp.IsCocycle W c ∧ GlobalTheory.CechCmp.cmp s W hW c = x := by
  first | exact @GlobalTheory.CechCmp.exists_isCocycle_cmp_eq | exact GlobalTheory.CechCmp.exists_isCocycle_cmp_eq | (intros; apply GlobalTheory.CechCmp.exists_isCocycle_cmp_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupFinrankLeMinSignatureUnitaryTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.UTrait

theorem finrank_le_min : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c),
    Module.finrank (𝓞 E) T.P.D.toPre.X ≤ min Dw.p Dw.q := by
  intro E _ _ _ H Dw l Xo c T
  obtain ⟨hdvr, -, hch⟩ := T.cdvr
  haveI := hdvr
  haveI := hch
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  let K := AlgebraicClosure (FractionRing T.V)
  let g : FractionRing T.V →+* K := algebraMap (FractionRing T.V) K
  let f : T.V →+* K := g.comp (algebraMap T.V (FractionRing T.V))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing T.V) K).injective.comp (IsFractionRing.injective T.V (FractionRing T.V))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := T.V) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Xo.X := spMap g ≫ T.y ≫ pullback.fst _ _
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective (x' ≫ Xo.s)
  have hβ : x' ≫ Xo.s = spMap β₀.hom := hβ₀.symm
  have hdet := (Xo.univ.geom K x' β₀.hom hβ).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hjK : spMap g ≫ jK T.V = spMap f := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Xo.univ.t.act x' τ N →
      Module.finrank (𝓞 E) T.P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₂.cart tK.act Xo.univ.t.act m₂.act (spMap g) τ N).2 hN
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₁.cart tK.act T.t.act m₁.act (spMap g) τ N).1 h₅
    rw [hjK] at h₆
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H T.V T.t T.P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

end GlobalTheory.UPoinc.UTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartsOfUpre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChartOf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem inv_apply_self {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (x : X) : inv f (f x) = x := by
  rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl

theorem chart_of_data {φ : InvFun (𝓞 E)} (Y : Model Xo c (RingHom.id c.F)) (BD' : EffCartierData Y.X) (d : ℕ)
    (x : gen Y) {k : Type} [Field k] {m e : ℕ} (ξ' : Sp (ChartRing k m e) ⟶ gen Y) (t : SAB H (Sp (ChartRing k m e)))
    (P : PELUnif (maximalIdeal (ChartRing k m e)) t) (n : ℕ) (h : n = m) (s : Fin n → ChartRing k m e)
    (hs : ∀ i, s i = bdParam k m e (Fin.cast h i)) (δ : Fin n → LinearMap.BilinForm ℤ P.D.toPre.X) (a : Fin n → ℕ)
    (hx : ξ' (closedPoint _) = x) (het : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ').hom)
    (hid : idlAlong (genBdIdeal Y) ξ' = Ideal.span {∏ i, s i})
    (hset : ∀ p : Sp (ChartRing k m e), ξ' p ∈ genBd Y ↔ ∏ i, s i ∈ p.asIdeal)
    (hsab : Nonempty (SABMap t Y.t (ξ' ≫ genι Y)))
    (hmono : IsMonomial P.D.toPre s (fun i => (l.M' : ℤ) • δ i))
    (hrank : Module.finrank (𝓞 E) P.D.toPre.X ≤ min Dw.p Dw.q) (hcone : IsCone H.bar φ δ)
    (ha : ∀ i, (a i : ℝ) = d * φ.evalZ ((l.M' : ℤ) • δ i))
    (hBD : idlAlong BD'.idealSheaf (ξ' ≫ genι Y) = Ideal.span {∏ i, s i ^ a i})
    (hrig : GlobalTheory.RigChart.IsRigid P.D.toPre s (fun i => (l.M' : ℤ) • δ i)) :
    GlobalTheory.MumfordChart.HasChartOf φ Y BD' d x ∧ GlobalTheory.RigChart.HasRigidChart Y x := by
  subst h
  obtain rfl : s = bdParam k n e := funext fun i => by simpa using hs i
  have hmem : ∀ i, (l.M' : ℤ) • δ i ∈ levelForms H l.M' P.D.toPre.X := fun i =>
    (mem_levelForms_iff_smul (GlobalTheory.MumfordChart.level_ne_zero l)).2
      ⟨δ i, (balForms_eq_levelForms H P.D.toPre.X) ▸ hcone.mem i, rfl⟩
  let gam : Fin n → levelForms H l.M' P.D.toPre.X := fun i => ⟨(l.M' : ℤ) • δ i, hmem i⟩
  have hgam : ∀ i, (gam i : LinearMap.BilinForm ℤ P.D.toPre.X) = (l.M' : ℤ) • δ i := fun _ => rfl
  have hpb : IsPartOfBasis gam := hcone.isPartOfBasis_level (GlobalTheory.MumfordChart.level_ne_zero l) hgam
  exact ⟨⟨k, _, n, e, ξ', t, P, gam, δ, a, hx, het, hid, fun p => (hset p).trans Iff.rfl, hsab, hmono, hrank, hcone, hgam,
      ha, hBD⟩,
    ⟨k, _, n, e, ξ', t, P, gam, hx, het, hid, hset, hsab, hmono, hpb, hrig⟩⟩

end GlobalTheory.UChartOf

namespace GlobalTheory.UChartOf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem charts_of_upre {φ : InvFun (𝓞 E)} {S : Scheme.{0}} {j : Xo.XF c ⟶ S} [IsOpenImmersion j]
    {BD : EffCartierData S} {d : ℕ} (Y : Model Xo c (RingHom.id c.F)) (ε : Y.X ≅ S) (hj : Y.j ≫ ε.hom = j)
    (hsab : ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C →
      ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → Nonempty (SABMap C.t Y.t (ξ ≫ ε.inv)))
    (hpre : ∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) (x : gen Y) (hx : x ∈ genBd Y) :
    GlobalTheory.MumfordChart.HasChartOf φ Y (BD.pull ε.hom (BD.keepsRegular_of_flat _)) d x ∧
      GlobalTheory.RigChart.HasRigidChart Y x := by
  let π : gen Y ⟶ S := genι Y ≫ ε.hom
  have hjQ : Y.jQ ≫ π = j := by
    simp only [π, ← Category.assoc]
    exact hj
  have hrange : ∀ w : gen Y, w ∈ Set.range Y.jQ ↔ π w ∈ Set.range j := by
    intro w
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [← hjQ]; rfl⟩
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have : π (Y.jQ z) = π w := by rw [← hz, ← hjQ]; rfl
      rw [← inv_apply_self π (Y.jQ z), this, inv_apply_self]
  have hx' : π x ∉ Set.range j := fun h => hx ((hrange x).2 h)
  obtain ⟨k, _, m, e, C, ξ, a, htaut, hy, hcl, het, hbd, hset, ha, hBD⟩ := hpre (π x) hx'
  obtain ⟨hm, hs, -, -, hrig, -, -⟩ := id htaut
  let ξ' : Sp (ChartRing k m e) ⟶ gen Y := ξ ≫ inv π
  have hξ : ξ' ≫ π = ξ := by simp [ξ']
  have hξg : ξ' ≫ genι Y = ξ ≫ ε.inv := by
    simp only [ξ', π, IsIso.inv_comp, IsIso.Iso.inv_hom, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hvan : (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl).comap π = genBdIdeal Y :=
    GlobalTheory.vanishingIdeal_comap_of_isOpenImmersion (gen Y) S π _ (genBd Y) fun w =>
      (not_congr (hrange w)).trans Iff.rfl
  refine chart_of_data Y _ d x ξ' C.t C.P C.m hm C.s hs C.δ a ?_ ?_ ?_ ?_ ?_ C.mono C.rank C.cone ha ?_ hrig.1
  · change inv π (ξ (closedPoint _)) = x
    rw [hcl, inv_apply_self]
  · exact GlobalTheory.Member.isEtaleCompletion_stalkClosedPointTo_comp_iso ξ (inv π) het
  · rw [← hvan, GlobalTheory.TorRef.idlAlong_comap, hξ]
    exact hbd
  · intro p
    rw [mem_genBd, hrange, ← Scheme.Hom.comp_apply, hξ, hset p, not_not]
  · rw [hξg]
    exact hsab C htaut ξ hy
  · rw [EffCartierData.idealSheaf_pull, GlobalTheory.TorRef.idlAlong_comap, hξg, Category.assoc, ε.inv_hom_id,
      Category.comp_id]
    exact hBD

end GlobalTheory.UChartOf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassLimitNormLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem class_limit_norm_le : ∀ (p : ℕ) [Fact p.Prime] (X Y : Type) [AddCommGroup X] [AddCommGroup Y] (e : X ≃+ Y) (β : LinearMap.BilinForm ℤ X) (be : LinearMap.BilinForm ℤ Y) (sc sc' : ℝ), 0 < sc → (∀ a b, sc * (β a b : ℝ) = sc' * (be (e a) (e b) : ℝ)) → ∀ (m : ℕ) (t : Y → PadicAlgCl p), (∀ μ, ‖t μ‖ ≤ Real.exp (-(sc' * (be μ μ : ℝ) / 2))) → ∀ (v : PadicAlgCl p) (ν : Y), (∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset Y, ∀ S : Finset Y, (∀ μ ∈ S, CongMod m μ ν) → (∀ μ ∈ S₀, CongMod m μ ν → μ ∈ S) → ‖v - ∑ μ ∈ S, t μ‖ ≤ δ) → ∀ μ : X, CongMod m (e μ) ν → (∀ μ' : X, CongMod m μ' μ → β μ μ ≤ β μ' μ') → ‖v‖ ≤ Real.exp (-(sc * (β μ μ : ℝ)) / 2) := by
  intro p _ X Y _ _ e β be sc sc' hsc hid m t ht v ν hv μ hμν hmin
  set R := Real.exp (-(sc * (β μ μ : ℝ)) / 2) with hR
  have hR0 : 0 ≤ R := (Real.exp_pos _).le
  have hterm : ∀ μ' : Y, CongMod m μ' ν → ‖t μ'‖ ≤ R := by
    intro μ' h'
    obtain ⟨w1, hw1⟩ := h'
    obtain ⟨w2, hw2⟩ := hμν
    have hc : CongMod m (e.symm μ') μ := by
      refine ⟨e.symm (w1 - w2), ?_⟩
      have : μ' = e μ + m • (w1 - w2) := by rw [hw1, hw2, smul_sub]; abel
      rw [this, map_add (f := _), map_nsmul, AddEquiv.symm_apply_apply]
    have hle := hmin _ hc
    have hle' : sc * (β μ μ : ℝ) ≤ sc' * (be μ' μ' : ℝ) := by
      have h2 := hid (e.symm μ') (e.symm μ')
      rw [AddEquiv.apply_symm_apply] at h2
      rw [← h2]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) hsc.le
    refine (ht μ').trans ?_
    rw [hR]
    apply Real.exp_le_exp.mpr
    linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨S₀, hS₀⟩ := hv δ hδ
  have h1 := hS₀ (S₀.filter (fun x => CongMod m x ν)) (fun x hx => (Finset.mem_filter.mp hx).2)
    (fun x hx hc => Finset.mem_filter.mpr ⟨hx, hc⟩)
  have h2 : ‖∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x‖ ≤ R :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR0 fun x hx => hterm x (Finset.mem_filter.mp hx).2
  calc ‖v‖ = ‖(v - ∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x) + ∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x‖ := by
          rw [sub_add_cancel]
    _ ≤ ‖v - ∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x‖ + ‖∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x‖ := norm_add_le _ _
    _ ≤ R + δ := by linarith

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleRootsEvaluationInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_roots_evaluation_injective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → (∃ (ζ : ℕ → kˣ) (ev : ℕ → D.La → (Over.mk x ⟶ o.A)), (∀ e, IsPrimitiveRoot (ζ e) (p ^ e)) ∧ (∀ e, ζ (e + 1) ^ p = ζ e) ∧ (∀ e y z, ev e (y + z) = ev e y * ev e z) ∧ (∀ e (c : D.O) y, ev e (c • y) = ev e y ≫ o.act.act c) ∧ (∀ e y, ev e y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ e (q : Over.mk x ⟶ o.A), q ^ (p ^ e) = 1 ↔ ∃ y, ev e y = q) ∧ (∀ e y, ev (e + 1) y ^ p = ev e y) ∧ (∀ e y z, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (p ^ e) (ev e y) (ev e z) (unitOn (ζ e ^ (2 * D.EF y z))))) → ∃ I : GTateIso D.toG k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ o.eta y = I.ev N y := by
  first | (exact @GlobalTheory.UPel.HT.GTateGlue.glue) | (exact GlobalTheory.UPel.HT.GTateGlue.glue) | (intros; apply GlobalTheory.UPel.HT.GTateGlue.glue  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverTraitExpansionScaleBothScalars
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem scalar_pullback_spec_mul {A : Type} [CommRing A] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of A)) (x y : A) :
    scal p (x * y) = scal p x * scal p y := by
  unfold scal; rw [map_mul, map_mul]

theorem Trait.exp_mul_left : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k) (a b c : W), T.Exp a b s F → T.Exp (c * a) (c * b) s F := by
  intro R _ _ _ D C W _ _ _ T k s F a b c ⟨σ, ⟨σ', f', hC, hP, hE⟩, hs⟩
  refine ⟨DVR.SecOps.secScale (scal T.G.hom c) σ, ⟨σ', f', ?_, hP, hE⟩, ?_⟩
  · intro Z r z J J' hJ hJ'
    rw [GlobalTheory.IntegralFamTriple.sval_secScale _ _ _ _ hJ, hC Z r z J J' hJ hJ', scalar_pullback_spec_mul, gs_mul _ z ⊤ trivial]
    ring
  · intro Z p p' hp z J hJ
    rw [GlobalTheory.IntegralFamTriple.sval_secScale _ _ _ _ hJ, hs Z p p' hp z J hJ, scalar_pullback_spec_mul, gs_mul _ z ⊤ trivial]
    ring

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingLabelStaysDividingDeeperModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.DeepDiv

end GlobalTheory.Poinc.Sep.DeepDiv

open GlobalTheory.Poinc.Sep

theorem GlobalTheory.Poinc.Sep.DeepDiv.div_lam : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂ :=
  _root_.GlobalTheory.Poinc.Sep.Tower.div_lam
end
end

