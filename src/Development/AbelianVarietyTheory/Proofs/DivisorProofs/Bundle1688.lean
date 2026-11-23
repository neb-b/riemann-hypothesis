module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1666
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDetOfMemSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0162
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0039
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1661
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0487
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTransferPosDef
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.DefTransfer

theorem sphOp_of_local : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (c : UA D.host.E V.rank ≃* GA D V),
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ∀ x,
      x ∈ locU V.rank P ↔ c x ∈ GfC V ∧ SuppF V f (c x)) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) x, c x ∈ GlobalTheory.Hk3.hyp V P ↔ x ∈ KP V.rank P) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : AE D) (ϖ : 𝓞 D.host.E) (d : List ℤ) (x : UA D.host.E V.rank),
      IsPrimeIdem P e f → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → x ∈ locU V.rank P →
      (DivAt V e (ϖ : D.host.E) d (c x) ↔ d.length = V.rank ∧ HasDiv (Ov D.host.E P) d (cLoc P x))) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (x y : UA D.host.E V.rank), x ∈ locU V.rank P →
      y ∈ locU V.rank P → HasDiv (Ov D.host.E P) d (cLoc P x) → HasDiv (Ov D.host.E P) d (cLoc P y) →
      ∃ k₁ ∈ KP V.rank P, ∃ k₂ ∈ KP V.rank P, y = k₁ * x * k₂) →
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) d R, GlobalTheory.Hk3.SphOp V P d R →
      (∀ γ ∈ R, c.symm γ ∈ locU V.rank P ∧ HasDiv (Ov D.host.E P) d (cLoc P (c.symm γ))) ∧
      ∀ x ∈ locU V.rank P, HasDiv (Ov D.host.E P) d (cLoc P x) →
        ∃! γ, γ ∈ R ∧ (c.symm γ)⁻¹ * x ∈ KP V.rank P := by
  intro D _ V c hloc hhyp hdiv hcart P d R hR
  obtain ⟨e, f, ϖ, α, -, hef, hϖ1, hϖ2, -, -, -, hαf, hαd, -, hrep⟩ := hR
  have hK : ∀ k, k ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔ c.symm k ∈ KP V.rank P := by
    intro k
    constructor
    · rintro ⟨hk1, hk2⟩
      refine (hhyp P _).1 ?_
      rw [c.apply_symm_apply]
      exact ⟨hk1, e, f, hef, hk2⟩
    · intro hk
      have h1 := (hhyp P _).2 hk
      rw [c.apply_symm_apply] at h1
      have h2 := (hloc P e f hef _).1 hk.1
      rw [c.apply_symm_apply] at h2
      exact ⟨h1.1, h2.2⟩
  have hK1 : (1 : GA D V) ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := by
    refine (hK 1).2 ?_
    rw [map_one]
    exact ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _⟩
  have hKG : ∀ k, k ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} → k ∈ GfC V := fun k hk => hk.1.1
  obtain ⟨γ0, ⟨hγ0R, -⟩, -⟩ := hrep.2 α ⟨1, hK1, 1, hK1, by simp⟩
  obtain ⟨hγ0G, k₁, hk₁, k₂, hk₂, hγ0⟩ := hrep.1 γ0 hγ0R
  have hαG : α ∈ GfC V := by
    have : α = k₁⁻¹ * γ0 * k₂⁻¹ := by rw [hγ0]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKG _ hk₁)) hγ0G) (Subgroup.inv_mem _ (hKG _ hk₂))
  have hαloc : c.symm α ∈ locU V.rank P :=
    (hloc P e f hef _).2 ⟨by rw [c.apply_symm_apply]; exact hαG, by rw [c.apply_symm_apply]; exact hαf⟩
  obtain ⟨-, hαdiv⟩ := (hdiv P e f ϖ d _ hef hϖ1 hϖ2 hαloc).1 (by rw [c.apply_symm_apply]; exact hαd)
  have hinv : ∀ x k₁ k₂, k₁ ∈ KP V.rank P → k₂ ∈ KP V.rank P → HasDiv (Ov D.host.E P) d (cLoc P x) →
      HasDiv (Ov D.host.E P) d (cLoc P (k₁ * x * k₂)) := by
    rintro x k₁ k₂ hk₁ hk₂ ⟨u, hu, a, ha, b, hb, h⟩
    refine ⟨u, hu, cLoc P k₁ * a, Subgroup.mul_mem _ hk₁.2 ha, b * cLoc P k₂, Subgroup.mul_mem _ hb hk₂.2, ?_⟩
    simp only [map_mul, Units.val_mul, h, Matrix.mul_assoc]
  refine ⟨fun γ hγ => ?_, fun x hx hxd => ?_⟩
  · obtain ⟨-, k₁, hk₁, k₂, hk₂, rfl⟩ := hrep.1 γ hγ
    have e1 : c.symm (k₁ * α * k₂) = c.symm k₁ * c.symm α * c.symm k₂ := by simp only [map_mul]
    rw [e1]
    have hk₁' := (hK _).1 hk₁
    have hk₂' := (hK _).1 hk₂
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk₁'.1 hαloc) hk₂'.1, hinv _ _ _ hk₁' hk₂' hαdiv⟩
  · obtain ⟨k₁, hk₁, k₂, hk₂, hxe⟩ := hcart P d _ x hαloc hx hαdiv hxd
    have hcx : c x = c k₁ * α * c k₂ := by rw [hxe]; simp only [map_mul, c.apply_symm_apply]
    have hk₁' : c k₁ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := (hK _).2 (by rwa [c.symm_apply_apply])
    have hk₂' : c k₂ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := (hK _).2 (by rwa [c.symm_apply_apply])
    have hconv : ∀ γ, γ⁻¹ * c x ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔ (c.symm γ)⁻¹ * x ∈ KP V.rank P := by
      intro γ
      rw [hK]
      simp only [map_mul, map_inv, c.symm_apply_apply]
    obtain ⟨γ, ⟨hγR, hγK⟩, huniq⟩ := hrep.2 (c x) ⟨_, hk₁', _, hk₂', hcx⟩
    exact ⟨γ, ⟨hγR, (hconv γ).1 hγK⟩, fun γ' hγ' => huniq γ' ⟨hγ'.1, (hconv γ').2 hγ'.2⟩⟩

theorem exists_isTransfer : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    IsInfFam θ → V.SigOK → V.IsPosDef → ∃ (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V), IsTransfer V θ j h₀ := by
  intro D _ V θ hθ hs hp
  obtain ⟨j, M, hM, hrat, hfin, hinf, hA, hform⟩ := GlobalTheory.T.exists_iso_definiteUnitary_adelicUnitaryGroup D V θ hθ hs hp
  obtain ⟨h₀, hh₀, hlat⟩ := _root_.GlobalTheory.DefTransfer.LatMove.exists_finite_point D V M hM
  obtain ⟨hex, hloc⟩ := GlobalTheory.T.definiteUnitary_localPoints_transfer_iff D V j h₀ M hM hh₀ hfin hform hlat
  have hhyp := GlobalTheory.T.hyperspecial_stabilizer_transfer_conj_selfDual_lattice D V j h₀ M hM hh₀ hfin hform hlat hloc
  have hdiv := GlobalTheory.T.divAt_selfDual_lattice_iff_hasElementaryDivisors D V j h₀ M hM hh₀ hfin hform hlat
  refine ⟨j, h₀, hh₀, hrat, hfin, hinf, hA, fun P x => ?_, hhyp, ?_⟩
  · obtain ⟨e, f, hef⟩ := hex P
    constructor
    · intro hx
      obtain ⟨h1, h2⟩ := (hloc P e f hef x).1 hx
      exact ⟨h1, e, f, hef, h2⟩
    · rintro ⟨h1, e', f', hef', h2⟩
      exact (hloc P e' f' hef' x).2 ⟨h1, h2⟩
  · exact sphOp_of_local D V (cj j h₀) hloc hhyp hdiv (fun P d x y => GlobalTheory.T.mem_sameDoubleCoset_of_hasElementaryDivisors_definiteUnitary D V.rank P d x y)

end GlobalTheory.DefTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupLevelStructureActionFixedRuns
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelActionOnto

def quotMap {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M) :
    (M ⧸ I • (⊤ : Submodule R M)) →ₗ[R] (M ⧸ I • (⊤ : Submodule R M)) :=
  (I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R M)) f
    (Submodule.map_le_iff_le_comap.1 (by rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top))

theorem quotMap_mk {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M) (a : M) :
    quotMap I f ((I • (⊤ : Submodule R M)).mkQ a) = (I • (⊤ : Submodule R M)).mkQ (f a) := rfl


open Classical in
def quotEquiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M) :
    (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R] (M ⧸ I • (⊤ : Submodule R M)) :=
  if hb : Function.Bijective (quotMap I f) then LinearEquiv.ofBijective _ hb else LinearEquiv.refl R _

theorem quotEquiv_mk {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M)
    (hb : Function.Bijective (quotMap I f)) (a : M) :
    quotEquiv I f ((I • (⊤ : Submodule R M)).mkQ a) = (I • (⊤ : Submodule R M)).mkQ (f a) := by
  unfold quotEquiv
  rw [dite_eq_left hb]
  rfl

theorem quotMap_bijective {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f f' : M →ₗ[R] M)
    (h1 : ∀ a, f (f' a) - a ∈ I • (⊤ : Submodule R M)) (h2 : ∀ a, f' (f a) - a ∈ I • (⊤ : Submodule R M)) :
    Function.Bijective (quotMap I f) := by
  have k1 : ∀ q, quotMap I f (quotMap I f' q) = q := fun q => by
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [quotMap_mk, quotMap_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact h1 a
  have k2 : ∀ q, quotMap I f' (quotMap I f q) = q := fun q => by
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [quotMap_mk, quotMap_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact h2 a
  exact ⟨Function.LeftInverse.injective k2, Function.RightInverse.surjective k1⟩

end GlobalTheory.LevelActionOnto

namespace GlobalTheory.LevelActionOnto

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem levelPin_actionPin : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → (∀ i, OMPins J R κ v₀ O i) → RhoGeo fw O → (∀ i, OneMapRow0 J R κ v₀ O i) → J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∃ ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l), ∀ (r : RunData J) (h : LawsFull r.full) (i : Fin D.R.m), letI : Algebra r.full.J.Q.c.F D.what₂.LL := ‹Algebra J.Q.c.F D.what₂.LL›; LevelPin (T := r.full) R i (ℓ i) ∧ ActionPin (T := r.full) (R := R) h.p fw i (ℓ i) := by
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw O hc hpins hrho hrow hMb
  classical
  refine ⟨fun i g => quotEquiv J.Q.l.Mb ((O i).lev g), fun r h i => ?_⟩
  have hlev : LevIs R i (iotaW J i) J.Q.l.M (Mfr J.Q.l) (O i).lev := (hpins i).2.lift.lev
  have hι : LatEmb (Wc D i) (iotaW J i) := GlobalTheory.TraceLattice.latEmb_iotaW h i
  have hβ : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1 := hc.lev.βW i
  obtain ⟨h1, hm⟩ := GlobalTheory.LevelActionPinned.congr_of_levIs R i hι hβ hMb hlev
  have hbij : ∀ g, Function.Bijective (quotMap J.Q.l.Mb ((O i).lev g)) := fun g => by
    refine quotMap_bijective _ _ ((O i).lev g⁻¹) (fun a => ?_) (fun a => ?_)
    · have e1 := hm g g⁻¹ a
      have e2 := h1 a
      rw [mul_inv_cancel] at e1
      have := Submodule.sub_mem _ e2 e1
      rwa [sub_sub_sub_cancel_left] at this
    · have e1 := hm g⁻¹ g a
      have e2 := h1 a
      rw [inv_mul_cancel] at e1
      have := Submodule.sub_mem _ e2 e1
      rwa [sub_sub_sub_cancel_left] at this
  have hspec : ∀ g a, liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a - (O i).lev g a ∈
      J.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (J.Q.Dw ((i : ℕ) + 1)).La) := fun g a => by
    rw [← Submodule.Quotient.eq]
    have := liftLa_spec (quotEquiv J.Q.l.Mb ((O i).lev g)) a
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at this
    rw [this]
    exact quotEquiv_mk _ _ (hbij g) a
  have hA : J.Q.l.A = 1 := h.j.pins.2.1.2
  refine ⟨?_, ?_⟩

  · change LevIs R i (iotaW J i) J.Q.l.M (Mfr J.Q.l) (fun g => liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)))
    intro g
    obtain ⟨k, hk, hw⟩ := hlev g
    refine ⟨k, hk, fun a ha => ?_⟩
    obtain ⟨w, hwm, e⟩ := hw a ha
    have hd : liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a - (O i).lev g a ∈
        (Ideal.span {(J.Q.l.M : 𝓞 D.host.E)}) • (⊤ : Submodule (𝓞 D.host.E) (J.Q.Dw ((i : ℕ) + 1)).La) := by
      rw [← J.Q.l.prod, mul_comm, Submodule.mul_smul]
      have key : ∀ f : (J.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (J.Q.Dw ((i : ℕ) + 1)).La,
          (∀ x, f x ∈ J.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (J.Q.Dw ((i : ℕ) + 1)).La)) →
          f a ∈ Mfr J.Q.l • J.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (J.Q.Dw ((i : ℕ) + 1)).La) := fun f hf => by
        refine Submodule.smul_induction_on ha (fun b hb x _ => ?_) (fun x y hx hy => ?_)
        · rw [map_smul]
          exact Submodule.smul_mem_smul hb (hf x)
        · rw [map_add (f := _)]
          exact add_mem hx hy
      exact key (liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) - (O i).lev g) (hspec g)
    rw [Submodule.ideal_span_singleton_smul] at hd
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hd
    have hy' : liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a = (O i).lev g a + J.Q.l.M • y := by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 D.host.E), hy, add_sub_cancel]
    have hmem : finVec (Wc D i) (iotaW J i y) ∈ latGHat (Wc D i) 1 :=
      ((GlobalTheory.MarkCoset.latG_spec D (Wc D i) 1).1 _).1 (hι.2 ▸ LinearMap.mem_range_self (iotaW J i) y)
    refine ⟨w + finVec (Wc D i) (iotaW J i y), add_mem hwm hmem, ?_⟩
    have e2 : GlobalTheory.LevelActionPinned.fvec (Wc D i) (iotaW J i) (liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a) =
        GlobalTheory.LevelActionPinned.fvec (Wc D i) (iotaW J i) ((O i).lev g a) +
          J.Q.l.M • GlobalTheory.LevelActionPinned.fvec (Wc D i) (iotaW J i) y := by
      rw [hy', map_add (f := _), map_nsmul]
    have e3 : finVec (Wc D i) (iotaW J i (liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a)) =
        finVec (Wc D i) (iotaW J i ((O i).lev g a)) + J.Q.l.M • finVec (Wc D i) (iotaW J i y) := e2
    rw [e3, nsmul_add, ← e]
    abel

  · obtain ⟨cc, ph, hone⟩ := hrow i
    have hkeep : ActKeeps (κ := κ) O i := fun g f hf => by
      obtain ⟨k, hk, -⟩ := hlev g
      exact (hone.1 g k hk f hf).1
    have hrho' := (hrho i).1 hkeep
    have hact_eq : ∀ g, actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (levFull (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)
        (quotEquiv J.Q.l.Mb ((O i).lev g)) = actLev J.Q.c (O i).lev2 g := fun g => by
      have e1 : actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (levFull (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)
          (quotEquiv J.Q.l.Mb ((O i).lev g)) = actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c
          (fun _ : Unit => levFull (J.Q.Dw ((i : ℕ) + 1)) J.Q.l (quotEquiv J.Q.l.Mb ((O i).lev g))) () := rfl
      have e2 : actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (O i).lev2 g =
          actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (fun _ : Unit => (O i).lev2 g) () := rfl
      rw [e1, e2, GlobalTheory.OneMapAllCompare.actLev_congr (lev' := fun _ : Unit => (O i).lev2 g) J.Q.c hA (fun _ a => hspec g a)]
    obtain ⟨act, hact⟩ := GlobalTheory.FormTies.exists_isLevAct D r.full.toTop h.p ((i : ℕ) + 1) (inR_succ i) (κ i) G
      (fun g => quotEquiv J.Q.l.Mb ((O i).lev g))
    refine ⟨act, hact, fun g F => ?_⟩
    obtain ⟨hf, he⟩ := hrho' g ⟨F.1, cutR_le J.toCore.C ((i : ℕ) + 1) (κ i) F.2⟩
    have e : (act g F).1 = actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (O i).lev2 g F.1 := (hact g F).trans (LinearMap.congr_fun (hact_eq g) F.1)
    change ((fw.e i ⟨(act g F).1, _⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) =
      (R.FW i).ρ g ((fw.e i ⟨F.1, _⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)
    rw [← he]
    congr 3

end GlobalTheory.LevelActionOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNuValuesTwistOnlyRamifiedEqOne
section
open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistPairs

open Formalism.L2.Host Formalism.L2.Host.CT GlobalTheory.CMVal.InvConj

theorem conjPl_eq_plMap {D : D7} [IsCMField D.host.E] (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Formalism.DivisionValues.conjPl P = plMap conjE P := by
  apply HeightOneSpectrum.ext
  rw [asIdeal_plMap]
  show P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) = _
  congr 1
  refine RingEquiv.ext fun x => RingOfIntegers.ext ?_
  rfl

theorem conjE_symm {E : Type} [Field E] [NumberField E] [IsCMField E] : (conjE (E := E)).symm = conjE :=
  RingEquiv.ext fun x => by rw [conjE_symm_apply, conjE_apply]

theorem finprod_val_nu_eq_one : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T},
    Lc.Is μ₀ → ∀ (i j : Fin D.R.m) (t : T), ∏ᶠ (w : HeightOneSpectrum (𝓞 D.host.E))
      (_ : ¬ (Lc.xiH t).UnrAt w ∧ (nuH G μ₀ i j).UnrAt w), (((nuH G μ₀ i j).val w : ℂˣ) : ℂ) = 1 := by
  intro D T Lc sc G μ₀ hL i j t
  classical
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  set ν := nuH G μ₀ i j with hν
  have hT : TrivOnF ν := (GlobalTheory.FunObj.SqNum.Model.isValChar_nu hL G i j (s := 0) (Nat.zero_le _)).1.2.1
  set c : HeightOneSpectrum (𝓞 D.host.E) → HeightOneSpectrum (𝓞 D.host.E) := fun P => Formalism.DivisionValues.conjPl P with hcdef
  have hc : ∀ P, c P = plMap conjE P := fun P => conjPl_eq_plMap P
  have hcc : ∀ P, c (c P) = P := fun P => by
    rw [hc, hc]
    have h := plMap_symm_plMap (conjE (E := D.host.E)) P
    rwa [conjE_symm] at h
  have hcinj : Function.Injective c := fun x y h => by rw [← hcc x, h, hcc y]
  have hunr : ∀ P, ν.UnrAt P ↔ ν.UnrAt (c P) := fun P => by
    rw [hc, ← unrAt_inv_iff ν hT P]
    have hloc (x : (P.adicCompletion D.host.E)ˣ) :
        (ν⁻¹).loc P x = (ν.loc P x)⁻¹ := by
      rw [← GlobalTheory.CMVal.finPart_single, ← GlobalTheory.CMVal.finPart_single,
        GlobalTheory.CMVal.finPart_inv]
    constructor <;> intro h x hx
    · rw [hloc, h x hx, inv_one]
    · have := h x hx
      rw [hloc, inv_eq_one] at this
      exact this
  have hval : ∀ P, ν.UnrAt P → ((ν.val P : ℂˣ) : ℂ) * ((ν.val (c P) : ℂˣ) : ℂ) = 1 := fun P hP => by
    have h1 := val_inv_eq ν hT P (by rw [← hc]; exact (hunr P).1 hP)
    rw [HChar.val_inv] at h1
    rw [hc, ← h1, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  set Q' := (Lc.Q t).filter fun P => ν.UnrAt P with hQ'
  have hset : {w | ¬ (Lc.xiH t).UnrAt w ∧ ν.UnrAt w} = (↑(Q' ∪ Q'.image c) : Set (HeightOneSpectrum (𝓞 D.host.E))) := by
    ext w
    simp only [Set.mem_setOf_eq, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image, Finset.mem_coe, hQ',
      Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      rcases (hL.Q_ram t w).1 h1 with h | ⟨P, hP, hcP⟩
      · exact Or.inl ⟨h, h2⟩
      · have e : w = c P := GlobalTheory.GoodPrimes.isConjPl_iff.1 hcP
        exact Or.inr ⟨P, ⟨hP, (hunr P).2 (e ▸ h2)⟩, e.symm⟩
    · rintro (⟨h, h2⟩ | ⟨P, ⟨hP, h2⟩, rfl⟩)
      · exact ⟨(hL.Q_ram t w).2 (Or.inl h), h2⟩
      · exact ⟨(hL.Q_ram t (c P)).2 (Or.inr ⟨P, hP, GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl⟩), (hunr P).1 h2⟩
  have hdisj : Disjoint Q' (Q'.image c) := by
    rw [Finset.disjoint_left]
    intro P hP hP'
    obtain ⟨P', hP'Q, e⟩ := Finset.mem_image.1 hP'
    exact ((hL.Q_pl t) P' (Finset.mem_filter.1 hP'Q).1).2 P (Finset.mem_filter.1 hP).1 (GlobalTheory.GoodPrimes.isConjPl_iff.2 e.symm)
  show ∏ᶠ w ∈ {w | ¬ (Lc.xiH t).UnrAt w ∧ ν.UnrAt w}, ((ν.val w : ℂˣ) : ℂ) = 1
  rw [hset, finprod_mem_coe_finset, Finset.prod_union hdisj, Finset.prod_image fun x _ y _ h => hcinj h,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun P hP => hval P (Finset.mem_filter.1 hP).2

end GlobalTheory.TwistPairs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionConstValuationEigenLatticeAtPrime
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.PtDeg

theorem rho_eq_vAdd_at_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), (∀ la, ∀ w ∈ valOn Z la, w s.sig = (ρ la : EReal)) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (t : 𝓞 E →+* 𝓞 K), (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a)) → ∀ (π : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 c.F)) (ε : HeightOneSpectrum (𝓞 K) → ℕ), (∀ 𝔓 (z : c.F), 𝔓.valuation K (algebraMap c.F K z) = (π 𝔓).valuation c.F z ^ ε 𝔓) → ∀ (u : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (u' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F τ.1 u → GlobalTheory.PtDeg.FrameCoord y m1 m2 F (conjEmb τ.1) u' → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (b : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (M : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) K) (b' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K) (M' : Matrix (Fin (Dw.mult (conjEmb τ.1))) (Fin (Dw.mult (conjEmb τ.1))) K), GlobalTheory.PtDeg.LocBasis 𝔓 (F.eigLat B.t.act t) b → (∀ i, u i = ∑ j, M i j • b j) → GlobalTheory.PtDeg.LocBasis 𝔓 (F.eigLat B.t.act (t.comp (H.bar : 𝓞 E →+* 𝓞 E))) b' → (∀ i, u' i = ∑ j, M' i j • b' j) → (ε 𝔓 : ℝ) * ρ (π 𝔓) = (vAdd 𝔓 (evR Xo c s.sig y) : ℝ) + (vAdd 𝔓 M.det : ℝ) - (vAdd 𝔓 M'.det : ℝ) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ s ρ hρ K _ _ _ y hyZ B t₀ m1 m2 F t ht π ε hπε u u' hu hu' 𝔓 b M b' M' hb hM hb' hM'
  have hε : 0 < ε 𝔓 := by
    rcases Nat.eq_zero_or_pos (ε 𝔓) with h | h
    · have h0 := hπε 𝔓 0
      rw [h, pow_zero, map_zero, map_zero] at h0
      exact absurd h0 zero_ne_one
    · exact h
  obtain ⟨T, iK, hFin, hT⟩ := _root_.GlobalTheory.exists_cdvr_completion_integral_iff K 𝔓
  obtain ⟨e, he, hv⟩ := GlobalTheory.T.exists_ramification_completeDVR_valuation_eq_mul K 𝔓 T iK hT
  letI := (iK.comp (algebraMap c.F K)).toAlgebra
  let φ : K →ₐ[c.F] T.Fr := { iK with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := GlobalTheory.FlagTan.exists_frMap φ y
  have htri := GlobalTheory.T.triangular_frameChange_basechange_integral_at_completion E H Dw l Xo c K y B t₀ m1 m2 𝔓 T iK hT yT hyT
  rcases htri with ⟨ρV, hρV, G, t', n, n', m1', m2', h1, h2, C, td, y', hlow, hdiag, hchg, hlie, hint⟩
  have hbor : FrBor td yT y' :=
    ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c T.Fr yT y' y').1 td).2 ⟨C, hlow, hdiag, hchg⟩
  have hover : OverLa (π 𝔓) T.V (iK.comp (algebraMap c.F K)) (e * ε 𝔓) := by
    refine ⟨Nat.mul_pos he hε, fun z => ?_⟩
    rw [RingHom.comp_apply, hv, vAdd, hπε, vLa]
    by_cases hz : z = 0
    · subst hz; simp
    · have hz' : (π 𝔓).valuation c.F z ≠ 0 := by simpa using hz
      rw [WithZero.log_pow]
      push_cast; ring
  let yI : IntFr Xo c T (iK.comp (algebraMap c.F K)) := ⟨y', GlobalTheory.FlagTan.fromTest_of_isLocalRing y', hint⟩
  have hyTZ : LiesOn Z yT := GlobalTheory.FlatLine.liesOn_frMap hyT hyZ
  have hlies : LiesOn Z y' := by
    have e1 : ptF y' = ptF yT := by
      unfold ptF
      congr 1
      exact hchg.1
    intro p
    rw [e1]
    exact hyTZ p
  have hmem : (fun f => nval T.V (e * ε 𝔓) (evI yI f)) ∈ valOn Z (π 𝔓) :=
    ⟨PtV.mk (π 𝔓) hover yI ⟨hFin, hlies⟩ () trivial, rfl⟩
  have hval := hρ (π 𝔓) _ hmem
  have hev1 := GlobalTheory.FlagTan.evR_frBor s.sig_mem hbor
  have hev2 : evR Xo c s.sig yT = φ (evR Xo c s.sig y) := GlobalTheory.FlagTan.evR_frMap s.sig_mem.1 hyT
  have hS4 := _root_.GlobalTheory.FlatChar.flatWt_char E H Dw τ T.Fr td
  have hct := GlobalTheory.ConjHostChar.conj_char E H Dw l Xo c τ K t ht
  obtain ⟨hA1, hA2⟩ := GlobalTheory.T.integralFrame_span_completed_eigenLattice E H Dw l Xo c K y B t₀ m1 m2 F τ.1 t ht u hu 𝔓 T iK hT ρV hρV yT hyT G t' n n'
    m1' m2' h1 h2 C (td none) y' hchg hlie
  obtain ⟨hB1, hB2⟩ := GlobalTheory.T.integralFrame_span_completed_eigenLattice E H Dw l Xo c K y B t₀ m1 m2 F (conjEmb τ.1) (t.comp (H.bar : 𝓞 E →+* 𝓞 E)) hct u' hu'
    𝔓 T iK hT ρV hρV yT hyT G t' n n' m1' m2' h1 h2 C (td none) y' hchg hlie
  obtain ⟨-, hCdet, hvC⟩ := _root_.GlobalTheory.TwoBasesDet.det_vV_add_eq_zero K 𝔓 T iK hT F.P₀.g _ _ b hb M u hM (C τ.1) hA1 hA2
  obtain ⟨-, -, hvC'⟩ := _root_.GlobalTheory.TwoBasesDet.det_vV_add_eq_zero K 𝔓 T iK hT F.P₀.g _ _ b' hb' M' u' hM' (C (conjEmb τ.1)) hB1 hB2
  have hdet : ∀ σ, (C σ).det = ∏ i, (td (some ⟨σ, i⟩) : T.Fr) := fun σ => by
    rw [Matrix.det_of_lowerTriangular (C σ) (fun i j hij => hlow σ i j hij)]
    exact Finset.prod_congr rfl fun i _ => hdiag σ i
  have hφ : ∀ z, φ z = iK z := fun _ => rfl
  have hprod : evR Xo c s.sig y' * (C τ.1).det = (C (conjEmb τ.1)).det * iK (evR Xo c s.sig y) := by
    rw [hev1, hev2, hdet, hdet, hφ, ← hS4]
    ring
  have hval' : nval T.V (e * ε 𝔓) (evR Xo c s.sig y') = (ρ (π 𝔓) : EReal) := hval
  have hy'0 : evR Xo c s.sig y' ≠ 0 := by
    intro h0
    rw [h0, nval_zero] at hval'
    exact EReal.coe_ne_top _ hval'.symm
  have ha0 : iK (evR Xo c s.sig y) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    exact mul_ne_zero hy'0 hCdet hprod
  have hC'0 : (C (conjEmb τ.1)).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hprod
    exact mul_ne_zero hy'0 hCdet hprod
  have hZ := congrArg (vV T.V) hprod
  rw [vV_mul hy'0 hCdet, vV_mul hC'0 ha0, hv] at hZ
  rw [hv] at hvC hvC'
  rw [nval_of_ne hy'0, EReal.coe_eq_coe_iff] at hval'
  have hvy : (vV T.V (evR Xo c s.sig y') : ℝ) = e * ((vAdd 𝔓 (evR Xo c s.sig y) : ℝ) + (vAdd 𝔓 M.det : ℝ) - (vAdd 𝔓 M'.det : ℝ)) := by
    have : vV T.V (evR Xo c s.sig y') = e * (vAdd 𝔓 (evR Xo c s.sig y) + vAdd 𝔓 M.det - vAdd 𝔓 M'.det) := by linarith
    rw [this]; push_cast; ring
  rw [← hval', hvy]
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hε' : (ε 𝔓 : ℝ) ≠ 0 := by exact_mod_cast hε.ne'
  push_cast
  field_simp

end GlobalTheory.PtDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterQuotientNotUnramifiedAtBasePlaceId
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RamifiedIdeleBasePlace

theorem ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ →
    ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v = G.pl.v0 →
      ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  intro D T Lc sc G μ₀ hL t v e he hv i j hU
  subst hv
  have hw : (G.pl.w G.pl.v0).under (𝓞 D.host.F) = G.pl.v0 := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have h1 := GlobalTheory.UnrOverPlace.unrAt_of_unramAt D _ G.pl.v0 e he hU _ hw
  exact GlobalTheory.RowTest.squareNuHeckeCharacter_not_unramified_at_chosenPlace hL G t i j
    ((GlobalTheory.LFun.unrAt_iff_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL) _).1 h1)

end GlobalTheory.RamifiedIdeleBasePlace
end

