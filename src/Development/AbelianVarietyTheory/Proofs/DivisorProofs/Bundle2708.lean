module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2420
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2671
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2674
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1128
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsIntegralUnitNormalLocalDo
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.IntTheta

section Pull
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {a : ℤ}

theorem sec_ext' {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  obtain ⟨f₁, p₁⟩ := s
  obtain ⟨f₂, p₂⟩ := s'
  obtain rfl : f₁ = f₂ := funext h
  rfl

theorem gs_pullS' {T T' : Over S} (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T' ⊗ A).left) (z : Z) (j : Fin 1 → L.ι) (hz : r z ∈ (LPow A L a T').U j) :
    gs r z ((LPow A L a T').U j) ((VVRank.pullS A a h s).f j) =
      gs (r ≫ (h ▷ A).left) z ((LPow A L a T).U j) (s.f j) :=
  (gs_res r z (chart_le_res A L (h ▷ A) (whiskerRight_snd _ _) a j) hz _).trans
    (gs_pull r (h ▷ A).left z _ (chart_le_res A L (h ▷ A) (whiskerRight_snd _ _) a j hz) _)

theorem pullS_comp' {T T' T'' : Over S} (h' : T'' ⟶ T') (h : T' ⟶ T) (s : LB.Sec (LPow A L a T)) :
    VVRank.pullS A a h' (VVRank.pullS A a h s) = VVRank.pullS A a (h' ≫ h) s :=
  sec_ext' fun j => fn_ext fun y hy => by
    refine (gs_pullS' h' _ _ y j hy).trans ((gs_pullS' h _ _ y j
      (chart_le_res A L (h' ▷ A) (whiskerRight_snd _ _) a j hy)).trans (Eq.trans ?_ (gs_pullS' _ _ _ y j hy).symm))
    rw [comp_whiskerRight, Over.comp_left]
    rfl

theorem pullS_heq {T : Over S} {Y : Scheme.{0}} {y₁ y₂ : Y ⟶ S} (e : y₁ = y₂) (h₁ : Over.mk y₁ ⟶ T)
    (h₂ : Over.mk y₂ ⟶ T) (he : h₁.left = h₂.left) (s : LB.Sec (LPow A L a T)) :
    HEq (VVRank.pullS A a h₁ s) (VVRank.pullS A a h₂ s) := by
  subst e
  obtain rfl : h₁ = h₂ := Over.OverMorphism.ext he
  rfl

end Pull

section Sec
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left)

theorem pull_pull {R K K' : Type} [CommRing R] [CommRing K] [CommRing K'] {x : Sp R ⟶ S} (θ : SecAt G L x)
    (i : R →+* K) (i' : K →+* K') :
    HEq (SecAt.pull G L (SecAt.pull G L θ i) i') (SecAt.pull G L θ (i'.comp i)) := by
  unfold SecAt.pull
  rw [pullS_comp']
  refine pullS_heq ?_ _ _ ?_ θ
  · rw [spMap_comp, Category.assoc]
  · simp only [Over.comp_left, Over.homMk_left]
    exact (spMap_comp i i').symm

theorem pull_heq_of_eq {R K : Type} [CommRing R] [CommRing K] {x : Sp R ⟶ S} (θ : SecAt G L x)
    {i₁ i₂ : R →+* K} (h : i₁ = i₂) : HEq (SecAt.pull G L θ i₁) (SecAt.pull G L θ i₂) := by
  subst h; rfl

variable {G L} in
theorem thList_of_heq (ρ : LB.Gen (L.pull (eSec G))) (m : ℕ) {K : Type} [Field K] {x₁ x₂ : Sp K ⟶ S} (e : x₁ = x₂)
    {θ₁ : SecAt G L x₁} {θ₂ : SecAt G L x₂} (h : HEq θ₁ θ₂) {N : ℕ} {pt : Fin N → (Over.mk x₁ ⟶ G)} {c : Fin N → K}
    (H : ThList G L ρ m x₁ θ₁ pt c) : ∃ pt' : Fin N → (Over.mk x₂ ⟶ G), ThList G L ρ m x₂ θ₂ pt' c := by
  subst e
  obtain rfl := eq_of_heq h
  exact ⟨pt, H⟩

end Sec

end GlobalTheory.UMin.IntTheta

namespace GlobalTheory.UMin.IntTheta

theorem at_cdvr (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S)
    (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (χ : Sp R ⟶ S) (σ : SecAt t.G t.PP.L χ)
    (e : Fin N → FractionRing R) (hm : Odd m) (hm3 : 3 ≤ m) (hmu : IsUnit (m : R)) (hN : N = m ^ (4 * g))
    (hP : PolFib t.G t.PP.L g (spMap (algebraMap R (FractionRing R)) ≫ χ)) (hNZ : NZ t.G t.PP.L χ σ)
    (hS : SymAt t.G t.PP.L t.PP.rig m (spMap (algebraMap R (FractionRing R)) ≫ χ)
      (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) e)
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.LN.CDvr V) (φ : R →+* V)
    (F : FractionRing R →+* FractionRing V)
    (hring₀ : F.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ) :
    ∃ eV : Fin N → V, (∀ j, algebraMap V (FractionRing V) (eV j) = F (e j)) ∧ ∃ j, IsUnit (eV j) := by
  obtain ⟨hdvr, -, -⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  obtain ⟨i, hi⟩ : ∃ i : V →+* AlgebraicClosure (FractionRing V),
      i = (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp (algebraMap V (FractionRing V)) :=
    ⟨_, rfl⟩
  obtain ⟨i', hi'⟩ : ∃ i' : FractionRing R →+* AlgebraicClosure (FractionRing V),
      i' = (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp F := ⟨_, rfl⟩
  have hring : i'.comp (algebraMap R (FractionRing R)) = i.comp φ := by
    rw [hi, hi', RingHom.comp_assoc, hring₀, RingHom.comp_assoc]

  have : IsMonHom (Iso.refl t.G).hom := inferInstanceAs (IsMonHom (𝟙 t.G))
  have hid : IsGrpPullback t.G t.G (𝟙 _) (𝟙 t.G.left) := isGrpPullback_of_iso (Iso.refl t.G)
  have hmove : ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S), ∀ (R'' : Type) [CommRing R''] (j : R' →+* R''),
      PolFib t.G t.PP.L g x → PolFib t.G t.PP.L g (spMap j ≫ x) := fun R' _ x =>
    (_root_.GlobalTheory.UMin.FibMove.polFib_move S S t.G t.PP.L t.G t.PP.L (𝟙 S) (𝟙 t.G.left) t.PP.isLB t.PP.isLB hid
      (GlobalTheory.ThetaAffineGlue.lbIso_pull_id t.PP.isLB) g R' x).2
  have hPK : PolFib t.G t.PP.L g (spMap i' ≫ spMap (algebraMap R (FractionRing R)) ≫ χ) :=
    hmove _ _ _ i' hP
  have hmK : ((m : ℕ) : AlgebraicClosure (FractionRing V)) ≠ 0 := by
    have := (hmu.map (i'.comp (algebraMap R (FractionRing R)))).ne_zero
    simpa using this
  obtain ⟨pt, c, hT⟩ := _root_.GlobalTheory.UMin.exists_thList S t.G t.PP.L t.PP.rig t.PP.isLB t.PP.rigGen g m N
    (AlgebraicClosure (FractionRing V)) _
    (SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) i') hm hmK hN hPK
  have hsym := hS _ i' pt c hT

  have ex : spMap i' ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap i ≫ spMap φ ≫ χ := by
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, hring]
  have hθ : HEq (SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) i')
      (SecAt.pull t.G t.PP.L (SecAt.pull t.G t.PP.L σ φ) i) :=
    ((pull_pull t.G t.PP.L σ _ i').trans (pull_heq_of_eq t.G t.PP.L σ hring)).trans
      (pull_pull t.G t.PP.L σ φ i).symm
  obtain ⟨pt', hT'⟩ := thList_of_heq t.PP.rig m ex hθ hT
  have hPV : PolFib t.G t.PP.L g (jK V ≫ spMap φ ≫ χ) := by
    have e₁ : jK V ≫ spMap φ ≫ χ = spMap F ≫ spMap (algebraMap R (FractionRing R)) ≫ χ := by
      rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, hring₀]
    rw [e₁]; exact hmove _ _ _ F hP
  have hNZV := GlobalTheory.UMin.nz_pull S t.G t.PP.L t.PP.isLB t.semi R V χ σ φ hNZ
  have hmV : IsUnit ((m : ℕ) : V) := by simpa using hmu.map φ
  have hinj : Function.Injective i := by
    rw [hi, RingHom.coe_comp]
    exact (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective.comp
      (IsFractionRing.injective V (FractionRing V))
  have hprim := _root_.GlobalTheory.UMin.prim_of_polFib E H S t g V hV (spMap φ ≫ χ) hPV (SecAt.pull t.G t.PP.L σ φ) hNZV m N hm hm3 hmV
    (AlgebraicClosure (FractionRing V)) i pt' c hinj hT'
  rw [hi] at hprim
  refine _root_.GlobalTheory.UMin.symTup_unit_of_prim V (AlgebraicClosure (FractionRing V)) (algebraMap (FractionRing V) _) N c (fun j => F (e j))
    hprim (fun j => ?_)
  rw [← hsym j, hi']; rfl

end GlobalTheory.UMin.IntTheta

namespace GlobalTheory.UMin.IntTheta

theorem comp_inj {R V : Type} [CommRing R] [CommRing V] [IsDomain V] (φ : R →+* V) (hφ : Function.Injective φ) :
    Function.Injective ((algebraMap V (FractionRing V)).comp φ) := by
  rw [RingHom.coe_comp]; exact (IsFractionRing.injective V (FractionRing V)).comp hφ

theorem integral_with_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (σ : SecAt t.G t.PP.L χ) (e : Fin N → FractionRing R), Odd m → 3 ≤ m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib t.G t.PP.L g (spMap (algebraMap R (FractionRing R)) ≫ χ) → NZ t.G t.PP.L χ σ → SymAt t.G t.PP.L t.PP.rig m (spMap (algebraMap R (FractionRing R)) ≫ χ) (SecAt.pull t.G t.PP.L σ (algebraMap R (FractionRing R))) e → ∃ e' : Fin N → R, (∀ j, algebraMap R (FractionRing R) (e' j) = e j) ∧ ∃ j, IsUnit (e' j) := by
  intro E _ _ _ H S t g m N R _ _ _ _ _ _ χ σ e hm hm3 hmu hN hP hNZ hS
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V)
      (hg : Function.Injective ((algebraMap V (FractionRing V)).comp φ)), ∃ eV : Fin N → V,
        (∀ j, algebraMap V (FractionRing V) (eV j) = IsFractionRing.lift hg (e j)) ∧ ∃ j, IsUnit (eV j) := by
    intro V _ _ _ hV φ hg
    have h₀ : (IsFractionRing.lift (K := FractionRing R) hg).comp (algebraMap R (FractionRing R)) =
        (algebraMap V (FractionRing V)).comp φ := by
      ext r
      rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
    exact at_cdvr E H S t g m N R χ σ e hm hm3 hmu hN hP hNZ hS V hV φ _ h₀
  have hint : ∀ j, ∃ r : R, algebraMap R (FractionRing R) r = e j := by
    intro j
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) (e j)
    change IsLocalization.mk' (FractionRing R) a b = e j at hab
    have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
    have hdvd : (b : R) ∣ a := _root_.GlobalTheory.DvrDiv.dvd_of_forall_cDvr R a b hb0 fun V _ _ _ hV φ hφ => by
      obtain ⟨eV, he, -⟩ := key V hV φ (comp_inj φ hφ)
      refine ⟨eV j, ?_⟩
      apply IsFractionRing.injective V (FractionRing V)
      have h1 := he j
      rw [← hab, IsFractionRing.lift_mk'] at h1
      have hb' : ((algebraMap V (FractionRing V)).comp φ) (b : R) ≠ 0 :=
        fun h => hb0 ((comp_inj φ hφ) (h.trans (map_zero _).symm))
      rw [eq_div_iff hb'] at h1
      simp only [RingHom.comp_apply] at h1
      rw [map_mul, ← h1, mul_comm]
    obtain ⟨r, hr⟩ := hdvd
    refine ⟨r, ?_⟩
    rw [← hab, hr, IsLocalization.mk'_mul_cancel_left]
  choose e' he' using hint
  refine ⟨e', he', ?_⟩
  obtain ⟨V, _, _, _, φ, hV, hφ, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating R
  obtain ⟨eV, he, j, hu⟩ := key V hV φ (comp_inj φ hφ)
  have hj : φ (e' j) = eV j := by
    apply IsFractionRing.injective V (FractionRing V)
    rw [he j, ← he' j, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  refine ⟨j, (isUnit_map_iff φ _).1 ?_⟩
  rw [hj]; exact hu

end GlobalTheory.UMin.IntTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSeesawDictionaryFramesSignatures
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem gBig_both {P Q S : GP} (hP : GBig P) (hQ : GBig Q)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → Q G μ₀ C x b → S G μ₀ C x b) : GBig S := by
  obtain ⟨CF1, h1⟩ := hP
  obtain ⟨CF2, h2⟩ := hQ
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, g1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, g2⟩ := h2 ε CF (le_of_max_le_right hCF)
  exact ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ
    (g1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hr T Lc μ₀ hμ G)
    (g2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hr T Lc μ₀ hμ G)⟩

private theorem fst_fin {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (FA : GlobalTheory.ChainFr.Fr A) (FW : GlobalTheory.ChainFr.Fr WW) (hA : ∀ τ, (GlobalTheory.SquareComm.frSgn true FA).cart τ = -X.rA.s τ)
    (hW : ∀ τ, FW.cart τ = X.rW.s τ) (hX : X.Is ψ θ α β νH S) (t : T) : GlobalTheory.SquareComm.IsFinF ψ θ true FA FW (X.f t) := by
  have hv := hX.isVac
  have hν : Formalism.L2.Theta.IsHeckeChar D (α t / β t) := by
    have h := (hX.weil t).hecT
    rw [← inv_div]
    refine ⟨?_, fun x => ?_⟩
    · exact continuous_inv.comp h.1
    · show ((β t / α t) _)⁻¹ = 1
      rw [h.2 x, inv_one]
  have hI : X.ideal S t ≠ ⊥ := by
    unfold Tri.ideal
    rw [← Ideal.zero_eq_bot]
    refine Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_
    rw [Ideal.zero_eq_bot]
    exact w.ne_bot
  obtain ⟨f₁, h1, h1t⟩ := GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D ψ θ A WW X.rA X.rW (α t / β t) (X.e t) (S t) (X.ideal S t) X.vac
    hX.rigA hX.rigW hν (hX.idem t) hI hv
  have heq : X.f t = f₁ := by
    obtain ⟨⟨Tm, hT⟩, hall⟩ := hX.fst t
    rw [hall Tm hT, h1.2 Tm hT]
  have hft : IsThetaFunO ψ (GlobalTheory.Grid.neg A) WW (X.f t) := heq ▸ h1t
  refine ⟨hft, fun τ => ?_⟩
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.idem t)
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hv.1.1.1 hv.2.inf ho.infPart_eq ho.conj.infPart_eq
    (hX.fst t) hv.2.theta hft (hv.2.fock τ)
  rw [hA τ, hW τ]
  exact hF

private theorem snd_fin {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (hA' : ∀ τ, (GlobalTheory.SquareComm.frSgn false FA').cart τ = X.rA'.s τ)
    (hW : ∀ τ, FW.cart τ = X.rW.s τ) (hI : X.Is ψ θ α β νH S) (t : T) : GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW (X.f' t) := by
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hth : IsThetaFunO ψ A' WW (X.f' t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hI.isVac'.1 hI.isVac'.2.inf (hI.snd t) hI.isVac'.2.theta
  refine ⟨hth, fun τ => ?_⟩
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hI.isVac'.1.1.1 hI.isVac'.2.inf ho.conj.infPart_eq
    ho.conj.conj.infPart_eq (hI.snd t) hI.isVac'.2.theta hth (hI.isVac'.2.fock τ)
  rw [hA' τ, hW τ]
  exact hF

open GlobalTheory.StageDict in
theorem _root_.GlobalTheory.T.towerStage_seesawDictionary_framesSignatures : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW),
  GlobalTheory.SqTower.IsStageC W i j p q X → ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ),
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) (A.rank - p) p) ∧ (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) (A'.rank - q) q) ∧
    (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) (WW.rank - (p + q)) (p + q)) ∧
    ∀ t : T, GlobalTheory.SquareComm.IsTriple A A' WW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧
      (∀ τ, HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ)) ∧
      GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) ∧ GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) ∧
      (∀ P g h, thetaKO (X.ω t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) = X.ker W.ψ W.θ t P h g) ∧
      ∀ P g h, thetaKO (X.ω' t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.ker' W.ψ W.θ t P h g := by
  refine gBig_both _root_.GlobalTheory.SquareInfGap.square_infExp_gap GlobalTheory.T.towerStage_finitePlaces_unramified_or_split ?_
  intro D T Lc sc G μ₀ C x b _ hinf hram W i j p q A A' WW X hX
  obtain ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩ := hX
  obtain ⟨a, b, hab⟩ := hinf W i j
  have hsz := stage_sizes i j hp hq hrA hrA'
  have hrk : WW.rank = A.rank + A'.rank := hXi.rank.symm
  have e1 : ∀ τ, (GlobalTheory.SquareComm.frSgn true (rigFr X.rA hXi.rigA)).cart τ = -X.rA.s τ := cart_frSgn_true_rigFr X.rA hXi.rigA
  have e1' : ∀ τ, (GlobalTheory.SquareComm.frSgn false (rigFr X.rA' hXi.rigA')).cart τ = X.rA'.s τ := cart_frSgn_false_rigFr X.rA' hXi.rigA'
  have e2 : ∀ τ, (rigFr X.rW hXi.rigW).cart τ = X.rW.s τ := cart_rigFr X.rW hXi.rigW
  refine ⟨rigFr X.rA hXi.rigA, rigFr X.rA' hXi.rigA', rigFr X.rW hXi.rigW, a, b, hnA, hnA', hnW, fun t => ⟨?_,
    fun τ => ⟨(hab t τ).1, (hab t τ).2.1⟩,
    fst_fin X _ _ _ _ _ _ _ _ e1 e2 hXi t, snd_fin X _ _ _ _ _ _ _ _ e1' e2 hXi t, ?_, ?_⟩⟩
  · refine
      { hecA := (hXi.weil' t).hecS
        hecB := (hXi.weil t).hecS
        resA := (hXi.weil' t).resS
        resB := (hXi.weil t).resS
        rank := hrk
        even := by rw [hrk]; exact hsz.1
        sig := ⟨p, q, fun τ => ⟨hnA τ, hnA' τ, hnW τ⟩, hsz.2.1, hsz.2.2.1⟩
        gap := fun τ => ⟨a τ, b τ, (hab t τ).1, (hab t τ).2.1, ?_⟩
        ram := hram W i j p q A A' WW X ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩ t }
    have h1 := (hab t τ).2.2
    have h2 : ((WW.rank : ℕ) : ℚ) ≤ ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) := by
      exact_mod_cast (hrk ▸ hsz.2.2.2)
    linarith
  · intro P g h
    have f1 : (GlobalTheory.SquareComm.frSgn true (rigFr X.rA hXi.rigA)).cart = fun τ => -X.rA.s τ := funext e1
    have f2 : (rigFr X.rW hXi.rigW).cart = X.rW.s := funext e2
    have f3 : (rigFr X.rA hXi.rigA).onb = X.rA.B := funext (onb_rigFr X.rA hXi.rigA)
    have f4 : (rigFr X.rW hXi.rigW).onb = X.rW.B := funext (onb_rigFr X.rW hXi.rigW)
    unfold GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker
    rw [f1, f2, f3, f4]
  · intro P g h
    have f1 : (GlobalTheory.SquareComm.frSgn false (rigFr X.rA' hXi.rigA')).cart = X.rA'.s := funext e1'
    have f2 : (rigFr X.rW hXi.rigW).cart = X.rW.s := funext e2
    have f3 : (rigFr X.rA' hXi.rigA').onb = X.rA'.B := funext (onb_rigFr X.rA' hXi.rigA')
    have f4 : (rigFr X.rW hXi.rigW).onb = X.rW.B := funext (onb_rigFr X.rW hXi.rigW)
    unfold GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker'
    rw [f1, f2, f3, f4]
    rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionCorrectionIsTopDegreeForm
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem isTopForm_corrDens : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → IsTopForm (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) := by
  intro F _ σ X m E O H H₀ hM hM₀ ρ hρ
  refine ⟨fun i j y hy hi hj => ?_, fun i => ?_⟩
  · exact _root_.GlobalTheory.GoodTop.corrTop_holoChart_trans E O H H₀ hM hM₀ hρ i.holo j hy hi hj (E.nonempty (under y)).choose_spec
  · refine GlobalTheory.T.aemeasurable_chart_of_locally_continuous_density i.e (isOpen_ptsIn O) fun y hy hc => ?_
    set A := (E.nonempty (under y)).choose with hAdef
    have hA : A ∈ E.S (under y) := (E.nonempty (under y)).choose_spec
    refine ⟨corrTop (fun v => ρ (i.e.symm v)) (fun v => H₀ A (i.e.symm v) ()) (fun v => H A (i.e.symm v) ()), ?_, ?_⟩
    · have hs : i.e.target ∩ i.e.symm ⁻¹' Set.univ ∈ 𝓝 (i.e y) := by
        simpa using i.e.open_target.mem_nhds (i.e.map_source hc)
      have hρ1 : ContDiffAt ℝ 1 (fun v => ρ (i.e.symm v)) (i.e y) :=
        ((contDiffOn_chart (S := Set.univ) (fun z _ => hρ z) i).contDiffAt hs).of_le (by norm_cast)
      have hc0 := _root_.GlobalTheory.GoodTop.continuousAt_corrC hρ1 (hM₀.mContDiffAt_chart mem_ptsIn_top i hc hA ())
        (hM₀.isUnit_det_chart mem_ptsIn_top i hc hA ()) (hM.mContDiffAt_chart hy i hc hA ())
        (hM.isUnit_det_chart hy i hc hA ())
      exact continuousAt_const.mul (Complex.continuous_re.continuousAt.comp hc0)
    · filter_upwards [(isOpen_ptsIn O).mem_nhds hy, i.e.open_source.mem_nhds hc, GlobalTheory.FrameLift.eventually_mem hA]
        with z hzO hzc hAz
      have h := _root_.GlobalTheory.GoodTop.corrTop_holoChart_trans E O H H₀ hM hM₀ hρ i.holo i hzO hzc hzc hAz
      rw [AlgChart.transDet_self i hzc, norm_one, one_pow, one_mul] at h
      exact h.symm

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateDualNumberPointInverseConstantTangent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TanAdd

theorem tanVal_const_point {S : Type} [CommRing S] {A : Over (Sp S)} (c : epsR S ⟶ A) (p : Sp S ⟶ A.left)
    (hc : c.left = spMap (algebraMap S (DualNumber S)) ≫ p) (f : Form (A.hom ≫ 𝟙 _)) :
    tanVal c f = 0 := by
  have e : GlobalTheory.GrpTangent.epsScale (0 : S) ≫ c = c := by
    refine Over.OverMorphism.ext ?_
    have h := Over.w (GlobalTheory.GrpTangent.epsScale (0 : S))
    rw [Over.comp_left, hc, ← Category.assoc]
    exact congrArg (· ≫ p) h
  rw [← e, tanVal_epsScale, zero_mul]

theorem isTangent_iff_reduction_eq_one {S : Type} [CommRing S] {A : Over (Sp S)} [GrpObj A] (z : epsR S ⟶ A) :
    IsTangent z ↔ spOver (TrivSqZeroExt.fstHom S S S) ≫ z = 1 := by
  have h1 : (1 : Over.mk (spMap (algebraMap S S)) ⟶ A).left = η[A].left := by
    rw [Hom.one_def, Over.comp_left]
    have : (CartesianMonoidalCategory.toUnit (Over.mk (spMap (algebraMap S S)))).left = 𝟙 (Sp S) := by
      have h := Over.w (CartesianMonoidalCategory.toUnit (Over.mk (spMap (algebraMap S S))))
      refine (Category.comp_id _).symm.trans (h.trans ?_)
      exact Spec.map_id _
    rw [this]
    exact Category.id_comp _
  constructor
  · intro h
    exact Over.OverMorphism.ext (h.trans h1.symm)
  · intro h
    exact (congrArg Over.Hom.left h).trans h1

theorem translate_const (hC : CrystallineSmoothLift) (hH : AbelianHodgeDeRham) (S : Type) [CommRing S]
    (A : Over (Sp S)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (c : epsR S ⟶ A) (p : Sp S ⟶ A.left)
    (hc : c.left = spMap (algebraMap S (DualNumber S)) ≫ p) (y : epsR S ⟶ A) :
    (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ y.left =
      spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ c.left ↔ IsTangent (y * c⁻¹)) ∧
      ∀ f, tanVal y f = tanVal (y * c⁻¹) f := by
  refine ⟨?_, fun f ↦ ?_⟩
  · rw [isTangent_iff_reduction_eq_one, MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_one]
    exact ⟨fun h ↦ Over.OverMorphism.ext h, fun h ↦ congrArg Over.Hom.left h⟩
  · have h := tanVal_mul_all hC hH S A g hA hg f (y * c⁻¹) c
    rw [inv_mul_cancel_right, tanVal_const_point c p hc f, add_zero] at h
    exact h

end GlobalTheory.TanAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_symmetric_lifts_theta_group_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ (x' : TFK (R := W) F ⟶ T.A.A) (x : TFK (R := R) F ⟶ C.A.A), (ptSecT T.A.A x').left ≫ f = (ptSecT C.A.A x).left → x' ^ (C.n ^ j) = 1 → ((∃ θ' : ThetaGrp T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := W) F), SymLift T.A.A T.A.L (C.n ^ j : ℕ) (C.n ^ j) x' θ') → ∃ θ : ThetaGrp C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := R) F), SymLift C.A.A C.A.L (C.n ^ j : ℕ) (C.n ^ j) x θ) ∧ ∀ θ : ThetaGrp C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := R) F), SymLift C.A.A C.A.L (C.n ^ j : ℕ) (C.n ^ j) x θ → ∃ θ' : ThetaGrp T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := W) F), SymLift T.A.A T.A.L (C.n ^ j : ℕ) (C.n ^ j) x' θ' ∧ ∀ (σ σ' : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j)) (τ τ' : SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ q z Jt) → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ' p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ' q z Jt) → IsActOf T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) θ' σ σ' → IsActOf C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) θ τ τ' := by
  first | exact @GlobalTheory.ThetaMove.transport_symLift | exact GlobalTheory.ThetaMove.transport_symLift | (intros; apply GlobalTheory.ThetaMove.transport_symLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumTermsEqThetaConstantTranslateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_sum_terms_eq_theta_constant_translate : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → ∃ e : ℕ, SumF (maximalIdeal V) (FractionRing V) (fun mu : Fin 8 → X => ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩) := by
  first | exact @GlobalTheory.Poinc.Sep.TwistTranslate.twistSum_translate | exact GlobalTheory.Poinc.Sep.TwistTranslate.twistSum_translate | (intros; apply GlobalTheory.Poinc.Sep.TwistTranslate.twistSum_translate <;> assumption)
end

